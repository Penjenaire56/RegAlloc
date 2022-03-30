open Assem
open Printf

(* DataStructure *)
module SSet = Set.Make(String);;
module IMap = Map.Make(Int);;

module Vertice = Map.Make(struct
    type t = int * int 
    let compare = compare
end);;

type graph = {
    (* L'ensemble des liens d'interférences *)
    adjSet : (int * int) Vertice.t;
    (* L'ensemble temporaire des interférences *)
    adjList : SSet.t IMap.t;
    (* Degree courrant des nodes *)
    degree : int IMap.t;
};;

(* Debug *)
let instrToString (i : instr) : string =  
    match i with
    | Label(l) -> l ^ ":\n" 
    | Move(s1,s2) -> s2 ^ " <- " ^ s1 ^ "\n"
    | Oper(l1,l2, None) -> 
        let s1 = (List.fold_left (fun x l -> x ^ l) "" l1) in 
        let s2 = (List.fold_left (fun x l -> x ^ l) "" l2) in 
        s1 ^ " <- " ^ s2 ^ "\n"
    | Oper(l1,l2, Some(l3)) -> 
        let s1 = (List.fold_left (fun x l -> x ^ l) "" l1) in 
        let s2 = (List.fold_left (fun x l -> x ^ l) "" l2) in 
        let s3 = (List.fold_left (fun x l -> x ^ l) "" l3) in 
            s1 ^ " <- " ^ s2 ^ " <== " ^ s3 ^ "\n"
    | Ret(s) ->
         "ret " ^ s ^ "\n"

let printInstr (i : instr) = 
    eprintf "%s" (instrToString i)

let printNode (nodes) = 
    IMap.iter(fun x i -> eprintf "%d\t" x ; printInstr i) nodes

let printSet s = 
    SSet.fold (fun x y -> x ^ y) s ""

let printNodeSet (nodes) = 
    IMap.iter (fun x i -> eprintf "%d\t%s\n" x (printSet i)) nodes

let printIMap f m = 
    IMap.fold (fun i v s -> s ^ (string_of_int i) ^ (f v)) m ""

(* Main *)


(* Temporaire *)
let simplifyWorklist = []
let freezeWorklist = []
let spillWorklist = []
let spilledNodes = []

(* Fonction principale

    Fait l'allocation des registres en implémentant la version du Tiger Book
*)
let rec regalloc(listInst : instr list) = 
    let (nodes, nodes_in, nodes_out) = livenessAnalysis(listInst) in 
    printNode(nodes);
    eprintf "IN : ";
    printNodeSet(nodes_in);
    eprintf "OUT : ";
    printNodeSet(nodes_out);

    let (_, worklistMoves, _, _) =  build(nodes) in 
    eprintf "%s" (printIMap instrToString worklistMoves);
    makeWorkList();
    
    let rec aux_alloc () = 
        if simplifyWorklist <> [] then
            (simplify() ; aux_alloc())
        else if not(IMap.is_empty worklistMoves) then 
            (coalesce(); aux_alloc())
        else if freezeWorklist <> [] then 
            (freeze(); aux_alloc())
        else if spillWorklist <> [] then 
            (selectSpill(); aux_alloc())
        else 
            assignColors();
        
        if spilledNodes <> [] then 
            (rewriteProgram(); aux_alloc())
    in aux_alloc()

(* Analyse de liveness *)
and livenessAnalysis (listInst : instr list) = 
    (* Initialisation des sets In et Out et création de la map regroupant les nodes *)
    let rec live_empty (i : int) = function 
        | [] -> (IMap.empty, IMap.empty, IMap.empty)
        | (x : instr) :: subL -> 
            let (nodes, node_in, node_out) = live_empty (i + 1) subL in
                (IMap.add i (x) nodes,
                 IMap.add i (SSet.empty) node_in,
                 IMap.add i (SSet.empty) node_out)

    in let (nodes, node_in', node_out') = live_empty 0 listInst
    
    (* Calcule des In et Out par recherche de point fixe *)
    in let rec update node_in' node_out' = 
        let node_in = 
            (* Calcule des entrées *)
            IMap.mapi (fun (n : int) _ -> 
                    SSet.union 
                        (useN (IMap.find n nodes)) 
                        (SSet.diff (IMap.find n node_out') (defN (IMap.find n nodes)))
            ) node_in'
        in let node_out = 
            (* Calcule des sorties *)
            IMap.mapi (fun (n : int) _ -> 
                let succs = (succN n nodes) in 
                let succs_in = List.map (fun x -> IMap.find x node_in') succs in
                List.fold_left (SSet.union) (SSet.empty) succs_in
            ) node_out'
        in if (IMap.equal (=) node_in' node_in) && (IMap.equal (=) node_out' node_out) then
            (nodes, node_in, node_out)
        else
            update node_in node_out
    in (update node_in' node_out')

(* Fonction calculant les successeurs d'une instruction
    Instruction suivante 
    
    ou 

    (Instruction suivante) U (label) 
*)
and succN (n : int) nodes = 
    let inst = IMap.find n nodes in 
    match inst with 
    | Ret(_) -> []
    | Oper(_,_, Some(label)) -> 
        List.fold_left (fun result (l : label) -> 
            (labelSucc nodes l) @ result
        ) [n + 1] label 
    | _ -> [n + 1]

(* Fonction de calcul du successeur d'un label

    Récupère le numéro ou se situe le label
*)
and labelSucc nodes lab = 
    IMap.fold (fun i v _ -> 
        (match v with 
        | Label(l) when l = lab -> [i]
        | _ -> [])
    ) nodes []

(* Calcule de l'ensemble des variables définies 

    Par exemple:
    1   x = 1 + a
    
    def(1) = {x}
*)
and defN (i : instr) = 
    match i with 
    | Move(dst, _) -> 
        SSet.singleton dst
    | Oper(dsts, _, _) -> 
        List.fold_left (fun m x -> SSet.union (SSet.singleton x) m) (SSet.empty) dsts
    | _ -> 
        SSet.empty

(* Calcule de l'ensemble des variables utilisées

    Par exemple:
    1   x = 1 + a
    
    use(1) = {a}
*)
and useN (i : instr) = 
    match i with 
    | Ret(src) ->  
        SSet.singleton src
    | Move(_, src) -> 
        SSet.singleton src
    | Oper( _, srcs, _) -> 
        List.fold_left (fun m x -> SSet.union (SSet.singleton x) m) (SSet.empty) srcs
    | _ -> 
        SSet.empty

(*  Construit le graph d'interférence 

*)
and build (instMap : instr IMap.t) = 
    let moveList = 
        IMap.fold (fun i _ m -> IMap.add i (SSet.empty) m) instMap IMap.empty 
    in
    let worklistMoves = IMap.empty in
    
    (* TODO Ajouter les variables existante avant *)
    let live = SSet.empty in   
    let g : graph = {
        adjSet = Vertice.empty;
        adjList = IMap.empty;
        degree = IMap.empty;
    } in IMap.fold(fun n v (m, w, l, g) -> 
            match v with 
            | Move(_,_) ->
                let (m, w, l, g) = (build_move n v (m, w, l, g)) in 
                    (build_allinstr v (m, w , l, g))
            | _ -> (build_allinstr v (m, w , l, g))
        ) instMap
        (moveList, worklistMoves, live, g) 

(* Construit les dépendances de l'instruction dans le graph d'interférence *)
and build_allinstr (i : instr) (m, w, live, graph) = 
    let live = SSet.union live (defN i) in 

    let graph = SSet.fold (fun d graph -> 
        SSet.fold (fun l graph -> 
            (addEdge graph d l) 
        ) live graph
    ) (defN i) graph in 

    let live = SSet.union (useN i) (SSet.diff live (defN(i))) in 
        (m, w, live, graph)

and build_move (n : int) (i : instr) (moveList, worklistMoves, live, g) = 
    let live = SSet.diff live (useN i) in
    let moveList = SSet.fold 
        (fun i m -> moveListUpdate i n m) 
        (SSet.union (defN i) (useN i)) 
        moveList 
    in 
    let worklistMoves = IMap.add n i worklistMoves in 
        (moveList, worklistMoves, live, g)

and moveListUpdate n x moveList = 
    IMap.add x (SSet.union 
        (IMap.find x moveList)
        (SSet.singleton n)
    ) moveList

(* Ajout des liens dans le graphs *)
and addEdge g _ _ : graph = g


(* Temporaire *)
and makeWorkList () = ()
and simplify () = ()
and coalesce () = ()
and freeze () = ()
and selectSpill () = ()
and assignColors () = ()
and rewriteProgram () = () 