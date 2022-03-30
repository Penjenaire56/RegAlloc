open Assem
open Printf

(* DataStructure *)
module SSet = Set.Make(String);;
module ISet = Set.Make(Int);;
module IMap = Map.Make(Int);;
module SMap = Map.Make(String);;

module Vertice = Set.Make(struct
    type t = string * string 
    let compare = compare
end);;

type graph = {
    (* L'ensemble des liens d'interférences *)
    adjSet : Vertice.t;
    (* L'ensemble temporaire des interférences *)
    adjList : SSet.t SMap.t;
    (* Degree courrant des nodes *)
    degree : int SMap.t;
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

let verticesToString v = 
    Vertice.fold (fun (x,y) t -> t ^ "(" ^ x ^ "," ^ y ^")") v ""

let printGraph g = 
    eprintf "%s\n" (verticesToString (g.adjSet))

(* Main *)


(* Temporaire *)
let spilledNodes = []

(* Fonction principale

    Fait l'allocation des registres en implémentant la version du Tiger Book
*)
let rec regalloc(listInst : instr list) = 
    let precolored = SMap.empty in
    let initial = SSet.empty in 
    let (nodes, nodes_in, nodes_out) = livenessAnalysis(listInst) in 
    printNode(nodes);
    eprintf "IN : \n";
    printNodeSet(nodes_in);
    eprintf "OUT : \n";
    printNodeSet(nodes_out);

    let (moveList, worklistMoves, _, g) =  
        build nodes precolored (IMap.find ((List.length listInst) - 2) nodes_out) in 
   
    eprintf "%s" (printIMap instrToString worklistMoves);
    printGraph g;
    let (spillWorklist, freezeWorklist, simplifyWorklist) = makeWorkList initial g moveList in
    
    let rec aux_alloc () = 
        if not(SSet.is_empty simplifyWorklist) then
            (simplify() ; aux_alloc())
        else if not(IMap.is_empty worklistMoves) then 
            (coalesce(); aux_alloc())
        else if not(SSet.is_empty  freezeWorklist) then 
            (freeze(); aux_alloc())
        else if not(SSet.is_empty spillWorklist) then 
            (selectSpill(); aux_alloc())
        else 
            assignColors();
        
        if spilledNodes <> [] then 
            (rewriteProgram(); aux_alloc())
    in aux_alloc()

(* Analyse de liveness *)
and livenessAnalysis (listInst : instr list) = 
    let listInst = List.rev listInst in
    let len = List.length listInst in
    (* Initialisation des sets In et Out et création de la map regroupant les nodes *)
    let rec live_empty (i : int) = function 
        | [] -> (IMap.empty, IMap.empty, IMap.empty)
        | (x : instr) :: subL -> 
            let (nodes, node_in, node_out) = live_empty (i - 1) subL in
                (IMap.add i (x) nodes,
                 IMap.add i (SSet.empty) node_in,
                 IMap.add i (SSet.empty) node_out)

    in let (nodes, node_in', node_out') = live_empty len listInst
    
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
            (update node_in node_out)
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
and build (instMap : instr IMap.t) precolored (liveout : SSet.t) = 
    let moveList : ISet.t SMap.t = 
        SMap.empty 
    in
    let worklistMoves = IMap.empty in
    
    (* TODO Ajouter les variables existante avant *)
    let live = liveout in   
    let g : graph = {
        adjSet = Vertice.empty;
        adjList = SMap.empty; 
        degree = SMap.empty;
    } in IMap.fold(fun n v (m, w, l, g) -> 
            match v with 
            | Move(_,_) ->
                let (m, w, l, g) = (build_move n v (m, w, l, g)) in 
                    (build_allinstr v (m, w , l, g) precolored)
            | _ -> (build_allinstr v (m, w , l, g) precolored)
        ) instMap
        (moveList, worklistMoves, live, g) 

(* Construit les dépendances de l'instruction dans le graph d'interférence *)
and build_allinstr (i : instr) (m, w, live, graph) precolored = 
    let live = SSet.union live (defN i) in 

    let graph = SSet.fold (fun d graph -> 
        SSet.fold (fun l graph -> 
            (addEdge graph d l precolored) 
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
    SMap.add n (ISet.union 
        (SMap.find n moveList)
        (ISet.singleton x)
    ) moveList

(* Ajout des liens dans le graphs *)
and addEdge g u v precolored : graph =
    match Vertice.find_opt (u,v) g.adjSet with 
    | None when u <> v ->
        let g = notPrecolored precolored u v g in
        let g = notPrecolored precolored v u g in
        {
            adjSet = 
                Vertice.union 
                    (g.adjSet) 
                    (Vertice.union 
                        (Vertice.singleton (u,v))
                        (Vertice.singleton (v,u))
                    );
            adjList = g.adjList;
            degree = g.degree;
        }
    | _ -> g

(* Ajoute la variable x au degree et au adjList si non précoloré *)
and notPrecolored precolored u v g =
    match SMap.find_opt u precolored with 
    | None -> {
        adjSet = g.adjSet;
        adjList = 
            (match SMap.find_opt u g.adjList with
            | None -> 
                SMap.add u (SSet.singleton v) g.adjList
            | Some(f) -> 
                SMap.add u (SSet.union f (SSet.singleton v)) g.adjList);
        degree = 
            (match SMap.find_opt u g.degree with
            | None -> 
                SMap.add u 0 g.degree
            | Some(f) -> 
                SMap.add u (f + 1) g.degree)
    }
    | _ -> g

(* Temporaire *)
and makeWorkList (initial : SSet.t) (g : graph) moveList =
    SSet.fold (fun n (spill,freeze,simplify) -> 
        if (SMap.find n g.degree) > 1 then
            (SSet.union spill (SSet.singleton n),freeze,simplify)
        else if (SMap.find_opt n moveList) != None then
            (spill,SSet.union freeze (SSet.singleton n),simplify)
        else
            (spill,freeze, SSet.union simplify (SSet.singleton n))  
    ) initial (SSet.empty,SSet.empty,SSet.empty)





and simplify () = ()
and coalesce () = ()
and freeze () = ()
and selectSpill () = ()
and assignColors () = ()
and rewriteProgram () = () 