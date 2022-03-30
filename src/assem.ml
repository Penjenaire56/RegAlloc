(* 
    Langage bas niveau sans limitation dans le nombre de registre 
    
    C'est le langage source de l'allocation de registre
*)

type label = string


(* destinations, sources, jump option *)
type instr = 
    | Oper of string list * string list * label list option
    (* label *)
    | Label of label 
    (* destination , source *)
    | Move of string * string 
    (* src *)
    | Ret of string
