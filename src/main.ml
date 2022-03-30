open Assem
(*
    Liste d'instruction correspondant à : 
    
    a <- 0
L1: b <- a + 1
    c <- c + b 
    a <- b * 2
    if a < N goto L1
    return c

*)
let example1 = [
    Oper(["a"], [], None);
    Label("L1");
    Oper(["b"], ["a"], None);
    Oper(["c"], ["c"; "b"], None);
    Oper(["a"], ["b"], None);
    Oper([], ["a"], Some(["L1"]));
    Ret("c")
]   
;;


Regalloc.regalloc example1