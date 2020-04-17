(* module Core

   Core typechecking and evaluation functions
*)

open Syntax

val eval : context -> term -> term 

(* val whnf : term -> term  *)
val typeof : context -> term -> ty 
val kindof : context -> ty -> kind 
val checkkind : context -> kind -> unit 
val kindeqv : context -> kind -> kind -> bool 
val tyeqv : context -> ty -> ty -> bool 
val tmeqv : context -> term -> term -> bool