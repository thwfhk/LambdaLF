(* module Syntax: syntax trees and associated support functions *)

(* Data type definitions *)
type ty = 
  TyVar of int * int
| TyPi of string * ty * ty  
| TyApp of ty * term
| TyBool

and term =
  TmVar of int * int            (* De Bruijn index, current contex length *)
| TmAbs of string * ty * term        (* original name, term *)
| TmApp of term * term
| TmTrue
| TmFalse
| TmIf of term * term * term

and kind = 
  KiStar
| KiPi of string * ty * kind

type binding =
  NameBind 
| VarBind of ty
| TyVarBind of kind

type context = (string * binding) list  (* name * binding *)

type command =
| Eval of term
| Bind of string * binding

(* Contexts *)
val emptycontext : context 
val ctxlength : context -> int
val addbinding : context -> string -> binding -> context
val addname: context -> string -> context
val index2name : context -> int -> string
val getbinding : context -> int -> binding
val name2index : context -> string -> int
val isnamebound : context -> string -> bool
val printctx : context -> unit


(* Shifting and substitution *)
val termShift: int -> term -> term
val termSubstTop: term -> term -> term
val tyShift: int -> ty -> ty
val tySubstTop: term -> ty -> ty

val getTypeFromContext: context -> int -> ty
val getKindFromContext: context -> int -> kind

val print: string -> unit
val pr: string -> unit
val error: string -> 'a

(* Printing *)

val printType: context -> ty -> unit
val printValue: context -> term -> unit


