(* ---------------------------------------------------------------------- *)
(* Datatypes *)

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
    NameBind               (* 只是占位 *)
  | VarBind of ty
  | TyVarBind of kind

type context = (string * binding) list  (* name * binding *)

type command =
  | Eval of term
  | Bind of string * binding

(* ---------------------------------------------------------------------- *)
(* Utilities *)

exception Exit

let pr = output_string stdout

let print x = output_string stdout x; flush stdout

let error x = pr x; pr " "; raise Exit

(* ---------------------------------------------------------------------- *)
(* Context management *)

let emptycontext = []

let ctxlength ctx = List.length ctx

let addbinding ctx x bind = (x,bind)::ctx (* 每次加入开头，index是0 *)

let addname ctx x = addbinding ctx x NameBind

let rec printctx ctx = 
  match ctx with
      [] -> ()
    | (x,_)::rest ->
        print x; print " "; printctx rest

let rec isnamebound ctx x =
  match ctx with
      [] -> false
    | (y,_)::rest ->
        if y=x then true
        else isnamebound rest x

let rec pickfreshname ctx x =
  if isnamebound ctx x then pickfreshname ctx (x^"'")
  else ((x,NameBind)::ctx), x

let index2name ctx x =
  try
    let (xn,_) = List.nth ctx x in xn
  with Failure _ -> error "Variable lookup failure! "

let rec name2index ctx x =
  match ctx with
      [] -> error ("Identifier " ^ x ^ " is unbound! ")
    | (y,_)::rest ->
        if y=x then 0
        else 1 + (name2index rest x)

(* ---------------------------------------------------------------------- *)
(* Shifting *)

(* 对于var应用onvar(substitution或者shift)，c记录当前是第几层abs(0开始) *)
let tmmap onvar c t = 
  let rec walk c t = match t with
      TmVar(x, n) -> onvar c x n
    | TmAbs(s, ty, t) -> TmAbs(s, ty, walk (c+1) t)
    | TmApp(t1, t2) -> TmApp(walk c t1, walk c t2)
    | TmTrue -> TmTrue
    | TmFalse -> TmFalse
    | TmIf(t1, t2, t3) -> TmIf(walk c t1, walk c t2, walk c t3)
  in walk c t

let tymap onvar c ty = 
  let rec walk c t = match t with
      TyVar(x, n) -> TyVar(x, n)
    | TyPi(s, ty1, ty2) -> TyPi(s, walk c ty1, walk (c+1) ty2)
    | TyApp(ty, t) -> TyApp(walk c ty, tmmap onvar c t)
    | TyBool -> TyBool
  in walk c ty

(* \uparrow^d_c (t) *)
let termShiftAbove d c t =
  tmmap 
    (fun c x n -> if x >= c then TmVar(x+d, n+d) else TmVar(x, n+d))
    c t

let termShift d t = termShiftAbove d 0 t

(* [j->s]t 其实只要用到j=0 *)
let termSubst j s t =
  tmmap
    (fun c x n -> if x=j+c then termShift c s else TmVar(x,n))
    0 t

(* [0->s]t加上外面去掉一层lambda *)
let termSubstTop s t = 
  termShift (-1) (termSubst 0 (termShift 1 s) t)

let tyShiftAbove d c t =
  tymap 
    (fun c x n -> if x >= c then TmVar(x+d, n+d) else TmVar(x, n+d))
    c t
let tyShift d t = tyShiftAbove d 0 t

(* [j->s]t 其实只要用到j=0 *)
let tySubst j s t =
  tymap 
    (fun c x n -> if x=j+c then termShift c s else TmVar(x, n))
    0 t
(* [0->s]t加上外面去掉一层lambda *)
let tySubstTop s t = 
  tyShift (-1) (tySubst 0 (termShift 1 s) t)

(* ---------------------------------------------------------------------- *)
(* Context management (continued) *)

(* return the i-th bind in ctx *)
let rec getbinding ctx i =
  try
    let (_,bind) = List.nth ctx i in
    bind 
  with Failure _ -> error "Variable lookup failure! "

let rec getTypeFromContext ctx i =
  match getbinding ctx i with
    VarBind(ty) -> ty
  | _ -> error "getTypeFromContext Error: Wrong kind of binding for variable "

let rec getKindFromContext ctx i =
  match  getbinding ctx i with
    TyVarBind(ki) -> ki
  | _ -> error "getKindFromContext Error: Wrong kind of binding for variable "

(* ---------------------------------------------------------------------- *)

let rec printType ctx ty = match ty with
    TyBool -> 
      pr "Bool"
  | TyPi(x, ty1, ty2) ->
      pr"Pi "; pr x; pr ":"; 
      printType ctx ty1; pr "."; printType ctx ty2
  | TyVar(x, n) ->
      if ctxlength ctx = n then
        pr (index2name ctx x)
      else
        error ("Unconsistency found when printing! ")
  | TyApp(tyT1, t2) ->
      printType ctx tyT1;
      pr " ";
      printValue ctx t2;

and printValue ctx t = match t with
    TmVar(x, n) ->
      if ctxlength ctx = n then
        pr (index2name ctx x)
      else
        error ("Unconsistency found when printing! ")
  | TmApp(t1, t2) ->
      printValue ctx t1;
      pr " ";
      printValue ctx t2
  | TmAbs(x, tyT1, t2) -> 
      let (ctx', x') = pickfreshname ctx x in
      pr "(lambda "; pr x'; pr ":"; printType ctx tyT1;
      pr "."; printValue ctx' t2; pr ")"
  | TmTrue -> 
      pr "true"
  | TmFalse ->
      pr "false"
  | TmIf(t1, t2, t3) ->
      pr "if "; printValue ctx t1; pr " then "; printValue ctx t2; pr " else "; printValue ctx t3