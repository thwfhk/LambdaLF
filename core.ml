open Format
open Syntax

let rec isval ctx t = match t with
    TmTrue -> true
  | TmFalse -> true
  | TmAbs(_,_,_) -> true
  | _ -> false

exception NoRuleApplies

let rec eval1 ctx t = match t with
    TmIf(TmTrue, t2, t3) ->
      t2
  | TmIf(TmFalse, t2, t3) ->
      t3
  | TmIf(t1, t2, t3) ->
      let t1' = eval1 ctx t1 in
      TmIf(t1', t2, t3)
  | TmApp(TmAbs(x, tyT11, t12), v2) when isval ctx v2 ->
      termSubstTop v2 t12
  | TmApp(v1, t2) when isval ctx v1 ->
      let t2' = eval1 ctx t2 in
      TmApp(v1, t2')
  | TmApp(t1, t2) ->
      let t1' = eval1 ctx t1 in
      TmApp(t1', t2)
  | _ ->
      raise NoRuleApplies (* include TmVar *)

let rec eval ctx t =
  try let t' = eval1 ctx t
      in eval ctx t'
  with NoRuleApplies -> t


let rec checkkind ctx ki = match ki with
    KiStar -> ()
  | KiPi(x, tyT, ki') -> 
      let () = kindstar ctx tyT in
      let ctx' = addbinding ctx x (VarBind(tyT)) 
      in checkkind ctx' ki'


and kindof ctx tyT = match tyT with
    TyVar(x, _) -> getKindFromContext ctx x
  | TyPi(x, tyT1, tyT2) ->
      let () = kindstar ctx tyT1 in
      let ctx' = addbinding ctx x (VarBind(tyT1)) in 
      let () = kindstar ctx' tyT2 in
      KiStar
  | TyApp(tyS, t) ->
      let ki = kindof ctx tyS in
      let tyT2 = typeof ctx t in
      (
        match ki with 
          KiPi(_, tyT1, kiK) ->
            if tyeqv ctx tyT1 tyT2 then kiK 
            (* should be [x->t2]kiK; maybe it is not needed in the current implementation *)
            else (printType ctx tyT1; printType ctx tyT2; error "kindof error: parameter type not equivalence")
        | _ -> error "kindof error: pi kind expected"
      )
  | TyBool -> KiStar

and kindstar ctx tyT = 
  if kindof ctx tyT = KiStar then ()
  else error "kind not equal to KiStar"
    

and typeof ctx t = match t with
    TmVar(x, _) -> getTypeFromContext ctx x
  | TmAbs(x, tyS, t) ->
      let () = kindstar ctx tyS in
      let ctx' = addbinding ctx x (VarBind(tyS)) in 
      let tyT = typeof ctx' t in
      TyPi(x, tyS, tyT)
  | TmApp(t1, t2) ->
      let ty = typeof ctx t1 in
      let tyS2 = typeof ctx t2 in 
      (match ty with
          TyPi(_, tyS1, tyT) ->
            if tyeqv ctx tyS1 tyS2 then tySubstTop t2 tyT (* [x->t2]tyT *)
            else error "typeof error: parameter type mismatch"
        | _ -> error "typeof error: arrow type expected")
  | TmTrue -> 
      TyBool
  | TmFalse -> 
      TyBool
  | TmIf(t1, t2, t3) ->
      if (=) (typeof ctx t1) TyBool then
        let tyT2 = typeof ctx t2 in
        if (=) tyT2 (typeof ctx t3) then tyT2
        else error "arms of conditional have different types"
      else error "guard of conditional not a boolean"

and kindeqv ctx ki1 ki2 = match (ki1, ki2) with
    (KiStar, KiStar) -> true
  | (KiPi(x, tyT1, kiK1), KiPi(_, tyT2, kiK2)) ->
      if tyeqv ctx tyT1 tyT2 then
        let ctx' = addbinding ctx x (VarBind(tyT1))
        in kindeqv ctx' kiK1 kiK2
      else false
  | _ -> false

and tyeqv ctx ty1 ty2 = match (ty1, ty2) with
    (TyBool, TyBool) -> true
  | (TyVar(x1,_), TyVar(x2,_)) -> x1 = x2
  | (TyPi(x, tyS1, tyS2), TyPi(_, tyT1, tyT2)) ->
      if tyeqv ctx tyS1 tyT1 then
        let ctx' = addbinding ctx x (VarBind(tyS1)) 
        in tyeqv ctx' tyS2 tyT2
      else false
  | (TyApp(tyS1, t1), TyApp(tyS2, t2)) -> 
      tyeqv ctx tyS1 tyS2 && tmeqv ctx t1 t2
  | _ -> false
  
and tmeqv ctx tm1 tm2 = match (tm1, tm2) with
  | _ -> true
  