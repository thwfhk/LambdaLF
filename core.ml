open Format
open Syntax

let rec isnumericval ctx t = match t with
    TmZero -> true
  | TmSucc(t1) -> isnumericval ctx t1
  | _ -> false

let rec isval ctx t = match t with
    TmTrue -> true
  | TmFalse -> true
  | t when isnumericval ctx t -> true
  | TmNil -> true
  | TmCons(n, t1, t2) -> isnumericval ctx n && isval ctx t1 && isval ctx t2
  | TmAbs(_,_,_) -> true
  | _ -> false

exception NoRuleApplies

let rec eval1 ctx t = match t with
    TmApp(TmAbs(x, tyT11, t12), v2) when isval ctx v2 ->
      termSubstTop v2 t12
  | TmApp(v1, t2) when isval ctx v1 ->
      let t2' = eval1 ctx t2 in
      TmApp(v1, t2')
  | TmApp(t1, t2) ->
      let t1' = eval1 ctx t1 in
      TmApp(t1', t2)

  | TmIf(TmTrue, t2, t3) ->
      t2
  | TmIf(TmFalse, t2, t3) ->
      t3
  | TmIf(t1, t2, t3) ->
      let t1' = eval1 ctx t1 in
      TmIf(t1', t2, t3)

  | TmSucc(t1) ->
      let t1' = eval1 ctx t1 in
      TmSucc(t1')
  | TmPred(TmZero) ->
      TmZero
  | TmPred(TmSucc(nv1)) when isnumericval ctx nv1 ->
      nv1
  | TmPred(t1) ->
      let t1' = eval1 ctx t1 in
      TmPred(t1')
  | TmIsZero(TmZero) ->
      TmTrue
  | TmIsZero(TmSucc(nv1)) when isnumericval ctx nv1 ->
      TmFalse
  | TmIsZero(t1) ->
      let t1' = eval1 ctx t1 in
      TmIsZero(t1')

  | TmCons(n, v1, t2) when isnumericval ctx v1 ->
      let t2' = eval1 ctx t2 in
      TmCons(n, v1, t2')
  | TmCons(n, t1, t2) ->
      let t1' = eval1 ctx t1 in
      TmCons(n, t1', t2)
  | TmIsNil(n, TmNil) ->
      TmTrue
  | TmIsNil(n, TmCons(m, t1, t2)) ->
      TmFalse
  | TmIsNil(n, t1) ->
      let t1' = eval1 ctx t1 in
      TmIsNil(n, t1')
  | TmHead(n, TmCons(m, v1, t2)) when isnumericval ctx v1 ->
      v1
  | TmHead(n, t1) ->
      let t1' = eval1 ctx t1 in
      TmHead(n, t1')
  | TmTail(n, TmCons(m, t1, v2)) when isval ctx v2 ->
      v2
  | TmTail(n, t1) ->
      let t1' = eval1 ctx t1 in
      TmTail(n, t1')
  (* NOTE: 这里对于TmHead和TmTail只关心了他的返回值是value的时候就可以返回 *)

  | TmFix(v1) as t when isval ctx v1 ->
      (match v1 with
         TmAbs(_,_,t12) -> termSubstTop t t12
       | _ -> raise NoRuleApplies)
  | TmFix(t1) ->
      let t1' = eval1 ctx t1
      in TmFix(t1')

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
            else (printType ctx tyT1; printType ctx tyT2; 
                  error "kindof error: parameter type not equivalence")
        | _ -> error "kindof error: pi kind expected"
      )
  | TyBool -> KiStar
  | TyNat -> KiStar
  | TyVector(t) -> KiStar

and kindstar ctx tyT = 
  if kindof ctx tyT = KiStar then ()
  else error "kind not equal to KiStar"
    

and typeof ctx t = match t with
    TmVar(x, _) -> getTypeFromContext ctx x
  | TmAbs(x, tyS, t) ->
      let () = kindstar ctx tyS in
      let ctx' = addbinding ctx x (VarBind(tyS)) in 
      let ctx'' = shiftContext ctx' in   (* notice *)
      let tyT = typeof ctx'' t in
      TyPi(x, tyS, tyT)
  | TmApp(t1, t2) ->
      let ty = typeof ctx t1 in
      let tyS2 = typeof ctx t2 in 
      (match ty with
          TyPi(_, tyS1, tyT) ->
            if tyeqv ctx tyS1 tyS2 then tySubstTop t2 tyT (* [x->t2]tyT *)
            else 
            let () = printctx ctx;pr"\n";debugType ctx tyS1;pr"\n";debugType ctx tyS2;pr"\n" in 
            error "typeof error: parameter type mismatch"
        | _ -> error "typeof error: [TmApp] arrow type expected")

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

  | TmZero ->
      TyNat
  | TmSucc(t1) ->
      if tyeqv ctx (typeof ctx t1) TyNat then TyNat
      else error "argument of succ is not a number"
  | TmPred(t1) ->
      if tyeqv ctx (typeof ctx t1) TyNat then TyNat
      else error "argument of pred is not a number"
  | TmIsZero(t1) ->
      if tyeqv ctx (typeof ctx t1) TyNat then TyBool
      else error "argument of iszero is not a number"

  | TmFix(t1) ->
      let tyT1 = typeof ctx t1 in
      (match tyT1 with
        TyPi(_, tyT11, tyT12) ->
          if tyeqvFix ctx tyT11 tyT12 0 then tyT11
          else (debugType ctx tyT11; pr"\n"; debugType ctx tyT12; pr"\n";
                error "result of body not compatible with domain")
      | _ -> error "typeof error: [TmFix] arrow type expected")
  
  | TmNil -> TyVector(TmZero)
  | TmCons(n, t1, t2) ->
      let tyN = typeof ctx n in
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      if not (tyeqv ctx tyN TyNat) 
      then error "typeof error: [TmCons] first argument not Nat"
      else if not (tyeqv ctx tyT1 TyNat)
      then error "typeof error: [TmCons] second argument not Nat"
      else if not (tyeqv ctx tyT2 (TyVector(n))) 
      then 
      let () = printType ctx tyT2; pr " "; printTerm ctx n in
      error "typeof error: [TmCons] Vector n mismatch"
      else TyVector(TmSucc(n))
  | TmIsNil(n, t1) ->
      let tyN = typeof ctx n in
      let tyT1 = typeof ctx t1 in
      if not (tyeqv ctx tyN TyNat) 
      then error "typeof error: [TmIsNil] first argument not Nat"
      else if not (tyeqv ctx tyT1 (TyVector(n))) 
      then error "typeof error: [TmIsNil] Vector n mismatch"
      else TyBool
  | TmHead(n, t1) ->
      let tyN = typeof ctx n in
      let tyT1 = typeof ctx t1 in
      if not (tyeqv ctx tyN TyNat) 
      then error "typeof error: [TmHead] first argument not Nat"
      else if not (tyeqv ctx tyT1 (TyVector(n))) 
      then error "typeof error: [TmHead] Vector n mismatch"
      else TyNat
  | TmTail(n, t1) ->
      let tyN = typeof ctx n in
      let tyT1 = typeof ctx t1 in
      if not (tyeqv ctx tyN TyNat) 
      then error "typeof error: [TmTail] first argument not Nat"
      else if not (tyeqv ctx tyT1 (TyVector(n))) 
      then error "typeof error: [TmTail] Vector n mismatch"
      else TyVector(TmPred(n))

and kindeqv ctx ki1 ki2 = match (ki1, ki2) with
    (KiStar, KiStar) -> true
  | (KiPi(x, tyT1, kiK1), KiPi(_, tyT2, kiK2)) ->
      tyeqv ctx tyT1 tyT2 &&
      let ctx' = addbinding ctx x (VarBind(tyT1))
      in kindeqv ctx' kiK1 kiK2
  | _ -> false

and tyeqv ctx ty1 ty2 = 
  (* let () = (pr "tyeqv "; debugType ctx ty1; pr" "; debugType ctx ty2; pr"\n") in *)
  match (ty1, ty2) with
    (TyBool, TyBool) -> true
  | (TyNat, TyNat) -> true
  | (TyVar(x1,_), TyVar(x2,_)) -> x1 = x2
  | (TyPi(x, tyS1, tyS2), TyPi(_, tyT1, tyT2)) ->
      tyeqv ctx tyS1 tyT1 &&
      let ctx' = addbinding ctx x (VarBind(tyS1)) 
      in tyeqv ctx' tyS2 tyT2
  | (TyApp(tyS1, t1), TyApp(tyS2, t2)) -> 
      tyeqv ctx tyS1 tyS2 && 
      (* let () = pr"TyApp tmeqv: ";pr (string_of_bool (tmeqv ctx t1 t2));pr"\n" in *)
      tmeqv ctx t1 t2
  | (TyVector(n1), TyVector(n2)) ->
      tmeqv ctx n1 n2
  | _ -> false
  
and tmeqv ctx tm1 tm2 = 
    (* let () = (pr "tmeqv tm "; debugTerm ctx tm1; pr" "; debugTerm ctx tm2; pr"\n") in *)
    let v1 = eval ctx tm1 in
    let v2 = eval ctx tm2 in
    (* let () = (pr "tmeqv v "; debugTerm ctx v1; pr" "; debugTerm ctx v2; pr"\n"; pr (string_of_bool (v1 = v2)); pr"\n") in *)
    match (v1, v2) with
        (TmTrue, TmTrue) -> true
      | (TmFalse, TmFalse) -> true
      | (TmIf(t1, t2, t3), TmIf(s1, s2, s3)) -> 
          tmeqv ctx t1 s1 && tmeqv ctx t2 s2 && tmeqv ctx t3 s3
      | (TmZero, TmZero) -> true
      | (TmSucc(t1), TmSucc(s1)) -> tmeqv ctx t1 s1
      | (TmPred(t1), TmPred(s1)) -> tmeqv ctx t1 s1
      | (TmIsZero(t1), TmIsZero(s1)) -> tmeqv ctx t1 s1
      | (TmNil, TmNil) -> true
      | (TmCons(t1, t2, t3), TmCons(s1, s2, s3)) -> 
          tmeqv ctx t1 s1 && tmeqv ctx t2 s2 && tmeqv ctx t3 s3
      | (TmIsNil(t1, t2), TmIsNil(s1,s2)) -> 
          tmeqv ctx t1 s1 && tmeqv ctx t2 s2
      | (TmHead(t1, t2), TmHead(s1,s2)) -> 
          tmeqv ctx t1 s1 && tmeqv ctx t2 s2
      | (TmTail(t1, t2), TmTail(s1,s2)) -> 
          tmeqv ctx t1 s1 && tmeqv ctx t2 s2
      | (TmApp(t1, t2), TmApp(s1,s2)) -> 
          tmeqv ctx t1 s1 && tmeqv ctx t2 s2
      | (TmAbs(_, tyT1, t2), TmAbs(_, tyS1, s2)) ->
          tyeqv ctx tyT1 tyS1 && tmeqv ctx t2 s2
      | (TmVar(x1, _), TmVar(x2, _)) -> x1 = x2
      | _ -> v1 = v2

and tmeqvFix ctx tm1 tm2 c=    
    (* let () = (pr "tmeqv tm "; debugTerm ctx tm1; pr" "; debugTerm ctx tm2; pr"\n") in *)
    let v1 = eval ctx tm1 in
    let v2 = eval ctx tm2 in
    (* let () = (pr "tmeqv v "; debugTerm ctx v1; pr" "; debugTerm ctx v2; pr"\n"; pr (string_of_bool (v1 = v2)); pr"\n") in *)
    match (v1, v2) with
        (TmTrue, TmTrue) -> true
      | (TmFalse, TmFalse) -> true
      | (TmIf(t1, t2, t3), TmIf(s1, s2, s3)) -> 
          tmeqvFix ctx t1 s1 c && tmeqvFix ctx t2 s2 c && tmeqvFix ctx t3 s3 c
      | (TmZero, TmZero) -> true
      | (TmSucc(t1), TmSucc(s1)) -> tmeqvFix ctx t1 s1 c
      | (TmPred(t1), TmPred(s1)) -> tmeqvFix ctx t1 s1 c
      | (TmIsZero(t1), TmIsZero(s1)) -> tmeqvFix ctx t1 s1 c
      | (TmNil, TmNil) -> true
      | (TmCons(t1, t2, t3), TmCons(s1, s2, s3)) -> 
          tmeqvFix ctx t1 s1 c && tmeqvFix ctx t2 s2 c && tmeqvFix ctx t3 s3 c
      | (TmIsNil(t1, t2), TmIsNil(s1,s2)) -> 
          tmeqvFix ctx t1 s1 c && tmeqvFix ctx t2 s2 c
      | (TmHead(t1, t2), TmHead(s1,s2)) -> 
          tmeqvFix ctx t1 s1 c && tmeqvFix ctx t2 s2 c
      | (TmTail(t1, t2), TmTail(s1,s2)) -> 
          tmeqvFix ctx t1 s1 c && tmeqvFix ctx t2 s2 c
      | (TmApp(t1, t2), TmApp(s1,s2)) -> 
          tmeqvFix ctx t1 s1 c && tmeqvFix ctx t2 s2 c
      | (TmAbs(_, tyT1, t2), TmAbs(_, tyS1, s2)) ->
          tyeqvFix ctx tyT1 tyS1 c && tmeqvFix ctx t2 s2 (c+1)
      | (TmVar(x1, _), TmVar(x2, _)) -> if x1>=c then x1+1 = x2 else x1 = x2
      | _ -> v1 = v2

  
and tyeqvFix ctx ty1 ty2 c = 
    (* let () = printctx ctx;pr " "; debugType ctx ty1; pr" "; debugType ctx ty2; pr"\n" in *)
    match (ty1, ty2) with 
    (TyBool, TyBool) -> true
  | (TyNat, TyNat) -> true
  | (TyVar(x1,_), TyVar(x2,_)) -> if x1>=c then x1+1 = x2 else x1 = x2
  (* ty2比ty1的ctx多了一个变量绑定，但是用的ctx是ty1的 *)
  | (TyPi(x, tyS1, tyS2), TyPi(_, tyT1, tyT2)) ->
      tyeqvFix ctx tyS1 tyT1 c &&
      let ctx' = addbinding ctx x (VarBind(tyS1)) 
      in tyeqvFix ctx' tyS2 tyT2 (c+1)
  | (TyApp(tyS1, t1), TyApp(tyS2, t2)) -> 
      tyeqvFix ctx tyS1 tyS2 c && tmeqvFix ctx t1 t2 c
  | (TyVector(n1), TyVector(n2)) ->
      tmeqvFix ctx n1 n2 c
  | _ -> false