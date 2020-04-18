open Syntax
open Core

let ctxlen = 6

let ctx = [("Vector", TyVarBind(KiPi("x", TyNat, KiStar))); 
          ("nil", VarBind(TyApp(TyVar(0, ctxlen), TmZero)));
          ("cons", VarBind( 
            TyPi("n", TyNat, 
              TyPi("x", TyNat, 
                TyPi("v", 
                  TyApp(TyVar(2, 2+ctxlen), TmVar(1, 2+ctxlen)), 
                  TyApp(TyVar(3, 3+ctxlen), TmSucc(TmVar(2, 3+ctxlen))) 
                ) 
              )
            )));
          ("isnil", VarBind(
            TyPi("n", TyNat,
              TyPi("v", TyApp(TyVar(1, 1+ctxlen), TmVar(0, 1+ctxlen)), TyBool)
            )
          ));
          ("head", VarBind(
            TyPi("n", TyNat,
              TyPi("v", TyApp(TyVar(1, 1+ctxlen), TmVar(0, 1+ctxlen)), TyNat)
            )
          ));
          ("tail", VarBind(
            TyPi("n", TyNat,
              TyPi("v", TyApp(TyVar(1, 1+ctxlen), TmVar(0, 1+ctxlen)), 
                TyApp(TyVar(2, 2+ctxlen), TmPred(TmVar(1, 2+ctxlen)))
              )
            )
          ));
          ]
(* 新的global binding加在后面，这样可以不改动之前的De Bruijn index *)

let prty t = printType ctx (typeof ctx t); pr"\n"

(* d表示有几层binding *)
let vector d = TyVar(d, d+ctxlen)
let nil d = TmVar(d+1, d+ctxlen)
let cons d = TmVar(d+2, d+ctxlen)
let isnil d = TmVar(d+3, d+ctxlen)
let head d = TmVar(d+4, d+ctxlen)
let tail d = TmVar(d+5, d+ctxlen)

let one = TmSucc(TmZero)
let two = TmSucc(one)

let mkone = TmAbs("x", TyNat, 
              TmApp(
                TmApp(
                  TmApp(cons 1, TmZero), 
                  TmVar(0, 1+ctxlen)
                ), 
                nil 1
              )
            )

let mktwo = TmAbs("y", TyNat, 
              TmAbs("x", TyNat, 
                TmApp(
                  TmApp(
                    TmApp(cons 2, TmSucc(TmZero)),
                    TmVar(1, 2+ctxlen)
                  ),
                  TmApp(
                    TmApp(
                      TmApp(cons 2, TmZero), 
                      TmVar(0, 2+ctxlen)
                    ), 
                    nil 2
                  )
                )
              )
            )

let vec1 = TmApp(mkone, TmZero)
let vec2 = TmApp(TmApp(mktwo, one), two)


(* ----------------------------------------------------- *)

let plus = 
  TmFix(
    TmAbs("plus", TyPi("X", TyNat, TyPi("Y", TyNat, TyNat)),
      TmAbs("x", TyNat, 
        TmAbs("y", TyNat,
          TmIf(
            TmIsZero(TmVar(1, ctxlen+3)),
            TmVar(0, ctxlen+3),
            TmApp(TmApp(TmVar(2, ctxlen+3), TmPred(TmVar(1, ctxlen+3))), TmSucc(TmVar(0, ctxlen+3)))
          )
        )
      )
    )
  )

let sum = 
  TmFix(
    TmAbs("sum", 
    (* 要注意这里是1+ctxlen，因为sum并没有加进去 *)
      TyPi("N", TyNat, TyPi("V", TyApp(vector 1, TmVar(0, ctxlen+1)), TyNat)),
      TmAbs("n", TyNat,
        TmAbs("v", TyApp(vector 2, TmVar(0, ctxlen+2)),
          TmIf(
            TmApp(TmApp(isnil 3, TmVar(1, ctxlen+3)), TmVar(0, ctxlen+3)),
            TmZero,
            TmApp(
              TmApp(plus, TmApp(TmApp(head 3, TmVar(1, ctxlen+3)), TmVar(0, ctxlen+3))),
              TmApp(TmApp(TmVar(2, ctxlen+3), 
                TmPred(TmVar(1, ctxlen+3))), 
                TmApp(TmApp(tail 3, TmVar(1, ctxlen+3)), TmVar(0, ctxlen+3))
              )
            )
          )
        )
      )
    )
  )

let sum_of_vec2 = TmApp(TmApp(sum, two), vec2)