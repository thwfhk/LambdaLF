open Syntax
open Core

let ctxlen = 0

let fool = 
  TmFix(
    TmAbs("fool", TyPi("X",TyNat,TyBool),
      TmAbs("x", TyNat,
        TmIf(
          TmIsZero(TmVar(0, ctxlen+2)),
          TmTrue,
          TmApp(TmVar(1, ctxlen+2), TmPred(TmVar(0, ctxlen+2)))
        )
      )
    )
  )

let fool_2 = TmApp(fool, TmSucc(TmZero))

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

let plus_1_2 = TmApp(TmApp(plus, TmSucc(TmZero)), TmSucc(TmSucc(TmZero)))