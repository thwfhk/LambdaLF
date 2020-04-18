open Syntax
open Core

let ctxlen = 0
let ctx = []

let zero = TmZero
let one = TmSucc(TmZero)
let two = TmSucc(one)
let three = TmSucc(two)

let mkthree =
  TmAbs("z", TyNat,
    TmAbs("y", TyNat,
      TmAbs("x", TyNat,
        TmCons(two, TmVar(2, 3+ctxlen),
          TmCons(one, TmVar(1, 3+ctxlen),
            TmCons(zero, TmVar(0, 3+ctxlen), TmNil)
          )
        )
      )
    )
  )

let vec3 = TmApp(TmApp(TmApp(mkthree, one), two), three)

let plus = 
  TmFix(
    TmAbs("plus", TyPi("X", TyNat, TyPi("Y", TyNat, TyNat)),
      TmAbs("x", TyNat, 
        TmAbs("y", TyNat,
          TmIf(
            TmIsZero(TmVar(1, 3+ctxlen)),
            TmVar(0, 3+ctxlen),
            TmApp(TmApp(TmVar(2, 3+ctxlen), TmPred(TmVar(1, 3+ctxlen))), TmSucc(TmVar(0, 3+ctxlen)))
          )
        )
      )
    )
  )

let sum = 
  TmFix(
    TmAbs("sum",
      TyPi("N", TyNat, TyPi("V", TyVector(TmVar(0, 1+ctxlen)), TyNat)),
      TmAbs("n", TyNat,
        TmAbs("v", TyVector(TmVar(0, 2+ctxlen)),
          TmIf(
            TmIsNil(TmVar(1, 3+ctxlen), TmVar(0, 3+ctxlen)),
            TmZero,
            TmApp(
              TmApp(
                plus,
                TmHead(TmVar(1, 3+ctxlen), TmVar(0, 3+ctxlen))
              ),
              TmApp(
                TmApp(TmVar(2, 3+ctxlen), TmPred(TmVar(1, 3+ctxlen))),
                TmTail(TmVar(1, 3+ctxlen), TmVar(0, 3+ctxlen))
              )
            )
          )
        )
      )
    )
  )

let test1 = TmApp(TmApp(sum, three), vec3)


let prty t = printType ctx (typeof ctx t); pr"\n"
let prtm t = printTerm ctx (eval ctx t); pr"\n"