open Syntax
open Core

let t = TmAbs("x", TyBool, TmVar(0, 1))

let ctx1 = [("hi", TyVarBind(KiPi("x", TyBool, KiStar))); ("hiIns", VarBind(TyApp(TyVar(0, 2), TmTrue)))]

let t1 = TmAbs("x", TyApp(TyVar(0, 2), TmTrue), TmVar(0, 3))

let t2 = TmApp(t1, TmVar(1,2)) (* :hi true *)

let t3 = TmAbs("x", TyBool, TmVar(2, 3))

(* 还没测试Pi中有lambda，不过应该没啥问题 'w| *)


let ctx2 = [("Vector", TyVarBind(KiPi("x", TyNat, KiStar))); ("nil", VarBind(TyApp(TyVar(0, 3), TmZero)));
            ("cons", VarBind( 
              TyPi("n", TyNat, 
                TyPi("x", TyBool, 
                  TyPi("v", 
                    TyApp(TyVar(2, 5), TmVar(1, 5)), 
                    TyApp(TyVar(3, 6), TmSucc(TmVar(2, 6))) 
                  ) 
                )
              ) ))]

let ty1 = typeof ctx2 (TmVar(2,3))

let one = TmSucc(TmZero)
let two = TmSucc(one)

let mkone = TmAbs("x", TyBool, 
              TmApp(
                TmApp(
                  TmApp(TmVar(3, 4), TmZero), 
                  TmVar(0, 4)
                ), 
                TmVar(2,  4)
              )
            )

let mktwo = TmAbs("y", TyBool, 
              TmAbs("x", TyBool, 
                TmApp(
                  TmApp(
                    TmApp(TmVar(4, 5), TmSucc(TmZero)),
                    TmVar(1, 5)
                  ),
                  TmApp(
                    TmApp(
                      TmApp(TmVar(4, 5), TmZero), 
                      TmVar(0, 5)
                    ), 
                    TmVar(3,  5)
                  )
                )
              )
            )

let vec1 = TmApp(mkone, TmTrue)
let vec2 = TmApp(TmApp(mktwo, TmTrue), TmFalse)
