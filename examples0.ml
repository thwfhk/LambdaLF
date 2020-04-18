open Syntax
open Core

let t = TmAbs("x", TyBool, TmVar(0, 1))

let ctx1 = [("hi", TyVarBind(KiPi("x", TyBool, KiStar))); ("hiIns", VarBind(TyApp(TyVar(0, 2), TmTrue)))]

let t1 = TmAbs("x", TyApp(TyVar(0, 2), TmTrue), TmVar(0, 3))

let t2 = TmApp(t1, TmVar(1,2)) (* :hi true *)

let t3 = TmAbs("x", TyBool, TmVar(2, 3))

(* 还没测试Pi中有lambda，不过应该没啥问题 'w| *)