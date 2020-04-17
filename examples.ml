open Syntax
open Core

let t = TmAbs("x", TyBool, TmVar(0, 1))

let ctx1 = [("hi", TyVarBind(KiPi("t", TyBool, KiStar))); ("hiIns", VarBind(TyApp(TyVar(0, 2), TmTrue)))]
(* 这里好像有点问题，由于ctx用的De Bruijn，默认他们都是某个bound的，不过也可以相互使用QwQ *)

let t1 = TmAbs("x", TyApp(TyVar(0, 2), TmTrue), TmVar(0, 3))

let t2 = TmApp(t1, TmVar(1,2)) (* :hi true *)

(* 还没测试Pi中有lambda，不过应该没啥问题 *)