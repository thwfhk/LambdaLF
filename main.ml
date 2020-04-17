open Syntax
open Core

let parse_channel inChannel = 
  let lexbuf = Lexing.from_channel inChannel in
  let result =
    Parser.toplevel Lexer.token lexbuf 
    (*with Parsing.Parse_error -> print "Parse Error! " ; raise Exit*)
  in
  Parsing.clear_parser(); close_in inChannel; result

let prbinding b = match b with
    NameBind -> ()
  | VarBind(tyT) -> pr ": "; printType tyT 

let rec process_command ctx cmd = match cmd with
  | Eval(t) -> 
      let tyT = typeof ctx t in 
      let t' = eval ctx t in
      printValue ctx t'; 
      pr ": "; printType tyT;
      print "\n";
      ctx
  | Bind(x,bind) -> 
      print x; prbinding bind; pr "\n";
      addbinding ctx x bind
  
let process_channel f =
  let cmds,_ = parse_channel f emptycontext in
  let g ctx c =  
    let results = process_command ctx c in
    results
  in
    List.fold_left g emptycontext cmds

let rec process_REPL lexbuf ctx =
  print "> ";
  let result = 
    Parser.cmd Lexer.token lexbuf 
    (*with Parsing.Parse_error -> print "Parse Error! " ; raise Exit*)
  in
  let cmds,_ = result ctx in (* 这里注意用_，因为parse的时候加了一次Bind，否则会加两次 *)
  if cmds = [] then ctx
  else 
    let newctx = 
      let g ctx c = 
        let ctx' = process_command ctx c in 
        (print "\n"; flush stdout; ctx')
      in List.fold_left g ctx cmds
    in print "[Current context: "; printctx newctx; print "]\n"; process_REPL lexbuf newctx

exception NoInputFile

let main () = 
  if Array.length Sys.argv < 2 then
    let () = print "You must specify an input file or use the '-i' mode!\n" in
    raise Exit
  else if Sys.argv.(1) = "-i" then
    (let lexbuf = Lexing.from_channel stdin in process_REPL lexbuf emptycontext)
  else process_channel (open_in Sys.argv.(1))

let _ = main ()