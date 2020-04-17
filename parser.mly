/*  
 *  Yacc grammar for the parser.  The files parser.mli and parser.ml
 *  are generated automatically from parser.mly.
 */

%{
open Syntax
%}

/* ---------------------------------------------------------------------- */
/* Preliminaries */

/* Keyword tokens */
%token LAMBDA
%token TRUE FALSE IF THEN ELSE
%token BOOL

/* Identifier and constant value tokens */
%token <string> UCID  /* uppercase-initial */
%token <string> LCID  /* lowercase/symbolic-initial */

/* Symbolic tokens */
%token ARROW
%token COLON
%token DOT
%token EOF
%token LPAREN
%token RPAREN
%token USCORE
%token SEMI
%token SLASH

/* ---------------------------------------------------------------------- */

%start toplevel, cmd
%type < Syntax.context -> (Syntax.command list * Syntax.context) > toplevel, cmd

%%

/* ---------------------------------------------------------------------- */
/* Main body of the parser definition */

cmd :
    EOF { fun ctx -> [],ctx } /* just the end of the input, do nothing */
  | Command SEMI cmd 
        { fun ctx ->
          let cmd,ctx = $1 ctx in
          let cmds,ctx = $3 ctx in
          cmd::cmds,ctx }
  | Command SEMI SEMI 
        { fun ctx ->
          let cmd,ctx = $1 ctx in
          cmd::[],ctx } /* return when encountered ;; */

/* The top level of a file is a sequence of commands, each terminated
   by a semicolon. */
toplevel :
    EOF
      { fun ctx -> [],ctx }
  | Command SEMI toplevel
      { fun ctx ->
          let cmd,ctx = $1 ctx in
          let cmds,ctx = $3 ctx in
          cmd::cmds,ctx }

/* A top-level command */
Command :
  | Term 
      { fun ctx -> (let t = $1 ctx in Eval(t)),ctx }
  | LCID Binder
      { fun ctx -> (Bind($1, $2 ctx)), addname ctx $1 }
    /* 这里处理的是全局的VarBind 
       但是生成term时只加了一个NameBind，因为这时候并不做type checking，只要De Bruijin能进行就行 */
    /* Parsing的时候用了NameBind来转De Bruijin表示法 
       但是后面typeof的过程用了VarBind，index和NameBind是一样哒
       eval的过程直接丢掉了type，还是NameBind，就是De Bruijin表示法 */

Binder :
    COLON Type
      { fun ctx -> VarBind ($2 ctx) }

Type :
    ArrType
      { $1 }

ArrType :
    AType
      { $1 }
  | AType ARROW AType
      { fun ctx -> TyArr ($1 ctx, $3 ctx) }

AType :
    LPAREN Type RPAREN
      { $2 }
  | BOOL 
      { fun ctx -> TyBool }

Term :
    AppTerm
      { $1 }
  | LAMBDA LCID COLON Type DOT Term 
      { fun ctx ->
          let ctx' = addname ctx $2 in
          TmAbs($2, $4 ctx, $6 ctx') }
  | LAMBDA USCORE COLON Type DOT Term 
      { fun ctx ->
          let ctx' = addname ctx "_" in
          TmAbs("_", $4 ctx, $6 ctx') }
  | IF Term THEN Term ELSE Term
      { fun ctx -> TmIf($2 ctx, $4 ctx, $6 ctx) }

AppTerm :
    ATerm
      { $1 }
  | AppTerm ATerm
      { fun ctx -> TmApp($1 ctx, $2 ctx) }

ATerm :
    LPAREN Term RPAREN  
      { $2 } 
  | LCID 
      { fun ctx -> TmVar(name2index ctx $1, ctxlength ctx) }    
  | TRUE
      { fun ctx -> TmTrue }
  | FALSE 
      { fun ctx -> TmFalse }


/*   */
