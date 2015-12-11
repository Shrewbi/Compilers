local
type t__1__ = (int*int)
type t__2__ = (int*int)
type t__3__ = (bool*(int*int))
type t__4__ = (int*int)
type t__5__ = char*(int*int)
type t__6__ = (int*int)
type t__7__ = (int*int)
type t__8__ = (int*int)
type t__9__ = (int*int)
type t__10__ = (int*int)
type t__11__ = (int*int)
type t__12__ = (int*int)
type t__13__ = string*(int*int)
type t__14__ = (int*int)
type t__15__ = (int*int)
type t__16__ = (int*int)
type t__17__ = (int*int)
type t__18__ = (int*int)
type t__19__ = (int*int)
type t__20__ = (int*int)
type t__21__ = (int*int)
type t__22__ = (int*int)
type t__23__ = (int*int)
type t__24__ = (int*int)
type t__25__ = (int*int)
type t__26__ = (int*int)
type t__27__ = (int*int)
type t__28__ = int*(int*int)
type t__29__ = (int*int)
type t__30__ = (int*int)
type t__31__ = (int*int)
type t__32__ = (int*int)
type t__33__ = (int*int)
type t__34__ = (int*int)
type t__35__ = (int*int)
type t__36__ = string*(int*int)
type t__37__ = (int*int)
type t__38__ = (int*int)
in
datatype token =
    AND of t__1__
  | BOOL of t__2__
  | BOOLVAL of t__3__
  | CHAR of t__4__
  | CHARLIT of t__5__
  | COMMA of t__6__
  | DEQ of t__7__
  | DIV of t__8__
  | ELSE of t__9__
  | EOF of t__10__
  | EQ of t__11__
  | FUN of t__12__
  | ID of t__13__
  | IF of t__14__
  | IN of t__15__
  | INT of t__16__
  | IOTA of t__17__
  | LBRACKET of t__18__
  | LCURLY of t__19__
  | LET of t__20__
  | LPAR of t__21__
  | LTH of t__22__
  | MAP of t__23__
  | MINUS of t__24__
  | MULT of t__25__
  | NEGATE of t__26__
  | NOT of t__27__
  | NUM of t__28__
  | OR of t__29__
  | PLUS of t__30__
  | RBRACKET of t__31__
  | RCURLY of t__32__
  | READ of t__33__
  | REDUCE of t__34__
  | RPAR of t__35__
  | STRINGLIT of t__36__
  | THEN of t__37__
  | WRITE of t__38__
end;

open Obj Parsing;
prim_val vector_ : int -> 'a -> 'a Vector.vector = 2 "make_vect";
prim_val update_ : 'a Vector.vector -> int -> 'a -> unit = 3 "set_vect_item";


(* A parser definition for Fasto, for use with mosmlyac. *)

open Fasto
open Fasto.UnknownTypes

(* Line 12, file Parser.sml *)
val yytransl = #[
  257 (* AND *),
  258 (* BOOL *),
  259 (* BOOLVAL *),
  260 (* CHAR *),
  261 (* CHARLIT *),
  262 (* COMMA *),
  263 (* DEQ *),
  264 (* DIV *),
  265 (* ELSE *),
  266 (* EOF *),
  267 (* EQ *),
  268 (* FUN *),
  269 (* ID *),
  270 (* IF *),
  271 (* IN *),
  272 (* INT *),
  273 (* IOTA *),
  274 (* LBRACKET *),
  275 (* LCURLY *),
  276 (* LET *),
  277 (* LPAR *),
  278 (* LTH *),
  279 (* MAP *),
  280 (* MINUS *),
  281 (* MULT *),
  282 (* NEGATE *),
  283 (* NOT *),
  284 (* NUM *),
  285 (* OR *),
  286 (* PLUS *),
  287 (* RBRACKET *),
  288 (* RCURLY *),
  289 (* READ *),
  290 (* REDUCE *),
  291 (* RPAR *),
  292 (* STRINGLIT *),
  293 (* THEN *),
  294 (* WRITE *),
    0];

val yylhs = "\255\255\
\\001\000\002\000\002\000\003\000\003\000\004\000\004\000\004\000\
\\004\000\005\000\005\000\006\000\006\000\006\000\006\000\006\000\
\\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\\006\000\006\000\006\000\006\000\006\000\007\000\007\000\000\000";

val yylen = "\002\000\
\\002\000\003\000\002\000\007\000\006\000\001\000\001\000\001\000\
\\003\000\004\000\002\000\001\000\001\000\001\000\001\000\003\000\
\\003\000\003\000\003\000\003\000\006\000\004\000\003\000\004\000\
\\004\000\003\000\006\000\004\000\004\000\003\000\001\000\002\000";

val yydefred = "\000\000\
\\000\000\000\000\000\000\032\000\000\000\007\000\008\000\006\000\
\\000\000\000\000\000\000\001\000\000\000\002\000\000\000\009\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\013\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\012\000\000\000\
\\015\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\010\000\000\000\000\000\023\000\000\000\
\\000\000\000\000\000\000\016\000\000\000\026\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\028\000\022\000\000\000\029\000\
\\030\000\000\000\024\000\025\000\000\000\000\000\000\000\000\000";

val yydgoto = "\002\000\
\\004\000\005\000\010\000\019\000\020\000\042\000\043\000";

val yysindex = "\012\000\
\\013\255\000\000\017\255\000\000\021\255\000\000\000\000\000\000\
\\017\255\013\255\025\255\000\000\008\255\000\000\026\255\000\000\
\\006\255\031\255\030\255\015\255\058\255\042\255\043\255\000\000\
\\249\254\058\255\034\255\058\255\045\255\058\255\000\000\038\255\
\\000\000\040\255\243\255\017\255\058\255\058\255\032\255\096\255\
\\058\255\128\255\037\255\051\255\209\255\017\255\058\255\058\255\
\\058\255\058\255\058\255\000\000\243\255\223\255\000\000\029\255\
\\058\255\213\255\058\255\000\000\058\255\000\000\039\255\216\255\
\\238\254\238\254\000\000\000\000\000\000\000\000\171\255\000\000\
\\000\000\234\255\000\000\000\000\058\255\058\255\243\255\243\255";

val yyrindex = "\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\056\255\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\041\255\000\000\000\000\
\\075\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\248\254\000\000\000\000\000\000\000\000\000\000\
\\000\000\239\254\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\022\255\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\150\255\182\255\107\255\139\255\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\190\255\197\255";

val yygindex = "\000\000\
\\000\000\063\000\000\000\254\255\044\000\235\255\220\255";

val YYTABLESIZE = 273;
val yytable = "\035\000\
\\011\000\005\000\056\000\005\000\040\000\050\000\013\000\006\000\
\\045\000\007\000\038\000\051\000\001\000\039\000\031\000\053\000\
\\054\000\031\000\006\000\058\000\007\000\008\000\073\000\009\000\
\\003\000\064\000\065\000\066\000\067\000\068\000\012\000\004\000\
\\008\000\004\000\009\000\071\000\024\000\015\000\016\000\074\000\
\\018\000\021\000\022\000\063\000\025\000\026\000\017\000\036\000\
\\027\000\023\000\028\000\029\000\030\000\037\000\041\000\079\000\
\\080\000\044\000\046\000\031\000\047\000\061\000\024\000\070\000\
\\032\000\003\000\055\000\033\000\060\000\034\000\025\000\026\000\
\\014\000\075\000\027\000\011\000\028\000\029\000\030\000\052\000\
\\014\000\014\000\000\000\014\000\014\000\031\000\014\000\000\000\
\\000\000\014\000\032\000\000\000\000\000\033\000\000\000\034\000\
\\014\000\000\000\014\000\000\000\000\000\000\000\048\000\000\000\
\\014\000\014\000\014\000\000\000\000\000\014\000\000\000\014\000\
\\018\000\018\000\000\000\018\000\018\000\049\000\018\000\050\000\
\\000\000\018\000\000\000\000\000\000\000\051\000\000\000\000\000\
\\018\000\000\000\018\000\000\000\057\000\059\000\048\000\000\000\
\\018\000\018\000\018\000\000\000\000\000\018\000\000\000\018\000\
\\017\000\017\000\000\000\017\000\017\000\049\000\017\000\050\000\
\\000\000\017\000\000\000\019\000\019\000\051\000\019\000\019\000\
\\017\000\019\000\017\000\000\000\019\000\000\000\000\000\000\000\
\\017\000\017\000\017\000\019\000\000\000\017\000\000\000\017\000\
\\000\000\048\000\000\000\077\000\019\000\019\000\000\000\000\000\
\\019\000\000\000\019\000\020\000\020\000\000\000\020\000\020\000\
\\049\000\020\000\050\000\021\000\020\000\000\000\021\000\021\000\
\\051\000\021\000\027\000\020\000\021\000\027\000\027\000\000\000\
\\027\000\000\000\000\000\027\000\020\000\020\000\000\000\048\000\
\\020\000\000\000\020\000\048\000\021\000\021\000\048\000\000\000\
\\021\000\000\000\021\000\027\000\027\000\048\000\049\000\027\000\
\\050\000\027\000\049\000\000\000\050\000\049\000\051\000\050\000\
\\048\000\000\000\051\000\062\000\049\000\051\000\050\000\072\000\
\\078\000\048\000\076\000\000\000\051\000\069\000\000\000\049\000\
\\000\000\050\000\000\000\000\000\000\000\000\000\000\000\051\000\
\\049\000\000\000\050\000\000\000\000\000\000\000\000\000\000\000\
\\051\000";

val yycheck = "\021\000\
\\003\000\010\001\039\000\012\001\026\000\024\001\009\000\002\001\
\\030\000\004\001\018\001\030\001\001\000\021\001\032\001\037\000\
\\038\000\035\001\002\001\041\000\004\001\016\001\059\000\018\001\
\\012\001\047\000\048\000\049\000\050\000\051\000\010\001\010\001\
\\016\001\012\001\018\001\057\000\005\001\013\001\031\001\061\000\
\\035\001\011\001\013\001\046\000\013\001\014\001\021\001\006\001\
\\017\001\035\001\019\001\020\001\021\001\011\001\021\001\077\000\
\\078\000\013\001\021\001\028\001\021\001\011\001\005\001\035\001\
\\033\001\010\001\035\001\036\001\032\001\038\001\013\001\014\001\
\\010\000\035\001\017\001\035\001\019\001\020\001\021\001\036\000\
\\006\001\007\001\255\255\009\001\010\001\028\001\012\001\255\255\
\\255\255\015\001\033\001\255\255\255\255\036\001\255\255\038\001\
\\022\001\255\255\024\001\255\255\255\255\255\255\007\001\255\255\
\\030\001\031\001\032\001\255\255\255\255\035\001\255\255\037\001\
\\006\001\007\001\255\255\009\001\010\001\022\001\012\001\024\001\
\\255\255\015\001\255\255\255\255\255\255\030\001\255\255\255\255\
\\022\001\255\255\024\001\255\255\037\001\006\001\007\001\255\255\
\\030\001\031\001\032\001\255\255\255\255\035\001\255\255\037\001\
\\006\001\007\001\255\255\009\001\010\001\022\001\012\001\024\001\
\\255\255\015\001\255\255\006\001\007\001\030\001\009\001\010\001\
\\022\001\012\001\024\001\255\255\015\001\255\255\255\255\255\255\
\\030\001\031\001\032\001\022\001\255\255\035\001\255\255\037\001\
\\255\255\007\001\255\255\009\001\031\001\032\001\255\255\255\255\
\\035\001\255\255\037\001\006\001\007\001\255\255\009\001\010\001\
\\022\001\012\001\024\001\006\001\015\001\255\255\009\001\010\001\
\\030\001\012\001\006\001\022\001\015\001\009\001\010\001\255\255\
\\012\001\255\255\255\255\015\001\031\001\032\001\255\255\007\001\
\\035\001\255\255\037\001\007\001\031\001\032\001\007\001\255\255\
\\035\001\255\255\037\001\031\001\032\001\007\001\022\001\035\001\
\\024\001\037\001\022\001\255\255\024\001\022\001\030\001\024\001\
\\007\001\255\255\030\001\035\001\022\001\030\001\024\001\035\001\
\\015\001\007\001\035\001\255\255\030\001\031\001\255\255\022\001\
\\255\255\024\001\255\255\255\255\255\255\255\255\255\255\030\001\
\\022\001\255\255\024\001\255\255\255\255\255\255\255\255\255\255\
\\030\001";

val yyact = vector_ 33 (fn () => ((raise Fail "parser") : obj));
(* Rule 1, file Parser.grm, line 39 *)
val _ = update_ yyact 1
(fn () => repr(let
val d__1__ = peekVal 1 : Fasto.UnknownTypes.FunDec list
val d__2__ = peekVal 0 : (int*int)
in
( (d__1__) ) end : Fasto.UnknownTypes.Prog))
;
(* Rule 2, file Parser.grm, line 42 *)
val _ = update_ yyact 2
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.FunDec
val d__3__ = peekVal 0 : Fasto.UnknownTypes.FunDec list
in
( (d__2__) :: (d__3__) ) end : Fasto.UnknownTypes.FunDec list))
;
(* Rule 3, file Parser.grm, line 43 *)
val _ = update_ yyact 3
(fn () => repr(let
val d__1__ = peekVal 1 : (int*int)
val d__2__ = peekVal 0 : Fasto.UnknownTypes.FunDec
in
( (d__2__) :: [] ) end : Fasto.UnknownTypes.FunDec list))
;
(* Rule 4, file Parser.grm, line 47 *)
val _ = update_ yyact 4
(fn () => repr(let
val d__1__ = peekVal 6 : Fasto.Type
val d__2__ = peekVal 5 : string*(int*int)
val d__3__ = peekVal 4 : (int*int)
val d__4__ = peekVal 3 : Fasto.Param list
val d__5__ = peekVal 2 : (int*int)
val d__6__ = peekVal 1 : (int*int)
val d__7__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( FunDec (#1 (d__2__), (d__1__), (d__4__), (d__7__), #2 (d__2__)) ) end : Fasto.UnknownTypes.FunDec))
;
(* Rule 5, file Parser.grm, line 49 *)
val _ = update_ yyact 5
(fn () => repr(let
val d__1__ = peekVal 5 : Fasto.Type
val d__2__ = peekVal 4 : string*(int*int)
val d__3__ = peekVal 3 : (int*int)
val d__4__ = peekVal 2 : (int*int)
val d__5__ = peekVal 1 : (int*int)
val d__6__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( FunDec (#1 (d__2__), (d__1__), [], (d__6__), #2 (d__2__)) ) end : Fasto.UnknownTypes.FunDec))
;
(* Rule 6, file Parser.grm, line 52 *)
val _ = update_ yyact 6
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Int ) end : Fasto.Type))
;
(* Rule 7, file Parser.grm, line 53 *)
val _ = update_ yyact 7
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Bool ) end : Fasto.Type))
;
(* Rule 8, file Parser.grm, line 54 *)
val _ = update_ yyact 8
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Char ) end : Fasto.Type))
;
(* Rule 9, file Parser.grm, line 55 *)
val _ = update_ yyact 9
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.Type
val d__3__ = peekVal 0 : (int*int)
in
( Array (d__2__) ) end : Fasto.Type))
;
(* Rule 10, file Parser.grm, line 59 *)
val _ = update_ yyact 10
(fn () => repr(let
val d__1__ = peekVal 3 : Fasto.Type
val d__2__ = peekVal 2 : string*(int*int)
val d__3__ = peekVal 1 : (int*int)
val d__4__ = peekVal 0 : Fasto.Param list
in
( Param (#1 (d__2__), (d__1__)) :: (d__4__) ) end : Fasto.Param list))
;
(* Rule 11, file Parser.grm, line 60 *)
val _ = update_ yyact 11
(fn () => repr(let
val d__1__ = peekVal 1 : Fasto.Type
val d__2__ = peekVal 0 : string*(int*int)
in
( Param (#1 (d__2__), (d__1__)) :: [] ) end : Fasto.Param list))
;
(* Rule 12, file Parser.grm, line 63 *)
val _ = update_ yyact 12
(fn () => repr(let
val d__1__ = peekVal 0 : int*(int*int)
in
( Constant (IntVal (#1 (d__1__)), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 13, file Parser.grm, line 64 *)
val _ = update_ yyact 13
(fn () => repr(let
val d__1__ = peekVal 0 : char*(int*int)
in
( Constant (CharVal (#1 (d__1__)), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 14, file Parser.grm, line 65 *)
val _ = update_ yyact 14
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( Var (d__1__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 15, file Parser.grm, line 66 *)
val _ = update_ yyact 15
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( StringLit (d__1__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 16, file Parser.grm, line 68 *)
val _ = update_ yyact 16
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.Exp list
val d__3__ = peekVal 0 : (int*int)
in
( ArrayLit ((d__2__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 17, file Parser.grm, line 69 *)
val _ = update_ yyact 17
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Plus ((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 18, file Parser.grm, line 70 *)
val _ = update_ yyact 18
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Minus((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 19, file Parser.grm, line 71 *)
val _ = update_ yyact 19
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Equal((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 20, file Parser.grm, line 72 *)
val _ = update_ yyact 20
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Less ((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 21, file Parser.grm, line 74 *)
val _ = update_ yyact 21
(fn () => repr(let
val d__1__ = peekVal 5 : (int*int)
val d__2__ = peekVal 4 : Fasto.UnknownTypes.Exp
val d__3__ = peekVal 3 : (int*int)
val d__4__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__5__ = peekVal 1 : (int*int)
val d__6__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( If ((d__2__), (d__4__), (d__6__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 22, file Parser.grm, line 76 *)
val _ = update_ yyact 22
(fn () => repr(let
val d__1__ = peekVal 3 : string*(int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp list
val d__4__ = peekVal 0 : (int*int)
in
( Apply (#1 (d__1__), (d__3__), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 23, file Parser.grm, line 78 *)
val _ = update_ yyact 23
(fn () => repr(let
val d__1__ = peekVal 2 : string*(int*int)
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : (int*int)
in
( Apply (#1 (d__1__), [], #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 24, file Parser.grm, line 81 *)
val _ = update_ yyact 24
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.Type
val d__4__ = peekVal 0 : (int*int)
in
( Read ((d__3__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 25, file Parser.grm, line 83 *)
val _ = update_ yyact 25
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Write ((d__3__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 26, file Parser.grm, line 85 *)
val _ = update_ yyact 26
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__3__ = peekVal 0 : (int*int)
in
( (d__2__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 27, file Parser.grm, line 87 *)
val _ = update_ yyact 27
(fn () => repr(let
val d__1__ = peekVal 5 : (int*int)
val d__2__ = peekVal 4 : string*(int*int)
val d__3__ = peekVal 3 : (int*int)
val d__4__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__5__ = peekVal 1 : (int*int)
val d__6__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Let (Dec (#1 (d__2__), (d__4__), (d__3__)), (d__6__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 28, file Parser.grm, line 89 *)
val _ = update_ yyact 28
(fn () => repr(let
val d__1__ = peekVal 3 : string*(int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Index (#1 (d__1__), (d__3__), (), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 29, file Parser.grm, line 91 *)
val _ = update_ yyact 29
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Iota ((d__3__), (d__1__))) end : Fasto.UnknownTypes.Exp))
;
(* Rule 30, file Parser.grm, line 94 *)
val _ = update_ yyact 30
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp list
in
( (d__1__) :: (d__3__) ) end : Fasto.UnknownTypes.Exp list))
;
(* Rule 31, file Parser.grm, line 95 *)
val _ = update_ yyact 31
(fn () => repr(let
val d__1__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( (d__1__) :: [] ) end : Fasto.UnknownTypes.Exp list))
;
(* Entry Prog *)
val _ = update_ yyact 32 (fn () => raise yyexit (peekVal 0));
val yytables : parseTables =
  ( yyact,
    yytransl,
    yylhs,
    yylen,
    yydefred,
    yydgoto,
    yysindex,
    yyrindex,
    yygindex,
    YYTABLESIZE,
    yytable,
    yycheck );
fun Prog lexer lexbuf = yyparse yytables 1 lexer lexbuf;
