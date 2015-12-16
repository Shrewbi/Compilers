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
\\006\000\006\000\006\000\006\000\006\000\006\000\006\000\007\000\
\\007\000\000\000";

val yylen = "\002\000\
\\002\000\003\000\002\000\007\000\006\000\001\000\001\000\001\000\
\\003\000\004\000\002\000\001\000\001\000\001\000\001\000\003\000\
\\003\000\003\000\003\000\003\000\006\000\004\000\003\000\004\000\
\\004\000\003\000\006\000\004\000\004\000\006\000\008\000\003\000\
\\001\000\002\000";

val yydefred = "\000\000\
\\000\000\000\000\000\000\034\000\000\000\007\000\008\000\006\000\
\\000\000\000\000\000\000\001\000\000\000\002\000\000\000\009\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\013\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\012\000\
\\000\000\000\000\015\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\010\000\
\\000\000\000\000\023\000\000\000\000\000\000\000\000\000\016\000\
\\000\000\026\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\028\000\022\000\000\000\029\000\032\000\000\000\
\\000\000\024\000\000\000\025\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\030\000\000\000\000\000\031\000";

val yydgoto = "\002\000\
\\004\000\005\000\010\000\019\000\020\000\044\000\045\000";

val yysindex = "\019\000\
\\248\254\000\000\016\000\000\000\017\255\000\000\000\000\000\000\
\\016\000\248\254\015\255\000\000\004\255\000\000\021\255\000\000\
\\008\255\034\255\033\255\013\255\079\255\043\255\039\255\000\000\
\\249\254\079\255\030\255\079\255\041\255\079\255\035\255\000\000\
\\036\255\038\255\000\000\042\255\094\255\016\000\079\255\079\255\
\\053\255\255\254\079\255\031\255\020\255\057\255\233\255\028\255\
\\016\000\037\255\079\255\079\255\079\255\079\255\079\255\000\000\
\\094\255\073\255\000\000\040\255\079\255\237\255\079\255\000\000\
\\079\255\000\000\071\255\044\255\076\255\240\255\234\254\234\254\
\\000\000\000\000\000\000\000\000\195\255\000\000\000\000\152\255\
\\079\255\000\000\079\255\000\000\079\255\079\255\247\255\120\255\
\\094\255\094\255\000\000\079\255\003\000\000\000";

val yyrindex = "\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\075\255\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\048\255\000\000\000\000\
\\099\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\005\255\000\000\000\000\000\000\
\\000\000\000\000\000\000\237\254\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\029\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\174\255\206\255\
\\131\255\163\255\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\214\255\221\255\000\000\000\000\000\000\000\000";

val yygindex = "\000\000\
\\000\000\080\000\000\000\254\255\056\000\235\255\218\255";

val YYTABLESIZE = 294;
val yytable = "\037\000\
\\011\000\054\000\060\000\003\000\042\000\052\000\013\000\055\000\
\\047\000\006\000\040\000\007\000\033\000\041\000\005\000\033\000\
\\005\000\057\000\058\000\001\000\053\000\062\000\054\000\008\000\
\\079\000\009\000\012\000\015\000\055\000\070\000\071\000\072\000\
\\073\000\074\000\016\000\061\000\063\000\052\000\004\000\077\000\
\\004\000\017\000\018\000\080\000\021\000\022\000\068\000\023\000\
\\038\000\039\000\043\000\064\000\053\000\046\000\054\000\048\000\
\\049\000\024\000\050\000\087\000\055\000\088\000\051\000\089\000\
\\090\000\025\000\026\000\065\000\067\000\027\000\093\000\028\000\
\\029\000\030\000\076\000\031\000\081\000\069\000\082\000\052\000\
\\032\000\083\000\011\000\024\000\003\000\033\000\034\000\059\000\
\\035\000\014\000\036\000\025\000\026\000\056\000\053\000\027\000\
\\054\000\028\000\029\000\030\000\052\000\031\000\055\000\075\000\
\\014\000\014\000\032\000\014\000\014\000\000\000\014\000\033\000\
\\034\000\014\000\035\000\053\000\036\000\054\000\000\000\000\000\
\\014\000\000\000\014\000\055\000\000\000\092\000\052\000\000\000\
\\014\000\014\000\014\000\000\000\000\000\014\000\000\000\014\000\
\\018\000\018\000\000\000\018\000\018\000\053\000\018\000\054\000\
\\000\000\018\000\000\000\000\000\000\000\055\000\000\000\000\000\
\\018\000\000\000\018\000\000\000\000\000\000\000\052\000\000\000\
\\018\000\018\000\018\000\000\000\000\000\018\000\086\000\018\000\
\\017\000\017\000\000\000\017\000\017\000\053\000\017\000\054\000\
\\000\000\017\000\000\000\019\000\019\000\055\000\019\000\019\000\
\\017\000\019\000\017\000\000\000\019\000\000\000\000\000\000\000\
\\017\000\017\000\017\000\019\000\000\000\017\000\000\000\017\000\
\\000\000\052\000\000\000\085\000\019\000\019\000\000\000\000\000\
\\019\000\000\000\019\000\020\000\020\000\000\000\020\000\020\000\
\\053\000\020\000\054\000\021\000\020\000\000\000\021\000\021\000\
\\055\000\021\000\027\000\020\000\021\000\027\000\027\000\000\000\
\\027\000\000\000\000\000\027\000\020\000\020\000\000\000\052\000\
\\020\000\000\000\020\000\052\000\021\000\021\000\052\000\000\000\
\\021\000\000\000\021\000\027\000\027\000\052\000\053\000\027\000\
\\054\000\027\000\053\000\000\000\054\000\053\000\055\000\054\000\
\\000\000\052\000\055\000\066\000\053\000\055\000\054\000\078\000\
\\000\000\006\000\084\000\007\000\055\000\000\000\000\000\000\000\
\\053\000\091\000\054\000\000\000\000\000\000\000\000\000\008\000\
\\055\000\009\000\000\000\000\000\000\000\094\000";

val yycheck = "\021\000\
\\003\000\024\001\041\000\012\001\026\000\007\001\009\000\030\001\
\\030\000\002\001\018\001\004\001\032\001\021\001\010\001\035\001\
\\012\001\039\000\040\000\001\000\022\001\043\000\024\001\016\001\
\\063\000\018\001\010\001\013\001\030\001\051\000\052\000\053\000\
\\054\000\055\000\031\001\037\001\006\001\007\001\010\001\061\000\
\\012\001\021\001\035\001\065\000\011\001\013\001\049\000\035\001\
\\006\001\011\001\021\001\032\001\022\001\013\001\024\001\021\001\
\\021\001\005\001\021\001\081\000\030\001\083\000\021\001\085\000\
\\086\000\013\001\014\001\011\001\041\001\017\001\092\000\019\001\
\\020\001\021\001\035\001\023\001\006\001\041\001\035\001\007\001\
\\028\001\006\001\035\001\005\001\010\001\033\001\034\001\035\001\
\\036\001\010\000\038\001\013\001\014\001\038\000\022\001\017\001\
\\024\001\019\001\020\001\021\001\007\001\023\001\030\001\031\001\
\\006\001\007\001\028\001\009\001\010\001\255\255\012\001\033\001\
\\034\001\015\001\036\001\022\001\038\001\024\001\255\255\255\255\
\\022\001\255\255\024\001\030\001\255\255\006\001\007\001\255\255\
\\030\001\031\001\032\001\255\255\255\255\035\001\255\255\037\001\
\\006\001\007\001\255\255\009\001\010\001\022\001\012\001\024\001\
\\255\255\015\001\255\255\255\255\255\255\030\001\255\255\255\255\
\\022\001\255\255\024\001\255\255\255\255\255\255\007\001\255\255\
\\030\001\031\001\032\001\255\255\255\255\035\001\015\001\037\001\
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
\\255\255\007\001\030\001\035\001\022\001\030\001\024\001\035\001\
\\255\255\002\001\035\001\004\001\030\001\255\255\255\255\255\255\
\\022\001\035\001\024\001\255\255\255\255\255\255\255\255\016\001\
\\030\001\018\001\255\255\255\255\255\255\035\001";

val yyact = vector_ 35 (fn () => ((raise Fail "parser") : obj));
(* Rule 1, file Parser.grm, line 40 *)
val _ = update_ yyact 1
(fn () => repr(let
val d__1__ = peekVal 1 : Fasto.UnknownTypes.FunDec list
val d__2__ = peekVal 0 : (int*int)
in
( (d__1__) ) end : Fasto.UnknownTypes.Prog))
;
(* Rule 2, file Parser.grm, line 43 *)
val _ = update_ yyact 2
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.FunDec
val d__3__ = peekVal 0 : Fasto.UnknownTypes.FunDec list
in
( (d__2__) :: (d__3__) ) end : Fasto.UnknownTypes.FunDec list))
;
(* Rule 3, file Parser.grm, line 44 *)
val _ = update_ yyact 3
(fn () => repr(let
val d__1__ = peekVal 1 : (int*int)
val d__2__ = peekVal 0 : Fasto.UnknownTypes.FunDec
in
( (d__2__) :: [] ) end : Fasto.UnknownTypes.FunDec list))
;
(* Rule 4, file Parser.grm, line 48 *)
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
(* Rule 5, file Parser.grm, line 50 *)
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
(* Rule 6, file Parser.grm, line 53 *)
val _ = update_ yyact 6
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Int ) end : Fasto.Type))
;
(* Rule 7, file Parser.grm, line 54 *)
val _ = update_ yyact 7
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Bool ) end : Fasto.Type))
;
(* Rule 8, file Parser.grm, line 55 *)
val _ = update_ yyact 8
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Char ) end : Fasto.Type))
;
(* Rule 9, file Parser.grm, line 56 *)
val _ = update_ yyact 9
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.Type
val d__3__ = peekVal 0 : (int*int)
in
( Array (d__2__) ) end : Fasto.Type))
;
(* Rule 10, file Parser.grm, line 60 *)
val _ = update_ yyact 10
(fn () => repr(let
val d__1__ = peekVal 3 : Fasto.Type
val d__2__ = peekVal 2 : string*(int*int)
val d__3__ = peekVal 1 : (int*int)
val d__4__ = peekVal 0 : Fasto.Param list
in
( Param (#1 (d__2__), (d__1__)) :: (d__4__) ) end : Fasto.Param list))
;
(* Rule 11, file Parser.grm, line 61 *)
val _ = update_ yyact 11
(fn () => repr(let
val d__1__ = peekVal 1 : Fasto.Type
val d__2__ = peekVal 0 : string*(int*int)
in
( Param (#1 (d__2__), (d__1__)) :: [] ) end : Fasto.Param list))
;
(* Rule 12, file Parser.grm, line 64 *)
val _ = update_ yyact 12
(fn () => repr(let
val d__1__ = peekVal 0 : int*(int*int)
in
( Constant (IntVal (#1 (d__1__)), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 13, file Parser.grm, line 65 *)
val _ = update_ yyact 13
(fn () => repr(let
val d__1__ = peekVal 0 : char*(int*int)
in
( Constant (CharVal (#1 (d__1__)), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 14, file Parser.grm, line 66 *)
val _ = update_ yyact 14
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( Var (d__1__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 15, file Parser.grm, line 67 *)
val _ = update_ yyact 15
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( StringLit (d__1__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 16, file Parser.grm, line 69 *)
val _ = update_ yyact 16
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.Exp list
val d__3__ = peekVal 0 : (int*int)
in
( ArrayLit ((d__2__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 17, file Parser.grm, line 70 *)
val _ = update_ yyact 17
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Plus ((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 18, file Parser.grm, line 71 *)
val _ = update_ yyact 18
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Minus((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 19, file Parser.grm, line 72 *)
val _ = update_ yyact 19
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Equal((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 20, file Parser.grm, line 73 *)
val _ = update_ yyact 20
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Less ((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 21, file Parser.grm, line 75 *)
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
(* Rule 22, file Parser.grm, line 77 *)
val _ = update_ yyact 22
(fn () => repr(let
val d__1__ = peekVal 3 : string*(int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp list
val d__4__ = peekVal 0 : (int*int)
in
( Apply (#1 (d__1__), (d__3__), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 23, file Parser.grm, line 79 *)
val _ = update_ yyact 23
(fn () => repr(let
val d__1__ = peekVal 2 : string*(int*int)
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : (int*int)
in
( Apply (#1 (d__1__), [], #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 24, file Parser.grm, line 82 *)
val _ = update_ yyact 24
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.Type
val d__4__ = peekVal 0 : (int*int)
in
( Read ((d__3__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 25, file Parser.grm, line 84 *)
val _ = update_ yyact 25
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Write ((d__3__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 26, file Parser.grm, line 86 *)
val _ = update_ yyact 26
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__3__ = peekVal 0 : (int*int)
in
( (d__2__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 27, file Parser.grm, line 88 *)
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
(* Rule 28, file Parser.grm, line 90 *)
val _ = update_ yyact 28
(fn () => repr(let
val d__1__ = peekVal 3 : string*(int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Index (#1 (d__1__), (d__3__), (), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 29, file Parser.grm, line 92 *)
val _ = update_ yyact 29
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Iota ((d__3__), (d__1__))) end : Fasto.UnknownTypes.Exp))
;
(* Rule 30, file Parser.grm, line 95 *)
val _ = update_ yyact 30
(fn () => repr(let
val d__1__ = peekVal 5 : (int*int)
val d__2__ = peekVal 4 : (int*int)
val d__3__ = peekVal 3 : Fasto.UnknownTypes.FunArg
val d__4__ = peekVal 2 : (int*int)
val d__5__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__6__ = peekVal 0 : (int*int)
in
( Map ((d__3__), (d__5__), (), (),  (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 31, file Parser.grm, line 98 *)
val _ = update_ yyact 31
(fn () => repr(let
val d__1__ = peekVal 7 : (int*int)
val d__2__ = peekVal 6 : (int*int)
val d__3__ = peekVal 5 : Fasto.UnknownTypes.FunArg
val d__4__ = peekVal 4 : (int*int)
val d__5__ = peekVal 3 : Fasto.UnknownTypes.Exp
val d__6__ = peekVal 2 : (int*int)
val d__7__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__8__ = peekVal 0 : (int*int)
in
( Reduce ((d__3__), (d__5__), (d__7__), (), (d__1__))) end : Fasto.UnknownTypes.Exp))
;
(* Rule 32, file Parser.grm, line 101 *)
val _ = update_ yyact 32
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp list
in
( (d__1__) :: (d__3__) ) end : Fasto.UnknownTypes.Exp list))
;
(* Rule 33, file Parser.grm, line 102 *)
val _ = update_ yyact 33
(fn () => repr(let
val d__1__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( (d__1__) :: [] ) end : Fasto.UnknownTypes.Exp list))
;
(* Entry Prog *)
val _ = update_ yyact 34 (fn () => raise yyexit (peekVal 0));
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
