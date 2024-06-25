(* This is the grammar for PDDL. The grammar spec by Kovacs is roughly followed, but 
  simplifications are made, where they lead to nicer code (by my judgement). *)


(* Some utility functions. *)
fun println x = print (x ^ "\n")

fun exit_fail msg = (
  println msg;
  OS.Process.exit(OS.Process.failure)
)

fun flatl3 ((a, b), c) = (a, b, c)
fun flat43 (a, (b, c, d)) = (a, b, c, d)
fun flat42 (a, b, (c, d)) = (a, b, c, d)
fun flat535 (a, (b, c, d), e) = (a, b, c, d, e)

fun invflat3 (a, b, c) = (a, (b, c))

structure PDDL =
(* An implementation that uses token parser. *)
struct

  open ParserCombinators
  open CharParser
  open PDDL_Checker_Exported

  infixr 4 << >>
  infixr 3 &&
  infix  2 -- ##
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  val requirementKeywords = 
    [":strips", ":equality", ":typing", ":action-costs", 
      ":negative-preconditions", ":disjunctive-preconditions", 
      ":existential-preconditions", ":universal-preconditions", ":quantified-preconditions",
      ":adl", ":numeric-fluents", ":object-fluents", ":action-costs"]
  
  structure PDDLDef :> LANGUAGE_DEF =
  struct

    type scanner = SubstringMonoStreamable.elem CharParser.charParser
    val commentStart   = NONE
    val commentEnd     = NONE
    val commentLine    = SOME ";"
    val nestedComments = false

    val identLetter    = alphaNum <|> oneOf (String.explode "_-") 
      (*Idents can be separated with " " or \n and can contain [Aa-Zz], [0-9], "-", "_"*)

    (* identStart is the first letter of any name. We rely on parcom being correct. *)
    val identStart     = letter (* <|> oneOf (String.explode "?") *)
      (* Variables start with "?", other things start with *)
    val opLetter      = letter <|> oneOf (String.explode "-/+*=><.")
    val opStart       = opLetter <|> oneOf (String.explode ":")

    val reservedOpNames = requirementKeywords @ 
      ["define", "domain", ":requirements", ":predicates", ":functions",
        ":types", ":constants", ":action", ":durative-action", ":parameters", ":precondition", ":effect", 
        ":invariant", ":name", ":vars", ":set-constraint",
        "problem", ":domain", ":init", ":objects", ":goal", ":metric", "maximize", "minimize",              
        "=", "+", "-", "/", "*", "<", ">", "<=", ">=", ".", "and", "or", "imply", "not", "forall", "exists", "when",
        "either", "assign", "scale-up", "scale-down", "increase", "decrease", 
        "at", "start", "end", "always", "sometime", "within", "at-most-once", "sometime-after", "sometime-before",
        "always-within", "hold-during", "hold-after", "is-violated"
        ]
    val reservedNames = reservedOpNames @ ["number", "undefined", "total-cost", "object", "?duration", "#t"]
    
    val caseSensitive  = false

  end
  (* From parcom.tokparse. Not included in the exported signature. *)
  val lineComment   =
  let fun comLine _  = newLine <|> done #"\n" <|> (anyChar >> $ comLine)
  in case PDDLDef.commentLine of
         SOME s => string s >> $ comLine return ()
       | NONE   => fail "Single-line comments not supported"
  end
  val mlComment      =
  case (PDDLDef.commentStart, PDDLDef.commentEnd) of
      (SOME st, SOME ed) =>
      let
    fun bcNest _   = try (string st) >> $contNest
    and contNest _ = try (string ed return ())
                                 <|> ($bcNest <|> (anyChar return ())) >> $contNest
    val bcU = try (string st) >> repeat (not (string ed) >> anyChar) >> string ed return ()
      in if PDDLDef.nestedComments then $ bcNest else bcU
      end
    | _ => fail "Multi-line comments not supported"
  val comment        = lineComment <|> mlComment

  type 'a pddl_parser = ('a, SubstringMonoStreamable.elem) parser

  datatype PDDL_OBJ_CONS = PDDL_OBJ_CONS of string   (* Object or constant, identified by name *)
  fun pddl_obj_name (PDDL_OBJ_CONS n) = n

  datatype PDDL_VAR = PDDL_VAR of string
  fun pddl_var_name (PDDL_VAR n) = n

  datatype PDDL_PRIM_TYPE = PDDL_PRIM_TYPE of string
  fun pddl_prim_type_name (PDDL_PRIM_TYPE n) = n

  type PDDL_TYPE = PDDL_PRIM_TYPE list

  datatype PDDL_FUN_TYPE = 
    Obj_Type of PDDL_TYPE
  | Num_Type

  type PDDL_PREDICATE_NAME = string

  type PDDL_FUN = string

  (* Parsed types in the domain *)

  (* Constants and types *)

  type 'a PDDL_TYPED_LIST = (('a list) * PDDL_TYPE) list

  type PDDL_TYPES_DEF = (PDDL_PRIM_TYPE PDDL_TYPED_LIST)

  type PDDL_CONSTS_DEF = (PDDL_OBJ_CONS PDDL_TYPED_LIST)


  (* Predicates *)
  type ATOMIC_FORM_SKEL = PDDL_PREDICATE_NAME * (PDDL_VAR PDDL_TYPED_LIST)

  type PDDL_PREDS_DEF = ATOMIC_FORM_SKEL list

  datatype PDDL_TERM =   
    VAR_TERM of PDDL_VAR
  | FUN_TERM of (string * PDDL_TERM list)
  
  (* Functions *)
  type 'a FUN_TYPED_LIST = (('a list) * PDDL_FUN_TYPE) list

  type ATOMIC_FUN_SKELETON = string * (PDDL_VAR PDDL_TYPED_LIST)

  type PDDL_FUNS_DEF = ATOMIC_FUN_SKELETON FUN_TYPED_LIST (* good *)

  (* other things *)

  type F_HEAD = (PDDL_FUN * PDDL_TERM list)

  type RAT = string * string option

  (* F_Head is a term with a well-formedness condition, because assignment updates are ambiguous. *)

  datatype PDDL_F_EXP = 
    PDDL_Num of RAT
  | F_Head of PDDL_TERM 
  | PDDL_Minus of (PDDL_F_EXP * PDDL_F_EXP)
  | PDDL_Div of (PDDL_F_EXP * PDDL_F_EXP)
  | PDDL_Neg of PDDL_F_EXP
  | PDDL_Times of PDDL_F_EXP list
  | PDDL_Plus of PDDL_F_EXP list

  (* Equality is an ambiguous comparison, when no numbers or arithmetic operations are 
      involved *)
  datatype PDDL_TERM_ATOM = 
    PDDL_Pred of (string * PDDL_TERM list)
  | PDDL_Eq of (PDDL_F_EXP * PDDL_F_EXP) 
  | PDDL_Num_Gt of (PDDL_F_EXP * PDDL_F_EXP)
  | PDDL_Num_Lt of (PDDL_F_EXP * PDDL_F_EXP)
  | PDDL_Num_Le of (PDDL_F_EXP * PDDL_F_EXP)
  | PDDL_Num_Ge of (PDDL_F_EXP * PDDL_F_EXP)

  datatype PDDL_OBJ_ATOM =
    PDDL_Obj_Pred of string * PDDL_OBJ_CONS list
  | PDDL_Obj_Eq of PDDL_OBJ_CONS * PDDL_OBJ_CONS

  type PDDL_PREF_NAME = string


  (* This type needs preferences *)
  datatype PDDL_FORM =
    PDDL_Form_Atom of PDDL_TERM_ATOM
  | PDDL_Not of PDDL_FORM
  | PDDL_And of PDDL_FORM list
  | PDDL_Or of PDDL_FORM list
  | PDDL_Imply of PDDL_FORM * PDDL_FORM
  | PDDL_All of PDDL_VAR PDDL_TYPED_LIST * PDDL_FORM
  | PDDL_Exists of PDDL_VAR PDDL_TYPED_LIST * PDDL_FORM
  | PDDL_Pref of PDDL_PREF_NAME * PDDL_FORM

  datatype PDDL_EFFECT = 
    PDDL_Add of PDDL_TERM_ATOM
  | PDDL_Del of PDDL_TERM_ATOM
  | PDDL_Unassign of F_HEAD
  | PDDL_Assign of (F_HEAD * PDDL_F_EXP) 
  | PDDL_EFF_ScaleUp of (F_HEAD * PDDL_F_EXP)
  | PDDL_EFF_ScaleDown of (F_HEAD * PDDL_F_EXP)
  | PDDL_EFF_Increase of (F_HEAD * PDDL_F_EXP)
  | PDDL_EFF_Decrease of (F_HEAD * PDDL_F_EXP)
  | PDDL_EFF_And of PDDL_EFFECT list
  | PDDL_EFF_Cond of (PDDL_FORM * PDDL_EFFECT)
  | PDDL_EFF_All of PDDL_VAR PDDL_TYPED_LIST * PDDL_EFFECT
  
  datatype PDDL_SIMPLE_DURATION_CONSTRAINT =
    PDDL_DUR_Eq of PDDL_F_EXP
  | PDDL_DUR_Le of PDDL_F_EXP
  | PDDL_DUR_Ge of PDDL_F_EXP
  | PDDL_DUR_At_Start of PDDL_SIMPLE_DURATION_CONSTRAINT
  | PDDL_DUR_At_End of PDDL_SIMPLE_DURATION_CONSTRAINT

  datatype PDDL_DURATION_CONSTRAINT = 
    PDDL_DUR_CON_And of PDDL_DURATION_CONSTRAINT list
  | PDDL_Simple_Duration_Constraint of PDDL_SIMPLE_DURATION_CONSTRAINT

  datatype PDDL_TIMED_GD = 
    PDDL_Over_All of PDDL_FORM
  | PDDL_At_Start of PDDL_FORM 
  | PDDL_At_End of PDDL_FORM

  datatype PDDL_DA_GD =
    PDDL_Timed_Gd of PDDL_TIMED_GD
  | PDDL_Temp_All of PDDL_VAR PDDL_TYPED_LIST * PDDL_DA_GD
  | PDDL_Temp_And of PDDL_DA_GD list
  | PDDL_Temp_Pref of PDDL_PREF_NAME * PDDL_TIMED_GD

  datatype PDDL_F_EXP_T = 
    PDDL_Time
  | PDDL_Time_Mult of PDDL_F_EXP

  datatype PDDL_F_EXP_DA =
    PDDL_DA_Minus of PDDL_F_EXP_DA * PDDL_F_EXP_DA
  | PDDL_DA_Div of PDDL_F_EXP_DA * PDDL_F_EXP_DA
  | PDDL_DA_Plus of PDDL_F_EXP_DA list
  | PDDL_DA_Times of PDDL_F_EXP_DA list
  | PDDL_DA_Neg of PDDL_F_EXP_DA
  | PDDL_DA_Dur
  | PDDL_F_Exp of PDDL_F_EXP


  datatype PDDL_F_ASSIGN_DA =
    PDDL_F_Assign_ScaleUp of F_HEAD * PDDL_F_EXP_DA
  | PDDL_F_Assign_ScaleDown of F_HEAD * PDDL_F_EXP_DA
  | PDDL_F_Assign_Increase of F_HEAD * PDDL_F_EXP_DA
  | PDDL_F_Assign_Decrease of F_HEAD * PDDL_F_EXP_DA
  | PDDL_F_Assign_Assign of F_HEAD * PDDL_F_EXP_DA

  datatype PDDL_TIMED_EFFECT =
    PDDL_Dur_Eff_At_Start of PDDL_F_ASSIGN_DA
  | PDDL_Dur_Eff_At_End of PDDL_F_ASSIGN_DA
  | PDDL_Eff_At_Start of PDDL_EFFECT
  | PDDL_Eff_At_End of PDDL_EFFECT
  | PDDL_Cont_Eff_Increase of F_HEAD * PDDL_F_EXP_T
  | PDDL_Cont_Eff_Decrease of F_HEAD * PDDL_F_EXP_T

  datatype PDDL_DA_EFFECT = 
    PDDL_Timed_Eff of PDDL_TIMED_EFFECT
  | PDDL_Da_Eff_And of PDDL_DA_EFFECT list
  | PDDL_Da_Eff_When of PDDL_DA_GD * PDDL_DA_EFFECT
  | PDDL_Da_Eff_All of PDDL_VAR PDDL_TYPED_LIST * PDDL_DA_EFFECT

  (* Actions *)
  type PDDL_PRE_GD = PDDL_FORM

  type PDDL_ACTION_DEF_BODY = (PDDL_PRE_GD option * PDDL_EFFECT option)
  type PDDL_DA_DEF_BODY = (PDDL_DURATION_CONSTRAINT option * PDDL_DA_GD option * PDDL_DA_EFFECT option)

  type PDDL_ACTION_SYMBOL = string

  datatype PDDL_STRUCTURE = 
      PDDL_ACTION of (PDDL_ACTION_SYMBOL * PDDL_VAR PDDL_TYPED_LIST * PDDL_ACTION_DEF_BODY)
    | PDDL_DURATIVE_ACTION of (PDDL_ACTION_SYMBOL * PDDL_VAR PDDL_TYPED_LIST * PDDL_DA_DEF_BODY)
    | PDDL_DERIVED of (PDDL_PREDICATE_NAME * PDDL_VAR PDDL_TYPED_LIST * PDDL_FORM)

  type PDDL_STRUCTURES_DEF = (PDDL_STRUCTURE list) (* good *)

  (* The actual domain *)
  type PDDL_DOMAIN = (
    PDDL_TYPES_DEF option * 
    PDDL_CONSTS_DEF option * 
    PDDL_PREDS_DEF option * 
    PDDL_FUNS_DEF option * 
    PDDL_STRUCTURES_DEF)


  (* Parsed types in the problem *)
  datatype PDDL_INIT =
    True_Pred of PDDL_OBJ_ATOM
  | False_Pred of PDDL_OBJ_ATOM
  | Init_Num_Func_Asmt of (PDDL_FUN * PDDL_OBJ_CONS list * RAT)
  | Init_Obj_Func_Asmt of (PDDL_FUN * PDDL_OBJ_CONS list * PDDL_OBJ_CONS)

  type PDDL_OBJ_DEF = PDDL_OBJ_CONS PDDL_TYPED_LIST

  type PDDL_GOAL = PDDL_FORM

  datatype PDDL_CON_GD =
    PDDL_Con_And of PDDL_CON_GD list
  | PDDL_Con_All of PDDL_VAR PDDL_TYPED_LIST * PDDL_CON_GD
  | PDDL_Con_At_End of PDDL_FORM
  | PDDL_Always of PDDL_CON_GD
  | PDDL_Sometime of PDDL_CON_GD
  | PDDL_Within of RAT * PDDL_CON_GD
  | PDDL_At_Most_Once of PDDL_CON_GD
  | PDDL_Sometime_After of PDDL_CON_GD * PDDL_CON_GD
  | PDDL_Sometime_Before of PDDL_CON_GD * PDDL_CON_GD
  | PDDL_Always_Within of RAT * PDDL_CON_GD * PDDL_CON_GD
  | PDDL_Hold_During of RAT * RAT * PDDL_CON_GD
  | PDDL_Hold_After of RAT * PDDL_CON_GD
  | PDDL_Con_Pref of PDDL_PREF_NAME * PDDL_CON_GD
  | PDDL_Gd of PDDL_FORM

  datatype PDDL_METRIC_F_EXP =
    PDDL_Metric_Times of PDDL_METRIC_F_EXP list
  | PDDL_Metric_Plus of PDDL_METRIC_F_EXP list
  | PDDL_Metric_Minus of PDDL_METRIC_F_EXP * PDDL_METRIC_F_EXP
  | PDDL_Metric_Div of PDDL_METRIC_F_EXP * PDDL_METRIC_F_EXP
  | PDDL_Metric_Neg of PDDL_METRIC_F_EXP
  | PDDL_Metric_Num of RAT
  | PDDL_Metric_Fun of PDDL_FUN * PDDL_OBJ_CONS list
  | PDDL_Metric_Is_Violated of PDDL_PREF_NAME

  datatype PDDL_OPT_OP = 
    Minimize
  | Maximize

  type PDDL_METRIC_SPEC = PDDL_OPT_OP * PDDL_METRIC_F_EXP

  type PDDL_PROBLEM = (
    PDDL_OBJ_DEF option *
    PDDL_INIT list *
    PDDL_GOAL *
    PDDL_CON_GD option *
    PDDL_METRIC_SPEC option
  )

  structure RTP = TokenParser (PDDLDef)
  open RTP

  fun pddl_reserved wrd = ((reservedOp wrd) return wrd) ?? "reserved word '" ^ wrd ^ "'"

  val lparen = (char #"(") ?? "lparen"
  val rparen = (char #")" ) ?? "rparen"

  val spaces_comm = repeatSkip (space wth (fn _ => ()) || comment)

  fun in_paren p = spaces_comm >> lparen >> spaces_comm >> p << spaces_comm << rparen << spaces_comm ?? "in_paren"

  (* identifier ensures that the parsed identifier is not a reserved word *)
  (* the rules above define what counts as an identifier in parcom *)
  val pddl_name = identifier ?? "pddl identifier" 

  val pref_name = pddl_name

  fun reserved_name name = ((reserved name) return name) ?? "reserved word '" ^ name ^ "'"

  val pddl_obj_cons = pddl_name wth PDDL_OBJ_CONS ?? "pddl object or constant"

  val require_key = 
    (foldr (fn (kw, p) => pddl_reserved kw || p) (fail "") requirementKeywords) ?? "require_key"

  val require_def = (in_paren(pddl_reserved ":requirements" >> repeat1 require_key)) ?? "require_def"

  val primitive_type = (pddl_name || reserved_name "object") 
        wth PDDL_PRIM_TYPE ?? "prim_type"

  val type_ = (in_paren (pddl_reserved "either" >> (repeat1 primitive_type))
               || (primitive_type wth (fn tp =>(tp::[])))) ?? "type"


  (* The default use of the object type should not be hardcoded here, I think. TODO *)
  fun typed_list x = repeat (((repeat1 x) && (pddl_reserved "-" >> type_))
                              || (repeat1 x) wth (fn tlist => (tlist, [PDDL_PRIM_TYPE "object"]))) ?? "typed_list"


  val types_def : PDDL_TYPES_DEF pddl_parser = 
    (in_paren (pddl_reserved ":types" >> typed_list primitive_type)) ?? "types def"

  val constants_def : PDDL_CONSTS_DEF pddl_parser =
    (in_paren (pddl_reserved ":constants" >> typed_list pddl_obj_cons)) ?? "consts def"

  val pddl_var = (((char #"?") >> pddl_name) wth (fn str => PDDL_VAR ("?" ^ str))) ?? "?var_name"

  val predicate = pddl_name ?? "predicate"

  fun optional_typed_list (x: 'a pddl_parser): ('a list * PDDL_PRIM_TYPE list) list pddl_parser = 
    (opt (typed_list x) wth 
      (fn parsed_typesOPT => 
        (case parsed_typesOPT of 
          (SOME parsed_types) => parsed_types
        | _ => [])))

  val atomic_formula_skeleton = (in_paren (predicate && optional_typed_list pddl_var)) ?? "predicate"

  val predicates_def: PDDL_PREDS_DEF pddl_parser = 
    (in_paren (pddl_reserved ":predicates" >> (repeat atomic_formula_skeleton))) ?? "predicates def"

  val function_type = (reserved_name "number") return Num_Type || type_ wth Obj_Type ?? "function type"

  (* no return type means number return type *)
  fun function_typed_list x =  repeat (((repeat1 x) && (pddl_reserved "-" >> function_type))
                                        || (repeat1 x) wth (fn tlist => (tlist, Num_Type))) ?? "function_typed_list"
  (* return types are applied to all preceding function declarations *)

  val function_symbol = (pddl_name || reserved_name "total-cost") ?? "function symbol"

  val atomic_function_skeleton = 
    (in_paren (function_symbol && optional_typed_list pddl_var)
      || function_symbol wth (fn x => (x, [])))  ?? "atomic function skeleton"

  val functions_def: PDDL_FUNS_DEF pddl_parser = 
    (in_paren(pddl_reserved ":functions" >>
         (function_typed_list atomic_function_skeleton)))?? "functions def"


  val term = fix (fn pddl_term => 
       pddl_var wth VAR_TERM
    || in_paren (function_symbol && repeat pddl_term) wth FUN_TERM
    || pddl_name wth (fn n => FUN_TERM (n, []))) ?? "term"

  (* parsing (postive) decimals as string *)
  val dec_num = ((lexeme ((char #"-" || digit) && (repeat digit) wth (fn (x,xs) => String.implode (x::xs))))
                && opt ((char #".") >> (digit && lexeme (repeat digit) wth (fn (x,xs) => String.implode (x::xs))))
                ) ?? "dec_num expression"

  val number = dec_num ?? "d value"

  val f_head = 
        in_paren(function_symbol && repeat1 term)
      || function_symbol wth (fn f => (f, [])) ?? "f_head"

  fun repeat2 p = p && repeat1 p wth op::

  val f_exp = fix (fn f => 
      dec_num wth PDDL_Num 
    || f_head wth F_Head o FUN_TERM
    || in_paren(pddl_reserved "-" >> f) wth PDDL_Neg
    || in_paren(pddl_reserved "-" >> f && f) wth PDDL_Minus
    || in_paren(pddl_reserved "/" >> f && f) wth PDDL_Div
    || in_paren(pddl_reserved "*" >> repeat2 f) wth PDDL_Times
    || in_paren(pddl_reserved "+" >> repeat2 f) wth PDDL_Plus
    ) ?? "f_exp"

  val f_comp : PDDL_TERM_ATOM pddl_parser = (
      (in_paren ((pddl_reserved "<") >> f_exp && f_exp)) wth PDDL_Num_Lt
    || (in_paren ((pddl_reserved "<=") >> f_exp && f_exp)) wth PDDL_Num_Le
    || (in_paren ((pddl_reserved "=") >> f_exp && f_exp)) wth PDDL_Eq 
    || (in_paren ((pddl_reserved ">") >> f_exp && f_exp)) wth PDDL_Num_Gt
    || (in_paren ((pddl_reserved ">=") >> f_exp && f_exp)) wth PDDL_Num_Ge
    ) ?? "f_comp"

  val atomic_formula_term = (
    (in_paren (predicate && repeat term) wth PDDL_Pred)
  || (in_paren ((pddl_reserved "=") >> term && term)) wth (fn (a, b) => PDDL_Eq (F_Head a, F_Head b))
  ) ?? "Atomic formula"

  val atomic_formula_obj = (
    (in_paren(predicate && repeat pddl_obj_cons) wth PDDL_Obj_Pred)
  || in_paren((pddl_reserved "=") >> pddl_obj_cons && pddl_obj_cons) wth PDDL_Obj_Eq) ?? "Atomic formula"

  val GD: PDDL_FORM pddl_parser = fix (fn f => 
      atomic_formula_term wth PDDL_Form_Atom 
      || f_comp wth PDDL_Form_Atom
      || in_paren(pddl_reserved "not" >> f) wth PDDL_Not
      || in_paren(pddl_reserved "and" >> repeat1 f) wth PDDL_And
      || in_paren(pddl_reserved "or" >> repeat1 f) wth PDDL_Or
      || in_paren(pddl_reserved "imply" >> f && f) wth PDDL_Imply
      || in_paren(pddl_reserved "forall" >> (in_paren(typed_list pddl_var) && f)) wth PDDL_All
      || in_paren(pddl_reserved "exists" >> (in_paren(typed_list pddl_var) && f)) wth PDDL_Exists
      ) ?? "GD"

  val pref_GD: PDDL_FORM pddl_parser = 
    in_paren(pddl_reserved "preference" >> pref_name && GD wth PDDL_Pref)
  || GD ?? "pref GD"
  
  val pre_GD =
    fix (fn f =>
      pref_GD
      || in_paren (pddl_reserved "and" >> repeat pref_GD wth PDDL_And)
      || in_paren (pddl_reserved "forall" >> in_paren (typed_list pddl_var) && f wth PDDL_All)  
    ) ?? "pre_GD" 


  val p_effect: PDDL_EFFECT pddl_parser =
      (atomic_formula_term wth PDDL_Add
      || (in_paren (pddl_reserved "not" >> atomic_formula_term) wth PDDL_Del)
      || (in_paren (pddl_reserved "assign" >> f_head << reserved_name "undefined") wth PDDL_Unassign)
      || (in_paren (pddl_reserved "assign" >> f_head && f_exp) wth PDDL_Assign) 
      || (in_paren (pddl_reserved "assign" >> f_head && term) wth (fn (h, t) => PDDL_Assign (h, F_Head t)))
      || (in_paren (pddl_reserved "scale-up" >> f_head && f_exp) wth PDDL_EFF_ScaleUp)
      || (in_paren (pddl_reserved "scale-down" >> f_head && f_exp) wth PDDL_EFF_ScaleDown)
      || (in_paren (pddl_reserved "increase" >> f_head && f_exp) wth PDDL_EFF_Increase)
      || (in_paren (pddl_reserved "decrease" >> f_head && f_exp) wth PDDL_EFF_Decrease)) ?? "p_effect"

  val cond_effect = (
      p_effect 
    || (in_paren (pddl_reserved "and" >> repeat1 p_effect)) wth PDDL_EFF_And
    )?? "cond_effect"

  val c_effect = 
    fix (fn c_eff => 
        cond_effect
      || in_paren (pddl_reserved "when" >> pre_GD && cond_effect) wth PDDL_EFF_Cond
      || in_paren (pddl_reserved "and" >> repeat1 c_eff) wth PDDL_EFF_And
      || in_paren (pddl_reserved "forall" >> (in_paren (typed_list pddl_var)) && c_eff) wth PDDL_EFF_All) ?? "c_effect"

  val effect = c_effect ?? "effect"
  
  fun emptyOR x = (x wth SOME || (char #"(" && char #")") return NONE )

  val action_def_body: PDDL_ACTION_DEF_BODY pddl_parser = 
    (pddl_reserved ":precondition" >> emptyOR pre_GD)
      && (pddl_reserved ":effect" >> emptyOR effect) ?? "action_def_body"

  val action_symbol: PDDL_ACTION_SYMBOL pddl_parser = pddl_name

  val da_symbol = pddl_name

  val action_def: PDDL_STRUCTURE pddl_parser = 
    (in_paren 
      (pddl_reserved ":action" >> action_symbol
        && (pddl_reserved ":parameters" >> (in_paren (optional_typed_list pddl_var)))
        && action_def_body)) wth PDDL_ACTION o flat3 ?? "action def"

  val d_value = f_exp

  val simple_duration_constraint: PDDL_SIMPLE_DURATION_CONSTRAINT pddl_parser =
    fix (fn sdc => (in_paren 
      (pddl_reserved "<=" >> pddl_reserved "?duration" >> d_value wth PDDL_DUR_Le)
    || (pddl_reserved ">=" >> pddl_reserved "?duration" >> d_value wth PDDL_DUR_Ge)
    || (pddl_reserved "=" >> pddl_reserved "?duration" >> d_value wth PDDL_DUR_Eq)
    || (pddl_reserved "at" >> pddl_reserved "start" >> sdc wth PDDL_DUR_At_Start)
    || (pddl_reserved "at" >> pddl_reserved "end" >> sdc wth PDDL_DUR_At_End)
    )) ?? "simple duration constraint"

  val duration_constraint: PDDL_DURATION_CONSTRAINT option pddl_parser = 
    (in_paren
      (pddl_reserved "and" >> simple_duration_constraint wth (SOME o PDDL_Simple_Duration_Constraint))
      || string "()" return NONE
      || simple_duration_constraint wth (SOME o PDDL_Simple_Duration_Constraint)
    ) ?? "duration constraint"

  val timed_GD: PDDL_TIMED_GD pddl_parser =
    (in_paren 
      (pddl_reserved "at" >> pddl_reserved "start" >> GD wth PDDL_At_Start
    || pddl_reserved "at" >> pddl_reserved "end" >> GD wth PDDL_At_End
    || pddl_reserved "over" >> pddl_reserved "all" >> GD wth PDDL_Over_All
    )) ?? "timed GD"

  val pref_timed_GD: PDDL_DA_GD pddl_parser = 
    (timed_GD wth PDDL_Timed_Gd
    || in_paren (pddl_reserved "preference" >> pref_name && timed_GD wth PDDL_Temp_Pref)  
    ) ?? "pref timed GD"

  val da_GD: PDDL_DA_GD pddl_parser = 
    fix (fn dgd => 
      pref_timed_GD
    || in_paren (pddl_reserved "and" >> repeat dgd wth PDDL_Temp_And)
    || in_paren (pddl_reserved "forall" >> in_paren (typed_list pddl_var) && dgd wth PDDL_Temp_All)
    ) ?? "da GD"
  
  val f_exp_t: PDDL_F_EXP_T pddl_parser =
    in_paren (pddl_reserved "*" >> pddl_reserved "#t" >> f_exp
    || pddl_reserved "#t" >> f_exp << pddl_reserved "*") wth PDDL_Time_Mult
    || pddl_reserved "#t" return PDDL_Time ?? "f exp t" 

  val f_exp_da: PDDL_F_EXP_DA pddl_parser = 
    fix (fn (f: PDDL_F_EXP_DA pddl_parser) => in_paren (
       pddl_reserved "-" >> f wth PDDL_DA_Neg
    || pddl_reserved "-" >> f && f wth PDDL_DA_Minus
    || pddl_reserved "/" >> f && f wth PDDL_DA_Div
    || pddl_reserved "*" >> repeat2 f wth PDDL_DA_Times
    || pddl_reserved "+" >> repeat2 f wth PDDL_DA_Plus
    || pddl_reserved "?duration" return PDDL_DA_Dur
    )) ?? "f exp da"

  val f_assign_da: PDDL_F_ASSIGN_DA pddl_parser =
    in_paren (pddl_reserved "=" >> f_head && f_exp_da wth PDDL_F_Assign_Assign)
  
  (* Conditional effects can also affect predicates and object fluents.
      The f_exp_t case is non_ambiguous. However, the f_exp_da case can
      be ambiguous with some of the cases in p_effect. It might be cleaner
      to combine them. This would then result in some wf-conditions which must
      be asserted in the .thy files. *)
  val timed_effect: PDDL_TIMED_EFFECT pddl_parser =
    in_paren (
      (pddl_reserved "at" >> pddl_reserved "start" >> (
        f_assign_da wth PDDL_Dur_Eff_At_Start
      || cond_effect wth PDDL_Eff_At_Start  
      ))
    || (pddl_reserved "at" >> pddl_reserved "end" >> (
        f_assign_da wth PDDL_Dur_Eff_At_End
      || cond_effect wth PDDL_Eff_At_End
      ))
    || (pddl_reserved "increase" >> f_head && f_exp_t wth PDDL_Cont_Eff_Increase)
    || (pddl_reserved "decrease" >> f_head && f_exp_t wth PDDL_Cont_Eff_Decrease) 
    ) ?? "timed effect"
  
  val da_effect: PDDL_DA_EFFECT pddl_parser = 
    fix (fn (da_eff: PDDL_DA_EFFECT pddl_parser) =>
      in_paren (pddl_reserved "and" >> repeat da_eff wth PDDL_Da_Eff_And)
    || in_paren (pddl_reserved "forall" >> typed_list pddl_var && da_eff wth PDDL_Da_Eff_All)
    || in_paren (pddl_reserved "when" >> da_GD && da_eff wth PDDL_Da_Eff_When)
    || timed_effect wth PDDL_Timed_Eff
    ) ?? "da effect"

  val da_def_body: PDDL_DA_DEF_BODY pddl_parser = 
      (pddl_reserved ":duration" >> duration_constraint
        && (pddl_reserved ":condition" >> emptyOR da_GD)
        && (pddl_reserved ":effect" >> emptyOR da_effect) wth flat3) ?? "da def"

  val durative_action_def: PDDL_STRUCTURE pddl_parser = 
    (in_paren (
      pddl_reserved ":durative-action" >> da_symbol
    && (pddl_reserved ":parameters" >> in_paren (optional_typed_list pddl_var))
    && da_def_body) wth PDDL_DURATIVE_ACTION o flat3) ?? "durative action def"

  val derived_def: PDDL_STRUCTURE pddl_parser =
    in_paren (
      pddl_reserved ":derived" >> atomic_formula_skeleton && GD wth PDDL_DERIVED o flatl3
    ) ?? "derived def"

  val structure_def = action_def || durative_action_def || derived_def ?? "struct def"

  val invariant_symbol = (pddl_reserved ":name" >> pddl_name) ?? "invariant symbol"

  val quantification = (pddl_reserved ":vars" >> in_paren(repeat pddl_var)) ?? "quantification"

  val constraints = (pddl_reserved ":set-constraint" >> pre_GD) ?? "constraint"

  val invariant_def = (in_paren(pddl_reserved ":invariant" >> spaces >>
                                 (invariant_symbol << spaces) &&
                                 (quantification << spaces) &&
                                 (constraints << spaces))) ?? "invariants def"

  val domain: PDDL_DOMAIN pddl_parser = 
    in_paren (pddl_reserved "define" 
      >> in_paren(pddl_reserved "domain" >> pddl_name)
      >> (opt require_def)
      >> (opt types_def)
      && (opt constants_def)
      && (opt predicates_def)
      && (opt functions_def)
      && (repeat structure_def)) wth flat5 ?? "domain"
      (*&& (repeat invariant_def)*)

  
  val object_declar = in_paren(pddl_reserved ":objects" >> (typed_list pddl_obj_cons))

  val basic_fun_term = (function_symbol wth (fn f => (f, []))
                    || in_paren(function_symbol && repeat pddl_obj_cons)
                    ) ?? "basic function term"


  (* We do not implement the literal parser. Instead, we distinguish the true and false cases explicitly *)
  val init_el: PDDL_INIT pddl_parser = (atomic_formula_obj wth True_Pred
                 || in_paren((pddl_reserved "not") >> atomic_formula_obj) wth False_Pred 
                 || in_paren((pddl_reserved "=") >> basic_fun_term && pddl_obj_cons)
                               wth (Init_Obj_Func_Asmt o flatl3)
                 || in_paren((pddl_reserved "=") >> basic_fun_term && dec_num)
                               wth (Init_Num_Func_Asmt o flatl3)) ?? "init element"

  val init = in_paren(pddl_reserved ":init" >> repeat init_el)


  (* The rule for goals is exactly as the one in Kovacs. It is wrong, nonetheless, since a goal
     should be only defined on GDs over objects or constants only and not terms 
     (symbols?, these used to be called terms) !! *)

  (* I think the above comment applies to STRIPS planning and not ADL planning, since we need symbols 
  for quantified goals. *)

  val goal = in_paren(pddl_reserved ":goal" >> pre_GD)

  val con_GD: PDDL_CON_GD pddl_parser = 
    fix (fn cGD => 
      in_paren (pddl_reserved "and" >> repeat cGD wth PDDL_Con_And)
    || in_paren (pddl_reserved "forall" >> typed_list pddl_var && cGD wth PDDL_Con_All)
    || in_paren (pddl_reserved "at end" >> GD wth PDDL_Con_At_End)
    || in_paren (pddl_reserved "always" >> cGD wth PDDL_Always)
    || in_paren (pddl_reserved "sometime" >> cGD wth PDDL_Sometime)
    || in_paren (pddl_reserved "within" >> dec_num && cGD wth PDDL_Within)
    || in_paren (pddl_reserved "at-most-once" >> cGD wth PDDL_At_Most_Once)
    || in_paren (pddl_reserved "sometime-after" >> cGD && cGD wth PDDL_Sometime_After)
    || in_paren (pddl_reserved "sometime-before" >> cGD && cGD wth PDDL_Sometime_Before)
    || in_paren (pddl_reserved "always-within" >> dec_num && cGD && cGD wth PDDL_Always_Within o flat3)
    || in_paren (pddl_reserved "hold-during" >> dec_num && dec_num && cGD wth PDDL_Hold_During o flat3)
    || in_paren (pddl_reserved "hold_after" >> dec_num && cGD wth PDDL_Hold_After)
    || GD wth PDDL_Gd
    ) ?? "con GD"

  val pref_con_GD: PDDL_CON_GD pddl_parser =
    fix (fn pcGD =>
      in_paren (pddl_reserved "and" >> repeat pcGD wth PDDL_Con_And)
    || in_paren (pddl_reserved "forall" >> typed_list pddl_var && pcGD wth PDDL_Con_All)
    || in_paren (pddl_reserved "preference" >> pref_name && con_GD wth PDDL_Con_Pref)
    || con_GD
    ) ?? "pref con GD"

  val constraints: PDDL_CON_GD pddl_parser =
    (pddl_reserved ":constraints" >> pref_con_GD) ?? "constraints"

  val metric_f_exp: PDDL_METRIC_F_EXP pddl_parser =
    fix (fn mfe =>
      in_paren (pddl_reserved "+" >> repeat mfe wth PDDL_Metric_Plus)
    || in_paren (pddl_reserved "*" >> repeat mfe wth PDDL_Metric_Times)
    || in_paren (pddl_reserved "-" >> mfe && mfe wth PDDL_Metric_Minus)
    || in_paren (pddl_reserved "/" >> mfe && mfe wth PDDL_Metric_Div)
    || in_paren (pddl_reserved "-" >> mfe wth PDDL_Metric_Neg)
    || dec_num wth PDDL_Metric_Num
    || in_paren (function_symbol && repeat pddl_obj_cons wth PDDL_Metric_Fun)
    || function_symbol wth (fn f => PDDL_Metric_Fun (f, []))
    || pddl_reserved "total-time" return PDDL_Metric_Fun ("total-time", [])
    || in_paren (pddl_reserved "is-violated" >> pref_name wth PDDL_Metric_Is_Violated)
    ) ?? "metric f exp"

  val optimisation: PDDL_OPT_OP pddl_parser = 
    (pddl_reserved "maximize" return Maximize
    || pddl_reserved "minimize" return Minimize) ?? "Optimisation"

  val metric_spec: PDDL_METRIC_SPEC pddl_parser = 
    in_paren(pddl_reserved ":metric" >> optimisation && metric_f_exp) ?? "metric spec"

  val problem: PDDL_PROBLEM pddl_parser = 
    in_paren (
      pddl_reserved "define" 
      >> in_paren(pddl_reserved "problem" >> pddl_name)
      >> in_paren(pddl_reserved ":domain" >> pddl_name)
      >> (opt require_def) 
      >> (opt object_declar)
      && init
      && goal
      && (opt constraints)
      && (opt metric_spec)) wth flat5 ?? "problem"

  val plan_action = in_paren(pddl_name && repeat pddl_obj_cons)
  val plan = repeat plan_action

end

open PDDL
  type METRIC = string option

  (*Types for the plan*)

  datatype PDDL_PLAN_ACTION = PDDL_PLAN_ACTION of string * (PDDL_OBJ_CONS list)
  fun pddl_plan_action_name (PDDL_PLAN_ACTION (name, args)) = name
  fun pddl_plan_action_args (PDDL_PLAN_ACTION (name, args)) = args


  (* Functions that are used to convert parsed types to Isabelle type and/or strings. They
     are common between both validating plans and invariants.*)

  fun stringToString s = "''" ^ s ^ "''"

  fun pddlVarToString (v:PDDL_VAR) = "Var " ^ stringToString (pddl_var_name v)

  fun pddlObjConsToString (oc:PDDL_OBJ_CONS) = "Obj " ^ stringToString (pddl_obj_name oc)

  fun pddlTypedListXTypesConv typedList cat_fn mk_pair_fn obj_v_conv_fun type_conv_fun =
    let
      fun wrap_var_with_type t = (fn v => mk_pair_fn (obj_v_conv_fun v) (type_conv_fun t))
    in
      cat_fn (map (fn (vars, type_) => (map (wrap_var_with_type type_) vars)) typedList)
    end



(*Some utility functions*)
(* 
fun fst (x,y) = x
fun snd (x,y) = y
fun pddl_prop_map f prop =
 case prop of PDDL_ATOM atm => PDDL_ATOM (map_atom f atm)
           | PDDL_Not sub_prop => PDDL_Not (pddl_prop_map f sub_prop)
           | PDDL_And props => PDDL_And (map (pddl_prop_map f) props)
           | PDDL_Or props => PDDL_Or (map (pddl_prop_map f) props)
           | Fluent => Fluent;

   *)