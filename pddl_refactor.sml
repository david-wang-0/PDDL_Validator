(* This is the grammar for PDDL. We tried to follow the grammar spec by Kovacs as closely as we could. *)


(* Some utility functions. *)
fun println x = print (x ^ "\n")

fun exit_fail msg = (
  println msg;
  OS.Process.exit(OS.Process.failure)
)

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

  structure PDDLDef :> LANGUAGE_DEF =
  struct

    type scanner = SubstringMonoStreamable.elem CharParser.charParser
    val commentStart   = NONE
    val commentEnd     = NONE
    val commentLine    = SOME ";"
    val nestedComments = false

    val identLetter    = alphaNum <|> oneOf (String.explode "_-,:;=") (*Idents can be separated with " " or \n and can contain [Aa-Zz], [0-9], "-", "_"*)
    val identStart     = identLetter
    val opStart        = fail "Operators not supported" : scanner
    val opLetter       = opStart

    val requirementKeywords = 
      [":requirements", ":strips", ":equality", ":typing", ":action-costs", 
        ":negative-preconditions", ":disjunctive-preconditions", 
        ":existential-preconditions", ":universal-preconditions", ":quantified-preconditions",
        ":adl", ":numeric-fluents", ":object-fluents", ":action-costs"]
    
    val reservedNames  = requirementKeywords @ ["define", "domain",
                          ":predicates", "either", ":functions",
                          ":types", (*"object",*)
                          ":constants",
                          ":action", ":parameters", ":precondition", ":effect", "-",
                          ":invariant", ":name", ":vars", ":set-constraint",
                          "=", "+", "-", "/", "*", "and", "or", "not", "forall", "exists", "number",
                          "assign", "scale-up", "scale-down", "increase", "decrease",
                          "problem", ":domain", ":init", ":objects", ":goal", ":metric", "maximize", "minimize",
                          "undefined", "total-cost"]
    val reservedOpNames= []
    val caseSensitive  = false

  end

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

  datatype PDDL_OBJ_CONS = PDDL_OBJ_CONS of string   (* Object or constant, identified by name *)
  fun pddl_obj_name (PDDL_OBJ_CONS n) = n

  datatype PDDL_VAR = PDDL_VAR of string
  fun pddl_var_name (PDDL_VAR n) = n

  datatype PDDL_PRIM_TYPE = 
    PDDL_Prim_Type of string
  | PDDL_Object_Type

  type PDDL_PRED = string

  type PDDL_FUN = string

  datatype PDDL_TERM = OBJ_CONS_TERM of PDDL_OBJ_CONS
                       | VAR_TERM of PDDL_VAR
                       | FUN_TERM of (PDDL_FUN * PDDL_TERM list)
  
  type RAT = string * string

  datatype PDDL_F_EXP = 
    Num of RAT
  | F_Head of (PDDL_FUN * PDDL_TERM list)
  | Sub of (PDDL_F_EXP * PDDL_F_EXP)
  | Div of (PDDL_F_EXP * PDDL_F_EXP)
  | Neg of PDDL_F_EXP
  | Mult of PDDL_F_EXP list
  | Add of PDDL_F_EXP list

  datatype PDDL_F_COMP = 
    PDDL_Lt of (PDDL_F_EXP * PDDL_F_EXP)
  | PDDL_Le of (PDDL_F_EXP * PDDL_F_EXP)
  | PDDL_Gt of (PDDL_F_EXP * PDDL_F_EXP)
  | PDDL_Ge of (PDDL_F_EXP * PDDL_F_EXP)

  datatype 't PDDL_ATOM = 
    PDDL_Pred of (string, 't list)
  | PDDL_Eq of ('t, 't)

  datatype PDDL_FORM =
    PDDL_Form_Atom of (PDDL_TERM PDDL_ATOM)
  | PDDL_Comp of PDDL_F_COMP
  | PDDL_Not of PDDL_FORM
  | PDDL_And of PDDL_FORM list
  | PDDL_Or of PDDL_FORM list
  | PDDL_All of (PDDL_VAR list * PDDL_PRIM_TYPE) list * PDDL_FORM
  | PDDL_Exists of (PDDL_VAR list * PDDL_PRIM_TYPE) list * PDDL_FORM;

  datatype PDDL_EFFECT = 
    Add of PDDL_ATOM
  | Del of PDDL_ATOM
  | Unassign of PDDL_TERM
  | Assign of (PDDL_TERM * PDDL_TERM)
  | N_Assign of (PDDL_F_EXP * PDDL_F_EXP) 
  | N_ScaleUp of (PDDL_F_EXP * PDDL_F_EXP)
  | N_ScaleDown of (PDDL_F_EXP * PDDL_F_EXP)
  | N_Increase of (PDDL_F_EXP * PDDL_F_EXP)
  | N_Decrease of (PDDL_F_EXP * PDDL_F_EXP)
  | EFF_And of PDDL_EFFECT list
  | EFF_Cond of (PDDL_FORM * PDDL_EFFECT)
  | EFF_All of (PDDL_VAR list * PDDL_PRIM_TYPE) list * PDDL_EFFECT

  (* To do: Check if the first parser in the alternative has higher precedence.
    If it does not, then the p_effect parser can be ambiguous for N_Assign.*)


  datatype PDDL_INIT =
    True_Pred of string PDDL_ATOM
  | False_Pred of string PDDL_ATOM
  | Init_Num_Func_Asmt of (PDDL_FUN * PDDL_OBJ_CONS list * RAT)
  | Init_Obj_Func_Asmt of (PDDL_FUN * PDDL_OBJ_CONS list * PDDL_OBJ_CONS)

  structure RTP = TokenParser (PDDLDef)
  open RTP

  val num = (lexeme ((char #"-" || digit) && (repeat digit)) when
        (fn (x,xs) => Int.fromString (String.implode (x::xs)))) ?? "num expression"

  val lparen = (char #"(" ) ?? "lparen"
  val rparen = (char #")" ) ?? "rparen"

  val spaces_comm = repeatSkip (space wth (fn _ => ())|| comment)

  fun in_paren p = spaces_comm >> lparen >> spaces_comm >> p << spaces_comm << rparen << spaces_comm

  (* identifier ensures that the parsed identifier is not a reserved word *)
  val pddl_name = identifier ?? "pddl identifier" (*First char should be a letter*)

  val pddl_obj_cons = pddl_name wth PDDL_OBJ_CONS ?? "pddl object or constant"

  fun pddl_reserved wrd = (reserved wrd) ?? "resereved word"

  val require_key = (foldr (fn kw p => pddl_reserved kw || p) (fail ()) requirementKeywords) ?? "require_key"

  val require_def = (in_paren(pddl_reserved ":requirements" >> repeat1 require_key)) ?? "require_def"

  val primitive_type = (pddl_name wth PDDL_PRIM_TYPE
                        || (pddl_reserved "object") >> success PDDL_Object_Type) ?? "prim_type"

  val type_ = (in_paren (pddl_reserved "either" >> (repeat1 primitive_type))
               || (primitive_type wth (fn tp => (tp::[])))) ?? "type"

  fun typed_list x = repeat (((repeat1 x) && (pddl_reserved "-" >> type_))
                              || (repeat1 x) wth (fn tlist => (tlist, [PDDL_PRIM_TYPE "object"]))) ?? "typed_list"

  val pddl_type = pddl_name wth PDDL_PRIM_TYPE ?? "pddl type"

  val types_def = (in_paren(pddl_reserved ":types" >> typed_list pddl_type)) ?? "types def"

  val constants_def = (in_paren(pddl_reserved ":constants" >> typed_list pddl_obj_cons)) ?? "consts def"

  val pddl_var = (((char #"?" ) && pddl_name) wth (fn (c, str) => PDDL_VAR (String.implode [c] ^ str))) ?? "?var_name"

  val predicate = pddl_name wth (fn name => PDDL_PRED name) ?? "predicate"

  fun optional_typed_list x = (opt (typed_list x)
                                wth (fn parsed_typesOPT => (case parsed_typesOPT of (SOME parsed_types) => parsed_types
                                                                                     | _ => [])))

  val atomic_formula_skeleton = (in_paren (predicate && optional_typed_list pddl_var)) ?? "predicate"

  val predicates_def = (in_paren(pddl_reserved ":predicates" >> (repeat (atomic_formula_skeleton)))) ?? "predicates def"

  val function_type = pddl_reserved "number" wth (fn _ => None) || pddl_type wth Some ?? "function type"

  fun function_typed_list x =  repeat1 (((repeat1 x) && (pddl_reserved "-" >> function_type))
                                        || (repeat1 x) wth (fn tlist => (tlist, None))) ?? "function_typed_list"
  (* return types are applied to all preceding function declarations *)

  val function_symbol = (pddl_name || pddl_reserved "total-cost") ?? "function symbol"

  val atomic_function_skeleton = (in_paren (function_symbol && optional_typed_list pddl_var))
                                 ?? "atomic function skeleton"
  (* every function declaration must be wrapped in parentheses -  *)

  (* WIP: parse numeric and object functions *)
  val functions_def = (in_paren(pddl_reserved ":functions" >>
                                (function_typed_list atomic_function_skeleton))) ?? "functions def"

  val term = (pddl_obj_cons wth (fn oc => OBJ_CONS_TERM oc) 
              || pddl_var wth (fn v => VAR_TERM v) 
              || in_paren (function_symbol && repeat1 pddl_term) wth FUN_TERM) ?? "term"

  (* parsing (postive) decimals as string *)
  val dec_num = ((lexeme ((char #"-" || digit) && (repeat digit) wth (fn (x,xs) => String.implode (x::xs))))
                && opt ((char #".") >> (digit && lexeme (repeat digit) wth (fn (x,xs) => String.implode (x::xs))))
                ) ?? "dec_num expression"

  val number = dec_num ?? "d value"

  val f_head = (in_paren(function_symbol && repeat term)
                || function_symbol wth (fn s => (s, []))) wth F_Head ?? "f_headhead"

  fun repeat2 p = p && p && repeat p wth op::

  val f_exp = fix (fn f => dec_num wth Num 
              || f_head wth F_Head
              || in_paren(pddl_reserved "-" >> f) wth Neg
              || in_paren(pddl_reserved "-" >> f && f) wth Sub
              || in_paren(pddl_reserved "/" >> f && f) wth Div
              || in_paren(pddl_reserved "*" >> repeat2 f) wth Mult
              || in_paren(pddl_reserved "+" >> repeat2 f) wth Add
              ) ?? "f_exp"

  val f_comp = ((in_paren ((char #"<") >> f_exp && f_exp)) wth PDDL_Lt
            || (in_paren ((char #"<=") >> f_exp && f_exp)) wth PDDL_Le
            || (in_paren ((char #">") >> f_exp && f_exp)) wth PDDL_Gt
            || (in_paren ((char #">=") >> f_exp && f_exp)) wth PDDL_Ge
            ) wth PDDL_Comp ?? "numeric comparison"

  fun atomic_formula t = ((in_paren(predicate && repeat t)
                             wth PDDL_Pred)
                         || in_paren((pddl_reserved "=") >> t && t)
                               wth PDDL_Eq) ?? "Atomic formula"

  (* we ignore this ... *)
  fun literal t = ((atomic_formula t) || (in_paren(pddl_reserved "not" >> atomic_formula t)) wth PDDL_Not t) ?? "literal"

  fun GD = fix (fn f => ((atomic_formula term) wth PDDL_Form_Atom)
            || in_paren(pddl_reserved "not" >> f) wth PDDL_Not
            || in_paren(pddl_reserved "and" >> repeat1 f) wth PDDL_And
            || in_paren(pddl_reserved "or" >> repeat1 f) wth PDDL_Or
            || in_paren(pddl_reserved "forall" >> (in_paren(typed_list pddl_var) && f)) wth PDDL_All
            || in_paren(pddl_reserved "exists" >> (in_paren(typed_list pddl_var) && f)) wth PDDL_Exists
            || f_comp
                ) ?? "GD"
  
  fun pre_GD = GD ?? "pre GD" (* the and in the pre_GD is parsed by GD *)

  val p_effect = ((in_paren (atomic_formula term) wth (Add o PDDL_Form_Atom))
                || (in_paren (pddl_reserved "not" >> atomic_formula term) wth (Del o PDDL_Form_Atom))
                || (in_paren (pddl_reserved "assign" >> term) wth Unassign)
                || (in_paren (pddl_reserved "assign" >> term && term) wth Assign)
                || (in_paren (pddl_reserved "assign" >> f_head && f_exp) wth N_Assign)
                || (in_paren (pddl_reserved "scale-up" >> f_head && f_exp) wth N_ScaleUp)
                || (in_paren (pddl_reserved "scale-down" >> f_head && f_exp) wth N_ScaleDown)
                || (in_paren (pddl_reserved "increase" >> f_head && f_exp) wth N_Increase)
                || (in_paren (pddl_reserved "decrease" >> f_head && f_exp) wth N_Decrease)) ?? "p_effect"

  val cond_effect = (p_effect || 
                || (in_parent (pddl_reserved "and" >> repeat p_effect)) wth EFF_And)
                ?? "cond_effect"

  (* effect and c_effect are mutually recursive in Kovac's definition.
      I have convinced myself that this definition is equivalent.*)
  val c_effect = fix (fn c_eff => 
                 (in_paren (pddl_reserved "and" >> repeat1 c_eff) wth EFF_And)
              || (in_paren (pddl_reserved "forall" >> (in_paren (typed_list variable)) && c_eff)) wth EFF_All
              || (in_paren (pddl_reserved "when" >> GD && cond_effect)) wth EFF_Cond
              || cond_effect) ?? "c_effect"

  val effect = c_effect ?? "effect"

  fun emptyOR x = opt x

  val action_def_body = (opt (pddl_reserved ":precondition" >> emptyOR pre_GD)
                         && opt (pddl_reserved ":effect" >> emptyOR effect)) ?? "Action def body"

  val action_symbol = pddl_name

  val action_def = (in_paren(pddl_reserved ":action" >>
                    action_symbol
                    && (pddl_reserved ":parameters" >> (in_paren(typed_list pddl_var)))
                    && action_def_body)) ?? "action def"

  val structure_def = (action_def (*|| durative_action_def || derived_def*) )?? "struct def"

  val invariant_symbol = (pddl_reserved ":name" >> pddl_name) ?? "invariant symbol"

  val quantification = (pddl_reserved ":vars" >> in_paren(repeat pddl_var)) ?? "quantification"

  val constraints = (pddl_reserved ":set-constraint" >> pre_GD) ?? "constraint"

  val invariant_def = (in_paren(pddl_reserved ":invariant" >> spaces >>
                                 (invariant_symbol << spaces) &&
                                 (quantification << spaces) &&
                                 (constraints << spaces))) ?? "invariants def"

  val domain = in_paren(pddl_reserved "define" >> in_paren(pddl_reserved "domain" >> pddl_name)
                                                  >> (opt require_def)
                                                  >> (opt types_def)
                                                  && (opt constants_def)
                                                  && (opt predicates_def)
                                                  && (opt functions_def)
                                                  && (repeat structure_def)) ?? "domain"
                                                  (*&& (repeat invariant_def)*)

  
  val object_declar = in_paren(pddl_reserved ":objects" >> (typed_list pddl_obj_cons))

  val basic_fun_term = (function_symbol 
                    || in_paren(function_symbol && repeat pddl_obj_cons)
                    ) ?? "basic function term"

  val init_el = ((atomic_formula pddl_name) wth True_Pred
                 || in_paren((pddl_reserved "not") >> atomic_formula pddl_name) wth False_Pred
                 || in_paren((pddl_reserved "=") >> basic_fun_term && pddl_name)
                               wth Init_Obj_Func_Asmt
                 || in_paren((pddl_reserved "=") >> basic_fun_term && (dec_num wth Num))
                               wth Init_Num_Func_Asmt) ?? "init element"

  val init = in_paren(pddl_reserved ":init" >> repeat (init_el))


  (* The rule for goals is exactly as the one in Kovacs. It is wrong, nonetheless, since a goal
     should be only defined on GDs over objects or constants only and not terms!! *)

  val goal = in_paren(pddl_reserved ":goal" >> pre_GD)

  val optimisation = (pddl_reserved "maximize" || pddl_reserved "minimize") ?? "Optimisation"

  val metric_f_exp = function_symbol

  val metric_spec = in_paren(pddl_reserved ":metric" >> optimisation >> in_paren(metric_f_exp))

  val problem = in_paren(pddl_reserved "define" >> in_paren(pddl_reserved "problem" >> pddl_name)
                                                >> in_paren(pddl_reserved ":domain" >> pddl_name)
                                                >> (opt (require_def))
                                                  && (object_declar)
                                                  && init
                                                  && goal
                                                  && opt metric_spec) ?? "problem"

  val plan_action = in_paren(pddl_name && repeat pddl_obj_cons)
  val plan = repeat plan_action

end

open PDDL()

  (* These are the data types of the objects parsed above. *)

  (*Types for the domain*)

  type PDDL_PRE_GD = PDDL_FORM

  type PDDL_ACTION_DEF_BODY = (PDDL_PRE_GD option) * (PDDL_EFFECT option)

  type PDDL_ACTION_SYMBOL = string


  type PDDL_ACTION = PDDL_ACTION_SYMBOL *
                          (PDDL_VAR PDDL_TYPED_LIST *
                                     (PDDL_ACTION_DEF_BODY))

  type PDDL_ACTIONS_DEF = (PDDL_ACTION list)


  type ATOMIC_FORM_SKEL = PDDL_PRED * (PDDL_VAR PDDL_TYPED_LIST)

  type PDDL_PREDS_DEF = ATOMIC_FORM_SKEL list

  type 'a FUN_TYPED_LIST = (('a list) * PDDL_TYPE option) list

  type ATOMIC_FUN_SKELETON = string * (PDDL_VAR PDDL_TYPED_LIST)

  type PDDL_FUNS_DEF = ATOMIC_FUN_SKELETON FUN_TYPED_LIST option

  type PDDL_TYPE = PDDL_PRIM_TYPE list

  type 'a PDDL_TYPED_LIST = (('a list) * PDDL_TYPE) list

  type PDDL_TYPES_DEF = (PDDL_PRIM_TYPE PDDL_TYPED_LIST) option

  type PDDL_CONSTS_DEF = (PDDL_OBJ_CONS PDDL_TYPED_LIST) option

  type PDDL_DOMAIN = (PDDL_TYPES_DEF option * PDDL_CONSTS_DEF option * PDDL_PREDS_DEF option * PDDL_FUNS_DEF option * PDDL_STRUCTURE_DEF list)

  (* Types for the instance *)

  type PDDL_OBJ_DEF = PDDL_OBJ_CONS PDDL_TYPED_LIST

  type PDDL_INIT_EL = PDDL_OBJ_CONS PDDL_FORM

  type PDDL_INIT = PDDL_INIT_EL list

  type PDDL_GOAL = PDDL_FORM

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

  fun pddlVarTermToString term = 

    case term of VAR_TERM v => pddlVarToString v
             | _ => exit_fail ("Var expected, but obejct found: pddlVarTermToString " ^ (pddlObjConsTermToString term))

  and pddlObjConsTermToString term = 
    case term of OBJ_CONS_TERM oc => pddlObjConsToString oc
             | _ => exit_fail ("Object expected, but variable found: pddlObjConsTermToString " ^ (pddlVarTermToString term))

  fun pddlTypedListXTypesConv typedList cat_fn mk_pair_fn obj_v_conv_fun type_conv_fun =
    let
      fun wrap_var_with_type t = (fn v => mk_pair_fn (obj_v_conv_fun v) (type_conv_fun t))
    in
      cat_fn (map (fn (vars, type_) => (map (wrap_var_with_type type_) vars)) typedList)
    end

  fun extractFlatTypedList cat_fn str_fn mk_pair_fn (typedList :PDDL_PRIM_TYPE PDDL_TYPED_LIST) = let
    fun sng_typ [t] = str_fn (pddl_prim_type_name t)
      | sng_typ _ = exit_fail "Either-types not supported as supertypes"
  in
    cat_fn (map (fn (ts, supt) => map (fn t => mk_pair_fn (str_fn (pddl_prim_type_name t)) (sng_typ supt)) ts) typedList)
  end


(*Some utility functions*)

fun fst (x,y) = x
fun snd (x,y) = y
fun pddl_prop_map f prop =
 case prop of PDDL_atom atm => PDDL_atom (map_atom f atm)
           | PDDL_Not sub_prop => PDDL_Not (pddl_prop_map f sub_prop)
           | PDDL_And props => PDDL_And (map (pddl_prop_map f) props)
           | PDDL_Or props => PDDL_Or (map (pddl_prop_map f) props)
           | Fluent => Fluent;
