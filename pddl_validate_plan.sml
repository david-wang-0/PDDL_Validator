  (* This file contains the code for converting the types in the parsed domain to those used
     by the validator exported by Isabelle in the file ../../../isabelle/code/PDDL_STRIPS_Checker_Exported.sml.
     It also calls the function exported by Isabelle to check the validity of a plan.*)
open PDDL

  val IsabelleStringImplode = implode;
  val IsabelleStringExplode = explode;
  val SMLCharImplode = String.implode;
  val SMLCharExplode = String.explode;

  type isa_prim_type = char list;

  val stringToIsabelle = IsabelleStringExplode
  fun stringListToIsabelle ss = (map stringToIsabelle ss)

  fun pddlVarToIsabelleVariable (v: PDDL_VAR): PDDL_Checker_Exported.variable = Variable (stringToIsabelle (pddl_var_name v))

  fun pddlObjConsToIsabelleObject (oc: PDDL_OBJ_CONS): PDDL_Checker_Exported.object = Object (stringToIsabelle (pddl_obj_name oc))

  fun pddlTermToIsabelleTerm (OBJ_CONS_TERM oc) = Ent (Const (pddlObjConsToIsabelleObject oc))
    | pddlTermToIsabelleTerm (VAR_TERM v) = Ent (Var (pddlVarToIsabelleVariable v))
    | pddlTermToIsabelleTerm (FUN_TERM (f, ts)) = Fun (Function (stringToIsabelle f), map pddlTermToIsabelleTerm ts)

  fun mk_pair x y = (x,y)
  fun snd (a, b) = b
  fun fst (a, b) = a
  fun map_pair (f1: 'a -> 'c) (f2: 'b -> 'd) (p: ('a * 'b)) : ('c * 'd)
    = case p of (a, b) => (f1 a, f2 b)

  fun type_str_cat_fun (l: string list list) = (String.concatWith ", ") (map (String.concatWith ", ") l)

  fun flattenTypedList (l: ('a list * 'b) list): ('a * 'b) list =
    List.concat (map (fn (vs, t) => map (fn v => (v, t)) vs) l)

  fun flatMapTypedList (f: ('a * 'b) -> 'c): ('a list * 'b) list -> 'c list =
    (map f) o flattenTypedList

  fun flatMapTypedList1 (f1: 'a -> 'c) (f2: 'b -> 'd): ('a list * 'b) list -> ('c * 'd) list = 
    (map (map_pair f1 f2)) o flattenTypedList
  
  val pddlPrimTypeToIsabellePrimType: PDDL_PRIM_TYPE -> isa_prim_type = stringToIsabelle o pddl_prim_type_name;

  fun pddlTypesDefToIsabelle (typesDefOPT: PDDL_TYPES_DEF option) =
    case typesDefOPT of
      SOME typesDef =>
        let 
          val pddlTypeToIsabelleSuperType: PDDL_TYPE -> isa_prim_type = 
            (fn t => case t of
              [x] => pddlPrimTypeToIsabellePrimType x
            | _   => exit_fail "'Either' supertypes not supported")
          val pddlPrimTypeToIsabelleSubType: PDDL_PRIM_TYPE -> isa_prim_type = 
            (fn t => case t of
              PDDL_PRIM_TYPE "object" => 
                exit_fail "'object' cannot be a subtype"
            | t => 
                pddlPrimTypeToIsabellePrimType t)
        in
          flatMapTypedList1 pddlPrimTypeToIsabellePrimType pddlTypeToIsabelleSuperType typesDef
        end
    | _ => []

  fun pddlTypeToIsabelleType (t: PDDL_TYPE): typea =
    Either (map pddlPrimTypeToIsabellePrimType t)

  fun pddlFunTypeToIsabelleType (t: PDDL_FUN_TYPE): typea =
    case t of 
      (Obj_Type t) => pddlTypeToIsabelleType t
    | _ => exit_fail "Invalid function return type"


  fun pddlConstsDefToIsabelle (constsDefOPT: PDDL_CONSTS_DEF option) =
    case constsDefOPT of
      SOME constsDef =>
        flatMapTypedList1 pddlObjConsToIsabelleObject pddlTypeToIsabelleType constsDef
    | _ => []

  
  fun pddlTypedListToIsabelleSig (l: 'a PDDL_TYPED_LIST): typea list =
    flatMapTypedList (pddlTypeToIsabelleType o snd) l;

  fun pddlPredDeclToIsabelle (p: ATOMIC_FORM_SKEL) =
    let 
      val (name, params) = p;
    in  
      PredDecl (Predicate (stringToIsabelle name),
        flatMapTypedList (pddlTypeToIsabelleType o snd) params)
    end

  fun pddlPredDefToIsabelle (pred_defOPT: PDDL_PREDS_DEF option): pred_decl list =
    case pred_defOPT of
      SOME pred_def =>
            (map pddlPredDeclToIsabelle pred_def)
      | _ => []
  

  (* According to Kovacs, the number return type is deprecated and inferred as a default since PDDL 3.1.
      The usual semantics (? not sure) of typed lists indicate that a type annotation applies to 
      all preceding elements. Therefore, the numeric return type would only be inferred for functions
      declared at the end of the list of declarations if we followed Kovac's definition. Instead, we
      support the number return type. 
      E.g.: in (f1 ... f2 ... - object f3. .. - number f5 ... - object f6 ...) only f3 and f6 are numeric *)
  fun pddlFunsDefToIsabelleFuns (funs_defOPT: PDDL_FUNS_DEF option): (obj_func_decl list * num_func_decl list) = 
    case funs_defOPT of
      SOME funs_def => 
      let 
        val (obj_funs, num_funs) = (List.partition (fn (v, t) => t <> Num_Type) funs_def);
        val fHead = map_pair (Function o stringToIsabelle) pddlTypedListToIsabelleSig;
        val fObj = flatMapTypedList (fn (h, r) => 
          case fHead h of
           (f, args) => ObjFunDecl (f, args, pddlFunTypeToIsabelleType r));
        val fNum = flatMapTypedList (NumFunDecl o fHead o fst);
      in 
        (fObj obj_funs, fNum num_funs)
      end
    | _ => ([], [])

  fun pddlObjDefToIsabelle (objs: PDDL_OBJ_DEF option): (object * typea) list =
    case objs of 
      SOME objs1  => flatMapTypedList1 pddlObjConsToIsabelleObject pddlTypeToIsabelleType objs1
    | NONE        => []

  fun pddlAtomToIsabellePredicate (f: 'a -> 'b) (atom: 'a PDDL_ATOM) =
    case atom of 
      PDDL_Pred (name, ts) => Pred (Predicate (stringToIsabelle name), map f ts)
    | PDDL_Pred_Eq (t1, t2)  => Eqa (f t1, f t2)

  val pddlTermAtomToIsabellePredicate: PDDL_TERM PDDL_ATOM -> symbol term predicate = 
    pddlAtomToIsabellePredicate pddlTermToIsabelleTerm

  fun pddlFExpToIsabelleNFluent (exp: PDDL_F_EXP) =
    case exp of
      PDDL_Num (i, d) => Num (rat_from_strings (stringToIsabelle i) (Option.map stringToIsabelle d))
    | F_Head (f, args) => NFun (Function (stringToIsabelle f), map pddlTermToIsabelleTerm args)
    | PDDL_Neg e => pddlFExpToIsabelleNFluent (PDDL_Minus (PDDL_Num ("0", NONE), e))
    | PDDL_Minus (e1, e2) => Sub (pddlFExpToIsabelleNFluent e1, pddlFExpToIsabelleNFluent e2) 
    | PDDL_Div (e1, e2) => Div (pddlFExpToIsabelleNFluent e1, pddlFExpToIsabelleNFluent e2)
    | PDDL_Times es => mult_list (map pddlFExpToIsabelleNFluent es)
    | PDDL_Plus es => add_list (map pddlFExpToIsabelleNFluent es)

  fun pddlCompToIsabelleComp (comp: PDDL_F_COMP) =
    case comp of
      PDDL_Num_Lt (e1, e2) => Num_Lt (pddlFExpToIsabelleNFluent e1, pddlFExpToIsabelleNFluent e2)
    | PDDL_Num_Le (e1, e2) => Num_Le (pddlFExpToIsabelleNFluent e1, pddlFExpToIsabelleNFluent e2)
    | PDDL_Num_Eq (e1, e2) => Num_Eq (pddlFExpToIsabelleNFluent e1, pddlFExpToIsabelleNFluent e2)
    | PDDL_Num_Gt (e1, e2) => Num_Le (pddlFExpToIsabelleNFluent e2, pddlFExpToIsabelleNFluent e1)
    | PDDL_Num_Ge (e1, e2) => Num_Lt (pddlFExpToIsabelleNFluent e2, pddlFExpToIsabelleNFluent e1)

  val pddlVarParamsToIsabelleParams: (PDDL_VAR PDDL_TYPED_LIST) -> (PDDL_Checker_Exported.variable * typea) list =
          flatMapTypedList1 pddlVarToIsabelleVariable pddlTypeToIsabelleType;


  fun pddlFormToIsabelleForm (prob_decs: ast_problem_decs) (phi: PDDL_FORM) =
      let 
        fun f1 (phi: PDDL_FORM): symbol term atom formula = case phi of 
          PDDL_Form_Atom atom   => Atom (PredAtom (pddlTermAtomToIsabellePredicate atom))
        | PDDL_Form_Comp comp   => Atom (NumComp (pddlCompToIsabelleComp comp))
        | PDDL_Not f            => Not (f1 f)
        | PDDL_And fs           => bigAnd (map f1 fs)
        | PDDL_Or fs            => bigOr (map f1 fs)
        | PDDL_All (vts, f)     => pddl_all_impl prob_decs (pddlVarParamsToIsabelleParams vts) (f1 f)
        | PDDL_Exists (vts, f)  => pddl_exists_impl prob_decs (pddlVarParamsToIsabelleParams vts) (f1 f)
      in
        f1 phi
      end

  fun pddlPreToIsabelleForm 
    (prob_decs: ast_problem_decs) 
    (pre: PDDL_PRE_GD option) = 
      case pre of 
        SOME (pre: PDDL_PRE_GD) => pddlFormToIsabelleForm prob_decs pre
      | _ => Not Bot (* If we have no precondition, the precondition is always true *)

  fun pddlFHeadToIsabelleFHead ((f, args): F_HEAD): (func * (symbol term list)) = 
    (Function (stringToIsabelle f), map pddlTermToIsabelleTerm args)

  fun opAndFHeadAndExpToIsaNfUpd (oper: upd_op) (h: F_HEAD) (v: PDDL_F_EXP): symbol term nf_upd =
    NF_Upd (flat43 (oper, flatl3 (pddlFHeadToIsabelleFHead h, pddlFExpToIsabelleNFluent v)))

  val ofUpdToEff =
    (fn v => Effect ([], [], [v], []))

  val nfUpdToEff =
    (fn v => Effect ([], [], [], [v]))

  datatype ('a, 'b) either = 
    Left of 'a
  | Right of 'b
  
  fun pddlAssignToIsabelleUpd (prob_decs: ast_problem_decs) (h: F_HEAD) (v: PDDL_F_EXP): symbol term ast_effect =
    case v of
      (F_Head (rh, rts)) => 
        let
          val rh1 = Function (stringToIsabelle rh)
        in
          case (is_obj_fun prob_decs rh1, is_num_fun prob_decs rh1) of
            (True, _) => ofUpdToEff (OF_Upd (flatl3 (pddlFHeadToIsabelleFHead h, SOME (pddlTermToIsabelleTerm (FUN_TERM (rh, rts))))))
          | (_, True) => nfUpdToEff (opAndFHeadAndExpToIsaNfUpd Assign h (F_Head (rh, rts)))
          | _  => exit_fail ("Function" ^ rh ^ "is undefined")
        end
    | v => nfUpdToEff (opAndFHeadAndExpToIsaNfUpd Assign h v)

  fun pddlEffToIsabelleCondEffList 
      (prob_decs: ast_problem_decs) (eff: PDDL_EFFECT option): 
        (symbol term atom formula * symbol term ast_effect) list = 
    let 
      fun f1 (eff: PDDL_EFFECT): symbol term ast_effect =
        (case eff of
          Add p => Effect ([pddlTermAtomToIsabellePredicate p], [], [], [])
        | Del p => Effect ([], [pddlTermAtomToIsabellePredicate p], [], [])
        | Unassign h => ofUpdToEff (OF_Upd (flatl3 (pddlFHeadToIsabelleFHead h, NONE)))
        | PDDL_Assign (h, v) => pddlAssignToIsabelleUpd prob_decs h v 
        | N_ScaleUp (h, v) => nfUpdToEff (opAndFHeadAndExpToIsaNfUpd ScaleUp h v)
        | N_ScaleDown (h, v) => nfUpdToEff (opAndFHeadAndExpToIsaNfUpd ScaleDown h v)
        | N_Increase (h, v) => nfUpdToEff (opAndFHeadAndExpToIsaNfUpd Increase h v)
        | N_Decrease (h, v) => nfUpdToEff (opAndFHeadAndExpToIsaNfUpd Decrease h v)
        | EFF_And _ => exit_fail "EFF_And does not result in a simple effect"
        | EFF_Cond _ => exit_fail "EFF_Cond does not result in a simple effect"
        | EFF_All _ => exit_fail "EFF_All does not result in a simpl_effect"
        )
      and f2 (eff: PDDL_EFFECT): (symbol term atom formula * symbol term ast_effect) list =
        (case eff of
          EFF_And effs        => List.concat (map f2 effs)
        | EFF_Cond (pre, eff) => 
            map (fn (p, e) => 
              if (p = Not Bot)
              then (pddlFormToIsabelleForm prob_decs pre, e)
              else (And (p, pddlFormToIsabelleForm prob_decs pre), e)
              ) (f2 eff)
        | EFF_All (vts, eff)  => pddl_univ_effect_list_impl prob_decs (pddlVarParamsToIsabelleParams vts) (f2 eff)
        | eff       => [(Not Bot, f1 eff)]
        );
    in
      case eff of 
        SOME (eff: PDDL_EFFECT) => f2 eff
      | _                       => []
    end
  
  fun pddlActDefBodyToIsabelle 
      (prob_decs: ast_problem_decs) 
      (pre: PDDL_PRE_GD option, 
        eff: PDDL_EFFECT option) = 
    (pddlPreToIsabelleForm prob_decs pre, pddlEffToIsabelleCondEffList prob_decs eff)

  fun pddlIsabelleActName actName = SMLCharImplode (map (fn c => if c = #"-" then #"_" else c) (SMLCharExplode actName))

  fun pddlActToIsabelle 
      (prob_decs: ast_problem_decs) 
      (actName: PDDL_ACTION_SYMBOL, 
        args: PDDL_VAR PDDL_TYPED_LIST, 
        defBody: PDDL_ACTION_DEF_BODY) =
    Action_Schema
      (flat42 (stringToIsabelle actName,
        pddlVarParamsToIsabelleParams args,
        pddlActDefBodyToIsabelle prob_decs defBody))

  fun pddlActionsDefToIsabelle 
      (prob_decs: ast_problem_decs) 
      (actsDef : PDDL_ACTION list) =
    map (pddlActToIsabelle prob_decs) actsDef

  val pddlObjAtomToIsabelleObjPredicate: PDDL_OBJ_CONS PDDL_ATOM -> object predicate =
    pddlAtomToIsabellePredicate pddlObjConsToIsabelleObject

  fun pddlInitPredToIsabellePred
      (init: PDDL_INIT): object predicate list =
    case init of 
      True_Pred p => [pddlObjAtomToIsabelleObjPredicate p]
    | False_Pred p => (
        println "Negative initial literals not supported. Closed world assumption is made"; 
        []
      )
    | _ => exit_fail "Invalid assignment to a predicate"

  fun pddlInitObjFunAsmtToIsabelleObjFunAsmt 
      (init: PDDL_INIT): (func * object list * object) =
    case init of 
      Init_Obj_Func_Asmt (f, args, v) => (Function (stringToIsabelle f), map pddlObjConsToIsabelleObject args, pddlObjConsToIsabelleObject v)
    | _ => exit_fail "Invalid assignment to an object function"

  fun pddlInitNumFunAsmtToIsabelleNumFunAsmt 
      (init: PDDL_INIT): (func * object list * rat) =
    case init of 
      Init_Num_Func_Asmt (f, args, (n, d)) => 
        (Function (stringToIsabelle f), 
          map pddlObjConsToIsabelleObject args, 
          rat_from_strings (stringToIsabelle n) (Option.map stringToIsabelle d))
    | _ => exit_fail "Invalid assignment to a numeric function"

  fun initIsPredicate (init: PDDL_INIT) =
    case init of 
      True_Pred _ => true
    | False_Pred _ => true
    | _ => false

  fun initIsObjFunAsmt (init: PDDL_INIT) =
    case init of 
      Init_Obj_Func_Asmt _ => true
    | _ => exit_fail "Invalid assignment to object function"

  fun initIsNumFunAsmt (init: PDDL_INIT) =
    case init of 
      Init_Num_Func_Asmt _ => true
    | _ => exit_fail "Invalid assignment to numeric function"

  fun pddlInitListToIsabelleInit (ls: PDDL_INIT list): 
        object predicate list *
        (func * (object list * object)) list * (* Isabelle exported a weird product type *)
        (func * (object list * rat)) list =
    let 
      val (preds, other) = List.partition initIsPredicate ls;
      val (initO, initN) = List.partition initIsObjFunAsmt other;
      val b = List.all initIsNumFunAsmt initN;
    in
      (List.concat (map pddlInitPredToIsabellePred preds), 
        map (invflat3 o pddlInitObjFunAsmtToIsabelleObjFunAsmt) initO, 
        map (invflat3 o pddlInitNumFunAsmtToIsabelleNumFunAsmt) initN)
    end

  val pddlGoalToIsabelle: ast_problem_decs -> PDDL_GOAL -> symbol term atom formula = 
    pddlFormToIsabelleForm

  fun pddlDomToIsabelleDomDecs 
      (types_def: PDDL_TYPES_DEF option, 
        consts_def: PDDL_CONSTS_DEF option, 
        pred_def: PDDL_PREDS_DEF option, 
        funs_def: PDDL_FUNS_DEF option, 
        actions_def: PDDL_ACTIONS_DEF): ast_domain_decs = 
    let 
      val (obj_funs, num_funs) = pddlFunsDefToIsabelleFuns funs_def;
    in
      PDDL_Checker_Exported.DomainDecls 
       (pddlTypesDefToIsabelle types_def,
        pddlConstsDefToIsabelle consts_def,
        pddlPredDefToIsabelle pred_def,
        obj_funs, 
        num_funs)
    end
  
  fun pddlProbAndDomDecsToIsaProbDecs 
      (dom_decs: ast_domain_decs)
      (objs: PDDL_OBJ_DEF option,
        init: PDDL_INIT list,
        goal: PDDL_GOAL): ast_problem_decs =
    PDDL_Checker_Exported.ProbDecls
     (dom_decs, 
      pddlObjDefToIsabelle objs)
  
  fun pddlDomAndProbDecsToIsaDom 
      (prob_decs: ast_problem_decs)
      (types_def: PDDL_TYPES_DEF option, 
        consts_def: PDDL_CONSTS_DEF option, 
        pred_def: PDDL_PREDS_DEF option, 
        funs_def: PDDL_FUNS_DEF option, 
        actions_def: PDDL_ACTIONS_DEF): ast_domain =
    PDDL_Checker_Exported.Domain
      (prob_decs, 
      pddlActionsDefToIsabelle prob_decs actions_def)

  fun pddlProbAndIsaDomToIsabelleProb 
      (dom: ast_domain)
      (objs: PDDL_OBJ_DEF option,
        init: PDDL_INIT list,
        goal_form: PDDL_GOAL): ast_problem = 
    case dom of 
      PDDL_Checker_Exported.Domain (prob_decs, actions) => 
        PDDL_Checker_Exported.Problem(
          flat535 (dom, pddlInitListToIsabelleInit init, 
          pddlGoalToIsabelle prob_decs goal_form))

  fun planActionToIsabelle (act_name, args) = PAction(stringToIsabelle act_name, map pddlObjConsToIsabelleObject args)

  fun planToIsabelle plan = map planActionToIsabelle plan

fun readFile file =
let
    fun next_String input = (TextIO.inputAll input)
    val stream = TextIO.openIn file
in
    next_String stream
end

fun writeFile file content =
    let val fd = TextIO.openOut file
        val _ = TextIO.output (fd, content) handle e => (TextIO.closeOut fd; raise e)
        val _ = TextIO.closeOut fd
    in () end

fun parse_wrapper parser file =
  case (CharParser.parseString parser (readFile file)) of
    Sum.INR x => x
  | Sum.INL err => exit_fail err

val parse_pddl_dom = parse_wrapper PDDL.domain
val parse_pddl_prob = parse_wrapper PDDL.problem
val parse_pddl_plan = parse_wrapper PDDL.plan


fun do_check_plan dom_file prob_file plan_file = let
  val _ = println "here";
  val parsedDom = parse_pddl_dom dom_file
  val _ = println "1";
  val parsedProb = parse_pddl_prob prob_file
  val _ = println "2";
  val parsedPlan = parse_pddl_plan plan_file
  val _ = println "3";
  val isaDomDecs = pddlDomToIsabelleDomDecs parsedDom
  val isaProbDecs = pddlProbAndDomDecsToIsaProbDecs isaDomDecs parsedProb
  val isaDom = pddlDomAndProbDecsToIsaDom isaProbDecs parsedDom
  val isaProb = pddlProbAndIsaDomToIsabelleProb isaDom parsedProb

  val isaPlan = planToIsabelle parsedPlan

in
  case PDDL_Checker_Exported.check_plan isaProb isaPlan of
      PDDL_Checker_Exported.Inl msg => exit_fail ("Invalid Plan: " ^ msg)
    | _ => println "Valid Plan"

end


val args = CommandLine.arguments()

fun print_help () = (
  println("c Usage: " ^ CommandLine.name() ^ "<domain> <problem> [<plan>]")
)
val _ = case args of
  [d,pr,pl] => do_check_plan d pr pl
| _ => (
    println("Invalid command line arguments");
    print_help ();
    exit_fail ""
  )

val _ = OS.Process.exit(OS.Process.success)
