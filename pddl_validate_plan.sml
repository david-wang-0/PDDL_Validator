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

  fun pddlVarToIsabelle (v: PDDL_VAR) = Variable (stringToIsabelle (pddl_var_name v))

  fun pddlObjConsToIsabelle (oc: PDDL_OBJ_CONS) = Object (stringToIsabelle (pddl_obj_name oc))

  fun pddlTermToIsabelle (OBJ_CONS_TERM oc) = Ent (Const (pddlObjConsToIsabelle oc))
    | pddlTermToIsabelle (VAR_TERM v) = Ent (Var (pddlVarToIsabelle v))
    | pddlTermToIsabelle (FUN_TERM (f, ts)) = Fun (Function (stringToIsabelle f), map pddlTermToIsabelle ts)

  fun pddlVarTermToIsabelle term = 
    case term of VAR_TERM v => pddlVarToIsabelle v
             | _ => exit_fail ("Var expected, but object found: pddlVarTermToIsabelle " ^ (pddlObjConsTermToString term))

  fun pddlObjConsTermToIsabelle term = 
    case term of OBJ_CONS_TERM v => pddlObjConsToIsabelle v
             | _ => exit_fail ("Object expected, but variable found: pddlObjConsTermToIsabelle " ^ (pddlVarTermToString term))

  fun pddlTypeToIsabelle (type_ :PDDL_TYPE) = Either (stringListToIsabelle (map pddl_prim_type_name type_))

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
  
  val pddlPrimTypeToIsabellePrimType = stringToIsabelle o pddl_prim_type_name;

  fun pddlTypesDefToIsabelle (typesDefOPT: PDDL_TYPES_DEF option) =
    case typesDefOPT of
      SOME typesDef =>
        let 
          val pddlTypeToIsabelleSuperType: PDDL_TYPE -> isa_prim_type = (fn t => case t of
            [x] => pddlPrimTypeToIsabellePrimType x
          | _   => exit_fail "'Either' supertypes not supported")
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
        flatMapTypedList1 pddlObjConsToIsabelle pddlTypeToIsabelleType constsDef
    | _ => []

  
  fun pddlTypedListToIsabelleSig (l: 'a PDDL_TYPED_LIST): typea list =
    flatMapTypedList (pddlTypeToIsabelleType o snd) l;

  fun pddlPredToIsabelle (p: ATOMIC_FORM_SKEL) =
    let 
      val (name, params) = p;
    in  
      PredDecl (Predicate (stringToIsabelle name),
        flatMapTypedList (pddlTypeToIsabelleType o snd) params)
    end

  fun pddlPredDefToIsabelle (pred_defOPT: PDDL_PREDS_DEF option): pred_decl list =
    case pred_defOPT of
      SOME pred_def =>
            (map pddlPredToIsabelle pred_def)
      | _ => []
  
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

  fun pddlEqToIsabelleTerm (term1, term2) = Eqa (pddlVarTermToIsabelle term1, pddlVarTermToIsabelle term2 )

  fun pddlEqToIsabelleObj (term1, term2) = Eqa (pddlObjConsToIsabelle term1, pddlObjConsToIsabelle term2)

  fun pddlFormulaToASTPropIsabelleTerm (prob_decs: ast_problem_decs) phi =
      let 
        fun f1 (phi: PDDL_TERM PDDL_PROP): term atom formula = 
          case phi of Prop_atom(atom : PDDL_TERM PDDL_ATOM) =>  Atom (map_atom pddlTermToIsabelle atom)
                 | Prop_not(prop: PDDL_TERM PDDL_PROP) =>  Not (f1 prop)
                 | Prop_and(propList: PDDL_TERM PDDL_PROP list) => bigAnd (map f1 propList)
                 | Prop_or(propList: PDDL_TERM PDDL_PROP list) => bigOr (map f1 propList)
                 | Prop_all(args: PDDL_VAR PDDL_TYPED_LIST, prop: PDDL_TERM PDDL_PROP) => pddl_all_impl prob_decs (pddlTypedListVarsTypesToIsabelle args) (f1 prop)
                 | Prop_exists(args: PDDL_VAR PDDL_TYPED_LIST, prop: PDDL_TERM PDDL_PROP) => pddl_exists_impl prob_decs (pddlTypedListVarsTypesToIsabelle args) (f1 prop)
                 | _ => Bot (*Fluents shall invalidate the problem*)
      in
        f1 phi
      end

  fun pddlFormulaToASTPropIsabelleObj phi =
    case phi of 
        Prop_atom(atom : PDDL_TERM PDDL_ATOM) =>  Atom (map_atom pddlObjConsTermToIsabelle atom)
      | Prop_not(prop: PDDL_TERM PDDL_PROP) =>  Not (pddlFormulaToASTPropIsabelleObj prop)
      | Prop_and(propList: PDDL_TERM PDDL_PROP list) => bigAnd (map pddlFormulaToASTPropIsabelleObj propList)
      | Prop_or(propList: PDDL_TERM PDDL_PROP list) => bigOr (map pddlFormulaToASTPropIsabelleObj propList)
      | _ => Bot (*Fluents and quantifiers shall invalidate the problem*)

  fun pddlPreGDToIsabelle (prob_decs: ast_problem_decs) PreGD =
    case PreGD of 
      SOME (prop: PDDL_TERM PDDL_PROP) => pddlFormulaToASTPropIsabelleTerm prob_decs prop
    | _ => Not Bot (*If we have no precondition, then it is a tautology*)

  fun isProp_atom fmla = 
    case fmla of 
      Prop_atom(atom) => true 
    | _ => false

  fun isNegProp_atom fmla = 
    case fmla of 
      Prop_not(Prop_atom(atom)) => true 
    | _ => false

  fun strToVarAtom atom = map_atom (fn x => pddlTermToIsabelle x) atom

  fun strToObjAtom atom = map_atom (fn x => pddlObjConsTermToIsabelle x) atom

  fun pddlPropLiteralToIsabelleAtom lit = 
      case lit of Prop_atom atom => Atom (strToVarAtom atom)
               | Prop_not(Prop_atom atom) => Atom (strToVarAtom atom)
               | _ => exit_fail "Literal expected"

  fun pddlPropToASTEffIsabelle (Prop: PDDL_TERM PDDL_PROP) =
      case Prop of Prop_atom atom => ([Atom (strToVarAtom atom)],[])
                 | Prop_not (Prop_atom atom) => ([],[Atom (strToVarAtom atom)])
                 | Prop_and propList
                     => (let val adds = (List.filter isProp_atom propList);
                             val dels = (List.filter isNegProp_atom propList);
                         in (map pddlPropLiteralToIsabelleAtom adds, map pddlPropLiteralToIsabelleAtom dels)
                         end)
                 | _ => ([], [])

  fun pddlCEffectToIsabelle CEff =
      case CEff of SOME (prop: PDDL_TERM PDDL_PROP) => Effect (pddlPropToASTEffIsabelle prop)
                 | _ => Effect ([],[])

  fun actDefBodyPreToIsabelle (prob_decs: ast_problem_decs) pre = case pre of SOME (u, pre: PDDL_PRE_GD) => pddlPreGDToIsabelle prob_decs pre
                                            | _ => Not Bot
  fun actDefBodyEffToIsabelle eff = case eff of SOME (u, eff: C_EFFECT) => pddlCEffectToIsabelle eff
                                            | _ => Effect ([],[])
  fun pddlActDefBodyToIsabelle (prob_decs: ast_problem_decs) (pre, eff) = ((actDefBodyPreToIsabelle prob_decs pre), (actDefBodyEffToIsabelle eff))

  fun pddlIsabelleActName actName = SMLCharImplode (map (fn c => if c = #"-" then #"_" else c) (SMLCharExplode actName))

  fun pddlActToIsabelle (prob_decs: ast_problem_decs) (actName, (args, defBody)) =
      Action_Schema(IsabelleStringExplode actName,
                    pddlTypedListVarsTypesToIsabelle args,
                    fst (pddlActDefBodyToIsabelle prob_decs defBody),
                    snd (pddlActDefBodyToIsabelle prob_decs defBody))


  fun pddlActionsDefToIsabelle (prob_decs: ast_problem_decs) (actsDef : PDDL_ACTION list) =
                    (map (pddlActToIsabelle prob_decs) actsDef)

  fun objDefToIsabelle (objs:PDDL_OBJ_DEF) = pddlTypedListObjsConsTypesToIsabelle objs

  fun isntFluent x = (case x of Fluent => false | _ => true)

  fun isntTautology x = (case x of Not Bot => false | _ => true)

  fun initElToIsabelle (init_el:PDDL_INIT_EL) = pddlFormulaToASTPropIsabelleObj (pddl_prop_map OBJ_CONS_TERM init_el)


  fun pddlInitToIsabelleWithObjEqs (init:PDDL_INIT) objs = (map initElToIsabelle (List.filter isntFluent init)) (*I don't want fluents in the init state. This is usually an init value for the plan-cost.*)
                                                           @ (map (fn obj => Atom (pddlEqToIsabelleObj (obj, obj))) objs)

  fun pddlInitToIsabelle (init:PDDL_INIT) objs = (map initElToIsabelle (List.filter isntFluent init)) (*I don't want fluents in the init state. This is usually an init value for the plan-cost.*)


  fun pddlGoalToIsabelle (prob_decs: ast_problem_decs) (goal:PDDL_GOAL) = pddlFormulaToASTPropIsabelleTerm prob_decs goal

  fun pddlDomToIsabelleDomDecs
      (types_def, (consts_def, (pred_def, (funs_def, actions_def)))) = 
    let 
      val (obj_funs, num_funs) = pddlFunsDefToIsabelleFunsfuns_def;
    in
      PDDL_Checker_Exported.DomainDecls(
          pddlTypesDefToIsabelle types_def,
          pddlConstsDefToIsabelle consts_def,
          pddlPredDefToIsabelle pred_def,
          obj_funs, num_funs)
    end
  
  fun pddlProbAndDomDecsToIsaProbDecs 
                        (reqs:PDDL_REQUIRE_DEF,
                        (objs: PDDL_OBJ_DEF,
                          (init: PDDL_INIT,
                            (goal_form: PDDL_GOAL, metric))))
                        (dom_decs: ast_domain_decs)
                      = PDDL_Checker_Exported.ProbDecls(
                          dom_decs, 
                          objDefToIsabelle objs)
  
  fun pddlDomAndProbDecsToIsaDom 
                        (reqs:PDDL_REQUIRE_DEF,
                        (types_def,
                          (consts_def,
                              (pred_def,
                                (fun_def,
                                  (actions_def,
                                    constraints_def))))))
                        (prob_decs: ast_problem_decs)
                      = PDDL_Checker_Exported.Domain (
                          prob_decs,
                          pddlActionsDefToIsabelle prob_decs actions_def)

  fun pddlProbAndIsaDomToIsabelleProb 
                          (reqs:PDDL_REQUIRE_DEF,
                          (objs:PDDL_OBJ_DEF,
                              (init:PDDL_INIT,
                                (goal_form:PDDL_GOAL,
                                   metric))))
                          (dom: ast_domain)
                          = case dom of 
                            PDDL_Checker_Exported.Domain (prob_decs, actions) => 
                              PDDL_Checker_Exported.Problem(
                                dom,
                                pddlInitToIsabelle init (List.concat (map #1 objs)), 
                                pddlGoalToIsabelle prob_decs goal_form)


  fun planActionToIsabelle (act_name, args) = PAction(stringToIsabelle act_name, map pddlObjConsToIsabelle args)

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
  val parsedDom = parse_pddl_dom dom_file
  val parsedProb = parse_pddl_prob prob_file
  val parsedPlan = parse_pddl_plan plan_file

  val isaDomDecs = pddlDomToIsabelleDomDecs parsedDom
  val isaProbDecs = pddlProbAndDomDecsToIsaProbDecs parsedProb isaDomDecs
  val isaDom = pddlDomAndProbDecsToIsaDom parsedDom isaProbDecs
  val isaProb = pddlProbAndIsaDomToIsabelleProb parsedProb isaDom

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
(* 
val _ = case args of
  [d,pr,pl] => do_check_plan d pr pl
| _ => (
    println("Invalid command line arguments");
    print_help ();
    exit_fail ""
  ) *)

val _ = case args of
  [dom_file] => (
      parse_pddl_dom dom_file;
      println("Domain parsed")
  )

val _ = OS.Process.exit(OS.Process.success)
