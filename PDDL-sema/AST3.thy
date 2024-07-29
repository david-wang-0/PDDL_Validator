theory AST3
  imports AST2
begin
  
type_synonym name = String.literal

type_synonym pred = name
type_synonym func = name
type_synonym pref = name

datatype type = Either (primitives: "name list")

datatype variable = Variable (var_name: name)

datatype object = name: Object (obj_name: name)

datatype symbol = Var variable | Const object | Num rat | Duration

datatype (sym: 'sym) "term" = 
  Sym 'sym
| Fun func (arguments: "'sym term list") 

datatype (ent: 'ent) f_exp = 
  NFun func (arguments: "'ent list")
| Num rat
| Neg "'ent f_exp"
| Add "'ent f_exp" "'ent f_exp"
| Sub "'ent f_exp" "'ent f_exp"
| Mult "'ent f_exp" "'ent f_exp"
| Div "'ent f_exp" "'ent f_exp"

datatype (ent: 'ent) atom = 
  Pred (pred: pred) (arguments: "'ent list")
| Ent_Eq (lhs: 'ent) (rhs: 'ent)
| Num_Le "'ent" "'ent"
| Num_Lt "'ent" "'ent"


datatype ('x, atoms: 'a) GD = 
  Atom 'a
| Bot
| Not "('x, 'a) GD"
| And "('x, 'a) GD" "('x, 'a) GD"
| Or "('x, 'a) GD" "('x, 'a) GD"
| Imp "('x, 'a) GD" "('x, 'a) GD"
| ForAll 'x "('x, 'a) GD"
| Exists 'x "('x, 'a) GD"

datatype ('x, 'a) pre_GD =
  PrefGD "pref option" "('x, 'a) GD"
| ForAll 'x "('x, 'a) pre_GD"
| And "('x, 'a) pre_GD" "('x, 'a) pre_GD"


datatype ('x, atoms: 'a) timed_GD =
  OverAll "('x, 'a) GD"
| AtStart "('x, 'a) GD"
| AtEnd "('x, 'a) GD"

datatype ('x, atoms: 'a) da_GD =
  ForAll "'x" "('x, 'a) da_GD"
| And "('x, 'a) da_GD" "('x, 'a) da_GD"
| PrefTimedGD "pref option" "('x, 'a) timed_GD"

datatype upd_op = 
  Assign
| ScaleUp
| ScaleDown
| Increase
| Decrease

datatype (ent: 'ent) of_upd = OF_Upd func "'ent list" (ret_val: "'ent option")
datatype ('t, 'exp) nf_upd = NF_Upd upd_op func "'t list" "'exp"

type_synonym 't s_nf_upd = "('t, 't f_exp) nf_upd"

datatype 'ent simple_update =
  S_OU "'ent of_upd"
| S_NU "'ent s_nf_upd"
| S_Add "'ent atom"
| S_Del "'ent atom"

datatype ('x, 'ent) simple_effect =
  Eff "'ent simple_update"
| Eff_And "('x, 'ent) simple_effect list"
| Eff_All 'x "('x, 'ent) simple_effect"
| Eff_When "('x, 'ent atom) GD" "('x, 'ent) simple_effect"

datatype 'ent f_exp_da =
  Duration
| NFun func (arguments: "'ent list")
| Num rat
| Neg "'ent f_exp_da"
| Add "'ent f_exp_da" "'ent f_exp_da"
| Sub "'ent f_exp_da" "'ent f_exp_da"
| Mult "'ent f_exp_da" "'ent f_exp_da"
| Div "'ent f_exp_da" "'ent f_exp_da"

datatype 'ent f_exp_t = 
  Time
| MultTime "'ent f_exp"

type_synonym 't d_nf_upd = "('t, 't f_exp_da) nf_upd"

datatype 'ent durative_update =
  D_Add "'ent atom"
| D_Del "'ent atom"
| D_OU "'ent of_upd"
| D_NU "'ent d_nf_upd"

datatype 'ent timed_effect = 
  DUpd_At_Start "'ent durative_update"
| DUpd_At_End "'ent durative_update"
| DurScaleUp func "'ent list" "'ent f_exp_t"
| DurScaleDown func "'ent list" "'ent f_exp_t"

datatype ('x, 'ent) durative_effect =
  Timed_Effect "'ent timed_effect"
| DEff_And "('x, 'ent) durative_effect" "('x, 'ent) durative_effect" 
| DEff_All 'x "('x, 'ent) durative_effect"
| DEff_When "('x, 'ent atom) da_GD" "'ent timed_effect"
  
datatype ('t) simple_action = Simple_Action
  (name: name)
  (parameters: "(variable \<times> type) list")
  (precondition: "((variable \<times> type) list, 't atom) pre_GD")
  (effect: "((variable \<times> type) list, 't) simple_effect")

type_synonym ast_pre_GD = "((variable \<times> type) list, variable term atom) pre_GD"
type_synonym ast_simple_effect = "((variable \<times> type) list, variable term) simple_effect"
type_synonym ast_simple_action = "variable term simple_action"

datatype 'ent duration_constraint = 
  DurLe "'ent f_exp"
| DurGe "'ent f_exp"
| DurEq "'ent f_exp"

datatype ('t) durative_action = 
  Durative_Action 
    (name: name)
    (duration: "'t duration_constraint list")
    (parameters: "(variable \<times> type) list")
    (condition: "((variable \<times> type) list, 't atom) da_GD")
    (effect: "((variable \<times> type) list, 't) durative_effect")

type_synonym ast_da_GD = "((variable \<times> type) list, variable term atom) da_GD"
type_synonym ast_durative_effect = "((variable \<times> type) list, variable term) durative_effect"
type_synonym ast_durative_action = "variable term durative_action"

datatype ('t) action = 
  SA "'t simple_action"
  | DA "'t durative_action"

type_synonym ast_action = "variable term action"

text \<open>A pred declaration contains the pred's name and its
  argument types.\<close>
datatype pred_decl = PredDecl
  (predicate: pred)
  (argTs: "type list")

datatype obj_fun_decl = ObjFunDecl (of_name: func) "type list" type
datatype num_fun_decl = NumFunDecl (nf_name: func) "type list"

datatype derived_pred = 
  DerivedPred pred 
    (params: "(variable \<times> type) list")
    ast_pre_GD

datatype ast_domain = Domain 
  (types: "(name \<times> name) list") \<comment> \<open> \<open>(type, supertype)\<close> declarations. \<close>
  ("consts": "(object \<times> type) list")
  (preds: "pred_decl list")
  (ofs: "obj_fun_decl list")
  (nfs: "num_fun_decl list")
  (actions: "ast_action list")
  (derived: "derived_pred list")

datatype init_asmt = 
  At rat "object atom"
  | NotAt rat "object atom"
  | ObjAsmt func "object list" object
  | NumAsmt func "object list" rat


(* This is used for constraints *)
datatype ('x, atoms: 'a) ltl_form = 
  Atom 'a
| Bot
| Not "('x, 'a) ltl_form"
| And "('x, 'a) ltl_form" "('x, 'a) ltl_form"
| Or "('x, 'a) ltl_form" "('x, 'a) ltl_form"
| Imp "('x, 'a) ltl_form" "('x, 'a) ltl_form"
| ForAll "'x" "('x, 'a) ltl_form"
| AtEnd "('x, 'a) ltl_form"
| Always "('x, 'a) ltl_form"
| SometimeAfter "('x, 'a) ltl_form" "('x, 'a) ltl_form"
| SometimeBefore "('x, 'a) ltl_form" "('x, 'a) ltl_form"
| AlwaysWithin rat "('x, 'a) ltl_form" "('x, 'a) ltl_form"
| HoldDuring rat rat "('x, 'a) ltl_form"
| HoldAfter rat "('x, 'a) ltl_form"

datatype ('x, 'a) pref_con_GD =
  con_GD "('x, 'a) ltl_form"
  | ForAll 'x "('x, 'a) pref_con_GD"
  | And "('x, 'a) pref_con_GD list"
  | Pref pref "('x, 'a) ltl_form"

type_synonym constraint = "((variable \<times> type) list, symbol term atom) pref_con_GD"

datatype metric_f_exp =
  Plus "metric_f_exp" "metric_f_exp"
  | Minus "metric_f_exp" "metric_f_exp"
  | Times "metric_f_exp" "metric_f_exp"
  | Divide "metric_f_exp" "metric_f_exp"
  | Neg "metric_f_exp"
  | Number rat
  | FFun func "object list"
  | IsViolated pref

text \<open>A problem consists of a domain, a list of objects,
  a description of the initial state, and a description of the goal state.\<close>
datatype ast_problem = Problem
  (domain: ast_domain)
  (init_asmts: "init_asmt list")
  (objects: "(object \<times> type) list")
  (goal: "ast_pre_GD")
  (constraints: "constraint list")


subsubsection \<open>Plans\<close>
type_synonym time = rat

datatype plan_action = 
  Simple_Plan_Action (name: name) (arguments: "object list")
| Durative_Plan_Action (name: name) (arguments: "object list") (duration: "time option")

type_synonym plan = "(time \<times> plan_action) list"

end