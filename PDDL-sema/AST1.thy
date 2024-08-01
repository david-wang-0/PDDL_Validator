theory AST1
  imports Main
  "HOL.Rat" 
  Util
begin

(* 
(* This is used for constraints *)
datatype ('x, atoms: 't) ltl_form = 
  Atom 't
| Bot
| Not "('x, 't) ltl_form"
| And "('x, 't) ltl_form" "('x, 't) ltl_form"
| Or "('x, 't) ltl_form" "('x, 't) ltl_form"
| Imp "('x, 't) ltl_form" "('x, 't) ltl_form"
| ForAll "'x" "('x, 't) ltl_form"
| AtEnd "('x, 't) ltl_form"
| Always "('x, 't) ltl_form"
| SometimeAfter "('x, 't) ltl_form" "('x, 't) ltl_form"
| SometimeBefore "('x, 't) ltl_form" "('x, 't) ltl_form"
| AlwaysWithin rat "('x, 't) ltl_form" "('x, 't) ltl_form"
| HoldDuring rat rat "('x, 't) ltl_form"
| HoldAfter rat "('x, 't) ltl_form"

datatype ('x, 't) pref_con_GD =
  con_GD "('x, 't) ltl_form"
  | ForAll 'x "('x, 't) pref_con_GD"
  | And "('x, 't) pref_con_GD list"
  | Pref pref "('x, 't) ltl_form"

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
 *)
  
type_synonym name = string

type_synonym pred = name
type_synonym func = name
type_synonym pref = name


datatype type = Either "name list" | Number

fun primitives::"type \<Rightarrow> name list" where
  "primitives (Either ps) = ps"
| "primitives Number = [''number'']"


datatype variable = Variable (var_name: name)
datatype object = name: Object (obj_name: name)

(* When we parse, we cannot know whether a simple name is an object or function. Thus,
  AST types do not have objects*)
datatype var_num = Var variable | Num rat 
datatype var_num_dur = Var variable | Num rat | Duration

(* Symbols represent one value, which can be determined independently of the state. 
    We cannot directly parse these, because objects and functions (in terms) are just strings.
    Therefore, these only occur after we have checked the function and object type declarations
    for well-formedness and disambiguated terms. *)
datatype instant_symbol = Var variable | Const object | Num rat
datatype symbol = Var variable | Const object | Num rat | Duration

(* When terms are grounded, these are the entities *)
datatype entity = Const object | Num rat


datatype (sym: 'sym) "term" = 
  Sym 'sym
| Fun func (arguments: "'sym term list") 

datatype (ent: 't) atom = 
  Pred (pred: pred) (arguments: "'t list")
| Ent_Eq (lhs: 't) (rhs: 't)
| Num_Le "'t" "'t"
| Num_Lt "'t" "'t"

datatype ('x, ent: 't) GD = 
  Atom "'t atom"
| Bot
| Not "('x, 't) GD"
| And "('x, 't) GD" "('x, 't) GD"
| Or "('x, 't) GD" "('x, 't) GD"
| Imp "('x, 't) GD" "('x, 't) GD"
| ForAll 'x "('x, 't) GD"
| Exists 'x "('x, 't) GD"

datatype ('x, 't) pre_GD =
  PrefGD "pref option" "('x, 't) GD"
| ForAll 'x "('x, 't) pre_GD"
| And "('x, 't) pre_GD" "('x, 't) pre_GD"

datatype ('x, terms: 't) timed_GD =
  OverAll "('x, 't) GD"
| AtStart "('x, 't) GD"
| AtEnd "('x, 't) GD"

datatype ('x, 't) da_GD =
  ForAll "'x" "('x, 't) da_GD"
| And "('x, 't) da_GD" "('x, 't) da_GD"
| PrefTimedGD "pref option" "('x, 't) timed_GD"

datatype upd_op = 
  Assign
| ScaleUp
| ScaleDown
| Increase
| Decrease

datatype (ent: 't) f_upd = Fun_Upd upd_op func "'t list" (ret_val: "'t option")

datatype 't update =
  S_FU "'t f_upd"
| S_Add "'t atom"
| S_Del "'t atom"

datatype ('x, 't) effect =
  Eff "'t update"
| Eff_And "('x, 't) effect list"
| Eff_All 'x "('x, 't) effect"
| Eff_When "('x, 't atom) GD" "('x, 't) effect"

datatype f_exp_t = 
  Time
  | MultTime "var_num term"

datatype 't timed_effect = 
  Upd_At_Start "'t update"
| Upd_At_End "'t update"
| ContScaleUp func "'t list" f_exp_t
| ContScaleDown func "'t list" f_exp_t

datatype ('x, 't) durative_effect =
  Timed_Effect "'t timed_effect"
| DEff_And "('x, 't) durative_effect" "('x, 't) durative_effect" 
| DEff_All 'x "('x, 't) durative_effect"
| DEff_When "('x, 't) da_GD" "'t timed_effect"
  
datatype ('x, 't) simple_action_body = 
  Simple_Action_Body
  (precondition: "('x, 't) pre_GD")
  (effect: "('x, 't) effect option")

type_synonym typed_params = "(variable \<times> type) list"

type_synonym ast_pre_GD = "(typed_params, var_num term) pre_GD"
type_synonym ast_simple_effect = "(typed_params, var_num term) effect"
type_synonym ast_simple_action_body = "(typed_params, var_num term) simple_action_body"

datatype 't timed_atom =
  AtStart "'t atom"
  | AtEnd "'t atom"

type_synonym 't duration_constraint = "'t term timed_atom"

type_synonym ast_duration_constraint = "var_num_dur duration_constraint"
type_synonym ast_da_GD = "(typed_params, var_num term) da_GD"
type_synonym ast_durative_effect = "(typed_params, var_num_dur term) durative_effect"

datatype ast_durative_action_body = 
  DA_Body 
    (duration: "ast_duration_constraint list")
    (condition: "ast_da_GD")
    (effect: "ast_durative_effect")

datatype ('s, 'd) action_body =
  SA 's
  | DA 'd

type_synonym ast_action_body = 
  "(ast_simple_action_body, ast_durative_action_body) action_body"

datatype 'b action = 
  Action (name: name)
    (parameters: "typed_params") 
    (body: 'b)

type_synonym ast_action = "ast_action_body action"

datatype pred_decl = PredDecl
  (predicate: pred)
  (argTs: "type list")

datatype fun_decl = FunDecl (f_name: func) "type list" type

datatype derived_pred = 
  DerivedPred pred (params: "typed_params") ast_pre_GD

datatype ast_domain = Domain 
  (types: "(name \<times> name) list") \<comment> \<open> \<open>(type, supertype)\<close> declarations. \<close>
  ("consts": "(object \<times> type) list")
  (preds: "pred_decl list")
  (funs: "fun_decl list")
  (actions: "ast_action list")
(*   (derived: "derived_pred list") *)
(*   (constraints: "constraint list") *)

datatype init_asmt = 
  At rat "object atom"
  | NotAt rat "object atom"
  | FunAsmt func "object list" entity

text \<open>A problem consists of a domain, a list of objects,
  a description of the initial state, and a description of the goal state.\<close>
datatype ast_problem = Problem
  (domain: ast_domain)
  (init_asmts: "init_asmt list")
  (objects: "(object \<times> type) list")
  (goal: "ast_pre_GD")
(*   (constraints: "constraint list") *)


subsubsection \<open>Plans\<close>
type_synonym time = rat

datatype plan_action = 
  Simple_Plan_Action (name: name) (arguments: "object list")
| Durative_Plan_Action (name: name) (arguments: "object list") (duration: "time")

type_synonym plan = "(time \<times> plan_action) list"

(* 
subsubsection \<open>Ground Actions\<close>

datatype ground_action = Ground_Action
  (condition: "pre_GD_form")
  (effects: "(sim \<times> ground_effect) list")

subsubsection \<open>Utility functions\<close>
text \<open>These utility functions help extract deeply embedded terms from
      other deeply embedded types. As we will see in a latter section, their usage 
      leads to elegant proofs regarding well-formedness conditions and preservation
      under different type environments and following syntax transformations.

      Most of these use helper functions generated by the datatype package.\<close>

text \<open>The variables in a symbol\<close>
fun sym_vars where
  "sym_vars (Var x) = {x}" 
| "sym_vars (Const c) = {}"

text \<open>The variables present in a term, in which non-functional entities
      are symbols.\<close>
definition term_vars::"symbol term \<Rightarrow> variable set" where
  "term_vars t \<equiv> \<Union> (sym_vars ` sym t)"

text \<open>A numeric fluent, in which the entities are terms also contains variables.\<close>
definition nf_vars where
  "nf_vars nf \<equiv> \<Union> (term_vars ` f_exp.ent nf)"

text \<open>A numeric comparison contains variables\<close>
definition nc_vars::"symbol term num_comp \<Rightarrow> variable set" where
  "nc_vars nc \<equiv> \<Union> (term_vars ` num_comp.ent nc)"

text \<open>Etc.\<close>
definition predicate_vars where
  "predicate_vars p \<equiv> \<Union> (term_vars ` predicate.ent p)"

definition atom_vars::"symbol term atom \<Rightarrow> variable set" where
  "atom_vars a \<equiv> \<Union> (term_vars ` atom.ent a)"

definition of_upd_vars::"symbol term of_upd \<Rightarrow> variable set" where
  "of_upd_vars tu = \<Union> (term_vars ` of_upd.ent tu)"

definition nf_upd_vars::"symbol term nf_upd \<Rightarrow> variable set" where
  "nf_upd_vars nu = \<Union> (term_vars ` nf_upd.ent nu)"


text \<open>The same functions but applied to constants/objects\<close>
fun sym_consts where
  "sym_consts (Var x) = {}"
| "sym_consts (Const obj) = {obj}"

definition term_consts::"symbol term \<Rightarrow> object set" where
  "term_consts t \<equiv> \<Union> (sym_consts ` sym t)"

definition nf_consts where
  "nf_consts nf \<equiv> \<Union> (term_consts ` f_exp.ent nf)"

definition nc_consts::"symbol term num_comp \<Rightarrow> object set" where
  "nc_consts nc \<equiv> \<Union> (term_consts ` num_comp.ent nc)"

definition predicate_consts where
  "predicate_consts p \<equiv> \<Union> (term_consts ` p)"

definition atom_consts::"symbol term atom \<Rightarrow> object set" where
  "atom_consts a \<equiv> \<Union> (term_consts ` atom.ent a)"

definition of_upd_consts::"symbol term of_upd \<Rightarrow> object set" where
  "of_upd_consts tu = \<Union> (term_consts ` of_upd.ent tu)"

definition nf_upd_consts::"symbol term nf_upd \<Rightarrow> object set" where
  "nf_upd_consts nu = \<Union> (term_consts ` nf_upd.ent nu)"

fun sym_subst::"variable \<Rightarrow> object \<Rightarrow> symbol \<Rightarrow> symbol" where
  "sym_subst v obj (Var x) = (if (x = v) then (Const obj) else Var x)" 
| "sym_subst _ _ (Const obj) = Const obj"


text \<open>Substitution of variables by constants. Used for quantifiers.\<close>
definition term_subst::"variable \<Rightarrow> object \<Rightarrow> symbol term \<Rightarrow> symbol term" where
  "term_subst v obj \<equiv> map_term (sym_subst v obj)"

definition sym_term_nf_subst::"variable \<Rightarrow> object \<Rightarrow> symbol term f_exp \<Rightarrow> symbol term f_exp" where
  "sym_term_nf_subst v obj \<equiv> map_f_exp (term_subst v obj)"

definition sym_term_nc_subst::"variable \<Rightarrow> object \<Rightarrow> symbol term num_comp \<Rightarrow> symbol term num_comp" where
  "sym_term_nc_subst v c \<equiv> map_num_comp (term_subst v c)"

definition sym_term_predicate_subst where
  "sym_term_predicate_subst v c \<equiv> map_predicate (term_subst )"

definition atom_subst::"variable \<Rightarrow> object \<Rightarrow> symbol term atom \<Rightarrow> symbol term atom" where
  "atom_subst v c \<equiv> map_atom (term_subst v c)"

definition ast_effect_subst where
"ast_effect_subst v c = map_ast_effect (term_subst v c)"


text \<open>\<^term>\<open>f_ent\<close> extracts the entities from a GD. Ent in this context
      are entities to which preds and numeric functions are applied. For instance,
      these could be {@typ object term}s, {@typ object}s, {@typ symbol term}s, etc.\<close>
definition f_ent::"'t atom GD \<Rightarrow> 't set" where
  "f_ent \<phi> = \<Union> (atom.ent ` atoms \<phi>)"

text \<open>Given an {@typ atom} which contains {@typ 't term}s, this
      function extracts members of {@typ 't}. In the case of {@typ symbol term},
      this would return all {@typ symbol}s in the atom.\<close>
definition atom_syms::"'t term atom \<Rightarrow> 't set" where
  "atom_syms a = \<Union> (sym ` atom.ent a)"

definition f_syms::"'t term atom GD \<Rightarrow> 't set" where
  "f_syms \<phi> = \<Union> (atom_syms ` atoms \<phi>)"

definition f_vars::"pre_GD_form \<Rightarrow> variable set" where
  "f_vars \<phi> = \<Union> (atom_vars ` atoms \<phi>)" 

definition f_consts::"pre_GD_form \<Rightarrow> object set" where
  "f_consts \<phi> = \<Union> (atom_consts ` atoms \<phi>)" 

definition f_subst where 
  "f_subst v c \<equiv> map_GD (atom_subst v c)"

fun eff_vars::"simple_effect_schema \<Rightarrow> variable set" where
  "eff_vars (Effect a d tu nu) = 
      \<Union> (predicate_vars ` (set a)) 
    \<union> \<Union> (predicate_vars ` (set d)) 
    \<union> \<Union> (of_upd_vars ` (set tu)) 
    \<union> \<Union> (nf_upd_vars ` (set nu))"

definition predicate_syms where
  "predicate_syms p = \<Union> (sym ` predicate.ent p)"

definition of_upd_syms where
  "of_upd_syms u = \<Union> (sym ` of_upd.ent u)"

definition nf_upd_syms where
  "nf_upd_syms u = \<Union> (sym ` nf_upd.ent u)"

fun eff_syms::"simple_effect_schema \<Rightarrow> symbol set" where
  "eff_syms (Effect a d tu nu) = 
    \<Union> (predicate_syms ` (set a))
  \<union> \<Union> (predicate_syms ` (set d))
  \<union> \<Union> (of_upd_syms ` (set tu))
  \<union> \<Union> (nf_upd_syms ` (set nu))"

fun cond_effect_ent::"'t atom GD \<times> 't ast_effect \<Rightarrow> 't set" where
  "cond_effect_ent (pre, eff) = f_ent pre \<union> ast_effect.ent eff"

fun cond_effect_vars::"pre_GD_form \<times> simple_effect_schema \<Rightarrow> variable set" where
  "cond_effect_vars (pre, eff) = f_vars pre \<union> eff_vars eff"

abbreviation map_cond_effect::"('t \<Rightarrow> 'b) \<Rightarrow> 't atom GD \<times> 't ast_effect 
  \<Rightarrow> 'b atom GD \<times> 'b ast_effect" where
"map_cond_effect f \<equiv> map_prod (map_GD (map_atom f)) (map_ast_effect f)"


fun cond_effect_subst::"variable \<Rightarrow> object 
  \<Rightarrow> pre_GD_form \<times> simple_effect_schema 
  \<Rightarrow> pre_GD_form \<times> simple_effect_schema" where
"cond_effect_subst v c (pre, eff) = 
  (f_subst v c pre, ast_effect_subst v c eff)"

lemma cond_effect_subst_alt: "cond_effect_subst v c = map_cond_effect (term_subst v c)"
  apply (rule ext)
  subgoal for x 
    apply (cases x)
    using f_subst_def atom_subst_def ast_effect_subst_def term_subst_def
    by simp
  done

  
text \<open>The variables in an atom which contains {@typ symbol term}s at the lowest
      level can be rewritten in terms of the symbols in the atom. \<close>
lemma stav_as_atom_syms: "atom_vars a = \<Union> (sym_vars ` atom_syms a)"
  unfolding atom_vars_def atom_syms_def term_vars_def
  by blast

lemma stao_as_atom_syms: "atom_consts a = \<Union> (sym_consts ` atom_syms a)"
  unfolding atom_consts_def atom_syms_def term_consts_def
  by blast

text \<open>The variables in a GD can be rewritten in terms of the
      symbols in the GD.\<close>
lemma f_vars_as_f_syms: "f_vars \<phi> = \<Union> (sym_vars ` f_syms \<phi>)"
  unfolding f_vars_def f_syms_def stav_as_atom_syms
  by blast

lemma f_consts_as_f_syms: "f_consts \<phi> = \<Union> (sym_consts ` f_syms \<phi>)"
  unfolding f_consts_def f_syms_def stao_as_atom_syms
  by blast

text \<open>\<open>ent\<close> in this context refers to the entities to which 
      numeric functions and preds are applied. In the 
      case of {@typ symbol term atom GD}s, these are 
      {@typ symbol term}s. \<^term>\<open>sym\<close> extracts the symbols
      from the terms.\<close>
lemma f_syms_as_f_ent: "f_syms \<phi> = \<Union> (sym ` f_ent \<phi>)"
  unfolding f_ent_def f_syms_def atom_syms_def 
  by blast

text \<open>Since variables must be contained within symbols, we can
      also rewrite the set of variables in a GD in terms
      of the entities (in this case {@typ symbol term}s).\<close>
lemma f_vars_as_f_ent: "f_vars \<phi> = \<Union> (term_vars ` f_ent \<phi>)"
  unfolding f_syms_as_f_ent f_vars_as_f_syms f_vars_def term_vars_def 
  by blast

text \<open>Similarly, we can extract variables and symbols from effects.\<close>
lemma eff_syms_as_eff_ent: "eff_syms eff = \<Union> (sym ` ast_effect.ent eff)"
  by (induction eff; simp add: predicate_syms_def of_upd_syms_def nf_upd_syms_def)
  
lemma eff_vars_as_eff_syms: "eff_vars eff = \<Union> (sym_vars ` eff_syms eff)"
  by (induction eff; simp add: predicate_vars_def of_upd_vars_def nf_upd_vars_def eff_syms_as_eff_ent term_vars_def)

lemma eff_vars_as_eff_ent: "eff_vars eff = \<Union> (term_vars ` ast_effect.ent eff)"
  by (induction eff; simp add: eff_vars_as_eff_syms eff_syms_as_eff_ent term_vars_def)

text \<open>When a variable is not present, the substition of it is an idempotent operation\<close>
lemma sym_subst_idem:
  assumes "v \<notin> sym_vars s"
  shows "sym_subst v c s = s"
  using assms by (cases s; auto)

lemma term_subst_idem:
  assumes "v \<notin> term_vars t"
  shows "term_subst v c t = t"
  using assms 
  by (induction t; auto simp: term_vars_def term_subst_def intro: sym_subst_idem map_idI)

lemma atom_subst_idem:
  assumes "v \<notin> atom_vars a"
  shows "atom_subst v c a = a"
  using assms
  unfolding atom_vars_def atom_subst_def
  by (auto intro: term_subst_idem atom.map_ident_strong)

lemma f_subst_idem:
  assumes "v \<notin> f_vars \<phi>"
  shows "f_subst v c \<phi> = \<phi>"
  using assms 
  unfolding f_vars_def f_subst_def
  by (auto intro: atom_subst_idem GD.map_ident_strong)

text \<open>Substitution ensures that a variable is no longer present\<close>
lemma sym_subst_replaces:
  "v \<notin> sym_vars (sym_subst v c s)"
  by (cases s; auto)

lemma sym_subst_v:
  assumes "v \<in> sym_vars s"
  shows "sym_subst v c s = Const c"
  using assms
  by (cases s; simp)

lemma term_subst_replaces:
  "v \<notin> term_vars (term_subst v c t)"
  unfolding term_vars_def term_subst_def
  by (simp add: term.set_map sym_subst_replaces)

lemma atom_subst_replaces:
  "v \<notin> atom_vars (atom_subst v c a)"
  unfolding atom_vars_def atom_subst_def
  by (simp add: atom.set_map term_subst_replaces)

lemma f_subst_replaces:
  "v \<notin> f_vars (f_subst v c \<phi>)"
  unfolding f_vars_def f_subst_def
  by (simp add: GD.set_map atom_subst_replaces)
 *)

end