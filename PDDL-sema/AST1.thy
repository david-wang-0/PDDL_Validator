theory AST1
  imports
  "Automatic_Refinement.Misc"
  "Automatic_Refinement.Refine_Util"
  "Show.Show_Instances" 
  Util
begin
  
type_synonym name = String.literal

datatype pred = Predicate (pred_name: name)

datatype func = Function (fun_name: name)

datatype pref = Preference (pref_name: name)

datatype type = Either (primitives: "name list")

datatype variable = Variable (var_name: name)

datatype object = name: Object (obj_name: name)

datatype symbol = Var variable | Const object

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
| TermEq (lhs: 'ent) (rhs: 'ent)
| Num_Eq "'ent f_exp" "'ent f_exp"
| Num_Le "'ent f_exp" "'ent f_exp"
| Num_Lt "'ent f_exp" "'ent f_exp"


datatype ('x, atoms: 'a) formula = 
  Atom 'a
| Bot
| Not "('x, 'a) formula"
| And "('x, 'a) formula" "('x, 'a) formula"
| Or "('x, 'a) formula" "('x, 'a) formula"
| Imp "('x, 'a) formula" "('x, 'a) formula"
| ForAll "'x" "('x, 'a) formula"

datatype ('x, atoms: 'a) timed_GD =
  OverAll "('x, 'a) formula"
| AtStart "('x, 'a) formula"
| AtEnd "('x, 'a) formula"

datatype ('x, atoms: 'a) da_GD =
  ForAll "'x" "('x, 'a) da_GD"
| And "('x, 'a) da_GD" "('x, 'a) da_GD"
| tGD "('x, 'a) timed_GD"

datatype upd_op = 
  Assign
| ScaleUp
| ScaleDown
| Increase
| Decrease

datatype (ent: 'ent) of_upd = OF_Upd func "'ent list" (ret_val: "'ent option")
datatype (ent: 'ent) nf_upd = NF_Upd upd_op func "'ent list" "'ent f_exp"

datatype 'ent simple_update =
  OU "'ent of_upd"
| NU "'ent nf_upd"
| Add "'ent atom"
| Del "'ent atom"

datatype ('x, 'ent) simple_effect =
  Eff "'ent simple_update"
| Eff_And "('x, 'ent) simple_effect list"
| Eff_All 'x "('x, 'ent) simple_effect"
| Eff_When "('x, 'ent atom) formula" "('x, 'ent) simple_effect"

datatype 'ent f_exp_da =
  Duration
| NFun func (arguments: "'ent list")
| Num rat
| Neg "'ent f_exp_da"
| Add "'ent f_exp_da" "'ent f_exp_da"
| Sub "'ent f_exp_da" "'ent f_exp_da"
| Mult "'ent f_exp_da" "'ent f_exp_da"
| Div "'ent f_exp_da" "'ent f_exp_da"

datatype (ent: 'ent) d_nf_upd = D_NF_Upd upd_op func "'ent list" "'ent f_exp_da"

datatype 'ent durative_update =
  D_Add "'ent atom"
| D_Del "'ent atom"
| D_OU "'ent of_upd"
| D_NU "'ent d_nf_upd"

datatype ('x, 'ent) timed_effect = 
  DUpd_At_Start "'ent durative_update"
| DUpd_At_End "'ent durative_update"
| Eff_At_Start "'ent simple_update list"
| Eff_At_End "'ent simple_update list"

(* Happenings can interfere. Effects can interfere, but conjunction in effects is not commutative.
    Also consider how to handle conditional effects with conditions at the end and effects at the start *)
datatype ('x, 'ent) durative_effect =
  Timed_Effect "('x, 'ent) timed_effect"
| DEff_And "('x, 'ent) durative_effect list" 
| DEff_All 'x "('x, 'ent) durative_effect"
| DEff_When "('x, 'ent atom) da_GD" "('x, 'ent) timed_effect"
  
type_synonym simple_formula_schema = "((variable \<times> type) list, variable term atom) formula"
type_synonym simple_effect_schema = "((variable \<times> type) list, variable term) simple_effect"

datatype simple_action = Simple_Action_Schema
  (name: name)
  (parameters: "(variable \<times> type) list")
  (precondition: simple_formula_schema)
  (effect: simple_effect_schema)

type_synonym durative_formula_schema = "((variable \<times> type) list, variable term atom) da_GD"
type_synonym durative_effect_schema = "((variable \<times> type) list, variable term) durative_effect"

datatype ('ent) duration_constraint = 
  DurLe "'ent f_exp"
| DurGe "'ent f_exp"
| DurEq "'ent f_exp"

datatype durative_action = 
  Durative_Action_Schema 
    (name: name)
    (duration: "variable term duration_constraint")
    (parameters: "(variable \<times> type) list")
    (condition: durative_formula_schema)
    (effect: durative_effect_schema)

datatype action_schema = 
  Simple_Action_Schema simple_action
| Durative_Action_Schema durative_action

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
| ConPref pref "('x, 'a) ltl_form"


datatype applicable_of_upd = AOFU func "object option list" (return_value: "object option")
datatype applicable_nf_upd = ANFU upd_op func "object option list" "rat option"


type_synonym object_function_interpretation = "func \<rightharpoonup> (object list \<rightharpoonup> object)"
type_synonym numeric_function_interpretation = "func \<rightharpoonup> (object list \<rightharpoonup> rat)"

datatype state = State 
  (predicates: "object atom set")
  (of_int: "object_function_interpretation")
  (nf_int: "numeric_function_interpretation")


text \<open>A pred declaration contains the pred's name and its
  argument types.\<close>
datatype pred_decl = PredDecl
  (predicate: pred)
  (argTs: "type list")

datatype obj_func_decl = ObjFunDecl (OFName: func) "type list" type

definition "of_name = fun_name o OFName"


datatype num_func_decl = NumFunDecl (NFName: func) "type list"

definition "nf_name = fun_name o NFName"


datatype ast_domain_decs = DomainDecls
 
type_synonym fact = "pred \<times> object list"

datatype ast_domain = Domain 
  (types: "(name \<times> name) list") \<comment> \<open> \<open>(type, supertype)\<close> declarations. \<close>
  ("consts": "(object \<times> type) list")
  (preds: "pred_decl list")
  (obj_funs: "obj_func_decl list")
  (num_funs: "num_func_decl list")
  (actions: "action_schema list")

text \<open>A problem consists of a domain, a list of objects,
  a description of the initial state, and a description of the goal state.\<close>
datatype ast_problem = Problem
  (domain: ast_domain)
  (init_ps: "object atom list")
  (init_ofs: "(func \<times> object list \<times> object) list")
  (init_nfs: "(func \<times> object list \<times> rat) list")
  (goal: "simple_formula_schema")
  (objects: "(object \<times> type) list")

subsubsection \<open>Plans\<close>
datatype plan_action = PAction
  (name: name)
  (arguments: "object list")

type_synonym plan = "plan_action list"

subsubsection \<open>Ground Actions\<close>

datatype ground_action = Ground_Action
  (condition: "simple_formula_schema")
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


text \<open>\<^term>\<open>f_ent\<close> extracts the entities from a formula. Ent in this context
      are entities to which preds and numeric functions are applied. For instance,
      these could be {@typ object term}s, {@typ object}s, {@typ symbol term}s, etc.\<close>
definition f_ent::"'ent atom formula \<Rightarrow> 'ent set" where
  "f_ent \<phi> = \<Union> (atom.ent ` atoms \<phi>)"

text \<open>Given an {@typ atom} which contains {@typ 'ent term}s, this
      function extracts members of {@typ 'ent}. In the case of {@typ symbol term},
      this would return all {@typ symbol}s in the atom.\<close>
definition atom_syms::"'ent term atom \<Rightarrow> 'ent set" where
  "atom_syms a = \<Union> (sym ` atom.ent a)"

definition f_syms::"'ent term atom formula \<Rightarrow> 'ent set" where
  "f_syms \<phi> = \<Union> (atom_syms ` atoms \<phi>)"

definition f_vars::"simple_formula_schema \<Rightarrow> variable set" where
  "f_vars \<phi> = \<Union> (atom_vars ` atoms \<phi>)" 

definition f_consts::"simple_formula_schema \<Rightarrow> object set" where
  "f_consts \<phi> = \<Union> (atom_consts ` atoms \<phi>)" 

definition f_subst where 
  "f_subst v c \<equiv> map_formula (atom_subst v c)"

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

fun cond_effect_ent::"'ent atom formula \<times> 'ent ast_effect \<Rightarrow> 'ent set" where
  "cond_effect_ent (pre, eff) = f_ent pre \<union> ast_effect.ent eff"

fun cond_effect_vars::"simple_formula_schema \<times> simple_effect_schema \<Rightarrow> variable set" where
  "cond_effect_vars (pre, eff) = f_vars pre \<union> eff_vars eff"

abbreviation map_cond_effect::"('a \<Rightarrow> 'b) \<Rightarrow> 'a atom formula \<times> 'a ast_effect 
  \<Rightarrow> 'b atom formula \<times> 'b ast_effect" where
"map_cond_effect f \<equiv> map_prod (map_formula (map_atom f)) (map_ast_effect f)"


fun cond_effect_subst::"variable \<Rightarrow> object 
  \<Rightarrow> simple_formula_schema \<times> simple_effect_schema 
  \<Rightarrow> simple_formula_schema \<times> simple_effect_schema" where
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

text \<open>The variables in a formula can be rewritten in terms of the
      symbols in the formula.\<close>
lemma f_vars_as_f_syms: "f_vars \<phi> = \<Union> (sym_vars ` f_syms \<phi>)"
  unfolding f_vars_def f_syms_def stav_as_atom_syms
  by blast

lemma f_consts_as_f_syms: "f_consts \<phi> = \<Union> (sym_consts ` f_syms \<phi>)"
  unfolding f_consts_def f_syms_def stao_as_atom_syms
  by blast

text \<open>\<open>ent\<close> in this context refers to the entities to which 
      numeric functions and preds are applied. In the 
      case of {@typ symbol term atom formula}s, these are 
      {@typ symbol term}s. \<^term>\<open>sym\<close> extracts the symbols
      from the terms.\<close>
lemma f_syms_as_f_ent: "f_syms \<phi> = \<Union> (sym ` f_ent \<phi>)"
  unfolding f_ent_def f_syms_def atom_syms_def 
  by blast

text \<open>Since variables must be contained within symbols, we can
      also rewrite the set of variables in a formula in terms
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
  by (auto intro: atom_subst_idem formula.map_ident_strong)

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
  by (simp add: formula.set_map atom_subst_replaces)


end