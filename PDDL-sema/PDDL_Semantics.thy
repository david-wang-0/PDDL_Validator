section \<open>PDDL Semantics\<close>
theory PDDL_Semantics
imports
  "Propositional_Proof_Systems.Formulas"
  "Propositional_Proof_Systems.Sema"
  "Automatic_Refinement.Misc"
  "Automatic_Refinement.Refine_Util"
  "Show.Show_Instances" 
  Util
begin

text \<open>This formalisation contains a subset of PDDL with a similar expressiveness to 
      functional STRIPS. Compared to classical STRIPS-like planning, this formalisation adds
      functions and numeric terms. As mentioned by Geffner, this brings the benefit of a reduction 
      in the number of ground actions. Moderns planners work by grounding, i.e. instantiating actions
      with all possible (or probable) arguments and computing a state-transition diagram. A functional
      language reduces the number of possible ground actions and thus improves the efficiency of
      a planner. 
      
      However, this functional extension to STRIPS and this plan-validator have some limitations.
      The main limitation lies in the method by which quantified formulas and effects are treated.
      These are implemented as macro-expansions, in which terms are instantiated by all plausible
      members of the domain, leading to an exponential growth in formula/effect size and therefore
      run-time with respect to quantifier nesting depth.

      Another limitation is that functions can never take numeric arguments. This corresponds to 
      the limitations imposed upon the syntax by the BNF definition of the grammar of PDDL 3.1
      (cite Kovacs). 
      \<close> (* TODO: is this really that expressive? *)

no_notation insert ("_ \<triangleright> _" [56,55] 55)

subsection \<open>Utility Functions\<close>
definition "index_by f l \<equiv> map_of (map (\<lambda>x. (f x,x)) l)"

lemma index_by_eq_Some_eq[simp]:
  assumes "distinct (map f l)"
  shows "index_by f l n = Some x \<longleftrightarrow> (x\<in>set l \<and> f x = n)"
  unfolding index_by_def
  using assms
  by (auto simp: o_def)

lemma index_by_eq_SomeD:
  shows "index_by f l n = Some x \<Longrightarrow> (x\<in>set l \<and> f x = n)"
  unfolding index_by_def
  by (auto dest: map_of_SomeD)


lemma lookup_zip_idx_eq:
  assumes "length params = length args"
  assumes "i<length args"
  assumes "distinct params"
  assumes "k = params ! i"
  shows "map_of (zip params args) k = Some (args ! i)"
  using assms
  by (auto simp: in_set_conv_nth)

lemma rtrancl_image_idem[simp]: "R\<^sup>* `` R\<^sup>* `` s = R\<^sup>* `` s"
  by (metis relcomp_Image rtrancl_idemp_self_comp)

lemma map_le_restr: "Q \<subseteq>\<^sub>m R \<Longrightarrow> S \<subseteq> dom Q \<Longrightarrow> Q |` S = R |` S"
  unfolding restrict_map_def map_le_def
  by fastforce

lemma map_restrict_mono: "S \<subseteq> T \<Longrightarrow> M |` S \<subseteq>\<^sub>m M |` T"
  unfolding map_le_def restrict_map_def
  by auto

lemma map_restrict_less: "Q |` S \<subseteq>\<^sub>m Q"
  unfolding map_le_def restrict_map_def
  by auto

abbreviation flatten where
  "flatten xs \<equiv> foldr append xs []"

value "flatten [[1::nat],[2],[3]]"

abbreviation flatmap where
 "flatmap f xs \<equiv> flatten (map f xs)"

value "flatmap (\<lambda>x. [x, 1::nat]) [1, 2, 3]"

subsection \<open>Important definitions\<close>

text \<open>
\begin{itemize}
    \item Deeply embedded types (e.g. {@typ object}, {@typ variable},
      {@typ term}, {@typ ast_effect}, {@typ formula}, etc.): These are terms/types
      in Isabelle
    \item Shallow types: represented by the {@typ type} type are types according to PDDL.
    \item Syntax transformation: A transformation of a term of a deeply embedded type to a term of another deeply-embedded type.
    \item Type-environment: A map from a term of a deeply-embedded type to a shallow {@typ type}.
\end{itemize}
\<close>

subsection \<open>Abstract Syntax\<close>
subsubsection \<open>Deeply embedded types\<close>
type_synonym name = string

datatype pred = Predicate (pred_name: name)
datatype pred = Predicate (pred_name: name)

datatype func = Function (fun_name: name)

datatype func = Function (fun_name: name)


text \<open>The terms and types we use have been to reflect the BNF grammar 
  of PDDL's syntax defined by Kovacs.\<close>

text \<open>Variables are identified by their names.\<close>
datatype variable = varname: Variable name

text \<open>Objects and constants are identified by their names.\<close>
datatype object = name: Object (obj_name: name)

text \<open>\<^term>\<open>symbol\<close>s correspond to variables (\<open>?variable\<close>) present
      in terms/formulas/etc. or objects declared in PDDL domains.\<close>
datatype symbol = Var variable | Const object

text \<open>This formalisation does not support numeric fluents or durative
      actions. However, the implementation of term-valued functions
      is somewhat interesting.\<close>

text \<open>A term can either be a symbol/entity or a function application,
      which represents a symbol/entity.\<close>
datatype (sym: 'sym) "term" = 
  Sym 'sym
| Fun func (arguments: "'sym term list") 

text \<open>A numeric fluent represents either a number, a number-valued function
    application or an arithmetic operation.\<close>
datatype (ent: 'ent) num_fluent = 
    NFun func (arguments: "'ent list")
  | Num rat
  | Add "'ent num_fluent" "'ent num_fluent"
  | Sub "'ent num_fluent" "'ent num_fluent"
  | Mult "'ent num_fluent" "'ent num_fluent"
  | Div "'ent num_fluent" "'ent num_fluent"

text \<open>A comparison operation can be applied to a numeric fluent\<close>
datatype (ent: 'ent) num_comp =
    Num_Eq "'ent num_fluent" "'ent num_fluent"
  | Num_Le "'ent num_fluent" "'ent num_fluent"
  | Num_Lt "'ent num_fluent" "'ent num_fluent"

text \<open>\<^term>\<open>predicate\<close> is used to model pred application to and equality of 
    entities (or terms/fluents, which evaluate to entities)\<close>
datatype (ent: 'ent) predicate = 
    Pred (pred: pred) (arguments: "'ent list")
    | Eq (lhs: 'ent) (rhs: 'ent)

text \<open>An atom is either a pred with arguments, or an equality statement.\<close>

datatype (ent: 'ent) atom = 
    PredAtom "'ent predicate"
  | NumComp "'ent num_comp"



text \<open>Some of the AST entities are defined over a polymorphic {@typ} type,
  which gets either instantiated by symbols or objects or terms of symbols or objects.
  A parsed domain has entities populated by {@typ term}s of {@typ symbol} type.
  
  Before a term can be evaluated in a world-state, its variables must be replaced
  by specific instances of objects. Therefore {@typ symbol}s must be replaced
  by {@typ object}s in formulas, preds, etc. This is what we will from now on refer to as a \emph{syntax transformation}.
  The evaluation of {@typ object term}s requires another syntax transformation
  to {@typ object}. Once we have substituted every term with the entity that it 
  evaluates to, we can evaluated preds and comparisons and numeric functions.
\<close>

text \<open>For instance, in this blocks world domain, we have the following function:\<close>


text \<open>A type is a list of primitive type names.
  To model a primitive type, we use a singleton list.\<close>
datatype type = Either (primitives: "name list")

text \<open>The operators used to model updates to numerical functions. Since we do not
      have durative effects, these are applied instantaneously with respect to the
      current value.\<close>
datatype upd_op = 
    Assign
  | ScaleUp
  | ScaleDown
  | Increase
  | Decrease

text \<open>An effect modifies the objects for which a pred holds as well
      as the return values of functions for argument lists. The assignment of 
      the return value to {@typ undefined} is implicitly modelled as \<^term>\<open>option.None\<close>.
      This simplifies the semantics of expression evaluation significantly compared to 
      the explicit usage of \<^term>\<open>undefined\<close>.

      One major benefit of this design decision is that the only location in which
      an undefined value might occur is syntactically enforced as the assignment of a 
      return value for a function application.\<close>

(* Put this into a locale *)
datatype (ent: 'ent) of_upd = OF_Upd func "'ent list" (ret_val: "'ent option")
datatype (ent: 'ent) nf_upd = NF_Upd upd_op func "'ent list" "'ent num_fluent"
(* replace the operator with cases in a datatype? *)

text \<open>We never have more than one operation encoded in a single effect. I did not think about 
  realistic restrictions of the grammar. I assumed that this is a \<open>cond_effect\<close>. I did not manage to
  represent this cleanly in the types used in the ML code. Therefore when those are converted to 
  these effects, we only get one update, unless we implement another conversion. This is difficult
  and (to me at least) the transformation from PDDL to this would then be too complex to be apparent.
  A weakness of this approach is reflected in the non-interference of effects. In the previous version,
  additions overrode deletions for an entire effect. Therefore the order of applying these partial
  effects inherently makes a difference. To remedy this, we just say that additions cannot intersect
  with deletions.\<close>
datatype (ent: 'ent) ast_effect = 
  Effect  (adds: "('ent predicate) list") 
          (dels: "('ent predicate) list")
          (of_upds: "('ent of_upd) list")
          (nf_upds: "('ent nf_upd) list")

text \<open>{@typ schematic_formula}s represent formulas that are used in action schemas.
      Action schemas model generic actions applied to arbitrary (sometimes typed) arguments,
      and thus require the presence of variables within terms. Effects can also contain variables
      and thus {@typ schematic_effect}s are of {@typ symbol term ast_effect}. 

      A benefit of this representation is that we can model any quantified formula and universal
      effect within a closed world as a macro expansion. See \cref{sec: Quantified Formulas and Effects}.

      When an action is executed against a specific list of arguments, we first instantiate the variables with specific members
      of the domain (objects) and then evaluate the object terms \cref{subsec:quant_form_eff}\<close>
type_synonym schematic_formula = "symbol term atom formula"
type_synonym schematic_effect = "symbol term ast_effect"

text \<open>{@typ ground_formula}s and {@typ ground_effect}s are those which have had their variables
      substituted for objects.\<close>
type_synonym ground_formula = "object term atom formula"
type_synonym ground_effect = "object term ast_effect"

text \<open>The types used to model fully instantiated effects. \<open>adds\<close> and \<open>dels\<close> 
      are lists of preds, which are added/removed from the set of true preds.
      
      Another benefit of our decision to model assignments of \<open>undefined\<close> to
      return values as {@typ option} can be seen here. When a term, pred,
      etc. is evaluated against a world model and a function returns \<open>undefined\<close>, 
      the semantics enforce that preds in which the term occurs evaluate to \<^term>\<open>None\<close>.
      Therefore we can explicitly deal with undefined at the level of effects. 
      See \cref{subsec:quant_form_eff}. This is also why we require another type to
      model these.

      This decision simplifies the well-formedness checks.\<close>

(* I think not changing the type that represents the not fully instantiated updates is a good choice:
  - I considered changing it to have two type parameters
    - This would mean that the whole line of reasoning regarding the preservation of well-formedness 
      must be restated, because there is no longer a simple way to extract all ('ent instances)
  TODO: Can you force a type constraint like this with dependent types?
*)
datatype instantiated_of_upd = OFU func "object option list" (return_value: "object option")
datatype instantiated_nf_upd = NFU upd_op func "object option list" "rat option"

datatype fully_instantiated_effect =
  Eff (eff_adds: "(object predicate option) list")
      (eff_dels: "(object predicate option) list")
      (ous: "instantiated_of_upd list")
      (nus: "instantiated_nf_upd list")


subsubsection \<open>Domains\<close>

text \<open>An action schema has a name, a typed parameter list, a precondition,
  and a list of conditional effects consisting of a pairs of a precondition
  and an effect each.\<close>
datatype ast_action_schema = Action_Schema
  (name: name)
  (parameters: "(variable \<times> type) list")
  (precondition: "schematic_formula")
  (effects: "(schematic_formula \<times> schematic_effect) list")

text \<open>A world model is required to interpret the value of functions and preds.
      \<open>predicates\<close> represents the set of true preds at a state of the world. Under 
      the closed-world assumption, every pred not present in this set is false.
      \<open>of_int\<close> (\emph{object function interpretation}) maps a function's name to a valuation 
      for various argument lists. \<open>nf_int\<close> (\emph{numeric function interpretation} maps a function's
      name to a valuation for argument lists. Numeric functions return rational numbers.\<close>


type_synonym object_function_interpretation = "func \<rightharpoonup> (object list \<rightharpoonup> object)"

type_synonym numeric_function_interpretation = "func \<rightharpoonup> (object list \<rightharpoonup> rat)"

datatype world_model = World_Model 
  (predicates: "object predicate set")
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


text \<open>A domain contains the declarations of primitive types, preds,
  and action schemas.\<close>

datatype ast_domain_decs = DomainDecls
  (types: "(name \<times> name) list") \<comment> \<open> \<open>(type, supertype)\<close> declarations. \<close>
  ("consts": "(object \<times> type) list")
  (preds: "pred_decl list")
  (obj_funs: "obj_func_decl list")
  (num_funs: "num_func_decl list")


subsubsection \<open>Problems\<close>

text \<open>A fact is a pred applied to objects.\<close>
type_synonym fact = "pred \<times> object list"

text \<open>Declarations of objects and an initial state in the problem.
      The \<close>
datatype ast_problem_decs = ProbDecls
  (domain_decs: ast_domain_decs)
  (objects: "(object \<times> type) list")

text \<open>In addition to the declaration of types, preds, and constants, 
      a domain contains actions\<close>
datatype ast_domain = Domain
  (problem_decs: ast_problem_decs)
  (actions: "ast_action_schema list")

text \<open>A problem consists of a domain, a list of objects,
  a description of the initial state, and a description of the goal state.\<close>
datatype ast_problem = Problem
  (domain: ast_domain)
  (init_ps: "object predicate list")
  (init_ofs: "(func \<times> object list \<times> object) list")
  (init_nfs: "(func \<times> object list \<times> rat) list")
  (goal: "schematic_formula")

subsubsection \<open>Plans\<close>
datatype plan_action = PAction
  (name: name)
  (arguments: "object list")

type_synonym plan = "plan_action list"

subsubsection \<open>Ground Actions\<close>
text \<open>The following datatype represents an action schema that has been
  instantiated by replacing the variable arguments with concrete objects.\<close>

datatype ground_action = Ground_Action
  (precondition: "ground_formula")
  (effects: "(ground_formula \<times> ground_effect) list")

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
  "nf_vars nf \<equiv> \<Union> (term_vars ` num_fluent.ent nf)"

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
  "nf_consts nf \<equiv> \<Union> (term_consts ` num_fluent.ent nf)"

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

definition sym_term_nf_subst::"variable \<Rightarrow> object \<Rightarrow> symbol term num_fluent \<Rightarrow> symbol term num_fluent" where
  "sym_term_nf_subst v obj \<equiv> map_num_fluent (term_subst v obj)"

definition sym_term_nc_subst::"variable \<Rightarrow> object \<Rightarrow> symbol term num_comp \<Rightarrow> symbol term num_comp" where
  "sym_term_nc_subst v c \<equiv> map_num_comp (term_subst v c)"

definition sym_term_predicate_subst where
  "sym_term_predicate_subst v c \<equiv> map_predicate (term_subst )"

definition atom_subst::"variable \<Rightarrow> object \<Rightarrow> symbol term atom \<Rightarrow> symbol term atom" where
  "atom_subst v c \<equiv> map_atom (term_subst v c)"

definition ast_effect_subst where
"ast_effect_subst v c = map_ast_effect (term_subst v c)"


text \<open>\<^term>\<open>f_ent\<close> extracts the entities from a formula. Symities in this context
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

definition f_vars::"schematic_formula \<Rightarrow> variable set" where
  "f_vars \<phi> = \<Union> (atom_vars ` atoms \<phi>)" 

definition f_consts::"schematic_formula \<Rightarrow> object set" where
  "f_consts \<phi> = \<Union> (atom_consts ` atoms \<phi>)" 

definition f_subst where 
  "f_subst v c \<equiv> map_formula (atom_subst v c)"

fun eff_vars::"schematic_effect \<Rightarrow> variable set" where
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

fun eff_syms::"schematic_effect \<Rightarrow> symbol set" where
  "eff_syms (Effect a d tu nu) = 
    \<Union> (predicate_syms ` (set a))
  \<union> \<Union> (predicate_syms ` (set d))
  \<union> \<Union> (of_upd_syms ` (set tu))
  \<union> \<Union> (nf_upd_syms ` (set nu))"

fun cond_effect_ent::"'ent atom formula \<times> 'ent ast_effect \<Rightarrow> 'ent set" where
  "cond_effect_ent (pre, eff) = f_ent pre \<union> ast_effect.ent eff"

fun cond_effect_vars::"schematic_formula \<times> schematic_effect \<Rightarrow> variable set" where
  "cond_effect_vars (pre, eff) = f_vars pre \<union> eff_vars eff"

abbreviation map_cond_effect::"('a \<Rightarrow> 'b) \<Rightarrow> 'a atom formula \<times> 'a ast_effect 
  \<Rightarrow> 'b atom formula \<times> 'b ast_effect" where
"map_cond_effect f \<equiv> map_prod (map_formula (map_atom f)) (map_ast_effect f)"


fun cond_effect_subst::"variable \<Rightarrow> object 
  \<Rightarrow> schematic_formula \<times> schematic_effect 
  \<Rightarrow> schematic_formula \<times> schematic_effect" where
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


(* To do: prove that the substitution function for effects replaces variables *)

subsection \<open>Semantics of terms\<close>
text \<open>\<open>undefined\<close> is interpreted as nothing. Due to the limitation imposed upon
        the syntax by Kovac's definition of PDDL 3.1's grammar in BNF, we know
        that \<open>undefined\<close> can only occur in the assignment of a return value for
        a term-valued function. Therefore, the decision was made to not model
        \<open>undefined\<close> as a member of a deeply embedded type. 

        One limitation here, is the fact that any pred application and equality check
        with \<^term>\<open>undefined\<close> as argument will return false.
        The semantics of an existential preconditions is thus not 
        as we might expect. Rather than \<^term>\<open>P undefined \<Longrightarrow> \<exists>x. P x\<close>, any
        formula containing \<open>undefined\<close> will evaluate to false.
        
        \<close>

lemma "P undefined \<Longrightarrow> \<exists>x. P x"
  by blast

text \<open>Here, we evaluate an {@typ object term} against world-model to
    find the object which it represents. If any argument is undefined, then
    the return value is undefined (i.e. \<^term>\<open>option.None\<close>).
    
    Moreover, this function is used for the full instantiation
    of ground effects into applicable effects. The definition of this
    functions brings benefits in that use-case (see \cref{subsec:wf_full_inst})
    \<close>
  fun term_val::"world_model \<Rightarrow> object term \<Rightarrow> object option" where
    "term_val M (Sym obj) = Some obj"
  | "term_val M (Fun fun as) = (case (of_int M fun) of
      Some f \<Rightarrow> (let arg_vals = map (\<lambda>t. term_val M t) as
        in (if (list_all (\<lambda>x. x \<noteq> None) arg_vals) 
            then f (map the arg_vals) else None))
    | None \<Rightarrow> None)"

  text \<open>We evaluate a numeric fluent's value with respect to a world-model.
        When \<close>
  fun nf_val::"world_model \<Rightarrow> (object term) num_fluent \<Rightarrow> rat option" where
    "nf_val M (NFun fun as) = (case (nf_int M fun) of 
      Some f  \<Rightarrow> (let arg_vals = map (\<lambda>t. term_val M t) as
        in (if (list_all (\<lambda>x. x \<noteq> None) arg_vals) 
            then f (map the arg_vals) else None)) 
    | None    \<Rightarrow> None)"
  | "nf_val M (Num n) = Some n"
  | "nf_val M (Add x y) = (combine_options plus (nf_val M x) (nf_val M y))"
  | "nf_val M (Sub x y) = (combine_options minus (nf_val M x) (nf_val M y))"
  | "nf_val M (Mult x y) = (combine_options times (nf_val M x) (nf_val M y))"
  | "nf_val M (Div x y) = (
      let 
        x' = nf_val M x;
        y' = nf_val M y
      in 
      if (y' = Some 0) 
      then None 
      else combine_options divide x' y')"
                             
  value "divide (rat_of_int 10) 3" 

  fun nc_val::"world_model \<Rightarrow> object term num_comp \<Rightarrow> bool" where
    "nc_val M (Num_Eq x y) = (case (nf_val M x, nf_val M y) of
      (Some x, Some y)  \<Rightarrow> x = y | _ \<Rightarrow> False)"
  | "nc_val M (Num_Le x y) = (case (nf_val M x, nf_val M y) of
      (Some x, Some y)  \<Rightarrow> x \<le> y | _ \<Rightarrow> False)"
  | "nc_val M (Num_Lt x y) = (case (nf_val M x, nf_val M y) of
      (Some x, Some y)  \<Rightarrow> x < y | _ \<Rightarrow> False)"

  text \<open>We have to make sure that the arguments are not undefined.\<close>
  fun predicate_inst::"world_model \<Rightarrow> (object term) predicate \<Rightarrow> object predicate option" where
    "predicate_inst M (Pred p as) = (let arg_vals = map (\<lambda>t. term_val M t) as
        in (if (list_all (\<lambda>x. x \<noteq> None) arg_vals) 
            then Some (Pred p (map the arg_vals)) 
            else None))"
  | "predicate_inst M (Eq t1 t2) = (case (term_val M t1, term_val M t2) of
      (Some x, Some y) \<Rightarrow> Some (Eq x y)
    | _                \<Rightarrow> None)"
  (* When we do not know what either term defines, then we cannot say that they are equal *)
  
  fun predicate_val::"world_model \<Rightarrow> (object term) predicate \<Rightarrow> bool" where
    "predicate_val M p = (case predicate_inst M p of 
      Some (Pred p as)  \<Rightarrow> (Pred p as) \<in> world_model.predicates M
    | Some (Eq x y)     \<Rightarrow> x = y
    | None              \<Rightarrow> False)"
  
  
  text \<open>We check the value of atoms against a world-model.\<close>
  fun valuation::"world_model \<Rightarrow> object term atom valuation" where
    "valuation M (PredAtom p) = predicate_val M p"
  | "valuation M (NumComp c) = nc_val M c"


subsection \<open>PDDL semantics\<close>
context
begin

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>


subsection \<open>Well-Formedness of PDDL\<close>


fun ty_sym::"(variable \<Rightarrow> type option) \<Rightarrow> (object \<Rightarrow> type option) \<Rightarrow> symbol \<Rightarrow> type option" where
  "ty_sym varT objT (Var v) = varT v"
| "ty_sym varT objT (Const c) = objT c"

lemma ty_sym_mono: "varT \<subseteq>\<^sub>m varT' \<Longrightarrow> objT \<subseteq>\<^sub>m objT' \<Longrightarrow>
  ty_sym varT objT \<subseteq>\<^sub>m ty_sym varT' objT'"
  apply (rule map_leI)
  subgoal for x v
    apply (cases x)
    apply (auto dest: map_leD)
    done
  done


subsubsection \<open>Declarations of types, constants and preds in the domain\<close>

locale ast_domain_decs =
  fixes DD :: ast_domain_decs
begin
  text \<open>The signature is a partial function that maps the preds
    of the domain to lists of argument types.\<close>
  definition sig :: "pred \<rightharpoonup> type list" where
  "sig \<equiv> map_of (map (\<lambda>PredDecl p n \<Rightarrow> (p,n)) (preds DD))"

  text \<open>The signature of functions from objects to other objects. The semantics
        of types and the subtype relationship are carried over from the work
        of Abdulaziz and Lammich.\<close>
  definition obj_fun_sig::"func \<rightharpoonup> (type list \<times> type)" where
  "obj_fun_sig \<equiv> map_of (map (\<lambda>ObjFunDecl f ts t \<Rightarrow> (f, (ts, t))) (obj_funs DD))"
  
  definition num_fun_sig::"func \<rightharpoonup> type list" where
  "num_fun_sig \<equiv> map_of (map (\<lambda>NumFunDecl f ts \<Rightarrow> (f, ts)) (num_funs DD))"

  text \<open>We use a flat subtype hierarchy, where every type is a subtype
    of object, and there are no other subtype relations.

    Note that we do not need to restrict this relation to declared types,
    as we will explicitly ensure that all types used in the problem are
    declared.
    \<close>
  
  fun subtype_edge where
    "subtype_edge (ty,superty) = (superty,ty)"


  text \<open>We have to think of types as sets of primitive types.
        The subtype relationship is the relation from every primitive type to
        its direct subtypes\<close>
  definition "subtype_rel \<equiv> set (map subtype_edge (types DD))"

  text \<open>To check whether a non-primitive type \<open>oT\<close> is a subtype of a different
        non-primitive type \<open>T\<close>.
        
        Every primitive type in \<open>oT\<close>, must be reachable from some primitive
        type in \<open>T\<close>. 

        Recall that \<open>``\<close> will take a relation \<open>('a \<times> 'b)\<close> and a set \<open>'a set\<close> and
        map it through the relation, finding the corresponding \<open>'b set\<close>.\<close>
  definition of_type :: "type \<Rightarrow> type \<Rightarrow> bool" where
    "of_type oT T \<equiv> set (primitives oT) \<subseteq> subtype_rel\<^sup>* `` set (primitives T)"
  


  context 
    fixes ty_ent::"'ent \<rightharpoonup> type"
  begin
  text \<open>We fix a type-environment, which assigns types to the entities in a term.\<close>
  
  text \<open>These two functions compute the type of a term. For a functinal term to
      have a type, we must also check that its parameters are well-typed with respect
      to its signature.\<close>
    fun is_term_of_type :: "'ent term \<Rightarrow> type \<Rightarrow> bool" and
        ty_term::"'ent term \<Rightarrow> type option" where
      "is_term_of_type v T = (case ty_term v of
        Some vT \<Rightarrow> of_type vT T
      | None \<Rightarrow> False)"
    | "ty_term (Sym e) = ty_ent e"
    | "ty_term (Fun f as) = (case (obj_fun_sig f) of 
        Some (Ts, T) \<Rightarrow> (if (list_all2 is_term_of_type as Ts) 
          then Some T else None)
      | None \<Rightarrow> None)"

    text \<open>When a term has a type, then all of the entities within it must
          be in the domain of the type environment.\<close>
    lemma ty_term_ent_dom:
      assumes "ty_term t = Some T"
      shows "sym t \<subseteq> dom ty_ent"
      using assms
    proof (induction t arbitrary: T)
      case (Fun f ts)
      from \<open>ty_term (Fun f ts) = Some T\<close>
      obtain Ts where
        "obj_fun_sig f = Some (Ts, T)"
        "list_all2 is_term_of_type ts Ts"
        by (auto split: option.splits if_splits)
      then have "\<forall>t \<in> set ts. \<exists>T. is_term_of_type t T"
        by (metis in_set_conv_nth list_all2_conv_all_nth)
      then have "\<forall>t \<in> set ts. \<exists>T. ty_term t = Some T" 
        by (auto split: option.splits)
      then
      show ?case using Fun.IH by fastforce
    next
      case (Sym x)
      then show ?case by auto
    qed
    
    lemma ty_term_ent_dom':
      assumes "t \<in> dom ty_term"
      shows "sym t \<subseteq> dom ty_ent"
      using ty_term_ent_dom assms by blast
  end

  type_synonym ('ent) ty_ent = "'ent \<rightharpoonup> type"

  text \<open>For the next few definitions, we fix a partial function that maps
    a polymorphic entity type @{typ "'e"} to types. An entity can be
    instantiated by variables or objects later.\<close>
  context
    fixes ty_ent :: "'ent ty_ent"  \<comment> \<open>Symity's type, None if invalid\<close>
  begin
    
    text \<open>Checks whether an entity has a given type\<close>
    definition is_of_type :: "'ent \<Rightarrow> type \<Rightarrow> bool" where
      "is_of_type v T \<longleftrightarrow> (
        case ty_ent v of
          Some vT \<Rightarrow> of_type vT T
        | None \<Rightarrow> False)"

    text \<open>A pred is well-formed if a declaration with the name exists
          and the type is correct\<close>
    fun wf_predicate::"pred \<times> 'ent list \<Rightarrow> bool" where
      "wf_predicate (p,vs) \<longleftrightarrow> (
        case sig p of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 is_of_type vs Ts)"
 
    fun wf_predicate_eq :: "'ent predicate \<Rightarrow> bool" where
      "wf_predicate_eq (Pred p vs) \<longleftrightarrow> wf_predicate (p,vs)"
    | "wf_predicate_eq (Eq a b) \<longleftrightarrow> ty_ent a \<noteq> None \<and> ty_ent b \<noteq> None"

    text \<open>This checks that a pred is well-formed and not an equality.\<close>
    fun wf_pred :: "'ent predicate \<Rightarrow> bool" where
      "wf_pred (Pred p vs) \<longleftrightarrow> wf_predicate (p, vs)"
    | "wf_pred (Eq _ _) \<longleftrightarrow> False"

    text \<open>A function call is well-formed if the function has been
          declared and the types of the arguments matches the types
          of the parameters\<close>
    fun wf_num_func::"func \<times> 'ent list \<Rightarrow> bool" where
      "wf_num_func (f, as) \<longleftrightarrow> (
        case num_fun_sig f of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 is_of_type as Ts
      )"

    text \<open>Fluents and comparisons are well-formed if the components are well-formed\<close>
    fun wf_num_fluent::"'ent num_fluent \<Rightarrow> bool" where
      "wf_num_fluent (NFun f as) = wf_num_func (f, as)"
    | "wf_num_fluent (Num _) = True"
    | "wf_num_fluent (Add a b) = (wf_num_fluent a \<and> wf_num_fluent b)"
    | "wf_num_fluent (Sub a b) = (wf_num_fluent a \<and> wf_num_fluent b)"
    | "wf_num_fluent (Mult a b) = (wf_num_fluent a \<and> wf_num_fluent b)"
    | "wf_num_fluent (Div a b) = (wf_num_fluent a \<and> wf_num_fluent b)"
    
    fun wf_num_comp :: "'ent num_comp \<Rightarrow> bool" where
      "wf_num_comp (Num_Eq a b) = (wf_num_fluent a \<and> wf_num_fluent b)"
    | "wf_num_comp (Num_Lt a b) = (wf_num_fluent a \<and> wf_num_fluent b)"
    | "wf_num_comp (Num_Le a b) = (wf_num_fluent a \<and> wf_num_fluent b)"

    text \<open>Predicate-atoms are well-formed if their arguments match the
      signature, equalities are well-formed if the arguments are valid
      objects (have a type), comparisons are well-formed if the functions
      and terms are well-typed.
    \<close>
    fun wf_atom :: "'ent atom \<Rightarrow> bool" where
      "wf_atom (PredAtom p) \<longleftrightarrow> wf_predicate_eq p"
    | "wf_atom (NumComp nc) \<longleftrightarrow> wf_num_comp nc"

    text \<open>A formula is well-formed if its components are well-formed
    \<close>
    fun wf_fmla :: "('ent atom) formula \<Rightarrow> bool" where
      "wf_fmla (Atom a) \<longleftrightarrow> wf_atom a"
    | "wf_fmla (\<bottom>) \<longleftrightarrow> True"
    | "wf_fmla (\<phi>1 \<^bold>\<and> \<phi>2) \<longleftrightarrow> (wf_fmla \<phi>1 \<and> wf_fmla \<phi>2)"
    | "wf_fmla (\<phi>1 \<^bold>\<or> \<phi>2) \<longleftrightarrow> (wf_fmla \<phi>1 \<and> wf_fmla \<phi>2)"
    | "wf_fmla (\<^bold>\<not>\<phi>) \<longleftrightarrow> wf_fmla \<phi>"
    | "wf_fmla (\<phi>1 \<^bold>\<rightarrow> \<phi>2) \<longleftrightarrow> (wf_fmla \<phi>1 \<and> wf_fmla \<phi>2)"

    lemma "wf_fmla \<phi> = (\<forall>a\<in>atoms \<phi>. wf_atom a)"
      by (induction \<phi>) auto

    text \<open>An update to a function on objects is well-formed if the function has 
          been declared, the signature matches the types of the arguments and new return value, 
          and the arguments and the term to assign the return value are well-formed.\<close>
    fun wf_of_upd::"'ent of_upd \<Rightarrow> bool" where
    "wf_of_upd (OF_Upd f as v) = (case obj_fun_sig f of 
      None \<Rightarrow> False
    | Some (Ts, T) \<Rightarrow>
          list_all2 is_of_type as Ts 
        \<and> (v = None \<or> is_of_type (the v) T))" 
  
    text \<open>An update to a numeric function is well-formed if the function has been declared,
          the signature matches the types of the arguments, the arguments are well-formed,
          and the value that is being assigned is well-formed.\<close>
    fun wf_nf_upd::"'ent nf_upd \<Rightarrow> bool" where
    "wf_nf_upd (NF_Upd op f as v) = (case num_fun_sig f of 
        None \<Rightarrow> False
      | Some Ts \<Rightarrow> 
          list_all2 is_of_type as Ts 
        \<and> wf_num_fluent v
    )"

    text \<open>An effect is well-formed if its constituent parts are well-formed\<close>
    fun wf_effect where
      "wf_effect (Effect a d tu nu) \<longleftrightarrow>
          (\<forall>u \<in> set a. wf_pred u)
        \<and> (\<forall>u \<in> set d. wf_pred u)
        \<and> (\<forall>u \<in> set tu. wf_of_upd u)
        \<and> (\<forall>u \<in> set nu. wf_nf_upd u)
        "

  definition wf_cond_effect where
      "wf_cond_effect eff \<longleftrightarrow> wf_fmla (fst eff) \<and> wf_effect (snd eff)"

    definition wf_cond_effect_list where
      "wf_cond_effect_list \<equiv> list_all wf_cond_effect"


    lemma list_all2_is_of_type_imp_set_in_ty_env:
      assumes "list_all2 is_of_type args Ts"
      shows "\<forall>arg \<in> set args. arg \<in> dom ty_ent"
      using assms
      by (induction rule: list_all2_induct; auto simp: is_of_type_def split: option.splits)
      
    lemma wf_predicate_imp_args_in_ty_env:
      fixes args::"'ent list"
      assumes "wf_predicate (p, args)"
      shows "set args \<subseteq> dom ty_ent"
      using assms
      by (auto split: option.splits dest: list_all2_is_of_type_imp_set_in_ty_env)

    lemma wf_predicate_imp_ent_in_ty_env:
      fixes p::"'ent predicate" 
        assumes "wf_predicate_eq p"
        shows "predicate.ent p \<subseteq> dom ty_ent"
      using assms
      by (cases p; auto simp: wf_predicate_imp_args_in_ty_env)
    
    lemma wf_num_func_imp_args_in_ty_env:
      fixes args::"'ent list"
      assumes "wf_num_func (f, args)"
      shows "set args \<subseteq> dom ty_ent"
      using assms
      by (auto split: option.splits dest: list_all2_is_of_type_imp_set_in_ty_env)
        
      lemma wf_num_fluent_imp_ent_in_ty_env:
        fixes f::"'ent num_fluent"
        assumes "wf_num_fluent f"
        shows "num_fluent.ent f \<subseteq> dom ty_ent"
        using assms
        by (induction f; auto simp: wf_num_func_imp_args_in_ty_env)
      
      lemma wf_num_comp_imp_ent_in_ty_env:
        fixes nf::"'ent num_comp"
        assumes "wf_num_comp nf"
        shows "num_comp.ent nf \<subseteq> dom ty_ent"
        using assms
        by (induction nf; auto simp: wf_num_fluent_imp_ent_in_ty_env)
      
      lemma wf_atom_imp_ent_in_ty_env:
        fixes a::"'ent atom"
        assumes "wf_atom a"
        shows "atom.ent a \<subseteq> dom ty_ent"
        using assms wf_predicate_imp_ent_in_ty_env
        by (cases a; auto simp: wf_num_comp_imp_ent_in_ty_env wf_predicate_imp_ent_in_ty_env)
      
      lemma wf_fmla_as_wf_atoms:
        shows "wf_fmla \<phi> \<longleftrightarrow> (\<forall>a \<in> atoms \<phi>. wf_atom a)"
        by (induction \<phi>; auto)
    
      lemma wf_fmla_imp_ent_in_ty_env: 
        assumes "wf_fmla \<phi>"
        shows "f_ent \<phi> \<subseteq> dom ty_ent"
        using assms wf_fmla_as_wf_atoms 
            wf_atom_imp_ent_in_ty_env f_ent_def by fast
    
end \<comment> \<open>Context fixing \<open>ty_ent\<close>\<close>
  
  definition constT :: "object \<rightharpoonup> type" where
    "constT \<equiv> map_of (consts DD)"
             
  text \<open>A type is well-formed if it consists only of declared primitive types,
     and the type object.\<close>
  fun wf_type where
    "wf_type (Either Ts) \<longleftrightarrow> set Ts \<subseteq> insert ''object'' (fst`set (types DD))"

  text \<open>A pred is well-formed if its argument types are well-formed.\<close>
  fun wf_pred_decl where
    "wf_pred_decl (PredDecl p Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. wf_type T)"

  text \<open>The types declaration is well-formed, if all supertypes are declared types (or object)\<close>
  definition "wf_types \<equiv> snd`set (types DD) \<subseteq> insert ''object'' (fst`set (types DD))"

  text \<open>The declarations in a domain are well-formed if 
    \<^item> there are no duplicate declared pred names,
    \<^item> all declared preds are well-formed,
    \<^item> there are no duplicate action names\<close>

  definition wf_domain_decs :: "bool" where
    "wf_domain_decs \<equiv>
      wf_types
    \<and> distinct (map (pred_decl.predicate) (preds DD))
    \<and> distinct (map of_name (obj_funs DD) @ map nf_name (num_funs DD) @ (map (obj_name o fst) (consts DD)))
    \<and> (\<forall>p\<in>set (preds DD). wf_pred_decl p)
    \<and> (\<forall>(c, T) \<in> set (consts DD). wf_type T)"

  (* all functions must be distinct from constants, because otherwise equality checks become ambiguous *)
  

  (* Functions in the domain cannot have the same name as objects *)


end \<comment> \<open>locale \<open>ast_domain\<close>\<close>

subsubsection \<open>Declarations of types and objects in the problem\<close>

text \<open>We fix the declarations of types and such from the domain and include the declarations
      from the problem as well\<close>
locale ast_problem_decs = ast_domain_decs "domain_decs PD"
  for PD::ast_problem_decs
begin
  
  text \<open>We refer to the problem domain as \<open>D\<close>\<close>
  abbreviation "DD \<equiv> domain_decs PD"

  (* constants are from the domain, objects are from the problem *)
  definition objT :: "object \<rightharpoonup> type" where
    "objT \<equiv> map_of (objects PD) ++ constT"

  lemma objT_alt: "objT = map_of (consts DD @ objects PD)"
    unfolding objT_def constT_def
    by clarsimp
  (* objects cannot have the same name as constants or functions *)
  
  definition wf_problem_decs where
    "wf_problem_decs \<equiv>
      wf_domain_decs
    \<and> distinct (map of_name (obj_funs DD) @ map nf_name (num_funs DD) @ (map (obj_name o fst) (consts DD)) @ (map (obj_name o fst) (objects PD)))
    \<and> (\<forall>(n,T) \<in> set (objects PD). wf_type T)"


  text \<open>An action schema is well-formed if the parameter names are distinct,
    and the precondition and effect is well-formed wrt. the parameters.
  \<close>
  fun wf_action_schema :: "ast_action_schema \<Rightarrow> bool" where
    "wf_action_schema (Action_Schema n params pre effs) \<longleftrightarrow> (
        let tyt = ty_term (ty_sym (map_of params) objT)
        in
        distinct (map fst params)
      \<and> wf_fmla tyt pre
      \<and> wf_cond_effect_list tyt effs)"

  definition wf_goal::"schematic_formula \<Rightarrow> bool" where
    "wf_goal \<equiv> wf_fmla (ty_term (ty_sym Map.empty objT))"

  
end

subsubsection \<open>The entire domain\<close>

text \<open>To fully assert the well-formedness of a domain, we need the set of objects declared
      in a problem as well. These are necessary to implement the macros that
      replace quantified formulas with quantifier-free ones.\<close>
locale ast_domain = ast_problem_decs "problem_decs D"
  for D::ast_domain
begin
abbreviation "PD \<equiv> problem_decs D"

  
  text \<open>A domain is well-formed if in addition to the declarations being well-formed
    \<^item> there are no duplicate declared actions,
    \<^item> and all declared actions are well-formed
    \<close>
  definition wf_domain :: "bool" where
    "wf_domain \<equiv>
      wf_problem_decs
      \<and> distinct (map ast_action_schema.name (actions D))
      \<and> (\<forall>a\<in>set (actions D). wf_action_schema a)
    "
end


subsubsection \<open>The problem\<close>

locale ast_problem = ast_domain "domain P"
  for P::ast_problem
begin
  abbreviation "D \<equiv> domain P"
  text \<open>This definition is needed for well-formedness of the initial model,
    and forward-references to the concept of world model.
  \<close>

  definition wf_of_arg_r_map::"func \<Rightarrow> (object list \<rightharpoonup> object) \<Rightarrow> bool" where
    "wf_of_arg_r_map f f' \<equiv> (case obj_fun_sig f of 
      None \<Rightarrow> False 
    | Some (Ts, T) \<Rightarrow> 
        (\<forall>(as, v) \<in> Map.graph f'. list_all2 (is_of_type objT) as Ts 
        \<and> is_of_type objT v T))"

    definition wf_of_int::"(func \<rightharpoonup> object list \<rightharpoonup> object) \<Rightarrow> bool" where
      "wf_of_int oi \<equiv> (\<forall>(f, m) \<in> Map.graph oi. wf_of_arg_r_map f m)"

    definition wf_nf_int_map::"func \<Rightarrow> (object list \<rightharpoonup> rat) \<Rightarrow> bool" where
      "wf_nf_int_map n f' \<equiv> (case num_fun_sig n of 
        None \<Rightarrow> False 
      | Some Ts \<Rightarrow> \<forall>as \<in> dom f'. list_all2 (is_of_type objT) as Ts)"
  
    definition wf_nf_int::"(func \<rightharpoonup> object list \<rightharpoonup> rat) \<Rightarrow> bool" where
      "wf_nf_int ni \<equiv> (\<forall>(f, m) \<in> Map.graph ni. wf_nf_int_map f m)"

  text \<open>The preds are well-formed, i.e. well-typed. The interpretations of 
        fluents are also well-formed, i.e. well-typed and only defined for those
        functions which have been declared in the domain or problem.\<close>
  definition wf_world_model::"world_model \<Rightarrow> bool" where
    "wf_world_model M \<equiv> (\<forall>p \<in> predicates M. wf_pred objT p) 
                      \<and> wf_of_int (of_int M)
                      \<and> wf_nf_int (nf_int M)"

  fun wf_init_of_a::"(func \<times> object list \<times> object) \<Rightarrow> bool" where
    "wf_init_of_a (f, as, v) = (case obj_fun_sig f of 
      Some (Ts, T) \<Rightarrow> list_all2 (is_of_type objT) as Ts \<and> is_of_type objT v T
    | None \<Rightarrow> False)"
  
  fun wf_init_nf_a::"(func \<times> object list \<times> rat) \<Rightarrow> bool" where
    "wf_init_nf_a (f, as, v) = (case num_fun_sig f of
      Some Ts \<Rightarrow> list_all2 (is_of_type objT) as Ts
    | None \<Rightarrow> False)"

  fun non_int_fun_assign::"('f \<times> 'as \<times> 'v) \<Rightarrow> ('f \<times> 'as \<times> 'v) \<Rightarrow> bool" where
    "non_int_fun_assign (f, as, v) (f', as', v') = (f = f' \<and> as = as' \<longrightarrow> v = v')"

  definition non_int_assign_list::"('f \<times> 'as \<times> 'v) list \<Rightarrow> bool" where
    "non_int_assign_list xs = pairwise non_int_fun_assign (set xs)"

  lemma non_int_assign_list_iff[simp]: "non_int_assign_list xs \<longleftrightarrow> (\<forall>x \<in> set xs. \<forall>y \<in> set xs. non_int_fun_assign x y)"
    unfolding non_int_assign_list_def pairwise_def
    apply (rule iffI)
     apply (rule ballI)+
    subgoal for x y
      apply (cases "x = y")
      subgoal by (cases x; cases y; auto)
      subgoal by auto
      done
    subgoal by blast
    done

  text \<open>A problem is well-formed if in addition to the domain being well-formed, the goal is\<close>
  definition wf_problem where
    "wf_problem \<equiv>
      wf_domain
    \<and> (\<forall>p \<in> set (init_ps P). wf_pred objT p)
    \<and> (\<forall>a \<in> set (init_ofs P). wf_init_of_a a)
    \<and> non_int_assign_list (init_ofs P)
    \<and> (\<forall>a \<in> set (init_nfs P). wf_init_nf_a a)
    \<and> non_int_assign_list (init_nfs P)
    \<and> wf_goal (goal P)
    " 
end


subsection \<open>Semantics of actions in dynamic world state.\<close>
context ast_domain
begin

text \<open>Important: thinking in terms of conditional lists of effects vs filtering by enabledness:
      - Pros: 
      - Cons: \<close>
    
  fun inst_of_upd::"world_model 
    \<Rightarrow> object term of_upd 
    \<Rightarrow> instantiated_of_upd" where
    "inst_of_upd M (OF_Upd f args r) = (OFU f (map (term_val M) args) (((term_val M) o the) r))"

  text \<open>When we instantiate an update to numeric functions, what do we do?
        \<close>

  fun inst_nf_upd::"world_model
    \<Rightarrow> object term nf_upd
    \<Rightarrow> instantiated_nf_upd" where
    "inst_nf_upd M (NF_Upd op f args t) = (
      let args' = map (term_val M) args
      in NFU op f args' (nf_val M t))"
  
  fun inst_effect :: "world_model \<Rightarrow> ground_effect \<Rightarrow> fully_instantiated_effect" where
    "inst_effect M (Effect a d tu nu) = (
      Eff (map (predicate_inst M) a) 
          (map (predicate_inst M) d) 
          (map (inst_of_upd M) tu) 
          (map (inst_nf_upd M) nu))"

  text \<open>\<open>undefined\<close> in the update is represented by @{term None}\<close>
  fun apply_of_upd::"instantiated_of_upd
    \<Rightarrow> (object_function_interpretation) 
    \<Rightarrow> (object_function_interpretation)" where
    "apply_of_upd (OFU f as v) ti = (
      case (ti f) of
        Some ti1 \<Rightarrow> (ti(f \<mapsto> (ti1((map the as) := v))))
      | None \<Rightarrow> (ti(f \<mapsto> (Map.empty((map the as) := v))))
    )"

  text \<open>The return value will never be undefined, unless the update is not well-formed.\<close>

  fun upd_nf_int::"(object list \<rightharpoonup> rat) \<Rightarrow> upd_op \<Rightarrow> object list \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> (object list \<rightharpoonup> rat)" where
    "upd_nf_int m Assign args old n = (m (args \<mapsto> n))"
  | "upd_nf_int m ScaleUp args old n = (m (args \<mapsto> (old * n)))"
  | "upd_nf_int m ScaleDown args old n = (m (args \<mapsto> (old / n)))"
  | "upd_nf_int m Increase args old n = (m (args \<mapsto> (old + n)))"
  | "upd_nf_int m Decrease args old n = (m (args \<mapsto> (old - n)))"

  fun upd_if_exists where
    "upd_if_exists m f k v = (
       let m' = (case m f of Some m' \<Rightarrow> m' | None \<Rightarrow> Map.empty)
       in m(f \<mapsto> (m'(k \<mapsto> v)))
      )"
  (* TODO: Would this lead to a shorter proof? *)

  fun apply_nf_upd::"instantiated_nf_upd
    \<Rightarrow> numeric_function_interpretation
    \<Rightarrow> numeric_function_interpretation" where
    "apply_nf_upd (NFU op n as v) ni = (
      let f' = (case ni n of Some f' \<Rightarrow> f' | None \<Rightarrow> Map.empty)
      in ni(n \<mapsto> (upd_nf_int f' op (map the as) (the (f' (map the as))) (the v))))"


  text \<open>It seems to be agreed upon that, in case of a contradictory effect,
    addition overrides deletion. We model this behaviour by first executing
    the deletions, and then the additions. Also, effects that occur later
    in the list override those that occur earlier.\<close>
  fun apply_effect::"fully_instantiated_effect \<Rightarrow> world_model \<Rightarrow> world_model" where
    "apply_effect (Eff a d ou nu) (World_Model p oi ni) = (
      World_Model 
        ((p - set (map the d)) \<union> set (map the a)) 
        (fold apply_of_upd ou oi) 
        (fold apply_nf_upd nu ni))"
 

  text \<open>This definition is faulty, because the effects will interfere\<close>
  (* fun inst_apply_conditional_effect::"(ground_formula \<times> ground_effect) \<Rightarrow> world_model \<Rightarrow> world_model" where
    "inst_apply_conditional_effect (pre, eff) M = (
      if (valuation M \<Turnstile> pre) 
      then apply_conditional_effect (pre, eff) M
      else M)" *)

  definition inst_apply_effect::"world_model \<Rightarrow> ground_effect \<Rightarrow> world_model \<Rightarrow> world_model" where
    "inst_apply_effect eM eff M = (apply_effect (inst_effect eM eff) M)"

  definition inst_apply_conditional_effect::"world_model \<Rightarrow> (ground_formula \<times> ground_effect) \<Rightarrow> world_model \<Rightarrow> world_model" where
    "inst_apply_conditional_effect eM eff M = (
      if (valuation eM \<Turnstile> (fst eff)) 
      then inst_apply_effect eM (snd eff) M 
      else M)"

  (* TODO: Define the non-interference of effects with one another *)
  (* Updates to numeric functions should contain the update operators even when fully instantiated *)
  (* One important point is the non-interference of effects. If effects interfere, then plans are invalid. *)
  (* TODO: When we apply conditional effects, we instantiate them with respect to
      one world model, but apply them with respect to another. We could define the function that applies
      a conditional effect to a world-model with respect to two world-models, one of which is used to 
      instantiate the effect, and one we apply it to. Moreover, preconditions should be evaluated w.r.t.
      the first world model. *)
  
  text \<open>We first have to filter out the inactive effects. Following that, we instantiate the 
        active effects. Then the effects are applied individually by a right fold.\<close>
  definition apply_conditional_effect_list where
    "apply_conditional_effect_list effs M = (fold (inst_apply_conditional_effect M) effs M)"

  text \<open>Execute a ground action\<close>
  definition execute_ground_action :: "ground_action \<Rightarrow> world_model \<Rightarrow> world_model" where
    "execute_ground_action a M = (apply_conditional_effect_list (effects a) M)"

  text \<open>An update to a pred can be applied only if it is defined and 
        it is a pred and not an equality. Equality is checked on the fly,
        rather than using set membership.\<close>
  fun wf_app_predicate_upd where
    "wf_app_predicate_upd None = False"
  | "wf_app_predicate_upd (Some (Eq _ _)) = False"
  | "wf_app_predicate_upd (Some (Pred p as)) = wf_predicate_eq objT (Pred p as)"

  fun is_some where
    "is_some (Some x) = True"
  | "is_some None = False"

  lemma the_inj_on_is_some:
    "inj_on the {x. is_some x}"
    apply (subst inj_on_def)
    apply (intro ballI)
    subgoal for x y
      apply (drule CollectD)+
      apply (cases x; cases y)
      by auto
    done

  find_theorems "inj_on ?f ?S \<Longrightarrow> ?T \<subseteq> ?S \<Longrightarrow> inj_on ?f ?T"

  lemma map_the_inj_on:
    "inj_on (map the) {x . list_all is_some x}"
    unfolding inj_on_def
    apply (intro ballI)
    subgoal for xs ys
      apply (rule impI)
      apply (erule map_inj_on[of the])
      apply (drule CollectD)+
      apply (rule inj_on_subset[OF the_inj_on_is_some])
      apply (subst (asm) list_all_iff)+
      apply (drule conjI[of "Ball (set xs) is_some" "Ball (set ys) is_some"], assumption)
      apply (thin_tac "Ball (set ys) is_some")
      apply (subst (asm) ball_Un[symmetric])
      by blast
    done

  lemma is_some_map_the_neq:
    assumes "a \<noteq> b"
        and "list_all is_some a"
        and "list_all is_some b"
      shows "map the a \<noteq> map the b"
    using assms inj_on_contraD[where f = "map the" and x = a and y = b, OF map_the_inj_on]
    by blast
          
  text \<open>An update to an object fluent (term function) is well-formed, if
        the arguments are defined and well-typed, and the return value is
        either None or well-typed.\<close>
  fun wf_app_of_upd::"instantiated_of_upd \<Rightarrow> bool" where
    "wf_app_of_upd (OFU f as v) = (case obj_fun_sig f of 
          None \<Rightarrow> False
        | Some (Ts, T) \<Rightarrow>
              list_all is_some as
            \<and> list_all2 ((is_of_type objT) o the) as Ts 
            \<and> (v = None \<or> is_of_type objT (the v) T))"

  definition nf_args_well_typed::"func \<Rightarrow> object list \<Rightarrow> bool" where
  "nf_args_well_typed f args = (case num_fun_sig f of None \<Rightarrow> False | Some Ts \<Rightarrow> list_all2 (is_of_type objT) args Ts)"

  text \<open>An update to a numeric fluent is well-formed, if the arguments are 
        defined and well-typed, and the return value is defined.\<close>
  fun wf_app_nf_upd::"instantiated_nf_upd \<Rightarrow> bool" where
    "wf_app_nf_upd (NFU op f args v) = (
        list_all is_some args 
      \<and> is_some v \<and> (op = ScaleDown \<longrightarrow> the v \<noteq> (of_rat 0))
      \<and> nf_args_well_typed f (map the args))"

  fun wf_fully_instantiated_effect where
    "wf_fully_instantiated_effect (Eff a d tu nu) \<longleftrightarrow> 
        (\<forall>ae \<in> set a. wf_app_predicate_upd ae)
      \<and> (\<forall>de \<in> set d. wf_app_predicate_upd de)
      \<and> (\<forall>u \<in> set tu. wf_app_of_upd u)     
      \<and> (\<forall>u \<in> set nu. wf_app_nf_upd u)"
  
  definition disjoint_upd_lists::"object predicate list \<Rightarrow> object predicate list \<Rightarrow> bool" where
    "disjoint_upd_lists a b = (set a \<inter> set b = {})"

  definition disjoint_inst_upd_lists::"object predicate option list \<Rightarrow> object predicate option list \<Rightarrow> bool" where
    "disjoint_inst_upd_lists = map_fun (map the) (map_fun (map the) id) disjoint_upd_lists"
      
  text \<open>In the previous version, we assumed that additions are applied after and override
    deletions. The datatype to represent effects is too far removed from PDDL to simulate that
    without applying another non-trivial transformation. In fact, we never have more than
    one update encoded in any effect right now.\<close>
  definition non_int_pred_upds where
    "non_int_pred_upds a d a' d' = 
       (disjoint_inst_upd_lists a d
      \<and> disjoint_inst_upd_lists a d'
      \<and> disjoint_inst_upd_lists a' d
      \<and> disjoint_inst_upd_lists a' d')"

  text \<open>Non-interference of updates to functions is important, since we could obtain lists
        of effects which make no sense.\<close>
    fun non_int_ops where
    "non_int_ops ScaleUp ScaleDown = True"
  | "non_int_ops ScaleDown ScaleUp = True"
  | "non_int_ops Increase Decrease = True"
  | "non_int_ops Decrease Increase = True"
  | "non_int_ops a b = (a = b \<and> a \<noteq> Assign)"

  text \<open>Numeric updates do not interfere, when they can be applied in any order\<close>
  fun non_int_nf_upds where
    "non_int_nf_upds (NFU op f as v) (NFU op' f' as' v') = 
      (f \<noteq> f' \<or> as \<noteq> as' \<or> (non_int_ops op op' \<or> (op = op' \<and> v = v')))"

  lemma non_int_nf_upd_refl[simp]:
    "non_int_nf_upds x x" by (cases x; auto)
  
  definition non_int_nf_upd_list where
    "non_int_nf_upd_list xs \<equiv> pairwise non_int_nf_upds (set xs)"

  lemma non_int_nf_upd_list_iff[simp]:
  "non_int_nf_upd_list xs \<longleftrightarrow> (\<forall>x \<in> set xs. \<forall>y \<in> set xs. non_int_nf_upds x y)"
  unfolding non_int_nf_upd_list_def pairwise_def 
  by force

  definition non_int_nf_upd_lists where
    "non_int_nf_upd_lists xs ys \<equiv> non_int_nf_upd_list (xs @ ys)"
  
  fun non_int_of_upds where
    "non_int_of_upds (OFU f as v) (OFU f' as' v') =
    (f \<noteq> f' \<or> as \<noteq> as' \<or> v = v')"
  
  lemma non_int_of_upd_refl[simp]:
    "non_int_of_upds x x" by (cases x; auto)
  
  definition non_int_of_upd_list where
    "non_int_of_upd_list xs \<equiv> pairwise non_int_of_upds (set xs)"
  (* using these is ok, because the set implementation is guaranteed 
      to be efficient *)

lemma non_int_of_upd_list_iff[simp]:
  "non_int_of_upd_list xs \<longleftrightarrow> (\<forall>x \<in> set xs. \<forall>y \<in> set xs. non_int_of_upds x y)"
  unfolding non_int_of_upd_list_def pairwise_def 
  by force

  definition non_int_of_upd_lists where
    "non_int_of_upd_lists xs ys \<equiv> non_int_of_upd_list (xs @ ys)"

  definition non_int_effs where
    "non_int_effs e1 e2 \<equiv> 
      (non_int_pred_upds (eff_adds e1) (eff_dels e1) (eff_adds e2) (eff_dels e2))
    \<and> non_int_nf_upd_lists (nus e1) (nus e2)
    \<and> non_int_of_upd_lists (ous e1) (ous e2)"
  
  definition non_int_cond_effs where
    "non_int_cond_effs M e1 e2 \<equiv> (valuation M \<Turnstile> fst e1 \<and> valuation M \<Turnstile> fst e2) 
      \<longrightarrow> (non_int_effs (inst_effect M (snd e1)) (inst_effect M (snd e2)))"

  abbreviation "pairwise' P S \<equiv> \<forall>x \<in> S. \<forall>y \<in> S. P x y"

  definition non_int_cond_eff_list where
    "non_int_cond_eff_list M xs \<equiv> pairwise' (non_int_cond_effs M) (set xs)"

  text \<open> \<^term>\<open>None\<close> represents the intentional update to a function
        using \<open>undefined\<close>. Another source of \<^term>\<open>None\<close> in the return value
        of a \<open>instantiated_of_upd\<close> is the instantiation process itself.\<close>
  fun valid_ret_val_inst::"'a option \<Rightarrow> 'b option \<Rightarrow> bool" where
    "valid_ret_val_inst None None = True"
  | "valid_ret_val_inst (Some r) (Some r') = True"
  | "valid_ret_val_inst _ _ = False"

  fun of_upd_rv_corr'::"object term of_upd \<Rightarrow> instantiated_of_upd \<Rightarrow> bool" where
    "of_upd_rv_corr' (OF_Upd f as v) (OFU f' as' v') = valid_ret_val_inst v v'"

  definition of_upd_rv_corr::"world_model \<Rightarrow> object term of_upd \<Rightarrow> bool" where
    "of_upd_rv_corr M u \<equiv> of_upd_rv_corr' u (inst_of_upd M u)"

  text \<open>I cannot come up with a better name for this

        Even following the final instantiation, we have to evaluate the update w.r.t. the world
        model in the case of the relative updates. In that case, we need to
        ensure that these have not been undefined.

        We instantiate with respect to one world model but we evaluate with
        respect to an updated one. Can we ensure that the updates preserve this?  
        
        Yes, if the world-model assigns some value to some function from objects to 
        numbers, it cannot be unassigned. Therefore checking this before the execution
        of a list of actions is sufficient.\<close>

  fun int_defines_nf_upd::"numeric_function_interpretation \<Rightarrow> instantiated_nf_upd \<Rightarrow> bool" where
    "int_defines_nf_upd _ (NFU Assign f _ _) = True"
  | "int_defines_nf_upd ni (NFU _ f args _) = (
      case ni f of 
        Some f' \<Rightarrow> f' (map the args) \<noteq> None
      | None \<Rightarrow> False)"

  definition nf_upd_defined::"world_model \<Rightarrow> world_model \<Rightarrow> object term nf_upd \<Rightarrow> bool" where
    "nf_upd_defined eM M upd = int_defines_nf_upd (nf_int M) (inst_nf_upd eM upd)"

  (* The names here are weird *)
  definition well_inst_effect::"world_model \<Rightarrow> ground_effect \<Rightarrow> world_model \<Rightarrow> bool" where
    "well_inst_effect eM eff M \<equiv> list_all (of_upd_rv_corr eM) (of_upds eff) \<and> list_all (nf_upd_defined eM M) (nf_upds eff)"

  definition well_inst_cond_effect::"world_model \<Rightarrow> world_model \<Rightarrow> (ground_formula \<times> ground_effect) \<Rightarrow> bool" where
    "well_inst_cond_effect eM M eff\<equiv> (valuation eM \<Turnstile> (fst eff)) \<longrightarrow> (well_inst_effect eM (snd eff) M)"
  
  definition well_inst_cond_effect_list::"world_model \<Rightarrow> world_model \<Rightarrow> (ground_formula \<times> ground_effect) list \<Rightarrow> bool" where
    "well_inst_cond_effect_list eM M effs \<equiv> list_all (well_inst_cond_effect eM M) effs"


  text \<open>Before a ground effect is applied, it must be fully instantiated. 
        That the fully instantiated effect is well-formed is only necessary
        if it is active. 

        This simplifies proofs regarding the preservation of well-formedness 
        following action execution. One condition for the preservation is that
        updates to numeric functions are well instantiated. This means that
        we do not attempt to apply a relative update if the term's value is
        undefined in the previous state. That is only checked for active effects,
        i.e. effects whose preconditions are met. 

        Since full instantiation requires the evaluation of nested terms against
        a world model, it is easier to only check the well-formedness of fully
        instantiated effects, when they are active. I believe that the presence
        of that precondition will simplify the proof for the successive application
        of effects. \<close>
  definition wf_inst_cond_effect::"world_model \<Rightarrow> (ground_formula \<times> ground_effect) \<Rightarrow> bool" where
    "wf_inst_cond_effect M eff = (valuation M \<Turnstile> (fst eff) \<longrightarrow> (wf_fully_instantiated_effect (inst_effect M (snd eff))))"

  definition wf_inst_cond_effect_list::"world_model \<Rightarrow> (ground_formula \<times> ground_effect) list \<Rightarrow> bool" where
    "wf_inst_cond_effect_list M effs = list_all (wf_inst_cond_effect M) effs"

  definition valid_effects::"world_model \<Rightarrow> (ground_formula \<times> ground_effect) list \<Rightarrow> bool" where
    "valid_effects M effs \<equiv> 
         (wf_inst_cond_effect_list M effs)
      \<and> (well_inst_cond_effect_list M M effs)
      \<and> (non_int_cond_eff_list M effs)"

  (* First instantiate, then filter, then check validity *)
  
  definition ground_action_enabled where
    "ground_action_enabled \<alpha> M \<equiv> valuation M \<Turnstile> precondition \<alpha>"

  definition wf_ground_action :: "ground_action \<Rightarrow> bool" where
    "wf_ground_action \<alpha> \<equiv> (
        wf_fmla (ty_term objT) (precondition \<alpha>)
      \<and> wf_cond_effect_list (ty_term objT) (effects \<alpha>)
      )"
  
  definition valid_ground_action where
    "valid_ground_action \<alpha> M \<equiv>
        wf_ground_action \<alpha>
      \<and> ground_action_enabled \<alpha> M 
      \<and> valid_effects M (effects \<alpha>)"

  text \<open>As plan actions are executed by first instantiating them, and then
    executing the action instance, it is natural to define a well-formedness
    concept for action instances.\<close>

  fun ground_action_path
    :: "world_model \<Rightarrow> ground_action list \<Rightarrow> world_model \<Rightarrow> bool"
  where
    "ground_action_path M [] M' \<longleftrightarrow> (M = M')"
  | "ground_action_path M (\<alpha>#\<alpha>s) M' \<longleftrightarrow> valid_ground_action \<alpha> M
    \<and> ground_action_path (execute_ground_action \<alpha> M) \<alpha>s M'"

  definition active_effects::"world_model \<Rightarrow> (ground_formula \<times> ground_effect) list \<Rightarrow> (ground_formula \<times> ground_effect) list" where
    "active_effects M effs = (filter (\<lambda>(pre, eff). valuation M \<Turnstile> pre) effs)"

  text \<open>Unfolded definition of ground_action_path. 
      The precondition of the action is well-formed.
      The list of conditional effects is well-formed.
      The precondition is satisfied by the initial state.
      For every effect in the set of active effects:
        - The full effect instantiation is valid
        - Applying, the effect (unfolded) will lead to a state
          from which a ground action path leads to the other state\<close>
  (* lemma ground_action_path_unfolded:
    "ground_action_path M [] M' \<longleftrightarrow> (M = M')"
    "ground_action_path M (\<alpha>#\<alpha>s) M' \<longleftrightarrow> 
      wf_fmla (ty_term objT) (precondition \<alpha>)
    \<and> wf_cond_effect_list (ty_term objT) (effects \<alpha>)
    \<and> valuation M \<Turnstile> precondition \<alpha>
    \<and> (\<forall>(pre, eff) \<in> set (active_effects M (effects \<alpha>)). wf_fully_instantiated_effect (inst_effect M eff))
    \<and> well_inst_cond_effect_list M (effects \<alpha>)
    \<and> non_int_cond_eff_list M (effects \<alpha>)
    \<and> ground_action_path (apply_conditional_effect_list (effects \<alpha>) M) \<alpha>s M'"
    sorry (* TODO: fix later -- not necessary for implementation *)
 *)
end

subsection \<open>Conditions for the preservation of well-formedness\<close>

context ast_problem_decs
begin
  
  text \<open>Here are some lemmas reused in multiple well-formedness proofs for instantiation\<close>

  lemma of_type_refl[simp, intro!]: "of_type T T"
    unfolding of_type_def by auto

  lemma of_type_trans[trans]:
    "of_type T1 T2 \<Longrightarrow> of_type T2 T3 \<Longrightarrow> of_type T1 T3"
    unfolding of_type_def
    by clarsimp (metis (no_types, opaque_lifting)
      Image_mono contra_subsetD order_refl rtrancl_image_idem)
 
  lemma is_of_type_map_ofE:
    assumes "is_of_type (map_of params) x T"
    obtains i xT where "i<length params" "params!i = (x,xT)" "of_type xT T"
    using assms
    unfolding is_of_type_def
    by (auto split: option.splits dest!: map_of_SomeD simp: in_set_conv_nth)
  
  lemma is_of_type_trans:
    assumes "is_of_type Q x T"
        and QR: "\<forall>T. Q x = Some T \<longrightarrow> is_of_type R (f x) T"
      shows "is_of_type R (f x) T"
  proof -
    from \<open>is_of_type Q x T\<close>
    obtain T' where
      "Q x = Some T'"
      "of_type T' T"
      unfolding is_of_type_def by (auto split: option.splits)
    from QR this(1)
    obtain T'' where
      "R (f x) = Some T''"
      "of_type T'' T'"
      unfolding is_of_type_def by (auto split: option.splits)
    from of_type_trans[OF this(2) \<open>of_type T' T\<close>] this(1)
    show "is_of_type R (f x) T" unfolding is_of_type_def by simp
  qed
  
  lemma list_all2_is_of_type: 
    assumes "\<forall>x \<in> set xs. \<forall>T. is_of_type Q x T \<longrightarrow> is_of_type R (f x) T"
        and "list_all2 (is_of_type Q) xs Ts"
      shows "list_all2 (is_of_type R) (map f xs) Ts"
    using assms(2, 1)
    by (induction rule: list_all2_induct;
        auto split: option.splits intro: is_of_type_trans)

  lemma option_is_of_type:
    assumes "\<forall>x \<in> set_option x. \<forall>T. is_of_type Q x T \<longrightarrow> is_of_type R (f x) T"
      and "pred_option (\<lambda>x. is_of_type Q x T) x"
    shows "pred_option (\<lambda>x. is_of_type R x T) (map_option f x)"
    using assms
    by (cases x; simp)
  
  lemma ent_type_imp_wf_num_fluent:
    assumes "\<forall>e \<in> num_fluent.ent nf. \<forall>T. is_of_type Q e T \<longrightarrow> is_of_type R (f e) T"
        and "wf_num_fluent Q nf"
      shows "wf_num_fluent R (map_num_fluent f nf)"
    using assms
    by (induction nf;
        auto split: option.splits intro: list_all2_is_of_type)

  
  lemma ent_type_imp_wf_num_comp:
    assumes "\<forall>e \<in> num_comp.ent nc. \<forall>T. is_of_type Q e T \<longrightarrow> is_of_type R (f e) T"
        and "wf_num_comp Q nc"
      shows "wf_num_comp R (map_num_comp f nc)"
    using assms
    by (cases nc; auto intro: ent_type_imp_wf_num_fluent)
  
  lemma is_of_type_imp_not_none:
    "\<exists>T. is_of_type R x T \<Longrightarrow> R x \<noteq> None"
    unfolding is_of_type_def by (auto split: option.splits)
  
  lemma ent_type_imp_wf_predicate_eq:
    assumes "\<forall>e \<in> predicate.ent p. \<forall>T. is_of_type Q e T \<longrightarrow> is_of_type R (f e) T"
        and "wf_predicate_eq Q p"
      shows "wf_predicate_eq R (map_predicate f p)"
    using assms
    apply (cases p) 
    subgoal by (auto split: option.splits intro: list_all2_is_of_type)
    by (auto split: option.splits simp: is_of_type_def)
  
  lemma ent_type_imp_wf_atom:
    assumes "\<forall>e \<in> atom.ent a. \<forall>T. is_of_type Q e T \<longrightarrow> is_of_type R (f e) T"
        and "wf_atom Q a"
      shows "wf_atom R (map_atom f a)"
    using assms 
    by (cases a; auto intro: ent_type_imp_wf_predicate_eq ent_type_imp_wf_num_comp)
  
  lemma ent_type_imp_wf_fmla:
    assumes "\<forall>e \<in> f_ent \<phi>. \<forall>T. is_of_type Q e T \<longrightarrow> is_of_type R (f e) T"
        and "wf_fmla Q \<phi>"
      shows "wf_fmla R (map_formula (map_atom f) \<phi>)"
    using assms
    by (induction \<phi>; auto simp: f_ent_def intro: ent_type_imp_wf_atom)


  lemma ent_type_imp_wf_pred:
    assumes "\<forall>e \<in> predicate.ent upd. \<forall>T. is_of_type Q e T \<longrightarrow> is_of_type R (f e) T"
        and "wf_pred Q upd"
      shows "wf_pred R (map_predicate f upd)"
      using assms 
      by (induction upd; auto split: option.splits simp: list_all2_is_of_type)

  lemma ent_type_imp_wf_preds:
    assumes "\<forall>e \<in> \<Union>(predicate.ent ` set upd). \<forall>T. is_of_type Q e T \<longrightarrow> is_of_type R (f e) T"
        and "\<forall>u \<in> set upd. wf_pred Q u"
      shows "\<forall>u \<in> set (map (map_predicate f) upd). wf_pred R u"
    using assms ent_type_imp_wf_pred by fastforce

  lemma ent_type_imp_wf_of_upd:
    assumes "\<forall>e \<in> of_upd.ent tu. \<forall>T. is_of_type Q e T \<longrightarrow> is_of_type R (f e) T"
    and "wf_of_upd Q tu"
    shows "wf_of_upd R (map_of_upd f tu)"
  proof (cases tu)
    case [simp]: (OF_Upd fn args r)
    from assms(2)
    obtain Ts T where
      a: "obj_fun_sig fn = Some (Ts, T)"
      "list_all2 (is_of_type Q) args Ts"
      "is_of_type Q (the r) T \<or> r = None"
      by (auto split: option.splits)
    from list_all2_is_of_type[OF assms(1)[simplified OF_Upd of_upd.set ball_Un, THEN conjunct1] a(2)]
    have "list_all2 (is_of_type R) (map f args) Ts" .
    moreover
    from a(3) assms(1)
    have "is_of_type R (the (map_option f r)) T \<or> map_option f r = None" by force
    ultimately 
    show ?thesis using of_upd.map[of f fn args r] using a(1) by auto
  qed

  lemma ent_type_imp_wf_of_upds:
    assumes "\<forall>e \<in> \<Union>(of_upd.ent ` set tu). \<forall>T. is_of_type Q e T \<longrightarrow> is_of_type R (f e) T"
        and "\<forall>u \<in> set tu. wf_of_upd Q u"
      shows "\<forall>u \<in> set (map (map_of_upd f) tu). wf_of_upd R u"
    using assms ent_type_imp_wf_of_upd by fastforce
  
  lemma ent_type_imp_wf_nf_upd:
    assumes "\<forall>e \<in> nf_upd.ent nu. \<forall>T. is_of_type Q e T \<longrightarrow> is_of_type R (f e) T"
      and "wf_nf_upd Q nu"
    shows "wf_nf_upd R (map_nf_upd f nu)"
    using assms by (cases nu; 
        auto split: option.splits intro: list_all2_is_of_type ent_type_imp_wf_num_fluent)
  
  lemma ent_type_imp_wf_nf_upds:
    assumes "\<forall>e \<in> \<Union>(nf_upd.ent ` set nu). \<forall>T. is_of_type Q e T \<longrightarrow> is_of_type R (f e) T"
        and "\<forall>u \<in> set nu. wf_nf_upd Q u"
      shows "\<forall>u \<in> set (map (map_nf_upd f) nu). wf_nf_upd R u"
    using assms ent_type_imp_wf_nf_upd by fastforce

  lemma ent_type_imp_wf_effect:
    assumes "\<forall>e \<in> ast_effect.ent eff. \<forall>T. is_of_type Q e T \<longrightarrow> is_of_type R (f e) T"
      and "wf_effect Q eff"
    shows "wf_effect R (map_ast_effect f eff)"
  proof (cases eff)
    case [simp]: (Effect a d tu nu)
    from assms(2)
    have "\<forall>u \<in> set a. (wf_pred Q) u" 
         "\<forall>u \<in> set d. (wf_pred Q) u"
         "\<forall>u \<in> set tu. (wf_of_upd Q) u"
         "\<forall>u \<in> set nu. (wf_nf_upd Q) u" by simp_all
    with assms(1)[simplified Effect ast_effect.set ball_Un] 
        ent_type_imp_wf_preds ent_type_imp_wf_of_upds ent_type_imp_wf_nf_upds
    show ?thesis 
      apply (subst Effect; subst ast_effect.map; subst wf_effect.simps)
      apply (elim conjE; intro conjI)
      by blast+
  qed

  lemma ent_type_imp_wf_cond_effect:
    assumes "\<forall>e \<in> cond_effect_ent ce. \<forall>T. is_of_type Q e T \<longrightarrow> is_of_type R (f e) T"
        and "wf_cond_effect Q ce"
      shows "wf_cond_effect R (map_cond_effect f ce)"
    using assms unfolding wf_cond_effect_def
    by (cases ce; auto intro: ent_type_imp_wf_effect ent_type_imp_wf_fmla)

  lemma ent_type_imp_wf_cond_effect_list:
    assumes "\<forall>eff \<in> set effs. \<forall>e \<in> cond_effect_ent eff. \<forall>T. is_of_type Q e T \<longrightarrow> is_of_type R (f e) T"
          and "wf_cond_effect_list Q effs"
        shows "wf_cond_effect_list R (map (map_cond_effect f) effs)"
    using assms(2, 1) unfolding wf_cond_effect_list_def
    apply (induction effs)
    using ent_type_imp_wf_cond_effect by force+

  
  lemma ent_type_imp_wf_fmla_strong:
    assumes "\<And>e T. is_of_type Q e T \<Longrightarrow> is_of_type R (f e) T"
          and "wf_fmla Q \<phi>"
        shows "wf_fmla R (map_formula (map_atom f) \<phi>)"
    using ent_type_imp_wf_fmla[OF _ assms(2)] assms(1)
    by blast

  lemma ent_type_imp_wf_cond_effect_strong:
    assumes "\<And>e T. is_of_type Q e T \<Longrightarrow> is_of_type R (f e) T"
        and "wf_cond_effect Q ce"
      shows "wf_cond_effect R (map_cond_effect f ce)"
    using ent_type_imp_wf_cond_effect[OF _ assms(2)] assms(1)
    by blast
  
  lemma ent_type_imp_wf_cond_effect_list_strong:
    assumes "\<And>e T. is_of_type Q e T \<Longrightarrow> is_of_type R (f e) T"
        and "wf_cond_effect_list Q effs"
      shows "wf_cond_effect_list R (map (map_cond_effect f) effs)"
    using ent_type_imp_wf_cond_effect_list[OF _ assms(2)] assms(1)
    by blast
  text \<open>lifting type preservation from entities to terms\<close>

  (* Using the mutual induction rule resulted in an uglier proof *)

  lemma ty_term_is_of_type_lift':
  assumes f_ent: "\<And>e T. e \<in> sym t \<Longrightarrow> is_of_type Q e T \<Longrightarrow> is_of_type R (f e) T"
            and "is_term_of_type Q t T"
          shows "is_term_of_type R (map_term f t) T"
    using assms
  proof (induction t arbitrary: T)
    case (Fun fn ts)
    from \<open>is_term_of_type Q (Fun fn ts) T\<close> 
    obtain T' Ts where
      "ty_term Q (Fun fn ts) = Some T'"
      "of_type T' T"
      "obj_fun_sig fn = Some (Ts, T')"
      "list_all2 (is_term_of_type Q) ts Ts"
      unfolding is_of_type_def
      by (auto split: option.splits prod.splits if_splits)
    from this(4) Fun.IH Fun.prems(1)
    have "list_all2 (is_term_of_type R) (map (map_term f) ts) Ts"
      by (induction rule: list_all2_induct) auto
    with \<open>obj_fun_sig fn = Some (Ts, T')\<close> \<open>of_type T' T\<close>
    show ?case by fastforce
  next
    case (Sym x)
    then show ?case using f_ent unfolding is_of_type_def by simp
  qed

  lemma ty_term_is_of_type_lift:
    assumes f_ent: "\<And>e T. e \<in> sym t \<Longrightarrow> is_of_type Q e T \<Longrightarrow> is_of_type R (f e) T"
            and "is_of_type (ty_term Q) t T"
          shows "is_of_type (ty_term R) (map_term f t) T"
  using assms ty_term_is_of_type_lift'
  unfolding is_term_of_type.simps(1) is_of_type_def
  by fast

  lemma ty_term_is_of_type_lift_weak:
    assumes f_ent: "\<And>e T. e \<in> sym t \<Longrightarrow> is_of_type Q e T \<Longrightarrow> is_of_type R e T"
        and "is_of_type (ty_term Q) t T"
      shows "is_of_type (ty_term R) t T"
  using assms ty_term_is_of_type_lift[where f = id, simplified term.map_id0]
  by force

  lemma ty_term_is_of_type_lift_strong:
    assumes "\<And>e T. is_of_type Q e T \<Longrightarrow> is_of_type R (f e) T"
        and "is_of_type (ty_term Q) t T"
      shows "is_of_type (ty_term R) (map_term f t) T"
    using ty_term_is_of_type_lift[OF _ assms(2)] assms(1)
    by blast

  lemma is_of_type_mono:
    assumes "Q \<subseteq>\<^sub>m R"
        and "is_of_type Q x T"
      shows "is_of_type R x T"
    using assms unfolding is_of_type_def 
    by (auto split: option.splits dest: map_leD)
  
  lemma ty_term_mono': (* clean up *)
    assumes "Q \<subseteq>\<^sub>m R"
      and "ty_term Q t = Some T"
    shows "ty_term R t = Some T"
  proof -
    have 1: "is_of_type (ty_term R) t T" 
      if "is_of_type (ty_term Q) t T" for T 
      using ty_term_is_of_type_lift[where f = id, 
          simplified term.map_id id_apply, OF _ that]
          is_of_type_mono[OF assms(1)] by blast
    have "of_type T T" using of_type_refl .
    with assms(2)
    have "is_of_type (ty_term Q) t T" unfolding is_of_type_def by simp
    with 1
    have "is_of_type (ty_term R) t T" unfolding is_of_type_def by simp
    then obtain T' where
      "ty_term R t = Some T'"
      "of_type T' T"
      unfolding is_of_type_def by (auto split: option.splits)
    show "ty_term R t = Some T" 
    proof (cases t)
      case [simp]: (Fun f xs)
      from assms(2)
      have "\<exists>Ts. obj_fun_sig f = Some (Ts, T)" 
        by (auto split: option.splits if_splits)
      with \<open>is_of_type (ty_term R) t T\<close>
      show ?thesis
        unfolding is_of_type_def 
        by (auto split: option.splits if_splits)
    next
      case [simp]: (Sym e)
      from assms(2)
      have "Q e = Some T" by simp
      with \<open>Q \<subseteq>\<^sub>m R\<close>
      have "R e = Some T" by (fast dest: map_leD)
      then show ?thesis by simp
    qed
  qed

  lemma ty_term_mono:
      assumes "Q \<subseteq>\<^sub>m R"
      shows "ty_term Q \<subseteq>\<^sub>m ty_term R"
    using ty_term_mono'[OF assms] map_leI by blast
  text \<open>weaker variations of the above\<close>

  lemma map_formula_map_atom_id: "map_formula (map_atom id) \<phi> = \<phi>"
    apply (subst atom.map_id0)
    by (rule formula.map_id)
    
  lemma ent_type_imp_wf_fmla_weak:
      assumes "\<forall>e \<in> f_ent \<phi>. \<forall>T. is_of_type Q e T \<longrightarrow> is_of_type R e T"
          and "wf_fmla Q \<phi>"
        shows "wf_fmla R \<phi>"
    using ent_type_imp_wf_fmla[where f = id,
              OF _ assms(2), simplified map_formula_map_atom_id] assms(1) by simp

  lemma ent_type_imp_wf_effect_weak:
    assumes "\<forall>e \<in> ast_effect.ent eff. \<forall>T. is_of_type Q e T \<longrightarrow> is_of_type R e T"
            and "wf_effect Q eff"
          shows "wf_effect R eff"
    using ent_type_imp_wf_effect[where f = id,
                OF _ assms(2), simplified ast_effect.map_id] assms(1) by simp
  
  lemma wf_fmla_mono:
    assumes "Q \<subseteq>\<^sub>m R"
        and "wf_fmla Q \<phi>"
      shows "wf_fmla R \<phi>"
    using is_of_type_mono[OF assms(1)] ent_type_imp_wf_fmla_weak[OF _ assms(2)]
    by blast

  lemma wf_effect_mono:
      assumes "Q \<subseteq>\<^sub>m R"
          and "wf_effect Q eff"
        shows "wf_effect R eff"
    using is_of_type_mono[OF assms(1)] ent_type_imp_wf_effect_weak[OF _ assms(2)]
    by blast

  lemma wf_cond_effect_mono:
      assumes "Q \<subseteq>\<^sub>m R"
          and "wf_cond_effect Q eff"
        shows "wf_cond_effect R eff"
    using assms
    apply (cases eff)
    using wf_effect_mono wf_fmla_mono unfolding wf_cond_effect_def by fastforce
  
  fun subst_sym_with_obj where
    "subst_sym_with_obj psubst (Var x) = psubst x"
  | "subst_sym_with_obj psubst (Const c) = c"

  fun inst_sym where
  "inst_sym params as = subst_sym_with_obj (the o (map_of (zip (map fst params) as)))"


  fun inst_term::"(variable \<times> type) list \<Rightarrow> object list \<Rightarrow> symbol term \<Rightarrow> object term" where
  "inst_term params as = map_term (inst_sym params as)"
                            
  abbreviation map_pre where
  "map_pre t pre \<equiv> (map_formula (map_atom t)) pre" 

  lemma INST_sym_to_obj:
    assumes var_to_obj: "\<forall>x \<in> sym_vars s. is_of_type Q x T \<longrightarrow> is_of_type R (f x) T"
        and "is_of_type (ty_sym Q R) s T"
    shows "is_of_type R (subst_sym_with_obj f s) T"
    using assms unfolding is_of_type_def
    by (cases s; auto split: option.splits)
  

end \<comment> \<open>locale \<open>ast_problem_decs\<close>\<close>

context ast_problem_decs
begin

text \<open>A well-formed goal is a well-formed formula without any free variables\<close>

  lemma sym_vars_in_var_dom:
    assumes "s \<in> dom (ty_sym Q R)"
    shows "sym_vars s \<subseteq> dom Q"
    using assms by (cases s; auto)
   
  lemma ty_sym_dom_vars:
    assumes "sym t \<subseteq> dom (ty_sym Q R)"
      shows "term_vars t \<subseteq> dom Q"
    using assms sym_vars_in_var_dom term_vars_def by blast
  
  lemma ty_sym_term_imp_var_in_dom:
    assumes "t \<in> dom (ty_term (ty_sym Q R))"
      shows "term_vars t \<subseteq> dom Q"
    using assms[THEN ty_term_ent_dom', THEN ty_sym_dom_vars] .

  text \<open>The variables that are present in a well-formed formula must be in the type environment\<close>
  
  lemma wf_fmla_vars:
    assumes "wf_fmla (ty_term (ty_sym Q R)) \<phi>"
      shows "f_vars \<phi> \<subseteq> dom Q"
  proof -
    from assms
    have "\<forall>t \<in> f_ent \<phi>. t \<in> dom (ty_term (ty_sym Q R))" 
      using wf_fmla_imp_ent_in_ty_env by blast
    hence "\<forall>t \<in> f_ent \<phi>. term_vars t \<subseteq> dom Q" 
      using ty_sym_term_imp_var_in_dom by fast
    thus "f_vars \<phi> \<subseteq> dom Q" 
      using f_vars_as_f_ent
      by (auto simp add: UN_subset_iff formula.set_map)
  qed

  text \<open>This section shows how restrictions in the type environment can preserve well-formedness.\<close>

  lemma ty_term_vars_restr: 
    assumes "e \<in> sym t"
        and "ty_sym Q R e = Some T"
      shows "ty_sym (Q |` (term_vars t)) R e = Some T"
  proof -
    from assms(1)
    have a: "sym_vars e \<subseteq> term_vars t" unfolding term_vars_def by blast
    from assms(2)
    have "ty_sym (Q |` (sym_vars e)) R e = Some T" by (cases e; auto)
    with ty_sym_mono[OF map_restrict_mono[OF a] map_le_refl]
    show "ty_sym (Q |` (term_vars t)) R e = Some T" by (auto dest: map_leD)
  qed

  lemma is_of_type_ty_sym_term_vars_restr:
    assumes "e \<in> sym t"
        and "is_of_type (ty_sym Q R) e T" 
      shows "is_of_type (ty_sym (Q |` (term_vars t)) R) e T"
    using assms ty_term_vars_restr unfolding is_of_type_def
    by (auto split: option.splits)

  lemma is_of_type_term_vars_restr:
    assumes "is_of_type (ty_term (ty_sym Q R)) t T"
    shows "is_of_type (ty_term (ty_sym (Q |` (term_vars t)) R)) t T"
    using ty_term_is_of_type_lift_weak[OF _ assms] is_of_type_ty_sym_term_vars_restr
    by force

  lemma is_of_type_f_vars_restr:
  assumes "t \<in> f_ent \<phi>"
      and "is_of_type (ty_term (ty_sym Q R)) t T"
    shows "is_of_type (ty_term (ty_sym (Q |` (f_vars \<phi>)) R)) t T"
  proof -
    from is_of_type_term_vars_restr[OF assms(2)]
    have a: "is_of_type (ty_term (ty_sym (Q |` term_vars t) R)) t T" .
    from assms(1)
    have "term_vars t \<subseteq> f_vars \<phi>" using f_vars_as_f_ent by fast
    from is_of_type_mono[OF ty_term_mono[OF ty_sym_mono[OF map_restrict_mono[OF this] map_le_refl]] a]
    show "is_of_type (ty_term (ty_sym (Q |` (f_vars \<phi>)) R)) t T" .
  qed

  lemma wf_fmla_restr_vars':
    assumes "wf_fmla (ty_term (ty_sym Q R)) \<phi>" 
      shows "wf_fmla (ty_term (ty_sym (Q |` (f_vars \<phi>)) R)) \<phi>"
    using ent_type_imp_wf_fmla_weak[OF _ assms] 
      is_of_type_f_vars_restr by blast

  lemma wf_fmla_restr_vars:
    "wf_fmla (ty_term (ty_sym Q S)) \<phi> \<longleftrightarrow> wf_fmla (ty_term (ty_sym (Q |` (f_vars \<phi>)) S)) \<phi>"
    using wf_fmla_restr_vars' wf_fmla_mono[OF ty_term_mono[OF ty_sym_mono[OF map_restrict_less[of Q "f_vars \<phi>"] map_le_refl]]]
    by blast

  lemma wf_fmla_alt_lemma: 
  assumes "Q \<subseteq>\<^sub>m R"
    shows "wf_fmla (ty_term (ty_sym Q S)) \<phi> \<longleftrightarrow> wf_fmla (ty_term (ty_sym R S)) \<phi> \<and> f_vars \<phi> \<subseteq> dom Q"
  proof (rule iffI)
    assume a: "wf_fmla (ty_term (ty_sym Q S)) \<phi>"
    from wf_fmla_mono[OF ty_term_mono[OF ty_sym_mono[OF assms(1) map_le_refl]] this]
    have "wf_fmla (ty_term (ty_sym R S)) \<phi>" .
    with wf_fmla_vars[OF a]
    show "wf_fmla (ty_term (ty_sym R S)) \<phi> \<and> f_vars \<phi> \<subseteq> dom Q" by blast
  next
    assume"wf_fmla (ty_term (ty_sym R S)) \<phi> \<and> f_vars \<phi> \<subseteq> dom Q"
    thus "wf_fmla (ty_term (ty_sym Q S)) \<phi>" 
      using wf_fmla_restr_vars[of Q S] wf_fmla_restr_vars[of R S] 
            map_le_restr[OF assms(1)] by simp
  qed

  text \<open>An alternative definition for the well-formedness of a goal\<close>
  theorem wf_goal_alt: "wf_goal \<phi> \<longleftrightarrow> wf_fmla (ty_term (ty_sym Q objT)) \<phi> \<and> f_vars \<phi> = {}"
    using wf_fmla_alt_lemma[where Q = Map.empty] unfolding wf_goal_def by simp


 lemma is_of_type_eff_vars_restr:
  assumes "t \<in> ast_effect.ent eff"
      and "is_of_type (ty_term (ty_sym Q R)) t T"
    shows "is_of_type (ty_term (ty_sym (Q |` (eff_vars eff)) R)) t T"
  proof -
    from is_of_type_term_vars_restr[OF assms(2)]
    have a: "is_of_type (ty_term (ty_sym (Q |` term_vars t) R)) t T" .
    from assms(1)
    have "term_vars t \<subseteq> eff_vars eff" using eff_vars_as_eff_ent by fast
    from is_of_type_mono[OF ty_term_mono[OF ty_sym_mono[OF map_restrict_mono[OF this] map_le_refl]] a]
    show "is_of_type (ty_term (ty_sym (Q |` (eff_vars eff)) R)) t T" .
  qed
  
  lemma wf_effect_restr_vars':
    assumes "wf_effect (ty_term (ty_sym Q R)) eff" 
    shows "wf_effect (ty_term (ty_sym (Q |` (eff_vars eff)) R)) eff"
    using ent_type_imp_wf_effect_weak[OF _ assms] 
        is_of_type_eff_vars_restr by blast

  lemma wf_effect_restr_vars:
    "wf_effect (ty_term (ty_sym Q S)) eff 
    \<longleftrightarrow> wf_effect (ty_term (ty_sym (Q |` (eff_vars eff)) S)) eff"
    using wf_effect_restr_vars' 
      wf_effect_mono[OF 
        ty_term_mono[OF 
          ty_sym_mono[OF map_restrict_less[of Q "eff_vars eff"] map_le_refl]]] by blast
end

subsection \<open>Quantifiers\<close>
context ast_problem_decs
begin
  text \<open>Filter those constants in the domain that belong to the type.\<close>
  definition t_dom::"type \<Rightarrow> object list" where
  "t_dom typ \<equiv> map fst (filter (\<lambda>(c, t). of_type t typ) (consts DD @ objects PD))"

  definition all::"variable \<Rightarrow> type \<Rightarrow> schematic_formula \<Rightarrow> schematic_formula" ("\<^bold>\<forall>_ - _._") where
    "all v t \<phi> \<equiv> (if (v \<notin> f_vars \<phi> \<and> (t_dom t \<noteq> [])) then \<phi> else \<^bold>\<And>(map (\<lambda>c. f_subst v c \<phi>) (t_dom t)))"
                                                                  
  definition exists::"variable \<Rightarrow> type \<Rightarrow> schematic_formula \<Rightarrow> schematic_formula" ("\<^bold>\<exists>_ - _._") where
    "exists v t \<phi> \<equiv> (if (v \<notin> f_vars \<phi> \<and> (t_dom t \<noteq> [])) then \<phi> else \<^bold>\<Or>(map (\<lambda>c. f_subst v c \<phi>) (t_dom t)))"

lemma "s = {} \<Longrightarrow> \<not>(\<exists> a \<in> s. P a)" by blast

lemma "s = {} \<Longrightarrow> (\<forall>a \<in> s. \<forall>a \<in> t. \<not>(\<exists>b. a = b))" by blast
  
  text \<open>PDDL quantifiers act on typed lists of variables\<close>
  text \<open>This function removes duplicate parameters, keeping the last occurrence. It is not necessary. \<close>
  fun unique_vars'::"(variable \<times> type) list \<Rightarrow> (variable \<times> type) list \<times> variable set" where
    "unique_vars' [] = ([], {})"
  | "unique_vars' ((v, t)#ps) = (let (ps', s) = unique_vars' ps in (if v \<in> s then (ps', s) else (((v, t)#ps'), insert v s)))"

  abbreviation "unique_vars \<equiv> fst o unique_vars'"

  text \<open>Why do we need \<^term>\<open>unique_vars\<close>? \<close>
  definition pddl_all::"(variable \<times> type) list \<Rightarrow> schematic_formula \<Rightarrow> schematic_formula" where
    "pddl_all ps \<phi> = foldr (\<lambda>(v, t) \<phi>. (\<^bold>\<forall> v - t. \<phi>)) ps \<phi>"

  text \<open>We do not need \<^term>\<open>unique_vars\<close>, because the quantifiers individually handle 
        cases where variables have been bound by the nested quantifiers. \<close>
  definition pddl_exists::"(variable \<times> type) list \<Rightarrow> schematic_formula \<Rightarrow> schematic_formula" where
    "pddl_exists ps \<phi> = foldr (\<lambda>(v, t) \<phi>. (\<^bold>\<exists> v - t. \<phi>)) ps \<phi>"

  text \<open>We only need to distinguish whether the variable is present in the effect. 
      Assume the variable is not in the effect: we apply it, regardless of the size
      of the domain. 

      Assume the variable exists in the effect: 
        - if the domain is empty, we get an empty list
        - if the domain is not empty, we create a larger list of effects to apply\<close>
  definition univ_effect::"variable \<Rightarrow> type 
    \<Rightarrow> (schematic_formula \<times> schematic_effect) 
    \<Rightarrow> (schematic_formula \<times> schematic_effect) list" where
    "univ_effect v t ce = (
      if (v \<notin> cond_effect_vars ce) 
      then [ce] 
      else (map (\<lambda>c. cond_effect_subst v c ce) (t_dom t)))"

  definition univ_effect_list::"variable \<Rightarrow> type \<Rightarrow> (schematic_formula \<times> schematic_effect) list 
    \<Rightarrow> (schematic_formula \<times> schematic_effect) list"  where 
  "univ_effect_list v t effs \<equiv> (flatmap (univ_effect v t) effs)"
  
  definition pddl_univ_effect_list::"(variable \<times> type) list \<Rightarrow> (schematic_formula \<times> schematic_effect) list
    \<Rightarrow> (schematic_formula \<times> schematic_effect) list" where
  "pddl_univ_effect_list vts effs \<equiv> (foldr (\<lambda>(v, t) effs. univ_effect_list v t effs) vts effs)"
   
  lemma v_in_unique_vars': "(v, t) \<in> set ps \<Longrightarrow> v \<in> snd (unique_vars' ps)"
  proof (induction ps)
    case (Cons p ps)
    obtain v' t' where
      v': "p = (v', t')"
      by fastforce
    show ?case 
    proof cases
      assume "(v, t) \<in> set ps"
      hence "v \<in> snd (unique_vars' ps)" using Cons.IH by blast
      show ?thesis
      proof (cases "v' \<in> snd (unique_vars' ps)")
        case True
        with v'
        have "unique_vars' (p # ps) = unique_vars' ps" by (auto simp: Let_def split: prod.split)
        with \<open>v \<in> snd (unique_vars' ps)\<close>
        show ?thesis by simp
      next
        case False
        with v'
        have "snd (unique_vars' (p # ps)) = insert v' (snd (unique_vars' ps))" by (auto simp: Let_def split: prod.split)
        with \<open>v \<in> snd (unique_vars' ps)\<close>
        show ?thesis by blast
      qed
    next
      assume "(v, t) \<notin> set ps"
      with v' Cons.prems
      show ?thesis by (auto simp: Let_def split: prod.split)
    qed
  qed simp
  
  lemma unique_vars_unique: "\<exists>t1. (v, t1) \<in> set ps \<Longrightarrow> unique_vars ((v, t2)#ps) = unique_vars ps"
  proof -
    assume "\<exists>t1. (v, t1) \<in> set ps"
    hence "v \<in> snd (unique_vars' ps)" using v_in_unique_vars' by blast
    thus "unique_vars ((v, t2)#ps) = unique_vars ps" by (auto simp: Let_def split: prod.split)
  qed

lemma big_and_replaces:
  assumes "\<forall>\<phi> \<in> set \<phi>s. v \<notin> f_vars \<phi>" 
  shows "v \<notin> f_vars (\<^bold>\<And>(\<phi>s))"
  using assms
  unfolding f_vars_def
  by fastforce

lemma big_or_replaces:
  assumes "\<forall>\<phi> \<in> set \<phi>s. v \<notin> f_vars \<phi>" 
  shows "v \<notin> f_vars (\<^bold>\<Or>(\<phi>s))"
  using assms
  unfolding f_vars_def
  by (induction \<phi>s; auto)
  
lemma all_replaces: "v \<notin> f_vars (\<^bold>\<forall>v - t. \<phi>)"
  unfolding all_def
  using f_subst_replaces big_and_replaces 
  by simp

lemma exists_replaces: "v \<notin> f_vars (\<^bold>\<exists>v - t. \<phi>)"
  unfolding exists_def
  using f_subst_replaces big_or_replaces
  by simp

end

locale wf_problem_decs = ast_problem_decs +
  assumes wf_problem_decs: wf_problem_decs
begin


lemma distinct_objs': "distinct (map (obj_name \<circ> fst) (consts DD) @ map (obj_name \<circ> fst) (objects PD)) \<Longrightarrow> distinct (map fst ((objects PD) @ (consts DD)))"
  apply (subst (asm) distinct_append)
  apply (subst (asm) Int_commute)
  apply (subst (asm) conj_assoc[symmetric])
  apply (subst (asm) conj_commute)
  apply (subst (asm) conj_assoc)
  apply (subst (asm) distinct_append[symmetric])
  apply (subst (asm) map_append[symmetric])
  apply (subst (asm) map_map[symmetric])
  by (rule distinct_mapI[where f = obj_name])

lemma distinct_objs: "distinct (map fst (objects PD @ consts DD))"
  using wf_problem_decs distinct_objs'
  unfolding wf_problem_decs_def
  by simp

  text \<open>The correctness of t_dom\<close>
  lemma t_dom_corr: "objT obj = Some t \<Longrightarrow> of_type t T \<longleftrightarrow> obj \<in> set (t_dom T)"
  proof -                                   
    assume "objT obj = Some t"
    hence "map_of (consts DD @ objects PD) obj = Some t"
      using objT_alt by argo
    moreover
    from wf_problem_decs
    have "distinct (map fst (objects PD @ consts DD))"
      using distinct_objs by simp
    moreover
    have "t_dom T = map fst (filter (\<lambda>(c, t). of_type t T) (consts DD @ objects PD))"
      unfolding t_dom_def by simp 
    ultimately
    show "of_type t T \<longleftrightarrow> obj \<in> set (t_dom T)" by fastforce+
  qed



  text \<open>The circumstances under which using a quantifier will result in a well-formed formula\<close>
  lemma c_ty: "\<forall>obj \<in> set (t_dom ty). \<exists>ty'. objT obj = Some ty' \<and> of_type ty' ty"
  proof 
    fix obj
    assume "obj \<in> set (t_dom ty)"
    hence "obj \<in> set (map fst (filter (\<lambda>(c, t) \<Rightarrow> of_type t ty) (consts DD @ objects PD)))"
      unfolding t_dom_def by blast
    then obtain t where
      "(obj,t) \<in> set (consts DD @ objects PD)" 
      "of_type t ty"
      unfolding t_dom_def by fastforce
    from wf_problem_decs
    have "distinct (map fst (consts DD @ objects PD))"
      using distinct_objs by auto
    from map_of_is_SomeI[OF this] \<open>(obj,t) \<in> set (consts DD @ objects PD)\<close>
    have "map_of (consts DD @ objects PD) obj = Some t" by auto
    with \<open>of_type t ty\<close>
    show "\<exists>ty'. objT obj = Some ty' \<and> of_type ty' ty"
      using objT_alt by auto
  qed

  lemma subst_type:
    assumes "v \<in> sym_vars s"
        and "R c = Some ty"
    shows "ty_sym Q R (sym_subst v c s) = Some ty"
    using assms sym_subst_v
    by simp
  
  lemma not_in_sym_vars_imp_typed:
  assumes "v \<notin> sym_vars s"
      and "ty_sym Q R s = Some T"
    shows "ty_sym (Q(v:=None)) R s = Some T"
    using assms by (cases s; fastforce)

  lemma subst_imp_not_in_vars:
    "v \<notin> sym_vars (sym_subst v c s)"
    by (cases s; auto)
  
  lemma quant_sym_inst: 
    assumes "c \<in> set (t_dom ty)"
        and "is_of_type (ty_sym (Q(v\<mapsto>ty)) objT) s T"
      shows "is_of_type (ty_sym Q objT) (sym_subst v c s) T"
  proof -
    from \<open>c \<in> set (t_dom ty)\<close>
    obtain ty' where 
      "objT c = Some ty'"
      "of_type ty' ty" 
    using c_ty by blast
    show "is_of_type (ty_sym Q objT) (sym_subst v c s) T"
    proof cases
      assume "v \<in> sym_vars s"
      from subst_type[OF \<open>v \<in> sym_vars s\<close>] \<open>objT c = Some ty'\<close> 
      have "ty_sym Q objT (sym_subst v c s) = Some ty'" by force
      from \<open>v \<in> sym_vars s\<close>
      have "s = Var v" by (cases s; simp)
      with \<open>is_of_type (ty_sym (Q(v\<mapsto>ty)) objT) s T\<close> 
      have "of_type ty T" unfolding is_of_type_def by simp+
      from of_type_trans[OF \<open>of_type ty' ty\<close> this] \<open>ty_sym Q objT (sym_subst v c s) = Some ty'\<close>
      show "is_of_type (ty_sym Q objT) (sym_subst v c s) T"
        by (auto split: option.splits simp: is_of_type_def)
    next
      assume "v \<notin> sym_vars s"
      from sym_subst_idem[OF this]
      have "(sym_subst v c s) = s" by presburger
      from \<open>v \<notin> sym_vars s\<close> \<open>is_of_type (ty_sym (Q(v\<mapsto>ty)) objT) s T\<close>
      have "is_of_type (ty_sym (Q(v\<mapsto>ty)) objT) (sym_subst v c s) T" by (cases s; auto)
      then obtain ty' where
        "(ty_sym (Q(v\<mapsto>ty)) objT) (sym_subst v c s) = Some ty'"
        "of_type ty' T"
        unfolding is_of_type_def by (auto split: option.splits)
      moreover
      have "v \<notin> sym_vars (sym_subst v c s)" by (cases s; auto)
      ultimately
      have "(ty_sym Q objT) (sym_subst v c s) = Some ty'" by (cases "sym_subst v c s"; auto)
      with \<open>of_type ty' T\<close>
      show "is_of_type (ty_sym Q objT) (sym_subst v c s) T" unfolding is_of_type_def by force
    qed
  qed

  lemma quant_sym_inst':
      assumes "c \<in> set (t_dom ty)"
          and "is_of_type (ty_sym (Q(v\<mapsto>ty)) objT) s T"
        shows "is_of_type (ty_sym (Q(v:=None)) objT) (sym_subst v c s) T"
    using quant_sym_inst[OF assms(1) assms(2)] not_in_sym_vars_imp_typed[OF subst_imp_not_in_vars]
    unfolding is_of_type_def by (auto split: option.splits)

  lemma term_upd_type:
    assumes "c \<in> set (t_dom ty)"
        and "is_of_type (ty_term (ty_sym (Q(v\<mapsto>ty)) objT)) t T" 
    shows "is_of_type (ty_term (ty_sym (Q(v:=None)) objT)) (term_subst v c t) T"
    using ty_term_is_of_type_lift_strong[OF _ assms(2)] quant_sym_inst'[OF assms(1)]
    unfolding term_subst_def
    by blast

  lemma wf_quant_fmla_inst: 
    assumes "c \<in> set (t_dom ty)"
        and "wf_fmla (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) \<phi>"
      shows "wf_fmla (ty_term (ty_sym (Q(v := None)) objT)) (f_subst v c \<phi>)"
    using term_upd_type[OF assms(1)] ent_type_imp_wf_fmla[OF _ assms(2)]
    unfolding f_subst_def atom_subst_def by blast


  lemma wf_fmlas_t_dom_map:
    assumes "wf_fmla (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) \<phi>"
    shows "list_all (wf_fmla (ty_term (ty_sym (Q(v := None)) objT))) 
        (map (\<lambda>c. f_subst v c \<phi>) (t_dom ty))"
    using assms wf_quant_fmla_inst
    by (subst sym[OF Ball_set], simp)

  lemma wf_cond_effect_inst:
    assumes "c \<in> set (t_dom ty)"
        and "wf_cond_effect (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) eff"
      shows "wf_cond_effect (ty_term (ty_sym (Q(v := None)) objT)) (cond_effect_subst v c eff)"
    using term_upd_type[OF assms(1)] ent_type_imp_wf_cond_effect_strong[OF _ assms(2)] 
    unfolding cond_effect_subst_alt
    by blast

  lemma wf_cond_effect_t_dom_map:
    assumes "wf_cond_effect (ty_term (ty_sym (Q (v \<mapsto> ty)) objT)) ce"
    shows "wf_cond_effect_list (ty_term (ty_sym (Q(v := None)) objT))
        (map (\<lambda>c. cond_effect_subst v c ce) (t_dom ty))"
    using assms wf_cond_effect_inst
    unfolding wf_cond_effect_list_def list_all_iff 
    by auto

  lemma wf_fmla_upd: 
    assumes "v \<notin> f_vars \<phi>"
    shows "wf_fmla (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) \<phi> 
          \<longleftrightarrow> wf_fmla (ty_term (ty_sym (Q(v := None)) objT)) \<phi>"
  proof -
    from \<open>v \<notin> f_vars \<phi>\<close>
    have "Q(v \<mapsto> ty) |` (f_vars \<phi>)
        = Q(v := None) |` (f_vars \<phi>)" by simp
    thus "wf_fmla (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) \<phi> 
        = wf_fmla (ty_term (ty_sym (Q(v := None)) objT)) \<phi>" 
      using wf_fmla_restr_vars[of "Q(v \<mapsto> ty)" objT \<phi>] 
        wf_fmla_restr_vars[of "Q(v := None)" objT \<phi>] by argo
  qed

  lemma wf_effect_upd:
    assumes "v \<notin> eff_vars eff"
    shows "wf_effect (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) eff
            \<longleftrightarrow> wf_effect (ty_term (ty_sym (Q(v := None)) objT)) eff"
  proof -
    from \<open>v \<notin> eff_vars eff\<close>
    have "Q(v \<mapsto> ty) |` (eff_vars eff) = Q(v := None) |` (eff_vars eff)" by simp
    thus "wf_effect (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) eff
            \<longleftrightarrow> wf_effect (ty_term (ty_sym (Q(v := None)) objT)) eff"
      using wf_effect_restr_vars[of "Q(v \<mapsto> ty)" objT eff] 
            wf_effect_restr_vars[of "Q(v := None)" objT eff] by argo
  qed

  lemma wf_cond_effect_upd:
    assumes "v \<notin> cond_effect_vars ce"
    shows "wf_cond_effect (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) ce
          \<longleftrightarrow> wf_cond_effect (ty_term (ty_sym (Q(v := None)) objT)) ce"
    using wf_fmla_upd wf_effect_upd assms
    by (cases "ce"; auto simp: wf_cond_effect_def)

  lemma Big_Or_wf_comm: "list_all (wf_fmla Q) \<phi>s \<longleftrightarrow> wf_fmla Q (\<^bold>\<Or> \<phi>s)"
    by (induction \<phi>s) auto
  
  lemma Big_And_wf_comm: "list_all (wf_fmla Q) \<phi>s \<longleftrightarrow> wf_fmla Q (\<^bold>\<And> \<phi>s)"
    by (induction \<phi>s) auto
  
  lemma wf_Big_Or:
    assumes "wf_fmla (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) \<phi>"
    shows "wf_fmla (ty_term (ty_sym (Q(v := None)) objT))
      (\<^bold>\<Or>(map (\<lambda>c. (f_subst v c \<phi>)) (t_dom ty)))"
    using wf_fmlas_t_dom_map[OF assms] Big_Or_wf_comm
    by blast
  
  lemma wf_Big_And:
    assumes "wf_fmla (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) \<phi>"
    shows "wf_fmla (ty_term (ty_sym (Q(v := None)) objT))
      (\<^bold>\<And>(map (\<lambda>c. (f_subst v c \<phi>)) (t_dom ty)))"
    using wf_fmlas_t_dom_map[OF assms] Big_And_wf_comm
    by blast
  
  lemma wf_exist_distrib_f':
    assumes "wf_fmla (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) \<phi>" 
      shows "wf_fmla (ty_term (ty_sym (Q(v := None)) objT)) \<^bold>\<exists>v - ty. \<phi>"
    using wf_Big_Or[OF assms] wf_fmla_upd assms unfolding exists_def by auto

  lemma wf_exist_distrib_f:
    assumes "wf_fmla (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) \<phi>" 
      shows "wf_fmla (ty_term (ty_sym Q objT)) \<^bold>\<exists>v - ty. \<phi>"
    using wf_fmla_mono[OF ty_term_mono[OF ty_sym_mono[OF _ map_le_refl]], OF _ wf_exist_distrib_f'[OF assms]]
    by simp
    
  
  (* Note: The other direction cannot be proven from these definitions. 
    Quantifiers expand into long con-/disjunctions 
    by substitution of variables for all suitably typed constants. 
    Assume there is a pred P::t2 \<Rightarrow> bool, a variable v::t1, t2 \<subseteq> t1, 
    and the only object o1 in the domain of t1 has a type t2. In this case, P(v) is not
    well-formed, but the instantiation P(o1) is. *)

  lemma wf_ex_goal: 
    assumes "wf_fmla (ty_term (ty_sym [v \<mapsto> ty] objT)) \<phi>" 
      shows "wf_goal \<^bold>\<exists>v - ty. \<phi>"
    unfolding wf_goal_def 
    using wf_exist_distrib_f'[OF assms] by simp

  lemma wf_ex_goal_alt:
    assumes "wf_fmla (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) \<phi>"
        and "f_vars \<phi> \<subseteq> {v}"
      shows "wf_goal \<^bold>\<exists>v - ty. \<phi>"                 
    using wf_fmla_alt_lemma[of "Map.empty(v \<mapsto> ty)" "(Q(v \<mapsto> ty))"] assms wf_ex_goal
    by simp
  
  lemma wf_univ_inst':
    assumes "wf_fmla (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) \<phi>" 
      shows "wf_fmla (ty_term (ty_sym (Q(v := None)) objT)) \<^bold>\<forall>v - ty. \<phi>"
    using wf_Big_And[OF assms] wf_fmla_upd assms unfolding all_def by auto

  lemma wf_univ_inst:
    assumes "wf_fmla (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) \<phi>" 
      shows "wf_fmla (ty_term (ty_sym Q objT)) \<^bold>\<forall>v - ty. \<phi>"
    using wf_fmla_mono[OF ty_term_mono[OF ty_sym_mono[OF _ map_le_refl]], OF _ wf_univ_inst'[OF assms]]
    by simp
  

  lemma wf_univ_goal: 
    assumes "wf_fmla (ty_term (ty_sym [v \<mapsto> ty] objT)) \<phi>" 
      shows "wf_goal \<^bold>\<forall>v - ty. \<phi>"
    unfolding wf_goal_def 
    using wf_univ_inst'[OF assms] by simp

  lemma wf_univ_goal_alt:
    assumes "wf_fmla (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) \<phi>"
        and "f_vars \<phi> \<subseteq> {v}"
      shows "wf_goal \<^bold>\<forall>v - ty. \<phi>"                 
    using wf_fmla_alt_lemma[of "Map.empty(v \<mapsto> ty)" "(Q(v \<mapsto> ty))"] assms wf_univ_goal
    by simp
  
  lemma wf_univ_effect_inst': 
    assumes "wf_cond_effect (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) ce"
    shows "wf_cond_effect_list (ty_term (ty_sym (Q(v := None)) objT)) (univ_effect v ty ce)"
    using wf_cond_effect_t_dom_map[OF assms] wf_cond_effect_upd assms 
    unfolding univ_effect_def wf_cond_effect_list_def
    by (cases "v \<notin> cond_effect_vars ce"; auto)
  
  lemma wf_univ_effect_inst: (* The second Q could be an arbitrary R which is a larger map than Q *)
    assumes "wf_cond_effect (ty_term (ty_sym (Q(v \<mapsto> ty)) objT)) ce"
    shows "wf_cond_effect_list (ty_term (ty_sym Q objT)) (univ_effect v ty ce)"
    using wf_univ_effect_inst'[OF assms]
    unfolding wf_cond_effect_list_def
    apply (simp add: list_all_iff)
    using wf_cond_effect_mono[OF ty_term_mono[OF ty_sym_mono[of "Q(v := None)" Q, OF _ map_le_refl]]]
    by simp
 (* Thinking about these only makes sense, if we implement a well-formedness check
    as a step before applying/expanding the universal effects. We never do.  *)
  
  lemma list_all_flatmap: "list_all (list_all P) (map f xs) \<longleftrightarrow> list_all P (flatmap f xs)"
    by (induction xs; auto)


  lemma wf_univ_effect_list_inst:
    assumes "wf_cond_effect_list (ty_term (ty_sym (Q (v \<mapsto> ty)) objT)) ces" (is "wf_cond_effect_list ?Q ces")
    shows "wf_cond_effect_list (ty_term (ty_sym Q objT)) (univ_effect_list v ty ces)" (is "wf_cond_effect_list ?R (univ_effect_list v ty ces)")
  proof -
    from assms(1)
    have "list_all (wf_cond_effect ?Q) ces" unfolding wf_cond_effect_list_def
      by blast
    from list.pred_mono_strong[OF this]
    have "list_all ((wf_cond_effect_list ?R) o (univ_effect v ty)) ces"
      using wf_univ_effect_inst[of Q v ty] by simp
    hence "list_all (wf_cond_effect_list ?R) (map (univ_effect v ty) ces)"
      using list.pred_map by blast
    then show "wf_cond_effect_list ?R (univ_effect_list v ty ces)"
      unfolding wf_cond_effect_list_def univ_effect_list_def
      using list_all_flatmap by auto
  qed
  
  definition upd_ty_env::"(variable \<rightharpoonup> type) \<Rightarrow> (variable \<times> type) list \<Rightarrow> (variable \<rightharpoonup> type)" where
    "upd_ty_env te params \<equiv> fold (\<lambda>(v, ty) Q. Q(v \<mapsto> ty)) params te"
  
  lemma wf_pddl_univ_effect_list_inst: 
    assumes "wf_cond_effect_list (ty_term (ty_sym (upd_ty_env Q vts) objT)) ces" (is "wf_cond_effect_list ?Q ces")
    shows "wf_cond_effect_list (ty_term (ty_sym Q objT)) (pddl_univ_effect_list vts ces)" (is "wf_cond_effect_list ?R (pddl_univ_effect_list vts ces)")
    using assms
  proof (induction vts arbitrary: ces Q)
    case Nil
    then show ?case unfolding pddl_univ_effect_list_def upd_ty_env_def by simp
  next
    case (Cons a vts)
    then obtain v ty where
      a: "a = (v, ty)"
      by fastforce
    from Cons.prems a
    have "wf_cond_effect_list (ty_term (ty_sym (upd_ty_env (Q(v\<mapsto>ty)) vts) objT)) ces" unfolding upd_ty_env_def by simp
    then have "wf_cond_effect_list (ty_term (ty_sym (Q(v\<mapsto>ty)) objT)) (pddl_univ_effect_list vts ces)" using Cons.IH by blast
    then have "wf_cond_effect_list (ty_term (ty_sym Q objT)) (univ_effect_list v ty (pddl_univ_effect_list vts ces))" using wf_univ_effect_list_inst by blast
    with a
    show ?case unfolding pddl_univ_effect_list_def by simp
  qed

  
end \<comment> \<open>Context of \<open>wf_problem_decs\<close>\<close>

subsection \<open>PDDL Semantics\<close>


context ast_domain begin

  definition resolve_action_schema :: "name \<rightharpoonup> ast_action_schema" where
    "resolve_action_schema n = index_by ast_action_schema.name (actions D) n"


 text \<open>To instantiate an action schema, we first compute a substitution from
    parameters to objects, and then apply this substitution to the
    precondition and effect. The substitution is applied via the \<open>map_xxx\<close>
    functions generated by the datatype package.
    \<close>

  fun instantiate_action_schema
    :: "ast_action_schema \<Rightarrow> object list \<Rightarrow> ground_action"
  where
    "instantiate_action_schema (Action_Schema n params pre effs) as = (let
        term_inst = inst_term params as;
        pre_inst = map_pre term_inst pre;
        eff_inst = map (map_cond_effect term_inst) effs
      in
        Ground_Action pre_inst eff_inst
      )"

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

subsection \<open>Preservation of Well-Formedness\<close>

subsection \<open>Instantiation\<close>

context ast_problem begin

  fun add_init_int::"(func \<times> 'b list \<times> 'c) 
    \<Rightarrow> (func \<rightharpoonup> ('b list \<rightharpoonup> 'c))
    \<Rightarrow> (func \<rightharpoonup> ('b list \<rightharpoonup> 'c))" where
  "add_init_int (f, as, v) fun_int = (
    case (fun_int f) of 
      Some fun_int' \<Rightarrow> (fun_int(f \<mapsto> (fun_int'(as \<mapsto> v))))
    | None          \<Rightarrow> (fun_int(f \<mapsto> [as \<mapsto> v]))
  )"
  
  definition ofi::"object_function_interpretation" where
    "ofi = fold add_init_int (init_ofs P) Map.empty"
  
  definition nfi::"numeric_function_interpretation" where
    "nfi = fold add_init_int (init_nfs P) Map.empty"

  text \<open>Initial model\<close>
  definition I :: "world_model" where
    "I \<equiv> (World_Model (set (init_ps P)) ofi nfi)"

  text \<open>Resolve a plan action and instantiate the referenced action schema.\<close>
  fun resolve_instantiate :: "plan_action \<Rightarrow> ground_action" where
    "resolve_instantiate (PAction n as) =
      instantiate_action_schema
        (the (resolve_action_schema n))
        as"


  text \<open>HOL encoding of matching an action's formal parameters against an
    argument list.
    The parameters of the action are encoded as a list of \<open>name\<times>type\<close> pairs,
    such that we map it to a list of types first. Then, the list
    relator @{const list_all2} checks that arguments and types have the same
    length, and each matching pair of argument and type
    satisfies the pred @{const is_of_type} @{term objT}.
  \<close>          
  definition "params_match ps as \<equiv> list_all2 (is_of_type objT) as (map snd ps)"

  definition "action_params_match a as
    \<equiv> params_match (parameters a) as"

  text \<open>At this point, we can define well-formedness of a plan action:
    The action must refer to a declared action schema, the arguments must
    be compatible with the formal parameters' types.
  \<close>
  fun wf_plan_action :: "plan_action \<Rightarrow> bool" where
    "wf_plan_action (PAction n as) = (
      case resolve_action_schema n of
        None \<Rightarrow> False
      | Some a \<Rightarrow>
          action_params_match a as
        )"

  text \<open>A sequence of plan actions form a path, if they are well-formed and
    their instantiations form a path.\<close>
  definition plan_action_path
    :: "world_model \<Rightarrow> plan_action list \<Rightarrow> world_model \<Rightarrow> bool"
  where
    "plan_action_path M \<pi>s M' =
        ((\<forall>\<pi> \<in> set \<pi>s. wf_plan_action \<pi>)
      \<and> ground_action_path M (map resolve_instantiate \<pi>s) M')"

  text \<open>Instantiation of a goal. No variables are instantiated\<close>
  fun inst_goal::"schematic_formula \<Rightarrow> ground_formula" where
  "inst_goal \<phi> = (let term_inst = inst_term [] []
        in (map_formula o map_atom) term_inst \<phi>)"
  
  text \<open>A plan is valid wrt.\ a given initial model, if it forms a path to a
    goal model \<close>
  definition valid_plan_from :: "world_model \<Rightarrow> plan \<Rightarrow> bool" where
    "valid_plan_from M \<pi>s = (\<exists>M'. plan_action_path M \<pi>s M' \<and> valuation M' \<Turnstile> inst_goal (goal P))"
  
  (* Implementation note: resolve and instantiate already done inside
      enabledness check, redundancy! *)

  text \<open>Finally, a plan is valid if it is valid wrt.\ the initial world
    model @{const I}\<close>
  definition valid_plan :: "plan \<Rightarrow> bool"
    where "valid_plan \<equiv> valid_plan_from I"

  text \<open>Concise definition used in paper:\<close>
  lemma valid_plan_alt: "valid_plan \<pi>s \<equiv> \<exists>M'. plan_action_path I \<pi>s M' \<and> valuation M' \<Turnstile> inst_goal (goal P)"
    unfolding valid_plan_def valid_plan_from_def by auto

end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>


subsubsection \<open>Well-Formed Action Instances\<close>
text \<open>The goal of this section is to establish that well-formedness of
  world models is preserved by execution of well-formed plan actions.
\<close>
             
context ast_problem begin
  text \<open>We first prove that instantiating a well-formed action schema will yield
    a well-formed action instance.

    We begin with some auxiliary lemmas before the actual theorem.
  \<close>

                    
  lemma constT_ss_objT: "constT \<subseteq>\<^sub>m objT"
    unfolding constT_def objT_def
    apply (rule map_leI)
    by (auto simp: map_add_def split: option.split)

  lemma is_term_of_type_is_of_type: "is_term_of_type Q a T \<longleftrightarrow> is_of_type (ty_term Q) a T"
    unfolding is_of_type_def
    by auto

  text \<open>Instantiating a well-formed goal will result in a well-formed formula\<close>
  theorem wf_instantiate_goal:
    assumes "wf_goal \<phi>"
    shows "wf_fmla (ty_term objT) (inst_goal \<phi>)"
  proof -
    have INST: "is_of_type objT (f x) T"
      if "is_of_type Q x T" 
      and "Q = Map.empty" 
      and "f = the \<circ> map_of (zip (map fst []) [])" (is "f = ?f")
      for x T and Q::"variable \<rightharpoonup> type" and f::"variable \<Rightarrow> object"
      using that unfolding is_of_type_def by simp
    
    from INST_sym_to_obj[where Q = Map.empty and R = objT] this
    have "is_of_type objT (inst_sym [] [] s) T" 
      if "is_of_type (ty_sym Map.empty objT) s T" 
      for s T using that by simp
  
    from ty_term_is_of_type_lift_strong[OF this]
    have "is_of_type (ty_term objT) (inst_term [] [] t) T"
      if "is_of_type (ty_term (ty_sym Map.empty objT)) t T" 
      for t T using that by fastforce
                      
    from ent_type_imp_wf_fmla_strong[OF this] assms
    show ?thesis 
      by (fastforce 
          split: term.splits 
          simp: Let_def comp_apply[abs_def] wf_goal_def)
  qed

  text \<open>Instantiating a well-formed action schema with compatible arguments
    will yield a well-formed action instance.
  \<close>
  theorem wf_instantiate_action_schema:
    assumes "action_params_match a as"
    assumes "wf_action_schema a"
    shows "wf_ground_action (instantiate_action_schema a as)"
  proof (cases a)
    case [simp]: (Action_Schema name params pre eff)
    let ?f = "the \<circ> map_of (zip (map fst params) as)"
    have "is_of_type objT (?f x) T"
      if "is_of_type (map_of params) x T" for x T
      using that
      apply (rule is_of_type_map_ofE)
      using assms
      apply (clarsimp simp: Let_def)
        apply (thin_tac "wf_fmla (ty_term (ty_sym (map_of params) objT)) pre")
        apply (thin_tac "wf_cond_effect_list (ty_term (ty_sym (map_of params) objT)) eff")
      subgoal for i xT
        unfolding action_params_match_def params_match_def
        apply (subst lookup_zip_idx_eq[where i=i];
          (clarsimp simp: list_all2_lengthD)?)
        apply (frule list_all2_nthD2[where p=i]; simp?)
        apply (auto               
                simp: is_of_type_def
                intro: of_type_trans
                split: option.splits)
        done
      done
    
    from INST_sym_to_obj[where f = ?f] this
    have "is_of_type objT (inst_sym params as s) T" 
      if "is_of_type (ty_sym (map_of params) objT) s T" 
      for s T using that by fastforce
  
    from ty_term_is_of_type_lift_strong this
    have "is_of_type (ty_term objT) (inst_term params as t) T"
      if "is_of_type (ty_term (ty_sym (map_of params) objT)) t T" 
      for t T using that by fastforce
  
    with ent_type_imp_wf_fmla_strong[where f = "inst_term params as" and Q = "ty_term (ty_sym (map_of params) objT)" and R = "ty_term objT"]
        ent_type_imp_wf_cond_effect_list_strong[where f = "inst_term params as" and Q = "ty_term (ty_sym (map_of params) objT)" and R = "ty_term objT"]
        assms(2)
    show ?thesis by (auto simp: Let_def wf_cond_effect_list_def wf_ground_action_def)
  qed

end

subsubsection \<open>Preservation\<close>

context ast_problem
begin


  text \<open>Shorthand for enabled plan action: It is well-formed, the
    precondition holds for its instance, and its effects are well-formed, i.e.
    will not cause the world model to become not well-formed.\<close>
(*   definition plan_action_enabled :: "plan_action \<Rightarrow> world_model \<Rightarrow> bool" where
    "plan_action_enabled \<pi> M
      \<longleftrightarrow> wf_plan_action \<pi> 
        \<and> ground_action_enabled (resolve_instantiate \<pi>) M" *)

  text \<open>Valid plan actions are those, whose preconditions hold and are valid once
        completely instantiated. \<close>
  definition valid_plan_action :: "plan_action \<Rightarrow> world_model \<Rightarrow> bool" where
    "valid_plan_action \<pi> M 
      \<longleftrightarrow> wf_plan_action \<pi>
      \<and> valid_ground_action (resolve_instantiate \<pi>) M"

  text \<open>Shorthand for executing a plan action: Resolve, instantiate, and
    apply effect\<close>
  definition execute_plan_action :: "plan_action \<Rightarrow> world_model \<Rightarrow> world_model"
    where "execute_plan_action \<pi> M
      = execute_ground_action (resolve_instantiate \<pi>) M"

  text \<open>The @{const plan_action_path} pred can be decomposed naturally
    using these shorthands: \<close>
  lemma plan_action_path_Nil[simp]: "plan_action_path M [] M' \<longleftrightarrow> M'=M"
    by (auto simp: plan_action_path_def)

  lemma plan_action_path_Cons[simp]:
    "plan_action_path M (\<pi>#\<pi>s) M' \<longleftrightarrow>
      valid_plan_action \<pi> M
    \<and> plan_action_path (execute_plan_action \<pi> M) \<pi>s M'"
    by (auto
      simp: plan_action_path_def execute_plan_action_def
            execute_ground_action_def valid_ground_action_def
            valid_plan_action_def)
end

text \<open>Locale to express a well-formed domain\<close>
locale wf_ast_domain = ast_domain +
  assumes wf_domain: wf_domain


text \<open>Locale to express a well-formed problem\<close>
locale wf_ast_problem = ast_problem P for P +
  assumes wf_problem: wf_problem
begin
  sublocale wf_ast_domain "domain P"
    apply unfold_locales
    using wf_problem                
    unfolding wf_problem_def by simp

  sublocale wf_problem_decs "problem_decs (domain P)"
    apply unfold_locales
    using wf_problem
    unfolding wf_problem_def wf_domain_def by blast


  lemma wf_add_one_init_oi:
    assumes "wf_of_int oi"
        and "wf_init_of_a a"
      shows "wf_of_int (add_init_int a oi)" (is "wf_of_int ?oi'")
  proof (cases a)
    case a [simp]: (fields f as v)
    have "wf_of_arg_r_map f' m"
      if "(f', m) \<in> Map.graph ?oi'" for f' m
    proof (cases "f = f'")
      case True
      show ?thesis
      proof (cases "oi f")
        case None
        from that[simplified a add_init_int.simps True this[simplified True]]
        have "(f', m) \<in> Map.graph (oi(f' \<mapsto> [as \<mapsto> v]))" by simp
        hence "m = [as \<mapsto> v]" using in_graphD by fastforce
        moreover
        have "wf_of_arg_r_map f [as \<mapsto> v]"
          unfolding wf_of_arg_r_map_def
          using assms(2)[simplified a wf_init_of_a.simps]
          by (cases "obj_fun_sig f"; auto)
        ultimately
        show ?thesis using True by simp
      next
        case (Some a)
        with that[simplified a add_init_int.simps]
        obtain fun_int' where
          fun_int': "oi f = Some fun_int'"
          "(f', m) \<in> Map.graph (oi(f \<mapsto> fun_int'(as \<mapsto> v)))"
          by simp
        moreover
        with \<open>f = f'\<close>
        have m: "m = fun_int'(as \<mapsto> v)" by (metis fun_upd_same in_graphD option.sel)
        moreover
        from assms(2)[simplified a wf_init_of_a.simps]
        obtain Ts T where
          Ts: "obj_fun_sig f = Some (Ts, T)" by fastforce
        moreover
        have "list_all2 (is_of_type objT) as' Ts \<and> is_of_type objT v' T"
          if "(as', v') \<in> Map.graph (fun_int'(as \<mapsto> v))" for as' v'
        proof (cases "as = as'")
          case True
          with that
          have "v = v'" using in_graphD by fastforce
          with assms(2)[simplified a wf_init_of_a.simps Ts True this]
          show ?thesis by auto
        next
          case False
          with that 
          have "(as', v') \<in> Map.graph fun_int'"
            by (metis fun_upd_other in_graphD in_graphI)
          with assms(1) fun_int'(1) Ts
          show "list_all2 (is_of_type objT) as' Ts \<and> is_of_type objT v' T"
            unfolding wf_of_int_def wf_of_arg_r_map_def 
            apply -
            apply (drule bspec[where x = "(f, fun_int')"])
             apply (rule in_graphI, assumption)
            by (auto split: option.splits prod.splits)
        qed
        ultimately
        show ?thesis using \<open>f = f'\<close> wf_of_arg_r_map_def by auto
      qed
    next
      case False
      from that
      have "(f', m) \<in> Map.graph oi" 
        apply -
        apply (subst (asm) a)
        apply (subst (asm) add_init_int.simps)
        apply (cases "oi f")
        subgoal 
          apply (simp) 
          by (metis fun_upd_triv False)
        subgoal for a
          using False
          by (auto simp: graph_fun_upd_None)
        done
      with assms(1)
      show ?thesis unfolding wf_of_int_def by blast 
    qed
    then show "wf_of_int (add_init_int a oi)" unfolding wf_of_int_def by blast
  qed
  
  lemma wf_ofi: "wf_of_int ofi"
  proof -
    have "\<And>a. a \<in> set (init_ofs P) \<Longrightarrow> wf_init_of_a a"
      using wf_problem unfolding wf_problem_def by simp
    moreover
    have "wf_of_int Map.empty" unfolding wf_of_int_def using in_graphD by auto
    ultimately
    show "wf_of_int ofi" 
      unfolding ofi_def
      using fold_invariant[where xs = "init_ofs P" and Q = wf_init_of_a and P = wf_of_int
          and f = add_init_int] wf_add_one_init_oi
      by blast
  qed
  
  lemma wf_add_one_init_ni:
    assumes "wf_nf_int ni"
        and "wf_init_nf_a a"
      shows "wf_nf_int (add_init_int a ni)" (is "wf_nf_int ?ni'")
  proof (cases a)
    case a [simp]: (fields f as v)
    have "wf_nf_int_map f' m"
      if "(f', m) \<in> Map.graph ?ni'" for f' m
    proof (cases "f = f'")
      case True
      show ?thesis
      proof (cases "ni f")
        case None
        from that[simplified a add_init_int.simps True this[simplified True]]
        have "(f', m) \<in> Map.graph (ni(f' \<mapsto> [as \<mapsto> v]))" by simp
        hence "m = [as \<mapsto> v]" using in_graphD by fastforce
        moreover
        have "wf_nf_int_map f [as \<mapsto> v]"
          unfolding wf_nf_int_map_def
          using assms(2)[simplified a wf_init_of_a.simps]
          by (cases "num_fun_sig f"; auto)
        ultimately
        show ?thesis using True by simp
      next
        case (Some a)
        with that[simplified a add_init_int.simps]
        obtain fun_int' where
          fun_int': "ni f = Some fun_int'"
          "(f', m) \<in> Map.graph (ni(f \<mapsto> fun_int'(as \<mapsto> v)))"
          by simp
        moreover
        with \<open>f = f'\<close>
        have m: "m = fun_int'(as \<mapsto> v)" by (metis fun_upd_same in_graphD option.sel)
        moreover
        from assms(2)[simplified a wf_init_of_a.simps]
        obtain Ts where
          Ts: "num_fun_sig f = Some Ts" by fastforce
        moreover
        have "list_all2 (is_of_type objT) as' Ts"
          if "as' \<in> dom (fun_int'(as \<mapsto> v))" for as'
        proof (cases "as = as'")
          case True
          from assms(2)[simplified a wf_init_nf_a.simps Ts this]
          show ?thesis by auto
        next
          case False
          with that 
          have "as'\<in> dom fun_int'" by simp
          with assms(1) fun_int'(1) Ts
          show "list_all2 (is_of_type objT) as' Ts"
            unfolding wf_nf_int_def wf_nf_int_map_def 
            apply -
            apply (drule bspec[where x = "(f, fun_int')"])
             apply (rule in_graphI, assumption)
            by simp
        qed
        ultimately
        show ?thesis using \<open>f = f'\<close> wf_nf_int_map_def by auto
      qed
    next
      case False
      from that
      have "(f', m) \<in> Map.graph ni" 
        apply -
        apply (subst (asm) a)
        apply (subst (asm) add_init_int.simps)
        apply (cases "ni f")
        subgoal 
          apply (simp) 
          by (metis fun_upd_triv False)
        subgoal for a
          using False
          by (auto simp: graph_fun_upd_None)
        done
      with assms(1)
      show ?thesis unfolding wf_nf_int_def by blast 
    qed
    then show "wf_nf_int (add_init_int a ni)" unfolding wf_nf_int_def by blast
  qed

  lemma wf_nfi: "wf_nf_int nfi"
  proof -
    have "\<And>a. a \<in> set (init_nfs P) \<Longrightarrow> wf_init_nf_a a"
      using wf_problem unfolding wf_problem_def by simp
    moreover
    have "wf_nf_int Map.empty" unfolding wf_nf_int_def using in_graphD by auto
    ultimately
    show "wf_nf_int nfi" 
      unfolding nfi_def
      using fold_invariant[where xs = "init_nfs P" and Q = wf_init_nf_a and P = wf_nf_int
          and f = add_init_int] wf_add_one_init_ni
      by blast
  qed
  
  theorem wf_I: "wf_world_model I"
    unfolding wf_world_model_def
    using wf_ofi wf_nfi I_def wf_problem[simplified wf_problem_def]
    by simp

  lemma wf_apply_predicate_upd:
    assumes "wf_app_predicate_upd u"
    shows "wf_pred objT (the u)"
    using assms
    apply (cases u)
    subgoal by simp
    subgoal for a by (cases a; auto)
    done

  lemma wf_apply_of_upd: 
      assumes "wf_of_int oi" 
              "wf_app_of_upd ou"
        shows "wf_of_int (apply_of_upd ou oi)" (is "wf_of_int ?oi'")
  proof (cases ou)
    case upd [simp]: (OFU f as v)
    have "wf_of_arg_r_map f' fn"
      if 1: "(f', fn) \<in> Map.graph ?oi'" for f' fn
    proof (cases "f = f'")
      case True
      with \<open>wf_app_of_upd ou\<close>
      obtain Ts T where 
        Ts: "obj_fun_sig f' = Some (Ts, T)" by (auto split: option.splits)
      have "fn (map the as) = v"
        apply (insert that[simplified upd apply_of_upd.simps]) 
        by (drule in_graphD, cases "oi f", auto simp: True)
      have "list_all2 (is_of_type objT) as' Ts 
          \<and> is_of_type objT v' T"
        if "(as', v') \<in> Map.graph fn" for as' v'
      proof (cases "map the as = as'")
        case True
        with \<open>wf_app_of_upd ou\<close> \<open>obj_fun_sig f' = Some (Ts, T)\<close> \<open>f = f'\<close>
        have "list_all2 ((is_of_type objT) o the) as Ts " by (auto split: option.splits)
        with \<open>map the as = as'\<close>
        have "list_all2 (is_of_type objT) as' Ts" 
          by (auto split: option.splits simp: list_all2_conv_all_nth)
        with \<open>map the as = as'\<close> \<open>fn (map the as) = v\<close>
        have "fn as' = v" by blast
        with that True
        have "v \<noteq> None" using in_graphD by fast
        with \<open>wf_app_of_upd ou\<close> \<open>f = f'\<close> \<open>obj_fun_sig f' = Some (Ts, T)\<close>
        have "is_of_type objT (the v) T" by auto
        with \<open>fn as' = v\<close> \<open>list_all2 (is_of_type objT) as' Ts\<close> that[THEN in_graphD]
        show ?thesis by fastforce
      next
        case False
        with 1 \<open>(as', v') \<in> Map.graph fn\<close>
        have "\<exists>fn'. (f', fn') \<in> Map.graph oi \<and> fn as' = fn' as'"
          apply -
          apply (drule in_graphD)
          apply (drule in_graphD)
          apply (subst (asm) upd)
          apply (subst (asm) apply_of_upd.simps)
          apply (cases "oi f")
          subgoal by (auto simp: \<open>f = f'\<close>)
          subgoal for fn'
            apply (simp add: \<open>f = f'\<close>)
            apply (rule exI[of _ fn'])
            apply (drule in_graphI[of oi])
            by auto
          done
        then obtain fn' where
          "(f', fn') \<in> Map.graph oi"
          "(as', v') \<in> Map.graph fn'"
          by (metis \<open>(as', v') \<in> Map.graph fn\<close> in_graphD in_graphI)
        then show ?thesis using assms(1) 
          unfolding wf_of_int_def wf_of_arg_r_map_def
          apply -
          apply (drule bspec, assumption)
          by (auto simp: Ts)
      qed
      with \<open>obj_fun_sig f' = Some (Ts, T)\<close>
      show ?thesis by (auto split: option.splits prod.splits simp: wf_of_arg_r_map_def)
    next
      case False
      hence "apply_of_upd (OFU f as v) oi f' = oi f'"
        by (auto split: option.splits)
      with \<open>(f', fn) \<in> Map.graph ?oi'\<close>
      have "(f', fn) \<in> Map.graph oi" apply - 
        unfolding upd 
        apply (drule in_graphD)
        apply (rule in_graphI)
        by auto
      with \<open>wf_of_int oi\<close>
      show ?thesis unfolding wf_of_int_def by (auto split: option.splits)
    qed
    then show ?thesis unfolding wf_of_int_def by blast
  qed

  lemma wf_apply_of_upds: 
      assumes "\<forall>u \<in> set tu. wf_app_of_upd u"
              "wf_of_int ti" 
        shows "wf_of_int (fold apply_of_upd tu ti)"
  using assms by (induction tu arbitrary: ti; auto simp: wf_apply_of_upd)
  
  lemma wf_apply_nf_upd:
        assumes "wf_nf_int ni" 
                "wf_app_nf_upd nu"
                "int_defines_nf_upd ni nu"
          shows "wf_nf_int (apply_nf_upd nu ni)" (is "wf_nf_int ?ni'")
  proof (cases nu)
    case [simp]: (NFU op n as v)
    from \<open>wf_app_nf_upd nu\<close>
    obtain Ts where
      "num_fun_sig n = Some Ts" 
      using nf_args_well_typed_def by fastforce

    have "wf_nf_int_map n' m" 
      if "(n', m) \<in> Map.graph ?ni'" for n' m
    proof cases
      assume "n' = n"
      show ?thesis
      proof (cases)
        assume "op = Assign"
        show ?thesis
        proof (cases "ni n")
          case None
          with  \<open>op = Assign\<close> \<open>n' = n\<close> that
          have m_def: "m = upd_nf_int Map.empty Assign (map the as) (the (Map.empty (map the as))) (the v)" 
          by (auto dest: in_graphD)
          hence "dom m = {(map the as)}" by simp
          moreover
          from \<open>wf_app_nf_upd nu\<close> \<open>n' = n\<close>
          have "nf_args_well_typed n' (map the as)" by auto
          ultimately
          show ?thesis unfolding nf_args_well_typed_def wf_nf_int_map_def by (auto split: option.splits)
        next
          case (Some m')
          with that \<open>n' = n\<close> \<open>op = Assign\<close>
          have m_def: "m = upd_nf_int m' Assign (map the as) (the (m' (map the as))) (the v)" 
            by (auto dest: in_graphD)
          have "list_all2 (is_of_type objT) as' Ts" 
            if "as' \<in> dom m" for as'
          proof (cases "as' = map the as")
            assume "as' = map the as"
            with \<open>wf_app_nf_upd nu\<close> \<open>num_fun_sig n = Some Ts\<close>
            show ?thesis using nf_args_well_typed_def by auto
          next
            assume "as' \<noteq> map the as" 
            with \<open>int_defines_nf_upd ni nu\<close> that m_def \<open>op = Assign\<close>
            have "as' \<in> dom m'" by auto
            from \<open>ni n = Some m'\<close> 
            have "(n, m') \<in> Map.graph ni" using in_graphI by fast
            with \<open>wf_nf_int ni\<close>
            have "wf_nf_int_map n m'" unfolding wf_nf_int_def by blast
            with \<open>n' = n\<close>
            have "wf_nf_int_map n' m'" by blast
            with \<open>as' \<in> dom m'\<close> \<open>num_fun_sig n = Some Ts\<close> \<open>n' = n\<close>
            show ?thesis unfolding wf_nf_int_map_def by auto
          qed
          with \<open>num_fun_sig n = Some Ts\<close> \<open>n' = n\<close>
          show ?thesis unfolding wf_nf_int_map_def by simp
        qed
      next
        assume "op \<noteq> Assign"
        with \<open>int_defines_nf_upd ni nu\<close>
        obtain m' where 
          "ni n = Some m'"
          by (cases op; auto split: option.splits)
        with that \<open>n' = n\<close> \<open>op \<noteq> Assign\<close>
        have m_def: "m = upd_nf_int m' op (map the as) (the (m' (map the as))) (the v)" 
          using in_graphD by fastforce
        have "list_all2 (is_of_type objT) as' Ts" 
            if "as' \<in> dom m" for as'
        proof (cases "as' = map the as")
          case True
          with \<open>wf_app_nf_upd nu\<close> \<open>num_fun_sig n = Some Ts\<close>
          show ?thesis using nf_args_well_typed_def by auto
        next
          case False
          with \<open>int_defines_nf_upd ni nu\<close> that m_def \<open>op \<noteq> Assign\<close>
          have "as' \<in> dom m'" by (cases op; auto split: option.splits)
          from \<open>ni n = Some m'\<close> 
          have "(n, m') \<in> Map.graph ni" using in_graphI by fast
          with \<open>wf_nf_int ni\<close>
          have "wf_nf_int_map n m'" unfolding wf_nf_int_def by blast
          with \<open>n' = n\<close>
          have "wf_nf_int_map n' m'" by blast
          with \<open>as' \<in> dom m'\<close> \<open>num_fun_sig n = Some Ts\<close> \<open>n' = n\<close>
          show ?thesis unfolding wf_nf_int_map_def by auto
        qed
        with \<open>num_fun_sig n = Some Ts\<close> \<open>n' = n\<close>
        show ?thesis unfolding wf_nf_int_map_def by simp
      qed
    next
      assume "n' \<noteq> n"
      moreover
      from \<open>int_defines_nf_upd ni nu\<close>
      have "\<exists>f. ?ni' = ni(n \<mapsto> upd_nf_int f op (map the as) (the (f (map the as))) (the v))" 
        by (auto split: option.splits)
      ultimately
      have "(n', m) \<in> Map.graph ni" by (metis fun_upd_other in_graphD in_graphI that)
      with \<open>wf_nf_int ni\<close>
      show ?thesis unfolding wf_nf_int_def by fast
    qed
    then
    show ?thesis unfolding wf_nf_int_def by blast
  qed
  
  lemma nf_upd_defined_inv:
    assumes "int_defines_nf_upd ni nu"
        and "wf_app_nf_upd nu"
        and "int_defines_nf_upd ni nu'"
        and "wf_app_nf_upd nu'"
      shows "int_defines_nf_upd (apply_nf_upd nu' ni) nu" (is "int_defines_nf_upd ?ni' nu")
  proof -
    from assms
    obtain n op as v n' op' as' v' where
      [simp]: "nu = NFU op n as v"
      "nu' = NFU op' n' as' v'"
      by (cases nu; cases nu'; simp)
    from \<open>int_defines_nf_upd ni nu\<close>
    have 1: "op \<noteq> Assign \<Longrightarrow> (\<exists>f. ni n = Some f \<and> f (map the as) \<noteq> None)" 
      by (cases op; cases "ni n"; auto)
  
    have 2: "\<exists>f'. ?ni' n = Some f' \<and> f' (map the as) \<noteq> None" if "op \<noteq> Assign"
    proof (cases "n = n'")
      assume [simp]: "n = n'"
      from \<open>int_defines_nf_upd ni nu\<close> \<open>op \<noteq> Assign\<close>
      obtain f' where
        f': "ni n = Some f'"
        "f' (map the as) \<noteq> None"
        using 1 by blast
      with \<open>wf_app_nf_upd nu'\<close> \<open>int_defines_nf_upd ni nu'\<close>
      have "upd_nf_int f' op' (map the as') (the (f' (map the as'))) (the v') (map the as) \<noteq> None"
        by (cases "map the as = map the as'"; cases op'; auto)
      with f' 
      show ?thesis by simp
    next
      assume "n \<noteq> n'"
      then have "?ni' n = ni n" by (auto split: option.splits simp: Let_def)
      with 1 that
      show ?thesis by auto
    qed
  
    show "int_defines_nf_upd ?ni' nu"
      apply (cases "op = Assign") 
      subgoal by (cases op; auto)
      subgoal by (drule 2; cases op; auto)
      done
  qed


  lemma wf_apply_nf_upds: 
    assumes "\<forall>u \<in> set upds. wf_app_nf_upd u"
            "\<forall>u \<in> set upds. int_defines_nf_upd ni u"
            "wf_nf_int ni" 
      shows "wf_nf_int (fold apply_nf_upd upds ni)"
    using assms
    by (induction upds arbitrary: ni; auto simp: wf_apply_nf_upd nf_upd_defined_inv)


  text \<open>Application of a well-formed effect preserves well-formedness
    of the model. We also need the fact that the effect is valid w.r.t. the 
    world model. However, the notion of validity is only defined for ground_effects.\<close>
  lemma wf_apply_effect:
    assumes "wf_world_model M"
        and "well_inst_effect eM eff M"
        and "wf_fully_instantiated_effect (inst_effect eM eff)"
      shows "wf_world_model (inst_apply_effect eM eff M)"
    using assms
  proof -
    obtain predicates oi ni where
      M: "M = World_Model predicates oi ni"
      by (cases M; simp)
    
    obtain a' d' ous' nus' where
      eff': "inst_effect eM eff = Eff a' d' ous' nus'"
      by (cases "inst_effect eM eff"; simp)
    
    obtain predicates' oi' ni' where
      M': "inst_apply_effect eM eff M = World_Model predicates' oi' ni'"
      using world_model.exhaust by blast
  
    have predicates': "predicates' = predicates - set (map the d') \<union> set (map the a')"
         and oi': "oi' = fold apply_of_upd ous' oi"
         and ni': "ni' = fold apply_nf_upd nus' ni"
      using M eff' M' unfolding inst_apply_effect_def by simp+
    
    have "wf_pred objT p" if "p \<in> predicates - set (map the d') \<union> set (map the a')" for p
    proof -
      have "list_all (wf_pred objT) (map the a')"
       "list_all (wf_pred objT) (map the d')"
        using assms(3)[simplified eff'] 
        subgoal by (induction a'; auto intro: wf_apply_predicate_upd simp: Ball_set) 
        using assms(3)[simplified eff'] 
        subgoal by (induction d'; auto intro: wf_apply_predicate_upd simp: Ball_set)
        done
      with that  assms(1)[simplified M wf_world_model_def]
      show "wf_pred objT p" by (auto simp: sym[OF Ball_set]) 
    qed 
    moreover
    have "wf_of_int (fold apply_of_upd ous' oi)"
      using assms(1)[simplified M wf_world_model_def] assms(3)[simplified eff']
        wf_apply_of_upds by simp
    moreover
    have "wf_nf_int (fold apply_nf_upd nus' ni)"
    proof -
      from eff'
      have "nus' = map (inst_nf_upd eM) (nf_upds eff)"
        by (cases eff; auto)
      with assms(2)[simplified M]
      have "list_all (int_defines_nf_upd ni) nus'" 
        unfolding well_inst_effect_def nf_upd_defined_def 
        apply simp
        apply (drule conjunct2)
        by (simp add: list_all_length)
      moreover
      from assms(3)[simplified eff'] 
      have "list_all wf_app_nf_upd nus'"
        by (simp add: Ball_set)
      moreover
      from assms(1)[simplified M]
      have "wf_nf_int ni" by (simp add: wf_world_model_def)
      ultimately
      show "wf_nf_int (fold apply_nf_upd nus' ni)" using wf_apply_nf_upds by (simp add: Ball_set)
    qed
    ultimately
    show "wf_world_model (inst_apply_effect eM eff M)"
      using  predicates' oi' ni' M'
      unfolding wf_world_model_def 
      by auto
  qed

  
  lemma well_inst_effect_inv:
    assumes "wf_world_model M"
            "wf_fully_instantiated_effect (inst_effect eM eff)"
            "well_inst_effect eM eff M"
            "wf_fully_instantiated_effect (inst_effect eM eff1)"
            "well_inst_effect eM eff1 M"
      shows "well_inst_effect eM eff (inst_apply_effect eM eff1 M)"
  proof -
    obtain p oi ni where
      M: "M = World_Model p oi ni"
      by (rule world_model.exhaust)
    obtain a' d' ou' nu' where
      eff': "inst_effect eM eff = Eff a' d' ou' nu'"
      by (rule fully_instantiated_effect.exhaust)
  
    obtain a1' d1' ou1' nu1' where
      eff1': "inst_effect eM eff1 = Eff a1' d1' ou1' nu1'"
      by (rule fully_instantiated_effect.exhaust)
  
    obtain p' oi' ni' where
      M': "inst_apply_effect eM eff1 M = World_Model p' oi' ni'"
      by (rule world_model.exhaust)
  
    have ni': "ni' = fold apply_nf_upd nu1' ni"
      using eff1' M' M unfolding inst_apply_effect_def
      by auto
  
    from eff'
    have nu': "nu' = map (inst_nf_upd eM) (nf_upds eff)"
      by (cases eff; auto)
    with assms(3)[simplified M]
    have "list_all (int_defines_nf_upd ni) nu'" 
      unfolding well_inst_effect_def nf_upd_defined_def
      apply simp
      apply (drule conjunct2)
      by (simp add: list_all_length)
    moreover
    from assms(2)[simplified eff']
    have "list_all wf_app_nf_upd nu'"
      by (simp add: Ball_set)
    moreover
    from eff1'
    have "nu1' = map (inst_nf_upd eM) (nf_upds eff1)"
      by (cases eff1; auto)
    with assms(5)[simplified M]
    have "list_all (int_defines_nf_upd ni) nu1'" 
      unfolding well_inst_effect_def nf_upd_defined_def 
      apply simp
      apply (drule conjunct2)
      by (simp add: list_all_length)
    moreover
    from assms(4)[simplified eff1']
    have "list_all wf_app_nf_upd nu1'"
      by (simp add: Ball_set)
    moreover
    have "int_defines_nf_upd (fold apply_nf_upd upds ni) nu"
      if "int_defines_nf_upd ni nu"
         "wf_app_nf_upd nu"
         "list_all (int_defines_nf_upd ni) upds"
         "list_all wf_app_nf_upd upds"
       for ni nu upds 
      using that
      apply (induction upds arbitrary: ni)
       apply simp
      using nf_upd_defined_inv
      by (metis Ball_set fold_simps(2) list_all_simps(1))
    ultimately
    have "list_all (int_defines_nf_upd ni') nu'"
      by (induction nu'; auto simp: ni')
    hence "list_all (nf_upd_defined eM (inst_apply_effect eM eff1 M)) (nf_upds eff)"
      unfolding nu' M' nf_upd_defined_def
      by (simp add: list_all_length)
    with assms(3)
    show "well_inst_effect eM eff (inst_apply_effect eM eff1 M)"
      unfolding well_inst_effect_def by simp
  qed

  lemma wf_apply_effects:
  assumes "wf_world_model M"
          "\<forall>eff \<in> set effs. wf_fully_instantiated_effect (inst_effect M eff)"
          "\<forall>eff \<in> set effs. well_inst_effect M eff M"
    shows "wf_world_model (fold (inst_apply_effect M) effs M)"
  proof -
    have "wf_world_model (fold (inst_apply_effect eM) effs M)" 
      if "wf_world_model M"
         "\<forall>eff \<in> set effs. wf_fully_instantiated_effect (inst_effect eM eff)"
         "\<forall>eff \<in> set effs. well_inst_effect eM eff M" for eM 
      using that
      apply (induction effs arbitrary: M)
       apply simp
      by (simp add: well_inst_effect_inv wf_apply_effect)
    from this[OF assms]
    show "wf_world_model (fold (inst_apply_effect M) effs M)" .
  qed


lemma wf_execute_cond_effect_list:
  assumes "wf_world_model M"
    "wf_inst_cond_effect_list M effs"
    "well_inst_cond_effect_list M M effs"
  shows "wf_world_model (apply_conditional_effect_list effs M)"
proof -
  have wf_apply_cond_effect:      
      "wf_world_model (inst_apply_conditional_effect eM eff M)"
    if "wf_world_model M"
       "wf_inst_cond_effect eM eff"
       "well_inst_cond_effect eM M eff" for eM M eff
      unfolding inst_apply_conditional_effect_def
      apply (cases "valuation eM \<Turnstile> fst eff")
      using wf_apply_effect that(2)[simplified wf_inst_cond_effect_def] 
        that(3)[simplified well_inst_cond_effect_def]
       apply auto[1]
      using that(1)
      by auto
  
  have ce_inv: "well_inst_cond_effect eM (inst_apply_conditional_effect eM eff' M) eff"
    if "well_inst_cond_effect eM M eff"
       "wf_inst_cond_effect eM eff"
       "well_inst_cond_effect eM M eff'"
       "wf_inst_cond_effect eM eff'"
       "wf_world_model M"
     for eM M eff eff'
    using that well_inst_effect_inv 
    unfolding inst_apply_conditional_effect_def 
      well_inst_cond_effect_def wf_inst_cond_effect_def by auto
 
  have "wf_world_model (fold (inst_apply_conditional_effect eM) effs M)"
    if "wf_world_model M"
       "wf_inst_cond_effect_list eM effs"
       "well_inst_cond_effect_list eM M effs" 
        for eM M effs
    using that
    unfolding wf_inst_cond_effect_list_def well_inst_cond_effect_list_def sym[OF Ball_set]
    apply (induction effs arbitrary: M)
     apply simp
    using ce_inv
    by (simp add: wf_apply_cond_effect)
  from this[OF assms]
  show "wf_world_model (apply_conditional_effect_list effs M)" 
    unfolding apply_conditional_effect_list_def .
qed
  
  lemma wf_execute_ground:
    assumes "valid_ground_action \<alpha> s"
            "wf_world_model s"
      shows "wf_world_model (execute_ground_action \<alpha> s)"
    using assms 
    unfolding execute_ground_action_def valid_ground_action_def valid_effects_def
    using wf_execute_cond_effect_list[OF assms(2)]
    by blast

  (* TODO: The execution of plan actions and ground actions does not 
            preserve well-formedness, unless we take into account that the
            effects are valid when fully instantiated *)

  text \<open>Execution of plan actions preserves well-formedness\<close>
  theorem wf_execute:
    assumes "valid_plan_action \<pi> s"
    assumes "wf_world_model s"
    shows "wf_world_model (execute_plan_action \<pi> s)"
    using assms wf_execute_ground valid_plan_action_def execute_plan_action_def
    by simp
  

  theorem wf_execute_compact_notation:
    "valid_plan_action \<pi> s \<Longrightarrow> wf_world_model s
    \<Longrightarrow> wf_world_model (execute_plan_action \<pi> s)"
    by (rule wf_execute)

  text \<open>Execution of a plan preserves well-formedness\<close>
  corollary wf_plan_action_path:
    assumes "wf_world_model M" 
      and "plan_action_path M \<pi>s M'"
    shows "wf_world_model M'"
    using assms
    by (induction \<pi>s arbitrary: M) (auto intro: wf_execute)

  corollary valid_plan: "valid_plan \<pi>s \<equiv>
    \<exists>M'. plan_action_path I \<pi>s M' 
    \<and> valuation M' \<Turnstile> inst_goal (goal P) 
    \<and> wf_world_model M'"
    apply (subst valid_plan_alt)
    apply (rule eq_reflection)
    using wf_plan_action_path[OF wf_I]
    by blast

  text \<open>Meaning of non-interfering effects\<close>

  lemma non_int_pred_upds_twist:
    assumes "non_int_pred_upds a d a' d'"
    shows "(p - (set (map the d)) \<union> (set (map the a))) - (set (map the d')) \<union> (set (map the a'))
    = (p - (set (map the d')) \<union> (set (map the a'))) - (set (map the d)) \<union> (set (map the a))"
    apply (insert assms)
    apply (subst (asm) non_int_pred_upds_def)
    apply (subst (asm) disjoint_inst_upd_lists_def)+
    apply (subst (asm) map_fun_def)+
    apply (subst (asm) comp_def)+
    apply (subst (asm) map_fun_def)+
    apply (subst (asm) comp_def)+
    apply (subst (asm) id_def)+
    apply (subst (asm) disjoint_upd_lists_def)+
    by blast

  lemma upd_nf_int_twist:
    assumes "non_int_ops op op'"
    shows "upd_nf_int (upd_nf_int m op args old n) op' args (the (upd_nf_int m op args old n args)) n'
        = upd_nf_int (upd_nf_int m op' args old n') op args (the (upd_nf_int m op' args old n' args)) n"
    using assms
    by (cases op; cases op'; auto)
  
  lemma upd_nf_int_twist':
    assumes "args \<noteq> args'"
    shows "upd_nf_int (upd_nf_int m op args old n) op' args' old' n'
        = upd_nf_int (upd_nf_int m op' args' old' n') op args old n"
    apply (induction op; induction op')
    by ((subst upd_nf_int.simps)+, subst fun_upd_twist[OF assms], rule refl)+
  
  lemma upd_nf_int_other:
    assumes "args \<noteq> args'"
    shows "upd_nf_int m op args old n args' = m args'"
    using fun_upd_other[OF assms]
    by (cases op, force+)

  lemma non_int_nf_upd_twist: 
    assumes "non_int_nf_upds a b" 
            "wf_app_nf_upd a"
            "wf_app_nf_upd b"
    shows "apply_nf_upd b (apply_nf_upd a ni) = apply_nf_upd a (apply_nf_upd b ni)"
  proof -
    obtain op f as v op' f' as' v' where
      a_b_def[simp]: "b = NFU op f as v"
              "a = NFU op' f' as' v'"
      by (cases a; cases b; auto)
    have "apply_nf_upd (NFU op f as v) (apply_nf_upd (NFU op' f' as' v') ni) x
      = apply_nf_upd (NFU op' f' as' v') (apply_nf_upd (NFU op f as v) ni) x" for x
    proof (cases "x = f"; cases "x = f'")
      assume "x = f" "x = f'"   
      hence "f' = f" by simp
  
      show "apply_nf_upd (NFU op f as v) (apply_nf_upd (NFU op' f' as' v') ni) x
        = apply_nf_upd (NFU op' f' as' v') (apply_nf_upd (NFU op f as v) ni) x"
      proof (cases "as' = as")
        case True
        show ?thesis
          proof (cases "op = Assign")
            case True
            with assms \<open>as' = as\<close> \<open>f' = f\<close>
            have "v' = v" "op' = op" by auto
            show ?thesis 
              using \<open>v' = v\<close> \<open>f' = f\<close> \<open>as' = as\<close> \<open>op' = op\<close>
              by simp
          next
            case False
            with \<open>f' = f\<close> \<open>as' = as\<close> assms
            have "non_int_ops op op'" by (cases op; cases op'; auto) 
            obtain m'' where 
              1: "(apply_nf_upd (NFU op' f as v') ni) f = 
              Some (upd_nf_int m'' op' (map the as) (the (m'' (map the as))) (the v'))"
              (is "_ = Some ?m1'")
              and 
              2: "(apply_nf_upd (NFU op f as v) ni) f = 
              Some (upd_nf_int m'' op (map the as) (the (m'' (map the as))) (the v))"
              (is "_ = Some ?m2'")
              by (cases "ni f"; auto)
    
            have "apply_nf_upd (NFU op f as v) (apply_nf_upd (NFU op' f as v') ni) f = 
              Some (upd_nf_int ?m1' op (map the as) (the (?m1' (map the as))) (the v))"
              apply (subst (1) apply_nf_upd.simps)
              apply (subst 1)
              by (simp add: Let_def)
            moreover
            have "apply_nf_upd (NFU op' f as v') (apply_nf_upd (NFU op f as v) ni) f =
              Some (upd_nf_int ?m2' op' (map the as) (the (?m2' (map the as))) (the v'))"
              apply (subst (1) apply_nf_upd.simps)
              apply (subst 2)
              by (simp add: Let_def)
            moreover
            have "upd_nf_int ?m1' op (map the as) (the (?m1' (map the as))) (the v) =
              upd_nf_int ?m2' op' (map the as) (the (?m2' (map the as))) (the v')"
              using upd_nf_int_twist[OF \<open>non_int_ops op op'\<close>] by auto
            ultimately
            have "apply_nf_upd (NFU op f as v) (apply_nf_upd (NFU op' f as v') ni) f = 
               apply_nf_upd (NFU op' f as v') (apply_nf_upd (NFU op f as v) ni) f" by argo
            then show ?thesis using \<open>f' = f\<close> \<open>as' = as\<close> \<open>x = f\<close> by simp
          qed
        next
          case False
          obtain m old new old' new' where
            1: "apply_nf_upd (NFU op' f as' v') ni f = Some (upd_nf_int m op' (map the as') old' new')"
              "old' = the (m (map the as'))"
              "new' = the v'"
            and 2: "apply_nf_upd (NFU op f as v) ni f = Some (upd_nf_int m op (map the as) old new)"
              "old = the (m (map the as))"
              "new = the v"
            by (cases "ni f"; auto)
          from assms(2, 3)[simplified a_b_def] False
          have 3: "map the as' \<noteq> map the as"
            using is_some_map_the_neq by auto
            
          have "apply_nf_upd (NFU op f as v) (apply_nf_upd (NFU op' f as' v') ni) f 
            = Some (upd_nf_int (upd_nf_int m op' (map the as') old' new') op (map the as) old new)"
            apply (subst (1) apply_nf_upd.simps)
            apply (subst 1)
            apply (subst 2(2,3))+
            apply (simp add: Let_def)
            apply (subst upd_nf_int_other[OF 3]) ..
          moreover
          have "apply_nf_upd (NFU op' f as' v') (apply_nf_upd (NFU op f as v) ni) f 
            = Some (upd_nf_int (upd_nf_int m op (map the as) old new) op' (map the as') old' new')"
            apply (subst (1) apply_nf_upd.simps)
            apply (subst 2)
            apply (subst 1(2,3))+
            apply (simp add: Let_def)
            apply (subst upd_nf_int_other[OF 3[symmetric]]) ..
          ultimately
          have "apply_nf_upd (NFU op f as v) (apply_nf_upd (NFU op' f as' v') ni) f
            = apply_nf_upd (NFU op' f as' v') (apply_nf_upd (NFU op f as v) ni) f"
            using upd_nf_int_twist'[OF \<open>map the as' \<noteq> map the as\<close>[symmetric]] by auto
          then show ?thesis using \<open>x = f\<close> \<open>f' = f\<close> \<open>x = f'\<close> by blast
        qed
      qed (auto simp: Let_def)
      thus ?thesis by auto
    qed


lemma non_int_nf_upd_list_rev:
  assumes "non_int_nf_upd_list xs"
      and "list_all wf_app_nf_upd xs"
  shows "fold apply_nf_upd xs ni = fold apply_nf_upd (rev xs) ni"
  apply (subst fold_rev)
  apply (subst comp_def)+
   apply (subst non_int_nf_upd_twist)
  by (simp add: assms[simplified non_int_nf_upd_list_iff pairwise_def list_all_iff])+
  
  lemma apply_of_upd_other: 
    assumes "f \<noteq> f'"
    shows "apply_of_upd (OFU f as v) oi f' = oi f'"
    using assms
    by (cases "oi f"; simp)
  
  lemma non_int_of_upd_twist:
    assumes "non_int_of_upds a b" 
        and "wf_app_of_upd a"
        and "wf_app_of_upd b"
      shows "apply_of_upd b (apply_of_upd a oi) = apply_of_upd a (apply_of_upd b oi)"
  proof -
    obtain f as v f' as' v' where
      a_b_def[simp]: "a = OFU f as v"
      "b = OFU f' as' v'"
      by (cases a; cases b; auto)
  
    have "apply_of_upd (OFU f as v) (apply_of_upd (OFU f' as' v') oi) x
      = apply_of_upd (OFU f' as' v') (apply_of_upd (OFU f as v) oi) x" for x
    proof(cases "x = f"; cases "x = f'")
      assume "x = f" "x = f'"
      hence "f' = f" by simp
      obtain m where
        1: "apply_of_upd (OFU f as v) oi f = Some (m((map the as) := v))"
        and 2: "apply_of_upd (OFU f as' v') oi f = Some (m((map the as') := v'))"
        by (cases "oi f"; auto)
      have "apply_of_upd (OFU f as v) (apply_of_upd (OFU f as' v') oi) f
        = apply_of_upd (OFU f as' v') (apply_of_upd (OFU f as v) oi) f"
      proof (cases "as' = as")
        case True
        with assms(1) \<open>f' = f\<close>
        have \<open>v = v'\<close> by simp
        with \<open>f' = f\<close> \<open>as' = as\<close>
        show ?thesis by simp
      next
        case False
        
        have "apply_of_upd (OFU f as v) (apply_of_upd (OFU f as' v') oi) f
          = Some ((m((map the as') := v'))((map the as) := v))"
          using 2 by simp
        moreover
        have "apply_of_upd (OFU f as' v') (apply_of_upd (OFU f as v) oi) f
          = Some ((m((map the as) := v))((map the as') := v'))"
          using 1 by simp
        moreover 
        have "map the as \<noteq> map the as'" 
          using assms(2, 3) is_some_map_the_neq[OF False]
          by (auto split: option.splits prod.split)
          (* the definition of wf_app_nf_upd is nicer here, because the case distinction is left out *)
        ultimately
        show ?thesis using fun_upd_twist by auto
      qed
      thus ?thesis using \<open>x = f\<close> \<open>f' = f\<close> by simp
    next
      assume "x = f" "x \<noteq> f'"
      hence "f \<noteq> f'" by simp
      have 1: "apply_of_upd (OFU f' as' v') oin f = oin f" for oin
        by (cases "oin f'"; auto simp: \<open>f \<noteq> f'\<close>)
      have "apply_of_upd (OFU f as v) (apply_of_upd (OFU f' as' v') oi) f 
        = apply_of_upd (OFU f' as' v') (apply_of_upd (OFU f as v) oi) f"
        apply (subst apply_of_upd.simps)
        apply (subst 1[where oin43 = oi])
        apply (subst 1[where oin43 = "apply_of_upd (OFU f as v) oi"])
        by (cases "oi f"; auto)
      with \<open>x = f\<close>
      show ?thesis by simp
    next
      assume "x \<noteq> f" "x = f'"
      hence "f \<noteq> f'" by simp
  
      have 1: "apply_of_upd (OFU f as v) oin f' = oin f'" for oin
        by (cases "oin f"; auto simp: \<open>f \<noteq> f'\<close>[symmetric])
      
      have "apply_of_upd (OFU f as v) (apply_of_upd (OFU f' as' v') oi) f' 
        = apply_of_upd (OFU f' as' v') (apply_of_upd (OFU f as v) oi) f'"
        apply (subst (3) apply_of_upd.simps)
        apply (subst 1[where oin43 = oi])
        apply (subst 1[where oin43 = "apply_of_upd (OFU f' as' v') oi"])
        by (cases "oi f'"; auto)
      with \<open>x = f'\<close>
      show ?thesis by simp
    next
      assume "x \<noteq> f" "x \<noteq> f'"
      then show ?thesis using apply_of_upd_other by simp
    qed
    thus ?thesis by fastforce 
  qed

lemma non_int_of_upd_list_rev:
  assumes "non_int_of_upd_list xs"
      and "list_all wf_app_of_upd xs"
    shows "fold apply_of_upd xs ni = fold apply_of_upd (rev xs) ni"
  apply (subst fold_rev)
  apply (subst comp_def)+
   apply (subst non_int_of_upd_twist)
  by (simp add: assms[simplified non_int_of_upd_list_iff pairwise_def list_all_iff])+
  
(* show that non-interfering effects commute *)

lemma non_int_eff_twist:
  assumes "non_int_effs x y"
      and "wf_fully_instantiated_effect x"
      and "wf_fully_instantiated_effect y"
  shows "apply_effect x (apply_effect y M) = apply_effect y (apply_effect x M)"
proof -
  obtain a d nu ou a' d' nu' ou' p oi ni where
    x_y_def[simp]: "x = Eff a d ou nu"
    "y = Eff a' d' ou' nu'"
    and M_def[simp]: "M = World_Model p oi ni"
    by (cases x; cases y; cases M; auto)
  from assms
  have "non_int_pred_upds a d a' d'"
    by (simp add: non_int_effs_def eff_adds_def eff_dels_def)
  from non_int_pred_upds_twist[OF this]
  have "p - set (map the d) \<union> set (map the a) - set (map the d') \<union> set (map the a') 
    = p - set (map the d') \<union> set (map the a') - set (map the d) \<union> set (map the a)" by simp
  moreover
  {
    from assms(1)
    have 1: "non_int_nf_upd_list (nu @ nu')"
      using non_int_effs_def nus_def non_int_nf_upd_lists_def by simp
    hence 11: "non_int_nf_upd_list (nu' @ nu)"
      unfolding non_int_nf_upd_list_def using set_append
      by (simp add: Un_commute)
    from 1 
    have 12: "non_int_nf_upd_list nu" "non_int_nf_upd_list nu'"
      unfolding non_int_nf_upd_list_def pairwise_def by auto
    from assms(2, 3)
    have 22: "list_all wf_app_nf_upd nu" "list_all wf_app_nf_upd nu'"
      by (simp add: list_all_iff)+
    hence 21: "list_all wf_app_nf_upd (nu' @ nu)" by simp
    have "fold apply_nf_upd nu (fold apply_nf_upd nu' ni) = fold apply_nf_upd nu' (fold apply_nf_upd nu ni)"
      apply (subst comp_apply[of "fold apply_nf_upd nu" "fold apply_nf_upd nu'", symmetric])
      apply (subst fold_append[symmetric])
      apply (subst non_int_nf_upd_list_rev[OF 11 21])
      apply (subst rev_append)
      apply (subst fold_append[simplified comp_def])
      apply (subst non_int_nf_upd_list_rev[OF 12(1) 22(1)])
      apply (subst non_int_nf_upd_list_rev[OF 12(2) 22(2)])
      by simp
  }
  moreover
  {
    from assms(1)
    have 1: "non_int_of_upd_list (ou @ ou')"
      using non_int_effs_def ous_def non_int_of_upd_lists_def by simp
    hence 11: "non_int_of_upd_list (ou' @ ou)"
      unfolding non_int_of_upd_list_def using set_append
      by (simp add: Un_commute)
    from 1 
    have 12: "non_int_of_upd_list ou" "non_int_of_upd_list ou'"
      unfolding non_int_of_upd_list_def pairwise_def by auto
    from assms(2, 3)
    have 22: "list_all wf_app_of_upd ou" "list_all wf_app_of_upd ou'"
      by (simp add: list_all_iff)+
    hence 21: "list_all wf_app_of_upd (ou' @ ou)" by simp
    have "fold apply_of_upd ou (fold apply_of_upd ou' oi) = fold apply_of_upd ou' (fold apply_of_upd ou oi)"
      apply (subst comp_apply[of "fold apply_of_upd ou" "fold apply_of_upd ou'", symmetric])
      apply (subst fold_append[symmetric])
      apply (subst non_int_of_upd_list_rev[OF 11 21])
      apply (subst rev_append)
      apply (subst fold_append[simplified comp_def])
      apply (subst non_int_of_upd_list_rev[OF 12(1) 22(1)])
      apply (subst non_int_of_upd_list_rev[OF 12(2) 22(2)])
      by simp
  }
  ultimately
  show "apply_effect x (apply_effect y M) = apply_effect y (apply_effect x M)"
    by simp
qed

lemma non_int_cond_effs_twist:
  assumes "non_int_cond_effs eM a b"
      and "wf_inst_cond_effect eM a"
      and "wf_inst_cond_effect eM b"
    shows "inst_apply_conditional_effect eM a (inst_apply_conditional_effect eM b M)
      = inst_apply_conditional_effect eM b (inst_apply_conditional_effect eM a M)"
proof -
  obtain pa ea pb eb where
    "a = (pa, ea)"
    "b = (pb, eb)"
    by force
  show ?thesis
  proof (cases "valuation eM \<Turnstile> (fst a)"; cases "valuation eM \<Turnstile> (fst b)")
    assume a: "valuation eM \<Turnstile> (fst a)" "valuation eM \<Turnstile> (fst b)"
    show ?thesis
      apply (subst inst_apply_conditional_effect_def)+
      apply (subst a)+
      apply (subst if_True)+
      apply (subst inst_apply_effect_def)+
      apply (rule non_int_eff_twist)
      using assms(1)[simplified non_int_cond_effs_def, THEN mp, OF conjI[OF a]]
        assms(2)[simplified wf_inst_cond_effect_def, THEN mp, OF a(1)]
        assms(3)[simplified wf_inst_cond_effect_def, THEN mp, OF a(2)]
      by simp+
      
  qed (auto simp: inst_apply_conditional_effect_def)
qed

lemma non_int_effects_apply_rev:
  assumes "non_int_cond_eff_list M xs"
      and "wf_inst_cond_effect_list M xs"
  shows "apply_conditional_effect_list xs M = apply_conditional_effect_list (rev xs) M"
 apply (subst apply_conditional_effect_list_def)+
  apply (subst List.fold_rev[simplified comp_def, where f = "inst_apply_conditional_effect M", symmetric])
  subgoal for x y
    using non_int_cond_effs_twist[where eM = M and a = y and b = x]
    assms[simplified non_int_cond_eff_list_def wf_inst_cond_effect_list_def list_all_iff]
    by blast
  ..
  
lemma non_int_init_assign_twist:
  assumes "non_int_fun_assign a b"
  shows "add_init_int a (add_init_int b M) = add_init_int b (add_init_int a M)"
proof -
  obtain f1 as1 v1 f2 as2 v2 where
    [simp]: "a = (f1, as1, v1)"
    "b = (f2, as2, v2)"
    by (cases a; cases b; auto)
  have "add_init_int (f1, as1, v1) (add_init_int (f2, as2, v2) M) 
    = add_init_int (f2, as2, v2) (add_init_int (f1, as1, v1) M)"
  proof (cases "f1 = f2")
    assume a: "f1 = f2"
    have "add_init_int (f1, as1, v1) (add_init_int (f1, as2, v2) M) x
      = add_init_int (f1, as2, v2) (add_init_int (f1, as1, v1) M) x" for x
    proof (cases "x = f1")
      case [simp]: True
      obtain m where
        "add_init_int (f1, as1, v1) M f1 = Some (m(as1\<mapsto>v1))"
        "add_init_int (f1, as2, v2) M f1 = Some (m(as2\<mapsto>v2))"
        by (cases "M f1"; auto)
      hence 1: "add_init_int (f1, as1, v1) (add_init_int (f1, as2, v2) M) f1
        = Some ((m(as2\<mapsto>v2))(as1\<mapsto>v1))"
        "add_init_int (f1, as2, v2) (add_init_int (f1, as1, v1) M) f1
        = Some ((m(as1\<mapsto>v1))(as2\<mapsto>v2))"
        by auto
      from assms \<open>f1 = f2\<close>
      consider "as1 \<noteq> as2" | "as1 = as2 \<and> v1 = v2" by auto
      then show ?thesis 
      proof cases
        assume "as1 \<noteq> as2"
        from 1 \<open>f1 = f2\<close> \<open>x = f1\<close>
        show ?thesis using fun_upd_twist[OF \<open>as1 \<noteq> as2\<close>, of m] 
          by simp
      next
        assume "as1 = as2 \<and> v1 = v2"
        with 1 \<open>f1 = f2\<close> \<open>x = f1\<close>
        show ?thesis by presburger
      qed
    next
      case False
      then show ?thesis by (cases "M f1"; auto)
    qed
    with a
    show ?thesis by blast
  next
    assume a: "f1 \<noteq> f2"
    obtain m1 m2 where
      a1: "add_init_int (f1, as1, v1) M = M(f1 \<mapsto> m1(as1 \<mapsto> v1))"
      and a2: "add_init_int (f2, as2, v2) M = M(f2 \<mapsto> m2(as2 \<mapsto> v2))"
      by (cases "M f1"; cases "M f2"; auto)
    have "add_init_int (f2, as2, v2) (add_init_int (f1, as1, v1) M) 
      = (M (f1 \<mapsto> m1(as1 \<mapsto> v1)))(f2 \<mapsto> m2(as2 \<mapsto> v2))" 
      using a1 a2 fun_upd_other[OF a[symmetric]]
      apply (cases "M f2")
      by (auto dest: map_upd_eqD1)
    moreover
    have "add_init_int (f1, as1, v1) (add_init_int (f2, as2, v2) M) 
      = (M (f2 \<mapsto> m2(as2 \<mapsto> v2)))(f1 \<mapsto> m1(as1 \<mapsto> v1))"
      using a1 a2 fun_upd_other[OF a]
      apply (cases "M f1")
      by (auto dest: map_upd_eqD1)
    ultimately
    show ?thesis using fun_upd_twist[OF a, of M] by presburger
  qed
  thus ?thesis by simp
qed

lemma (in wf_ast_problem) init_nfi_alt: 
  "nfi = fold add_init_int (rev (init_nfs P)) Map.empty"
  unfolding nfi_def 
proof (subst fold_rev[simplified comp_def])
  fix x y
  assume a: "x \<in> set (init_nfs P)" "y \<in> set (init_nfs P)"
  have "add_init_int y (add_init_int x M) = add_init_int x (add_init_int y M)" for M
  proof -
    from wf_problem[simplified wf_problem_def non_int_assign_list_iff] a
    have "non_int_fun_assign x y" by blast
    thus "add_init_int y (add_init_int x M) = add_init_int x (add_init_int y M)" 
      using non_int_init_assign_twist[where M = M, symmetric] by simp
  qed
  thus "(\<lambda>xa. add_init_int y (add_init_int x xa)) = (\<lambda>xa. add_init_int x (add_init_int y xa))" by simp
qed simp

end

subsubsection \<open>Semantics of quantifiers following instantiation\<close>

text \<open>Here are some lemmas that prove that the semantics of quantified formulas
      are correct following instantiation. If we have a goal or an action schema that
      used a macro expansion for formulae with quantifiers, we can be sure that it expresses
      what we wanted it to.\<close>
context ast_problem begin
  
  notation all ("\<^bold>\<forall>_ - _._")   
  notation exists ("\<^bold>\<exists>_ - _._")

  text \<open>The semantics of quantifiers in preconditions and the goal 
        will behave as expected\<close>
  
  context 
    fixes f::"schematic_formula \<Rightarrow> ground_formula"
      and \<A>::"object term atom valuation"
    assumes f: "\<exists>f'. f = map_formula f'"
  begin
  
    lemma f_dist_conj: "\<A> \<Turnstile> f (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) \<longleftrightarrow> \<A> \<Turnstile> f \<phi>\<^sub>1 \<and> \<A> \<Turnstile> f \<phi>\<^sub>2"
    using f by auto
  
    lemma f_dist_disj: "\<A> \<Turnstile> f (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<longleftrightarrow> \<A> \<Turnstile> f \<phi>\<^sub>1 \<or> \<A> \<Turnstile> f \<phi>\<^sub>2"
    using f by auto
      
    lemma Big_And_sem: "\<A> \<Turnstile> f (\<^bold>\<And>\<phi>s) \<longleftrightarrow> (\<forall>\<phi> \<in> set (\<phi>s). \<A> \<Turnstile> f \<phi>)"
      using f_dist_conj f
      by (induction \<phi>s) auto

    lemma Big_Or_sem: "\<A> \<Turnstile> f (\<^bold>\<Or>\<phi>s) \<longleftrightarrow> (\<exists>\<phi> \<in> set (\<phi>s). \<A> \<Turnstile> f \<phi>)"
      using f_dist_disj f
      by (induction \<phi>s) auto
    
    lemma all_distrib_f: "\<A> \<Turnstile> (f \<^bold>\<forall>v - ty. \<phi>) \<longleftrightarrow>
      (\<forall>c \<in> set (t_dom ty). \<A> \<Turnstile> f (f_subst v c \<phi>))"
    proof cases
      assume a: "v \<notin> f_vars \<phi> \<and> t_dom ty \<noteq> []"
      hence "\<^bold>\<forall>v - ty. \<phi> = \<phi>" unfolding all_def by auto
      hence "\<A> \<Turnstile> (f \<^bold>\<forall>v - ty. \<phi>) \<longleftrightarrow> \<A> \<Turnstile> f \<phi>" by presburger
      moreover 
      from a
      have "\<forall>c. f_subst v c \<phi> = \<phi>" using f_subst_idem by blast
      hence "(\<forall>c\<in>set (t_dom ty). \<A> \<Turnstile> f \<phi>) \<longleftrightarrow> (\<forall>c\<in>set (t_dom ty). \<A> \<Turnstile> f (f_subst v c \<phi>))" by simp
      ultimately show ?thesis unfolding all_def using a by blast
    next
      assume "\<not>(v \<notin> f_vars \<phi> \<and> t_dom ty \<noteq> [])"
      hence "\<A> \<Turnstile> (f \<^bold>\<forall>v - ty. \<phi>) \<longleftrightarrow> \<A> \<Turnstile> (f \<^bold>\<And>(map (\<lambda>c. f_subst v c \<phi>) (t_dom ty)))" unfolding all_def by force
      also have "... \<longleftrightarrow> (\<forall>\<phi> \<in> set (map (\<lambda>c. f_subst v c \<phi>) (t_dom ty)). \<A> \<Turnstile> f \<phi>)" using Big_And_sem by blast
      also have "... \<longleftrightarrow> (\<forall>c \<in> set (t_dom ty). \<A> \<Turnstile> f (f_subst v c \<phi>))" by auto
      finally show ?thesis .
    qed

    lemma exist_distrib_f: "\<A> \<Turnstile> (f \<^bold>\<exists>v - ty. \<phi>) \<longleftrightarrow>
      (\<exists>c \<in> set (t_dom ty). \<A> \<Turnstile> f (f_subst v c \<phi>))"
    proof cases
      assume a: "v \<notin> f_vars \<phi> \<and> t_dom ty \<noteq> []"
      hence "\<A> \<Turnstile> (f \<^bold>\<exists>v - ty. \<phi>) \<longleftrightarrow> \<A> \<Turnstile> f \<phi>" unfolding exists_def by auto
      moreover 
      from a
      have "\<forall>c. f_subst v c \<phi> = \<phi>" using f_subst_idem by blast
      hence "(\<exists>c\<in>set (t_dom ty). \<A> \<Turnstile> f \<phi>) \<longleftrightarrow> (\<exists>c\<in>set (t_dom ty). \<A> \<Turnstile> f (f_subst v c \<phi>))" by simp
      ultimately show ?thesis using a by blast
    next
      assume "\<not>(v \<notin> f_vars \<phi> \<and> t_dom ty \<noteq> [])"
      hence "\<A> \<Turnstile> (f \<^bold>\<exists>v - ty. \<phi>) \<longleftrightarrow> \<A> \<Turnstile> (f \<^bold>\<Or>(map (\<lambda>c. f_subst v c \<phi>) (t_dom ty)))" unfolding exists_def by force
      also have "... \<longleftrightarrow> (\<exists>\<phi> \<in> set (map (\<lambda>c. f_subst v c \<phi>) (t_dom ty)). \<A> \<Turnstile> f \<phi>)" using Big_Or_sem by blast
      also have "... \<longleftrightarrow> (\<exists>c \<in> set (t_dom ty). \<A> \<Turnstile> f (f_subst v c \<phi>))" by auto
      finally show ?thesis .
    qed
    
end


  lemma inst_goal_ex_sem: "valuation M \<Turnstile> (inst_goal \<^bold>\<exists>v - ty. \<phi>) \<longleftrightarrow>
        (\<exists>c \<in> set (t_dom ty). valuation M \<Turnstile> inst_goal (f_subst v c \<phi>))"
  proof -
    have "\<exists>f'. inst_goal = map_formula f'" by force
    thus ?thesis using exist_distrib_f by blast
  qed

  lemma map_pre_ex_sem:
      assumes "a = Action_Schema n params (\<^bold>\<exists>v - ty. \<phi>) eff"
      assumes "action_params_match a args"
      assumes "Ground_Action pre_inst eff_inst = instantiate_action_schema a args"
      shows "pre_inst = map_pre (inst_term params args) (\<^bold>\<exists>v - ty. \<phi>) \<and> 
          valuation M \<Turnstile> pre_inst \<longleftrightarrow> (\<exists>c \<in> set (t_dom ty). 
            valuation M \<Turnstile> map_pre (inst_term params args) (f_subst v c \<phi>))"
  proof -
    have 1: "\<exists>f'. map_pre (inst_term params args) = map_formula f'" by fastforce
    have "pre_inst = map_pre (inst_term params args) (\<^bold>\<exists>v - ty. \<phi>)" using assms by (auto simp: Let_def)
    then show ?thesis using exist_distrib_f[OF 1] by presburger
  qed
  
  lemma map_pre_all_sem:
      assumes "a = Action_Schema n params (\<^bold>\<forall>v - ty. \<phi>) eff"
      assumes "action_params_match a args"
      assumes "Ground_Action pre_inst eff_inst = instantiate_action_schema a args"
      shows "pre_inst = map_pre (inst_term params args) (\<^bold>\<forall>v - ty. \<phi>) \<and> 
          valuation M \<Turnstile> pre_inst \<longleftrightarrow> (\<forall>c \<in> set (t_dom ty). 
            valuation M \<Turnstile> map_pre (inst_term params args) (f_subst v c \<phi>))"
  proof -
    have 1: "\<exists>f'. map_pre (inst_term params args) = map_formula f'" by fastforce
    have "pre_inst = map_pre (inst_term params args) (\<^bold>\<forall>v - ty. \<phi>)" using assms by (auto simp: Let_def)
    then show ?thesis using all_distrib_f[OF 1] by presburger
  qed

lemma pddl_all_precondition_sem:
  assumes "a = Action_Schema n params (pddl_all vts \<phi>) eff"
    and "action_params_match a args"
    and "Ground_Action pre_inst eff_inst = instantiate_action_schema a args"
  shows "pre_inst = map_pre (inst_term params args) (pddl_all vts \<phi>) \<and>
        valuation M \<Turnstile> pre_inst \<longleftrightarrow> valuation M \<Turnstile> map_pre (inst_term params args) (foldr (\<lambda>(v, ty) \<phi>. (\<^bold>\<forall>v - ty. \<phi>)) vts \<phi>)"
proof -
  have "map_pre (inst_term params args) (pddl_all vts \<phi>) 
        = map_pre (inst_term params args) (foldr (\<lambda>(v, ty) \<phi>. (\<^bold>\<forall>v - ty. \<phi>)) vts \<phi>)" unfolding pddl_all_def assms
    by (auto simp: Let_def)
  hence "valuation M \<Turnstile> map_pre (inst_term params args) (pddl_all vts \<phi>) \<longleftrightarrow> valuation M \<Turnstile> map_pre (inst_term params args) (foldr (\<lambda>(v, ty) \<phi>. (\<^bold>\<forall>v - ty. \<phi>)) vts \<phi>)"
    by simp
  with assms
  show "pre_inst = map_pre (inst_term params args) (pddl_all vts \<phi>) \<and>
        valuation M \<Turnstile> pre_inst \<longleftrightarrow> valuation M \<Turnstile> map_pre (inst_term params args) (foldr (\<lambda>(v, ty) \<phi>. (\<^bold>\<forall>v - ty. \<phi>)) vts \<phi>)"
    by (metis ground_action.sel(1) instantiate_action_schema.simps)
qed

lemma pddl_exists_precondition_sem:
  assumes "a = Action_Schema n params (pddl_exists vts \<phi>) eff"
    and "action_params_match a args"
    and "Ground_Action pre_inst eff_inst = instantiate_action_schema a args"
  shows "pre_inst = map_pre (inst_term params args) (pddl_exists vts \<phi>) \<and> valuation M \<Turnstile> pre_inst 
    \<longleftrightarrow> valuation M \<Turnstile> map_pre (inst_term params args) (foldr (\<lambda>(v, ty) \<phi>. (\<^bold>\<exists>v - ty. \<phi>)) vts \<phi>)"
proof -
  have "map_pre (inst_term params args) (pddl_exists vts \<phi>) 
        = map_pre (inst_term params args) (foldr (\<lambda>(v, ty) \<phi>. (\<^bold>\<exists>v - ty. \<phi>)) vts \<phi>)" unfolding pddl_exists_def assms
    by (auto simp: Let_def)
  hence "valuation M \<Turnstile> map_pre (inst_term params args) (pddl_exists vts \<phi>) \<longleftrightarrow> valuation M \<Turnstile> map_pre (inst_term params args) (foldr (\<lambda>(v, ty) \<phi>. (\<^bold>\<exists>v - ty. \<phi>)) vts \<phi>)"
    by simp
  with assms
  show "pre_inst = map_pre (inst_term params args) (pddl_exists vts \<phi>) \<and>
        valuation M \<Turnstile> pre_inst \<longleftrightarrow> valuation M \<Turnstile> map_pre (inst_term params args) (foldr (\<lambda>(v, ty) \<phi>. (\<^bold>\<exists>v - ty. \<phi>)) vts \<phi>)"
    by (metis ground_action.sel(1) instantiate_action_schema.simps)
qed

lemma pddl_univ_effect_sem:
  assumes "ces = pddl_univ_effect_list vts eff"
      and "ces1 = foldr (\<lambda>(v, t) effs. univ_effect_list v t effs) vts eff"
      and "params_match params args"
      and "ces' = map (map_cond_effect (inst_term params args)) ces"
      and "ces1' = map (map_cond_effect (inst_term params args)) ces1"
  shows "foldr (inst_apply_conditional_effect M) ces' M = foldr (inst_apply_conditional_effect M) ces1' M"
  using assms unfolding pddl_univ_effect_list_def
  by simp

end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>

end \<comment> \<open>Theory\<close>
