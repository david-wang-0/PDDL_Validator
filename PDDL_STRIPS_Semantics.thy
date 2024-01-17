section \<open>PDDL and STRIPS Semantics\<close>
theory PDDL_STRIPS_Semantics
imports
  "FO-proof-systems/Formulas"
  "FO-proof-systems/Sema"
  "Automatic_Refinement.Misc"
  "Automatic_Refinement.Refine_Util"
  "Show.Show_Instances" 
begin

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

subsection \<open>Abstract Syntax\<close>

subsubsection \<open>Generic Entities\<close>
type_synonym name = string

datatype predicate = Pred (name: name)

text \<open>Some of the AST entities are defined over a polymorphic \<open>'val\<close> type,
  which gets either instantiated by variables (for domains)
  or objects (for problems).
\<close>

text \<open>An atom is either a predicate with arguments, or an equality statement.\<close>
datatype (ent: 'ent) atom = predAtm (predicate: predicate) (arguments: "'ent list")
                     | Eq (lhs: 'ent) (rhs: 'ent)

text \<open>A type is a list of primitive type names.
  To model a primitive type, we use a singleton list.\<close>
datatype type = Either (primitives: "name list")

text \<open>An effect contains a list of values to be added, and a list of values
  to be removed.\<close>
datatype ('ent, 'var, 'ty) ast_effect = 
  Effect  (adds: "(('ent atom, 'var, 'ty) formula) list") 
          (dels: "(('ent atom, 'var, 'ty) formula) list")

text \<open>Variables are identified by their names.\<close>
datatype variable = varname: Var name
text \<open>Objects and constants are identified by their names\<close>
datatype object = name: Obj name

datatype "term" = VAR variable | CONST object
hide_const (open) VAR CONST \<comment> \<open>Refer to constructors by qualified names only\<close>

find_theorems name: "map*term"

datatype inst_term = VAR variable | OBJ object
hide_const (open) VAR OBJ

type_synonym schematic_formula = "(term atom, variable, type) formula"
type_synonym schematic_effect = "(term, variable, type) ast_effect"

(* should not be called ground, but instantiated *)
type_synonym inst_formula = "(inst_term atom, variable, type) formula"
type_synonym inst_effect = "(inst_term, variable, type) ast_effect"

subsubsection \<open>Domains\<close>

text \<open>An action schema has a name, a typed parameter list, a precondition,
  and an effect.\<close>
datatype ast_action_schema = Action_Schema
  (name: name)
  (parameters: "(variable \<times> type) list")
  (precondition: "schematic_formula")
  (effect: "schematic_effect")


text \<open>A predicate declaration contains the predicate's name and its
  argument types.\<close>
datatype predicate_decl = PredDecl
  (pred: predicate)
  (argTs: "type list")

datatype type_env = TypeEnv
  (types: "(name \<times> name) list") \<comment> \<open> \<open>(type, supertype)\<close> declarations. \<close>
  ("consts": "(object \<times> type) list")
   

text \<open>A domain contains the declarations of primitive types, predicates,
  and action schemas.\<close>
datatype ast_domain = Domain
  (predicates: "predicate_decl list")
  (actions: "ast_action_schema list")
  (type_env: "type_env")

subsubsection \<open>Problems\<close>


text \<open>A fact is a predicate applied to objects.\<close>
text \<open>Changed to inst_term, because this makes some other changes easier.
    However, the change from object term to ground term in general requires
    us to assert that variables in instantiations are bound.\<close>
text \<open> Question: are facts only using in effects? See \<open>wf_fact\<close> as well. \<close>
type_synonym fact = "predicate \<times> inst_term list"

text \<open>A problem consists of a domain, a list of objects,
  a description of the initial state, and a description of the goal state. \<close>
datatype ast_problem = Problem
  (domain: ast_domain)
  (objects: "(object \<times> type) list")
  (init: "inst_formula list")
  (goal: "inst_formula")


subsubsection \<open>Plans\<close>
datatype plan_action = PAction
  (name: name)
  (arguments: "object list")

type_synonym plan = "plan_action list"

subsubsection \<open>Ground Actions\<close>
text \<open>The following datatype represents an action scheme that has been
  instantiated by replacing the arguments with concrete objects,
  also called ground action.
\<close>
datatype inst_action = Inst_Action
  (precondition: "inst_formula")
  (effect: "inst_effect")

(* Syntax helpers for schematic formulae *)

fun schematic_term_subst::"variable \<Rightarrow> object \<Rightarrow> term \<Rightarrow> term" where
  "schematic_term_subst v obj (term.VAR x) = (if (x = v) then (term.CONST obj) else term.VAR x)" 
| "schematic_term_subst _ _ (term.CONST obj) = term.CONST obj"

abbreviation schematic_term_atom_subst where
"schematic_term_atom_subst v obj \<equiv> map_atom (schematic_term_subst v obj)"

fun schematic_term_vars where
  "schematic_term_vars (term.VAR x) = {x}" 
| "schematic_term_vars (term.CONST c) = {}"


fun schematic_term_objs where
  "schematic_term_objs (term.VAR x) = {}"
| "schematic_term_objs (term.CONST obj) = {obj}"

definition schematic_term_atom_vars where
"schematic_term_atom_vars \<equiv> \<Union> o ent o (map_atom schematic_term_vars)"


lemma sa_subst_all: "v \<notin> schematic_term_atom_vars (schematic_term_atom_subst v obj a)"
proof -
  have "schematic_term_atom_vars (schematic_term_atom_subst v obj a) = (\<Union> o ent o (map_atom schematic_term_vars)) (map_atom (schematic_term_subst v obj) a)" unfolding schematic_term_atom_vars_def by simp
  also have "...  = \<Union> (ent (map_atom schematic_term_vars (map_atom (schematic_term_subst v obj) a)))" by simp
  also have "... = \<Union> (ent (map_atom (schematic_term_vars o (schematic_term_subst v obj)) a))" by (simp add: atom.map_comp)
  finally 
  have "schematic_term_atom_vars (schematic_term_atom_subst v obj a) = \<Union> ((schematic_term_vars o (schematic_term_subst v obj)) ` ent a)" by (simp add: atom.set_map)
  moreover 
  have "\<And>t. v \<notin> (schematic_term_vars (schematic_term_subst v obj t))" 
    subgoal for t
      by (cases t) auto
    done
  ultimately 
  show "v \<notin> schematic_term_atom_vars (schematic_term_atom_subst v obj a)" by auto
qed

global_interpretation schematic_formula_syntax: 
  formula_syntax schematic_term_atom_subst schematic_term_atom_vars
  defines sf_free_vars = schematic_formula_syntax.free_vars
    and sf_bound_vars = schematic_formula_syntax.bound_vars
  by (unfold_locales, auto simp: sa_subst_all)

(* These are needed to interpret syntax and semantics of instantiated formulae *)
fun inst_term_subst::"variable \<Rightarrow> object \<Rightarrow> inst_term \<Rightarrow> inst_term" where
  "inst_term_subst v obj (inst_term.VAR x) = (if (x = v) then (inst_term.OBJ obj) else inst_term.VAR x)" 
| "inst_term_subst _ _ (inst_term.OBJ obj) = inst_term.OBJ obj"

abbreviation inst_term_atom_subst where
"inst_term_atom_subst v obj \<equiv> map_atom (inst_term_subst v obj)"

fun inst_term_vars where
  "inst_term_vars (inst_term.VAR x) = {x}" 
| "inst_term_vars (inst_term.OBJ obj) = {}"

fun inst_term_objs where
  "inst_term_objs (inst_term.VAR x) = {}"
| "inst_term_objs (inst_term.OBJ obj) = {obj}"

definition inst_term_atom_vars::"inst_term atom \<Rightarrow> variable set" where
"inst_term_atom_vars \<equiv> \<Union> o ent o (map_atom inst_term_vars)"

lemma ia_subst_all: "v \<notin> inst_term_atom_vars (inst_term_atom_subst v obj a)"
proof -
  have "inst_term_atom_vars (inst_term_atom_subst v obj a) = (\<Union> o ent o (map_atom inst_term_vars)) (map_atom (inst_term_subst v obj) a)" unfolding inst_term_atom_vars_def by simp
  also have "...  = \<Union> (ent (map_atom inst_term_vars (map_atom (inst_term_subst v obj) a)))" by simp
  also have "... = \<Union> (ent (map_atom (inst_term_vars o (inst_term_subst v obj)) a))" by (simp add: atom.map_comp)
  finally 
  have "inst_term_atom_vars (inst_term_atom_subst v obj a) = \<Union> ((inst_term_vars o (inst_term_subst v obj)) ` ent a)" by (simp add: atom.set_map)
  moreover 
  have "\<And>t. v \<notin> (inst_term_vars (inst_term_subst v obj t))" 
    subgoal for t
      by (cases t) auto
    done
  ultimately 
  show "v \<notin> inst_term_atom_vars (inst_term_atom_subst v obj a)" by auto
qed

subsection \<open>Closed-World Assumption, Equality, and Negation\<close>
text \<open>Discriminator for atomic predicate formulas.\<close>

(* A type environment is necessary for the valuation of a formula *)
locale ClosedWorld =
  fixes type_env::"type_env"
begin

  fun is_predAtom where
    "is_predAtom (Atom (predAtm _ _)) = True" | "is_predAtom _ = False"

  text \<open>The world model is a set of (atomic) formulas\<close>
  type_synonym world_model = "inst_formula set"

  fun subtype_edge where
    "subtype_edge (ty,superty) = (superty,ty)"

  definition "subtype_rel \<equiv> set (map subtype_edge (types type_env))"

  text \<open>We use a flat subtype hierarchy, where every type is a subtype
    of object, and there are no other subtype relations.

    Note that we do not need to restrict this relation to declared types,
    as we will explicitly ensure that all types used in the problem are
    declared.
    \<close>

  (*
  definition "subtype_rel \<equiv> {''object''}\<times>UNIV"
  *)

  definition of_type :: "type \<Rightarrow> type \<Rightarrow> bool" where
    "of_type oT T \<equiv> set (primitives oT) \<subseteq> subtype_rel\<^sup>* `` set (primitives T)"
  text \<open>This checks that every primitive on the LHS is contained in or a
    subtype of a primitive on the RHS\<close>

  text \<open>Filter those constants in the domain that belong to the type.\<close>
  definition t_dom::"type \<Rightarrow> object list" where
  "t_dom typ \<equiv> map (\<lambda>(c, t) \<Rightarrow> c) (filter (\<lambda>(c, t) \<Rightarrow> of_type t typ) (consts type_env))"

end

sublocale ClosedWorld \<subseteq> formula_semantics 
    inst_term_atom_subst 
    inst_term_atom_vars 
    t_dom
  defines
  semantics (infix "\<Turnstile>" 55) = formula_semantics
  and
  entailment (infix "\<TTurnstile>" 55) = formula_entailment
  and
  free_vars = free_vars
  and
  bound_vars = bound_vars
  by (unfold_locales, auto simp: ia_subst_all)

context ClosedWorld
begin
  (* A lot of these proofs rely on implicit assumptions on the type relationship
    and substitution function. It might be a good idea to abstract away from the 
    details and lifts facts into locales using lemmas. On the other hand, we are 
    reasoning about ground terms specifically, so there is currently no need. 
    Arguments:
    + substitution is a syntactic operation and we are reasoning about semantics
    - the semantics of ground terms are inherently tied to their syntax
    ? we cannot predict every possible change that we might make in the future and 
      can save some effort right now
  *)

  text \<open>It is basic, if it only contains atoms\<close>
  definition "wm_basic M \<equiv> \<forall>a\<in>(M::world_model). is_predAtom a"
  
  text \<open>A valuation extracted from the atoms of the world model\<close>
  definition valuation :: "world_model \<Rightarrow> inst_term atom valuation"
    where "valuation M \<equiv> \<lambda>(predAtm p xs) \<Rightarrow> Atom (predAtm p xs) \<in> M | Eq a b \<Rightarrow> a=b"

  value "\<lambda>(predAtm p xs) \<Rightarrow> Atom (predAtm p xs) \<in> M | Eq a b \<Rightarrow> a=b"

  text \<open>Augment a world model by adding negated versions of all atoms
    not contained in it, as well as interpretations of equality.\<close>
  definition close_world :: "world_model \<Rightarrow> world_model" where "close_world M =
    M \<union> {\<^bold>\<not>(Atom (predAtm p as)) | p as. Atom (predAtm p as) \<notin> M}
    \<union> {Atom (Eq a a) | a. True} \<union> {\<^bold>\<not>(Atom (Eq a b)) | a b. a\<noteq>b}"

  definition "close_neg M \<equiv> M \<union> {\<^bold>\<not>(Atom a) | a. Atom a \<notin> M}"
  lemma "wm_basic M \<Longrightarrow> close_world M = close_neg (M \<union> {Atom (Eq a a) | a. True})"
    unfolding close_world_def close_neg_def wm_basic_def
    apply clarsimp
    apply (auto 0 3)[1] (* no blast 0 but instead more general solver 3 in more depth *)
    by (metis atom.exhaust)

  abbreviation cw_entailment::"world_model \<Rightarrow> inst_formula \<Rightarrow> bool" 
      (infix "\<^sup>c\<TTurnstile>\<^sub>=" 53) where
    "M \<^sup>c\<TTurnstile>\<^sub>= \<phi> \<equiv> close_world M \<TTurnstile> \<phi>"

  (* the closed-world assumption refers to the closure of the set
    of true atoms by adding the negation of every non-contained atom and equality and inequality *)
  lemma
    close_world_extensive: "M \<subseteq> close_world M" and
    close_world_idem[simp]: "close_world (close_world M) = close_world M"
    by (auto simp: close_world_def)

  lemma in_close_world_conv:
    "\<phi> \<in> close_world M \<longleftrightarrow> (
        \<phi>\<in>M
      \<or> (\<exists>p as. \<phi>=\<^bold>\<not>(Atom (predAtm p as)) \<and> Atom (predAtm p as)\<notin>M)
      \<or> (\<exists>a. \<phi>=Atom (Eq a a))
      \<or> (\<exists>a b. \<phi>=\<^bold>\<not>(Atom (Eq a b)) \<and> a\<noteq>b)
    )"
    by (auto simp: close_world_def)

  find_theorems name: "local*semantics"

  lemma valuation_aux_1:
    fixes M :: world_model and \<phi> :: "inst_formula"
    defines "C \<equiv> close_world M"
    assumes A: "\<forall>\<phi>\<in>C. \<A> \<Turnstile> \<phi>"
    shows "\<A> = valuation M"
    using A unfolding C_def
    apply -
    apply (subst (asm) Ball_def)
    apply (subst (asm) in_close_world_conv)
    apply (auto simp: valuation_def intro!: ext split: atom.split)[1]
    apply (metis formula_semantics.simps(1) formula_semantics.simps(3))
    apply (metis formula_semantics.simps(1) formula_semantics.simps(3))
    by (metis atom.collapse(2) formula_semantics.simps(1) is_predAtm_def)


  (* the valuation is an abstract state, which maps variables to truth-values  *)
  lemma valuation_aux_2:
    assumes "wm_basic M"
    shows "(\<forall>G\<in>close_world M. valuation M \<Turnstile> G)"
    using assms unfolding wm_basic_def
    by (force simp: in_close_world_conv valuation_def elim: is_predAtom.elims)

  lemma val_imp_close_world: "valuation M \<Turnstile> \<phi> \<Longrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<phi>"
    unfolding entailment_def
    using valuation_aux_1 entailment_def formula_entailment_def
    by auto

  lemma close_world_imp_val:
    "wm_basic M \<Longrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<phi> \<Longrightarrow> valuation M \<Turnstile> \<phi>"
    unfolding entailment_def
    using valuation_aux_2 entailment_def formula_entailment_def 
    by auto

  text \<open>Main theorem of this section:
    If a world model \<open>M\<close> contains only atoms, its induced valuation
    satisfies a formula \<open>\<phi>\<close> if and only if the closure of \<open>M\<close> entails \<open>\<phi>\<close>.

    Note that there are no syntactic restrictions on \<open>\<phi>\<close>,
    in particular, \<open>\<phi>\<close> may contain negation.
  \<close>
  theorem valuation_iff_close_world:
    assumes "wm_basic M"
    shows "valuation M \<Turnstile> \<phi> \<longleftrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<phi>"
    using assms val_imp_close_world close_world_imp_val by blast

  subsubsection \<open>Proper Generalization\<close>
  text \<open>Adding negation and equality is a proper generalization of the
    case without negation and equality\<close>
  
  (* STRIPS formulae don't have quantifiers, negation, or equality.
    (except that true in our language is defined as the negation of false) *)
  fun is_STRIPS_fmla :: "('tm atom, 'v , 'ty) formula \<Rightarrow> bool" where
    "is_STRIPS_fmla (Atom (predAtm _ _)) \<longleftrightarrow> True"
  | "is_STRIPS_fmla (\<bottom>) \<longleftrightarrow> True"
  | "is_STRIPS_fmla (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) \<longleftrightarrow> is_STRIPS_fmla \<phi>\<^sub>1 \<and> is_STRIPS_fmla \<phi>\<^sub>2"
  | "is_STRIPS_fmla (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<longleftrightarrow> is_STRIPS_fmla \<phi>\<^sub>1 \<and> is_STRIPS_fmla \<phi>\<^sub>2"
  | "is_STRIPS_fmla (\<^bold>\<not>\<bottom>) \<longleftrightarrow> True"
  | "is_STRIPS_fmla _ \<longleftrightarrow> False"
  
  lemma aux1: "\<lbrakk>wm_basic M; is_STRIPS_fmla \<phi>; valuation M \<Turnstile> \<phi>; \<forall>G\<in>M. \<A> \<Turnstile> G\<rbrakk> \<Longrightarrow> \<A> \<Turnstile> \<phi>"
    apply(induction \<phi> rule: is_STRIPS_fmla.induct)
    by (auto simp: valuation_def)
  (* If some valuation entails every formula in M, then it must entail anything that the valuation of M entails *)
  
  lemma aux2: "\<lbrakk>wm_basic M; is_STRIPS_fmla \<phi>; \<forall>\<A>. (\<forall>G\<in>M. \<A> \<Turnstile> G) \<longrightarrow> \<A> \<Turnstile> \<phi>\<rbrakk> \<Longrightarrow> valuation M \<Turnstile> \<phi>"
    apply(induction \<phi> rule: is_STRIPS_fmla.induct)
               apply simp_all
    apply (metis in_close_world_conv valuation_aux_2)
    using in_close_world_conv valuation_aux_2 apply blast
    using in_close_world_conv valuation_aux_2 by auto
  
  lemma valuation_iff_STRIPS:
    assumes "wm_basic M"
    assumes "is_STRIPS_fmla \<phi>"
    shows "valuation M \<Turnstile> \<phi> \<longleftrightarrow> M \<TTurnstile> \<phi>"
  proof -
    have aux1: "\<And>\<A>. \<lbrakk>valuation M \<Turnstile> \<phi>; \<forall>G\<in>M. \<A> \<Turnstile> G\<rbrakk> \<Longrightarrow> \<A> \<Turnstile> \<phi>"
      using assms apply(induction \<phi> rule: is_STRIPS_fmla.induct)
      by (auto simp: valuation_def)
    have aux2: "\<lbrakk>\<forall>\<A>. (\<forall>G\<in>M. \<A> \<Turnstile> G) \<longrightarrow> \<A> \<Turnstile> \<phi>\<rbrakk> \<Longrightarrow> valuation M \<Turnstile> \<phi>"
      using assms
      apply(induction \<phi> rule: is_STRIPS_fmla.induct)
      apply simp_all
      apply (metis in_close_world_conv valuation_aux_2)
      using in_close_world_conv valuation_aux_2 apply blast
      using in_close_world_conv valuation_aux_2 by auto
    show ?thesis          
      using entailment_def formula_entailment_def
      by (auto intro: aux1 aux2)
  qed
  
  text \<open>Our extension to negation and equality is a proper generalization of the
    standard STRIPS semantics for formula without negation and equality\<close>
  theorem proper_STRIPS_generalization:
    "\<lbrakk>wm_basic M; is_STRIPS_fmla \<phi>\<rbrakk> \<Longrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<phi> \<longleftrightarrow> M \<TTurnstile> \<phi>"
    by (simp add: valuation_iff_close_world[symmetric] valuation_iff_STRIPS)
  
end

subsection \<open>Well-Formedness of PDDL\<close>



(* Well-formedness *)

(*
  Compute signature: predicate/arity
  Check that all atoms (schemas and facts) satisfy signature

  for action:
    Check that used parameters \<subseteq> declared parameters

  for init/goal: Check that facts only use declared objects
*)



lemma stav_alt: "schematic_term_atom_vars x = \<Union> (schematic_term_vars ` ent x)" 
  unfolding schematic_term_atom_vars_def by (simp add: atom.set_map) 

lemma itav_alt: "inst_term_atom_vars x = \<Union> (inst_term_vars ` ent x)" 
  unfolding inst_term_atom_vars_def by (simp add: atom.set_map) 

lemma itav_empty: "inst_term_atom_vars x = {} \<longleftrightarrow> (\<forall>e \<in> ent x. inst_term_vars e = {})"
  using itav_alt by auto

lemma itavm_alt: "inst_term_atom_vars (map_atom f x) = \<Union> ((inst_term_vars o f) ` ent x)"
  unfolding inst_term_atom_vars_def by (simp add: atom.map_comp atom.set_map)

fun ty_term::"(variable \<Rightarrow> type option) \<Rightarrow> (object \<Rightarrow> type option) \<Rightarrow> term \<Rightarrow> type option" where
  "ty_term varT objT (term.VAR v) = varT v"
| "ty_term varT objT (term.CONST c) = objT c"

definition upd_te::"(term \<Rightarrow> type option) \<Rightarrow> variable \<Rightarrow> type \<Rightarrow> term \<Rightarrow> type option" where
"upd_te te var ty \<equiv> 
  \<lambda>(term.VAR v) \<Rightarrow> (if (v = var) then Some ty else te (term.VAR v)) |
  (term.CONST c) \<Rightarrow> te (term.CONST c)"

lemma ty_term_upd: "upd_te (ty_term Q R) v t = ty_term (Q(v\<mapsto>t)) R"
  unfolding upd_te_def by (auto split: term.split)

find_theorems name: "ty_term"

lemma ty_term_mono: "varT \<subseteq>\<^sub>m varT' \<Longrightarrow> objT \<subseteq>\<^sub>m objT' \<Longrightarrow>
  ty_term varT objT \<subseteq>\<^sub>m ty_term varT' objT'"
  apply (rule map_leI)
  subgoal for x v
    apply (cases x)
    apply (auto dest: map_leD)
    done
  done

locale ast_domain = ClosedWorld "type_env D" 
  for D :: ast_domain +
  fixes t :: type_env
  defines "t \<equiv> type_env D"
begin

(* having to re-declare syntax is weird *)
notation entailment (infix "\<TTurnstile>" 55)
notation semantics (infix "\<Turnstile>" 55)
notation cw_entailment (infix "\<^sup>c\<TTurnstile>\<^sub>=" 55)


  text \<open>The signature is a partial function that maps the predicates
    of the domain to lists of argument types.\<close>
  definition sig :: "predicate \<rightharpoonup> type list" where
    "sig \<equiv> map_of (map (\<lambda>PredDecl p n \<Rightarrow> (p,n)) (predicates D))"

type_synonym ('ent) ty_ent = "'ent \<rightharpoonup> type"

  text \<open>For the next few definitions, we fix a partial function that maps
    a polymorphic entity type @{typ "'e"} to types. An entity can be
    instantiated by variables or objects later.\<close>
  context
    fixes ty_ent :: "'ent ty_ent"  \<comment> \<open>Entity's type, None if invalid\<close>
begin

    text \<open>Checks whether an entity has a given type\<close>
    definition is_of_type :: "'ent \<Rightarrow> type \<Rightarrow> bool" where
      "is_of_type v T \<longleftrightarrow> (
        case ty_ent v of
          Some vT \<Rightarrow> of_type vT T
        | None \<Rightarrow> False)"

    fun wf_pred_atom :: "predicate \<times> 'ent list \<Rightarrow> bool" where
      "wf_pred_atom (p,vs) \<longleftrightarrow> (
        case sig p of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 is_of_type vs Ts)"

    text \<open>Predicate-atoms are well-formed if their arguments match the
      signature, equalities are well-formed if the arguments are valid
      objects (have a type).

      TODO: We could check that types may actually overlap
    \<close>
    fun wf_atom :: "'ent atom \<Rightarrow> bool" where
      "wf_atom (predAtm p vs) \<longleftrightarrow> wf_pred_atom (p,vs)"
    | "wf_atom (Eq a b) \<longleftrightarrow> ty_ent a \<noteq> None \<and> ty_ent b \<noteq> None"
  end \<comment> \<open>Context fixing \<open>ty_ent\<close>\<close>

  context
    fixes upd :: "'ent ty_ent \<Rightarrow> 'var \<Rightarrow> 'type \<Rightarrow> 'ent ty_ent"
  begin
    text \<open>A formula is well-formed if it consists of valid atoms,
      and does not contain negations, except for the encoding \<open>\<^bold>\<not>\<bottom>\<close> of true.
      Ignore this
    \<close>

    fun wf_fmla :: "'ent ty_ent \<Rightarrow> ('ent atom, 'var, 'type) formula \<Rightarrow> bool" where
      "wf_fmla te (Atom a) \<longleftrightarrow> wf_atom te a"
    | "wf_fmla te (\<bottom>) \<longleftrightarrow> True"
    | "wf_fmla te (\<phi>1 \<^bold>\<and> \<phi>2) \<longleftrightarrow> (wf_fmla te \<phi>1 \<and> wf_fmla te \<phi>2)"
    | "wf_fmla te (\<phi>1 \<^bold>\<or> \<phi>2) \<longleftrightarrow> (wf_fmla te \<phi>1 \<and> wf_fmla te \<phi>2)"
    | "wf_fmla te (\<^bold>\<not>\<phi>) \<longleftrightarrow> wf_fmla te \<phi>"
    | "wf_fmla te (\<phi>1 \<^bold>\<rightarrow> \<phi>2) \<longleftrightarrow> (wf_fmla te \<phi>1 \<and> wf_fmla te \<phi>2)"
    | "wf_fmla te (\<^bold>\<forall>\<^sub>\<tau> v. \<phi>) \<longleftrightarrow> (wf_fmla (upd te v \<tau>) \<phi>)"
    | "wf_fmla te (\<^bold>\<exists>\<^sub>\<tau> v. \<phi>) \<longleftrightarrow> (wf_fmla (upd te v \<tau>) \<phi>)" 

    (* When considering the well-typedness of formulae, when variables 
       are bound, we update the type. *)

    (* this no longer holds *)
    (* lemma "wf_fmla \<phi> = (\<forall>a\<in>formula.atoms \<phi>. wf_atom a)"
      by (induction \<phi>) auto *)

    (*lemma wf_fmla_add_simps[simp]: "wf_fmla (\<^bold>\<not>\<phi>) \<longleftrightarrow> \<phi>=\<bottom>"
      by (cases \<phi>) auto*)


    text \<open>Special case for a well-formed atomic predicate formula\<close>
    fun wf_fmla_atom where
      "wf_fmla_atom te (Atom (predAtm a vs)) \<longleftrightarrow> wf_pred_atom te (a,vs)"
    | "wf_fmla_atom _ _ \<longleftrightarrow> False"

    (* same as the above *)
    lemma wf_fmla_atom_alt: "wf_fmla_atom te \<phi> \<longleftrightarrow> is_predAtom \<phi> \<and> wf_fmla te \<phi>"
      by (cases "(te, \<phi>)" rule: wf_fmla_atom.cases) auto

    thm wf_fmla_atom.cases
    text \<open>An effect is well-formed if the added and removed formulas
      are atomic\<close>
    fun wf_effect where
      "wf_effect te (Effect a d) \<longleftrightarrow>
          (\<forall>ae\<in>set a. wf_fmla_atom te ae)
        \<and> (\<forall>de\<in>set d. wf_fmla_atom te de)"

  end \<comment> \<open>context fixing the update function for ty_ent\<close>

  definition constT :: "object \<rightharpoonup> type" where
    "constT \<equiv> map_of (consts t)"

  text \<open>An action schema is well-formed if the parameter names are distinct,
    and the precondition and effect is well-formed wrt.\ the parameters.
  \<close>
  fun wf_action_schema :: "ast_action_schema \<Rightarrow> bool" where
    "wf_action_schema (Action_Schema n params pre eff) \<longleftrightarrow> (
      let
        tyt = ty_term (map_of params) constT
      in
        distinct (map fst params)
      \<and> wf_fmla upd_te tyt pre
      \<and> wf_effect tyt eff)"
             
  text \<open>A type is well-formed if it consists only of declared primitive types,
     and the type object.\<close>
  fun wf_type where
    "wf_type (Either Ts) \<longleftrightarrow> set Ts \<subseteq> insert ''object'' (fst`set (types t))"

  text \<open>A predicate is well-formed if its argument types are well-formed.\<close>
  fun wf_predicate_decl where
    "wf_predicate_decl (PredDecl p Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. wf_type T)"

  text \<open>The types declaration is well-formed, if all supertypes are declared types (or object)\<close>
  definition "wf_types \<equiv> snd`set (types t) \<subseteq> insert ''object'' (fst`set (types t))"

  text \<open>A domain is well-formed if
    \<^item> there are no duplicate declared predicate names,
    \<^item> all declared predicates are well-formed,
    \<^item> there are no duplicate action names,
    \<^item> and all declared actions are well-formed
    \<close>
  definition wf_domain :: "bool" where
    "wf_domain \<equiv>
      wf_types
    \<and> distinct (map (predicate_decl.pred) (predicates D))
    \<and> (\<forall>p\<in>set (predicates D). wf_predicate_decl p)
    \<and> distinct (map fst (consts t))
    \<and> (\<forall>(n,T)\<in>set (consts t). wf_type T)
    \<and> distinct (map ast_action_schema.name (actions D))
    \<and> (\<forall>a\<in>set (actions D). wf_action_schema a)
    "

end \<comment> \<open>locale \<open>ast_domain\<close>\<close>


subsection \<open>STRIPS Semantics\<close>

text \<open>For this section, we fix a domain \<open>D\<close>, using Isabelle's
  locale mechanism.\<close>
context ast_domain
begin

  text \<open>It seems to be agreed upon that, in case of a contradictory effect,
    addition overrides deletion. We model this behaviour by first executing
    the deletions, and then the additions.\<close>
  fun apply_effect :: "inst_effect \<Rightarrow> world_model \<Rightarrow> world_model"
  where
     "apply_effect (Effect a d) s = (s - set d) \<union> (set a)"

  text \<open>Execute a ground action\<close>
  definition execute_inst_action :: "inst_action \<Rightarrow> world_model \<Rightarrow> world_model"
  where
    "execute_inst_action a M = apply_effect (effect a) M"


  text \<open>Predicate to model that the given list of action instances is
    executable, and transforms an initial world model \<open>M\<close> into a final
    model \<open>M'\<close>.

    Note that this definition over the list structure is more convenient in HOL
    than to explicitly define an indexed sequence \<open>M\<^sub>0\<dots>M\<^sub>N\<close> of intermediate world
     models, as done in [Lif87].
  \<close>

  fun inst_action_path
    :: "world_model \<Rightarrow> inst_action list \<Rightarrow> world_model \<Rightarrow> bool"
  where
    "inst_action_path M [] M' = (M = M')"
  | "inst_action_path M (\<alpha>#\<alpha>s) M' = (M \<^sup>c\<TTurnstile>\<^sub>= precondition \<alpha>
    \<and> inst_action_path (execute_inst_action \<alpha> M) \<alpha>s M')"

  text \<open>Function equations as presented in paper,
    with inlined @{const execute_inst_action}.\<close>
  lemma inst_action_path_in_paper:
    "inst_action_path M [] M' \<longleftrightarrow> (M = M')"
    "inst_action_path M (\<alpha>#\<alpha>s) M' \<longleftrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= precondition \<alpha>
    \<and> (inst_action_path (apply_effect (effect \<alpha>) M) \<alpha>s M')"
    by (auto simp: execute_inst_action_def)

  thm inst_action_path_in_paper

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>


fun ty_inst_term::"(variable \<Rightarrow> type option) \<Rightarrow> (object \<Rightarrow> type option) \<Rightarrow> inst_term \<Rightarrow> type option" where
  "ty_inst_term varT objT (inst_term.VAR v) = varT v"
| "ty_inst_term varT objT (inst_term.OBJ obj) = objT obj"

definition upd_inst_te::"(inst_term \<Rightarrow> type option) \<Rightarrow> variable \<Rightarrow> type \<Rightarrow> inst_term \<Rightarrow> type option" where
"upd_inst_te te var ty \<equiv> 
  \<lambda>(inst_term.VAR v) \<Rightarrow> (if (v = var) then Some ty else te (inst_term.VAR v)) |
  (inst_term.OBJ c) \<Rightarrow> te (inst_term.OBJ c)"

lemma ty_inst_term_upd: "upd_inst_te (ty_inst_term Q R) v t = ty_inst_term (Q(v \<mapsto> t)) R"
  unfolding upd_inst_te_def
  by (auto split: inst_term.splits)

find_theorems name: "ty_term"

lemma ty_inst_term_mono: "varT \<subseteq>\<^sub>m varT' \<Longrightarrow> objT \<subseteq>\<^sub>m objT' \<Longrightarrow>
  ty_inst_term varT objT \<subseteq>\<^sub>m ty_inst_term varT' objT'"
  apply (rule map_leI)
  subgoal for x v
    apply (cases x)
    apply (auto dest: map_leD)
    done
  done

text \<open>We fix a problem, and also include the definitions for the domain
  of this problem.\<close>
locale ast_problem = ast_domain "domain P"
  for P :: ast_problem +
  defines "t \<equiv> type_env (domain P)" (* for clarity *)
begin
  text \<open>We refer to the problem domain as \<open>D\<close>\<close>
  abbreviation "D \<equiv> ast_problem.domain P"

  (* constants are from the domain, objects are from the problem *)
  definition objT :: "object \<rightharpoonup> type" where
    "objT \<equiv> map_of (objects P) ++ constT"

  lemma objT_alt: "objT = map_of (consts t @ objects P)"
    unfolding objT_def constT_def
    apply (clarsimp)
    done

  definition wf_fact :: "fact \<Rightarrow> bool" where
    "wf_fact = wf_pred_atom (ty_inst_term (\<lambda>_. None) objT)"
  (* TODO: what is a fact? My assumption is that they are not quantified. *)

  text \<open>This definition is needed for well-formedness of the initial model,
    and forward-references to the concept of world model.
  \<close>
  (* What makes a world-model well-formed? Since the initial state is essentially
      equivalent to the effect of a non-action, it being well-formed means, that it
      is unquantified. *)
definition wf_world_model::
"inst_formula set \<Rightarrow> bool" where
    "wf_world_model M = (\<forall>f\<in>M. wf_fmla_atom (ty_inst_term (\<lambda>_. None) objT) f)"

  (*Note: current semantics assigns each object a unique type *)
  definition wf_problem where
    "wf_problem \<equiv>
      wf_domain
    \<and> distinct (map fst (objects P) @ map fst (consts t))
    \<and> (\<forall>(n,T)\<in>set (objects P). wf_type T)
    \<and> distinct (init P)
    \<and> wf_world_model (set (init P))
    \<and> wf_fmla upd_inst_te (ty_inst_term (\<lambda>_.None) objT) (goal P)
    "

  definition wf_inst_fmla::"inst_formula \<Rightarrow> bool" where
  "wf_inst_fmla f \<equiv> wf_fmla upd_inst_te (ty_inst_term (\<lambda>_. None) objT) f"

  fun wf_inst_fmla_atom::"inst_formula \<Rightarrow> bool" where
    "wf_inst_fmla_atom (Atom (predAtm a vs)) = wf_inst_fmla (Atom (predAtm a vs))"
  | "wf_inst_fmla_atom _ = False"

  fun wf_effect_inst :: "inst_effect \<Rightarrow> bool" where
    "wf_effect_inst (Effect (a) (d))
      \<longleftrightarrow> (\<forall>a\<in>set a \<union> set d. wf_inst_fmla_atom a)"

  text \<open>The following section reasons shows that well-formed instantiated formulae do not have free
        variables and relates wf_inst_fmla to wf_inst_fmla_atom. It also contains a few lemmas proving
        similar results for schematic formulas and terms\<close>

  lemma wf_imp_ent_typed:
    assumes wf: "wf_atom Q a"
    shows "\<forall>e \<in> ent a. Q e \<noteq> None"
  proof (cases a)
    case [simp]: (predAtm p vs)
    have "Q e \<noteq> None" if "e \<in> ent a" for e
    proof -
      from wf obtain Ts where 
        "sig p = Some Ts \<and> list_all2 (is_of_type Q) vs Ts"
        by (cases "sig p") auto
      hence "\<forall>v \<in> set vs. \<exists>T \<in> set Ts. (is_of_type Q) v T"
        by (metis in_set_conv_nth list_all2_conv_all_nth)
      hence "\<forall>e \<in> ent a. \<exists>T. (is_of_type Q) e T" by auto
      with that obtain T where
        "(is_of_type Q) e T" by auto
      thus "Q e \<noteq> None"
        apply (cases "Q e")
        unfolding is_of_type_def
        by auto
    qed
    then show ?thesis by auto
  next
    case (Eq x y)
    thus ?thesis using wf by auto
  qed

  text \<open>The following two lemmas concern the variables present in a schematic atom
        and an instantiated atom\<close>

  lemma wf_schematic_atom_vars: "wf_atom (ty_term Q constT) a \<Longrightarrow> schematic_term_atom_vars a \<subseteq> dom Q"
  proof (rule subsetI)
    fix v
    assume wf: "wf_atom (ty_term Q constT) a"
    assume "v \<in> schematic_term_atom_vars a"
    then obtain e where
      e: "e \<in> ent a" 
      "v \<in> schematic_term_vars e" 
      by (auto simp: stav_alt)
    hence "e = term.VAR v" by (cases e rule: term.exhaust) auto
    moreover
    have "ty_term Q constT e \<noteq> None" using e wf_imp_ent_typed wf by fastforce
    ultimately
    show "v \<in> dom Q" by auto
  qed
  
  lemma wf_inst_atom_vars: "wf_atom (ty_inst_term Q objT) a \<Longrightarrow> inst_term_atom_vars a \<subseteq> dom Q"
  proof (rule subsetI)
    fix v
    assume wf: "wf_atom (ty_inst_term Q objT) a"
    assume "v \<in> inst_term_atom_vars a"
    then obtain e where
      e: "e \<in> ent a" 
      "v \<in> inst_term_vars e" 
      by (auto simp: itav_alt)
    hence "e = inst_term.VAR v" by (cases e rule: inst_term.exhaust) auto
    moreover
    have "ty_inst_term Q objT e \<noteq> None" using e wf_imp_ent_typed wf by fastforce
    ultimately
    show "v \<in> dom Q" by auto
  qed

  text \<open>This section proves that under certain circumstances, namely the type environments assigning
        the same type to the same terms, well-formedness under one type environment implies
        well-formedness under another.\<close>

  lemma list_all2_ty:
    fixes xs Ts
    assumes "\<forall>x \<in> set xs. Q x = R x"
        and "list_all2 (is_of_type Q) xs Ts"
      shows "list_all2 (is_of_type R) xs Ts"
  using assms(2) assms(1)
  proof (induction xs Ts rule: list_all2_induct)
    case Nil
    then show ?case by simp
  next
    case (Cons x t xs ts)
    hence "is_of_type R x t" 
      unfolding is_of_type_def 
      by (auto split: option.splits)
    moreover have "list_all2 (is_of_type R) xs ts" using Cons by auto
    ultimately show ?case by auto
  qed
  
  lemma same_type_imp_wf_eq: 
    assumes same: "\<forall>e \<in> ent a. Q e = R e"
        and wf:   "wf_atom Q a"
      shows "wf_atom R a"
  proof (cases a)
    case [simp]: (predAtm p vs)
    from wf obtain Ts where 
        sig: "sig p = Some Ts" and
        ls: "list_all2 (is_of_type Q) vs Ts"
      by (cases "sig p") auto
    have "\<forall>x \<in> set vs. Q x = R x" using same by auto
    from list_all2_ty[OF this ls]
    show ?thesis using sig by simp
  next
    case [simp]: (Eq x y)
    then show ?thesis using assms by auto
  qed
  
  
  lemma map_le_imp_same_type: 
    assumes le: "Q \<subseteq>\<^sub>m R" 
        and wf: "wf_atom Q a"
    shows "\<forall>e \<in> ent a. Q e = R e"
    using wf_imp_ent_typed[OF wf] map_leD le by fastforce


  lemma wf_atom_mono:
    assumes SS: "tys \<subseteq>\<^sub>m tys'"
    assumes WF: "wf_atom tys a"
    shows "wf_atom tys' a"
    using map_le_imp_same_type[OF SS WF] WF same_type_imp_wf_eq
    by blast

  lemma wf_fmla_atom_mono:
    assumes SS: "tys \<subseteq>\<^sub>m tys'"
    assumes WF: "wf_fmla_atom tys a"
    shows "wf_fmla_atom tys' a"
  proof -
    obtain p vs where
      [simp]: "a = Atom (predAtm p vs)"
      "wf_atom tys (predAtm p vs)"
      using WF
      by (cases "(tys, a)" rule: wf_fmla_atom.cases) auto
    from wf_atom_mono[OF SS this(2)]
    show ?thesis by simp
  qed
  
  lemma wf_inst_atom_mono: 
    assumes le: "Q \<subseteq>\<^sub>m R" 
        and wf: "wf_atom (ty_inst_term Q objT) a"
      shows "wf_atom (ty_inst_term R objT) a"
    using ty_inst_term_mono[OF le map_le_refl[of objT], THEN wf_atom_mono] wf
    by blast

  lemma inst_term_vars_restr_same_type: "\<forall>e \<in> ent a. (ty_inst_term Q objT) e = (ty_inst_term (Q |` (inst_term_atom_vars a)) objT) e"
  proof
    fix e
    assume "e \<in> ent a"
    hence "inst_term_vars e \<subseteq> inst_term_atom_vars a" using itav_alt by blast
    hence "(ty_inst_term (Q |` (inst_term_vars e)) objT) e = (ty_inst_term (Q |` (inst_term_atom_vars a)) objT) e" by (cases e) auto
    moreover
    have "(ty_inst_term Q objT) e = (ty_inst_term (Q |` (inst_term_vars e)) objT) e" by (cases e) auto
    ultimately 
    show "(ty_inst_term Q objT) e = (ty_inst_term (Q |` (inst_term_atom_vars a)) objT) e" by argo
  qed

  lemma wf_atom_restr: 
    assumes wf: "wf_atom (ty_inst_term Q objT) a" 
      shows "wf_atom (ty_inst_term (Q |` (inst_term_atom_vars a)) objT) a"
    using same_type_imp_wf_eq[OF inst_term_vars_restr_same_type wf]
    .

  text \<open>The type environment must contain a type for all free variables in a formula.\<close>
  lemma wf_schematic_fmla_free_vars: "wf_fmla upd_te (ty_term Q constT) \<phi> \<Longrightarrow> sf_free_vars \<phi> \<subseteq> dom Q"
  proof (induction \<phi> arbitrary: Q)
    case (Atom x)
    then show ?case using wf_schematic_atom_vars by simp
  next
    case (Exists t x \<phi>)
    hence "wf_fmla upd_te (ty_term (Q(x \<mapsto> t)) constT) \<phi>" using ty_term_upd by simp
    hence "sf_free_vars \<phi> \<subseteq> dom (Q(x \<mapsto> t))" using Exists.IH by blast
    then show ?case by auto
  next
    case (All t x \<phi>)
    hence "wf_fmla upd_te (ty_term (Q(x \<mapsto> t)) constT) \<phi>" using ty_term_upd by simp
    hence "sf_free_vars \<phi> \<subseteq> dom (Q(x \<mapsto> t))" using All.IH by blast                
    then show ?case by auto
  qed simp_all
  
  lemma wf_inst_fmla_free_vars: "wf_fmla upd_inst_te (ty_inst_term Q objT) \<phi> \<Longrightarrow> free_vars \<phi> \<subseteq> dom Q"
  proof (induction \<phi> arbitrary: Q)
    case (Atom x)
    then show ?case using wf_inst_atom_vars by simp
  next
    case (Exists t x \<phi>)
    hence "wf_fmla upd_inst_te (ty_inst_term (Q(x \<mapsto> t)) objT) \<phi>" using ty_inst_term_upd by simp
    hence "free_vars \<phi> \<subseteq> dom (Q(x \<mapsto> t))" using Exists.IH by blast
    then show ?case by auto
  next
    case (All t x \<phi>)
    hence "wf_fmla upd_inst_te (ty_inst_term (Q(x \<mapsto> t)) objT) \<phi>" using ty_inst_term_upd by simp
    hence "free_vars \<phi> \<subseteq> dom (Q(x \<mapsto> t))" using All.IH by blast                  
    then show ?case by auto
  qed simp_all
  
  lemma wf_fmla_fw: "Q \<subseteq>\<^sub>m R \<Longrightarrow> wf_fmla upd_inst_te (ty_inst_term Q objT) \<phi> 
    \<Longrightarrow> wf_fmla upd_inst_te (ty_inst_term R objT) \<phi>"
  proof (induction \<phi> arbitrary: Q R)
    case (Atom x)
    then show ?case using wf_inst_atom_mono by simp
  next
    case (Exists t x \<phi>)
    then show ?case 
      using Exists.IH[OF map_le_upd[OF \<open>Q \<subseteq>\<^sub>m R\<close>, of x "Some t"]] ty_inst_term_upd
      by fastforce
  next
    case (All t x \<phi>)
    then show ?case 
      using All.IH[OF map_le_upd[OF \<open>Q \<subseteq>\<^sub>m R\<close>, of x "Some t"]] ty_inst_term_upd
      by fastforce
  qed auto
  
  lemma wf_fmla_restr': "wf_fmla upd_inst_te (ty_inst_term Q objT) \<phi> 
    \<Longrightarrow> wf_fmla upd_inst_te (ty_inst_term (Q |` (free_vars \<phi>)) objT) \<phi>"
  proof (induction \<phi> arbitrary: Q)
    case (Atom x)
    then show ?case using wf_atom_restr by simp
  next
    case Bot
    then show ?case by simp
  next
    case (Not \<phi>)
    then show ?case by simp
  next
    case (And \<phi>1 \<phi>2)
    have "free_vars \<phi>1 \<subseteq> free_vars (\<phi>1 \<^bold>\<and> \<phi>2)" by simp
    hence "Q |` free_vars \<phi>1 \<subseteq>\<^sub>m Q |` free_vars (\<phi>1 \<^bold>\<and> \<phi>2)"
      using map_restrict_mono[of "free_vars \<phi>1" _ Q] by blast
    hence "wf_fmla upd_inst_te (ty_inst_term (Q |` free_vars (\<phi>1 \<^bold>\<and> \<phi>2)) objT) \<phi>1"
      using wf_fmla_fw And by fastforce
    moreover
    have "free_vars \<phi>2 \<subseteq> free_vars (\<phi>1 \<^bold>\<and> \<phi>2)" by simp
    hence "Q |` free_vars \<phi>2 \<subseteq>\<^sub>m Q |` free_vars (\<phi>1 \<^bold>\<and> \<phi>2)"
      using map_restrict_mono by blast
    hence "wf_fmla upd_inst_te (ty_inst_term (Q |` free_vars (\<phi>1 \<^bold>\<and> \<phi>2)) objT) \<phi>2"
      using wf_fmla_fw And by fastforce
    ultimately
    show ?case by simp
  next
    case (Or \<phi>1 \<phi>2)
    have "free_vars \<phi>1 \<subseteq> free_vars (\<phi>1 \<^bold>\<or> \<phi>2)" by simp
    hence "Q |` free_vars \<phi>1 \<subseteq>\<^sub>m Q |` free_vars (\<phi>1 \<^bold>\<or> \<phi>2)"
      using map_restrict_mono[of "free_vars \<phi>1" _ Q] by blast
    hence "wf_fmla upd_inst_te (ty_inst_term (Q |` free_vars (\<phi>1 \<^bold>\<or> \<phi>2)) objT) \<phi>1"
      using wf_fmla_fw Or by fastforce
    moreover
    have "free_vars \<phi>2 \<subseteq> free_vars (\<phi>1 \<^bold>\<or> \<phi>2)" by simp
    hence "Q |` free_vars \<phi>2 \<subseteq>\<^sub>m Q |` free_vars (\<phi>1 \<^bold>\<or> \<phi>2)"
      using map_restrict_mono by blast
    hence "wf_fmla upd_inst_te (ty_inst_term (Q |` free_vars (\<phi>1 \<^bold>\<or> \<phi>2)) objT) \<phi>2"
      using wf_fmla_fw Or by fastforce
    ultimately
    show ?case by simp
  next
    case (Imp \<phi>1 \<phi>2)
    have "free_vars \<phi>1 \<subseteq> free_vars (\<phi>1 \<^bold>\<rightarrow> \<phi>2)" by simp
    hence "Q |` free_vars \<phi>1 \<subseteq>\<^sub>m Q |` free_vars (\<phi>1 \<^bold>\<rightarrow> \<phi>2)"
      using map_restrict_mono[of "free_vars \<phi>1" _ Q] by blast
    hence "wf_fmla upd_inst_te (ty_inst_term (Q |` free_vars (\<phi>1 \<^bold>\<rightarrow> \<phi>2)) objT) \<phi>1"
      using wf_fmla_fw Imp by fastforce
    moreover
    have "free_vars \<phi>2 \<subseteq> free_vars (\<phi>1 \<^bold>\<rightarrow> \<phi>2)" by simp
    hence "Q |` free_vars \<phi>2 \<subseteq>\<^sub>m Q |` free_vars (\<phi>1 \<^bold>\<rightarrow> \<phi>2)"
      using map_restrict_mono by blast
    hence "wf_fmla upd_inst_te (ty_inst_term (Q |` free_vars (\<phi>1 \<^bold>\<rightarrow> \<phi>2)) objT) \<phi>2"
      using wf_fmla_fw Imp by fastforce
    ultimately
    show ?case by simp
  next
    case (Exists t x \<phi>)
    hence "wf_fmla upd_inst_te (ty_inst_term (Q(x \<mapsto> t)) objT) \<phi>" using ty_inst_term_upd by simp
    hence 1: "wf_fmla upd_inst_te (ty_inst_term (Q(x \<mapsto> t) |` (free_vars \<phi>)) objT) \<phi>" using Exists.IH by blast
    have "Q (x \<mapsto> t) |` (free_vars \<phi>) \<subseteq>\<^sub>m (Q |` (free_vars (\<^bold>\<exists>\<^sub>t x. \<phi>))) (x \<mapsto> t)"
      unfolding restrict_map_def map_le_def by (cases "x \<in> free_vars \<phi>") auto
    from wf_fmla_fw[OF this] 1
    have "wf_fmla upd_inst_te (ty_inst_term ((Q |` free_vars (\<^bold>\<exists>\<^sub>t x. \<phi>))(x \<mapsto> t)) objT) \<phi>" .
    thus ?case using ty_inst_term_upd by simp
  next
    case (All t x \<phi>)
    hence "wf_fmla upd_inst_te (ty_inst_term (Q(x \<mapsto> t)) objT) \<phi>" using ty_inst_term_upd by simp
    hence 1: "wf_fmla upd_inst_te (ty_inst_term (Q(x \<mapsto> t) |` (free_vars \<phi>)) objT) \<phi>" using All.IH by blast
    have "Q (x \<mapsto> t) |` (free_vars \<phi>) \<subseteq>\<^sub>m (Q |` (free_vars (\<^bold>\<forall>\<^sub>t x. \<phi>))) (x \<mapsto> t)"
      unfolding restrict_map_def map_le_def by (cases "x \<in> free_vars \<phi>") auto
    from wf_fmla_fw[OF this] 1
    have "wf_fmla upd_inst_te (ty_inst_term ((Q |` free_vars (\<^bold>\<forall>\<^sub>t x. \<phi>))(x \<mapsto> t)) objT) \<phi>" .
    thus ?case using ty_inst_term_upd by simp
  qed 
  
  lemma wf_fmla_restr: "wf_fmla upd_inst_te (ty_inst_term Q objT) \<phi> 
    \<longleftrightarrow> wf_fmla upd_inst_te (ty_inst_term (Q |` (free_vars \<phi>)) objT) \<phi>"
    using wf_fmla_restr' wf_fmla_fw map_restrict_less
    by blast
  
  lemma wf_fmla_bw: "Q \<subseteq>\<^sub>m R \<Longrightarrow> free_vars \<phi> \<subseteq> dom Q
    \<Longrightarrow> wf_fmla upd_inst_te (ty_inst_term R objT) \<phi> 
    \<longleftrightarrow> wf_fmla upd_inst_te (ty_inst_term Q objT) \<phi>"
    using wf_fmla_restr[of R] sym[OF wf_fmla_restr[of Q]] map_le_restr
    by metis
  
  lemma wf_inst_fmla_alt_lemma: "Q \<subseteq>\<^sub>m R \<Longrightarrow> wf_fmla upd_inst_te (ty_inst_term Q objT) \<phi> 
    \<longleftrightarrow> wf_fmla upd_inst_te (ty_inst_term R objT) \<phi> \<and> free_vars \<phi> \<subseteq> dom Q"
    using wf_fmla_fw wf_inst_fmla_free_vars wf_fmla_bw 
    by blast
  
  lemma wf_inst_fmla_alt: "wf_inst_fmla \<phi> \<longleftrightarrow> wf_fmla upd_inst_te (ty_inst_term Q objT) \<phi> \<and> free_vars \<phi> = {}"
    unfolding wf_inst_fmla_def
    using wf_inst_fmla_alt_lemma[of "(\<lambda>_. None)"]
    by simp
  
  lemma wf_inst_fmla_atom_corr: "wf_inst_fmla_atom f \<equiv> wf_fmla_atom (ty_inst_term (\<lambda>_. None) objT) f \<and> wf_inst_fmla f"
    apply (induction f)
    subgoal for x
      apply (cases x)
       apply auto[1]
      subgoal for p vs
        unfolding wf_inst_fmla_def
        by (auto split: option.splits)
      by auto
    by auto

  lemma wf_fmla_atom_is_wf_fmla: "wf_fmla_atom (ty_inst_term (\<lambda>_. None) objT) x \<Longrightarrow> wf_fmla upd_inst_te (ty_inst_term (\<lambda>_. None) objT) x"
    using wf_fmla_atom_alt by auto

  lemma wf_effect_inst_alt: 
  "wf_effect_inst eff = wf_effect (ty_inst_term (\<lambda>_. None) objT) eff"
    apply (cases eff)
    subgoal for add del
      apply (auto simp: wf_inst_fmla_atom_corr)[1]
      unfolding wf_inst_fmla_def
      by (auto intro: wf_fmla_atom_is_wf_fmla)
    done


end \<comment> \<open>locale \<open>ast_problem\<close>\<close>

thm ast_problem.objT_alt

text \<open>Locale to express a well-formed domain\<close>
locale wf_ast_domain = ast_domain +
  assumes wf_domain: wf_domain

print_locale ast_problem

text \<open>Locale to express a well-formed problem\<close>
locale wf_ast_problem = ast_problem t P for t P +
  assumes wf_problem: wf_problem
begin
  sublocale wf_ast_domain "domain P"
    apply unfold_locales
    using wf_problem
    unfolding wf_problem_def by simp

end \<comment> \<open>locale \<open>wf_ast_problem\<close>\<close>

subsection \<open>PDDL Semantics\<close>

(* Semantics *)

(*  To apply plan_action:
    find action schema, instantiate, check precond, apply effect
*)



context ast_domain begin

  definition resolve_action_schema :: "name \<rightharpoonup> ast_action_schema" where
    "resolve_action_schema n = index_by ast_action_schema.name (actions D) n"

  fun inst_var::"(variable \<Rightarrow> inst_term) \<Rightarrow> term \<Rightarrow> inst_term" where
    "inst_var psubst (term.VAR x) = psubst x" 
  | "inst_var psubst (term.CONST obj) = inst_term.OBJ obj"

  fun cap_avoid_map::"(term \<Rightarrow> inst_term) \<Rightarrow> schematic_formula \<Rightarrow> inst_formula"
    where
    "cap_avoid_map f (Atom x) = Atom (map_atom f x)"
  | "cap_avoid_map f \<bottom> = \<bottom>"
  | "cap_avoid_map f (\<^bold>\<not>\<phi>) = \<^bold>\<not> (cap_avoid_map f \<phi>)"
  | "cap_avoid_map f (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = cap_avoid_map f \<phi>\<^sub>1 \<^bold>\<and> cap_avoid_map f \<phi>\<^sub>2"
  | "cap_avoid_map f (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = cap_avoid_map f \<phi>\<^sub>1 \<^bold>\<or> cap_avoid_map f \<phi>\<^sub>2"
  | "cap_avoid_map f (\<phi>\<^sub>1 \<^bold>\<rightarrow> \<phi>\<^sub>2) = cap_avoid_map f \<phi>\<^sub>1 \<^bold>\<rightarrow> cap_avoid_map f \<phi>\<^sub>2"
  | "cap_avoid_map f (\<^bold>\<exists>\<^sub>T x. \<phi>\<^sub>1) = (\<^bold>\<exists>\<^sub>T x. (cap_avoid_map (f(term.VAR x := inst_term.VAR x)) \<phi>\<^sub>1))"
  | "cap_avoid_map f (\<^bold>\<forall>\<^sub>T x. \<phi>\<^sub>1) = (\<^bold>\<forall>\<^sub>T x. (cap_avoid_map (f(term.VAR x := inst_term.VAR x)) \<phi>\<^sub>1))"


  fun instantiate_action_schema
    :: "ast_action_schema \<Rightarrow> object list \<Rightarrow> inst_action"
  where
    "instantiate_action_schema (Action_Schema n params pre (Effect add del)) args = (let
        tsubst = inst_var (the o (map_of (zip (map fst params) (map inst_term.OBJ args))));
        pre_inst = cap_avoid_map tsubst pre;
        eff_inst = Effect (map (cap_avoid_map tsubst) add) (map (cap_avoid_map tsubst) del)
      in
        Inst_Action pre_inst eff_inst
      )"


lemma map_atom_maintains_vars'':
    assumes v: "v \<in> schematic_term_atom_vars x"
        and a: "f (term.VAR v) = inst_term.VAR v"
      shows "v \<in> inst_term_atom_vars (map_atom f x)"
  proof -
    from v 
    have "\<exists>e \<in> ent x. v \<in> schematic_term_vars e" using stav_alt by simp
    then obtain e where
      e: "e \<in> ent x" 
      "v \<in> schematic_term_vars e" 
      by auto
    hence "e = term.VAR v"by (cases e rule: term.exhaust) auto
    hence "f e = inst_term.VAR v" using a v by auto
    hence "(inst_term_vars o f) e = {v}" by auto
    with e
    show "v \<in> inst_term_atom_vars (map_atom f x)" using itavm_alt by blast
  qed

  lemma map_atom_maintains_vars':
    assumes v: "v \<in> schematic_term_atom_vars x"
        and a: "\<exists>v'. f (term.VAR v) = inst_term.VAR v'"
        and var_inst: "(\<forall>v \<in> schematic_term_atom_vars x. 
             f (term.VAR v) = inst_term.VAR v 
            \<or> (\<exists>obj. f(term.VAR v) = inst_term.OBJ obj))"
      shows "v \<in> inst_term_atom_vars (map_atom f x)"
  proof -
    from a var_inst v
    have "f (term.VAR v) = inst_term.VAR v" by fastforce
    with v
    show ?thesis using map_atom_maintains_vars'' by simp
  qed
  
  lemma map_atom_maintains_vars:
    fixes v
    assumes a: "\<exists>v'. f (term.VAR v) = inst_term.VAR v'"
        and var_inst: "(\<forall>v \<in> schematic_term_atom_vars x. 
             f (term.VAR v) = inst_term.VAR v 
            \<or> (\<exists>obj. f(term.VAR v) = inst_term.OBJ obj))"
        and obj_inst: "\<forall>c. f (term.CONST c) = inst_term.OBJ c" 
      shows "v \<in> schematic_term_atom_vars x \<longleftrightarrow> v \<in> inst_term_atom_vars (map_atom f x)"
    using assms
  proof -
    { assume "v \<in> inst_term_atom_vars (map_atom f x)"
      hence "\<exists>e \<in> ent x. v \<in> inst_term_vars (f e)" using itavm_alt by fastforce
      then obtain e where
        e: "e \<in> ent x"
        "v \<in> inst_term_vars (f e)"
        by auto
      hence "f e = inst_term.VAR v" by (cases "f e") auto
      then obtain v' where
        v': "e = term.VAR v'" 
        using obj_inst by (cases e) auto
      moreover
      hence "v' \<in> schematic_term_atom_vars x" using e stav_alt itavm_alt by fastforce
      moreover
      hence "e = term.VAR v" using obj_inst var_inst e v' by fastforce
      ultimately
      have "v \<in> schematic_term_atom_vars x"  by auto
    }
    with map_atom_maintains_vars' a var_inst
    show "v \<in> schematic_term_atom_vars x \<longleftrightarrow> v \<in> inst_term_atom_vars (map_atom f x)" by blast
  qed 

  lemma cam_avoids_capture:
    assumes "v \<in> sf_free_vars \<phi>"
        and "f (term.VAR v) = inst_term.VAR v"
    shows "v \<in> free_vars (cap_avoid_map f \<phi>)"
    using assms map_atom_maintains_vars''
    by (induction \<phi> arbitrary: f) (simp, auto)
  
  lemma cam_leaves_bound: 
    assumes "v \<in> sf_bound_vars \<phi>"
    shows "v \<in> bound_vars (cap_avoid_map f \<phi>)"
    using assms
    apply (induction \<phi> arbitrary: f)
           apply auto[6]
     apply (cases "v \<in> sf_bound_vars \<phi>")
    using cam_avoids_capture 
    by auto
  
  lemma free_is_cam_free:
    assumes "\<exists>v'. f (term.VAR v) = inst_term.VAR v'"
        and "\<forall>v \<in> sf_free_vars \<phi>. f (term.VAR v) = inst_term.VAR v 
            \<or> (\<exists>obj. f(term.VAR v) = inst_term.OBJ obj)"
        and "\<forall>c. f (term.CONST c) = inst_term.OBJ c" 
      shows "v \<in> sf_free_vars \<phi> \<longleftrightarrow> v \<in> free_vars (cap_avoid_map f \<phi>)"
    using assms 
    apply (induction \<phi> arbitrary: f)
    subgoal 1 using map_atom_maintains_vars by force
    apply auto[5]
    subgoal for t x
      by (cases "x = v") auto
    subgoal for t x
      by (cases "x = v") auto
    done
  
  lemma bound_is_cam_bound:
    assumes var_inst: "\<forall>v \<in> sf_free_vars \<phi>. f (term.VAR v) = inst_term.VAR v 
            \<or> (\<exists>obj. f(term.VAR v) = inst_term.OBJ obj)"
        and obj_inst: "\<And>c. f (term.CONST c) = inst_term.OBJ c" 
    shows "v \<in> sf_bound_vars \<phi> \<longleftrightarrow> v \<in> bound_vars (cap_avoid_map f \<phi>)"
    using assms
  proof (induction \<phi> arbitrary: f)
    case (Exists t x \<phi>)
    have "v \<in> sf_bound_vars (\<^bold>\<exists>\<^sub>t x. \<phi>)" if a: "v \<in> bound_vars (cap_avoid_map f (\<^bold>\<exists>\<^sub>t x. \<phi>))"
    proof (cases "v \<in> bound_vars (cap_avoid_map (f(term.VAR x := inst_term.VAR x)) \<phi>)")
      case True
      then show ?thesis using Exists by auto
    next
      case False
      with a
      have "v \<in> free_vars (cap_avoid_map (f(term.VAR x := inst_term.VAR x)) \<phi>) \<and> x = v" by auto
      then show ?thesis using free_is_cam_free[of "(f(term.VAR x := inst_term.VAR x))"] Exists by fastforce
    qed
    thus ?case using cam_leaves_bound by blast
  next
    case (All t x \<phi>)
    have "v \<in> sf_bound_vars (\<^bold>\<forall>\<^sub>t x. \<phi>)" if a: "v \<in> bound_vars (cap_avoid_map f (\<^bold>\<forall>\<^sub>t x. \<phi>))"
    proof (cases "v \<in> bound_vars (cap_avoid_map (f(term.VAR x := inst_term.VAR x)) \<phi>)")
      case True
      then show ?thesis using All by auto
    next
      case False
      with a
      have "v \<in> free_vars (cap_avoid_map (f(term.VAR x := inst_term.VAR x)) \<phi>) \<and> x = v" by auto
      then show ?thesis using free_is_cam_free[of "(f(term.VAR x := inst_term.VAR x))"] All by fastforce
    qed
    thus ?case using cam_leaves_bound by blast
  qed auto

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>


context ast_problem begin

  text \<open>Initial model\<close>
  definition I :: "world_model" where
    "I \<equiv> set (init P)"

  text \<open>Resolve a plan action and instantiate the referenced action schema.\<close>
  fun resolve_instantiate :: "plan_action \<Rightarrow> inst_action" where
    "resolve_instantiate (PAction n args) =
      instantiate_action_schema
        (the (resolve_action_schema n))
        args"

  text \<open>Check whether object has specified type\<close>
  definition "is_obj_of_type n T \<equiv> case objT n of
    None \<Rightarrow> False
  | Some oT \<Rightarrow> of_type oT T"

  text \<open>We can also use the generic \<open>is_of_type\<close> function.\<close>
  lemma is_obj_of_type_alt: "is_obj_of_type = is_of_type objT"
    apply (intro ext)
    unfolding is_obj_of_type_def is_of_type_def by auto


  text \<open>HOL encoding of matching an action's formal parameters against an
    argument list.
    The parameters of the action are encoded as a list of \<open>name\<times>type\<close> pairs,
    such that we map it to a list of types first. Then, the list
    relator @{const list_all2} checks that arguments and types have the same
    length, and each matching pair of argument and type
    satisfies the predicate @{const is_obj_of_type}.
  \<close>
  definition "action_params_match a args
    \<equiv> list_all2 is_obj_of_type args (map snd (parameters a))"

  text \<open>At this point, we can define well-formedness of a plan action:
    The action must refer to a declared action schema, the arguments must
    be compatible with the formal parameters' types.
  \<close>
 (* Objects are valid and match parameter types *)
  fun wf_plan_action :: "plan_action \<Rightarrow> bool" where
    "wf_plan_action (PAction n args) = (
      case resolve_action_schema n of
        None \<Rightarrow> False
      | Some a \<Rightarrow>
          action_params_match a args
        \<and> wf_effect_inst (effect (instantiate_action_schema a args))
        )"
  text \<open>
    TODO: The second conjunct is redundant, as instantiating a well formed
      action with valid objects yields a valid effect.
  \<close>



  text \<open>A sequence of plan actions form a path, if they are well-formed and
    their instantiations form a path.\<close>
  definition plan_action_path
    :: "world_model \<Rightarrow> plan_action list \<Rightarrow> world_model \<Rightarrow> bool"
  where
    "plan_action_path M \<pi>s M' =
        ((\<forall>\<pi> \<in> set \<pi>s. wf_plan_action \<pi>)
      \<and> inst_action_path M (map resolve_instantiate \<pi>s) M')"
                                              
  text \<open>A plan is valid wrt.\ a given initial model, if it forms a path to a
    goal model \<close>
  definition valid_plan_from :: "world_model \<Rightarrow> plan \<Rightarrow> bool" where
    "valid_plan_from M \<pi>s = (\<exists>M'. plan_action_path M \<pi>s M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= (goal P))"

  (* Implementation note: resolve and instantiate already done inside
      enabledness check, redundancy! *)

  text \<open>Finally, a plan is valid if it is valid wrt.\ the initial world
    model @{const I}\<close>
  definition valid_plan :: "plan \<Rightarrow> bool"
    where "valid_plan \<equiv> valid_plan_from I"

  text \<open>Concise definition used in paper:\<close>
  lemma "valid_plan \<pi>s \<equiv> \<exists>M'. plan_action_path I \<pi>s M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= (goal P)"
    unfolding valid_plan_def valid_plan_from_def by auto


end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>



subsection \<open>Preservation of Well-Formedness\<close>

subsubsection \<open>Well-Formed Action Instances\<close>
text \<open>The goal of this section is to establish that well-formedness of
  world models is preserved by execution of well-formed plan actions.
\<close>
             
context ast_problem begin

  text \<open>As plan actions are executed by first instantiating them, and then
    executing the action instance, it is natural to define a well-formedness
    concept for action instances.\<close>

  fun wf_inst_action :: "inst_action \<Rightarrow> bool" where
    "wf_inst_action (Inst_Action pre eff) \<longleftrightarrow> (
        wf_inst_fmla pre   
      \<and> wf_effect (ty_inst_term (\<lambda>_. None) objT) eff
      )
    "

  text \<open>We first prove that instantiating a well-formed action schema will yield
    a well-formed action instance.

    We begin with some auxiliary lemmas before the actual theorem.
  \<close>

  lemma (in ast_domain) of_type_refl[simp, intro!]: "of_type T T"
    unfolding of_type_def by auto

  lemma (in ast_domain) of_type_trans[trans]:
    "of_type T1 T2 \<Longrightarrow> of_type T2 T3 \<Longrightarrow> of_type T1 T3"
    unfolding of_type_def
    by clarsimp (metis (no_types, opaque_lifting)
      Image_mono contra_subsetD order_refl rtrancl_image_idem)

  lemma is_of_type_map_ofE:
    assumes "is_of_type (map_of params) x T"
    obtains i xT where "i<length params" "params!i = (x,xT)" "of_type xT T"
    using assms
    unfolding is_of_type_def
    apply -
    apply (split option.splits)
     apply (rule HOL.FalseE)
     apply assumption
    apply (drule map_of_SomeD)
    apply (subst (asm) in_set_conv_nth)
    apply (erule exE)
    apply (erule conjE)
    apply assumption
    done
                    
  lemma constT_ss_objT: "constT \<subseteq>\<^sub>m objT"
    unfolding constT_def objT_def
    apply (rule map_leI)
    by (auto simp: map_add_def split: option.split)

  lemma wf_atom_constT_imp_objT: "wf_atom (ty_term Q constT) a \<Longrightarrow> wf_atom (ty_term Q objT) a"
    apply (erule wf_atom_mono[rotated])
    apply (rule ty_term_mono)
    by (simp_all add: constT_ss_objT)

  lemma wf_fmla_atom_constT_imp_objT: "wf_fmla_atom (ty_term Q constT) a \<Longrightarrow> wf_fmla_atom (ty_term Q objT) a"
    apply (erule wf_fmla_atom_mono[rotated])
    apply (rule ty_term_mono)
    by (simp_all add: constT_ss_objT)

  context
    fixes Q S and f :: "variable \<Rightarrow> inst_term"
    assumes INST: "is_of_type Q x T \<Longrightarrow> is_of_type (ty_inst_term (Q |` S) objT) (f x) T"
  begin 
    
    lemma is_of_type_var_conv: "is_of_type (ty_term Q objT) (term.VAR x) T  \<longleftrightarrow> is_of_type Q x T"
      unfolding is_of_type_def by (auto)

    lemma is_of_type_const_conv: "is_of_type (ty_term Q objT) (term.CONST x) T  \<longleftrightarrow> is_of_type objT x T"
      unfolding is_of_type_def
      by (auto split: option.split)

    lemma INST': "is_of_type (ty_term Q objT) x T \<Longrightarrow> is_of_type (ty_inst_term (Q |` S) objT) (inst_var f x) T"
      apply (cases x) using INST 
      apply auto[1]
       apply (simp add: ast_domain.is_of_type_def)
      by (simp add: is_of_type_def)

    lemma wf_inst_eq_aux: "Q x = Some T \<Longrightarrow> ty_inst_term (Q |` S) objT (f x) \<noteq> None"
      using INST[of x T] unfolding is_of_type_def
      by (auto split: option.splits)

    lemma wf_inst_eq_aux1: "Q x = Some T \<Longrightarrow>\<exists>T'. ty_inst_term (Q |` S) objT (f x) = Some T' \<and> of_type T' T"
    proof -
      assume "Q x = Some T"
      hence "is_of_type Q x T" unfolding is_of_type_def by simp
      from this[THEN INST] have "is_of_type (ty_inst_term (Q |` S) objT) (f x) T" .
      then obtain T' where
        "ty_inst_term (Q |` S) objT (f x) = Some T'" 
        "of_type T' T"
        unfolding is_of_type_def
        by (auto split: option.splits)
      thus ?thesis
        by auto
    qed

    lemma wf_inst_eq_aux': "ty_term Q objT x = Some T \<Longrightarrow> ty_inst_term (Q |` S) objT (inst_var f x) \<noteq> None"
      apply (cases x) 
      by (auto simp: wf_inst_eq_aux split: option.split)

    lemma wf_inst_atom:
      assumes "wf_atom (ty_term Q constT) a"
      shows "wf_atom (ty_inst_term (Q |` S) objT) ((map_atom o inst_var) f a)"
    proof -
      have X1: "list_all2 (is_of_type (ty_inst_term (Q |` S) objT)) (map (inst_var f) xs) Ts" if
        "list_all2 (is_of_type (ty_term Q objT)) xs Ts" for xs Ts
        using that
        apply induction
        using INST'
        by auto
      then show ?thesis
        using assms[THEN wf_atom_constT_imp_objT] wf_inst_eq_aux'
        by (cases a; auto split: option.splits)
    qed

    lemma wf_inst_formula_atom:
      assumes "wf_fmla_atom (ty_term Q constT) a"
      shows "wf_fmla_atom (ty_inst_term (Q |` S) objT) ((cap_avoid_map o inst_var) f a)"
      using assms[THEN wf_fmla_atom_constT_imp_objT] wf_inst_atom
      apply (cases "((ty_term Q constT), a)" rule: wf_fmla_atom.cases; auto split: option.splits)
      by (simp add: INST' list.rel_map(1) list_all2_mono)

    lemma wf_inst_effect_aux:
      assumes "wf_effect (ty_term Q constT) (Effect add del)"
      shows "wf_effect (ty_inst_term (Q |` S) objT) (Effect ((map o cap_avoid_map o inst_var) f add) ((map o cap_avoid_map o inst_var) f del))"
      using assms
      proof (induction "(Effect add del)")
        case (Effect)
        then show ?case using wf_inst_formula_atom by auto
      qed
end

  lemma f'_maintains_type:
    fixes v T
    assumes a: "is_of_type (Q(v\<mapsto>ty)) x T"
        and f': "f' = f(v := inst_term.VAR v)"
        and S': "S' = {x. \<exists>x'. x \<in> dom (Q(v\<mapsto>ty)) \<and> f' x = inst_term.VAR x'}"
        and S:  "S = {x. \<exists>x'. x \<in> dom Q \<and> f x = inst_term.VAR x'}"
        and INST: "\<And>x T. is_of_type Q x T \<Longrightarrow> is_of_type (ty_inst_term (Q |` S) objT) (f x) T"
        and inv: "\<And>v v'. v \<in> dom Q \<Longrightarrow> f v = inst_term.VAR v' \<Longrightarrow> v = v'"
      shows "is_of_type (ty_inst_term (Q(v\<mapsto>ty) |` S') objT) (f' x) T"
    using assms
  proof -
    fix v T
    assume a:  "is_of_type (Q(v\<mapsto>ty)) x T"
    assume f': "f' = f(v := inst_term.VAR v)"
    assume S': "S' = {x. \<exists>x'. x \<in> dom (Q(v\<mapsto>ty)) \<and> f' x = inst_term.VAR x'}"
    show "is_of_type (ty_inst_term (Q(v\<mapsto>ty) |` S') objT) (f' x) T"
    proof (cases "v = x")
      case v: True
      with a
      have "(Q(v\<mapsto>ty)) v = Some ty \<and> of_type ty T"
        unfolding is_of_type_def by auto
      moreover
      have "v \<in> S'" using S' f' by auto
      ultimately 
      have "(Q(v\<mapsto>ty) |` S') v = Some ty \<and> of_type ty T" by auto
      hence "is_of_type (ty_inst_term (Q(v\<mapsto>ty) |` S') objT) (inst_term.VAR v) T"
        unfolding is_of_type_def by simp
      moreover 
      have "inst_term.VAR v = f' x" using v f' by auto
      ultimately 
      show "is_of_type (ty_inst_term (Q(v\<mapsto>ty) |` S') objT) (f' x) T"
        by simp
    next
      case v: False
      obtain xt where
        x': "(Q(v\<mapsto>ty)) x  = Some xt \<and> of_type xt T" 
        using a
        unfolding is_of_type_def
        by (auto split: option.splits)
      
      have "Q x = Some xt \<and> of_type xt T" using v x' by auto
      hence "is_of_type Q x T" unfolding is_of_type_def by auto
      from INST[OF this]
      have inst_term_start: "is_of_type (ty_inst_term (Q |` S) objT) (f x) T " .

      show ?thesis  
      proof (cases "f x" rule: inst_term.exhaust)
        case (OBJ obj')
        with inst_term_start
        have "is_of_type (ty_inst_term (Q |` S) objT) (inst_term.OBJ obj') T" by auto
        hence "is_of_type objT obj' T" unfolding is_of_type_def by auto
        hence "is_of_type (ty_inst_term (Q(v\<mapsto>ty) |` S') objT) (inst_term.OBJ obj') T" unfolding is_of_type_def by auto
        thus ?thesis using OBJ f' v by auto
      next
        case (VAR v')
        with inst_term_start
        have "is_of_type (ty_inst_term (Q |` S) objT) (inst_term.VAR v') T" by auto
        hence iQS: "is_of_type (Q |` S) v' T" unfolding is_of_type_def by auto
        hence "\<exists>xt'. (Q |` S) v' = Some xt'" unfolding is_of_type_def using case_optionE by blast
        hence "v' \<in> S" by (simp add: restrict_map_eq(2))
        with S' f' VAR 
        have "v' \<in> S'" using S by auto
        from  iQS \<open>v' \<in> S\<close> 
        have "is_of_type Q v' T" by (simp add: is_of_type_def)
        hence "is_of_type (Q(v\<mapsto>ty)) v' T" using v a VAR inv \<open>Q x = Some xt \<and> of_type xt T\<close> by blast 
        hence "is_of_type (Q(v\<mapsto>ty) |` S') v' T" using \<open>v' \<in> S'\<close> unfolding is_of_type_def using restrict_in by metis
        hence "is_of_type (ty_inst_term (Q(v \<mapsto> ty) |` S') objT) (inst_term.VAR v') T" unfolding is_of_type_def by auto
        moreover 
        have "f' x = f x" using f' v by simp
        ultimately 
        show ?thesis using VAR by auto
      qed
    qed
  qed 


  lemma wf_inst_formula_aux:
    assumes "wf_fmla upd_te (ty_term Q constT) \<phi>"
        and "S = {x. \<exists>x'. x \<in> dom Q \<and>  f x = inst_term.VAR x'}"
        and "\<And>x T. is_of_type Q x T \<Longrightarrow> is_of_type (ty_inst_term (Q |` S) objT) (f x) T"
        and "\<And>v v'. v \<in> dom Q \<Longrightarrow> f v = inst_term.VAR v' \<Longrightarrow> v = v'"
    shows "wf_fmla upd_inst_te (ty_inst_term (Q |` S) objT) ((cap_avoid_map o inst_var) f \<phi>)"
  using assms
  proof (induction \<phi> arbitrary: Q f S)
    case (Atom x)
    hence 1: "wf_atom (ty_term Q constT) x" by auto
    with wf_inst_atom[of Q S f x] Atom(3) 
    have "wf_atom (ty_inst_term (Q |` S) objT) ((map_atom o inst_var) f x)" by blast
    hence "wf_fmla upd_inst_te (ty_inst_term (Q |` S) objT) ((cap_avoid_map o inst_var) f (Atom x))" by auto
    then show ?case unfolding wf_inst_fmla_def 
      using 1 Atom(1) by auto
  next
    case (Exists t v \<phi>)
    thm Exists.prems
    have "wf_fmla upd_te (ty_term (Q(v\<mapsto>t)) constT) \<phi>" using ty_term_upd Exists.prems(1) by simp
    moreover
    obtain S' f' where 
          S': "S' = {x. \<exists>x'. x \<in> dom (Q(v\<mapsto>t)) \<and> f' x = inst_term.VAR x'}"
      and f': "f' = f(v := inst_term.VAR v)"
      by auto
    moreover
    with Exists.prems(2)
    have S'_def: "S'= insert v S"  by auto
    moreover
    from Exists.prems
    have "\<And>x T. is_of_type (Q(v\<mapsto>t)) x T \<Longrightarrow> is_of_type (ty_inst_term (Q(v\<mapsto>t) |` S') objT) (f' x) T"
      using f'_maintains_type[OF _ f' S'] by blast
    moreover 
    from Exists.prems(4) f'
    have "\<And>x x'. x \<in> dom (Q(v\<mapsto>t)) \<Longrightarrow> f' x = inst_term.VAR x' \<Longrightarrow> x = x'"
      subgoal for x1 x2
        by (cases "x1 = v") auto
      done
    ultimately
    have "wf_fmla upd_inst_te (ty_inst_term (Q(v\<mapsto>t) |` (S')) objT) ((cap_avoid_map \<circ> inst_var) f' \<phi>)"
      using Exists.IH by blast 
    hence "wf_fmla upd_inst_te (ty_inst_term ((Q |` S) (v\<mapsto>t)) objT) ((cap_avoid_map \<circ> inst_var) f' \<phi>)"
      using S'_def restrict_map_upd 
      by metis
    hence "wf_fmla upd_inst_te (upd_inst_te (ty_inst_term ((Q |` S) (v\<mapsto>t)) objT) v t) ((cap_avoid_map \<circ> inst_var) f' \<phi>)"
      using ty_inst_term_upd by force
    moreover
    have "inst_var f' = (inst_var f)(term.VAR v := inst_term.VAR v)"
      apply (subst f', rule ext)
      subgoal for x
        by (cases x) auto
      done
    hence "cap_avoid_map (inst_var f') = cap_avoid_map ((inst_var f)(term.VAR v := inst_term.VAR v))"
      by simp
    hence "(cap_avoid_map \<circ> inst_var) f (\<^bold>\<exists>\<^sub>t v. \<phi>) = (\<^bold>\<exists>\<^sub>t v. ((cap_avoid_map \<circ> inst_var) f' \<phi>))"
      using f' by simp
    ultimately
    show "wf_fmla upd_inst_te (ty_inst_term (Q |` S) objT) ((cap_avoid_map \<circ> inst_var) f (\<^bold>\<exists>\<^sub>t v. \<phi>))"
      using f' ty_inst_term_upd by auto
  next
    case (All t v \<phi>)
    hence "wf_fmla upd_te (ty_term (Q(v\<mapsto>t)) constT) \<phi>" using ty_term_upd by auto
    moreover
    obtain S' f' where 
          S': "S' = {x. \<exists>x'. x \<in> dom (Q(v\<mapsto>t)) \<and> f' x = inst_term.VAR x'}"
      and f': "f' = f(v := inst_term.VAR v)"
      by auto
    moreover
    hence S'_def: "S'= insert v S" using All.prems(2) by auto
    moreover
    have "\<And>x T. is_of_type (Q(v\<mapsto>t)) x T \<Longrightarrow> is_of_type (ty_inst_term (Q(v\<mapsto>t) |` S') objT) (f' x) T"
      using f'_maintains_type[OF _ f' S' ] All.prems by blast
    moreover 
    from All.prems(4) f'
    have "\<And>x x'. x \<in> dom (Q(v\<mapsto>t)) \<Longrightarrow> f' x = inst_term.VAR x' \<Longrightarrow> x = x'"
      subgoal for x1 x2
        by (cases "x1 = v") auto
      done
    ultimately
    have "wf_fmla upd_inst_te (ty_inst_term (Q(v\<mapsto>t) |` (S')) objT) ((cap_avoid_map \<circ> inst_var) f' \<phi>)"
      using All.IH by blast 
    hence "wf_fmla upd_inst_te (ty_inst_term ((Q |` S) (v\<mapsto>t)) objT) ((cap_avoid_map \<circ> inst_var) f' \<phi>)"
      using S'_def restrict_map_upd 
      by metis
    hence "wf_fmla upd_inst_te (upd_inst_te (ty_inst_term ((Q |` S) (v\<mapsto>t)) objT) v t) ((cap_avoid_map \<circ> inst_var) f' \<phi>)"
      using ty_inst_term_upd by force
    moreover
    have "inst_var f' = (inst_var f)(term.VAR v := inst_term.VAR v)"
      apply (subst f', rule ext)
      subgoal for x
        by (cases x) auto
      done
    hence "cap_avoid_map (inst_var f') = cap_avoid_map ((inst_var f)(term.VAR v := inst_term.VAR v))"
      by simp
    hence "(cap_avoid_map \<circ> inst_var) f (\<^bold>\<forall>\<^sub>t v. \<phi>) = (\<^bold>\<forall>\<^sub>t v. ((cap_avoid_map \<circ> inst_var) f' \<phi>))"
      using f' by simp
    ultimately
    show "wf_fmla upd_inst_te (ty_inst_term (Q |` S) objT) ((cap_avoid_map \<circ> inst_var) f (\<^bold>\<forall>\<^sub>t v. \<phi>))"
      using f' ty_inst_term_upd by auto
  qed auto

  lemma full_inst_imp_dom_empty:
    assumes INST: "\<And>x T. is_of_type Q x T \<Longrightarrow> is_of_type (ty_inst_term (\<lambda>_. None) objT) (f x) T"
        and inv:  "\<And>v x. x \<in> dom Q \<Longrightarrow> f x = inst_term.VAR v \<Longrightarrow> x = v"
      shows "{x. \<exists>x'. x \<in> dom Q \<and> f x = inst_term.VAR x'} = {}"
    using assms
  proof -
    have "\<exists>obj. f x = inst_term.OBJ obj" 
      if "x \<in> dom Q" for x 
      using that
    proof -
      assume "x \<in> dom Q"
      then obtain T where
        "is_of_type Q x T"
        unfolding is_of_type_def by fastforce
      with INST
      have "is_of_type (ty_inst_term (\<lambda>_. None) objT) (f x) T"
        by blast
      then obtain vT where
        "ty_inst_term (\<lambda>_. None) objT (f x) = Some vT \<and> of_type vT T" 
        unfolding is_of_type_def by (auto split: option.splits)
      thus "\<exists>obj. f x = inst_term.OBJ obj"
        by (cases "f x") auto
    qed
    thus "{x. \<exists>x'. x \<in> dom Q \<and> f x = inst_term.VAR x'} = {}" by force
  qed

  lemma wf_inst_formula:
    assumes wff:  "wf_fmla upd_te (ty_term Q constT) \<phi>"
        and INST: "\<And>x T. is_of_type Q x T \<Longrightarrow> is_of_type (ty_inst_term (\<lambda>_. None) objT) (f x) T"
        and inv:  "\<And>v x. x \<in> dom Q \<Longrightarrow> f x = inst_term.VAR v \<Longrightarrow> x = v"
      shows "wf_inst_fmla ((cap_avoid_map o inst_var) f \<phi>)"
  proof -
    have S: "{} = {x. \<exists>x'. x \<in> dom Q \<and> f x = inst_term.VAR x'}" 
      using full_inst_imp_dom_empty[OF INST inv] by presburger
    
    with INST
    have "\<And>x T. is_of_type Q x T \<Longrightarrow> is_of_type (ty_inst_term (Q |` {}) objT) (f x) T" by auto
    
    from wf_inst_formula_aux[OF wff S this inv]
    have "wf_fmla upd_inst_te (ty_inst_term (Q |` {}) objT) ((cap_avoid_map o inst_var) f \<phi>)" by presburger
    hence "wf_fmla upd_inst_te (ty_inst_term (\<lambda>_. None) objT) ((cap_avoid_map o inst_var) f \<phi>)"using restrict_map_to_empty[of Q] by argo
    thus "wf_inst_fmla ((cap_avoid_map o inst_var) f \<phi>)" unfolding wf_inst_fmla_def by simp
  qed 

  lemma wf_inst_effect:
    fixes add::"schematic_formula list" and del::"schematic_formula list" and f
    assumes "wf_effect (ty_term Q constT) (Effect add del)"
      and INST: "\<And>x T. is_of_type Q x T \<Longrightarrow> is_of_type (ty_inst_term (\<lambda>_. None) objT) (f x) T"
      and inv:  "\<And>v x. x \<in> dom Q \<Longrightarrow> f x = inst_term.VAR v \<Longrightarrow> x = v"
    shows "wf_effect (ty_inst_term (\<lambda>_.None) objT) (Effect ((map o cap_avoid_map o inst_var) f add) ((map o cap_avoid_map o inst_var) f del))"
    using assms
  proof -
    assume a: "wf_effect (ty_term Q constT) (Effect add del)"
    have S: "{} = {x. \<exists>x'. x \<in> dom Q \<and> f x = inst_term.VAR x'}" 
      using full_inst_imp_dom_empty[OF INST inv] by presburger

    with INST
    have INST': "\<And>x T. is_of_type Q x T \<Longrightarrow> is_of_type (ty_inst_term (Q |` {}) objT) (f x) T" by auto

    from wf_inst_effect_aux[OF this a]
    have "wf_effect (ty_inst_term (Q |` {}) objT) 
                  (Effect ((map o cap_avoid_map o inst_var) f add) 
                          ((map o cap_avoid_map o inst_var) f del))" 
      by presburger

    thus "wf_effect (ty_inst_term (\<lambda>_. None) objT) 
                  (Effect ((map o cap_avoid_map o inst_var) f add) 
                          ((map o cap_avoid_map o inst_var) f del))" 
      using restrict_map_to_empty[of Q] by argo
  qed


  
  text \<open>Instantiating a well-formed action schema with compatible arguments
    will yield a well-formed action instance.
  \<close>
  theorem wf_instantiate_action_schema:
    assumes "action_params_match a args"
    assumes "wf_action_schema a"
    shows "wf_inst_action (instantiate_action_schema a args)"
  proof (cases a)
    case [simp]: (Action_Schema name params pre eff)
    let ?f = "the o (map_of (zip (map fst params) (map inst_term.OBJ args)))"
    
    have INST: "is_of_type (ty_inst_term (\<lambda>_. None) objT) (?f x) T"
      if "is_of_type (map_of params) x T" for x T
      using that
      apply (rule is_of_type_map_ofE)
      using assms
      apply (clarsimp simp: Let_def)
      subgoal for i xT
        unfolding action_params_match_def
        apply (subst lookup_zip_idx_eq[where i=i];
          (clarsimp simp: list_all2_lengthD)?)
        apply (frule list_all2_nthD2[where p=i]; simp?)
        apply (auto
                simp: is_obj_of_type_alt is_of_type_def
                intro: of_type_trans
                split: option.splits)
        done
      done

    have inv:   "x = v" 
      if  d:    "x \<in> dom (map_of params)" 
      and asmt: "?f x = inst_term.VAR v" 
    for x v
      using that
      apply (subst (asm) dom_map_of_conv_image_fst, subst (asm) sym[OF set_map], subst (asm) in_set_conv_nth)
      using assms
      unfolding action_params_match_def
      apply (clarsimp simp: Let_def)
      subgoal for i
        apply (drule list_all2_lengthD)
        apply (subst (asm) lookup_zip_idx_eq)
        by auto
      done

    have "wf_fmla upd_te (ty_term (map_of params) constT) pre" 
      using assms by (auto simp: Let_def)
    with INST inv
    have inst_pre: "wf_inst_fmla ((cap_avoid_map o inst_var) ?f pre)" 
      using wf_inst_formula by blast

    obtain add del where
      eff: "eff = Effect add del"
      by (cases rule: ast_effect.exhaust)
    with assms
    have "wf_effect (ty_term (map_of params) constT) (Effect add del)"
      by (auto simp: Let_def)
    with INST inv
    have inst_eff: "wf_effect (ty_inst_term (\<lambda>_.None) objT)
        (Effect ((map o cap_avoid_map o inst_var) ?f add) 
                ((map o cap_avoid_map o inst_var) ?f del))"
      using wf_inst_effect by blast

    from inst_pre eff inst_eff
    show "wf_inst_action (instantiate_action_schema a args)"
      by (simp add: Let_def)
  qed

  corollary inst_leaves_no_free_vars:
    assumes match:"action_params_match a args"
          and wf: "wf_action_schema a"
          and inst: "Inst_Action pre' (Effect add' del') = instantiate_action_schema a args"
        shows "free_vars pre' = {} 
              \<and> (\<forall>a \<in> set add'. free_vars a = {})
              \<and> (\<forall>d \<in> set del'. free_vars d = {})"
  proof -
    from wf_instantiate_action_schema[OF match wf] inst
    have 1: "wf_inst_action (Inst_Action pre' (Effect add' del'))" by auto
    hence "wf_inst_fmla pre'" by fastforce
    hence "free_vars pre' = {}" using wf_inst_fmla_alt by blast
    moreover
    from 1
    have "\<forall>a \<in> set add'. wf_inst_fmla a"
      using wf_fmla_atom_alt unfolding wf_inst_fmla_def
      by auto
    hence "\<forall>a \<in> set add'. free_vars a = {}" using wf_inst_fmla_alt by blast
    moreover
    from 1
    have "\<forall>d \<in> set del'. wf_inst_fmla d"
      using wf_fmla_atom_alt wf_inst_fmla_def unfolding wf_inst_fmla_def
      by fastforce
    hence "\<forall>d \<in> set del'. free_vars d = {}" using wf_inst_fmla_alt by blast
    ultimately
    show ?thesis by simp
  qed
  
  corollary inst_maintains_bound:
    assumes a[simp]: "a = Action_Schema n params pre (Effect add del)"
        and match:"action_params_match a args"
        and wf: "wf_action_schema a"
        and inst: "Inst_Action pre' (Effect add' del') = instantiate_action_schema a args"
      shows "sf_bound_vars pre = bound_vars pre' 
            \<and> (\<forall>i < length add. sf_bound_vars (add ! i) = bound_vars (add' ! i))
            \<and> (\<forall>i < length del. sf_bound_vars (del ! i) = bound_vars (del' ! i))"
  proof -
    let ?f = "inst_var (the o (map_of (zip (map fst params) (map inst_term.OBJ args))))"

    have well_inst:
     "\<forall>v. v \<in> sf_bound_vars \<phi> \<longleftrightarrow> v \<in> bound_vars (cap_avoid_map ?f \<phi>)"
      if "wf_fmla upd_te (ty_term (map_of params) constT) \<phi>"
        for \<phi> 
    proof -
      from that 
      have  "sf_free_vars \<phi> \<subseteq> dom (map_of params)" 
        using wf_schematic_fmla_free_vars[of "map_of params"]
        by force
      hence "sf_free_vars \<phi> \<subseteq> set (map fst params)"
        by (simp add: dom_map_of_conv_image_fst)
      moreover
      from match
      have "length params = length args"
        unfolding action_params_match_def using list_all2_lengthD by fastforce
      hence "length (map fst params) = length (map inst_term.OBJ args)"
        by fastforce
      hence "\<forall>v \<in> set (map fst params).(\<exists>obj. (map_of (zip (map fst params) (map inst_term.OBJ args))) v = Some (inst_term.OBJ obj))"
        find_theorems name: "map_of_zip"
        apply -
        apply (rule ballI)
        subgoal for v
          apply (drule map_of_zip_is_Some)
          apply auto[1]
          apply (drule map_of_SomeD)
          apply (erule in_set_zipE)
          by auto
        done
      ultimately
      have "\<forall>v \<in> sf_free_vars \<phi>.(\<exists>obj. (the o (map_of (zip (map fst params) (map inst_term.OBJ args)))) v = inst_term.OBJ obj)"
        by fastforce
      hence "\<forall>v \<in> sf_free_vars \<phi>.(\<exists>obj. ?f (term.VAR v) = inst_term.OBJ obj)"
        by simp
      thus "\<forall>v. v \<in> sf_bound_vars \<phi> \<longleftrightarrow> v \<in> bound_vars (cap_avoid_map ?f \<phi>)"
        using bound_is_cam_bound
        by simp
    qed
    
    have "sf_bound_vars pre = bound_vars pre'" using inst wf well_inst by (auto simp: Let_def)
    moreover
    have "sf_bound_vars (add ! i) = bound_vars (add' ! i)" 
      if "i < length add" for i
    proof -
      have "wf_fmla_atom (ty_term (map_of params) constT) (add ! i)" 
        using wf that by (auto simp: Let_def)
      hence "wf_fmla upd_te (ty_term (map_of params) constT) (add ! i)" 
        using wf_fmla_atom_alt by blast
      moreover have "add' ! i = cap_avoid_map ?f (add ! i)" using inst that by (auto simp: Let_def)
      ultimately show "sf_bound_vars (add ! i) = bound_vars (add' ! i)"
        using well_inst by auto
    qed
    moreover
    have "sf_bound_vars (del ! i) = bound_vars (del' ! i)" 
      if "i < length del" for i
    proof -
      have "wf_fmla_atom (ty_term (map_of params) constT) (del ! i)" 
        using wf that by (auto simp: Let_def)
      hence "wf_fmla upd_te (ty_term (map_of params) constT) (del ! i)" 
        using wf_fmla_atom_alt by blast
      moreover have "del' ! i = cap_avoid_map ?f (del ! i)" using inst that by (auto simp: Let_def)
      ultimately show "sf_bound_vars (del ! i) = bound_vars (del' ! i)"
        using well_inst by auto
    qed
    ultimately show ?thesis by simp
  qed
  
end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>



subsubsection \<open>Preservation\<close>

context ast_problem begin

  text \<open>We start by defining two shorthands for enabledness and execution of
    a plan action.\<close>

  text \<open>Shorthand for enabled plan action: It is well-formed, and the
    precondition holds for its instance.\<close>
  definition plan_action_enabled :: "plan_action \<Rightarrow> world_model \<Rightarrow> bool" where
    "plan_action_enabled \<pi> M
      \<longleftrightarrow> wf_plan_action \<pi> \<and> M \<^sup>c\<TTurnstile>\<^sub>= precondition (resolve_instantiate \<pi>)"

  text \<open>Shorthand for executing a plan action: Resolve, instantiate, and
    apply effect\<close>
  definition execute_plan_action :: "plan_action \<Rightarrow> world_model \<Rightarrow> world_model"
    where "execute_plan_action \<pi> M
      = (apply_effect (effect (resolve_instantiate \<pi>)) M)"

  text \<open>The @{const plan_action_path} predicate can be decomposed naturally
    using these shorthands: \<close>
  lemma plan_action_path_Nil[simp]: "plan_action_path M [] M' \<longleftrightarrow> M'=M"
    by (auto simp: plan_action_path_def)

  lemma plan_action_path_Cons[simp]:
    "plan_action_path M (\<pi>#\<pi>s) M' \<longleftrightarrow>
      plan_action_enabled \<pi> M
    \<and> plan_action_path (execute_plan_action \<pi> M) \<pi>s M'"
    by (auto
      simp: plan_action_path_def execute_plan_action_def
            execute_inst_action_def plan_action_enabled_def)



end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>

context wf_ast_problem begin
  text \<open>The initial world model is well-formed\<close>
  lemma wf_I: "wf_world_model I"
    using wf_problem
    unfolding I_def wf_world_model_def wf_problem_def
    apply(safe) subgoal for f by (induction f) auto
    done

  text \<open>Application of a well-formed effect preserves well-formedness
    of the model\<close>
  lemma wf_apply_effect:
    assumes "wf_effect (ty_inst_term (\<lambda>_.None) objT) e"
    assumes "wf_world_model s"
    shows "wf_world_model (apply_effect e s)"
    using assms wf_problem
    unfolding wf_world_model_def wf_problem_def wf_domain_def
    by (cases e) (auto split: formula.splits prod.splits)

  text \<open>Execution of plan actions preserves well-formedness\<close>
  theorem wf_execute:
    assumes "plan_action_enabled \<pi> s"
    assumes "wf_world_model s"
    shows "wf_world_model (execute_plan_action \<pi> s)"
    using assms
  proof (cases \<pi>)
    case [simp]: (PAction name args)

    from \<open>plan_action_enabled \<pi> s\<close> have "wf_plan_action \<pi>"
      unfolding plan_action_enabled_def by auto
    then obtain a where
      "resolve_action_schema name = Some a" and
      T: "action_params_match a args"
      by (auto split: option.splits)

    from wf_domain have
      [simp]: "distinct (map ast_action_schema.name (actions D))"
      unfolding wf_domain_def by auto

    from \<open>resolve_action_schema name = Some a\<close> have
      "a \<in> set (actions D)"
      unfolding resolve_action_schema_def by auto
    with wf_domain have "wf_action_schema a"
      unfolding wf_domain_def by auto
    hence "wf_inst_action (resolve_instantiate \<pi>)"
      using \<open>resolve_action_schema name = Some a\<close> T
        wf_instantiate_action_schema
      by auto
    thus ?thesis
      apply (simp add: execute_plan_action_def execute_inst_action_def)
      apply (rule wf_apply_effect)
      apply (cases "resolve_instantiate \<pi>"; simp)
      by (rule \<open>wf_world_model s\<close>)
  qed

  theorem wf_execute_compact_notation:
    "plan_action_enabled \<pi> s \<Longrightarrow> wf_world_model s
    \<Longrightarrow> wf_world_model (execute_plan_action \<pi> s)"
    by (rule wf_execute)


  text \<open>Execution of a plan preserves well-formedness\<close>
  corollary wf_plan_action_path:
    assumes "wf_world_model M" and " plan_action_path M \<pi>s M'"
    shows "wf_world_model M'"
    using assms
    by (induction \<pi>s arbitrary: M) (auto intro: wf_execute)


end \<comment> \<open>Context of \<open>wf_ast_problem\<close>\<close>




end \<comment> \<open>Theory\<close>
