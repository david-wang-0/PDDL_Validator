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
datatype 'ent ast_effect = 
  Effect  (adds: "(('ent atom) formula) list") 
          (dels: "(('ent atom) formula) list")

text \<open>Variables are identified by their names.\<close>
datatype variable = varname: Var name
text \<open>Objects and constants are identified by their names\<close>
datatype object = name: Obj name

datatype "term" = VAR variable | CONST object
hide_const (open) VAR CONST


type_synonym schematic_formula = "(term atom) formula"
type_synonym schematic_effect = "term ast_effect"

type_synonym ground_formula = "(object atom) formula"
type_synonym ground_effect = "object ast_effect"

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

text \<open>A domain contains the declarations of primitive types, predicates,
  and action schemas.\<close>
datatype ast_domain = Domain
  (predicates: "predicate_decl list")
  (actions: "ast_action_schema list")
  (types: "(name \<times> name) list") \<comment> \<open> \<open>(type, supertype)\<close> declarations. \<close>
  ("consts": "(object \<times> type) list")

subsubsection \<open>Problems\<close>


text \<open>A fact is a predicate applied to objects.\<close>
text \<open>Changed to object, because this makes some other changes easier.
    However, the change from object term to ground term in general requires
    us to assert that variables in instantiations are bound.\<close>
text \<open> Question: are facts only used in effects? See \<open>wf_fact\<close> as well. \<close>
type_synonym fact = "predicate \<times> object list"

text \<open>A problem consists of a domain, a list of objects,
  a description of the initial state, and a description of the goal state. \<close>
datatype ast_problem = Problem
  (domain: ast_domain)
  (objects: "(object \<times> type) list")
  (init: "ground_formula list")
  (goal: "schematic_formula")

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
datatype ground_action = Ground_Action
  (precondition: "ground_formula")
  (effect: "ground_effect")

(* Syntax helpers for schematic formulae *)

fun term_vars where
  "term_vars (term.VAR x) = {x}" 
| "term_vars (term.CONST c) = {}"

fun term_objs where
  "term_objs (term.VAR x) = {}"
| "term_objs (term.CONST obj) = {obj}"

fun term_subst::"variable \<Rightarrow> object \<Rightarrow> term \<Rightarrow> term" where
  "term_subst v obj (term.VAR x) = (if (x = v) then (term.CONST obj) else term.VAR x)" 
| "term_subst _ _ (term.CONST obj) = term.CONST obj"

abbreviation term_atom_subst where
"term_atom_subst v obj \<equiv> map_atom (term_subst v obj)"

definition term_atom_vars where
"term_atom_vars \<equiv> \<Union> o ent o (map_atom term_vars)"

definition term_atom_objs where
"term_atom_objs \<equiv> \<Union> o ent o (map_atom term_objs)"


lemma tav_alt: "term_atom_vars x = \<Union> (term_vars ` ent x)" 
  unfolding term_atom_vars_def by (simp add: atom.set_map) 

lemma tao_alt: "term_atom_objs x = \<Union> (term_objs ` ent x)" 
  unfolding term_atom_objs_def by (simp add: atom.set_map) 

lemma tav_empty: "term_atom_vars x = {} \<longleftrightarrow> (\<forall>e \<in> ent x. term_vars e = {})"
  using tav_alt by auto

lemma tavm_alt: "term_atom_vars (map_atom f x) = \<Union> ((term_vars o f) ` ent x)"
  unfolding term_atom_vars_def by (simp add: atom.map_comp atom.set_map)

lemma taom_alt: "term_atom_objs (map_atom f x) = \<Union> ((term_objs o f) ` ent x)"
  unfolding term_atom_objs_def by (simp add: atom.map_comp atom.set_map)

lemma subst_subst_all: "v \<notin> term_atom_vars (term_atom_subst v obj a)"
proof -
  have "term_atom_vars (term_atom_subst v obj a) = (\<Union> o ent o (map_atom term_vars)) (map_atom (term_subst v obj) a)" unfolding term_atom_vars_def by simp
  also have "...  = \<Union> (ent (map_atom term_vars (map_atom (term_subst v obj) a)))" by simp
  also have "... = \<Union> (ent (map_atom (term_vars o (term_subst v obj)) a))" by (simp add: atom.map_comp)
  finally 
  have "term_atom_vars (term_atom_subst v obj a) = \<Union> ((term_vars o (term_subst v obj)) ` ent a)" by (simp add: atom.set_map)
  moreover 
  have "\<And>t. v \<notin> (term_vars (term_subst v obj t))" 
    subgoal for t
      by (cases t) auto
    done
  ultimately 
  show "v \<notin> term_atom_vars (term_atom_subst v obj a)" by auto
qed

lemma term_subst_replaces: "v \<in> term_vars t \<Longrightarrow> c \<in> term_objs (term_subst v c t)"
  by (cases t) auto

lemma subst_replaces: "v \<in> term_atom_vars a \<Longrightarrow> c \<in> term_atom_objs (term_atom_subst v c a)"
proof -
  assume "v \<in> term_atom_vars a"
  hence "v \<in> \<Union> (term_vars ` ent a)" using tav_alt by blast
  hence "c \<in> \<Union> ((term_objs o (term_subst v c)) ` ent a)" using term_subst_replaces by auto
  thus "c \<in> term_atom_objs (term_atom_subst v c a)" using taom_alt tao_alt by blast
qed

lemma term_subst_idem: "v \<notin> term_vars t \<Longrightarrow> term_subst v c t = t"
  by (cases t) auto

lemma subst_idem: "v \<notin> term_atom_vars a \<Longrightarrow> term_atom_subst v c a = a"
proof -
  assume "v \<notin> term_atom_vars a"
  hence "v \<notin> \<Union> (term_vars ` ent a)" using tav_alt by blast
  hence "\<forall>e \<in> ent a. term_subst v c e = e" using term_subst_idem by auto
  thus "term_atom_subst v c a = a" by (simp add: atom.map_ident_strong)
qed

subsection \<open>Closed-World Assumption, Equality, and Negation\<close>
  text \<open>Discriminator for atomic predicate formulas.\<close>
  fun is_predAtom where
    "is_predAtom (Atom (predAtm _ _)) = True" | "is_predAtom _ = False"


  text \<open>The world model is a set of (atomic) formulas\<close>
  type_synonym world_model = "object atom formula set"

  text \<open>It is basic, if it only contains atoms\<close>
  definition "wm_basic M \<equiv> \<forall>a\<in>M. is_predAtom a"

  text \<open>A valuation extracted from the atoms of the world model\<close>
  definition valuation :: "world_model \<Rightarrow> object atom valuation"
    where "valuation M \<equiv> \<lambda>predAtm p xs \<Rightarrow> Atom (predAtm p xs) \<in> M | Eq a b \<Rightarrow> a=b"

  text \<open>Augment a world model by adding negated versions of all atoms
    not contained in it, as well as interpretations of equality.\<close>
  definition close_world :: "world_model \<Rightarrow> world_model" where "close_world M =
    M \<union> {\<^bold>\<not>(Atom (predAtm p as)) | p as. Atom (predAtm p as) \<notin> M}
    \<union> {Atom (Eq a a) | a. True} \<union> {\<^bold>\<not>(Atom (Eq a b)) | a b. a\<noteq>b}"

  definition "close_neg M \<equiv> M \<union> {\<^bold>\<not>(Atom a) | a. Atom a \<notin> M}"
  lemma "wm_basic M \<Longrightarrow> close_world M = close_neg (M \<union> {Atom (Eq a a) | a. True})"
    unfolding close_world_def close_neg_def wm_basic_def
    apply clarsimp
    apply (auto 0 3)
    by (metis atom.exhaust)


  abbreviation cw_entailment (infix "\<^sup>c\<TTurnstile>\<^sub>=" 53) where
    "M \<^sup>c\<TTurnstile>\<^sub>= \<phi> \<equiv> close_world M \<TTurnstile> \<phi>"


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

  lemma valuation_aux_1:
    fixes M :: world_model and \<phi> :: "object atom formula"
    defines "C \<equiv> close_world M"
    assumes A: "\<forall>\<phi>\<in>C. \<A> \<Turnstile> \<phi>"
    shows "\<A> = valuation M"
    using A unfolding C_def
    apply -
    apply (auto simp: in_close_world_conv valuation_def Ball_def intro!: ext split: atom.split)
    apply (metis formula_semantics.simps(1) formula_semantics.simps(3))
    apply (metis formula_semantics.simps(1) formula_semantics.simps(3))
    by (metis atom.collapse(2) formula_semantics.simps(1) is_predAtm_def)



  lemma valuation_aux_2:
    assumes "wm_basic M"
    shows "(\<forall>G\<in>close_world M. valuation M \<Turnstile> G)"
    using assms unfolding wm_basic_def
    by (force simp: in_close_world_conv valuation_def elim: is_predAtom.elims)

  lemma val_imp_close_world: "valuation M \<Turnstile> \<phi> \<Longrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<phi>"
    unfolding entailment_def
    using valuation_aux_1
    by blast

  lemma close_world_imp_val:
    "wm_basic M \<Longrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<phi> \<Longrightarrow> valuation M \<Turnstile> \<phi>"
    unfolding entailment_def using valuation_aux_2 by blast

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

fun is_STRIPS_fmla :: "'ent atom formula \<Rightarrow> bool" where
  "is_STRIPS_fmla (Atom (predAtm _ _)) \<longleftrightarrow> True"
| "is_STRIPS_fmla (\<bottom>) \<longleftrightarrow> True"
| "is_STRIPS_fmla (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) \<longleftrightarrow> is_STRIPS_fmla \<phi>\<^sub>1 \<and> is_STRIPS_fmla \<phi>\<^sub>2"
| "is_STRIPS_fmla (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<longleftrightarrow> is_STRIPS_fmla \<phi>\<^sub>1 \<and> is_STRIPS_fmla \<phi>\<^sub>2"
| "is_STRIPS_fmla (\<^bold>\<not>\<bottom>) \<longleftrightarrow> True"
| "is_STRIPS_fmla _ \<longleftrightarrow> False"

lemma aux1: "\<lbrakk>wm_basic M; is_STRIPS_fmla \<phi>; valuation M \<Turnstile> \<phi>; \<forall>G\<in>M. \<A> \<Turnstile> G\<rbrakk> \<Longrightarrow> \<A> \<Turnstile> \<phi>"
  apply(induction \<phi> rule: is_STRIPS_fmla.induct)
  by (auto simp: valuation_def)

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
    by (auto simp: entailment_def intro: aux1 aux2)
qed

text \<open>Our extension to negation and equality is a proper generalization of the
  standard STRIPS semantics for formula without negation and equality\<close>
theorem proper_STRIPS_generalization:
  "\<lbrakk>wm_basic M; is_STRIPS_fmla \<phi>\<rbrakk> \<Longrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<phi> \<longleftrightarrow> M \<TTurnstile> \<phi>"
  by (simp add: valuation_iff_close_world[symmetric] valuation_iff_STRIPS)

subsection \<open>STRIPS Semantics\<close>

text \<open>For this section, we fix a domain \<open>D\<close>, using Isabelle's
  locale mechanism.\<close>
locale ast_domain =
  fixes D :: ast_domain
begin
  text \<open>It seems to be agreed upon that, in case of a contradictory effect,
    addition overrides deletion. We model this behaviour by first executing
    the deletions, and then the additions.\<close>
  fun apply_effect :: "object ast_effect \<Rightarrow> world_model \<Rightarrow> world_model"
  where
     "apply_effect (Effect a d) s = (s - set d) \<union> (set a)"

  text \<open>Execute a ground action\<close>
  definition execute_ground_action :: "ground_action \<Rightarrow> world_model \<Rightarrow> world_model"
  where
    "execute_ground_action a M = apply_effect (effect a) M"

  text \<open>Predicate to model that the given list of action instances is
    executable, and transforms an initial world model \<open>M\<close> into a final
    model \<open>M'\<close>.

    Note that this definition over the list structure is more convenient in HOL
    than to explicitly define an indexed sequence \<open>M\<^sub>0\<dots>M\<^sub>N\<close> of intermediate world
     models, as done in [Lif87].
  \<close>
  fun ground_action_path
    :: "world_model \<Rightarrow> ground_action list \<Rightarrow> world_model \<Rightarrow> bool"
  where
    "ground_action_path M [] M' \<longleftrightarrow> (M = M')"
  | "ground_action_path M (\<alpha>#\<alpha>s) M' \<longleftrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= precondition \<alpha>
    \<and> ground_action_path (execute_ground_action \<alpha> M) \<alpha>s M'"

  text \<open>Function equations as presented in paper,
    with inlined @{const execute_ground_action}.\<close>
  lemma ground_action_path_in_paper:
    "ground_action_path M [] M' \<longleftrightarrow> (M = M')"
    "ground_action_path M (\<alpha>#\<alpha>s) M' \<longleftrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= precondition \<alpha>
    \<and> (ground_action_path (apply_effect (effect \<alpha>) M) \<alpha>s M')"
    by (auto simp: execute_ground_action_def)

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>


subsection \<open>Well-Formedness of PDDL\<close>



(* Well-formedness *)

(*
  Compute signature: predicate/arity
  Check that all atoms (schemas and facts) satisfy signature

  for action:
    Check that used parameters \<subseteq> declared parameters

  for init/goal: Check that facts only use declared objects
*)


fun ty_term::"(variable \<Rightarrow> type option) \<Rightarrow> (object \<Rightarrow> type option) \<Rightarrow> term \<Rightarrow> type option" where
  "ty_term varT objT (term.VAR v) = varT v"
| "ty_term varT objT (term.CONST c) = objT c"

lemma ty_term_mono: "varT \<subseteq>\<^sub>m varT' \<Longrightarrow> objT \<subseteq>\<^sub>m objT' \<Longrightarrow>
  ty_term varT objT \<subseteq>\<^sub>m ty_term varT' objT'"
  apply (rule map_leI)
  subgoal for x v
    apply (cases x)
    apply (auto dest: map_leD)
    done
  done

context ast_domain
begin
  
  text \<open>The signature is a partial function that maps the predicates
    of the domain to lists of argument types.\<close>
  definition sig :: "predicate \<rightharpoonup> type list" where
    "sig \<equiv> map_of (map (\<lambda>PredDecl p n \<Rightarrow> (p,n)) (predicates D))"

  text \<open>We use a flat subtype hierarchy, where every type is a subtype
    of object, and there are no other subtype relations.

    Note that we do not need to restrict this relation to declared types,
    as we will explicitly ensure that all types used in the problem are
    declared.
    \<close>

  fun subtype_edge where
    "subtype_edge (ty,superty) = (superty,ty)"

  definition "subtype_rel \<equiv> set (map subtype_edge (types D))"

  (*
  definition "subtype_rel \<equiv> {''object''}\<times>UNIV"
  *)

  definition of_type :: "type \<Rightarrow> type \<Rightarrow> bool" where
    "of_type oT T \<equiv> set (primitives oT) \<subseteq> subtype_rel\<^sup>* `` set (primitives T)"
  text \<open>This checks that every primitive on the LHS is contained in or a
    subtype of a primitive on the RHS\<close>




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

    text \<open>A formula is well-formed if it consists of valid atoms,
      and does not contain negations, except for the encoding \<open>\<^bold>\<not>\<bottom>\<close> of true.
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

    (*lemma wf_fmla_add_simps[simp]: "wf_fmla (\<^bold>\<not>\<phi>) \<longleftrightarrow> \<phi>=\<bottom>"
      by (cases \<phi>) auto*)

    text \<open>Special case for a well-formed atomic predicate formula\<close>
    fun wf_fmla_atom where
      "wf_fmla_atom (Atom (predAtm a vs)) \<longleftrightarrow> wf_pred_atom (a,vs)"
    | "wf_fmla_atom _ \<longleftrightarrow> False"

    lemma wf_fmla_atom_alt: "wf_fmla_atom \<phi> \<longleftrightarrow> is_predAtom \<phi> \<and> wf_fmla \<phi>"
      by (cases \<phi> rule: wf_fmla_atom.cases) auto

    text \<open>An effect is well-formed if the added and removed formulas
      are atomic\<close>
    fun wf_effect where
      "wf_effect (Effect a d) \<longleftrightarrow>
          (\<forall>ae\<in>set a. wf_fmla_atom ae)
        \<and> (\<forall>de\<in>set d. wf_fmla_atom de)"

end \<comment> \<open>Context fixing \<open>ty_ent\<close>\<close>

  definition constT :: "object \<rightharpoonup> type" where
    "constT \<equiv> map_of (consts D)"
             
  text \<open>A type is well-formed if it consists only of declared primitive types,
     and the type object.\<close>
  fun wf_type where
    "wf_type (Either Ts) \<longleftrightarrow> set Ts \<subseteq> insert ''object'' (fst`set (types D))"

  text \<open>A predicate is well-formed if its argument types are well-formed.\<close>
  fun wf_predicate_decl where
    "wf_predicate_decl (PredDecl p Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. wf_type T)"

  text \<open>The types declaration is well-formed, if all supertypes are declared types (or object)\<close>
  definition "wf_types \<equiv> snd`set (types D) \<subseteq> insert ''object'' (fst`set (types D))"

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
    \<and> distinct (map fst (consts D))
    \<and> (\<forall>(n,T)\<in>set (consts  D). wf_type T)
    \<and> distinct (map ast_action_schema.name (actions D))
    "

end \<comment> \<open>locale \<open>ast_domain\<close>\<close>



text \<open>We fix a problem, and also include the definitions for the domain
  of this problem.\<close>
locale ast_problem = ast_domain "domain P"
  for P :: ast_problem 
begin

  text \<open>We refer to the problem domain as \<open>D\<close>\<close>
  abbreviation "D \<equiv> ast_problem.domain P"

  (* constants are from the domain, objects are from the problem *)
  definition objT :: "object \<rightharpoonup> type" where
    "objT \<equiv> map_of (objects P) ++ constT"

  lemma objT_alt: "objT = map_of (consts D @ objects P)"
    unfolding objT_def constT_def
    apply (clarsimp)
    done
  
  text \<open>Filter those constants in the domain that belong to the type.\<close>
  definition t_dom::"type \<Rightarrow> object list" where
  "t_dom typ \<equiv> map fst (filter (\<lambda>(c, t). of_type t typ) (consts D @ objects P))"


  definition wf_fact :: "fact \<Rightarrow> bool" where
    "wf_fact = wf_pred_atom objT"

  text \<open>An action schema is well-formed if the parameter names are distinct,
    and the precondition and effect is well-formed wrt.\ the parameters.
  \<close>

  (* action schemas are well-formed only in relation to the problem *)
  fun wf_action_schema :: "ast_action_schema \<Rightarrow> bool" where
    "wf_action_schema (Action_Schema n params pre eff) \<longleftrightarrow> (
      let
        tyt = ty_term (map_of params) objT
      in
        distinct (map fst params)
      \<and> wf_fmla tyt pre
      \<and> wf_effect tyt eff)"

  text \<open>This definition is needed for well-formedness of the initial model,
    and forward-references to the concept of world model.
  \<close>
  (* What makes a world-model well-formed? Since the initial state is essentially
      equivalent to the effect of a non-action, it being well-formed means, that it
      is unquantified. *)
  definition wf_world_model::"ground_formula set \<Rightarrow> bool" where
    "wf_world_model M = (\<forall>f\<in>M. wf_fmla_atom objT f)"

  definition wf_goal::"schematic_formula \<Rightarrow> bool" where
    "wf_goal = wf_fmla (ty_term (Map.empty) objT)"

  (*Note: current semantics assigns each object a unique type *)
  definition wf_problem where
    "wf_problem \<equiv>
      wf_domain
    \<and> (\<forall>a\<in>set (actions D). wf_action_schema a)
    \<and> distinct (map fst (objects P) @ map fst (consts D))
    \<and> (\<forall>(n,T)\<in>set (objects P). wf_type T)
    \<and> distinct (init P)
    \<and> wf_world_model (set (init P))
    \<and> wf_goal (goal P)
    "

  fun wf_effect_inst :: "object ast_effect \<Rightarrow> bool" where
    "wf_effect_inst (Effect (a) (d))
      \<longleftrightarrow> (\<forall>a\<in>set a \<union> set d. wf_fmla_atom objT a)"

  lemma wf_effect_inst_alt: "wf_effect_inst eff = wf_effect objT eff"
    by (cases eff) auto

end

sublocale ast_problem \<subseteq> quantifier_semantics term_atom_vars term_atom_objs term_atom_subst t_dom
  by (unfold_locales) (auto simp: subst_subst_all subst_replaces subst_idem)

thm ast_problem.objT_alt

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
  text \<open>This section proves that well-formedness under one type environment implies
        well-formedness under another.\<close>

  notation all    ("\<^bold>\<forall>_ - _._") 
  notation exists ("\<^bold>\<exists>_ - _._") 

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

  lemma list_all2_ty':
      fixes xs Ts
    assumes "\<forall>x \<in> set xs. Q x = R x" 
      shows "list_all2 (is_of_type Q) xs Ts = list_all2 (is_of_type R) xs Ts"
    using list_all2_ty assms by metis
  
  lemma same_type_imp_wf_atom_eq: 
    assumes same: "\<forall>e \<in> ent a. Q e = R e"
        and wf:   "wf_atom Q a"
      shows       "wf_atom R a"
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

 lemma same_type_imp_wf_fmla_eq: 
  assumes same: "\<forall>t \<in> \<Union>(ent ` atoms \<phi>). Q t = R t"
      and wf:   "wf_fmla Q \<phi>"
    shows       "wf_fmla R \<phi>"
   using assms same_type_imp_wf_atom_eq
   by (induction \<phi>) auto

  lemma wf_pred_atom_ent_typed: 
    assumes wf: "list_all2 (is_of_type Q) vs Ts"
    shows "\<forall>e \<in> set vs. \<exists>t. Q e = Some t"
  using assms
  apply (induction vs Ts rule: list_all2_induct)
  by (auto split: option.splits simp: is_of_type_def)
  
  lemma wf_imp_ent_typed:
    assumes wf: "wf_atom Q a"
    shows "\<forall>e \<in> ent a. \<exists>t. Q e = Some t"
    using wf wf_pred_atom_ent_typed
    apply (cases a) 
     apply (auto split: option.splits)[2]
    by blast
  
  lemma map_le_imp_same_type: 
    assumes le: "Q \<subseteq>\<^sub>m R" 
        and wf: "wf_atom Q a"
    shows "\<forall>e \<in> ent a. Q e = R e"
    using wf_imp_ent_typed[OF wf] map_leD le by fastforce

  lemma wf_atom_mono:
    assumes SS: "tys \<subseteq>\<^sub>m tys'"
    assumes WF: "wf_atom tys a"
    shows "wf_atom tys' a"
    using map_le_imp_same_type[OF SS WF] WF same_type_imp_wf_atom_eq
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
      by (cases "a" rule: wf_fmla_atom.cases) auto
    from wf_atom_mono[OF SS this(2)]
    show ?thesis by simp
  qed

  lemma wf_fmla_mono: 
    assumes "wf_fmla Q \<phi>"
            "Q \<subseteq>\<^sub>m R"
    shows   "wf_fmla R \<phi>"
    using wf_atom_mono[OF assms(2)] assms(1)
    by (induction \<phi>) auto

  lemma term_vars_restr_same_type: "\<forall>e \<in> ent a. (ty_term Q cT) e = 
    (ty_term (Q |` (term_atom_vars a)) cT) e"
  proof
    fix e
    assume "e \<in> ent a"
    hence "term_vars e \<subseteq> term_atom_vars a" using tav_alt by blast
    hence "(ty_term (Q |` (term_vars e)) cT) e = (ty_term (Q |` (term_atom_vars a)) cT) e" by (cases e) auto
    moreover
    have "(ty_term Q cT) e = (ty_term (Q |` (term_vars e)) cT) e" by (cases e) auto
    ultimately 
    show "(ty_term Q cT) e = (ty_term (Q |` (term_atom_vars a)) cT) e" by argo
  qed

  lemma restrict_union: "\<forall>e \<in> S. (Q |` S) e = (Q |` (S \<union> T)) e"
    unfolding restrict_map_def
    by (auto split: if_splits)

  lemma var_in_fmla_vars: "(term.VAR x) \<in> \<Union> (ent ` atoms \<phi>) \<Longrightarrow> x \<in> fvars \<phi>" 
    apply (induction \<phi>)
    using tav_alt by fastforce auto
  
  lemma wf_atom_restr: 
    assumes wf: "wf_atom (ty_term Q cT) a" 
      shows "wf_atom (ty_term (Q |` (term_atom_vars a)) cT) a"
    using same_type_imp_wf_atom_eq[OF term_vars_restr_same_type wf]
    .

  lemma fmla_vars_restr_same_type: "\<forall>e \<in> \<Union> (ent ` atoms \<phi>). (ty_term Q cT) e 
    = (ty_term (Q |` (fvars \<phi>)) cT) e"
  proof (induction \<phi>)
    case (Atom x)
    moreover have "\<Union> (ent ` atoms (Atom x)) = ent x" by simp
    moreover have "fvars (Atom x) = term_atom_vars x" by simp
    ultimately show ?case 
      using term_vars_restr_same_type
      by presburger
  next
    case (And \<phi>1 \<phi>2)
    thus ?case
      apply -
      apply (rule ballI)
      subgoal for e
      apply (cases e)
      using var_in_fmla_vars
      by fastforce+
    done
  next
    case (Or \<phi>1 \<phi>2)
    thus ?case
      apply -
      apply (rule ballI)
      subgoal for e
      apply (cases e)
      using var_in_fmla_vars
      by fastforce+
    done
  next
    case (Imp \<phi>1 \<phi>2)
    thus ?case
      apply -
      apply (rule ballI)
      subgoal for e
      apply (cases e)
      using var_in_fmla_vars
      by fastforce+
    done
  qed auto

  lemma wf_schematic_atom_vars: "wf_atom (ty_term Q cT) a \<Longrightarrow> term_atom_vars a \<subseteq> dom Q"
  proof (rule subsetI)
    fix v
    assume wf: "wf_atom (ty_term Q cT) a"
    assume "v \<in> term_atom_vars a"
    then obtain e where
      e: "e \<in> ent a" 
      "v \<in> term_vars e" 
      by (auto simp: tav_alt)
    hence "e = term.VAR v" by (cases e rule: term.exhaust) auto
    moreover
    have "ty_term Q cT e \<noteq> None" using e wf_imp_ent_typed wf by fastforce
    ultimately
    show "v \<in> dom Q" by auto
  qed

  text \<open>The type environment must contain a type for all free variables in a formula.\<close>
  lemma wf_fmla_vars: "wf_fmla (ty_term Q cT) \<phi> \<Longrightarrow> fvars \<phi> \<subseteq> dom Q"
    using wf_schematic_atom_vars
    by (induction \<phi>) auto
  
  lemma wf_fmla_restr': "wf_fmla (ty_term Q cT) \<phi> 
    \<Longrightarrow> wf_fmla (ty_term (Q |` (fvars \<phi>)) cT) \<phi>"
    using same_type_imp_wf_fmla_eq[OF fmla_vars_restr_same_type]
    by blast

  lemma wf_fmla_mono': 
    assumes "wf_fmla (ty_term Q cT) \<phi>"
            "Q \<subseteq>\<^sub>m R"
    shows   "wf_fmla (ty_term R cT) \<phi>"
    using wf_fmla_mono[OF assms(1) ty_term_mono[OF assms(2) map_le_refl[of cT]]]
    .

  lemma wf_fmla_restr: "wf_fmla (ty_term Q cT) \<phi> 
    \<longleftrightarrow> wf_fmla (ty_term (Q |` (fvars \<phi>)) cT) \<phi>"
    using wf_fmla_restr' wf_fmla_mono' map_restrict_less
    by blast
  
  lemma wf_fmla_bw: "Q \<subseteq>\<^sub>m R \<Longrightarrow> fvars \<phi> \<subseteq> dom Q
    \<Longrightarrow> wf_fmla (ty_term R cT) \<phi> \<longleftrightarrow> wf_fmla (ty_term Q cT) \<phi>"
    using wf_fmla_restr[of R] sym[OF wf_fmla_restr[of Q]] map_le_restr
    by metis
  
  lemma wf_fmla_alt_lemma: "Q \<subseteq>\<^sub>m R 
    \<Longrightarrow> wf_fmla (ty_term Q cT) \<phi> \<longleftrightarrow> wf_fmla (ty_term R cT) \<phi> \<and> fvars \<phi> \<subseteq> dom Q"
    using wf_fmla_mono wf_fmla_vars wf_fmla_bw 
    by blast
  
  theorem wf_goal_alt: "wf_goal \<phi> \<longleftrightarrow> wf_fmla (ty_term Q objT) \<phi> \<and> fvars \<phi> = {}"
    unfolding wf_goal_def
    using wf_fmla_alt_lemma[of "(\<lambda>_. None)"]
    by simp

  text \<open>Here are some lemmas reused in multiple well-formedness proofs for instantiation\<close>

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
    by (auto split: option.splits dest!: map_of_SomeD simp: in_set_conv_nth)

  context
    fixes Q::"'a \<rightharpoonup> type" and R::"'b \<rightharpoonup> type" and f :: "'a \<Rightarrow> 'b"
    assumes INST: "is_of_type Q x T \<Longrightarrow> is_of_type R (f x) T"
  begin
    lemma X1: assumes "list_all2 (is_of_type Q) xs Ts"
      shows "list_all2 (is_of_type R) (map f xs) Ts" 
      using assms INST by (induction rule: list_all2_induct) auto

    lemma wf_inst_eq_aux: "Q x = Some T \<Longrightarrow> R (f x) \<noteq> None"
      using INST[of x T] unfolding is_of_type_def
      by (auto split: option.splits)

    lemma wf_inst_atom:
      assumes "wf_atom Q a"
      shows "wf_atom R (map_atom f a)"
      using X1 assms wf_inst_eq_aux
      by (cases a; auto split: option.splits)

    lemma wf_inst_formula_atom:
      assumes "wf_fmla_atom Q a"
      shows "wf_fmla_atom R (map_formula (map_atom f) a)"
      using assms wf_inst_atom
      apply (cases a rule: wf_fmla_atom.cases; auto split: option.splits)
      by (simp add: INST list.rel_map(1) list_all2_mono)

    lemma wf_inst_effect:
      assumes "wf_effect Q \<phi>"
      shows "wf_effect R (map_ast_effect f \<phi>)"
      using assms wf_inst_formula_atom by (cases \<phi>) auto

    lemma wf_inst_formula:
      assumes "wf_fmla Q \<phi>"
      shows "wf_fmla R (map_formula (map_atom f) \<phi>)"
      using assms
      by (induction \<phi>) (auto simp: wf_inst_atom dest: wf_inst_eq_aux)
  end

  text \<open>The following section proves under which circumstances a quantified formula is well-formed\<close>
  
  lemma c_ty: "\<forall>c \<in> set (t_dom ty). \<exists>ty'. objT c = Some ty' \<and> of_type ty' ty"
  proof 
    fix c
    assume "c \<in> set (t_dom ty)"
    hence "c \<in> set (map fst (filter (\<lambda>(c, t) \<Rightarrow> of_type t ty) (consts D @ objects P)))"
      unfolding t_dom_def by blast
    hence "\<exists>t. (c,t) \<in> set (consts D @ objects P) \<and> of_type t ty"
      unfolding t_dom_def
      by auto
    then obtain t where
      t: "(c,t) \<in> set (consts D @ objects P)" 
      "of_type t ty"
      by auto
    from wf_problem
    have "distinct (map fst (consts D @ objects P))"
      unfolding wf_problem_def
      by auto
    with t
    have "map_of (consts D @ objects P) c = Some t"
      using map_of_is_SomeI
      by metis
    with t
    show "\<exists>ty'. objT c = Some ty' \<and> of_type ty' ty"
      using objT_alt
      by auto
  qed
  
  lemma quant_inst:
    assumes "c \<in> set (t_dom ty)"
        and "is_of_type (ty_term (Q(v\<mapsto>ty)) objT) t T" 
    shows "is_of_type (ty_term (Q(v:=None)) objT) (term_subst v c t) T"
  proof (cases t)
    case (VAR x)
    show ?thesis
    proof (cases "x = v")
      case True
      hence "ty_term (Q(v\<mapsto>ty)) objT t = Some ty \<and> of_type ty T" using VAR assms
        unfolding is_of_type_def by auto
      moreover 
      have "\<exists>ty'. ty_term (Q(v:=None)) objT (term_subst v c t) = Some ty' \<and> of_type ty' T"
        by (metis True VAR assms(1) ast_domain.of_type_trans calculation term_subst.simps(1) ty_term.simps(2) wf_ast_problem.c_ty wf_ast_problem_axioms)
      then show ?thesis unfolding is_of_type_def of_type_trans by force
    next
      case False
      thus ?thesis using VAR assms unfolding is_of_type_def by simp
    qed
  next
    case (CONST c)
    then show ?thesis using assms unfolding is_of_type_def by fastforce
  qed
  
  lemma wf_quant_inst': 
    assumes "wf_fmla (ty_term (Q(v \<mapsto> ty)) objT) \<phi>"
        and "c \<in> set (t_dom ty)"
      shows "wf_fmla (ty_term (Q(v := None)) objT) (map_formula (term_atom_subst v c) \<phi>)"
    using wf_inst_formula[OF quant_inst[OF assms(2)] assms(1)]
    by simp
  
  lemma wf_subst_t_dom:
    assumes "wf_fmla (ty_term (Q(v \<mapsto> ty)) objT) \<phi>"
    shows "list_all (wf_fmla (ty_term (Q(v := None)) objT)) 
        (map (\<lambda>c. map_formula (term_atom_subst v c) \<phi>) (t_dom ty))"
    using assms wf_quant_inst'
    by (subst sym[OF Ball_set], simp)
    
  lemma wf_fmla_upd: 
    assumes "v \<notin> fvars \<phi>"
      shows "wf_fmla (ty_term (Q(v \<mapsto> ty)) objT) \<phi> \<longleftrightarrow> wf_fmla (ty_term (Q(v := None)) objT) \<phi>"
    using wf_fmla_restr[of "Q(v \<mapsto> ty)"] wf_fmla_restr[of "Q(v := None)"] assms
    by simp
  
  lemma Big_Or_wf_comm: "list_all (wf_fmla Q) \<phi>s \<longleftrightarrow> wf_fmla Q (\<^bold>\<Or> \<phi>s)"
    by (induction \<phi>s) auto
  
  lemma Big_And_wf_comm: "list_all (wf_fmla Q) \<phi>s \<longleftrightarrow> wf_fmla Q (\<^bold>\<And> \<phi>s)"
    by (induction \<phi>s) auto
  
  lemma wf_Big_Or:
    assumes "wf_fmla (ty_term (Q(v \<mapsto> ty)) objT) \<phi>"
    shows "wf_fmla (ty_term (Q(v := None)) objT) 
      (\<^bold>\<Or>(map (\<lambda>c. (map_formula (term_atom_subst v c)) \<phi>) (t_dom ty)))"
    using wf_subst_t_dom[OF assms] Big_Or_wf_comm
    by blast
  
  lemma wf_Big_And:
    assumes "wf_fmla (ty_term (Q(v \<mapsto> ty)) objT) \<phi>"
    shows "wf_fmla (ty_term (Q(v := None)) objT) 
      (\<^bold>\<And>(map (\<lambda>c. (map_formula (term_atom_subst v c)) \<phi>) (t_dom ty)))"
    using wf_subst_t_dom[OF assms] Big_And_wf_comm
    by blast
  
  lemma wf_ex_inst':
    assumes "wf_fmla (ty_term (Q(v \<mapsto> ty)) objT) \<phi>" 
      shows "wf_fmla (ty_term (Q(v := None)) objT) \<^bold>\<exists>v - ty. \<phi>"
    using wf_Big_Or[OF assms] wf_fmla_upd assms by auto
  
  lemma wf_ex_inst:
    assumes "wf_fmla (ty_term (Q(v \<mapsto> ty)) objT) \<phi>" 
      shows "wf_fmla (ty_term Q objT) \<^bold>\<exists>v - ty. \<phi>"
    using wf_fmla_mono'[OF wf_ex_inst'] assms by auto

  
  (* Note: The other direction does not work. Quantifiers expand into long formulae 
            by substitution of variables for constants. Assume there is a 
            predicate P:: t2 \<Rightarrow> bool, that v has a type of t1, that t2 \<subseteq> t1, and the only
            object in the domain of t1 has a type t2. In this case, P is not
            well-formed. *)
  
  lemma wf_ex_goal: 
    assumes "wf_fmla (ty_term [v \<mapsto> ty] objT) \<phi>" 
      shows "wf_goal \<^bold>\<exists>v - ty. \<phi>"
    unfolding wf_goal_def using wf_ex_inst'[OF assms] by simp

  lemma wf_ex_goal_alt:
    assumes "wf_fmla (ty_term (Q(v \<mapsto> ty)) objT) \<phi>"
        and "fvars \<phi> \<subseteq> {v}"
      shows "wf_goal \<^bold>\<exists>v - ty. \<phi>"
    using assms wf_fmla_alt_lemma[of "Map.empty(v \<mapsto> ty)" "(Q(v \<mapsto> ty))"] wf_ex_goal by simp
    
    
  lemma wf_univ_inst':
    assumes "wf_fmla (ty_term (Q(v \<mapsto> ty)) objT) \<phi>" 
      shows "wf_fmla (ty_term (Q(v := None)) objT) \<^bold>\<forall>v - ty. \<phi>"
    using wf_Big_And[OF assms] wf_fmla_upd assms by auto
  
  lemma wf_univ_inst:
    assumes "wf_fmla (ty_term (Q(v \<mapsto> ty)) objT) \<phi>" 
      shows "wf_fmla (ty_term Q objT) \<^bold>\<forall>v - ty. \<phi>"
    using wf_fmla_mono'[OF wf_univ_inst'] assms by auto
  
  lemma wf_univ_goal: 
    assumes "wf_fmla (ty_term [v \<mapsto> ty] objT) \<phi>" 
      shows "wf_goal \<^bold>\<forall>v - ty. \<phi>"
    unfolding wf_goal_def using wf_univ_inst'[OF assms] by simp

   lemma wf_univ_goal_alt:
    assumes "wf_fmla (ty_term (Q(v \<mapsto> ty)) objT) \<phi>"
        and "fvars \<phi> \<subseteq> {v}"
      shows "wf_goal \<^bold>\<forall>v - ty. \<phi>"
    using assms wf_fmla_alt_lemma[of "Map.empty(v \<mapsto> ty)" "(Q(v \<mapsto> ty))"] wf_univ_goal by simp

end \<comment> \<open>locale \<open>wf_ast_problem\<close>\<close>

subsection \<open>PDDL Semantics\<close>

(* Semantics *)

(*  To apply plan_action:
    find action schema, instantiate, check precond, apply effect
*)



context ast_domain begin

  definition resolve_action_schema :: "name \<rightharpoonup> ast_action_schema" where
    "resolve_action_schema n = index_by ast_action_schema.name (actions D) n"

  fun subst_term where
    "subst_term psubst (term.VAR x) = psubst x"
  | "subst_term psubst (term.CONST c) = c"

 text \<open>To instantiate an action schema, we first compute a substitution from
    parameters to objects, and then apply this substitution to the
    precondition and effect. The substitution is applied via the \<open>map_xxx\<close>
    functions generated by the datatype package.
    \<close>

  fun tsubst where
  "tsubst params args = subst_term (the o (map_of (zip (map fst params) args)))"

  fun inst_pre where
  "inst_pre t pre = (map_formula o map_atom) t pre" 
  
  fun instantiate_action_schema
    :: "ast_action_schema \<Rightarrow> object list \<Rightarrow> ground_action"
  where
    "instantiate_action_schema (Action_Schema n params pre eff) args = (let
        tsubst = tsubst params args;
        pre_inst = inst_pre tsubst pre;
        eff_inst = (map_ast_effect) tsubst eff
      in
        Ground_Action pre_inst eff_inst
      )"

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>


context wf_ast_problem begin

  text \<open>Initial model\<close>
  definition I :: "world_model" where
    "I \<equiv> set (init P)"

  text \<open>Resolve a plan action and instantiate the referenced action schema.\<close>
  fun resolve_instantiate :: "plan_action \<Rightarrow> ground_action" where
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
      action with valid objects yield a valid effect.
  \<close>

  text \<open>A sequence of plan actions form a path, if they are well-formed and
    their instantiations form a path.\<close>
  definition plan_action_path
    :: "world_model \<Rightarrow> plan_action list \<Rightarrow> world_model \<Rightarrow> bool"
  where
    "plan_action_path M \<pi>s M' =
        ((\<forall>\<pi> \<in> set \<pi>s. wf_plan_action \<pi>)
      \<and> ground_action_path M (map resolve_instantiate \<pi>s) M')"

  text \<open>Instantiation of a goal\<close>
  fun inst_goal::"schematic_formula \<Rightarrow> ground_formula" where
  "inst_goal \<phi> = (let tsubst = subst_term (the o (Map.empty))
        in (map_formula o map_atom) tsubst \<phi>)"                           
  
  text \<open>A plan is valid wrt.\ a given initial model, if it forms a path to a
    goal model \<close>
  definition valid_plan_from :: "world_model \<Rightarrow> plan \<Rightarrow> bool" where
    "valid_plan_from M \<pi>s = (\<exists>M'. plan_action_path M \<pi>s M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= inst_goal (goal P))"
  (* instantiate the goal wrt nothing *)
  (* Implementation note: resolve and instantiate already done inside
      enabledness check, redundancy! *)

  text \<open>Finally, a plan is valid if it is valid wrt.\ the initial world
    model @{const I}\<close>
  definition valid_plan :: "plan \<Rightarrow> bool"
    where "valid_plan \<equiv> valid_plan_from I"

  text \<open>Concise definition used in paper:\<close>
  lemma "valid_plan \<pi>s \<equiv> \<exists>M'. plan_action_path I \<pi>s M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= inst_goal (goal P)"
    unfolding valid_plan_def valid_plan_from_def by auto


end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>



subsection \<open>Preservation of Well-Formedness\<close>

subsubsection \<open>Well-Formed Action Instances\<close>
text \<open>The goal of this section is to establish that well-formedness of
  world models is preserved by execution of well-formed plan actions.
\<close>
             
context wf_ast_problem begin

  text \<open>As plan actions are executed by first instantiating them, and then
    executing the action instance, it is natural to define a well-formedness
    concept for action instances.\<close>

  fun wf_ground_action :: "ground_action \<Rightarrow> bool" where
    "wf_ground_action (Ground_Action pre eff) \<longleftrightarrow> (
        wf_fmla objT pre
      \<and> wf_effect objT eff
      )
    "

  text \<open>We first prove that instantiating a well-formed action schema will yield
    a well-formed action instance.

    We begin with some auxiliary lemmas before the actual theorem.
  \<close>
                    
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
    fixes Q and f :: "variable \<Rightarrow> object"
    assumes INST: "is_of_type Q x T \<Longrightarrow> is_of_type objT (f x) T"
  begin

    lemma is_of_type_var_conv: "is_of_type (ty_term Q objT) (term.VAR x) T  \<longleftrightarrow> is_of_type Q x T"
      unfolding is_of_type_def by (auto)

    lemma is_of_type_const_conv: "is_of_type (ty_term Q objT) (term.CONST x) T  \<longleftrightarrow> is_of_type objT x T"
      unfolding is_of_type_def
      by (auto split: option.split)

    lemma INST': "is_of_type (ty_term Q objT) x T \<Longrightarrow> is_of_type objT (subst_term f x) T"
      using INST by (cases x) (auto simp: is_of_type_var_conv is_of_type_const_conv)

  end

  text \<open>Instantiating a well-formed goal will result in a well-formed formula\<close>
  theorem wf_instantiate_goal:
    assumes "wf_goal \<phi>"
    shows "wf_fmla objT (inst_goal \<phi>)"
  proof -
    let ?f = "(the \<circ> Map.empty)"
    have INST: "is_of_type objT (?f x) T"
      if "is_of_type (Map.empty) x T" for x T
      using that 
      unfolding is_of_type_def
      by (auto split: option.splits)
    have INST': "is_of_type objT (subst_term ?f x) T"
      if "is_of_type (ty_term Map.empty objT) x T" for x T
      using INST'[OF INST that] .
    from wf_inst_formula[OF this] assms
    show ?thesis by (fastforce split: term.splits simp: Let_def comp_apply[abs_def] wf_goal_def)
  qed

  text \<open>Instantiating a well-formed action schema with compatible arguments
    will yield a well-formed action instance.
  \<close>
  theorem wf_instantiate_action_schema:
    assumes "action_params_match a args"
    assumes "wf_action_schema a"
    shows "wf_ground_action (instantiate_action_schema a args)"
  proof (cases a)
    case [simp]: (Action_Schema name params pre eff)
    let ?f = "the \<circ> map_of (zip (map fst params) args)"
    have INST:
      "is_of_type objT (?f x) T"
      if "is_of_type (map_of params) x T" for x T
      using that
      apply (rule is_of_type_map_ofE)
      using assms
      apply (clarsimp simp: Let_def)
        apply (thin_tac "wf_fmla (ty_term (map_of params) objT) pre")
        apply (thin_tac "wf_effect (ty_term (map_of params) objT) eff")
      subgoal for i xT
        unfolding action_params_match_def
        thm lookup_zip_idx_eq
        apply (subst lookup_zip_idx_eq[where i=i];
          (clarsimp simp: list_all2_lengthD)?)
        thm list_all2_nthD2
        apply (frule list_all2_nthD2[where p=i]; simp?)
        apply (auto
                simp: is_obj_of_type_alt is_of_type_def
                intro: of_type_trans
                split: option.splits)
        done
      done
    have INST': "is_of_type objT (tsubst params args x) T"
      if "is_of_type (ty_term (map_of params) objT) x T" for x T
      using INST INST' that by fastforce
    from wf_inst_formula[OF this] wf_inst_effect[OF this] assms(2)
    show ?thesis
      by (fastforce split: term.splits simp: Let_def comp_apply[abs_def])
  qed

  text \<open>The semantics of quantifiers in preconditions and the goal 
        will behave as expected\<close>
  
  context 
    fixes f::"schematic_formula \<Rightarrow> ground_formula"
      and \<A>::"object atom valuation"
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

    lemma all_inst: "\<A> \<Turnstile> (f \<^bold>\<forall>v - ty. \<phi>) \<longleftrightarrow>
      (\<forall>c \<in> set (t_dom ty). \<A> \<Turnstile> f (map_formula (term_atom_subst v c) \<phi>))"
    proof cases
      assume a: "v \<notin> fvars \<phi> \<and> t_dom ty \<noteq> []"
      hence "\<^bold>\<forall>v - ty. \<phi> = \<phi>" by auto
      hence "\<A> \<Turnstile> (f \<^bold>\<forall>v - ty. \<phi>) \<longleftrightarrow> \<A> \<Turnstile> f \<phi>" by presburger
      moreover from a
      have "\<forall>c. map_formula (term_atom_subst v c) \<phi> = \<phi>" using subst_idem fvars_alt by (simp add: formula.map_ident_strong)
      hence "(\<forall>c\<in>set (t_dom ty). \<A> \<Turnstile> f \<phi>) \<longleftrightarrow> (\<forall>c\<in>set (t_dom ty). \<A> \<Turnstile> f (map_formula (term_atom_subst v c) \<phi>))" by simp
      ultimately show ?thesis using a by blast
    next
      assume "\<not>(v \<notin> fvars \<phi> \<and> t_dom ty \<noteq> [])"
      hence "\<A> \<Turnstile> (f \<^bold>\<forall>v - ty. \<phi>) \<longleftrightarrow> \<A> \<Turnstile> (f \<^bold>\<And>(map (\<lambda>c. map_formula (term_atom_subst v c) \<phi>) (t_dom ty)))" by force
      also have "... \<longleftrightarrow> (\<forall>\<phi> \<in> set (map (\<lambda>c. map_formula (term_atom_subst v c) \<phi>) (t_dom ty)). \<A> \<Turnstile> f \<phi>)" using Big_And_sem by blast
      also have "... \<longleftrightarrow> (\<forall>c \<in> set (t_dom ty). \<A> \<Turnstile> f (map_formula (term_atom_subst v c) \<phi>))" by auto
      finally show ?thesis .
    qed

    lemma ex_inst: "\<A> \<Turnstile> (f \<^bold>\<exists>v - ty. \<phi>) \<longleftrightarrow>
      (\<exists>c \<in> set (t_dom ty). \<A> \<Turnstile> f (map_formula (term_atom_subst v c) \<phi>))"
    proof cases
      assume a: "v \<notin> fvars \<phi> \<and> t_dom ty \<noteq> []"
      hence "\<A> \<Turnstile> (f \<^bold>\<exists>v - ty. \<phi>) \<longleftrightarrow> \<A> \<Turnstile> f \<phi>" by auto
      moreover from a
      have "\<forall>c. map_formula (term_atom_subst v c) \<phi> = \<phi>" using subst_idem fvars_alt by (simp add: formula.map_ident_strong)
      hence "(\<exists>c\<in>set (t_dom ty). \<A> \<Turnstile> f \<phi>) \<longleftrightarrow> (\<exists>c\<in>set (t_dom ty). \<A> \<Turnstile> f (map_formula (term_atom_subst v c) \<phi>))" by simp
      ultimately show ?thesis using a by blast
    next
      assume "\<not>(v \<notin> fvars \<phi> \<and> t_dom ty \<noteq> [])"
      hence "\<A> \<Turnstile> (f \<^bold>\<exists>v - ty. \<phi>) \<longleftrightarrow> \<A> \<Turnstile> (f \<^bold>\<Or>(map (\<lambda>c. map_formula (term_atom_subst v c) \<phi>) (t_dom ty)))" by force
      also have "... \<longleftrightarrow> (\<exists>\<phi> \<in> set (map (\<lambda>c. map_formula (term_atom_subst v c) \<phi>) (t_dom ty)). \<A> \<Turnstile> f \<phi>)" using Big_Or_sem by blast
      also have "... \<longleftrightarrow> (\<exists>c \<in> set (t_dom ty). \<A> \<Turnstile> f (map_formula (term_atom_subst v c) \<phi>))" by auto
      finally show ?thesis .
    qed
  end

  lemma inst_goal_all_sem: "valuation M \<Turnstile> (inst_goal \<^bold>\<forall>v - ty. \<phi>) \<longleftrightarrow>
        (\<forall>c \<in> set (t_dom ty). valuation M \<Turnstile> inst_goal (map_formula (term_atom_subst v c) \<phi>))"
  proof -
    have "\<exists>f'. inst_goal = map_formula f'" by force
    thus ?thesis using all_inst by blast
  qed

  lemma inst_goal_ex_sem: "valuation M \<Turnstile> (inst_goal \<^bold>\<exists>v - ty. \<phi>) \<longleftrightarrow>
        (\<exists>c \<in> set (t_dom ty). valuation M \<Turnstile> inst_goal (map_formula (term_atom_subst v c) \<phi>))"
  proof -
    have "\<exists>f'. inst_goal = map_formula f'" by force
    thus ?thesis using ex_inst by blast
  qed

  lemma inst_pre_ex_sem:
      assumes "a = Action_Schema n params (\<^bold>\<exists>v - ty. \<phi>) eff"
      assumes "action_params_match a args"
      assumes "Ground_Action pre_inst eff_inst = instantiate_action_schema a args"
      shows "pre_inst = inst_pre (tsubst params args) (\<^bold>\<exists>v - ty. \<phi>) \<and> 
          valuation M \<Turnstile> pre_inst \<longleftrightarrow> (\<exists>c \<in> set (t_dom ty). 
            valuation M \<Turnstile> inst_pre (tsubst params args) (map_formula (term_atom_subst v c) \<phi>))"
  proof -
    have "\<exists>f'. inst_pre (tsubst params args) = map_formula f'" by fastforce
    moreover have "pre_inst = inst_pre (tsubst params args) (\<^bold>\<exists>v - ty. \<phi>)" using assms by (auto simp: Let_def)
    ultimately show ?thesis using ex_inst[where f = "inst_pre (tsubst params args)"] by blast
  qed
  
  lemma inst_pre_all_sem:
      assumes "a = Action_Schema n params (\<^bold>\<forall>v - ty. \<phi>) eff"
      assumes "action_params_match a args"
      assumes "Ground_Action pre_inst eff_inst = instantiate_action_schema a args"
      shows "pre_inst = inst_pre (tsubst params args) (\<^bold>\<forall>v - ty. \<phi>) \<and> 
          valuation M \<Turnstile> pre_inst \<longleftrightarrow> (\<forall>c \<in> set (t_dom ty). 
            valuation M \<Turnstile> inst_pre (tsubst params args) (map_formula (term_atom_subst v c) \<phi>))"
  proof -
    have "\<exists>f'. inst_pre (tsubst params args) = map_formula f'" by fastforce
    moreover have "pre_inst = inst_pre (tsubst params args) (\<^bold>\<forall>v - ty. \<phi>)" using assms by (auto simp: Let_def)
    ultimately show ?thesis using all_inst[where f = "inst_pre (tsubst params args)"] by blast
  qed
end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>

subsubsection \<open>Preservation\<close>

context wf_ast_problem begin

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
            execute_ground_action_def plan_action_enabled_def)



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
    assumes "wf_effect objT e"
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
    with wf_problem have "wf_action_schema a"
      unfolding wf_problem_def by auto
    hence "wf_ground_action (resolve_instantiate \<pi>)"
      using \<open>resolve_action_schema name = Some a\<close> T
        wf_instantiate_action_schema
      by auto
    thus ?thesis
      apply (simp add: execute_plan_action_def execute_ground_action_def)
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
    assumes "wf_world_model M" and "plan_action_path M \<pi>s M'"
    shows "wf_world_model M'"
    using assms
    by (induction \<pi>s arbitrary: M) (auto intro: wf_execute)


end \<comment> \<open>Context of \<open>wf_ast_problem\<close>\<close>




end \<comment> \<open>Theory\<close>
