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

definition schematic_term_atom_vars where
"schematic_term_atom_vars \<equiv> ent o (map_atom (the o (\<lambda>(term.VAR x) \<Rightarrow> Some x | _ \<Rightarrow> None)))"

global_interpretation schematic_formula_syntax: 
  formula_syntax schematic_term_atom_subst schematic_term_atom_vars
  defines free_vars = schematic_formula_syntax.free_vars
  .

(* These are needed to interpret syntax and semantics of instantiated formulae *)
fun inst_term_subst::"variable \<Rightarrow> object \<Rightarrow> inst_term \<Rightarrow> inst_term" where
  "inst_term_subst v obj (inst_term.VAR x) = (if (x = v) then (inst_term.OBJ obj) else inst_term.VAR x)" 
| "inst_term_subst _ _ (inst_term.OBJ obj) = inst_term.OBJ obj"

abbreviation inst_term_atom_subst where
"inst_term_atom_subst v obj \<equiv> map_atom (inst_term_subst v obj)"

definition inst_term_atom_vars::"inst_term atom \<Rightarrow> variable set" where
"inst_term_atom_vars \<equiv> \<Union> o ent o (map_atom (\<lambda>(inst_term.VAR x) \<Rightarrow> {x} | _ \<Rightarrow> {}))"

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
  .

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
    apply (auto 0 3) (* no blast 0 but instead more general solver 3 in more depth *)
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
    apply (auto simp: valuation_def intro!: ext split: atom.split)
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
    (* How did you find the next step? *)
    apply (metis in_close_world_conv valuation_aux_2)
    using in_close_world_conv valuation_aux_2 apply blast
    using in_close_world_conv valuation_aux_2 by auto
  
  thm bspec
  
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


fun ty_term::"(variable \<Rightarrow> type option) \<Rightarrow> (object \<Rightarrow> type option) \<Rightarrow> term \<Rightarrow> type option" where
  "ty_term varT objT (term.VAR v) = varT v"
| "ty_term varT objT (term.CONST c) = objT c"

definition upd_te::"(term \<Rightarrow> type option) \<Rightarrow> variable \<Rightarrow> type \<Rightarrow> term \<Rightarrow> type option" where
"upd_te te var ty \<equiv> 
  \<lambda>(term.VAR v) \<Rightarrow> (if (v = var) then Some ty else te (term.VAR v)) |
  (term.CONST c) \<Rightarrow> te (term.CONST c)"


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

definition upd_gt_te::"(inst_term \<Rightarrow> type option) \<Rightarrow> variable \<Rightarrow> type \<Rightarrow> inst_term \<Rightarrow> type option" where
"upd_gt_te te var ty \<equiv> 
  \<lambda>(inst_term.VAR v) \<Rightarrow> (if (v = var) then Some ty else te (inst_term.VAR v)) |
  (inst_term.OBJ c) \<Rightarrow> te (inst_term.OBJ c)"


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
    \<and> wf_fmla upd_gt_te (ty_inst_term (\<lambda>_.None) objT) (goal P)
    "



  definition wf_inst_fmla::"inst_formula \<Rightarrow> bool" where
  "wf_inst_fmla f \<equiv> (wf_fmla upd_gt_te (ty_inst_term (\<lambda>_. None) objT) f \<and> free_vars f = {})"
  (* Effects are atomic predicate, which also makes them quantifier-free and thus
     actually ground. Maybe effects should use the object atom type, while preconditions
     should use the "ground" (instantiated) type. *)
  fun wf_effect_inst :: "inst_effect \<Rightarrow> bool" where
    "wf_effect_inst (Effect (a) (d))
      \<longleftrightarrow> (\<forall>a\<in>set a \<union> set d. wf_inst_fmla  a)"
                                          
(* lemma wf_effect_inst_alt: 
  "wf_effect_inst eff = (wf_effect (ty_inst_term (\<lambda>_. None) objT) eff 
    \<and> eff = Effect add del \<and> (\<forall> a \<in> set add. free_vars a = {}) \<and> (\<forall> d \<in> set del. free_vars d = {}))"
  apply (auto simp: wf_inst_fmla_def) *)

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

  fun subst_term::"(variable \<Rightarrow> object) \<Rightarrow> term \<Rightarrow> (object)" where
    "subst_term psubst (term.VAR x) = psubst x"
  | "subst_term psubst (term.CONST c) = c"

  fun ground::"(variable \<Rightarrow> inst_term) \<Rightarrow> term \<Rightarrow> inst_term" where
    "ground psubst (term.VAR x) = psubst x" 
  | "ground psubst (term.CONST obj) = inst_term.OBJ obj"

  (* Not every variable is mapped to an object. Some are left *)
  text \<open>A capture-avoiding map from schematic_formulas to instantiated formulas\<close>

  fun cap_avoid_map::"(term \<Rightarrow> inst_term) \<Rightarrow> schematic_formula \<Rightarrow> inst_formula"
    where
    "cap_avoid_map f (Atom x) = Atom (map_atom f x)"
  | "cap_avoid_map f \<bottom> = \<bottom>"
  | "cap_avoid_map f (\<^bold>\<not>f1) = \<^bold>\<not> (cap_avoid_map f f1)"
  | "cap_avoid_map f (f1 \<^bold>\<and> f2) = cap_avoid_map f f1 \<^bold>\<and> cap_avoid_map f f2"
  | "cap_avoid_map f (f1 \<^bold>\<or> f2) = cap_avoid_map f f1 \<^bold>\<or> cap_avoid_map f f2"
  | "cap_avoid_map f (f1 \<^bold>\<rightarrow> f2) = cap_avoid_map f f1 \<^bold>\<rightarrow> cap_avoid_map f f2"
  | "cap_avoid_map f (\<^bold>\<exists>\<^sub>T x. f1) = (\<^bold>\<exists>\<^sub>T x. (cap_avoid_map (f(term.VAR x := inst_term.VAR x)) f1))"
  | "cap_avoid_map f (\<^bold>\<forall>\<^sub>T x. f1) = (\<^bold>\<forall>\<^sub>T x. (cap_avoid_map (f(term.VAR x := inst_term.VAR x)) f1))"

  (* Because the types have multiple parameters, each needs a mapping. 
      Therefore we use the identity function for the other types *)
  fun instantiate_action_schema
    :: "ast_action_schema \<Rightarrow> object list \<Rightarrow> inst_action"
  where
    "instantiate_action_schema (Action_Schema n params pre (Effect add del)) args = (let
        tsubst = ground (the o (map_of (zip (map fst params) (map inst_term.OBJ args))));
        pre_inst = cap_avoid_map tsubst pre;
        eff_inst = Effect (map (cap_avoid_map tsubst) add) (map (cap_avoid_map tsubst) del)
      in
        Inst_Action pre_inst eff_inst
      )"

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

  definition wf_inst_fmla::"inst_formula \<Rightarrow> bool" where
  "wf_inst_fmla f \<equiv> (wf_fmla upd_gt_te (ty_inst_term (\<lambda>_. None) objT) f \<and> free_vars f = {})"

  fun wf_inst_action :: "inst_action \<Rightarrow> bool" where
    "wf_inst_action (Inst_Action pre eff) \<longleftrightarrow> (
        wf_inst_fmla pre
      \<and> wf_effect (ty_inst_term (\<lambda>_. None) objT) eff
      )
    "

  (* TODO: interpret the formula_syntax for schematic_formulas *)
  
  

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

  thm is_of_type_map_ofE

  find_theorems name: "option*case"

  find_theorems name: "case*option"

  find_theorems name: "option"
  find_theorems "?a = ?c \<Longrightarrow> ?b = ?d \<Longrightarrow> ?c \<noteq> ?d \<Longrightarrow> ?a \<noteq> ?b"
  lemma "Some x \<noteq> None" using option.simps(3) .


  lemma list_all_mono:
    fixes xs Ts 
    assumes SS: "tys \<subseteq>\<^sub>m tys'"
        and "list_all2 (is_of_type tys) xs Ts" 
      shows "list_all2 (is_of_type tys') xs Ts"
  proof - 
    have "list_all2 (is_of_type tys') xs Ts" 
      if "list_all2 (is_of_type tys) xs Ts" for xs Ts
      using that
    proof (induction xs Ts rule: list_all2_induct)
      case Nil
      then show ?case by simp
    next
      case (Cons x t xs ts)
      hence "is_of_type tys' x t" 
        using map_leD is_of_type_def SS
        by (smt (verit, del_insts) case_optionE)
      thus ?case 
        using \<open>list_all2 (is_of_type tys') xs ts\<close> list_all2_def 
        by auto
    qed
    with assms show ?thesis by auto
  qed

  lemma wf_atom_mono:
    assumes SS: "tys \<subseteq>\<^sub>m tys'"
    assumes WF: "wf_atom tys a"
    shows "wf_atom tys' a"
  proof -
    from list_all_mono[OF SS] WF show ?thesis
      by (cases a) (auto split: option.splits dest: map_leD[OF SS])
  qed

  lemma wf_fmla_atom_mono:
    assumes SS: "tys \<subseteq>\<^sub>m tys'"
    assumes WF: "wf_fmla_atom tys a"
    shows "wf_fmla_atom tys' a"
  proof -
    from list_all_mono[OF SS] WF show ?thesis
      by (cases "(tys, a)" rule: wf_fmla_atom.cases) 
        (auto split: option.splits dest: map_leD[OF SS])
  qed
                                    
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
    fixes Q and f :: "variable \<Rightarrow> inst_term"
    assumes INST: "is_of_type Q x T \<Longrightarrow> is_of_type (ty_inst_term (\<lambda>_. None) objT) (f x) T"
  begin 

    (* f is the manner in which parameters are substituted for arguments *)

    (* if f x is none, then the ground formula must leave it as a variable *)
  
    
    lemma is_of_type_var_conv: "is_of_type (ty_term Q objT) (term.VAR x) T  \<longleftrightarrow> is_of_type Q x T"
      unfolding is_of_type_def by (auto)

    lemma is_of_type_const_conv: "is_of_type (ty_term Q objT) (term.CONST x) T  \<longleftrightarrow> is_of_type objT x T"
      unfolding is_of_type_def
      by (auto split: option.split)

    lemma INST': "is_of_type (ty_term Q objT) x T \<Longrightarrow> is_of_type (ty_inst_term (\<lambda>_. None) objT) (ground f x) T"
      apply (cases x) using INST 
      apply auto
       apply (simp add: ast_domain.is_of_type_def)
      by (simp add: is_of_type_def)

    lemma wf_inst_eq_aux: "Q x = Some T \<Longrightarrow> ty_inst_term (\<lambda>_. None) objT (f x) \<noteq> None"
      using INST[of x T] unfolding is_of_type_def
      by (auto split: option.splits)

    lemma wf_inst_eq_aux1: "Q x = Some T \<Longrightarrow>\<exists>T'. ty_inst_term (\<lambda>_. None) objT (f x) = Some T' \<and> of_type T' T"
    proof -
      assume "Q x = Some T"
      hence "is_of_type Q x T" unfolding is_of_type_def by simp
      from this[THEN INST] have "is_of_type (ty_inst_term (\<lambda>_. None) objT) (f x) T" .
      then obtain T' where
        "ty_inst_term (\<lambda>_. None) objT (f x) = Some T'" 
        "of_type T' T"
        unfolding is_of_type_def
        by (auto split: option.splits)
      thus ?thesis
        by auto
    qed

    lemma wf_inst_eq_aux': "ty_term Q objT x = Some T \<Longrightarrow> ty_inst_term (\<lambda>_. None) objT (ground f x) \<noteq> None"
      apply (cases x) 
      by (auto simp: wf_inst_eq_aux split: option.split)

    lemma wf_inst_atom:
      assumes "wf_atom (ty_term Q constT) a"
      shows "wf_atom (ty_inst_term (\<lambda>_. None) objT) ((map_atom o ground) f a)"
    proof -
      have X1: "list_all2 (is_of_type (ty_inst_term (\<lambda>_. None) objT)) (map (ground f) xs) Ts" if
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
      shows "wf_fmla_atom (ty_inst_term (\<lambda>_. None) objT) ((cap_avoid_map o ground) f a)"
      using assms[THEN wf_fmla_atom_constT_imp_objT] wf_inst_atom
      apply (cases "((ty_term Q constT), a)" rule: wf_fmla_atom.cases; auto split: option.splits)
      by (simp add: INST' list.rel_map(1) list_all2_mono)

    lemma wf_inst_effect:
      assumes "wf_effect (ty_term Q constT) (Effect add del)"
      shows "wf_effect (ty_inst_term (\<lambda>_. None) objT) (Effect ((map o cap_avoid_map o ground) f add) ((map o cap_avoid_map o ground) f del))"
      using assms
      proof (induction "(Effect add del)")
        case (Effect)
        then show ?case using wf_inst_formula_atom by auto
      qed

    lemma wf_atom_no_vars: 
      assumes a: "wf_atom (ty_inst_term (\<lambda>_. None) objT) it" (is "wf_atom ?ty_ent it")
      shows "inst_term_atom_vars it = {}" (is "?vars it = {}")
    proof (cases it)
      fix p vs
      assume it: "it = predAtm p vs"
      with a have "wf_pred_atom ?ty_ent (p, vs)" by auto
      then obtain Ts where
        "sig p = Some Ts"
        "list_all2 (is_of_type ?ty_ent) vs Ts"
        using case_optionE by force
      find_theorems name: "list_all2*"
      hence b: "\<forall>i<length vs. (is_of_type ?ty_ent) (vs ! i) (Ts ! i)"
        using list_all2_conv_all_nth by auto
      have "\<And>i. i < length vs \<Longrightarrow> \<exists>v'. (vs ! i) = inst_term.OBJ v'"
      proof -
        fix i
        assume "i < length vs"
        hence "is_of_type ?ty_ent (vs ! i) (Ts ! i)" using b by simp
        hence "?ty_ent (vs ! i) \<noteq> None" 
          by (metis is_of_type_def option.simps(4))
        thus "\<exists>v'. (vs ! i) = inst_term.OBJ v'" by (metis ty_inst_term.elims)
      qed
      hence "\<forall>i < length vs. \<exists>v'. (vs ! i) = inst_term.OBJ v'" by auto
      hence "\<forall>v \<in> set vs. \<exists>v'. v = inst_term.OBJ v'"
        by (metis in_set_conv_nth)
      then show ?thesis  
        using it 
        unfolding inst_term_atom_vars_def 
        by (auto split: option.splits)
    next
      fix a b
      assume it: "it = Eq a b"
      with a have "?ty_ent a \<noteq> None" "?ty_ent b \<noteq> None" by auto
      hence "\<exists>a'. a = inst_term.OBJ a' \<and> objT a' \<noteq> None" 
            "\<exists>b'. b = inst_term.OBJ b' \<and> objT b' \<noteq> None" 
        by (metis ty_inst_term.elims)+
      then obtain a' b' where
        "a = inst_term.OBJ a'"
        "b = inst_term.OBJ b'" 
        by auto
      with it have "it = Eq (inst_term.OBJ a') (inst_term.OBJ b')" by simp
      then show ?thesis using it unfolding inst_term_atom_vars_def by (auto split: option.splits)
    qed

    lemma wf_inst_formula:
      assumes "wf_fmla upd_te (ty_term Q constT) \<phi>"
      shows "wf_inst_fmla ((cap_avoid_map o ground) f \<phi>)"
      using assms
    proof (induction \<phi>)
      case (Atom x)
      hence "wf_atom (ty_term Q constT) x" by auto
      hence 1: "wf_atom (ty_inst_term (\<lambda>_. None) objT) ((map_atom o ground) f x)" 
        using wf_inst_atom by auto
      hence "wf_fmla upd_gt_te (ty_inst_term (\<lambda>_. None) objT) ((cap_avoid_map o ground) f (Atom x))" by auto
      then show ?case unfolding wf_inst_fmla_def 
        using 1 wf_atom_no_vars by auto
    next
      case (Exists x1a x2 \<phi>)
      (* can't work *)
      then show ?case sorry
    next
      case (All x1a x2 \<phi>)
      then show ?case sorry
    qed (auto simp add: wf_inst_fmla_def)
  end



  text \<open>Instantiating a well-formed action schema with compatible arguments
    will yield a well-formed action instance.
  \<close>
  theorem wf_instantiate_action_schema:
    assumes "action_params_match a args"
    assumes "wf_action_schema a"
    shows "wf_inst_action (instantiate_action_schema a args)"
  proof (cases a)
    case [simp]: (Action_Schema name params pre eff)
    have INST:
      "is_of_type (ty_inst_term (\<lambda>_. None) objT) ((the \<circ> (map_of (zip (map fst params) (map inst_term.OBJ args)))) x) T"
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
    then show ?thesis
      using assms(2) wf_inst_formula wf_inst_effect
      by (fastforce split: term.sp lits simp: Let_def comp_apply[abs_def])
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
