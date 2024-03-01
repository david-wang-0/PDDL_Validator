section \<open>PDDL and STRIPS Semantics\<close>
theory PDDL_STRIPS_Semantics
imports
  "Propositional_Proof_Systems.Formulas"
  "Propositional_Proof_Systems.Sema"
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

datatype func = Func (name: name)


text \<open>Variables are identified by their names.\<close>
datatype variable = varname: Var name

text \<open>Objects and constants are identified by their names. term \<open>Undef\<close> is mainly
      used to represent updates to object fluents which unassign them. When it occurs
      in an argument list, the term is invalid.\<close>
datatype object = name: Obj name

text \<open>Schemas are used for action schemas and contain variables to be initialised\<close>
datatype symbol = Var variable | Const object

text \<open>A term represents a member of the domain, but can contain function application.\<close>
datatype (sym: 'sym) "term" = 
  Fun func (args: "'sym term list") 
  | Ent 'sym

datatype (ent: 'ent) num_fluent = 
  NFun func (args: "'ent list")
  | Num rat
  | Add "'ent num_fluent" "'ent num_fluent"
  | Sub "'ent num_fluent" "'ent num_fluent"
  | Mult "'ent num_fluent" "'ent num_fluent"
  | Div "'ent num_fluent" "'ent num_fluent"

datatype (ent: 'ent) num_comp =
  Num_Eq "'ent num_fluent" "'ent num_fluent"
  | Le "'ent num_fluent" "'ent num_fluent"
  | Lt "'ent num_fluent" "'ent num_fluent"

datatype (ent: 'ent) pred = 
    Pred (predicate: predicate) (arguments: "'ent list")
  | Eq (lhs: 'ent) (rhs: 'ent)


text \<open>An atom is either a predicate with arguments, or an equality statement.\<close>

datatype (ent: 'ent) atom = 
  PredAtom "'ent pred"
  | NumComp "'ent num_comp"



text \<open>Some of the AST entities are defined over a polymorphic \<open>'val\<close> type,
  which gets either instantiated by variables (for domains)
  or objects (for problems).
\<close>


text \<open>A type is a list of primitive type names.
  To model a primitive type, we use a singleton list.\<close>
datatype type = Either (primitives: "name list")

datatype upd_op = Assign
  | ScaleUp
  | ScaleDown
  | Increase
  | Decrease

text \<open>An effect contains a list of values to be added, and a list of values
  to be removed.\<close>
datatype 'ent ast_effect = 
  Effect  (adds: "('ent pred) list") 
          (dels: "('ent pred) list")
          (tf_upds: "(func \<times> 'ent option list \<times> 'ent option) list")
          (nf_upds: "(func \<times> upd_op \<times> 'ent option list \<times> 'ent num_fluent) list")

type_synonym schematic_formula = "symbol term atom formula"
type_synonym schematic_effect = "symbol term ast_effect"

type_synonym ground_formula = "object term atom formula"
type_synonym ground_effect = "object term ast_effect"

datatype fully_instantiated_effect =
  Eff (adds: "(object pred option) list")
      (dels: "(object pred option) list")
      (tf_upds: "(func \<times> object option list \<times> object option) list")
      (nf_upds: "(func \<times> object option list \<times> rat option) list")


subsubsection \<open>Domains\<close>

text \<open>An action schema has a name, a typed parameter list, a precondition,
  and an effect.\<close>
datatype ast_action_schema = Action_Schema
  (name: name)
  (parameters: "(variable \<times> type) list")
  (precondition: "schematic_formula")
  (effects: "(schematic_formula \<times> schematic_effect) list")


datatype world_model = World_Model 
  (preds: "object pred set")
  (tf_int: "func \<rightharpoonup> object list \<rightharpoonup> object")
  (nf_int: "func \<rightharpoonup> object list \<rightharpoonup> rat")


text \<open>A predicate declaration contains the predicate's name and its
  argument types.\<close>
datatype predicate_decl = PredDecl
  (pred: predicate)
  (argTs: "type list")

datatype object_fluent_decl = ObjFluentDecl
  (func: func)
  (argTs: "type list")
  (rT: type)

datatype num_fluent_decl = NumFluentDecl
  (func: func)
  (argTs: "type list")

text \<open>A domain contains the declarations of primitive types, predicates,
  and action schemas.\<close>

datatype ast_domain_decs = DomainDecls
  (types: "(name \<times> name) list") \<comment> \<open> \<open>(type, supertype)\<close> declarations. \<close>
  (predicates: "predicate_decl list")
  (object_fluents: "object_fluent_decl list")
  (num_fluents: "num_fluent_decl list")
  ("consts": "(object \<times> type) list")


subsubsection \<open>Problems\<close>


text \<open>A fact is a predicate applied to objects.\<close>
type_synonym fact = "predicate \<times> object list"

text \<open>Declarations of objects and an initial state in the problem\<close>
datatype ast_problem_decs = ProbDecls
  (domain_decs: ast_domain_decs)
  (objects: "(object \<times> type) list")

text \<open>In addition to the declaration of types, predicates, and constants, 
      a domain contains actions\<close>
datatype ast_domain = Domain
  (problem_decs: ast_problem_decs)
  (actions: "ast_action_schema list")

text \<open>A problem consists of a domain, a list of objects,
  a description of the initial state, and a description of the goal state.\<close>
datatype ast_problem = Problem
  (domain: ast_domain)
  (init: "world_model")
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
  (effects: "(ground_formula \<times> ground_effect) list")

(* Syntax helpers for schematic formulae *)

fun sym_vars where
  "sym_vars (Var x) = {x}" 
| "sym_vars (Const c) = {}"

fun sym_objs where
  "sym_objs (Var x) = {}"
| "sym_objs (Const obj) = {obj}"

fun sym_subst::"variable \<Rightarrow> object \<Rightarrow> symbol \<Rightarrow> symbol" where
  "sym_subst v obj (Var x) = (if (x = v) then (Const obj) else Var x)" 
| "sym_subst _ _ (Const obj) = Const obj"

abbreviation sym_term_vars where
  "sym_term_vars \<equiv> \<Union> o sym o (map_term sym_vars)"

abbreviation sym_term_objs where
  "sym_term_objs \<equiv> \<Union> o sym o (map_term sym_objs)"

abbreviation sym_term_subst::"variable \<Rightarrow> object \<Rightarrow> symbol term \<Rightarrow> symbol term" where
  "sym_term_subst v obj\<equiv> map_term (sym_subst v obj)"


abbreviation sym_term_nf_vars where
  "sym_term_nf_vars \<equiv> \<Union> o num_fluent.ent o (map_num_fluent sym_term_vars)"

abbreviation sym_term_nf_objs where
  "sym_term_nf_objs \<equiv> \<Union> o num_fluent.ent o (map_num_fluent sym_term_objs)"

abbreviation sym_term_nf_subst::"variable \<Rightarrow> object \<Rightarrow> symbol term num_fluent \<Rightarrow> symbol term num_fluent" where
  "sym_term_nf_subst v obj \<equiv> map_num_fluent (sym_term_subst v obj)"


abbreviation sym_term_nc_vars::"symbol term num_comp \<Rightarrow> variable set" where
  "sym_term_nc_vars \<equiv> \<Union> o num_comp.ent o (map_num_comp sym_term_vars)"

abbreviation sym_term_nc_objs::"symbol term num_comp \<Rightarrow> object set" where
  "sym_term_nc_objs \<equiv> \<Union> o num_comp.ent o (map_num_comp sym_term_objs)"

abbreviation sym_term_nc_subst::"variable \<Rightarrow> object \<Rightarrow> symbol term num_comp \<Rightarrow> symbol term num_comp" where
  "sym_term_nc_subst v c \<equiv> map_num_comp (map_term (sym_subst v c))"


abbreviation sym_term_pred_vars where
  "sym_term_pred_vars \<equiv> \<Union> o pred.ent o (map_pred sym_term_vars)"

abbreviation sym_term_pred_objs where
  "sym_term_pred_objs \<equiv> \<Union> o pred.ent o (map_pred sym_term_objs)"

abbreviation sym_term_pred_subst where
  "sym_term_pred_subst v c \<equiv> map_pred (map_term (sym_subst v c))"


abbreviation sym_term_atom_vars::"symbol term atom \<Rightarrow> variable set" where
  "sym_term_atom_vars \<equiv> \<Union> o ent o (map_atom sym_term_vars)"

abbreviation sym_term_atom_objs::"symbol term atom \<Rightarrow> object set" where
  "sym_term_atom_objs \<equiv> \<Union> o ent o (map_atom sym_term_objs)"

abbreviation sym_term_atom_subst::"variable \<Rightarrow> object \<Rightarrow> symbol term atom \<Rightarrow> symbol term atom" where
  "sym_term_atom_subst v c \<equiv> map_atom (map_term (sym_subst v c))"


fun tf_upd_subst::"variable \<Rightarrow> object \<Rightarrow> (func \<times> symbol term option list \<times> symbol term option) 
  \<Rightarrow> (func \<times> symbol term option list \<times> symbol term option)" where
  "tf_upd_subst v c (f, as, r) = (f, (map o map_option) (sym_term_subst v c) as, map_option (sym_term_subst v c) r)"

fun nf_upd_subst::"variable \<Rightarrow> object \<Rightarrow> (func \<times> upd_op \<times> symbol term option list \<times> symbol term num_fluent)
  \<Rightarrow> (func \<times> upd_op \<times> symbol term option list \<times> symbol term num_fluent)" where
  "nf_upd_subst v c (f, op, as, r) = 
    (f, op, (map o map_option) (sym_term_subst v c) as, sym_term_nf_subst v c r)"

fun schematic_effect_subst::"variable \<Rightarrow> object \<Rightarrow> schematic_effect 
  \<Rightarrow> schematic_effect" where
  "schematic_effect_subst v c (Effect a d tu nu) =
    (Effect 
      (map (sym_term_pred_subst v c) a) 
      (map (sym_term_pred_subst v c) d) 
      (map (tf_upd_subst v c) tu)
      (map (nf_upd_subst v c) nu))"

definition f_vars::"schematic_formula \<Rightarrow> variable set" where
  "f_vars = \<Union> o atoms o (map_formula sym_term_atom_vars)" 

definition f_objs::"schematic_formula \<Rightarrow> object set" where
  "f_objs = \<Union> o atoms o (map_formula sym_term_atom_objs)" 

definition f_subst where 
  "f_subst v c \<equiv> map_formula (sym_term_atom_subst v c)"

subsection \<open>Semantics of terms\<close>
  text \<open>Although using option.None instead of a distinguished member 
        object.Undef makes this function a bit more difficult to 
        reason about, it is worth it. The well-formedness checks for 
        updates to fluents can be implemented generically rather than
        requiring into the underlying type. The return value has a different
        notion of well-formedness compared to the arguments, since it permits
        the usage of None/Undefined. If we did not use option, we would have
        to make the wf checks much more involved. We would have to define
        wf_return_type.

        The well-formedness of the world model would also require it not to
        assign any value to undefined parameters for functions. Additionally,
        it becomes messy when a return value is explicitly assigned Undefined.
        
        Moreover, this specific function is used for the full instantiation
        of ground effects into applicable effects. \<close>
  (* fun term_val::"world_model \<Rightarrow> object term \<Rightarrow> object" where
    "term_val M (Ent obj) = obj"
  | "term_val M (Fun fun as) = (case (tf_int M fun) of 
      Some f \<Rightarrow> (case (f (map (\<lambda>t. term_val M t) as)) of 
        Some obj \<Rightarrow> obj
      | None \<Rightarrow> Undef)
    | None \<Rightarrow> Undef)" *)

  fun term_val::"world_model \<Rightarrow> object term \<Rightarrow> object option" where
    "term_val M (Ent obj) = Some obj"
  | "term_val M (Fun fun as) = (case (tf_int M fun) of
      Some f \<Rightarrow> (let arg_vals = map (\<lambda>t. term_val M t) as
        in (if (list_all (\<lambda>x. x \<noteq> None) arg_vals) 
            then f (map the arg_vals) else None))
    | None \<Rightarrow> None)"
  
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
  | "nf_val M (Div x y) = (combine_options inverse_divide (nf_val M x) (nf_val M y))"
  
  fun nc_val::"world_model \<Rightarrow> (object term) num_comp \<Rightarrow> bool" where
    "nc_val M (Num_Eq x y) = (case (nf_val M x, nf_val M y) of
      (Some x, Some y)  \<Rightarrow> x = y | _ \<Rightarrow> False)"
  | "nc_val M (Le x y) = (case (nf_val M x, nf_val M y) of
      (Some x, Some y)  \<Rightarrow> x \<le> y | _ \<Rightarrow> False)"
  | "nc_val M (Lt x y) = (case (nf_val M x, nf_val M y) of
      (Some x, Some y)  \<Rightarrow> x < y | _ \<Rightarrow> False)"
  
  fun pred_inst::"world_model \<Rightarrow> (object term) pred \<Rightarrow> object pred option" where
    "pred_inst M (Pred p as) = (let arg_vals = map (\<lambda>t. term_val M t) as
        in (if (list_all (\<lambda>x. x \<noteq> None) arg_vals) 
            then Some (Pred p (map the arg_vals)) 
            else None))"
  | "pred_inst M (Eq t1 t2) = (case (term_val M t1, term_val M t2) of
      (Some x, Some y) \<Rightarrow> Some (Eq x y)
    | _                \<Rightarrow> None)"
  
  fun pred_val::"world_model \<Rightarrow> (object term) pred \<Rightarrow> bool" where
    "pred_val M p = (case pred_inst M p of 
      Some (Pred p as)  \<Rightarrow> (Pred p as) \<in> preds M
    | Some (Eq x y)     \<Rightarrow> x = y
    | None              \<Rightarrow> False)"
  
  
  text \<open>A valuation according to more or less standard FOL\<close>
  fun valuation::"world_model \<Rightarrow> object term atom valuation" where
    "valuation M (PredAtom p) = pred_val M p"
  | "valuation M (NumComp c) = nc_val M c"


subsection \<open>PDDL semantics\<close>
context
begin

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


subsubsection \<open>Declarations of types, constants and predicates in the domain\<close>

locale ast_domain_decs =
  fixes DD :: ast_domain_decs
begin
  text \<open>The signature is a partial function that maps the predicates
    of the domain to lists of argument types.\<close>
  definition sig :: "predicate \<rightharpoonup> type list" where
  "sig \<equiv> map_of (map (\<lambda>PredDecl p n \<Rightarrow> (p,n)) (predicates DD))"

  definition obj_fluent_sig::"func \<rightharpoonup> (type list \<times> type)" where
  "obj_fluent_sig \<equiv> map_of (map (\<lambda>ObjFluentDecl f ts t \<Rightarrow> (f, (ts, t))) (object_fluents DD))"
  
  definition num_fluent_sig::"func \<rightharpoonup> type list" where
  "num_fluent_sig \<equiv> map_of (map (\<lambda>NumFluentDecl f ts \<Rightarrow> (f, ts)) (num_fluents DD))"

  text \<open>We use a flat subtype hierarchy, where every type is a subtype
    of object, and there are no other subtype relations.

    Note that we do not need to restrict this relation to declared types,
    as we will explicitly ensure that all types used in the problem are
    declared.
    \<close>
  
  fun subtype_edge where
    "subtype_edge (ty,superty) = (superty,ty)"

  definition "subtype_rel \<equiv> set (map subtype_edge (types DD))"

  (*
  definition "subtype_rel \<equiv> {''object''}\<times>UNIV"
  *)

  definition of_type :: "type \<Rightarrow> type \<Rightarrow> bool" where
    "of_type oT T \<equiv> set (primitives oT) \<subseteq> subtype_rel\<^sup>* `` set (primitives T)"
  text \<open>This checks that every primitive on the LHS is contained in or a
    subtype of a primitive on the RHS\<close>

  fun of_opt_type::"type option \<Rightarrow> type \<Rightarrow> bool" where
    "of_opt_type None T = False" |
    "of_opt_type (Some oT) T = of_type oT T"

  context 
    fixes entT::"'ent \<rightharpoonup> type"
      and funT::"func \<rightharpoonup> (type list \<times> type)"
  begin
    fun ty_term::"'ent term \<Rightarrow> type option" where
      "ty_term (Ent e) = entT e"
    | "ty_term (Fun f as) = (case (funT f) of 
        Some (Ts, T) \<Rightarrow> (if (list_all2 of_opt_type (map ty_term as) Ts) 
          then Some T else None)
      | None \<Rightarrow> None
      )"
  end


  lemma ty_term_mono': "entT \<subseteq>\<^sub>m entT' \<Longrightarrow> funT \<subseteq>\<^sub>m funT' 
    \<Longrightarrow> ty_term entT funT x = Some t 
    \<Longrightarrow> ty_term entT' funT' x = Some t"
  proof (induction x arbitrary: t)
    case (Fun f args)
    then obtain Ts where 
      "funT f = Some (Ts, t)" 
      "list_all2 of_opt_type (map (ty_term entT funT) args) Ts"
      by (auto split: option.splits if_splits)
    hence "\<forall>i < length args. of_opt_type (ty_term entT funT (args!i)) (Ts!i)"
      using list_all2_nthD by fastforce
    hence "\<forall>i < length args. \<exists>t. ty_term entT funT (args!i) = Some t \<and> of_type t (Ts!i)"
      by (metis of_opt_type.elims(2))
    hence "\<forall>i < length args. \<exists>t. ty_term entT' funT' (args!i) = Some t \<and> of_type t (Ts!i)"
      using Fun by auto
    hence "\<forall>i < length args. (of_opt_type o (ty_term entT' funT')) (args!i) (Ts!i)"
      by auto
    from \<open>list_all2 of_opt_type (map (ty_term entT funT) args) Ts\<close>
    have "length args = length Ts" using list_all2_lengthD by fastforce
    with \<open>\<forall>i < length args. (of_opt_type o ty_term entT' funT') (args!i) (Ts!i)\<close>
    have "list_all2 (of_opt_type o (ty_term entT' funT')) args Ts" 
      using list_all2_conv_all_nth[where xs = args and ys = Ts and P = "(of_opt_type o (ty_term entT' funT'))"]
      by blast
    hence "list_all2 of_opt_type (map (ty_term entT' funT') args) Ts"
      by (simp add: list_all2_conv_all_nth)
    from \<open>funT f = Some (Ts, t)\<close>
    have "funT' f = Some (Ts, t)" using Fun.prems(2) map_leD by fast
    with \<open>list_all2 of_opt_type (map (ty_term entT' funT') args) Ts\<close>
    show ?case by simp
  next
    case (Ent x)
    then show ?case by (auto dest: map_leD)
  qed
  
  lemma ty_term_mono: assumes "entT \<subseteq>\<^sub>m entT'" "funT \<subseteq>\<^sub>m funT'"
    shows "ty_term entT funT \<subseteq>\<^sub>m ty_term entT' funT'"
    using ty_term_mono'[OF assms] map_leI
    by blast

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

    fun wf_pred::"predicate \<times> 'ent list \<Rightarrow> bool" where
      "wf_pred (p,vs) \<longleftrightarrow> (
        case sig p of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 is_of_type vs Ts)"

    fun wf_pred_atom :: "'ent pred \<Rightarrow> bool" where
      "wf_pred_atom (Pred p vs) \<longleftrightarrow> wf_pred (p,vs)"
    | "wf_pred_atom (Eq a b) \<longleftrightarrow> ty_ent a \<noteq> None \<and> ty_ent b \<noteq> None"
  
    fun wf_num_func::"func \<times> 'ent list \<Rightarrow> bool" where
      "wf_num_func (f, as) \<longleftrightarrow> (
        case num_fluent_sig f of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 is_of_type as Ts
      )"
  
    fun wf_num_fluent::"'ent num_fluent \<Rightarrow> bool" where
      "wf_num_fluent (NFun f as) = wf_num_func (f, as)"
    | "wf_num_fluent (Num _) = True"
    | "wf_num_fluent (Add a b) = (wf_num_fluent a \<and> wf_num_fluent b)"
    | "wf_num_fluent (Sub a b) = (wf_num_fluent a \<and> wf_num_fluent b)"
    | "wf_num_fluent (Mult a b) = (wf_num_fluent a \<and> wf_num_fluent b)"
    | "wf_num_fluent (Div a b) = (wf_num_fluent a \<and> wf_num_fluent b)"
  
    fun wf_num_comp :: "'ent num_comp \<Rightarrow> bool" where
      "wf_num_comp (Num_Eq a b) = (wf_num_fluent a \<and> wf_num_fluent b)"
    | "wf_num_comp (Lt a b) = (wf_num_fluent a \<and> wf_num_fluent b)"
    | "wf_num_comp (Le a b) = (wf_num_fluent a \<and> wf_num_fluent b)"

    text \<open>Predicate-atoms are well-formed if their arguments match the
      signature, equalities are well-formed if the arguments are valid
      objects (have a type).

    \<close>
    fun wf_atom :: "'ent atom \<Rightarrow> bool" where
      "wf_atom (PredAtom p) \<longleftrightarrow> wf_pred_atom p"
    | "wf_atom (NumComp nc) \<longleftrightarrow> wf_num_comp nc"

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
    
    fun is_some where
      "is_some (Some x) = True"
    | "is_some None = False"
    
    text \<open>An update to a function on objects is well-formed if the function has 
          been declared, the signature matches the types of the arguments and new return value, 
          and the arguments and the term to assign the return value are well-formed.\<close>
    fun wf_tf_upd::"(func \<times> 'ent option list \<times> 'ent option) \<Rightarrow> bool" where
    "wf_tf_upd (f, as, v) = (case obj_fluent_sig f of 
      None \<Rightarrow> False
    | Some (Ts, T) \<Rightarrow> 
          list_all is_some as
        \<and> list_all2 (is_of_type o the) as Ts 
        \<and> (v = None \<or> is_of_type (the v) T)
    )" (* is_of_type prevents usage of Undef for the 
          return value, unless we define another notion of 
          well-formedness.
        - By using option for the update, we have to use the every time. *)
  
    text \<open>An update to a numeric function is well-formed if the function has been declared,
          the signature matches the types of the arguments, the arguments are well-formed,
          and the value that is being assigned is well-formed.\<close>
    fun wf_nf_upd::"(func \<times> upd_op \<times> 'ent option list \<times> 'ent num_fluent) \<Rightarrow> bool" where
    "wf_nf_upd (f, op, as, v) = (case num_fluent_sig f of 
        None \<Rightarrow> False
      | Some Ts \<Rightarrow> 
          list_all is_some as
        \<and> list_all2 (is_of_type o the) as Ts 
        \<and> wf_num_fluent v
    )"

    fun wf_pred_upd where
      "wf_pred_upd (Eq _ _) = False" |
      "wf_pred_upd p = wf_pred_atom p"

    text \<open>An effect is well-formed if its constituent parts are well-formed\<close>
    fun wf_effect where
      "wf_effect (Effect a d tu nu) \<longleftrightarrow>
          (\<forall>ae\<in>set a. wf_pred_upd ae)
        \<and> (\<forall>de\<in>set d. wf_pred_upd de)
        \<and> (\<forall>u \<in>set tu. wf_tf_upd u)
        \<and> (\<forall>u \<in> set nu. wf_nf_upd u)
        "

    fun wf_cond_effect where
      "wf_cond_effect (pre, eff) \<longleftrightarrow> wf_fmla pre \<and> wf_effect eff"

    definition wf_cond_effect_list where
      "wf_cond_effect_list effs \<equiv> \<forall>e \<in> set effs. wf_cond_effect e"


    definition wf_tf_int''::"'ent list \<Rightarrow> 'ent \<Rightarrow> type list \<Rightarrow> type \<Rightarrow> bool" where
      "wf_tf_int'' as v Ts T = (list_all2 is_of_type as Ts \<and> is_of_type v T)"
    
    definition wf_tf_int'::"func \<Rightarrow> ('ent list \<rightharpoonup> 'ent) \<Rightarrow> bool" where
      "wf_tf_int' f ti' = (case obj_fluent_sig f of 
        None \<Rightarrow> False 
      | Some (Ts, T) \<Rightarrow> (\<forall>as \<in> dom ti'. wf_tf_int'' as (the (ti' as)) Ts T))"
  
    definition wf_tf_int::"(func \<rightharpoonup> 'ent list \<rightharpoonup> 'ent) \<Rightarrow> bool" where
      "wf_tf_int ti \<equiv> (\<forall>f \<in> dom ti. wf_tf_int' f (the (ti f)))"

    definition wf_nf_int'::"func \<Rightarrow> ('ent list \<rightharpoonup> rat) \<Rightarrow> bool" where
      "wf_nf_int' f ti' = (case num_fluent_sig f of 
        None \<Rightarrow> False 
      | Some Ts \<Rightarrow> (\<forall>as \<in> dom ti'. list_all2 is_of_type as Ts))"
  
    definition wf_nf_int::"(func \<rightharpoonup> 'ent list \<rightharpoonup> rat) \<Rightarrow> bool" where
      "wf_nf_int ti \<equiv> (\<forall>f \<in> dom ti. wf_nf_int' f (the (ti f)))"
  end \<comment> \<open>Context fixing \<open>ty_ent\<close>\<close>

  definition constT :: "object \<rightharpoonup> type" where
    "constT \<equiv> map_of (consts DD)"
             
  text \<open>A type is well-formed if it consists only of declared primitive types,
     and the type object.\<close>
  fun wf_type where
    "wf_type (Either Ts) \<longleftrightarrow> set Ts \<subseteq> insert ''object'' (fst`set (types DD))"

  text \<open>A predicate is well-formed if its argument types are well-formed.\<close>
  fun wf_predicate_decl where
    "wf_predicate_decl (PredDecl p Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. wf_type T)"

  text \<open>The types declaration is well-formed, if all supertypes are declared types (or object)\<close>
  definition "wf_types \<equiv> snd`set (types DD) \<subseteq> insert ''object'' (fst`set (types DD))"

  text \<open>The declarations in a domain are well-formed if 
    \<^item> there are no duplicate declared predicate names,
    \<^item> all declared predicates are well-formed,
    \<^item> there are no duplicate action names\<close>

  definition wf_domain_decs :: "bool" where
    "wf_domain_decs \<equiv>
      wf_types
    \<and> distinct (map (predicate_decl.pred) (predicates DD))
    \<and> (\<forall>p\<in>set (predicates DD). wf_predicate_decl p)
    \<and> distinct (map fst (consts DD)) 
    \<and> (\<forall>(c, T) \<in> set (consts DD). wf_type T)"

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

  definition wf_problem_decs where
    "wf_problem_decs \<equiv>
      wf_domain_decs
    \<and> distinct (map fst (objects PD) @ map fst (consts DD))
    \<and> (\<forall>(n,T) \<in> set (objects PD). wf_type T)"


  text \<open>An action schema is well-formed if the parameter names are distinct,
    and the precondition and effect is well-formed wrt.\ the parameters.
  \<close>
  text \<open>This is here, because the semantic properties of an action schema
        containing semantic properties require the declarations from the problem
        to be well-formed. \<close>
  (* action schemas are well-formed only in relation to the problem *)
  fun wf_action_schema :: "ast_action_schema \<Rightarrow> bool" where
    "wf_action_schema (Action_Schema n params pre effs) \<longleftrightarrow> (
      let
        tys = ty_sym (map_of params) objT;
        tyt = ty_term tys obj_fluent_sig
      in
        distinct (map fst params)
      \<and> wf_fmla tyt pre
      \<and> wf_cond_effect_list tyt effs)"

  abbreviation wf_cond_effect_inst::"(ground_formula \<times> ground_effect) \<Rightarrow> bool" where
    "wf_cond_effect_inst \<equiv> wf_cond_effect (ty_term objT obj_fluent_sig)"

  definition wf_cond_effect_inst_list where
    "wf_cond_effect_inst_list effs \<equiv> \<forall>e \<in> set effs. wf_cond_effect_inst e" 
  
  definition wf_goal::"schematic_formula \<Rightarrow> bool" where
    "wf_goal = (
      let tys = ty_sym (\<lambda>_. None) objT;
          tyt = ty_term tys obj_fluent_sig
      in wf_fmla tyt)"

end

subsubsection \<open>The entire domain\<close>

text \<open>To fully assert the well-formedness of a domain, we need the set of objects declared
      in a problem as well. These are necessary to implement the macros that
      replace quantified formulas with quantifier-free ones.\<close>
locale ast_domain = ast_problem_decs "problem_decs D"
  for D::ast_domain
begin
abbreviation "PD \<equiv> problem_decs D"

  text \<open>This definition is needed for well-formedness of the initial model,
    and forward-references to the concept of world model.
  \<close>
  text \<open>The predicates are well-formed, i.e. well-typed. The interpretations of 
        fluents are also well-formed, i.e. well-typed and only defined for those
        functions which have been declared in the domain or problem.\<close>
  definition wf_world_model::"world_model \<Rightarrow> bool" where
    "wf_world_model M \<equiv> (\<forall>p \<in> preds M. wf_pred_atom objT p) 
                      \<and> wf_tf_int objT (tf_int M)
                      \<and> wf_nf_int objT (nf_int M)"
  
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

context ast_domain
begin
    
  fun inst_tf_upd::"world_model 
    \<Rightarrow> (func \<times> object term option list \<times> object term option) 
    \<Rightarrow> (func \<times> object option list \<times> object option)" where
    "inst_tf_upd M (F, as, v) = (F, map ((term_val M) o the) as, term_val M (the v))"

  fun inst_nf_upd::"world_model
    \<Rightarrow> (func \<times> upd_op \<times> object term option list \<times> object term num_fluent)
    \<Rightarrow> (func \<times> object option list \<times> rat option)" where
    "inst_nf_upd M (f, op, as, t) = (
      let args = map ((term_val M) o the) as
      in
      (case (nf_val M (NFun f (map the as)), nf_val M t) of
        (None, change) \<Rightarrow> (case op of 
          Assign \<Rightarrow> (f, args, change) 
        | _      \<Rightarrow> (f, args, None)
        )
      | (Some current, Some change) \<Rightarrow> (case op of
          Assign \<Rightarrow> (f, args, Some change)
        | ScaleUp \<Rightarrow> (f, args, Some (current * change))
        | ScaleDown \<Rightarrow> (f, args, Some (current / change))
        | Increase \<Rightarrow> (f, args, Some (current + change))
        | Decrease \<Rightarrow> (f, args, Some (current - change))
        )
      )
    )"
  
  fun inst_effect :: "world_model \<Rightarrow> ground_effect \<Rightarrow> fully_instantiated_effect" where
    "inst_effect M (Effect a d tu nu) = (
      Eff (map (pred_inst M) a) 
          (map (pred_inst M) d) 
          (map (inst_tf_upd M) tu) 
          (map (inst_nf_upd M) nu))"

  text \<open>When we apply an update that returns undefined, we can either unassign the interpretation
        or update it to Undefined. In both cases, term_val will return Undefined.
        We have removed Undefined for now.\<close>
  fun apply_tf_upd::"(func \<times> object option list \<times> object option) 
    \<Rightarrow> (func \<rightharpoonup> object list \<rightharpoonup> object) 
    \<Rightarrow> (func \<rightharpoonup> object list \<rightharpoonup> object)" where
    "apply_tf_upd (f, as, v) ti = (
      case (ti f) of
        Some ti1 \<Rightarrow> (ti(f \<mapsto> (ti1((map the as) := v))))
      | None \<Rightarrow> (ti(f \<mapsto> (Map.empty((map the as) := v))))
    )"

  text \<open>The return value will never be undefined, unless the update is not well-formed.\<close>
  fun apply_nf_upd::"(func \<times> object option list \<times> rat option) 
    \<Rightarrow> (func \<rightharpoonup> object list \<rightharpoonup> rat) 
    \<Rightarrow> (func \<rightharpoonup> object list \<rightharpoonup> rat)" where
    "apply_nf_upd (f, as, v) ni = (
      case (ni f) of
        Some ni1 \<Rightarrow> (ni(f \<mapsto> (ni1((map the as) := v))))
      | None \<Rightarrow> (ni(f \<mapsto> (Map.empty((map the as) := v)))))"

  text \<open>It seems to be agreed upon that, in case of a contradictory effect,
    addition overrides deletion. We model this behaviour by first executing
    the deletions, and then the additions. Also, effects that occur later
    in the list override those that occur earlier.\<close>
  fun apply_effect::"fully_instantiated_effect \<Rightarrow> world_model \<Rightarrow> world_model" where
    "apply_effect (Eff a d tu nu) (World_Model p ti ni) = (
      World_Model 
        ((p - set (map the d)) \<union> set (map the a)) 
        (fold (apply_tf_upd) tu ti) 
        (fold (apply_nf_upd) nu ni))"

  definition active_effects::"world_model \<Rightarrow> (ground_formula \<times> ground_effect) list \<Rightarrow> ground_effect list" where
    "active_effects M e = (
      let active = filter (\<lambda>(pre, eff). valuation M \<Turnstile> pre) e
      in map snd active)"


  text \<open>Execute a ground action\<close>
  definition execute_ground_action :: "ground_action \<Rightarrow> world_model \<Rightarrow> world_model" where
    "execute_ground_action a M = (
      let active = map (inst_effect M) (active_effects M (effects a))     
      in fold apply_effect active M)"

  text \<open>Predicate to model that the given list of action instances is
    executable, and transforms an initial world model \<open>M\<close> into a final
    model \<open>M'\<close>.

    Note that this definition over the list structure is more convenient in HOL
    than to explicitly define an indexed sequence \<open>M\<^sub>0\<dots>M\<^sub>N\<close> of intermediate world
     models, as done in [Lif87].
  \<close>

    fun wf_app_pred_upd where
      "wf_app_pred_upd None = False"
    | "wf_app_pred_upd (Some (Eq _ _)) = False"
    | "wf_app_pred_upd (Some (Pred p as)) = wf_pred_atom objT (Pred p as)"
                            
    fun wf_ret_val::"'a option \<Rightarrow> 'b option \<Rightarrow> bool" where
      "wf_ret_val None None = True"
    | "wf_ret_val (Some r) (Some r') = True"
    | "wf_ret_val _ _ = False"

    fun wf_app_tf_upd::"(func \<times> object term option list \<times> object term option) 
      \<Rightarrow> (func \<times> object option list \<times> object option) \<Rightarrow> bool" where
      "wf_app_tf_upd (f, as, v) (f', as', v') = (
          wf_ret_val v v' 
        \<and> wf_tf_upd objT (f', as', v'))"
  
    fun wf_app_nf_upd::"(func \<times> object option list \<times> rat option) \<Rightarrow> bool" where
      "wf_app_nf_upd (f, as, v) = (case (num_fluent_sig f) of 
        None \<Rightarrow> False
      | Some Ts \<Rightarrow> 
          list_all is_some as
        \<and> list_all2 ((is_of_type objT) o the) as Ts 
        \<and> is_some v)"

    
    fun wf_fully_instantiated_effect where
      "wf_fully_instantiated_effect (Effect a d tu nu) (Eff a' d' tu' nu') \<longleftrightarrow> 
          (\<forall>ae\<in>set a'. wf_app_pred_upd ae)
        \<and> (\<forall>de\<in>set d'. wf_app_pred_upd de)
        \<and> (\<forall>(u, u') \<in> set (zip tu tu'). wf_app_tf_upd u u')
        \<and> (\<forall>u' \<in> set nu'. wf_app_nf_upd u')"
  
  (* fun ground_action_path
    :: "world_model \<Rightarrow> ground_action list \<Rightarrow> world_model \<Rightarrow> bool"
  where
    "ground_action_path M [] M' \<longleftrightarrow> (M = M')"
  | "ground_action_path M (\<alpha>#\<alpha>s) M' \<longleftrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= precondition \<alpha>
    \<and> wf_active_effects (fully_instantiated_effects \<alpha>) M
    \<and> ground_action_path (execute_ground_action \<alpha> M) \<alpha>s M'" *)
  
  definition wf_active_effects::"world_model \<Rightarrow> (ground_formula \<times> ground_effect) list \<Rightarrow> bool" where
    "wf_active_effects M e = (\<forall>e \<in> set (active_effects M e). wf_fully_instantiated_effect e (inst_effect M e))"
  
  fun ground_action_path
    :: "world_model \<Rightarrow> ground_action list \<Rightarrow> world_model \<Rightarrow> bool"
  where
    "ground_action_path M [] M' \<longleftrightarrow> (M = M')"
  | "ground_action_path M (\<alpha>#\<alpha>s) M' \<longleftrightarrow> valuation M \<Turnstile> precondition \<alpha>
    \<and> wf_active_effects M (effects \<alpha>)
    \<and> ground_action_path (execute_ground_action \<alpha> M) \<alpha>s M'"

  text \<open>Unfolded definition of ground_action_path.\<close>
  lemma ground_action_path_in_paper:
    "ground_action_path M [] M' \<longleftrightarrow> (M = M')"
    "ground_action_path M (\<alpha>#\<alpha>s) M' \<longleftrightarrow> valuation M \<Turnstile> precondition \<alpha>
    \<and> (\<forall>e \<in> set (active_effects M (effects \<alpha>)). wf_fully_instantiated_effect e (inst_effect M e))
    \<and> ground_action_path (fold apply_effect (map (inst_effect M) (active_effects M (effects \<alpha>))) M) \<alpha>s M'"
    by (auto simp: execute_ground_action_def wf_active_effects_def)

end

subsubsection \<open>The problem\<close>

locale ast_problem = ast_domain "domain P"
  for P::ast_problem
begin
  abbreviation "D \<equiv> domain P"
  text \<open>A problem is well-formed if in addition to the domain being well-formed, the goal is\<close>
  definition wf_problem where
    "wf_problem \<equiv>
      wf_domain
    \<and> wf_world_model (init P)
    \<and> wf_goal (goal P)
    "
end
subsection \<open>Conditions for the preservation of well-formedness\<close>

context ast_problem_decs
begin
  text \<open>This section proves that well-formedness under one type environment implies
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

  lemma var_in_fmla_vars: "(term.VAR x) \<in> \<Union> (ent ` atoms \<phi>) \<Longrightarrow> x \<in> f_vars \<phi>" 
    apply (induction \<phi>)
    using tav_alt by fastforce auto
  
  lemma wf_atom_restr: 
    assumes wf: "wf_atom (ty_term Q cT) a" 
      shows "wf_atom (ty_term (Q |` (term_atom_vars a)) cT) a"
    using same_type_imp_wf_atom_eq[OF term_vars_restr_same_type wf]
    .

  lemma fmla_vars_restr_same_type: "\<forall>e \<in> \<Union> (ent ` atoms \<phi>). (ty_term Q cT) e 
    = (ty_term (Q |` (f_vars \<phi>)) cT) e"
  proof (induction \<phi>)
    case (Atom x)
    moreover have "\<Union> (ent ` atoms (Atom x)) = ent x" by simp
    moreover have "f_vars (Atom x) = term_atom_vars x" by simp
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
  lemma wf_fmla_vars: "wf_fmla (ty_term Q cT) \<phi> \<Longrightarrow> f_vars \<phi> \<subseteq> dom Q"
    using wf_schematic_atom_vars
    by (induction \<phi>) auto
  
  lemma wf_fmla_restr': "wf_fmla (ty_term Q cT) \<phi> 
    \<Longrightarrow> wf_fmla (ty_term (Q |` (f_vars \<phi>)) cT) \<phi>"
    using same_type_imp_wf_fmla_eq[OF fmla_vars_restr_same_type]
    by blast

  lemma wf_fmla_mono': 
    assumes "wf_fmla (ty_term Q cT) \<phi>"
            "Q \<subseteq>\<^sub>m R"
    shows   "wf_fmla (ty_term R cT) \<phi>"
    using wf_fmla_mono[OF assms(1) ty_term_mono[OF assms(2) map_le_refl[of cT]]]
    .

  lemma wf_fmla_restr: "wf_fmla (ty_term Q cT) \<phi> 
    \<longleftrightarrow> wf_fmla (ty_term (Q |` (f_vars \<phi>)) cT) \<phi>"
    using wf_fmla_restr' wf_fmla_mono' map_restrict_less
    by blast
  
  lemma wf_fmla_bw: "Q \<subseteq>\<^sub>m R \<Longrightarrow> f_vars \<phi> \<subseteq> dom Q
    \<Longrightarrow> wf_fmla (ty_term R cT) \<phi> \<longleftrightarrow> wf_fmla (ty_term Q cT) \<phi>"
    using wf_fmla_restr[of R] sym[OF wf_fmla_restr[of Q]] map_le_restr
    by metis
  
  lemma wf_fmla_alt_lemma: "Q \<subseteq>\<^sub>m R 
    \<Longrightarrow> wf_fmla (ty_term Q cT) \<phi> \<longleftrightarrow> wf_fmla (ty_term R cT) \<phi> \<and> f_vars \<phi> \<subseteq> dom Q"
    using wf_fmla_mono wf_fmla_vars wf_fmla_bw 
    by blast

end

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

  context
    fixes Q::"'a \<rightharpoonup> type" and R::"'b \<rightharpoonup> type" and f :: "'a \<Rightarrow> 'b"
    assumes INST: "is_of_type Q x T \<Longrightarrow> is_of_type R (f x) T"
  begin
    lemma X1: assumes "list_all2 (is_of_type Q) xs Ts"
      shows "list_all2 (is_of_type R) (map f xs) Ts" 
      using assms INST by (induction rule: list_all2_induct) auto

    thm is_of_type_def
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

end \<comment> \<open>locale \<open>ast_problem_decs\<close>\<close>

context ast_problem_decs
begin

  text \<open>A well-formed goal is a well-formed formula without any free variables\<close>
  
  theorem wf_goal_alt: "wf_goal \<phi> \<longleftrightarrow> wf_fmla (ty_term Q objT) \<phi> \<and> f_vars \<phi> = {}"
    unfolding wf_goal_def
    using wf_fmla_alt_lemma[of "(\<lambda>_. None)"]
    by simp

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

  fun univ_effect::"variable \<Rightarrow> type \<Rightarrow> (schematic_formula \<times> schematic_effect) \<Rightarrow> (schematic_formula \<times> schematic_effect) list" where
    "univ_effect v t (pre, eff) = (map (\<lambda>c.((map_formula (sym_term_atom_subst v c) pre), (schematic_effect_subst v c eff))) (t_dom t))"
  
  text \<open>PDDL quantifiers act on typed lists of variables\<close>
  text \<open>This function removes duplicate parameters, keeping the last occurrence\<close>
  fun unique_vars'::"(variable \<times> type) list \<Rightarrow> (variable \<times> type) list \<times> variable set" where
    "unique_vars' [] = ([], {})"
  | "unique_vars' ((v, t)#ps) = (let (ps', s) = unique_vars' ps in (if v \<in> s then (ps', s) else (((v, t)#ps'), insert v s)))"

  abbreviation "unique_vars \<equiv> fst o unique_vars'"

  definition pddl_all::"(variable \<times> type) list \<Rightarrow> schematic_formula \<Rightarrow> schematic_formula" where
    "pddl_all ps \<phi> = foldr (\<lambda>(v, t) \<phi>. (\<^bold>\<forall> v - t. \<phi>)) (unique_vars ps) \<phi>"

  definition pddl_exists::"(variable \<times> type) list \<Rightarrow> schematic_formula \<Rightarrow> schematic_formula" where
    "pddl_exists ps \<phi> = foldr (\<lambda>(v, t) \<phi>. (\<^bold>\<exists> v - t. \<phi>)) (unique_vars ps) \<phi>"


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
  
  lemma unique_vars_unique: "(v, t1) \<in> set ps \<Longrightarrow> unique_vars ((v, t2)#ps) = unique_vars ps"
  proof -
    assume "(v, t1) \<in> set ps"
    hence "v \<in> snd (unique_vars' ps)" using v_in_unique_vars' by blast
    thus "unique_vars ((v, t2)#ps) = unique_vars ps" by (auto simp: Let_def split: prod.split)
  qed
  
  lemma pddl_all_bind_order: "(v, t1) \<in> set ps \<Longrightarrow> pddl_all ps \<phi> = pddl_all ((v, t2)#ps) \<phi>"
    unfolding pddl_all_def
    using unique_vars_unique
    by simp
   
  lemma pddl_exists_bind_order: "(v, t1) \<in> set ps \<Longrightarrow> pddl_exists ps \<phi> = pddl_exists ((v, t2)#ps) \<phi>"
    unfolding pddl_exists_def
    using unique_vars_unique
    by simp
end

locale wf_problem_decs = ast_problem_decs +
  assumes wf_problem_decs: wf_problem_decs
begin

  text \<open>The correctness of t_dom\<close>
  lemma t_dom_corr: "objT obj = Some t \<Longrightarrow> of_type t T \<longleftrightarrow> obj \<in> set (t_dom T)"
  proof -                                   
    assume "objT obj = Some t"
    hence "map_of (consts DD @ objects PD) obj = Some t"
      using objT_alt by argo
    moreover
    from wf_problem_decs
    have "distinct (map fst (objects PD @ consts DD))"
      unfolding wf_problem_decs_def by simp
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
    hence "\<exists>t. (obj,t) \<in> set (consts DD @ objects PD) \<and> of_type t ty"
      unfolding t_dom_def
      by auto
    then obtain t where
      t: "(obj,t) \<in> set (consts DD @ objects PD)" 
      "of_type t ty"
      by auto
    from wf_problem_decs
    have "distinct (map fst (consts DD @ objects PD))"
      unfolding wf_problem_decs_def
      by auto
    with t
    have "map_of (consts DD @ objects PD) obj = Some t"
      using map_of_is_SomeI
      by metis
    with t
    show "\<exists>ty'. objT obj = Some ty' \<and> of_type ty' ty"
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
        by (metis True VAR assms(1) of_type_trans calculation term_subst.simps(1) ty_term.simps(2) c_ty)
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
    assumes "v \<notin> f_vars \<phi>"
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
    using wf_Big_Or[OF assms] wf_fmla_upd assms unfolding exists_def by auto
  
  lemma wf_ex_inst:
    assumes "wf_fmla (ty_term (Q(v \<mapsto> ty)) objT) \<phi>" 
      shows "wf_fmla (ty_term Q objT) \<^bold>\<exists>v - ty. \<phi>"
    using wf_fmla_mono'[OF wf_ex_inst'] assms unfolding exists_def by auto

  
  (* Note: The other direction does not work. Quantifiers expand into long con-/disjunctions 
            by substitution of variables for all suitably typed constants. Assume there is a 
            predicate P::t2 \<Rightarrow> bool, a v::t1, t2 \<subseteq> t1, and the only
            object o1 in the domain of t1 has a type t2. In this case, P(v) is not
            well-formed, but the instantiation P(o1) is. *)
  
  lemma wf_ex_goal: 
    assumes "wf_fmla (ty_term [v \<mapsto> ty] objT) \<phi>" 
      shows "wf_goal \<^bold>\<exists>v - ty. \<phi>"
    unfolding wf_goal_def using wf_ex_inst'[OF assms] by simp

  lemma wf_ex_goal_alt:
    assumes "wf_fmla (ty_term (Q(v \<mapsto> ty)) objT) \<phi>"
        and "f_vars \<phi> \<subseteq> {v}"
      shows "wf_goal \<^bold>\<exists>v - ty. \<phi>"
    using assms wf_fmla_alt_lemma[of "Map.empty(v \<mapsto> ty)" "(Q(v \<mapsto> ty))"] wf_ex_goal by simp
    
    
  lemma wf_univ_inst':
    assumes "wf_fmla (ty_term (Q(v \<mapsto> ty)) objT) \<phi>" 
      shows "wf_fmla (ty_term (Q(v := None)) objT) \<^bold>\<forall>v - ty. \<phi>"
    using wf_Big_And[OF assms] wf_fmla_upd assms unfolding all_def by auto
  
  lemma wf_univ_inst:
    assumes "wf_fmla (ty_term (Q(v \<mapsto> ty)) objT) \<phi>" 
      shows "wf_fmla (ty_term Q objT) \<^bold>\<forall>v - ty. \<phi>"
    using wf_fmla_mono'[OF wf_univ_inst'] assms unfolding all_def by auto
  
  lemma wf_univ_goal: 
    assumes "wf_fmla (ty_term [v \<mapsto> ty] objT) \<phi>" 
      shows "wf_goal \<^bold>\<forall>v - ty. \<phi>"
    using wf_univ_inst'[OF assms] unfolding wf_goal_def by simp

   lemma wf_univ_goal_alt:
    assumes "wf_fmla (ty_term (Q(v \<mapsto> ty)) objT) \<phi>"
        and "f_vars \<phi> \<subseteq> {v}"
      shows "wf_goal \<^bold>\<forall>v - ty. \<phi>"
    using assms wf_fmla_alt_lemma[of "Map.empty(v \<mapsto> ty)" "(Q(v \<mapsto> ty))"] wf_univ_goal by simp


end \<comment> \<open>Context of \<open>wf_problem_decs\<close>\<close>

subsection \<open>PDDL Semantics\<close>


context ast_domain begin

  definition resolve_action_schema :: "name \<rightharpoonup> ast_action_schema" where
    "resolve_action_schema n = index_by ast_action_schema.name (actions D) n"

  fun subst_sym where
    "subst_sym psubst (Var x) = psubst x"
  | "subst_sym psubst (Const c) = c"

 text \<open>To instantiate an action schema, we first compute a substitution from
    parameters to objects, and then apply this substitution to the
    precondition and effect. The substitution is applied via the \<open>map_xxx\<close>
    functions generated by the datatype package.
    \<close>

  fun ssubst where
  "ssubst params as = subst_sym (the o (map_of (zip (map fst params) as)))"

  fun tsubst where
  "tsubst params as = map_term (ssubst params as)"

  fun inst_pre where
  "inst_pre t pre = (map_formula (map_atom t)) pre" 

  fun instantiate_action_schema
    :: "ast_action_schema \<Rightarrow> object list \<Rightarrow> ground_action"
  where
    "instantiate_action_schema (Action_Schema n params pre eff) as = (let
        tsubst = tsubst params as;
        pre_inst = inst_pre tsubst pre;
        eff_inst = map (\<lambda>(p, e).((map_formula (map_atom tsubst)) p, map_ast_effect tsubst e)) eff
      in
        Ground_Action pre_inst eff_inst
      )"

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

subsection \<open>Instantiation\<close>

context ast_problem begin

  text \<open>Initial model\<close>
  definition I :: "world_model" where
    "I \<equiv> init P"

  text \<open>Resolve a plan action and instantiate the referenced action schema.\<close>
  fun resolve_instantiate :: "plan_action \<Rightarrow> ground_action" where
    "resolve_instantiate (PAction n as) =
      instantiate_action_schema
        (the (resolve_action_schema n))
        as"

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
  definition "action_params_match a as
    \<equiv> list_all2 is_obj_of_type as (map snd (parameters a))"

  text \<open>At this point, we can define well-formedness of a plan action:
    The action must refer to a declared action schema, the arguments must
    be compatible with the formal parameters' types.
  \<close>
 (* Objects are valid and match parameter types *)
  fun wf_plan_action :: "plan_action \<Rightarrow> bool" where
    "wf_plan_action (PAction n as) = (
      case resolve_action_schema n of
        None \<Rightarrow> False
      | Some a \<Rightarrow>
          action_params_match a as
        \<and> wf_cond_effect_inst_list (effects (instantiate_action_schema a as))
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
  "inst_goal \<phi> = (let tsubst = map_term (subst_sym (the o (Map.empty)))
        in (map_formula o map_atom) tsubst \<phi>)"
  
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
  lemma "valid_plan \<pi>s \<equiv> \<exists>M'. plan_action_path I \<pi>s M' \<and> valuation M' \<Turnstile> inst_goal (goal P)"
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

  fun wf_ground_action :: "ground_action \<Rightarrow> bool" where
    "wf_ground_action (Ground_Action pre eff) \<longleftrightarrow> (
        wf_fmla (ty_term objT obj_fluent_sig) pre
      \<and> wf_cond_effect_list (ty_term objT obj_fluent_sig) eff
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

end

subsubsection \<open>Preservation\<close>

context ast_problem
begin

  definition wf_active_effect :: "fully_instantiated_effect \<Rightarrow> bool" where

  text \<open>Shorthand for enabled plan action: It is well-formed, and the
    precondition holds for its instance.\<close>
  definition plan_action_enabled :: "plan_action \<Rightarrow> world_model \<Rightarrow> bool" where
    "plan_action_enabled \<pi> M
      \<longleftrightarrow> wf_plan_action \<pi> \<and> valuation M \<Turnstile> precondition (resolve_instantiate \<pi>)"

  text \<open>Shorthand for executing a plan action: Resolve, instantiate, and
    apply effect\<close>
  definition execute_plan_action :: "plan_action \<Rightarrow> world_model \<Rightarrow> world_model"
    where "execute_plan_action \<pi> M
      = (apply_effects (effects (resolve_instantiate \<pi>)) M)"

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
  
  text \<open>We start by defining two shorthands for enabledness and execution of
    a plan action.\<close>


  text \<open>The initial world model is well-formed\<close>
  lemma wf_I: "wf_world_model I"
    using wf_problem
    unfolding I_def wf_world_model_def wf_problem_def wf_problem_decs_def wf_domain_def wf_domain_decs_def
    by safe

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
      unfolding wf_domain_def
      by blast
    from \<open>resolve_action_schema name = Some a\<close> have
      "a \<in> set (actions D)"
      unfolding resolve_action_schema_def by auto
    with wf_problem have "wf_action_schema a"
      unfolding wf_problem_def wf_domain_def by auto
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

end

subsubsection \<open>Semantics of quantifiers under instantiation\<close>

text \<open>Here are some lemmas that prove that the semantics of quantified formulas
      are correct following instantiation. If we have a goal or an action schema that
      used a macro expansion for formulae with quantifiers, we can be sure that its 
      semantics are behaving as we expected.\<close>
context ast_problem begin
  
  notation all ("\<^bold>\<forall>_ - _._")   
  notation exists ("\<^bold>\<exists>_ - _._")

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
      assume a: "v \<notin> f_vars \<phi> \<and> t_dom ty \<noteq> []"
      hence "\<^bold>\<forall>v - ty. \<phi> = \<phi>" unfolding all_def by auto
      hence "\<A> \<Turnstile> (f \<^bold>\<forall>v - ty. \<phi>) \<longleftrightarrow> \<A> \<Turnstile> f \<phi>" by presburger
      moreover from a
      have "\<forall>c. map_formula (term_atom_subst v c) \<phi> = \<phi>" using subst_idem by (induction \<phi>) auto
      hence "(\<forall>c\<in>set (t_dom ty). \<A> \<Turnstile> f \<phi>) \<longleftrightarrow> (\<forall>c\<in>set (t_dom ty). \<A> \<Turnstile> f (map_formula (term_atom_subst v c) \<phi>))" by simp
      ultimately show ?thesis unfolding all_def using a by blast
    next
      assume "\<not>(v \<notin> f_vars \<phi> \<and> t_dom ty \<noteq> [])"
      hence "\<A> \<Turnstile> (f \<^bold>\<forall>v - ty. \<phi>) \<longleftrightarrow> \<A> \<Turnstile> (f \<^bold>\<And>(map (\<lambda>c. map_formula (term_atom_subst v c) \<phi>) (t_dom ty)))" unfolding all_def by force
      also have "... \<longleftrightarrow> (\<forall>\<phi> \<in> set (map (\<lambda>c. map_formula (term_atom_subst v c) \<phi>) (t_dom ty)). \<A> \<Turnstile> f \<phi>)" using Big_And_sem by blast
      also have "... \<longleftrightarrow> (\<forall>c \<in> set (t_dom ty). \<A> \<Turnstile> f (map_formula (term_atom_subst v c) \<phi>))" by auto
      finally show ?thesis .
    qed

    lemma ex_inst: "\<A> \<Turnstile> (f \<^bold>\<exists>v - ty. \<phi>) \<longleftrightarrow>
      (\<exists>c \<in> set (t_dom ty). \<A> \<Turnstile> f (map_formula (term_atom_subst v c) \<phi>))"
    proof cases
      assume a: "v \<notin> f_vars \<phi> \<and> t_dom ty \<noteq> []"
      hence "\<A> \<Turnstile> (f \<^bold>\<exists>v - ty. \<phi>) \<longleftrightarrow> \<A> \<Turnstile> f \<phi>" unfolding exists_def by auto
      moreover from a
      have "\<forall>c. map_formula (term_atom_subst v c) \<phi> = \<phi>" using subst_idem by (induction \<phi>) auto
      hence "(\<exists>c\<in>set (t_dom ty). \<A> \<Turnstile> f \<phi>) \<longleftrightarrow> (\<exists>c\<in>set (t_dom ty). \<A> \<Turnstile> f (map_formula (term_atom_subst v c) \<phi>))" by simp
      ultimately show ?thesis using a by blast
    next
      assume "\<not>(v \<notin> f_vars \<phi> \<and> t_dom ty \<noteq> [])"
      hence "\<A> \<Turnstile> (f \<^bold>\<exists>v - ty. \<phi>) \<longleftrightarrow> \<A> \<Turnstile> (f \<^bold>\<Or>(map (\<lambda>c. map_formula (term_atom_subst v c) \<phi>) (t_dom ty)))" unfolding exists_def by force
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

end \<comment> \<open>Theory\<close>
