theory Sema
  imports States
begin

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
  assumes "length ps = length args"
  assumes "i<length args"
  assumes "distinct ps"
  assumes "k = ps ! i"
  shows "map_of (zip ps args) k = Some (args ! i)"
  using assms
  by (auto simp: in_set_conv_nth)

lemma rtrancl_image_idem[simp]: "R\<^sup>* `` R\<^sup>* `` s = R\<^sup>* `` s"
  by (metis relcomp_Image rtrancl_idemp_self_comp)

datatype plan_action = 
  Simple_Plan_Action (name: name) (arguments: "object list")
| Durative_Plan_Action (name: name) (arguments: "object list") (duration: "rat option")

type_synonym plan = "plan_action list"


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


type_synonym form_schema = "((variable \<times> type) list, symbol term atom) pre_GD"
type_synonym simple_effect_schema = "((variable \<times> type) list, symbol term) simple_effect"

datatype simple_action_schema = SAction_Schema
  (name: name)
  (parameters: "(variable \<times> type) list")
  (precondition: form_schema)
  (effect: simple_effect_schema)

locale ast_domain =
  fixes D::ast_domain
begin

fun filter_map::"('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "filter_map f [] = []"
| "filter_map f (a#as) = (case f a of Some b \<Rightarrow> (b # (filter_map f as)) | None \<Rightarrow> filter_map f as)"



definition "obj_fun_names = set (map of_name (ofs D))"
definition "num_fun_names = set (map nf_name (nfs D))"
definition "obj_names = set (map (obj_name o fst) (consts D))"

fun disambiguate_term::"variable term \<Rightarrow> symbol term" where
  "disambiguate_term (Sym v) = Sym (Var v)"
| "disambiguate_term (Fun f (a#as)) = Fun f (map disambiguate_term (a#as))"
| "disambiguate_term (Fun f []) = (
    if f \<in> obj_names then Sym (Const (Object f)) else (Fun f [])
  )"

fun disambiguate_f_exp::"variable term f_exp \<Rightarrow> symbol term f_exp" where
  "disambiguate_f_exp (f_exp.NFun f as) = f_exp.NFun f (map disambiguate_term as)"
| "disambiguate_f_exp (f_exp.Num n) = f_exp.Num n"
| "disambiguate_f_exp (f_exp.Neg e) = f_exp.Neg (disambiguate_f_exp e)"
| "disambiguate_f_exp (f_exp.Add e f) = f_exp.Add (disambiguate_f_exp e) (disambiguate_f_exp f)"
| "disambiguate_f_exp (f_exp.Sub e f) = f_exp.Sub (disambiguate_f_exp e) (disambiguate_f_exp f)"
| "disambiguate_f_exp (f_exp.Mult e f) = f_exp.Mult (disambiguate_f_exp e) (disambiguate_f_exp f)"
| "disambiguate_f_exp (f_exp.Div e f) = f_exp.Div (disambiguate_f_exp e) (disambiguate_f_exp f)"

fun f_exp_eq_to_eq::"variable term f_exp \<Rightarrow> variable term f_exp \<Rightarrow> symbol term atom" where
  "f_exp_eq_to_eq (f_exp.NFun f1 as1) (f_exp.NFun f2 as2) = 
    (if (f1 \<in> obj_names \<or> f2 \<in> obj_names \<or> f1 \<in> obj_fun_names \<or> f2 \<in> obj_fun_names) 
    then Ent_Eq (disambiguate_term (Fun f1 as1)) (disambiguate_term (Fun f2 as2))
    else Num_Eq (f_exp.NFun f1 (map disambiguate_term as1)) (f_exp.NFun f2 (map disambiguate_term as2))
    )"

fun disambiguate_atom::"variable term atom \<Rightarrow> symbol term atom" where
  "disambiguate_atom (Pred p as) = Pred p (map disambiguate_term as)"
| "disambiguate_atom (Ent_Eq a b) = Ent_Eq (disambiguate_term a) (disambiguate_term b)"
| "dismabiguate_atom (

abbreviation simple_actions::"action_schema list \<Rightarrow> simple_action_schema list" where
  "simple_actions \<equiv> filter_map (\<lambda>(Simple_Action_Schema a) \<Rightarrow> Some a | _ \<Rightarrow> None)"

definition simple_action_schemas where
  "simple_action_schemas \<equiv> simple_actions (actions D)"

abbreviation durative_actions::"action_schema list \<Rightarrow> durative_action list" where
  "durative_actions \<equiv> filter_map (\<lambda>(Durative_Action_Schema a) \<Rightarrow> Some a | _ \<Rightarrow> None)"

definition durative_action_schemas where
  "durative_action_schemas \<equiv> durative_actions (actions D)"

abbreviation resolve_simple_action_schema::"name \<rightharpoonup> simple_action" where
  "resolve_simple_action_schema \<equiv> index_by simple_action.name simple_action_schemas"

abbreviation resolve_durative_action_schema::"name \<rightharpoonup> durative_action" where
  "resolve_durative_action_schema \<equiv> index_by durative_action.name durative_action_schemas"

end

type_synonym time = rat

datatype ('x, 'a) fixed_GD =
  Over time time "('x, 'a) GD"
  | At time "('x, 'a) GD"

datatype ('x, 'a) fixed_da_GD =
  ForAll 'x "('x, 'a) fixed_da_GD"
  | And "('x, 'a) fixed_da_GD" "('x, 'a) fixed_da_GD"
  | tGD "('x, 'a) fixed_GD"

(* Simple update to a state at a certain time *)
type_synonym 'ent timed_update = "(time \<times> 'ent simple_update)"

(* Continuous update to some function symbol *)
type_synonym 'ent timed_continuous_effect = "time \<times> time \<times> func \<times> symbol term list \<times> symbol term f_exp_t"

datatype 'ent fixed_timed_effect =
  EffAt "'ent timed_update"
  | EffCont "'ent timed_continuous_effect"

(* We use this to represent a durative effect, of which the start and end are known *)
datatype ('x, 'ent) fixed_durative_effect = 
  FTE "'ent fixed_timed_effect"
  | TWhen "('x, 'ent atom) fixed_da_GD" "'ent fixed_timed_effect"
  | TAnd "('x, 'ent) fixed_durative_effect" "('x, 'ent) fixed_durative_effect"
  | TAll "'x" "('x, 'ent) fixed_durative_effect"

datatype ('x, 'ent) fixed_timed_action =
  FTA (prec: "('x, 'ent atom) fixed_da_GD")
    (eff: "('x, 'ent) fixed_durative_effect")

type_synonym e_simple_update = "symbol term simple_update"
type_synonym e_effect = "(variable \<times> type, symbol term) fixed_durative_effect"
type_synonym e_action = "(variable \<times> type, symbol term) fixed_timed_action"
type_synonym e_timed_form = "(variable \<times> type, symbol term atom) fixed_GD"
type_synonym e_cond_form = "(variable \<times> type, symbol term atom) fixed_da_GD"
type_synonym e_form = "(variable \<times> type, symbol term atom) GD"

locale ast_problem = ast_domain "domain P"
  for P::ast_problem
begin
  abbreviation "D \<equiv> domain P"

  fun subtype_edge where
    "subtype_edge (ty,superty) = (superty,ty)"


  text \<open>We have to think of types as sets of primitive types.
        The subtype relationship is the relation from every primitive type to
        its direct subtypes\<close>
  definition "subtype_rel \<equiv> set (map subtype_edge (types D))"

  text \<open>To check whether a non-primitive type \<open>oT\<close> is a subtype of a different
        non-primitive type \<open>T\<close>.
        
        Every primitive type in \<open>oT\<close>, must be reachable from some primitive
        type in \<open>T\<close>. 

        Recall that \<open>``\<close> will take a relation \<open>('a \<times> 'b)\<close> and a set \<open>'a set\<close> and
        map it through the relation, finding the corresponding \<open>'b set\<close>.\<close>
  definition of_type :: "type \<Rightarrow> type \<Rightarrow> bool" where
    "of_type oT T \<equiv> set (primitives oT) \<subseteq> subtype_rel\<^sup>* `` set (primitives T)"
  
 definition t_dom::"type \<Rightarrow> object list" where
  "t_dom typ \<equiv> map fst (filter (\<lambda>(c, t). of_type t typ) (consts D @ objects P))"

(* remove preferences, because we do not need them *)
fun pref_GD_to_GD::"('x, 'a) pref_GD \<Rightarrow> ('x, 'a) GD" where
  "pref_GD_to_GD (pref_GD.Pref _ _) = GD.Not (GD.Bot)"
| "pref_GD_to_GD (GD \<phi>) = \<phi>"

fun pre_GD_to_GD::"('x, 'a) pre_GD \<Rightarrow> ('x, 'a) GD" where
  "pre_GD_to_GD (pre_GD.PrefGD \<phi>) = pref_GD_to_GD \<phi>"
| "pre_GD_to_GD (pre_GD.ForAll vs \<phi>) = GD.ForAll vs (pre_GD_to_GD \<phi>)"
| "pre_GD_to_GD (pre_GD.And f g) = GD.And (pre_GD_to_GD f) (pre_GD_to_GD g)"

fun f_exp_da_to_f_exp::"time \<Rightarrow> 'ent f_exp_da \<Rightarrow> 'ent f_exp" where 
  "f_exp_da_to_f_exp dur Duration = f_exp.Num dur"
| "f_exp_da_to_f_exp _ (f_exp_da.NFun f as) = f_exp.NFun f as"
| "f_exp_da_to_f_exp _ (f_exp_da.Num n) = f_exp.Num n"
| "f_exp_da_to_f_exp dur (f_exp_da.Neg e) = f_exp.Neg (f_exp_da_to_f_exp dur e)"
| "f_exp_da_to_f_exp dur (f_exp_da.Add e f) = f_exp.Add (f_exp_da_to_f_exp dur e) (f_exp_da_to_f_exp dur f)"
| "f_exp_da_to_f_exp dur (f_exp_da.Sub e f) = f_exp.Sub (f_exp_da_to_f_exp dur e) (f_exp_da_to_f_exp dur f)"
| "f_exp_da_to_f_exp dur (f_exp_da.Mult e f) = f_exp.Mult (f_exp_da_to_f_exp dur e) (f_exp_da_to_f_exp dur f)"
| "f_exp_da_to_f_exp dur (f_exp_da.Div e f) = f_exp.Div (f_exp_da_to_f_exp dur e) (f_exp_da_to_f_exp dur f)"

definition ground_PDDL_GD::"(symbol \<Rightarrow> object) \<Rightarrow> ((variable \<times> type) list, symbol term atom) GD \<Rightarrow> (unit, object term atom) GD" where
  "ground_PDDL_GD f \<phi> = ground_GD f (replace_types_with_objects t_dom (split_quant \<phi>))"

fun ground_simple_action_schema::"(object \<times> type) list \<Rightarrow> simple_action \<Rightarrow> unit" where
  "ground_simple_action_schema as (simple_action.Simple_Action_Schema n ps c e) = (
    let inst_sym = the o (map_of (zip (map fst ps) as));
        cf = ground_PDDL_GD f (pre_GD_to_GD c)
    in undefined
  )"

fun plan_action_to_happenings::"time \<Rightarrow> plan_action \<Rightarrow> (time \<times> unit)" where
  "plan_action_to_happenings t (Simple_Plan_Action n as) = (
    resolve_simple_action_schema n
  )"
| "plan_action_to_happenings t (Durative_Plan_Action n as dur) = undefined" 

end

end