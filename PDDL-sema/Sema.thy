theory Sema
  imports States
  "Show.Show_Instances" 
  Util
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

type_synonym simple_action_schema = "symbol term simple_action"
type_synonym durative_action_schema = "symbol term durative_action"

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

abbreviation "disambiguate_f_exp \<equiv> map_f_exp disambiguate_term"

fun f_exp_eq_to_eq::"variable term f_exp \<Rightarrow> variable term f_exp \<Rightarrow> symbol term atom" where
  "f_exp_eq_to_eq (f_exp.NFun f1 as1) (f_exp.NFun f2 as2) = 
    (if (f1 \<in> obj_names \<or> f2 \<in> obj_names \<or> f1 \<in> obj_fun_names \<or> f2 \<in> obj_fun_names) 
    then Ent_Eq (disambiguate_term (Fun f1 as1)) (disambiguate_term (Fun f2 as2))
    else Num_Eq (f_exp.NFun f1 (map disambiguate_term as1)) (f_exp.NFun f2 (map disambiguate_term as2))
   )"
| "f_exp_eq_to_eq e1 e2 = Num_Eq (disambiguate_f_exp e1) (disambiguate_f_exp e2)"

(* Equality cannot be unambiguously parsed, so we have this pre-processing step *)
fun disambiguate_atom::"variable term atom \<Rightarrow> symbol term atom" where
  "disambiguate_atom (Pred p as) = Pred p (map disambiguate_term as)"
| "disambiguate_atom (Ent_Eq a b) = Ent_Eq (disambiguate_term a) (disambiguate_term b)"
| "disambiguate_atom (Num_Eq a b) = f_exp_eq_to_eq a b"
| "disambiguate_atom (Num_Le a b) = Num_Le (disambiguate_f_exp a) (disambiguate_f_exp b)"
| "disambiguate_atom (Num_Lt a b) = Num_Lt (disambiguate_f_exp a) (disambiguate_f_exp b)"

fun process_ast_simple_action::"ast_simple_action \<Rightarrow> simple_action_schema" where
  "process_ast_simple_action (Simple_Action n p pre eff) = 
    Simple_Action n p (map_pre_GD id disambiguate_atom pre) (map_simple_effect id disambiguate_term eff)"

fun process_ast_durative_action::"ast_durative_action \<Rightarrow> durative_action_schema" where
  "process_ast_durative_action (Durative_Action n d p pre eff) =
    Durative_Action n (map (map_duration_constraint disambiguate_term) d) p (map_da_GD id disambiguate_atom pre) (map_durative_effect id disambiguate_term eff)"

abbreviation simple_actions::"ast_action list \<Rightarrow> simple_action_schema list" where
  "simple_actions \<equiv> filter_map (\<lambda>(SA a) \<Rightarrow> Some (process_ast_simple_action a) | _ \<Rightarrow> None)"

definition simple_action_schemas where
  "simple_action_schemas \<equiv> simple_actions (actions D)"

abbreviation durative_actions::"ast_action list \<Rightarrow> durative_action_schema list" where
  "durative_actions \<equiv> filter_map (\<lambda>(DA a) \<Rightarrow> Some (process_ast_durative_action a) | _ \<Rightarrow> None)"

definition durative_action_schemas where
  "durative_action_schemas \<equiv> durative_actions (actions D)"

abbreviation resolve_simple_action_schema::"name \<rightharpoonup> simple_action_schema" where
  "resolve_simple_action_schema \<equiv> index_by simple_action.name simple_action_schemas"

abbreviation resolve_durative_action_schema::"name \<rightharpoonup> durative_action_schema" where
  "resolve_durative_action_schema \<equiv> index_by durative_action.name durative_action_schemas"

end

datatype ('x, 'a) fixed_GD =
  Over time time "('x, 'a) GD"
  | At time "('x, 'a) GD"

datatype ('x, 'a) fixed_da_GD =
  ForAll 'x "('x, 'a) fixed_da_GD"
  | And "('x, 'a) fixed_da_GD" "('x, 'a) fixed_da_GD"
  | FixedPrefGD "pref option" "('x, 'a) fixed_GD"

(* Simple update to a state at a certain time *)
type_synonym 'ent timed_update = "(time \<times> 'ent simple_update)"

(* Continuous update to some function symbol. Not supported. *) 
(* type_synonym 'ent timed_continuous_effect = "time \<times> time \<times> func \<times> symbol term list \<times> symbol term f_exp_t" *)

datatype 'ent fixed_upd =
  UpdAt "time" "'ent simple_update"
(*
  | ContUpd "'ent timed_continuous_effect"
*)
(* We use this to represent a durative effect, of which the start and end are known *)
datatype ('x, 'ent) fixed_effect = 
    FUpd "'ent fixed_upd"
  | FE_When "('x, 'ent atom) fixed_da_GD" "'ent fixed_upd"
  | FE_And "('x, 'ent) fixed_effect" "('x, 'ent) fixed_effect"
  | FE_All "'x" "('x, 'ent) fixed_effect"

datatype ('x, 'ent) fixed_timed_action =
  FTA (prec: "('x, 'ent atom) fixed_da_GD")
    (eff: "('x, 'ent) fixed_effect")

type_synonym dur_eff_1 = "((variable \<times> type) list, symbol term) durative_effect"

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

fun pre_GD_to_GD::"('x, 'a) pre_GD \<Rightarrow> ('x, 'a) GD" where
  "pre_GD_to_GD (pre_GD.PrefGD None \<phi>) = \<phi>"
| "pre_GD_to_GD (pre_GD.PrefGD (Some pref) \<phi>) = GD.Not GD.Bot"
| "pre_GD_to_GD (pre_GD.ForAll vs \<phi>) = GD.ForAll vs (pre_GD_to_GD \<phi>)"
| "pre_GD_to_GD (pre_GD.And f g) = GD.And (pre_GD_to_GD f) (pre_GD_to_GD g)"

fun fix_timed_GD::"time \<Rightarrow> time \<Rightarrow> ('x, 'a) timed_GD \<Rightarrow> ('x, 'a) fixed_GD" where
  "fix_timed_GD start dur (OverAll f) = Over start (start + dur) f"
| "fix_timed_GD start dur (AtStart f) = At start f"
| "fix_timed_GD start dur (timed_GD.AtEnd f) = At (start + dur) f"

fun fix_da_GD::"time \<Rightarrow> time \<Rightarrow> ('x, 'a) da_GD \<Rightarrow> ('x, 'a) fixed_da_GD" where
  "fix_da_GD start dur (da_GD.ForAll v f) = fixed_da_GD.ForAll v (fix_da_GD start dur f)" 
| "fix_da_GD start dur (da_GD.And f g) = fixed_da_GD.And (fix_da_GD start dur f) (fix_da_GD start dur g)"
| "fix_da_GD start dur (da_GD.PrefTimedGD pref f) = fixed_da_GD.FixedPrefGD pref (fix_timed_GD start dur f)"

fun f_exp_da_to_f_exp::"time \<Rightarrow> 'ent f_exp_da \<Rightarrow> 'ent f_exp" where 
  "f_exp_da_to_f_exp dur Duration = f_exp.Num dur"
| "f_exp_da_to_f_exp _ (f_exp_da.NFun f as) = f_exp.NFun f as"
| "f_exp_da_to_f_exp _ (f_exp_da.Num n) = f_exp.Num n"
| "f_exp_da_to_f_exp dur (f_exp_da.Neg e) = f_exp.Neg (f_exp_da_to_f_exp dur e)"
| "f_exp_da_to_f_exp dur (f_exp_da.Add e f) = f_exp.Add (f_exp_da_to_f_exp dur e) (f_exp_da_to_f_exp dur f)"
| "f_exp_da_to_f_exp dur (f_exp_da.Sub e f) = f_exp.Sub (f_exp_da_to_f_exp dur e) (f_exp_da_to_f_exp dur f)"
| "f_exp_da_to_f_exp dur (f_exp_da.Mult e f) = f_exp.Mult (f_exp_da_to_f_exp dur e) (f_exp_da_to_f_exp dur f)"
| "f_exp_da_to_f_exp dur (f_exp_da.Div e f) = f_exp.Div (f_exp_da_to_f_exp dur e) (f_exp_da_to_f_exp dur f)"

fun durative_update_to_simple_update::"time \<Rightarrow> 't durative_update \<Rightarrow> 't simple_update" where
  "durative_update_to_simple_update _ (D_Add a) = S_Add a"
| "durative_update_to_simple_update _ (D_Del a) = S_Del a"
| "durative_update_to_simple_update _ (D_OU u) = S_OU u"
| "durative_update_to_simple_update t (D_NU u) = S_NU (map_nf_upd id (f_exp_da_to_f_exp t) u)"

fun fix_timed_effect::"time \<Rightarrow> time \<Rightarrow> 't timed_effect \<Rightarrow> 't fixed_upd" where
  "fix_timed_effect start dur (DUpd_At_Start e) = UpdAt start (durative_update_to_simple_update dur e)"
| "fix_timed_effect start dur (DUpd_At_End e) = UpdAt (start + dur) (durative_update_to_simple_update dur e)"
(* continuous effects are not supported *)

fun fix_durative_effect::"time \<Rightarrow> time \<Rightarrow> ('x, 't) durative_effect \<Rightarrow> ('x, 't) fixed_effect" where
  "fix_durative_effect start dur (Timed_Effect e) = FUpd (fix_timed_effect start dur e)"
| "fix_durative_effect start dur (DEff_And a b) = FE_And (fix_durative_effect start dur a) (fix_durative_effect start dur b)"
| "fix_durative_effect start dur (DEff_All vs e) = FE_All vs (fix_durative_effect start dur e)"
| "fix_durative_effect start dur (DEff_When f e) = FE_When (fix_da_GD start dur f) (fix_timed_effect start dur e)"


definition ground_PDDL_GD::"(symbol \<Rightarrow> object) \<Rightarrow> ((variable \<times> type) list, symbol term atom) GD \<Rightarrow> (unit, object term atom) GD" where
  "ground_PDDL_GD f \<phi> = ground_GD f (replace_types_with_objects t_dom (split_quant \<phi>))"



fun ground_fixed_effect::"(symbol \<Rightarrow> object) \<Rightarrow> ((variable \<times> type) list, symbol term) fixed_effect \<Rightarrow> (unit, object term) fixed_effect" where
  "ground_fixed_effect f (FUpd e) = FUpd (map_fixed_upd (map_term f) e)"
| "ground_fixed_effect f (FE_And a b) = FE_And (ground_fixed_effect f a) (ground_fixed_effect f b)"


(*
fun ground_simple_action_schema::"(object \<times> type) list \<Rightarrow> simple_action_schema \<Rightarrow> unit" where
  "ground_simple_action_schema as (simple_action.Simple_Action n ps c e) = (
    let inst_sym = the o (map_of (zip (map fst ps) as));
        cf = ground_PDDL_GD f (pre_GD_to_GD c)
    in undefined
  )"

fun plan_action_to_happenings::"time \<Rightarrow> plan_action \<Rightarrow> (time \<times> unit)" where
  "plan_action_to_happenings t (Simple_Plan_Action n as) = (
    resolve_simple_action_schema n
  )"
| "plan_action_to_happenings t (Durative_Plan_Action n as dur) = undefined" 
 *)
end

end