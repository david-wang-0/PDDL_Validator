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

context 
  fixes varT::"variable \<rightharpoonup> type"
    and objT::"object \<rightharpoonup> type"
begin
  fun ty_vn::"var_num \<Rightarrow> type option" where
    "ty_vn (var_num.Var v) = varT v"
  | "ty_vn (var_num.Num n) = Some Number"

  fun ty_vnd::"var_num_dur \<Rightarrow> type option" where
    "ty_vnd (var_num_dur.Var v) = varT v"
  | "ty_vnd (var_num_dur.Num n) = Some Number"
  | "ty_vnd (var_num_dur.Duration) = Some Number"

  fun ty_isym::"instant_symbol \<Rightarrow> type option" where
    "ty_isym (instant_symbol.Var v) = varT v"
  | "ty_isym (instant_symbol.Const c) = objT c"
  | "ty_isym (instant_symbol.Num n) = Some Number"

  fun ty_sym::"symbol \<Rightarrow> type option" where
    "ty_sym (symbol.Var v) = varT v"
  | "ty_sym (symbol.Const c) = objT c"
  | "ty_sym (symbol.Num v) = Some Number"
  | "ty_sym symbol.Duration = Some Number"

  fun ty_ent::"entity \<Rightarrow> type option" where
    "ty_ent (entity.Const c) = objT c"
  | "ty_ent (entity.Num n) = Some Number"
end

fun is_some::"'a option \<Rightarrow> bool" where
  "is_some (Some _) = True"
| "is_some None = False"

text \<open>Cleaner type- and well-formedness-checks.\<close>
context 
  fixes ty_e::"'a \<rightharpoonup> type"
    and of_type::"type \<Rightarrow> type \<Rightarrow> bool"
begin
  text \<open>Checks whether an entity has a given type\<close>
  definition is_of_type :: "'a \<Rightarrow> type \<Rightarrow> bool" where
    "is_of_type v T \<longleftrightarrow> (
      case ty_e v of
        Some vT \<Rightarrow> of_type vT T
      | None \<Rightarrow> False)"
end

context (* finding the type of terms *)
  fixes ty_e::"'a \<rightharpoonup> type"
    and ty_f::"func \<rightharpoonup> (type list \<times> type)" (* need this for executability *)
    and of_type::"type \<Rightarrow> type \<Rightarrow> bool" 
begin
(* well-formedness will anyways recurse, 
    so separate return types and argument types *)

  fun ty_term::"'a term \<Rightarrow> type option" where
    "ty_term (Sym a) = ty_e a"
  | "ty_term (Fun f as) = map_option snd (ty_f f)"
  
  fun wf_term::"'a term \<Rightarrow> bool" where
    "wf_term (Sym a) = is_some (ty_e a)"
  | "wf_term (Fun f as) = (case (ty_f f) of 
      Some (Ts, T) \<Rightarrow> list_all2 (is_of_type ty_term of_type) as Ts 
    | None \<Rightarrow> False)"
end

context 
  fixes ty_p::"pred \<rightharpoonup> type list"
    and ty_t::"'t \<rightharpoonup> type"
    and wf_t::"(type \<Rightarrow> type \<Rightarrow> bool) \<Rightarrow> 't \<Rightarrow> bool"
    and of_type::"type \<Rightarrow> type \<Rightarrow> bool"
begin
fun wf_atom::"'t atom \<Rightarrow> bool" where
  "wf_atom (Pred p as) = (case (ty_p p) of 
    Some Ts \<Rightarrow> 
      list_all2 (is_of_type ty_t of_type) as Ts 
      \<and> list_all (wf_t of_type) as
  | None \<Rightarrow> False)"
| "wf_atom (Ent_Eq a b) = (wf_t of_type a \<and> wf_t of_type b)"
| "wf_atom (Num_Lt a b) = (
    wf_t of_type a \<and> wf_t of_type b 
    \<and> ty_t a = Some Number \<and> ty_t b = Some Number)"
| "wf_atom (Num_Le a b) = (
    wf_t of_type a \<and> wf_t of_type b 
    \<and> ty_t a = Some Number \<and> ty_t b = Some Number)"
end

type_synonym simple_action_schema = "symbol term simple_action_body"

datatype durative_action_schema =
  DA_Schema (duration: "ast_duration_constraint list")
    (condition: "ast_da_GD")
    (effect: "ast_durative_effect")
  "((variable \<times> type) list, instant_symbol term) da_GD"
  "((variable \<times> type) list, symbol term) durative_effect"

type_synonym action_schema_body = "(simple_action_schema, durative_action_schema) action_body"

type_synonym action_schema = "action_schema_body action"

section \<open>Well-formedness\<close>
locale ast_domain =
  fixes D::ast_domain
begin

  fun subtype_edge where
    "subtype_edge (ty,superty) = (superty,ty)"

  text \<open>We have to think of types as sets of primitive types.
        The subtype relationship is the relation from every primitive type to
        its direct subtypes\<close>
  definition "subtype_rel \<equiv> set (map subtype_edge (types D))"

  definition of_type :: "type \<Rightarrow> type \<Rightarrow> bool" where
    "of_type oT T \<equiv> set (primitives oT) \<subseteq> subtype_rel\<^sup>* `` set (primitives T)"


(* disambiguation of parsed terms *)
(* var_num to instant_symbol *)
(* var_num_dur to symbol *)

fun vn_to_is::"var_num \<Rightarrow> instant_symbol" where
  "vn_to_is (var_num.Num n) = instant_symbol.Num n"
| "vn_to_is (var_num.Var v) = instant_symbol.Var v"

fun vnd_to_sym::"var_num_dur \<Rightarrow> symbol" where
  "vnd_to_sym (var_num_dur.Num n) = symbol.Num n"
| "vnd_to_sym (var_num_dur.Var v) = symbol.Var v"
| "vnd_to_sym (var_num_dur.Duration) = symbol.Duration"

context
  fixes is_const::"name \<Rightarrow> bool"
    and val_map::"'e \<Rightarrow> 'f"
    and to_const::"name \<Rightarrow> 'f"
begin
definition disambiguate_term::"'e term \<Rightarrow> 'f term" where
  "disambiguate_term t \<equiv> (case (map_term val_map t) of
    Sym e \<Rightarrow> Sym e
  | Fun f [] \<Rightarrow> if (is_const f) then Sym (to_const f) else Fun f []
  | Fun f as \<Rightarrow> Fun f as
  )"
end

definition is_obj::"name \<Rightarrow> bool" where
  "is_obj n \<equiv> n \<in> set (map (obj_name o fst) (consts D))"

abbreviation "ast_instant_term_to_schema \<equiv> disambiguate_term is_obj vn_to_is (instant_symbol.Const o Object)"

abbreviation "ast_durative_term_to_schema \<equiv> disambiguate_term is_obj vnd_to_sym (symbol.Const o Object)"


(* symbol to instant_symbol *)
(* instant_symbol to entity *)
context (* instantiation of terms *)
  fixes e::"'a \<Rightarrow> 'b" 
begin 
  
end

fun ast_action_to_action_schema::"ast_action \<Rightarrow> action_schema"

definition action_schemas::"action_schema list" where
  "action_schemas = actions D"

  definition constT :: "object \<rightharpoonup> type" where
    "constT \<equiv> map_of (consts D)"

  find_theorems name: "literal*rep"

  text \<open>A type must consist of at least one primitive.\<close>
  abbreviation "wf_prims Ts \<equiv> Ts \<noteq> [] \<and> set Ts \<subseteq> insert (''object'') (fst`set (types D))"
             
  text \<open>An object cannot be a number.\<close>
  fun wf_obj_type where
    "wf_obj_type (Either Ts) \<longleftrightarrow> wf_prims Ts"
  | "wf_obj_type Number = False"

  text \<open>Predicates cannot be defined with numeric parameters.\<close>
  fun wf_pred_decl where
    "wf_pred_decl (PredDecl p Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. wf_obj_type T)"

  
  text \<open>Numbers are not invalid types.\<close>
  fun wf_type where
    "wf_type (Either Ts) \<longleftrightarrow> wf_prims Ts"
  | "wf_type Number = True"

  text \<open>Functions cannot be defined with numeric parameters.\<close>
  fun wf_fun_decl where
    "wf_fun_decl (FunDecl f Ts T) =
      ((\<forall>T\<in>set Ts. wf_obj_type T) \<and> wf_type T)"

(*  \<and> f \<notin> {''+'', ''-'', ''*'', ''/''} *)

  text \<open>It is only possible to inherit from a declared type or object. It is not
        possible to inherit from number.\<close>
  definition "wf_types \<equiv> 
    snd`set (types D) \<subseteq> insert ''object'' (fst`set (types D)) 
    \<and> (''number'' \<notin> fst ` set (types D))"
  
  definition fun_sig::"func \<rightharpoonup> (type list \<times> type)" where
    "fun_sig \<equiv> map_of (map (\<lambda>FunDecl f ts t \<Rightarrow> (f, (ts, t))) (funs D))"

  text \<open>The only functions which are allowed to take numeric arguments are 
          predefined.\<close>
  definition nf_sig::"func \<rightharpoonup> (type list \<times> type)" where
    "nf_sig f = (
      if (f = ''+'' \<or> f = ''-'' \<or> f = ''*'' \<or> f = ''/'') 
      then Some ([Number, Number], Number) 
      else fun_sig f)"

  fun wf_action_schema :: "ast_action \<Rightarrow> bool" where
    "wf_action_schema (AST_Action n p body) \<longleftrightarrow> (
        let tyt = ty_term (ty_sym (map_of params) objT)
        in
        distinct (map fst params)
      \<and> wf_fmla tyt pre
      \<and> wf_effect tyt effs)"

  text \<open>The declarations in a domain are well-formed if 
    \<^item> Types are well-formed,
    \<^item> No duplicate predicate names
    \<^item> Declared predicates cannot be applied to numbers
    \<^item> No ambiguous fluent/constant declarations
    \<^item> Functions cannot be applied to numbers
    \<^item> Constants are not numeric
    \<^item> Actions are distinctly named
    \<^item> Actions are well-formed.\<close>

  definition wf_domain :: "bool" where
    "wf_domain \<equiv>
      wf_types
    \<and> distinct (map (pred_decl.predicate) (preds D))
    \<and> (\<forall>p\<in>set (preds D). wf_pred_decl p)
    \<and> distinct (map f_name (funs D) @ (map (obj_name o fst) (consts D)))
    \<and> (\<forall>f \<in> set (funs D). wf_fun_decl f)
    \<and> (\<forall>(c, T) \<in> set (consts D). wf_obj_type T)
    \<and> distinct (map action.name (actions D))
    \<and> (\<forall>a\<in>set (actions D). wf_action_schema a)"



lemma "wf_type T \<Longrightarrow> of_type T Number \<Longrightarrow> T = Number"
  by (cases T, auto simp: of_type_def subtype_rel_def)
  
fun filter_map::"('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "filter_map f [] = []"
| "filter_map f (a#as) = (case f a of Some b \<Rightarrow> (b # (filter_map f as)) | None \<Rightarrow> filter_map f as)"
end
text \<open>Locale to express a well-formed domain\<close>
locale wf_ast_domain = ast_domain +
  assumes wf_domain: wf_domain
begin
  (* TODO: function arguments cannot be  *)
end
context ast_domain
begin

definition "obj_fun_names = set (map of_name (ofs D))"
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


context
  fixes varT::"variable \<rightharpoonup> type"
    and objT::"object \<rightharpoonup> type"
  assumes le: "varT \<subseteq>\<^sub>m varT'" "objT \<subseteq>\<^sub>m objT'"
begin

  lemma ty_vn_mono: "ty_vn varT \<subseteq>\<^sub>m ty_vn varT'"
    apply (rule map_leI)
    subgoal for x v 
      using le 
      by (cases x, auto dest: map_leD)
    done

  lemma ty_vnd_mono: "ty_vnd varT \<subseteq>\<^sub>m ty_vnd varT' "
    apply (rule map_leI)
    subgoal for x v 
      using le 
      by (cases x, auto dest: map_leD)
    done

  lemma ty_isym_mono: "ty_isym varT objT \<subseteq>\<^sub>m ty_isym varT' objT'"
    apply (rule map_leI)
    subgoal for x v 
      using le 
      by (cases x, auto dest: map_leD)
    done
  
  lemma ty_sym_mono: "ty_sym varT objT \<subseteq>\<^sub>m ty_sym varT' objT'"
    apply (rule map_leI)
    subgoal for x v 
      using le 
      by (cases x, auto dest: map_leD)
    done

  lemma ty_ent_mono: "ty_ent objT \<subseteq>\<^sub>m ty_ent objT'"
    apply (rule map_leI)
    subgoal for x v 
      using le 
      by (cases x, auto dest: map_leD)
    done
end

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