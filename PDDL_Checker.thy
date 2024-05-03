section \<open>Executable PDDL Checker\<close>
theory PDDL_Checker
imports
  PDDL_Semantics

  Error_Monad_Add
  "HOL.String"

  (*"HOL-Library.Code_Char"     TODO: This might lead to performance loss! CHECK! *)
  "HOL-Library.Code_Target_Nat"

  "HOL-Library.While_Combinator"
  "HOL-Library.Cardinality"

  "Containers.Containers"
  "Containers.Set_Linorder"
begin

subsection \<open>Generic DFS Reachability Checker\<close>
text \<open>Used for subtype checks\<close>

text \<open>Creates a relation from a function. We have a function
      \<open>succ\<close> and that function maps one element \<open>u\<close> to some elements \<open>v\<close> (by adjacency).
      Then, here we get relation characterising which elements touch in a graph.\<close>
definition "E_of_succ succ \<equiv> { (u,v). v\<in>set (succ u) }"
lemma succ_as_E: "set (succ x) = E_of_succ succ `` {x}"
  unfolding E_of_succ_def by auto

context
  fixes succ :: "'a \<Rightarrow> 'a list"
begin

  private abbreviation (input) "E \<equiv> E_of_succ succ"


definition "dfs_reachable D w \<equiv>
  let (V,w,brk) = while (\<lambda>(V,w,brk). \<not>brk \<and> w\<noteq>[]) (\<lambda>(V,w,_).
    case w of v#w \<Rightarrow>
    if D v then (V,v#w,True)
    else if v\<in>V then (V,w,False)
    else
      let V = insert v V in
      let w = succ v @ w in
      (V,w,False)
    ) ({},w,False)
  in brk"

definition "dfs_all w \<equiv>
  let (V,w) = while (\<lambda>(V,w). w\<noteq>[]) (\<lambda>(V,w).
    case w of v#w \<Rightarrow>
    if v\<in>V then (V,w)
    else
      let V = insert v V in
      let w = succ v @ w in
      (V,w)
    ) ({},w)
  in V"


context
  fixes w\<^sub>0 :: "'a list"
  assumes finite_dfs_reachable[simp, intro!]: "finite (E\<^sup>* `` set w\<^sub>0)"
begin

  private abbreviation (input) "W\<^sub>0 \<equiv> set w\<^sub>0"
text \<open>A DFS can be used to traverse the graph representing the transitive closure of 
      a relation.\<close>
definition "dfs_reachable_invar D V W brk \<longleftrightarrow>
    W\<^sub>0 \<subseteq> W \<union> V
  \<and> W \<union> V \<subseteq> E\<^sup>* `` W\<^sub>0
  \<and> E``V \<subseteq> W \<union> V
  \<and> Collect D \<inter> V = {}
  \<and> (brk \<longrightarrow> Collect D \<inter> E\<^sup>* `` W\<^sub>0 \<noteq> {})"

definition "dfs_all_invar V W \<longleftrightarrow>
    W\<^sub>0 \<subseteq> W \<union> V
  \<and> W \<union> V \<subseteq> E\<^sup>* `` W\<^sub>0
  \<and> E``V \<subseteq> W \<union> V"

lemma card_decreases: "
   \<lbrakk>finite V; y \<notin> V; dfs_reachable_invar D V (Set.insert y W) brk \<rbrakk>
   \<Longrightarrow> card (E\<^sup>* `` W\<^sub>0 - Set.insert y V) < card (E\<^sup>* `` W\<^sub>0 - V)"
  apply (rule psubset_card_mono)
  by (auto simp: dfs_reachable_invar_def)

find_theorems name: folding

lemma all_neq_Cons_is_Nil[simp]: (* Odd term remaining in goal \<dots> *)
  "(\<forall>y ys. x2 \<noteq> y # ys) \<longleftrightarrow> x2 = []" by (cases x2) auto

lemma dfs_reachable_correct: "dfs_reachable D w\<^sub>0 \<longleftrightarrow> Collect D \<inter> E\<^sup>* `` set w\<^sub>0 \<noteq> {}"
  unfolding dfs_reachable_def
  thm while_rule
  apply (rule while_rule[where
    P="\<lambda>(V,w,brk). dfs_reachable_invar D V (set w) brk \<and> finite V"
    and r="measure (\<lambda>V. card (E\<^sup>* `` (set w\<^sub>0) - V)) <*lex*> measure length <*lex*> measure (\<lambda>True\<Rightarrow>0 | False\<Rightarrow>1)"
    ])
  subgoal by (auto simp: dfs_reachable_invar_def)
  subgoal by (auto simp: neq_Nil_conv succ_as_E[of succ] split: if_splits) (auto simp: dfs_reachable_invar_def Image_iff intro: rtrancl.rtrancl_into_rtrancl)
  subgoal by (fastforce simp: dfs_reachable_invar_def dest: Image_closed_trancl)
  subgoal by blast
  subgoal by (auto simp: neq_Nil_conv card_decreases)
  done

lemma card_decreases': "\<lbrakk>finite V; y \<notin> V; dfs_all_invar V (Set.insert y W) \<rbrakk>
   \<Longrightarrow> card (E\<^sup>* `` W\<^sub>0 - Set.insert y V) < card (E\<^sup>* `` W\<^sub>0 - V)"
  apply (rule psubset_card_mono)
  apply (auto simp: dfs_all_invar_def)
  done

lemma dfs_all_correct: "dfs_all w\<^sub>0 = E\<^sup>* `` set w\<^sub>0"
  unfolding dfs_all_def
  thm while_rule
  apply (rule while_rule[where
    P="\<lambda>(V, w). dfs_all_invar V (set w) \<and> finite V"
    and r="measure (\<lambda>V. card (E\<^sup>* `` (set w\<^sub>0) - V)) <*lex*> measure length"
    ])
  subgoal by (auto simp: dfs_all_invar_def)
  subgoal by (auto simp: neq_Nil_conv succ_as_E[of succ] split: if_splits) (auto simp: dfs_all_invar_def Image_iff intro: rtrancl.rtrancl_into_rtrancl)
  subgoal by (fastforce simp: dfs_all_invar_def dest: Image_closed_trancl)
  subgoal by blast
  subgoal by (auto simp: neq_Nil_conv card_decreases')
  done

end

(* maps every element to a list of elements that is reachable from it *)
definition "tab_succ l \<equiv> Mapping.lookup_default [] (
  fold (\<lambda>(u,v). Mapping.map_default u [] (Cons v)) l Mapping.empty
)"


lemma Some_eq_map_option [iff]: "(Some y = map_option f xo) = (\<exists>z. xo = Some z \<and> f z = y)"
  by (auto simp add: map_option_case split: option.split)


lemma tab_succ_correct: "E_of_succ (tab_succ l) = set l"
proof -
  have "set (Mapping.lookup_default [] (fold (\<lambda>(u,v). Mapping.map_default u [] (Cons v)) l m) u) = set l `` {u} \<union> set (Mapping.lookup_default [] m u)"
    for m u
    apply (induction l arbitrary: m)
    by (auto
      simp: Mapping.lookup_default_def Mapping.map_default_def Mapping.default_def
      simp: lookup_map_entry' lookup_update' keys_is_none_rep Option.is_none_def
      split: if_splits
    )
  from this[where m=Mapping.empty] show ?thesis
    by (auto simp: E_of_succ_def tab_succ_def lookup_default_empty)
qed

end

lemma finite_imp_finite_dfs_reachable:
  "\<lbrakk>finite E; finite S\<rbrakk> \<Longrightarrow> finite (E\<^sup>*``S)"
  apply (rule finite_subset[where B="S \<union> (Relation.Domain E \<union> Relation.Range E)"])
  apply (auto simp: intro: finite_Domain finite_Range elim: rtranclE)
  done

lemma dfs_reachable_tab_succ_correct: "dfs_reachable (tab_succ l) D vs\<^sub>0 \<longleftrightarrow> Collect D \<inter> (set l)\<^sup>*``set vs\<^sub>0 \<noteq> {}"
  apply (subst dfs_reachable_correct)
  by (simp_all add: tab_succ_correct finite_imp_finite_dfs_reachable)

lemma dfs_all_tab_succ_correct: "dfs_all (tab_succ l) vs\<^sub>0 = (set l)\<^sup>*``set vs\<^sub>0"
  apply (subst dfs_all_correct)
  by (simp_all add: tab_succ_correct finite_imp_finite_dfs_reachable)

subsection \<open>Implementation Refinements\<close>

subsection \<open>World models and valuations\<close>

text \<open>Executable world model\<close>
type_synonym mp_ofi = "(func, (object list, object) mapping) mapping"
type_synonym mp_nfi = "(func, (object list, rat) mapping) mapping"

datatype exec_world_model = 
  EWM
  (ps: "object pred set")
  (eofi: mp_ofi)
  (enfi: mp_nfi)

definition to_nested_map::"('a, ('b, 'c) mapping) mapping \<Rightarrow> 'a \<rightharpoonup> 'b \<rightharpoonup> 'c" where
  "to_nested_map = Mapping.lookup o (Mapping.map_values (\<lambda>k v. Mapping.lookup v))"


fun exec_wm_to_wm::"exec_world_model \<Rightarrow> world_model" where
  "exec_wm_to_wm (EWM p oi ni) = World_Model p (to_nested_map oi) (to_nested_map ni)"

lemma enfi_nf_int[simp]: "to_nested_map (enfi M) = world_model.nf_int (exec_wm_to_wm M)"
  by (cases M; simp)

lemma ps_preds[simp]: "ps M = preds (exec_wm_to_wm M)"
  by (cases M; simp)

lemma eofi_of_int[simp]: "to_nested_map (eofi M) = world_model.of_int (exec_wm_to_wm M)"
  by (cases M; simp)

fun term_val_impl::"exec_world_model \<Rightarrow> object term \<Rightarrow> object option" where
  "term_val_impl M (Ent obj) = Some obj"
| "term_val_impl M (Fun fun as) = (case (Mapping.lookup (eofi M) fun) of
      Some f \<Rightarrow> (let arg_vals = map (\<lambda>t. term_val_impl M t) as
        in (if (list_all (\<lambda>x. x \<noteq> None) arg_vals) 
            then Mapping.lookup f (map the arg_vals) else None))
    | None \<Rightarrow> None)"

lemma term_val_impl_correct: "term_val_impl M x = term_val (exec_wm_to_wm M) x"
proof (induction x)
  case (Fun f as)
  show ?case 
  proof (cases "Mapping.lookup (eofi M) f")
    case None
    then have "of_int (exec_wm_to_wm M) f = None"
      by (cases M; simp add: eofi_def to_nested_map_def lookup_map_values)
    with None
    show ?thesis by simp
  next
    case (Some a)
    then have 1: "of_int (exec_wm_to_wm M) f = Some (Mapping.lookup a)"
      by (cases M; simp add: eofi_def to_nested_map_def  lookup_map_values)
    
    have 2: "map (term_val_impl M) as = map (term_val (exec_wm_to_wm M)) as"
      using Fun.IH by auto
    
    show ?thesis by (simp add: 1 Some 2)
  qed
qed simp

fun nf_val_impl::"exec_world_model \<Rightarrow> object term num_fluent \<Rightarrow> rat option" where
"nf_val_impl M (NFun fun as) = (case (Mapping.lookup (enfi M) fun) of 
    Some f \<Rightarrow> (let arg_vals = map (\<lambda>t. term_val_impl M t) as
      in (if (list_all (\<lambda>x. x \<noteq> None) arg_vals) 
          then Mapping.lookup f (map the arg_vals) else None)) 
  | None    \<Rightarrow> None)"
| "nf_val_impl M (Num n) = Some n"
| "nf_val_impl M (Add x y) = (combine_options plus (nf_val_impl M x) (nf_val_impl M y))"
| "nf_val_impl M (Sub x y) = (combine_options minus (nf_val_impl M x) (nf_val_impl M y))"
| "nf_val_impl M (Mult x y) = (combine_options times (nf_val_impl M x) (nf_val_impl M y))"
| "nf_val_impl M (Div x y) = (combine_options divide (nf_val_impl M x) (nf_val_impl M y))"


lemma nf_val_impl_correct: "nf_val_impl M x = nf_val (exec_wm_to_wm M) x"
proof (induction x)
  case (NFun f as)
  show ?case
  proof (cases "Mapping.lookup (enfi M) f")
    case None
    then show ?thesis by (cases M; simp add: enfi_def to_nested_map_def lookup_map_values)
  next
    case (Some a)
    then have 1: "nf_int (exec_wm_to_wm M) f = Some (Mapping.lookup a)"
      by (cases M; simp add: eofi_def to_nested_map_def  lookup_map_values)
    
    have 2: "map (term_val_impl M) as = map (term_val (exec_wm_to_wm M)) as"
      using term_val_impl_correct by auto
    
    show ?thesis by (simp add: 1 Some 2)
  qed
qed auto

context
  fixes term_val::"object term \<rightharpoonup> object"
    and nf_val::"object term num_fluent \<rightharpoonup> rat"
begin

fun nc_val'::"object term num_comp \<Rightarrow> bool" where
  "nc_val' (Num_Eq x y) = (case (nf_val x, nf_val y) of
      (Some x, Some y)  \<Rightarrow> x = y | _ \<Rightarrow> False)"
  | "nc_val'(num_comp.Le x y) = (case (nf_val x, nf_val y) of
      (Some x, Some y)  \<Rightarrow> x \<le> y | _ \<Rightarrow> False)"
  | "nc_val'(num_comp.Lt x y) = (case (nf_val x, nf_val y) of
      (Some x, Some y)  \<Rightarrow> x < y | _ \<Rightarrow> False)"

fun pred_inst'::"object term pred \<Rightarrow> object pred option" where
  "pred_inst' (Pred p as) = (let arg_vals = map (\<lambda>t. term_val t) as
        in (if (list_all (\<lambda>x. x \<noteq> None) arg_vals) 
            then Some (Pred p (map the arg_vals)) 
            else None))"
  | "pred_inst' (pred.Eq t1 t2) = (case (term_val t1, term_val t2) of
      (Some x, Some y) \<Rightarrow> Some (pred.Eq x y)
    | _                \<Rightarrow> None)"

end

definition "nc_val_impl M = nc_val' (nf_val_impl M)"

lemma nc_val_impl_correct: "nc_val_impl M x = nc_val (exec_wm_to_wm M) x"
  unfolding nc_val_impl_def
  by (cases x; auto simp: nf_val_impl_correct)

definition "pred_inst_impl M = pred_inst' (term_val_impl M)"

lemma pred_inst_impl_correct: "pred_inst_impl M x = pred_inst (exec_wm_to_wm M) x"
  unfolding pred_inst_impl_def
  by (induction x; auto simp: term_val_impl_correct[THEN ext])

fun pred_val_impl::"exec_world_model \<Rightarrow> object term pred \<Rightarrow> bool" where
  "pred_val_impl M p = (case pred_inst_impl M p of 
      Some (Pred p as)  \<Rightarrow> (Pred p as) \<in> ps M
    | Some (pred.Eq x y)     \<Rightarrow> x = y
    | None              \<Rightarrow> False)"

lemma pred_val_impl_correct: "pred_val_impl M x = pred_val (exec_wm_to_wm M) x"
  apply (cases "pred_inst_impl M x")
  subgoal by (simp add: pred_inst_impl_correct)
  subgoal for a by (cases a; auto simp: pred_inst_impl_correct)
  done

fun valuation_impl::"exec_world_model \<Rightarrow> object term atom valuation" where
  "valuation_impl M (PredAtom p) = pred_val_impl M p"
| "valuation_impl M (NumComp c) = nc_val_impl M c"

lemma valuation_impl_correct: "valuation_impl M x = valuation (exec_wm_to_wm M) x"
  using pred_val_impl_correct nc_val_impl_correct
  by (cases x; auto)

  subsubsection \<open>Of-Type\<close>


definition "of_type' G oT T \<equiv> (\<forall>pt\<in>set (primitives oT). dfs_reachable G ((=) pt) (primitives T))"

(* definition "of_type_impl = of_type' STG" -- TODO: simpler
 *)
text \<open>The mapping from variables to types tends to be small, since it 
      is derived from an argument list, so using the default implementation
      of a map as a list is sufficient.\<close>

context ast_domain_decs begin

  text \<open>We check whether a single primitive can be reached from any primitive in a set 
      (this set is the supertype).\<close>
  definition "of_type1 pt T \<longleftrightarrow> pt \<in> subtype_rel\<^sup>* `` set (primitives T)"

  lemma of_type_refine1: "of_type oT T \<longleftrightarrow> (\<forall>pt\<in>set (primitives oT). of_type1 pt T)"
    unfolding of_type_def of_type1_def by auto

  text \<open>We declare types and their supertypes. \<open>subtype_edge\<close> is therefore
        the \<close>
  definition "STG \<equiv> (tab_succ (map subtype_edge (types DD)))"

  definition "of_type_impl = of_type' STG"
  
  lemma subtype_rel_impl: "subtype_rel = E_of_succ (tab_succ (map subtype_edge (types DD)))"
    by (simp add: tab_succ_correct subtype_rel_def)

  lemma of_type1_impl: "of_type1 pt T \<longleftrightarrow> dfs_reachable (tab_succ (map subtype_edge (types DD))) ((=)pt) (primitives T)"
    by (simp add: subtype_rel_impl of_type1_def dfs_reachable_tab_succ_correct tab_succ_correct)

  lemma of_type_impl_correct: "of_type_impl oT T \<longleftrightarrow> of_type oT T"
    unfolding of_type1_impl STG_def of_type_impl_def of_type_refine1 of_type'_def 
    ..

  text \<open>Refining the declarations of signatures for predicates and functions.\<close>
  definition sig'::"(predicate, type list) mapping" where
    "sig' = Mapping.of_alist (map (\<lambda>PredDecl p n \<Rightarrow> (p,n)) (predicates DD))"

  definition "sig_impl = Mapping.lookup sig'"

  lemma sig_impl_correct: "Mapping.lookup sig' = sig"
    unfolding sig'_def sig_def
    by (rule ext; rule lookup_of_alist)

  text \<open>Implementation of the signatures for functions.\<close>
  definition obj_fun_sig'::"(func, (type list \<times> type)) mapping" where
    "obj_fun_sig' = Mapping.of_alist (map (\<lambda>ObjFunDecl f ts t \<Rightarrow> (f, (ts, t))) (object_funs DD))"
  
  definition "ofs_impl = Mapping.lookup obj_fun_sig'"
    
  lemma ofs_impl_correct: "ofs_impl = obj_fun_sig"
    unfolding ofs_impl_def obj_fun_sig'_def obj_fun_sig_def
    by (rule ext; rule lookup_of_alist)
  
  definition num_fun_sig'::"(func, type list) mapping" where
    "num_fun_sig' = Mapping.of_alist (map (\<lambda>NumFunDecl f ts \<Rightarrow> (f, ts)) (num_funs DD))"

  definition "nfs_impl = Mapping.lookup num_fun_sig'"

  lemma nfs_impl_correct: "nfs_impl = num_fun_sig"
    unfolding nfs_impl_def num_fun_sig'_def num_fun_sig_def
    by (rule ext; rule lookup_of_alist)


  text \<open>Executable constT\<close>
  definition mp_constT :: "(object, type) mapping" where
    "mp_constT = Mapping.of_alist (consts DD)"

  lemma mp_constT_correct[simp]: "Mapping.lookup mp_constT = constT"
    unfolding mp_constT_def constT_def
    by (rule ext; rule lookup_of_alist)


  subsubsection \<open>Well-formedness checks\<close>
  
  context (* This could be used for the original ty_term as well. Next iteration *)
    fixes of_type:: "type \<Rightarrow> type \<Rightarrow> bool"
      and ofs:: "func \<rightharpoonup> (type list \<times> type)"
      and ty_ent:: "'ent \<rightharpoonup> type"
  begin
    fun is_term_of_type' :: "'ent term \<Rightarrow> type \<Rightarrow> bool" and
          ty_term'::"'ent term \<Rightarrow> type option" where
        "is_term_of_type' v T = (case ty_term' v of
          Some vT \<Rightarrow> of_type vT T
        | None \<Rightarrow> False)"
      | "ty_term' (Ent e) = ty_ent e"
      | "ty_term' (Fun f as) = (case (ofs f) of 
          Some (Ts, T) \<Rightarrow> (if (list_all2 is_term_of_type' as Ts) 
            then Some T else None)
        | None \<Rightarrow> None)"
  end

  (* This definition is a workaround, since the usage of 
      of_type and obj_fun_sig are hardcoded in ty_term *)
  abbreviation ty_term_impl::"('ent \<rightharpoonup> type) \<Rightarrow> 'ent term \<rightharpoonup> type" where
    "ty_term_impl ty_ent \<equiv> (ty_term' of_type_impl ofs_impl ty_ent)"

  abbreviation is_term_of_type_impl::"('ent \<rightharpoonup> type) \<Rightarrow> 'ent term \<Rightarrow> type \<Rightarrow> bool" where
    "is_term_of_type_impl ty_ent \<equiv> (is_term_of_type' of_type_impl ofs_impl ty_ent)"

  lemma ty_term_impl_correct: "ty_term_impl ty_ent = ty_term ty_ent"
    apply (rule ext)
    subgoal for x
    apply (induction x rule: is_term_of_type_ty_term.induct(2)[
          where P = "\<lambda>t T. is_term_of_type_impl ty_ent t T = is_term_of_type ty_ent t T"])
    subgoal 
      apply (subst is_term_of_type'.simps, subst is_term_of_type.simps)
      apply (rule ssubst, assumption)
      apply (subst of_type_impl_correct)
      by simp
    subgoal by simp
    subgoal for f vs
      apply (subst ty_term.simps, subst ty_term'.simps)
      apply (subst ofs_impl_correct)+
      apply (rule option.case_cong)
        apply simp
       apply simp
      subgoal for x
        apply (rule prod.case_cong)
         apply simp
        subgoal for Ts T
          apply (rule if_cong)
          subgoal by (metis list.rel_mono_strong ofs_impl_correct)
          by auto
        done
      done
    done
  done
  
  context 
    fixes of_type::"type \<Rightarrow> type \<Rightarrow> bool"
      and ty_ent::"'ent \<rightharpoonup> type"
  begin
    definition is_of_type' :: "'ent \<Rightarrow> type \<Rightarrow> bool" where
      "is_of_type' v T \<longleftrightarrow> (
        case ty_ent v of
          Some vT \<Rightarrow> of_type vT T
        | None \<Rightarrow> False)"
  end


  text \<open>It would be nice, if we could remove the ty_ent call in wf_pred_eq'.
        If we could, we could pass is_term_of_type/is_object_of_type/etc.
        rather than of_type and ty_ent.\<close>
  context 
    fixes of_type:: "type \<Rightarrow> type \<Rightarrow> bool"
      and ofs:: "func \<rightharpoonup> (type list \<times> type)"
      and nfs:: "func \<rightharpoonup> type list"
      and ty_ent:: "'ent \<rightharpoonup> type"
  begin
    abbreviation "is_of_type'' \<equiv> is_of_type' of_type ty_ent"

    fun wf_pred'::"predicate \<times> 'ent list \<Rightarrow> bool" where
      "wf_pred' (p,vs) \<longleftrightarrow> (
        case Mapping.lookup sig' p of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 is_of_type'' vs Ts)"
 
    fun wf_pred_eq' :: "'ent pred \<Rightarrow> bool" where
      "wf_pred_eq' (Pred p vs) \<longleftrightarrow> wf_pred' (p,vs)"
    | "wf_pred_eq' (pred.Eq a b) \<longleftrightarrow> ty_ent a \<noteq> None \<and> ty_ent b \<noteq> None"

    text \<open>This checks that a predicate is well-formed and not an equality.\<close>
    fun wf_predicate' :: "'ent pred \<Rightarrow> bool" where
      "wf_predicate' (Pred p vs) \<longleftrightarrow> wf_pred' (p, vs)"
    | "wf_predicate' (pred.Eq _ _) \<longleftrightarrow> False"

    text \<open>A function call is well-formed if the function has been
          declared and the types of the arguments matches the types
          of the parameters\<close>
    fun wf_num_func'::"func \<times> 'ent list \<Rightarrow> bool" where
      "wf_num_func' (f, as) \<longleftrightarrow> (
        case nfs f of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 is_of_type'' as Ts
      )"

    text \<open>Fluents and comparisons are well-formed if the components are well-formed\<close>
    fun wf_num_fluent'::"'ent num_fluent \<Rightarrow> bool" where
      "wf_num_fluent' (NFun f as) = wf_num_func' (f, as)"
    | "wf_num_fluent' (Num _) = True"
    | "wf_num_fluent' (Add a b) = (wf_num_fluent' a \<and> wf_num_fluent' b)"
    | "wf_num_fluent' (Sub a b) = (wf_num_fluent' a \<and> wf_num_fluent' b)"
    | "wf_num_fluent' (Mult a b) = (wf_num_fluent' a \<and> wf_num_fluent' b)"
    | "wf_num_fluent' (Div a b) = (wf_num_fluent' a \<and> wf_num_fluent' b)"
    
    fun wf_num_comp' :: "'ent num_comp \<Rightarrow> bool" where
      "wf_num_comp' (Num_Eq a b) = (wf_num_fluent' a \<and> wf_num_fluent' b)"
    | "wf_num_comp' (num_comp.Lt a b) = (wf_num_fluent' a \<and> wf_num_fluent' b)"
    | "wf_num_comp' (num_comp.Le a b) = (wf_num_fluent' a \<and> wf_num_fluent' b)"

    text \<open>Predicate-atoms are well-formed if their arguments match the
      signature, equalities are well-formed if the arguments are valid
      objects (have a type), comparisons are well-formed if the functions
      and terms are well-typed.
    \<close>
    fun wf_atom' :: "'ent atom \<Rightarrow> bool" where
      "wf_atom' (PredAtom p) \<longleftrightarrow> wf_pred_eq' p"
    | "wf_atom' (NumComp nc) \<longleftrightarrow> wf_num_comp' nc"

    text \<open>A formula is well-formed if its components are well-formed
    \<close>
    fun wf_fmla' :: "('ent atom) formula \<Rightarrow> bool" where
      "wf_fmla' (Atom a) \<longleftrightarrow> wf_atom' a"
    | "wf_fmla' (\<bottom>) \<longleftrightarrow> True"
    | "wf_fmla' (\<phi>1 \<^bold>\<and> \<phi>2) \<longleftrightarrow> (wf_fmla' \<phi>1 \<and> wf_fmla' \<phi>2)"
    | "wf_fmla' (\<phi>1 \<^bold>\<or> \<phi>2) \<longleftrightarrow> (wf_fmla' \<phi>1 \<and> wf_fmla' \<phi>2)"
    | "wf_fmla' (\<^bold>\<not>\<phi>) \<longleftrightarrow> wf_fmla' \<phi>"
    | "wf_fmla' (\<phi>1 \<^bold>\<rightarrow> \<phi>2) \<longleftrightarrow> (wf_fmla' \<phi>1 \<and> wf_fmla' \<phi>2)"


    text \<open>An update to a function on objects is well-formed if the function has 
          been declared, the signature matches the types of the arguments and new return value, 
          and the arguments and the term to assign the return value are well-formed.\<close>
    fun wf_of_upd'::"'ent of_upd \<Rightarrow> bool" where
    "wf_of_upd' (OF_Upd f as v) = (case obj_fun_sig f of 
      None \<Rightarrow> False
    | Some (Ts, T) \<Rightarrow>
          list_all2 is_of_type'' as Ts 
        \<and> (v = None \<or> is_of_type'' (the v) T))" 
  
    text \<open>An update to a numeric function is well-formed if the function has been declared,
          the signature matches the types of the arguments, the arguments are well-formed,
          and the value that is being assigned is well-formed.\<close>
    fun wf_nf_upd'::"'ent nf_upd \<Rightarrow> bool" where
    "wf_nf_upd' (NF_Upd f op as v) = (case nfs f of 
        None \<Rightarrow> False
      | Some Ts \<Rightarrow> 
          list_all2 is_of_type'' as Ts 
        \<and> wf_num_fluent' v
    )"

    text \<open>An effect is well-formed if its constituent parts are well-formed\<close>
    fun wf_effect' where
      "wf_effect' (Effect a d tu nu) \<longleftrightarrow>
          (\<forall>u \<in> set a. wf_predicate' u)
        \<and> (\<forall>u \<in> set d. wf_predicate' u)
        \<and> (\<forall>u \<in> set tu. wf_of_upd' u)
        \<and> (\<forall>u \<in> set nu. wf_nf_upd' u)
        "

    definition wf_cond_effect' where
      "wf_cond_effect' eff \<longleftrightarrow> wf_fmla' (fst eff) \<and> wf_effect' (snd eff)"

    definition wf_cond_effect_list' where
      "wf_cond_effect_list' \<equiv> list_all wf_cond_effect'"
 end

  abbreviation "is_of_type_impl \<equiv> is_of_type'' of_type_impl"
  
  lemma is_of_type_impl_correct: "is_of_type_impl ty_ent = is_of_type ty_ent"
    unfolding is_of_type_def is_of_type'_def
    using of_type_impl_correct
    by (auto split: option.splits)

  (* To do: maybe replace definitions by abbreviations *)
abbreviation "wf_pred_impl \<equiv> wf_pred' of_type_impl"

  lemma wf_pred_impl_correct: "wf_pred_impl ty_ent = wf_pred ty_ent"
    apply (rule ext)
    subgoal for x
    apply (cases x)
      subgoal for p vs
        apply (rule ssubst[of x], assumption)
        apply (subst wf_pred'.simps, subst wf_pred.simps)
        by (rule option.case_cong; simp add: sig_impl_correct is_of_type_impl_correct)
      done
    done 
  
  abbreviation "wf_pred_eq_impl \<equiv> wf_pred_eq' of_type_impl"
  
  lemma wf_pred_eq_impl_correct: "wf_pred_eq_impl ty_ent = wf_pred_eq ty_ent"
    apply (intro ext)
    subgoal for x
      by (cases x; simp add: wf_pred_impl_correct)
    done
    
  abbreviation "wf_predicate_impl \<equiv> wf_predicate' of_type_impl"
                                           
    lemma wf_predicate_impl_correct: "wf_predicate_impl ty_ent = wf_predicate ty_ent"
      apply (intro ext)
      subgoal for x
        by (cases x; simp add: wf_pred_impl_correct)
      done
  
  abbreviation "wf_num_func_impl \<equiv> wf_num_func' of_type_impl nfs_impl"
  
  lemma wf_num_func_impl_correct: "wf_num_func_impl ty_ent = wf_num_func ty_ent"
    apply (rule ext)
    subgoal for x 
      apply (cases x)
      subgoal for a b
        apply (rule ssubst[of x], assumption)
        apply (subst wf_num_func'.simps, subst wf_num_func.simps)
        by (rule option.case_cong; simp add: nfs_impl_correct is_of_type_impl_correct)
      done
    done
  
  abbreviation "wf_num_fluent_impl \<equiv> wf_num_fluent' of_type_impl nfs_impl"
  
  lemma wf_num_fluent_impl_correct: "wf_num_fluent_impl ty_ent = wf_num_fluent ty_ent"
    apply (rule ext)
    subgoal for x
      apply (induction x)
      subgoal by (simp add: wf_num_func_impl_correct)
      subgoal by simp
      by auto
    done
    
  abbreviation "wf_num_comp_impl \<equiv> wf_num_comp' of_type_impl nfs_impl"
  
  lemma wf_num_comp_impl_correct: "wf_num_comp_impl ty_ent = wf_num_comp ty_ent"
    apply (rule ext)
    subgoal for x
      by (induction x; simp add: wf_num_fluent_impl_correct)+
    done
  
  abbreviation "wf_atom_impl \<equiv> wf_atom' of_type_impl nfs_impl"
  
  lemma wf_atom_impl_correct: "wf_atom_impl ty_ent = wf_atom ty_ent"
    apply (rule ext)
    subgoal for x 
      by (cases x; simp add: wf_num_comp_impl_correct wf_pred_eq_impl_correct)
    done

  abbreviation "wf_fmla_impl \<equiv> wf_fmla' of_type_impl nfs_impl"
  
  lemma wf_fmla_impl_correct: "wf_fmla_impl ty_ent = wf_fmla ty_ent"
    apply (rule ext)
    subgoal for x
      apply (induction x)
      subgoal by (simp add: wf_atom_impl_correct)
      by auto
    done

  abbreviation "wf_of_upd_impl \<equiv> wf_of_upd' of_type_impl"
  
  lemma wf_of_upd_impl_correct: "wf_of_upd_impl ty_ent = wf_of_upd ty_ent"
    apply (rule ext)
    subgoal for x
      apply (cases x)
      subgoal for f as v
        apply (rule ssubst[of x], assumption)
        apply (subst wf_of_upd'.simps, subst wf_of_upd.simps)
        by (rule option.case_cong; simp add: is_of_type_impl_correct)
      done
    done
  
  abbreviation "wf_nf_upd_impl \<equiv> wf_nf_upd' of_type_impl nfs_impl"
  
  lemma wf_nf_upd_impl_correct: "wf_nf_upd_impl ty_ent = wf_nf_upd ty_ent"
    apply (rule ext)
    subgoal for x
      apply (cases x)
      subgoal for f op as v
        apply (rule ssubst[of x], assumption)
        apply (subst wf_nf_upd'.simps, subst wf_nf_upd.simps)
        apply (subst wf_num_fluent_impl_correct)
        apply (subst nfs_impl_correct)
        apply (subst is_of_type_impl_correct)
        ..
      done
    done
  
  abbreviation "wf_effect_impl \<equiv> wf_effect' of_type_impl nfs_impl"
  
  lemma wf_effect_impl_correct: "wf_effect_impl ty_ent = wf_effect ty_ent"
    apply (rule ext)
    subgoal for x
      apply (cases x)
      by (simp add: wf_predicate_impl_correct 
          wf_of_upd_impl_correct
          wf_nf_upd_impl_correct)
    done
  
  abbreviation "wf_cond_effect_impl \<equiv> wf_cond_effect' of_type_impl nfs_impl"
  
  lemma wf_cond_effect_impl_correct: "wf_cond_effect_impl ty_ent = wf_cond_effect ty_ent"
    apply (rule ext)
    subgoal for x
      apply (cases x)
      unfolding wf_cond_effect'_def wf_cond_effect_def 
        wf_fmla_impl_correct
        wf_effect_impl_correct
      ..
    done

  abbreviation "wf_cond_effect_list_impl \<equiv> wf_cond_effect_list' of_type_impl nfs_impl"
  
  lemma wf_cond_effect_list_impl_correct: "wf_cond_effect_list_impl ty_ent = wf_cond_effect_list ty_ent"
    unfolding wf_cond_effect_list_def wf_cond_effect_list'_def
    by (simp add: wf_cond_effect_impl_correct)

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

context ast_problem_decs begin

  text \<open> We start by defining a mapping from objects to types. The container
    framework will generate efficient, red-black tree based code for that
    later. \<close>

  type_synonym objT = "(object, type) mapping"

  definition mp_objT :: "(object, type) mapping" where
    "mp_objT = Mapping.of_alist (consts DD @ objects PD)"

  definition "objT_impl = Mapping.lookup mp_objT"

  lemma objT_impl_correct: "objT_impl = objT"
    unfolding objT_impl_def mp_objT_def objT_alt
    by (rule ext, rule lookup_of_alist)

  text \<open>We refine the well-formedness checks to use the mapping\<close>
  
  fun wf_action_schema' :: "(type \<Rightarrow> type \<Rightarrow> bool) 
    \<Rightarrow> (func \<rightharpoonup> (type list \<times> type))
    \<Rightarrow> (func \<rightharpoonup> type list) 
    \<Rightarrow> (object \<rightharpoonup> type) \<Rightarrow> ast_action_schema \<Rightarrow> bool" where
      "wf_action_schema' ot ofs nfs obT (Action_Schema n params pre eff) \<longleftrightarrow> (
        let
          tyt = ty_term' ot ofs (ty_sym (map_of params) obT)
        in
          distinct (map fst params)
        \<and> wf_fmla' ot nfs tyt pre
        \<and> wf_cond_effect_list' ot nfs tyt eff)"
  
  abbreviation "wf_action_schema_impl \<equiv> wf_action_schema' of_type_impl ofs_impl nfs_impl objT_impl"
  
  lemma wf_action_schema_impl_correct: "wf_action_schema_impl = wf_action_schema"
    apply (intro ext)
    subgoal for a
      apply (induction a)
      subgoal for n params pre effs
        unfolding wf_action_schema.simps wf_action_schema'.simps
          ty_term_impl_correct
          wf_fmla_impl_correct
          wf_cond_effect_list_impl_correct
          objT_impl_correct
        ..
      done
    done

    definition "wf_goal' ot ofs nfs = wf_fmla' ot nfs (ty_term' ot ofs (ty_sym Map.empty objT_impl))"

definition "wf_goal_impl \<equiv> wf_goal' of_type_impl ofs_impl nfs_impl"

    lemma wf_goal_impl_correct: "wf_goal_impl = wf_goal"
      unfolding wf_goal'_def wf_goal_def wf_goal_impl_def
        ty_term_impl_correct
        wf_fmla_impl_correct
        objT_impl_correct
      ..
end

context ast_domain
begin
  definition wf_domain' :: "(type \<Rightarrow> type \<Rightarrow> bool) 
    \<Rightarrow> (func \<rightharpoonup> (type list \<times> type)) \<Rightarrow> (func \<rightharpoonup> type list) 
    \<Rightarrow> (object \<rightharpoonup> type) \<Rightarrow> bool" where
  "wf_domain' ot ofs nfs obT \<equiv>
    wf_problem_decs 
  \<and> distinct (map ast_action_schema.name (actions D))
  \<and> (\<forall>a\<in>set (actions D). wf_action_schema' ot ofs nfs obT a)
  "

  abbreviation "wf_domain_impl \<equiv> wf_domain' of_type_impl 
    ofs_impl nfs_impl objT_impl"

  lemma wf_domain_impl_correct: "wf_domain_impl = wf_domain"
    unfolding wf_domain'_def wf_domain_def
      wf_action_schema_impl_correct
    ..
  
end

context ast_problem
begin
  context
    fixes of_type:: "type \<Rightarrow> type \<Rightarrow> bool"
      and ofs:: "func \<rightharpoonup> (type list \<times> type)"
      and nfs:: "func \<rightharpoonup> type list"
      and obt:: "object \<rightharpoonup> type"
  begin
    fun wf_init_of_a'::"(func \<times> object list \<times> object) \<Rightarrow> bool" where
      "wf_init_of_a' (f, as, v) = (case ofs f of 
        Some (Ts, T) \<Rightarrow> list_all2 (is_of_type' of_type obt) as Ts \<and> (is_of_type' of_type obt) v T
      | None \<Rightarrow> False)"
    
    fun wf_init_nf_a'::"(func \<times> object list \<times> rat) \<Rightarrow> bool" where
      "wf_init_nf_a' (f, as, v) = (case nfs f of
        Some Ts \<Rightarrow> list_all2 (is_of_type' of_type obt) as Ts
      | None \<Rightarrow> False)"
  end

  abbreviation "wf_init_of_a_impl \<equiv> wf_init_of_a' of_type_impl ofs_impl objT_impl"
  
  lemma wf_init_of_a_impl_correct: "wf_init_of_a_impl = wf_init_of_a"
    apply (rule ext)
    subgoal for x
      apply (cases x, rule ssubst[of x], assumption)
      unfolding wf_init_of_a'.simps wf_init_of_a.simps
        is_of_type_impl_correct
        objT_impl_correct ofs_impl_correct
      ..
    done

  abbreviation "wf_init_nf_a_impl \<equiv> wf_init_nf_a' of_type_impl nfs_impl objT_impl"
  
  lemma wf_init_nf_a_impl_correct: "wf_init_nf_a_impl = wf_init_nf_a"
    apply (rule ext)
    subgoal for x
      apply (cases x, rule ssubst[of x], assumption)
      unfolding wf_init_nf_a'.simps wf_init_nf_a.simps
        is_of_type_impl_correct
        objT_impl_correct nfs_impl_correct
      ..
    done

  definition "wf_problem' ot ofs nfs obT\<equiv>
      wf_domain' ot ofs nfs obT
    \<and> (\<forall>p \<in> (init_ps P). wf_predicate' ot obT p)
    \<and> (\<forall>a \<in> set (init_ofs P). wf_init_of_a' ot ofs obT a)
    \<and> (\<forall>a \<in> set (init_nfs P). wf_init_nf_a' ot nfs obT a)
    \<and> wf_goal' ot ofs nfs (goal P)"

definition "wf_problem_impl \<equiv>
    wf_problem' of_type_impl ofs_impl nfs_impl  objT_impl"

  lemma wf_problem_impl_correct: "wf_problem_impl = wf_problem"
    unfolding wf_problem_impl_def wf_problem'_def wf_problem_def
     wf_domain_impl_correct wf_predicate_impl_correct
      wf_init_of_a_impl_correct wf_init_nf_a_impl_correct
      wf_goal_impl_correct[simplified wf_goal_impl_def] apply (subst objT_impl_correct)
    ..
end
subsubsection \<open>Implementation of the quantifier macros\<close>

derive ceq variable
derive ccompare variable
derive (rbt) set_impl variable 


(* this syntax also works for Mapping *)

context ast_problem_decs begin


  (* "of_type_impl G oT T \<equiv> (\<forall>pt\<in>set (primitives oT). dfs_reachable G ((=) pt) (primitives T))" *)
  
  (* definition "t_dom_impl G T \<equiv> \<Inter> (dfs_all G (primitives T))" *)
              
  find_theorems name: "collect"
  
  fun term_vars_impl::"symbol term \<Rightarrow> variable set" where
    "term_vars_impl (Ent x) = sym_vars x"
  | "term_vars_impl (Fun f as) = fold ((\<union>) o term_vars_impl) as {}"
  
  lemma term_vars_impl_correct: "term_vars_impl x = term_vars x"
  proof (induction x)
    case (Fun f as)
    have "term_vars (Fun f as) = \<Union> (term_vars ` (set as))"
      using term_vars_def by simp
    also have "... = \<Union> (term_vars_impl ` (set as))"
      using Fun.IH by simp
    also have "... = fold (\<union>) (map term_vars_impl as) {}"
      by (simp add: SUP_set_fold fold_map)
    finally show ?case
      by (simp add: fold_map)
  qed (simp add: term_vars_def)
  
  fun pred_vars_impl::"symbol term pred \<Rightarrow> variable set" where
    "pred_vars_impl (Pred p as) = fold ((\<union>) o term_vars_impl) as {}"
  | "pred_vars_impl (pred.Eq a b) = term_vars_impl a \<union> term_vars_impl b"
  
  lemma pred_vars_impl_correct: "pred_vars x = pred_vars_impl x"
  proof (cases x)
    case [simp]: (Pred p as)
    have "pred_vars (Pred p as) = \<Union> (term_vars_impl ` (set as))"
      unfolding pred_vars_def
      using term_vars_impl_correct by simp
    also have "... = fold (\<union>) (map term_vars_impl as) {}"
        by (simp add: SUP_set_fold fold_map)
    finally show ?thesis 
      by (simp add: fold_map)
  next
    case (Eq a b)
    then show ?thesis 
      unfolding pred_vars_def 
      using term_vars_impl_correct 
      by simp
  qed

  fun nf_vars_impl::"symbol term num_fluent \<Rightarrow> variable set" where
    "nf_vars_impl (NFun f as) = fold ((\<union>) o term_vars_impl) as {}"
  | "nf_vars_impl (Num n) = {}"
  | "nf_vars_impl (Add a b) = nf_vars_impl a \<union> nf_vars_impl b"
  | "nf_vars_impl (Sub a b) = nf_vars_impl a \<union> nf_vars_impl b"
  | "nf_vars_impl (Mult a b) = nf_vars_impl a \<union> nf_vars_impl b"
  | "nf_vars_impl (Div a b) = nf_vars_impl a \<union> nf_vars_impl b"

lemma nf_vars_impl_correct: "nf_vars_impl x = nf_vars x"
proof (induction x)
  case (NFun f as)
    have "nf_vars (NFun f as) = \<Union> (term_vars_impl ` (set as))"
      unfolding nf_vars_def
      using term_vars_impl_correct by simp
    also have "... = fold (\<union>) (map term_vars_impl as) {}"
        by (simp add: SUP_set_fold fold_map)
    finally show ?case 
      by (simp add: fold_map)
qed (auto simp: nf_vars_def)

fun nc_vars_impl::"symbol term num_comp \<Rightarrow> variable set" where
  "nc_vars_impl (Num_Eq a b) = nf_vars_impl a \<union> nf_vars_impl b"
| "nc_vars_impl (Le a b) = nf_vars_impl a \<union> nf_vars_impl b"
| "nc_vars_impl (num_comp.Lt a b) = nf_vars_impl a \<union> nf_vars_impl b"

lemma nc_vars_impl_correct: "nc_vars_impl x = nc_vars x"
  by (induction x; simp add: nc_vars_def nf_vars_def nf_vars_impl_correct)

fun atom_vars_impl::"symbol term atom \<Rightarrow> variable set" where
  "atom_vars_impl (PredAtom p) = pred_vars_impl p"
| "atom_vars_impl (NumComp nc) = nc_vars_impl nc"

lemma atom_vars_impl_correct: "atom_vars_impl x = atom_vars x"
  unfolding atom_vars_def
proof (induction x)
  case (PredAtom p)
  then show ?case using pred_vars_impl_correct atom_vars_def pred_vars_def by simp
next
  case (NumComp nc)
  then show ?case using nc_vars_impl_correct atom_vars_def nc_vars_def by simp
qed


  primrec f_vars_impl::"symbol term atom formula \<Rightarrow> variable set" where
    "f_vars_impl (Atom p) = atom_vars_impl p" 
  | "f_vars_impl Bot = {}"
  | "f_vars_impl (Not \<phi>\<^sub>1) = f_vars_impl \<phi>\<^sub>1"
  | "f_vars_impl (And \<phi>\<^sub>1 \<phi>\<^sub>2) = f_vars_impl \<phi>\<^sub>1 \<union> f_vars_impl \<phi>\<^sub>2"
  | "f_vars_impl (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = f_vars_impl \<phi>\<^sub>1 \<union> f_vars_impl \<phi>\<^sub>2"
  | "f_vars_impl (Imp \<phi>\<^sub>1 \<phi>\<^sub>2) = f_vars_impl \<phi>\<^sub>1 \<union> f_vars_impl \<phi>\<^sub>2"

  lemma f_vars_impl_correct: "f_vars_impl \<phi> = f_vars \<phi>"
    by (induction \<phi>; auto simp: f_vars_def atom_vars_impl_correct)

  definition t_dom_impl::"type \<Rightarrow> object list" where    
    "t_dom_impl typ = map fst (filter (\<lambda>(c, t). of_type_impl t typ) (consts DD @ objects PD))"
  
  lemma t_dom_impl_correct: "t_dom_impl t = t_dom t" 
    unfolding t_dom_def t_dom_impl_def
    using of_type_impl_correct
    by presburger

  definition all_impl::"variable \<Rightarrow> type \<Rightarrow> schematic_formula \<Rightarrow> schematic_formula" where
    "all_impl v t \<phi> \<equiv> (if (v \<notin> f_vars_impl \<phi> \<and> (t_dom_impl t \<noteq> [])) then \<phi> else  \<^bold>\<And>(map (\<lambda>c. f_subst v c \<phi>) (t_dom_impl t)))"

  definition exists_impl::"variable \<Rightarrow> type \<Rightarrow> schematic_formula \<Rightarrow> schematic_formula" where
    "exists_impl v t \<phi> \<equiv> (if (v \<notin> f_vars_impl \<phi> \<and> (t_dom_impl t \<noteq> [])) then \<phi> else \<^bold>\<Or>(map (\<lambda>c. f_subst v c \<phi>) (t_dom_impl t)))"

  lemma all_impl_correct: "all_impl v t \<phi> = \<^bold>\<forall>v - t. \<phi>"
    unfolding all_def all_impl_def 
    using t_dom_impl_correct f_vars_impl_correct
    by presburger

  lemma exists_impl_correct: "exists_impl v t \<phi> = \<^bold>\<exists>v - t. \<phi>"
    unfolding exists_def exists_impl_def
    using t_dom_impl_correct f_vars_impl_correct
    by presburger

  text \<open>Functions to apply our quantifiers to PDDL quantifiers with argument lists\<close>
  definition pddl_all_impl::"(variable \<times> type) list \<Rightarrow> schematic_formula \<Rightarrow> schematic_formula" where
    "pddl_all_impl vts \<phi> = foldr (\<lambda>(v, t) f. all_impl v t f) vts \<phi>"

  definition pddl_exists_impl::"(variable \<times> type) list \<Rightarrow> schematic_formula \<Rightarrow> schematic_formula" where
    "pddl_exists_impl vts \<phi> = foldr (\<lambda>(v, t) f. exists_impl v t f) vts \<phi>"

  lemma pddl_all_impl_correct: "pddl_all_impl vts \<phi> = pddl_all vts \<phi>"
    unfolding pddl_all_def pddl_all_impl_def
    using all_impl_correct
    by presburger

  lemma pddl_exists_impl_correct: "pddl_exists_impl vts \<phi> = pddl_exists vts \<phi>"
    unfolding pddl_exists_def pddl_exists_impl_def
    using exists_impl_correct
    by presburger

end


subsection \<open>Semantics of actions in dynamic world state.\<close>

context ast_domain begin

context 
  fixes term_val::"object term \<rightharpoonup> object"
  fixes nf_val::"object term num_fluent \<rightharpoonup> rat"
  fixes pred_inst::"object term pred \<rightharpoonup> object pred"
begin

fun inst_of_upd'::"object term of_upd \<Rightarrow> instantiated_of_upd" where
  "inst_of_upd' (OF_Upd f args r) = (OFU f (map term_val args) (term_val (the r)))"

fun inst_nf_upd'::"object term nf_upd \<Rightarrow> instantiated_nf_upd" where
  "inst_nf_upd' (NF_Upd f op args r) = (
    let args' = map term_val args
    in NFU f op args' (nf_val r))"

fun inst_effect'::" ground_effect \<Rightarrow> fully_instantiated_effect" where
    "inst_effect' (Effect a d tu nu) = (
      Eff (map pred_inst a) 
          (map pred_inst d) 
          (map inst_of_upd' tu) 
          (map inst_nf_upd' nu))"
end

definition "inst_of_upd_impl M \<equiv> inst_of_upd' (term_val_impl M)"

lemma inst_of_upd_impl_correct: "inst_of_upd_impl M u = inst_of_upd (exec_wm_to_wm M) u"
  unfolding inst_of_upd_impl_def
  by (cases u; auto simp: term_val_impl_correct)

definition "inst_nf_upd_impl M \<equiv> inst_nf_upd' (term_val_impl M) (nf_val_impl M)"

lemma inst_nf_upd_impl_correct: "inst_nf_upd_impl M u = inst_nf_upd (exec_wm_to_wm M) u"
  unfolding inst_nf_upd_impl_def
  by (cases u; auto simp: term_val_impl_correct nf_val_impl_correct)

definition "inst_effect_impl M \<equiv> inst_effect' (term_val_impl M) (nf_val_impl M) (pred_inst_impl M)"

lemma inst_effect_impl_correct: "inst_effect_impl M eff = inst_effect (exec_wm_to_wm M) eff"
  unfolding inst_effect_impl_def
  by (cases eff; auto simp:
      inst_nf_upd_impl_correct[simplified inst_nf_upd_impl_def]
      inst_of_upd_impl_correct[simplified inst_of_upd_impl_def]
      pred_inst_impl_correct)



fun apply_of_upd_impl::"instantiated_of_upd \<Rightarrow> mp_ofi \<Rightarrow> mp_ofi" where
  "apply_of_upd_impl (OFU f as v) oi = (
      let m' = case (Mapping.lookup oi f) of Some m' \<Rightarrow> m' | None \<Rightarrow> Mapping.empty
      in case v of 
        Some v \<Rightarrow> Mapping.update f (Mapping.update (map the as) v m') oi
      | None   \<Rightarrow> Mapping.update f (Mapping.delete (map the as) m') oi
    )"

lemma to_nested_map_None: "to_nested_map M x = None \<longleftrightarrow> Mapping.lookup M x = None"
  unfolding to_nested_map_def
  by (simp add: lookup_map_values)

lemma to_nested_map_NoneE: "to_nested_map M x = None \<Longrightarrow> Mapping.lookup M x = None"
  using to_nested_map_None
  by fastforce

lemma to_nested_map_NoneI: "Mapping.lookup M x = None \<Longrightarrow> to_nested_map M x = None"
  using to_nested_map_None
  by fastforce

lemma to_nested_map_SomeI: "Mapping.lookup M x = Some v \<Longrightarrow> to_nested_map M x = Some (Mapping.lookup v)"
  unfolding to_nested_map_def
  by (metis Mapping.map_values_def comp_apply lookup_map_values option.simps(9))

lemma to_nested_map_SomeE: "to_nested_map M x = Some (Mapping.lookup v) \<Longrightarrow> Mapping.lookup M x = Some v"
  unfolding to_nested_map_def
  by (metis Some_eq_map_option comp_apply lookup_map_values mapping_eqI)

lemma to_nested_map_SomeE1: assumes "to_nested_map M x = Some v"
  obtains v' where "Mapping.lookup M x = Some v' \<and> v = Mapping.lookup v'"
  using assms
  by (metis Mapping.lookup.abs_eq to_nested_map_SomeE)

lemma to_nested_map_Some: "to_nested_map M x = Some (Mapping.lookup v) \<longleftrightarrow> Mapping.lookup M x = Some v"
  using to_nested_map_SomeE to_nested_map_SomeI
  by fast

lemma lookup_inj: "inj Mapping.lookup"
  by (simp add: injI mapping_eqI)

lemma lookup_surj: "surj Mapping.lookup"
  try


lemma to_nested_map_inj: "inj to_nested_map"
proof (rule injI)
  fix x y
  assume a: "to_nested_map x = to_nested_map y" 
  have b: "to_nested_map x a = b \<Longrightarrow> to_nested_map y a = b" 
       "to_nested_map y a = b \<Longrightarrow> to_nested_map x a = b" for a b
    using a by simp_all
  
  have "Mapping.lookup x a = Mapping.lookup y a" for a
    apply (cases "to_nested_map x a")
     apply (frule b(1))
     apply (drule to_nested_map_NoneE)+ 
     apply simp
    subgoal for b apply (frule b(1))
      apply (drule to_nested_map_SomeE1[where thesis = "\<exists>v'. Mapping.lookup x a = Some v' \<and> b = Mapping.lookup v'"])
      apply simp
      apply (drule to_nested_map_SomeE1[where thesis = "\<exists>v'. Mapping.lookup y a = Some v' \<and> b = Mapping.lookup v'"])
       apply simp
      
      
  show "x = y" sorry
qed

lemma exec_wm_to_wm_inj: "inj exec_wm_to_wm"
proof (rule injI)
  fix x y
  assume a[simp]: "exec_wm_to_wm x = exec_wm_to_wm y"
  show "x = y"
  proof (induction x; induction y)
    fix ps ps' ofi ofi' nfi nfi'
    assume xy[simp]: "x = EWM ps ofi nfi"
           "y = EWM ps' ofi' nfi'"
    have 1: "exec_wm_to_wm (EWM ps ofi nfi) = exec_wm_to_wm (EWM ps' ofi' nfi')" using a xy by fast
    hence "ps = ps'" by simp
    have "ofi = ofi'" using 1 
    
    show "EWM ps ofi nfi = EWM ps' ofi' nfi'" sorry
  qed
qed

lemma to_nested_map_upd_other: "x \<noteq> k \<Longrightarrow> to_nested_map (Mapping.update k v M) x = to_nested_map M x"
  unfolding to_nested_map_def by (simp add: lookup_map_values)

lemma to_nested_map_del_other: "x \<noteq> k \<Longrightarrow> to_nested_map (Mapping.delete k M) x = to_nested_map M x"
  unfolding to_nested_map_def by (simp add: lookup_map_values)

lemma to_nested_map_upd: "to_nested_map M = M' \<Longrightarrow> to_nested_map (Mapping.update k v M) = M'(k \<mapsto> (Mapping.lookup v))"
  apply (rule ext)
  subgoal for x
    apply (cases "x = k")
    subgoal by (simp add: to_nested_map_SomeI)
    subgoal by (auto simp: fun_upd_other to_nested_map_upd_other)
    done
  done

lemma to_nested_map_del: "to_nested_map M = M' \<Longrightarrow> to_nested_map (Mapping.delete k M) = M'(k := None)"
  apply (rule ext)
  subgoal for x
    by (cases "x = k"; auto simp: to_nested_map_NoneI fun_upd_other to_nested_map_del_other)
  done

(* To do: clean up using above lemmas *)
lemma apply_of_upd_impl_correct: "to_nested_map (apply_of_upd_impl u ofi) = apply_of_upd u (to_nested_map ofi)"
proof (rule ext; induction u)
  fix x::func
  and f::func
  and as::"object option list"
  and v::"object option"
  let ?m1 = "to_nested_map (apply_of_upd_impl (OFU f as v) ofi)"
  let ?m2 = "apply_of_upd (OFU f as v) (to_nested_map ofi)"
  have case_None: "?m1 x = None \<longleftrightarrow> ?m2 x = None"
  proof
    assume "?m1 x = None"
    hence 1: "Mapping.lookup (apply_of_upd_impl (OFU f as v) ofi) x = None"
      by (subst (asm) to_nested_map_None)
    hence 2: "f \<noteq> x"
      by (cases "Mapping.lookup ofi f"; cases v; auto)
    show "?m2 x = None" 
      apply (insert 1 2)
      apply (subst apply_of_upd.simps, subst (asm) apply_of_upd_impl.simps)
      apply (subst (3) to_nested_map_def)
      by (cases "Mapping.lookup ofi f"; simp add: Let_def lookup_map_values; cases v; simp add: to_nested_map_None)  
  next
    assume a: "?m2 x = None"
    hence "f \<noteq> x" 
      by (cases "to_nested_map ofi f"; auto)
    with a
    have "to_nested_map ofi x = None"
      by (cases "to_nested_map ofi f"; auto)
    hence "Mapping.lookup ofi x = None"
      using to_nested_map_None by fastforce
    with \<open>f \<noteq> x\<close>
    have "Mapping.lookup (apply_of_upd_impl (OFU f as v) ofi) x = None" 
      apply (subst apply_of_upd_impl.simps)
      apply (cases "Mapping.lookup ofi f"; cases v)
      by auto
    then 
    show "?m1 x = None" by (subst to_nested_map_None)
  qed

  show "?m1 x = ?m2 x"
  proof (cases "?m1 x")
    case None
    then show ?thesis using case_None by auto
  next
    case m: (Some m)
    then obtain m' where
      m': "?m2 x = Some m'"
      using case_None by auto
    have "m as' = m' as'" for as'
    proof (cases "f = x")
      case True
      show ?thesis
      proof (cases "Mapping.lookup ofi f")
        case None
        hence "to_nested_map ofi f = None"
          by (simp add: to_nested_map_None)
        hence 1: "?m2 f = Some (Map.empty ((map the as) := v))"
          by auto
        show ?thesis
        proof (cases v)
          case None
          have "Mapping.lookup (apply_of_upd_impl (OFU f as v) ofi) f = Some Mapping.empty"
            using None \<open>Mapping.lookup ofi f = None\<close>
            by auto
          hence "?m1 f = Some Map.empty"
            using to_nested_map_SomeI by fastforce
          moreover
          from None 1
          have "?m2 f = Some Map.empty"
            by simp 
          ultimately
          show ?thesis using m m' \<open>f = x\<close> by simp
        next
          case (Some v')
          with 1
          have "?m2 f = Some (Map.empty ((map the as) := v))"
            by simp 
          moreover
          have "Mapping.lookup (apply_of_upd_impl (OFU f as v) ofi) f = Some (Mapping.update (map the as) v' Mapping.empty)"
            using Some \<open>Mapping.lookup ofi f = None\<close>
            by auto
          hence "?m1 f = Some (Map.empty ((map the as) := v))"
            using to_nested_map_SomeI Some by fastforce
          ultimately 
          show ?thesis using m m' \<open>f = x\<close> by simp
        qed
      next
        case (Some a)
        then obtain a' where
         a': "to_nested_map ofi f = Some a'"
          "a' = Mapping.lookup a"
          using to_nested_map_SomeI by fast
        hence 1: "?m2 f = Some (a' ((map the as) := v))"
          by auto
        show ?thesis
        proof (cases v)
          case None
          have "Mapping.lookup (apply_of_upd_impl (OFU f as v) ofi) f = Some (Mapping.delete (map the as) a)"
            using None \<open>Mapping.lookup ofi f = Some a\<close>
            by auto
          hence 2: "?m1 f = Some (Mapping.lookup (Mapping.delete (map the as) a))"
            using to_nested_map_SomeI by fastforce
          
          from None 1
          have "?m2 f = Some (a' ((map the as) := None))"
            by simp 
          from this 2
          show ?thesis 
            apply -
            apply (subst (asm) (2) \<open>f = x\<close>)
            apply (subst (asm) (3) \<open>f = x\<close>)
            apply (subst (asm) m, subst (asm) m')
            by (auto simp: a')
        next
          case (Some v')
          have "Mapping.lookup (apply_of_upd_impl (OFU f as v) ofi) f = Some (Mapping.update (map the as) v' a)"
            using Some \<open>Mapping.lookup ofi f = Some a\<close>
            by auto
          hence 2: "?m1 f = Some (Mapping.lookup (Mapping.update (map the as) v' a))"
            using to_nested_map_SomeI by fastforce
          
          from Some 1
          have "?m2 f = Some (a' ((map the as) := v))"
            by simp 
          from this 2
          show ?thesis 
            apply -
            apply (subst (asm) (2) \<open>f = x\<close>)
            apply (subst (asm) (3) \<open>f = x\<close>)
            apply (subst (asm) m, subst (asm) m')
            by (auto simp: a' Some)
        qed
      qed
    next
      case False
      then have "Mapping.lookup (apply_of_upd_impl (OFU f as v) ofi) x = Mapping.lookup ofi x"
        by (cases "Mapping.lookup ofi f"; cases v; auto)
      then have "?m1 x = to_nested_map ofi x"
        unfolding to_nested_map_def by (simp add: lookup_map_values)
      moreover
      from False
      have "?m2 x = to_nested_map ofi x"
        by (cases "to_nested_map ofi f"; cases v; auto)
      ultimately
      show ?thesis using m' m by simp
    qed
    with m m'
    show ?thesis by auto
  qed
qed


  fun upd_nf_int_impl::"(object list, rat) mapping \<Rightarrow> upd_op \<Rightarrow> object list \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> (object list, rat) mapping" where
    "upd_nf_int_impl m Assign args old n = (Mapping.update args n m)"
  | "upd_nf_int_impl m ScaleUp args old n = (Mapping.update args (old * n) m)"
  | "upd_nf_int_impl m ScaleDown args old n = (Mapping.update args (old / n) m)"
  | "upd_nf_int_impl m Increase args old n = (Mapping.update args (old + n) m)"
  | "upd_nf_int_impl m Decrease args old n = (Mapping.update args (old - n) m)"

  fun apply_nf_upd_impl::"instantiated_nf_upd \<Rightarrow> mp_nfi \<Rightarrow> mp_nfi" where
    "apply_nf_upd_impl (NFU n op as v) ni = (
      let f' = (case Mapping.lookup ni n of Some f' \<Rightarrow> f' | None \<Rightarrow> Mapping.empty)
      in Mapping.update n (upd_nf_int_impl f' op (map the as) (the (Mapping.lookup f' (map the as))) (the v)) ni)"

fun nf_upd_defined'_impl::"mp_nfi \<Rightarrow> instantiated_nf_upd \<Rightarrow> bool" where
  "nf_upd_defined'_impl _ (NFU _ Assign _ _) = True"
| "nf_upd_defined'_impl ni (NFU n _ args _) = (
    case (Mapping.lookup ni n) of
      Some f' \<Rightarrow> Mapping.lookup f' (map the args) \<noteq> None
    | None \<Rightarrow> False
)"

lemma upd_nf_int_impl_correct: "Mapping.lookup (upd_nf_int_impl m op args old new) = upd_nf_int (Mapping.lookup m) op args old new"
  by (cases op; auto)

lemma apply_nf_upd_impl_correct: "to_nested_map (apply_nf_upd_impl u nfi) = apply_nf_upd u (to_nested_map nfi)"
proof (rule ext; induction u)
  fix x::func
  and n::func
  and op::upd_op
  and as::"object option list"
  and v::"rat option"
  let ?m1 = "to_nested_map (apply_nf_upd_impl (NFU n op as v) nfi)"
  let ?m2 = "apply_nf_upd (NFU n op as v) (to_nested_map nfi)"

  have case_None: "?m1 x = None \<longleftrightarrow> ?m2 x = None"
  proof
    assume "?m1 x = None"
    hence 1: "Mapping.lookup (apply_nf_upd_impl (NFU n op as v) nfi) x = None"
      by (simp add: to_nested_map_None)
    hence "n \<noteq> x"
      by (cases "Mapping.lookup nfi n"; auto)
    with 1
    have "Mapping.lookup nfi x = None"
      by (cases "Mapping.lookup nfi n"; auto)
    hence "to_nested_map nfi x = None" by (simp add: to_nested_map_None)
    with 1
    show "?m2 x = None"
      by (auto simp: Let_def)
  next
    assume a: "?m2 x = None"
    hence n: "n \<noteq> x"
      by (cases "to_nested_map nfi n"; auto)
    with a
    have "to_nested_map nfi x = None"
      by (cases "to_nested_map nfi n"; auto)
    with n
    have "Mapping.lookup (apply_nf_upd_impl (NFU n op as v) nfi) x = None"
      by (cases "Mapping.lookup nfi n"; auto elim: to_nested_map_NoneE)
    thus "?m1 x = None"
      by (auto intro: to_nested_map_NoneI)
  qed 

  show "?m1 x = ?m2 x"
  proof (cases "?m1 x")
    case None
    thus ?thesis using case_None by presburger
  next
    case (Some a)
    then obtain a' where
      "?m2 x = a'" using case_None by blast
    
    show ?thesis
    proof (cases "n = x")
      case True
      have "?m1 n = ?m2 n"
      proof (cases "Mapping.lookup nfi n")
        case None
        hence "?m1 n = Some (Mapping.lookup (upd_nf_int_impl Mapping.empty op (map the as) (the (Mapping.lookup Mapping.empty (map the as))) (the v)))"
          using to_nested_map_Some by fastforce
        hence "?m1 n = Some (Mapping.lookup (upd_nf_int_impl Mapping.empty op (map the as) (the None) (the v)))"
          by simp
        moreover
        from None
        have "to_nested_map nfi n = None" by (rule to_nested_map_NoneI)
        hence "?m2 n = Some (upd_nf_int Map.empty op (map the as) (the (Map.empty (map the as))) (the v))"
          by auto
        hence "?m2 n = Some (upd_nf_int (Mapping.lookup Mapping.empty) op (map the as) (the None) (the v))"
          by (simp add: Mapping.empty_def Mapping.lookup.abs_eq)
        ultimately 
        show ?thesis using  upd_nf_int_impl_correct by presburger
      next
        case (Some a)
        hence "?m1 n = Some (Mapping.lookup (upd_nf_int_impl a op (map the as) (the (Mapping.lookup a (map the as))) (the v)))"
          using to_nested_map_Some by fastforce
        moreover
        from Some
        have "to_nested_map nfi n = Some (Mapping.lookup a)" by (rule to_nested_map_SomeI)
        hence "?m2 n = Some (upd_nf_int (Mapping.lookup a) op (map the as) (the (Mapping.lookup a (map the as))) (the v))"
          by (auto simp: Let_def)
        ultimately
        show ?thesis using upd_nf_int_impl_correct by presburger
      qed
      with \<open>n = x\<close> 
      show ?thesis by simp
    next
      case False
      hence "Mapping.lookup (apply_nf_upd_impl (NFU n op as v) nfi) x = Mapping.lookup nfi x"
        by (cases "Mapping.lookup nfi n"; auto)
      hence "?m1 x = to_nested_map nfi x" by (simp add: lookup_map_values to_nested_map_def)      
      with False
      show ?thesis by (cases "to_nested_map nfi n"; auto)
    qed
  qed
qed

lemma apply_of_upd_impl_correct': "to_nested_map (fold apply_of_upd_impl upds oi) = fold apply_of_upd upds (to_nested_map oi)"
  by (induction upds arbitrary: oi; auto simp: apply_of_upd_impl_correct)

lemma apply_nf_upd_impl_correct': "to_nested_map (fold apply_nf_upd_impl upds ni) = fold apply_nf_upd upds (to_nested_map ni)"
  using apply_nf_upd_impl_correct
  by (induction upds arbitrary: ni, auto)


  text \<open>We implement the application of an effect by explicit iteration over
    the additions and deletions\<close>
  fun apply_effect_impl
    :: "fully_instantiated_effect \<Rightarrow> exec_world_model \<Rightarrow> exec_world_model"
  where
    "apply_effect_impl (Eff a d ou nu) (EWM p ofi nfi)
      = EWM (fold (\<lambda>add s. Set.insert (the add) s) a
          (fold (\<lambda>del s. Set.remove (the del) s) d p)) 
          (fold apply_of_upd_impl ou ofi)
          (fold apply_nf_upd_impl nu nfi)"

lemma fold_comp: "fold (f o g) = (fold f) o (map g)"
  apply (rule ext)
  subgoal for xs
    by (induction xs, auto)
  done

lemma apply_effect_impl_correct: "exec_wm_to_wm (apply_effect_impl e wm) = apply_effect e (exec_wm_to_wm wm)"
  apply (induction e; induction wm)
  subgoal for ps ofi nfi a d ous nus
    unfolding apply_effect_impl.simps apply_effect.simps exec_wm_to_wm.simps
    apply (subst apply_nf_upd_impl_correct', subst apply_of_upd_impl_correct')
    apply (subst sym[OF comp_def[of insert the]])
    apply (subst sym[OF comp_def[of Set.remove the]])
    apply (subst fold_comp[of insert the])
    apply (subst fold_comp[of Set.remove the])
    by (metis Un_commute comp_apply minus_set_fold union_set_fold)
  done

definition inst_apply_effect_impl::"exec_world_model \<Rightarrow> ground_effect \<Rightarrow> exec_world_model \<Rightarrow> exec_world_model" where
  "inst_apply_effect_impl eM eff M = (apply_effect_impl (inst_effect_impl eM eff) M)"

lemma inst_apply_effect_impl_correct:
  assumes "exec_wm_to_wm eM = eM'"
      and "exec_wm_to_wm M = M'"
    shows "exec_wm_to_wm (inst_apply_effect_impl eM eff M) = inst_apply_effect eM' eff M'"
  using assms apply_effect_impl_correct inst_effect_impl_correct inst_apply_effect_def inst_apply_effect_impl_def
  by simp

definition inst_apply_conditional_effect_impl::"exec_world_model \<Rightarrow> (ground_formula \<times> ground_effect) 
  \<Rightarrow> exec_world_model \<Rightarrow> exec_world_model" where
  "inst_apply_conditional_effect_impl eM eff M = (
    if (valuation_impl eM \<Turnstile> (fst eff))
    then (inst_apply_effect_impl eM (snd eff) M)
    else M)"

lemma inst_apply_conditional_effect_impl_correct: 
  assumes "exec_wm_to_wm eM = eM'"
      and "exec_wm_to_wm M = M'"
    shows "exec_wm_to_wm (inst_apply_conditional_effect_impl eM eff M) = inst_apply_conditional_effect eM' eff M'"
  using assms inst_apply_conditional_effect_def inst_apply_conditional_effect_impl_def valuation_impl_correct inst_apply_effect_impl_correct
  by presburger

definition apply_conditional_effect_list_impl where
  "apply_conditional_effect_list_impl effs M = foldr (inst_apply_conditional_effect_impl M) effs M"

lemma apply_conditional_effect_list_impl_correct: 
  "exec_wm_to_wm (apply_conditional_effect_list_impl effs M) 
    = apply_conditional_effect_list effs (exec_wm_to_wm M)"
  unfolding apply_conditional_effect_list_impl_def apply_conditional_effect_list_def
  by (induction effs arbitrary: M; auto simp: inst_apply_conditional_effect_impl_correct)

definition execute_ground_action_impl::"ground_action \<Rightarrow> exec_world_model \<Rightarrow> exec_world_model" where
  "execute_ground_action_impl a M = apply_conditional_effect_list_impl (effects a) M"

lemma execute_ground_action_impl_correct: 
  "exec_wm_to_wm (execute_ground_action_impl a M) 
    = execute_ground_action a (exec_wm_to_wm M)"
  using execute_ground_action_def execute_ground_action_impl_def
  apply_conditional_effect_list_impl_correct by simp

context 
  fixes of_type::"type \<Rightarrow> type \<Rightarrow> bool"
    and ofs::"func \<rightharpoonup> (type list \<times> type)"
    and nfs::"func \<rightharpoonup> type list"
    and obT::"object \<rightharpoonup> type"
begin
  abbreviation "is_obj_of_type' \<equiv> is_of_type' of_type obT"

  fun wf_app_pred_upd' where
    "wf_app_pred_upd' None = False"
  | "wf_app_pred_upd' (Some (pred.Eq _ _)) = False"
  | "wf_app_pred_upd' (Some (Pred p as)) = wf_pred_eq' of_type obT (Pred p as)" 

  fun wf_app_of_upd'::"instantiated_of_upd \<Rightarrow> bool" where
      "wf_app_of_upd' (OFU f as v) = (case ofs f of 
            None \<Rightarrow> False
          | Some (Ts, T) \<Rightarrow>
                list_all is_some as
              \<and> list_all2 (is_obj_of_type' o the) as Ts 
              \<and> (v = None \<or> is_obj_of_type' (the v) T))"
  
  definition nf_args_well_typed'::"func \<Rightarrow> object list \<Rightarrow> bool" where
    "nf_args_well_typed' f args = (case nfs f of None \<Rightarrow> False | Some Ts \<Rightarrow> list_all2 is_obj_of_type' args Ts)"

  fun wf_app_nf_upd'::"instantiated_nf_upd \<Rightarrow> bool" where
      "wf_app_nf_upd' (NFU f op args v) = (
          list_all is_some args 
        \<and> is_some v \<and> (op = ScaleDown \<longrightarrow> the v \<noteq> (of_rat 0))
        \<and> nf_args_well_typed' f (map the args))"

  fun wf_fully_instantiated_effect' where
    "wf_fully_instantiated_effect' (Eff a d tu nu) \<longleftrightarrow> 
        (\<forall>ae \<in> set a. wf_app_pred_upd' ae)
      \<and> (\<forall>de \<in> set d. wf_app_pred_upd' de)
      \<and> (\<forall>u \<in> set tu. wf_app_of_upd' u)     
      \<and> (\<forall>u \<in> set nu. wf_app_nf_upd' u)"

end

abbreviation "wf_app_pred_upd_impl \<equiv> wf_app_pred_upd' of_type_impl objT_impl"

lemma wf_app_pred_upd_impl_correct: "wf_app_pred_upd_impl x = wf_app_pred_upd x"
  apply (cases x)
  subgoal by simp
  subgoal for p
    apply (cases p)
    subgoal using wf_pred_eq_impl_correct[of objT] 
          objT_impl_correct[THEN arg_cong[of _ _ wf_pred_eq_impl]] by auto
    subgoal by auto
    done
  done

abbreviation "wf_app_of_upd_impl \<equiv> wf_app_of_upd' of_type_impl ofs_impl objT_impl"

lemma wf_app_of_upd_impl_correct: "wf_app_of_upd_impl u = wf_app_of_upd u"
  apply (induction u)
  unfolding wf_app_of_upd.simps wf_app_of_upd'.simps
    ofs_impl_correct is_of_type_impl_correct objT_impl_correct 
  ..


abbreviation "nf_args_well_typed_impl \<equiv> nf_args_well_typed' of_type_impl nfs_impl objT_impl"

lemma nf_args_well_typed_impl_correct: "nf_args_well_typed_impl f args = nf_args_well_typed f args"
  unfolding nf_args_well_typed_def nf_args_well_typed'_def
  apply (subst nfs_impl_correct)
  apply (subst is_of_type_impl_correct)
  apply (subst objT_impl_correct)
  ..

abbreviation "wf_app_nf_upd_impl \<equiv> wf_app_nf_upd' of_type_impl nfs_impl objT_impl"

lemma wf_app_nf_upd_impl_correct: "wf_app_nf_upd_impl u = wf_app_nf_upd u"
  apply (induction u)
  unfolding wf_app_nf_upd'.simps wf_app_nf_upd.simps
    apply (subst nf_args_well_typed_impl_correct)
  ..

abbreviation "wf_fully_instantiated_effect_impl \<equiv> wf_fully_instantiated_effect' of_type_impl ofs_impl nfs_impl objT_impl"

lemma wf_fully_instantiated_effect_impl_correct: "wf_fully_instantiated_effect_impl e = wf_fully_instantiated_effect e"
  apply (induction e)
  unfolding wf_fully_instantiated_effect'.simps wf_fully_instantiated_effect.simps
      wf_app_pred_upd_impl_correct wf_app_of_upd_impl_correct wf_app_nf_upd_impl_correct ..

definition non_int_cond_effs_impl::"exec_world_model \<Rightarrow> (ground_formula \<times> ground_effect) 
  \<Rightarrow> (ground_formula \<times> ground_effect) \<Rightarrow> bool" where
  "non_int_cond_effs_impl M e1 e2 = ((valuation_impl M \<Turnstile> fst e1 \<and> valuation_impl M \<Turnstile> fst e2)
    \<longrightarrow> (non_int_effs (inst_effect_impl M (snd e1)) (inst_effect_impl M (snd e2))))"

lemma non_int_cond_effs_impl_correct: "non_int_cond_effs_impl M e1 e2 = non_int_cond_effs (exec_wm_to_wm M) e1 e2"
  unfolding non_int_cond_effs_impl_def non_int_cond_effs_def
    inst_effect_impl_correct valuation_impl_correct
  ..

definition "non_int_cond_eff_list_impl M xs \<equiv> pairwise (non_int_cond_effs_impl M) (set xs)"

lemma non_int_cond_eff_list_impl_correct: 
  "non_int_cond_eff_list_impl M xs = non_int_cond_eff_list (exec_wm_to_wm M) xs"
  unfolding non_int_cond_eff_list_impl_def non_int_cond_eff_list_def
  using non_int_cond_effs_impl_correct by presburger

definition of_upd_rv_corr_impl::"exec_world_model \<Rightarrow> object term of_upd \<Rightarrow> bool" where
  "of_upd_rv_corr_impl M u \<equiv> of_upd_rv_corr' u (inst_of_upd_impl M u)"

lemma of_upd_rv_corr_impl_correct: "of_upd_rv_corr_impl M u = of_upd_rv_corr (exec_wm_to_wm M) u"
  unfolding of_upd_rv_corr_def of_upd_rv_corr_impl_def
  inst_of_upd_impl_correct 
  ..

fun int_defines_nf_upd_impl::"mp_nfi \<Rightarrow> instantiated_nf_upd \<Rightarrow> bool" where
    "int_defines_nf_upd_impl _ (NFU _ Assign _ _) = True"
  | "int_defines_nf_upd_impl ni (NFU f _ args _) = (
      case Mapping.lookup ni f of 
        Some f' \<Rightarrow> Mapping.lookup f' (map the args) \<noteq> None
      | None \<Rightarrow> False)"

lemma int_defines_nf_upd_impl_correct: "int_defines_nf_upd_impl nfi upd = int_defines_nf_upd (to_nested_map nfi) upd"
  apply (cases upd)
  subgoal for f op args
    apply (cases "Mapping.lookup nfi f")
    subgoal by (frule to_nested_map_NoneI; cases op; simp)
    subgoal by (frule to_nested_map_SomeI; cases op; simp)
    done
  done

definition nf_upd_defined_impl::"exec_world_model \<Rightarrow> exec_world_model \<Rightarrow> object term nf_upd \<Rightarrow> bool" where
    "nf_upd_defined_impl eM M upd = int_defines_nf_upd_impl (enfi M) (inst_nf_upd_impl eM upd)"


lemma nf_upd_defined_impl_correct: "nf_upd_defined_impl eM M upd = nf_upd_defined (exec_wm_to_wm eM) (exec_wm_to_wm M) upd"
  unfolding nf_upd_defined_def nf_upd_defined_impl_def
  using int_defines_nf_upd_impl_correct inst_nf_upd_impl_correct
  by simp

definition well_inst_effect_impl::"exec_world_model \<Rightarrow> ground_effect \<Rightarrow> exec_world_model \<Rightarrow> bool" where
    "well_inst_effect_impl eM eff M \<equiv> list_all (of_upd_rv_corr_impl eM) (of_upds eff) \<and> list_all (nf_upd_defined_impl eM M) (nf_upds eff)"

lemma well_inst_effect_impl_correct: "well_inst_effect_impl eM eff M = well_inst_effect (exec_wm_to_wm eM) eff (exec_wm_to_wm M)"
  unfolding well_inst_effect_def well_inst_effect_impl_def
  using nf_upd_defined_impl_correct of_upd_rv_corr_impl_correct
  by presburger

definition well_inst_cond_effect_impl::"exec_world_model \<Rightarrow> exec_world_model \<Rightarrow> (ground_formula \<times> ground_effect) \<Rightarrow> bool" where
    "well_inst_cond_effect_impl eM M eff\<equiv> (valuation_impl eM \<Turnstile> (fst eff)) \<longrightarrow> (well_inst_effect_impl eM (snd eff) M)"

lemma well_inst_cond_effect_impl_correct: "well_inst_cond_effect_impl eM M eff = well_inst_cond_effect (exec_wm_to_wm eM) (exec_wm_to_wm M) eff"
  unfolding well_inst_cond_effect_impl_def well_inst_cond_effect_def
  using well_inst_effect_impl_correct valuation_impl_correct
  by presburger


definition well_inst_cond_effect_list_impl::"exec_world_model \<Rightarrow> exec_world_model \<Rightarrow> (ground_formula \<times> ground_effect) list \<Rightarrow> bool" where
  "well_inst_cond_effect_list_impl eM M effs \<equiv> list_all (well_inst_cond_effect_impl eM M) effs"

lemma well_inst_cond_effect_list_impl_correct: "well_inst_cond_effect_list_impl eM M effs = well_inst_cond_effect_list (exec_wm_to_wm eM) (exec_wm_to_wm M) effs"
  unfolding well_inst_cond_effect_list_impl_def well_inst_cond_effect_list_def
  using well_inst_cond_effect_impl_correct
  by presburger

definition wf_inst_cond_effect_impl::"exec_world_model \<Rightarrow> (ground_formula \<times> ground_effect) \<Rightarrow> bool" where
    "wf_inst_cond_effect_impl M eff = (valuation_impl M \<Turnstile> (fst eff) \<longrightarrow> (wf_fully_instantiated_effect_impl (inst_effect_impl M (snd eff))))"

lemma wf_inst_cond_effect_impl_correct: "wf_inst_cond_effect_impl M eff = wf_inst_cond_effect (exec_wm_to_wm M) eff"
  unfolding wf_inst_cond_effect_def wf_inst_cond_effect_impl_def
  using valuation_impl_correct wf_fully_instantiated_effect_impl_correct inst_effect_impl_correct
  by presburger

  definition wf_inst_cond_effect_list_impl::"exec_world_model \<Rightarrow> (ground_formula \<times> ground_effect) list \<Rightarrow> bool" where
    "wf_inst_cond_effect_list_impl M effs = list_all (wf_inst_cond_effect_impl M) effs"

lemma wf_inst_cond_effect_list_impl_correct: "wf_inst_cond_effect_list_impl M effs = wf_inst_cond_effect_list (exec_wm_to_wm M) effs"
  unfolding wf_inst_cond_effect_list_def wf_inst_cond_effect_list_impl_def
  using wf_inst_cond_effect_impl_correct by presburger

  definition valid_effects_impl::"exec_world_model \<Rightarrow> (ground_formula \<times> ground_effect) list \<Rightarrow> bool" where
    "valid_effects_impl M effs \<equiv> 
         (wf_inst_cond_effect_list_impl M effs)
      \<and> (well_inst_cond_effect_list_impl M M effs)
      \<and> (non_int_cond_eff_list_impl M effs)"

lemma valid_effects_impl_correct: "valid_effects_impl M effs = valid_effects (exec_wm_to_wm M) effs"
  unfolding valid_effects_impl_def valid_effects_def
  using wf_inst_cond_effect_list_impl_correct
        well_inst_cond_effect_list_impl_correct
        non_int_cond_eff_list_impl_correct
  by presburger


definition ground_action_enabled_impl::"ground_action \<Rightarrow> exec_world_model \<Rightarrow> bool" where
  "ground_action_enabled_impl \<alpha> M = valuation_impl M \<Turnstile> precondition \<alpha>"

lemma ground_action_enabled_impl_correct: "ground_action_enabled_impl \<alpha> M = ground_action_enabled \<alpha> (exec_wm_to_wm M)"
  unfolding ground_action_enabled_def ground_action_enabled_impl_def 
  using valuation_impl_correct by presburger

definition wf_ground_action_impl::"ground_action \<Rightarrow> bool" where
  "wf_ground_action_impl \<alpha> \<equiv> (
    wf_fmla_impl (ty_term_impl objT_impl) (precondition \<alpha>)
    \<and> wf_cond_effect_list_impl (ty_term_impl objT_impl) (effects \<alpha>))"

lemma wf_ground_action_impl_correct: "wf_ground_action_impl a = wf_ground_action a"
  unfolding wf_ground_action_impl_def wf_ground_action_def
    objT_impl_correct ty_term_impl_correct wf_fmla_impl_correct
    wf_cond_effect_list_impl_correct
  ..

definition valid_ground_action_impl::"ground_action \<Rightarrow> exec_world_model \<Rightarrow> bool" where
    "valid_ground_action_impl \<alpha> M \<equiv>
        wf_ground_action_impl \<alpha>
      \<and> ground_action_enabled_impl \<alpha> M 
      \<and> valid_effects_impl M (effects \<alpha>)"

lemma valid_ground_action_impl_correct: "valid_ground_action_impl a M = valid_ground_action a (exec_wm_to_wm M)"
  unfolding valid_ground_action_def valid_ground_action_impl_def
   wf_ground_action_impl_correct ground_action_enabled_impl_correct 
   valid_effects_impl_correct
  ..

 fun ground_action_path_impl
    :: "exec_world_model \<Rightarrow> ground_action list \<Rightarrow> exec_world_model \<Rightarrow> bool"
  where
    "ground_action_path_impl M [] M' \<longleftrightarrow> (M = M')"
  | "ground_action_path_impl M (\<alpha>#\<alpha>s) M' \<longleftrightarrow> valid_ground_action_impl \<alpha> M
    \<and> ground_action_path_impl (execute_ground_action_impl \<alpha> M) \<alpha>s M'"


lemma ground_action_path_impl_correct: "ground_action_path_impl M as M' = ground_action_path (exec_wm_to_wm M) as (exec_wm_to_wm M')"
  using valid_ground_action_impl_correct execute_ground_action_impl_correct
  apply (induction as arbitrary: M)
  apply (simp add: arg_cong[of M M' exec_wm_to_wm])

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>



context ast_problem
begin

  
  context 
    fixes of_type:: "type \<Rightarrow> type \<Rightarrow> bool"
      and ofs:: "func \<rightharpoonup> (type list \<times> type)"
      and nfs:: "func \<rightharpoonup> type list"
      and obt:: "object \<rightharpoonup> type"
  begin
    definition wf_of_arg_r_map'::"func \<Rightarrow> (object list \<rightharpoonup> object) \<Rightarrow> bool" where
      "wf_of_arg_r_map' f f' \<equiv> (case ofs f of 
        None \<Rightarrow> False 
      | Some (Ts, T) \<Rightarrow> 
          (\<forall>(as, v) \<in> Map.graph f'. list_all2 (is_of_type' of_type obt) as Ts 
          \<and> is_of_type' of_type obt v T))"
  
    definition wf_of_int'::"(func \<rightharpoonup> object list \<rightharpoonup> object) \<Rightarrow> bool" where
      "wf_of_int' oi \<equiv> (\<forall>(f, m) \<in> Map.graph oi. wf_of_arg_r_map' f m)"

    definition wf_of_int''::"(func \<rightharpoonup> (object list, object) mapping) \<Rightarrow> bool" where
      "wf_of_int'' oi \<equiv> (\<forall>(f, m) \<in> Map.graph oi. wf_of_arg_r_map' f (Mapping.lookup m))"

    definition wf_nf_int_map'::"func \<Rightarrow> (object list \<rightharpoonup> rat) \<Rightarrow> bool" where
      "wf_nf_int_map' n f' \<equiv> (case nfs n of 
        None \<Rightarrow> False 
      | Some Ts \<Rightarrow> \<forall>as \<in> dom f'. list_all2 (is_of_type' of_type obt) as Ts)"
  
    definition wf_nf_int'::"(func \<rightharpoonup> object list \<rightharpoonup> rat) \<Rightarrow> bool" where
      "wf_nf_int' ni \<equiv> (\<forall>(f, m) \<in> Map.graph ni. wf_nf_int_map' f m)"
    
    definition wf_nf_int''::"(func \<rightharpoonup> (object list, rat) mapping) \<Rightarrow> bool" where
      "wf_nf_int'' ni \<equiv> (\<forall>(f, m) \<in> Map.graph ni. wf_nf_int_map' f (Mapping.lookup m))"

  end

  abbreviation "wf_of_arg_r_map_refine \<equiv> wf_of_arg_r_map' of_type_impl ofs_impl objT_impl"
  
  lemma wf_of_arg_r_map_refine_correct: "wf_of_arg_r_map_refine = wf_of_arg_r_map"
    apply (intro ext)
    subgoal for f f'
      unfolding wf_of_arg_r_map_def wf_of_arg_r_map'_def
       ofs_impl_correct is_of_type_impl_correct
         objT_impl_correct
      ..
    done

  definition "wf_of_arg_r_map_impl f m = (wf_of_arg_r_map' of_type_impl ofs_impl objT_impl) f (Mapping.lookup m)"

lemma wf_of_arg_r_map_impl_correct: "wf_of_arg_r_map_impl f m = wf_of_arg_r_map f (Mapping.lookup m)"
  apply (subst wf_of_arg_r_map_impl_def)
  apply (subst wf_of_arg_r_map_refine_correct)
  ..

  definition "wf_of_int_refine = wf_of_int' of_type_impl ofs_impl objT_impl"
  
  lemma wf_of_int_refine_correct: "wf_of_int_refine ty_ent = wf_of_int ty_ent"
    unfolding wf_of_int_refine_def
      wf_of_int'_def wf_of_int_def
      wf_of_arg_r_map_refine_correct
    ..
(* To do: decide whether you even need these *)
definition "wf_of_int_impl oi = wf_of_int'' of_type_impl ofs_impl objT_impl (Mapping.lookup oi)"


lemma wf_of_int_impl_correct

  definition "wf_nf_int_map_refine = wf_nf_int_map' of_type_impl nfs_impl objT_impl"

  lemma wf_nf_int_map_refine_correct: "wf_nf_int_map_refine ty_ent = wf_nf_int_map ty_ent"
    unfolding wf_nf_int_map_refine_def
    apply (rule ext)
    subgoal for x
      unfolding wf_nf_int_map'_def wf_nf_int_map_def 
        is_of_type_impl_correct
        objT_impl_correct nfs_impl_correct
      ..
    done

  definition "wf_nf_int_refine = wf_nf_int' of_type_impl nfs_impl objT_impl"
  
  lemma wf_nf_int_refine_correct: "wf_nf_int_refine = wf_nf_int"
    unfolding wf_nf_int_refine_def  wf_nf_int'_def wf_nf_int_def
    wf_nf_int_map_refine_correct[simplified wf_nf_int_map_refine_def]
    ..

  definition wf_world_model'::"(type \<Rightarrow> type \<Rightarrow> bool) 
    \<Rightarrow> (func \<rightharpoonup> (type list \<times> type))
    \<Rightarrow> (func \<rightharpoonup> (type list))
    \<Rightarrow> (object \<rightharpoonup> type) 
    \<Rightarrow> world_model \<Rightarrow> bool" where
    "wf_world_model' ot ofs nfs obT M \<equiv> 
      (\<forall>p \<in> preds M. wf_predicate' ot obT p)
      \<and> wf_of_int' ot ofs obT (of_int M)
      \<and> wf_nf_int' ot nfs obT (nf_int M)"
  
  definition "wf_world_model_refine = 
    wf_world_model' 
      of_type_impl 
      ofs_impl
      nfs_impl
      objT_impl"
  
  lemma wf_world_model_refine_correct: "wf_world_model_refine = wf_world_model"
    unfolding wf_world_model_refine_def wf_world_model_def wf_world_model'_def
     wf_predicate_impl_correct
     wf_of_int_refine_correct[simplified wf_of_int_refine_def]
     wf_nf_int_refine_correct[simplified wf_nf_int_refine_def]
      apply (subst objT_impl_correct)
    ..
(* 
  text \<open>We refine the typecheck to use the mapping\<close>

  definition "is_obj_of_type_impl stg mp n T = (
    case Mapping.lookup mp n of None \<Rightarrow> False | Some oT \<Rightarrow> of_type_impl stg oT T
  )"

  lemma is_obj_of_type_impl_correct[simp]:
    "is_obj_of_type_impl STG mp_objT = is_obj_of_type"
    apply (intro ext)
    apply (auto simp: is_obj_of_type_impl_def is_obj_of_type_def of_type_impl_correct split: option.split)
    done
  text \<open>Instantiating actions will yield well-founded effects.
    Corollary of @{thm wf_instantiate_action_schema}.\<close>
  lemma wf_effect_inst_weak:
    fixes a args
    defines "ai \<equiv> instantiate_action_schema a args"
    assumes A: "action_params_match a args"
      "wf_action_schema a"
    shows "wf_effect_inst (effect ai)"
    using wf_instantiate_action_schema[OF A] unfolding ai_def[symmetric]
    by (cases ai) (auto simp: wf_effect_inst)
  find_theorems name: "wf*effe" *)

end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>


context wf_ast_problem begin
  text \<open>Resolving an action yields a well-founded action schema.\<close>
  (* TODO: This must be implicitly proved when showing that plan execution
    preserves wf. Try to remove this redundancy!*)
  lemma resolve_action_wf:
    assumes "resolve_action_schema n = Some a"
    shows "wf_action_schema a"
  proof -
    from wf_problem have
      X1: "distinct (map ast_action_schema.name (actions D))"
      and X2: "\<forall>a\<in>set (actions D). wf_action_schema a"
      unfolding wf_problem_def wf_domain_def by auto

    show ?thesis
      using assms unfolding resolve_action_schema_def
      by (auto simp add: index_by_eq_Some_eq[OF X1] X2)
  qed

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

subsubsection \<open>Execution of Plan Actions\<close>

text \<open>We will perform two refinement steps, to summarize redundant operations\<close>

text \<open>We first lift action schema lookup into the error monad. \<close>
context ast_domain begin
  definition "resolve_action_schemaE n \<equiv>
    lift_opt
      (resolve_action_schema n)
      (ERR (shows ''No such action schema '' o shows n))"
end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

context ast_problem begin

(*TODO: change to this valuation definition to hanlde equalities nicely
definition "valuation s \<equiv> \<lambda>x. case x of (atom.Atom P ARGS) \<Rightarrow>
                                                ((formula.Atom x) \<in> s)
                                    | (atom.Eq t1 t2) \<Rightarrow> (t1 = t2)"

primrec holds :: "'a formula set \<Rightarrow> 'a formula \<Rightarrow> bool" where
"holds s (Atom k) = ((Atom k) \<in> s)" |
"holds _ \<bottom> = False" |
"holds s (Not F) = (\<not> (holds s F))" |
"holds s (And F G) = (holds s F \<and> holds s G)" |
"holds s (Or F G) = (holds s F \<or> holds s G)" |
"holds s (Imp F G) = (holds s F \<longrightarrow> holds s G)"

  lemma holds_for_valid_formulas:
        assumes "\<forall>x\<in>s. \<exists>x'. x = formula.Atom x'"
        shows "s \<TTurnstile> F \<Longrightarrow> holds s F"
        unfolding holds_def entailment_def
        using assms
        apply (induction F; auto)
        subgoal for x apply(cases x)*)


  text \<open>We define a function to determine whether a formula holds in
    a world model\<close>
  definition "holds M F \<equiv> (valuation M) \<Turnstile> F"

  text \<open>Justification of this function\<close>

  lemma holds_for_wf_fmlas:
    assumes "wm_basic s"
    shows "holds s F \<longleftrightarrow> close_world s \<TTurnstile> F"
    unfolding holds_def using assms valuation_iff_close_world
    by blast

  (*
  lemma holds_for_wf_fmlas:
    assumes "\<forall>x\<in>s. is_Atom x" "wf_fmla Q F"
    shows "holds s F \<longleftrightarrow> s \<TTurnstile> F"
    unfolding holds_def entailment_def valuation_def
    using assms
  proof (induction F)
    case (Atom x)
    then show ?case
      apply auto
      by (metis formula_semantics.simps(1) is_Atom.elims(2) valuation_def)
  next
    case (Or F1 F2)
    then show ?case
      apply simp apply (safe; clarsimp?)
      by (metis (mono_tags) is_Atom.elims(2) formula_semantics.simps(1))
  qed auto
  *)

  text \<open>The first refinement summarizes the enabledness check and the execution
    of the action. Moreover, we implement the precondition evaluation by our
     @{const holds} function. This way, we can eliminate redundant resolving
     and instantiation of the action.
  \<close>

  definition en_exE :: "plan_action \<Rightarrow> world_model \<Rightarrow> _+world_model" where
    "en_exE \<equiv> \<lambda>(PAction n args) \<Rightarrow> \<lambda>s. do {
      a \<leftarrow> resolve_action_schemaE n;
      check (action_params_match a args) (ERRS ''Parameter mismatch'');
      let ai = instantiate_action_schema a args;
      check (wf_effect_inst (effect ai)) (ERRS ''Effect not well-formed'');
      check ( holds s (precondition ai)) (ERRS ''Precondition not satisfied'');
      Error_Monad.return (apply_effect (effect ai) s)
    }"

  (* here we check that an effect is well formed and we execute it *)

  text \<open>Justification of implementation.\<close>
  lemma (in wf_ast_problem) en_exE_return_iff:
    assumes "wm_basic s"
    shows "en_exE a s = Inr s'
      \<longleftrightarrow> plan_action_enabled a s \<and> s' = execute_plan_action a s"
    apply (cases a)
    using assms holds_for_wf_fmlas wf_domain
    unfolding plan_action_enabled_def execute_plan_action_def
      and execute_ground_action_def en_exE_def wf_domain_def
    by (auto
        split: option.splits
        simp: resolve_action_schemaE_def return_iff)

  text \<open>Next, we use the efficient implementation @{const is_obj_of_type_impl}
    for the type check, and omit the well-formedness check, as effects obtained
    from instantiating well-formed action schemas are always well-formed
    (@{thm [source] wf_effect_inst_weak}).\<close>
  abbreviation "action_params_match2 stg mp a args
    \<equiv> list_all2 (is_obj_of_type_impl stg mp)
        args (map snd (ast_action_schema.parameters a))"

  definition en_exE2
    :: "_ \<Rightarrow> (object, type) mapping \<Rightarrow> plan_action \<Rightarrow> world_model \<Rightarrow> _+world_model"
  where
    "en_exE2 G mp \<equiv> \<lambda>(PAction n args) \<Rightarrow> \<lambda>M. do {
      a \<leftarrow> resolve_action_schemaE n;
      check (action_params_match2 G mp a args) (ERRS ''Parameter mismatch'');
      let ai = instantiate_action_schema a args;
      check (holds M (precondition ai)) (ERRS ''Precondition not satisfied'');
      Error_Monad.return (apply_effect (effect ai) M)
    }"

  text \<open>Justification of refinement\<close>
  lemma (in wf_ast_problem) wf_en_exE2_eq:
    shows "en_exE2 STG mp_objT pa s = en_exE pa s"
    apply (cases pa; simp add: en_exE2_def en_exE_def Let_def)
    apply (auto
      simp: return_iff resolve_action_schemaE_def resolve_action_wf
      simp: wf_effect_inst_weak action_params_match_def
      split: error_monad_bind_split)
    done

  text \<open>Combination of the two refinement lemmas\<close>
  lemma (in wf_ast_problem) en_exE2_return_iff:
    assumes "wm_basic M"
    shows "en_exE2 STG mp_objT a M = Inr M'
      \<longleftrightarrow> plan_action_enabled a M \<and> M' = execute_plan_action a M"
    unfolding wf_en_exE2_eq
    apply (subst en_exE_return_iff)
    using assms
    by (auto)

  lemma (in wf_ast_problem) en_exE2_return_iff_compact_notation:
    "\<lbrakk>wm_basic s\<rbrakk> \<Longrightarrow>
      en_exE2 STG mp_objT a s = Inr s'
      \<longleftrightarrow> plan_action_enabled a s \<and> s' = execute_plan_action a s"
    using en_exE2_return_iff .

end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>

subsubsection \<open>Checking of Plan\<close>

context ast_problem begin

  text \<open>First, we combine the well-formedness check of the plan actions and
    their execution into a single iteration.\<close>
  fun valid_plan_from1 :: "world_model \<Rightarrow> plan \<Rightarrow> bool" where
    "valid_plan_from1 s [] \<longleftrightarrow> valuation s \<Turnstile> (inst_goal (goal P))"
  | "valid_plan_from1 s (\<pi>#\<pi>s)
      \<longleftrightarrow> valid_plan_action \<pi> s
        \<and> (valid_plan_from1 (execute_plan_action \<pi> s) \<pi>s)"

  lemma valid_plan_from1_refine: "valid_plan_from s \<pi>s = valid_plan_from1 s \<pi>s"
  proof(induction \<pi>s arbitrary: s)
    case Nil
    then show ?case by (auto simp add: plan_action_path_def valid_plan_from_def)
  next
    case (Cons a \<pi>s)
    then show ?case
      by (auto
        simp: valid_plan_from_def plan_action_path_def plan_action_enabled_def
        simp: execute_ground_action_def execute_plan_action_def)
  qed

  text \<open>Next, we use our efficient combined enabledness check and execution
    function, and transfer the implementation to use the error monad: \<close>
  fun valid_plan_fromE
    :: "_ \<Rightarrow> (object, type) mapping \<Rightarrow> nat \<Rightarrow> world_model \<Rightarrow> plan \<Rightarrow> _+unit"
  where
    "valid_plan_fromE stg mp si s []
      = check (holds s (inst_goal (goal P))) (ERRS ''Postcondition does not hold'')"
  | "valid_plan_fromE stg mp si s (\<pi>#\<pi>s) = do {
        s \<leftarrow> en_exE2 stg mp \<pi> s
          <+? (\<lambda>e _. shows ''at step '' o shows si o shows '': '' o e ());
        valid_plan_fromE stg mp (si+1) s \<pi>s
      }"


  text \<open>For the refinement, we need to show that the world models only
    contain atoms, i.e., containing only atoms is an invariant under execution
    of well-formed plan actions.\<close>
  lemma (in wf_ast_problem) wf_actions_only_add_atoms:
    "\<lbrakk> wm_basic s; wf_plan_action a \<rbrakk>
      \<Longrightarrow> wm_basic (execute_plan_action a s)"
    using wf_problem wf_domain
    unfolding wf_problem_def wf_domain_def
    apply (cases a)
    apply (clarsimp
      split: option.splits
      simp: wf_fmla_atom_alt execute_plan_action_def wm_basic_def
      simp: execute_ground_action_def)
    subgoal for n args schema fmla
      apply (cases "effect (instantiate_action_schema schema args)"; simp)
      by (metis ground_action.sel(2) wf_effect.simps
            wf_fmla_atom_alt resolve_action_wf
            wf_ground_action.elims(2) wf_instantiate_action_schema)
    done

  text \<open>Refinement lemma for our plan checking algorithm\<close>
  lemma (in wf_ast_problem) valid_plan_fromE_return_iff[return_iff]:
    assumes "wm_basic s"
    shows "valid_plan_fromE STG mp_objT k s \<pi>s = Inr () \<longleftrightarrow> valid_plan_from s \<pi>s"
    using assms unfolding valid_plan_from1_refine
  proof (induction stg\<equiv>STG mp\<equiv>mp_objT k s \<pi>s rule: valid_plan_fromE.induct)
    case (1 si s)
    then show ?case
      using wf_problem holds_for_wf_fmlas
      by (auto
        simp: return_iff Let_def wf_en_exE2_eq wf_problem_def
        split: plan_action.split)
  next
    case (2 si s \<pi> \<pi>s)
    then show ?case
      apply (clarsimp
        simp: return_iff en_exE2_return_iff
        split: plan_action.split)
      by (meson ast_problem.plan_action_enabled_def wf_actions_only_add_atoms)
  qed

  lemmas valid_plan_fromE_return_iff'[return_iff]
    = wf_ast_problem.valid_plan_fromE_return_iff[of P, OF wf_ast_problem.intro]

  (* TODO: This function is unused! *)
  (*fun apply_effect_exec''
    :: "object atom ast_effect \<Rightarrow> world_model \<Rightarrow> world_model"
    where
    "apply_effect_exec'' (Effect (adds) (dels)) s
      = fold (%add s. insert add s)
          (map formula.Atom adds)
          (fold (%del s. Set.remove del s) (map formula.Atom dels) s)"
  *)


end \<comment> \<open>Context of \<open>wf_ast_problem\<close>\<close>

subsection \<open>Executable Plan Checker\<close>
text \<open>We obtain the main plan checker by combining the well-formedness check
  and executability check. \<close>


definition "check_all_list P l msg msgf \<equiv>
  forallM (\<lambda>x. check (P x) (\<lambda>_::unit. shows msg o shows '': '' o msgf x) ) l <+? snd"

lemma check_all_list_return_iff[return_iff]: "check_all_list P l msg msgf = Inr () \<longleftrightarrow> (\<forall>x\<in>set l. P x)"
  unfolding check_all_list_def
  by (induction l) (auto)

definition "check_wf_types D \<equiv> do {
  check_all_list (\<lambda>(_,t). t=''object'' \<or> t\<in>fst`set (types D)) (types D) ''Undeclared supertype'' (shows o snd)
}"

lemma check_wf_types_return_iff[return_iff]: "check_wf_types D = Inr () \<longleftrightarrow> ast_domain_decs.wf_types D"
  unfolding ast_domain_decs.wf_types_def check_wf_types_def
  by (force simp: return_iff)


definition "check_wf_domain_decs DD stg conT \<equiv> do {
  check_wf_types DD;
  check (distinct (map (predicate_decl.pred) (predicates DD))) (ERRS ''Duplicate predicate declaration'');
  check_all_list (ast_domain_decs.wf_predicate_decl DD) (predicates DD) ''Malformed predicate declaration'' (shows o predicate.name o predicate_decl.pred);
  check (distinct (map fst (consts DD))) (ERRS  ''Duplicate constant declaration'');
  check (\<forall>(n,T)\<in>set (consts DD). ast_domain_decs.wf_type DD T) (ERRS ''Malformed type'')
}"

lemma check_wf_domain_decs_return_iff[return_iff]:
  "check_wf_domain_decs DD stg conT = Inr () \<longleftrightarrow> ast_domain_decs.wf_domain_decs' DD stg conT"
proof -
  interpret ast_domain_decs DD .
  show ?thesis
    unfolding check_wf_domain_decs_def wf_domain_decs'_def
    by (auto simp: return_iff)
qed


definition "prepend_err_msg msg e \<equiv> \<lambda>_::unit. shows msg o shows '': '' o e ()"


definition "check_wf_problem_decs PD stg conT mp \<equiv> do {
  let DD = ast_problem_decs.domain_decs PD;
  check_wf_domain_decs DD stg conT <+? prepend_err_msg ''Domain declarations not well-formed'';
  check (distinct (map fst (objects PD) @ map fst (consts DD))) (ERRS ''Duplicate object declaration'');
  check ((\<forall>(n,T)\<in>set (objects PD). ast_domain_decs.wf_type DD T)) (ERRS ''Malformed type'')
}"

lemma check_wf_problem_decs_return_iff[return_iff]:
  "check_wf_problem_decs PD stg conT mp = Inr () \<longleftrightarrow> ast_problem_decs.wf_problem_decs' PD stg conT mp"
proof -
  interpret ast_problem_decs PD .
  show ?thesis
    unfolding check_wf_problem_decs_def wf_problem_decs'_def
    by (auto simp: return_iff)
qed


definition "check_wf_domain D stg conT mp \<equiv> do {
  let PD = ast_domain.problem_decs D;
  check_wf_problem_decs PD stg conT mp <+? prepend_err_msg ''Declarations from problem not well-formed'';
  check (distinct (map ast_action_schema.name (actions D))  ) (ERRS ''Duplicate action name'');
  check_all_list (ast_problem_decs.wf_action_schema' PD stg mp) (actions D) ''Malformed action'' (shows o ast_action_schema.name)
}"

lemma check_wf_domain_return_iff[return_iff]:
  "check_wf_domain D stg conT mp = Inr () \<longleftrightarrow> ast_domain.wf_domain' D stg conT mp"
proof -
  interpret ast_domain D .
  show ?thesis
    unfolding check_wf_domain_def wf_domain'_def
    by (auto simp: return_iff)
qed
definition "check_wf_problem P stg conT mp \<equiv> do {
  let D = ast_problem.domain P;
  let PD = ast_domain.problem_decs D;
  check_wf_domain D stg conT mp <+? prepend_err_msg ''Domain not well-formed'';
  check (ast_problem_decs.wf_goal' PD mp stg (goal P)) (ERRS ''Malformed goal formula'');
  check (distinct (init P)) (ERRS ''Duplicate fact in initial state'');
  check (\<forall>f\<in>set (init P). ast_problem_decs.wf_fmla_atom2' PD mp stg f) (ERRS ''Malformed formula in initial state'')
}"

lemma check_wf_problem_return_iff[return_iff]:
  "check_wf_problem P stg conT mp = Inr () \<longleftrightarrow> ast_problem.wf_problem' P stg conT mp"
proof -
  interpret ast_problem P .
  show ?thesis
    unfolding check_wf_problem_def wf_problem'_def
    by (auto simp: return_iff)
qed

definition "check_plan P \<pi>s \<equiv> do {
  let D = ast_problem.domain P;
  let PD = ast_domain.problem_decs D;
  let DD = ast_problem_decs.domain_decs PD;
  let stg=ast_domain_decs.STG DD;
  let conT = ast_domain_decs.mp_constT DD;
  let mp = ast_problem_decs.mp_objT PD;
  check_wf_problem P stg conT mp;
  ast_problem.valid_plan_fromE P stg mp 1 (ast_problem.I P) \<pi>s
} <+? (\<lambda>e. String.implode (e () ''''))"

text \<open>Correctness theorem of the plan checker: It returns @{term "Inr ()"}
  if and only if the problem is well-formed and the plan is valid.
\<close>
theorem check_plan_return_iff[return_iff]: "check_plan P \<pi>s = Inr ()
  \<longleftrightarrow> ast_problem.wf_problem P \<and> ast_problem.valid_plan P \<pi>s"
proof -
  interpret ast_problem P .
  thm return_iff
  show ?thesis
    unfolding check_plan_def 
    by (auto
      simp: return_iff wf_world_model_def wf_fmla_atom_alt I_def wf_problem_def wf_domain_def wf_problem_decs_def wf_domain_decs_def isOK_iff 
      simp: wf_problem'_correct ast_problem.I_def ast_problem.valid_plan_def wm_basic_def
      simp: Let_def
      )
qed


subsection \<open>Code Setup\<close>

text \<open>In this section, we set up the code generator to generate verified
  code for our plan checker.\<close>

subsubsection \<open>Code Equations\<close>
text \<open>We first register the code equations for the functions of the checker.
  Note that we not necessarily register the original code equations, but also
  optimized ones.
\<close>

lemmas wf_domain_decs_code =
  ast_domain_decs.sig_def
  ast_domain_decs.wf_types_def
  ast_domain_decs.wf_type.simps
  ast_domain_decs.wf_predicate_decl.simps
  ast_domain_decs.STG_def
  ast_domain_decs.is_of_type'_def
  ast_domain_decs.wf_atom'.simps(* 
  ast_domain_decs.wf_pred_atom'.simps *)
  ast_domain_decs.wf_fmla'.simps(* 
  ast_domain_decs.wf_fmla_atom1'.simps *)
  ast_domain_decs.wf_effect'.simps(* 
  ast_domain_decs.wf_domain_decs'_def *)
  ast_domain_decs.mp_constT_def
  ast_domain_decs.subtype_edge.simps
  ast_domain_decs.of_type_impl_def

declare wf_domain_decs_code[code]

lemmas wf_problem_decs_code =
  ast_problem_decs.wf_goal'_def(* 
  ast_problem_decs.term_vars_impl.simps *)
  ast_problem_decs.f_vars_impl.simps
  ast_problem_decs.t_dom_impl_def
  ast_problem_decs.unique_vars'.simps
  ast_problem_decs.all_impl_def
  ast_problem_decs.exists_impl_def
  ast_problem_decs.pddl_all_impl_def
  ast_problem_decs.pddl_all_def
  ast_problem_decs.pddl_exists_impl_def
  ast_problem_decs.wf_action_schema'.simps
  ast_problem_decs.atom_vars_impl.simps
  ast_problem_decs.pred_vars_impl.simps
  ast_problem_decs.nc_vars_impl.simps
  ast_problem_decs.term_vars_impl.simps 
  ast_problem_decs.nf_vars_impl.simps
  f_vars_def

declare wf_problem_decs_code[code]

lemmas wf_domain_code =
  ast_domain.inst_of_upd.simps
  ast_domain.upd_nf_int.simps
  ast_domain.apply_nf_upd.simps
  ast_domain.apply_of_upd_impl.simps
  ast_domain.upd_nf_int_impl.simps
  ast_domain.apply_nf_upd_impl.simps
  ast_domain.apply_effect_impl.simps
  ast_domain.non_int_nf_upds.simps
  ast_domain.non_int_nf_upd_list_def
(*
  ast_domain.wf_domain_def
  ast_domain.wf_action_schema.simps
  ast_domain.wf_effect.simps
  ast_domain.wf_fmla.simps
  ast_domain.wf_atom.simps
  ast_domain.is_of_type_def
  ast_domain.of_type_code
*)

declare wf_domain_code[code]

find_theorems name: "ast_problem*all"

lemmas wf_problem_code =
  ast_problem.wf_problem'_def(* 
  ast_problem.is_obj_of_type_alt *)
  ast_problem.inst_goal.simps 
  ast_problem.wf_plan_action.simps
  (*ast_problem.wf_effect_inst_weak.simps*)
  (*ast_problem.wf_object_def*)
  (*ast_problem.objT_def*)

declare wf_problem_code[code]


lemmas check_code =
  ast_problem.valid_plan_def(* 
  ast_problem.valid_plan_fromE.simps *)(* 
  ast_problem.en_exE2_def *)
  ast_problem.resolve_instantiate.simps
  ast_domain.resolve_action_schema_def
  ast_domain.resolve_action_schemaE_def
  ast_problem.I_def
  ast_domain.instantiate_action_schema.simps(* 
  ast_domain.apply_effect_exec.simps *)
  (*ast_domain.apply_effect_exec'.simps*)
(*   ast_domain.apply_effect_eq_impl_eq
 *)  (*ast_domain.apply_atomic.simps*)
  ast_problem.holds_def
  ast_problem_decs.mp_objT_def
(*   ast_problem.is_obj_of_type_impl_def
 ast_problem_decs.wf_fmla_atom2'_def
(*  *)  ast_problem_decs.valuation.simps
 *) 
declare check_code[code]

subsubsection \<open>Setup for Containers Framework\<close>

derive (linorder) compare rat

derive (eq) ceq predicate func num_fluent 
  num_comp pred atom object formula  
derive ccompare predicate func pred num_fluent num_comp 
  atom object formula
derive (rbt) set_impl atom formula

derive (rbt) mapping_impl object

derive linorder predicate object atom "object atom formula"

subsubsection \<open>More Efficient Distinctness Check for Linorders\<close>
(* TODO: Can probably be optimized even more. *)
fun no_stutter :: "'a list \<Rightarrow> bool" where
  "no_stutter [] = True"
| "no_stutter [_] = True"
| "no_stutter (a#b#l) = (a\<noteq>b \<and> no_stutter (b#l))"

lemma sorted_no_stutter_eq_distinct: "sorted l \<Longrightarrow> no_stutter l \<longleftrightarrow> distinct l"
  apply (induction l rule: no_stutter.induct)
  apply (auto simp: )
  done

definition distinct_ds :: "'a::linorder list \<Rightarrow> bool"
  where "distinct_ds l \<equiv> no_stutter (quicksort l)"

lemma [code_unfold]: "distinct = distinct_ds"
  apply (intro ext)
  unfolding distinct_ds_def
  apply (auto simp: sorted_no_stutter_eq_distinct)
  done

subsubsection \<open>Code Generation\<close>

derive (eq) ceq symbol "term"
derive ccompare "term" symbol 
derive (no) cenum variable
derive (rbt) set_impl "term"

print_derives

find_theorems name: "finite_UNIV_nat"


lemma "CARD(variable) = 0"
  using card_eq_0_iff
  using [[simp_trace_new]]
  apply simp
  sorry
find_theorems name: "nat*inf"

datatype test = Test1 | Test2

lemma "UNIV = {Test1, Test2}"
  apply (rule UNIV_eq_I)
  subgoal for x
    apply (cases x)
    by simp+
  done

value "UNIV::string set"

find_theorems name: "String*UNIV"

thm UNIV_eq_I insert_iff

lemma [simp]: "CARD(test) = 2"
  by (meson UNIV_I card_2_iff' test.distinct(2) test.exhaust)

value "length (replicate 4 CHR ''A'')"

lemma "infinite (range (\<lambda>n. replicate n CHR ''A''))"
  thm finite_range_imageI [of _ length]
  apply (auto dest: finite_range_imageI [of _ length])
  done

lemma "infinite (range (\<lambda>n. length (replicate n CHR ''B'')))"
  apply (subst length_replicate)
  using [[simp_trace]]
  by simp

thm Finite_Set.infinite_UNIV_nat

thm surj_def

lemma endo_inj_surj: "finite A \<Longrightarrow> f ` A \<subseteq> A \<Longrightarrow> inj_on f A \<Longrightarrow> f ` A = A"
  by (simp add: card_seteq card_image)

lemma finite_UNIV_inj_surj: "finite(UNIV:: 'a set) \<Longrightarrow> inj f \<Longrightarrow> surj f"
  for f :: "'a \<Rightarrow> 'a"
  by (fastforce simp:surj_def dest!: endo_inj_surj)

lemma infinite_UNIV_nat [iff]: "infinite (UNIV :: nat set)"
proof
  thm endo_inj_surj
  assume "finite (UNIV :: nat set)" 
    (* given a finite universal set, any function from the set to itself
       is surjective (\<forall>y. \<exists>x . f(x) = y) 
        if it is injective (f(a) = f(b) \<Longrightarrow> a = b)*)
  with finite_UNIV_inj_surj [of Suc] show False
    by simp (blast dest: Suc_neq_Zero surjD)
qed

lemma "range (\<lambda>n. n) \<equiv> UNIV"
  using [[simp_trace]]
  by simp
find_theorems name: "length*rep"

thm ex_new_if_finite finite.emptyI finite_insert insert_iff test.exhaust UNIV_I finite_maxlen length_replicate less_irrefl
lemma infinite_literal:
  "infinite (UNIV :: String.literal set)"
proof -
  define S where "S = range (\<lambda>n. replicate n CHR ''A'')"
  have "inj_on String.implode S"
  proof (rule inj_onI)
    fix cs ds
    assume "String.implode cs = String.implode ds"
    then have "String.explode (String.implode cs) = String.explode (String.implode ds)"
      by simp
    moreover assume "cs \<in> S" and "ds \<in> S"
    ultimately show "cs = ds"
      by (auto simp add: S_def)
  qed
  thm finite_range_imageI [of _ length]
  moreover have "infinite S"
    by (auto simp add: S_def dest: finite_range_imageI [of _ length])
  ultimately have "infinite (String.implode ` S)"
    thm finite_image_iff
    by (simp add: finite_image_iff)
  then show ?thesis
    thm finite_subset
    by (auto intro: finite_subset)
qed

axiomatization a::bool and b::bool
  where R1: "a \<Longrightarrow> b"


lemma "a \<Longrightarrow> b"
  by (rule R1)

lemma "\<not>b \<Longrightarrow> \<not>a"
  by (auto intro: R1)


thm finite_subset

  

instantiation test :: card_UNIV begin 
definition "finite_UNIV = Phantom(test) True"
definition "card_UNIV = Phantom(test) 2"
instance 
  apply (intro_classes)
   apply (simp_all add: finite_UNIV_test_def card_UNIV_test_def)
  by (metis ex_new_if_finite finite.emptyI finite_insert insert_iff test.exhaust)
end


(* is it possible to get the original definition of f_vars working? *)
instantiation variable::finite_UNIV 
begin
definition "finite_UNIV = Phantom(variable) False"
lemma "infinite (UNIV::string set)"
  by (rule infinite_UNIV_listI)

lemma UNIV_var_def: "(UNIV::variable set) = variable.Var ` (UNIV::string set)"
  apply (rule UNIV_eq_I)
  subgoal for x
    apply (cases x)
    subgoal for s
      by blast
    done
  done


lemma inf: "infinite (UNIV::variable set)"
  unfolding UNIV_var_def
  find_theorems name: "finite*ran"
  thm finite_imageD
  apply (auto dest: finite_range_imageI)
  apply (drule finite_imageD)
  using inj_def apply blast
  by (simp add: infinite_UNIV_listI)
  find_theorems name: finite_range
instance 
  by (intro_classes; simp_all add: finite_UNIV_variable_def inf)
end

find_theorems name: "String*co"

value "STR ''abc''"

value "STR ''abc'' < STR ''bcd''"

lemma "STR '''' < x"

find_theorems name: "proper_interval*char"
                         
instantiation variable::ord begin
  fun less_eq_variable::"variable \<Rightarrow> variable \<Rightarrow> bool" where
    "less_eq_variable (variable.Var x) (variable.Var y) = (String.implode x \<le> String.implode y)"
  
  fun less_variable::"variable \<Rightarrow> variable \<Rightarrow> bool" where
    "less_variable (variable.Var x) (variable.Var y) = (String.implode x < String.implode y)"
instance proof
qed
end

lemma "String.implode x < String.implode y \<longleftrightarrow> variable.Var x < variable.Var y"
  by simp

lemma "x < y \<longleftrightarrow> variable.Var (literal.explode x) < variable.Var (literal.explode y)"
  by simp

lemma variable_bot: "variable.Var [] \<le> y"
proof -
  have "(0::String.literal) \<le> s" for s
    apply (induction s)
    subgoal for l
      find_theorems name: "less*eq*li"
      unfolding String.less_eq_literal_def
      by (simp add: zero_literal.rep_eq)
    done
  moreover
  have "literal.explode 0 = []" by (rule zero_literal.rep_eq)
  ultimately
  have "\<forall>y. variable.Var [] \<le> variable.Var y"
    by (metis String.implode_explode_eq less_eq_variable.simps)
  thus "variable.Var [] \<le> y"
    by (cases y; auto)
qed

lemma var_le_not_less: "(x::variable) \<le> y \<Longrightarrow> \<not>(y < x)"
  by (metis leD less_eq_variable.elims(2) less_variable.elims(2) variable.inject)

lemma inj_var: "inj variable.Var"
  using inj_def by blast
lemma surj_var: "surj variable.Var"
  unfolding surj_def
  by (rule variable.nchotomy)
lemma bij_var: "bij variable.Var"
  using inj_var surj_var bij_def
  by blast

value "String.implode [CHR 0x00]"

lemma "(x::variable) < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"
  apply (cases x; cases y)
  subgoal for x' y'
    apply (rule ssubst[of x], assumption)
    apply (rule ssubst[of y], assumption)
    quickcheck

lemma "x \<noteq> [] \<Longrightarrow> \<exists>y. y < variable.Var x"
proof -
  assume a: "x \<noteq> []"
  have "variable.Var [] \<le> variable.Var x"
    using variable_bot by blast
  moreover
  have "variable.Var [] \<noteq> variable.Var x"
    using bij_var a by blast
  ultimately
  have "variable.Var [] < variable.Var x"
    quickcheck
qed

instantiation variable::proper_interval begin
  (* To do: redefine considering that the 7th bit cannot be set *)
  fun proper_interval_variable::"variable proper_interval" where
    "proper_interval_variable None None = True"
  | "proper_interval_variable None (Some (variable.Var x)) = (x \<noteq> [])"
  | "proper_interval_variable (Some x) None = True"
  | "proper_interval_variable (Some (variable.Var x)) (Some (variable.Var y)) = 
    (less (variable.Var x) (variable.Var y) \<and> y \<noteq> (x @ [CHR 0x00]))"
instance sorry (* proof
  show "proper_interval (None::variable option) (None::variable option) = True" by simp
  fix x::variable and y::variable
  show "proper_interval None (Some y) = (\<exists>z. z < y)" 
    apply (cases y)
    subgoal for v
      apply (rule ssubst[of y], assumption)
      apply (subst proper_interval_variable.simps(2))
      using variable_bot[THEN var_le_not_less]
      apply (cases v)
       apply blast
      
      
    qed *)
end


instantiation variable::cproper_interval begin
  fun cproper_interval_variable::"variable proper_interval" where
    "cproper_interval_variable None None = True"
  | "cproper_interval_variable None (Some (variable.Var x)) = (x \<noteq> [])"
  | "cproper_interval_variable (Some x) None = True"
  | "cproper_interval_variable (Some x) (Some y) = (less x y \<and> not_adj x y)"
instance sorry (* proof 
  assume "ID CCOMPARE(variable) \<noteq> None"
  assume "finite (UNIV::variable set)"
  fix x::variable and y::variable
  show "class.proper_interval cless (cproper_interval :: variable proper_interval)"
  proof
    fix x::variable and y::variable
    show "cproper_interval None None = True"
  qed
qed *)
end

fun string_chars::"string \<Rightarrow> char set" where
  "string_chars (c#cs) = (
  let cs' = string_chars cs
  in (if (c \<in> cs') then cs' else insert c cs'))"
| "string_chars [] = {}"

definition f_chars::"string formula \<Rightarrow> char set" where
  "f_chars \<phi> = \<Union>(string_chars ` (atoms \<phi>))"

print_derives

derive (eq) ceq instantiated_nf_upd
derive ccompare upd_op instantiated_nf_upd
derive (rbt) set_impl instantiated_nf_upd

(* TODO/FIXME: Code_Char was removed from Isabelle-2018! 
  Check for performance regression of generated code!
*)
export_code
  (* check_plan *)
  nat_of_integer integer_of_nat Inl Inr
  (* predAtm *) Eq predicate Pred Either Var Obj PredDecl BigAnd BigOr
  ast_problem_decs.pddl_all_impl ast_problem_decs.pddl_exists_impl
  formula.Not formula.Bot Effect ast_action_schema.Action_Schema
  map_atom Domain Problem DomainDecls ProbDecls PAction
  valuation f_chars term_val_impl ast_domain.apply_effect_impl (* f_vars \<comment> Need to instantiate a few classes for symbol, but that is difficult *)
  (* term.CONST *) (* term.VAR *) 
  String.explode String.implode ast_domain.non_int_nf_upd_list
  in Scala
  module_name PDDL_Checker_Exported
  file "PDDL_STRIPS_Checker_Exported.scala"

export_code ast_domain.apply_effect_exec in SML module_name ast_domain

(* Usage example from within Isabelle *)
(*
ML_val \<open>
  let
    val prefix="/home/lammich/devel/isabelle/planning/papers/pddl_validator/experiments/results/"

    fun check name =
      (name,@{code parse_check_dpp_impl}
        (file_to_string (prefix ^ name ^ ".dom.pddl"))
        (file_to_string (prefix ^ name ^ ".prob.pddl"))
        (file_to_string (prefix ^ name ^ ".plan")))

  in
    (*check "IPC5_rovers_p03"*)
    check "Test2_rover_untyped_pfile07"
  end
\<close>
*)
end \<comment> \<open>Theory\<close>
