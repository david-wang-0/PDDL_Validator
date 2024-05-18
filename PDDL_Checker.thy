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
  (ps: "object predicate set")
  (eofi: mp_ofi)
  (enfi: mp_nfi)

definition to_map_map::"('a, ('b, 'c) mapping) mapping \<Rightarrow> 'a \<rightharpoonup> 'b \<rightharpoonup> 'c" where
  "to_map_map = Mapping.lookup o (Mapping.map_values (\<lambda>k v. Mapping.lookup v))"

fun exec_wm_to_wm::"exec_world_model \<Rightarrow> world_model" where
  "exec_wm_to_wm (EWM p oi ni) = World_Model p (to_map_map oi) (to_map_map ni)"

lemma ps_predicates[simp]: "ps M = predicates (exec_wm_to_wm M)"
  by (cases M; simp)

lemma eofi_of_int[simp]: "to_map_map (eofi M) = world_model.of_int (exec_wm_to_wm M)"
  by (cases M; simp)

lemma enfi_nf_int[simp]: "to_map_map (enfi M) = world_model.nf_int (exec_wm_to_wm M)"
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
      by (cases M; simp add: eofi_def to_map_map_def lookup_map_values)
    with None
    show ?thesis by simp
  next
    case (Some a)
    then have 1: "of_int (exec_wm_to_wm M) f = Some (Mapping.lookup a)"
      by (cases M; simp add: eofi_def to_map_map_def  lookup_map_values)
    
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
    then show ?thesis by (cases M; simp add: enfi_def to_map_map_def lookup_map_values)
  next
    case (Some a)
    then have 1: "nf_int (exec_wm_to_wm M) f = Some (Mapping.lookup a)"
      by (cases M; simp add: eofi_def to_map_map_def  lookup_map_values)
    
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
  | "nc_val'(Num_Le x y) = (case (nf_val x, nf_val y) of
      (Some x, Some y)  \<Rightarrow> x \<le> y | _ \<Rightarrow> False)"
  | "nc_val'(Num_Lt x y) = (case (nf_val x, nf_val y) of
      (Some x, Some y)  \<Rightarrow> x < y | _ \<Rightarrow> False)"

fun predicate_inst'::"object term predicate \<Rightarrow> object predicate option" where
  "predicate_inst' (Pred p as) = (let arg_vals = map (\<lambda>t. term_val t) as
        in (if (list_all (\<lambda>x. x \<noteq> None) arg_vals) 
            then Some (Pred p (map the arg_vals)) 
            else None))"
  | "predicate_inst' (predicate.Eq t1 t2) = (case (term_val t1, term_val t2) of
      (Some x, Some y) \<Rightarrow> Some (predicate.Eq x y)
    | _                \<Rightarrow> None)"

end

definition "nc_val_impl M = nc_val' (nf_val_impl M)"

lemma nc_val_impl_correct: "nc_val_impl M x = nc_val (exec_wm_to_wm M) x"
  unfolding nc_val_impl_def
  by (cases x; auto simp: nf_val_impl_correct)

definition "predicate_inst_impl M = predicate_inst' (term_val_impl M)"

lemma predicate_inst_impl_correct: "predicate_inst_impl M x = predicate_inst (exec_wm_to_wm M) x"
  unfolding predicate_inst_impl_def
  by (induction x; auto simp: term_val_impl_correct[THEN ext])

fun predicate_val_impl::"exec_world_model \<Rightarrow> object term predicate \<Rightarrow> bool" where
  "predicate_val_impl M p = (case predicate_inst_impl M p of 
      Some (Pred p as)  \<Rightarrow> (Pred p as) \<in> ps M
    | Some (predicate.Eq x y)     \<Rightarrow> x = y
    | None              \<Rightarrow> False)"

lemma predicate_val_impl_correct: "predicate_val_impl M x = predicate_val (exec_wm_to_wm M) x"
  apply (cases "predicate_inst_impl M x")
  subgoal by (simp add: predicate_inst_impl_correct)
  subgoal for a by (cases a; auto simp: predicate_inst_impl_correct)
  done

fun valuation_impl::"exec_world_model \<Rightarrow> object term atom valuation" where
  "valuation_impl M (PredAtom p) = predicate_val_impl M p"
| "valuation_impl M (NumComp c) = nc_val_impl M c"

lemma valuation_impl_correct: "valuation_impl M x = valuation (exec_wm_to_wm M) x"
  using predicate_val_impl_correct nc_val_impl_correct
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

  text \<open>Refining the declarations of signatures for preds and functions.\<close>
  definition sig'::"(pred, type list) mapping" where
    "sig' = Mapping.of_alist (map (\<lambda>PredDecl p n \<Rightarrow> (p,n)) (preds DD))"

  definition "sig_impl = Mapping.lookup sig'"

  lemma sig_impl_correct: "Mapping.lookup sig' = sig"
    unfolding sig'_def sig_def
    by (rule ext; rule lookup_of_alist)

  text \<open>Implementation of the signatures for functions.\<close>
  definition obj_fun_sig'::"(func, (type list \<times> type)) mapping" where
    "obj_fun_sig' = Mapping.of_alist (map (\<lambda>ObjFunDecl f ts t \<Rightarrow> (f, (ts, t))) (obj_funs DD))"
  
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


  text \<open>It would be nice, if we could remove the ty_ent call in wf_predicate_eq'.
        If we could, we could pass is_term_of_type/is_object_of_type/etc.
        rather than of_type and ty_ent.\<close>
  context 
    fixes of_type:: "type \<Rightarrow> type \<Rightarrow> bool"
      and ofs:: "func \<rightharpoonup> (type list \<times> type)"
      and nfs:: "func \<rightharpoonup> type list"
      and ty_ent:: "'ent \<rightharpoonup> type"
  begin
    abbreviation "is_of_type'' \<equiv> is_of_type' of_type ty_ent"

    fun wf_predicate'::"pred \<times> 'ent list \<Rightarrow> bool" where
      "wf_predicate' (p,vs) \<longleftrightarrow> (
        case Mapping.lookup sig' p of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 is_of_type'' vs Ts)"
 
    fun wf_predicate_eq' :: "'ent predicate \<Rightarrow> bool" where
      "wf_predicate_eq' (Pred p vs) \<longleftrightarrow> wf_predicate' (p,vs)"
    | "wf_predicate_eq' (predicate.Eq a b) \<longleftrightarrow> ty_ent a \<noteq> None \<and> ty_ent b \<noteq> None"

    text \<open>This checks that a pred is well-formed and not an equality.\<close>
    fun wf_pred' :: "'ent predicate \<Rightarrow> bool" where
      "wf_pred' (Pred p vs) \<longleftrightarrow> wf_predicate' (p, vs)"
    | "wf_pred' (predicate.Eq _ _) \<longleftrightarrow> False"

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
    | "wf_num_comp' (Num_Lt a b) = (wf_num_fluent' a \<and> wf_num_fluent' b)"
    | "wf_num_comp' (Num_Le a b) = (wf_num_fluent' a \<and> wf_num_fluent' b)"

    text \<open>Predicate-atoms are well-formed if their arguments match the
      signature, equalities are well-formed if the arguments are valid
      objects (have a type), comparisons are well-formed if the functions
      and terms are well-typed.
    \<close>
    fun wf_atom' :: "'ent atom \<Rightarrow> bool" where
      "wf_atom' (PredAtom p) \<longleftrightarrow> wf_predicate_eq' p"
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
    "wf_nf_upd' (NF_Upd op f as v) = (case nfs f of 
        None \<Rightarrow> False
      | Some Ts \<Rightarrow> 
          list_all2 is_of_type'' as Ts 
        \<and> wf_num_fluent' v
    )"

    text \<open>An effect is well-formed if its constituent parts are well-formed\<close>
    fun wf_effect' where
      "wf_effect' (Effect a d tu nu) \<longleftrightarrow>
          (\<forall>u \<in> set a. wf_pred' u)
        \<and> (\<forall>u \<in> set d. wf_pred' u)
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
abbreviation "wf_predicate_impl \<equiv> wf_predicate' of_type_impl"

  lemma wf_predicate_impl_correct: "wf_predicate_impl ty_ent = wf_predicate ty_ent"
    apply (rule ext)
    subgoal for x
    apply (cases x)
      subgoal for p vs
        apply (rule ssubst[of x], assumption)
        apply (subst wf_predicate'.simps, subst wf_predicate.simps)
        by (rule option.case_cong; simp add: sig_impl_correct is_of_type_impl_correct)
      done
    done 
  
  abbreviation "wf_predicate_eq_impl \<equiv> wf_predicate_eq' of_type_impl"
  
  lemma wf_predicate_eq_impl_correct: "wf_predicate_eq_impl ty_ent = wf_predicate_eq ty_ent"
    apply (intro ext)
    subgoal for x
      by (cases x; simp add: wf_predicate_impl_correct)
    done
    
  abbreviation "wf_pred_impl \<equiv> wf_pred' of_type_impl"
                                           
    lemma wf_pred_impl_correct: "wf_pred_impl ty_ent = wf_pred ty_ent"
      apply (intro ext)
      subgoal for x
        by (cases x; simp add: wf_predicate_impl_correct)
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
      by (cases x; simp add: wf_num_comp_impl_correct wf_predicate_eq_impl_correct)
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
      by (simp add: wf_pred_impl_correct 
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

  abbreviation "wf_goal_impl \<equiv> wf_goal' of_type_impl ofs_impl nfs_impl"

    lemma wf_goal_impl_correct: "wf_goal_impl = wf_goal"
      unfolding wf_goal'_def wf_goal_def
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
    \<and> (\<forall>p \<in> set (init_ps P). wf_pred' ot obT p)
    \<and> (\<forall>a \<in> set (init_ofs P). wf_init_of_a' ot ofs obT a)
    \<and> non_int_assign_list (init_ofs P)
    \<and> (\<forall>a \<in> set (init_nfs P). wf_init_nf_a' ot nfs obT a)
    \<and> non_int_assign_list (init_nfs P)
    \<and> wf_goal' ot ofs nfs (goal P)"

abbreviation "wf_problem_impl \<equiv>
    wf_problem' of_type_impl ofs_impl nfs_impl objT_impl"

  lemma wf_problem_impl_correct: "wf_problem_impl = wf_problem"
    unfolding  wf_problem'_def wf_problem_def
     wf_domain_impl_correct wf_pred_impl_correct
      wf_init_of_a_impl_correct wf_init_nf_a_impl_correct
      wf_goal_impl_correct apply (subst objT_impl_correct)
    ..
end
subsubsection \<open>Implementation of the quantifier macros\<close>



(* this syntax also works for Mapping *)

context ast_problem_decs begin

              
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
  
  fun predicate_vars_impl::"symbol term predicate \<Rightarrow> variable set" where
    "predicate_vars_impl (Pred p as) = fold ((\<union>) o term_vars_impl) as {}"
  | "predicate_vars_impl (predicate.Eq a b) = term_vars_impl a \<union> term_vars_impl b"
  
  lemma predicate_vars_impl_correct: "predicate_vars x = predicate_vars_impl x"
  proof (cases x)
    case [simp]: (Pred p as)
    have "predicate_vars (Pred p as) = \<Union> (term_vars_impl ` (set as))"
      unfolding predicate_vars_def
      using term_vars_impl_correct by simp
    also have "... = fold (\<union>) (map term_vars_impl as) {}"
        by (simp add: SUP_set_fold fold_map)
    finally show ?thesis 
      by (simp add: fold_map)
  next
    case (Eq a b)
    then show ?thesis 
      unfolding predicate_vars_def 
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
| "nc_vars_impl (Num_Le a b) = nf_vars_impl a \<union> nf_vars_impl b"
| "nc_vars_impl (Num_Lt a b) = nf_vars_impl a \<union> nf_vars_impl b"

lemma nc_vars_impl_correct: "nc_vars_impl x = nc_vars x"
  by (induction x; simp add: nc_vars_def nf_vars_def nf_vars_impl_correct)

fun atom_vars_impl::"symbol term atom \<Rightarrow> variable set" where
  "atom_vars_impl (PredAtom p) = predicate_vars_impl p"
| "atom_vars_impl (NumComp nc) = nc_vars_impl nc"

lemma atom_vars_impl_correct: "atom_vars_impl x = atom_vars x"
  unfolding atom_vars_def
proof (induction x)
  case (PredAtom p)
  then show ?case using predicate_vars_impl_correct atom_vars_def predicate_vars_def by simp
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
  fixes predicate_inst::"object term predicate \<rightharpoonup> object predicate"
begin

fun inst_of_upd'::"object term of_upd \<Rightarrow> instantiated_of_upd" where
  "inst_of_upd' (OF_Upd f args r) = (OFU f (map term_val args) (term_val (the r)))"

fun inst_nf_upd'::"object term nf_upd \<Rightarrow> instantiated_nf_upd" where
  "inst_nf_upd' (NF_Upd op f args r) = (
    let args' = map term_val args
    in NFU op f args' (nf_val r))"

fun inst_effect'::" ground_effect \<Rightarrow> fully_instantiated_effect" where
    "inst_effect' (Effect a d tu nu) = (
      Eff (map predicate_inst a) 
          (map predicate_inst d) 
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

definition "inst_effect_impl M \<equiv> inst_effect' (term_val_impl M) (nf_val_impl M) (predicate_inst_impl M)"

lemma inst_effect_impl_correct: "inst_effect_impl M eff = inst_effect (exec_wm_to_wm M) eff"
  unfolding inst_effect_impl_def
  by (cases eff; auto simp:
      inst_nf_upd_impl_correct[simplified inst_nf_upd_impl_def]
      inst_of_upd_impl_correct[simplified inst_of_upd_impl_def]
      predicate_inst_impl_correct)



fun apply_of_upd_impl::"instantiated_of_upd \<Rightarrow> mp_ofi \<Rightarrow> mp_ofi" where
  "apply_of_upd_impl (OFU f as v) oi = (
      let m' = case (Mapping.lookup oi f) of Some m' \<Rightarrow> m' | None \<Rightarrow> Mapping.empty
      in case v of 
        Some v \<Rightarrow> Mapping.update f (Mapping.update (map the as) v m') oi
      | None   \<Rightarrow> Mapping.update f (Mapping.delete (map the as) m') oi
    )"

lemma to_map_map_None: "to_map_map M x = None \<longleftrightarrow> Mapping.lookup M x = None"
  unfolding to_map_map_def
  by (simp add: lookup_map_values)

lemma to_map_map_NoneE: "to_map_map M x = None \<Longrightarrow> Mapping.lookup M x = None"
  using to_map_map_None
  by fastforce

lemma to_map_map_NoneI: "Mapping.lookup M x = None \<Longrightarrow> to_map_map M x = None"
  using to_map_map_None
  by fastforce

lemma to_map_map_SomeI: "Mapping.lookup M x = Some v \<Longrightarrow> to_map_map M x = Some (Mapping.lookup v)"
  unfolding to_map_map_def
  by (metis Mapping.map_values_def comp_apply lookup_map_values option.simps(9))

lemma to_map_map_SomeE: "to_map_map M x = Some (Mapping.lookup v) \<Longrightarrow> Mapping.lookup M x = Some v"
  unfolding to_map_map_def
  by (metis Some_eq_map_option comp_apply lookup_map_values mapping_eqI)

lemma to_map_map_SomeE1: assumes "to_map_map M x = Some v"
  obtains v' where "Mapping.lookup M x = Some v' \<and> v = Mapping.lookup v'"
  using assms
  by (metis Mapping.lookup.abs_eq to_map_map_SomeE)

lemma to_map_map_Some: "to_map_map M x = Some (Mapping.lookup v) \<longleftrightarrow> Mapping.lookup M x = Some v"
  using to_map_map_SomeE to_map_map_SomeI
  by fast

lemma to_map_map_empty: "to_map_map Mapping.empty = Map.empty"
  unfolding to_map_map_def 
  by (metis Mapping.lookup_empty to_map_map_NoneI to_map_map_def)

lemma lookup_inj: "inj Mapping.lookup"
  by (simp add: injI mapping_eqI)

lemma lookup_surj: "surj Mapping.lookup"
  apply (subst surj_def)
  by (metis Mapping.lookup.abs_eq)

lemma lookup_bij: "bij Mapping.lookup"
  using lookup_inj lookup_surj bij_def
  by blast

thm inj_on_def

lemma to_map_map_inj: "inj to_map_map"
proof (rule injI)
  fix x y
  assume a: "to_map_map x = to_map_map y" 
  have "Mapping.lookup x = Mapping.lookup y" 
    by (metis a mapping_eqI not_None_eq to_map_map_Some)
  then show "x = y"
    by (simp add: mapping_eqI)
qed


lemma exec_wm_to_wm_inj: "inj exec_wm_to_wm"
proof (rule injI)
  fix x y
  assume a[simp]: "exec_wm_to_wm x = exec_wm_to_wm y"
  show "x = y"
  proof (cases x; cases y)
    fix ps ps' ofi ofi' nfi nfi'
    assume xy[simp]: "x = EWM ps ofi nfi"
           "y = EWM ps' ofi' nfi'"
    have 1: "exec_wm_to_wm (EWM ps ofi nfi) = exec_wm_to_wm (EWM ps' ofi' nfi')" using a xy by fast
    hence "ps = ps'" by simp
    moreover
    obtain ofi1 ofi'1 where
      ofi1: "ofi1 = to_map_map ofi"
      "ofi'1 = to_map_map ofi'"
      by auto
    hence "ofi1 = ofi'1" using 1 by fastforce
    hence "ofi = ofi'" using to_map_map_inj ofi1 inj_eq by fastforce
    moreover
    obtain nfi1 nfi'1 where
      nfi1: "nfi1 = to_map_map nfi"
      "nfi'1 = to_map_map nfi'"
      by auto
    hence "nfi1 = nfi'1" using 1 by fastforce
    hence "nfi = nfi'" using to_map_map_inj nfi1 inj_eq by fastforce
    ultimately
    show "x = y" by auto
  qed
qed

lemma to_map_map_upd_other: "x \<noteq> k \<Longrightarrow> to_map_map (Mapping.update k v M) x = to_map_map M x"
  unfolding to_map_map_def by (simp add: lookup_map_values)

lemma to_map_map_del_other: "x \<noteq> k \<Longrightarrow> to_map_map (Mapping.delete k M) x = to_map_map M x"
  unfolding to_map_map_def by (simp add: lookup_map_values)

lemma to_map_map_upd: "to_map_map M = M' \<Longrightarrow> to_map_map (Mapping.update k v M) = M'(k \<mapsto> (Mapping.lookup v))"
  apply (rule ext)
  subgoal for x
    apply (cases "x = k")
    subgoal by (simp add: to_map_map_SomeI)
    subgoal by (auto simp: fun_upd_other to_map_map_upd_other)
    done
  done

lemma to_map_map_del: "to_map_map M = M' \<Longrightarrow> to_map_map (Mapping.delete k M) = M'(k := None)"
  apply (rule ext)
  subgoal for x
    by (cases "x = k"; auto simp: to_map_map_NoneI fun_upd_other to_map_map_del_other)
  done

(* To do: clean up using above lemmas *)
lemma apply_of_upd_impl_correct: "to_map_map (apply_of_upd_impl u ofi) = apply_of_upd u (to_map_map ofi)"
proof (rule ext; induction u)
  fix x::func
  and f::func
  and as::"object option list"
  and v::"object option"
  let ?m1 = "to_map_map (apply_of_upd_impl (OFU f as v) ofi)"
  let ?m2 = "apply_of_upd (OFU f as v) (to_map_map ofi)"
  have case_None: "?m1 x = None \<longleftrightarrow> ?m2 x = None"
  proof
    assume "?m1 x = None"
    hence 1: "Mapping.lookup (apply_of_upd_impl (OFU f as v) ofi) x = None"
      by (subst (asm) to_map_map_None)
    hence 2: "f \<noteq> x"
      by (cases "Mapping.lookup ofi f"; cases v; auto)
    show "?m2 x = None" 
      apply (insert 1 2)
      apply (subst apply_of_upd.simps, subst (asm) apply_of_upd_impl.simps)
      apply (subst (3) to_map_map_def)
      by (cases "Mapping.lookup ofi f"; simp add: Let_def lookup_map_values; cases v; simp add: to_map_map_None)  
  next
    assume a: "?m2 x = None"
    hence "f \<noteq> x" 
      by (cases "to_map_map ofi f"; auto)
    with a
    have "to_map_map ofi x = None"
      by (cases "to_map_map ofi f"; auto)
    hence "Mapping.lookup ofi x = None"
      using to_map_map_None by fastforce
    with \<open>f \<noteq> x\<close>
    have "Mapping.lookup (apply_of_upd_impl (OFU f as v) ofi) x = None" 
      apply (subst apply_of_upd_impl.simps)
      apply (cases "Mapping.lookup ofi f"; cases v)
      by auto
    then 
    show "?m1 x = None" by (subst to_map_map_None)
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
        hence "to_map_map ofi f = None"
          by (simp add: to_map_map_None)
        hence 1: "?m2 f = Some (Map.empty ((map the as) := v))"
          by auto
        show ?thesis
        proof (cases v)
          case None
          have "Mapping.lookup (apply_of_upd_impl (OFU f as v) ofi) f = Some Mapping.empty"
            using None \<open>Mapping.lookup ofi f = None\<close>
            by auto
          hence "?m1 f = Some Map.empty"
            using to_map_map_SomeI by fastforce
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
            using to_map_map_SomeI Some by fastforce
          ultimately 
          show ?thesis using m m' \<open>f = x\<close> by simp
        qed
      next
        case (Some a)
        then obtain a' where
         a': "to_map_map ofi f = Some a'"
          "a' = Mapping.lookup a"
          using to_map_map_SomeI by fast
        hence 1: "?m2 f = Some (a' ((map the as) := v))"
          by auto
        show ?thesis
        proof (cases v)
          case None
          have "Mapping.lookup (apply_of_upd_impl (OFU f as v) ofi) f = Some (Mapping.delete (map the as) a)"
            using None \<open>Mapping.lookup ofi f = Some a\<close>
            by auto
          hence 2: "?m1 f = Some (Mapping.lookup (Mapping.delete (map the as) a))"
            using to_map_map_SomeI by fastforce
          
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
            using to_map_map_SomeI by fastforce
          
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
      then have "?m1 x = to_map_map ofi x"
        unfolding to_map_map_def by (simp add: lookup_map_values)
      moreover
      from False
      have "?m2 x = to_map_map ofi x"
        by (cases "to_map_map ofi f"; cases v; auto)
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
    "apply_nf_upd_impl (NFU op n as v) ni = (
      let f' = (case Mapping.lookup ni n of Some f' \<Rightarrow> f' | None \<Rightarrow> Mapping.empty)
      in Mapping.update n (upd_nf_int_impl f' op (map the as) (the (Mapping.lookup f' (map the as))) (the v)) ni)"

fun nf_upd_defined'_impl::"mp_nfi \<Rightarrow> instantiated_nf_upd \<Rightarrow> bool" where
  "nf_upd_defined'_impl _ (NFU Assign _ _ _) = True"
| "nf_upd_defined'_impl ni (NFU _ n args _) = (
    case (Mapping.lookup ni n) of
      Some f' \<Rightarrow> Mapping.lookup f' (map the args) \<noteq> None
    | None \<Rightarrow> False
)"

lemma upd_nf_int_impl_correct: "Mapping.lookup (upd_nf_int_impl m op args old new) = upd_nf_int (Mapping.lookup m) op args old new"
  by (cases op; auto)

lemma apply_nf_upd_impl_correct: "to_map_map (apply_nf_upd_impl u nfi) = apply_nf_upd u (to_map_map nfi)"
proof (rule ext; induction u)
  fix x::func
  and n::func
  and op::upd_op
  and as::"object option list"
  and v::"rat option"
  let ?m1 = "to_map_map (apply_nf_upd_impl (NFU op n as v) nfi)"
  let ?m2 = "apply_nf_upd (NFU op n as v) (to_map_map nfi)"

  have case_None: "?m1 x = None \<longleftrightarrow> ?m2 x = None"
  proof
    assume "?m1 x = None"
    hence 1: "Mapping.lookup (apply_nf_upd_impl (NFU op n as v) nfi) x = None"
      by (simp add: to_map_map_None)
    hence "n \<noteq> x"
      by (cases "Mapping.lookup nfi n"; auto)
    with 1
    have "Mapping.lookup nfi x = None"
      by (cases "Mapping.lookup nfi n"; auto)
    hence "to_map_map nfi x = None" by (simp add: to_map_map_None)
    with 1
    show "?m2 x = None"
      by (auto simp: Let_def)
  next
    assume a: "?m2 x = None"
    hence n: "n \<noteq> x"
      by (cases "to_map_map nfi n"; auto)
    with a
    have "to_map_map nfi x = None"
      by (cases "to_map_map nfi n"; auto)
    with n
    have "Mapping.lookup (apply_nf_upd_impl (NFU op n as v) nfi) x = None"
      by (cases "Mapping.lookup nfi n"; auto elim: to_map_map_NoneE)
    thus "?m1 x = None"
      by (auto intro: to_map_map_NoneI)
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
          using to_map_map_Some by fastforce
        hence "?m1 n = Some (Mapping.lookup (upd_nf_int_impl Mapping.empty op (map the as) (the None) (the v)))"
          by simp
        moreover
        from None
        have "to_map_map nfi n = None" by (rule to_map_map_NoneI)
        hence "?m2 n = Some (upd_nf_int Map.empty op (map the as) (the (Map.empty (map the as))) (the v))"
          by auto
        hence "?m2 n = Some (upd_nf_int (Mapping.lookup Mapping.empty) op (map the as) (the None) (the v))"
          by (simp add: Mapping.empty_def Mapping.lookup.abs_eq)
        ultimately 
        show ?thesis using  upd_nf_int_impl_correct by presburger
      next
        case (Some a)
        hence "?m1 n = Some (Mapping.lookup (upd_nf_int_impl a op (map the as) (the (Mapping.lookup a (map the as))) (the v)))"
          using to_map_map_Some by fastforce
        moreover
        from Some
        have "to_map_map nfi n = Some (Mapping.lookup a)" by (rule to_map_map_SomeI)
        hence "?m2 n = Some (upd_nf_int (Mapping.lookup a) op (map the as) (the (Mapping.lookup a (map the as))) (the v))"
          by (auto simp: Let_def)
        ultimately
        show ?thesis using upd_nf_int_impl_correct by presburger
      qed
      with \<open>n = x\<close> 
      show ?thesis by simp
    next
      case False
      hence "Mapping.lookup (apply_nf_upd_impl (NFU op n as v) nfi) x = Mapping.lookup nfi x"
        by (cases "Mapping.lookup nfi n"; auto)
      hence "?m1 x = to_map_map nfi x" by (simp add: lookup_map_values to_map_map_def)      
      with False
      show ?thesis by (cases "to_map_map nfi n"; auto)
    qed
  qed
qed

lemma apply_of_upd_impl_correct': "to_map_map (fold apply_of_upd_impl upds oi) = fold apply_of_upd upds (to_map_map oi)"
  by (induction upds arbitrary: oi; auto simp: apply_of_upd_impl_correct)

lemma apply_nf_upd_impl_correct': "to_map_map (fold apply_nf_upd_impl upds ni) = fold apply_nf_upd upds (to_map_map ni)"
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
  "apply_conditional_effect_list_impl effs M = fold (inst_apply_conditional_effect_impl M) effs M"

lemma fold_apply_conditional_effect_list_impl_correct:
  "exec_wm_to_wm (fold (inst_apply_conditional_effect_impl eM) effs M)
  = fold (inst_apply_conditional_effect (exec_wm_to_wm eM)) effs (exec_wm_to_wm M)"
  by (induction effs arbitrary: M; simp add: inst_apply_conditional_effect_impl_correct)

lemma apply_conditional_effect_list_impl_correct:
  "exec_wm_to_wm (apply_conditional_effect_list_impl effs M) 
    = apply_conditional_effect_list effs (exec_wm_to_wm M)"
  unfolding apply_conditional_effect_list_def apply_conditional_effect_list_impl_def
  using fold_apply_conditional_effect_list_impl_correct
  by simp
    
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

  fun wf_app_predicate_upd' where
    "wf_app_predicate_upd' None = False"
  | "wf_app_predicate_upd' (Some (predicate.Eq _ _)) = False"
  | "wf_app_predicate_upd' (Some (Pred p as)) = wf_predicate_eq' of_type obT (Pred p as)" 

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
      "wf_app_nf_upd' (NFU op f args v) = (
          list_all is_some args 
        \<and> is_some v \<and> (op = ScaleDown \<longrightarrow> the v \<noteq> (of_rat 0))
        \<and> nf_args_well_typed' f (map the args))"

  fun wf_fully_instantiated_effect' where
    "wf_fully_instantiated_effect' (Eff a d tu nu) \<longleftrightarrow> 
        (\<forall>ae \<in> set a. wf_app_predicate_upd' ae)
      \<and> (\<forall>de \<in> set d. wf_app_predicate_upd' de)
      \<and> (\<forall>u \<in> set tu. wf_app_of_upd' u)     
      \<and> (\<forall>u \<in> set nu. wf_app_nf_upd' u)"

end

abbreviation "wf_app_predicate_upd_impl \<equiv> wf_app_predicate_upd' of_type_impl objT_impl"

lemma wf_app_predicate_upd_impl_correct: "wf_app_predicate_upd_impl x = wf_app_predicate_upd x"
  apply (cases x)
  subgoal by simp
  subgoal for p
    apply (cases p)
    subgoal using wf_predicate_eq_impl_correct[of objT] 
          objT_impl_correct[THEN arg_cong[of _ _ wf_predicate_eq_impl]] by auto
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
      wf_app_predicate_upd_impl_correct wf_app_of_upd_impl_correct wf_app_nf_upd_impl_correct ..

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
    "int_defines_nf_upd_impl _ (NFU Assign _ _ _) = True"
  | "int_defines_nf_upd_impl ni (NFU _ f args _) = (
      case Mapping.lookup ni f of 
        Some f' \<Rightarrow> Mapping.lookup f' (map the args) \<noteq> None
      | None \<Rightarrow> False)"

lemma int_defines_nf_upd_impl_correct: "int_defines_nf_upd_impl nfi upd = int_defines_nf_upd (to_map_map nfi) upd"
  apply (cases upd)
  subgoal for op f args
    apply (cases "Mapping.lookup nfi f")
    subgoal by (frule to_map_map_NoneI; cases op; simp)
    subgoal by (frule to_map_map_SomeI; cases op; simp)
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
  proof (induction as arbitrary: M)
    case Nil
    then show ?case using exec_wm_to_wm_inj
      by (simp add: inj_eq)
  next
    case (Cons a as)
    have "ground_action_path_impl M (a # as) M' = 
      (valid_ground_action a (exec_wm_to_wm M) \<and> 
      ground_action_path_impl (execute_ground_action_impl a M) as M')" 
      using valid_ground_action_impl_correct by simp
    have "valid_ground_action_impl a M = valid_ground_action a (exec_wm_to_wm M)" 
      by (rule valid_ground_action_impl_correct)
    moreover
    have "ground_action_path_impl (execute_ground_action_impl a M) as M' 
     = ground_action_path (execute_ground_action a (exec_wm_to_wm M)) as (exec_wm_to_wm M')"
      using Cons.IH execute_ground_action_impl_correct by simp
    ultimately
    show ?case by simp
  qed

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>


definition "mp_index_by f l \<equiv> Mapping.of_alist (map (\<lambda>x. (f x, x)) l)"

text \<open>Refinement of the resolution and instantiation of action schemas.\<close>
context ast_problem begin

definition mp_res_as::"(name, ast_action_schema) mapping" where
  "mp_res_as = mp_index_by ast_action_schema.name (actions D)"

definition "resolve_action_schema_impl = Mapping.lookup mp_res_as"

lemma resolve_action_schema_impl_correct: "resolve_action_schema_impl x = resolve_action_schema x"
  unfolding resolve_action_schema_impl_def resolve_action_schema_def mp_res_as_def mp_index_by_def index_by_def
  by (simp add: lookup_of_alist)

context
  fixes is_obj_of_type:: "object \<Rightarrow> type \<Rightarrow> bool"
    and res::"name \<rightharpoonup> ast_action_schema"
begin

definition "params_match' params as \<equiv> list_all2 is_obj_of_type as (map snd params)"

definition "action_params_match' a as \<equiv> params_match' (parameters a) as"

fun wf_plan_action'::"plan_action \<Rightarrow> bool" where
  "wf_plan_action' (PAction n as) = (
      case res n of
        None \<Rightarrow> False
      | Some a \<Rightarrow>
          action_params_match' a as
        )"


fun resolve_instantiate'::"plan_action \<Rightarrow> ground_action" where
  "resolve_instantiate' (PAction n as) =
      instantiate_action_schema
        (the (res n))
        as"

definition plan_action_path'::"exec_world_model \<Rightarrow> plan_action list \<Rightarrow> exec_world_model \<Rightarrow> bool" where
  "plan_action_path' M \<pi>s M' = ((\<forall>\<pi> \<in> set \<pi>s. wf_plan_action' \<pi>) 
    \<and> ground_action_path_impl M (map resolve_instantiate' \<pi>s) M')"

definition valid_plan_action'::"plan_action \<Rightarrow> exec_world_model \<Rightarrow> bool" where
  "valid_plan_action' \<pi> M \<equiv> wf_plan_action' \<pi> 
  \<and> valid_ground_action_impl (resolve_instantiate' \<pi>) M"

definition execute_plan_action'::"plan_action \<Rightarrow> exec_world_model \<Rightarrow> exec_world_model" where
  "execute_plan_action' \<pi> M = execute_ground_action_impl (resolve_instantiate' \<pi>) M"

end

term execute_plan_action'
term valid_plan_action'

abbreviation "is_obj_of_type_impl \<equiv> is_of_type' of_type_impl objT_impl"

lemma is_obj_of_type_impl_correct: "is_obj_of_type_impl x = is_of_type objT x"
  unfolding objT_impl_correct is_of_type_impl_correct
  ..

abbreviation "params_match_impl \<equiv> params_match' is_obj_of_type_impl"

lemma params_match_impl_correct: "params_match_impl params args = params_match params args"
  unfolding params_match'_def params_match_def is_obj_of_type_impl_correct
  ..

abbreviation "action_params_match_impl \<equiv> action_params_match' is_obj_of_type_impl"

lemma action_params_match_impl_correct: "action_params_match_impl a as = action_params_match a as"
  unfolding action_params_match'_def action_params_match_def params_match_impl_correct
  ..

abbreviation "wf_plan_action_impl \<equiv> wf_plan_action' is_obj_of_type_impl resolve_action_schema_impl"

lemma wf_plan_action_impl_correct: "wf_plan_action_impl a = wf_plan_action a"
  apply (induction a)
  subgoal for a as
    apply (subst wf_plan_action'.simps)
    apply (subst wf_plan_action.simps)
    apply (subst resolve_action_schema_impl_correct)
    apply (subst action_params_match_impl_correct) 
    .. (* the simplifier does not handle these substitutions well *)
  .

abbreviation "resolve_instantiate_impl \<equiv> resolve_instantiate' resolve_action_schema_impl"

lemma resolve_instantiate_impl_correct: "resolve_instantiate_impl a = resolve_instantiate a"
  by (cases a; simp add: resolve_action_schema_impl_correct)

abbreviation "plan_action_path_impl \<equiv> plan_action_path' is_obj_of_type_impl resolve_action_schema_impl"

lemma plan_action_path_impl_correct: "plan_action_path_impl M as M' = plan_action_path (exec_wm_to_wm M) as (exec_wm_to_wm M')"
  unfolding plan_action_path'_def plan_action_path_def
  by (simp add: wf_plan_action_impl_correct ground_action_path_impl_correct ext[OF resolve_instantiate_impl_correct])

(* There is no consistency in when type environments and functions are passed as parameters
  and when they are coded hard *)
abbreviation valid_plan_action_impl::"plan_action \<Rightarrow> exec_world_model \<Rightarrow> bool" where
  "valid_plan_action_impl \<equiv> valid_plan_action' is_obj_of_type_impl resolve_action_schema_impl"

lemma valid_plan_action_impl_correct: "valid_plan_action_impl \<pi> M = valid_plan_action \<pi> (exec_wm_to_wm M)"
  unfolding valid_plan_action'_def valid_plan_action_def wf_plan_action_impl_correct
    valid_ground_action_impl_correct resolve_instantiate_impl_correct
  ..

abbreviation "execute_plan_action_impl \<equiv> execute_plan_action' resolve_action_schema_impl"

lemma execute_plan_action_impl_correct: "exec_wm_to_wm (execute_plan_action_impl \<pi> M) \<equiv> execute_plan_action \<pi> (exec_wm_to_wm M)"
  unfolding execute_plan_action'_def execute_plan_action_def 
    resolve_instantiate_impl_correct execute_ground_action_impl_correct .
end

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
      (\<forall>p \<in> predicates M. wf_pred' ot obT p)
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
     wf_pred_impl_correct
     wf_of_int_refine_correct[simplified wf_of_int_refine_def]
     wf_nf_int_refine_correct[simplified wf_nf_int_refine_def]
      apply (subst objT_impl_correct)
    .. 
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

text \<open>Our error type is a function from unit to shows. shows encodes a string 
  and its concatenation operation. The error type is a function from unit to 
  shows, because it allws binding \<close>

text \<open>Checks that a pred holds for each element in a list.\<close>
definition check_all_list::"('a \<Rightarrow> bool) \<Rightarrow> 'a list 
  \<Rightarrow> string \<Rightarrow> ('a \<Rightarrow> shows) 
  \<Rightarrow> (unit \<Rightarrow> shows) + _" where 
"check_all_list P l msg msgf \<equiv>
  forallM (\<lambda>x. check (P x) (\<lambda>_::unit. shows msg o shows '': '' o msgf x) ) l 
    <+? snd"


lemma check_all_list_return_iff[return_iff]: "check_all_list P l msg msgf = Inr () \<longleftrightarrow> (\<forall>x\<in>set l. P x)"
  unfolding check_all_list_def
  by (induction l) (auto)

lemma isOK_check_all_list[simp]: "isOK (check_all_list P l msg msgf) \<longleftrightarrow> list_all P l"
  unfolding check_all_list_def
  by (simp add: Ball_set)


definition check_all_list_index::"('a \<Rightarrow> bool) \<Rightarrow> 'a list
  \<Rightarrow> (nat \<Rightarrow> shows) \<Rightarrow> ('a \<Rightarrow> shows) 
  \<Rightarrow> (unit \<Rightarrow> shows) + _" where
  "check_all_list_index P l msgf1 msgf2 = 
    (forallM_index 
      (\<lambda>x n. check (P x) (\<lambda>_::unit. msgf1 n o shows '': '' o msgf2 x)) 
      l <+? snd)" (* Cannot prove when this returns, since forallM_index_aux is hidden *)


text \<open>Functions to allow printing of instances of these types\<close>
derive "show" pred func upd_op object "term" formula 

instantiation predicate::("show") "show" begin
fun shows_prec_predicate::"nat \<Rightarrow> 'a predicate \<Rightarrow> shows" where
  "shows_prec_predicate n (predicate.Eq a b) = shows a o shows  b"
| "shows_prec_predicate n (predicate.Pred p xs) = shows ''Pred '' o shows p o shows '' '' o shows_list xs"

definition shows_list_predicate :: "'a predicate list \<Rightarrow> shows" where
  "shows_list_predicate xs = showsp_list shows_prec 0 xs"

lemma shows_prec_predicate_append: fixes n::nat and p::"'a predicate" and r::string and s::string
  shows "shows_prec n p (r @ s) = shows_prec n p r @ s" 
  by (induction p; simp add: shows_list_append shows_prec_append)
instance proof
  fix n::nat and p::"'a predicate" and r::string and s::string
  show "shows_prec n p (r @ s) = shows_prec n p r @ s" 
  by (rule shows_prec_predicate_append)
next
  fix xs::"'a predicate list" and r::string and s::string
  show "shows_list xs (r @ s) = shows_list xs r @ s"
    unfolding shows_list_predicate_def
    by (induction xs; auto intro: showsp_list_append simp: shows_prec_predicate_append)
qed                                      
end

instantiation num_fluent::("show") "show" begin
fun shows_prec_num_fluent::"nat \<Rightarrow> 'a num_fluent \<Rightarrow> shows" where
  "shows_prec_num_fluent n (NFun f as) = shows ''NFun '' o shows f o shows '' '' o shows_list as"
| "shows_prec_num_fluent n (Add a b) = shows ''Add '' o shows_prec_num_fluent n a o shows '' '' o shows_prec_num_fluent n b"
| "shows_prec_num_fluent n (Sub a b) = shows ''Sub '' o shows_prec_num_fluent n a o shows '' '' o shows_prec_num_fluent n b"
| "shows_prec_num_fluent n (Mult a b) = shows ''Mult '' o shows_prec_num_fluent n a o shows '' '' o shows_prec_num_fluent n b"
| "shows_prec_num_fluent n (Div a b) = shows ''Div '' o shows_prec_num_fluent n a o shows '' '' o shows_prec_num_fluent n b"
| "shows_prec_num_fluent n (Num x) = shows ''Num '' o shows '' '' o shows x"

definition shows_list_num_fluent::"'a num_fluent list \<Rightarrow> shows" where
  "shows_list_num_fluent xs = showsp_list shows_prec 0 xs"

lemma shows_prec_num_fluent_append: fixes n::nat and nf::"'a num_fluent" and r::string and s::string
  shows "shows_prec n nf (r @ s) = shows_prec n nf r @ s" 
  by (induction nf arbitrary: r s; auto simp: shows_list_append shows_prec_append)
instance 
  apply standard
  subgoal by (auto simp: shows_prec_num_fluent_append)
  subgoal for xs by (induction xs; auto simp: shows_list_num_fluent_def shows_prec_num_fluent_append intro: showsp_list_append)
  done
end

instantiation num_comp::("show") "show" begin
fun shows_prec_num_comp::"nat \<Rightarrow> 'a num_comp \<Rightarrow> shows" where
  "shows_prec_num_comp n (Num_Eq a b) = shows ''Num_Eq '' o shows a o shows b"
| "shows_prec_num_comp n (Num_Lt a b) = shows ''Num_Lt '' o shows a o shows b"
| "shows_prec_num_comp n (Num_Le a b) = shows ''Num_Le '' o shows a o shows b"

definition shows_list_num_comp::"'a num_comp list \<Rightarrow> shows" where
  "shows_list_num_comp xs = showsp_list shows_prec 0 xs"

lemma shows_prec_num_comp_append: fixes n::nat and nc::"'a num_comp" and r::string and s::string
  shows "shows_prec n nc (r @ s) = shows_prec n nc r @ s"
  by (cases nc; auto simp: shows_list_append shows_prec_append)
instance
  apply standard
  subgoal by (auto simp: shows_prec_num_comp_append)
  subgoal for xs by (induction xs; auto simp: shows_list_num_comp_def shows_prec_num_comp_append intro: showsp_list_append)
  done
end

instantiation atom::("show") "show" begin
fun shows_prec_atom::"nat \<Rightarrow> 'a atom \<Rightarrow> shows" where
  "shows_prec_atom n (PredAtom p) = shows ''PredAtom '' o shows p"
| "shows_prec_atom n (NumComp nc) = shows ''NumComp '' o shows nc"

definition shows_list_atom::"'a atom list \<Rightarrow> shows" where
  "shows_list_atom xs = showsp_list shows_prec 0 xs"

lemma shows_prec_atom_append: fixes n::nat and a::"'a atom" and r::string and s::string
  shows "shows_prec n a (r @ s) = shows_prec n a r @ s"
  by (cases a; auto simp: shows_list_append shows_prec_append)

instance 
  apply standard
  subgoal by (auto simp: shows_prec_atom_append)
  subgoal for xs by (induction xs; auto simp: shows_list_atom_def shows_prec_atom_append intro: showsp_list_append)
  done
end

instantiation of_upd::("show") "show" begin
fun shows_prec_of_upd::"nat \<Rightarrow> 'a of_upd \<Rightarrow> shows" where
  "shows_prec_of_upd n (OF_Upd f as v) = shows ''OF_Upd '' o shows f o shows as o shows v"

definition shows_list_of_upd :: "'a of_upd list \<Rightarrow> shows" where
  "shows_list_of_upd xs = showsp_list shows_prec 0 xs"

lemma shows_prec_of_upd_append: fixes n::nat and u::"'a of_upd" and r::string and s::string
  shows "shows_prec n u (r @ s) = shows_prec n u r @ s"
  by (cases u; auto simp: shows_list_append shows_prec_append)
instance 
  apply standard
  subgoal by (auto simp: shows_prec_of_upd_append)
  subgoal for xs by (induction xs; auto simp: shows_list_of_upd_def shows_prec_of_upd_append intro: showsp_list_append)
  done
end


instantiation nf_upd::("show") "show" begin
fun shows_prec_nf_upd::"nat \<Rightarrow> 'a nf_upd \<Rightarrow> shows" where
  "shows_prec_nf_upd n (NF_Upd op f as v) = shows ''NF_Upd '' o shows f o shows op o shows as o shows v"

definition shows_list_nf_upd :: "'a nf_upd list \<Rightarrow> shows" where
  "shows_list_nf_upd xs = showsp_list shows_prec 0 xs"

lemma shows_prec_nf_upd_append: fixes n::nat and u::"'a nf_upd" and r::string and s::string
  shows "shows_prec n u (r @ s) = shows_prec n u r @ s"
  by (cases u; auto simp: shows_list_append shows_prec_append)
instance 
  apply standard
  subgoal by (auto simp: shows_prec_nf_upd_append)
  subgoal for xs by (induction xs; auto simp: shows_list_nf_upd_def shows_prec_nf_upd_append intro: showsp_list_append)
  done
end

instantiation ast_effect::("show") "show" begin
fun shows_prec_ast_effect::"nat \<Rightarrow> 'a ast_effect \<Rightarrow> shows" where
  "shows_prec_ast_effect n (Effect a d ou nu) = shows ''Effect '' o shows a o shows d o shows ou o shows nu"

definition shows_list_ast_effect :: "'a ast_effect list \<Rightarrow> shows" where
  "shows_list_ast_effect xs = showsp_list shows_prec 0 xs"

lemma shows_prec_ast_effect_append: fixes n::nat and eff::"'a ast_effect" and r::string and s::string
  shows "shows_prec n eff (r @ s) = shows_prec n eff r @ s"
  by (cases eff; auto simp: shows_list_append shows_prec_append)
instance 
  apply standard
  subgoal by (auto simp: shows_prec_ast_effect_append)
  subgoal for xs by (induction xs; auto simp: shows_list_ast_effect_def shows_prec_ast_effect_append intro: showsp_list_append)
  done
end

context ast_problem begin


  text \<open>We define a function to determine whether a formula holds in
    a world model\<close>

  text \<open>We have to be able to output every possible error message which
    may arise during execution. \<close>

  text \<open>The first refinement, therefore, must check each conditional effect
    in the list.\<close>

definition ex_conditional_effect_list::"(ground_formula \<times> ground_effect) list \<Rightarrow>
  world_model \<Rightarrow> _+unit" where
"ex_conditional_effect_list effs M \<equiv> undefined "

definition ex_ground_action:: "ground_action \<Rightarrow> world_model \<Rightarrow> _+unit" where
  "ex_ground_action \<equiv>  undefined"

  text \<open>The first refinement summarizes the enabledness check and the execution
    of the action. Moreover, we implement the precondition evaluation by our
     holds function. This way, we can eliminate redundant resolving
     and instantiation of the action.
  \<close>

  definition "resolve_action_schemaE n \<equiv>
    lift_opt
      (resolve_action_schema_impl n)
      (ERR (shows ''No such action schema '' o shows n))"
                                            
lemma resolve_action_schemaE_return_iff[return_iff]:
  "(resolve_action_schemaE n = Inr s) \<longleftrightarrow> (resolve_action_schema_impl n = Some s)"
  unfolding resolve_action_schemaE_def 
  by (rule return_iff)

  (* check non-interference *)
  definition en_exE :: "plan_action \<Rightarrow> exec_world_model \<Rightarrow> _+exec_world_model" where
    "en_exE \<equiv> \<lambda>(PAction n args) \<Rightarrow> \<lambda>s. do {
      a \<leftarrow> resolve_action_schemaE n;
      check (action_params_match_impl a args) (ERRS ''Parameter mismatch'');
      let ai = instantiate_action_schema a args;
      check (wf_fmla_impl (ty_term_impl objT_impl) (precondition ai)) (ERRS ''Precondition not well-formed'');
      check_all_list (wf_cond_effect_impl (ty_term_impl objT_impl)) (effects ai) (''Conditional effect not well-formed'') shows;
      check (valuation_impl s \<Turnstile> (precondition ai)) (ERRS ''Precondition not satisfied'');
      check_all_list (wf_inst_cond_effect_impl s) (effects ai) (''Conditional effect cannot be instantiated correctly'') shows;
      check_all_list (well_inst_cond_effect_impl s s) (effects ai) (''Conditional effect cannot be instantiated correctly'') shows;
      check (non_int_cond_eff_list_impl s (effects ai)) (ERRS ''Effects interfere'');
      Error_Monad.return (apply_conditional_effect_list_impl (effects ai) s)
    }"
  thm wf_ground_action_impl_def


  term "check (action_params_match a args) (ERRS ''Parameter mismatch'')"
  term "\<lambda>x. do {x; check (action_params_match a args) (ERRS ''Parameter mismatch'')}"
  (* here we check that an effect is well formed and we execute it *)

  text \<open>Justification of implementation.\<close>
  lemma (in wf_ast_problem) en_exE_return_iff[return_iff]:
    shows "en_exE a s = Inr s'
      \<longleftrightarrow> valid_plan_action_impl a s \<and> s' = execute_plan_action_impl a s"
    by (cases a; auto
        split: option.splits
        simp: en_exE_def valid_plan_action'_def valid_ground_action_impl_def 
          ground_action_enabled_impl_def valid_effects_impl_def 
          well_inst_cond_effect_list_impl_def wf_inst_cond_effect_list_impl_def
          wf_cond_effect_list'_def wf_ground_action_impl_def execute_plan_action'_def
          execute_ground_action_impl_def return_iff)

  text \<open>Now, we eliminate the well-formedness check for ground actions, because \<close>
  
  definition en_exE2
    :: "plan_action \<Rightarrow> exec_world_model \<Rightarrow> _+exec_world_model"
  where
    "en_exE2 \<equiv> \<lambda>(PAction n args) \<Rightarrow> \<lambda>s. do {
      a \<leftarrow> resolve_action_schemaE n;
      check (action_params_match_impl a args) (ERRS ''Parameter mismatch'');
      let ai = instantiate_action_schema a args;
      check (valuation_impl s \<Turnstile> (precondition ai)) (ERRS ''Precondition not satisfied'');
      check_all_list (wf_inst_cond_effect_impl s) (effects ai) (''Conditional effect cannot be instantiated correctly'') shows;
      check_all_list (well_inst_cond_effect_impl s s) (effects ai) (''Conditional effect cannot be instantiated correctly'') shows;
      check (non_int_cond_eff_list_impl s (effects ai)) (ERRS ''Effects interfere'');
      Error_Monad.return (apply_conditional_effect_list_impl (effects ai) s)
    }"

  find_theorems name: "resolve*w"

lemmas wf_instantiate_action_schema_impl =
  wf_instantiate_action_schema[simplified 
    sym[OF action_params_match_impl_correct]
    sym[OF wf_action_schema_impl_correct]
    sym[OF wf_ground_action_impl_correct]
      ]

lemmas (in wf_ast_problem) resolve_action_wf_impl  =
  resolve_action_wf[simplified 
    sym[OF wf_action_schema_impl_correct]
    sym[OF resolve_action_schema_impl_correct]
      ]

lemma (in wf_ast_problem) en_exE2_return_iff[return_iff]:
  shows "en_exE2 a s = Inr s' \<longleftrightarrow> valid_plan_action_impl a s \<and> s' = execute_plan_action_impl a s"
  unfolding en_exE2_def
  apply (induction a)
  subgoal for n as
    apply (simp add: return_iff)
    apply (rule iffI)
     apply (erule exE)
    apply (erule conjE)+
    subgoal for action_schema
      unfolding valid_plan_action'_def valid_ground_action_impl_def
      apply (rule conjI)
       apply (subst wf_plan_action'.simps)
       apply simp
      apply (rule conjI)
         apply (drule resolve_action_wf_impl, rule wf_instantiate_action_schema_impl; assumption)
       apply (simp add: ground_action_enabled_impl_def valid_effects_impl_def well_inst_cond_effect_list_impl_def wf_inst_cond_effect_list_impl_def)
      by (simp add: execute_plan_action'_def execute_ground_action_impl_def)
    apply (cases "resolve_action_schema_impl n") 
    subgoal by (auto simp: valid_plan_action'_def)
    subgoal by (auto simp:  valid_plan_action'_def
       valid_ground_action_impl_def valid_effects_impl_def
       ground_action_enabled_impl_def wf_inst_cond_effect_list_impl_def
       well_inst_cond_effect_list_impl_def execute_plan_action'_def
       execute_ground_action_impl_def)
   done
  done

lemma "(if True then [] else [x]) = []"
  thm if_split
  apply (split if_split)
  by simp

lemma "(case Some x of None \<Rightarrow> [] | Some y \<Rightarrow> [y]) = [x]"
  thm option.splits
  apply (split option.splits)
  by simp

lemma return_idk:
  assumes "\<And>R. m = Inr R ==> f R = Inr R"
  shows "Error_Monad.bind m f \<bind> g = m \<bind> g"
  using assms
  by (cases m; auto)

text \<open>Justification of refinement\<close>
text \<open>We know that the problem is well-formed, because our executable check is equivalent to 
      the abstract check. Therefore, we can use the assumption\<close>
lemma (in wf_ast_problem) wf_en_exE2_eq:
  shows "en_exE2 pa s = en_exE pa s"
proof (induction pa)
  case (PAction n as)
  show ?case
  proof (cases "en_exE2 (PAction n as) s")
    case ret_val: (Inl l)
    then show ?thesis 
    proof (cases "resolve_action_schemaE n")
      case (Inl a)
      then show ?thesis unfolding en_exE_def en_exE2_def plan_action.case
        by auto
    next
      case action_schema: (Inr a)
      with ret_val obtain ai where
        ai: "ai = instantiate_action_schema a as"
        and do:
        "do {check (action_params_match_impl a as) (ERRS ''Parameter mismatch'');
          check (valuation_impl s \<Turnstile> (precondition ai)) (ERRS ''Precondition not satisfied'');
          check_all_list (wf_inst_cond_effect_impl s) (effects ai) (''Conditional effect cannot be instantiated correctly'') shows;
          check_all_list (well_inst_cond_effect_impl s s) (effects ai) (''Conditional effect cannot be instantiated correctly'') shows;
          check (non_int_cond_eff_list_impl s (effects ai)) (ERRS ''Effects interfere'');
          Error_Monad.return (apply_conditional_effect_list_impl (effects ai) s)} = Inl l"
        unfolding en_exE2_def plan_action.case
        by (auto simp: Let_def)
      from this(2)[simplified Error_Monad.bind_assoc] this(2)
      show ?thesis 
      proof (cases "action_params_match_impl a as")
        case True
        from action_schema 
        have "wf_action_schema_impl a" using resolve_action_schemaE_return_iff resolve_action_wf_impl by simp
        with True ai
        have "wf_ground_action_impl ai" using wf_instantiate_action_schema_impl by blast
        hence "wf_fmla_impl (ty_term_impl objT_impl) (precondition ai)"
              "list_all (wf_cond_effect_impl (ty_term_impl objT_impl)) (effects ai)" 
          unfolding wf_ground_action_impl_def wf_cond_effect_list'_def by simp+
        hence "\<forall>x. do { Inr x;
                check (wf_fmla_impl (ty_term_impl objT_impl) (precondition ai)) (ERRS ''Precondition not well-formed'');
                check_all_list (wf_cond_effect_impl (ty_term_impl objT_impl)) (effects ai) (''Conditional effect not well-formed'') shows}
            = Inr ()" 
          by (auto split: error_monad_bind_split simp: check_all_list_return_iff Ball_set)
        hence "en_exE (PAction n as) s = Inl l" 
          unfolding en_exE_def plan_action.case 
          using ai do action_schema
          by (auto simp: Let_def)
        with ret_val
        show ?thesis by simp
      next
        case False
        then show ?thesis 
          unfolding en_exE_def en_exE2_def plan_action.case
          by (simp add: action_schema)
      qed
    qed
  next
    case (Inr r)
    hence "valid_plan_action_impl (PAction n as) s \<and> r = execute_plan_action_impl (PAction n as) s" using en_exE2_return_iff by simp
    hence "en_exE (PAction n as) s = Inr r" using en_exE_return_iff by simp
    with Inr
    show ?thesis by simp
  qed
qed
  
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
        simp: valid_plan_from_def plan_action_path_def valid_plan_action_def
        simp: execute_ground_action_def execute_plan_action_def)
  qed

  text \<open>Next we re-implement the function with our efficient datatypes
    from the container framework.\<close>
  fun valid_plan_from2::"exec_world_model \<Rightarrow> plan \<Rightarrow> bool" where
    "valid_plan_from2 s [] \<longleftrightarrow> valuation_impl s \<Turnstile> (inst_goal (goal P))"
  | "valid_plan_from2 s (\<pi>#\<pi>s) \<longleftrightarrow> valid_plan_action_impl \<pi> s 
      \<and> (valid_plan_from2 (execute_plan_action_impl \<pi> s) \<pi>s)"

  lemma valid_plan_from2_refine: "valid_plan_from2 s \<pi>s = valid_plan_from1 (exec_wm_to_wm s) \<pi>s"
    by (induction \<pi>s arbitrary: s; simp add: ext[OF valuation_impl_correct] valid_plan_action_impl_correct execute_plan_action_impl_correct)

  text \<open>Next, we use our efficient combined enabledness check and execution
    function, and transfer the implementation to use the error monad: \<close>
  fun valid_plan_fromE
    :: "nat \<Rightarrow> exec_world_model \<Rightarrow> plan \<Rightarrow> (unit \<Rightarrow> shows) + unit"
  where
    "valid_plan_fromE si s []
      = check (valuation_impl s \<Turnstile> (inst_goal (goal P))) (ERRS ''Postcondition does not hold'')"
  | "valid_plan_fromE si s (\<pi>#\<pi>s) = do {
        s \<leftarrow> en_exE2 \<pi> s
          <+? (\<lambda>e _. shows ''at step '' o shows si o shows '': '' o e ());
        valid_plan_fromE (si+1) s \<pi>s
      }"

lemma (in wf_ast_problem) valid_plan_fromE_return_iff':
  "valid_plan_fromE n s \<pi>s = Inr () \<longleftrightarrow> valid_plan_from2 s \<pi>s"
  apply (induction \<pi>s arbitrary: n s)
   apply (simp add: check_return_iff)
  by (simp add: bind_return_iff en_exE2_return_iff)

lemma (in wf_ast_problem) valid_plan_fromE_return_iff[return_iff]:
  shows "valid_plan_fromE n s \<pi>s = Inr () \<longleftrightarrow> valid_plan_from (exec_wm_to_wm s) \<pi>s"
  by (simp add: valid_plan_from1_refine 
      valid_plan_fromE_return_iff'
      valid_plan_from2_refine)

end

context ast_problem begin
fun add_init_int_impl::"(func \<times> 'b list \<times> 'c)
  \<Rightarrow> (func, ('b list, 'c) mapping) mapping
  \<Rightarrow> (func, ('b list, 'c) mapping) mapping" where
"add_init_int_impl (f, as, v) fun_int = (
  case (Mapping.lookup fun_int f) of
    Some fun_int' \<Rightarrow> (Mapping.update f (Mapping.update as v fun_int') fun_int)
  | None          \<Rightarrow> (Mapping.update f (Mapping.update as v Mapping.empty) fun_int)
)"

lemma add_init_int_impl_correct: "to_map_map (add_init_int_impl i fi) = add_init_int i (to_map_map fi)"
proof (induction i)
  case (fields f as v)
  have a: "map_option Mapping.lookup (Mapping.lookup (add_init_int_impl (f, as, v) fi) f')
    = add_init_int (f, as, v) (to_map_map fi) f'" for f'
  proof (cases "Mapping.lookup (add_init_int_impl (f, as, v) fi) f'")
    case None
    from None
    have "map_option Mapping.lookup (Mapping.lookup (add_init_int_impl (f, as, v) fi) f') = None"
      by simp
    moreover
    from None 
    have "f \<noteq> f'" by (auto split: option.splits)
    with None
    have "Mapping.lookup fi f' = None" 
      by (cases "Mapping.lookup fi f"; simp)
    from this[simplified sym[OF to_map_map_None]] \<open>f \<noteq> f'\<close>
    have "add_init_int (f, as, v) (to_map_map fi) f' = None"
      by (cases "to_map_map fi f"; auto)
    ultimately
    show ?thesis by simp
  next
    case (Some a)
    show ?thesis
    proof (cases "f = f'")
      case True
      have "map_option Mapping.lookup (Mapping.lookup (add_init_int_impl (f, as, v) fi) f) 
        = add_init_int (f, as, v) (to_map_map fi) f"
      proof (cases "Mapping.lookup fi f")
        case None
        hence "map_option Mapping.lookup (Mapping.lookup (add_init_int_impl (f, as, v) fi) f) = Some [as \<mapsto> v]"
          by auto
        moreover
        from None
        have "to_map_map fi f = None" using to_map_map_None by fastforce
        hence "add_init_int (f, as, v) (to_map_map fi) f = Some [as \<mapsto> v]"
          by simp
        ultimately
        show ?thesis by simp
      next
        case (Some a)
        hence "map_option Mapping.lookup (Mapping.lookup (add_init_int_impl (f, as, v) fi) f)
          = Some (Mapping.lookup (Mapping.update as v a))" by simp
        moreover
        from Some
        have "to_map_map fi f = Some (Mapping.lookup a)" by (rule to_map_map_SomeI)
        hence "add_init_int (f, as, v) (to_map_map fi) f = Some ((Mapping.lookup a)(as \<mapsto> v))" by simp
        ultimately
        show ?thesis by force
      qed
      with True
      show ?thesis by simp
    next
      case False
      hence "Mapping.lookup (add_init_int_impl (f, as, v) fi) f' = Mapping.lookup fi f'"
        by (cases "Mapping.lookup fi f"; auto)
      hence "map_option Mapping.lookup (Mapping.lookup (add_init_int_impl (f, as, v) fi) f') 
        = map_option Mapping.lookup (Mapping.lookup fi f')" by simp
      also have "... = to_map_map fi f'" unfolding to_map_map_def
        by (simp add: lookup_map_values)
      finally show ?thesis using False by (cases "to_map_map fi f"; auto)
    qed
  qed
  have b: "(Mapping.lookup \<circ>\<circ> Mapping.map_values) (\<lambda>k. Mapping.lookup) mp x = 
    map_option Mapping.lookup (Mapping.lookup mp x)" for mp x
    by (simp add: lookup_map_values)
  show ?case unfolding to_map_map_def a[THEN ext] b[THEN ext] by simp
qed


lemma add_init_int_impl_fold_correct: 
  "to_map_map (fold add_init_int_impl xs m) = fold add_init_int xs (to_map_map m)"
  apply (induction xs arbitrary: m)
   apply simp
  using add_init_int_impl_correct
  by (metis List.fold_simps(2))
  

definition ofi_impl::"mp_ofi" where
  "ofi_impl = fold add_init_int_impl (init_ofs P) Mapping.empty"

lemma ofi_impl_correct: "to_map_map ofi_impl = ofi"
  unfolding ofi_impl_def ofi_def
  apply (subst add_init_int_impl_fold_correct)
  apply (subst to_map_map_empty)
  ..

definition nfi_impl::"mp_nfi" where
  "nfi_impl = fold add_init_int_impl (init_nfs P) Mapping.empty"

lemma nfi_impl_correct: "to_map_map nfi_impl = nfi"
  unfolding nfi_impl_def nfi_def
  apply (subst add_init_int_impl_fold_correct)
  apply (subst to_map_map_empty)
  ..

definition I_impl::"exec_world_model" where
  "I_impl = EWM (set (init_ps P)) ofi_impl nfi_impl"

lemma I_impl_correct: "exec_wm_to_wm I_impl = I"
  unfolding I_impl_def I_def
  using nfi_impl_correct ofi_impl_correct by simp
end

subsection \<open>Executable Plan Checker\<close>
text \<open>We obtain the main plan checker by combining the well-formedness check
  and executability check. \<close>


definition "check_wf_types DD \<equiv> do {
  check_all_list (\<lambda>(_,t). t=''object'' \<or> t\<in>fst`set (types DD)) (types DD) ''Undeclared supertype'' (shows o snd)
}"

(* To do: implement check for types which output all errors *)


lemma check_wf_types_return_iff[return_iff]: "check_wf_types DD = Inr () \<longleftrightarrow> ast_domain_decs.wf_types DD"
  unfolding ast_domain_decs.wf_types_def check_wf_types_def
  by (force simp: return_iff)


definition "check_wf_domain_decs DD \<equiv> do {
  check_wf_types DD;
  check (distinct (map (pred_decl.predicate) (preds DD))) (ERRS ''Duplicate pred declaration'');
  check (distinct (map OFName (obj_funs DD) @ map NFName (num_funs DD))) (ERRS ''Duplicate function declaration'');
  check_all_list (ast_domain_decs.wf_pred_decl DD) (preds DD) ''Malformed pred declaration'' (shows o pred.name o pred_decl.predicate);
  check (distinct (map fst (consts DD))) (ERRS  ''Duplicate constant declaration'');
  check (\<forall>(n,T)\<in>set (consts DD). ast_domain_decs.wf_type DD T) (ERRS ''Malformed type'')
}"

lemma check_wf_domain_decs_return_iff[return_iff]:
  "check_wf_domain_decs DD = Inr () \<longleftrightarrow> ast_domain_decs.wf_domain_decs DD"
proof -
  interpret ast_domain_decs DD .
  show ?thesis
    unfolding check_wf_domain_decs_def wf_domain_decs_def
    by (auto simp: check_wf_types_return_iff Ball_set check_return_iff)
qed


definition "prepend_err_msg msg e \<equiv> \<lambda>_::unit. shows msg o shows '': '' o e ()"


definition "check_wf_problem_decs PD \<equiv> do {
  let DD = ast_problem_decs.domain_decs PD;
  check_wf_domain_decs DD <+? prepend_err_msg ''Domain declarations not well-formed'';
  check (distinct (map fst (objects PD) @ map fst (consts DD))) (ERRS ''Duplicate object declaration'');
  check ((\<forall>(n,T)\<in>set (objects PD). ast_domain_decs.wf_type DD T)) (ERRS ''Malformed type'')
}"

lemma check_wf_problem_decs_return_iff[return_iff]:
  "check_wf_problem_decs PD = Inr () \<longleftrightarrow> ast_problem_decs.wf_problem_decs PD"
proof -
  interpret ast_problem_decs PD .
  show ?thesis
    unfolding check_wf_problem_decs_def wf_problem_decs_def
    by (auto simp: return_iff)
qed

(* Why do we need a well-formed domain? *)
term ast_problem_decs.wf_action_schema'
(* We check that the domain is well-formed *)
definition "check_wf_domain D \<equiv> do {
  let PD = ast_domain.problem_decs D;
  let DD = ast_problem_decs.domain_decs PD;
  
  check_wf_problem_decs PD <+? prepend_err_msg ''Declarations from problem not well-formed'';
  check (distinct (map ast_action_schema.name (actions D))) (ERRS ''Duplicate action name'');
  check_all_list (ast_problem_decs.wf_action_schema_impl PD) (actions D) ''Malformed action'' (shows o ast_action_schema.name)
}"


term "Error_Monad.bind"

term "shows o ast_action_schema.name"

lemma check_wf_domain_return_iff':
  "check_wf_domain D = Inr x \<longleftrightarrow> ast_domain.wf_domain_impl D"
proof -
  interpret ast_domain D .
  show ?thesis
    unfolding check_wf_domain_def wf_domain'_def
    by (auto simp: return_iff)
qed

lemma check_wf_domain_return_iff[return_iff]:
  "check_wf_domain D = Inr x \<longleftrightarrow> ast_domain.wf_domain D"
  apply (subst check_wf_domain_return_iff')
  apply (subst ast_domain.wf_domain_impl_correct)
  ..

definition "check_wf_problem P \<equiv> do {
  let D = ast_problem.domain P;
  let PD = ast_domain.problem_decs D;
  let DD = ast_problem_decs.domain_decs PD;
  
  check_wf_domain D <+? prepend_err_msg ''Domain not well-formed'';
  check_all_list (ast_domain_decs.wf_pred_impl DD (ast_problem_decs.objT_impl PD)) (init_ps P) ''Predicate not well-formed'' shows;
  check_all_list (ast_problem.wf_init_of_a_impl P) (init_ofs P) ''Malformed initial assignment to object function'' shows;
  check (ast_problem.non_int_assign_list (init_ofs P)) (ERRS ''Initial function assignments interfere'');
  check_all_list (ast_problem.wf_init_nf_a_impl P) (init_nfs P) ''Malformed initial assignment to numeric function'' shows;
  check (ast_problem.non_int_assign_list (init_nfs P)) (ERRS ''Initial function assignments interfere'');
  check (ast_problem_decs.wf_goal_impl PD (goal P)) (ERRS ''Malformed goal formula'')
}"

lemma check_wf_problem_return_iff':
  "check_wf_problem P = Inr () \<longleftrightarrow> ast_problem.wf_problem_impl P"
proof -
  interpret ast_problem P .
  show ?thesis
    unfolding check_wf_problem_def wf_problem'_def
    by (auto simp: check_wf_domain_return_iff' return_iff Ball_set)
qed


lemma check_wf_problem_return_iff[return_iff]:
  "check_wf_problem P = Inr () \<longleftrightarrow> ast_problem.wf_problem P"
  apply (subst check_wf_problem_return_iff')
  apply (subst ast_problem.wf_problem_impl_correct)
  ..

(* To do: implement executable plan checker *)

definition "check_plan P \<pi>s \<equiv> do {
  let D = ast_problem.domain P;
  let PD = ast_domain.problem_decs D;
  let DD = ast_problem_decs.domain_decs PD;
  let stg=ast_domain_decs.STG DD;
  let conT = ast_domain_decs.mp_constT DD;
  let mp = ast_problem_decs.mp_objT PD;
  let init = ast_problem.I_impl P;
  check_wf_problem P;
  ast_problem.valid_plan_fromE P 0 init \<pi>s
}"

(* valid_plan_fromE should be as efficient as possible *)
(* after checking that the problem is valid, we can just pass the 
    necessary components of the problem to valid_plan_fromE *)

(* the correctness of valid_plan_fromE is relative to valid_plan_from, which
  needs (what?) *)

term ast_problem.valid_plan_from
theorem check_plan_return_iff': "check_plan P \<pi>s = Inr () 
  \<longleftrightarrow> ast_problem.wf_problem_impl P \<and> ast_problem.valid_plan_from2 P (ast_problem.I_impl P) \<pi>s"
  unfolding check_plan_def
  by (auto simp: check_wf_problem_return_iff' ast_problem.wf_problem_impl_correct wf_ast_problem.valid_plan_fromE_return_iff' wf_ast_problem_def)

  text \<open>Correctness theorem of the plan checker: It returns @{term "Inr ()"}
  if and only if the problem is well-formed and the plan is valid.
\<close>
theorem check_plan_return_iff[return_iff]: "check_plan P \<pi>s = Inr ()
  \<longleftrightarrow> ast_problem.wf_problem P \<and> ast_problem.valid_plan P \<pi>s"
proof -
  interpret ast_problem P .
  thm return_iff
  show ?thesis
    by (simp add: check_plan_return_iff' 
        ast_problem.valid_plan_from2_refine 
        ast_problem.valid_plan_from1_refine
        wf_problem_impl_correct I_impl_correct 
        valid_plan_def)
qed

subsubsection \<open>TODO\<close>
context ast_problem_decs
begin

definition "object_function_names = set (map OFName (obj_funs DD))"

definition "numeric_function_names = set (map NFName (num_funs DD))"

lemma (in wf_problem_decs) f_exclusively_numeric_or_object: 
  "f \<notin> numeric_function_names \<or> f \<notin> object_function_names"
proof (cases "f \<in> numeric_function_names")
  case True
  then show ?thesis unfolding numeric_function_names_def object_function_names_def
    using wf_problem_decs unfolding wf_problem_decs_def wf_domain_decs_def
    by auto
next
  case False
  then show ?thesis by simp
qed

definition is_obj_fun::"func \<Rightarrow> bool" where
  "is_obj_fun f \<equiv> f \<in> object_function_names"

(* To do: 
  - Better error message for assignment/update to undefined functions? 
  - Currently handled implicitly? Disambiguation could be implemented in a manner
      that always returns a result. Well-formedness checks then catch the error.
  - Should be done before.
*)


fun combine_effects::"'a ast_effect \<Rightarrow> 'a ast_effect \<Rightarrow> 'a ast_effect" where
  "combine_effects (Effect a d ou nu) (Effect a' d' ou' nu') = Effect (a @ a') (d @ d') (ou @ ou') (nu @ nu')"

term "string map"

fun combine_conditional_effects::"('a formula \<times> 'a ast_effect) 
  \<Rightarrow> ('a formula \<times> 'a ast_effect) 
  \<Rightarrow> ('a formula \<times> 'a ast_effect) list" where
  "combine_conditional_effects (pre, eff) (pre', eff') = (
    if (pre = pre') 
    then
      [(pre, combine_effects eff eff')]
    else 
      [(pre, eff), (pre', eff')])"

term Mapping.combine_with_key

(*
  Mapping.combine_with_key

  1. Group effects by precondition
    1a. Sort effects by precondition
      1a1. Define an order on effects
        1a1a. Define an order on formulas
        1a1b. Lexicographic order on products
    1b. fold ('a, 'b) list into ('a, 'b list) list
  2. map fold ('a, 'b list) list into ('a, 'b) list

*)
(* This is highly inefficient *)

definition compact_conditional_effect_list::"('a formula \<times> 'a ast_effect) list
  \<Rightarrow> ('a formula \<times> 'a ast_effect) list" where
  "compact_conditional_effect_list xs = (
    Mapping.entries (foldr (\<lambda>(pre, eff) mp. Mapping.combine_with_key (Mapping.update pre eff Mapping.empty) mp) xs Mapping.empty)
)"
  
end 

find_theorems name: "Mapping*rep"

value "Mapping.lookup (Mapping.update (1::nat) (0::nat) Mapping.empty) 1"

term "set [0]"

find_theorems name: "Mapping*abs"

lemma "inj (mapping.rep)"
  by (meson injI rep_inject)

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
  ast_domain_decs.wf_pred_decl.simps
  ast_domain_decs.STG_def
  ast_domain_decs.is_of_type'_def
  ast_domain_decs.wf_atom'.simps
  ast_domain_decs.wf_fmla'.simps
  ast_domain_decs.wf_effect'.simps
  ast_domain_decs.mp_constT_def
  ast_domain_decs.subtype_edge.simps
  ast_domain_decs.of_type_impl_def
  ast_domain_decs.ty_term'.simps
  ast_domain_decs.ofs_impl_def
  ast_domain_decs.nfs_impl_def
  ast_domain_decs.wf_cond_effect'_def
  ast_domain_decs.wf_cond_effect_list'_def
  ast_domain_decs.wf_num_comp'.simps 
  ast_domain_decs.wf_predicate_eq.simps
  ast_domain_decs.is_term_of_type'.simps
  ast_domain_decs.wf_num_fluent'.simps 
  ast_domain_decs.wf_pred'.simps 
  ast_domain_decs.obj_fun_sig'_def 
  ast_domain_decs.num_fun_sig'_def 
  ast_domain_decs.wf_predicate_eq'.simps 
  ast_domain_decs.wf_of_upd'.simps 
  ast_domain_decs.wf_nf_upd'.simps
  ast_domain_decs.obj_fun_sig_def
  ast_domain_decs.wf_num_func'.simps 
  ast_domain_decs.wf_predicate'.simps
  ast_domain_decs.sig'_def

declare wf_domain_decs_code[code]

lemmas wf_problem_decs_code =
  ast_problem_decs.wf_goal'_def
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
  ast_problem_decs.predicate_vars_impl.simps
  ast_problem_decs.nc_vars_impl.simps
  ast_problem_decs.term_vars_impl.simps 
  ast_problem_decs.nf_vars_impl.simps
  ast_problem_decs.mp_objT_def
  ast_problem_decs.objT_impl_def
  ast_problem_decs.is_obj_fun_def
  ast_problem_decs.object_function_names_def

declare wf_problem_decs_code[code]

lemmas wf_domain_code =
  ast_problem.resolve_action_schemaE_def
  ast_problem.action_params_match'_def
  ast_problem.add_init_int_impl.simps
  ast_problem_decs.inst_sym.simps

declare wf_domain_code[code]

find_theorems name: "ast_problem*all"

lemmas wf_problem_code =
  ast_problem.wf_problem'_def
  ast_problem.wf_plan_action.simps
  ast_problem.non_int_assign_list.simps
  ast_problem.valid_plan_fromE.simps
  ast_problem.wf_init_of_a'.simps
  ast_problem.wf_init_nf_a'.simps
  ast_problem.non_int_fun_assign.simps
  ast_problem.ofi_impl_def
  ast_problem.nfi_impl_def

declare wf_problem_code[code]


lemmas check_code =
  ast_domain.inst_of_upd.simps
  ast_domain.upd_nf_int.simps
  ast_domain.apply_nf_upd.simps
  ast_domain.apply_of_upd_impl.simps
  ast_domain.upd_nf_int_impl.simps
  ast_domain.apply_nf_upd_impl.simps
  ast_domain.apply_effect_impl.simps
  ast_domain.non_int_nf_upds.simps
  ast_domain.non_int_nf_upd_list_def
  ast_domain.apply_conditional_effect_list_impl_def
  ast_domain.well_inst_cond_effect_impl_def
  ast_domain.non_int_cond_eff_list_impl_def
  ast_domain.wf_inst_cond_effect_impl_def
  ast_problem.en_exE2_def
  ast_problem.resolve_instantiate.simps
  ast_domain.resolve_action_schema_def
  ast_problem.I_def
  ast_domain.instantiate_action_schema.simps
  ast_domain.inst_apply_conditional_effect_impl_def
  ast_domain.wf_fully_instantiated_effect'.simps
  ast_problem.resolve_action_schema_impl_def
  ast_problem_decs.subst_sym_with_obj.simps
  ast_domain.non_int_cond_effs_impl_def
  ast_domain.well_inst_effect_impl_def
  ast_domain.inst_effect_impl_def
  ast_problem.params_match'_def
  ast_domain.inst_apply_effect_impl_def
  ast_domain.wf_app_predicate_upd'.simps
  ast_domain.of_upd_rv_corr_impl_def
  ast_domain.nf_upd_defined_impl_def
  ast_domain.non_int_effs_def
  ast_domain.wf_app_of_upd'.simps
  ast_domain.wf_app_nf_upd'.simps
  ast_domain.inst_effect'.simps
  ast_problem.mp_res_as_def
  ast_domain.int_defines_nf_upd_impl.simps
  ast_domain.non_int_of_upd_lists_def
  ast_domain.non_int_nf_upd_lists_def
  ast_domain.nf_args_well_typed'_def
  ast_domain.of_upd_rv_corr'.simps
  ast_domain.inst_of_upd_impl_def
  ast_domain.inst_nf_upd_impl_def
  ast_domain.inst_of_upd'.simps
  ast_domain.inst_nf_upd'.simps
  ast_domain.is_some.simps
  ast_domain.non_int_of_upd_list_def 
  ast_domain.valid_ret_val_inst.simps
  ast_domain.non_int_of_upds.simps
  f_vars_def
  ast_problem.inst_goal.simps 
  ast_problem.I_impl_def
  ast_problem_decs.inst_term.simps
  ast_problem_decs.mp_objT_def

declare check_code[code]


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

value "10::int"

value "00005.4::rat"

find_theorems name: "Enum"

value "(CHR ''1'')"


print_syntax 

find_consts name: "_constify"

fun digit_from_char::"char \<Rightarrow> nat" where
  "digit_from_char (CHR ''0'') = 0"
| "digit_from_char (CHR ''1'') = 1"
| "digit_from_char (CHR ''2'') = 2"
| "digit_from_char (CHR ''3'') = 3"
| "digit_from_char (CHR ''4'') = 4"
| "digit_from_char (CHR ''5'') = 5"
| "digit_from_char (CHR ''6'') = 6"
| "digit_from_char (CHR ''7'') = 7"
| "digit_from_char (CHR ''8'') = 8"
| "digit_from_char (CHR ''9'') = 9"

fun nat_from_string'::"string \<Rightarrow> nat" where
  "nat_from_string' [] = 0"
| "nat_from_string' (x#xs) = digit_from_char x + nat_from_string' xs"

fun nfs1::"string \<Rightarrow> nat \<Rightarrow> nat" where
  "nfs1 [] acc = acc"
| "nfs1 (x#xs) acc = nfs1 xs (10 * acc + digit_from_char x)"

definition nat_from_string::"string \<Rightarrow> nat" where
  "nat_from_string s \<equiv> nfs1 s 0"

fun int_from_string::"string \<Rightarrow> int" where
  "int_from_string (CHR ''-'' # n) = - (nat_from_string n)" 
| "int_from_string n = nat_from_string n"

definition pos_int_from_string::"string \<Rightarrow> int" where
  "pos_int_from_string = nat_from_string"

fun wf_digit::"char \<Rightarrow> bool" where
  "wf_digit (CHR ''0'') = True"
| "wf_digit (CHR ''1'') = True"
| "wf_digit (CHR ''2'') = True"
| "wf_digit (CHR ''3'') = True"
| "wf_digit (CHR ''4'') = True"
| "wf_digit (CHR ''5'') = True"
| "wf_digit (CHR ''6'') = True"
| "wf_digit (CHR ''7'') = True"
| "wf_digit (CHR ''8'') = True"
| "wf_digit (CHR ''9'') = True"
| "wf_digit _ = False"

fun wf_int::"string \<Rightarrow> bool" where
  "wf_int (CHR ''-'' # s) = list_all wf_digit s"
| "wf_int s = list_all wf_digit s"

definition "wf_dec = list_all wf_digit"

fun reverse'::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "reverse' [] acc = acc"
| "reverse' (x#xs) acc = reverse' xs (x#acc)"

definition "reverse xs \<equiv> reverse' xs []"

fun trim'::"string \<Rightarrow> string" where
  "trim' (CHR ''0'' # s) = s"
| "trim' s = s"

definition "trim \<equiv> reverse o trim' o reverse"

definition rat_from_strings'::"string \<Rightarrow> string \<Rightarrow> rat" where
  "rat_from_strings' i d =  (
  let
    td = trim d;
    l = length td
  in 
    Fract ((pos_int_from_string i) * (10 ^ l)) (pos_int_from_string td))"

fun rat_from_strings::"string \<Rightarrow> string option \<Rightarrow> rat" where
  "rat_from_strings i None = rat_from_strings' i ''''"
| "rat_from_strings i (Some d) = rat_from_strings' i d"

(* TODO: prove correct *)
definition mult_list::"'a num_fluent list \<Rightarrow> 'a num_fluent" where
  "mult_list l = foldr Mult l (Num 1)"

definition add_list::"'a num_fluent list \<Rightarrow> 'a num_fluent" where
  "add_list l = foldr Add l (Num 0)"

subsubsection \<open>Setup for Containers Framework\<close>
derive (eq) ceq rat pred func variable object symbol "term" num_fluent num_comp 
  predicate atom formula ast_effect instantiated_nf_upd instantiated_of_upd 
derive (linorder) compare rat 
derive ccompare rat func pred variable object "term" symbol upd_op predicate num_fluent num_comp 
  atom formula of_upd nf_upd ast_effect instantiated_of_upd instantiated_nf_upd
derive (no) cenum variable
derive (rbt) set_impl rat func variable object "term" atom predicate formula instantiated_nf_upd
  of_upd nf_upd ast_effect instantiated_of_upd
derive (rbt) mapping_impl func object pred

print_derives

(* TODO/FIXME: Code_Char was removed from Isabelle-2018! 
  Check for performance regression of generated code!
*)
export_code
  nat_of_integer integer_of_nat Inl Inr 
  Predicate Function
  Either Variable Object Var Const Ent Fun PredDecl BigAnd BigOr mult_list add_list
  ObjFunDecl NumFunDecl NFun Num_Eq PDDL_Semantics.Eq PDDL_Semantics.PredAtom
  OF_Upd NF_Upd Assign
  ast_problem_decs.is_obj_fun
  ast_problem_decs.pddl_all_impl ast_problem_decs.pddl_exists_impl
  formula.Bot Effect ast_action_schema.Action_Schema
  map_atom Domain Problem DomainDecls ProbDecls PAction
  valuation term_val_impl ast_domain.apply_effect_impl
  check_all_list check_wf_domain check_plan rat_from_strings
  String.explode String.implode ast_domain.non_int_nf_upd_list check_all_list_index
  in SML
  module_name PDDL_Checker_Exported
  file "PDDL_Checker_Exported.sml"


(* 
export_code ast_domain.apply_effect_exec in SML module_name ast_domain *)

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
