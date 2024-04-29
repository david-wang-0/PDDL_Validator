section \<open>Executable PDDL Checker\<close>
theory PDDL_Checker
imports
  PDDL_Semantics

  Error_Monad_Add
  "HOL.String"

  (*"HOL-Library.Code_Char"     TODO: This might lead to performance loss! CHECK! *)
  "HOL-Library.Code_Target_Nat"

  "HOL-Library.While_Combinator"

  "Containers.Containers"
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
  apply (auto simp: dfs_reachable_invar_def)
  done

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

subsubsection \<open>Of-Type\<close>

definition "of_type_impl G oT T \<equiv> (\<forall>pt\<in>set (primitives oT). dfs_reachable G ((=) pt) (primitives T))"

definition "of_type' G oT T \<equiv> (\<forall>pt\<in>set (primitives oT). dfs_reachable G ((=) pt) (primitives T))"

(* definition "of_type_impl = of_type' STG" -- TODO: simpler
 *)
text \<open>The mapping from variables to types tends to be small, since it 
      is derived from an argument list, so using the default implementation
      of a map as a list is sufficient.\<close>

context ast_domain_decs begin
  
  definition sig_impl::"(predicate, type list) mapping" where
    "sig_impl = Mapping.of_alist (map (\<lambda>PredDecl p n \<Rightarrow> (p,n)) (predicates DD))"
  (* TODO: simplify *)
  lemma sig_impl_correct: "Mapping.lookup sig_impl = sig"
    unfolding sig_impl_def sig_def
    by (rule ext; rule lookup_of_alist)

  text \<open>Implementation of the signatures for functions.\<close>
  definition obj_fun_sig_impl::"(func, (type list \<times> type)) mapping" where
    "obj_fun_sig_impl = Mapping.of_alist (map (\<lambda>ObjFunDecl f ts t \<Rightarrow> (f, (ts, t))) (object_funs DD))"
  
  lemma ofs_impl_correct: "Mapping.lookup obj_fun_sig_impl = obj_fun_sig"
    unfolding obj_fun_sig_impl_def obj_fun_sig_def
    by (rule ext; rule lookup_of_alist)
  
  definition num_fun_sig_impl::"(func, type list) mapping" where
    "num_fun_sig_impl = Mapping.of_alist (map (\<lambda>NumFunDecl f ts \<Rightarrow> (f, ts)) (num_funs DD))"
  
  lemma nfs_impl_correct: "Mapping.lookup num_fun_sig_impl = num_fun_sig"
    unfolding num_fun_sig_impl_def num_fun_sig_def
    by (rule ext; rule lookup_of_alist)

  text \<open>We check whether a single primitive can be reached from any primitive in a set 
      (this set is the supertype).\<close>
  definition "of_type1 pt T \<longleftrightarrow> pt \<in> subtype_rel\<^sup>* `` set (primitives T)"

  lemma of_type_refine1: "of_type oT T \<longleftrightarrow> (\<forall>pt\<in>set (primitives oT). of_type1 pt T)"
    unfolding of_type_def of_type1_def by auto

  text \<open>We declare types and their supertypes. \<open>subtype_edge\<close> is therefore
        the \<close>
  definition "STG \<equiv> (tab_succ (map subtype_edge (types DD)))"
  
  lemma subtype_rel_impl: "subtype_rel = E_of_succ (tab_succ (map subtype_edge (types DD)))"
    by (simp add: tab_succ_correct subtype_rel_def)

  lemma of_type1_impl: "of_type1 pt T \<longleftrightarrow> dfs_reachable (tab_succ (map subtype_edge (types DD))) ((=)pt) (primitives T)"
    by (simp add: subtype_rel_impl of_type1_def dfs_reachable_tab_succ_correct tab_succ_correct)

  lemma of_type_impl_correct: "of_type_impl STG oT T \<longleftrightarrow> of_type oT T"
    unfolding of_type1_impl STG_def of_type_impl_def of_type_refine1 ..


  text \<open>Executable constT\<close>
  definition mp_constT :: "(object, type) mapping" where
    "mp_constT = Mapping.of_alist (consts DD)"

  lemma mp_constT_correct[simp]: "Mapping.lookup mp_constT = constT"
    unfolding mp_constT_def constT_def
    by (rule ext; rule lookup_of_alist)

  
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
  definition ty_term_impl::"('ent \<rightharpoonup> type) \<Rightarrow> 'ent term \<rightharpoonup> type" where
    "ty_term_impl ty_ent \<equiv> (ty_term' (of_type_impl STG) (Mapping.lookup obj_fun_sig_impl) ty_ent)"

  abbreviation is_term_of_type_impl::"('ent \<rightharpoonup> type) \<Rightarrow> 'ent term \<Rightarrow> type \<Rightarrow> bool" where
    "is_term_of_type_impl ty_ent \<equiv> (is_term_of_type' (of_type_impl STG) (Mapping.lookup obj_fun_sig_impl) ty_ent)"

  lemma ty_term_impl_correct: "ty_term_impl ty_ent = ty_term ty_ent"
    unfolding ty_term_impl_def
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
          thm if_cong
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

  context 
    fixes of_type:: "type \<Rightarrow> type \<Rightarrow> bool"
      and ofs:: "func \<rightharpoonup> (type list \<times> type)"
      and nfs:: "func \<rightharpoonup> type list"
      and ty_ent:: "'ent \<rightharpoonup> type"
  begin
    definition "is_of_type'' = is_of_type' of_type ty_ent"

    fun wf_pred'::"predicate \<times> 'ent list \<Rightarrow> bool" where
      "wf_pred' (p,vs) \<longleftrightarrow> (
        case Mapping.lookup sig_impl p of
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

    definition wf_of_arg_r_map'::"func \<Rightarrow> ('ent list \<rightharpoonup> 'ent) \<Rightarrow> bool" where
      "wf_of_arg_r_map' f f' \<equiv> (case ofs f of 
        None \<Rightarrow> False 
      | Some (Ts, T) \<Rightarrow> 
          (\<forall>as \<in> dom f'. list_all2 is_of_type'' as Ts 
          \<and> is_of_type'' (the (f' as)) T))"
  
    definition wf_of_int'::"(func \<rightharpoonup> 'ent list \<rightharpoonup> 'ent) \<Rightarrow> bool" where
      "wf_of_int' ti \<equiv> (\<forall>f \<in> dom ti. wf_of_arg_r_map' f (the (ti f)))"

    definition wf_nf_int_map'::"func \<Rightarrow> ('ent list \<rightharpoonup> rat) \<Rightarrow> bool" where
      "wf_nf_int_map' n f' \<equiv> (case nfs n of 
        None \<Rightarrow> False 
      | Some Ts \<Rightarrow> \<forall>as \<in> dom f'. list_all2 is_of_type'' as Ts)"
  
    definition wf_nf_int'::"(func \<rightharpoonup> 'ent list \<rightharpoonup> rat) \<Rightarrow> bool" where
      "wf_nf_int' ni \<equiv> (\<forall>(f, m) \<in> Map.graph ni. wf_nf_int_map' f m)"
  end

  abbreviation "is_of_type_impl \<equiv> is_of_type'' (of_type_impl STG)"
  
  lemma is_of_type_impl_correct: "is_of_type_impl ty_ent = is_of_type ty_ent"
    unfolding  is_of_type_def is_of_type''_def is_of_type'_def
    using of_type_impl_correct
    by (auto split: option.splits)

  definition "wf_pred_impl \<equiv> wf_pred' (of_type_impl STG)"

  lemma wf_pred_impl_correct: "wf_pred_impl ty_ent = wf_pred ty_ent"
    unfolding wf_pred_impl_def
    apply (rule ext)
    subgoal for x
    apply (cases x)
      subgoal for p vs
        apply (rule ssubst[of x], assumption)
        apply (subst wf_pred'.simps, subst wf_pred.simps)
        by (rule option.case_cong; simp add: sig_impl_correct is_of_type_impl_correct)
      done
    done 
  
  definition "wf_pred_eq_impl = wf_pred_eq' (of_type_impl STG)"
  
  lemma wf_pred_eq_impl_correct: "wf_pred_eq_impl ty_ent = wf_pred_eq ty_ent"
    unfolding wf_pred_eq_impl_def
    apply (intro ext)
    subgoal for x
      by (cases x; simp add: wf_pred_impl_correct[simplified wf_pred_impl_def])
    done
    
    definition "wf_predicate_impl = wf_predicate' (of_type_impl STG)"
                                           
    lemma wf_predicate_impl_correct: "wf_predicate_impl ty_ent = wf_predicate ty_ent"
      unfolding wf_predicate_impl_def
      apply (intro ext)
      subgoal for x
        by (cases x; simp add: wf_pred_impl_correct[simplified wf_pred_impl_def])
      done
  
  definition "wf_num_func_impl = wf_num_func' (of_type_impl STG) (Mapping.lookup num_fun_sig_impl)"
  
  lemma wf_num_func_impl_correct: "wf_num_func_impl ty_ent = wf_num_func ty_ent"
    unfolding wf_num_func_impl_def
    apply (rule ext)
    subgoal for x 
      apply (cases x)
      subgoal for a b
        apply (rule ssubst[of x], assumption)
        apply (subst wf_num_func'.simps, subst wf_num_func.simps)
        by (rule option.case_cong; simp add: nfs_impl_correct is_of_type_impl_correct)
      done
    done
  
  definition "wf_num_fluent_impl = wf_num_fluent' (of_type_impl STG) (Mapping.lookup num_fun_sig_impl)"
  
  lemma wf_num_fluent_impl_correct: "wf_num_fluent_impl ty_ent = wf_num_fluent ty_ent"
    unfolding wf_num_fluent_impl_def
    apply (rule ext)
    subgoal for x
      apply (induction x)
      subgoal by (simp add: wf_num_func_impl_correct[simplified wf_num_func_impl_def])
      subgoal by simp
      by auto
    done
    
  definition "wf_num_comp_impl = wf_num_comp' (of_type_impl STG) (Mapping.lookup num_fun_sig_impl)"
  
  lemma wf_num_comp_impl_correct: "wf_num_comp_impl ty_ent = wf_num_comp ty_ent"
    unfolding wf_num_comp_impl_def
    apply (rule ext)
    subgoal for x
      by (induction x; simp add: wf_num_fluent_impl_correct[simplified wf_num_fluent_impl_def])+
    done
  
  definition "wf_atom_impl = wf_atom' (of_type_impl STG) (Mapping.lookup num_fun_sig_impl)"
  
  lemma wf_atom_impl_correct: "wf_atom_impl ty_ent = wf_atom ty_ent"
    unfolding wf_atom_impl_def
    apply (rule ext)
    subgoal for x 
      by (cases x; simp add: wf_num_comp_impl_correct[simplified wf_num_comp_impl_def]
                        wf_pred_eq_impl_correct[simplified wf_pred_eq_impl_def])
    done

  definition "wf_fmla_impl = wf_fmla' (of_type_impl STG) (Mapping.lookup num_fun_sig_impl)"
  
  lemma wf_fmla_impl_correct: "wf_fmla_impl ty_ent = wf_fmla ty_ent"
    unfolding wf_fmla_impl_def
    apply (rule ext)
    subgoal for x
      apply (induction x)
      subgoal by (simp add: wf_atom_impl_correct[simplified wf_atom_impl_def])
      by auto
    done

  definition "wf_of_upd_impl = wf_of_upd' (of_type_impl STG)"
  
  lemma wf_of_upd_impl_correct: "wf_of_upd_impl ty_ent = wf_of_upd ty_ent"
    unfolding wf_of_upd_impl_def
    apply (rule ext)
    subgoal for x
      apply (cases x)
      subgoal for f as v
        apply (rule ssubst[of x], assumption)
        apply (subst wf_of_upd'.simps, subst wf_of_upd.simps)
        by (rule option.case_cong; simp add: is_of_type_impl_correct)
      done
    done
  
  definition "wf_nf_upd_impl = wf_nf_upd' (of_type_impl STG) (Mapping.lookup num_fun_sig_impl)"
  
  lemma wf_nf_upd_impl_correct: "wf_nf_upd_impl ty_ent = wf_nf_upd ty_ent"
    unfolding wf_nf_upd_impl_def
    apply (rule ext)
    subgoal for x
      apply (cases x)
      subgoal for f op as v
        apply (rule ssubst[of x], assumption)
        apply (subst wf_nf_upd'.simps, subst wf_nf_upd.simps)
        apply (subst wf_num_fluent_impl_correct[simplified wf_num_fluent_impl_def])
        apply (subst nfs_impl_correct)
        apply (subst is_of_type_impl_correct)
        by simp
      done
    done
  
  definition "wf_effect_impl = wf_effect' (of_type_impl STG) (Mapping.lookup num_fun_sig_impl)"
  
  lemma wf_effect_impl_correct: "wf_effect_impl ty_ent = wf_effect ty_ent"
    unfolding wf_effect_impl_def
    apply (rule ext)
    subgoal for x
      apply (cases x)
      by (simp add: wf_predicate_impl_correct[simplified wf_predicate_impl_def]
                        wf_of_upd_impl_correct[simplified wf_of_upd_impl_def]
                        wf_nf_upd_impl_correct[simplified wf_nf_upd_impl_def])
    done
  
  definition "wf_cond_effect_impl = wf_cond_effect' (of_type_impl STG) (Mapping.lookup num_fun_sig_impl)"
  
  lemma wf_cond_effect_impl_correct: "wf_cond_effect_impl ty_ent = wf_cond_effect ty_ent"
    unfolding wf_cond_effect_impl_def
    apply (rule ext)
    subgoal for x
      apply (cases x)
      unfolding wf_cond_effect'_def wf_cond_effect_def 
        wf_fmla_impl_correct[simplified wf_fmla_impl_def]
        wf_effect_impl_correct[simplified wf_effect_impl_def]
      by simp
    done

  definition "wf_cond_effect_list_impl = wf_cond_effect_list' (of_type_impl STG) (Mapping.lookup num_fun_sig_impl)"
  
  lemma wf_cond_effect_list_impl_correct: "wf_cond_effect_list_impl ty_ent = wf_cond_effect_list ty_ent"
    unfolding wf_cond_effect_list_impl_def wf_cond_effect_list_def wf_cond_effect_list'_def
    by (simp add: wf_cond_effect_impl_correct[simplified wf_cond_effect_impl_def])

  definition "wf_of_arg_r_map_impl = wf_of_arg_r_map' (of_type_impl STG) (Mapping.lookup obj_fun_sig_impl)"
  
  lemma wf_of_arg_r_map_impl_correct: "wf_of_arg_r_map_impl ty_ent = wf_of_arg_r_map ty_ent"
    unfolding wf_of_arg_r_map_impl_def
    apply (intro ext)
    subgoal for f f'
      unfolding wf_of_arg_r_map_def wf_of_arg_r_map'_def
       ofs_impl_correct is_of_type_impl_correct
      by auto
    done

  definition "wf_of_int_impl = wf_of_int' (of_type_impl STG) (Mapping.lookup obj_fun_sig_impl)"
  
  lemma wf_of_int_impl_correct: "wf_of_int_impl ty_ent = wf_of_int ty_ent"
    unfolding wf_of_int_impl_def
      wf_of_int'_def wf_of_int_def
      wf_of_arg_r_map_impl_correct[simplified wf_of_arg_r_map_impl_def]
    by simp
  
  definition "wf_nf_int_map_impl = wf_nf_int_map' (of_type_impl STG) (Mapping.lookup num_fun_sig_impl)"

  lemma wf_nf_int_map_impl_correct: "wf_nf_int_map_impl ty_ent = wf_nf_int_map ty_ent"
    unfolding wf_nf_int_map_impl_def
    apply (rule ext)
    subgoal for x
      unfolding wf_nf_int_map'_def wf_nf_int_map_def 
        is_of_type_impl_correct nfs_impl_correct
      by simp
    done

  definition "wf_nf_int_impl = wf_nf_int' (of_type_impl STG) (Mapping.lookup num_fun_sig_impl)"
  
  lemma wf_nf_int_impl_correct: "wf_nf_int_impl ty_ent = wf_nf_int ty_ent"
    unfolding wf_nf_int_impl_def  wf_nf_int'_def wf_nf_int_def
    apply (subst wf_nf_int_map_impl_correct[simplified wf_nf_int_map_impl_def])
    by simp
end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

subsubsection \<open>Well-Formedness\<close>

context ast_problem_decs begin

  text \<open> We start by defining a mapping from objects to types. The container
    framework will generate efficient, red-black tree based code for that
    later. \<close>

  type_synonym objT = "(object, type) mapping"

  definition mp_objT :: "(object, type) mapping" where
    "mp_objT = Mapping.of_alist (consts DD @ objects PD)"

  lemma mp_objT_correct[simp]: "Mapping.lookup mp_objT = objT"
    unfolding mp_objT_def objT_alt
    by transfer (simp add: Map_To_Mapping.map_apply_def)

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
  
  definition "wf_action_schema_impl = wf_action_schema' (of_type_impl STG) (Mapping.lookup obj_fun_sig_impl) (Mapping.lookup num_fun_sig_impl) (Mapping.lookup mp_objT)"
  
  lemma wf_action_schema_impl_correct: "wf_action_schema_impl = wf_action_schema"
    unfolding wf_action_schema_impl_def
    apply (intro ext)
    subgoal for a
      apply (induction a)
      subgoal for n params pre effs
        unfolding wf_action_schema.simps wf_action_schema'.simps
          ty_term_impl_correct[simplified ty_term_impl_def]
          wf_fmla_impl_correct[simplified wf_fmla_impl_def]
          wf_cond_effect_list_impl_correct[simplified wf_cond_effect_list_impl_def]
          mp_objT_correct
        by simp
      done    
    done

    definition "wf_goal' ot ofs nfs = wf_fmla' ot nfs (ty_term' ot ofs (ty_sym Map.empty (Mapping.lookup mp_objT)))"

    definition "wf_goal_impl = wf_goal' (of_type_impl STG) (Mapping.lookup obj_fun_sig_impl) (Mapping.lookup num_fun_sig_impl)"

    lemma wf_goal_impl_correct: "wf_goal_impl = wf_goal"
      unfolding wf_goal_impl_def wf_goal'_def wf_goal_def
        ty_term_impl_correct[simplified ty_term_impl_def]
        wf_fmla_impl_correct[simplified wf_fmla_impl_def]
        mp_objT_correct
      by simp
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

  definition "wf_domain_impl \<equiv> wf_domain' (of_type_impl STG) 
    (Mapping.lookup obj_fun_sig_impl) (Mapping.lookup num_fun_sig_impl) (Mapping.lookup mp_objT)"

  lemma wf_domain_impl_correct: "wf_domain_impl = wf_domain"
    unfolding wf_domain_impl_def wf_domain'_def wf_domain_def
    apply (subst wf_action_schema_impl_correct[simplified wf_action_schema_impl_def])
    by simp
  
  definition wf_world_model'::"(type \<Rightarrow> type \<Rightarrow> bool) 
    \<Rightarrow> (func \<rightharpoonup> (type list \<times> type))
    \<Rightarrow> (func \<rightharpoonup> (type list))
    \<Rightarrow> (object \<rightharpoonup> type) 
    \<Rightarrow> world_model \<Rightarrow> bool" where
    "wf_world_model' ot ofs nfs obT M \<equiv> 
      (\<forall>p \<in> preds M. wf_predicate' ot obT p)
      \<and> wf_of_int' ot ofs obT (of_int M)
      \<and> wf_nf_int' ot nfs obT (nf_int M)"
  
  definition "wf_world_model_impl = 
    wf_world_model' 
      (of_type_impl STG) 
      (Mapping.lookup obj_fun_sig_impl)
      (Mapping.lookup num_fun_sig_impl)
      (Mapping.lookup mp_objT)"
  
  lemma wf_world_model_impl_correct: "wf_world_model_impl = wf_world_model"
    unfolding wf_world_model_impl_def wf_world_model_def wf_world_model'_def
     mp_objT_correct 
     wf_predicate_impl_correct[simplified wf_predicate_impl_def]
     wf_of_int_impl_correct[simplified wf_of_int_impl_def]
     wf_nf_int_impl_correct[simplified wf_nf_int_impl_def]
    by simp

end

context ast_problem
begin

  definition "wf_problem' ot ofs nfs obT\<equiv>
      wf_domain' ot ofs nfs obT
    \<and> wf_goal' ot ofs nfs (goal P)
    \<and> wf_world_model' ot ofs nfs obT (init P)"

definition "wf_problem_impl = 
  wf_problem' 
    (of_type_impl STG) 
    (Mapping.lookup obj_fun_sig_impl) 
    (Mapping.lookup num_fun_sig_impl) 
    (Mapping.lookup mp_objT)"

lemma wf_problem_impl_correct: "wf_problem_impl = wf_problem"
  unfolding wf_problem_impl_def wf_problem'_def wf_problem_def
  wf_domain_impl_correct[simplified wf_domain_impl_def]
  wf_world_model_impl_correct[simplified wf_world_model_impl_def]
  wf_goal_impl_correct[simplified wf_goal_impl_def]
  by blast
end
subsubsection \<open>Implementation of the quantifier macros\<close>

derive ceq variable
derive ccompare variable
derive (rbt) set_impl variable 

(* this syntax also works for Mapping *)

context ast_problem_decs begin

find_theorems name: "pair*inv"

  (* "of_type_impl G oT T \<equiv> (\<forall>pt\<in>set (primitives oT). dfs_reachable G ((=) pt) (primitives T))" *)
  
  (* definition "t_dom_impl G T \<equiv> \<Inter> (dfs_all G (primitives T))" *)

  fun term_atom_vars_impl::"term atom \<Rightarrow> variable set" where
    "term_atom_vars_impl (predAtm p vs) = (foldr (\<lambda>v l. term_vars v \<union> l) vs {})"
  | "term_atom_vars_impl (atom.Eq v1 v2) = term_vars v1 \<union> term_vars v2"

  lemma term_atom_vars_impl_correct': "term_atom_vars_impl a = term_atom_vars a"
  proof (cases a)
    case (predAtm p vs)
    have "x \<in> term_atom_vars_impl (predAtm p vs)" 
      if "x \<in> term_atom_vars (predAtm p vs)"
      for x
      using that
      apply (induction vs)
      unfolding term_atom_vars_def by fastforce+
    moreover 
    have "x \<in> term_atom_vars (predAtm p vs)"
      if "x \<in> term_atom_vars_impl (predAtm p vs)" 
      for x
      using that
      apply (induction vs)
      unfolding term_atom_vars_def by fastforce+
    ultimately
    show ?thesis using predAtm by blast
  next
    case (Eq a b)
    then show ?thesis unfolding term_atom_vars_def by simp
  qed

  primrec fvars_impl::"term atom formula \<Rightarrow> variable set" where
    "fvars_impl (Atom p) = term_atom_vars_impl p" 
  | "fvars_impl Bot = {}"
  | "fvars_impl (Not \<phi>\<^sub>1) = fvars_impl \<phi>\<^sub>1"
  | "fvars_impl (And \<phi>\<^sub>1 \<phi>\<^sub>2) = fvars_impl \<phi>\<^sub>1 \<union> fvars_impl \<phi>\<^sub>2"
  | "fvars_impl (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = fvars_impl \<phi>\<^sub>1 \<union> fvars_impl \<phi>\<^sub>2"
  | "fvars_impl (Imp \<phi>\<^sub>1 \<phi>\<^sub>2) = fvars_impl \<phi>\<^sub>1 \<union> fvars_impl \<phi>\<^sub>2"

  lemma fvars_impl_correct': "fvars_impl \<phi> = fvars \<phi>"
    using term_atom_vars_impl_correct'
    apply (induction \<phi>)
    by auto

  definition t_dom_impl::"type \<Rightarrow> object list" where    
    "t_dom_impl typ = map fst (filter (\<lambda>(c, t). of_type_impl STG t typ) (consts DD @ objects PD))"
  
  lemma t_dom_impl_correct': "t_dom_impl t = t_dom t" 
    unfolding t_dom_def t_dom_impl_def
    using of_type_impl_correct
    by presburger

  definition all_impl::"variable \<Rightarrow> type \<Rightarrow> schematic_formula \<Rightarrow> schematic_formula" where
    "all_impl v t \<phi> \<equiv> (if (v \<notin> fvars_impl \<phi> \<and> (t_dom_impl t \<noteq> [])) then \<phi> else  \<^bold>\<And>(map (\<lambda>c. (map_formula (term_atom_subst v c)) \<phi>) (t_dom_impl t)))"

  definition exists_impl::"variable \<Rightarrow> type \<Rightarrow> schematic_formula \<Rightarrow> schematic_formula" where
    "exists_impl v t \<phi> \<equiv> (if (v \<notin> fvars_impl \<phi> \<and> (t_dom_impl t \<noteq> [])) then \<phi> else \<^bold>\<Or>(map (\<lambda>c. (map_formula (term_atom_subst v c)) \<phi>) (t_dom_impl t)))"

  value "all_impl (Var ''idk'') (Either [''object'']) (Atom (atom.Eq (term.VAR (Var ''idk'')) (term.VAR (Var ''2''))))"

  lemma all_impl_correct': "all_impl v t \<phi> = \<^bold>\<forall>v - t. \<phi>"
    unfolding all_def all_impl_def 
    using t_dom_impl_correct' fvars_impl_correct'
    by presburger

  lemma exists_impl_correct': "exists_impl v t \<phi> = \<^bold>\<exists>v - t. \<phi>"
    unfolding exists_def exists_impl_def
    using t_dom_impl_correct' fvars_impl_correct'
    by presburger

  text \<open>Functions to apply our quantifiers to PDDL quantifiers with argument lists\<close>
  definition pddl_all_impl::"(variable \<times> type) list \<Rightarrow> schematic_formula \<Rightarrow> schematic_formula" where
    "pddl_all_impl ps \<phi> = foldr (\<lambda>(v, t) f. all_impl v t f) (unique_vars ps) \<phi>"

  definition pddl_exists_impl::"(variable \<times> type) list \<Rightarrow> schematic_formula \<Rightarrow> schematic_formula" where
    "pddl_exists_impl ps \<phi> = foldr (\<lambda>(v, t) f. exists_impl v t f) (unique_vars ps) \<phi>"

  lemma pddl_all_impl_correct': "pddl_all_impl ps \<phi> = pddl_all ps \<phi>"
    unfolding pddl_all_def pddl_all_impl_def
    using all_impl_correct'
    by presburger

  lemma pddl_exists_impl_correct': "pddl_exists_impl ps \<phi> = pddl_exists ps \<phi>"
      unfolding pddl_exists_def pddl_exists_impl_def
      using exists_impl_correct'
      by presburger

end


subsubsection \<open>Application of Effects\<close>

context ast_domain begin
  text \<open>We implement the application of an effect by explicit iteration over
    the additions and deletions\<close>
  fun apply_effect_exec
    :: "object ast_effect \<Rightarrow> world_model \<Rightarrow> world_model"
  where
    "apply_effect_exec (Effect a d) s
      = fold (\<lambda>add s. Set.insert add s) a
          (fold (\<lambda>del s. Set.remove del s) d s)"

  lemma apply_effect_exec_refine[simp]:
    "apply_effect_exec (Effect (a) (d)) s
    = apply_effect (Effect (a) (d)) s"
  proof(induction a arbitrary: s)
    case Nil
    then show ?case
    proof(induction d arbitrary: s)
      case Nil
      then show ?case by auto
    next
      case (Cons a d)
      then show ?case
        by (auto simp add: image_def)
    qed
  next
    case (Cons a a)
    then show ?case
    proof(induction d arbitrary: s)
      case Nil
      then show ?case by (auto; metis Set.insert_def sup_assoc insert_iff)
    next
      case (Cons a d)
      then show ?case
        by (auto simp: Un_commute minus_set_fold union_set_fold)
    qed
  qed

  lemmas apply_effect_eq_impl_eq
    = apply_effect_exec_refine[symmetric, unfolded apply_effect_exec.simps]
  
end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

context ast_problem
begin

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
  find_theorems name: "wf*effe"

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
  ast_domain_decs.wf_atom'.simps
  ast_domain_decs.wf_pred_atom'.simps
  ast_domain_decs.wf_fmla'.simps
  ast_domain_decs.wf_fmla_atom1'.simps
  ast_domain_decs.wf_effect'.simps
  ast_domain_decs.wf_domain_decs'_def
  ast_domain_decs.mp_constT_def
  ast_domain_decs.subtype_edge.simps

declare wf_domain_decs_code[code]

lemmas wf_problem_decs_code =
  ast_problem_decs.wf_fact'_def
  ast_problem_decs.wf_fact_def
  ast_problem_decs.wf_goal'.simps
  ast_problem_decs.term_atom_vars_impl.simps
  ast_problem_decs.fvars_impl.simps
  ast_problem_decs.t_dom_impl_def
  ast_problem_decs.unique_vars'.simps
  ast_problem_decs.all_impl_def
  ast_problem_decs.exists_impl_def
  ast_problem_decs.pddl_all_impl_def
  ast_problem_decs.pddl_exists_impl_def
  ast_problem_decs.wf_action_schema'.simps

declare wf_problem_decs_code[code]

lemmas wf_domain_code =
  ast_domain.subst_term.simps
  ast_domain.tsubst.simps
  ast_domain.inst_pre.simps
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
  ast_problem.wf_problem'_def
  ast_problem.is_obj_of_type_alt
  ast_problem.inst_goal.simps 
  ast_problem.wf_plan_action.simps
  (*ast_problem.wf_effect_inst_weak.simps*)
  (*ast_problem.wf_object_def*)
  (*ast_problem.objT_def*)

declare wf_problem_code[code]

thm wf_problem_code

lemmas check_code =
  ast_problem.valid_plan_def
  ast_problem.valid_plan_fromE.simps
  ast_problem.en_exE2_def
  ast_problem.resolve_instantiate.simps
  ast_domain.resolve_action_schema_def
  ast_domain.resolve_action_schemaE_def
  ast_problem.I_def
  ast_domain.instantiate_action_schema.simps
  ast_domain.apply_effect_exec.simps
  (*ast_domain.apply_effect_exec'.simps*)
  ast_domain.apply_effect_eq_impl_eq
  (*ast_domain.apply_atomic.simps*)
  ast_problem.holds_def
  ast_problem_decs.mp_objT_def
  ast_problem.is_obj_of_type_impl_def
  ast_problem_decs.wf_fmla_atom2'_def
  valuation_def
declare check_code[code]

subsubsection \<open>Setup for Containers Framework\<close>

derive ceq predicate atom object formula
derive ccompare predicate atom object formula
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

(* TODO/FIXME: Code_Char was removed from Isabelle-2018! 
  Check for performance regression of generated code!
*)
export_code
  check_plan
  nat_of_integer integer_of_nat Inl Inr
  predAtm Eq predicate Pred Either Var Obj PredDecl BigAnd BigOr
  ast_problem_decs.pddl_all_impl ast_problem_decs.pddl_exists_impl
  formula.Not formula.Bot Effect ast_action_schema.Action_Schema
  map_atom Domain Problem DomainDecls ProbDecls PAction
  term.CONST term.VAR (* I want to export the entire type, but I can only export the constructor because term is already an isabelle keyword. *)
  String.explode String.implode
  in SML
  module_name PDDL_Checker_Exported
  file "PDDL_STRIPS_Checker_Exported.sml"

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
