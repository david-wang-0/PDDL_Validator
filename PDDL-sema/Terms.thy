theory Terms
  imports AST1
begin

type_synonym 'sym function_interpretation = "'sym term \<rightharpoonup> 'sym term"

fun subterms::"'a term \<Rightarrow> 'a term set" where
  "subterms (Sym x) = {Sym x}"
| "subterms (Fun f as) = insert (Fun f as) (\<Union> (subterms ` (set as)))"

lemma term_in_subterms: "x \<in> subterms x"
  by (cases x) auto

lemma args_in_subterms: "set as \<subseteq> subterms (Fun f as)"
  using term_in_subterms by auto
  
inductive nf_fi::"'a function_interpretation \<Rightarrow> bool"
      and nf_term::"'a function_interpretation \<Rightarrow> 'a term \<Rightarrow> bool" where
  "\<lbrakk>\<not>(\<exists>obj. Sym obj \<in> dom fi); 
      \<forall>(l, r) \<in> Map.graph fi. \<exists>f as. Fun f as = l \<and> list_all (nf_term fi) as \<and> nf_term fi r\<rbrakk> 
    \<Longrightarrow> nf_fi fi"
| "nf_fi fi \<Longrightarrow> nf_term fi (Sym s)"
| "\<lbrakk>nf_fi fi; list_all (nf_term fi) as; fi (Fun f as) = None\<rbrakk> 
    \<Longrightarrow> nf_term fi (Fun f as)"

lemma nf_subterms:
  "nf_term fi x \<longleftrightarrow> (\<forall>t \<in> subterms x. nf_term fi t)"
proof (induction x)
  case (Sym x)
  then show ?case by auto
next
  case (Fun f as)
  show ?case 
  proof (rule iffI)
    assume a: "nf_term fi (Fun f as)"
    hence "list_all (nf_term fi) as"
      apply (cases rule: nf_term.cases)
      by auto
    from this[simplified list_all_iff]
    have "\<forall>a \<in> set as. \<forall>t \<in> subterms a. nf_term fi t" 
      using Fun.IH by blast
    hence "\<forall>t \<in> \<Union> (subterms ` (set as)). nf_term fi t" by simp
    with a
    show "\<forall>t\<in>subterms (Fun f as). nf_term fi t" by simp
  next
    assume "\<forall>t\<in>subterms (Fun f as). nf_term fi t"
    thus "nf_term fi (Fun f as)" by simp
  qed
qed

locale term_eq =
  fixes fi::"'sym function_interpretation"
begin
    
  inductive reduce::"'sym term \<Rightarrow> 'sym term \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>t" 55)where
      refl: "t \<rightarrow>\<^sub>t t"
    | step: "(t1, t2) \<in> Map.graph fi \<Longrightarrow> t1 \<rightarrow>\<^sub>t t2"
    | app: "list_all2 (\<rightarrow>\<^sub>t) as as' \<Longrightarrow> (Fun f as) \<rightarrow>\<^sub>t (Fun f as')"

  inductive_cases reduce_appE: "(Fun f as) \<rightarrow>\<^sub>t (Fun f as')"
  
  inductive_cases reduce_funE: "(Fun f as) \<rightarrow>\<^sub>t t"

  definition term_eq::"'sym term \<Rightarrow> 'sym term \<Rightarrow> bool" (infix "=\<^sub>t" 55) where
    "term_eq \<equiv> equivclp (\<rightarrow>\<^sub>t)"

  lemma reduce_refl: "(\<rightarrow>\<^sub>t)\<^sup>=\<^sup>= = (\<rightarrow>\<^sub>t)"
    by (blast intro: refl)
  
  lemma reduce_rtrancl_is_trancl: "(\<rightarrow>\<^sub>t)\<^sup>*\<^sup>* = (\<rightarrow>\<^sub>t)\<^sup>+\<^sup>+"
    apply (rule ext)+
    subgoal by (auto simp: Nitpick.rtranclp_unfold intro: refl)
    done
  
  find_theorems "?a = ?b \<Longrightarrow> (?a \<Longrightarrow> ?b)"

  lemma reduce_rtranclp_induct': 
    assumes "reduce\<^sup>*\<^sup>* x y" 
      "\<And>a b. reduce a b \<Longrightarrow> P a b" 
      "\<And>a b c. reduce\<^sup>+\<^sup>+ a b \<Longrightarrow> P a b \<Longrightarrow> reduce b c \<Longrightarrow> P a c" 
    shows "P x y"
    using assms(1)[simplified reduce_rtrancl_is_trancl]
    apply (induction rule: tranclp.induct)
    using assms(2,3) by auto

lemmas reduce_rtranclp_induct = reduce_rtranclp_induct'[rotated, OF reduce.induct, rotated 5]
thm rtranclp_induct[OF reduce.induct]
end
  
locale decidable_eq = term_eq fi 
  for fi::"'sym term \<Rightarrow> 'sym term option" +
  assumes nf: "nf_fi fi"
begin
  
  fun normalise_term::"'sym term \<Rightarrow> 'sym term" where
    "normalise_term (Sym s) = (Sym s)"
  | "normalise_term (Fun f as) = (
      let as' = map normalise_term as 
      in (case (fi (Fun f as')) of
        Some t  \<Rightarrow> t
      | None    \<Rightarrow> (Fun f as')
      )
    )"

  definition decidable_eq::"'sym term \<Rightarrow> 'sym term \<Rightarrow> bool" where
    "decidable_eq a b \<equiv> (normalise_term a) = (normalise_term b)"

  lemma nf_cannot_reduce': 
    assumes "nf_term fi t"
    shows "t \<notin> dom fi"
  proof (cases t)
    case (Sym s)
    with nf
    show "t \<notin> dom fi" 
      apply (cases rule: nf_fi.cases)
      by simp
  next
    case (Fun f as)
    with assms(1)
    show ?thesis 
      apply (cases rule: nf_term.cases)
      by auto
  qed

  lemma nf_term_not_fst: "\<not>((x, y) \<in> Map.graph fi \<and> nf_term fi x)"
    apply (rule notI)
    apply (erule conjE)
    apply (drule graph_domD)
    apply (subst (asm) fst_conv)
    apply (drule nf_cannot_reduce')
    by simp


  thm rtranclp_induct
  find_theorems name: "rtranclp"
lemma list_all2_tranclp: "list_all2 (R\<^sup>*\<^sup>*) xs ys \<Longrightarrow> reflp R \<Longrightarrow> (list_all2 R)\<^sup>*\<^sup>* xs ys"
proof (induction rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons x y xs ys)
  then show ?case
  proof (induction rule: rtranclp.induct)
    case (rtrancl_refl a)
    then show ?case sorry
  next
    case (rtrancl_into_rtrancl a b c)
    then show ?case sorry
  qed
qed

  lemma nf_cannot_reduce: 
    assumes "t \<rightarrow>\<^sub>t t'"
        and "nf_term fi t"
      shows "t = t'"
    using assms
  proof (induction t arbitrary: t')
    case (Sym x)
    then show ?case 
    proof (induction "Sym x" t' rule: reduce.induct)
      case refl
      then show ?case by simp
    next
      case (step t2)
      then show ?case using nf_term_not_fst by simp
    qed
  next
    case (Fun f as)
    show ?case
    proof (cases rule: reduce_funE[OF Fun(2)])
      case 1
      then show ?thesis by simp
    next
      case 2
      with Fun(3)
      show ?thesis using nf_term_not_fst by simp
    next
      fix t' as'
      assume a: "t' = Fun f as'"
             "list_all2 (\<rightarrow>\<^sub>t) as as'"
      from Fun(3)
      have "list_all (nf_term fi) as" by (cases rule: nf_term.cases) auto
      from a(2) Fun(1) this
      have "list_all2 (=) as as'"
        by (induction rule:list_all2_induct) auto
      from a(1) this[simplified list_all2_eq[symmetric]]
      show "Fun f as = t'" by blast
    qed
  qed

  find_theorems name: "list_all*"

lemma normalise_in_trans_reduce: "(\<rightarrow>\<^sub>t)\<^sup>*\<^sup>* t (normalise_term t)"
proof (induction t)
  case (Sym x)
  then show ?case by simp
next
  case (Fun f as)
  have 1: "list_all2 ((\<rightarrow>\<^sub>t)\<^sup>*\<^sup>*) as (map normalise_term as)" 
    using Fun.IH by (induction as, auto)
  hence "((list_all2 (\<rightarrow>\<^sub>t))\<^sup>*\<^sup>*) as (map normalise_term as)"
    apply (induction rule: list_all2_induct)
     apply simp
    
  show ?case 
  proof (cases "fi (Fun f (map normalise_term as))")
    case None
    then have 2: "normalise_term (Fun f as) = (Fun f (map normalise_term as))" by simp

    show ?thesis 
      unfolding 2
    proof (induction rule: rtranclp.induct)
  next
    case (Some a)
    then show ?thesis sorry
  qed
qed

  
  lemma normalise_nf: "nf_term fi (normalise_term t)"
    sorry
  
  theorem decidable_eq_correct: "term_eq a b \<longleftrightarrow> decidable_eq a b"
    sorry
end
  
end