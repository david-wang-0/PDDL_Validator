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

  definition eq::"'sym term \<Rightarrow> 'sym term \<Rightarrow> bool" (infix "=\<^sub>t" 55) where
    "x =\<^sub>t y \<equiv> ((\<rightarrow>\<^sub>t)\<^sup>=\<^sup>=) x y"

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

lemma unique_reduction:
  assumes "t1 \<rightarrow>\<^sub>t t2"
      and "(t1, t2) \<in> Map.graph fi"
      and "t1 \<rightarrow>\<^sub>t t'"
    shows "t' = t1 \<or> t' = t2"
proof (cases t1)
  case (Sym x)
  with assms(2)
  have "False" 
    apply (cases rule: nf_fi.cases[OF nf])
    apply (drule graph_domD)
    by simp
  then show ?thesis by simp
next
  case (Fun f as)
  show ?thesis
  proof (rule ccontr)
    assume "\<not> (t' = t1 \<or> t' = t2)"
    hence "t' \<noteq> t1" "t' \<noteq> t2" by auto
    from assms(3, 2) this
    have "\<exists>as'. list_all2 (\<rightarrow>\<^sub>t) as as' \<and> as \<noteq> as'"
      unfolding Fun
    proof (induction "Fun f as" t' arbitrary: t2 rule: reduce.induct)
      case (refl t)
      then show ?case by simp
    next
      case (trans t t' t'')
      show ?case 
      proof (cases "t = Fun f as")
        case True
        with trans
        show ?thesis by simp
      next
        case False
        from \<open>(Fun f as, t'') \<in> Map.graph fi\<close>
        have "nf_term fi t''" 
          by (cases rule: nf_fi.cases[OF nf]) auto 
        have "t \<noteq> t''" 
        proof
          assume "t = t''"
          from nf_cannot_reduce[OF \<open>nf_term fi t''\<close> trans(3)[simplified this]] trans(7)
          show False by simp
        qed    
        from trans(2)[OF trans(5) False this]
        show ?thesis .
      qed
    next
      case (def t t2')
      from in_graphD[OF this(1)] in_graphD[OF this(2)] this(4)
      show ?case by simp
    next
      case (app as' t')
      from this (1)
      have "list_all2 (\<rightarrow>\<^sub>t) as as'" 
        by (induction rule: list_all2_induct) auto
      with app(3)
      show ?case by blast
    qed
    then obtain as' where
      as': "list_all2 (\<rightarrow>\<^sub>t) as as'"
      "as \<noteq> as'" by auto 
    
    from assms(2)[simplified Fun]
    have "list_all (nf_term fi) as" 
    proof (cases rule: nf_fi.cases[OF nf])
      case (1 fi)
      with assms(2)[simplified Fun]
      show ?thesis by fast 
    qed
    with as'(1)
    have "as = as'" 
    proof (subst list_all2_eq, induction rule: list_all2_induct)
      case Nil
      then show ?case by auto
    next
      case (Cons x y xs ys)
      hence "nf_term fi x" by auto
      with Cons(1)
      have "x = y" using nf_cannot_reduce by simp
      then show ?case using Cons by auto
    qed
    with as'(2)
    show False by simp
  qed
qed

lemma unique_application:
  assumes "Fun f as \<rightarrow>\<^sub>t Fun f as'"
      and "Fun f as \<rightarrow>\<^sub>t t'"
    shows "t' \<rightarrow>\<^sub>t Fun f as' \<or> Fun f as' \<rightarrow>\<^sub>t t'"
  using assms(2,1)
proof (induction rule: reduce.induct)
  case (refl t)
  then show ?case sorry
next
  case (trans t1 t2 t3)
  then show ?case sorry
next
  case (def t1 t2)
  then show ?case sorry
next
  case (app as as' f)
  then show ?case sorry
qed

lemma idk:
  assumes "t1 \<rightarrow>\<^sub>t t2" 
      and "t1 \<rightarrow>\<^sub>t t'"
    shows "t2 \<rightarrow>\<^sub>t t' \<or> t' \<rightarrow>\<^sub>t t2"
  using assms
proof (induction arbitrary: t' rule: reduce.induct)
  case (refl t)
  then show ?case by simp
next
  case (trans t t2 t3)
  then consider "t2 \<rightarrow>\<^sub>t t'" | "t' \<rightarrow>\<^sub>t t2" by auto
  then show ?case 
  proof (cases)
    case 1
    from trans.IH(2)[OF this]
    show ?thesis .
  next
    case 2
    from reduce.trans[OF this \<open>t2 \<rightarrow>\<^sub>t t3\<close>]
    show ?thesis by simp
  qed
next
  case (def t1 t2)
  from unique_reduction def(1)[THEN reduce.def] def
  consider "t' = t1" | "t' = t2" by blast
  then show ?case
  proof (cases)
    case 1
    from def 
    have "t1 \<rightarrow>\<^sub>t t2" using reduce.def by auto 
    with 1
    show ?thesis by simp
  next
    case 2
    then show ?thesis using refl by auto
  qed
next
  case (app as as' f)
  have "list_all2 (\<lambda>x1 x2. x1 \<rightarrow>\<^sub>t x2) as as'" using app(1)
    by (induction rule: list_all2_induct) auto
  then
  have "Fun f as \<rightarrow>\<^sub>t Fun f as'" using reduce.app by simp
  with app(2, 1) this
  show ?case 
  proof (induction "Fun f as" t' rule: reduce.induct)
    case refl
    then show ?case by simp
  next
    case (trans t2 t3)
    show ?case
    proof (cases "t2 = Fun f as")
      case True
      with trans 
      show ?thesis by auto
    next
      case False
      from trans
      have "Fun f as' \<rightarrow>\<^sub>t t2 \<or> t2 \<rightarrow>\<^sub>t Fun f as'" by auto
      with trans(1,3,4,5,6,7) app
      show ?thesis 
    qed
  next
    case (def t2)
    then show ?case sorry
  next
    case (app as')
    then show ?case sorry
  qed
qed

lemma nf_reachable: 
  assumes "t \<rightarrow>\<^sub>t t'" "nf_term fi t'"
          "t \<rightarrow>\<^sub>t t''"
    shows "t'' \<rightarrow>\<^sub>t t'"
  using assms
proof (induction arbitrary: t'' rule: reduce.induct)
  case (refl t)
  then show ?case using nf_cannot_reduce by blast
next
  case (trans t1 t2 t3)
  with 
  show ?case
  proof (cases "t2 = t3")
    case True
    then show ?thesis using trans by simp
  next
    case False
    show ?thesis 
    proof (cases "t'' = t3")
      case True
      then show ?thesis using refl by simp
    next
      case False
      show ?thesis 
      proof (cases "t'' = t2")
        case True
        then show ?thesis using trans by simp
      next
        case False
        with \<open>t'' \<noteq> t3\<close> \<open>t2 \<noteq> t3\<close>
        show ?thesis using trans 
      qed
    qed
  qed
next
  case (def t1 t2)
  then show ?case sorry
next
  case (app as as' f)
  then show ?case sorry
qed


lemma nf_unique:
  assumes 1: "t \<rightarrow>\<^sub>t t'" "nf_term fi t'"
      and 2: "t \<rightarrow>\<^sub>t t''" "nf_term fi t''"
    shows "t' = t''"
  using assms
proof (induction arbitrary: t'' rule: reduce.induct)
  case (refl t)
  then show ?case using nf_cannot_reduce by simp
next
  case (trans t1 t2 t3)
  from nf_reachable[OF \<open>t1 \<rightarrow>\<^sub>t t''\<close> \<open>nf_term fi t''\<close> \<open>t1 \<rightarrow>\<^sub>t t2\<close>]
  have "t2 \<rightarrow>\<^sub>t t''" by auto
  with trans.IH(2) trans.prems
  show ?case by simp 
next
  case (def t1 t2)
  then show ?case sorry
next
  case (app as as' f)
  then show ?case sorry
qed

  
  lemma normalise_nf: "nf_term fi (normalise_term t)"
    sorry
  theorem decidable_eq_correct: "eq a b \<longleftrightarrow> decidable_eq a b"
    sorry
  end
  
end