theory Terms
  imports AST1
begin


  find_theorems name: "list_all*"

  thm rtranclp.induct

lemma list_all2_rtranclp: "((list_all2 R)\<^sup>*\<^sup>*) xs ys \<Longrightarrow> list_all2 (R\<^sup>*\<^sup>*) xs ys"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by (induction a; simp)
next
  case (rtrancl_into_rtrancl xs ys zs)
  from this(2)[simplified list_all2_conv_all_nth]
  have 1: "length ys = length zs \<and> (\<forall>i<length ys. R (ys ! i) (zs ! i))" by simp
  from rtrancl_into_rtrancl(3)[simplified list_all2_conv_all_nth]
  have 2: "length xs = length ys \<and> (\<forall>i<length xs. R\<^sup>*\<^sup>* (xs ! i) (ys ! i))" by simp
  from 1 2
  have "(\<forall>i<length xs. R\<^sup>*\<^sup>* (xs ! i) (ys ! i) \<and> R (ys ! i) (zs ! i))" by simp+
  then
  have "(\<forall>i<length xs. R\<^sup>*\<^sup>* (xs ! i) (zs ! i))" using rtrancl.rtrancl_into_rtrancl by auto
  with 1 2
  show ?case by (subst list_all2_conv_all_nth) simp
qed

lemma reflp_imp_step:
  assumes "(R\<^sup>*\<^sup>*) x z" "reflp R" 
  obtains y where "(R\<^sup>*\<^sup>*) x y" "R y z" 
  using assms
  by (simp add: reflpD)

lemma list_all2_Cons_rtranclp': "((list_all2 R)\<^sup>*\<^sup>*) xs ys \<Longrightarrow> reflp R \<Longrightarrow> (R\<^sup>*\<^sup>*) x y \<Longrightarrow> ((list_all2 R)\<^sup>*\<^sup>*) (x#xs) (y#ys)"
proof (induction arbitrary: x y rule: rtranclp_induct)
  case base
  from \<open>R\<^sup>*\<^sup>* x y\<close> 
  show ?case
  proof (induction rule: rtranclp_induct)
    case base
    then show ?case using rtranclp.rtrancl_refl by simp
  next
    case (step y z)
    from \<open>R y z\<close> \<open>reflp R\<close>[THEN list.rel_reflp, THEN reflpD]
    have "(list_all2 R) (y#xs) (z#xs)" by simp
    from rtranclp.rtrancl_into_rtrancl[OF \<open>(list_all2 R)\<^sup>*\<^sup>* (x # xs) (y # xs)\<close> this] 
    show ?case by simp
  qed
next
  case (step ys zs)
  then 
  have "(list_all2 R)\<^sup>*\<^sup>* (x # xs) (y # ys)" by simp
  moreover
  from step(4)
  have "R y y" using reflpD by fastforce
  with step(2)
  have "list_all2 R (y # ys) (y # zs)" by blast
  ultimately
  show ?case using rtranclp.rtrancl_into_rtrancl by force
qed

lemma list_all2_rtranclp': "list_all2 (R\<^sup>*\<^sup>*) xs ys \<Longrightarrow> reflp R \<Longrightarrow> ((list_all2 R)\<^sup>*\<^sup>*) xs ys"
proof (induction rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons x z xs zs)
  from Cons(3)[OF Cons(4)]
  obtain ys where
    "((list_all2 R)\<^sup>*\<^sup>*) xs ys" 
    "list_all2 R ys zs" 
    using reflp_imp_step Cons(4) list.rel_reflp by metis
  with Cons
  show ?case using list_all2_Cons_rtranclp' by fast
qed

lemma rtranclp_mono_rel: assumes "(R\<^sup>*\<^sup>*) x y"
  "\<And>a b. R a b \<Longrightarrow> R (F a) (F b)"
shows "(R\<^sup>*\<^sup>*) (F x) (F y)"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  from step(3)[OF step(4), THEN rtranclp.rtrancl_into_rtrancl] step(4)[OF step(2)]
  show ?case by blast
qed

lemma list_all2_singleton: "list_all2 R [x] [y] = R x y"
  by simp

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

  
  abbreviation term_eq::"'sym term \<Rightarrow> 'sym term \<Rightarrow> bool" (infix "=\<^sub>t" 55) where
    "term_eq \<equiv> equivclp (\<rightarrow>\<^sub>t)"

  lemma reduce_refl: "(\<rightarrow>\<^sub>t)\<^sup>=\<^sup>= = (\<rightarrow>\<^sub>t)"
    by (blast intro: refl)
  
  lemma reduce_rtrancl_is_trancl: "(\<rightarrow>\<^sub>t)\<^sup>*\<^sup>* = (\<rightarrow>\<^sub>t)\<^sup>+\<^sup>+"
    apply (rule ext)+
    subgoal by (auto simp: Nitpick.rtranclp_unfold intro: refl)
    done

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


lemma normalise_in_rtrancl_reduce: "(\<rightarrow>\<^sub>t)\<^sup>*\<^sup>* t (normalise_term t)"
proof (induction t)
  case (Sym x)
  then show ?case by simp
next
  case (Fun f as)
  have "list_all2 ((\<rightarrow>\<^sub>t)\<^sup>*\<^sup>*) as (map normalise_term as)" 
    using Fun.IH by (induction as, auto)
  from this[THEN list_all2_rtranclp', OF reflpI]
    have "(list_all2 (\<rightarrow>\<^sub>t))\<^sup>*\<^sup>* as (map normalise_term as)" by (auto simp: refl)
  from rtranclp_mono_rel[OF this, where F = "\<lambda>x. [Fun f x]", 
        simplified list_all2_singleton, OF reduce.app, 
        THEN list_all2_rtranclp, simplified list_all2_singleton]
  have 2: "(\<rightarrow>\<^sub>t)\<^sup>*\<^sup>* (Fun f as) (Fun f (map normalise_term as))" by simp
  show ?case 
  proof (cases "fi (Fun f (map normalise_term as))")
    case None
    then have 3: "normalise_term (Fun f as) = (Fun f (map normalise_term as))" by simp
    with 2
    show ?thesis by simp
  next
    case (Some a)
    then have "Fun f (map normalise_term as) \<rightarrow>\<^sub>t a" using in_graphI[of fi] reduce.step by blast
    from rtranclp.rtrancl_into_rtrancl[OF 2 this]
    show ?thesis using Some by simp
  qed
qed

  
  lemma normalise_nf: "nf_term fi (normalise_term t)"
    sorry
  
  theorem decidable_eq_correct: "term_eq a b \<longleftrightarrow> decidable_eq a b"
    sorry
end
  
end