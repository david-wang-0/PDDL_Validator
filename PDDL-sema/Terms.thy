theory Terms
  imports AST1 
  "Automatic_Refinement.Misc"
  "Automatic_Refinement.Refine_Util"
  Util
begin

text \<open>Some useful lemmas to reason about the reflexive transitive closure. \<close>

lemma list_all2_rtranclp: "((list_all2 R)\<^sup>*\<^sup>*) xs ys \<Longrightarrow> list_all2 (R\<^sup>*\<^sup>*) xs ys"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by (induction a; simp)
next
  case (rtrancl_into_rtrancl xs ys zs)
  from this(2)[simplified list_all2_conv_all_nth]
  have 1: "length ys = length zs \<and> (\<forall>i<length ys. R (ys ! i) (zs ! i))" by simp
  moreover
  from rtrancl_into_rtrancl(3)[simplified list_all2_conv_all_nth]
  have 2: "length xs = length ys \<and> (\<forall>i<length xs. R\<^sup>*\<^sup>* (xs ! i) (ys ! i))" by simp
  ultimately
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

subsection \<open>Terms, interpretations, normal forms, and normalisation\<close>

type_synonym 'sym function_interpretation = "'sym term \<rightharpoonup> 'sym term"

fun subterms::"'a term \<Rightarrow> 'a term set" where
  "subterms (Sym x) = {Sym x}"
| "subterms (Fun f as) = insert (Fun f as) (\<Union> (subterms ` (set as)))"

lemma term_in_subterms: "x \<in> subterms x"
  by (cases x) auto

lemma args_in_subterms: "set as \<subseteq> subterms (Fun f as)"
  using term_in_subterms by auto
   
(* inductive n_fi::"'a function_interpretation \<Rightarrow> bool"
      and nf_term::"'a function_interpretation \<Rightarrow> 'a term \<Rightarrow> bool" where
  int_normalising: "\<lbrakk>\<not>(\<exists>obj. Sym obj \<in> dom fi); 
      \<forall>(l, r) \<in> Map.graph fi. \<exists>f as. (Fun f as = l \<and> list_all (nf_term fi) as) \<and> nf_term fi r\<rbrakk> \<Longrightarrow> n_fi fi"
| sym_normal: "n_fi fi \<Longrightarrow> nf_term fi (Sym s)"
| fun_normal: "\<lbrakk>n_fi fi; list_all (nf_term fi) as; fi (Fun f as) = None\<rbrakk> 
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

inductive_cases n_fiE: "n_fi fi" *)

context 
  fixes fi::"'sym function_interpretation"
begin
  subsubsection \<open>Reduction under an interpretation and equality\<close>
  inductive reduce::"'sym term \<Rightarrow> 'sym term \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>t" 55)where
      refl: "t \<rightarrow>\<^sub>t t"
    | step: "(t1, t2) \<in> Map.graph fi \<Longrightarrow> t1 \<rightarrow>\<^sub>t t2"
    | app: "list_all2 (\<rightarrow>\<^sub>t) as as' \<Longrightarrow> (Fun f as) \<rightarrow>\<^sub>t (Fun f as')"
  
  abbreviation term_eq::"'sym term \<Rightarrow> 'sym term \<Rightarrow> bool" (infix "=\<^sub>t" 55) where
    "term_eq \<equiv> equivclp (\<rightarrow>\<^sub>t)"

  inductive_cases reduce_funE: "Fun f as \<rightarrow>\<^sub>t a"

  lemma reduce_refl: "(\<rightarrow>\<^sub>t)\<^sup>=\<^sup>= = (\<rightarrow>\<^sub>t)"
    by (blast intro: refl)
  
  lemma reduce_rtrancl_is_trancl: "(\<rightarrow>\<^sub>t)\<^sup>*\<^sup>* = (\<rightarrow>\<^sub>t)\<^sup>+\<^sup>+"
    apply (rule ext)+
    subgoal by (auto simp: Nitpick.rtranclp_unfold intro: refl)
    done
  
inductive n_fi::"bool"
      and n_asmt::"'sym term \<Rightarrow> 'sym term \<Rightarrow> bool"
      and nf_term::"'sym term \<Rightarrow> bool" where
    int_normalising: "\<lbrakk>\<not>(\<exists>obj. Sym obj \<in> dom fi); 
        \<forall>(l, r) \<in> Map.graph fi. n_asmt l r\<rbrakk> 
          \<Longrightarrow> n_fi"
  | asmt_is_final: "list_all nf_term as \<Longrightarrow> nf_term r \<Longrightarrow> n_asmt (Fun f as) r"
  | any_asmt: "(\<forall>as'. list_all2 (\<rightarrow>\<^sub>t) as as' \<longrightarrow> Fun f as' \<rightarrow>\<^sub>t r) \<Longrightarrow> nf_term r \<Longrightarrow> n_asmt (Fun f as) r"
  | sym_normal: "n_fi \<Longrightarrow> nf_term (Sym s)"
  | fun_normal: "\<lbrakk>n_fi; list_all nf_term as; fi (Fun f as) = None\<rbrakk> 
      \<Longrightarrow> nf_term (Fun f as)"

inductive_cases n_fiE: "n_fi"
inductive_cases n_asmtE: "n_asmt l r"
end

context
  fixes fi::"'sym function_interpretation"
  assumes nf: "n_fi fi"
begin
abbreviation "red \<equiv> reduce fi"
abbreviation "t_eq \<equiv> term_eq fi"
notation "red" ("_ \<rightarrow>\<^sub>t _")
notation t_eq ("_ =\<^sub>t _")

thm n_asmtE[of fi]

lemmas red_funE = reduce_funE[of fi]

text \<open>When an interpretation is normalising, equality becomes decidable by inside-out reduction.\<close>  
  fun normalise_term::"'sym term \<Rightarrow> 'sym term" where
    "normalise_term (Sym s) = (Sym s)"
  | "normalise_term (Fun f as) = (
      let as' = map normalise_term as 
      in (case (fi (Fun f as')) of
        Some t  \<Rightarrow> t
      | None    \<Rightarrow> (Fun f as')
      )
    )"

  definition check_eq::"'sym term \<Rightarrow> 'sym term \<Rightarrow> bool" where
    "check_eq a b \<equiv> (normalise_term a) = (normalise_term b)"

  lemma nf_cannot_reduce': 
    assumes "nf_term fi t"
    shows "t \<notin> dom fi"
  proof (cases t)
    case (Sym s)
    with nf
    show "t \<notin> dom fi" 
      apply (cases rule: n_fi.cases)
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


  text \<open>If a term is in normal form, it can only reduce to itself.\<close>
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
    proof (cases rule: red_funE[OF Fun(2)])
      case 1
      then show ?thesis by simp
    next
      case 2
      with Fun(3)
      show ?thesis using nf_term_not_fst by simp
    next
      fix as'
      assume a: "t' = Fun f as'"
             "list_all2 red as as'"
      from Fun(3)
      have "list_all (nf_term fi) as" by (cases rule: nf_term.cases) auto
      from a(2) Fun(1) this
      have "list_all2 (=) as as'"
        by (induction rule:list_all2_induct) auto
      from a(1) this[simplified list_all2_eq[symmetric]]
      show "Fun f as = t'" by blast
    qed
  qed

  lemma nf_cannot_reduce_trans: 
    assumes "(red\<^sup>*\<^sup>*) t t'"
        and "nf_term fi t"
      shows "t = t'"
    using assms
    apply (induction rule: rtranclp_induct)
     apply simp
    subgoal for y z
      apply (drule nf_cannot_reduce)
      by auto
    done


  text \<open>The normalisation function returns something related to the original term by the 
        reflexive transitive close of the reduction relation\<close>
  lemma normalise_in_rtrancl_reduce: "red\<^sup>*\<^sup>* t (normalise_term t)"
  proof (induction t)
    case (Sym x)
    then show ?case by simp
  next
    case (Fun f as)
    have 1: "list_all2 (red\<^sup>*\<^sup>*) as (map normalise_term as)" 
      using Fun.IH by (induction as, auto)
    from this[THEN list_all2_rtranclp', OF reflpI]
      have "(list_all2 red)\<^sup>*\<^sup>* as (map normalise_term as)" by (auto simp: refl)
    from rtranclp_mono_rel[OF this, where F = "\<lambda>x. [Fun f x]", 
          simplified list_all2_singleton, OF reduce.app, 
          THEN list_all2_rtranclp, simplified list_all2_singleton]
    have 2: "red\<^sup>*\<^sup>* (Fun f as) (Fun f (map normalise_term as))" by simp
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

  text \<open>The normalisation function returns a term in normal form.\<close>
  lemma normalise_nf: "nf_term fi (normalise_term t)"
  proof (induction t)
    case (Sym x)
    then show ?case using sym_normal[OF nf] by simp
  next
    case (Fun f as)
    show ?case
    proof (cases "fi (Fun f (map normalise_term as))")
      case None
      then have "normalise_term (Fun f as) = Fun f (map normalise_term as)" by simp
      moreover
      have "list_all (nf_term fi) (map normalise_term as)" using Fun.IH
        apply (subst list_all_iff)
        by simp
      ultimately
      show ?thesis using fun_normal[OF nf] None by presburger
    next
      case (Some a)
      have "nf_term fi a"
        apply (cases rule: n_fi.cases[OF nf])
        apply (drule bspec[OF _ in_graphI[where m = fi, OF Some]])
        apply (cases rule: n_asmtE[of fi])
        by auto
      moreover
      from Some
      have "normalise_term (Fun f as) = a" by simp
      ultimately
      show ?thesis by simp
    qed
  qed

  lemma reduce_confluent: 
    assumes "t \<rightarrow>\<^sub>t t'"
            "t \<rightarrow>\<^sub>t t''"
      shows "\<exists>t'''. t' \<rightarrow>\<^sub>t t''' \<and> t'' \<rightarrow>\<^sub>t t'''"
    using assms
  proof (induction arbitrary: t'' rule: reduce.induct)
    case (refl t)
    then show ?case using reduce.refl[of fi t''] by blast
  next
    case (step t1 t2)
    obtain f as where
      t1: "t1 = Fun f as"
      using step(1)
      apply (cases rule: n_fiE[OF nf])
      apply (cases rule: n_asmt.cases[of fi])
      by auto

    from step(1)[simplified t1] 
    consider  "list_all (nf_term fi) as" | "(\<forall>as'. list_all2 red as as' \<longrightarrow> Fun f as' \<rightarrow>\<^sub>t t2)"
      apply (cases rule: n_fi.cases[OF nf]) 
      apply (drule bspec, assumption)
      apply (cases rule: n_asmt.cases[of fi])
      by auto
    note inner_red = this

    have t'': "t'' = t1 \<or> t'' = t2 \<or> (\<exists>as'. list_all2 red as as' \<and> Fun f as' \<rightarrow>\<^sub>t t2 \<and> t'' = Fun f as')"
    proof (cases rule: reduce_funE[OF step(2)[simplified t1]])
      case 1
      then show ?thesis using t1 by simp
    next
      case 2
      with step(1)[simplified t1]
      show ?thesis
        apply -
        apply (drule in_graphD)+
        by simp
    next
      case (3 as')
      show ?thesis
      proof (cases rule: inner_red)
        case 1
        from 3(2) this
        have "as = as'"
          apply (subst list_all2_eq)
          by (induction rule: list_all2_induct, auto intro: nf_cannot_reduce)
        with t1 3(1)
        show ?thesis by argo 
      next
        case 2
        then show ?thesis using 3 by blast
      qed
    qed
    then consider "t'' = t1" | "t'' = t2" | "(\<exists>as'. list_all2 local.red as as' \<and> Fun f as' \<rightarrow>\<^sub>t t2 \<and> t'' = Fun f as')" by auto
    then show ?case
    proof cases
      case 1
      show ?thesis
        using step
        apply (subst 1)
        apply (subst (asm) 1)
        apply (drule reduce.step)
        apply (insert refl[of fi t2])
        by auto
    next
      case 2
      show ?thesis
        apply (subst 2)
        using refl[of fi t2]
        by auto
    next
      case 3
      show ?thesis
        using 3 refl[of fi t2]
        by blast
    qed 
  next
    case (app as as' f)
    have as_as': "list_all2 red as as'"
      using app(1) 
      using app(1) by (induction rule: list_all2_induct) auto
    then have t': "Fun f as \<rightarrow>\<^sub>t Fun f as'"
      by (rule reduce.app)
      
    show ?case
    proof (cases rule: red_funE[OF app(2)])
      case 1
      with t'
      show ?thesis using refl[of fi "Fun f as'"] by auto
    next
      case 2
      with as_as' 
      consider "list_all (nf_term fi) as" | "(Fun f as' \<rightarrow>\<^sub>t t'')"
        apply (cases rule: n_fi.cases[OF nf])
        by (cases rule: n_asmt.cases[of fi]) auto
      then show ?thesis 
      proof cases
        case 1
        with as_as' 
        have "as = as'"
          by (induction rule: list_all2_induct) (auto intro: nf_cannot_reduce simp: list_all2_eq)
        then show ?thesis 
          using reduce.step[OF 2] reduce.refl[of fi t'']
          by blast
      next
        case 2
        then show ?thesis using reduce.refl[of fi t''] by blast
      qed
    next
      case (3 as'')
      from app.IH
      have "list_all2 (\<lambda>x1 x2.\<forall>x. x1 \<rightarrow>\<^sub>t x \<longrightarrow> (\<exists>t'''. x2 \<rightarrow>\<^sub>t t''' \<and> x \<rightarrow>\<^sub>t t''')) as as'"
        by (induction rule: list_all2_induct) auto
      from this[simplified list_all2_conv_all_nth]
      have "(\<forall>i<length as. \<forall>x. as ! i \<rightarrow>\<^sub>t x \<longrightarrow> (\<exists>t'''. as' ! i \<rightarrow>\<^sub>t t''' \<and> x \<rightarrow>\<^sub>t t'''))" by simp
      moreover
      from as_as'[simplified list_all2_conv_all_nth]
      have "length as = length as'" "\<forall>i<length as. as ! i \<rightarrow>\<^sub>t as' ! i" by simp+
      moreover
      from 3(2)[simplified list_all2_conv_all_nth]
      have "length as = length as''" "\<forall>i<length as. as ! i \<rightarrow>\<^sub>t as'' ! i" by simp+
      ultimately
      have "length as' = length as''" "\<forall>i<length as'.(\<exists>t'''. as' ! i \<rightarrow>\<^sub>t t''' \<and> as'' ! i \<rightarrow>\<^sub>t t''')"
        by auto
      then have "list_all2 (\<lambda>x y. \<exists>t. x \<rightarrow>\<^sub>t t \<and> y \<rightarrow>\<^sub>t t) as' as''" 
        apply (subst list_all2_conv_all_nth)
        by blast
      then have "\<exists>as'''. list_all2 (red) as' as''' \<and> list_all2 (red) as'' as'''"
        by (induction rule: list_all2_induct) auto
      then obtain as''' where
        "Fun f as' \<rightarrow>\<^sub>t Fun f as'''"
        "Fun f as'' \<rightarrow>\<^sub>t Fun f as'''"
        using reduce.app by blast
      with 3 
      show ?thesis by blast 
      qed
    qed

lemma reduce_rtrancl_confluent':
  assumes "(red\<^sup>*\<^sup>*) t t'"
          "t \<rightarrow>\<^sub>t t''"
    shows "\<exists>t'''. t' \<rightarrow>\<^sub>t t''' \<and> (red\<^sup>*\<^sup>*) t'' t'''"
  using assms
proof (induction arbitrary: t'' rule: rtranclp_induct)
  case base
  then show ?case using rtranclp.rtrancl_refl by auto
next
  case (step y z)
  then obtain t''' where
    t''': "y \<rightarrow>\<^sub>t t'''" "red\<^sup>*\<^sup>* t'' t'''" by blast
  from reduce_confluent[OF this(1) step(2)]
  obtain a where
    "t''' \<rightarrow>\<^sub>t a" "z \<rightarrow>\<^sub>t a" by blast
  from rtranclp.rtrancl_into_rtrancl[OF t'''(2) this(1)] this(2)
  show ?case by blast
qed

lemma reduce_rtrancl_confluent: 
  assumes "(red\<^sup>*\<^sup>*) t t'"
          "(red\<^sup>*\<^sup>*) t t''"
    shows "\<exists>t'''.(red\<^sup>*\<^sup>*) t' t''' \<and> (red\<^sup>*\<^sup>*) t'' t'''"
  using assms
proof (induction arbitrary: t'' rule: rtranclp_induct)
  case base
  then show ?case 
    using rtranclp.rtrancl_refl[where a = t'']
    by blast
next
  case (step y z)
  then obtain t''' where
    t''': "red\<^sup>*\<^sup>* y t'''" "red\<^sup>*\<^sup>* t'' t'''"
    by blast
  from reduce_rtrancl_confluent'[OF this(1) step(2)]
  obtain a where
    "t''' \<rightarrow>\<^sub>t a" 
    "red\<^sup>*\<^sup>* z a" by blast
  from rtranclp.rtrancl_into_rtrancl[OF t'''(2) this(1)] this(2)
  show ?case by auto
qed
  

  lemma unique_nf: 
    assumes t': "red\<^sup>*\<^sup>* t t'" "nf_term fi t'" 
        and t'': "red\<^sup>*\<^sup>* t t''" "nf_term fi t''" 
    shows "t'' = t'"
  proof -
    from t'(1) t''(1)
    obtain t''' where
      "red\<^sup>*\<^sup>* t' t'''"
      "red\<^sup>*\<^sup>* t'' t'''"
      using reduce_rtrancl_confluent by blast
    with t'(2) t''(2)
    have "t' = t'''"
         "t'' = t'''" using nf_cannot_reduce_trans by blast+
    then show "t'' = t'" by simp
  qed
  
  theorem decidable_eq_correct: "a =\<^sub>t b \<longleftrightarrow> check_eq a b"
  proof (rule iffI)
    assume a: "t_eq a b"
    then have "red\<^sup>*\<^sup>* a (normalise_term b) \<or> red\<^sup>*\<^sup>* b (normalise_term a)"
    proof (induction rule: equivclp_induct)
      case base
      then show ?case using normalise_in_rtrancl_reduce by simp
    next
      case (step y z)
      from step consider "y \<rightarrow>\<^sub>t z" | "z \<rightarrow>\<^sub>t y" by auto
      note 1 = this
      from step consider "red\<^sup>*\<^sup>* a (normalise_term y)" | "red\<^sup>*\<^sup>* y (normalise_term a)" by auto
      note 2 = this
      then show ?case 
      proof (cases rule: 1)
        assume yz: "y \<rightarrow>\<^sub>t z"
        then
        have yz': "red\<^sup>*\<^sup>* y z" by blast
        show ?thesis 
        proof (cases rule: 2)
          assume ay: "red\<^sup>*\<^sup>* a (normalise_term y)"
          have "red\<^sup>*\<^sup>* y (normalise_term y)" using normalise_in_rtrancl_reduce by simp
          with yz'
          have "\<exists>y'. red\<^sup>*\<^sup>* (normalise_term y) y' \<and> red\<^sup>*\<^sup>* z y'" using reduce_rtrancl_confluent by blast
          hence "red\<^sup>*\<^sup>* z (normalise_term y)" using nf_cannot_reduce_trans normalise_nf[of y] by blast
          with normalise_in_rtrancl_reduce[of z]
          have "\<exists>y'. red\<^sup>*\<^sup>* (normalise_term y) y' \<and> red\<^sup>*\<^sup>* (normalise_term z) y'" using reduce_rtrancl_confluent by blast
          hence "normalise_term y = normalise_term z" using nf_cannot_reduce_trans normalise_nf[of z] normalise_nf[of y] by blast
          with ay
          show ?thesis by simp
        next
          assume ya: "red\<^sup>*\<^sup>* y (normalise_term a)"
          with yz'
          have "\<exists>z'. red\<^sup>*\<^sup>* (normalise_term a) z' \<and> red\<^sup>*\<^sup>* z z'" using reduce_rtrancl_confluent by blast
          then
          show ?thesis using nf_cannot_reduce_trans[OF _ normalise_nf[of a]] by blast
        qed
      next
        assume zy: "z \<rightarrow>\<^sub>t y"
        then have zy': "red\<^sup>*\<^sup>* z y" by blast
        show ?thesis
        proof (cases rule: 2)
          assume ay: "red\<^sup>*\<^sup>* a (normalise_term y)"
          from zy' normalise_in_rtrancl_reduce[of y]
          have "red\<^sup>*\<^sup>* z (normalise_term y)" using rtranclp_trans by simp
          from reduce_rtrancl_confluent[OF this normalise_in_rtrancl_reduce[of z]]
          have "normalise_term z = normalise_term y" 
            using nf_cannot_reduce_trans[OF _ normalise_nf[of z]] nf_cannot_reduce_trans[OF _ normalise_nf[of y]] 
            by blast
          with ay
          show ?thesis by simp
        next
          assume ya: "red\<^sup>*\<^sup>* y (normalise_term a)"
          from rtranclp_trans[OF zy' this]
          show ?thesis by simp
        qed
      qed
    qed
    then 
    consider "red\<^sup>*\<^sup>* a (normalise_term b)" | "red\<^sup>*\<^sup>* b (normalise_term a)" by blast
    then have "normalise_term a = normalise_term b"
    proof cases
      assume ab: "red\<^sup>*\<^sup>* a (normalise_term b)"
      from normalise_in_rtrancl_reduce[of a]
      have "red\<^sup>*\<^sup>* a (normalise_term a)" .
      from reduce_rtrancl_confluent[OF ab this]
      show "normalise_term a = normalise_term b" 
        using nf_cannot_reduce_trans[OF _ normalise_nf] by blast
    next
      assume ba: "red\<^sup>*\<^sup>* b (normalise_term a)"
      from normalise_in_rtrancl_reduce[of b]
      have "red\<^sup>*\<^sup>* b (normalise_term b)" .
      from reduce_rtrancl_confluent[OF ba this]
      show "normalise_term a = normalise_term b" 
        using nf_cannot_reduce_trans[OF _ normalise_nf] by blast
    qed
    then show "check_eq a b" using check_eq_def by simp
  next
    assume a: "check_eq a b"
    have "a =\<^sub>t normalise_term a" using normalise_in_rtrancl_reduce[THEN rtranclp_into_equivclp] .
    with a
    have "a =\<^sub>t normalise_term b" using check_eq_def by simp
    from equivclp_trans[OF this] normalise_in_rtrancl_reduce[of b, THEN rtranclp_into_equivclp, THEN equivclp_sym]
    show "a =\<^sub>t b" by simp
  qed
end


end