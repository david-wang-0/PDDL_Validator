theory Terms
  imports AST1
begin

  (* this is an equivalence relation *)
  type_synonym 'sym function_interpretation = "'sym term \<rightharpoonup> 'sym term"

  fun subterms::"'a term \<Rightarrow> 'a term set" where
    "subterms (Sym x) = {Sym x}"
  | "subterms (Fun f as) = insert (Fun f as) (\<Union> (subterms ` (set as)))"

  inductive nf_fi::"'a function_interpretation \<Rightarrow> bool"
        and nf_term::"'a function_interpretation \<Rightarrow> 'a term \<Rightarrow> bool" where
    "\<lbrakk>\<not>(\<exists>obj. Sym obj \<in> dom fi); 
        \<forall>(l, r) \<in> Map.graph fi. (\<forall>t \<in> subterms l - {l}. nf_term fi t)  \<and> nf_term fi r\<rbrakk> 
      \<Longrightarrow> nf_fi fi"
  | "nf_term fi (Sym _)"
  | "\<lbrakk>nf_fi fi; list_all (nf_term fi) as; fi (Fun f as) = None\<rbrakk> 
      \<Longrightarrow> nf_term fi (Fun f as)"

  locale term_eq =
    fixes fi::"'sym function_interpretation"
  begin
    inductive reduce::"'sym term \<Rightarrow> 'sym term \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>t" 55) where
      refl: "t \<rightarrow>\<^sub>t t"
    | trans: "\<lbrakk>t1 \<rightarrow>\<^sub>t t2; t2 \<rightarrow>\<^sub>t t3\<rbrakk> \<Longrightarrow> t1 \<rightarrow>\<^sub>t t3"
    | def: "(t1, t2) \<in> Map.graph fi \<Longrightarrow> t1 \<rightarrow>\<^sub>t t2"
    | app: "list_all2 (\<rightarrow>\<^sub>t) as as' \<Longrightarrow> (Fun f as) \<rightarrow>\<^sub>t (Fun f as')"
  
    lemma "reduce = (reduce\<^sup>*\<^sup>*)"
      apply (rule ext)+
      subgoal for a b
        apply (rule iffI)
         apply (induction rule: reduce.induct)
        subgoal by (rule rtranclp.rtrancl_refl)
        subgoal for t t' t2
          apply (rule rtranclp.rtrancl_into_rtrancl)
          by assumption+
        subgoal apply (drule def)
          apply (rule rtranclp.rtrancl_into_rtrancl)
           apply (rule rtranclp.rtrancl_refl)
          by assumption
        subgoal for as as' f
          apply (rule rtranclp.rtrancl_into_rtrancl[where b = "Fun f as"])
           apply (rule rtranclp.rtrancl_refl)
          apply (rule app)
          apply (induction rule: list_all2_induct)
           apply simp
            by auto
        apply (induction rule: rtranclp.induct)
         apply (rule refl)
        subgoal for a b c
          apply (rule trans)
          by simp+
        done
      done
  
      definition eq::"'sym term \<Rightarrow> 'sym term \<Rightarrow> bool" (infix "=\<^sub>t" 55) where
        "x =\<^sub>t y \<equiv> ((\<rightarrow>\<^sub>t)\<^sup>=\<^sup>=) x y"
  end
  
  locale decidable_eq = term_eq fi 
    for fi::"'sym term \<Rightarrow> 'sym term option" +
    assumes "nf_fi fi"
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

lemma nf_unique:
  assumes 1: "t \<rightarrow>\<^sub>t t'" "nf_term fi t'"
      and 2: "t \<rightarrow>\<^sub>t t''" "nf_term fi t''"
    shows "t' = t''"
  using assms
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

  
  lemma normalise_nf: "nf_term fi (normalise_term t)"
    sorry
  theorem decidable_eq_correct: "eq a b \<longleftrightarrow> decidable_eq a b"
    sorry
  end
  
end