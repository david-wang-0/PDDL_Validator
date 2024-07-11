theory Terms
  imports AST1
begin
  
  type_synonym 'sym function_interpretation = "'sym term \<rightharpoonup> 'sym term"

  fun subterms::"'a term \<Rightarrow> 'a term set" where
    "subterms (Sym x) = {Sym x}"
  | "subterms (Fun f as) = insert (Fun f as) (\<Union> (subterms ` (set as)))"
  
  (* Normal forms for terms and interpretations *)
  inductive nf_fi::"'a function_interpretation \<Rightarrow> bool" 
        and nf_term::"'a function_interpretation \<Rightarrow> 'a term \<Rightarrow> bool" where
    "\<lbrakk>\<not>(\<exists>obj. Sym obj \<in> dom fi); 
        \<forall>(f, a) \<in> Map.graph fi. (\<forall>t \<in> subterms t - {t}. nf_term fi t)  \<and> nf_term fi a\<rbrakk> 
      \<Longrightarrow> nf_fi fi"
  | "nf_term fi (Sym _)"
  | "\<lbrakk>nf_fi fi; list_all (nf_term fi) as; fi (Fun f as) = None\<rbrakk> 
      \<Longrightarrow> nf_term fi (Fun f as)"
  
  locale term_eq =
    fixes fi::"'sym function_interpretation"
    assumes "nf_fi fi"
  begin
    definition "eq \<equiv> equivclp (\<lambda>x y. fi x = Some y)"
  end

end