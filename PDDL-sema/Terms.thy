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
    "\<lbrakk>\<not>(\<exists>obj. Sym obj \<in> dom ofi); 
        \<forall>(f, a) \<in> Map.graph ofi. 
          (\<forall>t \<in> (subterms f - {f}). nf_term ofi t) 
        \<and> (\<forall>t \<in> subterms a. nf_term ofi a)\<rbrakk> 
      \<Longrightarrow> nf_fi ofi"
  | "nf_term ofi (Sym _)"
  | "\<lbrakk>nf_fi ofi; list_all (nf_term ofi) as; ofi (Fun f as) = None\<rbrakk> 
      \<Longrightarrow> nf_term ofi (Fun f as)"
  
  locale term_eq =
    fixes ofi::"object function_interpretation"
    assumes "nf_ofi ofi"
  begin
    definition "eq \<equiv> equivclp (\<lambda>x y. ofi x = Some y)"
  end

end