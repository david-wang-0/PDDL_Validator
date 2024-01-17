subsection\<open>Semantics\<close>
theory Sema
imports Formulas
begin

type_synonym 'a valuation = "'a \<Rightarrow> bool"
text\<open>The implicit statement here is that an assignment or valuation is always defined on all atoms (because HOL is a total logic).
Thus, there are no unsuitable assignments.\<close>
      
locale formula_semantics = formula_syntax subst vars objs
  for subst::"'v \<Rightarrow> 'c \<Rightarrow> 'p \<Rightarrow> 'p"
  and vars ::"'p \<Rightarrow> 'v set"
  and objs ::"'p \<Rightarrow> 'c set"
  +
  fixes dom::"'ty \<Rightarrow> 'c list"
begin
                                               
fun height::"('p valuation \<times> ('p, 'v, 'ty) formula) \<Rightarrow> nat" where
"height (v, (Atom _)) = 0" |
"height (v, \<bottom>) = 0" |
"height (v, (Not \<phi>)) = 1 + height (v, \<phi>)" |
"height (v, (And \<phi>\<^sub>1 \<phi>\<^sub>2)) = 1 + max (height (v, \<phi>\<^sub>1)) (height (v, \<phi>\<^sub>2))" |
"height (v, (Or \<phi>\<^sub>1 \<phi>\<^sub>2)) = 1 + max (height (v, \<phi>\<^sub>1)) (height (v, \<phi>\<^sub>2))" |
"height (v, (Imp \<phi>\<^sub>1 \<phi>\<^sub>2)) = 1 + max (height (v, \<phi>\<^sub>1)) (height (v, \<phi>\<^sub>2))" |
"height (v, (Exists t x \<phi>\<^sub>1)) = 1 + height (v, \<phi>\<^sub>1)" |
"height (v, (All t x \<phi>\<^sub>1)) = 1 + height (v, \<phi>\<^sub>1)"

lemma fsubst_maintains_height: "height (v, f) = height (v, fsubst x x1 f)"
  by (induction f) auto

function formula_semantics :: "'p valuation \<Rightarrow> ('p, 'v, 'ty) formula \<Rightarrow> bool" (infix "\<Turnstile>" 61) where
"\<A> \<Turnstile> Atom k = \<A> k" |
"_ \<Turnstile> \<bottom> = False" |
"\<A> \<Turnstile> Not \<phi> = (\<not> \<A> \<Turnstile> \<phi>)" |
"\<A> \<Turnstile> And \<phi>\<^sub>1 \<phi>\<^sub>2 = (\<A> \<Turnstile> \<phi>\<^sub>1 \<and> \<A> \<Turnstile> \<phi>\<^sub>2)" |
"\<A> \<Turnstile> Or \<phi>\<^sub>1 \<phi>\<^sub>2 = (\<A> \<Turnstile> \<phi>\<^sub>1 \<or> \<A> \<Turnstile> \<phi>\<^sub>2)" |
"\<A> \<Turnstile> Imp \<phi>\<^sub>1 \<phi>\<^sub>2 = (\<A> \<Turnstile> \<phi>\<^sub>1 \<longrightarrow> \<A> \<Turnstile> \<phi>\<^sub>2)" |
"\<A> \<Turnstile> Exists t x \<phi>\<^sub>1 = (find (\<lambda>v. \<A> \<Turnstile> (fsubst x v \<phi>\<^sub>1)) (dom t) \<noteq> None)" |
"\<A> \<Turnstile> All t x \<phi>\<^sub>1 = (list_all (\<lambda>v. \<A> \<Turnstile> (fsubst x v \<phi>\<^sub>1)) (dom t))"
  by (pat_completeness) auto
termination formula_semantics
  by (relation "measure height")(auto simp add: sym[OF fsubst_maintains_height])

abbreviation valid ("\<Turnstile> _" 51) where
"\<Turnstile> F \<equiv> \<forall>A. A \<Turnstile> F"

definition formula_entailment :: "('p, 'v, 'ty) formula set \<Rightarrow> ('p, 'v, 'ty) formula \<Rightarrow> bool" 
  (infix "\<TTurnstile>" 63) where
"\<Gamma> \<TTurnstile> F \<equiv> (\<forall>\<A>. ((\<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G) \<longrightarrow> (\<A> \<Turnstile> F)))"

lemma irrelevant_atom[simp]: "A \<notin> atoms F \<Longrightarrow> (\<A>(A := V)) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
  by (induction F; auto)
lemma relevant_atoms_same_semantics: "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
  by(induction F; simp)

lemma top_semantics[simp,intro!]: "A \<Turnstile> \<top>" unfolding Top_def by simp
lemma BigAnd_semantics[simp]: "A \<Turnstile> \<^bold>\<And>F \<longleftrightarrow> (\<forall>f \<in> set F. A \<Turnstile> f)" by(induction F; simp)
lemma BigOr_semantics[simp]: "A \<Turnstile> \<^bold>\<Or>F \<longleftrightarrow> (\<exists>f \<in> set F. A \<Turnstile> f)" by(induction F; simp)
    

definition "sat S \<equiv> \<exists>\<A>. \<forall>F \<in> S. \<A> \<Turnstile> F"
definition "fin_sat S \<equiv> (\<forall>s \<subseteq> S. finite s \<longrightarrow> sat s)"
  
lemma entail_sat: "\<Gamma> \<TTurnstile> \<bottom> \<longleftrightarrow> \<not> sat \<Gamma>" (* btw. *)
  unfolding sat_def formula_entailment_def by simp

end

end
