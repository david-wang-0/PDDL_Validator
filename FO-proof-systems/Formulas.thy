section \<open>Formulas\<close>

theory Formulas
imports Main "HOL-Library.Countable"
begin

(* unrelated, but I need this in too many places. *)
notation insert ("_ \<triangleright> _" [56,55] 55)

datatype (atoms: 'p, vars: 'v, types: 'ty) formula = 
    Atom 'p
  | Bot                                                     ("\<bottom>")  
  | Not "('p, 'v, 'ty) formula"                             ("\<^bold>\<not>")
  | And "('p, 'v, 'ty) formula" "('p, 'v, 'ty) formula"     (infix "\<^bold>\<and>" 68)
  | Or "('p, 'v, 'ty) formula" "('p, 'v, 'ty) formula"      (infix "\<^bold>\<or>" 68)
  | Imp "('p, 'v, 'ty) formula" "('p, 'v, 'ty) formula"     (infixr "\<^bold>\<rightarrow>" 68)
  | Exists 'ty 'v "('p, 'v, 'ty) formula"                   ("\<^bold>\<exists>\<^sub>_ _. _ " 0)
  | All 'ty 'v "('p, 'v, 'ty) formula"                      ("\<^bold>\<forall>\<^sub>_ _. _" 0)
(* In a standard Isabelle/jEdit config, bold can be done with C-e rightarrow.
   I learned that way too late. *)
(* I'm not sure I'm happy about the definition of what is an atom.
   I'm inclined to treat 'a as our atom type and call an Atom k an "atom formula",
   but this goes against anything the literature does. So, Atom k will be an atom,
   k its index, but there are probably a few cases where I call 'a an atom\<dots> *)
(* like here: *)
lemma atoms_finite[simp,intro!]: "finite (atoms F)" by(induction F; simp)

primrec subformulae where
"subformulae \<bottom> = [\<bottom>]" |
"subformulae (Atom k) = [Atom k]" |
"subformulae (Not F) = Not F # subformulae F" |
"subformulae (And F G) = And F G # subformulae F @ subformulae G" |
"subformulae (Imp F G) = Imp F G # subformulae F @ subformulae G" |
"subformulae (Or F G) = Or F G # subformulae F @ subformulae G" |
"subformulae (Exists t x F) = (Exists t x F) # subformulae F" |
"subformulae (All t x F) = (All t x F) # subformulae F"

lemma atoms_are_subformulae: "Atom ` atoms F \<subseteq> set (subformulae F)"
  by (induction F) auto
    
lemma subsubformulae: "G \<in> set (subformulae F) \<Longrightarrow> H \<in> set (subformulae G) \<Longrightarrow> H \<in> set (subformulae F)"
  by(induction F; force)
    
lemma subformula_atoms: "G \<in> set (subformulae F) \<Longrightarrow> atoms G \<subseteq> atoms F"
  by(induction F) auto
    
lemma subformulae_self[simp,intro]: "F \<in> set (subformulae F)"
  by(induction F; simp)

lemma subformulas_in_subformulas:
  "G \<^bold>\<and> H \<in> set (subformulae F) \<Longrightarrow> G \<in> set (subformulae F) \<and> H \<in> set (subformulae F)"
  "G \<^bold>\<or> H \<in> set (subformulae F) \<Longrightarrow> G \<in> set (subformulae F) \<and> H \<in> set (subformulae F)"
  "G \<^bold>\<rightarrow> H \<in> set (subformulae F) \<Longrightarrow> G \<in> set (subformulae F) \<and> H \<in> set (subformulae F)"
  "\<^bold>\<not> G \<in> set (subformulae F) \<Longrightarrow> G \<in> set (subformulae F)"
  by(fastforce elim: subsubformulae)+

lemma length_subformulae: "length (subformulae F) = size F" by(induction F; simp)

subsection\<open>Derived Connectives\<close>
    
definition Top ("\<top>") where
"\<top> \<equiv> \<bottom> \<^bold>\<rightarrow> \<bottom>"
lemma top_atoms_simp[simp]: "atoms \<top> = {}" unfolding Top_def by simp

primrec BigAnd :: "('p, 'v, 'ty) formula list \<Rightarrow> ('p, 'v, 'ty) formula" ("\<^bold>\<And>_") where
"\<^bold>\<And>Nil = (\<^bold>\<not>\<bottom>)" \<comment> \<open>essentially, it doesn't matter what I use here. But since I want to use this in CNFs, implication is not a nice thing to have.\<close> |
"\<^bold>\<And>(F#Fs) = F \<^bold>\<and> \<^bold>\<And>Fs"

lemma atoms_BigAnd[simp]: "atoms (\<^bold>\<And>Fs) = \<Union>(atoms ` set Fs)"
  by(induction Fs; simp)

primrec BigOr :: "('p, 'v, 'ty) formula list \<Rightarrow> ('p, 'v, 'ty) formula" ("\<^bold>\<Or>_") where
"\<^bold>\<Or>Nil = \<bottom>" |
"\<^bold>\<Or>(F#Fs) = F \<^bold>\<or> \<^bold>\<Or>Fs"


locale formula_syntax =
  fixes subst ::"'v \<Rightarrow> 'c \<Rightarrow> 'p \<Rightarrow> 'p"
    and vars  ::"'p \<Rightarrow> 'v set"
  assumes subst_subst_all: "v \<notin> vars (subst v c p)"
begin
fun fsubst::"'v \<Rightarrow> 'c \<Rightarrow> ('p, 'v, 'ty) formula \<Rightarrow> ('p, 'v, 'ty) formula" where
  "fsubst v c (Atom p) = Atom (subst v c p)" |
  "fsubst _ _ \<bottom> = \<bottom>" |
  "fsubst v c (Not \<phi>\<^sub>1) = Not (fsubst v c \<phi>\<^sub>1)" |
  "fsubst v c (And \<phi>\<^sub>1 \<phi>\<^sub>2) = And (fsubst v c \<phi>\<^sub>1) (fsubst v c \<phi>\<^sub>2)" |
  "fsubst v c (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = Or (fsubst v c \<phi>\<^sub>1) (fsubst v c \<phi>\<^sub>2)" |
  "fsubst v c (Imp \<phi>\<^sub>1 \<phi>\<^sub>2) = Imp (fsubst v c \<phi>\<^sub>1) (fsubst v c \<phi>\<^sub>2)" |
  "fsubst v c (Exists t x \<phi>\<^sub>1) = (if x = v then Exists t x \<phi>\<^sub>1 else Exists t x (fsubst v c \<phi>\<^sub>1))" |
  "fsubst v c (All t x \<phi>\<^sub>1) = (if x = v then All t x \<phi>\<^sub>1 else All t x (fsubst v c \<phi>\<^sub>1))"

fun free_vars::"('p, 'v, 'ty) formula \<Rightarrow> 'v set" where
  "free_vars (Atom p) = vars p" 
| "free_vars Bot = {}"
| "free_vars (Not \<phi>\<^sub>1) = free_vars \<phi>\<^sub>1"
| "free_vars (And \<phi>\<^sub>1 \<phi>\<^sub>2) = free_vars \<phi>\<^sub>1 \<union> free_vars \<phi>\<^sub>2"
| "free_vars (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = free_vars \<phi>\<^sub>1 \<union> free_vars \<phi>\<^sub>2"
| "free_vars (Imp \<phi>\<^sub>1 \<phi>\<^sub>2) = free_vars \<phi>\<^sub>1 \<union> free_vars \<phi>\<^sub>2"
| "free_vars (Exists t x \<phi>\<^sub>1) = free_vars \<phi>\<^sub>1 - {x}"
| "free_vars (All t x \<phi>\<^sub>1) = free_vars \<phi>\<^sub>1 - {x}"

(* these are not bound variables in the typical sense, but those that exist as bound variables
    somewhere down the syntax tree *)
fun bound_vars::"('p, 'v, 'ty) formula \<Rightarrow> 'v set" where
  "bound_vars (Atom p) = {}"
| "bound_vars Bot = {}"
| "bound_vars (Not \<phi>\<^sub>1) = bound_vars \<phi>\<^sub>1"
| "bound_vars (And \<phi>\<^sub>1 \<phi>\<^sub>2) = bound_vars \<phi>\<^sub>1 \<union> bound_vars \<phi>\<^sub>2"
| "bound_vars (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = bound_vars \<phi>\<^sub>1 \<union> bound_vars \<phi>\<^sub>2"
| "bound_vars (Imp \<phi>\<^sub>1 \<phi>\<^sub>2) = bound_vars \<phi>\<^sub>1 \<union> bound_vars \<phi>\<^sub>2"
| "bound_vars (Exists t x \<phi>) = (free_vars \<phi> \<inter> {x}) \<union> bound_vars \<phi>"
| "bound_vars (All t x \<phi>) = (free_vars \<phi> \<inter> {x}) \<union> bound_vars \<phi>"

lemma fsubst_subst_free: "v \<notin> free_vars (fsubst v c f)"
  by (induction f) (auto simp: subst_subst_all)

lemma fsubst_leaves_bound: "v \<in> bound_vars f \<Longrightarrow> v \<in> bound_vars (fsubst v c f)"
  by (induction f) auto
end
end
