theory Util
  imports Main
begin
context comp_fun_commute_on
begin

find_theorems name: "local*fold"
thm fold_fun_left_comm

lemma list_fold_left_comm:
  assumes "set (x # xs) \<subseteq> S"
  shows "f x (fold f xs B) = fold f xs (f x B)"
  using assms
proof (induction xs arbitrary: B)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "f x (fold f (a # xs) B) = f x (fold f xs (f a B))"
    by simp            
  also have "... = fold f xs (f x (f a B))" using Cons by simp
  also have "... = fold f xs (f a (f x B))" 
    using Cons 
    apply (subst comp_apply[of "f x" "f a", symmetric])
    apply (subst comp_fun_commute_on[where x = a and y = x])
    by auto
  finally show ?case by simp
qed

lemma fold_rev:
  assumes "set xs \<subseteq> S"
  shows "fold f xs = fold f (rev xs)"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have "fold f (x # xs) = f x o (fold f xs)" 
    using list_fold_left_comm Cons by auto
  also have "... = f x o (fold f (rev xs))" using Cons by auto
  also have "... = f x o (fold id (map f (rev xs)))" 
    apply (subst fold_map[of id, simplified id_comp, symmetric])
    ..
  also have "... = (id (f x)) o (fold id (map f (rev xs)))" by simp
  also have "... = fold id (map f ((rev xs)@[x]))" by simp
  finally show ?case 
    apply (subst rev.simps(2))
    apply (subst (asm) fold_map[of id, simplified id_comp])
    by simp
qed
end


end