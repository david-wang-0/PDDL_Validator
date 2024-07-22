theory States
  imports Terms
begin


  type_synonym 'sym num_fun_interpretation = "'sym term f_exp \<rightharpoonup> 'sym term f_exp"
  datatype 'sym state = 
    State (term_int: "'sym function_interpretation") 
          (num_term_int: "'sym num_fun_interpretation")
          (true_preds: "'sym term atom set") 
          (false_preds: "'sym term atom set")


fun nf_f_exp::"'sym function_interpretation \<Rightarrow> 'sym num_fun_interpretation \<Rightarrow> 'sym term f_exp \<Rightarrow> bool" where
"nf_f_exp fi nfi e = (
  nfi e = None
\<and> (case e of 
    (f_exp.NFun f as) \<Rightarrow> list_all (nf_term fi) as
  | (f_exp.Num _)     \<Rightarrow> True
  | (f_exp.Neg a)     \<Rightarrow> nf_f_exp fi nfi a
  | (f_exp.Add a b)   \<Rightarrow> nf_f_exp fi nfi a \<and> nf_f_exp fi nfi b
  | (f_exp.Sub a b)   \<Rightarrow> nf_f_exp fi nfi a \<and> nf_f_exp fi nfi b
  | (f_exp.Mult a b)   \<Rightarrow> nf_f_exp fi nfi a \<and> nf_f_exp fi nfi b
  | (f_exp.Div a b)   \<Rightarrow> nf_f_exp fi nfi a \<and> nf_f_exp fi nfi b
))"


abbreviation n_nfi::"'sym function_interpretation \<Rightarrow>'sym num_fun_interpretation \<Rightarrow> bool" where
  "n_nfi fi nfi \<equiv> (\<forall>(l, r) \<in> Map.graph nfi. nf_f_exp fi nfi l \<and> nf_f_exp fi nfi r)"

locale atom_sem = decidable_eq fi
  for fi::"'sym function_interpretation" +
  fixes nfi::"'sym num_fun_interpretation"
    and tp::"'sym term atom set"
    and fp::"'sym term atom set"
  assumes nf_nfi: "n_nfi fi nfi"
      and nf_tp: "\<forall>a \<in> tp. \<forall>t \<in> (atom.ent a). nf_term fi t"
      and nf_fp: "\<forall>a \<in> fp. \<forall>t \<in> (atom.ent a). nf_term fi t"
begin

(* Arithmetic simplifications could be applied here but are not. *)
fun eval_f_exp::"'sym term f_exp \<Rightarrow> 'sym term f_exp" where
  "eval_f_exp (f_exp.NFun f as) = (
      let as' = map normalise_term  as
      in (case nfi (f_exp.NFun f as') of
        Some v  \<Rightarrow> v
      | None    \<Rightarrow> f_exp.NFun f as')
    )"
| "eval_f_exp (f_exp.Num n) = f_exp.Num n"
| "eval_f_exp (f_exp.Neg x) =
    (case x of
      f_exp.Num n   \<Rightarrow> f_exp.Num (-n)
    | x             \<Rightarrow> f_exp.Neg x)"
| "eval_f_exp (f_exp.Add a b) = 
    (case (a, b) of
      (f_exp.Num a', f_exp.Num b')  \<Rightarrow> f_exp.Num (a' + b')
    | (a, b)                        \<Rightarrow> f_exp.Add a b)"
| "eval_f_exp (f_exp.Sub a b) = 
    (case (a, b) of
      (f_exp.Num a', f_exp.Num b')  \<Rightarrow> f_exp.Num (a' - b')
    | (a, b)                        \<Rightarrow> f_exp.Sub a b)"
| "eval_f_exp (f_exp.Mult a b) = 
    (case (a, b) of
      (f_exp.Num a', f_exp.Num b')  \<Rightarrow> f_exp.Num (a' * b')
    | (a, b)                        \<Rightarrow> f_exp.Mult a b)"
| "eval_f_exp (f_exp.Div a b) = 
    (case (a, b) of
      (f_exp.Num a', f_exp.Num b')  \<Rightarrow> if (b' \<noteq> 0) then f_exp.Num (a' / b') else f_exp.Div a b
    | (a, b)                        \<Rightarrow> f_exp.Div a b)"


(* We could capture more cases of numeric (in-)equalities using rewrite rules, 
    but they are not trivial *)
fun atom_sem::"'sym term atom \<Rightarrow> bool option" where
  "atom_sem (Ent_Eq a b) = (if (check_eq a b) then Some True else None)"
| "atom_sem (Num_Eq a b) = 
    (case (eval_f_exp a, eval_f_exp b) of
      (f_exp.Num a', f_exp.Num b')  \<Rightarrow> Some (a' = b')
    | (a', b')                      \<Rightarrow> if (a' = b') then Some True else None)"
| "atom_sem (Num_Le a b) = 
    (case (eval_f_exp a, eval_f_exp b) of
      (f_exp.Num a', f_exp.Num b')  \<Rightarrow> Some (a' \<le> b')
    | (a', b')                      \<Rightarrow> if (a' = b') then Some True else None)"
| "atom_sem (Num_Lt a b) = 
    (case (eval_f_exp a, eval_f_exp b) of
      (f_exp.Num a', f_exp.Num b')  \<Rightarrow> Some (a' < b')
    | (a', b')                      \<Rightarrow> if (a' = b') then Some False else None)"
| "atom_sem (Pred p as) = 
    (let as' = map normalise_term as in
      if      (Pred p as') \<in> tp then Some True 
      else if (Pred p as') \<in> fp then Some False 
      else None)"
end

locale form_sem = atom_sem fi nfi tp fp
  for fi::"object function_interpretation"
  and nfi::"object num_fun_interpretation"
  and tp::"object term atom set"
  and fp::"object term atom set"
  and ty_dom::"type \<Rightarrow> object set"
begin

find_consts name: "Set*fold"

  definition all::"variable \<Rightarrow> type \<Rightarrow> schematic_formula \<Rightarrow> schematic_formula" ("\<^bold>\<forall>_ - _._") where
    "all v t \<phi> \<equiv> (if (v \<notin> f_vars \<phi> \<and> (t_dom t \<noteq> [])) then \<phi> else \<^bold>\<And>(map (\<lambda>c. f_subst v c \<phi>) (t_dom t)))"
                                                                  
  definition exists::"variable \<Rightarrow> type \<Rightarrow> schematic_formula \<Rightarrow> schematic_formula" ("\<^bold>\<exists>_ - _._") where
    "exists v t \<phi> \<equiv> (if (v \<notin> f_vars \<phi> \<and> (t_dom t \<noteq> [])) then \<phi> else \<^bold>\<Or>(map (\<lambda>c. f_subst v c \<phi>) (t_dom t)))"

fun GD_sem::"(unit, object term atom) GD \<Rightarrow> bool option" where
  "GD_sem (GD.Atom a)   = atom_sem a"
| "GD_sem GD.Bot        = Some False"
| "GD_sem (GD.Not gd)   = map_option (\<lambda>x. \<not>x) (GD_sem gd)"
| "GD_sem (GD.And x y)  = combine_options (\<lambda>x y. x \<and> y) (GD_sem x) (GD_sem y)"
| "GD_sem (GD.Or x y)   = 
    (case (GD_sem x, GD_sem y) of 
      (Some True, _)            \<Rightarrow> Some True
    | (_, Some True)            \<Rightarrow> Some True
    | (Some False, Some False)  \<Rightarrow> Some False
    | _                         \<Rightarrow> None)"
| "GD_sem (GD.Imp x y)   = 
    (case (GD_sem x, GD_sem y) of
      (_, Some True)            \<Rightarrow> Some True
    | (Some False, _)           \<Rightarrow> Some True
    | (Some x', Some y')        \<Rightarrow> Some (\<not>x' \<or> y')
    | _                         \<Rightarrow> None)"

fun GD_sem::"('sym \<Rightarrow> object) \<Rightarrow> (('sym \<times> type) list, 'sym term atom) GD \<Rightarrow> bool option" where
  "GD_sem f (GD.Atom a)   = atom_sem (map_atom (map_term f) a)"
| "GD_sem f GD.Bot        = Some False"
| "GD_sem f (GD.Not gd)   = map_option (\<lambda>x. \<not>x) (GD_sem f gd)"
| "GD_sem f (GD.And x y)  = combine_options (\<lambda>x y. x \<and> y) (GD_sem f x) (GD_sem f y)"
| "GD_sem f (GD.Or x y)   = 
    (case (GD_sem f x, GD_sem f y) of 
      (Some True, _)            \<Rightarrow> Some True
    | (_, Some True)            \<Rightarrow> Some True
    | (Some False, Some False)  \<Rightarrow> Some False
    | _                         \<Rightarrow> None)"
| "GD_sem f (GD.Imp x y)   = 
    (case (GD_sem f x, GD_sem f y) of
      (_, Some True)            \<Rightarrow> Some True
    | (Some False, _)           \<Rightarrow> Some True
    | (Some x', Some y')        \<Rightarrow> Some (\<not>x' \<or> y')
    | _                         \<Rightarrow> None)"

end

end