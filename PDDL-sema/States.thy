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
  and ty_dom::"type \<Rightarrow> object list"

begin
text \<open>The variables in a symbol\<close>
fun sym_vars where
  "sym_vars (Var x) = {x}" 
| "sym_vars (Const c) = {}"

fun term_vars::"symbol term \<Rightarrow> variable set" where
  "term_vars (Sym x) = sym_vars x"
| "term_vars (Fun f as) = fold (\<union>) (map term_vars as) {}"

fun f_exp_vars::"symbol term f_exp \<Rightarrow> variable set" where
    "f_exp_vars (f_exp.NFun f as) = fold (\<union>) (map term_vars as) {}"
  | "f_exp_vars (f_exp.Num n) = {}"
  | "f_exp_vars (f_exp.Neg e) = f_exp_vars e"
  | "f_exp_vars (f_exp.Add a b) = f_exp_vars a \<union> f_exp_vars b"
  | "f_exp_vars (f_exp.Sub a b) = f_exp_vars a \<union> f_exp_vars b"
  | "f_exp_vars (f_exp.Mult a b) = f_exp_vars a \<union> f_exp_vars b"
  | "f_exp_vars (f_exp.Div a b) = f_exp_vars a \<union> f_exp_vars b"

fun atom_vars::"symbol term atom \<Rightarrow> variable set" where
  "atom_vars (Pred p as) = fold (\<union>) (map term_vars as) {}"
| "atom_vars (Ent_Eq a b) = term_vars a \<union> term_vars b"
| "atom_vars (Num_Eq a b) = f_exp_vars a \<union> f_exp_vars b"
| "atom_vars (Num_Le a b) = f_exp_vars a \<union> f_exp_vars b"
| "atom_vars (Num_Lt a b) = f_exp_vars a \<union> f_exp_vars b"

fun f_vars::"((variable \<times> 'x) list, symbol term atom) GD \<Rightarrow> variable set" where
  "f_vars (GD.Atom a) = atom_vars a"
| "f_vars GD.Bot = {}"
| "f_vars (GD.Not f) = f_vars f"
| "f_vars (GD.Or f g) = f_vars f \<union> f_vars g"
| "f_vars (GD.And f g) = f_vars f \<union> f_vars g"
| "f_vars (GD.Imp f g) = f_vars f \<union> f_vars g"
| "f_vars (GD.ForAll vts f) = f_vars f - (set (map fst vts))"
| "f_vars (GD.Exists vts f) = f_vars f - (set (map fst vts))"

fun f_vars'::"(variable \<times> 'x, symbol term atom) GD \<Rightarrow> variable set" where
  "f_vars' (GD.Atom a) = atom_vars a"
| "f_vars' GD.Bot = {}"
| "f_vars' (GD.Not f) = f_vars' f"
| "f_vars' (GD.Or f g) = f_vars' f \<union> f_vars' g"
| "f_vars' (GD.And f g) = f_vars' f \<union> f_vars' g"
| "f_vars' (GD.Imp f g) = f_vars' f \<union> f_vars' g"
| "f_vars' (GD.ForAll (v, os) f) = f_vars' f - {v}"
| "f_vars' (GD.Exists (v, os) f) = f_vars' f - {v}"

fun ground_GD_sem::"(unit, object term atom) GD \<Rightarrow> bool option" where
  "ground_GD_sem (GD.Atom a)   = atom_sem a"
| "ground_GD_sem GD.Bot        = Some False"
| "ground_GD_sem (GD.Not gd)   = map_option (\<lambda>x. \<not>x) (ground_GD_sem gd)"
| "ground_GD_sem (GD.And x y)  = combine_options (\<lambda>x y. x \<and> y) (ground_GD_sem x) (ground_GD_sem y)"
| "ground_GD_sem (GD.Or x y)   = 
    (case (ground_GD_sem x, ground_GD_sem y) of 
      (Some True, _)            \<Rightarrow> Some True
    | (_, Some True)            \<Rightarrow> Some True
    | (Some False, Some False)  \<Rightarrow> Some False
    | _                         \<Rightarrow> None)"
| "ground_GD_sem (GD.Imp x y)   = 
    (case (ground_GD_sem x, ground_GD_sem y) of
      (_, Some True)            \<Rightarrow> Some True
    | (Some False, _)           \<Rightarrow> Some True
    | (Some x', Some y')        \<Rightarrow> Some (\<not>x' \<or> y')
    | _                         \<Rightarrow> None)"
| "ground_GD_sem (GD.ForAll _ _) = None"
| "ground_GD_sem (GD.Exists _ _) = None"

fun BigAnd::"('a, 'b) GD list \<Rightarrow> ('a, 'b) GD" where
  "BigAnd [] = (GD.Not (GD.Bot))"
| "BigAnd (f#fs) = GD.And f (BigAnd fs)"

fun BigOr::"('a, 'b) GD list \<Rightarrow> ('a, 'b) GD" where
  "BigOr [] = GD.Bot"
| "BigOr (f#fs) = GD.Or f (BigOr fs)"

  fun subst_sym_with_obj where
    "subst_sym_with_obj psubst (Var x) = psubst x"
  | "subst_sym_with_obj psubst (Const c) = c"

fun ground_GD::"(symbol \<Rightarrow> object) \<Rightarrow> (variable \<times> (object list), symbol term atom) GD \<Rightarrow> (unit, object term atom) GD" where
  "ground_GD f (GD.Atom a) = GD.Atom (map_atom (map_term f) a)"
| "ground_GD f GD.Bot = GD.Bot"
| "ground_GD f (GD.Not x) = GD.Not (ground_GD f x)"
| "ground_GD f (GD.And x y) = GD.And (ground_GD f x) (ground_GD f y)"
| "ground_GD f (GD.Or x y) = GD.Or (ground_GD f x) (ground_GD f y)"
| "ground_GD f (GD.Imp x y) = GD.Imp (ground_GD f x) (ground_GD f y)"
| "ground_GD f (GD.ForAll (v, os) x) = (if (v \<notin> f_vars' x \<and> os \<noteq> []) then ground_GD f x else BigAnd (map (\<lambda>obj. ground_GD (f((Var v):=obj)) x) os))"
| "ground_GD f (GD.Exists (v, os) x) = (if (v \<notin> f_vars' x \<and> os \<noteq> []) then ground_GD f x else BigOr (map (\<lambda>obj. ground_GD (f((Var v):=obj)) x) os))"

abbreviation replace_types_with_objects where
  "replace_types_with_objects \<equiv> map_GD (\<lambda>(v, t). (v, ty_dom t)) id"

fun split_quant::"(('a \<times> 'b) list, 'c) GD \<Rightarrow> ('a \<times> 'b, 'c) GD" where
  "split_quant (GD.Atom a) = GD.Atom a"
| "split_quant GD.Bot = GD.Bot"
| "split_quant (GD.Not x) = GD.Not (split_quant x)"
| "split_quant (GD.And x y) = GD.And (split_quant x) (split_quant y)"
| "split_quant (GD.Or x y) = GD.Or (split_quant x) (split_quant y)"
| "split_quant (GD.Imp x y) = GD.Imp (split_quant x) (split_quant y)"
| "split_quant (GD.ForAll vs x) = fold (\<lambda>v x. GD.ForAll v x) vs (split_quant x)"
| "split_quant (GD.Exists vs x) = fold (\<lambda>v x. GD.Exists v x) vs (split_quant x)"

definition GD_sem::"(symbol \<Rightarrow> object) \<Rightarrow> ((variable \<times> type) list, symbol term atom) GD \<Rightarrow> bool option" where
  "GD_sem f \<phi> = ground_GD_sem (ground_GD f (replace_types_with_objects (split_quant \<phi>)))"

end

end