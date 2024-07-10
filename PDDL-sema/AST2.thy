theory AST2
  imports AST1
begin


type_synonym time = rat

(* Time-annotated condition, which should be evaluated against a sequence of states *)
datatype ('x, 'a) fixed_GD = 
  Over time time "('x, 'a) pref_GD"
  | At time "('x, 'a) pref_GD"

datatype ('x, 'a) pref_fixed_GD =
  PrefFixedGD pref "('x, 'a) fixed_GD"
  | FixedGD "('x, 'a) fixed_GD"

datatype ('x, 'a) fixed_da_GD =
  ForAll 'x "('x, 'a) fixed_da_GD"
  | And "('x, 'a) fixed_da_GD" "('x, 'a) fixed_da_GD"
  | tGD "('x, 'a) pref_fixed_GD"

text \<open>Preferences can be compiled away, since they do not affect the truth-value 
of formulas. Note: preferences cannot occur in preconditions to effects\<close>

datatype ('x, 'a) fixed_GD' =
  Over time time "('x, 'a) GD"
  | At time "('x, 'a) GD"

datatype ('x, 'a) fixed_da_GD' =
  ForAll 'x "('x, 'a) fixed_da_GD'"
  | And "('x, 'a) fixed_da_GD'" "('x, 'a) fixed_da_GD'"
  | tGD "('x, 'a) fixed_GD'"

(* Simple update to a state at a certain time *)
type_synonym 'ent timed_update = "(time \<times> 'ent simple_update)"

(* Continuous update to some function symbol *)
type_synonym 'ent timed_continuous_effect = "time \<times> time \<times> func \<times> symbol term list \<times> symbol term f_exp_t"

datatype 'ent fixed_timed_effect =
  EffAt "'ent timed_update"
  | EffCont "'ent timed_continuous_effect"

(* We use this to represent a durative effect, of which the start and end are known *)
datatype ('x, 'ent) fixed_durative_effect = 
  FTE "'ent fixed_timed_effect"
  | TWhen "('x, 'ent atom) fixed_da_GD'" "'ent fixed_timed_effect"
  | TAnd "('x, 'ent) fixed_durative_effect" "('x, 'ent) fixed_durative_effect"
  | TAll "'x" "('x, 'ent) fixed_durative_effect"

datatype ('x, 'ent) fixed_timed_action =
  FTA (prec: "('x, 'ent atom) fixed_da_GD")
    (eff: "('x, 'ent) fixed_durative_effect")

type_synonym e_simple_update = "symbol term simple_update"
type_synonym e_effect = "(variable \<times> type, symbol term) fixed_durative_effect"
type_synonym e_action = "(variable \<times> type, symbol term) fixed_timed_action"
type_synonym e_timed_form = "(variable \<times> type, symbol term atom) fixed_GD'"
type_synonym e_cond_form = "(variable \<times> type, symbol term atom) fixed_da_GD'"
type_synonym e_form = "(variable \<times> type, symbol term atom) GD"

section \<open>Semantics of formulas\<close>
text \<open>Formulas and their terms are evaluated against a state. 
  We must also fix a domain. An attempt is made to capture unknown values as \<^term>\<open>None\<close>\<close>

locale formulas =
  fixes dom::"type \<Rightarrow> object set"
    and derived_preds::"pred \<rightharpoonup> ((variable \<times> type) list \<times> e_form)"
begin
  datatype applicable_of_upd = AOFU func "object option list" (return_value: "object option")
  datatype applicable_nf_upd = ANFU upd_op func "object option list" "rat option"
  
  type_synonym object_function_interpretation = "func \<rightharpoonup> (object list \<rightharpoonup> object)"
  type_synonym numeric_function_interpretation = "func \<rightharpoonup> (object list \<rightharpoonup> rat)"
  
  datatype state = State 
    (true_preds: "object atom set")
    (false_preds: "object atom set")
    (of_int: object_function_interpretation)
    (nf_int: numeric_function_interpretation)
    (var_int: "variable \<rightharpoonup> object")
  
  fun sym_val::"state \<Rightarrow> symbol \<Rightarrow> object option" where
    "sym_val s (Var v) = (var_int s) v"
  | "sym_val _ (Const c) = Some c"
  
  fun term_val::"state \<Rightarrow> symbol term \<Rightarrow> object option" where
  "term_val s (Sym x) = sym_val s x"
    | "term_val s (Fun fun as) = (case (of_int s fun) of
        Some f \<Rightarrow> (let arg_vals = map (\<lambda>t. term_val s t) as
          in (if (list_all (\<lambda>x. x \<noteq> None) arg_vals) 
              then f (map the arg_vals) else None))
      | None \<Rightarrow> None)"
  
  fun f_exp_val::"state \<Rightarrow> symbol term f_exp \<Rightarrow> rat option" where
      "f_exp_val s (f_exp.NFun fun as) = (case (nf_int s fun) of 
        Some f  \<Rightarrow> (let arg_vals = map (\<lambda>t. term_val s t) as
          in (if (list_all (\<lambda>x. x \<noteq> None) arg_vals) 
              then f (map the arg_vals) else None)) 
      | None    \<Rightarrow> None)"
    | "f_exp_val s (f_exp.Num n) = Some n"
    | "f_exp_val s (f_exp.Add x y) = (combine_options plus (f_exp_val s x) (f_exp_val s y))"
    | "f_exp_val s (f_exp.Sub x y) = (combine_options minus (f_exp_val s x) (f_exp_val s y))"
    | "f_exp_val s (f_exp.Mult x y) = (combine_options times (f_exp_val s x) (f_exp_val s y))"
    | "f_exp_val s (f_exp.Div x y) = (
        let 
          x' = f_exp_val s x;
          y' = f_exp_val s y
        in 
        if (y' = Some 0) 
        then None 
        else combine_options divide x' y')"
    | "f_exp_val s (f_exp.Neg x) = (map_option (\<lambda>x. 0 - x) (f_exp_val s x))"


  definition asmt where
    "asmt ps as = (map_of (zip (map fst ps) as))"

  (* terminates under some well-formedness conditions for derived predicates *)
  function atom_val::"state \<Rightarrow> symbol term atom \<Rightarrow> bool option" 
       and form_val::"state \<Rightarrow> e_form \<Rightarrow> bool option" where
    "atom_val (State tp fp oi ni vi) (Pred p as) = (
      let arg_vals = map (\<lambda>t. term_val (State tp fp oi ni vi) t) as
      in (
        if (list_all (\<lambda>x. x \<noteq> None) arg_vals) 
        then (
          let args = (map the arg_vals)
          in (
            if ((Pred p args) \<in> tp)
            then (Some True)
            else (
              if ((Pred p args) \<in> fp)
              then Some False
              else case derived_preds p of 
                Some (ps, f) \<Rightarrow> form_val (State tp fp oi ni (asmt ps args)) f
              | None         \<Rightarrow> None
            )
          )
        )
        else None
      )
    )"
  | "atom_val s (Ent_Eq a b) = (
      case (term_val s a, term_val s b) of
        (Some a', Some b') \<Rightarrow> Some (a' = b')
      | _                  \<Rightarrow> None
    )"
  | "atom_val s (Num_Eq a b) = (
      case (f_exp_val s a, f_exp_val s b) of
        (Some a', Some b') \<Rightarrow> Some (a' = b')
      | _                  \<Rightarrow> None
    )"
  | "atom_val s (Num_Le a b) = (
      case (f_exp_val s a, f_exp_val s b) of
        (Some a', Some b') \<Rightarrow> Some (a' \<le> b')
      | _                  \<Rightarrow> None
    )"
  | "atom_val s (Num_Lt a b) = (
      case (f_exp_val s a, f_exp_val s b) of
        (Some a', Some b') \<Rightarrow> Some (a' < b')
      | _                  \<Rightarrow> None
    )"
  | "form_val s GD.Bot = Some False"
  | "form_val s (GD.Atom a) = atom_val s a" 
  | "form_val s (GD.Not x) = map_option (\<lambda>x. \<not>x) (form_val s x)"
  | "form_val s (GD.And x y) = combine_options (\<and>) (form_val s x) (form_val s y)"
  | "form_val s (GD.Or x y) = combine_options (\<or>) (form_val s x) (form_val s y)"
  | "form_val s (GD.Imp x y) = combine_options (\<longrightarrow>) (form_val s x) (form_val s y)"
  | "form_val (State tp fp oi ni vi) (GD.ForAll (v, t) x) = (
      if (\<forall>obj \<in> (dom t). (form_val (State tp fp oi ni (vi(v \<mapsto> obj))) x) = Some True)
      then Some True
      else (
        if (\<exists>obj \<in> (dom t). (form_val (State tp fp oi ni (vi(v \<mapsto> obj))) x) = Some False)
        then Some False
        else None
      )
    )"
  | "form_val (State tp fp oi ni vi) (GD.Exists (v, t) x) = (
      if (\<exists>obj \<in> (dom t). (form_val (State tp fp oi ni (vi(v \<mapsto> obj))) x) = Some True)
      then Some True
      else (
        if (\<exists>obj \<in> (dom t). (form_val (State tp fp oi ni (vi(v \<mapsto> obj))) x) = None)
        then None
        else Some False
      )
    )"
    by (pat_completeness) auto
  (* to do: termination *)
end


  type_synonym object_function_interpretation = "object term \<rightharpoonup> object term"
  type_synonym numeric_function_interpretation = "(func \<times> object term list) \<rightharpoonup> object term f_exp"
  
  datatype state = State 
    (true_preds: "object atom set")
    (false_preds: "object atom set")
    (of_int: object_function_interpretation)
    (nf_int: numeric_function_interpretation)
    (var_int: "variable \<rightharpoonup> object")

locale term_eq =
  fixes ofs::object_function_interpretation
begin
inductive int::"object term \<Rightarrow> object term \<Rightarrow> bool" where
  "(t1, t2) \<in> Map.graph ofs \<Longrightarrow> int t1 t2"
| "(t1, t2) \<in> Map.graph ofs \<Longrightarrow> int t2 t1"

definition "term_eq \<equiv> (int\<^sup>*\<^sup>*)"

end

locale formulas1 =
  fixes dom::"type \<Rightarrow> object set"
    and derived_preds::"pred \<rightharpoonup> ((variable \<times> type) list \<times> e_form)"
    and s::state
  where 
begin

(* object terms are ground terms *)
  
  fun sym_val::"state \<Rightarrow> symbol \<Rightarrow> object option" where
    "sym_val s (Var v) = (var_int s) v"
  | "sym_val _ (Const c) = Some c"
  
  fun term_val::"state \<Rightarrow> symbol term \<Rightarrow> object option" where
    "term_val s (Sym x) = sym_val s x"
  | "term_val s (Fun fun as) = (
    let arg_vals = map (\<lambda>t. term_val s t) as
    in (
      if (list_all (\<lambda>x. x \<noteq> None) arg_vals)
      then
      else
    case (of_int s (fun, as)) of
        Some term \<Rightarrow> (if (list_all (\<lambda>x. x \<noteq> None) arg_vals) 
              then f (map the arg_vals) else None)
      | None \<Rightarrow> None))"
  
  fun f_exp_val::"state \<Rightarrow> symbol term f_exp \<Rightarrow> rat option" where
      "f_exp_val s (f_exp.NFun fun as) = (case (nf_int s fun) of 
        Some f  \<Rightarrow> (let arg_vals = map (\<lambda>t. term_val s t) as
          in (if (list_all (\<lambda>x. x \<noteq> None) arg_vals) 
              then f (map the arg_vals) else None)) 
      | None    \<Rightarrow> None)"
    | "f_exp_val s (f_exp.Num n) = Some n"
    | "f_exp_val s (f_exp.Add x y) = (combine_options plus (f_exp_val s x) (f_exp_val s y))"
    | "f_exp_val s (f_exp.Sub x y) = (combine_options minus (f_exp_val s x) (f_exp_val s y))"
    | "f_exp_val s (f_exp.Mult x y) = (combine_options times (f_exp_val s x) (f_exp_val s y))"
    | "f_exp_val s (f_exp.Div x y) = (
        let 
          x' = f_exp_val s x;
          y' = f_exp_val s y
        in 
        if (y' = Some 0) 
        then None 
        else combine_options divide x' y')"
    | "f_exp_val s (f_exp.Neg x) = (map_option (\<lambda>x. 0 - x) (f_exp_val s x))"


  definition asmt where
    "asmt ps as = (map_of (zip (map fst ps) as))"

  (* terminates under some well-formedness conditions for derived predicates *)
  function atom_val::"state \<Rightarrow> symbol term atom \<Rightarrow> bool option" 
       and form_val::"state \<Rightarrow> e_form \<Rightarrow> bool option" where
    "atom_val (State tp fp oi ni vi) (Pred p as) = (
      let arg_vals = map (\<lambda>t. term_val (State tp fp oi ni vi) t) as
      in (
        if (list_all (\<lambda>x. x \<noteq> None) arg_vals) 
        then (
          let args = (map the arg_vals)
          in (
            if ((Pred p args) \<in> tp)
            then (Some True)
            else (
              if ((Pred p args) \<in> fp)
              then Some False
              else case derived_preds p of 
                Some (ps, f) \<Rightarrow> form_val (State tp fp oi ni (asmt ps args)) f
              | None         \<Rightarrow> None
            )
          )
        )
        else None
      )
    )"
  | "atom_val s (Ent_Eq a b) = (
      case (term_val s a, term_val s b) of
        (Some a', Some b') \<Rightarrow> Some (a' = b')
      | _                  \<Rightarrow> None
    )"
  | "atom_val s (Num_Eq a b) = (
      case (f_exp_val s a, f_exp_val s b) of
        (Some a', Some b') \<Rightarrow> Some (a' = b')
      | _                  \<Rightarrow> None
    )"
  | "atom_val s (Num_Le a b) = (
      case (f_exp_val s a, f_exp_val s b) of
        (Some a', Some b') \<Rightarrow> Some (a' \<le> b')
      | _                  \<Rightarrow> None
    )"
  | "atom_val s (Num_Lt a b) = (
      case (f_exp_val s a, f_exp_val s b) of
        (Some a', Some b') \<Rightarrow> Some (a' < b')
      | _                  \<Rightarrow> None
    )"
  | "form_val s GD.Bot = Some False"
  | "form_val s (GD.Atom a) = atom_val s a" 
  | "form_val s (GD.Not x) = map_option (\<lambda>x. \<not>x) (form_val s x)"
  | "form_val s (GD.And x y) = combine_options (\<and>) (form_val s x) (form_val s y)"
  | "form_val s (GD.Or x y) = combine_options (\<or>) (form_val s x) (form_val s y)"
  | "form_val s (GD.Imp x y) = combine_options (\<longrightarrow>) (form_val s x) (form_val s y)"
  | "form_val (State tp fp oi ni vi) (GD.ForAll (v, t) x) = (
      if (\<forall>obj \<in> (dom t). (form_val (State tp fp oi ni (vi(v \<mapsto> obj))) x) = Some True)
      then Some True
      else (
        if (\<exists>obj \<in> (dom t). (form_val (State tp fp oi ni (vi(v \<mapsto> obj))) x) = Some False)
        then Some False
        else None
      )
    )"
  | "form_val (State tp fp oi ni vi) (GD.Exists (v, t) x) = (
      if (\<exists>obj \<in> (dom t). (form_val (State tp fp oi ni (vi(v \<mapsto> obj))) x) = Some True)
      then Some True
      else (
        if (\<exists>obj \<in> (dom t). (form_val (State tp fp oi ni (vi(v \<mapsto> obj))) x) = None)
        then None
        else Some False
      )
    )"
    by (pat_completeness) auto
end

end