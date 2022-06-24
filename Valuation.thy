theory Valuation imports NTerm Algebra Locales
begin

section \<open>Valuation\<close>

subsection \<open>Valuations\<close>

type_synonym 'a valuation = "(variable \<times> nat) \<Rightarrow> 'a operation"

definition update_valuation :: "'a valuation \<Rightarrow> variable list \<Rightarrow> 'a list \<Rightarrow> 'a valuation" 
  ("_{_ := _}" [1000, 51, 51] 1000)
where
  "\<upsilon>{xs := us} = (\<lambda> (x, n). 
     (if n = 0 then 
       (case index_of x xs of
          Some i \<Rightarrow> value_op (us!i)
        | None \<Rightarrow> \<upsilon> (x, 0))
      else \<upsilon> (x, n)))"

definition qequal_valuation :: "variables \<Rightarrow> 'a quotient \<Rightarrow> 'a valuation \<Rightarrow> 'a valuation \<Rightarrow> bool"
where 
  "qequal_valuation X \<U> \<tau> \<upsilon> = (\<forall> (x, n) \<in> X. \<tau> (x, n) = \<upsilon> (x, n) (mod operations \<U> n))"

lemma qequal_valuation_sym: "symp (qequal_valuation X \<U> )"
  by (metis (no_types, lifting) case_prodD case_prodI2 qequal_valuation_def qequals_sym sympI)

lemma qequal_valuation_trans: "transp (qequal_valuation X \<U>)"
  by (smt (verit, best) case_prodD case_prodI2 qequal_valuation_def qequals_trans transpI)

definition valuation_quotient :: "variables \<Rightarrow> 'a quotient \<Rightarrow> 'a valuation quotient" (infix "\<Zinj>" 90)
where
  "X \<Zinj> \<U> = QuotientP (qequal_valuation X \<U>)"

lemma valuation_quotient_Rel: 
  "Rel (X \<Zinj> \<U>) = { (\<tau>, \<upsilon>). qequal_valuation X \<U> \<tau> \<upsilon> }"
  by (simp add: QuotientP_Rel qequal_valuation_sym qequal_valuation_trans valuation_quotient_def)

lemma valuation_quotient_mod:
  "(\<tau> = \<upsilon> (mod X \<Zinj> \<U>)) = qequal_valuation X \<U> \<tau> \<upsilon>"
  by (simp add: QuotientP_mod qequal_valuation_sym qequal_valuation_trans valuation_quotient_def)

lemma valuation_quotient_in:
  "(\<upsilon> /\<in> X \<Zinj> \<U>) = qequal_valuation X \<U> \<upsilon> \<upsilon>"
  by (simp add: qin_mod valuation_quotient_mod)

lemma valuation_quotient_app:
  "\<tau> = \<upsilon> (mod X \<Zinj> \<U>) \<Longrightarrow> (x, n) \<in> X \<Longrightarrow> us = vs (mod \<U> /^ n) \<Longrightarrow> \<tau> (x, n) us = \<upsilon> (x, n) vs (mod \<U>)"
  by (metis (no_types, lifting) QuotientP_mod case_prodD fun_quotient_app_mod operations_def 
      qequal_valuation_def qequal_valuation_sym qequal_valuation_trans valuation_quotient_def)

lemma valuation_mod_subdomain:
  assumes mod: "\<tau> = \<upsilon> (mod X \<Zinj> \<U>)" 
  assumes sub: "Y \<subseteq> X"
  shows "\<tau> = \<upsilon> (mod Y \<Zinj> \<U>)"
proof -
  have "\<forall> (x, n) \<in> X. \<tau> (x, n) = \<upsilon> (x, n) (mod operations \<U> n)"
    using mod 
    by (simp add: qequal_valuation_def valuation_quotient_mod)
  then show ?thesis
    by (meson mod qequal_valuation_def sub subset_iff valuation_quotient_mod)
qed

lemma update_valuation_skipvar:
  assumes x: "x \<notin> set xs"
  shows "\<upsilon>{xs := us}(x, n) = \<upsilon>(x, n)"
proof - 
  have "index_of x xs = None" 
    by (metis index_of_is_Some nth_mem option.exhaust x)
  then show ?thesis 
    by (simp add: update_valuation_def)
qed

lemma subtracted_bound_vars: 
  assumes x: "(x, n) \<in> X - xs`,0"
  shows "n > 0 \<or> x \<notin> set xs"
  using x
  by (simp add: binders_as_vars_def)

lemma update_valuation_eq_intro:
  assumes "\<tau> = \<upsilon> (mod X \<Zinj> \<U>)"
  assumes "us = vs (mod \<U>/^n)"
  assumes "length xs = n"  
  shows "\<tau>{xs := us} = \<upsilon>{xs := vs} (mod (X \<union> ((xs)`,0)) \<Zinj> \<U>)"
proof -
  { 
    fix x :: variable
    assume "x \<in> set xs"
    then have "\<exists> i. index_of x xs = Some i"
      by (simp add: index_of_exists)
    then obtain i where i: "index_of x xs = Some i" by blast
    then have "i < n" 
      using assms(3) index_of_is_Some by fastforce
    then have us_vs_eq_at_i: "us ! i = vs ! i (mod \<U>)"
      using assms(2) vector_quotient_nth_mod by blast
    have "\<tau>{xs := us}(x, 0) = \<upsilon>{xs := vs}(x, 0) (mod operations \<U> 0)"
      apply (auto simp add: update_valuation_def i)
      using us_vs_eq_at_i
      by (simp add: operations_eq_intro value_op_def)
  }
  note main = this
  {
    fix x :: variable
    fix n :: nat
    assume xn: "(x, n) \<in> X - xs`,0"
    then have x_or_n: "x \<notin> set xs \<or> n > 0" 
      using subtracted_bound_vars by blast
    have "\<tau>{xs := us} (x, n) = \<upsilon>{xs := vs} (x, n) (mod operations \<U> n)"
      by (smt (verit, ccfv_threshold) DiffE assms(1) not_gr0 operations_mod prod.simps(2) 
          update_valuation_def update_valuation_skipvar valuation_quotient_app x_or_n xn)
  }
  note simple = this
  show ?thesis 
    apply (simp add: valuation_quotient_mod qequal_valuation_def)  
    using main simple binders_as_vars_def  by fastforce
qed

lemma valuations_empty_domain[simp]: "{} \<Zinj> \<U> = /\<one>\<U>"
  by (meson equals0D qequal_valuation_def qsubset_antisym_weak qsubset_weak_def 
      subset_universal_singleton_weak valuation_quotient_mod)

subsection \<open>Evaluation\<close>

context algloc
begin

abbreviation Valuations :: "variables \<Rightarrow> 'a valuation quotient" ("\<bbbV>")
  where "\<bbbV> X \<equiv> (X \<Zinj> \<U>)"

fun eval :: "nterm \<Rightarrow> 'a valuation \<Rightarrow> 'a" ("\<langle>_; _\<rangle>") where
  "eval (VarApp x ts) \<upsilon> = \<upsilon> (x, length ts) (\<section>map t = ts!_. eval t \<upsilon>)"
| "eval (AbsApp a xs ts) \<upsilon> = 
    (let op = \<O> !! a in
     let rs = (\<section>map t = ts!i. 
       let bs = a!@i(xs) in 
       (\<lambda> us. (let \<upsilon>' = \<upsilon> {bs := us} in eval t \<upsilon>'))) 
     in op rs)"

lemma eval_modulo:
  "wf t \<Longrightarrow> 
   frees t \<subseteq> X \<Longrightarrow>
   \<tau> = \<upsilon> (mod \<bbbV> X) \<Longrightarrow> 
   eval t \<tau> = eval t \<upsilon> (mod \<U>)"
proof (induct t arbitrary: \<tau> \<upsilon> X)
  case (VarApp x ts)
  have \<tau>_eq_\<upsilon>: "\<tau> = \<upsilon> (mod \<bbbV> X)" using VarApp by auto
  thm valuation_quotient_app[OF \<tau>_eq_\<upsilon>]
  have "frees (VarApp x ts) \<subseteq> X" using VarApp by force
  then have xInX: "(x, length ts) \<in> X" 
    using nt_free_VarApp by force
  have frees_sub: "\<And> i. i < length ts \<Longrightarrow> frees (ts ! i) \<subseteq> X" 
    using VarApp.prems(2) nt_free_VarApp_arg_subset by presburger
  show ?case 
    apply (auto simp add: list_unindexed_map)
    apply (rule valuation_quotient_app[where X=X])
    apply (rule \<tau>_eq_\<upsilon>)
    apply (rule xInX)
    apply (subst vector_quotient_mod)
    apply (auto simp add: qequal_vector_def)
    by (metis VarApp.hyps VarApp.prems(1) VarApp.prems(3) frees_sub nth_mem wf_VarApp)
next
  case (AbsApp a xs ts)
  have valid: "\<checkmark>a" using AbsApp wf_implies_valid_abs by blast
  have len_ts: "length ts = \<section>ar (\<S> !! a)"
    by (smt (z3) AbsApp.prems(1) map_forced_get_def nt_wf.simps(2) option.case_eq_if sig_contains_def)
  have frees: "\<And> i. i < length ts \<Longrightarrow> frees (ts!i) \<subseteq> X \<union> (a!@i(xs))`,0" 
    using AbsApp.prems(2) nt_free_ConsApp_arg_subset by auto
  show ?case
    apply simp
    apply (rule operator_appeq_intro)
    apply (rule valid_in_operators)
    using valid apply blast
    apply (simp add: len_ts)+
    apply (simp add: len_ts[symmetric])
    apply (rule operations_eq_intro)
    apply (rule AbsApp(1))
    apply force
    using AbsApp.prems(1) apply auto[1]
    apply (rule frees, simp)
    apply (rule update_valuation_eq_intro)
    using AbsApp
    apply simp
    apply simp
    using valid
    apply auto
    apply (rule length_boundvars_at[OF AbsApp(2)])
    by simp
qed

lemma eval_is_fun_modulo: 
  assumes wf: "wf t" 
  shows "eval t /\<in> \<bbbV> (frees t) /\<Rightarrow> \<U>"
  using eval_modulo[where X="frees t", OF wf, simplified]
  by (simp add: fun_quotient_in qequal_fun_def)

lemma eval_closed:
  assumes wf: "wf t"
  assumes cl: "closed t"
  shows "eval t \<tau> = eval t \<upsilon> (mod \<U>)"
proof -
  have frees: "frees t \<subseteq> {}" using cl
    by (simp add: closed_def)
  show ?thesis by (rule eval_modulo[OF wf frees, simplified])
qed

subsection \<open>Semantical Equivalence\<close>

text \<open>Two terms are semantically equivalent if for all abstraction algebras, and all valuations, 
they evaluate to the same value. We cannot really define this as a closed notion in HOL, 
as quantifying over all abstraction algebras requires quantifying over type variables, which is not 
possible in HOL. So we first define semantical equivalence just relative to a fixed abstraction algebra,
and then relative to the base type of the abstraction algebra.\<close>

definition sem_equiv :: "nterm \<Rightarrow> nterm \<Rightarrow> bool"
  where "sem_equiv s t = (\<forall> \<upsilon>. \<upsilon> /\<in> \<bbbV> UNIV \<longrightarrow> eval s \<upsilon> = eval t \<upsilon> (mod \<U>))"

end


text \<open>HOL can be extended with quantification over type variables~@{cite "Melham-typequantification"},
and then the notion of semantical equivalence of two terms could be defined via 

@{text \<open>semantically_equivalent s t = \<forall>\<alpha>. \<forall> \<AA> :: \<alpha> algebra. algloc.sem_equiv \<AA> s t\<close>} 

But all we can do here is to define semantical equivalence relative to @{text \<open>\<alpha>\<close>}:
\<close>

definition semantically_equivalent :: "'a \<Rightarrow> nterm \<Rightarrow> nterm \<Rightarrow> bool"
  where "semantically_equivalent \<alpha> s t = (\<forall> \<AA> :: 'a algebra. algloc.sem_equiv \<AA> s t)"

lemma "semantically_equivalent (\<alpha>\<^sub>1::'a) s t = semantically_equivalent (\<alpha>\<^sub>2::'a) s t"
  by (simp add: semantically_equivalent_def)

end