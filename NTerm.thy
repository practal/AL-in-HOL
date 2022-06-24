theory NTerm imports Algebra 
begin

section \<open>Term\<close>

subsection \<open>Variables\<close>

type_synonym variable = string 

type_synonym variables = "(variable \<times> nat) set"

definition binders_as_vars :: "variable list \<Rightarrow> variables" ("_`,0" [1000] 1000) where 
  "xs`,0 = { (x, 0) | x. x \<in> set xs }"

lemma binders_as_vars_empty[simp]: "[]`,0 = {}"
  by (simp add: binders_as_vars_def) 

lemma deduction_forall_deps_0[iff]: "\<DD>!!abstr_forall.@0([x]) = [x]"
  apply (auto)
  apply (subst has_shape_get)
  apply blast
  apply (subst operator_shape_deps_0)
  by blast

subsection \<open>Terms\<close>

datatype nterm = 
  VarApp variable "nterm list" 
| AbsApp abstraction "variable list" "nterm list"

definition xvar :: variable ("`x") where "`x = ''x''"
definition xvar0 :: nterm ("\<section>x")  where "\<section>x = VarApp `x []"

definition yvar :: variable ("`y") where "`y = ''y''"
definition yvar0 :: nterm ("\<section>y")  where "\<section>y = VarApp `y []"

definition Avar :: variable ("`A") where "`A = ''A''"
definition Avar0 :: nterm ("\<section>A")  where "\<section>A = VarApp `A []"
definition Avar1 :: "nterm \<Rightarrow> nterm" ("\<section>A[_]")  where "\<section>A[t] = VarApp `A [t]"

definition Bvar :: variable ("`B") where "`B = ''B''"
definition Bvar0 :: nterm ("\<section>B")  where "\<section>B = VarApp `B []"
definition Bvar1 :: "nterm \<Rightarrow> nterm" ("\<section>B[_]")  where "\<section>B[t] = VarApp `B [t]"

definition Cvar :: variable ("`C") where "`C = ''C''"
definition Cvar0 :: nterm ("\<section>C")  where "\<section>C = VarApp `C []"
definition Cvar1 :: "nterm \<Rightarrow> nterm" ("\<section>C[_]")  where "\<section>C[t] = VarApp `C [t]"

definition implies_app :: "nterm \<Rightarrow> nterm \<Rightarrow> nterm" (infix "`\<Rightarrow>" 225) where 
  "A `\<Rightarrow> B = AbsApp abstr_implies [] [A, B]"  

definition true_app :: nterm ("`\<top>") where "`\<top> = AbsApp abstr_true [] []"

definition false_app :: nterm ("`\<bottom>") where "`\<bottom> = AbsApp abstr_false [] []"

definition forall_app :: "variable \<Rightarrow> nterm \<Rightarrow> nterm" ("(3`\<forall>_. _)" [1000, 210] 210) where
  "forall_app x P = AbsApp abstr_forall [x] [P]"

subsection \<open>Wellformedness\<close>

fun nt_wf :: "signature \<Rightarrow> nterm \<Rightarrow> bool" where
  "nt_wf sig (VarApp x ts) = (\<forall> t = ts!_. nt_wf sig t)"
| "nt_wf sig (AbsApp a xs ts) = 
     (sig_contains sig a (length xs) (length ts) \<and>
      distinct xs \<and>
      (\<forall> t = ts!_. nt_wf sig t))"

lemma nt_wf_x0[iff]: "nt_wf sig \<section>x" by (simp add: xvar0_def)
lemma nt_wf_y0[iff]: "nt_wf sig \<section>y" by (simp add: yvar0_def)
lemma nt_wf_A0[iff]: "nt_wf sig \<section>A" by (simp add: Avar0_def)
lemma nt_wf_A1[iff]: "nt_wf sig \<section>A[t] = nt_wf sig t" 
  by (simp add: Avar1_def)
lemma nt_wf_B0[iff]: "nt_wf sig \<section>B" by (simp add: Bvar0_def)
lemma nt_wf_B1[iff]: "nt_wf sig \<section>B[t] = nt_wf sig t" 
  by (simp add: Bvar1_def)
lemma nt_wf_C0[iff]: "nt_wf sig \<section>C" by (simp add: Cvar0_def)
lemma nt_wf_C1[iff]: "nt_wf sig \<section>C[t] = nt_wf sig t" 
  by (simp add: Cvar1_def)

lemma nt_wf_true[simp]: "nt_wf \<DD> `\<top>"
  by (simp add: true_app_def)

lemma nt_wf_implies[simp]: "nt_wf \<DD> (A `\<Rightarrow> B) = (nt_wf \<DD> A \<and> nt_wf \<DD> B)"
  by (auto simp add: implies_app_def shift_index_def)

lemma nt_wf_forall[simp]: "nt_wf \<DD> (`\<forall> `x. t) = nt_wf \<DD> t"
  by (auto simp add: forall_app_def)

lemma sig_extends_nt_wf: "V \<succeq> U \<Longrightarrow> nt_wf U t \<Longrightarrow> nt_wf V t"
proof (induct t)
  case (VarApp x ts)
  then show ?case by simp
next
  case (AbsApp a xs ts)
  then show ?case 
    by (auto simp add: extends_sig_contains)
qed

subsection \<open>Free Variables\<close>

fun nt_free :: "signature \<Rightarrow> nterm \<Rightarrow> variables" where
  "nt_free sig (VarApp x ts) = 
     (\<section>fold X = {(x, length ts)}, t = ts!_. X \<union> nt_free sig t)" 
| "nt_free sig (AbsApp a xs ts) = 
     (\<section>fold X = {}, t = ts!i. X \<union> (nt_free sig t - (sig!!a.@i(xs))`,0))"

lemma nt_free_x0: "nt_free sig \<section>x = {(`x, 0)}" by (simp add: xvar0_def)
 
lemma nt_free_y0: "nt_free sig \<section>y = {(`y, 0)}" by (simp add: yvar0_def)

lemma nt_free_A0:  "nt_free sig \<section>A = {(`A, 0)}" by (simp add: Avar0_def)
lemma nt_free_A1:  "nt_free sig \<section>A[t] = {(`A, Suc 0)} \<union> nt_free sig t" 
  by (simp add: Avar1_def)

lemma nt_free_B0:  "nt_free sig \<section>B = {(`B, 0)}" by (simp add: Bvar0_def)
lemma nt_free_B1:  "nt_free sig \<section>B[t] = {(`B, Suc 0)} \<union> nt_free sig t" 
  by (simp add: Bvar1_def)

lemma nt_free_C0:  "nt_free sig \<section>C = {(`C, 0)}" by (simp add: Cvar0_def)
lemma nt_free_C1:  "nt_free sig \<section>C[t] = {(`C, Suc 0)} \<union> nt_free sig t" 
  by (simp add: Cvar1_def)

lemma nt_free_true: "nt_free \<DD> `\<top> = {}"
  by (simp add: true_app_def)

lemma nt_free_implies: "nt_free \<DD> (s `\<Rightarrow> t) = nt_free \<DD> s \<union> nt_free \<DD> t"
  by (auto simp add: implies_app_def shift_index_def)

lemma nt_free_forall: "nt_free \<DD> (`\<forall> x. t) = nt_free \<DD> t - {(x, 0)}"
  thm forall_app_def binders_as_vars_def
  apply (subst forall_app_def)
  apply auto
  apply (auto simp add: binders_as_vars_def)
  using deduction_sig_forall has_shape_get by auto

lemma sig_extends_nt_free: "V \<succeq> U \<Longrightarrow> nt_wf U t \<Longrightarrow> nt_free V t = nt_free U t"
proof(induct t)
  case (VarApp x ts)
  then show ?case 
    apply simp
    apply (subst list_indexed_fold_cong)
    using VarApp
    by auto
next
  case (AbsApp a xs ts)
  let ?F = "\<lambda> i X t. X \<union> (nt_free V t - (V!!a.@i(xs))`,0)"
  let ?G = "\<lambda> i X t. X \<union> (nt_free U t - (U!!a.@i(xs))`,0)"
  show ?case 
    apply simp
    thm list_indexed_fold_eq[where ?F = ?F and ?G = ?G]
    apply (subst list_indexed_fold_eq[where ?F = ?F and ?G = ?G])
    using AbsApp
    apply auto
    apply (metis (no_types, lifting) extends_sig_def map_forced_get_def option.case_eq_if 
           sig_contains_def)
    by (metis (no_types, lifting) extends_sig_def map_forced_get_def option.case_eq_if 
        sig_contains_def)
qed
 
lemma nt_free_VarApp: "nt_free sig (VarApp x ts) =
  {(x, length ts)} \<union> \<Union> { nt_free sig t | t. t \<in> set ts }"
proof - 
  have "nt_free sig (VarApp x ts) = (\<section>fold X = {(x, length ts)}, t = ts!_. X \<union> nt_free sig t)"
    by simp
  moreover have "(\<section>fold X = {(x, length ts)}, t = ts!_. X \<union> nt_free sig t) =
         {(x, length ts)} \<union> \<Union> { nt_free sig t | t. t \<in> set ts }"
    by (subst union_unindexed_fold, simp)
  ultimately show ?thesis by simp
qed

lemma nt_free_VarApp_arg_subset:
  assumes "nt_free sig (VarApp x ts) \<subseteq> X"
  assumes "i < length ts" 
  shows "nt_free sig (ts ! i) \<subseteq> X"
  by (smt (verit, best) CollectI assms(1) assms(2) le_supE mem_simps(9) nt_free_VarApp nth_mem subset_iff)

lemma nt_free_ConsApp: 
  shows "nt_free sig (AbsApp a xs ts) = 
    \<Union> { nt_free sig (ts!i) - (sig!!a.@i(xs))`,0 | i. i < length ts }"
  by (simp add: union_indexed_fold)

lemma nt_free_ConsApp_arg_subset:
  assumes "nt_free sig (AbsApp a xs ts) \<subseteq> X"
  assumes "i < length ts"
  shows "nt_free sig (ts!i) \<subseteq> X \<union> (sig!!a.@i(xs))`,0"
proof - 
  have "nt_free sig (ts!i) - (sig!!a.@i(xs))`,0 \<subseteq> X"
    by (smt (verit, del_insts) CollectI assms(1) assms(2) mem_simps(9) nt_free_ConsApp subset_eq)
  then show ?thesis by blast
qed

end