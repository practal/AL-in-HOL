theory Signature imports Shape
begin

section \<open>Signature\<close>

subsection \<open>Abstractions\<close>

datatype abstraction = Abs string

definition abstr_true :: abstraction where "abstr_true = Abs ''true''"
definition abstr_implies :: abstraction where "abstr_implies = Abs ''implies''"
definition abstr_forall :: abstraction where "abstr_forall = Abs ''forall''"
definition abstr_false :: abstraction where "abstr_false = Abs ''false''"

lemma noteq_abstr_true_implies[simp]: "abstr_true \<noteq> abstr_implies"
  by (simp add: abstr_implies_def abstr_true_def)

lemma noteq_abstr_implies_forall[simp]: "abstr_implies \<noteq> abstr_forall"
  by (simp add: abstr_implies_def abstr_forall_def)

lemma noteq_abstr_true_forall[simp]: "abstr_true \<noteq> abstr_forall"
  by (simp add: abstr_true_def abstr_forall_def)

subsection \<open>Signatures\<close>

type_synonym signature = "(abstraction, shape) map"

definition empty_sig :: signature where 
  "empty_sig = (\<lambda> a. None)"

definition has_shape :: "signature \<Rightarrow> abstraction \<Rightarrow> shape \<Rightarrow> bool" where
  "has_shape S a shape = (S a = Some shape)"
  
definition extends_sig :: "signature \<Rightarrow> signature \<Rightarrow> bool" (infix "\<succeq>" 50) where
  "extends_sig T S = (\<forall> a. S a = None \<or> T a = S a)"

lemma has_shape_extends: "T \<succeq> S \<Longrightarrow> has_shape S a s \<Longrightarrow> has_shape T a s"
  by (metis extends_sig_def has_shape_def option.discI)

definition sig_contains :: "signature \<Rightarrow> abstraction \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "sig_contains sig abstr valence arity = 
     (case sig abstr of 
        Some s \<Rightarrow> \<section>val s = valence \<and> \<section>ar s = arity 
      | None \<Rightarrow> False)"

lemma has_shape_sig_contains: "has_shape sig a s \<Longrightarrow> sig_contains sig a (\<section>val s) (\<section>ar s)"
  by (simp add: has_shape_def sig_contains_def)

lemma has_shape_get: "has_shape sig a s \<Longrightarrow> sig !! a = s"
  by (simp add: has_shape_def map_forced_get_def)

lemma extends_sig_contains: "V \<succeq> U \<Longrightarrow> sig_contains U a val ar \<Longrightarrow> sig_contains V a val ar"
  by (smt (verit) extends_sig_def option.case_eq_if sig_contains_def)

subsection \<open>Logic Signatures\<close>

definition deduction_sig :: signature ("\<DD>") where 
  "\<DD> = empty_sig(
     abstr_true := Some value_shape,
     abstr_implies := Some binop_shape,
     abstr_forall := Some operator_shape)"

lemma deduction_sig_true[iff]: "has_shape deduction_sig abstr_true value_shape"
  by (simp add: has_shape_def deduction_sig_def)

lemma deduction_sig_implies[iff]: "has_shape \<DD> abstr_implies binop_shape"
  by (simp add: has_shape_def deduction_sig_def)

lemma deduction_sig_forall[iff]: "has_shape \<DD> abstr_forall operator_shape"
  by (simp add: has_shape_def deduction_sig_def)

lemma deduction_sig_contains_true[iff]: "sig_contains \<DD> abstr_true 0 0"
  by (simp add: deduction_sig_def sig_contains_def)

lemma deduction_sig_contains_implies[iff]: "sig_contains \<DD> abstr_implies 0 (Suc (Suc 0))"
  by (simp add: deduction_sig_def sig_contains_def)

lemma deduction_sig_contains_forall[iff]: "sig_contains \<DD> abstr_forall (Suc 0) (Suc 0)"
  using has_shape_sig_contains deduction_sig_forall by fastforce  





end


