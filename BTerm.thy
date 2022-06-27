theory BTerm imports Valuation
begin

section \<open>De Bruijn Term\<close>

subsection \<open>De Bruijn Terms\<close>

datatype bterm = 
  FreeVar variable \<open>bterm list\<close>
| BoundVar nat
| Abstr abstraction \<open>bterm list\<close>

subsection \<open>Unbound and Free Variables\<close>

context sigloc begin

definition raise_indices :: "nat set \<Rightarrow> nat \<Rightarrow> nat set" (infixl ".\<up>" 80)
  where "raise_indices I m = { i + m | i. i \<in> I }"

definition lower_indices :: "nat set \<Rightarrow> nat \<Rightarrow> nat set" (infixl ".\<down>" 80)
  where "I .\<down> m = { i - m | i. i \<in> I \<and> i \<ge> m }"

lemma raise_indices_0[simp]: "I .\<up> 0 = I"
  by (simp add: raise_indices_def)

lemma lower_indices_0[simp]: "I .\<down> 0 = I"
  by (simp add: lower_indices_def)

lemma raise_indices_mono: "A \<subseteq> B \<Longrightarrow> A .\<up> m \<subseteq> B .\<up> m"
  using raise_indices_def by auto

lemma lower_indices_mono: "A \<subseteq> B \<Longrightarrow> A .\<down> m \<subseteq> B .\<down> m"
  using lower_indices_def by auto

lemma raise_lower_indices_le[simp]: "n \<le> m \<Longrightarrow> I .\<up> m .\<down> n = I .\<up> (m - n)"
  by (auto simp add: lower_indices_def raise_indices_def)

lemma raise_lower_indices_ge[simp]: "n \<ge> m \<Longrightarrow> I .\<up> m .\<down> n = I .\<down> (n - m)"
  by (auto simp add: lower_indices_def raise_indices_def)

lemma erase_bottom_indices: "i \<in> I .\<down> m .\<up> m \<Longrightarrow> i \<ge> m \<and> i \<in> I"
  using lower_indices_def raise_indices_def by force

lemma undo_raise_indices: "i \<in> I .\<up> m \<Longrightarrow> i - m \<in> I"
  using raise_indices_def by fastforce

fun unbounds :: "bterm \<Rightarrow> nat set"  where 
  "unbounds (FreeVar x ts) = (\<section>fold I = {}, t=ts!_. I \<union> unbounds t)"
| "unbounds (BoundVar i) = {i}"
| "unbounds (Abstr a ts) = (\<section>fold I = {}, t=ts!_. I \<union> unbounds t) .\<down> \<section>v a" 

lemma unbounds_freeVar_arg: "\<And> i. i < length ts \<Longrightarrow> unbounds (ts ! i) \<subseteq> unbounds (FreeVar x ts)"
  by (auto simp add:  union_indexed_fold)

lemma unbounds_abstr: 
  assumes i: "k < length ts"
  shows "unbounds (ts ! k) \<subseteq> unbounds (Abstr a ts) .\<up> \<section>v a \<union> nats (\<section>v a)"
proof - 
  {
    fix i :: nat
    assume i: "i \<in> unbounds (ts ! k) \<and> i \<ge> \<section>v a"
    have "i - \<section>v a \<in> unbounds (Abstr a ts)"
      apply (auto simp add: union_indexed_fold)
      using assms(1) i lower_indices_def by auto
    have "i \<in> unbounds (Abstr a ts) .\<up> \<section>v a"
      apply (auto simp add: union_indexed_fold)
      by (smt (verit, ccfv_SIG) CollectI UnionI assms(1) i le_add_diff_inverse2 lower_indices_def 
          raise_indices_def)
  }
  then show ?thesis by force
qed

fun bfrees :: "bterm \<Rightarrow> variables" where 
  "bfrees (FreeVar x ts) = 
     (\<section>fold X = {(x, length ts)}, t=ts!_. X \<union> bfrees t)"
| "bfrees (BoundVar i) = {}" 
| "bfrees (Abstr a ts) = (\<section>fold X = {}, t=ts!_. X \<union> bfrees t)" 

lemma bfrees_freeVar_arg: "\<And> i. i < length ts \<Longrightarrow> bfrees (ts ! i) \<subseteq> bfrees (FreeVar x ts)"
  by (auto simp add: union_indexed_fold)

lemma bfrees_abstr_arg: "\<And> i. i < length ts \<Longrightarrow> bfrees (ts ! i) \<subseteq> bfrees (Abstr a ts)"
  by (auto simp add: union_indexed_fold)

subsection \<open>Wellformedness\<close>

fun bwf :: "bterm \<Rightarrow> bool" where
  "bwf (FreeVar x ts) = (\<forall> t=ts!_. bwf t)"
| "bwf (BoundVar i) = True"
| "bwf (Abstr a ts) = (\<checkmark>a \<and> \<section>a a = length ts \<and> 
     (\<forall> t=ts!i. bwf t \<and> unbounds t \<inter> nats (\<section>v a) \<subseteq> a!\<natural>i))"

lemma bwf_freeVar_arg: "bwf (FreeVar x ts) \<Longrightarrow> i < length ts \<Longrightarrow> bwf (ts!i)"
  by auto

lemma bwf_abstr_arg: "bwf (Abstr a ts) \<Longrightarrow> i < length ts \<Longrightarrow> bwf (ts!i)"
  by (simp add: list_indexed_forall_def)

lemma unbounds_bwf_abstr: 
  assumes i: "k < length ts"
  assumes wf: "bwf (Abstr a ts)"
  shows "unbounds (ts ! k) \<subseteq> unbounds (Abstr a ts) .\<up> \<section>v a \<union> a!\<natural>k"
proof - 
  {
    fix i :: nat
    assume i: "i \<in> unbounds (ts ! k) \<and> i \<ge> \<section>v a"
    have "i - \<section>v a \<in> unbounds (Abstr a ts)"
      apply (auto simp add: union_indexed_fold)
      using assms(1) i lower_indices_def by auto
    have "i \<in> unbounds (Abstr a ts) .\<up> \<section>v a"
      apply (auto simp add: union_indexed_fold)
      by (smt (verit, ccfv_SIG) CollectI UnionI assms(1) i le_add_diff_inverse2 lower_indices_def 
          raise_indices_def)
  }
  note left = this
  {
    fix i :: nat
    assume i: "i \<in> unbounds (ts ! k) \<and> i < \<section>v a"
    have "unbounds (ts!k) \<inter> nats (\<section>v a) \<subseteq> a!\<natural>k" using wf
      by (simp add: assms(1) list_indexed_forall_def)
    with i have i': "i \<in> a!\<natural>k" by (simp add: in_mono)
  }
  note right = this
  show ?thesis using left right by fastforce
qed

lemma upper_bound_unbounds_abstr_arg:
  assumes i:"i \<in> \<Union> { unbounds t | t. t \<in> set ts }" 
  shows "i \<in> unbounds (Abstr a ts) .\<up> \<section>v a \<union> (nats (\<section>v a))"
proof -
  have conv: "\<Union> { unbounds t | t. t \<in> set ts } =  \<Union> { unbounds (ts!k) | k. k < length ts }"
    by (metis in_set_conv_nth)
  with i have "i \<in> \<Union> { unbounds (ts!k) | k. k < length ts }"
    by auto
  then have "i \<in> \<Union> { unbounds (Abstr a ts).\<up> \<section>v a \<union> (nats (\<section>v a)) | k. k < length ts }"
    using unbounds_abstr by fastforce
  then show ?thesis by blast
qed

lemma upper_bound_erased_unbounds_abstr_arg:
  assumes i:"i \<in> \<Union> { unbounds t | t. t \<in> set ts } .\<down> \<section>v a .\<up> \<section>v a" 
  shows "i \<in> unbounds (Abstr a ts) .\<up> \<section>v a"
proof - 
  have i1: "i \<in> unbounds (Abstr a ts) .\<up> \<section>v a \<union> (nats (\<section>v a))"
    by (meson erase_bottom_indices i upper_bound_unbounds_abstr_arg)
  have i2: "i \<ge> \<section>v a"
    using erase_bottom_indices i by blast
  from i1 i2 show ?thesis by fastforce
qed

end

subsection \<open>Environments\<close>

type_synonym 'a env = "nat \<Rightarrow> 'a"

definition update_env :: "'a env \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> 'a list \<Rightarrow> 'a env" 
  ("_\<up>_{_ := _}" [1000, 51, 51, 51] 1000)
where 
  "update_env env m js xs = (\<lambda> j. 
     (case index_of j (sorted_list js) of
        Some i \<Rightarrow> xs!i
      | None \<Rightarrow> env (j - m)))"

abbreviation raise_env :: "'a env \<Rightarrow> nat \<Rightarrow> 'a env"
  ("_\<up>_{}" [1000, 51] 1000)
where 
  "env \<up> m {} \<equiv> env \<up> m { {} := [] }"

lemma env_app_noupdate: "finite js \<Longrightarrow> j \<notin> js \<Longrightarrow> env \<up> m { js := xs } j = env \<up> m {} j"
  by (simp add: update_env_def no_index_sorted_list)

lemma env_raised_app: "env \<up> m {} j = env (j - m)"
  by (simp add: no_index_sorted_list update_env_def)

lemma env_app_update: 
  "finite js \<Longrightarrow> j \<in> js \<Longrightarrow> env \<up> m { js := us } j = us ! the (index_of j (sorted_list js))"
  by (metis index_of_is_None option.case_eq_if set_sorted_list update_env_def)
  
context algloc begin

definition env_quotient :: "nat set \<Rightarrow> ('a env) quotient" ("\<bbbE>")
  where "env_quotient I = (/\<equiv>I /\<Rightarrow> \<U>)"

lemma env_subset: "A \<subseteq> B \<Longrightarrow> \<bbbE> B /\<le> \<bbbE> A"
  by (simp add: env_quotient_def fun_quotient_subset_weak_intro set_quotient_subset_weak)
  
lemma env_subset_mod: "A \<subseteq> B \<Longrightarrow> env1 = env2 (mod \<bbbE> B) \<Longrightarrow> env1 = env2 (mod \<bbbE> A)"
  by (meson env_subset qsubset_mod_weak)

lemma env_app: "i \<in> I \<Longrightarrow> env1 = env2 (mod \<bbbE> I) \<Longrightarrow> env1 i = env2 i (mod \<U>)"
  by (simp add: env_quotient_def fun_quotient_app_mod set_quotient_mod)

lemma env_mod: "(env1 = env2 (mod \<bbbE> I)) = (\<forall> i \<in> I. env1 i = env2 i (mod \<U>))"
  by (smt (verit, best) env_quotient_def fun_quotient_mod qequal_fun_def set_quotient_mod)

subsection \<open>Evaluation\<close>

fun beval :: "bterm \<Rightarrow> 'a valuation \<Rightarrow> 'a env \<Rightarrow> 'a" ("\<langle>_; _, _\<rangle>") where
  "beval (FreeVar x ts) \<upsilon> env = \<upsilon> (x, length ts) (\<section>map t = ts!_. beval t \<upsilon> env)"
| "beval (BoundVar i) \<upsilon> env = env i" 
| "beval (Abstr a ts) \<upsilon> env = (\<O>!!a) (\<section>map t = ts!i. 
     (\<lambda> us. beval t \<upsilon> (env \<up> \<section>v a {a!\<natural>i := us})))" 

lemma beval_modulo:
  "bwf t \<Longrightarrow>
   bfrees t \<subseteq> X \<Longrightarrow> 
   \<tau> = \<upsilon> (mod \<bbbV> X) \<Longrightarrow> 
   unbounds t \<subseteq> I \<Longrightarrow>
   env1 = env2 (mod \<bbbE> I) \<Longrightarrow>
   beval t \<tau> env1 = beval t \<upsilon> env2 (mod \<U>)"
proof (induct t arbitrary: env1 env2 I)
  case (FreeVar x ts)
  have "(x, length ts) \<in> bfrees (FreeVar x ts)"
    by (simp add: union_indexed_fold)
  then have x: "(x, length ts) \<in> X"
    using FreeVar.prems(2) by blast
  have bfrees: "\<And> i. i < length ts \<Longrightarrow> bfrees (ts ! i) \<subseteq> X" using bfrees_freeVar_arg
    using FreeVar.prems(2) by blast
  show ?case apply simp 
    apply (rule valuation_quotient_app[where X="X"])
    using FreeVar apply simp
    apply (simp add: x)
    apply (auto simp add: vector_quotient_mod qequal_vector_def)
    apply (rule FreeVar(1))
    apply simp
    apply (erule bwf_freeVar_arg[OF FreeVar.prems(1)])
    apply (erule bfrees)
    using FreeVar apply simp
    apply force
    apply (rule env_subset_mod[where B = "I"])
    apply (meson FreeVar.prems(4) sigloc.unbounds_freeVar_arg subset_trans)
    using FreeVar apply simp
    done
next
  case (BoundVar i)
  have i: "i \<in> I"
    using BoundVar.prems(4) by auto
  show ?case 
    apply simp 
    using BoundVar i env_app 
    by force
next
  case (Abstr a ts)
  have valid: "\<checkmark> a"
    using Abstr.prems(1) by force
  have length_ts: "\<section>a a = length ts"
    using Abstr.prems(1) by force
  show ?case 
    apply simp
    apply (rule operator_appeq_intro[of "\<O> !! a" \<U> "\<S> !! a"])
    using valid valid_in_operators apply force
    apply (simp add: length_ts)+
    apply (auto simp add: operations_mod)
    apply (rule Abstr(1))
    apply simp
    using Abstr.prems(1) sigloc.bwf_abstr_arg apply blast
    using Abstr.prems(2) bfrees_abstr_arg apply blast
    using Abstr.prems(3) apply blast
    apply (rule unbounds_bwf_abstr[where a=a], simp)
    using Abstr apply simp
    apply (auto simp add: env_mod union_unindexed_fold)
    apply (subst env_app_noupdate[where env=env1])
    using length_ts finite_shape_deps valid apply presburger
    apply (metis (no_types, lifting) erase_bottom_indices length_ts linorder_not_le shape_deps_valence) 
    apply (subst env_app_noupdate[where env=env2])
    using length_ts finite_shape_deps valid apply presburger
    apply (metis (no_types, lifting) erase_bottom_indices length_ts linorder_not_le shape_deps_valence) 
    apply (simp add: env_raised_app)
    apply (rule env_app[where I="I"])
    using upper_bound_unbounds_abstr_arg erase_bottom_indices
    apply (metis (no_types, lifting) Abstr.prems(4) subset_eq undo_raise_indices 
           upper_bound_erased_unbounds_abstr_arg)
    using Abstr apply simp
    apply (subst env_app_update[where env=env1])
    using finite_shape_deps length_ts valid apply presburger
    apply simp
    apply (subst env_app_update[where env=env2])
    using finite_shape_deps length_ts valid apply presburger
    apply simp
    apply (rule  vector_quotient_nth_mod)
    apply auto using valid
    using length_ts sigloc.finite_shape_deps upper_bound_index_sorted_list by presburger
qed

end

end