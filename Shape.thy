theory Shape imports General
begin

section \<open>Shape\<close>

subsection \<open>Preshapes\<close>

type_synonym preshape = "(nat set) list"

definition preshape_alldeps :: "preshape \<Rightarrow> nat set" where
  "preshape_alldeps s = \<Union> {s ! i | i. i < length s}"

definition wellformed_preshape :: "preshape \<Rightarrow> bool" where
  "wellformed_preshape s = (\<exists> m. nats m = preshape_alldeps s)"

lemma wellformed_preshape_empty[intro]: "wellformed_preshape []"
  using nats_def preshape_alldeps_def wellformed_preshape_def by auto

subsection \<open>Shapes are Wellformed Preshapes\<close>

typedef shape = "{s . wellformed_preshape s}" morphisms Preshape Shape
  by auto

lemma wellformed_Preshape[iff]: "wellformed_preshape (Preshape s)"
  using Preshape by auto

subsection \<open>Valence and Arity\<close>

definition shape_valence :: "shape \<Rightarrow> nat" ("\<section>val") where
  "\<section>val s = (THE m. nats m = preshape_alldeps (Preshape s))"

definition shape_arity :: "shape \<Rightarrow> nat" ("\<section>ar") where
  "\<section>ar s = length (Preshape s)"

lemma preshape_alldeps[intro]: "wellformed_preshape s \<Longrightarrow> \<exists> m. nats m = preshape_alldeps s"
  using wellformed_preshape_def by auto

lemma preshape_valence: "preshape_alldeps (Preshape s) = nats (shape_valence s)"
  by (metis (mono_tags, lifting) nats_eq_nats shape_valence_def the_equality 
      wellformed_Preshape wellformed_preshape_def)

lemma empty_deps_Shape_valence: 
  "preshape_alldeps s = {} \<Longrightarrow> (shape_valence (Shape s) = 0)"
  by (metis CollectI Shape_inverse nats_0 nats_eq_nats preshape_valence wellformed_preshape_def)

lemma nonempty_deps_Shape_valence: 
  assumes wf: "wellformed_preshape s"
  assumes nonemtpy: "preshape_alldeps s \<noteq> {}"
  shows "shape_valence (Shape s) = 1 + Max (preshape_alldeps s)"
proof - 
  have "\<exists> m. preshape_alldeps s = nats m"
    using wf wellformed_preshape_def by blast
  then obtain m where "preshape_alldeps s = nats m" by blast
  then show ?thesis using Max_nats wf
    by (metis CollectI nats_0 nonemtpy preshape_valence Shape_inverse zero_less_iff_neq_zero)
qed

lemma Shape_arity[intro]: "wellformed_preshape s \<Longrightarrow> shape_arity (Shape s) = length s"
  by (simp add: Shape_inverse shape_arity_def)

subsection \<open>Dependencies\<close>

definition shape_deps :: "shape \<Rightarrow> nat \<Rightarrow> nat set" (infixl ".\<natural>" 100)
  where "s.\<natural>i = (Preshape s) ! i"

abbreviation shape_select_deps :: "shape \<Rightarrow> nat \<Rightarrow> ('a list \<Rightarrow> 'a list)" ("_.@_'(_')" [100, 101, 0] 100)
  where "s.@i(xs) \<equiv> nths xs (s.\<natural>i)"

abbreviation shape_deps_card :: "shape \<Rightarrow> nat \<Rightarrow> nat" (infixl ".#" 100) 
  where "s.#i \<equiv> card(s.\<natural>i)"

lemma shape_deps_in_alldeps: 
  "i < shape_arity s \<Longrightarrow> shape_deps s i \<subseteq> preshape_alldeps (Preshape s)"
  using preshape_alldeps_def shape_arity_def shape_deps_def by auto

lemma "i < shape_arity s \<Longrightarrow> shape_deps s i \<subseteq> nats (shape_valence s)"
  using preshape_valence shape_deps_in_alldeps by presburger

lemma shape_valence_deps:
  assumes d: "d < shape_valence s"
  shows "\<exists> i < shape_arity s. d \<in> shape_deps s i"
proof -
  have d': "d \<in> preshape_alldeps (Preshape s)" 
    using d preshape_valence by auto
  have "\<exists> i. i < length (Preshape s) \<and> d \<in> (Preshape s) ! i"
    using d' by (auto simp add: preshape_alldeps_def)
  then obtain i where i: " i < length (Preshape s) \<and> d \<in> (Preshape s) ! i" by blast
  show ?thesis using i
    using shape_arity_def shape_deps_def by auto
qed

lemma shape_deps_valence:
  assumes i: "i < shape_arity s \<and> d \<in> shape_deps s i"
  shows "d < shape_valence s"
  by (metis i nats_elem preshape_valence shape_deps_in_alldeps subsetD)

lemma nats_shape_valence_is_union: 
  "nats (shape_valence s) = \<Union> { shape_deps s i | i . i < shape_arity s }"
  using preshape_alldeps_def preshape_valence shape_arity_def shape_deps_def by presburger

lemma zero_arity_valence: "shape_arity s = 0 \<Longrightarrow> shape_valence s = 0"
  by (metis less_nat_zero_code not_gr_zero shape_valence_deps)

lemma zero_valence_deps: "i < shape_arity s \<Longrightarrow> shape_valence s = 0 \<Longrightarrow> shape_deps s i = {}"
  by (metis all_not_in_conv less_nat_zero_code shape_deps_valence)

definition shape_valence_at :: "shape \<Rightarrow> nat \<Rightarrow> nat" where
  "shape_valence_at s i = card(shape_deps s i)"

subsection \<open>Common Concrete Shapes\<close>

subsubsection \<open>@{text value_shape}\<close>

definition value_shape :: shape where
  "value_shape = Shape []"

lemma value_shape_valence[iff]: "shape_valence (value_shape) = 0"
  by (simp add: value_shape_def empty_deps_Shape_valence preshape_alldeps_def)

lemma Preshape_Shape[intro]: "wellformed_preshape s \<Longrightarrow> Preshape (Shape s) = s"
  by (auto simp add: Shape_inverse)

lemma value_Preshape[simp]: "Preshape value_shape = []"
  by (auto simp add: value_shape_def)
  
lemma value_shape_arity[simp]: "\<section>ar value_shape = 0"
  by (simp add: Shape_arity value_shape_def wellformed_preshape_empty)

subsubsection \<open>@{text unop_shape}\<close>

definition unop_shape :: shape where
  "unop_shape = Shape [{}]"

lemma wf_unop_preshape: "wellformed_preshape [{}]"
  using preshape_alldeps_def wellformed_preshape_def 
  by auto

lemma unop_Preshape[simp]: "Preshape (unop_shape) = [{}]"
  by (simp add: Shape_inverse unop_shape_def wf_unop_preshape)

lemma unop_shape_arity[simp]: "\<section>ar unop_shape = 1"
  by (simp add: Shape_arity unop_shape_def wf_unop_preshape)

lemma unop_shape_valence[simp]: "\<section>val unop_shape = 0"
  by (simp add: empty_deps_Shape_valence preshape_alldeps_def unop_shape_def)

lemma unop_shape_deps_0[simp]: "shape_deps unop_shape 0 = {}"
  by (simp add: zero_valence_deps)

subsubsection \<open>@{text binop_shape}\<close>

definition binop_shape :: shape where
  "binop_shape = Shape [{}, {}]"

lemma wf_binop_preshape: "wellformed_preshape [{}, {}]"
  using preshape_alldeps_def wellformed_preshape_def 
  by (metis Sup_insert Union_empty List.set_simps nats_0 preshape_valence 
      set_conv_nth unop_Preshape unop_shape_valence)
  
lemma binop_Preshape[simp]: "Preshape (binop_shape) = [{}, {}]" 
  by (simp add: Shape_inverse binop_shape_def wf_binop_preshape)

lemma binop_shape_arity[simp]: "\<section>ar binop_shape = Suc (Suc 0)"
  by (simp add: shape_arity_def)

lemma binop_shape_valence[simp]: "\<section>val binop_shape = 0"
  by (metis Preshape_inverse Sup_insert binop_Preshape empty_deps_Shape_valence 
      list.set(2) nats_0 preshape_alldeps_def preshape_valence set_conv_nth sup.idem 
      unop_Preshape unop_shape_valence)

lemma binop_shape_deps_0[simp]: "binop_shape.\<natural>0 = {}"
  by (simp add: zero_valence_deps)

lemma binop_shape_deps_1[simp]: "binop_shape.\<natural>1 = {}"
  by (simp add: zero_valence_deps)

subsubsection \<open>@{text operator_shape}\<close>

definition operator_shape :: shape where
  "operator_shape = Shape [{0}]"

lemma wf_operator_preshape: "wellformed_preshape [{0}]"
  by (auto simp add: wellformed_preshape_def preshape_alldeps_def nats_def)

lemma operator_Preshape[simp]: "Preshape (operator_shape) = [{0}]"
  by (simp add: Shape_inverse operator_shape_def wf_operator_preshape)

lemma operator_shape_arity[simp]: "\<section>ar operator_shape = Suc 0"
  by (simp add: shape_arity_def)

lemma operator_shape_valence[simp]: "\<section>val operator_shape = Suc 0"
  by (metis atMost_0 ccpo_Sup_singleton empty_set lessThan_Suc_atMost lessThan_def 
      list.set(2) nats_def nats_eq_nats operator_Preshape preshape_alldeps_def preshape_valence 
      set_conv_nth)

lemma operator_shape_deps_0[iff]: "operator_shape.\<natural>0 = {0}"
  by (simp add: shape_deps_def)

end



