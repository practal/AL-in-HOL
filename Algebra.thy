theory Algebra imports Signature Quotients
begin

section \<open>Abstraction Algebra\<close>

text \<open>
  We will abbreviate @{emph \<open>Abstraction Algebra\<close>} by leaving the prefix  
  @{emph \<open>Algebra\<close>} implicit, and just saying @{emph \<open>Algebra\<close>} instead. 
\<close>

subsection \<open>Operations and Operators as Quotients\<close>

type_synonym 'a operation = "'a list \<Rightarrow> 'a"
type_synonym 'a operator = "'a operation list \<Rightarrow> 'a"

definition operations :: "'a quotient \<Rightarrow> nat \<Rightarrow> ('a operation) quotient" where
  "operations U n = U /^ n /\<Rightarrow> U"

definition operators :: "'a quotient \<Rightarrow> shape \<Rightarrow> ('a operator) quotient" where
  "operators U s = /\<times> (map (\<lambda> deps. operations U (card deps)) (Preshape s)) /\<Rightarrow> U"

definition value_op :: "'a \<Rightarrow> 'a operation" where 
  "value_op u = (\<lambda> _. u) "

lemma operators_appeq_intro: 
  assumes FG: "F = G (mod operators \<U> s)"
  assumes lenfs: "length fs = \<section>ar s"
  assumes lengs: "length gs = \<section>ar s"
  assumes fsgs: "(\<And> i. i < \<section>ar s \<Longrightarrow> fs!i = gs!i (mod operations \<U> (s.#i)))"
  shows "F fs = G gs (mod \<U>)"
proof -
  have appeq: "\<And> x y. x = y (mod /\<times> (map (\<lambda>deps. operations \<U> (card deps)) (Preshape s))) \<Longrightarrow> F x = G y (mod \<U>)"
    using FG[simplified operators_def fun_quotient_mod qequal_fun_def]
    by blast
  show ?thesis 
    apply (rule appeq)
    apply (simp add: tuple_quotient_mod qequal_tuple_def)
    apply auto
    using fsgs
    apply (simp add: lenfs shape_arity_def)
    apply (simp add: lengs shape_arity_def)
    using fsgs shape_arity_def shape_deps_def by auto    
qed

lemma operator_appeq_intro: 
  assumes F: "F /\<in> operators \<U> s"
  assumes lenfs: "length fs = \<section>ar s"
  assumes lengs: "length gs = \<section>ar s"
  assumes fsgs: "(\<And> i. i < \<section>ar s \<Longrightarrow> fs!i = gs!i (mod operations \<U> (s.#i)))"
  shows "F fs = F gs (mod \<U>)"
  by (meson F fsgs lenfs lengs operators_appeq_intro qin_mod)

lemma operations_eq_intro:
  assumes "\<And> us vs. us = vs (mod \<U> /^ n) \<Longrightarrow> f us = g vs (mod \<U>)"
  shows "f = g (mod operations \<U> n)"
  by (simp add: assms fun_quotient_mod operations_def qequal_fun_def)

lemma operations_mod:
  "(f = g (mod operations \<U> n)) = (\<forall> us vs. us = vs (mod \<U>/^n) \<longrightarrow> f us = g vs (mod \<U>))"
  by (metis fun_quotient_app_mod operations_def operations_eq_intro)

subsection \<open>Compatibility of Shape and Operator\<close>

definition shape_compatible  :: "'a quotient \<Rightarrow> shape \<Rightarrow> 'a operator \<Rightarrow> bool" where
  "shape_compatible U s op = (op /\<in> operators U s)"

definition shape_compatible_opt :: "'a quotient \<Rightarrow> shape option \<Rightarrow> 'a operator option \<Rightarrow> bool" where
  "shape_compatible_opt U s op = ((s = None \<and> op = None) \<or> (s \<noteq> None \<and> op \<noteq> None \<and> 
     shape_compatible U (the s) (the op)))"

subsection \<open>Abstraction Algebras\<close>

type_synonym 'a operators = "(abstraction, 'a operator) map"

type_synonym 'a prealgebra = "'a quotient \<times> signature \<times> 'a operators"

definition is_algebra :: "'a prealgebra \<Rightarrow> bool" where
  "is_algebra paa = 
     (let U = fst paa in
      let sig = fst (snd paa) in
      let ops = snd (snd paa) in
      U \<noteq> /\<emptyset> \<and> (\<forall> a. shape_compatible_opt U (sig a) (ops a)))" 

definition trivial_prealgebra :: "'a prealgebra" where 
  "trivial_prealgebra = (/\<U>, Map.empty, Map.empty)"

lemma trivial_prealgebra: "is_algebra trivial_prealgebra"
  by (metis (no_types, lifting) empty_quotient_in fst_conv is_algebra_def 
      shape_compatible_opt_def snd_conv trivial_prealgebra_def univ_quotient_in)

typedef 'a algebra = "{ aa :: 'a prealgebra . is_algebra aa }" morphisms Prealgebra Algebra
  using trivial_prealgebra by blast

definition Univ :: "'a algebra \<Rightarrow> 'a quotient" where 
  "Univ aa = fst (Prealgebra aa)"

definition Sig :: "'a algebra \<Rightarrow> signature" where 
  "Sig aa = fst (snd (Prealgebra aa))"

definition Ops :: "'a algebra \<Rightarrow> 'a operators" where
  "Ops aa = snd (snd (Prealgebra aa))"

lemma Prealgebra_components: "Prealgebra aa = (Univ aa, Sig aa, Ops aa)"
  by (simp add: Ops_def Sig_def Univ_def)

lemma Univ_nonempty: "Univ aa \<noteq> /\<emptyset>"
  by (metis Prealgebra Univ_def is_algebra_def mem_Collect_eq)

lemma algebra_compatibility: "shape_compatible_opt (Univ aa) (Sig aa a) (Ops aa a)"
  by (metis Ops_def Prealgebra Sig_def Univ_def is_algebra_def mem_Collect_eq)

end