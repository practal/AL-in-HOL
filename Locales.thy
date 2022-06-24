theory Locales imports NTerm
begin

subsection \<open>Signature Locale\<close>

locale sigloc = 
  fixes Signature :: "signature" ("\<S>")

context sigloc
begin

abbreviation
  Deps :: "abstraction \<Rightarrow> nat \<Rightarrow> nat set" (infixl "!\<natural>" 100)
  where "a !\<natural> i \<equiv> \<S>!!a.\<natural>i"

abbreviation
  CardDeps :: "abstraction \<Rightarrow> nat \<Rightarrow> nat" (infixl "!#" 100)
  where "a !# i \<equiv> \<S>!!a.#i"

abbreviation
  SelDeps :: "abstraction \<Rightarrow> nat \<Rightarrow> 'b list \<Rightarrow> 'b list" ("_!@_'(_')" [100, 101, 0] 100)
  where "a!@i(xs) \<equiv> \<S>!!a.@i(xs)"

abbreviation wf :: "nterm \<Rightarrow> bool"
  where "wf t \<equiv> nt_wf \<S> t"

abbreviation frees :: "nterm \<Rightarrow> variables" 
  where "frees t \<equiv> nt_free \<S> t"

abbreviation is_valid_abstraction :: "abstraction \<Rightarrow> bool" ("\<checkmark>")
  where "\<checkmark>a \<equiv> ((\<S> a) \<noteq> None)"

abbreviation valence_of_abstraction :: "abstraction \<Rightarrow> nat" ("\<section>v")
  where "\<section>v a \<equiv> \<section>val (\<S>!!a)"

abbreviation arity_of_abstraction :: "abstraction \<Rightarrow> nat" ("\<section>a")
  where "\<section>a a \<equiv> \<section>ar (\<S>!!a)"

lemma wf_implies_valid_abs:
  assumes wf: "wf (AbsApp a xs ts)"
  shows "\<checkmark>a"
proof -
  have "sig_contains \<S> a (length xs) (length ts)" 
    using local.wf nt_wf.simps(2) by blast
  then show ?thesis
    by (metis (no_types, lifting) option.case_eq_if sig_contains_def)
qed

lemma wf_VarApp: "wf (VarApp x ts) = (\<forall> t \<in> set ts. wf t)"
  by simp

lemma wf_AbsApp_valence: assumes wf: "wf (AbsApp a xs ts)" shows "length xs = \<section>v a"
  by (smt (z3) local.wf map_forced_get_def nt_wf.simps(2) option.case_eq_if sig_contains_def)

lemma shape_deps_upper_bound: "\<checkmark>a \<Longrightarrow> i < \<section>a a \<Longrightarrow> a!\<natural>i \<subseteq> nats (\<section>v a)"
  using preshape_valence shape_deps_in_alldeps by auto

lemma length_boundvars_at:
  assumes wf: "wf (AbsApp a xs ts)"
  assumes i: "i < length ts" 
  shows "length (a!@i(xs)) = a !# i"
proof - 
  have valid: "\<checkmark>a"
    using wf wf_implies_valid_abs by blast
  have val: "\<section>v a = length xs"
    by (metis wf_AbsApp_valence wf)
  have deps: "(a!\<natural>i) \<subseteq> nats (\<section>v a)"
    by (smt (z3) shape_deps_upper_bound i local.wf map_forced_get_def nt_wf.simps(2) 
        option.case_eq_if sig_contains_def)
  then show ?thesis
    by (simp add: nats_length_nths val)
qed

definition closed :: "nterm \<Rightarrow> bool" 
  where "closed t = (frees t = {})"

end

subsection \<open>Abstraction Algebra Locale\<close>

locale algloc = sigloc "Sig \<AA>" for AA :: "'a algebra" ("\<AA>")
begin

abbreviation
  Universe :: "'a quotient" ("\<U>")
  where "\<U> \<equiv> Univ \<AA>"

abbreviation
  Operators :: "'a operators" ("\<O>")
  where "\<O> \<equiv> Ops \<AA>"

abbreviation
  Signature :: "signature" ("\<S>")
  where "\<S> \<equiv> Sig \<AA>" 

notation 
  Deps (infixl "!\<natural>" 100) and
  CardDeps (infixl "!#" 100) and
  SelDeps ("_!@_'(_')" [100, 101, 0] 100) and
  is_valid_abstraction ("\<checkmark>") and 
  valence_of_abstraction ("\<section>v") and
  arity_of_abstraction ("\<section>a") 

end

context algloc begin

lemma valid_in_operators: "\<checkmark>a \<Longrightarrow> (\<O>!!a) /\<in> operators \<U> (\<S>!!a)"
  by (metis algebra_compatibility map_forced_get_def shape_compatible_def shape_compatible_opt_def)
 
end


end