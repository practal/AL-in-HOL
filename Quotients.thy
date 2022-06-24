theory Quotients imports Main
begin

section \<open>Quotient\<close>

subsection \<open>Quotients\<close>

text \<open>
  We define a  @{emph \<open>quotient\<close>} to be a set with custom equality.
  In fact, we identify the set with the custom equivalence relation. We can do this because  
  the set is uniquely determined by the equivalence relation.

  Our approach does not replace @{theory HOL.Equiv_Relations}, but builds on top of it
  by encoding as a type invariant the property of a relation to be an equivalence relation.
\<close>

typedef 'a quotient = "{ r::'a rel. \<exists> A. equiv A r }" morphisms Rel Quotient
  by (metis empty_iff equivI mem_Collect_eq refl_on_def subsetI sym_def trans_def)

definition QField :: "'a quotient \<Rightarrow> 'a set" where 
  "QField q = Field (Rel q)"

lemma equiv_Field: 
  assumes "equiv A r"
  shows "Field r = A"
proof - 
  have "A \<subseteq> Field r"
    by (meson FieldI2 assms equivE refl_onD subsetI)
  moreover have "Field r \<subseteq> A"
    by (metis Field_square assms equiv_type mono_Field)
  ultimately show "Field r = A"
    by blast
qed

lemma equiv_QField_Rel: "equiv (QField q) (Rel q)"
  by (smt (verit, ccfv_SIG) Rel equiv_Field mem_Collect_eq QField_def)

definition qin :: "'a \<Rightarrow> 'a quotient \<Rightarrow> bool" (infix "'/\<in>" 50) where
  "(a /\<in> q) = (a \<in> QField q)"

abbreviation qnin :: "'a \<Rightarrow> 'a quotient \<Rightarrow> bool" (infix "'/\<notin>" 50) where
  "(a /\<notin> q) \<equiv> (a \<in> QField q)"


subsection \<open>Equality Modulo\<close>

definition qequals :: "'a \<Rightarrow> 'a \<Rightarrow> 'a quotient \<Rightarrow> bool" ("_ = _ '(mod _')" [51, 51, 0] 50) where 
  "(a = b (mod q)) = ((a, b) \<in> Rel q)"

abbreviation qnequals :: "'a \<Rightarrow> 'a \<Rightarrow> 'a quotient \<Rightarrow> bool" ("_ \<noteq> _ '(mod _')" [51, 51, 0] 50) where 
  "(a \<noteq> b (mod q)) \<equiv> \<not> (a = b (mod q))"

lemma qin_mod: "(a /\<in> q) = (a = a (mod q))"
  by (metis equiv_QField_Rel equiv_class_eq_iff qequals_def qin_def)

lemma qequals_in: "a = b (mod q) \<Longrightarrow> a /\<in> q \<and> b /\<in> q"
  by (metis FieldI1 FieldI2 QField_def qequals_def qin_def)

lemma qequals_sym: "a = b (mod q) \<Longrightarrow> b = a (mod q)"
  by (meson equiv_QField_Rel equiv_def qequals_def sym_def)

lemma qequals_trans: "a = b (mod q) \<Longrightarrow> b = c (mod q) \<Longrightarrow> a = c (mod q)"
  by (meson equiv_QField_Rel equiv_def qequals_def trans_def)

subsection \<open>Subsets of Quotients\<close>

text \<open>There isn't a unique definition of what a subset of quotients is. There
are at least 3 different notions that all make sense.\<close>

definition qsubset_weak :: "'a quotient \<Rightarrow> 'a quotient \<Rightarrow> bool" (infix "'/\<le>" 50) where
  "(p /\<le> q) = (\<forall> x y. x = y (mod p) \<longrightarrow> x = y (mod q))"

definition qsubset_bishop :: "'a quotient \<Rightarrow> 'a quotient \<Rightarrow> bool" (infix "'/\<sqsubseteq>" 50) where
  "(p /\<sqsubseteq> q) = (\<forall> x y. x /\<in> p \<and> y /\<in> p \<longrightarrow> (x = y (mod p) \<longleftrightarrow> x = y (mod q)))"

definition qsubset_strong :: "'a quotient \<Rightarrow> 'a quotient \<Rightarrow> bool" (infix "'/\<subseteq>" 50) where
  "(p /\<subseteq> q) = (\<forall> x y. x /\<in> p \<longrightarrow> (x = y (mod p) \<longleftrightarrow> x = y (mod q)))"

lemma qsubset_strong_implies_bishop: "p /\<subseteq> q \<Longrightarrow> p /\<sqsubseteq> q"
  by (simp add: qsubset_bishop_def qsubset_strong_def)

lemma qsubset_strong_implies_weak: "p /\<subseteq> q \<Longrightarrow> p /\<le> q"
  by (meson qequals_in qsubset_strong_def qsubset_weak_def)

lemma qsubset_bishop_implies_weak: "p /\<sqsubseteq> q \<Longrightarrow> p /\<le> q"
  by (meson qequals_in qsubset_bishop_def qsubset_weak_def)

lemma qsubset_QField_strong: "p /\<subseteq> q \<Longrightarrow> QField p \<subseteq> QField q"
  by (meson qin_def qin_mod qsubset_strong_def subset_iff)

lemma qsubset_QField_weak: "p /\<le> q \<Longrightarrow> QField p \<subseteq> QField q"
  by (meson qin_def qin_mod qsubset_weak_def subset_iff)

lemma qsubset_QField_bishop: "p /\<sqsubseteq> q \<Longrightarrow> QField p \<subseteq> QField q"
  using qsubset_QField_weak qsubset_bishop_implies_weak by blast

lemma qubseteq_refl_strong[iff]: "q /\<subseteq> q"
  using qsubset_strong_def by blast

lemma qubseteq_refl_bishop[iff]: "q /\<sqsubseteq> q"
  using qsubset_bishop_def by blast

lemma qubseteq_refl_weak[iff]: "q /\<le> q"
  using qsubset_weak_def by auto

lemma qsubset_trans_strong: "p /\<subseteq> q \<Longrightarrow> q /\<subseteq> r \<Longrightarrow> p /\<subseteq> r"
  by (meson qin_mod qsubset_strong_def)
 
lemma qsubset_trans_bishop: "p /\<sqsubseteq> q \<Longrightarrow> q /\<sqsubseteq> r \<Longrightarrow> p /\<sqsubseteq> r"
  by (smt (verit, best) qin_mod qsubset_bishop_def)

lemma qsubset_trans_weak: "p /\<le> q \<Longrightarrow> q /\<le> r \<Longrightarrow> p /\<le> r"
  by (simp add: qsubset_weak_def)

lemma qsubset_antisym_weak: "p /\<le> q \<Longrightarrow> q /\<le> p \<Longrightarrow> p = q"
  by (smt (verit) Rel_inverse dual_order.refl qequals_def qsubset_weak_def subsetI 
      subset_antisym subset_iff surj_pair sym_def)

lemma qsubset_antisym_bishop: "p /\<sqsubseteq> q \<Longrightarrow> q /\<sqsubseteq> p \<Longrightarrow> p = q"
  by (simp add: qsubset_antisym_weak qsubset_bishop_implies_weak)

lemma qsubset_antisym_strong: "p /\<subseteq> q \<Longrightarrow> q /\<subseteq> p \<Longrightarrow> p = q"
  by (simp add: qsubset_antisym_bishop qsubset_strong_implies_bishop)

lemma qsubset_mod_weak: "x = y (mod q) \<Longrightarrow> q /\<le> p \<Longrightarrow> x = y (mod p)"
  by (simp add: qsubset_weak_def)

lemma qsubset_mod_bishop: "x = y (mod q) \<Longrightarrow> q /\<sqsubseteq> p \<Longrightarrow> x = y (mod p)"
  by (metis qsubset_bishop_implies_weak qsubset_mod_weak)

lemma qsubset_mod_strong:  "x = y (mod q) \<Longrightarrow> q /\<subseteq> p \<Longrightarrow> x = y (mod p)"
  by (meson qsubset_mod_bishop qsubset_strong_implies_bishop)

subsection \<open>Equivalence Classes\<close>

definition qclass :: "'a \<Rightarrow> 'a quotient \<Rightarrow> 'a set" (infix "'/%" 80) where
  "a /% q = (Rel q)``{a}"

lemma qequals_implies_equal_qclasses: "a = b (mod q) \<Longrightarrow> a /% q = b /% q"
  by (metis equiv_QField_Rel equiv_class_eq_iff qclass_def qequals_def)

lemma empty_qclass: "(a /% q = {}) = (\<not> (a /\<in> q))" 
  by (metis Image_singleton_iff ex_in_conv qclass_def qequals_def qequals_in qin_mod)

lemma qclass_elems: "(b \<in> a /% q) = (a = b (mod q))"
  by (simp add: qclass_def qequals_def)

subsection \<open>Construction via Symmetric and Transitive Predicate\<close>

definition QuotientP :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a quotient" where 
  "QuotientP eq = Quotient { (x, y) . eq x y }"

lemma QuotientP_eq_refl: "symp eq \<Longrightarrow> transp eq \<Longrightarrow> eq x y \<Longrightarrow> eq x x \<and> eq y y"
  by (meson sympD transpE)

lemma QuotientP_equiv:
  assumes "symp eq" 
  assumes "transp eq"
  shows "equiv { x . eq x x}  { (x, y) . eq x y }"
proof -
  let ?A = "{ x . eq x x}"
  let ?r = "{ (x, y) . eq x y }"
  have "?r \<subseteq> ?A \<times> ?A" using QuotientP_eq_refl assms by fastforce
  then show "equiv ?A ?r" 
    by (smt (verit, best) CollectD CollectI Sigma_cong assms case_prodD case_prodI equivI 
        refl_onI sym_def symp_def trans_def transp_def)
qed

lemma QuotientP_Rel: "symp eq \<Longrightarrow> transp eq \<Longrightarrow> Rel (QuotientP eq) = { (x, y) . eq x y }"
  by (metis (no_types, lifting) CollectI QuotientP_def QuotientP_equiv Quotient_inverse)

lemma QuotientP_mod: "symp eq \<Longrightarrow> transp eq \<Longrightarrow> (x = y (mod QuotientP eq)) = (eq x y)"
  by (metis CollectD CollectI QuotientP_Rel case_prodD case_prodI qequals_def)

lemma QuotientP_in: "symp eq \<Longrightarrow> transp eq \<Longrightarrow> (x /\<in> QuotientP eq) = eq x x"
  by (simp add: QuotientP_mod qin_mod)

subsection \<open>Set with Identity as Quotient\<close>

definition qequal_set :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where 
  "qequal_set U x y = (x \<in> U \<and> x = y)"

lemma qequal_set_sym: "symp (qequal_set U)" 
  by (simp add: qequal_set_def symp_def)

lemma qequal_set_trans: "transp (qequal_set I)"
  by (simp add: qequal_set_def transp_def)

definition set_quotient :: "'a set \<Rightarrow> 'a quotient" ("'/\<equiv>") where 
  "/\<equiv>U = QuotientP (qequal_set U)"

lemma set_quotient_Rel: "Rel(/\<equiv>U) = { (x, y) . x \<in> U \<and> x = y }"
  by (simp add: QuotientP_Rel qequal_set_def qequal_set_sym qequal_set_trans set_quotient_def)

lemma set_quotient_mod: "(x = y (mod /\<equiv>U)) = (x \<in> U \<and> x = y)"
  by (simp add: QuotientP_mod qequal_set_def qequal_set_sym qequal_set_trans set_quotient_def)

lemma set_quotient_in: "(x /\<in> /\<equiv>U) = (x \<in> U)"
  by (simp add: qin_mod set_quotient_mod)

lemma set_quotient_subset_strong: "(/\<equiv>U /\<subseteq> /\<equiv>V) = (U \<subseteq> V)"
  by (smt (verit, ccfv_SIG) qsubset_strong_def set_quotient_in set_quotient_mod subsetD subsetI)

lemma set_quotient_subset_weak: "(/\<equiv>U /\<le> /\<equiv>V) = (U \<subseteq> V)"
  by (meson qsubset_mod_weak qsubset_strong_implies_weak set_quotient_mod 
    set_quotient_subset_strong subset_iff)

lemma set_quotient_subset_bishop: "(/\<equiv>U /\<sqsubseteq> /\<equiv>V) = (U \<subseteq> V)"
  by (meson qsubset_bishop_implies_weak qsubset_strong_implies_bishop 
    set_quotient_subset_strong set_quotient_subset_weak)

subsection \<open>Empty and Universal Quotients\<close>

definition empty_quotient :: "'a quotient" ("'/\<emptyset>") where
  "/\<emptyset> = /\<equiv>{}"

definition univ_quotient :: "'a quotient" ("'/\<U>") where
  "/\<U> = /\<equiv>UNIV"

lemma empty_quotient_Rel: "Rel /\<emptyset> = {}"
  by (simp add: empty_quotient_def set_quotient_Rel)

lemma empty_quotient_mod: "\<not> (x = y (mod /\<emptyset>))"
  by (simp add: empty_quotient_def set_quotient_mod)

lemma empty_quotient_in: "\<not> (x /\<in> /\<emptyset>)"
  by (simp add: empty_quotient_def set_quotient_in)

lemma univ_quotient_Rel: "Rel /\<U> = Id"
  by (auto simp add: set_quotient_Rel univ_quotient_def)

lemma univ_quotient_in: "x /\<in> /\<U>"
  by (simp add: set_quotient_in univ_quotient_def)

lemma univ_quotient_mod: "(x = y (mod /\<U>)) = (x = y)"
  by (simp add: set_quotient_mod univ_quotient_def)

subsection \<open>Singleton Quotients\<close>

definition qequal_singleton :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "qequal_singleton U x y = (x \<in> U \<and> y \<in> U)"

lemma qequal_singleton_sym: "qequal_singleton U x y \<Longrightarrow> qequal_singleton U y x"
  by (simp add: qequal_singleton_def)

lemma qequal_singleton_trans: 
  "qequal_singleton U x y \<Longrightarrow> qequal_singleton U y z \<Longrightarrow> qequal_singleton U x z"
  by (simp add: qequal_singleton_def)

definition singleton_quotient :: "'a set \<Rightarrow> 'a quotient" ("'/\<one>") where
  "/\<one>U = QuotientP (qequal_singleton U)"

lemma singleton_quotient_Rel: "Rel (/\<one>U) = { (x, y). qequal_singleton U x y }"
  by (metis QuotientP_Rel qequal_singleton_def singleton_quotient_def sympI transpI)

lemma singleton_quotient_mod[simp]: "(x = y (mod /\<one>U)) = (x \<in> U \<and> y \<in> U)"
  by (simp add: qequal_singleton_def qequals_def singleton_quotient_Rel)

lemma singleton_quotient_in: "(x /\<in> /\<one>U) = (x \<in> U)"
  by (meson qin_mod singleton_quotient_mod)

lemma empty_singleton_quotient[iff]: "/\<one>{} = /\<emptyset>"
  by (simp add: empty_quotient_in qsubset_antisym_strong qsubset_strong_def 
      singleton_quotient_in)

abbreviation universal_singleton_quotient:: "'a quotient" ("'/\<one>\<U>") where
  "/\<one>\<U> \<equiv> /\<one>UNIV"

subsection \<open>Comparing Notions of Quotient Subsets\<close>

lemma empty_subset_singleton_quotient_weak: "/\<emptyset> /\<le> q" 
  by (simp add: empty_quotient_mod qsubset_weak_def)

lemma empty_subset_singleton_quotient_bishop: "/\<emptyset> /\<sqsubseteq> q" 
  by (simp add: empty_quotient_in qsubset_bishop_def)

lemma  empty_subset_singleton_quotient_strong: "/\<emptyset> /\<subseteq> q"
  by (simp add: empty_quotient_in qsubset_strong_def)

lemma same_QField_bishop: "QField p = QField q \<Longrightarrow> p /\<sqsubseteq> q \<Longrightarrow> p = q"
  by (simp add: qin_def qsubset_antisym_bishop qsubset_bishop_def)

lemma same_QField_strong: "QField p = QField q \<Longrightarrow> p /\<subseteq> q \<Longrightarrow> p = q"
  by (simp add: qsubset_strong_implies_bishop same_QField_bishop)

lemma singleton_quotient_subset_weak: "(/\<one>U /\<le> /\<one>V) = (U \<subseteq> V)"
  by (meson qsubset_weak_def singleton_quotient_mod subset_iff)

lemma singleton_quotient_subset_bishop: "(/\<one>U /\<sqsubseteq> /\<one>V) = (U \<subseteq> V)"
  by (meson qsubset_bishop_def qsubset_bishop_implies_weak singleton_quotient_in 
      singleton_quotient_mod singleton_quotient_subset_weak subsetD)

lemma singleton_quotient_subset_strong: "(/\<one>U /\<subseteq> /\<one>V) = (U = V \<or> U = {})"
proof -
  have implies_sub:"(/\<one>U /\<subseteq> /\<one>V) \<Longrightarrow> (U \<subseteq> V)"
    by (metis qsubset_strong_implies_weak singleton_quotient_subset_weak)
  
  {
    assume singleton_UV: "(/\<one>U /\<subseteq> /\<one>V)"
    have UV: "U \<subseteq> V"
      using implies_sub singleton_UV by auto
    fix x y
    assume x: "x \<in> V" 
    assume notx: "x \<notin> U"
    assume y: "y \<in> U"
    have xV: "x /\<in> /\<one>V"
      by (simp add: singleton_quotient_in x) 
    have xU: "\<not> (x /\<in> /\<one>U)"
      by (simp add: notx singleton_quotient_in)
    have "x = y (mod /\<one>V)" 
      by (meson UV singleton_quotient_mod subsetD x y)
    then have "x = y (mod /\<one>U)"
      by (meson qequals_sym qsubset_strong_def singleton_UV singleton_quotient_in y)
    then have "False"
      by (simp add: notx)
  }
  with implies_sub have "(/\<one>U /\<subseteq> /\<one>V) \<Longrightarrow> U = V \<or> U = {}"
    by auto
  then show ?thesis
    using empty_subset_singleton_quotient_strong by force
qed

lemma subset_universal_singleton_weak: "q /\<le> /\<one>\<U>"
  by (simp add: qsubset_weak_def)

lemma subset_universal_singleton_bishop: "(q /\<sqsubseteq> /\<one>\<U>) = (q = /\<one>(QField q))"
proof - 
  {
    assume q: "q /\<sqsubseteq> /\<one>\<U>" 
    then have "\<And> x y. x /\<in> q \<and> y /\<in> q \<Longrightarrow> (x = y (mod q)) = (x = y (mod /\<one>\<U>))"
      by (simp add: qsubset_bishop_def)
    then have "\<And> x y. x /\<in> q \<and> y /\<in> q \<Longrightarrow> x = y (mod q)"
      by simp
    then have "q = /\<one>(QField q)"
      by (meson qequals_in qin_def qsubset_antisym_weak qsubset_weak_def singleton_quotient_mod)
  }
  then show ?thesis
    by (metis singleton_quotient_subset_bishop subset_UNIV)
qed

lemma subset_universal_singleton_strong:  "(q /\<subseteq> /\<one>\<U>) = (q = /\<emptyset> \<or> q = /\<one>\<U>)"
proof -
  {
    assume q: "q /\<subseteq> /\<one>\<U>"
    then have "q /\<sqsubseteq> /\<one>\<U>"
      using qsubset_strong_implies_bishop by auto
    then have "q = /\<one>(QField q)"
      using subset_universal_singleton_bishop by blast 
  }
  note isSingleton = this
  {
    assume q: "q /\<subseteq> /\<one>\<U>"
    then have "QField q = UNIV \<or> QField q = {}"
      by (metis q singleton_quotient_subset_strong isSingleton)
    then have "q = /\<one>\<U> \<or> q = /\<emptyset> "
      using isSingleton q by auto
  }
  then show ?thesis
    using empty_subset_singleton_quotient_strong by auto
qed  

lemma identity_QField_subset_weak: "/\<equiv>(QField q) /\<le> q"
  by (metis eq_equiv_class equiv_QField_Rel qequals_def qsubset_weak_def set_quotient_mod)

lemma identity_QField_subset_bishop: "(/\<equiv>(QField q) /\<sqsubseteq> q) = (q = /\<equiv>(QField q))"
  by (metis qin_def qubseteq_refl_bishop same_QField_bishop set_quotient_in subsetI subset_antisym)

lemma identity_QField_subset_strong: "(/\<equiv>(QField q) /\<subseteq> q) = (q = /\<equiv>(QField q))"
  using identity_QField_subset_bishop qsubset_strong_implies_bishop by auto

lemma qsubset_weak_neq_bishop: 
  assumes xy: "(x::'a) \<noteq> y" 
  shows "((/\<le>) :: 'a quotient \<Rightarrow> 'a quotient \<Rightarrow> bool) \<noteq> (/\<sqsubseteq>)"
proof -
  let ?U = "/\<equiv>{x, y}"
  have sub: "?U /\<le> /\<one>\<U>" 
    by (simp add: subset_universal_singleton_weak)
  from xy have notsub: "\<not> (?U /\<sqsubseteq> /\<one>\<U>)"
    by (metis insert_iff set_quotient_mod singleton_quotient_mod subset_universal_singleton_bishop)
  show ?thesis using sub notsub by auto
qed

lemma qsubset_bishop_neq_strong: 
  assumes xy: "(x::'a) \<noteq> y" 
  shows "((/\<sqsubseteq>) :: 'a quotient \<Rightarrow> 'a quotient \<Rightarrow> bool) \<noteq> (/\<subseteq>)"
proof -
  let ?U = "/\<equiv>{x}"
  have sub: "?U /\<sqsubseteq> /\<one>\<U>" 
    by (simp add: qsubset_bishop_def set_quotient_in set_quotient_mod)
  from xy have notsub: "\<not> (?U /\<subseteq> /\<one>\<U>)"
    by (metis(full_types) UNIV_I empty_quotient_in insertI1 set_quotient_in set_quotient_mod 
        singleton_quotient_mod subset_universal_singleton_strong)
  show ?thesis using sub notsub by auto
qed

lemma qsubset_weak_neq_strong: 
  assumes xy: "(x::'a) \<noteq> y" 
  shows "((/\<le>) :: 'a quotient \<Rightarrow> 'a quotient \<Rightarrow> bool) \<noteq> (/\<subseteq>)"
  using qsubset_bishop_implies_weak qsubset_strong_implies_bishop qsubset_weak_neq_bishop xy by fastforce
  
subsection \<open>Functions between Quotients\<close>

definition qequal_fun :: 
  "'a quotient \<Rightarrow> 'b quotient \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a => 'b) \<Rightarrow> bool"
where
  "qequal_fun p q f g =  (\<forall> x y. x = y (mod p) \<longrightarrow> f x = g y (mod q))"

lemma qequal_fun_sym: "symp (qequal_fun p q)" by (metis qequal_fun_def qequals_sym sympI)

lemma qequal_fun_trans: "transp (qequal_fun p q)" 
  by (smt (verit) qclass_elems qequal_fun_def qequals_implies_equal_qclasses transpI)

definition fun_quotient :: "'a quotient \<Rightarrow> 'b quotient \<Rightarrow> ('a \<Rightarrow> 'b) quotient" (infixr "'/\<Rightarrow>" 90) where
  "p /\<Rightarrow> q = QuotientP (qequal_fun p q)"

lemma fun_quotient_Rel: "Rel (p /\<Rightarrow> q) =  { (f, g) . qequal_fun p q f g }"
  by (simp add: QuotientP_Rel fun_quotient_def qequal_fun_sym qequal_fun_trans)

lemma fun_quotient_mod: " (f = g (mod p /\<Rightarrow> q)) = (qequal_fun p q f g)"
  by (metis QuotientP_mod fun_quotient_def qequal_fun_sym qequal_fun_trans)

lemma fun_quotient_in: "(f /\<in> p /\<Rightarrow> q) = (qequal_fun p q f f)"
  by (simp add: fun_quotient_mod qin_mod)

lemma fun_quotient_app_in: "f /\<in> p /\<Rightarrow> q \<Longrightarrow> x /\<in> p \<Longrightarrow> f x /\<in> q"
  by (meson fun_quotient_in qequal_fun_def qin_mod)

lemma fun_quotient_app_mod: "f = g (mod p /\<Rightarrow> q) \<Longrightarrow> x = y (mod p) \<Longrightarrow> f x = g y (mod q)"
  by (meson qequal_fun_def fun_quotient_mod)

lemma fun_quotient_app_in_mod: "f /\<in> p /\<Rightarrow> q \<Longrightarrow> x = y (mod p) \<Longrightarrow> f x = f y (mod q)"
  by (meson fun_quotient_app_mod qin_mod)

lemma fun_quotient_compose: "(\<circ>) /\<in> (q /\<Rightarrow> r) /\<Rightarrow> (p /\<Rightarrow> q) /\<Rightarrow> (p /\<Rightarrow> r)"
  by (auto simp add: fun_quotient_in qequal_fun_def fun_quotient_mod)

lemma fun_quotient_empty_domain: "(/\<emptyset> /\<Rightarrow> q) = /\<one>\<U>"
  by (metis empty_quotient_mod fun_quotient_mod qequal_fun_def qsubset_antisym_weak qsubset_weak_def subset_universal_singleton_weak)

lemma fun_quotient_empty_range: "q \<noteq> /\<emptyset> \<Longrightarrow> (q /\<Rightarrow> /\<emptyset>) = /\<emptyset>"
  by (metis empty_quotient_in fun_quotient_app_in qsubset_antisym_strong qsubset_strong_def)

lemma fun_quotient_subset_weak_intro:
  assumes "p2 /\<le> p1 \<and> q1 /\<le> q2" 
  shows "p1 /\<Rightarrow> q1 /\<le> p2 /\<Rightarrow> q2"
  by (smt (verit, best) assms fun_quotient_mod qequal_fun_def qsubset_weak_def)

lemma fun_quotient_subset_weakdef: 
  "(p1 /\<Rightarrow> q1 /\<le> p2 /\<Rightarrow> q2) = 
   (\<forall> f g. (\<forall>x y. x = y (mod p1) \<longrightarrow> f x = g y (mod q1)) \<longrightarrow>
           (\<forall>x y. x = y (mod p2) \<longrightarrow> f x = g y (mod q2)))"
  by (simp add: fun_quotient_mod qequal_fun_def qsubset_weak_def)

lemma fun_quotient_range_subset_weak:
  assumes sub: "((p1 :: 'a quotient) /\<Rightarrow> q1 /\<le> p2 /\<Rightarrow> q2)"
  assumes nonempty: "p2 \<noteq> /\<emptyset>"
  shows "q1 /\<le> q2"
proof - 
  {
    assume contra: "\<not> q1 /\<le> q2"
    have "\<exists> a b. (a = b (mod q1)) \<and> \<not> (a = b (mod q2))"
      using contra qsubset_weak_def by blast
    then obtain a b where ab: "(a = b (mod q1)) \<and> \<not> (a = b (mod q2))" by blast
    let ?f = "\<lambda> x :: 'a. a"
    let ?g = "\<lambda> x :: 'a. b"
    have "\<forall> x y. x = y (mod p1) \<longrightarrow> ?f x = ?g y (mod q1)"
      using ab by blast
    then have "\<forall> x y. x = y (mod p2) \<longrightarrow> ?f x = ?g y (mod q2)" 
      using fun_quotient_subset_weakdef[of p1 q1 p2 q2, simplified sub]
      by meson
    then have "\<And> x y. x = y (mod p2) \<Longrightarrow> a = b (mod q2)"
      by blast
    with nonempty have "False"
      by (metis ab empty_quotient_mod fun_quotient_empty_range fun_quotient_mod qequal_fun_def)
  }
  then show ?thesis by blast
qed

lemma trivializing_qsuperset:
  shows "(/\<one>(QField p) /\<le> q) = (\<not> (\<exists> x y. x /\<in> p \<and> y /\<in> p \<and> x \<noteq> y (mod q)))"
  by (meson qin_def qsubset_weak_def singleton_quotient_mod)

lemma fun_quotient_domain_subset_weak:
  assumes sub: "((p1 :: 'a quotient) /\<Rightarrow> q1 /\<le> p2 /\<Rightarrow> q2)"
  assumes nontrivial: "\<not> (/\<one>(QField q1) /\<le> q2)"
  shows "p2 /\<le> p1"
proof - 
  {
    assume ex: "\<exists> a b. a = b (mod p2) \<and> a \<noteq> b (mod p1)"
    
    text \<open>Construct zero and one\<close>
    then have  "p2 \<noteq> /\<emptyset>"
      using empty_quotient_mod by fastforce
    then have q1_sub_q2: "q1 /\<le> q2" using fun_quotient_range_subset_weak sub by auto
    have "\<exists> x y. x /\<in> q1 \<and> y /\<in> q1 \<and> x \<noteq> y (mod q2)"
      using nontrivial trivializing_qsuperset by blast
    then obtain zero one where zo: "zero /\<in> q1 \<and> one /\<in> q1 \<and> zero \<noteq> one (mod q2)"
      by blast
    then have zo_q1: "zero \<noteq> one (mod q1)" using q1_sub_q2 qsubset_mod_weak by force
    
    have "False"
    proof (cases "\<exists> a b. a = b (mod p2) \<and> a \<noteq> b (mod p1) \<and> a \<noteq> b")
      case True
      then obtain a b where ab: "a = b (mod p2) \<and> a \<noteq> b (mod p1) \<and> a \<noteq> b" by blast
      let ?f = "\<lambda> x. if x /\<in> p1 then (if x = a (mod p1) then one else zero) else (if x = a then one else zero)"
      have "\<forall> x y. x = y (mod p1) \<longrightarrow> ?f x = ?f y (mod q1)"
        by (smt (verit, best) qequals_sym qequals_trans qin_mod zo)
      then have "\<forall> x y. x = y (mod p2) \<longrightarrow> ?f x = ?f y (mod q2)" 
        using sub[simplified fun_quotient_subset_weakdef] by meson
      then have contra: "?f a = ?f b (mod q2)" using ab by blast
      then show "False" by (metis(full_types) ab qequals_sym qin_mod zo)      
    next
      case False
      then have "\<exists> a. a = a (mod p2) \<and> a \<noteq> a (mod p1)" using ex by blast
      then obtain a where a: "a = a (mod p2) \<and> a \<noteq> a (mod p1)" by blast
      let ?f = "\<lambda> x. if x = a then one else zero"
      let ?g = "\<lambda> x. zero"
      have "\<forall> x y. x = y (mod p1) \<longrightarrow> ?f x = ?g y (mod q1)"
        by (metis(full_types) a qequals_in qin_mod zo)
      then have "\<forall> x y. x = y (mod p2) \<longrightarrow> ?f x = ?g y (mod q2)"
        using sub[simplified fun_quotient_subset_weakdef] by meson
      then have contra: "?f a = ?g a (mod q2)"
        using a by blast
      then show "False" sledgehammer
        using qequals_sym zo by force
    qed
  }
  then show ?thesis
    using qsubset_weak_def by blast
qed

subsection \<open>Vectors as Quotients\<close>

definition qequal_vector :: "'a quotient \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "qequal_vector q n u v = (length u = n \<and> length v = n \<and> (\<forall> i < n. u ! i = v ! i (mod q)))"

lemma qequal_vector_sym: "symp (qequal_vector q n)"
  by (metis qequal_vector_def qequals_sym sympI)

lemma qequal_vector_trans: "transp (qequal_vector q n)"
  by (smt (verit, del_insts) qequal_vector_def qequals_trans transpI)

definition vector_quotient :: "'a quotient \<Rightarrow> nat \<Rightarrow> 'a list quotient" (infix "'/^" 100) where
  "q /^ n = QuotientP (qequal_vector q n)"

lemma vector_quotient_Rel: "Rel (q /^ n) = { (u, v). qequal_vector q n u v }"
  by (simp add: QuotientP_Rel qequal_vector_sym qequal_vector_trans vector_quotient_def)

lemma vector_quotient_in: "(u /\<in> q /^ n) = (qequal_vector q n u u)"
  by (simp add: QuotientP_in qequal_vector_sym qequal_vector_trans vector_quotient_def)

lemma vector_quotient_mod: "(u = v (mod q /^ n)) = (qequal_vector q n u v)"
  using qequals_def vector_quotient_Rel by fastforce

lemma vector_quotient_nth: "i < n \<Longrightarrow> (\<lambda> u. u ! i) /\<in> q /^ n /\<Rightarrow> q"
  by (simp add: fun_quotient_in qequal_fun_def qequal_vector_def vector_quotient_mod)

lemma vector_quotient_nth_in: "i < n \<Longrightarrow> u /\<in> q /^ n \<Longrightarrow> u ! i /\<in> q"
  by (blast intro: fun_quotient_app_in[where f = "\<lambda> u . u ! i"] vector_quotient_nth)

lemma vector_quotient_nth_mod: "i < n \<Longrightarrow> u = v (mod q /^ n) \<Longrightarrow> u ! i = v ! i (mod q)"
  by (blast intro: fun_quotient_app_in_mod[where f = "\<lambda> u . u ! i"] vector_quotient_nth)

lemma vector_quotient_append: "(@) /\<in> q /^ n /\<Rightarrow> q /^ m /\<Rightarrow> q /^ (n+m)"
  by (simp add: fun_quotient_in fun_quotient_mod nth_append qequal_fun_def qequal_vector_def 
      vector_quotient_mod)

lemma vector_quotient_append_in: "x /\<in> q /^ n \<Longrightarrow> y /\<in> q /^ m \<Longrightarrow> x @ y /\<in> q /^ (n+m)"
  by (meson fun_quotient_app_in_mod qin_mod vector_quotient_append)

lemma vector_quotient_append_mod: 
  "x = x' (mod q /^ n) \<Longrightarrow> y = y' (mod q /^ m) \<Longrightarrow> x@y = x'@y' (mod q /^ (n+m))"
  by (meson fun_quotient_app_in_mod fun_quotient_app_mod vector_quotient_append)

lemma vector_quotient_weak_subset_intro: "p /\<le> q \<Longrightarrow> p/^n /\<le> q/^n"
  by (simp add: qequal_vector_def qsubset_weak_def vector_quotient_mod)

lemma vector_quotient_strong_subset_intro: "p /\<subseteq> q \<Longrightarrow> p/^n /\<subseteq> q/^n"  
  by (simp add: qequal_vector_def qsubset_strong_def vector_quotient_mod vector_quotient_nth_in)

lemma vector_quotient_bishop_subset_intro: "p /\<sqsubseteq> q \<Longrightarrow> p/^n /\<sqsubseteq> q/^n"  
  by (simp add: qequal_vector_def qsubset_bishop_def vector_quotient_mod vector_quotient_nth_in)

subsection \<open>Tuples as Quotients\<close>

definition qequal_tuple :: "'a quotient list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "qequal_tuple qs u v = (length u = length qs \<and> length v = length qs \<and> 
     (\<forall> i < length qs. u ! i = v ! i (mod qs!i)))"

lemma qequal_tuple_sym: "symp (qequal_tuple qs)"
  by (metis qequal_tuple_def qequals_sym sympI)

lemma qequal_tuple_trans: "transp (qequal_tuple qs)"
  by (smt (verit, best) qequal_tuple_def qequals_trans transpI)

definition tuple_quotient :: "'a quotient list \<Rightarrow> 'a list quotient" ("'/\<times>") where
  "/\<times> qs = QuotientP (qequal_tuple qs)"

lemma tuple_quotient_rel: "Rel (/\<times> qs) = { (u, v). qequal_tuple qs u v }"
  by (simp add: QuotientP_Rel tuple_quotient_def qequal_tuple_sym qequal_tuple_trans)

lemma tuple_quotient_in: "(u /\<in> (/\<times> qs)) = (qequal_tuple qs u u)"
  by (simp add: QuotientP_in tuple_quotient_def qequal_tuple_sym qequal_tuple_trans)

lemma tuple_quotient_mod: "(u = v (mod /\<times> qs)) = (qequal_tuple qs u v)"
  by (simp add: QuotientP_mod tuple_quotient_def qequal_tuple_sym qequal_tuple_trans)

lemma tuple_quotient_nth: "i < length qs \<Longrightarrow> (\<lambda> u. u ! i) /\<in> /\<times> qs /\<Rightarrow> qs ! i"
  by (simp add: fun_quotient_in qequal_fun_def qequal_tuple_def tuple_quotient_mod)

lemma tuple_quotient_append: "(@) /\<in> /\<times> ps /\<Rightarrow> /\<times> qs /\<Rightarrow> /\<times> (ps@qs)"
  by (simp add: QuotientP_mod fun_quotient_in fun_quotient_mod nth_append tuple_quotient_def 
      qequal_fun_def qequal_tuple_def qequal_tuple_sym qequal_tuple_trans)

lemma vectors_are_tuples: "q /^ n = /\<times> (replicate n q)"
  by (smt (verit, ccfv_SIG) vector_quotient_def tuple_quotient_def
      Collect_cong QuotientP_def case_prodD case_prodI2 
      length_replicate nth_replicate qequal_tuple_def qequal_vector_def)   

lemma tuple_quotient_strong_subset_intro: 
  "length ps = length qs \<Longrightarrow> (\<And> i. i < length ps \<Longrightarrow> ps!i /\<subseteq> qs!i) \<Longrightarrow> /\<times> ps /\<subseteq> /\<times> qs"
  by (smt (verit, ccfv_threshold) qequal_tuple_def qequals_in qsubset_strong_def tuple_quotient_in tuple_quotient_mod)

lemma tuple_quotient_bishop_subset_intro: 
  "length ps = length qs \<Longrightarrow> (\<And> i. i < length ps \<Longrightarrow> ps!i /\<sqsubseteq> qs!i) \<Longrightarrow> /\<times> ps /\<sqsubseteq> /\<times> qs"
  apply (auto simp add: qsubset_bishop_def)
  by (metis (no_types, lifting) qequal_tuple_def qin_mod tuple_quotient_mod)+
  
end