theory General 
  imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar"
begin

section \<open>General\<close>

subsection \<open>nats\<close>

definition nats :: "nat \<Rightarrow> nat set" where
  "nats n = {..< n }"

lemma finite_nats[iff]: "finite (nats n)"
  using nats_def by auto

lemma nats_elem[simp]: "(d \<in> nats n) = (d < n)"
  using nats_def by auto

lemma nats_0[simp]: "nats 0 = {}"
  by (simp add: nats_def)

lemma card_nats[simp]: "card (nats n) = n"
  by (simp add: nats_def)

lemma nats_eq_nats[simp]: "(nats n = nats m) = (n = m)"
  by (metis card_nats)

lemma Max_nats: "n > 0 \<Longrightarrow> 1 + Max (nats n) = n"
  by (metis Max_gr_iff Max_in Suc_eq_plus1_left Suc_leI finite_nats lessI 
      linorder_neqE_nat nats_0 nats_elem not_le)

subsection \<open>Lists\<close>

subsubsection \<open>Tools for Indices\<close>

lemma nats_length_nths: 
  assumes "A \<subseteq> nats (length xs)" 
  shows "length (nths xs A) = card A"
proof - 
  have l1: "length (nths xs A) = card {i. i < length xs \<and> i \<in> A}"
    using length_nths by force
  have l2: "card {i. i < length xs \<and> i \<in> A} = card A"
    by (smt (verit, ccfv_SIG) Collect_cong Collect_mem_eq Orderings.order_eq_iff 
        assms le_fun_def less_eq_set_def nats_elem subsetI)
  from l1 l2 show ?thesis by presburger
qed  

fun index_of :: "'a \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "index_of x [] = None"
| "index_of x (a#as) = (if x = a then Some 0 else 
     (case index_of x as of 
        None \<Rightarrow> None
      | Some i \<Rightarrow> Some (Suc i)))"

lemma index_of_head: "index_of x (x # xs) = Some 0"
  by simp

lemma index_of_exists: "x \<in> set xs \<Longrightarrow> \<exists> i. index_of x xs = Some i"
proof (induct xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
  proof (cases "a = x")
    case True
    then show ?thesis
      by auto
  next
    case False
    then show ?thesis 
      using Cons.hyps Cons.prems by fastforce
  qed
qed

lemma index_of_is_None: "index_of x xs = None \<Longrightarrow> x \<notin> set xs"
  using index_of_exists by fastforce

lemma index_of_is_Some: "index_of x xs = Some i \<Longrightarrow> i < length xs \<and> xs!i = x"
proof(induct xs arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  then show ?case 
  proof(cases "a = x")
    case True
    then have "i = 0" using Cons by auto
    then show ?thesis using Cons True by simp
  next
    case False
    then have rec: "index_of x (a#as) = (case index_of x as of
                 None \<Rightarrow> None 
               | Some k \<Rightarrow> Some (Suc k))"
      by auto
    then have "\<exists> k. index_of x (a#as) = Some (Suc k) \<and> index_of x as = Some k"
      by (metis Cons.prems not_None_eq option.simps(4) option.simps(5))
    then obtain k where k: " index_of x (a#as) = Some (Suc k) \<and> index_of x as = Some k" by blast
    then show ?thesis using Cons by force
  qed
qed

definition shift_index  :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) => (nat => 'a)" where 
  "shift_index d f x = f (x + d)"  

lemma shift_index_0[simp]: "shift_index 0 = id"
  by (subst fun_eq_iff, auto simp add: shift_index_def)

lemma shift_index_acc_append[simp]: 
  "shift_index d (\<lambda>i acc x. acc @ [f i x]) = (\<lambda> i acc x. acc @ [shift_index d f i x])"
  by (auto simp add: shift_index_def)

lemma shift_index_gather:
  "shift_index d (\<lambda>i acc x. g (f i x) acc) = (\<lambda>i acc x. g (shift_index d f i x) acc)"
  by (auto simp add: shift_index_def)

lemma shift_index_applied_twice[simp]:
  "shift_index a (shift_index b f) = shift_index (a+b) f"
  apply (subst fun_eq_iff)
  apply (auto simp add: shift_index_def)
  by (metis ab_semigroup_add_class.add_ac(1))

lemma shift_index_unindexed[simp]: "shift_index d (\<lambda> i. F) = (\<lambda> i. F)"
  by (auto simp add: shift_index_def)

subsubsection \<open>Indexed Quantification\<close>

definition list_indexed_forall :: "'a list \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "list_indexed_forall xs f = (\<forall> i < length xs. f i (xs ! i))"

syntax
  "_list_indexed_forall" :: "pttrn \<Rightarrow> 'a list \<Rightarrow> pttrn \<Rightarrow> bool \<Rightarrow> bool"  
    ("(3\<forall> _ = _!_./ _)" [1000, 100, 1000, 10] 10)

translations
  "\<forall> x = xs!i. P" \<rightleftharpoons> "CONST list_indexed_forall xs (\<lambda> i x. P)"

lemma list_indexed_forall_cong[fundef_cong]:
  assumes "xs = ys"
  assumes "\<And>i x. i < length ys \<Longrightarrow> x = ys!i \<Longrightarrow> P i x = Q i x"
  shows "(\<forall> x = xs!i. P i x) = (\<forall> y = ys!i. Q i y)"
  by (simp add: assms list_indexed_forall_def)

lemma size_nth[termination_simp]: "i < length ts \<Longrightarrow> size (ts ! i) < Suc (size_list size ts)"
  by (meson Suc_n_not_le_n linorder_not_less nth_mem size_list_estimation')

lemma list_indexed_forall_empty[simp]: "list_indexed_forall [] f = True"
  by (simp add: list_indexed_forall_def)

lemma list_indexed_forall_cons[simp]: 
  "list_indexed_forall (x#xs) f = (f 0 x \<and> list_indexed_forall xs (shift_index 1 f))"
  using less_Suc_eq_0_disj
  by (auto simp add: list_indexed_forall_def shift_index_def)



subsubsection \<open>Indexed Fold\<close>

definition list_indexed_fold :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where 
  "list_indexed_fold f xs y = fold (\<lambda> (i, x) y. f i x y) (zip [0 ..< length xs] xs) y"

syntax
  "_list_indexed_fold" :: "pttrn \<Rightarrow> 'b \<Rightarrow> pttrn \<Rightarrow> 'a list \<Rightarrow> pttrn \<Rightarrow> 'b \<Rightarrow> 'b" 
    ("(3\<section>fold _ =/ _,/ _ =/ _!_./ _)"  [1000, 51, 1000, 100, 1000, 10] 10)

translations
   "\<section>fold a = a0, x = xs!i. F" \<rightleftharpoons> "CONST list_indexed_fold (\<lambda> i x a. F) xs a0"

lemma list_indexed_fold_empty[simp]: "list_indexed_fold f [] y = y"
  by (simp add: list_indexed_fold_def)

lemma list_indexed_fold_cong[fundef_cong]:
  assumes "xs = ys"
  assumes "\<And>i a x. i < length ys \<Longrightarrow> x = ys!i \<Longrightarrow> F i a x = G i a x"
  shows "(\<section>fold a = a0, x = xs!i. F i a x) = (\<section>fold a = a0, y = ys!i. G i a y)"
  apply (simp add: list_indexed_fold_def)
  apply (rule fold_cong)
  using assms
  apply auto
  by (metis add.left_neutral assms(2) in_set_zip nth_upt prod.sel(1) prod.sel(2))

lemma list_indexed_fold_eq:
  assumes "\<And>i a x. i < length xs \<Longrightarrow> F i a (xs!i) = G i a (xs!i)"
  shows "(\<section>fold a = a0, x = xs!i. F i a x) = (\<section>fold a = a0, x = xs!i. G i a x)"
  by (metis assms list_indexed_fold_cong) 

lemma list_unindexed_forall[simp]: "(\<forall> x = xs!i. P x) = (\<forall> x \<in> set xs. P x)"
  apply (auto simp add: list_indexed_forall_def)
  by (metis in_set_conv_nth)

lemma fold_zip_interval_shift: 
  "i + length xs = j \<Longrightarrow> 
     fold (\<lambda> (i, x) a. F (i + d) x a) (zip [i ..< j] xs) a = 
     fold (\<lambda> (i, x) a. F i x a) (zip [i+d ..< j+d] xs) a"
proof (induct xs arbitrary: i j a)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  have ij: "i + length xs + 1 = j"
    using Cons(2)
    by auto
  then have ij_interval: "[i..<j] = i # [Suc i ..< j]"
    by (simp add: upt_conv_Cons)
  from ij have ijd_interval: "[i+d..<j+d] = (i+d) # [Suc (i+d) ..< j+d]"
    by (simp add: upt_conv_Cons)
  show ?case using Cons(1) ij
    by (auto simp add: ij_interval ijd_interval)
qed

lemma fold_zip_interval_shift1: 
  assumes "i + length xs = j"
  shows "fold (\<lambda> (i, x) a. F (Suc i) x a) (zip [i ..< j] xs) a = 
           fold (\<lambda> (i, x) a. F i x a) (zip [Suc i ..< Suc j] xs) a"
proof -
  have add: "\<And> i. Suc i = i + 1" by auto
  show ?thesis
    apply ((subst add)+)
    apply (rule fold_zip_interval_shift)
    by (simp add: assms)
qed

lemma list_indexed_fold_cons[simp]:
  "(\<section>fold a = a0, x = (u#us)!i. F i a x) = (\<section>fold a = F 0 a0 u, x = us!i. shift_index 1 F i a x)"
proof (induct us arbitrary: a0)
  case Nil
  then show ?case 
    by (simp add: list_indexed_fold_def)
next
  case (Cons a us)
  have interval: "\<And> n. [0..<n] @ [n, Suc n] = 0 # [(Suc 0) ..< Suc (Suc n)]"
    by (simp add: upt_conv_Cons)
  have app1: "\<And> i n. i \<le> n \<Longrightarrow> [i ..<n] @ [n] = [i ..< Suc n]"
    by auto
  have app2: "\<And> i n. i \<le> n \<Longrightarrow> [i ..<n] @ [n, Suc n] = [i ..< Suc (Suc n)]" 
    by auto
  have empty: "\<And> us. \<not> Suc 0 \<le> length us \<Longrightarrow> us = []"
    by (meson Suc_leI length_greater_0_conv)
  from Cons show ?case
    apply (auto simp add: list_indexed_fold_def interval shift_index_def)
    apply (simp only: app1 app2)
    apply (subst fold_zip_interval_shift1)
    by (auto simp add: empty)
qed

lemma list_unindexed_fold: 
  "(\<section>fold a = a0, x = xs!i. F x a) = fold F xs a0"
proof (induct xs arbitrary: a0)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case 
    apply simp
    apply (simp add: list_indexed_fold_def shift_index_def)
    by (metis list_indexed_fold_def local.Cons)
qed

(*lemma list_indexed_fold_collect: 
  "(\<section>fold X = X0, x = xs!i. X \<union> F i x) = X0 \<union> \<Union> { F i (xs!i) | i. i < length xs }"  
proof (induct xs arbitrary: X0 F)
  case Nil
  show ?case by simp    
next
  case (Cons a xs)
  show ?case using Cons
    apply simp
    sledgehammer
qed*)

subsubsection \<open>Indexed Map\<close>

definition list_indexed_map :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "list_indexed_map f xs = (\<section>fold acc = [], x = xs!i. acc @ [f i x]) "

syntax
  "_list_indexed_map" :: "pttrn \<Rightarrow> 'a list \<Rightarrow> pttrn \<Rightarrow> 'b \<Rightarrow> 'b list" 
    ("(3\<section>map _ =/ _!_./ _)" [1000, 100, 1000, 10] 10)

translations
   "\<section>map x = xs!i. F"  \<rightleftharpoons> "CONST list_indexed_map (\<lambda> i x. F) xs"

lemma list_indexed_map_cong[fundef_cong]:
  assumes "xs = ys"
  assumes "\<And>i x. i < length ys \<Longrightarrow> x = ys!i \<Longrightarrow> F i x = G i x"
  shows "(\<section>map x = xs!i. F i x) = (\<section>map y = ys!i. G i y)"
  apply (simp add: list_indexed_map_def)
  apply (rule list_indexed_fold_cong)
  by (auto simp add: assms)

lemma "[9, 49] = (\<section>map x = [3 :: nat, 7]!i. x * x)"
  by (simp add: list_indexed_map_def shift_index_def)

lemma list_indexed_map_empty[simp]: "list_indexed_map F [] = []"
  by (simp add: list_indexed_map_def)

lemma list_indexed_map_append_gen1: "(\<section>fold acc = acc0, x = (as@bs)!i. acc @ [f i x]) = 
       (\<section>fold acc = (\<section>fold acc = acc0, x = as!i. acc @ [f i x]), x = 
          bs!i. acc @ [shift_index (length as) f i x])"
proof (induct as arbitrary: acc0 bs f)
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  show ?case by (auto, subst Cons, simp)    
qed

lemma list_indexed_map_append_gen2: 
  "(\<section>fold acc = as@bs, x = xs!i. acc @ [f i x]) = 
      as @ (\<section>fold acc = bs, x = xs!i. acc @ [f i x])"
proof (induct xs arbitrary: bs f)
  case Nil
  then show ?case by simp
next
  case (Cons c cs) 
  show ?case using Cons by simp
qed

lemma list_indexed_map_append:
  "(\<section>map x = (as@bs)!i. F i x) = (\<section>map x = as!i. F i x)@(\<section>map x = bs!i. shift_index (length as) F i x)"
  by (metis list_indexed_map_def append.right_neutral list_indexed_map_append_gen1 
      list_indexed_map_append_gen2) 

lemma list_indexed_map_single[simp]: "list_indexed_map F [a] = [F 0 a]"
  by (simp add: list_indexed_map_def)

lemma list_indexed_map_cons: "(\<section>map x = (a#as)!i. F i x) = F 0 a # (\<section>map x = as!i. shift_index 1 F i x)"
  using list_indexed_map_append[where as="[a]", simplified]
  by force        

lemma map_cons: "map f (a#as) = f a # (map f as)"
  by force

lemma map_snoc: "map f (as@[a]) = (map f as) @ [f a]"
  by auto

lemma "map (\<lambda>i. F i ((a # xs) ! i)) [0..<length xs] @ [F (length xs) ((a # xs) ! length xs)] =
       map (\<lambda>i. F i ((a # xs) ! i)) [0..<Suc(length xs)]"
  by simp

lemma map_eq_intro: 
  "length xs = length ys \<Longrightarrow> 
   (\<And> i. i < length xs \<Longrightarrow> f (xs!i) = g (ys!i)) \<Longrightarrow> 
   map f xs = map g ys"
  by (simp add: list_eq_iff_nth_eq)

lemma list_indexed_map_alt:
  "(\<section>map x = xs!i. F i x) = map (\<lambda> i. F i (xs!i)) [0 ..< length xs]"
proof (induct xs arbitrary: F)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have m1: "map (\<lambda>i. F i ((a # xs) ! i)) [0..<length xs] @ [F (length xs) ((a # xs) ! length xs)] =
        map (\<lambda>i. F i ((a # xs) ! i)) [0..<Suc(length xs)]"
    by simp
  have m2: "map (\<lambda>i. F (Suc i) (xs ! i)) [0..<length xs] =
        map (\<lambda> i. F i ((a#xs) ! i)) [Suc 0 ..< Suc(length xs)]"
    apply (rule map_eq_intro)
    apply auto
    using Suc_le_eq apply blast
    by (metis Suc_le_eq add_Suc comm_monoid_add_class.add_0 not_less_eq_eq not_less_zero 
        nth_Cons_Suc nth_upt upt_Suc_append zero_less_iff_neq_zero)
  have m3: "F 0 a # map (\<lambda>i. F i ((a # xs) ! i)) [Suc 0..<Suc (length xs)] = 
        map (\<lambda>i. F i ((a # xs) ! i)) [0..<Suc (length xs)]"
    by (metis (no_types, lifting) map_cons nth_Cons_0 upt_conv_Cons zero_less_Suc)
  show ?case 
    apply (auto simp add: list_indexed_map_cons)
    apply (subst Cons)
    apply (simp add: shift_index_def)
    apply (subst m1)
    apply (subst m2)
    apply (subst m3)
    by blast    
qed

lemma list_unindexed_map: "(\<section>map x = xs!i. F x) = map F xs"
proof (induct xs)
  case Nil
  then show ?case 
    by (simp add: list_indexed_map_def)
next
  case (Cons a xs)
  show ?case by (simp add: list_indexed_map_cons Cons)
qed

lemma list_indexed_map_length[simp]: "length (\<section>map x = xs!i. F i x) = length xs"
  by (simp add: list_indexed_map_alt)

lemma list_indexed_map_at[simp]: "i < length xs \<Longrightarrow> (\<section>map x = xs!i. F i x) ! i = F i (xs!i)"
  by (simp add: list_indexed_map_alt)

subsubsection \<open>Fold over Indexed Map\<close>

lemma fold_indexed_map: "(\<section>fold acc = a, x = xs!i. g (F i x) acc) = fold g (\<section>map x=xs!i. F i x) a"
proof (induct xs arbitrary: a F)
  case Nil
  show ?case by simp
next
  case (Cons u us)
  show ?case using Cons
    by (simp add: list_indexed_map_cons shift_index_gather)
qed

lemma fold_union: "fold (\<lambda>a b. b \<union> a) xs a0 = a0 \<union> \<Union> (set xs)"
proof (induct xs arbitrary: a0)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by auto
qed

lemma Un_indexed_nats: "(\<Union>i\<in>{0..<n::nat}. F i) = \<Union> { F i | i. i < n }" 
  by (auto, blast)

lemma union_indexed_fold: 
  "(\<section>fold X = X0, x = xs!i. X \<union> F i x) = X0 \<union> \<Union> { F i (xs!i) | i. i < length xs }"
  apply (subst fold_indexed_map)
  apply (subst fold_union)
  apply (subst list_indexed_map_alt)
  by (simp add: Un_indexed_nats)

lemma union_unindexed_fold:
  "(\<section>fold X = X0, x = xs!_. X \<union> F x) = X0 \<union> \<Union> { F x | x. x \<in> set xs }"
  apply (subst union_indexed_fold)
  by (metis in_set_conv_nth)

subsection \<open>Other\<close>

type_synonym ('a, 'b) map = "'a \<Rightarrow> 'b option"

definition map_forced_get :: "('a, 'b) map \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "!!" 100) where
  "m !! x = the (m x)" 

end