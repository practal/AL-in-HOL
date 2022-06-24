theory BTerm imports Locales
begin

section \<open>De Bruijn Term\<close>

subsection \<open>Terms\<close>

datatype bterm = 
  FreeVar variable \<open>bterm list\<close>
| BoundVar nat
| Abstr abstraction \<open>bterm list\<close>

subsection \<open>Free Atoms\<close>

datatype atom =
  Var variable nat
| Unbound nat 

type_synonym atoms = "atom set"

context sigloc begin

fun freeAtomsAt :: "nat \<Rightarrow> bterm \<Rightarrow> atoms" where 
  "freeAtomsAt level (FreeVar x ts) = 
     (\<section>fold atoms = {Var x (length ts)}, t=ts!_. atoms \<union> freeAtomsAt level t)"
| "freeAtomsAt level (BoundVar i) = 
     (if i < level then {} else {Unbound (i - level)})"
| "freeAtomsAt level (Abstr a ts) = 
     (\<section>fold atoms = {}, t=ts!_. atoms \<union> freeAtomsAt (level + \<section>v a) t)" 

definition freeAtoms :: "bterm \<Rightarrow> atoms" where
  "freeAtoms t = freeAtomsAt 0 t"

definition unboundAtoms :: "nat set \<Rightarrow> atoms" ("\<up>") where
  "\<up>ubs = { Unbound u | u. u \<in> ubs }"

subsection \<open>Wellformedness\<close>

fun bt_wf :: "bterm \<Rightarrow> bool" where
  "bt_wf (FreeVar x ts) = (\<forall> t=ts!_. bt_wf t)"
| "bt_wf (BoundVar i) = True"
| "bt_wf (Abstr a ts) = (\<checkmark>a \<and> \<section>a a = length ts \<and> 
     (\<forall> t=ts!i. bt_wf t \<and> freeAtoms t \<inter> \<up>(nats (\<section>v a)) \<subseteq> \<up>(a!\<natural>i)))"

end

end