theory Utilities 
  imports 
    ZF 
    "Forcing/Forcing_Main"
begin 

lemma function_value : "x \<in> D \<Longrightarrow> { <y, f(y)>. y \<in> D }`x = f(x)" 
proof - 
  fix x assume p1 : "x \<in> D"
  have "f(x) \<in> ({ <y, f(y)>. y \<in> D }``{x})" using p1 by auto
  then have "({ <y, f(y)>. y \<in> D }``{x}) = { f(x) }" 
    apply (rule_tac b="f(x)" and a = "f(x)" in equal_singleton)
    by auto 
  then have p2 : "(\<Union>({ <y, f(y)>. y \<in> D }``{x})) = f(x)" by auto 
  have "({ <y, f(y)>. y \<in> D })`x = (\<Union>({ <y, f(y)>. y \<in> D }``{x}))" 
    unfolding ZF_Base.apply_def by auto 
  then show "({ <y, f(y)>. y \<in> D })`x = f(x)" using p2 by auto 
qed

lemma function_value_in : "f \<in> A \<rightarrow> B \<Longrightarrow> a \<in> A \<Longrightarrow> f`a \<in> B" 
  by auto 

lemma relation_subset_domran : 
  "relation(C) \<Longrightarrow> x \<in> C \<Longrightarrow> x \<in> domain(C) \<times> range(C)" 
proof - 
  assume assms: "relation(C)" "x \<in> C"
  then obtain a b where abh: "x = <a, b>" unfolding relation_def by auto 
  then have adom : "a \<in> domain(C)" unfolding domain_def using assms by auto
  have "b \<in> range(C)" using rangeI abh assms by auto 
  then have "<a, b> \<in> domain(C) \<times> range(C)" using adom by auto 
  then show "x \<in>  domain(C) \<times> range(C)" using abh by auto 
qed

lemma pair_rel_arg : 
  "relation(C) \<Longrightarrow> v \<in> { F(x, y) . <x, y> \<in> C } \<Longrightarrow> \<exists>x. \<exists>y. <x, y> \<in> C \<and> v = F(x, y)"
proof - 
  assume assms: "relation(C)" "v \<in> { F(x, y) . <x, y> \<in> C }" 
  then obtain u where i: "u \<in> C" "v = split(F, u)" by auto 
  then have h : "v = F(fst(u), snd(u))" unfolding split_def i by auto 
  have "<fst(u), snd(u)> = u" 
    apply (rule_tac a=u and A="domain(C)" and B="\<lambda>x. range(C)" in pair.Pair_fst_snd_eq)
    apply (rule_tac relation_subset_domran) 
    using assms i by auto
  then have "<fst(u), snd(u)> \<in> C" using i by auto 
  then show ?thesis using h by auto 
qed

lemma pair_relI : "<a, b> \<in> x \<Longrightarrow> F(a, b) \<in> { F(a, b). <a, b> \<in> x }"
  apply auto apply (rule_tac x="<a, b>" in bexI) apply auto done 

lemma eq_flip : "A = B \<Longrightarrow> B = A" by auto 

lemma pair_rel_eq : 
  "relation(C)
   \<Longrightarrow> (\<forall>x. \<forall>y. <x, y> \<in> C \<longrightarrow> F(x, y) = G(x, y)) 
   \<Longrightarrow> { F(x, y). <x, y> \<in> C } = { G(x, y). <x, y> \<in> C }" 
  apply (rule equality_iffI; rule iffI)
proof - 
  fix v assume assms :
    "relation(C)"
    "\<forall>x. \<forall>y. <x, y> \<in> C \<longrightarrow> F(x, y) = G(x, y)" 
    "v \<in> {F(x, y) . \<langle>x,y\<rangle> \<in> C}"
  then have "\<exists>x y. \<langle>x, y\<rangle> \<in> C \<and> v = F(x, y)" 
    by (rule_tac pair_rel_arg; auto)
  then obtain x y where p1 : "<x, y> \<in> C" "v=F(x, y)" by auto
  then have p2 : "v = G(x, y)" using assms by auto 
  then have p3 : "v = split(G, <x, y>)" using p2 by auto 
  then show "v \<in> {G(x, y) . \<langle>x,y\<rangle> \<in> C}" 
    apply simp
    apply (rule_tac x="<x,y>" in bexI)
    using p1 p2 p3 by auto 
next 
  fix v assume assms :
    "relation(C)" 
    "\<forall>x. \<forall>y. <x, y> \<in> C \<longrightarrow> F(x, y) = G(x, y)" 
    "v \<in> {G(x, y) . \<langle>x,y\<rangle> \<in> C}"
  then have "\<exists>x y. \<langle>x, y\<rangle> \<in> C \<and> v = G(x, y)" 
    by (rule_tac pair_rel_arg; auto)
  then obtain x y where p1 : "<x, y> \<in> C" "v=G(x, y)" using pair_rel_arg by auto 
  then have p2 : "v = F(x, y)" using assms by auto 
  then have p3 : "v = split(F, <x, y>)" using p2 by auto 
  then show "v \<in> {F(x, y) . \<langle>x,y\<rangle> \<in> C}" 
    apply simp
    apply (rule_tac x="<x,y>" in bexI)
    using p1 p2 p3 by auto 
qed


lemma OUN_UN_equals : "Ord(a) \<Longrightarrow> (\<Union> b < a. F(b)) = (\<Union> b \<in> a . F(b))" 
  apply (rule equality_iffI; rule iffI)
proof - 
  fix x assume "x \<in> (\<Union> b < a. F(b))" 
  then obtain b where bp :  "b < a" "x \<in> F(b)" using OUN_iff by auto 
  then have "b \<in> a" using ltD by auto 
  then have "\<exists> b \<in> a. x \<in> F(b)" using bp by auto 
  then show "x \<in> (\<Union> b \<in> a . F(b))" using UN_iff by auto 
next 
  fix x assume assms : "x \<in> (\<Union> b \<in> a . F(b))" "Ord(a)"
  then obtain b where bp :  "b \<in> a" "x \<in> F(b)" using UN_iff by auto
  then have "b < a" using \<open>b \<in> a\<close> \<open>Ord(a)\<close> ltI by auto 
  then have "\<exists>b < a. x \<in> F(b)" using bp by auto 
  then show "x \<in> (\<Union> b < a. F(b))" by auto 
qed

lemma lt_le_lt : "a < b \<Longrightarrow> b \<le> c \<Longrightarrow> a < c" 
  apply (rule_tac i=b and j=c in leE)
  apply assumption 
  using lt_trans by auto

lemma le_lt_lt : "a \<le> b \<Longrightarrow> b < c \<Longrightarrow> a < c"  
  apply (rule_tac i=a and j=b in leE)
  apply assumption 
  using lt_trans by auto

lemma le_succ_le : "Ord(b) \<Longrightarrow> a \<le> b \<Longrightarrow> a \<le> succ(b)" 
  apply (rule_tac j=b in le_trans) 
  apply simp
  apply (rule_tac j="succ(b)" in lt_trans) 
  using le_refl by auto

lemma lt_succ_lt : "Ord(b) \<Longrightarrow> a < b \<Longrightarrow> a < succ(b)" 
  apply (rule_tac j=b in lt_trans) 
  using le_refl by auto
    

lemma ex_larger_limit : "Ord(a) \<Longrightarrow> \<exists>b. a < b \<and> Limit(b)"
proof -
  assume assm : "Ord(a)"
  have p1 : "Card(csucc(a))" "a < csucc(a)" using assm csucc_basic by auto
  then have p2 : "csucc(a) \<le> (csucc(a) \<oplus> nat)" using cadd_le_self by auto
  have p3 : "Ord(csucc(a))" using p1 Card_is_Ord by auto
  have p4 : "Ord(nat)" by auto 
  have p5 : "Card(nat)" using Ord_nat_subset_into_Card by auto 
  then have p6 : "nat \<le> (nat \<oplus> csucc(a))" using p3 cadd_le_self by auto
  then have p7 : "nat \<le> (csucc(a) \<oplus> nat)" using cadd_commute by auto 
  have p8 : "Card(csucc(a) \<oplus> nat)" "Ord(csucc(a) \<oplus> nat)" unfolding cadd_def by auto 
  then have p9 : "InfCard(csucc(a) \<oplus> nat)" unfolding InfCard_def 
    using p7 by auto 
  then have p10 : "Limit(csucc(a) \<oplus> nat)" using InfCard_is_Limit by auto 
  have p11 : "a < csucc(a) \<oplus> nat" 
    apply (rule_tac P="csucc(a) < (csucc(a) \<oplus> nat)" and Q = "csucc(a) = (csucc(a) \<oplus> nat)" in disjE) 
  proof - 
    show "csucc(a) < csucc(a) \<oplus> nat \<or> csucc(a) = csucc(a) \<oplus> nat" 
      using le_iff p2 by auto 
  next 
    assume "csucc(a) < csucc(a) \<oplus> nat" 
    then show "a < csucc(a) \<oplus> nat" 
      using lt_trans p1 by auto 
  next 
    assume "csucc(a) = csucc(a) \<oplus> nat" 
    then show "a < csucc(a) \<oplus> nat" using p1 by auto 
  qed
  then show ?thesis using p10 by auto 
qed


lemma UN_RepFunI : "a \<in> b \<Longrightarrow> x \<in> F(a) \<Longrightarrow> x \<in> (\<Union>a \<in> b. F(a))" 
  by auto
lemma OUN_RepFunI : "a < b \<Longrightarrow> x \<in> F(a) \<Longrightarrow> x \<in> (\<Union>a < b. F(a))"
  by auto 

lemma RepFun_eq : "\<forall>x \<in> A. (\<exists>y \<in> B. F(x) = G(y))
                   \<Longrightarrow> \<forall>y \<in> B. (\<exists>x \<in> A. G(y) = F(x))
                   \<Longrightarrow> { F(x) . x \<in> A } = { G(y) . y \<in> B} " 
  apply (rule_tac equality_iffI; rule iffI)
proof - 
  fix v assume assms : "v \<in> {F(x) . x \<in> A}" "\<forall>x\<in>A. \<exists>y\<in>B. F(x) = G(y)" 
  then obtain x where vp: "v = F(x)" "x \<in> A" by auto 
  then obtain y where yp: "F(x) = G(y)" "y \<in> B" using assms by auto
  then have "v = G(y)" using vp by auto 
  then show "v \<in> {G(y) . y \<in> B}" using yp by auto 
next                  
  fix v assume assms : "v \<in> {G(x) . x \<in> B}" "\<forall>x\<in>B. \<exists>y\<in>A. G(x) = F(y)" 
  then obtain x where vp: "v = G(x)" "x \<in> B" by auto 
  then obtain y where yp: "G(x) = F(y)" "y \<in> A" using assms by auto
  then have "v = F(y)" using vp by auto 
  then show "v \<in> {F(y) . y \<in> A}" using yp by auto 
qed


lemma pair_ball_mp :
  "C \<subseteq> D \<times> E \<Longrightarrow> \<forall><d, e> \<in> C. P(d, e)
   \<Longrightarrow> \<forall>d \<in> D. \<forall>e \<in> E. P(d, e) \<longrightarrow> Q(d, e) \<Longrightarrow> \<forall><d, e> \<in> C. Q(d, e)" 
proof (clarify)
  fix x
  assume assms: "\<forall>\<langle>d,e\<rangle>\<in>C. P(d, e)" " \<forall>d\<in>D. \<forall>e\<in>E. P(d, e) \<longrightarrow> Q(d, e)" "x \<in> C" "C \<subseteq> D \<times> E" 
  then obtain d e where de : "x = <d, e>" "d \<in> D" "e \<in> E" by auto
  then have "P(d, e)" using assms by auto 
  then have "Q(d, e)" using de assms by auto 
  then show "(\<lambda>\<langle>d,e\<rangle>. Q(d, e))(x)" using de by auto
qed

lemma pair_ball_conj : 
  "C \<subseteq> D \<times> E \<Longrightarrow> \<forall><d, e> \<in> C. P(d, e) \<Longrightarrow> \<forall><d, e> \<in> C. Q(d, e) \<Longrightarrow> \<forall><d, e> \<in> C. P(d, e) \<and> Q(d,e)" 
proof (clarify)
  fix x
  assume assms: "\<forall>\<langle>d,e\<rangle>\<in>C. P(d, e)" "\<forall>\<langle>d,e\<rangle>\<in>C. Q(d, e)" "x \<in> C" "C \<subseteq> D \<times> E" 
  then obtain d e where de : "x = <d, e>" "d \<in> D" "e \<in> E" by auto
  then have p1:"P(d, e)" using assms by auto 
  then have p2:"Q(d, e)" using de assms by auto 
  then show " (\<lambda>\<langle>d,e\<rangle>. P(d, e) \<and> Q(d, e))(x)" using de p1 p2 by auto
qed

lemma inter_eq : "A = B \<Longrightarrow> A \<inter> C = B \<inter> C" by auto 

lemma iff_flip : "A \<longleftrightarrow> B \<Longrightarrow> B \<longleftrightarrow> A" by auto 

lemma empty_or_not : "\<And>x. (x = 0 \<longrightarrow> P(x)) \<Longrightarrow> (x \<noteq> 0 \<longrightarrow> P(x)) \<Longrightarrow> P(x)"
  by auto

lemma Ord_nat' : "m \<in> nat \<Longrightarrow> Ord(m)" 
  using lt_Ord ltI Ord_nat by auto

lemma in_dom_or_not : "\<And>P F x. function(F) \<Longrightarrow> P(0) \<Longrightarrow> (x \<in> domain(F) \<Longrightarrow> P(F`x)) \<Longrightarrow> P(F`x)" 
proof - 
 fix P F x 
 assume assm : "function(F)" "P(0)" "(x \<in> domain(F) \<Longrightarrow> P(F`x))"
 show "P(F`x)" 
 proof (cases "x \<in> domain(F)")
   case True
   then show ?thesis using assm by auto
 next
   case False
   then have "F`x = 0" unfolding apply_def ZF_Base.image_def domain_def by auto 
   then show "P(F`x)" using assm by auto 
 qed
qed

lemma pair_forallI : 
  "\<And>A x. relation(x) \<Longrightarrow> (\<And>y p. <y, p> \<in> x \<Longrightarrow> A(y, p)) \<Longrightarrow> \<forall><y, p> \<in> x. A(y, p)"
proof (clarify) 
  fix A x v assume assms : "relation(x)""(\<And>y p. \<langle>y, p\<rangle> \<in> x \<Longrightarrow> A(y, p))""v \<in> x" 
  then obtain y p where yph : "v = <y, p>" unfolding relation_def by auto 
  then have "A(y, p)" using assms by auto 
  then show "(\<lambda>\<langle>y,p\<rangle>. A(y, p))(v)" using assms yph by auto 
qed

lemma pair_forallD : 
  "\<And>A x. relation(x) \<Longrightarrow> \<forall><y, p> \<in> x. A(y, p) \<Longrightarrow> (\<And>y p. <y, p> \<in> x \<Longrightarrow> A(y, p))"
proof (simp)
  fix A x assume assms : "relation(x)" "\<forall>v\<in>x. (\<lambda>\<langle>y,p\<rangle>. A(y, p))(v)"
  show "\<And>y p. \<langle>y, p\<rangle> \<in> x \<Longrightarrow> A(y, p)"
  proof - 
    fix y p assume "<y, p> \<in> x" 
    then show "A(y, p)" using assms by auto
  qed
qed

lemma pair_forallE : 
  "\<And>A Q x. relation(x) \<Longrightarrow> \<forall><y, p> \<in> x. A(y, p) \<Longrightarrow> ((\<And>y p. <y, p> \<in> x \<Longrightarrow> A(y, p)) \<Longrightarrow> Q) \<Longrightarrow> Q" 
proof - 
  fix A Q x assume "relation(x)" "\<forall><y, p> \<in> x. A(y, p)" and r: "((\<And>y p. <y, p> \<in> x \<Longrightarrow> A(y, p)) \<Longrightarrow> Q)" 
  then show "Q" 
    apply (rule_tac r) 
    apply (rule_tac x=x in pair_forallD) 
    by auto 
qed

lemma converse_apply : "f \<in> bij(A, B) \<Longrightarrow> x \<in> A \<Longrightarrow> converse(f) ` (f ` x) = x" 
proof - 
  assume assms : "f \<in> bij(A, B)" "x \<in> A"                   
  then have "A \<subseteq> domain(f)" using bij_is_fun unfolding Pi_def by auto 
  then have "<x, f`x> \<in> f"  
    apply (rule_tac function_apply_Pair) using bij_is_fun assms unfolding Pi_def apply simp
    using bij_is_fun assms by auto
  then have H: "<f`x, x> \<in> converse(f)" apply (rule_tac converseI) apply simp done 
  have "converse(f) \<in> bij(B, A)" using bij_converse_bij assms by auto 
  then have "converse(f) \<in> B \<rightarrow> A" using bij_is_fun  by auto 
  then show "converse(f) ` (f ` x) = x" using apply_fun H by auto 
qed

lemma image_converse_image : "f \<in> bij(A, B) \<Longrightarrow> C \<subseteq> A \<Longrightarrow> converse(f) `` (f `` C) = C" 
  apply (rule equality_iffI) 
  apply (rule iffI) 
proof - 
  fix x assume assms : "f \<in> bij(A, B) " "C\<subseteq>A" "x \<in> converse(f) `` (f `` C)" 
  then obtain y where yh : "y \<in> f``C" "<y, x> \<in> converse(f)" using image_iff by auto 
  then have "<x, y> \<in> f" using converseE by auto 
  then have H : "x \<in> A \<and> f`x = y" 
    apply (rule_tac B="(\<lambda>_. B)" in apply_fun) 
    using bij_is_fun assms by auto 
  then obtain z where zh: "z \<in> C" "<z, y> \<in> f" using yh image_iff by auto 
  then have H2 : "z \<in> A \<and> f`z = y" 
    apply (rule_tac B="(\<lambda>_. B)" in apply_fun) 
    using bij_is_fun assms by auto 
  have "f \<in> inj(A, B)" using bij_is_inj assms by auto 
  then have "x=z" unfolding inj_def using H H2 by auto 
  then show "x \<in> C" using zh by auto 
next 
  fix x assume assms : "f \<in> bij(A, B) " "C\<subseteq>A" "x \<in> C"
  then have "f`x \<in> f``C" 
    apply (rule_tac a=x in imageI) 
    apply (rule_tac function_apply_Pair) 
    using bij_is_fun unfolding Pi_def apply simp_all apply blast done
  then show "x \<in> converse(f) `` (f``C)" 
    apply (rule_tac a="f`x" in imageI) 
    apply (rule_tac converseI)
    apply (rule_tac function_apply_Pair)
    using bij_is_fun assms unfolding Pi_def apply simp_all apply blast done
qed  

lemma ifT_eq : "a \<noteq> b \<Longrightarrow> (if P then a else b) = a \<Longrightarrow> P" 
  apply (rule_tac P=P and Q="\<not>P" in disjE) apply simp_all done 

lemma ifF_eq : "a \<noteq> b \<Longrightarrow> (if P then a else b) = b \<Longrightarrow> \<not>P" 
  apply (rule_tac P=P and Q="\<not>P" in disjE) apply simp_all done 

lemma neq_flip : "a \<noteq> b \<Longrightarrow> b \<noteq> a" by auto

lemma iff_eq : "\<And>A P Q. (\<And>x. x \<in> A \<Longrightarrow> P(x) \<longleftrightarrow> Q(x)) \<Longrightarrow> { x \<in> A. P(x) } = { x \<in> A. Q(x) }" by auto

lemma ex_iff : "\<And>A P Q. (\<And>x. x \<in> A \<Longrightarrow> P(x) \<longleftrightarrow> Q(x)) \<Longrightarrow> (\<exists>x \<in> A. P(x)) \<longleftrightarrow> (\<exists>x \<in> A. Q(x))" by auto (*todo : bex_iff ni rename *)
lemma all_iff : "\<And>A P Q. (\<And>x. P(x) \<longleftrightarrow> Q(x)) \<Longrightarrow> (\<forall>x. P(x)) \<longleftrightarrow> (\<forall>x. Q(x))" by auto 
lemma ball_iff : "\<And>A P Q. (\<And>x. x \<in> A \<Longrightarrow> P(x) \<longleftrightarrow> Q(x)) \<Longrightarrow> (\<forall>x \<in> A. P(x)) \<longleftrightarrow> (\<forall>x \<in> A. Q(x))" by auto 
lemma iff_disjI : "\<And>P Q R S. P \<longleftrightarrow> Q \<Longrightarrow> R \<longleftrightarrow> S \<Longrightarrow> P \<or> R \<longleftrightarrow> Q \<or> S" by auto
lemma iff_conjI : "\<And>P Q R S. P \<longleftrightarrow> Q \<Longrightarrow> R \<longleftrightarrow> S \<Longrightarrow> P \<and> R \<longleftrightarrow> Q \<and> S" by auto
lemma iff_conjI2 : "\<And>P Q R S. P \<longleftrightarrow> Q \<Longrightarrow> (Q \<Longrightarrow> R \<longleftrightarrow> S) \<Longrightarrow> (P \<and> R \<longleftrightarrow> Q \<and> S)" by auto 
lemma iff_iff : "\<And>P Q R S. P \<longleftrightarrow> Q \<Longrightarrow> R \<longleftrightarrow> S \<Longrightarrow> (P \<longleftrightarrow> R) \<longleftrightarrow> (Q \<longleftrightarrow> S)" by auto  
lemma imp_iff : "\<And>P Q R S. P \<longleftrightarrow> Q \<Longrightarrow> (R \<longleftrightarrow> S) \<Longrightarrow> (P \<longrightarrow> R) \<longleftrightarrow> (Q \<longrightarrow> S)" by auto
lemma imp_iff2 : "\<And>P Q R S. P \<longleftrightarrow> Q \<Longrightarrow> (Q \<Longrightarrow> R \<longleftrightarrow> S) \<Longrightarrow> (P \<longrightarrow> R) \<longleftrightarrow> (Q \<longrightarrow> S)" by auto  

lemma max_le1 : "Ord(a) \<Longrightarrow> Ord(b) \<Longrightarrow> a \<le> a \<union> b" (*todo : Un_upper1_le ni okikae *)
  using le_Un_iff le_refl by auto

lemma max_le2 : "Ord(a) \<Longrightarrow> Ord(b) \<Longrightarrow> b \<le> a \<union> b" (*todo : Un_upper2_le ni okikae *)
  using le_Un_iff le_refl by auto  

lemma zero_le : "\<And>i. Ord(i) \<Longrightarrow> 0 \<le> i" 
  apply(rule mp)
  apply(rule_tac P="\<lambda>i. Ord(i) \<longrightarrow> 0 \<le> i" in eps_induct, rule impI)
  apply(rename_tac i x, case_tac "\<exists>y. y \<in> x")
   apply clarify 
    apply(rule lt_succ_lt, simp)
    apply(rename_tac i x y, rule_tac b=y in le_lt_lt)
  using Ord_in_Ord ltI 
     apply auto[2]
   apply(rename_tac i x, rule_tac b=x and a=0 in ssubst)
  by auto

lemma Ord_un_eq1 : "Ord(a) \<Longrightarrow> Ord(b) \<Longrightarrow> b \<le> a \<Longrightarrow> a \<union> b = a"
  apply(rule leE) 
    apply simp
   apply(subst Ord_Un_if) 
  by simp_all

lemma Ord_un_eq2 : "Ord(a) \<Longrightarrow> Ord(b) \<Longrightarrow> a \<le> b \<Longrightarrow> a \<union> b = b"
  apply(subst Un_commute)
  apply(rule Ord_un_eq1) 
  by auto

lemma pred_le' : "a \<in> nat \<Longrightarrow> b \<in> nat \<Longrightarrow> a \<le> b \<Longrightarrow> pred(a) \<le> pred(b)" 
  apply(rule_tac n=b in natE)
    apply simp
   apply(subgoal_tac "a = 0", simp, simp, simp)
  using pred_le 
  by auto

lemma domain_elem_rank_lt : "y \<in> domain(x) \<Longrightarrow> rank(y) < rank(x)" 
proof - 
  assume "y \<in> domain(x)" 
  then obtain p where "<y, p> \<in> x" by auto 
  then show "rank(y) < rank(x)" 
    apply(rule_tac j="rank(<y, p>)" in lt_trans)
     apply(rule rank_pair1, rule rank_lt, simp)
    done
qed

lemma final_app_notation : 
  fixes l assumes lin : "l \<in> list(A)" and lnotnil : "l \<noteq> []"
  shows "\<exists>l' \<in> list(A). \<exists> a \<in> A. l = l' @ [a]" 

  apply(rule_tac P="l \<noteq> [] \<longrightarrow> (\<exists>l' \<in> list(A). \<exists> a \<in> A. l = l' @ [a])" in mp)  
  using lnotnil apply simp
  using lin
proof (induct)
  case Nil 
  then show ?case by auto
next
  case (Cons a l')
  then show ?case
    apply(cases "l' = []") apply clarify apply(rule_tac x="[]" in bexI) apply(rule_tac x=a in bexI) apply simp_all 
  proof - 
    assume "\<exists>l'a\<in>list(A). \<exists>a\<in>A. l' = l'a @ [a]" 
    then obtain l'' t where "t \<in> A" "l'' \<in> list(A)" "l' = l'' @ [t]" by auto 
    then show "\<exists>l'a\<in>list(A). \<exists>aa\<in>A. Cons(a, l') = l'a @ [aa]" 
      apply(rule_tac x="Cons(a, l'')" in bexI) 
      apply(rule_tac x=t in bexI) using \<open>a \<in> A\<close> apply simp_all done 
  qed
qed

lemma length1_notation : 
  fixes l assumes "l \<in> list(A)"  "length(l) = 1" 
  shows "\<exists>a \<in> A. l = [a]" 
proof - 
  have "l \<noteq> Nil" using assms length_is_0_iff by auto 
  then have "\<exists>l' \<in> list(A). \<exists> a \<in> A. l = l' @ [a]" using final_app_notation assms by auto 
  then obtain l' a where H: "l' \<in> list(A)" "a \<in> A" "l = l' @ [a]" by auto 
  then have "l = [a]" using assms by auto
  then show ?thesis using H by auto
qed 

lemma not_nil_obtain_hd_tl : 
  fixes A l assumes "l \<in> list(A)" "l \<noteq> Nil" 
  shows "\<exists>hd \<in> A. \<exists>tl \<in> list(A). l = Cons(hd, tl)" 

  using \<open>l \<in> list(A)\<close> apply cases using assms apply simp 
  by auto 

lemma append_notation : 
  fixes l n assumes "l \<in> list(A)" "n \<in> nat" "n \<le> length(l)" 
  shows "\<exists>l1 \<in> list(A). \<exists>l2 \<in> list(A). length(l1) = n \<and> l = l1 @ l2" 
  apply(rule_tac P="\<forall>n \<in> nat. n \<le> length(l) \<longrightarrow> ( \<exists>l1 \<in> list(A). \<exists>l2 \<in> list(A). length(l1) = n \<and> l = l1 @ l2 )" in mp) 
  using assms apply simp apply clarify 
  using \<open>l \<in> list(A)\<close>
proof (induct)
  case Nil
  then have "n = 0" by auto  
  then show ?case 
    apply(rule_tac x=Nil in bexI)
    apply(rule_tac x=Nil in bexI)
    by auto 
next
  case (Cons hd tl)
  then show ?case 
    apply(rule_tac n=n in natE) apply simp apply simp
  proof - 
    fix n' assume assms1: "n = succ(n')" "n' \<in> nat" "n \<le> length(Cons(hd, tl))" "hd \<in> A " "tl \<in> list(A)" 
      "(\<And>n. n \<in> nat \<Longrightarrow> n \<le> length(tl) \<Longrightarrow> \<exists>l1\<in>list(A). \<exists>l2\<in>list(A). length(l1) = n \<and> tl = l1 @ l2)" 

    then have "n' \<le> length(tl)" by auto 
    then have "\<exists>l1\<in>list(A). \<exists>l2\<in>list(A). length(l1) = n' \<and> tl = l1 @ l2" using assms1 by auto 
    then obtain l1 l2 where H : "l1 \<in> list(A)" "l2 \<in> list(A)" "length(l1) = n'" "tl = l1 @ l2" by auto 
    then show "\<exists>l1\<in>list(A). \<exists>l2\<in>list(A). length(l1) = n \<and> Cons(hd, tl) = l1 @ l2" 
      apply(rule_tac x="Cons(hd, l1)" in bexI)
      apply(rule_tac x=l2 in bexI) 
      using assms1 H by auto 
  qed
qed

lemma Pi_memberI : "relation(f) \<Longrightarrow> function(f) \<Longrightarrow> A = domain(f) \<Longrightarrow> range(f) \<subseteq> B \<Longrightarrow> f \<in> Pi(A, \<lambda>_. B)"
  apply(rule_tac iffD2) apply(rule_tac Pi_iff) apply simp apply(rule subsetI)   
proof - 
  fix x assume assms : "x \<in> f" "relation(f)" "function(f)" "A = domain(f)" "range(f) \<subseteq> B"
  then obtain a b where abH : "x = <a, b>" unfolding relation_def by auto 
  then have "a \<in> A \<and> b \<in> B" using assms apply auto done 
  then show "x \<in> domain(f) \<times> B" using assms abH by auto
qed

lemma domain_Pi : "f \<in> A \<rightarrow> B \<Longrightarrow> domain(f) = A" 
  unfolding Pi_def 
  by auto

lemma function_eq_helper : "\<And>A B C f g. f \<in> A \<rightarrow> B \<Longrightarrow> g \<in> A \<rightarrow> C \<Longrightarrow> \<forall>x \<in> A. f`x = g`x \<Longrightarrow> f = g" 
  apply (rule_tac equality_iffI)
proof -
  
  have helper :  "\<And>A B f x. f \<in> A \<rightarrow> B \<Longrightarrow> x \<in> f \<longleftrightarrow> (\<exists>a \<in> A. x = <a, f`a>)" 
  proof (rule iffI)
    fix A B f x assume assms : "f \<in> A \<rightarrow> B" "x \<in> f" 
    then obtain a b where abH : "a \<in> A" "<a, b> = x" unfolding Pi_def by auto 
    then have "b = f`a" using apply_equality assms by auto 
    then show "\<exists>a\<in>A. x = <a, f`a>" using abH by auto 
  next 
    fix A B f x assume assms : "f \<in> A \<rightarrow> B" "\<exists>a\<in>A. x = \<langle>a, f ` a\<rangle>" 
    then obtain a where aH : "a \<in> A" "x = <a, f`a>" by auto 
    then have "<a, f`a> \<in> f" 
      apply (rule_tac function_apply_Pair) using assms Pi_iff aH by auto 
    then show "x \<in> f" using aH by auto
  qed

  fix A B C f g x assume assms : "f \<in> A \<rightarrow> B" "g \<in> A \<rightarrow> C" "\<forall>x \<in> A. f`x = g`x"  
  have H1:"x \<in> f \<longleftrightarrow> (\<exists>a \<in> A. <a, f`a> = x)" apply (rule_tac iffI) using helper assms by auto 
  have H2:"... \<longleftrightarrow> (\<exists>a \<in> A. <a, g`a> = x)" using assms by auto
  have H3:"... \<longleftrightarrow> x \<in> g" using helper assms by auto 
  show " x \<in> f \<longleftrightarrow> x \<in> g " using H1 H2 H3 by auto 
qed

lemma function_eq : "\<And>f g. relation(f) \<Longrightarrow> relation(g) \<Longrightarrow> function(f) \<Longrightarrow> function(g) \<Longrightarrow> domain(f) = domain(g) \<Longrightarrow> (\<And>x. x \<in> domain(f) \<Longrightarrow> f`x = g`x) \<Longrightarrow> f = g" 
  apply(rule_tac A="domain(f)" and B="range(f)" and C="range(g)" in function_eq_helper)
    apply(rule Pi_memberI)
  apply simp_all
    apply(rule Pi_memberI)
     apply simp_all
  done

lemma nat_in_nat : "n \<in> nat \<Longrightarrow> m \<in> n \<Longrightarrow> m \<in> nat"
  by(rule lt_nat_in_nat, rule ltI, simp_all)

lemma union_in_nat : "n \<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> n \<union> m \<in> nat" 
  by auto

lemma add_diff_swap : 
  fixes a b c 
  assumes "a \<in> nat" "b \<in> nat" "c \<in> nat" "c \<le> b"
  shows "a #+ b #- c = a #+ (b #- c)"
proof - 
  have "c #+ (a #+ b #- c) = (a #+ b #- c) #+ c" by auto 
  also have "... = a #+ b" 
    apply(rule add_diff_inverse2)
     apply(rule_tac j=b in le_trans)
    using assms 
    by auto
  also have "... = a #+ ((b #- c) #+ c)" 
    apply(rule_tac i=a and j = a in add_left_cancel, simp, simp add:assms)
      apply(subst add_diff_inverse2)
    using assms 
    by auto
  also have "... = c #+ (a #+ (b #- c))" by auto 

  finally show ?thesis 
    apply(rule_tac i=c and j=c in add_left_cancel)
    by auto
qed

lemma le_succ_pred : 
  "\<And>n. n \<in> nat \<Longrightarrow> n \<le> succ(pred(n))" 
  apply(rule_tac n=n in natE)
  by auto

lemma relation_recfun : 
  assumes "is_recfun(r, x, H, f)" 
  shows "relation(f)"

  using assms 
  unfolding is_recfun_def 
  apply(rule_tac a="(\<lambda>x\<in>r -`` {x}. H(x, restrict(f, r -`` {x})))" and b=f in ssubst, simp)
  apply(rule relation_lam)
  done


end 