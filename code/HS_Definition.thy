theory HS_Definition
  imports 
    Automorphism_Theorems
begin 

context forcing_data_Automorphism_M
begin

definition is_P_auto_group where 
  "is_P_auto_group(G) \<equiv> 
    G \<subseteq> { \<pi> \<in> P \<rightarrow> P. is_P_auto(\<pi>) } 
  \<and> (\<forall>\<pi> \<in> G. \<forall>\<tau> \<in> G. \<pi> O \<tau> \<in> G) 
  \<and> (\<forall>\<pi> \<in> G. converse(\<pi>) \<in> G)"   

definition P_auto_subgroups where "P_auto_subgroups(G) \<equiv> { H \<in> Pow(G) \<inter> M. is_P_auto_group(H) }" 

end

locale M_symmetric_system = forcing_data_Automorphism_M + 
  fixes \<G> \<F> 
  assumes \<G>_in_M : "\<G> \<in> M"  
  and \<G>_P_auto_group : "is_P_auto_group(\<G>)"   
  and \<F>_in_M : "\<F> \<in> M"
  and \<F>_subset : "\<F> \<subseteq> P_auto_subgroups(\<G>)" 
  and \<F>_nonempty : "\<F> \<noteq> 0" 
  and \<F>_closed_under_intersection : "\<forall>A \<in> \<F>. \<forall>B \<in> \<F>. A \<inter> B \<in> \<F>" 
  and \<F>_closed_under_supergroup : "\<forall>A \<in> \<F>. \<forall>B \<in> P_auto_subgroups(\<G>). A \<subseteq> B \<longrightarrow> B \<in> \<F>" 
  and \<F>_normal : "\<forall>H \<in> \<F>. \<forall>\<pi> \<in> \<G>. { \<pi> O \<tau> O converse(\<pi>). \<tau> \<in> H } \<in> \<F>" 
begin

definition sym where "sym(x) \<equiv> { \<pi> \<in> \<G>. Pn_auto(\<pi>)`x = x }"  

definition symmetric where "symmetric(x) \<equiv> sym(x) \<in> \<F>"  

definition HHS_set_succ where "HHS_set_succ(a, X) \<equiv> { x \<in> P_set(succ(a)). domain(x) \<subseteq> X \<and> symmetric(x) }" 

definition HS_set where "HS_set(a) \<equiv> transrec2(a, 0, HHS_set_succ)" 
definition HS where "HS \<equiv> { x \<in> P_names. \<exists>a. Ord(a) \<and> x \<in> HS_set(a) }" 

lemma HS_in_HS_set_succ' : "Ord(a) \<Longrightarrow> x \<in> HS_set(a) \<Longrightarrow> \<exists>b < a. Ord(b) \<and> x \<in> HS_set(succ(b))" 
  apply(rule_tac P="\<forall>x. x \<in> HS_set(a) \<longrightarrow> (\<exists>b < a. Ord(b) \<and> x \<in> HS_set(succ(b)))" in mp) 
   apply simp 
  apply(rule_tac P="\<lambda>a. \<forall>x. x \<in> HS_set(a) \<longrightarrow> (\<exists>b < a. Ord(b) \<and> x \<in> HS_set(succ(b)))" in trans_induct3_raw)  
     apply simp 
    apply(simp add:HS_set_def) 
   apply blast 
  apply clarify 
proof - 
  fix a x assume assms : "Limit(a)" "\<forall>b\<in>a. \<forall>x. x \<in> HS_set(b) \<longrightarrow> (\<exists>c < b. Ord(c) \<and> x \<in> HS_set(succ(c)))" "x \<in> HS_set(a)" 
  have "HS_set(a) = (\<Union>b<a. HS_set(b))" 
    unfolding HS_set_def using transrec2_Limit assms by auto 
  then obtain b where bH : "b < a" "x \<in> HS_set(b)" using assms by auto 
  then obtain c where cH : "c < b" "Ord(c) \<and> x \<in> HS_set(succ(c))" using assms ltD by blast  
  then have "c < a" using lt_trans bH by auto
  then show "\<exists>c < a. Ord(c) \<and> x \<in> HS_set(succ(c))" using cH by auto 
qed

lemma HS_in_HS_set_succ : "x \<in> HS \<Longrightarrow> \<exists>b. Ord(b) \<and> x \<in> HS_set(succ(b))" 
proof - 
  assume "x \<in> HS" 
  then obtain a where "Ord(a)" "x \<in> HS_set(a)" unfolding HS_def by auto 
  then show ?thesis using HS_in_HS_set_succ' by auto
qed

lemma HS_set_succ : "Ord(a) \<Longrightarrow> HS_set(succ(a)) = { x \<in> P_set(succ(a)). domain(x) \<subseteq> HS_set(a) \<and> symmetric(x) }" 
  unfolding HS_set_def 
  apply(rule_tac b="transrec2(succ(a), 0, HHS_set_succ)" and a="HHS_set_succ(a, transrec2(a, 0, HHS_set_succ))" in ssubst)
   apply(rule transrec2_succ) 
  unfolding HHS_set_succ_def 
  by simp

lemma HS_set_subset : "Ord(a) \<Longrightarrow> HS_set(a) \<subseteq> P_set(a)" 
  apply(rule_tac P="Ord(a) \<longrightarrow> HS_set(a) \<subseteq> P_set(a)" in mp) 
   apply simp 
  apply(rule_tac P="\<lambda>a. Ord(a) \<longrightarrow> HS_set(a) \<subseteq> P_set(a)" in trans_induct3_raw) 
     apply simp 
    apply (simp add:HS_set_def) 
   apply (simp add:HS_set_def HHS_set_succ_def) 
   apply blast 
  apply auto 
proof - 
  fix x a assume assms : "Limit(a)" "x \<in> HS_set(a)" "\<forall>b\<in>a. Ord(b) \<longrightarrow> HS_set(b) \<subseteq> P_set(b)"
  then have "x \<in> (\<Union>b < a. HS_set(b))" unfolding HS_set_def using transrec2_Limit by auto 
  then obtain b where bH : "b < a" "x \<in> HS_set(b)" "Ord(b)" using assms Limit_is_Ord lt_Ord by auto 
  then have "x \<in> P_set(b)" using assms ltD by auto 
  then show "x \<in> P_set(a)" using P_set_lim assms bH by auto 
qed

lemma HS_iff: "x \<in> HS \<longleftrightarrow> x \<in> P_names \<and> domain(x) \<subseteq> HS \<and> symmetric(x)" 
  apply(rule_tac Q="\<lambda>x. x \<in> HS \<longleftrightarrow> x \<in> P_names \<and> domain(x) \<subseteq> HS \<and> symmetric(x)" in ed_induction) 
  apply (rule iffI)
proof - 
  fix x assume assms : "(\<And>y. ed(y, x) \<Longrightarrow> y \<in> HS \<longleftrightarrow> y \<in> P_names \<and> domain(y) \<subseteq> HS \<and> symmetric(y))" "x \<in> HS"
  
  obtain a where aH : "Ord(a)" "x \<in> HS_set(succ(a))" using assms HS_in_HS_set_succ by blast
  then have "domain(x) \<subseteq> HS_set(a)" "symmetric(x)" using HS_set_succ by auto 
  then show "x \<in> P_names \<and> domain(x) \<subseteq> HS \<and> symmetric(x)" 
    apply auto 
    using assms 
     apply(simp add:HS_def) 
    unfolding HS_def 
    using aH 
    apply auto
  proof - 
    fix y p assume "<y, p> \<in> x" then show "y \<in> P_names" using P_name_domain_P_name assms unfolding HS_def by auto
  qed
next 
  fix x assume assms : "(\<And>y. ed(y, x) \<Longrightarrow> y \<in> HS \<longleftrightarrow> y \<in> P_names \<and> domain(y) \<subseteq> HS \<and> symmetric(y))" 
                       "x \<in> P_names \<and> domain(x) \<subseteq> HS \<and> symmetric(x)"

  define I where "I \<equiv> { (\<mu> a. y \<in> HS_set(a)) . y \<in> domain(x) }" 
  then have "Ord(\<Union>I)"
    apply(rule_tac Ord_Union) 
    by auto 
  then obtain L where LH : "(\<Union>I) < L"  "Limit(L)" 
    using ex_larger_limit by auto 
  then have "HS_set(L) = (\<Union>a < L. HS_set(a))" unfolding HS_set_def using transrec2_Limit by auto 
  then have H : "domain(x) \<subseteq> HS_set(L)" 
  proof (auto) 
    fix y p assume assm : "<y, p> \<in> x"
    then have "y \<in> HS" using assms by auto 
    then obtain a where "Ord(a)" "y \<in> HS_set(a)" unfolding HS_def by auto 
    then have H: "y \<in> HS_set(\<mu> a. y \<in> HS_set(a))" 
      apply(rule_tac LeastI) 
      by auto
 
    have "(\<mu> a. y \<in> HS_set(a)) \<le> (\<Union>y \<in> domain(x). (\<mu> a. y \<in> HS_set(a)))"  
      apply(rule_tac j="(\<mu> a. y \<in> HS_set(a))" in Union_upper_le) 
      using assm le_refl 
        apply auto 
      done 
    then have "(\<mu> a. y \<in> HS_set(a)) \<le> (\<Union>I)" unfolding I_def by auto 
    then have "(\<mu> a. y \<in> HS_set(a)) < L" 
      apply(rule_tac b="\<Union>I" in le_lt_lt) 
      using LH 
      by auto 
    then show "y \<in> (\<Union>a < L. HS_set(a))"
      apply(rule_tac OUN_I) 
      using H 
      by auto
  qed
  then have "x \<in> { x \<in> P_set(succ(L)). domain(x) \<subseteq> HS_set(L) \<and> symmetric(x) }"
    using assms 
    apply auto 
    apply(rule_tac P="x \<in> Pow(P_set(L) \<times> P) \<inter> M" in mp)
    using P_set_succ P_name_in_M 
     apply auto  
  proof - 
    fix v assume vin : "v \<in> x" 
    then obtain y p where ypH : "v = <y, p>" using assms relation_P_name unfolding relation_def by blast 
    then have pin:"p \<in> P" using assms ypH vin P_name_range by auto 
    have "y \<in> P_set(L)" using H ypH vin HS_set_subset LH Limit_is_Ord by auto 
    then show "v \<in> P_set(L) \<times> P" using pin ypH by auto 
  qed
  then have "x \<in> HS_set(succ(L))" 
    using HS_set_succ LH Limit_is_Ord by auto 
  then show "x \<in> HS" 
    unfolding HS_def 
    using assms 
    apply simp 
    apply(rule_tac x="succ(L)" in exI) 
    using LH Limit_is_Ord 
    by auto
qed

lemma \<G>_is_subgroup_of_\<G> : "\<G> \<in> P_auto_subgroups(\<G>)" 
  unfolding P_auto_subgroups_def 
  using \<G>_in_M local.\<G>_P_auto_group 
  by auto

lemma \<G>_in_\<F> : "\<G> \<in> \<F>" 
proof - 
  obtain \<I> where H: "\<I> \<in> \<F>" "\<I> \<in> P_auto_subgroups(\<G>)"  using \<F>_nonempty \<F>_subset by auto 
  then have "\<I> \<subseteq> \<G>" using P_auto_subgroups_def by auto 
  then show "\<G> \<in> \<F>" using \<F>_closed_under_supergroup \<G>_is_subgroup_of_\<G> H by auto
qed

end
end
