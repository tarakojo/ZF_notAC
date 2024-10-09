theory HS_Theorems
  imports 
    HS_M
begin 

context M_symmetric_system_HS_M
begin
    
lemma check_in_HS : "x \<in> M \<Longrightarrow> check(x) \<in> HS" 
proof - 
  assume "x \<in> M" 
  have "\<And>x. x \<in> M \<longrightarrow> check(x) \<in> HS" 
  proof(rule_tac P="\<lambda>x. x \<in> M \<longrightarrow> check(x) \<in> HS" in eps_induct, rule impI) 
    fix x assume assms : "x \<in> M" "\<forall>y \<in> x. y \<in> M \<longrightarrow> check(y) \<in> HS"
    thm HS_iff 
    have H1: "check(x) \<in> P_names"  using check_P_name assms by auto
    have "\<And>\<pi>. \<pi> \<in> \<G> \<Longrightarrow> Pn_auto(\<pi>)`check(x) = check(x)" 
      apply(rule check_fixpoint) 
      using \<G>_P_auto_group assms
      unfolding is_P_auto_group_def 
      by auto
    then have "sym(check(x)) = \<G>"
      using check_fixpoint \<G>_P_auto_group  
      unfolding is_P_auto_group_def sym_def 
      by auto
    then have H2: "symmetric(check(x))" 
      unfolding symmetric_def 
      using \<G>_in_\<F>
      by auto 
    have "domain(check(x)) \<subseteq> HS" 
    proof(rule subsetI)
      fix v assume assm1: "v \<in> domain(check(x))" 
      then obtain p where vpH: "<v, p> \<in> check(x)" by auto 
      have "check(x) = { <check(y), one> . y \<in> x }" by(rule def_check) 
      then obtain y where "v = check(y)" "y \<in> x" using vpH by auto 
      then show "v \<in> HS" using assms transM by auto
    qed

    then show "check(x) \<in> HS" using HS_iff H1 H2 by auto
  qed
  then show ?thesis using \<open>x \<in> M\<close> by auto
qed

lemma comp_in_sym : "x \<in> P_names \<Longrightarrow> \<pi> \<in> sym(x) \<Longrightarrow> \<tau> \<in> sym(x) \<Longrightarrow> \<pi> O \<tau> \<in> sym(x)" 
  unfolding sym_def 
  apply simp
  apply(rule conjI)
  using \<G>_P_auto_group is_P_auto_group_def 
   apply force
  apply(subst Pn_auto_comp)
  using \<G>_P_auto_group is_P_auto_group_def 
    apply (force, force)
  apply(subst comp_fun_apply) 
  apply(rule Pn_auto_type)
  using \<G>_P_auto_group is_P_auto_group_def 
    apply (force, force)
  by auto

lemma converse_in_sym : "x \<in> P_names \<Longrightarrow> \<pi> \<in> sym(x) \<Longrightarrow> converse(\<pi>) \<in> sym(x)" 
proof - 
  assume assms : "x \<in> P_names" "\<pi> \<in> sym(x)" 

  have "<x, Pn_auto(\<pi>)`x> \<in> Pn_auto(\<pi>)" 
    apply(rule function_apply_Pair)
    using Pn_auto_function Pn_auto_domain assms 
    by auto 
  then have "<x, x> \<in> Pn_auto(\<pi>)" 
    using assms 
    unfolding sym_def 
    by auto
  then have "<x, x> \<in> converse(Pn_auto(\<pi>))" by auto 
  then have "<x, x> \<in> Pn_auto(converse(\<pi>))" 
    using Pn_auto_converse assms sym_def \<G>_P_auto_group is_P_auto_group_def 
    by auto
  then have H : "Pn_auto(converse(\<pi>))`x = x" 
    apply(rule function_apply_equality)
    by(rule Pn_auto_function)

  have "\<pi> \<in> \<G>" 
    using assms
    unfolding sym_def 
    by auto 
  then have "converse(\<pi>) \<in> \<G>" 
    using \<G>_P_auto_group 
    unfolding is_P_auto_group_def 
    by auto 

  then show "converse(\<pi>) \<in> sym(x)" 
    unfolding sym_def
    using H 
    by auto
qed

lemma sym_P_auto_subgroup : "x \<in> P_names \<Longrightarrow> sym(x) \<in> P_auto_subgroups(\<G>)" 
proof - 
  assume assm : "x \<in> P_names" 
  thm P_auto_subgroups_def is_P_auto_group_def

  have "sym(x) \<subseteq> { \<pi> \<in> P \<rightarrow> P. is_P_auto(\<pi>) }" 
    unfolding sym_def 
    using \<G>_P_auto_group is_P_auto_group_def 
    by auto

  then show "sym(x) \<in> P_auto_subgroups(\<G>)" 
    unfolding P_auto_subgroups_def is_P_auto_group_def
    apply simp 
    apply(rule conjI, simp add:sym_def, force)
    apply(rule conjI, rule sym_in_M, simp add:assm)
    apply(rule conjI)
    using comp_in_sym assm converse_in_sym
    by auto
qed

lemma HS_Pn_auto_helper : "\<pi> \<in> \<G> \<Longrightarrow> x \<in> HS \<Longrightarrow> Pn_auto(\<pi>)`x \<in> HS" 
proof - 
  assume assms : "\<pi> \<in> \<G>" "x \<in> HS" 

  have main : "x \<in> HS \<longrightarrow> Pn_auto(\<pi>)`x \<in> HS" 
  proof (rule_tac Q="\<lambda>x. x \<in> HS \<longrightarrow> Pn_auto(\<pi>)`x \<in> HS" in ed_induction, rule impI)
    fix x assume assms1 : "(\<And>y. ed(y, x) \<Longrightarrow> y \<in> HS \<longrightarrow> Pn_auto(\<pi>) ` y \<in> HS)" "x \<in> HS" 

    have pi_pauto : "\<pi> \<in> P_auto" 
      using assms \<G>_P_auto_group is_P_auto_group_def P_auto_def by auto 

    have "Pn_auto(\<pi>)`x \<in> P_names" using Pn_auto_value assms P_auto_def assms1 HS_iff pi_pauto by auto

    have eq:"Pn_auto(\<pi>)`x = { <Pn_auto(\<pi>)`y, \<pi>`p> . <y,p> \<in> x }" using Pn_auto assms P_auto_def assms1 HS_iff by auto
    have domsubset : "domain(Pn_auto(\<pi>)`x) \<subseteq> HS" 
    proof (rule subsetI)
      fix v assume vin : "v \<in> domain(Pn_auto(\<pi>)`x)" 
      then obtain q where qH: "<v, q> \<in> Pn_auto(\<pi>)`x" by auto
      have "\<exists>y. \<exists>p. <y, p> \<in> x \<and> <v, q> = <Pn_auto(\<pi>)`y, \<pi>`p>" 
        apply(rule pair_rel_arg)
        using assms1 HS_iff relation_P_name eq qH 
        by auto
      then obtain y where yH: "y \<in> domain(x)" "v = Pn_auto(\<pi>)`y" by auto
      then have "y \<in> HS" using assms1 HS_iff by blast
      then show "v \<in> HS" using yH assms1 ed_def by auto
    qed

    then have H1: "{ \<pi> O \<tau> O converse(\<pi>). \<tau> \<in> sym(x) } \<in> \<F>" 
      using assms1 HS_iff symmetric_def \<F>_normal assms by auto 

    have H2 : "{ \<pi> O \<tau> O converse(\<pi>). \<tau> \<in> sym(x) } \<subseteq> sym(Pn_auto(\<pi>)`x)" 
    proof (rule subsetI) 
      fix \<sigma> assume assm : "\<sigma> \<in> {\<pi> O \<tau> O converse(\<pi>) . \<tau> \<in> sym(x)}"

      have sigmain : "\<sigma> \<in> \<G>" using \<F>_subset P_auto_subgroups_def H1 assm by auto

      obtain \<tau> where tauH : "\<sigma> = \<pi> O \<tau> O converse(\<pi>)" "\<tau> \<in> sym(x)" using assm by auto 

      then have "Pn_auto(\<sigma>) ` (Pn_auto(\<pi>)`x) = Pn_auto(\<pi> O \<tau> O converse(\<pi>)) ` (Pn_auto(\<pi>)`x)" by auto 
      also have "... = (Pn_auto(\<pi> O \<tau> O converse(\<pi>)) O Pn_auto(\<pi>))`x" 
        apply(rule eq_flip, rule_tac A=P_names in comp_fun_apply)
        using Pn_auto_type assms P_auto_def assms1 HS_iff pi_pauto
        by auto
      also have "... = Pn_auto((\<pi> O \<tau> O converse(\<pi>)) O \<pi>)`x" 
        apply(rule eq_flip)
        apply(subst Pn_auto_comp)
        apply(rule P_auto_comp)
        using assms P_auto_def pi_pauto
           apply simp
          apply(rule P_auto_comp)
        using tauH \<G>_P_auto_group 
        unfolding sym_def is_P_auto_group_def
           apply force
          apply(rule P_auto_converse)
        using assms P_auto_def pi_pauto
        by auto
      also have "... = Pn_auto(\<pi> O \<tau> O (converse(\<pi>) O \<pi>))`x" 
        using comp_assoc by auto
      also have "... = Pn_auto(\<pi> O (\<tau> O id(P)))`x"
        apply(subst left_comp_inverse, rule bij_is_inj)
        using assms P_auto_def is_P_auto_def pi_pauto
        by auto
      also have "... = Pn_auto(\<pi> O \<tau>)`x" 
        apply(subst right_comp_id)
        using tauH sym_def \<G>_P_auto_group is_P_auto_group_def is_P_auto_def bij_def inj_def Pi_def 
        by auto
      also have "... = (Pn_auto(\<pi>) O Pn_auto(\<tau>)) ` x"
        apply(subst Pn_auto_comp)
        using assms P_auto_def is_P_auto_def pi_pauto
        apply force
        using tauH \<G>_P_auto_group 
        unfolding sym_def is_P_auto_group_def
        by auto
      also have "... = Pn_auto(\<pi>) ` (Pn_auto(\<tau>)` x)"
        apply(subst comp_fun_apply)
        apply(rule Pn_auto_type)
        using tauH sym_def \<G>_P_auto_group is_P_auto_group_def assms1 HS_iff 
        by auto
      also have "... = Pn_auto(\<pi>) ` x" 
        using tauH sym_def by auto 
      finally show "\<sigma> \<in> sym(Pn_auto(\<pi>) ` x)" 
        unfolding sym_def 
        using sigmain
        by auto 
    qed

    have H3 : "sym(Pn_auto(\<pi>)`x) \<in> P_auto_subgroups(\<G>)" 
      apply(rule sym_P_auto_subgroup)
      apply(rule Pn_auto_value)
      using assms \<G>_P_auto_group is_P_auto_group_def assms1 HS_iff 
      by auto

    then have "symmetric(Pn_auto(\<pi>)`x)" 
      unfolding symmetric_def 
      using H1 H2 \<F>_closed_under_supergroup sym_P_auto_subgroup assms1 Pn_auto_value HS_iff 
      by auto

    then show "Pn_auto(\<pi>) ` x \<in> HS" 
      apply(rule_tac iffD2, rule_tac HS_iff)
      apply(rule conjI, rule Pn_auto_value)
      using assms \<G>_P_auto_group is_P_auto_group_def 
        apply force
      using assms1 HS_iff 
       apply force
      apply(rule conjI, rule domsubset, simp)
      done
  qed

  then show "Pn_auto(\<pi>) ` x \<in> HS" 
    using assms 
    by auto
qed

lemma HS_Pn_auto : "\<pi> \<in> \<G> \<Longrightarrow> x \<in> P_names \<Longrightarrow> x \<in> HS \<longleftrightarrow> Pn_auto(\<pi>)`x \<in> HS" 
proof(rule iffI)
  fix \<pi> assume "\<pi> \<in> \<G>" "x \<in> HS" 
  then show "Pn_auto(\<pi>)`x \<in> HS" 
    using HS_Pn_auto_helper by auto
next 
  fix \<pi> assume assms : "\<pi> \<in> \<G>" "Pn_auto(\<pi>)`x \<in> HS" "x \<in> P_names"
  have H : "Pn_auto(converse(\<pi>)) ` (Pn_auto(\<pi>)`x) \<in> HS" 
    apply(rule HS_Pn_auto_helper)
    using \<G>_P_auto_group is_P_auto_group_def assms 
    by auto
  have "Pn_auto(converse(\<pi>)) ` (Pn_auto(\<pi>)`x) = converse(Pn_auto(\<pi>)) ` (Pn_auto(\<pi>)`x)"
    apply(subst Pn_auto_converse)
    using assms \<G>_P_auto_group is_P_auto_group_def 
    by auto
  also have "... = (converse(Pn_auto(\<pi>)) O Pn_auto(\<pi>)) ` x" 
    apply(rule sym, rule comp_fun_apply)
     apply(rule Pn_auto_type)
    using assms \<G>_P_auto_group is_P_auto_group_def  
    by auto 
  also have "... = Pn_auto(id(P)) ` x" 
    apply(subst left_comp_inverse)
     apply(rule bij_is_inj)
    apply(rule Pn_auto_bij)
    using assms \<G>_P_auto_group is_P_auto_group_def Pn_auto_id
    by auto
  also have "... = id(P_names) ` x" 
    by(subst Pn_auto_id, simp)
  also have "... = x" 
    using assms 
    by auto 
  finally show "x \<in> HS" using H by auto
qed

lemma Pn_auto_domain_closed_helper :
  fixes x y \<pi>
  assumes "x \<in> P_names" "y \<in> domain(x)" "\<pi> \<in> sym(x)" 
  shows "Pn_auto(\<pi>)`y \<in> domain(x)" 
proof - 
  obtain p where pH: "<y, p> \<in> x" using assms by auto
  have "<Pn_auto(\<pi>)`y, \<pi>`p> \<in> Pn_auto(\<pi>)`x"
    apply(subst (2) Pn_auto)
    using assms 
     apply simp
    apply(rule pair_relI)
    using pH
    by auto
  then have "<Pn_auto(\<pi>)`y, \<pi>`p> \<in> x" 
    using assms sym_def 
    by auto
  then show ?thesis by auto
qed

lemma Pn_auto_domain_closed:
  fixes x y \<pi>
  assumes "x \<in> P_names" "\<pi> \<in> sym(x)" "y \<in> P_names" 
  shows "y \<in> domain(x) \<longleftrightarrow> Pn_auto(\<pi>)`y \<in> domain(x)" 
proof(rule iffI)
  assume "y \<in> domain(x)" 
  then obtain p where "<y, p> \<in> x" by auto
  then show "Pn_auto(\<pi>) ` y \<in> domain(x)" 
    apply(rule_tac Pn_auto_domain_closed_helper)
    using assms P_name_domain_P_name 
    by auto
next 
  assume assms1 : "Pn_auto(\<pi>) ` y \<in> domain(x)" 

  have H : "Pn_auto(converse(\<pi>))`(Pn_auto(\<pi>)`y) \<in> domain(x)" 
    apply(rule Pn_auto_domain_closed_helper)
    using assms assms1 converse_in_sym assms 
    by auto
  have "Pn_auto(converse(\<pi>)) ` (Pn_auto(\<pi>)`y) = converse(Pn_auto(\<pi>)) ` (Pn_auto(\<pi>)`y)"
    apply(subst Pn_auto_converse)
    using assms \<G>_P_auto_group is_P_auto_group_def sym_def
    by auto
  also have "... = (converse(Pn_auto(\<pi>)) O Pn_auto(\<pi>)) ` y" 
    apply(rule sym, rule comp_fun_apply)
     apply(rule Pn_auto_type)
    using assms \<G>_P_auto_group is_P_auto_group_def sym_def
    by auto 
  also have "... = Pn_auto(id(P)) ` y" 
    apply(subst left_comp_inverse)
     apply(rule bij_is_inj)
    apply(rule Pn_auto_bij)
    using assms \<G>_P_auto_group is_P_auto_group_def Pn_auto_id sym_def
    by auto
  also have "... = id(P_names) ` y" 
    by(subst Pn_auto_id, simp)
  also have "... = y" 
    using assms 
    by auto 
  finally show "y \<in> domain(x)" 
    using H by auto
qed

end
end
