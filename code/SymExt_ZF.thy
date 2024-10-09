theory SymExt_ZF
  imports SymExt_Replacement "Forcing/Powerset_Axiom" "Forcing/Foundation_Axiom" 
begin

locale M_symmetric_system_SymExt_ZF = M_symmetric_system_SymExt_Separation_Base + forcing_data_Powerset_Axiom_G_generic +
  assumes SymExt_upair_fms : "SymExt_separation_fms(Or(Equal(0, 1), Equal(0, 2)), length([a, b])) \<subseteq> \<Phi>"  
  and SymExt_Union_fms : "SymExt_separation_fms(Exists(And(Member(1, 0), Member(0, 2))), length([x])) \<subseteq> \<Phi>" 
  and SymExt_powerset_fms : "SymExt_separation_fms(subset_fm(0, 1), 1) \<union> { is_least_index_of_Vset_contains_witness_fm(Equal(0, 1))} \<subseteq> \<Phi>"
begin

lemma zero_in_SymExt : "0 \<in> SymExt(G)" 
  using zero_in_M M_subset_SymExt by auto

lemma upair_in_SymExt : 
  fixes a b 
  assumes "a \<in> SymExt(G)" "b \<in> SymExt(G)" 
  shows "{a, b} \<in> SymExt(G)" 
proof - 
  obtain a' b' where a'b'H: "a' \<in> HS" "b' \<in> HS" "val(G, a') = a" "val(G, b') = b" 
    using assms SymExt_def
    by auto
  have "\<exists>S \<in> SymExt(G). { val(G, x). x \<in> {a', b'} } \<subseteq> S"
    apply(rule ex_separation_base)
    apply(subgoal_tac "a' \<in> M \<and> b' \<in> M")
    using upair_ax upair_abs HS_iff P_name_in_M a'b'H
    unfolding upair_ax_def 
    by auto
  then obtain S where SH : "S \<in> SymExt(G)" "{ a, b } \<subseteq> S" using a'b'H by auto

  define X where "X \<equiv> { x \<in> S. sats(SymExt(G), Or(Equal(0, 1), Equal(0, 2)), [x] @ [a, b] ) }" 
  have Xin : "X \<in> SymExt(G)" 
    unfolding X_def 
    apply(rule SymExt_separation)
    using SH assms 
       apply auto[3]
     apply(simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union) 
    using SymExt_upair_fms
    by auto
  have "X = { x \<in> S. x = a \<or> x = b }" 
    unfolding X_def 
    apply(rule iff_eq)
    apply(rename_tac x, subgoal_tac "x \<in> SymExt(G)") 
    using assms SymExt_trans SH
    by auto
  also have "... = { a, b }" using SH by auto
  finally show "{a, b} \<in> SymExt(G)" using Xin by auto
qed

lemma Union_in_SymExt : 
  fixes x 
  assumes "x \<in> SymExt(G)" 
  shows "\<Union>x \<in> SymExt(G)" 
proof - 
  obtain x' where x'H: "x' \<in> HS" "val(G, x') = x" using assms SymExt_def by auto
  define X where "X \<equiv> domain(\<Union>(domain(x')))" 

  have "X \<subseteq> HS" 
  proof(rule subsetI)
    fix z assume xin : "z \<in> X" 
    then obtain p where "<z, p> \<in> \<Union>(domain(x'))" using X_def by auto
    then obtain y where yH: "y \<in> domain(x')" "<z, p> \<in> y" by auto 
    then have "y \<in> HS" using HS_iff x'H by auto
    then show "z \<in> HS" using HS_iff yH by auto 
  qed
  then have "\<exists> S \<in> SymExt(G).  { val(G, x). x \<in> X } \<subseteq> S" 
    apply(rule ex_separation_base)
    unfolding X_def
    using domain_closed Union_closed HS_iff P_name_in_M x'H 
    by auto
  then obtain S where SH : "S \<in> SymExt(G)" "{ val(G, x). x \<in> X } \<subseteq> S" by auto
  have subsetS : "\<Union>x \<subseteq> S" 
  proof(rule subsetI)
    fix z 
    assume zin : "z \<in> \<Union>x" 
    then obtain y where yH : "z \<in> y" "y \<in> x" by auto
    then have yin : "y \<in> val(G, x')" using x'H by auto
    then have "\<exists>y' \<in> domain(x'). val(G, y') = y" 
      apply(rule_tac P="y \<in> val(G, x')" in mp)
      apply(subst def_val, force)
      using x'H yH HS_iff
      by auto
    then obtain y' where y'H: "y' \<in> domain(x')" "val(G, y') = y" using yin by auto 
    then have "\<exists>z' \<in> domain(y'). val(G, z') = z" 
      apply(rule_tac P="z \<in> val(G, y')" in mp)
      apply(subst def_val, force)
      using y'H HS_iff x'H yH 
      by auto
    then obtain z' p where z'H : "val(G, z') = z" "<z', p> \<in> y'" by auto
    then have "z' \<in> X" 
      unfolding X_def 
      apply(rule_tac b=p in domainI)
      apply(rule_tac B=y' in UnionI)
      using y'H z'H 
      by auto
    then have "val(G, z') \<in> S" using SH by auto
    then show "z \<in> S" using z'H by auto
  qed

  define T where "T \<equiv> { z \<in> S. sats(SymExt(G), Exists(And(Member(1, 0), Member(0, 2))), [z] @ [x]) }" 
  have Tin : "T \<in> SymExt(G)" 
    unfolding T_def 
    apply(rule SymExt_separation)
    using SH assms 
       apply auto[3]
    unfolding BExists_def BExists'_def 
     apply(simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union) 
    using SymExt_Union_fms
    by auto

  have "T = { z \<in> S. \<exists>y \<in> SymExt(G). y \<in> x \<and> z \<in> y }" 
    unfolding T_def 
    apply(rule iff_eq)
    apply(rename_tac z, subgoal_tac "z \<in> SymExt(G)")
    unfolding BExists_def BExists'_def 
    using assms SymExt_trans SH 
    by auto
  also have "... = { z \<in> S. \<exists>y \<in> x. z \<in> y }" 
    using SymExt_trans assms
    by auto
  also have "... = { z \<in> S. z \<in> \<Union>x }" 
    by auto
  also have "... = \<Union>x" 
    using subsetS 
    by auto
  finally show ?thesis 
    using Tin by auto
qed

lemma Un_in_SymExt : 
  fixes a b 
  assumes "a \<in> SymExt(G)" "b \<in> SymExt(G)" 
  shows "a \<union> b \<in> SymExt(G)" 

  apply(rule_tac b="a \<union> b" and a="\<Union>{a, b}" in ssubst, simp)
  apply(rule Union_in_SymExt)
  apply(rule upair_in_SymExt)
  using assms
  by auto

lemma powerset_in_SymExt : 
  fixes x 
  assumes "x \<in> SymExt(G)" 
  shows "Pow(x) \<inter> SymExt(G) \<in> SymExt(G)" 
proof - 
  have "x \<in> M[G]" using assms SymExt_subset_GenExt by auto
  then have "\<exists>powx \<in> M[G] . powerset(##M[G], x, powx)" using power_in_MG power_ax_def by auto
  then obtain powx where powxH : "powx \<in> M[G]" "powerset(##M[G], x, powx)" by auto
  then have "\<And>y. y \<in> M[G] \<Longrightarrow> y \<subseteq> x \<Longrightarrow> y \<in> powx" 
    apply(rename_tac y, subgoal_tac "(\<forall>z[##M[G]]. z \<in> y \<longrightarrow> z \<in> x)")
    unfolding powerset_def subset_def 
    by auto
  then have subsetpowx : "Pow(x) \<inter> M[G] \<subseteq> powx" by auto

  obtain powx' where powx'H : "powx' \<in> M" "val(G, powx') = powx" 
    using powxH GenExt_def 
    by auto

  have "\<exists>S. S \<in> M \<and> S \<subseteq> HS \<and> (\<forall>p\<in>G. \<forall>y\<in>domain(powx'). (\<exists>z\<in>HS. p \<tturnstile>HS Equal(0, 1) [y, z] @ []) \<longleftrightarrow> (\<exists>z\<in>S. p \<tturnstile>HS Equal(0, 1) [y, z] @ []))" 
    apply(rule ex_hs_subset_contains_witnesses)
    using Un_least_lt powx'H SymExt_powerset_fms
    by auto
  then obtain S where SH : "S \<in> M" "S \<subseteq> HS" "\<forall>p\<in>G. \<forall>y\<in>domain(powx'). (\<exists>z\<in>HS. p \<tturnstile>HS Equal(0, 1) [y, z]) \<longleftrightarrow> (\<exists>z\<in>S. p \<tturnstile>HS Equal(0, 1) [y, z])" 
    by auto
  then have SE: "\<And>p y. p \<in> G \<Longrightarrow> y \<in> domain(powx') \<Longrightarrow> (\<exists>z\<in>HS. p \<tturnstile>HS Equal(0, 1) [y, z]) \<longleftrightarrow> (\<exists>z\<in>S. p \<tturnstile>HS Equal(0, 1) [y, z])" by auto

  have "\<exists>T \<in> SymExt(G). { val(G, x). x \<in> S } \<subseteq> T"
    apply(rule ex_separation_base)
    using SH 
    by auto
  then obtain T where TH : "T \<in> SymExt(G)" "{ val(G, x). x \<in> S } \<subseteq> T" by auto

  have subsetT: "Pow(x) \<inter> SymExt(G) \<subseteq> T" 
  proof (rule subsetI)
    fix y assume yin: "y \<in> Pow(x) \<inter> SymExt(G)" 

    then have "y \<in> powx" using SymExt_subset_GenExt subsetpowx by auto
    then have "\<exists>y'\<in>domain(powx'). val(G, y') = y"
      apply(rule_tac P="powx = val(G, powx')" in mp)
      apply(subst def_val, force)
      using powx'H 
      by auto
    then obtain y' where y'H : "y' \<in> domain(powx')" "val(G, y') = y" by auto
    then have y'inM : "y' \<in> M" 
      using powx'H domain_elem_in_M 
      by auto

    obtain y'' where y''H: "y'' \<in> HS" "val(G, y'') = y" using yin SymExt_def by auto

    have "sats(M[G], Equal(0, 1), map(val(G), [y', y'']))" using y'H y''H yin SymExt_subset_GenExt by auto
    then have "\<exists>p \<in> G. p \<tturnstile> Equal(0, 1) [y', y'']" 
      apply(rule_tac iffD2)
       apply(rule truth_lemma)
      using generic y'inM y''H HS_iff P_name_in_M Un_least_lt
      by auto
    then have "\<exists>p \<in> G. p \<tturnstile>HS Equal(0, 1) [y', y'']" 
      apply(rule_tac iffD1)
       apply(rule bex_iff, rule ForcesHS_Equal)
      using generic y'inM y''H HS_iff P_name_in_M Un_least_lt generic M_genericD P_in_M transM 
      by auto
    then have "\<exists>p \<in> G. \<exists>y'' \<in> HS. p \<tturnstile>HS Equal(0, 1) [y', y'']" (is ?A) using y''H by auto
    then have "\<exists>p \<in> G. \<exists>y'' \<in> S. p \<tturnstile>HS Equal(0, 1) [y', y'']"
      apply(rule_tac P="?A" in iffD1)
       apply(rule bex_iff, rule SE)
      using y'H 
      by auto
    then have "\<exists>y''' \<in> S. \<exists>p \<in> G. p \<tturnstile>HS Equal(0, 1) [y', y''']" (is ?B) by auto
    then have "\<exists>y''' \<in> S. \<exists>p \<in> G. p \<tturnstile> Equal(0, 1) [y', y''']" (is ?C)
      apply(rule_tac Q="?B" in iffD2)
       apply(rule bex_iff)+
       apply(rule ForcesHS_Equal)
      using y'H SH transM y'inM generic M_genericD P_in_M
      by auto
    then have "\<exists>y''' \<in> S. sats(M[G], Equal(0, 1), map(val(G), [y', y''']))"
      apply(rule_tac P="?C" in iffD1)
       apply(rule bex_iff, rule truth_lemma)
      using generic y'inM SH transM Un_least_lt
      by auto
    then obtain y''' where y'''H: "y''' \<in> S" "sats(M[G], Equal(0, 1), [val(G, y'), val(G, y''')])" by auto

    then have "val(G, y') = val(G, y''')"
      apply(subgoal_tac "val(G, y') \<in> M[G] \<and> val(G, y''') \<in> M[G]")
       apply simp
      using GenExt_def y'inM y'''H SH transM 
      by auto
    then have "val(G, y''') = y" using y'H by auto
    then show "y \<in> T" using y'''H TH by auto
  qed

  define U where "U \<equiv> { y \<in> T. sats(SymExt(G), subset_fm(0, 1), [y] @ [x]) }"

  have "U \<in> SymExt(G)" 
    unfolding U_def
    apply(rule SymExt_separation)
    using TH assms subset_fm_def 
       apply auto[3]
    apply(subst arity_subset_fm)
    using Un_least_lt SymExt_powerset_fms
    by auto

  have "U = { y \<in> T. y \<subseteq> x }" 
    unfolding U_def
    apply(rule iff_eq)
    apply(rule iff_trans, rule sats_subset_fm)
    using TH SymExt_trans assms Transset_SymExt
    by auto
  also have "... = Pow(x) \<inter> SymExt(G)" 
    using subsetT TH SymExt_trans 
    by auto
  finally show "Pow(x) \<inter> SymExt(G) \<in> SymExt(G)" 
    using \<open>U \<in> SymExt(G)\<close> by auto
qed

lemma SymExt_foundation_ax : "foundation_ax(##SymExt(G))" 
  apply(rule ccontr)
  apply(subgoal_tac "\<not>foundation_ax(##M[G])")
  using foundation_in_MG 
   apply force 
  unfolding foundation_ax_def 
  apply clarsimp
  apply(rename_tac x y, rule_tac x=x in bexI, rule conjI)
    apply(rename_tac x y, rule_tac x=y in bexI, simp)
  using SymExt_subset_GenExt 
    apply force 
   apply(rule ballI)
   apply(rename_tac x y y', case_tac "y' \<notin> x", force, simp)
   apply(rename_tac x y y', subgoal_tac "(\<exists>z\<in>SymExt(G). z \<in> x \<and> z \<in> y')")
    apply clarsimp
    apply(rename_tac x y y' z, rule_tac x=z in bexI, force)
  using SymExt_subset_GenExt SymExt_trans
    apply force
  using SymExt_trans
   apply force
  using SymExt_subset_GenExt
  by auto

lemma succ_in_SymExt : 
  fixes x
  assumes "x \<in> SymExt(G)" 
  shows "succ(x) \<in> SymExt(G)" 
proof - 
  have "succ(x) = {x} \<union> x" by auto
  also have "... = \<Union> { {x, x} , x }" by auto
  finally have H: "succ(x) = \<Union> { {x, x} , x }" by auto

  have "\<Union> { {x, x} , x } \<in> SymExt(G)" 
    apply(rule Union_in_SymExt)
    apply(rule upair_in_SymExt)+
    using assms
    by auto
  then show ?thesis using H by auto
qed

lemma SymExt_infinity_ax : "infinity_ax(##SymExt(G))"
  unfolding infinity_ax_def 
  apply(rule_tac x=nat in rexI, rule conjI)
    apply(rule_tac x=0 in rexI)
  unfolding empty_def 
  using zero_in_SymExt 
     apply auto[2]
   apply(rule rallI, rule impI)
   apply(rename_tac n, rule_tac x="succ(n)" in rexI)
  unfolding successor_def is_cons_def 
    apply(rule conjI, rename_tac n, rule_tac x="{n}" in rexI, rule conjI)
  unfolding upair_def 
       apply force
  unfolding union_def 
      apply force 
     apply simp
     apply(rename_tac n, rule_tac b="{n}" and a="{n, n}" in ssubst, force)
     apply (rule upair_in_SymExt)
  using succ_in_SymExt 
      apply auto[4]
  using nat_in_M M_subset_SymExt 
  by auto

(*
lemma SymExt_M_ZF : "M_ZF(SymExt(G))" 
  unfolding M_ZF_def 
  apply(rule conjI)+
  unfolding upair_ax_def upair_def 
     apply(rule rallI)+
     apply(rename_tac x y, rule_tac x="{x, y}" in rexI)
      apply(rule conjI, simp, rule conjI, simp)
      apply(rule rallI, rule impI, force, simp)
     apply(rule upair_in_SymExt)
      apply auto[2]
  unfolding Union_ax_def 
    apply(rule rallI)
    apply(rename_tac x, rule_tac x="\<Union>x" in rexI)
  unfolding big_union_def 
     apply(rule rallI)
  using SymExt_trans 
     apply force 
  using Union_in_SymExt 
    apply force 
   apply(rule conjI)
  unfolding power_ax_def 
    apply(rule rallI, rename_tac x, rule_tac x="Pow(x) \<inter> SymExt(G)" in rexI)
  unfolding powerset_def subset_def 
     apply(rule rallI, rule iffI, force)
     apply simp
     apply(rule subsetI)
     apply(rename_tac x y z, subgoal_tac "z \<in> SymExt(G)", force)
  using SymExt_trans
     apply(rename_tac x y z, rule_tac x=y in SymExt_trans, force, force)
  using powerset_in_SymExt 
    apply force 
  unfolding extensionality_def
   apply(rule rallI)+
   apply(rule impI)
   apply(rule equality_iffI, rule iffI)
    apply(rename_tac x y z, subgoal_tac "z \<in> SymExt(G)", force)
    apply(rename_tac x y z, rule_tac x=x in SymExt_trans, force, force)
    apply(rename_tac x y z, subgoal_tac "z \<in> SymExt(G)", force)
   apply(rename_tac x y z, rule_tac x=y in SymExt_trans, force, force)
  apply(rule conjI)+
  using SymExt_foundation_ax 
    apply force 
   apply(rule SymExt_infinity_ax)
  apply(rule conjI)
   apply(rule allI)+
   apply(rule impI)+
  unfolding separation_def 
   apply(rule rallI)
   apply(rename_tac \<phi> env x, rule_tac x="{ y \<in> x. sats(SymExt(G), \<phi>, [y]@env) }" in rexI)
    apply force 
  using SymExt_separation
   apply force 
   apply(rule allI)+
   apply(rule impI)+
  using SymExt_replacement 
  by auto

lemma SymExt_M_ZF_trans : "M_ZF_trans(SymExt(G))"
  unfolding M_ZF_trans_def 
  using SymExt_M_ZF M_ZF_def Transset_SymExt
  by auto

theorem SymExt_sats_ZF : "SymExt(G) \<Turnstile> ZF" 
  using M_ZF_iff_M_satT SymExt_M_ZF by auto
*)

end
end