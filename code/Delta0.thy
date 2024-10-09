theory Delta0
  imports 
    Utilities_M
begin 

thm bool_of_o_def

definition BExists' where "BExists'(n, \<phi>) \<equiv> Exists(And(Member(0, n), \<phi>))"  
definition BExists where "BExists(n, \<phi>) \<equiv> BExists'(succ(n), \<phi>)" 
definition BForall where "BForall(n, \<phi>) \<equiv> Neg(BExists(n, Neg(\<phi>)))" 

definition \<Delta>0_from where "\<Delta>0_from(X) \<equiv> X \<union> { Nand(\<phi>, \<psi>). <\<phi>, \<psi>> \<in> X \<times> X } \<union> { \<psi> \<in> formula. \<exists>n \<in> nat. \<exists>\<phi> \<in> X. n \<noteq> 0 \<and> \<psi> = BExists'(n, \<phi>) }" 
definition \<Delta>0_base where "\<Delta>0_base \<equiv> { \<phi> \<in> formula. \<exists> n \<in> nat. \<exists> m \<in> nat. \<phi> = Member(n, m) \<or> \<phi> = Equal(n, m) }" 

definition \<Delta>0 where "\<Delta>0 \<equiv> \<Union>n \<in> nat. \<Delta>0_from^n (\<Delta>0_base)" 

lemma \<Delta>0_subset : "\<Delta>0 \<subseteq> formula" 
proof -
  have main : "\<And>n. n \<in> nat \<Longrightarrow> \<Delta>0_from^n (\<Delta>0_base) \<subseteq> formula" 
    apply (rule_tac P="\<lambda>n. \<Delta>0_from^n (\<Delta>0_base) \<subseteq> formula" in nat_induct, simp)
    unfolding \<Delta>0_from_def \<Delta>0_base_def
    by auto
  then show ?thesis 
    unfolding \<Delta>0_def 
    by auto
qed

lemma \<Delta>0_from_increasing : 
  fixes n m 
  assumes "n \<in> nat" "m \<in> nat" "n \<le> m"
  shows "\<Delta>0_from^n(\<Delta>0_base) \<subseteq> \<Delta>0_from^m(\<Delta>0_base)" 
proof- 
  have main : "\<forall>n \<in> nat. n \<le> m \<longrightarrow> \<Delta>0_from^n(\<Delta>0_base) \<subseteq> \<Delta>0_from^m(\<Delta>0_base)" 
    apply(rule_tac P="\<lambda>m. \<forall>n \<in> nat. n \<le> m \<longrightarrow> \<Delta>0_from^n(\<Delta>0_base) \<subseteq> \<Delta>0_from^m(\<Delta>0_base)" in nat_induct)
    apply(simp add:assms, force)
    apply(rule ballI, rule impI)
    apply(rename_tac k n, rule_tac P="n \<le> k" and Q="n = succ(k)" in disjE)
    using le_iff
      apply force
     apply(simp, subst \<Delta>0_from_def)
     apply(rule subsetI, simp, rule disjI1, force, force)
    done
  then show ?thesis 
    using assms
    by auto
qed

lemma Member_\<Delta>0 [simp] : 
  fixes n m 
  assumes "n \<in> nat" "m \<in> nat" 
  shows "Member(n, m) \<in> \<Delta>0" 
  unfolding \<Delta>0_def 
  apply simp
  apply(rule_tac x=0 in bexI)
  unfolding \<Delta>0_base_def 
  using assms
  by auto

lemma Equal_\<Delta>0 [simp] : 
  fixes n m 
  assumes "n \<in> nat" "m \<in> nat" 
  shows "Equal(n, m) \<in> \<Delta>0" 
  unfolding \<Delta>0_def 
  apply simp
  apply(rule_tac x=0 in bexI)
  unfolding \<Delta>0_base_def 
  using assms
  by auto

lemma Nand_\<Delta>0 [simp] : 
  fixes \<phi> \<psi>
  assumes "\<phi> \<in> \<Delta>0" "\<psi> \<in> \<Delta>0" 
  shows "Nand(\<phi>, \<psi>) \<in> \<Delta>0" 
proof -
  obtain n where nH:"\<phi> \<in> \<Delta>0_from^n(\<Delta>0_base)" "n \<in> nat" 
    using assms
    unfolding \<Delta>0_def 
    by auto

  obtain m where mH:"\<psi> \<in> \<Delta>0_from^m(\<Delta>0_base)" "m \<in> nat" 
    using assms
    unfolding \<Delta>0_def 
    by auto

  define k where "k \<equiv> n \<union> m"

  have knat: "k \<in> nat" using Un_nat_type nH mH k_def by auto
  have mnle: "m \<le> k \<and> n \<le> k" using k_def max_le1 max_le2 nH mH by auto
  
  have "\<phi> \<in> \<Delta>0_from^k(\<Delta>0_base) \<and> \<psi> \<in> \<Delta>0_from^k(\<Delta>0_base)"
    using mnle \<Delta>0_from_increasing knat mH nH 
    by auto
  then have "Nand(\<phi>, \<psi>) \<in> \<Delta>0_from^succ(k)(\<Delta>0_base)"
    apply simp
    apply(subst \<Delta>0_from_def)
    by auto
  then show ?thesis 
    unfolding \<Delta>0_def
    using knat 
    by blast
qed 

lemma Neg_\<Delta>0 [simp]: 
  fixes \<phi> 
  assumes "\<phi> \<in> \<Delta>0" 
  shows "Neg(\<phi>) \<in> \<Delta>0" 
  unfolding Neg_def 
  using assms
  by auto

lemma And_\<Delta>0 [simp]: 
  fixes \<phi> \<psi>
  assumes "\<phi> \<in> \<Delta>0" "\<psi> \<in> \<Delta>0"
  shows "And(\<phi>, \<psi>) \<in> \<Delta>0" 
  unfolding And_def 
  using assms
  by auto

lemma Or_\<Delta>0 [simp] : 
  fixes \<phi> \<psi>
  assumes "\<phi> \<in> \<Delta>0" "\<psi> \<in> \<Delta>0"
  shows "Or(\<phi>, \<psi>) \<in> \<Delta>0" 
  unfolding Or_def 
  using assms
  by auto

lemma Implies_\<Delta>0 [simp] : 
  fixes \<phi> \<psi>
  assumes "\<phi> \<in> \<Delta>0" "\<psi> \<in> \<Delta>0"
  shows "Implies(\<phi>, \<psi>) \<in> \<Delta>0" 
  unfolding Implies_def 
  using assms
  by auto
  
lemma Iff_\<Delta>0 [simp] : 
  fixes \<phi> \<psi>
  assumes "\<phi> \<in> \<Delta>0" "\<psi> \<in> \<Delta>0"
  shows "Iff(\<phi>, \<psi>) \<in> \<Delta>0" 
  unfolding Iff_def 
  using assms
  by auto

lemma BExists_\<Delta>0[simp] : 
  fixes \<phi> n 
  assumes "\<phi> \<in> \<Delta>0" "n \<in> nat" 
  shows "BExists(n, \<phi>) \<in> \<Delta>0" 
proof - 
  obtain m where mH: "\<phi> \<in> \<Delta>0_from^m(\<Delta>0_base)" "m \<in> nat" using assms unfolding \<Delta>0_def by auto
  then have "BExists(n, \<phi>) \<in> \<Delta>0_from^succ(m)(\<Delta>0_base)"
    apply simp
    apply(subst \<Delta>0_from_def, simp, rule disjI2, rule disjI2)
    unfolding BExists_def
    apply(rule conjI)
    unfolding BExists'_def
    using assms \<Delta>0_subset
     apply force
    apply(rule_tac x="succ(n)" in bexI, rule conjI, simp)
     apply(rule_tac x="\<phi>" in bexI, simp, simp, simp add:assms)
    done
  then show ?thesis 
    using assms mH
    unfolding \<Delta>0_def
    by blast
qed

lemma BExists_formula : 
  fixes \<phi> n 
  assumes "\<phi> \<in> \<Delta>0" "n \<in> nat" 
  shows "BExists(n, \<phi>) \<in> formula" 
  using assms \<Delta>0_subset
  by auto

lemma BForall_\<Delta>0 [simp] : 
  fixes \<phi> n 
  assumes "\<phi> \<in> \<Delta>0" "n \<in> nat" 
  shows "BForall(n, \<phi>) \<in> \<Delta>0" 
  unfolding BForall_def 
  using assms
  by auto

lemma \<Delta>0_sats_iff : 
  fixes A B env \<phi>
  assumes "A \<subseteq> B" "env \<in> list(A)" "\<phi> \<in> \<Delta>0" "Transset(A)" "arity(\<phi>) \<le> length(env)" 
  shows "sats(A, \<phi>, env) \<longleftrightarrow> sats(B, \<phi>, env)" 
proof - 
  have main : "\<And>n. n \<in> nat \<Longrightarrow> \<forall>\<phi> \<in> \<Delta>0_from^n (\<Delta>0_base). (\<forall>env \<in> list(A). arity(\<phi>) \<le> length(env) \<longrightarrow> (sats(A, \<phi>, env) \<longleftrightarrow> sats(B, \<phi>, env)))" 
  proof (rule_tac P="\<lambda>n. \<forall>\<phi> \<in> \<Delta>0_from^n (\<Delta>0_base). (\<forall>env \<in> list(A). arity(\<phi>) \<le> length(env) \<longrightarrow> (sats(A, \<phi>, env) \<longleftrightarrow> sats(B, \<phi>, env)))" in nat_induct, simp)
    show "\<forall>\<phi> \<in> \<Delta>0_from^0 (\<Delta>0_base). (\<forall>env \<in> list(A). arity(\<phi>) \<le> length(env) \<longrightarrow> (sats(A, \<phi>, env) \<longleftrightarrow> sats(B, \<phi>, env)))" 
      unfolding \<Delta>0_base_def
      apply (simp, clarify)
      apply(rename_tac \<phi> n m env, subgoal_tac "env \<in> list(B)") 
       apply(rename_tac \<phi> n m env, case_tac "\<phi> = Member(n, m)", simp, simp)
      apply(rule subsetD, rule list_mono)
      using assms 
      by auto
  next 
    fix n 
    assume assms1 : "n \<in> nat" "\<forall>\<phi>\<in> \<Delta>0_from^n (\<Delta>0_base).(\<forall>env\<in>list(A). arity(\<phi>) \<le> length(env) \<longrightarrow> (A, env \<Turnstile> \<phi> \<longleftrightarrow> B, env \<Turnstile> \<phi>))"

    define X where "X \<equiv> \<Delta>0_from^n (\<Delta>0_base)"

    have Xsubset : "X \<subseteq> formula" 
      using \<Delta>0_subset assms1
      unfolding \<Delta>0_def X_def 
      by auto

    have ih1 : "\<And>env \<phi>. \<phi> \<in> X \<Longrightarrow> env \<in> list(A) \<Longrightarrow> arity(\<phi>) \<le> length(env) \<Longrightarrow> A, env \<Turnstile> \<phi> \<Longrightarrow> B, env \<Turnstile> \<phi>" using assms1 X_def by auto
    have ih2 : "\<And>env \<phi>. \<phi> \<in> X \<Longrightarrow> env \<in> list(A) \<Longrightarrow> arity(\<phi>) \<le> length(env) \<Longrightarrow> B, env \<Turnstile> \<phi> \<Longrightarrow> A, env \<Turnstile> \<phi>" using assms1 X_def by auto

    have Hnand: "\<And>\<phi> \<psi> env. \<phi> \<in> X \<Longrightarrow> \<psi> \<in> X \<Longrightarrow> env \<in> list(A) \<Longrightarrow> arity(Nand(\<phi>, \<psi>)) \<le> length(env) \<Longrightarrow> A, env \<Turnstile> Nand(\<phi>, \<psi>) \<longleftrightarrow> B, env \<Turnstile> Nand(\<phi>, \<psi>)" 
    proof - 
      fix \<phi> \<psi> env 
      assume assms2 : "\<phi> \<in> X" "\<psi> \<in> X" "env \<in> list(A)" "arity(Nand(\<phi>, \<psi>)) \<le> length(env)" 
      have "arity(\<phi>) \<le> length(env)" 
        apply(rule_tac j="arity(Nand(\<phi>, \<psi>))" in le_trans)
         apply simp
         apply(rule max_le1)
        using assms2 Xsubset 
        by auto
      then have iff1: "A, env \<Turnstile> \<phi> \<longleftrightarrow> B, env \<Turnstile> \<phi>" 
        using ih1 ih2 assms2 by auto

      have "arity(\<psi>) \<le> length(env)" 
        apply(rule_tac j="arity(Nand(\<phi>, \<psi>))" in le_trans)
         apply simp
         apply(rule max_le2)
        using assms2 Xsubset 
        by auto
      then have iff2: "A, env \<Turnstile> \<psi> \<longleftrightarrow> B, env \<Turnstile> \<psi>" 
        using ih1 ih2 assms2 by auto
      
      have envinBlist : "env \<in> list(B)"
        apply(rule subsetD, rule list_mono)
        using assms2 assms
        by auto

      then show "A, env \<Turnstile> Nand(\<phi>, \<psi>) \<longleftrightarrow> B, env \<Turnstile> Nand(\<phi>, \<psi>)" 
        using iff1 iff2 assms2 Xsubset 
        by auto
    qed

    have Hbex : "\<And>m \<phi> env. m \<in> nat \<Longrightarrow> \<phi> \<in> X \<Longrightarrow> env \<in> list(A) \<Longrightarrow> arity(BExists'(m, \<phi>)) \<le> length(env) \<Longrightarrow> A, env \<Turnstile> BExists'(m, \<phi>) \<longleftrightarrow> B, env \<Turnstile> BExists'(m, \<phi>)"
    proof - 
      fix m \<phi> env
      assume assms2 : "m \<in> nat" "\<phi> \<in> X" "env \<in> list(A)" "arity(BExists'(m, \<phi>)) \<le> length(env)"

      have "\<phi> \<in> \<Delta>0" 
        unfolding \<Delta>0_def 
        using assms1 assms2 X_def 
        by auto
      then have phiformula: "\<phi> \<in> formula" 
        using \<Delta>0_subset 
        by auto

      have envinBlist : "env \<in> list(B)"
        apply(rule subsetD, rule list_mono)
        using assms2 assms
        by auto

      have eq: "succ(arity(BExists'(m, \<phi>))) = 1 \<union> succ(m) \<union> arity(\<phi>)"
        unfolding BExists'_def 
        apply simp
        apply(subst succ_pred_eq)
        apply(rule Un_nat_type, rule Un_nat_type, simp, simp add:assms2)
        using phiformula 
        by auto
      have "arity(\<phi>) \<le> succ(arity(BExists'(m, \<phi>)))"
        apply(subst eq) 
        apply(rule max_le2, rule Ord_Un, simp, simp, simp add:assms2)
        using phiformula 
        by auto
      then have arityle:  "arity(\<phi>) \<le> succ(length(env))" 
        by(rule_tac j="succ(arity(BExists'(m, \<phi>)))" in le_trans, simp, simp add:assms2)

      have mle : "m \<le> length(env)"
        apply(rule_tac b="succ(arity(BExists'(m, \<phi>)))" in lt_le_lt)
         apply(subst eq, rule ltI, simp)
         apply(rule Ord_Un, rule Ord_Un, simp, simp add:assms2)
        using phiformula assms2 
        by auto

      have I1 : "A, env \<Turnstile> BExists'(m, \<phi>) \<longleftrightarrow> (\<exists>x \<in> A. x \<in> nth(m, Cons(x, env)) \<and> sats(A, \<phi>, Cons(x, env)))"
        unfolding BExists'_def 
        using assms2
        by auto
      have I2 : "... \<longleftrightarrow> (\<exists>x \<in> B. x \<in> nth(m, Cons(x, env)) \<and> sats(B, \<phi>, Cons(x, env)))" 
        apply(rule iffI, clarify)
         apply(rename_tac x, rule_tac x=x in bexI, rule conjI, simp, rule ih1, simp add:assms2, simp add:assms2, simp, simp add:arityle, simp)
        using assms 
         apply force
        apply clarify 
        apply(rename_tac x, subgoal_tac "x \<in> A", rule_tac x=x in bexI, simp)
          apply(rule ih2, simp add:assms2, simp, simp add:assms2, simp, simp add:arityle, simp, simp)
        apply(rule_tac n=m in natE, simp add:assms2)
         apply(rule mem_irrefl, simp)
        apply simp 
        apply(rename_tac x m', subgoal_tac "nth(m', env) \<in> A") 
        using assms Transset_def 
         apply force
        apply(rule nth_type, simp add:assms2, rule_tac b=m in lt_le_lt, simp, rule mle)
        done
      have I3 : "... \<longleftrightarrow> B, env \<Turnstile> BExists'(m, \<phi>)"
        using envinBlist BExists'_def by auto
      show " A, env \<Turnstile> BExists'(m, \<phi>) \<longleftrightarrow> B, env \<Turnstile> BExists'(m, \<phi>)" 
        using I1 I2 I3 
        by auto 
    qed
        
    show "\<forall>\<phi>\<in>\<Delta>0_from^succ(n) (\<Delta>0_base). \<forall>env\<in>list(A). arity(\<phi>) \<le> length(env) \<longrightarrow> A, env \<Turnstile> \<phi> \<longleftrightarrow> B, env \<Turnstile> \<phi>" 
      apply(simp, rule_tac b="\<Delta>0_from^n (\<Delta>0_base)" and a=X in ssubst, simp add:X_def, clarify)
      unfolding \<Delta>0_from_def 
      apply simp
      apply(rename_tac \<phi> env, case_tac "\<phi> \<in> X", simp)
      using ih1 ih2 
       apply force
      apply clarify
      apply(rule disjE, simp)
      apply(clarify, rule Hnand, simp, simp, simp, simp)
      apply(clarify, rule Hbex, simp, simp, simp)
      unfolding BExists'_def 
      by simp
  qed

  then show "A, env \<Turnstile> \<phi> \<longleftrightarrow> B, env \<Turnstile> \<phi>" 
    using assms 
    unfolding \<Delta>0_def 
    by auto
qed

lemma ren_\<Delta>0 : 
  fixes \<phi> m n f
  assumes "\<phi> \<in> \<Delta>0" "m \<in> nat" "n \<in> nat" "f \<in> m \<rightarrow> n" "arity(\<phi>) \<le> m"
  shows "ren(\<phi>)`m`n`f \<in> \<Delta>0" 
proof - 

  have value_type: "\<And>k f m n. m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> f \<in> m \<rightarrow> n \<Longrightarrow> f`k \<in> nat" 
  proof(rename_tac k f m n, case_tac "k \<in> m")
    fix k f m n assume assms2 : "k \<in> m" "m \<in> nat" "n \<in> nat" "f \<in> m \<rightarrow> n"    
    then have "f`k \<in> range(f)" using apply_rangeI assms2 Pi_def by auto 
    then have "f`k \<in> n" using assms2 Pi_def by auto 
    then have "f`k < n" using ltI assms2 by auto
    then show "f`k \<in> nat" using assms2 lt_nat_in_nat by auto
  next 
    fix k f m n assume assms2 : "k \<notin> m" "m \<in> nat" "n \<in> nat" "f \<in> m \<rightarrow> n"
    then have "k \<notin> domain(f)" using assms2 Pi_def by auto 
    then have "f`k = 0" using apply_0 by auto 
    then show "f`k \<in> nat" by auto
  qed

  have "\<And>i. i \<in> nat \<Longrightarrow>  \<forall>m \<in> nat. \<forall>n \<in> nat. \<forall>f \<in> m \<rightarrow> n. \<forall>\<phi> \<in> formula. \<phi> \<in> \<Delta>0_from^i(\<Delta>0_base) \<longrightarrow> arity(\<phi>) \<le> m \<longrightarrow> ren(\<phi>)`m`n`f \<in> \<Delta>0_from^i(\<Delta>0_base)"
  proof(rule_tac P="\<lambda>i. \<forall>m \<in> nat. \<forall>n \<in> nat. \<forall>f \<in> m \<rightarrow> n. \<forall>\<phi> \<in> formula. \<phi> \<in> \<Delta>0_from^i(\<Delta>0_base) \<longrightarrow> arity(\<phi>) \<le> m \<longrightarrow> ren(\<phi>)`m`n`f \<in> \<Delta>0_from^i(\<Delta>0_base)" in nat_induct, simp)
    fix i 
    assume assms1 : "i \<in> nat" 
    show "\<forall>m\<in>nat. \<forall>n\<in>nat. \<forall>f\<in>m \<rightarrow> n. \<forall>\<phi>\<in>formula. \<phi> \<in> \<Delta>0_from^0 (\<Delta>0_base) \<longrightarrow> arity(\<phi>) \<le> m \<longrightarrow> ren(\<phi>) ` m ` n ` f \<in> \<Delta>0_from^0 (\<Delta>0_base)" 
    proof(rule ballI, rule ballI, rule ballI, rule ballI , rule impI, rule impI)
      fix m n f \<phi> 
      assume assms2: "m \<in> nat" "n \<in> nat" "f \<in> m \<rightarrow> n" "\<phi> \<in> formula" "\<phi> \<in> \<Delta>0_from^0 (\<Delta>0_base)" 
      show "ren(\<phi>) ` m ` n ` f \<in> \<Delta>0_from^0 (\<Delta>0_base)"
        using assms2 
        unfolding \<Delta>0_base_def
        apply auto
               apply(rule value_type, simp_all)+
        done
    qed
  next 
    fix i 
    assume assms1: "i \<in> nat" "\<forall>m\<in>nat. \<forall>n\<in>nat. \<forall>f\<in>m \<rightarrow> n. \<forall>\<phi>\<in>formula. \<phi> \<in> \<Delta>0_from^i (\<Delta>0_base) \<longrightarrow> arity(\<phi>) \<le> m \<longrightarrow> ren(\<phi>) ` m ` n ` f \<in> \<Delta>0_from^i (\<Delta>0_base)"

    have ih : "\<And>m n f \<phi>. m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> f \<in> m \<rightarrow> n \<Longrightarrow> \<phi> \<in> \<Delta>0_from^i(\<Delta>0_base) \<Longrightarrow> arity(\<phi>) \<le> m \<Longrightarrow> ren(\<phi>)`m`n`f \<in> \<Delta>0_from^i(\<Delta>0_base)" 
      apply(rename_tac m n f \<phi>, subgoal_tac "\<phi> \<in> \<Delta>0")
      using \<Delta>0_subset assms1
       apply blast
      unfolding \<Delta>0_def 
      using assms1
      by auto

    show " \<forall>m\<in>nat. \<forall>n\<in>nat. \<forall>f\<in>m \<rightarrow> n. \<forall>\<phi>\<in>formula. \<phi> \<in> \<Delta>0_from^succ(i) (\<Delta>0_base) \<longrightarrow> arity(\<phi>) \<le> m \<longrightarrow> ren(\<phi>) ` m ` n ` f \<in> \<Delta>0_from^succ(i) (\<Delta>0_base)" 
    proof (rule ballI, rule ballI, rule ballI, rule ballI , rule impI, rule impI)
      fix m n f \<phi> 
      assume assms2: "m \<in> nat" "n \<in> nat" "f \<in> m \<rightarrow> n" "\<phi> \<in> formula" "\<phi> \<in> \<Delta>0_from^succ(i) (\<Delta>0_base)" "arity(\<phi>) \<le> m"

      have H: "\<phi> \<in> \<Delta>0_from^i (\<Delta>0_base) \<or> (\<exists>x\<in>\<Delta>0_from^i (\<Delta>0_base). \<exists>y\<in>\<Delta>0_from^i (\<Delta>0_base). \<phi> = Nand(x, y)) \<or>
            (\<exists>j\<in>nat. \<exists>\<psi>\<in>\<Delta>0_from^i (\<Delta>0_base). j \<noteq> 0 \<and> \<phi> = BExists'(j, \<psi>))"
        using assms2 \<Delta>0_from_def
        by auto

      show "ren(\<phi>) ` m ` n ` f \<in> \<Delta>0_from^succ(i) (\<Delta>0_base)" 
        using H 
        apply(rule disjE, simp)
        using assms1 assms2 \<Delta>0_from_def
         apply force
        apply(rule disjE, simp, simp)
         apply clarify
         apply(rename_tac x y, subgoal_tac "x \<in> \<Delta>0 \<and> y \<in> \<Delta>0")
        using assms2
         apply simp
         apply(rename_tac x y, subgoal_tac "ren(x)`m`n`f \<in> \<Delta>0_from^i (\<Delta>0_base) \<and> ren(y)`m`n`f \<in> \<Delta>0_from^i (\<Delta>0_base)")
          apply(subst \<Delta>0_from_def)
        using assms2 assms1
          apply force
         apply(rule conjI, rule ih)
              apply auto[4]
          apply(rename_tac x y, rule_tac b="arity(x) \<union> arity(y)" in le_lt_lt)
            apply(rule max_le1)
        using \<Delta>0_subset
             apply auto[3]
          apply(rule ih)
              apply auto[4]
          apply(rename_tac x y, rule_tac b="arity(x) \<union> arity(y)" in le_lt_lt)
           apply(rule max_le2)
        using \<Delta>0_subset
            apply auto[3]
         apply(simp add:\<Delta>0_def)
        using assms1
         apply force
        apply simp
        apply clarify 
        apply(rename_tac j \<psi>, subgoal_tac "\<psi> \<in> \<Delta>0")
         apply(rename_tac j \<psi>, subgoal_tac "j \<le> m")
          apply(subst \<Delta>0_from_def, simp, rule disjI2, rule disjI2, rule conjI)
           apply(rule ren_tc, simp add:BExists'_def)
        using \<Delta>0_subset
              apply force
        using assms2
             apply auto[3]
          apply(rename_tac j \<psi>, rule_tac x="sum_id(m, f)`j" in bexI, rule conjI)
            apply(rename_tac j \<psi>, rule_tac n=j in natE, simp, simp, simp)
            apply(subst sum_idS[where q=n])
        using assms2
                apply auto[3]
             apply(rule ltD)
             apply auto[3]
           apply(rule_tac x="ren(\<psi>) ` succ(m) ` succ(n) ` sum_id(m, f)" in bexI)
        unfolding BExists'_def Exists_def Neg_def And_def
            apply(subgoal_tac "sum_id(m, f) \<in> succ(m) \<rightarrow> succ(n)", simp add:assms2)
             apply(rule sum_id0, simp add:assms2, rule sum_id_tc)
        using assms2
              apply auto[3]
           apply(rule ih)
        using assms2
               apply auto[2]
             apply(rule sum_id_tc)
        using assms2
               apply auto[4]
           apply(rename_tac j \<psi>, subgoal_tac "arity(\<psi>) \<le> succ(arity(\<phi>))")
            apply(rename_tac j \<psi>, rule_tac j="succ(arity(\<phi>))" in le_trans, simp)
        using assms2
            apply (simp, simp)
           apply(subst succ_pred_eq)
        using \<Delta>0_subset
             apply force
            apply simp
           apply(rule ltI)
        using \<Delta>0_subset
            apply(subst succ_Un_distrib, simp, force)+
            apply simp
        using \<Delta>0_subset
           apply force
          apply(rule_tac m="succ(m)" and n="succ(n)" in value_type)
        using assms2
            apply auto[2]
          apply(rule sum_id_tc)
        using assms2
            apply auto[3]
         apply(rule_tac b="arity(\<phi>)" in le_lt_lt)
          apply simp
          apply(rename_tac j \<psi>, subgoal_tac "succ(j) \<le> succ(pred(1 \<union> succ(j) \<union> arity(\<psi>)))")
           apply simp
          apply(subst succ_pred_eq)
        using \<Delta>0_subset
            apply force
           apply simp
        apply(rule ltI)
        using \<Delta>0_subset
           apply(subst succ_Un_distrib, simp, force)+
           apply simp
        using \<Delta>0_subset assms2
          apply auto[2]
        unfolding \<Delta>0_def
        using assms1
        by auto
    qed
  qed
  then have main : "\<And>i m n f \<phi>. i \<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> f \<in> m \<rightarrow> n \<Longrightarrow> arity(\<phi>) \<le>  m \<Longrightarrow> \<phi> \<in> formula \<Longrightarrow> \<phi> \<in> \<Delta>0_from^i(\<Delta>0_base) \<Longrightarrow> ren(\<phi>)`m`n`f \<in> \<Delta>0_from^i(\<Delta>0_base)"
    by auto

  have "\<exists>i \<in> nat. \<phi> \<in> \<Delta>0_from^i(\<Delta>0_base)" 
    using assms
    unfolding \<Delta>0_def
    by auto
  then obtain i where iH: "i \<in> nat" "\<phi> \<in> \<Delta>0_from^i(\<Delta>0_base)" by auto

  show ?thesis 
    unfolding \<Delta>0_def 
    apply simp
    apply(rule_tac x=i in bexI)
     apply(rule main)
    using assms iH \<Delta>0_subset 
    apply auto
    done
qed

lemma sats_BExists_iff :
  fixes A \<phi> env n 
  assumes "\<phi> \<in> formula" "n < length(env)" "env \<in> list(A)" 
  shows "sats(A, BExists(n, \<phi>), env) \<longleftrightarrow> (\<exists>x \<in> A. x \<in> nth(n, env) \<and> sats(A, \<phi>, Cons(x, env)))" 
  unfolding BExists_def BExists'_def 
  using assms lt_nat_in_nat
  by auto
  
lemma sats_BForall_iff : 
  fixes A \<phi> env n 
  assumes "\<phi> \<in> formula" "n < length(env)" "env \<in> list(A)" 
  shows "sats(A, BForall(n, \<phi>), env) \<longleftrightarrow> (\<forall>x \<in> A. x \<in> nth(n, env) \<longrightarrow> sats(A, \<phi>, Cons(x, env)))" 
  unfolding BForall_def BExists_def BExists'_def 
  using assms lt_nat_in_nat
  by auto

lemma arity_BExists : 
  fixes \<phi> n 
  assumes "n \<in> nat" "\<phi> \<in> formula" 
  shows "arity(BExists(n, \<phi>)) \<le> succ(n) \<union> pred(arity(\<phi>))" 

  unfolding BExists_def BExists'_def 
  using assms
  apply simp
  apply(rule pred_le, simp_all)
  apply(rule Un_least_lt)+
    apply simp_all
   apply(rule ltI, simp_all)
  apply(subst succ_Un_distrib, simp_all)
  apply(rule_tac n="arity(\<phi>)" in natE, simp_all)
  apply(rule ltI, simp_all)
  done

end