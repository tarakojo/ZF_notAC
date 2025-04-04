theory Fn_Perm_Definition
  imports SymExt_ZF 
begin 

context M_ctm begin 

definition finite_M where "finite_M(x) \<equiv> \<exists>n \<in> nat. inj(x, n) \<inter> M \<noteq> 0"  
definition finite_M_fm where "finite_M_fm(N, x) \<equiv> Exists(Exists(And(Member(0, N#+2), injection_fm(x#+2, 0, 1))))"

lemma finite_M_fm_type : 
  fixes i j 
  assumes "i \<in> nat" "j \<in> nat" 
  shows "finite_M_fm(i, j) \<in> formula" 
  unfolding finite_M_fm_def 
  using assms
  by auto

lemma arity_finite_M_fm : 
  fixes i j 
  assumes "i \<in> nat" "j \<in> nat" 
  shows "arity(finite_M_fm(i, j)) \<le> succ(i) \<union> succ(j)" 
  unfolding finite_M_fm_def bijection_fm_def injection_fm_def surjection_fm_def typed_function_fm_def
  using assms
  apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  done

lemma sats_finite_M_fm_iff : 
  fixes env i j x
  assumes "env \<in> list(M)" "i < length(env)" "j < length(env)" "nth(i, env) = nat" "nth(j, env) = x"
  shows "sats(M, finite_M_fm(i, j), env) \<longleftrightarrow> finite_M(x)" 

  unfolding finite_M_fm_def finite_M_def
  using assms nth_type lt_nat_in_nat nat_in_M
  apply simp
  apply(rule iffI, clarsimp)
   apply(rename_tac f n, rule_tac x=n in bexI, force, force)
  apply clarsimp
  apply(rule not_emptyE, assumption)
  apply(rename_tac n f, rule_tac x=f in bexI)
   apply(rename_tac n f, rule_tac x=n in bexI, force)
  using nat_in_M transM 
  by auto

definition is_finite_function_fm where 
  "is_finite_function_fm(d, r, N, f) \<equiv> 
    And(function_fm(f), 
    And(Exists(
      And(domain_fm(f#+1, 0), 
      And(subset_fm(0, d #+ 1), 
          finite_M_fm(N #+ 1, 0)))), 
        Exists(And(range_fm(f#+1, 0), subset_fm(0, r#+1)))))" 

lemma is_finite_function_fm_type [simp] : 
  fixes i j k l 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" "l \<in> nat" 
  shows "is_finite_function_fm(i, j, k, l) \<in> formula"
  unfolding is_finite_function_fm_def 
  apply(subgoal_tac "finite_M_fm(k #+ 1, 0) \<in> formula")
  using assms 
   apply force
  using finite_M_fm_type
  by auto

lemma arity_is_finite_function_fm : 
  fixes i j k l 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" "l \<in> nat" 
  shows "arity(is_finite_function_fm(i, j, k, l)) \<le> succ(i) \<union> succ(j) \<union> succ(k) \<union> succ(l)" 
  unfolding is_finite_function_fm_def 
  unfolding bijection_fm_def injection_fm_def surjection_fm_def typed_function_fm_def
  apply(subgoal_tac "finite_M_fm(k #+ 1, 0) \<in> formula")
  using assms
   apply simp
   apply(rule Un_least_lt)
    apply(subst arity_function_fm, simp)
    apply(subst succ_Un_distrib, simp, simp)+
    apply(rule ltI, simp, simp)
   apply(rule Un_least_lt)
    apply(rule pred_le, simp, simp)+
    apply(rule Un_least_lt)
     apply(subst arity_domain_fm, simp, simp)
     apply(rule Un_least_lt)
      apply simp
      apply(rule ltI, simp, simp, simp)
    apply(rule Un_least_lt)+
      apply (simp, simp)
     apply(rule ltI, simp, simp)
    apply(rule le_trans, rule arity_finite_M_fm, simp, simp)
    apply(rule Un_least_lt)+
     apply simp
     apply(rule ltI, simp, simp, simp)
   apply(rule pred_le, simp, simp)+
   apply(rule Un_least_lt)+
    apply(subst arity_range_fm, simp, simp)
    apply(rule Un_least_lt)+
     apply (simp, rule ltI, simp, simp, simp)
   apply(rule Un_least_lt)+
    apply(simp, simp, rule ltI, simp, simp)
  using finite_M_fm_type assms
  by auto

lemma sats_is_finite_function_fm : 
  fixes d r f i j k l env 
  assumes "env \<in> list(M)" "i < length(env)" "j < length(env)" "k < length(env)" "l < length(env)" 
          "nth(i, env) = d" "nth(j, env) = r" "nth(k, env) = nat" "nth(l, env) = f" 
  shows "sats(M, is_finite_function_fm(i, j, k, l), env) \<longleftrightarrow> 
         (function(f) \<and> domain(f) \<subseteq> d \<and> finite_M(domain(f)) \<and> range(f) \<subseteq> r)" 
  unfolding is_finite_function_fm_def
  apply(rule_tac Q="function(f) \<and> 
                    (\<exists>d' \<in> M. d' = domain(f) \<and> d' \<subseteq> d \<and> finite_M(d')) \<and> 
                    (\<exists>r' \<in> M. r' = range(f) \<and> r' \<subseteq> r)" in iff_trans)
   apply(rule iff_trans, rule sats_And_iff, simp add:assms)
   apply(rule iff_conjI2)
  using lt_nat_in_nat assms nth_type
    apply force
   apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
    apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)+
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
  using lt_nat_in_nat assms nth_type
     apply force
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
     apply(rule iff_trans, rule sats_subset_fm)
  using lt_nat_in_nat assms nth_type M_ctm_axioms M_ctm_def M_ctm_axioms_def
         apply auto[5]
    apply(rule sats_finite_M_fm_iff)
  using lt_nat_in_nat assms nth_type M_ctm_axioms M_ctm_def M_ctm_axioms_def
        apply auto[5]
   apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)
   apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
  using sats_range_fm lt_nat_in_nat assms nth_type 
    apply auto[1]
  apply(rule iff_trans, rule sats_subset_fm)
  using sats_range_fm lt_nat_in_nat assms nth_type M_ctm_axioms M_ctm_def M_ctm_axioms_def
       apply auto[5]
  apply(rule iff_conjI2, simp)
  apply (rule iffI, clarsimp, rule conjI)
  using assms nth_type lt_nat_in_nat domain_closed range_closed
  by auto

definition Fn where "Fn \<equiv> { f \<in> Pow((nat \<times> nat) \<times> 2) \<inter> M. function(f) \<and> domain(f) \<subseteq> nat \<times> nat \<and> finite_M(domain(f)) \<and> range(f) \<subseteq> 2 }"

lemma Fn_in_M : "Fn \<in> M" 
proof - 

  define X where "X \<equiv> { f \<in> Pow((nat \<times> nat) \<times> 2) \<inter> M. sats(M, is_finite_function_fm(1, 2, 3, 0), [f] @ [nat\<times>nat, 2, nat]) }"
  have "X \<in> M" 
    unfolding X_def
    apply(rule separation_notation)
     apply(rule separation_ax, rule is_finite_function_fm_type)
    using nat_in_M cartprod_closed zero_in_M succ_in_MI
          apply auto[5]
     apply(rule le_trans, rule arity_is_finite_function_fm)
         apply auto[4]
     apply(rule Un_least_lt)+
        apply auto[4]
    apply(rule M_powerset)
    using cartprod_closed nat_in_M zero_in_M succ_in_MI
    by auto

  have "X = Fn" 
    unfolding X_def Fn_def 
    apply(rule iff_eq)
    apply(rule sats_is_finite_function_fm)
    using nat_in_M cartprod_closed zero_in_M succ_in_MI
    apply auto[6]
    by auto
  then show ?thesis using \<open>X \<in> M\<close> by auto
qed

definition Fn_leq where "Fn_leq \<equiv> { <f, g> \<in> Fn \<times> Fn. g \<subseteq> f }" 

lemma Fn_leq_in_M : "Fn_leq \<in> M" 
proof - 
  define X where "X \<equiv> { v \<in> Fn \<times> Fn . sats(M, Exists(Exists(And(pair_fm(0, 1, 2), subset_fm(1, 0)))), [v] @ []) }" 
  have "X \<in> M" 
    unfolding X_def
    apply(rule separation_notation)
     apply(rule separation_ax)
       apply auto[2]
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    using Fn_in_M cartprod_closed
    by auto
  have "X = { <f, g> \<in> Fn \<times> Fn. g \<subseteq> f }" 
    unfolding X_def 
    apply(rule equality_iffI, rule iffI)
    using pair_in_M_iff sats_subset_fm' Fn_in_M transM
    by auto
  then show ?thesis using \<open>X \<in> M\<close> Fn_leq_def by auto
qed

lemma Fn_partial_ord : "partial_order_on(Fn, Fn_leq)" 
  unfolding partial_order_on_def preorder_on_def 
  apply(rule conjI)+
  unfolding refl_def Fn_leq_def trans_on_def antisym_def
  by auto

lemma zero_in_Fn : "0 \<in> Fn" 
  apply(subst Fn_def, simp, rule conjI, rule zero_in_M, rule conjI)
   apply(simp add:function_def)
  unfolding finite_M_def 
  apply(rule_tac x=0 in bexI, rule_tac a="0" in not_emptyI) 
   apply simp
   apply(rule conjI)
  unfolding inj_def
  using zero_in_M
  by auto

lemma Fn_forcing_notion : "forcing_notion(Fn, Fn_leq, 0)"
  unfolding forcing_notion_def
  using Fn_partial_ord partial_order_on_def zero_in_Fn
  apply simp
  unfolding Fn_leq_def
  apply(rule ballI, simp)
  done

lemma Fn_forcing_data_partial : "forcing_data_partial(Fn, Fn_leq, 0, M, enum)" 
  unfolding forcing_data_partial_def forcing_data_def forcing_data_partial_axioms_def forcing_data_axioms_def 
  using Fn_forcing_notion M_ctm_axioms Fn_in_M Fn_leq_in_M Fn_leq_def Fn_partial_ord
  by auto

definition nat_perms where "nat_perms \<equiv> bij(nat, nat) \<inter> M" 

lemma nat_perms_in_M : "nat_perms \<in> M" 
proof - 
  define X where "X \<equiv> { f \<in> Pow(nat \<times> nat) \<inter> M. sats(M, bijection_fm(1, 1, 0), [f] @ [nat]) }" 

  have XinM : "X \<in> M" 
    unfolding X_def
    apply(rule separation_notation)
     apply(rule separation_ax)
    using nat_in_M
       apply auto[2]
    unfolding bijection_fm_def injection_fm_def surjection_fm_def
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    apply(rule M_powerset)
    using cartprod_closed nat_in_M
    by auto

  have "X = nat_perms"
    unfolding X_def nat_perms_def 
    using nat_in_M bij_def inj_def Pi_def 
    by auto
  then show "nat_perms \<in> M" using XinM by auto
qed

definition Fn_perm where "Fn_perm(f, p) \<equiv> { <<f`n, m>, l> . <<n, m>, l> \<in> p }" 
definition Fn_perm' where "Fn_perm'(f) \<equiv> { <p, Fn_perm(f, p)>. p \<in> Fn }" 
definition Fn_perms where "Fn_perms \<equiv> { Fn_perm'(f). f \<in> nat_perms }" 

lemma Fn_permE : 
  fixes f p b 
  assumes "p \<in> Fn" "f \<in> nat_perms" "b \<in> Fn_perm(f, p)" 
  shows "\<exists>n \<in> nat. \<exists>m \<in> nat. \<exists>l \<in> 2. <<n, m>, l> \<in> p \<and> b = <<f`n, m>, l>" 
proof - 
  have H: "p \<subseteq> (nat \<times> nat) \<times> 2" 
    using assms Fn_def 
    by auto
  have "\<exists>v \<in> p. b = \<langle>\<langle>f ` fst(fst(v)), snd(fst(v))\<rangle>, snd(v)\<rangle>"
    using assms
    unfolding Fn_perm_def split_def
    by auto
  then obtain v where vH: "v \<in> p" "b = \<langle>\<langle>f ` fst(fst(v)), snd(fst(v))\<rangle>, snd(v)\<rangle>" by auto
  then obtain x y z where veq: "v = <<x, y>, z>" "x \<in> nat" "y \<in> nat" "z \<in> 2" using H by blast
  then have beq: "b = <<f`x, y>, z>" using vH by auto
  have "p \<in> M" using Fn_in_M transM assms by auto
  then have "v \<in> M" using transM vH by auto
  then have "x \<in> nat \<and> y \<in> nat \<and> z \<in> 2" using veq pair_in_M_iff by auto
  then show ?thesis using beq veq vH by auto
qed


definition is_Fn_perm_elem_fm where (* n m l <n, m> fn <fn, m> (f a v) *)
  "is_Fn_perm_elem_fm(f, a, v) \<equiv> 
    Exists(Exists(Exists(Exists(Exists(Exists(
      And(pair_fm(0, 1, 3), 
      And(pair_fm(3, 2, a #+ 6), 
      And(pair_fm(4, 1, 5), 
      And(fun_apply_fm(f #+ 6, 0, 4), 
          pair_fm(5, 2, v #+ 6)))))))))))" 

lemma is_Fn_perm_elem_fm_type : 
  fixes i j k
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" 
  shows "is_Fn_perm_elem_fm(i, j, k) \<in> formula" 
  unfolding is_Fn_perm_elem_fm_def 
  using assms
  by auto

lemma arity_is_Fn_perm_elem_fm : 
  fixes i j k
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" 
  shows "arity(is_Fn_perm_elem_fm(i, j, k)) \<le> succ(i) \<union> succ(j) \<union> succ(k)"
  unfolding is_Fn_perm_elem_fm_def
  using assms
  apply simp
  apply(rule pred_le, simp, simp)+
  apply(subst arity_fun_apply_fm, simp, simp, simp)
  apply(subst arity_pair_fm, simp, simp, simp)+
  apply simp
  apply(rule Un_least_lt)+
    apply simp
   apply(rule Un_least_lt)+
    apply auto[2]
  apply(rule Un_least_lt)+
    apply simp
   apply(rule Un_least_lt)+
    apply (simp, simp)
   apply(rule ltI, simp, simp)
  apply(rule Un_least_lt)+
    apply simp
   apply(rule Un_least_lt)+
    apply auto[2]
  apply(rule Un_least_lt)+
     apply simp
     apply(rule ltI)
      apply auto[4]
  apply(rule Un_least_lt)+
   apply simp
  apply(rule Un_least_lt)+
   apply (simp, simp)
  apply(rule ltI, simp, simp)
  done

lemma sats_is_Fn_perm_elem_fm_iff : 
  fixes env i j k f a v
  assumes "env \<in> list(M)" "i < length(env)" "j < length(env)" "k < length(env)"
          "nth(i, env) = f" "nth(j, env) = a" "nth(k, env) = v" 
  shows "sats(M, is_Fn_perm_elem_fm(i, j, k), env) \<longleftrightarrow> (\<exists>n m l. <<n, m>, l> = a \<and> v = <<f`n, m>, l>)" 
  unfolding is_Fn_perm_elem_fm_def 
  using assms pair_in_M_iff nth_type lt_nat_in_nat  
  apply clarsimp
  apply(rule iffI, clarsimp, clarsimp)
  apply(rename_tac n m l, subgoal_tac "n \<in> M \<and> m \<in> M \<and> l \<in> M")
  apply(rename_tac n m l, rule_tac x="<f`n, m>" in bexI)
   apply(rename_tac n m l, rule_tac x="f`n" in bexI)
    apply(rename_tac n m l, rule_tac x="<n, m>" in bexI)
     apply(rename_tac n m l, rule_tac x="l" in bexI)
      apply(rename_tac n m l, rule_tac x="m" in bexI)
        apply(rename_tac n m l, rule_tac x="n" in bexI)
  using pair_in_M_iff apply_closed
         apply auto[7]
  apply(rename_tac n m l, subgoal_tac "(##M)(<n, m>) \<and> (##M)(l)")
  using pair_in_M_iff nth_type 
   apply force
  apply(rule iffD1, rule pair_in_M_iff)
  using nth_type 
  by auto

lemma Fn_perm_in_M : 
  fixes f p 
  assumes "f \<in> nat_perms" "p \<in> Fn" 
  shows "Fn_perm(f, p) \<in> M" 

proof - 
  define Q where "Q \<equiv> \<lambda>x y. \<exists>n m l. <<n, m>, l> = x \<and> y = <<f`n, m>, l>" 

  have "strong_replacement(##M, \<lambda>x y. sats(M, is_Fn_perm_elem_fm(2, 0, 1), [x, y] @ [f]))" (is ?A)
    apply(rule replacement_ax)
    apply(rule is_Fn_perm_elem_fm_type)
    using assms nat_perms_in_M transM
        apply auto[4]
    apply(rule le_trans, rule arity_is_Fn_perm_elem_fm)
    using Un_least_lt 
    by auto
  have "strong_replacement(##M, \<lambda>x y. Q(x, y))" 
    unfolding Q_def
    apply(rule_tac P="?A" in iffD1)
     apply(rule strong_replacement_cong)
     apply(rule sats_is_Fn_perm_elem_fm_iff)
    using assms \<open>?A\<close> Fn_in_M transM nat_perms_in_M
    by auto
  then have "\<exists>Y[##M]. \<forall>b[##M]. b \<in> Y \<longleftrightarrow> (\<exists>x[##M]. x \<in> p \<and> Q(x, b))"
    apply(rule strong_replacementD)
    using assms univalent_def Q_def Fn_in_M transM
    by auto
  then obtain Y where YH: "Y \<in> M" "\<And>b. b \<in> M \<Longrightarrow> b \<in> Y \<longleftrightarrow> (\<exists>x \<in> M. x \<in> p \<and> Q(x, b))" by auto

  have "Y = Fn_perm(f, p)"
  proof (rule equality_iffI, rule iffI)
    fix b 
    assume bin: "b \<in> Y" 
    then have "b \<in> M" using YH transM by auto
    then have "\<exists>x \<in> M. x \<in> p \<and> Q(x, b)" using YH bin by auto
    then obtain x where xH : "x \<in> M" "x \<in> p" "Q(x, b)" by auto
    then have "\<exists>n m l. <<n, m>, l> = x \<and> b = <<f`n, m>, l>" unfolding Q_def by auto
    then obtain n m l where H: "<<n, m>, l> = x" "b = <<f`n, m>, l>" by auto
    then show "b \<in> Fn_perm(f, p)"
      unfolding Fn_perm_def 
      apply clarsimp
      apply(rule_tac x="<<n, m>, l>" in bexI)
      using xH H
      by auto
  next 
    fix b 
    assume bin : "b \<in> Fn_perm(f, p)"
    then obtain n m l where H: "b = <<f`n, m>, l>" "<<n, m>, l> \<in> p" "n \<in> nat" "m \<in> nat" "l \<in> 2"  using Fn_permE assms by blast
    then have "Q(<<n, m>, l>, b)"
      unfolding Q_def 
      by auto
    then have "\<exists>x \<in> M. x \<in> p \<and> Q(x, b)" (is ?A)
      apply(rule_tac x="<<n, m>, l>" in bexI)
      using H 
       apply force
      apply(rule to_rin, rule pair_in_MI, rule conjI, rule pair_in_MI)
      using H nat_in_M zero_in_M succ_in_MI transM
      by auto
    have "<<f`n, m>, l> \<in> M" 
      apply(rule to_rin, rule pair_in_MI, rule conjI, rule pair_in_MI, rule conjI)
        apply(rule apply_closed)
      using H nat_in_M zero_in_M succ_in_MI transM assms nat_perms_in_M
      by auto
    then show "b \<in> Y" using YH \<open>?A\<close> H by auto
  qed

  then show ?thesis using YH by auto
qed

definition is_Fn_perm_fm where 
  "is_Fn_perm_fm(f, p, v) \<equiv> Forall(Iff(Member(0, v#+1), Exists(And(Member(0,p#+2),is_Fn_perm_elem_fm(f#+2, 0, 1)))))" 

lemma is_Fn_perm_fm_type : 
  fixes i j k 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" 
  shows "is_Fn_perm_fm(i, j, k) \<in> formula" 
  unfolding is_Fn_perm_fm_def
  apply(subgoal_tac "is_Fn_perm_elem_fm(i #+ 2, 0, 1) \<in> formula", force)
  using is_Fn_perm_elem_fm_type assms
  by force

lemma arity_is_Fn_perm_fm : 
  fixes i j k 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" 
  shows "arity(is_Fn_perm_fm(i, j, k)) \<le> succ(i) \<union> succ(j) \<union> succ(k)"
  unfolding is_Fn_perm_fm_def 
  using assms
  apply(subgoal_tac "is_Fn_perm_elem_fm(i #+ 2, 0, 1) \<in> formula")
  apply simp
   apply(rule pred_le, simp, simp)
   apply(rule Un_least_lt)+
     apply auto[1]
    apply simp
    apply(rule ltI, simp, simp)
   apply(rule pred_le, simp, simp)
   apply(rule Un_least_lt)+
     apply (simp, simp)
    apply(rule ltI, simp, simp)
   apply(rule le_trans, rule arity_is_Fn_perm_elem_fm)
      apply auto[3]
   apply(rule Un_least_lt)+
     apply simp
     apply(rule ltI, simp, simp, simp, simp)
  using is_Fn_perm_elem_fm_type assms
  by force

lemma sats_is_Fn_perm_fm_iff : 
  fixes env i j k f p v 
  assumes "env \<in> list(M)" "i < length(env)" "j < length(env)" "k < length(env)" 
          "f = nth(i, env)" "p = nth(j, env)" "v = nth(k, env)" 
          "p \<in> Fn" "f \<in> nat_perms"
  shows "sats(M, is_Fn_perm_fm(i, j, k), env) \<longleftrightarrow> v = Fn_perm(f, p)"
proof - 
  have I1:  "sats(M, is_Fn_perm_fm(i, j, k), env) \<longleftrightarrow> (\<forall>x \<in> M. (x \<in> v \<longleftrightarrow> (\<exists>a \<in> M. a \<in> p \<and> (\<exists>n m l. <<n, m>, l> = a \<and> x = <<f`n, m>, l>))))"
    unfolding is_Fn_perm_fm_def
    using assms lt_nat_in_nat
    apply simp
    apply(rule ball_iff, rule iff_iff, simp)
    apply(rule bex_iff, rule iff_conjI2, simp)
    apply(rule sats_is_Fn_perm_elem_fm_iff)
    by auto
  have I2: "... \<longleftrightarrow> (\<forall>x. x \<in> v \<longleftrightarrow> (\<exists>a \<in> M. a \<in> p \<and> (\<exists>n m l. <<n, m>, l> = a \<and> x = <<f`n, m>, l>)))"
    apply(rule iffI, rule allI, rule iffI)
    using assms nth_type lt_nat_in_nat transM
      apply force
    apply(rename_tac x, subgoal_tac "x \<in> M", force)
    using assms lt_nat_in_nat nth_type pair_in_M_iff apply_closed
    by auto
  have I3: "... \<longleftrightarrow> (\<forall>x. x \<in> v \<longleftrightarrow> (\<exists>a. a \<in> p \<and> (\<exists>n m l. <<n, m>, l> = a \<and> x = <<f`n, m>, l>)))"  
    apply(rule all_iff, rule iff_iff, simp, rule iffI, force, clarify)
    using assms nth_type lt_nat_in_nat transM 
    apply force
    done 
  have I4: "... \<longleftrightarrow> v = Fn_perm(f, p)"
    apply(rule iffI, rule equality_iffI, rule iffI)
    using Fn_perm_def
      apply force 
     apply(rename_tac x, subgoal_tac "\<exists>n \<in> nat. \<exists>m \<in> nat. \<exists>l \<in> 2. <<n, m>, l> \<in> p \<and> x = <<f`n, m>, l>", force)
     apply(rule Fn_permE)
    using assms
       apply auto[3]
    apply simp
    apply(rule allI, rule iffI)
     apply(rename_tac x, subgoal_tac "\<exists>n \<in> nat. \<exists>m \<in> nat. \<exists>l \<in> 2. <<n, m>, l> \<in> p \<and> x = <<f`n, m>, l>", force)
     apply(rule Fn_permE)
    using assms
       apply auto[3]
    using Fn_perm_def
    apply force 
    done
  show ?thesis using I1 I2 I3 I4 by auto
qed

definition is_Fn_perm'_elem_fm where 
  "is_Fn_perm'_elem_fm(f, p, v) \<equiv> Exists(And(is_Fn_perm_fm(f #+ 1, p #+ 1, 0), pair_fm(p #+ 1, 0, v #+ 1)))"

lemma is_Fn_perm'_elem_fm_type: 
  fixes i j k 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" 
  shows "is_Fn_perm'_elem_fm(i, j, k) \<in> formula" 
  unfolding is_Fn_perm'_elem_fm_def
  apply(subgoal_tac "is_Fn_perm_fm(i #+ 1, j #+ 1, 0) \<in> formula")
   apply force 
  using is_Fn_perm_fm_type assms
  by auto

lemma arity_is_Fn_perm'_elem_fm : 
  fixes i j k 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" 
  shows "arity(is_Fn_perm'_elem_fm(i, j, k)) \<le> succ(i) \<union> succ(j) \<union> succ(k)"

  unfolding is_Fn_perm'_elem_fm_def
  apply(subgoal_tac "is_Fn_perm_fm(succ(i), succ(j), 0) \<in> formula")
  using assms
  apply simp
   apply(rule pred_le, simp, simp)
   apply(rule Un_least_lt, rule le_trans, rule arity_is_Fn_perm_fm)
       apply auto[3]
    apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
   apply(subst arity_pair_fm)
  apply auto[3]
   apply simp
   apply(rule Un_least_lt, simp, rule ltI, simp, simp)
   apply(rule Un_least_lt, simp, simp, rule ltI, simp, simp)
  apply(rule is_Fn_perm_fm_type)
  using assms
  by auto

lemma sats_is_Fn_perm'_elem_fm_iff : 
  fixes env i j k f p v 
  assumes "env \<in> list(M)" "i < length(env)" "j < length(env)" "k < length(env)" 
          "f = nth(i, env)" "p = nth(j, env)" "v = nth(k, env)" 
          "p \<in> Fn" "f \<in> nat_perms"
  shows "sats(M, is_Fn_perm'_elem_fm(i, j, k), env) \<longleftrightarrow> v = <p, Fn_perm(f, p)>" 
proof - 
  have I1: "sats(M, is_Fn_perm'_elem_fm(i, j, k), env) \<longleftrightarrow> (\<exists>u \<in> M. u = Fn_perm(f, p) \<and> v = <p, u>)" 
    unfolding is_Fn_perm'_elem_fm_def
    apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
     apply(rule sats_is_Fn_perm_fm_iff)
    using assms nth_type lt_nat_in_nat
    by auto
  also have I2: "... \<longleftrightarrow> v = <p, Fn_perm(f, p)>"
    using Fn_perm_in_M assms
    by auto
  show ?thesis using I1 I2 by auto
qed

lemma Fn_perm'_subset : 
  fixes f 
  assumes "f \<in> nat_perms" 
  shows "Fn_perm'(f) \<subseteq> Fn \<times> (Pow((nat \<times> nat) \<times> 2) \<inter> M)" 
  unfolding Fn_perm'_def 
  apply (rule subsetI, clarsimp, rule conjI)
   apply(rule subsetI, rename_tac p x, subgoal_tac "\<exists>n \<in> nat. \<exists>m \<in> nat. \<exists>l \<in> 2. <<n, m>, l> \<in> p \<and> x = <<f`n, m>, l>")
    apply(clarify, rule function_value_in)
  using assms nat_perms_def bij_def inj_def 
     apply auto[2]
   apply(rule Fn_permE)
  using assms Fn_perm_in_M
  by auto

lemma Fn_perm'_in_M : 
  fixes f 
  assumes "f \<in> nat_perms" 
  shows "Fn_perm'(f) \<in> M" 
proof -    

  define X where "X \<equiv> { v \<in> Fn \<times> (Pow((nat \<times> nat) \<times> 2) \<inter> M). sats(M, Exists(And(Member(0, 2), is_Fn_perm'_elem_fm(3, 0, 1))), [v] @ [Fn, f]) }" 

  have "X \<in> M"
    apply(subgoal_tac "is_Fn_perm'_elem_fm(3, 0, 1) \<in> formula")
    unfolding X_def
    apply(rule separation_notation, rule separation_ax)
    using assms nat_perms_in_M transM Fn_in_M
        apply auto[2]
      apply simp
      apply(rule pred_le, simp, simp)
      apply(rule Un_least_lt)+
        apply auto[3]
      apply(rule le_trans, rule arity_is_Fn_perm'_elem_fm)
    using Un_least_lt
         apply auto[4]
     apply(rule to_rin, rule cartprod_closed, simp add:Fn_in_M, simp, rule M_powerset)
    using cartprod_closed nat_in_M zero_in_M succ_in_MI is_Fn_perm'_elem_fm_type
    by auto

  have "X = { v \<in> Fn \<times> (Pow((nat \<times> nat) \<times> 2) \<inter> M). \<exists>p \<in> M. p \<in> Fn \<and> v = <p, Fn_perm(f, p)> }"
    unfolding X_def 
    apply(rule iff_eq)
    apply(rule iff_trans, rule sats_Exists_iff)
    using Fn_in_M transM nat_perms_in_M assms pair_in_M_iff
     apply auto[1]
    apply(rule bex_iff, rule iff_trans, rule sats_And_iff)
    using Fn_in_M transM nat_perms_in_M assms pair_in_M_iff
     apply auto[1]
    apply(rule iff_conjI2)
    using Fn_in_M transM nat_perms_in_M assms pair_in_M_iff
     apply auto[1]
    apply(rule sats_is_Fn_perm'_elem_fm_iff)
    using Fn_in_M transM nat_perms_in_M assms pair_in_M_iff
    by auto

  also have "... = Fn_perm'(f)" 
    apply(rule equality_iffI, rule iffI)
    apply(subst Fn_perm'_def)
    using Fn_perm'_subset assms Fn_in_M transM 
    unfolding Fn_perm'_def
    by auto

  finally show ?thesis using \<open>X \<in> M\<close> by auto
qed

definition is_Fn_perm'_fm where
  "is_Fn_perm'_fm(f, fn, v) \<equiv> Forall(Iff(Member(0, v #+ 1), Exists(And(Member(0, fn#+2), is_Fn_perm'_elem_fm(f#+2, 0, 1)))))" 

lemma is_Fn_perm'_fm_type : 
  fixes i j k 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" 
  shows "is_Fn_perm'_fm(i, j, k) \<in> formula" 
  unfolding is_Fn_perm'_fm_def 
  apply(subgoal_tac "is_Fn_perm'_elem_fm(i #+ 2, 0, 1) \<in> formula")
  using assms
   apply force 
  apply(rule is_Fn_perm'_elem_fm_type)
  using assms
  by auto

lemma arity_is_Fn_perm'_fm : 
  fixes i j k 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" 
  shows "arity(is_Fn_perm'_fm(i, j, k)) \<le> succ(i) \<union> succ(j) \<union> succ(k)"

  unfolding is_Fn_perm'_fm_def
  apply(subgoal_tac "is_Fn_perm'_elem_fm(i #+ 2, 0, 1) \<in> formula")
  using assms
  apply simp
   apply(rule pred_le, simp, simp)
   apply(rule Un_least_lt)+
     apply (simp, simp)
    apply(rule ltI, simp, simp)
   apply(rule pred_le, simp, simp)
   apply(rule Un_least_lt)+
     apply (simp, simp)
    apply(rule ltI, simp, simp)
   apply(rule le_trans, rule arity_is_Fn_perm'_elem_fm)
  using assms
      apply auto[3]
   apply(rule Un_least_lt)+
     apply (simp, rule ltI, simp_all)
  apply(rule is_Fn_perm'_elem_fm_type)
  using assms
  by auto

lemma sats_is_Fn_perm'_fm_iff : 
  fixes env i j k f v 
  assumes "env \<in> list(M)" "i < length(env)" "j < length(env)" "k < length(env)" 
          "f = nth(i, env)" "Fn = nth(j, env)" "v = nth(k, env)" 
          "f \<in> nat_perms"
  shows "sats(M, is_Fn_perm'_fm(i, j, k), env) \<longleftrightarrow> v = Fn_perm'(f)"
proof - 
  have I1: "sats(M, is_Fn_perm'_fm(i, j, k), env) \<longleftrightarrow> (\<forall>x \<in> M. x \<in> v \<longleftrightarrow> (\<exists>p \<in> M. p \<in> Fn \<and> x = <p, Fn_perm(f, p)>))" 
    unfolding is_Fn_perm'_fm_def 
    apply(rule iff_trans, rule sats_Forall_iff, simp add:assms, rule ball_iff)
    apply(rule iff_trans, rule sats_Iff_iff, simp add:assms, rule iff_iff)
    using assms lt_nat_in_nat nth_type
     apply simp
    apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
    using assms lt_nat_in_nat nth_type
     apply auto[1]
    apply(rule sats_is_Fn_perm'_elem_fm_iff)
    using assms lt_nat_in_nat nth_type
    by auto
  have I2: "... \<longleftrightarrow> (\<forall>x. x \<in> v \<longleftrightarrow> (\<exists>p \<in> M. p \<in> Fn \<and> x = <p, Fn_perm(f, p)>))" 
    apply(rule iffI, rule allI, rule iffI)
    using assms lt_nat_in_nat nth_type transM
      apply force 
     apply (rename_tac x, subgoal_tac "x \<in> M", force)
     apply clarsimp
    using Fn_in_M Fn_perm_in_M assms pair_in_M_iff
    by auto
  have I3: "... \<longleftrightarrow> (\<forall>x. x \<in> v \<longleftrightarrow> (\<exists>p \<in> Fn. x = <p, Fn_perm(f, p)>))" 
    using Fn_in_M transM 
    by force 
  have I4: "... \<longleftrightarrow> v = Fn_perm'(f)" 
    unfolding Fn_perm'_def 
    by auto
  show ?thesis
    using I1 I2 I3 I4 
    by auto 
qed

lemma Fn_perms_in_M : "Fn_perms \<in> M" 
proof - 
  have "univalent(##M, nat_perms, \<lambda>x b. b = Fn_perm'(x))" (is ?B)
    unfolding univalent_def 
    by auto
  have "univalent(##M, nat_perms, \<lambda>x b. (M, [x, b] @ [Fn] \<Turnstile> is_Fn_perm'_fm(0, 2, 1)))" (is ?C)
    apply(rule_tac Q="?B" in iffD2)
     apply(rule univalent_cong, simp)
     apply(rule sats_is_Fn_perm'_fm_iff)
    using Fn_in_M \<open>?B\<close>
    by auto

  have "strong_replacement(##M, \<lambda>x y. sats(M, is_Fn_perm'_fm(0, 2, 1), [x, y] @ [Fn]))"
    apply(rule replacement_ax)
      apply(rule is_Fn_perm'_fm_type)
    using Fn_in_M
        apply auto[4]
    apply(rule le_trans, rule arity_is_Fn_perm'_fm)
    using Un_least_lt
    by auto

  then have "\<exists>Y[##M]. \<forall>b[##M]. b \<in> Y \<longleftrightarrow> (\<exists>x[##M]. x \<in> nat_perms \<and> sats(M, is_Fn_perm'_fm(0, 2, 1), [x, b] @ [Fn]))" 
    apply(rule strong_replacementD)
    using nat_perms_in_M \<open>?C\<close>
    by auto
  then obtain Y where YH: "Y \<in> M" "\<And>b. b \<in> M \<Longrightarrow> b \<in> Y \<longleftrightarrow> (\<exists>f \<in> M. f \<in> nat_perms \<and> sats(M, is_Fn_perm'_fm(0, 2, 1), [f, b] @ [Fn]))"
    by auto
  have "\<And>b. b \<in> M \<Longrightarrow> b \<in> Y \<longleftrightarrow> (\<exists>f \<in> M. f \<in> nat_perms \<and> b = Fn_perm'(f))"
    apply(rename_tac b, rule_tac Q="(\<exists>f \<in> M. f \<in> nat_perms \<and> sats(M, is_Fn_perm'_fm(0, 2, 1), [f, b] @ [Fn]))" in iff_trans)
    using YH 
     apply force 
    apply(rule bex_iff, rule iff_conjI2, simp)
    apply(rule sats_is_Fn_perm'_fm_iff)
    using Fn_in_M 
    by auto
  then have "\<And>b. b \<in> Y \<longleftrightarrow> (\<exists>f. f \<in> nat_perms \<and> b = Fn_perm'(f))"
    apply(rule_tac iffI)
    using YH transM 
     apply force 
    apply(rule exE, assumption)
    apply(rename_tac b f, subgoal_tac "f \<in> M \<and> b \<in> M", force)
    using nat_perms_in_M Fn_perm'_in_M transM pair_in_M_iff
    by auto 
  then have "Y = Fn_perms" 
    unfolding Fn_perms_def
    by auto
  then show ?thesis using YH by auto
qed 

end
end