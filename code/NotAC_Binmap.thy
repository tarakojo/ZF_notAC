theory NotAC_Binmap
  imports Fn_Perm_Filter HS_Forces
begin 

context M_ctm begin 

interpretation M_symmetric_system "Fn" "Fn_leq" "0" "M" "enum" "Fn_perms" "Fn_perms_filter"
  using Fn_M_symmetric_system by auto

definition binmap_row' where "binmap_row'(n) \<equiv> { x \<in> domain(check(nat)) \<times> Fn. \<exists>F \<in> Fn. \<exists>m \<in> nat. x = <check(m), F> \<and> F`<n, m> = 1 }" 
definition binmap_row where "binmap_row(G, n) \<equiv> { m \<in> nat. \<exists>p \<in> G. p`<n, m> = 1 }" 
definition binmap' where "binmap' \<equiv> { binmap_row'(n). n \<in> nat } \<times> { 0 }" 
definition binmap where "binmap(G) \<equiv> { binmap_row(G, n). n \<in> nat }" 


lemma binmap_row'_eq : 
  fixes n f 
  assumes "n \<in> nat" "f \<in> nat_perms" 
  shows "binmap_row'(n) = { <check(m), F>.. <m, F> \<in> nat \<times> Fn, F`<n, m> = 1 }" (is "_ = ?A")

proof(rule equality_iffI, rule iffI)
  fix v
  assume vin : "v \<in> binmap_row'(n)" 
  then obtain m F where "v = <check(m), F>" "m \<in> nat" "F \<in> Fn" "F`<n, m> = 1" 
    using binmap_row'_def 
    by force 
  then show "v \<in> ?A" 
    by auto
next 
  fix v 
  assume vin : "v \<in> { <check(m), F>.. <m, F> \<in> nat \<times> Fn, F`<n, m> = 1 }" 
  then obtain m F where mFH: "v = <check(m), F>" "m \<in> nat" "F \<in> Fn" "F`<n, m> = 1" 
    using binmap_row'_def 
    by force 
  then have "check(m) \<in> domain(check(nat))" 
    by(subst (2) def_check, force)
  then show "v \<in> binmap_row'(n)" 
    using binmap_row'_def mFH 
    by force 
qed

definition binmap_row'_member_fm where 
  "binmap_row'_member_fm(x, n, fn, N) \<equiv> 
    Exists(Exists(Exists(Exists(Exists(Exists(
      And(empty_fm(0), 
      And(Member(1, fn #+ 6), 
      And(Member(2, N #+ 6), 
      And(check_fm(2, 0, 3), 
      And(pair_fm(3, 1, x#+6), 
      And(pair_fm(n#+6, 2, 4), 
      And(fun_apply_fm(1, 4, 5), 
          is_1_fm(5))))))))))))))" 

lemma binmap_row'_member_fm_type : 
  fixes i j k l 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" "l \<in> nat" 
  shows "binmap_row'_member_fm(i, j, k, l) \<in> formula" 
  
  apply(subst binmap_row'_member_fm_def)
  apply(subgoal_tac "check_fm(2, 0, 3) \<in> formula \<and> is_1_fm(5) \<in> formula", force)
  apply(rule conjI, rule check_fm_type)
     apply auto[3]
  apply(rule is_1_fm_type, force)
  done

lemma arity_binmap_row'_member_fm : 
  fixes i j k l 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" "l \<in> nat" 
  shows "arity(binmap_row'_member_fm(i, j, k, l)) \<le> succ(i) \<union> succ(j) \<union> succ(k) \<union> succ(l)" 

  unfolding binmap_row'_member_fm_def check_fm_def rcheck_fm_def
   apply simp
   apply(subst arity_tran_closure_fm, simp, simp)
  apply(subst arity_Memrel_fm, simp, simp)
   apply(subst arity_empty_fm, simp)
   apply(subst arity_singleton_fm, simp, simp)
   apply(subst arity_is_eclose_fm, simp, simp)
   apply(subst arity_is_wfrec_fm [where i=7], simp, simp, simp, simp, simp)
  unfolding is_Hcheck_fm_def Replace_fm_def PHcheck_fm_def
    apply simp
   apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  unfolding is_1_fm_def
  apply simp
  apply(subst arity_empty_fm, simp add:assms)
  apply(subst arity_fun_apply_fm, simp, simp, simp)
  apply(insert assms)
  apply(rule pred_le, simp, simp)+ 
  apply(subst succ_Un_distrib, simp, simp)+
  apply(rule Un_least_lt, rule Un_upper2_lt, simp, simp)
  apply(rule Un_least_lt)+
    apply(rule Un_upper2_lt, simp, simp)
   apply(rule Un_upper1_lt, rule Un_upper2_lt, simp, simp, simp)
  apply(rule Un_least_lt)+
    apply(rule Un_upper2_lt, simp, simp)+
  apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  using le_trans 
   apply force
  done

lemma sats_binmap_row'_member_fm_iff : 
  fixes i j k l x n env
  assumes "i < length(env)" "j < length(env)" "k < length(env)" "l < length(env)" 
          "x = nth(i, env)" "n = nth(j, env)" "Fn = nth(k, env)" "nat = nth(l, env)" 
          "env \<in> list(M)"
  shows "sats(M, binmap_row'_member_fm(i, j, k, l), env) \<longleftrightarrow> (\<exists>F \<in> Fn. \<exists>m \<in> nat. x = <check(m), F> \<and> F`<n, m> = 1)" 

  unfolding binmap_row'_member_fm_def 
  apply(rule_tac Q="\<exists>Fnm \<in> M. \<exists>nm \<in> M. \<exists>checkm \<in> M. \<exists>m \<in> M. \<exists>F \<in> M. \<exists>zero \<in> M. 
                    zero = 0 \<and> F \<in> Fn \<and> m \<in> nat \<and> checkm = check(m) \<and> x = <checkm, F> \<and> nm = <n, m> \<and> F`nm = Fnm \<and> Fnm = 1" in iff_trans)
   apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)+
   apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
    apply(rule iff_trans, rule sats_empty_fm, force, simp add:assms, force)
   apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
  using assms lt_nat_in_nat length_type 
    apply force
   apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
  using assms lt_nat_in_nat length_type 
    apply force
   apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
    apply(rule iff_trans, rule sats_check_fm)
  using assms check_abs
           apply auto[8]
   apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
  using assms lt_nat_in_nat length_type 
    apply force
   apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
  using assms lt_nat_in_nat length_type 
    apply force
   apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
  using assms lt_nat_in_nat length_type 
    apply force
   apply(rule iff_trans, rule sats_is_1_fm_iff)
  using assms lt_nat_in_nat length_type zero_in_M transM 
      apply auto[4]
  apply(rule iffI, force, clarsimp)
  apply(rule conjI, simp add:zero_in_M)
  apply(rule conjI)
  using Fn_in_M transM 
   apply force
  apply(rename_tac F m, rule_tac x="F`<n, m>" in bexI)
   apply(rename_tac F m, rule_tac x="<n, m>" in bexI)
    apply(rename_tac F m, rule_tac x="check(m)" in bexI)
     apply(rename_tac F m, rule_tac x=m in bexI, force)
  using nat_in_M transM check_in_M pair_in_M_iff assms lt_nat_in_nat nth_type apply_closed
  by auto

lemma binmap_row'_in_M : 
  fixes n 
  assumes "n \<in> nat" 
  shows "binmap_row'(n) \<in> M" 
proof - 
  define X where "X \<equiv> { x \<in> domain(check(nat)) \<times> Fn. sats(M, binmap_row'_member_fm(0, 1, 2, 3), [x] @ [n, Fn, nat]) }" 

  have "X \<in> M" 
    unfolding X_def 
    apply(rule separation_notation)
     apply(rule separation_ax)
       apply(subst binmap_row'_member_fm_def)
       apply(subgoal_tac "check_fm(2, 0, 3) \<in> formula \<and> is_1_fm(5) \<in> formula", force)
       apply(rule conjI, rule check_fm_type)
          apply auto[3]
       apply(rule is_1_fm_type, force)
    using assms nat_in_M transM Fn_in_M 
      apply force 
     apply(rule le_trans, rule arity_binmap_row'_member_fm)
         apply auto[4]
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    using domain_closed check_in_M nat_in_M Fn_in_M cartprod_closed
    by auto

  have "X = binmap_row'(n)" 
    unfolding X_def binmap_row'_def 
    apply(rule iff_eq)
    apply(rule sats_binmap_row'_member_fm_iff)
    using assms Fn_in_M nat_in_M pair_in_M_iff transM check_in_M
            apply (auto, blast)
    done

  then show ?thesis using \<open>X \<in> M\<close> by auto
qed 

definition is_binmap_row'_fm where 
  "is_binmap_row'_fm(y, n, checknatdom, fn, N) \<equiv>
    Forall(Iff(Member(0, y#+1), 
      And(Exists(And(cartprod_fm(checknatdom#+2, fn#+2, 0), Member(1, 0))),  
      binmap_row'_member_fm(0, n#+1, fn#+1, N#+1))))"  

lemma is_binmap_row'_fm_type : 
  fixes i j k l m 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" "l \<in> nat" "m \<in> nat" 
  shows "is_binmap_row'_fm(i, j, k, l, m) \<in> formula"
  unfolding is_binmap_row'_fm_def
  using assms
  apply simp
  apply(subgoal_tac "binmap_row'_member_fm(0, succ(j), succ(l), succ(m)) \<in> formula", force)
  apply(rule binmap_row'_member_fm_type)
  by auto

lemma arity_is_binmap_row'_fm : 
  fixes i j k l m 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" "l \<in> nat" "m \<in> nat" 
  shows "arity(is_binmap_row'_fm(i, j, k, l, m)) \<le> succ(i) \<union> succ(j) \<union> succ(k) \<union> succ(l) \<union> succ(m)" 
  unfolding is_binmap_row'_fm_def
  apply simp
  apply(insert assms binmap_row'_member_fm_type [of 0 "succ(j)" "succ(l)" "succ(m)"])
  apply(rule pred_le, simp, simp)
  apply(rule Un_least_lt)+
    apply auto[1]
   apply(subst succ_Un_distrib, simp, simp)+
   apply(rule Un_upper1_lt)+
       apply auto[5]
  apply(rule Un_least_lt)+
  apply(subst arity_cartprod_fm, simp, simp, simp)
   apply(rule pred_le, simp, simp)
   apply(rule Un_least_lt)+
      apply(subst succ_Un_distrib, simp, simp)+
      apply(rule Un_upper1_lt, rule Un_upper1_lt, rule Un_upper2_lt, simp, simp, simp, simp)
      apply(subst succ_Un_distrib, simp, simp)+
     apply(rule Un_upper1_lt, rule Un_upper2_lt, simp, simp, simp, simp)
   apply(rule Un_least_lt, simp, simp)
  apply(rule le_trans, rule arity_binmap_row'_member_fm)
      apply auto[4]
  apply(rule Un_least_lt)+
     apply simp
    apply simp
    apply(rule ltI, simp, simp, simp, rule ltI, simp, simp)
  apply(simp, rule ltI, simp, simp)
  done

lemma sats_is_binmap_row'_fm : 
  fixes i j k l m y n env 
  assumes "i < length(env)" "j < length(env)" "k < length(env)" "l < length(env)" "m < length(env)"
          "nth(i, env) = y" "nth(j, env) = n" "nth(k, env) = domain(check(nat))" "nth(l, env) = Fn" "nth(m, env) = nat" 
          "env \<in> list(M)" "n \<in> nat" 
  shows "sats(M, is_binmap_row'_fm(i, j, k, l, m), env) \<longleftrightarrow> y = binmap_row'(n)" 

  apply(rule_tac Q="\<forall>v \<in> M. v \<in> y \<longleftrightarrow> ((\<exists>A \<in> M. A = domain(check(nat)) \<times> Fn \<and> v \<in> A) \<and> (\<exists>F \<in> Fn. \<exists>m \<in> nat. v = <check(m), F> \<and> F`<n, m> = 1))" in iff_trans)
  unfolding is_binmap_row'_fm_def
   apply(rule iff_trans, rule sats_Forall_iff, simp add:assms, rule ball_iff)
   apply(rule iff_trans, rule sats_Iff_iff, simp add:assms, rule iff_iff)
  using lt_nat_in_nat length_type assms
    apply force 
   apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI)
    apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)
    apply(rule iff_trans, rule sats_And_iff, simp add:assms)
    apply(rule iff_conjI2, rule iff_trans, rule sats_cartprod_fm)
  using lt_nat_in_nat length_type assms nth_type
         apply auto[4]
     apply(rule iff_trans, rule cartprod_abs)
        apply simp
        apply(rule nth_type)
  using lt_nat_in_nat length_type assms nth_type
         apply auto[2]
        apply simp
        apply(rule nth_type)
  using lt_nat_in_nat length_type assms nth_type
        apply auto[5]
   apply(rule sats_binmap_row'_member_fm_iff)
  using lt_nat_in_nat length_type assms nth_type
           apply auto[9]
  apply(rule_tac Q="\<forall>v \<in> M. v \<in> y \<longleftrightarrow> v \<in> binmap_row'(n)" in iff_trans)
   apply(rule ball_iff, rule iff_iff, simp)
   apply(simp add: binmap_row'_def)
   apply (rule iffI, force, simp)
  using cartprod_closed domain_closed check_in_M nat_in_M Fn_in_M 
   apply force 
  apply(rule iffI, rule equality_iffI, rule iffI)
    apply(rename_tac x, subgoal_tac "x \<in> M", force)
  using lt_nat_in_nat transM nth_type length_type assms 
    apply force
   apply(rename_tac x, subgoal_tac "x \<in> M", force)
  using lt_nat_in_nat transM nth_type length_type assms binmap_row'_in_M
   apply force
  by auto

lemma binmap'_in_M : "binmap' \<in> M" 
proof - 
  define X where "X \<equiv> { x \<in> Pow(domain(check(nat)) \<times> Fn) \<inter> M. \<exists>n \<in> M. n \<in> nat \<and> x = binmap_row'(n) }" 

  have "X = { x \<in> Pow(domain(check(nat)) \<times> Fn) \<inter> M. sats(M, Exists(And(Member(0, 4), is_binmap_row'_fm(1,0,2,3,4))), [x] @ [domain(check(nat)), Fn, nat]) }"
    (is "_ = ?A")
    
    unfolding X_def
    apply(rule iff_eq, rule iff_flip)
    apply(rule iff_trans, rule sats_Exists_iff)
    using domain_closed check_in_M nat_in_M Fn_in_M transM
     apply force
    apply(rule bex_iff, rule iff_trans, rule sats_And_iff)
    using domain_closed check_in_M nat_in_M Fn_in_M transM
     apply force
    apply(rule iff_conjI2)
    using domain_closed check_in_M nat_in_M Fn_in_M transM
     apply force
    apply(rule sats_is_binmap_row'_fm)
    using domain_closed check_in_M nat_in_M Fn_in_M transM
    by auto
  
  have "?A \<in> M" 
    apply(rule separation_notation)
     apply(rule separation_ax)
       apply(insert is_binmap_row'_fm_type [of 1 0 2 3 4], force)
    using domain_closed check_in_M nat_in_M Fn_in_M transM
      apply force
     apply simp
    apply(rule pred_le, simp, simp)
     apply(rule Un_least_lt)+
       apply auto[2]
     apply(rule le_trans, rule arity_is_binmap_row'_fm)
          apply auto[5]
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    apply(rule M_powerset)
    using domain_closed check_in_M nat_in_M Fn_in_M transM cartprod_closed
    by auto

  then have "X \<in> M" using \<open>X = ?A\<close> by auto

  have "X = { binmap_row'(n). n \<in> nat }" (is "_ = ?B")
    unfolding X_def 
    apply(rule equality_iffI, rule iffI, force, clarsimp)
    apply(rule conjI, simp add:binmap_row'_def, force)
    apply(rule conjI, rule binmap_row'_in_M, simp)
    using nat_in_M transM 
    by auto

  then have "?B \<in> M" using \<open>X \<in> M\<close> by auto
  then have "?B \<times> { 0 } \<in> M" using singleton_in_M_iff one_in_M cartprod_closed by auto
  then show ?thesis 
    using binmap'_def
    by auto
qed

lemma binmap_row'_P_name : 
  fixes n 
  assumes "n \<in> nat"  
  shows "binmap_row'(n) \<in> P_names" 

  apply(rule iffD2, rule P_name_iff, rule conjI)
   apply(rule binmap_row'_in_M, simp add:assms)
  unfolding binmap_row'_def 
  using check_P_name nat_in_M P_name_domain_P_name
  by auto    

lemma binmap_row'_pauto : 
  fixes n f 
  assumes "n \<in> nat" "f \<in> nat_perms" 
  shows "Pn_auto(Fn_perm'(f))`binmap_row'(n) = binmap_row'(f`n)" (is "?A = ?B")
proof - 

  have H: "\<And>p m. p \<in> Fn \<Longrightarrow> m \<in> nat \<Longrightarrow> <n, m> \<in> domain(p) \<Longrightarrow> p`<n, m> = 1 \<longleftrightarrow> (Fn_perm'(f)`p)`<f`n, m> = 1" 
  proof - 
    fix p m 
    assume assms1: "p \<in> Fn" "m \<in> nat" "<n, m> \<in> domain(p)" 

    then obtain l where "<<n, m>, l> \<in> p" by auto
    then have "<<f`n, m>, l> \<in> Fn_perm(f, p)" 
      unfolding Fn_perm_def 
      by force 
    then have domin:  "<f`n, m> \<in> domain(Fn_perm(f, p))" by auto

    have "p`<n, m> = 1 \<longleftrightarrow> <<n, m>, 1> \<in> p" 
      apply(rule iffI)
      apply(rule_tac b=1 and a="p`<n,m>" in ssubst, simp)
       apply(rule function_apply_Pair)
      using assms1 Fn_def 
        apply auto[2]
      apply(rule function_apply_equality)
      using assms1 Fn_def 
       apply auto[2]
      done
    also have "... \<longleftrightarrow> <<f`n, m>, 1> \<in> Fn_perm(f, p)" 
    proof(rule iffI)
      assume "\<langle>\<langle>n, m\<rangle>, 1\<rangle> \<in> p" 
      then show "\<langle>\<langle>f ` n, m\<rangle>, 1\<rangle> \<in> Fn_perm(f, p)" 
        unfolding Fn_perm_def 
        by force 
    next 
      assume "\<langle>\<langle>f ` n, m\<rangle>, 1\<rangle> \<in> Fn_perm(f, p)" 
      then have "\<exists>n'\<in>nat. \<exists>m'\<in>nat. \<exists>l \<in> 2. \<langle>\<langle>n', m'\<rangle>, l\<rangle> \<in> p \<and> \<langle>\<langle>f ` n, m\<rangle>, 1\<rangle> = \<langle>\<langle>f ` n', m'\<rangle>, l\<rangle>" 
        apply(rule_tac Fn_permE)
        using assms1 assms 
        by auto
      then obtain n' where H: "n' \<in> nat" "\<langle>\<langle>n', m\<rangle>, 1\<rangle> \<in> p" "\<langle>\<langle>f ` n, m\<rangle>, 1\<rangle> = \<langle>\<langle>f ` n', m\<rangle>, 1\<rangle>" 
        by force 
      then have "f`n = f`n'" by auto 
      then have "n = n'" using assms nat_perms_def bij_def inj_def H by force
      then show "\<langle>\<langle>n, m\<rangle>, 1\<rangle> \<in> p" using H by auto
    qed
    also have "... \<longleftrightarrow> Fn_perm(f, p)`<f`n, m> = 1" 
      apply(rule iffI, rule function_apply_equality, simp)
       apply(rule function_Fn_perm)
      using assms1 assms
        apply auto[2]
      apply(rule_tac b=1 and a="Fn_perm(f, p) ` \<langle>f ` n, m\<rangle>" in ssubst, simp)
      apply(rule function_apply_Pair)
       apply(rule function_Fn_perm)
      using assms1 assms domin
        apply auto[3]
      done
    also have "... \<longleftrightarrow> Fn_perm'(f) ` p ` \<langle>f ` n, m\<rangle> = 1"  
      apply(subst Fn_perm'_eq)
      using assms assms1
      by auto
    finally show "p ` \<langle>n, m\<rangle> = 1 \<longleftrightarrow> Fn_perm'(f) ` p ` \<langle>f ` n, m\<rangle> = 1" by simp
  qed

  have apply_not0_indom : "\<And>f x. function(f) \<Longrightarrow> f`x \<noteq> 0 \<Longrightarrow> x \<in> domain(f)" 
    apply(rule ccontr)
    apply(rename_tac f x, subgoal_tac "f`x = 0", simp)
    apply(rule apply_0)
    by auto

  have indom : "\<And>m p. m \<in> nat \<Longrightarrow> Fn_perm'(f) ` p \<in> Fn \<Longrightarrow> Fn_perm'(f) ` p ` \<langle>f ` n, m\<rangle> = 1 \<Longrightarrow> p \<in> Fn \<Longrightarrow> \<langle>n, m\<rangle> \<in> domain(p)"
  proof - 
    fix m p 
    assume assms1 : "m \<in> nat" "Fn_perm'(f) ` p \<in> Fn" "Fn_perm'(f) ` p ` \<langle>f ` n, m\<rangle> = 1" "p \<in> Fn" 
    have "\<langle>f ` n, m\<rangle> \<in> domain(Fn_perm'(f) ` p)" 
      apply(rule apply_not0_indom)
       apply(subgoal_tac "Fn_perm'(f) ` p \<in> Fn")
      using Fn_def 
        apply force
      apply(rule function_value_in, rule Fn_perm'_type)
      using assms assms1 
      by auto
    then obtain l where "<<f`n, m>, l> \<in> Fn_perm'(f) ` p" by auto
    then have "<<f`n, m>, l> \<in> Fn_perm(f, p)" 
      using Fn_perm'_eq assms assms1
      by auto 
    then have "\<exists>n'\<in>nat. \<exists>m'\<in>nat. \<exists>l' \<in> 2. \<langle>\<langle>n', m'\<rangle>, l'\<rangle> \<in> p \<and> \<langle>\<langle>f ` n, m\<rangle>, l\<rangle> = \<langle>\<langle>f ` n', m'\<rangle>, l'\<rangle>" 
        apply(rule_tac Fn_permE)
        using assms1 assms 
        by auto
    then obtain n' where n'H : "f`n = f`n'" "n' \<in> nat" "<<n', m>, l> \<in> p" by auto
    then have "n = n'" using assms nat_perms_def bij_def inj_def by auto
    then show "<n, m> \<in> domain(p)" using n'H by auto
  qed
     
  have "?A = { <Pn_auto(Fn_perm'(f))`y, Fn_perm'(f) ` p> . <y, p> \<in> binmap_row'(n) }" 
    apply(subst Pn_auto, rule binmap_row'_P_name)
    using assms
    by auto
  also have "... = { <Pn_auto(Fn_perm'(f))`y, Fn_perm'(f) ` p> . <y, p> \<in> { <check(m), F>.. <m, F> \<in> nat \<times> Fn, F`<n, m> = 1 } }" 
    apply(subst binmap_row'_eq)
    using assms
    by auto
  also have "... = { <Pn_auto(Fn_perm'(f))`check(m), Fn_perm'(f) ` p>.. <m, p> \<in> nat \<times> Fn, p`<n, m> = 1 }" 
    by(rule equality_iffI, rule iffI, force, force) 
  also have "... = { <check(m), Fn_perm'(f) ` p>.. <m, p> \<in> nat \<times> Fn, p`<n, m> = 1 }" 
    apply(rule equality_iffI, rule iffI, clarsimp)
     apply(rename_tac m F, rule_tac x=m in bexI)
      apply(subst check_fixpoint, rule Fn_perm'_is_P_auto)
    using assms P_auto_def nat_in_M transM 
        apply auto[4]
    apply clarsimp
     apply(rename_tac m F, rule_tac x=m in bexI)
      apply(subst check_fixpoint, rule Fn_perm'_is_P_auto)
    using assms P_auto_def nat_in_M transM 
    by auto 
  also have "... = { <check(m), p>.. <m, p> \<in> nat \<times> Fn, p`<f`n, m> = 1 }" 
    apply(rule equality_iffI, rule iffI, clarsimp)
     apply(rename_tac m p, rule_tac x=m in bexI)
      apply(rule conjI, simp, rule conjI)
       apply(rule function_value_in, rule Fn_perm'_type, simp add:assms, simp)
      apply(rule iffD1, rule H, simp, simp)
       apply(rule apply_not0_indom)
    using Fn_def 
        apply auto[4]
    apply clarsimp
    apply(rename_tac m p, rule_tac x=m in bexI, rule conjI, simp)
     apply(rename_tac m p, subgoal_tac "\<exists>y\<in>Fn. p = Fn_perm'(f) ` y", clarsimp)
      apply(rename_tac m p, rule_tac x=p in bexI, rule conjI, simp)
       apply(rule iffD2, rule H)
          apply auto[2]
        apply(subgoal_tac "\<langle>f ` n, m\<rangle> \<in> domain(Fn_perm'(f) ` p)")
         apply(rule indom)
            apply auto[4]
        apply(rule apply_not0_indom)
         apply(subgoal_tac "Fn_perm'(f) ` p \<in> Fn")
    using Fn_def
          apply auto[5]
    using Fn_perm'_bij assms bij_is_surj surj_def
     apply force
    by auto
  also have "... = binmap_row'(f`n)" 
    unfolding binmap_row'_def
    apply(rule equality_iffI, rule iffI)
     apply clarsimp
     apply(rule conjI)
      apply(subst (2) def_check, force)
     apply force
    apply force
    done
  finally show ?thesis by simp
qed

lemma binmap_row'_symmetric : 
  fixes n 
  assumes "n \<in> nat" 
  shows "symmetric(binmap_row'(n))" 
proof - 
  have H: "Fix({n}) \<subseteq> sym(binmap_row'(n))" 
  proof(rule subsetI)
    fix F assume Fin : "F \<in> Fix({n})" 
    then obtain f where fH: "Fn_perm'(f) = F" "f \<in> nat_perms" "f`n = n" 
      unfolding Fix_def 
      by force
    have "Pn_auto(Fn_perm'(f))`binmap_row'(n) = binmap_row'(f`n)" 
      apply(rule binmap_row'_pauto)
      using fH assms 
      by auto
    also have "... = binmap_row'(n)" using fH by auto
    finally show "F \<in> sym(binmap_row'(n))" 
      unfolding sym_def 
      using fH Fn_perms_def assms
      by auto
  qed

  show ?thesis 
    unfolding symmetric_def 
    unfolding Fn_perms_filter_def
    apply simp
    apply(rule conjI, rule sym_P_auto_subgroup)
     apply(rule binmap_row'_P_name, simp add:assms)
    apply(rule_tac x="{n}" in bexI, rule conjI)
    unfolding finite_M_def 
      apply(rule_tac x=1 in bexI, rule_tac a="{<n, 0>}" in not_emptyI, simp, rule conjI)
    unfolding inj_def 
        apply simp
        apply(rule Pi_memberI)
    using relation_def function_def range_def nat_in_M transM assms pair_in_M_iff singleton_in_M_iff H
    by auto
qed
    
lemma binmap_row'_HS : 
  fixes n 
  assumes "n \<in> nat" 
  shows "binmap_row'(n) \<in> HS" 
  apply(rule iffD2, rule HS_iff, rule conjI)
   apply(rule iffD2, rule P_name_iff, rule conjI)
    apply(rule binmap_row'_in_M, simp add:assms)
   apply(simp add: binmap_row'_def)
   apply(subgoal_tac "domain(check(nat)) \<subseteq> P_names", force)
  using check_P_name nat_in_M P_name_domain_P_name'
   apply force
  apply(rule conjI, simp add: binmap_row'_def)
  using check_in_HS nat_in_M HS_iff 
   apply blast
  apply(rule binmap_row'_symmetric)
  using assms
  by auto

lemma binmap'_in_P_name : 
  shows "binmap' \<in> P_names" 

  apply(rule iffD2, rule P_name_iff, rule conjI)
   apply(rule binmap'_in_M)
  unfolding binmap'_def 
  using zero_in_Fn binmap_row'_P_name 
  by auto

lemma pauto_0 : 
  fixes F 
  assumes "F \<in> Fn_perms" 
  shows "F`0 = 0" 
  apply(rule P_auto_preserves_one)
  using Fn_perm'_is_P_auto Fn_perms_def assms
  by force

lemma binmap'_pnauto : 
  fixes F 
  assumes "F \<in> Fn_perms" 
  shows "Pn_auto(F)`binmap' = binmap'" 
proof(rule equality_iffI, rule iffI)
  fix v 
  assume vin : "v \<in> Pn_auto(F) ` binmap'"

  obtain f where fH: "F = Fn_perm'(f)" "f \<in> nat_perms" using assms Fn_perms_def by force

  have "Pn_auto(F)`binmap' = { <Pn_auto(F)`y, F`p>. <y, p> \<in> binmap' }" 
    by(rule Pn_auto, rule binmap'_in_P_name)
  then have "v \<in> { <Pn_auto(F)`y, F`p>. <y, p> \<in> binmap' }" 
    using vin 
    by auto
  then have "\<exists>y p. <y, p> \<in> binmap' \<and> v = <Pn_auto(F)`y, F`p>" 
    apply(rule_tac pair_rel_arg)
    using relation_def binmap'_def 
    by auto
  then obtain m where mH: "<binmap_row'(m), 0> \<in> binmap'" "v = <Pn_auto(Fn_perm'(f))`binmap_row'(m), F`0>" "m \<in> nat" 
    using binmap'_def fH
    by force
  then have "v = <binmap_row'(f`m), 0>"
    using pauto_0 assms binmap_row'_pauto fH
    by auto
  then show "v \<in> binmap'" 
    unfolding binmap'_def 
    apply(subgoal_tac "f`m \<in> nat", force)
    apply(rule function_value_in)
    using mH nat_perms_def bij_def inj_def fH
    by auto
next 

  obtain f where fH: "F = Fn_perm'(f)" "f \<in> nat_perms" using assms Fn_perms_def by force

  fix v 
  assume "v \<in> binmap'" 
  then obtain m where mH: "v = <binmap_row'(m), 0>" "m \<in> nat" using binmap'_def by force

  have "f \<in> surj(nat, nat)" using fH nat_perms_def bij_is_surj by force
  then obtain m' where "m = f`m'" using surj_def mH by auto

  have "Pn_auto(F)`binmap_row'(converse(f)`m) = Pn_auto(Fn_perm'(f))`binmap_row'(converse(f)`m)" using fH by auto
  also have "... = binmap_row'(f`(converse(f)`m))"
    apply(rule binmap_row'_pauto)
     apply(rule function_value_in)
      apply(insert bij_converse_bij [of f nat nat])
    using bij_def inj_def fH nat_perms_def mH
    by auto
  also have "... = binmap_row'(m)" 
    apply(subst right_inverse_bij)
    using fH nat_perms_def mH 
    by auto
  finally have eq: "Pn_auto(F) ` binmap_row'(converse(f) ` m) = binmap_row'(m)" by simp

  have "<Pn_auto(F) ` binmap_row'(converse(f) ` m), F`0> \<in> Pn_auto(F) ` binmap'"  
    apply(subst (2) Pn_auto, rule binmap'_in_P_name)
    apply(rule pair_relI, simp add:binmap'_def)
    apply(rule_tac x="converse(f)`m" in bexI, simp)
     apply(rule function_value_in)
      apply(insert bij_converse_bij [of f nat nat])
    using bij_def inj_def fH nat_perms_def mH
    by auto
  then have "<binmap_row'(m), 0> \<in> Pn_auto(F) ` binmap'"  
    using eq pauto_0 assms 
    by auto
  then show "v \<in> Pn_auto(F) ` binmap'"  
    using mH
    by auto
qed

lemma sym_binmap' : "sym(binmap') = Fn_perms" 
  unfolding sym_def 
  using binmap'_pnauto 
  by auto

lemma binmap'_HS : "binmap' \<in> HS" 
  apply(rule iffD2, rule HS_iff, rule conjI)
   apply(rule iffD2, rule P_name_iff, rule conjI)
    apply(rule binmap'_in_M)
  using binmap'_def binmap_row'_P_name zero_in_Fn 
   apply force
  apply(rule conjI)
  using binmap'_def binmap_row'_HS 
   apply force
  unfolding symmetric_def 
  unfolding Fn_perms_filter_def
  apply simp
  apply(rule conjI, rule sym_P_auto_subgroup)
   apply(rule iffD2, rule P_name_iff, rule conjI)
    apply(rule binmap'_in_M)
  using binmap'_def binmap_row'_P_name zero_in_Fn 
   apply force
  apply(rule_tac x=0 in bexI)
  unfolding finite_M_def 
   apply(rule conjI, rule_tac x=0 in bexI)
  apply(rule_tac a=0 in not_emptyI)
  using inj_def zero_in_M
     apply auto[2]
   apply(subst sym_binmap')
  using Fix_def Fn_perms_def zero_in_M
  by auto

lemma finite_M_cons : 
  fixes A x 
  assumes "finite_M(A)" "x \<in> M" "x \<notin> A"  
  shows "finite_M(cons(x, A))" 
proof - 

  obtain n f where nfH: "n \<in> nat" "f \<in> inj(A, n)" "f \<in> M" using assms finite_M_def by force

  define g where "g \<equiv> f \<union> { <x, n> }" 

  have "\<And>y. <x, y> \<notin> f" 
    using nfH inj_def Pi_def assms
    by force
  then have functionH: "function(g)" 
    unfolding function_def g_def
    using nfH inj_def Pi_def assms function_def
    by force

  have "domain(g) = domain(f) \<union> {x}" 
    unfolding g_def 
    by auto
  then have domH: "domain(g) = cons(x, A)"
    using cons_def assms nfH inj_def Pi_def
    by auto

  have ranH: "range(g) \<subseteq> succ(n)" 
    unfolding g_def 
    using nfH inj_def Pi_def
    by auto
  
  have gpiH: "g \<in> cons(x, A) \<rightarrow> succ(n)" 
    apply(rule Pi_memberI)
    using relation_def g_def nfH inj_def Pi_def
       apply force
    using functionH domH ranH 
    by auto

  have appAH: "\<And>a. a \<in> A \<Longrightarrow> g`a = f`a" 
    apply(rule function_apply_equality)
    unfolding g_def 
     apply simp
     apply(rule disjI1, rule function_apply_Pair)
    using nfH inj_def Pi_def g_def functionH
    by auto

  have appAH' : "\<And>a. a \<in> A \<Longrightarrow> g`a \<in> n" 
  proof - 
    fix a 
    assume ain : "a \<in> A" 
    then have "g`a = f`a" using appAH by auto
    have "a \<in> domain(f)" using nfH inj_def Pi_def ain by auto
    then obtain m where mH: "<a, m> \<in> f" by auto
    then have "f`a = m" using function_apply_equality nfH inj_def Pi_def by auto
    have "m \<in> n" using nfH inj_def Pi_def mH by auto
    then show "g`a \<in> n" using \<open>f`a = m\<close> \<open>g`a = f`a\<close> by auto
  qed    

  have appxH: "g`x = n" 
    apply(rule function_apply_equality)
    using g_def functionH
    by auto

  have appneq : "\<And>a. a \<in> A \<Longrightarrow> g`a \<noteq> g`x" 
    apply(rule ccontr)
    using appAH' appxH
    apply simp
    apply(subgoal_tac "n \<in> n", rule mem_irrefl, simp)
    by auto

  have appneq' : "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> g`a = g`b \<Longrightarrow> a = b" 
    using appAH nfH inj_def 
    by force

  have "\<And>a b. a \<in> cons(x, A) \<Longrightarrow> b \<in> cons(x, A) \<Longrightarrow> g`a = g`b \<Longrightarrow> a = b"
    apply auto
    using appneq
    apply auto[2] 
    apply(rule appneq')
    by auto
  then have "g \<in> inj(cons(x, A), succ(n))" 
    unfolding inj_def
    using gpiH 
    by auto

  then show ?thesis 
    unfolding finite_M_def 
    apply(rule_tac x="succ(n)" in bexI)
     apply(subgoal_tac "g \<in> M", force)
    unfolding g_def
    using nfH Un_closed singleton_in_M_iff pair_in_M_iff assms nat_in_M transM
    by auto  
qed

lemma generic_filter_contains_max : 
  fixes G 
  assumes "M_generic(G)" 
  shows "0 \<in> G" 
proof - 
  thm M_generic_def
  filter_def

  have "dense(Fn)" 
    unfolding dense_def Fn_leq_def
    apply(subst forcing_notion.dense_def)
    using Fn_leq_def forcing_notion_axioms
     apply force
    by auto

  then have "G \<inter> Fn \<noteq> 0" using M_generic_def assms Fn_in_M by blast
  then obtain p where pH: "p \<in> Fn" "p \<in> G" by auto

  show "0 \<in> G" 
    apply(rule M_generic_leqD)
    using assms pH zero_in_Fn
       apply auto[3]
    unfolding Fn_leq_def
    using zero_in_Fn pH
    by auto
qed
   
lemma binmap_row_eq : 
  fixes n G  
  assumes "n \<in> nat" "M_generic(G)" 
  shows "binmap_row(G, n) = val(G, binmap_row'(n))" 
proof(rule equality_iffI, rule iffI)
  fix v 
  assume vin: "v \<in> val(G, binmap_row'(n))" 
  have "v \<in> { val(G, m) .. m \<in> domain(binmap_row'(n)), \<exists>p \<in> Fn. \<langle>m, p\<rangle> \<in> binmap_row'(n) \<and> p \<in> G }"
    apply(rule_tac P="v \<in> val(G, binmap_row'(n))" in mp)
    apply(subst def_val)
    using vin 
    by auto
  then obtain m p where mpH: "p \<in> Fn" "m \<in> nat" "\<langle>check(m), p\<rangle> \<in> binmap_row'(n)" "p \<in> G" "v = val(G, check(m))" "p`<n, m> = 1" 
    unfolding binmap_row'_def
    by force
  
  have "val(G, check(m)) = m"
    apply(rule valcheck)
    using generic_filter_contains_max zero_in_Fn assms
    by auto
  then have "v = m" using mpH by auto 
  then show "v \<in> binmap_row(G, n)" 
    unfolding binmap_row_def 
    using mpH 
    by auto
next 
  fix v
  assume "v \<in> binmap_row(G, n)" 
  then obtain m p where mpH: "m \<in> nat" "p \<in> G" "p`<n, m> = 1" "v = m" using binmap_row_def by auto
  then have "<check(m), p> \<in> binmap_row'(n)" 
    unfolding binmap_row'_def 
    apply auto
      apply(subst (2) def_check)
    using mpH M_genericD assms
    by auto
  then have "val(G, check(m)) \<in> { val(G, m) .. m \<in> domain(binmap_row'(n)), \<exists>p \<in> Fn. \<langle>m, p\<rangle> \<in> binmap_row'(n) \<and> p \<in> G }"
    apply simp
    apply(rule_tac x="check(m)" in bexI)
    using mpH M_genericD assms
    by auto
  then have "val(G, check(m)) \<in> val(G, binmap_row'(n))" 
    by(subst (2) def_val, force)
  then show "v \<in> val(G, binmap_row'(n))" 
    apply(subgoal_tac "m = val(G, check(m))")
    using mpH 
     apply force
    apply(rule sym)
    apply(rule valcheck)
    using generic_filter_contains_max zero_in_Fn assms
    by auto
qed

lemma binmap_eq : 
  fixes G 
  assumes "M_generic(G)" 
  shows "binmap(G) = val(G, binmap')" 

  apply(subst def_val)
  unfolding binmap_def
  apply(rule equality_iffI, rule iffI)
   apply clarsimp
   apply(rename_tac n, rule_tac x="binmap_row'(n)" in bexI)
    apply(rule conjI)
  using binmap_row_eq assms
     apply force
    apply(rule_tac x=0 in bexI)
  using binmap'_def assms generic_filter_contains_max zero_in_Fn
     apply auto[3]
  using binmap'_def
  apply clarsimp
  apply(rename_tac n m, rule_tac x=m in bexI)
  using binmap_row_eq assms
  by auto

lemma Fn_leq_preserves_value : 
  fixes p q 
  assumes "<q, p> \<in> Fn_leq" "<m, n> \<in> domain(p)" 
  shows "q`<m, n> = p`<m, n>" 
proof - 
  obtain v where vH: "<<m, n>, v> \<in> p" using assms by auto 
  then have vH': "<<m, n>, v> \<in> q" using assms Fn_leq_def by auto

  have papp : "p`<m, n> = v" 
    apply(rule function_apply_equality)
    using vH assms Fn_leq_def Fn_def 
    by auto

  have qapp : "q`<m, n> = v" 
    apply(rule function_apply_equality)
    using vH assms Fn_leq_def Fn_def 
    by auto

  show "q`<m, n> = p`<m, n>" using papp qapp by auto 
qed

lemma Fn_1_forces : 
  fixes p n m 
  assumes "p \<in> Fn" "n \<in> nat" "m \<in> nat" "p`<n, m> = 1" 
  shows "\<forall>G. M_generic(G) \<and> p \<in> G \<longrightarrow> SymExt(G), map(val(G), [check(m), binmap_row'(n)]) \<Turnstile> Member(0, 1)" 
  apply(clarsimp)
  apply(rule iffD2, rule sats_Member_iff)
   apply clarsimp
   apply(rule conjI, subst SymExt_def)
  using check_in_HS assms transM nat_in_M 
    apply force
  using binmap_row'_HS assms SymExt_def
   apply force
  apply simp
  apply(rename_tac G, subgoal_tac "val(G, check(m)) = m \<and> val(G, binmap_row'(n)) = binmap_row(G, n)")
   apply (simp add:binmap_row_def)
  using assms
   apply force
  apply(rule conjI)
   apply(rule valcheck)
  using generic_filter_contains_max zero_in_Fn assms binmap_row_eq
  by auto

lemma Fn_0_forces : 
  fixes p n m 
  assumes "p \<in> Fn" "n \<in> nat" "m \<in> nat" "p`<n, m> = 0" "<n ,m> \<in> domain(p)"  
  shows "\<forall>G. M_generic(G) \<and> p \<in> G \<longrightarrow> SymExt(G), map(val(G), [check(m), binmap_row'(n)]) \<Turnstile> Neg(Member(0, 1))" 
proof(rule ccontr)
  assume "\<not> (\<forall>G. M_generic(G) \<and> p \<in> G \<longrightarrow> SymExt(G), map(val(G), [check(m), binmap_row'(n)]) \<Turnstile> Neg(Member(0, 1)))" 
  then obtain G where GH: "M_generic(G)" "p \<in> G" "\<not>(SymExt(G), map(val(G), [check(m), binmap_row'(n)]) \<Turnstile> Neg(Member(0, 1)))"
    by auto

  have listin : "[check(m), binmap_row'(n)] \<in> list(HS)" 
      apply simp
      apply(rule conjI)
    using check_in_HS assms nat_in_M transM
       apply force
    using binmap_row'_HS assms
    apply force 
    done

  have mapin : "map(val(G), [check(m), binmap_row'(n)]) \<in> list(SymExt(G))" 
    unfolding SymExt_def 
    using listin 
    by auto

  have "SymExt(G), map(val(G), [check(m), binmap_row'(n)]) \<Turnstile> Member(0, 1)"
    using mapin GH by auto

  then have "val(G, check(m)) \<in> val(G, binmap_row'(n))" 
    using mapin 
    by auto
  then have "m \<in> binmap_row(G, n)" 
    apply(subgoal_tac "val(G, check(m)) = m \<and> val(G, binmap_row'(n)) = binmap_row(G, n)")
     apply (simp add:binmap_row_def)
    apply(rule conjI)
     apply(rule valcheck)
    using generic_filter_contains_max zero_in_Fn assms binmap_row_eq GH
    by auto
  then obtain q where qH: "q \<in> G" "q`<n, m> = 1" 
    using binmap_row_def
    by auto

  have domin : "<n, m> \<in> domain(q)" 
    apply(rule ccontr)
    using qH apply_0
    by force

  have "\<forall>p\<in>G. \<forall>q\<in>G. compat_in(G, Fn_leq, p, q)" 
    using GH M_generic_def filter_def by auto
  then obtain r where rH: "<r, p> \<in> Fn_leq" "<r, q> \<in> Fn_leq" "r \<in> G" 
    using compat_in_def qH GH by force
  then have "r`<n, m> = q`<n, m>" 
    using Fn_leq_preserves_value domin 
    by auto
  then have v1: "r`<n, m> = 1" using qH by auto

  have "r`<n, m> = 0" 
    using rH GH Fn_leq_preserves_value assms
    by force
  then show "False" using v1 by auto
qed 

lemma binmap_row'_distinct_helper : 
  fixes n m p
  assumes "n \<in> nat" "n' \<in> nat" "n \<noteq> n'" "p \<in> Fn" "ForcesHS(p, Equal(0, 1), [binmap_row'(n), binmap_row'(n')])" 
  shows False 
proof - 
  have H: "\<And>A. A \<subseteq> nat \<Longrightarrow> Finite(A) \<Longrightarrow> \<exists>a \<in> nat. a \<notin> A" 
    apply(rule ccontr)
    apply(rename_tac A, subgoal_tac "A = nat")
    using nat_not_Finite 
     apply force 
    apply(rule equalityI)
    by auto

  have "finite_M(domain(p)) \<and> domain(p) \<subseteq> nat \<times> nat" using assms Fn_def by auto

  then have finitedom : "Finite(domain(p))" 
    unfolding finite_M_def  
    apply clarsimp
    apply(rename_tac n, rule_tac X=n in lepoll_Finite)
    unfolding lepoll_def
     apply(rule not_emptyE, force, force)
    apply(rule nat_into_Finite, simp)
    done

  have "{ snd(x). x \<in> domain(p) } = range(domain(p))" (is "?A = _")
    apply(rule equality_iffI, rule iffI)
    using assms Fn_def
     apply(force, force)
    done

  have "Finite(?A)" 
    apply(rule Finite_RepFun, rule finitedom)
    done
  then have "Finite(range(domain(p)))" using \<open>?A = range(domain(p))\<close> by auto
  then have "\<exists>x \<in> nat. x \<notin> range(domain(p))" 
    apply(rule_tac H)
    using assms Fn_def 
    by auto
  then obtain m where mH: "m \<in> nat" "m \<notin> range(domain(p))" by auto

  define q where "q \<equiv> p \<union> { <<n, m>, 1> } \<union> { <<n', m>, 0> }" 

  have "domain(q) = domain(p) \<union> { <n, m>, <n', m> }" using q_def by auto
  then have "domain(q) = cons(<n, m>, cons(<n', m>, domain(p)))" by auto 
  then have domfin: "finite_M(domain(q))" 
    apply simp
    apply(rule finite_M_cons)+
    using pair_in_M_iff assms nat_in_M transM mH Fn_def
    by auto

  have qinFn : "q \<in> Fn" 
    unfolding q_def Fn_def  
    apply clarsimp
    apply(rule conjI)
    using assms Fn_def mH 
     apply force 
    apply(rule conjI)
    using Fn_def assms Un_closed pair_in_M_iff singleton_in_M_iff nat_in_M transM zero_in_M mH
     apply force
    unfolding function_def
    apply(rule conjI)
     apply auto[1]
    using assms Fn_def function_def mH
           apply auto[7]
    apply(rule conjI)
    using assms Fn_def mH
     apply auto[1]
    apply(rule conjI)
    using domfin q_def 
     apply force
    using assms Fn_def mH
    by auto

  have appn : "q`<n, m> = 1"
    apply(rule function_apply_equality)
    using q_def qinFn Fn_def 
    by auto

  have appn' : "q`<n', m> = 0" 
    apply(rule function_apply_equality)
    using q_def qinFn Fn_def 
    by auto    

  have listin : "[binmap_row'(n), binmap_row'(n')] \<in> list(HS)" 
    using binmap_row'_HS assms
    by auto
  then have mapin : "\<And>G. map(val(G), [binmap_row'(n), binmap_row'(n')]) \<in> list(SymExt(G))" 
    unfolding SymExt_def
    by auto

  have "\<forall>G. M_generic(G) \<and> q \<in> G \<longrightarrow> SymExt(G), map(val(G), [binmap_row'(n), binmap_row'(n')]) \<Turnstile> Equal(0, 1)"
    apply(rule iffD1, rule definition_of_forcing_HS)
    using assms binmap_row'_HS qinFn
        apply auto[3]
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    apply(rule_tac p=p in HS_strengthening_lemma)
    using assms qinFn Fn_leq_def q_def listin HS_iff P_name_in_M
    apply auto[5]
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    using assms
    by auto
  then have eqH: "\<forall>G. M_generic(G) \<and> q \<in> G \<longrightarrow> val(G, binmap_row'(n)) = val(G, binmap_row'(n'))"
    using mapin
    by force

  have "\<forall>G. M_generic(G) \<and> q \<in> G \<longrightarrow> SymExt(G), map(val(G), [check(m), binmap_row'(n)]) \<Turnstile> Member(0, 1)" 
    apply(rule Fn_1_forces)
    using assms mH qinFn appn
    by auto
  then have memH: "\<forall>G. M_generic(G) \<and> q \<in> G \<longrightarrow> val(G, check(m)) \<in> val(G, binmap_row'(n))"
    apply(rule_tac allI)
    apply(rename_tac G, subgoal_tac "map(val(G), [check(m), binmap_row'(n)]) \<in> list(SymExt(G))")
     apply force
    unfolding SymExt_def
    using check_in_HS listin mH nat_in_M transM
    by auto

  have "\<forall>G. M_generic(G) \<and> q \<in> G \<longrightarrow> SymExt(G), map(val(G), [check(m), binmap_row'(n')]) \<Turnstile> Neg(Member(0, 1))"
    apply(rule Fn_0_forces)
    using assms mH qinFn appn' q_def
    by auto
  then have "\<forall>G. M_generic(G) \<and> q \<in> G \<longrightarrow> val(G, check(m)) \<notin> val(G, binmap_row'(n'))"
    apply(rule_tac allI)
    apply(rename_tac G, subgoal_tac "map(val(G), [check(m), binmap_row'(n')]) \<in> list(SymExt(G))")
     apply force
    unfolding SymExt_def
    using check_in_HS listin mH nat_in_M transM
    by auto
  then have neqH: "\<forall>G. M_generic(G) \<and> q \<in> G \<longrightarrow> val(G, binmap_row'(n)) \<noteq> val(G, binmap_row'(n'))"
    using memH by auto
  
  have "\<exists>G. M_generic(G) \<and> q \<in> G" 
    using generic_filter_existence qinFn 
    by force

  then show False 
    using eqH neqH 
    by force
qed

lemma binmap_row'_distinct : 
  fixes n m 
  assumes "n \<in> nat" "m \<in> nat" "n \<noteq> m" 
  shows "ForcesHS(0, Neg(Equal(0, 1)), [binmap_row'(n), binmap_row'(m)])" 

  apply(rule iffD2, rule ForcesHS_Neg)
  using Fn_in_M binmap_row'_in_M assms zero_in_Fn
     apply auto[3]
  apply(rule ccontr, clarsimp)
  using binmap_row'_distinct_helper assms
  by auto

lemma binmap_row_distinct : 
  fixes G n m 
  assumes "M_generic(G)" "n \<in> nat" "m \<in> nat" "n \<noteq> m" 
  shows "binmap_row(G, n) \<noteq> binmap_row(G, m)" 
proof - 

  have listin : "[binmap_row'(n), binmap_row'(m)] \<in> list(HS)" 
    using binmap_row'_HS assms
    by auto
  
  have "ForcesHS(0, Neg(Equal(0, 1)), [binmap_row'(n), binmap_row'(m)])"
    apply(rule binmap_row'_distinct)
    using assms
    by auto
  then have "(\<forall>H. M_generic(H) \<and> 0\<in>H  \<longrightarrow>  SymExt(H), map(val(H),[binmap_row'(n), binmap_row'(m)]) \<Turnstile> Neg(Equal(0, 1)))"
    apply(rule_tac iffD1)
     apply(rule definition_of_forcing_HS)
    using zero_in_M assms zero_in_Fn listin
    apply auto[4]
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    by auto
  then have "SymExt(G), map(val(G),[binmap_row'(n), binmap_row'(m)]) \<Turnstile> Neg(Equal(0, 1))"
    using assms local.generic_filter_contains_max 
    by auto
  then have "val(G, binmap_row'(n)) \<noteq> val(G, binmap_row'(m))" (is ?A)
    apply(subgoal_tac "val(G, binmap_row'(n)) \<in> SymExt(G) \<and> val(G, binmap_row'(m)) \<in> SymExt(G)")
     apply force
    using SymExt_def listin
    by auto
  then show rowneq: "binmap_row(G, n) \<noteq> binmap_row(G, m)" 
    apply(rule_tac P="?A" in iffD1)
     apply(subst binmap_row_eq)
    using assms  
       apply auto[2]
     apply(subst binmap_row_eq)
    using assms nat_perms_def bij_def inj_def
    by auto
qed

end
end