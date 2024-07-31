theory P_Names_M
  imports 
    "Forcing/Forcing_Main"
    RecFun_M_Memrel
    P_Names
begin 

context forcing_data
begin 

definition is_1 where "is_1(x) \<equiv> \<forall>y \<in> M. y \<in> x \<longleftrightarrow> empty(##M, y)" 

lemma is_1D : "A \<in> M \<Longrightarrow> \<forall>x \<in> M. x \<in> A \<longleftrightarrow> x = 0 \<Longrightarrow> A = 1" 
  apply(rule equality_iffI; rule iffI) 
  using transM 
  by auto

lemma is_1_iff : 
  fixes x 
  assumes "x \<in> M" 
  shows "is_1(x) \<longleftrightarrow> x = 1" 
  unfolding is_1_def 
  apply(rule iffI, rule equality_iffI, rule iffI)
  using transM assms zero_in_M 
    apply (force, force)
  by auto

end

definition is_1_fm where "is_1_fm(x) \<equiv> Forall(Iff(Member(0, x #+ 1), empty_fm(0)))"

context forcing_data
begin 

lemma is_1_fm_type : 
  fixes i 
  assumes "i \<in> nat" 
  shows "is_1_fm(x) \<in> formula" 
  unfolding is_1_fm_def by auto

lemma arity_is_1_fm : 
  fixes i  assumes "i \<in> nat" 
  shows "arity(is_1_fm(i)) = succ(i)" 
  unfolding is_1_fm_def 
  using assms 
  apply simp
  apply(subst arity_empty_fm, simp)
  apply(subst Ord_un_eq2, simp_all, subst Ord_un_eq1, simp_all)
  done
  
lemma sats_is_1_fm_iff : 
  fixes i x env 
  assumes "i < length(env)" "nth(i, env) = x" "env \<in> list(M)"
  shows "sats(M, is_1_fm(i), env) \<longleftrightarrow> x = 1" 

  unfolding is_1_fm_def 
  apply(subgoal_tac "i \<in> nat")
  apply(rule_tac Q="\<forall>v \<in> M. v \<in> x \<longleftrightarrow> v = 0" in iff_trans)
   apply(rule iff_trans, rule sats_Forall_iff, simp add:assms)
   apply(rule ball_iff, rule iff_trans, rule sats_Iff_iff, simp add:assms, rule iff_iff, simp add:assms)
   apply(rule iff_trans, rule sats_empty_fm, simp, simp add:assms, simp add:assms)
  using is_1_iff assms
  unfolding is_1_def 
   apply force
  apply(rule lt_nat_in_nat)
  using assms 
  by auto
  
definition His_P_name where "His_P_name(x, g) \<equiv> if relation(x) \<and> range(x) \<subseteq> P \<and> (\<forall>y \<in> domain(x). g`y = 1) then 1 else 0" 

definition is_P_name where "is_P_name(x) \<equiv> wftrec(Memrel(M)^+, x, His_P_name)" 

lemma def_is_P_name : 
  fixes x 
  assumes "x \<in> M" 
  shows "x \<in> P_names \<longleftrightarrow> is_P_name(x) = 1" 

proof-
  have "\<And>x. x \<in> M \<longrightarrow> x \<in> P_names \<longleftrightarrow> is_P_name(x) = 1" 
  proof(rule_tac Q="\<lambda>x. x \<in> M \<longrightarrow> x \<in> P_names \<longleftrightarrow> is_P_name(x) = 1" in ed_induction, rule impI)
    fix x assume assms1: "x \<in> M" "(\<And>y. ed(y, x) \<Longrightarrow> y \<in> M \<longrightarrow> y \<in> P_names \<longleftrightarrow> is_P_name(y) = 1)"
    have "is_P_name(x) = 1 \<longleftrightarrow> His_P_name(x, \<lambda>y \<in> Memrel(M)^+ -`` {x}. is_P_name(y)) = 1"
      unfolding is_P_name_def 
      apply(subst wftrec)
        apply(rule wf_trancl, rule wf_Memrel, rule trans_trancl)
      by simp
    also have "... \<longleftrightarrow> relation(x) \<and> range(x) \<subseteq> P \<and> (\<forall>y \<in> domain(x). (\<lambda>y \<in> Memrel(M)^+ -`` {x}. is_P_name(y))`y = 1)" 
      unfolding His_P_name_def 
      apply(rule iffI, rule_tac a=1 and b=0 in ifT_eq, simp, simp)
      apply(subst if_P, auto)
      done
    also have "... \<longleftrightarrow> relation(x) \<and> range(x) \<subseteq> P \<and> (\<forall>y \<in> domain(x). is_P_name(y) = 1)" 
      apply(rule iff_conjI, simp)+
      apply(rule ball_iff)
      apply(rename_tac y, subgoal_tac "y \<in> Memrel(M)^+ -`` {x}", simp, rule_tac b=x in vimageI)
       apply(rule domain_elem_Memrel_trancl)
      using assms1 
      by auto 
    also have "... \<longleftrightarrow> relation(x) \<and> range(x) \<subseteq> P \<and> (\<forall>y \<in> domain(x). y \<in> P_names)" 
      apply(rule iff_conjI, simp)+ 
      apply(rule ball_iff)
      apply(rename_tac y, subgoal_tac "y \<in> M")
      using assms1 ed_def 
       apply blast
      using domain_elem_in_M assms1
      by auto 
    also have "... \<longleftrightarrow> x \<subseteq> P_names \<times> P" 
    proof(rule iffI, rule subsetI)
      fix v assume assms2: "relation(x) \<and> range(x) \<subseteq> P \<and> (\<forall>y\<in>domain(x). y \<in> P_names)" "v \<in> x" 
      then obtain y p where ypH : "v = <y, p>" using assms2 relation_def by auto
      then have H1: "y \<in> P_names" using assms2 by auto 
      then have H2: "p \<in> P" using assms2 ypH by auto 
      then show "v \<in> P_names \<times> P" using ypH H1 H2 by auto 
    next 
      assume assms2: "x \<subseteq> P_names \<times> P" 
      show "relation(x) \<and> range(x) \<subseteq> P \<and> (\<forall>y\<in>domain(x). y \<in> P_names)" 
        unfolding relation_def
        using assms2 
        by auto
    qed
    also have "... \<longleftrightarrow> x \<in> P_names" using P_name_iff assms1 by auto

    finally show "x \<in> P_names \<longleftrightarrow> is_P_name(x) = 1" by simp
  qed
  then show ?thesis using assms by auto 
qed

definition His_P_name_M where 
  "His_P_name_M(x', g) \<equiv> (if \<exists>x \<in> M. \<exists>P \<in> M. x' = <x, P> \<and> relation(x) \<and> range(x) \<subseteq> P \<and> (\<forall>y \<in> domain(x). g`<y, P> = 1) then 1 else 0)" 

definition His_P_name_M_cond where 
  "His_P_name_M_cond(x', g) \<equiv> 
      (\<exists>x \<in> M. \<exists>P \<in> M. \<exists>xrange \<in> M. \<exists>xdomain \<in> M.
      pair(##M, x, P, x') \<and> is_relation(##M, x) \<and> is_range(##M, x, xrange) \<and> is_domain(##M, x, xdomain) 
      \<and> subset(##M, xrange, P) \<and> (\<forall>y \<in> M. y \<in> xdomain \<longrightarrow> (\<exists>y_P \<in> M. \<exists>gy \<in> M. pair(##M, y, P, y_P) \<and> fun_apply(##M, g, y_P, gy) \<and> (\<forall>z \<in> M. z \<in> gy \<longleftrightarrow> empty(##M, z)))))"

lemma His_P_name_M_cond_iff : 
  "\<And>x' g. x' \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> 
    (\<exists>x \<in> M. \<exists>P \<in> M. x' = <x, P> \<and> relation(x) \<and> range(x) \<subseteq> P \<and> (\<forall>y \<in> domain(x). g`<y, P> = 1)) \<longleftrightarrow> His_P_name_M_cond(x', g)" 
  unfolding His_P_name_M_cond_def 
  using domain_closed range_closed pair_in_M_iff 
  apply auto  
  apply(rule_tac is_1D) 
   apply(rule_tac to_rin) 
   apply(rule_tac apply_closed) 
    apply simp 
   apply simp 
   apply(rule_tac x=x in domain_elem_in_M) 
    apply simp 
   apply(rule_tac P="y \<in> M \<and> y \<in> domain(x)" in mp) 
    apply simp 
  using domain_elem_in_M domainI 
  by auto 

schematic_goal His_P_name_M_fm_auto:
  assumes
    "nth(0,env) = v" 
    "nth(1,env) = g" 
    "nth(2,env) = x'"   
    "env \<in> list(M)" 
 shows 
    "(\<forall>e \<in> M. e \<in> v \<longleftrightarrow> (empty(##M, e) \<and> His_P_name_M_cond(x', g))) \<longleftrightarrow> sats(M,?fm(0,1,2),env)" 
  unfolding His_P_name_M_cond_def subset_def 
  by (insert assms ; (rule sep_rules | simp)+) 

end 

definition His_P_name_M_fm where "His_P_name_M_fm \<equiv> 
       Forall
             (Iff(Member(0, 1),
                  And(empty_fm(0),
                      Exists
                       (Exists
                         (Exists
                           (Exists
                             (And(pair_fm(3, 2, 7),
                                  And(relation_fm(3),
                                      And(range_fm(3, 1),
                                          And(domain_fm(3, 0),
                                              And(Forall(Implies(Member(0, 2), Member(0, 3))),
                                                  Forall
                                                   (Implies
                                                     (Member(0, 1),
                                                      Exists
                                                       (Exists
                                                         (And(pair_fm(2, 5, 1),
                                                              And(fun_apply_fm(9, 1, 0),
                                                                  Forall(Iff(Member(0, 1), empty_fm(0)))))))))))))))))))))   "


context forcing_data
begin 

lemma His_P_name_M_fm_iff_sats : 
  "v \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> x' \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> sats(M, His_P_name_M_fm, [v, g, x'] @ env) \<longleftrightarrow> v = His_P_name_M(x', g)" 

  apply(rule_tac Q="\<forall>e \<in> M. e \<in> v \<longleftrightarrow> (empty(##M, e) \<and> His_P_name_M_cond(x', g))" in iff_trans)
   apply(rule_tac iff_flip) 
  unfolding His_P_name_M_fm_def 
   apply(rule_tac v=v in His_P_name_M_fm_auto) 
      apply simp_all   
  unfolding His_P_name_M_def 
  apply(rule_tac iffD2) 
   apply(rule_tac P="\<lambda>X. ((\<forall>e\<in>M. e \<in> v \<longleftrightarrow> e = 0 \<and> His_P_name_M_cond(x', g))) \<longleftrightarrow> v = X" in split_if) 
  apply(rule conjI) 
   apply(rule impI) 
   apply(rule_tac P="His_P_name_M_cond(x', g)" in mp) 
    apply (rule impI; simp) 
    apply(rule iffI) 
     apply(rule_tac is_1D) 
      apply simp 
     apply simp 
    apply(clarify) 
    apply blast 
  using His_P_name_M_cond_iff 
   apply blast 
  apply clarify
  apply(rule_tac P="\<not>His_P_name_M_cond(x', g)" in mp)
  using empty_abs empty_def 
   apply simp 
  using His_P_name_M_cond_iff 
  apply blast 
  done

end

definition is_P_name_fm where "is_P_name_fm(p, x) \<equiv> Exists(And(is_memrel_wftrec_fm(His_P_name_M_fm, x #+ 1, p #+ 1, 0), is_1_fm(0)))" 

context forcing_data
begin 

lemma is_P_name_fm_type : 
  fixes i j 
  assumes "i \<in> nat" "j \<in> nat" 
  shows "is_P_name_fm(i, j) \<in> formula" 
  unfolding is_P_name_fm_def 
  apply(rule Exists_type, rule And_type, rule is_memrel_wftrec_fm_type)
  unfolding His_P_name_M_fm_def 
  using assms 
      apply auto[4]
  apply(rule is_1_fm_type)
  by auto

lemma arity_is_P_name_fm : 
  fixes i j 
  assumes "i \<in> nat" "j \<in> nat" 
  shows "arity(is_P_name_fm(i, j)) \<le> succ(i) \<union> succ(j)" 
  apply(subgoal_tac "is_memrel_wftrec_fm(His_P_name_M_fm, succ(j), succ(i), 0) \<in> formula")
  apply(subgoal_tac "is_1_fm(0) \<in> formula")
  unfolding is_P_name_fm_def 
  apply simp
  using assms
    apply(subst pred_Un_distrib, simp_all)
    apply(rule Un_least_lt, rule pred_le, simp, simp)
     apply(rule le_trans, rule arity_is_memrel_wftrec_fm)
          apply(simp add:His_P_name_M_fm_def)+
         apply(simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union) 
        apply auto[3]
     apply(rule Un_least_lt)+
       apply(simp, rule ltI, simp, simp)+
     apply simp
    apply(rule pred_le, simp_all)
    apply(rule_tac j=1 in le_trans, simp add:is_1_fm_def)
     apply(subst arity_empty_fm, simp)
     apply(simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union, simp)
   apply(rule is_1_fm_type, simp)
  apply(rule is_memrel_wftrec_fm_type)
     apply(simp add:His_P_name_M_fm_def)
  by auto  

lemma sats_is_P_name_fm_iff : 
  fixes env i j x 
  assumes "env \<in> list(M)" "i < length(env)" "j < length(env)" "nth(i, env) = P" "nth(j, env) = x"  
  shows "sats(M, is_P_name_fm(i, j), env) \<longleftrightarrow> x \<in> P_names" 
proof - 
  have inat : "i \<in> nat" using assms lt_nat_in_nat by auto
  have jnat : "j \<in> nat" using assms lt_nat_in_nat by auto
  have xinM : "x \<in> M" using assms by auto

  have Heq: "\<And>h g x. h \<in> eclose(x) \<rightarrow> M \<Longrightarrow> g \<in> eclose(x) \<times> {P} \<rightarrow> M \<Longrightarrow> g \<in> M
               \<Longrightarrow> x \<in> M \<Longrightarrow> (\<And>y. y \<in> eclose(x) \<Longrightarrow> h`y = g`<y, P>) \<Longrightarrow> His_P_name(x, h) = His_P_name_M(<x, P>, g)"   
    unfolding His_P_name_def His_P_name_M_def 
    apply(rule if_cong, rule iffI, simp add:P_in_M, rule ballI)
       apply(rename_tac h g x y, subgoal_tac "y \<in> eclose(x)")
        apply auto[2]
       apply(rule domain_elem_in_eclose, force)
      apply simp
    apply(rule ballI)
      apply(rename_tac h g x y, subgoal_tac "y \<in> eclose(x)")
       apply auto[1]
      apply(rule domain_elem_in_eclose)
    by auto
    
  have "sats(M, is_P_name_fm(i, j), env) \<longleftrightarrow> (\<exists>v \<in> M. v = wftrec(Memrel(M)^+, x, His_P_name) \<and> v = 1)" 
    unfolding is_P_name_fm_def 
    apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
     apply(rule_tac a=P and G=His_P_name_M 
        in sats_is_memrel_wftrec_fm_iff)
    using assms singleton_in_M_iff P_in_M xinM inat jnat
                   apply auto[10]
         apply(simp add: His_P_name_M_fm_def)
        apply (simp add: His_P_name_M_fm_def, simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union) 
       apply(simp add: His_P_name_M_def, rule impI, simp add:zero_in_M)
      apply(rule Heq)
           apply auto[5]
     apply(rule iff_flip, rule His_P_name_M_fm_iff_sats)
        apply auto[4]
    apply(rule sats_is_1_fm_iff)
    using assms 
    by auto
  also have "... \<longleftrightarrow> is_P_name(x) = 1" unfolding is_P_name_def by auto
  also have "... \<longleftrightarrow> x \<in> P_names"  
    apply(rule iff_flip, rule def_is_P_name)
    using assms
    by auto 
  finally show ?thesis by simp
qed

end 
end













