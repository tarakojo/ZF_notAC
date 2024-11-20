theory HS_M
  imports 
    "Forcing/Forcing_Main" 
    HS_Definition
begin 


definition apply_all_1_fm where 
  "apply_all_1_fm(g, s, param) \<equiv> 
    Forall(Implies(Member(0, s #+ 1), Exists(Exists(And(pair_fm(2, param #+ 3, 1), And(fun_apply_fm(g #+ 3, 1, 0), is_1_fm(0)))))))" 

context M_symmetric_system
begin

lemma apply_all_1_fm_type : 
  fixes g s param
  assumes "g \<in> nat" "s \<in> nat" "param \<in> nat" 
  shows "apply_all_1_fm(g, s, param) \<in> formula" 
  unfolding apply_all_1_fm_def 
  apply(clarify, rule Implies_type, simp, rule Exists_type, rule Exists_type, rule And_type)
   apply simp
  apply(rule And_type)
  using is_1_fm_type assms 
  by auto

lemma arity_apply_all_1_fm :
  fixes g s param
  assumes "g \<in> nat" "s \<in> nat" "param \<in> nat"
  shows "arity(apply_all_1_fm(g, s, param)) \<le> succ(g) \<union> succ(s) \<union> succ(param)"
  apply(subgoal_tac "is_1_fm(0) \<in> formula")
  unfolding apply_all_1_fm_def 
   apply simp 
  using assms
   apply(subst pred_Un_distrib, simp_all)+
   apply(rule Un_least_lt, simp, rule ltI, simp, simp add:assms)
   apply(rule Un_least_lt, rule_tac j="succ(param)" in le_trans)
     apply(rule pred_le, simp_all)+
     apply(subst arity_pair_fm)
  apply auto[4]
     apply(rule Un_least_lt)+
      apply auto[1]
     apply(rule Un_least_lt, simp, simp)
    apply(rule ltI, simp, simp)
     apply(rule Un_least_lt)+
     apply(subst arity_fun_apply_fm)
  using assms 
        apply auto[3]
    apply(rule_tac j="succ(g)" in le_trans)
     apply(rule pred_le, simp_all)+
     apply(rule Un_least_lt)+
       apply(simp, simp, simp)
    apply(rule ltI, simp , simp)
   apply(subst arity_is_1_fm, simp)
   apply simp
  apply(rule is_1_fm_type)
  by auto

lemma sats_apply_all_1_fm_iff :
  fixes env i j k g s param
  assumes "i < length(env)" "j < length(env)" "k < length(env)" "env \<in> list(M)" "nth(i, env) = g" "nth(j, env) = s" "nth(k, env) = param" 
  shows "sats(M, apply_all_1_fm(i, j, k), env) \<longleftrightarrow> (\<forall>y. y \<in> s \<longrightarrow> g`<y, param> = 1)" 
proof - 
  have "sats(M, apply_all_1_fm(i, j, k), env) \<longleftrightarrow> (\<forall>y \<in> M. y \<in> s \<longrightarrow> g`<y, param> = 1)" 
    unfolding apply_all_1_fm_def 
    apply(rule iff_trans, rule sats_Forall_iff, simp add:assms)
    apply(rule ball_iff)
    apply(rule iff_trans, rule sats_Implies_iff, simp add:assms)
    apply(rule imp_iff)
    apply(subgoal_tac "j \<in> nat")
    using assms 
      apply simp
    using assms lt_nat_in_nat 
     apply force
    apply(rename_tac x, rule_tac Q= "\<exists>a \<in> M. \<exists>v \<in> M. a = <x, param> \<and>  g`a = v \<and> v = 1" in iff_trans)
     apply(rule iff_trans, rule sats_Exists_iff, simp add:assms)
     apply(rule bex_iff, rule iff_trans, rule sats_Exists_iff, simp add:assms)
     apply(rule bex_iff, rule iff_trans, rule sats_And_iff, simp add:assms)
     apply(rule iff_conjI)
    apply(subgoal_tac "i \<in> nat \<and> k \<in> nat \<and> g \<in> M")
    using assms 
       apply simp
      apply(rule conjI)
    using assms lt_nat_in_nat 
       apply force
      apply(rule conjI)
    using assms lt_nat_in_nat 
       apply force
    using assms nth_type 
      apply force
     apply(rule iff_trans, rule sats_And_iff, simp add:assms)
     apply(rule iff_conjI)
      apply(rule iff_trans, rule sats_fun_apply_fm)
    using assms lt_nat_in_nat 
          apply auto[5]
     apply(rule sats_is_1_fm_iff)
    using assms
       apply auto[3]
    apply(rule iffI, simp)
    apply(rename_tac x, rule_tac x="<x, param>" in bexI, simp)
    using assms nth_type pair_in_M_iff
    by auto
  also have "... \<longleftrightarrow> (\<forall>y. y \<in> s \<longrightarrow> g`<y, param> = 1)" 
    apply(rule iffI, clarify)
     apply(rename_tac y, subgoal_tac "y \<in> M", force)
     apply(subgoal_tac "s \<in> M")
    using transM 
      apply force
    using assms nth_type 
    by auto 
  finally show ?thesis by auto
qed

end

definition is_sym_elem_fm where
  "is_sym_elem_fm(p, G, x, v) \<equiv> And(Member(v, G), Exists(And(is_Pn_auto_fm(p #+ 1, v #+ 1, x #+ 1, 0), Equal(0, x #+ 1))))" 


context M_symmetric_system
begin

lemma is_sym_elem_fm_type :       
  fixes p G x v
  assumes "p \<in> nat" "G \<in> nat" "x \<in> nat" "v \<in> nat" 
  shows "is_sym_elem_fm(p, G, x, v) \<in> formula" 

  unfolding is_sym_elem_fm_def 
  apply(rule And_type)
  using assms 
   apply simp
  apply(rule Exists_type, rule And_type, rule is_Pn_auto_fm_type)
  using assms
  by auto

lemma arity_is_sym_elem_fm :    
  fixes p G x v
  assumes "p \<in> nat" "G \<in> nat" "x \<in> nat" "v \<in> nat" 
  shows "arity(is_sym_elem_fm(p, G, x, v)) \<le>  succ(p) \<union> succ(G) \<union> succ(x) \<union> succ(v)"

  apply(subgoal_tac "is_Pn_auto_fm(succ(p), succ(v), succ(x), 0) \<in> formula")
  unfolding is_sym_elem_fm_def
  apply simp 
  apply(rule Un_least_lt)+
    apply(rule ltI)
  using assms
     apply(subst succ_Un_distrib, simp_all)+
   apply(rule ltI, simp, simp)
  apply(rule pred_le, simp, simp)
   apply(rule Un_least_lt)+
    apply(rule le_trans, rule arity_is_Pn_auto_fm)
        apply auto[4]
    apply(subst succ_Un_distrib, simp_all)+
   apply(rule Un_least_lt)+
       apply(rule ltI, simp_all)+
    apply(rule disjI1, rule ltD, simp)
  apply(rule Un_least_lt, simp)
   apply(subst succ_Un_distrib, simp_all)+
   apply(rule ltI, simp, simp)
  apply(rule is_Pn_auto_fm_type)
  by auto

lemma sats_is_sym_elem_fm_iff : 
  fixes env p G x v i j k l 
  assumes "env \<in> list(M)" "i < length(env)" "j < length(env)" "k < length(env)" "l < length(env)"
          "nth(i, env) = P" "nth(j, env) = \<G>" "nth(k, env) = x" "nth(l, env) = v" 
          "x \<in> P_names" 
  shows "sats(M, is_sym_elem_fm(i, j, k, l), env) \<longleftrightarrow> v \<in> sym(x)" 
proof - 
  have "(M, env \<Turnstile> is_sym_elem_fm(i, j, k, l)) \<longleftrightarrow> (v \<in> \<G> \<and> (\<exists>u \<in> M. (x \<in> P_names \<and> u = Pn_auto(v)`x) \<and> u = x))" 
    unfolding is_sym_elem_fm_def 
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2, simp add:assms)
    apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)  
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
     apply(rule sats_is_Pn_auto_fm_iff) 
    using assms lt_nat_in_nat nth_type apply auto[9]
    using \<G>_P_auto_group P_auto_def is_P_auto_group_def 
     apply force
    apply(subgoal_tac "k \<in> nat", simp add:assms)
    using lt_nat_in_nat assms
    by auto 
  also have "... \<longleftrightarrow> (v \<in> \<G> \<and> Pn_auto(v)`x = x)" 
    apply(rule iffI, simp)
    apply(rule conjI, simp)
    apply(rule_tac x=x in bexI)
    using assms P_name_in_M 
    by auto
  also have "... \<longleftrightarrow> v \<in> sym(x)" 
    unfolding sym_def 
    apply force
    done
  finally show ?thesis by simp
qed
end

definition is_sym_fm where 
  "is_sym_fm(p, G, x, s) \<equiv> 
    Forall(Iff(Member(0, s #+ 1), is_sym_elem_fm(p #+ 1, G #+ 1, x #+ 1, 0)))" 


context M_symmetric_system
begin

lemma is_sym_fm_type : 
  fixes p G x s 
  assumes "p \<in> nat" "G \<in> nat" "x \<in> nat" "s \<in> nat" 
  shows "is_sym_fm(p, G, x, s) \<in> formula" 
  unfolding is_sym_fm_def 
  apply(clarify, rule Iff_type)
  using assms
   apply force
  apply(rule is_sym_elem_fm_type)
  using assms
  by auto

lemma arity_is_sym_fm : 
  fixes p G x s 
  assumes "p \<in> nat" "G \<in> nat" "x \<in> nat" "s \<in> nat" 
  shows "arity(is_sym_fm(p, G, x, s)) \<le> succ(p) \<union> succ(G) \<union> succ(x) \<union> succ(s)"

  apply(subgoal_tac "is_sym_elem_fm(p #+ 1, G #+ 1, x #+ 1, 0) \<in> formula")
  unfolding is_sym_fm_def 
  using assms
  apply simp
   apply(rule pred_le, simp_all)+
   apply(rule Un_least_lt)+
     apply simp
    apply(simp, rule ltI, simp, simp)
   apply(rule le_trans, rule arity_is_sym_elem_fm)
       apply auto[4]
   apply(subst succ_Un_distrib, simp_all)+
   apply(rule Un_least_lt)+
      apply(rule ltI, simp, simp)+
   apply(rule ltI, simp, rule disjI1, rule ltD, simp, simp)
  apply(rule is_sym_elem_fm_type)
  using assms 
  by auto

lemma sats_is_sym_fm_iff : 
  fixes env i j k l p G x s 
  assumes "env \<in> list(M)" "x \<in> P_names" "i < length(env)" "j < length(env)" "k < length(env)" "l < length(env)" 
          "nth(i, env) = P" "nth(j, env) = \<G>" "nth(k, env) = x" "nth(l, env) = s"  
  shows "sats(M, is_sym_fm(i, j, k, l), env) \<longleftrightarrow> s = sym(x)" 
proof - 

  have iff_lemma : "\<And>a b c. b = c \<Longrightarrow> a = b \<longleftrightarrow> a = c" by auto

  have innat : "i \<in> nat \<and> j \<in> nat \<and> k \<in> nat \<and> l \<in> nat" 
    using assms lt_nat_in_nat by auto

  have "(M, env \<Turnstile> is_sym_fm(i, j, k, l)) \<longleftrightarrow> (\<forall>\<pi> \<in> M. \<pi> \<in> s \<longleftrightarrow> \<pi> \<in> sym(x))" 
    unfolding is_sym_fm_def 
    apply(rule iff_trans, rule sats_Forall_iff, simp add:assms)
    apply(rule ball_iff, rule iff_trans, rule sats_Iff_iff, simp add:assms)
    apply(rule iff_iff)
    using assms innat 
     apply force
    apply(rule sats_is_sym_elem_fm_iff)
    using assms innat 
    by auto 
  also have "... \<longleftrightarrow> s = sym(x)" 
    apply(rule iffI, rule equality_iffI, rule iffI)
      apply(rename_tac \<tau>, subgoal_tac "\<tau> \<in> M", force)
      apply(subgoal_tac "s \<in> M")
    using transM assms nth_type
       apply auto[2]
    apply(rename_tac \<tau>, subgoal_tac "\<tau> \<in> M", force)
    using transM \<G>_in_M sym_def
     apply force
    by auto 
  finally show ?thesis by auto
qed

lemma sym_in_M : 
  fixes x
  assumes "x \<in> P_names" 
  shows "sym(x) \<in> M" 

proof - 

  define S where "S \<equiv> { v \<in> \<G>. sats(M, is_sym_elem_fm(1, 2, 3, 0), [v] @ [P, \<G>, x]) }" 

  have "separation(##M, \<lambda>v. sats(M, is_sym_elem_fm(1, 2, 3, 0), [v] @ [P, \<G>, x]))" 
    apply(rule separation_ax)
      apply(rule is_sym_elem_fm_type)
    using P_in_M \<G>_in_M assms P_name_in_M
         apply auto[5]
    apply(rule le_trans, rule arity_is_sym_elem_fm)
        apply auto[4]
    apply simp 
    apply(rule Un_least_lt)+
    by auto
  
  then have SinM : "S \<in> M"
    unfolding S_def 
    apply(rule separation_notation)
    using \<G>_in_M
    by auto 

  have "S = sym(x)" 
    unfolding S_def sym_def 
    apply(rule iff_eq)
    apply(rule iff_trans, rule sats_is_sym_elem_fm_iff)
    using assms \<G>_in_M transM P_in_M P_name_in_M 
              apply auto[10]
    unfolding sym_def 
    by auto
  then show ?thesis using SinM by auto
qed

end

(* 
  0 ... x 
  1 ... <\<F>, \<G>, P, P_auto>
  2 ... \<F> 
  3 ... <\<G>, P, P_auto> 
  4 ... \<G>
  5 ... <P, P_auto> 
  6 ... P 
  7 ... P_auto 
  8 ... domain(x) 
  9 ... sym(x) 
*) 

definition His_HS_M_cond_fm where 
  "His_HS_M_cond_fm(x', g) \<equiv> 
    Exists(Exists(Exists(Exists(Exists(Exists(Exists(Exists(Exists(Exists(
      And(pair_fm(0, 1, x' #+ 10), 
      And(pair_fm(2, 3, 1), 
      And(pair_fm(4, 5, 3), 
      And(pair_fm(6, 7, 5), 
      And(domain_fm(0, 8), 
      And(is_P_name_fm(6, 0), 
      And(apply_all_1_fm(g #+ 10, 8, 1), 
      And(is_sym_fm(6, 4, 0, 9), Member(9, 2)))))))))))))))))))" 


context M_symmetric_system
begin

lemma His_HS_M_cond_fm_type : 
  fixes x' g 
  assumes "x' \<in> nat" "g \<in> nat" 
  shows "His_HS_M_cond_fm(x', g) \<in> formula" 

  unfolding His_HS_M_cond_fm_def
  apply (rule Exists_type)+
  apply(rule And_type, simp)+
  apply(rule And_type, rule is_P_name_fm_type, simp, simp)
   apply(rule And_type, rule apply_all_1_fm_type, simp, simp, simp)
  apply(rule And_type, rule is_sym_fm_type)
  by auto

lemma arity_His_HS_M_cond_fm : 
  fixes x' g 
  assumes "x' \<in> nat" "g \<in> nat" 
  shows "arity(His_HS_M_cond_fm(x', g)) \<le> succ(x') \<union> succ(g)"

  unfolding His_HS_M_cond_fm_def 
  apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  using assms
  apply simp
  apply(subgoal_tac "apply_all_1_fm(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(natify(g))))))))))), 8, 1) \<in> formula") 
  apply(subgoal_tac "is_sym_fm(6, 4, 0, 9) \<in> formula")
  apply(subgoal_tac "is_P_name_fm(6, 0) \<in> formula")
    apply(rule_tac pred_le, simp_all)+
    apply(subst succ_Un_distrib, simp_all)+
    apply(rule Un_least_lt, rule ltI, simp, simp)
     apply(rule Un_least_lt, rule ltI, simp, rule disjI1, rule ltD, simp, simp)+
     apply(rule Un_least_lt, rule le_lt_lt, rule arity_is_P_name_fm, simp, simp)
      apply(rule Un_least_lt, rule ltI, simp, rule disjI1, rule ltD, simp, simp)
      apply(rule ltI, simp ,rule disjI1, rule ltD, simp, simp)
     apply(rule Un_least_lt, rule le_lt_lt, rule arity_apply_all_1_fm, simp, simp, simp)
      apply(rule Un_least_lt)+
        apply(rule ltI, simp, simp)
       apply(rule ltI, simp, rule disjI1, rule ltD, simp, simp)+
     apply(rule Un_least_lt)+
      apply(rule le_lt_lt)
       apply(rule arity_is_sym_fm)
          apply auto[4]
      apply(rule Un_least_lt)+
         apply(rule ltI, simp, rule disjI1, rule ltD, simp, simp)+
    apply(rule is_P_name_fm_type)
     apply auto[2]
   apply(rule is_sym_fm_type)
      apply auto[4]
  apply(rule apply_all_1_fm_type)
  using assms 
  by auto

end

definition His_HS_M_cond_fm_ren where "His_HS_M_cond_fm_ren(i, j) \<equiv> { <0, i>, <1, j> }" 
definition His_HS_M_cond_fm' where "His_HS_M_cond_fm'(i, j) \<equiv> ren(His_HS_M_cond_fm(0, 1))`2`(succ(i) \<union> succ(j))`His_HS_M_cond_fm_ren(i, j)" 

context M_symmetric_system
begin

lemma His_HS_M_cond_fm'_type : 
  fixes i j 
  assumes "i \<in> nat" "j \<in> nat"
  shows "His_HS_M_cond_fm'(i, j) \<in> formula" 
  unfolding His_HS_M_cond_fm'_def 
  apply(rule ren_tc)
     apply(rule His_HS_M_cond_fm_type)
  using assms 
      apply auto[4] 
  apply(rule Pi_memberI)
  unfolding relation_def function_def domain_def range_def His_HS_M_cond_fm_ren_def 
  by auto

lemma arity_His_HS_M_cond_fm' :  
  fixes i j 
  assumes "i \<in> nat" "j \<in> nat"
  shows "arity(His_HS_M_cond_fm'(i, j)) \<le> succ(i) \<union> succ(j)"
  unfolding His_HS_M_cond_fm'_def 
  apply(rule arity_ren)
      apply(rule His_HS_M_cond_fm_type)
  using assms 
       apply auto[4] 
   apply(rule Pi_memberI)
  unfolding relation_def function_def domain_def range_def His_HS_M_cond_fm_ren_def 
      apply auto[4]
  apply(rule le_trans, rule arity_His_HS_M_cond_fm)
    apply auto[2]
  apply(rule Un_least_lt)
  by auto

lemma sats_His_HS_M_cond_fm'_iff : 
  fixes env x' g i j 
  assumes "env \<in> list(M)" "i < length(env)" "j < length(env)" "nth(i, env) = x'" "nth(j, env) = g" 
  shows "sats(M, His_HS_M_cond_fm(0, 1), [x', g]) \<longleftrightarrow> sats(M, His_HS_M_cond_fm'(i, j), env)" 

  unfolding His_HS_M_cond_fm'_def
  apply(rule sats_iff_sats_ren)
         apply(rule His_HS_M_cond_fm_type)
  using assms nth_type  
          apply auto[6]
     apply(subgoal_tac "i \<in> nat \<and> j \<in> nat")
      apply force
  using lt_nat_in_nat 
     apply simp
  unfolding His_HS_M_cond_fm_ren_def 
    apply(rule Pi_memberI)
  unfolding relation_def function_def 
       apply auto[4]
   apply(rule le_trans, rule arity_His_HS_M_cond_fm, simp, simp)
   apply(rule Un_least_lt, simp, simp)
  apply(rename_tac k, subgoal_tac "k = 0 \<or> k = 1")
   apply auto[1]
    apply(rule_tac b="{\<langle>0, i\<rangle>, \<langle>1, j\<rangle>} ` 0" and a=i in ssubst)
     apply(rule function_apply_equality, simp, simp add:function_def, force, simp add:assms)
     apply(rule_tac b="{\<langle>0, i\<rangle>, \<langle>1, j\<rangle>} ` 1" and a=j in ssubst)
    apply(rule function_apply_equality, simp, simp add:function_def, force, simp add:assms)
  using le_iff 
  apply force
  done                            

end

definition His_HS_M_fm where "His_HS_M_fm(x', g, v) \<equiv> Forall(Iff(Member(0, v #+ 1), And(His_HS_M_cond_fm'(x' #+ 1, g #+ 1), empty_fm(0))))" 

context M_symmetric_system
begin

lemma His_HS_M_fm_type : 
  fixes x' g v 
  assumes "x' \<in> nat" "g \<in> nat" "v \<in> nat" 
  shows "His_HS_M_fm(x', g, v) \<in> formula" 
  unfolding His_HS_M_fm_def 
  apply(subgoal_tac "His_HS_M_cond_fm'(x' #+ 1, g #+ 1) \<in> formula")
   apply simp
  apply(rule His_HS_M_cond_fm'_type)
  using assms 
  by auto

lemma arity_His_HS_M_fm : 
  fixes x' g v 
  assumes "x' \<in> nat" "g \<in> nat" "v \<in> nat" 
  shows "arity(His_HS_M_fm(x', g, v)) \<le> succ(x') \<union> succ(g) \<union> succ(v)" 
  unfolding His_HS_M_fm_def 
  apply(subgoal_tac "His_HS_M_cond_fm'(succ(x'), succ(g)) \<in> formula")
  apply (simp add:assms)
   apply(rule pred_le)
     apply (rule union_in_nat)+
  using assms
       apply auto[4]
   apply(rule Un_least_lt)+
     apply (simp, rule ltI)
      apply(subst succ_Un_distrib, simp add:assms, simp add:assms)+
      apply (simp, rule disjI1, rule ltD, simp add:assms, simp add:assms)
    apply(subst succ_Un_distrib, simp add:assms, simp add:assms)+
    apply(rule ltI, simp, simp add:assms)
   apply(rule Un_least_lt, rule le_trans, rule arity_His_HS_M_cond_fm', simp add:assms, simp add:assms)
    apply(rule Un_least_lt)
     apply(subst succ_Un_distrib, simp add:assms, simp add:assms)+
     apply(rule ltI, simp, simp add:assms)
    apply(subst succ_Un_distrib, simp add:assms, simp add:assms)+
    apply(rule ltI, simp, simp add:assms)
   apply (subst arity_empty_fm, simp, simp)
  apply (rule ltI)
    apply(subst succ_Un_distrib, simp add:assms, simp add:assms)+
    apply(simp, rule disjI1, rule ltD, simp add:assms, simp add:assms)
  apply(rule His_HS_M_cond_fm'_type)
  using assms
  by auto

definition His_HS_M where                      
  "His_HS_M(x', g) = (if (sats(M, His_HS_M_cond_fm(0, 1), [x', g])) then 1 else 0)"  

lemma sats_His_HS_M_fm_iff : 
  fixes env i j k x' g v
  assumes "env \<in> list(M)" "i < length(env)" "j < length(env)" "k < length(env)" "nth(i, env) = x'" "nth(j, env) = g" "nth(k, env) = v"
  shows "sats(M, His_HS_M_fm(i, j, k), env) \<longleftrightarrow> v = His_HS_M(x', g)" 

proof - 
  have innat : "i \<in> nat \<and> j \<in> nat \<and> k \<in> nat" using assms lt_nat_in_nat by auto
  have inM : "x' \<in> M \<and> g \<in> M \<and> v \<in> M" using nth_type assms by auto

  have "sats(M, His_HS_M_fm(i, j, k), env) \<longleftrightarrow> 
        (\<forall>s \<in> M. s \<in> v \<longleftrightarrow> sats(M, His_HS_M_cond_fm'(i #+ 1, j #+ 1), Cons(s, env)) \<and> s = 0)" 
    unfolding His_HS_M_fm_def 
    apply(rule iff_trans, rule sats_Forall_iff, simp add:assms, rule ball_iff)
    apply(rule iff_trans, rule sats_Iff_iff, simp add:assms, rule iff_iff)
     apply(simp add:assms innat inM)
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI, simp)
    apply(rule iff_trans, rule sats_empty_fm, simp, simp add:assms)
    using assms 
    apply simp
    done

  also have "... \<longleftrightarrow> (\<forall>s \<in> M. s \<in> v \<longleftrightarrow> sats(M, His_HS_M_cond_fm(0, 1), [x', g]) \<and> s = 0)" 
    apply(rule ball_iff, rule iff_iff, simp, rule iff_conjI)
     apply(rule iff_flip, rule sats_His_HS_M_cond_fm'_iff)
    using assms innat inM
         apply auto[6]
    done

  also have "... \<longleftrightarrow> (\<forall>s. s \<in> v \<longleftrightarrow> sats(M, His_HS_M_cond_fm(0, 1), [x', g]) \<and> s = 0)" 
    apply(rule iffI, clarify, rule iffI)
      apply(rename_tac s, subgoal_tac "s \<in> M", force)
    using inM transM 
      apply force
    using zero_in_M 
     apply force
    apply auto
    done

  also have "... \<longleftrightarrow> v = His_HS_M(x', g)" 
    unfolding His_HS_M_def 
    by auto 

  finally show ?thesis by simp
qed

end

definition is_HS_fm where 
  "is_HS_fm(FGppauto, x) \<equiv> Exists(And(is_memrel_wftrec_fm(His_HS_M_fm(2, 1, 0), x #+ 1, FGppauto #+ 1, 0), is_1_fm(0)))" 

context M_symmetric_system
begin

lemma is_HS_fm_type : 
  fixes i j 
  assumes "i \<in> nat" "j \<in> nat" 
  shows "is_HS_fm(i, j) \<in> formula" 
  unfolding is_HS_fm_def 
  apply(rule Exists_type, rule And_type, rule is_memrel_wftrec_fm_type)
      apply(rule His_HS_M_fm_type)
  using assms is_1_fm_type 
  by auto

lemma arity_is_HS_fm : 
  fixes i j 
  assumes "i \<in> nat" "j \<in> nat" 
  shows "arity(is_HS_fm(i, j)) \<le> succ(i) \<union> succ(j)" 
  unfolding is_HS_fm_def
  apply simp
  apply(subgoal_tac "is_memrel_wftrec_fm(His_HS_M_fm(2, 1, 0), succ(natify(j)), succ(natify(i)), 0) \<in> formula")
  apply(subgoal_tac "is_1_fm(0) \<in> formula") 
    apply(rule pred_le, simp add:assms, rule union_in_nat)
  using assms 
      apply auto[2]
    apply(rule Un_least_lt)
  using assms 
     apply simp
     apply(subst succ_Un_distrib, simp add:assms, simp add:assms)
     apply(rule le_trans, rule arity_is_memrel_wftrec_fm)
          apply(rule His_HS_M_fm_type)
            apply auto[3]
         apply(rule le_trans, rule arity_His_HS_M_fm)
            apply auto[3]
         apply(rule Un_least_lt)+
           apply auto[6]
     apply(rule Un_least_lt)+
       apply(simp, rule ltI, simp, simp, simp, rule ltI, simp, simp, simp)
     apply(rule ltI, simp, rule disjI1, rule ltD, simp, simp)
    apply(subst arity_is_1_fm, simp, simp)
    apply(rule_tac j="succ(i)" in le_trans, simp, simp add:assms, simp, rule ltI, simp, simp add:assms)
   apply(rule_tac i=0 in is_1_fm_type, simp)
  apply(rule is_memrel_wftrec_fm_type)
     apply(rule His_HS_M_fm_type)
  using assms 
  by auto

definition His_HS where 
  "His_HS(x, g) \<equiv> if (x \<in> P_names \<and> (\<forall>y \<in> domain(x). g`y = 1) \<and> sym(x) \<in> \<F>) then 1 else 0" 

lemma His_HS_eq : 
    "\<And>h g u.
     u \<in> M \<Longrightarrow>
     h \<in> eclose(u) \<rightarrow> M \<Longrightarrow>
     g \<in> eclose(u) \<times> {<\<F>, \<G>, P, P_auto>} \<rightarrow> M \<Longrightarrow>
     g \<in> M \<Longrightarrow> (\<And>y. y \<in> eclose(u) \<Longrightarrow> h ` y = g ` \<langle>y, \<F>, \<G>, P, P_auto\<rangle>) \<Longrightarrow> His_HS(u, h) = His_HS_M(\<langle>u, \<F>, \<G>, P, P_auto\<rangle>, g)" 
proof - 
  fix h g u
  assume assms: "u \<in> M" "h \<in> eclose(u) \<rightarrow> M" "g \<in> eclose(u) \<times> {<\<F>, \<G>, P, P_auto>} \<rightarrow> M" "g \<in> M" 
                 "(\<And>y. y \<in> eclose(u) \<Longrightarrow> h ` y = g ` \<langle>y, \<F>, \<G>, P, P_auto\<rangle>)" 
 
  have "M, [\<langle>u, \<F>, \<G>, P, P_auto\<rangle>, g] \<Turnstile> His_HS_M_cond_fm(0, 1) \<longleftrightarrow> 
        (\<exists>symx \<in> M. \<exists>domx \<in> M. \<exists>pauto \<in> M. \<exists>p \<in> M. \<exists>ppauto \<in> M.  \<exists>G \<in> M.  \<exists>Gppauto \<in> M. \<exists>F \<in> M. \<exists>FGppauto \<in> M. \<exists>x \<in> M.
          \<langle>u, \<F>, \<G>, P, P_auto\<rangle> = <x, FGppauto> \<and> FGppauto = <F, Gppauto> \<and> Gppauto = <G, ppauto> \<and> ppauto = <p, pauto> \<and> 
          domx = domain(x) \<and> x \<in> P_names \<and> (\<forall>y. y \<in> domx \<longrightarrow> g`\<langle>y, \<F>, \<G>, P, P_auto\<rangle> = 1) \<and> symx = sym(x) \<and> symx \<in> \<F>)"   
    unfolding His_HS_M_cond_fm_def 
    apply(subgoal_tac "\<langle>u, \<F>, \<G>, P, P_auto\<rangle> \<in> M")
     apply(rule_tac iff_trans, rule_tac sats_Exists_iff, simp add:assms, rule_tac bex_iff)+
     apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2, simp add:assms)+
      apply(rename_tac symx domx pauto p ppauto G Gppauto F FGppauto x)
      apply(rule_tac b="forcing_data.P_names(p, M)" and a=P_names in ssubst, force)
      apply(rule sats_is_P_name_fm_iff)
    using assms
          apply auto[5]
     apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
      apply(rule sats_apply_all_1_fm_iff)
    using assms 
            apply auto[7]
     apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
      apply(rule sats_is_sym_fm_iff, simp add:assms)
    using assms
              apply auto[10]
    using assms \<F>_in_M \<G>_in_M P_in_M P_auto_in_M pair_in_M_iff 
    by auto 
  also have "... \<longleftrightarrow> u \<in> P_names \<and> (\<forall>y \<in> domain(u). g`\<langle>y, \<F>, \<G>, P, P_auto\<rangle> = 1) \<and> sym(u) \<in> \<F>" 
    apply(rule iffI, clarify)
    using pair_in_M_iff \<F>_in_M \<G>_in_M P_in_M P_auto_in_M assms domain_closed transM 
    by auto
  also have "... \<longleftrightarrow> u \<in> P_names \<and> (\<forall>y \<in> domain(u). h`y = 1) \<and> sym(u) \<in> \<F>" 
    apply(rule iff_conjI, simp, rule iff_conjI, rule ball_iff)
    using domain_elem_in_eclose assms 
     apply force
    by auto 
  finally show "His_HS(u, h) = His_HS_M(\<langle>u, \<F>, \<G>, P, P_auto\<rangle>, g)" 
    unfolding His_HS_def His_HS_M_def
    apply(rule_tac if_cong)
    by auto 
qed

definition is_HS where "is_HS(x) \<equiv> wftrec(Memrel(M)^+, x, His_HS)" 

lemma def_is_HS : 
  fixes x 
  assumes "x \<in> M" 
  shows "is_HS(x) = 1 \<longleftrightarrow> x \<in> HS" 

proof - 
  have "\<And>u. u \<in> M \<longrightarrow> is_HS(u) = 1 \<longleftrightarrow> u \<in> HS" 
  proof (rule_tac Q="\<lambda>u. u \<in> M \<longrightarrow> is_HS(u) = 1 \<longleftrightarrow> u \<in> HS" in ed_induction, rule impI)
    fix u 
    assume assms1: "(\<And>y. ed(y, u) \<Longrightarrow> y \<in> M \<longrightarrow> is_HS(y) = 1 \<longleftrightarrow> y \<in> HS)" "u \<in> M"

    define F where "F \<equiv> \<lambda>y \<in> Memrel(M)^+ -`` {u}. wftrec(Memrel(M)^+, y, His_HS)" 

    have iff_lemma : "\<And>a b c. a = b \<Longrightarrow> a = c \<longleftrightarrow> b = c" by auto

    have "is_HS(u) = 1 \<longleftrightarrow> His_HS(u, F) = 1"
      unfolding is_HS_def F_def
      apply(rule iff_lemma, rule wftrec)
       apply(rule wf_trancl, rule wf_Memrel, rule trans_trancl)
      done 
    also have "... \<longleftrightarrow> u \<in> P_names \<and> (\<forall>y \<in> domain(u). F`y = 1) \<and> sym(u) \<in> \<F>" 
      unfolding His_HS_def 
      apply(rule iffI, rule_tac a=1 and b=0 in ifT_eq, simp, simp, simp)
      done 
    also have "... \<longleftrightarrow> u \<in> P_names \<and> (\<forall>y \<in> domain(u). is_HS(y) = 1) \<and> sym(u) \<in> \<F>" 
      apply(rule iff_conjI, simp, rule iff_conjI, rule ball_iff)
       apply(rule iff_lemma)
      unfolding F_def is_HS_def 
       apply(rename_tac y, subgoal_tac "y \<in> Memrel(M)^+ -`` {u}", simp)
       apply(rule_tac b=u in vimageI, rule domain_elem_Memrel_trancl)
      using assms1 
      by auto 
    also have "... \<longleftrightarrow> u \<in> P_names \<and> (\<forall>y \<in> domain(u). y \<in> HS) \<and> sym(u) \<in> \<F>" 
      apply(rule iff_conjI, simp, rule iff_conjI, rule ball_iff)
      apply(rename_tac y, subgoal_tac "y \<in> M")
      using assms1 unfolding ed_def  
        apply blast
      using domain_elem_in_M assms1 
      by auto 
    also have "... \<longleftrightarrow> u \<in> HS"
      apply(rule iff_flip, rule iff_trans, rule HS_iff)
      unfolding symmetric_def 
      by auto 
    finally show "is_HS(u) = 1 \<longleftrightarrow> u \<in> HS" by simp
  qed
  then show ?thesis using assms by auto
qed

lemma sats_is_HS_fm_iff : 
  fixes x i j env 
  assumes "env \<in> list(M)" "i < length(env)" "j < length(env)" 
          "nth(i, env) = <\<F>, \<G>, P, P_auto>" "nth(j, env) = x" 
  shows "sats(M, is_HS_fm(i, j), env) \<longleftrightarrow> x \<in> HS" 

proof - 
  have innat : "i \<in> nat \<and> j \<in> nat" using lt_nat_in_nat assms by auto 

  have "sats(M, is_HS_fm(i, j), env) \<longleftrightarrow> (\<exists>v \<in> M. v = wftrec(Memrel(M)^+, x, His_HS) \<and> v = 1)" 
    unfolding is_HS_fm_def 
    apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI)
     apply(rule_tac a="<\<F>, \<G>, P, P_auto>" and G="His_HS_M" in sats_is_memrel_wftrec_fm_iff)
    using assms \<F>_in_M \<G>_in_M P_in_M P_auto_in_M pair_in_M_iff innat
                  apply auto[9]
    apply(rule His_HS_M_fm_type)
           apply auto[3]
        apply(rule le_trans, rule arity_His_HS_M_fm)
           apply auto[3]
        apply(rule Un_least_lt)+
          apply auto[3]
    using zero_in_M succ_in_MI 
       apply(simp add:His_HS_M_def)
      apply(rule His_HS_eq)
             apply auto[5]
     apply(rule iff_flip, rule sats_His_HS_M_fm_iff)
           apply auto[7]
    apply(rule sats_is_1_fm_iff)
    using assms 
    by auto
  also have "... \<longleftrightarrow> is_HS(x) = 1" unfolding is_HS_def by auto 
  also have "... \<longleftrightarrow> x \<in> HS" using def_is_HS assms nth_type by auto 
  finally show ?thesis by simp
qed

lemma HS_separation : 
  fixes A 
  assumes "A \<in> M" 
  shows "A \<inter> HS \<in> M" 
proof - 
  have sep : "separation(##M, \<lambda>x. sats(M, is_HS_fm(1, 0), [x] @ [<\<F>, \<G>, P, P_auto>]))"
    apply(rule separation_ax)
    apply(rule is_HS_fm_type)
    using assms \<F>_in_M \<G>_in_M P_in_M P_auto_in_M pair_in_M_iff  
       apply auto[4]
    apply(rule le_trans, rule arity_is_HS_fm, simp, simp)
    apply(rule Un_least_lt)
    by auto

  define S where "S \<equiv> { x \<in> A. sats(M, is_HS_fm(1, 0), [x] @ [<\<F>, \<G>, P, P_auto>]) }" 
  have SinM : "S \<in> M" 
    unfolding S_def 
    apply(rule separation_notation)
    using assms sep 
    by auto

  have "S = { x \<in> A. x \<in> HS }" 
    unfolding S_def
    apply(rule iff_eq)
    apply(rule sats_is_HS_fm_iff)
    using assms \<F>_in_M \<G>_in_M P_in_M P_auto_in_M pair_in_M_iff transM
        apply auto[5]
    done 

  also have "... = A \<inter> HS" by auto 

  finally show ?thesis using SinM by auto
qed
  
end
end
























