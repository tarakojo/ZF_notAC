theory Fn_Perm_Filter
  imports Fn_Perm_Automorphism
begin 

context M_ctm begin 

lemma Fn_perms_group : "forcing_data_partial.is_P_auto_group(Fn, Fn_leq, M, Fn_perms)" 
  apply(subst forcing_data_partial.is_P_auto_group_def)
   apply(rule Fn_forcing_data_partial, rule conjI)
   apply(subst Fn_perms_def)
  using Fn_perm'_type Fn_perm'_is_P_auto
   apply force
  apply(rule conjI)
   apply(subst Fn_perms_def)+
   apply clarsimp
   apply(rename_tac f f', rule_tac x="f O f'" in bexI)
    apply(rule Fn_perm'_comp)
  using nat_perms_def comp_closed comp_bij 
     apply auto[3]
  unfolding Fn_perms_def 
  apply(clarsimp)
  apply(rename_tac f, rule_tac x="converse(f)" in bexI)
   apply(rule Fn_perm'_converse)
  using converse_in_nat_perms
  by auto

definition Fix where "Fix(E) \<equiv> { Fn_perm'(f).. f \<in> nat_perms, \<forall>n \<in> E. f`n = n }"

definition is_Fix_elem_fm where "is_Fix_elem_fm(perms, fn, E, v) \<equiv> 
  Exists(And(Member(0, perms#+1), And(is_Fn_perm'_fm(0, fn#+1, v#+1), Forall(Implies(Member(0, E#+2), fun_apply_fm(1, 0, 0))))))"  

lemma is_Fix_elem_fm_type : 
  fixes i j k l 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" "l \<in> nat" 
  shows "is_Fix_elem_fm(i, j, k, l) \<in> formula" 
  apply(subgoal_tac "is_Fn_perm'_fm(0, j #+ 1, l#+1) \<in> formula")
  unfolding is_Fix_elem_fm_def
  apply force
  using is_Fn_perm'_fm_type assms
  by auto

lemma arity_is_Fix_elem_fm : 
  fixes i j k l 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" "l \<in> nat" 
  shows "arity(is_Fix_elem_fm(i, j, k, l)) \<le> succ(i) \<union> succ(j) \<union> succ(k) \<union> succ(l)"
  apply(subgoal_tac "is_Fn_perm'_fm(0, j #+ 1, l#+1) \<in> formula")
  unfolding is_Fix_elem_fm_def 
  using assms
  apply simp
   apply(rule pred_le, simp, simp)
   apply(rule Un_least_lt)+
     apply(simp, simp)
    apply(rule ltI, simp, simp)
   apply(rule Un_least_lt)+
    apply(rule le_trans, rule arity_is_Fn_perm'_fm)
       apply auto[3]
    apply(rule Un_least_lt)+
      apply (simp, simp)
     apply(rule ltI, simp, simp, simp)
  apply(rule union_lt2, simp, simp, simp, simp)
   apply(rule pred_le, simp, simp)
   apply(rule Un_least_lt)+
     apply(simp, simp)
    apply(rule ltI, simp, simp)
   apply(subst arity_fun_apply_fm, simp, simp)
   apply(rule Un_least_lt)+
  using is_Fn_perm'_fm_type assms
     apply auto
  done

lemma sats_is_Fix_elem_fm_iff : 
  fixes env i j k l E v 
  assumes "env \<in> list(M)" "i < length(env)" "j < length(env)" "k < length(env)" "l < length(env)"
          "nth(i, env) = nat_perms" "nth(j, env) = Fn" "nth(k, env) = E" "nth(l, env) = v" 
  shows "sats(M, is_Fix_elem_fm(i, j, k, l), env) \<longleftrightarrow> v \<in> Fix(E)" 
proof - 
  have I1:"sats(M, is_Fix_elem_fm(i, j, k, l), env) \<longleftrightarrow> (\<exists>f \<in> M. f \<in> nat_perms \<and> v = Fn_perm'(f) \<and> (\<forall>n \<in> M. n \<in> E \<longrightarrow> f`n = n))" 
    unfolding is_Fix_elem_fm_def
    apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
    using assms nth_type lt_nat_in_nat
     apply simp
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
     apply(rule sats_is_Fn_perm'_fm_iff)
    using assms nth_type lt_nat_in_nat
            apply auto[8]
    apply(rule iff_trans, rule sats_Forall_iff, simp add:assms, rule ball_iff)
    apply(rule iff_trans, rule sats_Implies_iff, simp add:assms, rule imp_iff2)
    using assms nth_type lt_nat_in_nat
     apply simp
    apply(rule iff_trans, rule sats_fun_apply_fm)
    using assms
    by auto
  have I2:"... \<longleftrightarrow> (\<exists>f. f \<in> nat_perms \<and> v = Fn_perm'(f) \<and> (\<forall>n \<in> M. n \<in> E \<longrightarrow> f`n = n))" 
    using nat_perms_in_M transM
    by auto
  have I3:"... \<longleftrightarrow> (\<exists>f. f \<in> nat_perms \<and> v = Fn_perm'(f) \<and> (\<forall>n \<in> E. f`n = n))" 
    using assms nth_type lt_nat_in_nat transM
    by auto
  have I4:"... \<longleftrightarrow> v \<in> Fix(E)" 
    unfolding Fix_def
    by auto
  show ?thesis using I1 I2 I3 I4 by auto
qed

lemma Fix_in_M : 
  fixes E 
  assumes "E \<in> M" 
  shows "Fix(E) \<in> M" 
proof - 
  define X where "X \<equiv> { \<pi> \<in> Fn_perms . sats(M, is_Fix_elem_fm(1,2,3,0), [\<pi>] @ [nat_perms, Fn, E]) }"

  have "X \<in> M" 
    unfolding X_def
    apply(rule separation_notation, rule separation_ax)
       apply(rule is_Fix_elem_fm_type)
    using assms nat_perms_in_M Fn_in_M 
          apply auto[5]
     apply(rule le_trans, rule local.arity_is_Fix_elem_fm)
    using Un_least_lt Fn_perms_in_M
    by auto
  have "X = { \<pi> \<in> Fn_perms . \<pi> \<in> Fix(E) }"
    unfolding X_def
    apply(rule iff_eq, rule sats_is_Fix_elem_fm_iff)
    using Fn_perms_in_M assms nat_perms_in_M Fn_in_M transM
    by auto
  also have "... = Fix(E)" 
    apply(rule equalityI, force)
    unfolding Fix_def Fn_perms_def
    by auto
  finally show ?thesis using \<open>X \<in> M\<close> by auto
qed

definition is_Fix_fm where "is_Fix_fm(perms, fn, E, v) \<equiv> Forall(Iff(Member(0, v#+1), is_Fix_elem_fm(perms#+1, fn#+1, E#+1, 0)))" 

lemma is_Fix_fm_type : 
  fixes i j k l 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" "l \<in> nat"
  shows "is_Fix_fm(i, j, k, l) \<in> formula" 

  unfolding is_Fix_fm_def
  apply(subgoal_tac "is_Fix_elem_fm(i #+ 1, j #+ 1, k #+ 1, 0) \<in> formula", force)
  apply(rule is_Fix_elem_fm_type)
  using assms
  by auto

lemma arity_is_Fix_fm : 
  fixes i j k l 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat" "l \<in> nat"
  shows "arity(is_Fix_fm(i, j, k, l)) \<le> succ(i) \<union> succ(j) \<union> succ(k) \<union> succ(l)"

  unfolding is_Fix_fm_def
  apply(subgoal_tac "is_Fix_elem_fm(i #+ 1, j #+ 1, k #+ 1, 0) \<in> formula")
  using assms
   apply simp
   apply(rule pred_le, simp, simp)
   apply(rule Un_least_lt)+
     apply (simp, simp)
    apply(rule ltI, simp, simp)
   apply(rule le_trans, rule arity_is_Fix_elem_fm)
       apply auto[4]
   apply(rule Un_least_lt)+
      apply(simp, rule ltI, simp, simp)+
   apply simp
  apply(rule is_Fix_elem_fm_type)
  using assms
  by auto

lemma sats_is_Fix_fm_iff : 
  fixes env i j k l E v 
  assumes "env \<in> list(M)" "i < length(env)" "j < length(env)" "k < length(env)" "l < length(env)"
          "nth(i, env) = nat_perms" "nth(j, env) = Fn" "nth(k, env) = E" "nth(l, env) = v" 
  shows "sats(M, is_Fix_fm(i, j, k, l), env) \<longleftrightarrow> v = Fix(E)" 
proof-
  have I1: "sats(M, is_Fix_fm(i, j, k, l), env) \<longleftrightarrow> (\<forall>u \<in> M. u \<in> v \<longleftrightarrow> u \<in> Fix(E))" 
    unfolding is_Fix_fm_def
    apply(rule iff_trans, rule sats_Forall_iff, simp add:assms, rule ball_iff)
    apply(rule iff_trans, rule sats_Iff_iff, simp add:assms, rule iff_iff)
    using assms nth_type lt_nat_in_nat
     apply force 
    apply(rule sats_is_Fix_elem_fm_iff)
    using assms nth_type lt_nat_in_nat
    by auto
  have I2: "... \<longleftrightarrow> (\<forall>u. u \<in> v \<longleftrightarrow> u \<in> Fix(E))" 
    apply(rule iffI)
    using assms nth_type lt_nat_in_nat transM Fix_in_M
     apply force 
    by auto
  have I3: "... \<longleftrightarrow> v = Fix(E)" by auto
  show ?thesis using I1 I2 I3 by auto
qed


schematic_goal converse_fm_auto:
  assumes
    "i \<in> nat"
    "j \<in> nat"
    "nth(i,env) = A"
    "nth(j,env) = B"
    "env \<in> list(M)" 
  shows "is_relation(##M, A) \<and> is_relation(##M, B) \<and> (\<forall>x \<in> M. \<forall>y \<in> M. (\<exists>z \<in> M. pair(##M, x, y, z) \<and> z \<in> A) \<longleftrightarrow> (\<exists>w \<in> M. pair(##M, y, x, w) \<and> w \<in> B)) \<longleftrightarrow> sats(M,?fm(i, j),env)" 
  by (insert assms ; (rule sep_rules | simp)+) 

definition converse_fm where "converse_fm(i, j) \<equiv> And(relation_fm(i),
                                                    And(relation_fm(j),
                                                        Forall
                                                         (Forall
                                                           (Iff(Exists(And(pair_fm(2, 1, 0), Member(0, succ(succ(succ(i)))))),
                                                                Exists(And(pair_fm(1, 2, 0), Member(0, succ(succ(succ(j))))))))))) "

lemma sats_converse_fm_iff : 
  fixes env i j A B 
  assumes "env \<in> list(M)" "i < length(env)" "j < length(env)" "nth(i, env) = A" "nth(j, env) = B" 
  shows "sats(M, converse_fm(i, j), env) \<longleftrightarrow> relation(A) \<and> relation(B) \<and> B = converse(A)" 
proof - 
  have I1: "sats(M, converse_fm(i, j), env) \<longleftrightarrow> is_relation(##M, A) \<and> is_relation(##M, B) \<and> (\<forall>x \<in> M. \<forall>y \<in> M. (\<exists>z \<in> M. pair(##M, x, y, z) \<and> z \<in> A) \<longleftrightarrow> (\<exists>w \<in> M. pair(##M, y, x, w) \<and> w \<in> B))" 
    unfolding converse_fm_def 
    apply(rule iff_flip, rule converse_fm_auto)
    using assms lt_nat_in_nat nth_type
    by auto
  have I2: "... \<longleftrightarrow> relation(A) \<and> relation(B) \<and> (\<forall>x \<in> M. \<forall> y \<in> M. <x, y> \<in> A \<longleftrightarrow> <y, x> \<in> B)" 
    using assms lt_nat_in_nat nth_type relation_abs pair_in_M_iff
    by auto
  have I3: "... \<longleftrightarrow> relation(A) \<and> relation(B) \<and> (\<forall>x. \<forall>y. <x, y> \<in> A \<longleftrightarrow> <y, x> \<in> B)" 
    apply(rule iffI, simp, rule allI, rule allI, rule iffI)
      apply(rename_tac x y, subgoal_tac "<x, y> \<in> M")
    using pair_in_M_iff
       apply force
    using assms lt_nat_in_nat nth_type transM 
      apply force
      apply(rename_tac x y, subgoal_tac "<y, x> \<in> M")
    using pair_in_M_iff
       apply force
    using assms lt_nat_in_nat nth_type transM 
     apply force
    by auto
  have I4: "... \<longleftrightarrow> relation(A) \<and> relation(B) \<and> B = converse(A)"
    apply (rule iffI)
     apply(simp, rule equality_iffI, rule iffI)
      apply(rename_tac x, subgoal_tac "\<exists>y z. x = <y, z>", force, simp add:relation_def)
     apply(rename_tac x, subgoal_tac "\<exists>y z. x = <y, z>", force, simp add:relation_def, force)
    by auto
  show ?thesis using I1 I2 I3 I4 by auto 
qed
   
schematic_goal closed_under_comp_fm_auto:
  assumes
    "i \<in> nat"
    "nth(i,env) = A"
    "env \<in> list(M)" 
 shows 
    "(\<forall>x \<in> M. \<forall>y \<in> M. x \<in> A \<longrightarrow> y \<in> A \<longrightarrow> (\<exists>z \<in> M. composition(##M, x, y, z) \<and> z \<in> A))
     \<longleftrightarrow> sats(M,?fm(i),env)" 
  unfolding is_converse_def 
  by (insert assms ; (rule sep_rules | simp)+) 
definition closed_under_comp_and_converse_fm where 
  "closed_under_comp_and_converse_fm(i) \<equiv> 
      And(Forall(Forall(Implies(Member(1, succ(succ(i))),
                        Implies(Member(0, succ(succ(i))), 
                        Exists(And(composition_fm(2, 1, 0), Member(0, succ(succ(succ(i)))))))))), 
          Forall(Implies(Member(0, succ(i)), Exists(And(Member(0, succ(succ(i))), converse_fm(1, 0))))))" 

lemma sats_closed_under_comp_and_converse_fm_iff : 
  fixes env i A
  assumes "env \<in> list(M)" "i < length(env)" "nth(i, env) = A" "\<And>x. x \<in> A \<Longrightarrow> relation(x)" 
  shows "sats(M, closed_under_comp_and_converse_fm(i), env) \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> A. x O y \<in> A) \<and> (\<forall>x \<in> A. converse(x) \<in> A)" 

proof - 
  have I1:"sats(M, closed_under_comp_and_converse_fm(i), env) \<longleftrightarrow> 
        (\<forall>x \<in> M. \<forall>y \<in> M. x \<in> A \<longrightarrow> y \<in> A \<longrightarrow> (\<exists>z \<in> M. composition(##M, x, y, z) \<and> z \<in> A)) \<and> 
        (\<forall>x \<in> M. x \<in> A \<longrightarrow> (\<exists>y \<in> M. y \<in> A \<and> y = converse(x)))"
    unfolding closed_under_comp_and_converse_fm_def 
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI)
    apply(rule iff_flip, rule closed_under_comp_fm_auto)
    using assms lt_nat_in_nat 
       apply auto[3]
    apply(rule iff_trans, rule sats_Forall_iff, simp add:assms, rule ball_iff)
    apply(rule iff_trans, rule sats_Implies_iff, simp add:assms, rule imp_iff2)
    using assms lt_nat_in_nat 
     apply simp
    apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
    using assms lt_nat_in_nat 
     apply simp
    apply(rule iff_trans, rule sats_converse_fm_iff)  
    using assms lt_nat_in_nat
    by auto
  also have I2: "... \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> A. x O y \<in> A) \<and> (\<forall>x \<in> A. converse(x) \<in> A)" 
    apply(rule iff_conjI)
    using transM nth_type lt_nat_in_nat assms comp_closed
     apply force
    using transM nth_type lt_nat_in_nat assms comp_closed converse_closed 
    apply force
    done
  show ?thesis using I1 I2 by auto
qed

lemma closed_under_comp_and_converse_fm_type : 
  fixes i 
  assumes "i \<in> nat" 
  shows "closed_under_comp_and_converse_fm(i) \<in> formula" 
  unfolding closed_under_comp_and_converse_fm_def converse_fm_def
  using assms
  by auto

lemma arity_closed_under_comp_and_converse_fm : 
  fixes i 
  assumes "i \<in> nat" 
  shows "arity(closed_under_comp_and_converse_fm(i)) \<le> succ(i)" 
  unfolding closed_under_comp_and_converse_fm_def converse_fm_def
  using assms 
  apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  done


definition Fn_perms_filter where "Fn_perms_filter \<equiv> { H \<in> forcing_data_partial.P_auto_subgroups(Fn, Fn_leq, M, Fn_perms).  \<exists>E \<in> Pow(nat) \<inter> M. finite_M(E) \<and> Fix(E) \<subseteq> H }" 

lemma Fn_perms_filter_in_M : "Fn_perms_filter \<in> M" 
proof - 
  define X where "X \<equiv> { H \<in> Pow(Fn_perms) \<inter> M. sats(M, And(closed_under_comp_and_converse_fm(0), Exists(Exists(And(Member(0, 3), And(finite_M_fm(6, 0), And(is_Fix_fm(4, 5, 0, 1), subset_fm(1, 2))))))), [H] @ [Pow(nat)\<inter>M, nat_perms, Fn, nat]) }" 

  have XinM: "X \<in> M" 
    unfolding X_def
       apply(subgoal_tac "finite_M_fm(6, 0) \<in> formula \<and> is_Fix_fm(4, 5, 0, 1) \<in> formula \<and> closed_under_comp_and_converse_fm(0) \<in> formula")
    apply(rule separation_notation, rule separation_ax, force)
    using nat_in_M nat_perms_in_M Fn_in_M M_powerset 
      apply force 
      apply simp
      apply(rule Un_least_lt, rule le_trans, rule arity_closed_under_comp_and_converse_fm, simp, simp)
      apply(rule pred_le, force, force)+
      apply(rule Un_least_lt)+
        apply auto[2]
      apply(rule Un_least_lt)
       apply(rule le_trans, rule arity_finite_M_fm)
    using Un_least_lt 
         apply auto[3]
      apply(rule Un_least_lt)
       apply(rule le_trans, rule arity_is_Fix_fm)
    using Un_least_lt Fn_perms_in_M M_powerset is_Fix_fm_type finite_M_fm_type closed_under_comp_and_converse_fm_type
           apply auto
    done

  have "X = { H \<in> Pow(Fn_perms) \<inter> M. ((\<forall>x \<in> H. \<forall>y \<in> H. x O y \<in> H) \<and> (\<forall>x \<in> H. converse(x) \<in> H)) \<and> (\<exists>F \<in> M. \<exists>E \<in> M. E \<in> Pow(nat) \<inter> M \<and> finite_M(E) \<and> F = Fix(E) \<and> F \<subseteq> H) }" 
    unfolding X_def
    apply(rule iff_eq)
    apply(insert M_powerset Fn_in_M nat_perms_in_M nat_in_M)
    apply(rule iff_trans, rule sats_And_iff, simp, rule iff_conjI)
     apply(rule sats_closed_under_comp_and_converse_fm_iff, simp, simp, simp)
    using Fn_perms_def relation_def Fn_perm'_def 
     apply force
    apply(rule iff_trans, rule sats_Exists_iff, force, rule bex_iff)+
    apply(rule iff_trans, rule sats_And_iff, force, rule iff_conjI2, simp)+
    apply(rule sats_finite_M_fm_iff, simp, simp, simp, simp, simp)
    apply(rule iff_trans, rule sats_And_iff, force, rule iff_conjI2, simp)+
     apply(rule sats_is_Fix_fm_iff)
             apply auto[9]
    apply(rule iff_trans, rule sats_subset_fm)
    using M_ctm_axioms M_ctm_def M_ctm_axioms_def 
    by auto
  also have "... = { H \<in> Pow(Fn_perms) \<inter> M. (\<forall>x \<in> H. \<forall>y \<in> H. x O y \<in> H) \<and> (\<forall>x \<in> H. converse(x) \<in> H) \<and> (\<exists>E \<in> Pow(nat) \<inter> M. finite_M(E) \<and> Fix(E) \<subseteq> H) }" 
    apply(rule iff_eq, rule iffI, force)
    using Fix_in_M
    by auto
  also have "... = Fn_perms_filter" 
    unfolding Fn_perms_filter_def
    apply(subst forcing_data_partial.P_auto_subgroups_def)
     apply(rule Fn_forcing_data_partial, simp)
    apply(rule iff_eq)
    apply(subst forcing_data_partial.is_P_auto_group_def)
     apply(rule Fn_forcing_data_partial, rule iffI)
     apply(rule conjI)+
       apply(rule subsetI, simp)
       apply(rename_tac H x, subgoal_tac "\<exists>f \<in> nat_perms. Fn_perm'(f) = x")
    using Fn_perm'_type Fn_perm'_is_P_auto Fn_perms_def
    by auto
    
  finally show ?thesis using \<open>X \<in> M\<close> by auto
qed

lemma Fn_perms_filter_nonempty : "Fn_perms_filter \<noteq> 0" 
  apply(rule_tac a="Fn_perms" in not_emptyI)
  unfolding Fn_perms_filter_def
  apply simp
  apply(rule conjI, subst forcing_data_partial.P_auto_subgroups_def, rule Fn_forcing_data_partial)
   apply (simp, rule conjI, rule Fn_perms_in_M, rule Fn_perms_group)
  apply(rule_tac x=0 in bexI, rule conjI, simp add:finite_M_def)
    apply(rule_tac x=0 in bexI, rule_tac a=0 in not_emptyI)
  using inj_def zero_in_M
     apply auto[2]
  unfolding Fix_def Fn_perms_def
   apply force
  using zero_in_M
  by auto

lemma Fix_subset : 
  fixes A B 
  assumes "A \<subseteq> B" 
  shows "Fix(B) \<subseteq> Fix(A)" 
  unfolding Fix_def 
  using assms
  by force


definition succ_fun where "succ_fun \<equiv> { <n, succ(n)> . n \<in> nat }"

lemma succ_fun_type : "succ_fun \<in> nat \<rightarrow> nat" 
  apply(rule Pi_memberI)
  unfolding relation_def succ_fun_def function_def
  by auto

lemma succ_fun_in_M : "succ_fun \<in> M"
proof - 
  define X where "X \<equiv> { v \<in> nat \<times> nat. sats(M, Exists(Exists(And(pair_fm(0, 1, 2), succ_fm(0, 1)))), [v] @ []) }"
  have "X \<in> M" 
    unfolding X_def
    apply(rule separation_notation)
     apply(rule separation_ax)
       apply auto[2]
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    using nat_in_M cartprod_closed 
    by auto
  have "X = { <n, succ(n)> . n \<in> nat }" 
    unfolding X_def
    apply(rule equality_iffI, rule iffI)
    using pair_in_M_iff nat_in_M transM
    by auto
  then show ?thesis using succ_fun_def \<open>X \<in> M\<close> by auto
qed

definition add_fun where "add_fun(m) \<equiv> { <n, n #+ m>. n \<in> nat }" 

lemma add_fun_type : "m \<in> nat \<Longrightarrow> add_fun(m) \<in> nat \<rightarrow> nat" 
  apply(rule Pi_memberI)
  unfolding add_fun_def relation_def function_def
  by auto

lemma add_fun_comp : 
  fixes m 
  assumes "m \<in> nat" 
  shows "add_fun(succ(m)) = add_fun(m) O succ_fun" 

  apply(rule function_eq)
  using relation_def add_fun_def succ_fun_def comp_def function_def
       apply auto[3]
    apply(subgoal_tac "add_fun(m) O succ_fun \<in> nat \<rightarrow> nat")
  using Pi_def
     apply force
    apply(rule_tac A=nat and B=nat and C=nat in comp_fun)
  using succ_fun_type add_fun_type assms 
     apply auto[2]
   apply(subst domain_comp_eq, subst succ_fun_def, subst add_fun_def)
  using succ_fun_def add_fun_def assms
    apply force
   apply(subst succ_fun_def, subst add_fun_def, force)
  apply(subst function_apply_equality, simp add:add_fun_def, force)
  using add_fun_type assms Pi_def
   apply force 
  apply(subst comp_fun_apply, rule succ_fun_type)
  using add_fun_def
   apply force
  apply(subst (2)function_apply_equality, simp add:succ_fun_def)
  using add_fun_def succ_fun_type Pi_def
    apply auto[2]
  apply(subst function_apply_equality, simp add:add_fun_def, force)
  using add_fun_type Pi_def assms
  by auto

lemma add_fun_in_M : 
  fixes m 
  assumes "m \<in> nat" 
  shows "add_fun(m) \<in> M" 
  using assms
  apply(induct)
  apply(rule_tac b = "add_fun(0)" and a="id(nat)" in ssubst)
  using add_fun_def id_def lam_def
    apply force 
  using id_closed nat_in_M 
   apply force
  apply(subst add_fun_comp)
  using comp_closed succ_fun_in_M 
  by auto
  
schematic_goal finite_M_union_h_elem_fm_auto:
  assumes
    "nth(0,env) = v"
    "nth(1,env) = A"
    "nth(2,env) = f"
    "nth(3,env) = g"
    "nth(4,env) = addn"
    "env \<in> list(M)" 
  shows "((\<exists>x \<in> M. \<exists>fx \<in> M. x \<in> A \<and> fun_apply(##M, f, x, fx) \<and> pair(##M, x, fx, v)) \<or> 
          (\<exists>x \<in> M. \<exists>gx \<in> M. \<exists>gxn \<in> M. x \<notin> A \<and> fun_apply(##M, g, x, gx) \<and> fun_apply(##M, addn, gx, gxn) \<and> pair(##M, x, gxn, v))) \<longleftrightarrow> sats(M,?fm,env)" 
  by (insert assms ; (rule sep_rules | simp)+) 

lemma finite_M_union : 
  fixes A B 
  assumes "A \<in> Pow(nat) \<inter> M" "B \<in> Pow(nat) \<inter> M" "finite_M(A)" "finite_M(B)" 
  shows "finite_M(A \<union> B)"
proof - 
  obtain n f where nfH: "n \<in> nat" "f \<in> M" "f \<in> inj(A, n)" using assms finite_M_def by force
  obtain m g where mgH: "m \<in> nat" "g \<in> M" "g \<in> inj(B, m)" using assms finite_M_def by force

  have subsetH : "n \<subseteq> n #+ m \<and> m \<subseteq> n #+ m" 
    apply(rule conjI, rule subsetI, rule ltD, rule_tac b=n in lt_le_lt, rule ltI, simp, simp add:nfH)
    using nfH mgH 
     apply force 
    apply(rule subsetI, rule ltD, rule_tac b=m in lt_le_lt, rule ltI, simp, simp add:mgH)
    using nfH mgH 
    apply force 
    done 

  have fvn: "\<And>x. x \<in> A \<Longrightarrow> f`x \<in> n" 
    apply(rule function_value_in) 
    using nfH inj_def 
    by auto
  have gvm: "\<And>x. x \<in> B \<Longrightarrow> g`x \<in> m" 
    apply(rule function_value_in) 
    using mgH inj_def 
    by auto
  then have gvnat: "\<And>x. x \<in> B \<Longrightarrow> g`x \<in> nat" 
    apply(rule_tac ltD)
    apply(rule_tac j=m in lt_trans, rule ltI)
    using mgH ltI
    by auto

  define h where "h \<equiv> { <a, if a \<in> A then f`a else n #+ g`a> . a \<in> A \<union> B }" 

  define hfm where "hfm \<equiv> Or(Exists(Exists(And(Member(1, 3), And(fun_apply_fm(4, 1, 0), pair_fm(1, 0, 2))))),
                            Exists(Exists(Exists(And(Neg(Member(2, 4)), And(fun_apply_fm(6, 2, 1), And(fun_apply_fm(7, 1, 0), pair_fm(2, 0, 3))))))))  "

  have "{ v \<in> (A \<union> B) \<times> (n #+ m). sats(M, hfm, [v] @ [A, f, g, add_fun(n)]) } = 
        { v \<in> (A \<union> B) \<times> (n #+ m). (\<exists>x \<in> M. \<exists>fx \<in> M. x \<in> A \<and> fun_apply(##M, f, x, fx) \<and> pair(##M, x, fx, v)) \<or> 
                                   (\<exists>x \<in> M. \<exists>gx \<in> M. \<exists>gxn \<in> M. x \<notin> A \<and> fun_apply(##M, g, x, gx) \<and> fun_apply(##M, add_fun(n), gx, gxn) \<and> pair(##M, x, gxn, v)) }" 
    (is "?A = _")
    
    unfolding hfm_def
    apply(rule iff_eq, rule iff_flip, rule finite_M_union_h_elem_fm_auto)
          apply auto[6]
    using assms nfH mgH add_fun_in_M cartprod_closed Un_closed nat_in_M transM 
    by auto
  also have "... = { v \<in> (A \<union> B) \<times> (n #+ m). (\<exists>x \<in> A. v = <x, f`x>) \<or> (\<exists>x \<in> B. x \<notin> A \<and> v = <x, g`x #+ n>) }" 
    apply(rule iff_eq)
    using assms nfH mgH transM add_fun_in_M apply_closed  cartprod_closed Un_closed nat_in_M
    apply simp
    apply(rule iff_disjI)
    using assms transM
     apply auto[1]
    apply(rule iffI, clarsimp, subst function_apply_equality, simp add:add_fun_def, rule conjI)
        apply(rule gvnat, simp, force)
    using add_fun_type Pi_def
      apply auto[2]
    apply clarsimp
    apply(subst function_apply_equality, simp add:add_fun_def, rule conjI)
       apply(rule gvnat, simp, force)
    using add_fun_type Pi_def
     apply auto[2]
    done
  also have "... = h" 
    unfolding h_def
    apply(rule equality_iffI, rule iffI, clarsimp)
     apply(rule disjE, assumption, simp)
      apply(rename_tac x y, rule_tac x=x in bexI, clarsimp, force)
     apply(rename_tac x y, rule_tac x=x in bexI, force, force)
    apply clarsimp
    apply(rule conjI, rule impI)
     apply(rule ltD, rule_tac b=n in lt_le_lt, rule ltI, rule fvn)
    using nfH mgH 
       apply auto[3]
    apply(rule impI, rule conjI, rule ltD, rule add_lt_mono2)
      apply(rule ltI, rule gvm)
    using mgH 
    by auto

  finally have "?A = h" by simp

  have "?A \<in> M" 
    apply(rule separation_notation, rule separation_ax)
    unfolding hfm_def
       apply force
    using mgH nfH add_fun_in_M assms
      apply force 
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    using assms nfH mgH transM add_fun_in_M apply_closed  cartprod_closed Un_closed nat_in_M
    apply simp
    done
  then have hinM: "h \<in> M" using \<open>?A = h\<close> by auto

  have htype: "h \<in> A \<union> B \<rightarrow> n #+ m"
    apply(rule Pi_memberI)
    using relation_def function_def h_def 
       apply auto[3]
    apply(rule subsetI)
    unfolding h_def
    apply clarsimp
    apply(rule conjI)
     apply(rule impI, rule_tac A=A in function_value_in)
      apply(rule Pi_memberI)
    using inj_def relation_def nfH Pi_def subsetH
         apply auto[5]
    apply(rule impI, rule ltD)
    using mgH gvnat 
    apply simp
    apply(rule add_lt_mono2, rule ltI)
    using mgH gvm 
    by auto
  have hinj: "\<And>x y. x \<in> A \<union> B \<Longrightarrow> y \<in> A \<union> B \<Longrightarrow> h`x = h`y \<longrightarrow> x = y" 
    apply(subst function_apply_equality)
      apply(simp add:h_def)
    using htype Pi_def
     apply force
    apply(subst (3) function_apply_equality)
      apply(simp add:h_def)
    using htype Pi_def
     apply force
    apply simp
    apply(rule conjI, rule impI)+
    using nfH inj_def 
      apply force
     apply(rule impI)+
     apply(rename_tac x y, subgoal_tac "f`x < n #+ g`y", force)
     apply(rule_tac b=n in lt_le_lt, rule ltI)
    using fvn nfH 
       apply (force, force, force)
    apply(rule impI, rule conjI)+
     apply(rule impI)
    apply(rename_tac x y, subgoal_tac "f`y < n #+ g`x", force)
     apply(rule_tac b=n in lt_le_lt, rule ltI)
    using fvn nfH 
       apply (force, force, force)
    using gvnat inj_def mgH 
    by auto

  have "h \<in> inj(A \<union> B, n #+ m)" using htype hinj inj_def by auto
  then show ?thesis 
    unfolding finite_M_def 
    apply(rule_tac x="n#+m" in bexI)
    using hinM mgH nfH
    by auto
qed

lemma Fn_perms_filter_subset : "Fn_perms_filter \<subseteq> Pow(Fn_perms) \<inter> M"
proof(rule subsetI)
  fix x assume "x \<in> Fn_perms_filter" 
  then have "x \<in> forcing_data_partial.P_auto_subgroups(Fn, Fn_leq, M, Fn_perms)" (is ?A)
    using Fn_perms_filter_def
    by auto
  have "?A \<longrightarrow> x \<subseteq> Fn_perms \<and> x \<in> M" 
    apply(subst forcing_data_partial.P_auto_subgroups_def)
     apply(rule Fn_forcing_data_partial)
    by auto
  then show "x \<in> Pow(Fn_perms) \<inter> M" 
    using \<open>?A\<close>
    by auto
qed

lemma Fn_perms_filter_intersection :
  fixes A B 
  assumes "A \<in> Fn_perms_filter" "B \<in> Fn_perms_filter" 
  shows "A \<inter> B \<in> Fn_perms_filter" 
proof- 
  obtain E where EH: "E \<in> Pow(nat) \<inter> M" "finite_M(E)" "Fix(E) \<subseteq> A"
    using Fn_perms_filter_def assms
    by auto
  obtain F where FH: "F \<in> Pow(nat) \<inter> M" "finite_M(F)" "Fix(F) \<subseteq> B"
    using Fn_perms_filter_def assms
    by auto

  define G where "G \<equiv> E \<union> F" 
  have H: "Fix(G) \<subseteq> A \<inter> B" 
  proof -
    have "Fix(G) \<subseteq> Fix(E) \<inter> Fix(F)" 
      using G_def Fix_subset
      by blast
    also have "... \<subseteq> A \<inter> B" 
      using EH FH 
      by blast
    finally show "Fix(G) \<subseteq> A \<inter> B" by auto
  qed

  show "A \<inter> B \<in> Fn_perms_filter" 
    unfolding Fn_perms_filter_def
    apply simp
    apply(rule conjI, subst forcing_data_partial.P_auto_subgroups_def, rule Fn_forcing_data_partial)
     apply simp
     apply(rule conjI)
    using assms Fn_perms_filter_subset 
      apply force
     apply(rule conjI)
    using assms int_closed Fn_perms_filter_in_M transM
      apply force
     apply(subst forcing_data_partial.is_P_auto_group_def)
      apply(rule Fn_forcing_data_partial, rule conjI, rule subsetI, simp, rule conjI)
    using assms Fn_perms_filter_subset Fn_perms_def Fn_perm'_type Fn_perm'_is_P_auto
       apply auto[2]
     apply(rule_tac P="A \<in> Fn_perms_filter \<and> B \<in> Fn_perms_filter" in mp) 
      apply(subst Fn_perms_filter_def, subst forcing_data_partial.P_auto_subgroups_def, rule Fn_forcing_data_partial)+
      apply simp
      apply(subst forcing_data_partial.is_P_auto_group_def, rule Fn_forcing_data_partial)+
      apply force
    using assms
     apply force
    apply(rule_tac x=G in bexI)
    using finite_M_union assms EH FH H Un_closed
    unfolding G_def
    by auto
qed

end
end