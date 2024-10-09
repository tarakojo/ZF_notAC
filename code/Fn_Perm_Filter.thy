theory Fn_Perm_Filter
  imports Fn_Perm_Automorphism
begin 

context M_symmetric_system_Fn_Perm_Automorphism begin 

definition is_Fix_elem_fm where "is_Fix_elem_fm(perms, fn, E, v) \<equiv> 
  Exists(And(Member(0, perms#+1), And(is_Fn_perm'_fm(0, fn#+1, v#+1), Forall(Implies(Member(0, E#+2), fun_apply_fm(1, 0, 0))))))"  


definition is_Fix_fm where "is_Fix_fm(perms, fn, E, v) \<equiv> Forall(Iff(Member(0, v#+1), is_Fix_elem_fm(perms#+1, fn#+1, E#+1, 0)))" 

definition converse_fm where "converse_fm(i, j) \<equiv> And(relation_fm(i),
                                                    And(relation_fm(j),
                                                        Forall
                                                         (Forall
                                                           (Iff(Exists(And(pair_fm(2, 1, 0), Member(0, succ(succ(succ(i)))))),
                                                                Exists(And(pair_fm(1, 2, 0), Member(0, succ(succ(succ(j))))))))))) "

definition closed_under_comp_and_converse_fm where 
  "closed_under_comp_and_converse_fm(i) \<equiv> 
      And(Forall(Forall(Implies(Member(1, succ(succ(i))),
                        Implies(Member(0, succ(succ(i))), 
                        Exists(And(composition_fm(2, 1, 0), Member(0, succ(succ(succ(i)))))))))), 
          Forall(Implies(Member(0, succ(i)), Exists(And(Member(0, succ(succ(i))), converse_fm(1, 0))))))" 

end

locale M_symmetric_system_Fn_Perm_Filter = M_symmetric_system_Fn_Perm_Automorphism + 
  assumes fn_perm_filer_Fix_in_M_fm : "is_Fix_elem_fm(1, 2, 3, 0) \<in> \<Phi>" 
  and fn_perm_filter_Fn_perms_filter_in_M_fm : "And(closed_under_comp_and_converse_fm(0),
        Exists(Exists(And(Member(0, 3), And(finite_M_fm(6, 0), And(is_Fix_fm(4, 5, 0, 1), subset_fm(1, 2))))))) \<in> \<Phi>"
begin
 
lemma Fn_perms_group : "forcing_data_Automorphism_M.is_P_auto_group(Fn, Fn_leq, M, Fn_perms)" 
  apply(subst forcing_data_Automorphism_M.is_P_auto_group_def)
   apply(rule Fn_forcing_data_Automorphism_M, rule conjI)
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
    using assms nat_perms_in_M Fn_in_M fn_perm_filer_Fix_in_M_fm
          apply auto[6]
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


definition Fn_perms_filter where "Fn_perms_filter \<equiv> { H \<in> forcing_data_Automorphism_M.P_auto_subgroups(Fn, Fn_leq, M, Fn_perms).  \<exists>E \<in> Pow(nat) \<inter> M. finite_M(E) \<and> Fix(E) \<subseteq> H }" 

lemma Fn_perms_filter_in_M : "Fn_perms_filter \<in> M" 
proof - 
  define X where "X \<equiv> { H \<in> Pow(Fn_perms) \<inter> M. sats(M, And(closed_under_comp_and_converse_fm(0), Exists(Exists(And(Member(0, 3), And(finite_M_fm(6, 0), And(is_Fix_fm(4, 5, 0, 1), subset_fm(1, 2))))))), [H] @ [Pow(nat)\<inter>M, nat_perms, Fn, nat]) }" 

  have XinM: "X \<in> M" 
    unfolding X_def
       apply(subgoal_tac "finite_M_fm(6, 0) \<in> formula \<and> is_Fix_fm(4, 5, 0, 1) \<in> formula \<and> closed_under_comp_and_converse_fm(0) \<in> formula")
     apply(rule separation_notation, rule separation_ax, force)
    using fn_perm_filter_Fn_perms_filter_in_M_fm
        apply force
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
    using trans_M
    by auto
  also have "... = { H \<in> Pow(Fn_perms) \<inter> M. (\<forall>x \<in> H. \<forall>y \<in> H. x O y \<in> H) \<and> (\<forall>x \<in> H. converse(x) \<in> H) \<and> (\<exists>E \<in> Pow(nat) \<inter> M. finite_M(E) \<and> Fix(E) \<subseteq> H) }" 
    apply(rule iff_eq, rule iffI, force)
    using Fix_in_M
    by auto
  also have "... = Fn_perms_filter" 
    unfolding Fn_perms_filter_def
    apply(subst forcing_data_Automorphism_M.P_auto_subgroups_def)
     apply(rule Fn_forcing_data_Automorphism_M, simp)
    apply(rule iff_eq)
    apply(subst forcing_data_Automorphism_M.is_P_auto_group_def)
     apply(rule Fn_forcing_data_Automorphism_M, rule iffI)
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
  apply(rule conjI, subst forcing_data_Automorphism_M.P_auto_subgroups_def, rule Fn_forcing_data_Automorphism_M)
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

lemma finite_M_implies_Finite : 
  fixes A 
  assumes "finite_M(A)" 
  shows "Finite(A)" 

  using assms
  unfolding finite_M_def 
  apply clarsimp
  apply(rename_tac n, rule_tac X=n in lepoll_Finite)
  using lepoll_def nat_into_Finite
  by auto

lemma finite_M_union : 
  fixes A B 
  assumes "A \<in> M" "B \<in> M" "finite_M(A)" "finite_M(B)" 
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

lemma Fn_perms_filter_supergroup : 
  fixes A B
  assumes "A \<in> Fn_perms_filter" "B \<in> forcing_data_partial.P_auto_subgroups(Fn, Fn_leq, M, Fn_perms)" "A \<subseteq> B" 
  shows "B \<in> Fn_perms_filter" 
  using assms
  unfolding Fn_perms_filter_def Fn_perms_filter_def
  by auto

definition normal_comp_elem_fm where 
  "normal_comp_elem_fm(X, Y, F) \<equiv> 
      Exists(Exists(
          And(converse_fm(F#+2, 0), 
          And(composition_fm(F#+2, X#+2, 1), 
              composition_fm(1, 0, Y#+2)))))" 

lemma sats_normal_comp_elem_fm : 
  fixes i j k X Y H env  
  assumes "i < length(env)" "j < length(env)" "k < length(env)" 
          "nth(i, env) = X" "nth(j, env) = Y" "nth(k, env) = F" 
          "env \<in> list(M)" "relation(F)" 
  shows "sats(M, normal_comp_elem_fm(i, j, k), env) \<longleftrightarrow> Y = F O X O converse(F)" 
  apply(rule_tac Q="\<exists>FX \<in> M. \<exists>Finv \<in> M. Finv = converse(F) \<and> FX = F O X \<and> Y = FX O Finv" in iff_trans)
  unfolding normal_comp_elem_fm_def 
  apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)+
  apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
   apply(rule iff_trans, rule sats_converse_fm_iff)
  using assms lt_nat_in_nat length_type relation_def converse_def
        apply auto[6]
  apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
  apply(rule iff_trans, rule sats_composition_fm)
  using assms lt_nat_in_nat length_type
       apply auto[5]
  apply(rule iff_trans, rule sats_composition_fm)
  using assms lt_nat_in_nat length_type comp_closed 
       apply auto[5]
  apply(rule iffI, force)
  apply(rule_tac x="F O X" in bexI)
   apply(rule_tac x="converse(F)" in bexI)
  using comp_assoc
    apply simp
  using assms lt_nat_in_nat nth_type length_type converse_closed comp_closed
   apply auto
  done

lemma normal_comp_closed : 
  fixes Y F 
  assumes "Y \<in> M" "F \<in> M" "relation(F)" 
  shows "{ F O X O converse(F). X \<in> Y } \<in> M"

  apply(rule to_rin, rule RepFun_closed)
    apply(rule iffD1, rule_tac P="\<lambda>X Y. sats(M, normal_comp_elem_fm(0, 1, 2), [X, Y] @ [F])" in strong_replacement_cong)
     apply(rule sats_normal_comp_elem_fm)
  using assms
            apply auto[8]
    apply(rule replacement_ax)
  unfolding normal_comp_elem_fm_def converse_fm_def composition_fm_def
  using assms
      apply auto[2]
  apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  using assms transM comp_closed converse_closed
  by auto

lemma Fn_perms_filter_normal : 
  fixes H F
  assumes "H \<in> Fn_perms_filter" "F \<in> Fn_perms" 
  shows "{ F O G O converse(F) . G \<in> H } \<in> Fn_perms_filter" 
proof - 
  obtain f where fH: "F = Fn_perm'(f)" "f \<in> nat_perms"
    using assms Fn_perms_def 
    by force

  define X where "X \<equiv> { F O G O converse(F) . G \<in> H }" 

  have XinM : "X \<in> M" 
    unfolding X_def
    apply(rule normal_comp_closed)
    using transM Fn_perms_in_M Fn_perms_filter_in_M assms relation_def Fn_perms_def Fn_perm'_def
    by auto

  have Xsubset: "X \<subseteq> Fn_perms" 
  proof(rule subsetI)
    fix x 
    assume "x \<in> X" 
    then obtain G where xH: "x = F O G O converse(F)" "G \<in> H" using X_def by force 
    then have "G \<in> Fn_perms" using assms Fn_perms_filter_subset by force 
    then obtain g where gH : "G = Fn_perm'(g)" "g \<in> nat_perms" using Fn_perms_def by force 
    then have "x = F O G O converse(F)" using xH by auto 
    also have "... = (Fn_perm'(f) O Fn_perm'(g)) O Fn_perm'(converse(f))" 
      using fH Fn_perm'_converse gH by auto
    also have "... = Fn_perm'(f O g) O Fn_perm'(converse(f))" 
      apply(subst Fn_perm'_comp)
      using gH converse_in_nat_perms fH
      by auto
    also have "... = Fn_perm'(f O g O converse(f))" 
      apply(subst Fn_perm'_comp)
        apply(simp add:nat_perms_def)
        apply(rule conjI, rule comp_bij)
      using gH fH nat_perms_def comp_closed converse_in_nat_perms comp_assoc
      by auto
    finally show "x \<in> Fn_perms" 
      unfolding Fn_perms_def
      apply simp
      apply(rule_tac x="f O g O converse(f)" in bexI)
       apply simp
      unfolding nat_perms_def 
      apply(simp, rule conjI)
       apply(rule comp_bij)+
      using converse_in_nat_perms fH gH nat_perms_def comp_closed converse_closed
         apply auto[4]
      done
  qed

  have Xsubset': "X \<subseteq> bij(Fn, Fn)" 
  proof(rule subsetI)
    fix x 
    assume "x \<in> X" 
    then have "x \<in> Fn_perms" using Xsubset by auto
    then obtain f where fH : "f \<in> nat_perms" "x = Fn_perm'(f)" using Fn_perms_def by force 
    then have "Fn_perm'(f) \<in> bij(Fn, Fn)" by(rule_tac Fn_perm'_bij)
    then show "x \<in> bij(Fn, Fn)" using fH by auto
  qed

  have Xsubset'': "\<And>x. x \<in> X \<Longrightarrow> forcing_data_partial.is_P_auto(Fn, Fn_leq, M, x)" 
    apply(subst forcing_data_partial.is_P_auto_def)
     apply(rule Fn_forcing_data_partial)
    apply(rule conjI)
    using transM XinM 
     apply force 
    apply(rule conjI)
    using Xsubset'
     apply force
    apply(rename_tac x, subgoal_tac "\<exists>f \<in> nat_perms. x = Fn_perm'(f)", clarsimp)
    using Fn_perm'_preserves_order Fn_perm'_preserves_order'
     apply force
    using Xsubset Fn_perms_def
    by auto

  have compin: "\<And>A B. A \<in> X \<Longrightarrow> B \<in> X \<Longrightarrow> A O B \<in> X"
  proof - 
    fix A B 
    assume assms1: "A \<in> X" "B \<in> X" 
    obtain S where SH: "A = F O S O converse(F)" "S \<in> H" 
      using assms1 X_def by auto
    obtain T where TH: "B = F O T O converse(F)" "T \<in> H" 
      using assms1 X_def by auto

    have"S \<in> Fn_perms" using SH assms Fn_perms_filter_subset by auto
    then have "S \<in> bij(Fn, Fn)" using Fn_perms_def Fn_perm'_bij by auto
    then have Ssubset : "S \<subseteq> Fn \<times> Fn" using bij_def inj_def Pi_def by force

    have "A O B = F O ((S O (converse(F) O F)) O T) O converse(F)"
      using SH TH comp_assoc by auto
    also have "... = F O ((S O (id(Fn))) O T) O converse(F)"
      apply(subst left_comp_inverse, rule bij_is_inj)
      using assms Fn_perms_def Fn_perm'_bij 
      by auto
    also have "... = F O (S O T) O converse(F)"
      apply(subst right_comp_id [where B=Fn])
       apply(rule Ssubset, simp)
      done
    finally show "A O B \<in> X" 
      apply (simp add:X_def)
      apply(rule_tac x="S O T" in bexI, simp)
      apply(rule_tac P="H \<in> forcing_data_partial.P_auto_subgroups(Fn, Fn_leq, M, Fn_perms)" in mp)
       apply(subst forcing_data_partial.P_auto_subgroups_def, rule Fn_forcing_data_partial, simp)
       apply(subst forcing_data_partial.is_P_auto_group_def, rule Fn_forcing_data_partial)
      using SH TH 
       apply force
      using assms Fn_perms_filter_def 
      by auto
  qed

  have conversein : "\<And>A. A \<in> X \<Longrightarrow> converse(A) \<in> X" 
  proof - 
    fix A 
    assume assms1 : "A \<in> X"
    obtain S where SH: "A = F O S O converse(F)" "S \<in> H" 
      using assms1 X_def by auto
    then have "converse(A) = converse(F O (S O converse(F)))" by auto 
    also have "... = converse(S O converse(F)) O converse(F)" by (subst converse_comp, simp)
    also have "... = (converse(converse(F)) O converse(S)) O converse(F)" by (subst converse_comp, simp)
    also have "... = F O converse(S) O converse(F)" using comp_assoc by auto
    finally show "converse(A) \<in> X" 
      apply(simp add:X_def)
      apply(rule_tac x="converse(S)" in bexI, simp)
      apply(rule_tac P="H \<in> forcing_data_partial.P_auto_subgroups(Fn, Fn_leq, M, Fn_perms)" in mp)
       apply(subst forcing_data_partial.P_auto_subgroups_def, rule Fn_forcing_data_partial, simp)
       apply(subst forcing_data_partial.is_P_auto_group_def, rule Fn_forcing_data_partial)
      using SH
       apply force
      using assms Fn_perms_filter_def 
      by auto
  qed

  have Xgroup : "forcing_data_partial.is_P_auto_group(Fn, Fn_leq, M, X)"
    apply(subst forcing_data_partial.is_P_auto_group_def)
    apply(rule Fn_forcing_data_partial)
    using Xsubset' Xsubset'' bij_def inj_def compin conversein
    by auto

  have Xsubgroup :"X \<in> forcing_data_partial.P_auto_subgroups(Fn, Fn_leq, M, Fn_perms)" 
    apply(subst forcing_data_partial.P_auto_subgroups_def)
     apply(rule Fn_forcing_data_partial)
    using Xsubset XinM Xgroup
    by auto

  obtain E where EH : "E \<in> Pow(nat) \<inter> M" "finite_M(E)" "Fix(E) \<subseteq> H" 
    using assms Fn_perms_filter_def
    by auto

  then obtain m e where meH: "m \<in> nat" "e \<in> inj(E, m)" "e \<in> M" using finite_M_def by force

  have imgsubset: "f``E \<subseteq> nat" 
  proof (rule subsetI)
    fix y assume "y \<in> f``E" 
    then obtain x where "<x, y> \<in> f" by auto
    then show "y \<in> nat" using fH nat_perms_def bij_def inj_def Pi_def by auto
  qed

  define e' where "e' \<equiv> e O converse(restrict(f, E))" 
  have e'in : "e' \<in> M" using e'_def comp_closed meH converse_closed fH nat_perms_def restrict_closed EH image_closed by auto

  have "e' \<in> inj(f``E, m)" 
    unfolding e'_def
    apply(rule_tac B=E in comp_inj)
     apply(rule bij_is_inj, rule bij_converse_bij)
     apply(rule restrict_bij, rule bij_is_inj)
    using fH nat_perms_def EH meH
    by auto

  then have imgfinite: "finite_M(f``E)" 
    unfolding finite_M_def
    using meH e'in 
    by force

  have fixsubset: "Fix(f``E) \<subseteq> X" 
  proof(rule subsetI)
    fix A assume assms1 : "A \<in> Fix(f``E)" 
    then obtain a where aH: "A = Fn_perm'(a)" "a \<in> nat_perms" "\<forall>n \<in> f``E. a`n = n" using Fix_def by auto
  
    define g where "g \<equiv> converse(f) O a O f" 
    have gin: "g \<in> nat_perms" 
      unfolding g_def 
      using composition_in_nat_perms fH aH converse_in_nat_perms
      by auto

    have "\<And>n. n \<in> E \<Longrightarrow> g`n = n"
    proof-  
      fix n assume nin : "n \<in> E" 
      have "g`n = ((converse(f) O a) O f) ` n" using g_def comp_assoc by simp
      also have "... = (converse(f) O a) ` (f ` n)" 
        apply(subst comp_fun_apply)
        using fH nat_perms_def bij_def inj_def 
          apply auto[1]
        using nin EH 
         apply force
        by simp
      also have "... = converse(f) ` (a ` (f ` n))"
        apply(subst comp_fun_apply)
        using aH nat_perms_def bij_def inj_def 
          apply auto[1]
         apply(rule function_value_in)
        using fH nat_perms_def bij_def inj_def 
          apply auto[1]
        using nin EH 
         apply force
        by simp
      also have "... = converse(f) ` (f ` n)" 
        apply(subgoal_tac "f ` n \<in> f `` E")
        using aH 
         apply force 
        apply(rule imageI, rule function_apply_Pair)
        using fH nat_perms_def bij_def inj_def Pi_def nin EH
        by auto
      also have "... = n"
        apply(rule left_inverse)
        using fH nat_perms_def bij_def
         apply force
        using nin EH
        by auto
      finally show "g`n = n" by auto
    qed
        
    then have gfix : "Fn_perm'(g) \<in> Fix(E)" 
      unfolding Fix_def 
      using gin
      by auto

    have "f O g O converse(f) = (f O converse(f)) O a O (f O converse(f))" 
      unfolding g_def
      using comp_assoc
      by auto
    also have "... = id(nat) O (a O id(nat))" 
      apply(subst right_comp_inverse)
      using fH nat_perms_def bij_def
      apply force
      apply(subst right_comp_inverse)
      using fH nat_perms_def bij_def
      by auto
    also have "... = id(nat) O a" 
      apply(subst right_comp_id)
      using aH nat_perms_def bij_def inj_def Pi_def
      by auto
    also have "... = a"
      apply(subst left_comp_id)
      using aH nat_perms_def bij_def inj_def Pi_def
      by auto
    finally have "a = f O g O converse(f)" by simp
    then have "Fn_perm'(a) = Fn_perm'(f O g O converse(f))" by simp
    then have "A = Fn_perm'(f O g O converse(f))" using aH by auto
    also have "... = Fn_perm'(f) O Fn_perm'(g O converse(f))" 
      apply(subst Fn_perm'_comp)
      using fH composition_in_nat_perms converse_in_nat_perms fH gin
      by auto
    also have "... = Fn_perm'(f) O Fn_perm'(g) O Fn_perm'(converse(f))" 
      apply(subst (2) Fn_perm'_comp)
      using fH composition_in_nat_perms converse_in_nat_perms fH gin
      by auto
    also have "... = Fn_perm'(f) O Fn_perm'(g) O converse(Fn_perm'(f))" 
      using Fn_perm'_converse fH converse_in_nat_perms
      by auto
    also have "... = F O Fn_perm'(g) O converse(F)" using fH by auto
    finally show "A \<in> X" 
      apply(simp add:X_def)
      apply(rule_tac x="Fn_perm'(g)" in bexI, simp)
      using gfix EH 
      by auto
  qed

  have "X \<in> Fn_perms_filter" 
    unfolding Fn_perms_filter_def 
    using Xsubgroup imgsubset fH EH nat_perms_def image_closed imgfinite fixsubset
    by force

  then show ?thesis 
    using X_def 
    by auto
qed

interpretation forcing_data_partial "Fn" "Fn_leq" "0" "M" "enum" using Fn_forcing_data_partial by auto

lemma Fn_M_symmetric_system : "M_symmetric_system(Fn, Fn_leq, 0, M, enum, Fn_perms, Fn_perms_filter)" 
  unfolding M_symmetric_system_def
  apply(rule conjI)
   apply(rule forcing_data_partial_axioms)
  unfolding M_symmetric_system_axioms_def 
  using Fn_perms_in_M Fn_perms_group Fn_perms_filter_in_M Fn_perms_filter_def
        Fn_perms_filter_nonempty Fn_perms_filter_intersection  
        Fn_perms_filter_supergroup Fn_perms_filter_normal
  by auto

end
end