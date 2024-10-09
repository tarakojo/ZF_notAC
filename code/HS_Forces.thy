theory HS_Forces 
  imports 
    SymExt_Definition 
    Delta0 
    "Forcing/Forcing_Theorems" 
begin
  
definition
  ren_forcesHS_forall :: "i\<Rightarrow>i" where
  "ren_forcesHS_forall(n) \<equiv> { <0, 1>, <1, 2>, <2, 3>, <3, 4>, <4, 5>, <5, 0> } \<union> { <k, k>.. k \<in> n, 6 \<le> k }" 

consts forcesHS' :: "i\<Rightarrow>i"
primrec
  "forcesHS'(Member(x,y)) = incr_bv(forces'(Member(x, y)))`4"
  "forcesHS'(Equal(x,y))  = incr_bv(forces'(Equal(x, y)))`4"
  "forcesHS'(Nand(p,q))   =
        Neg(Exists(And(Member(0,2),And(leq_fm(3,0,1),And(ren_forces_nand(forcesHS'(p)),
                                         ren_forces_nand(forcesHS'(q)))))))"
  "forcesHS'(Forall(p))   = Forall(Implies(is_HS_fm(5, 0), ren(forcesHS'(p))`(6\<union>arity(forcesHS'(p)))`(6\<union>arity(forcesHS'(p)))`ren_forcesHS_forall(arity(forcesHS'(p)))))"

definition
  forcesHS :: "i\<Rightarrow>i" where
  "forcesHS(\<phi>) \<equiv> And(Member(0,1),forcesHS'(\<phi>))"

locale M_symmetric_system_HS_Forces = M_symmetric_system_HS_M + forcing_data_Forces_Theorems  
locale M_symmetric_system_HS_Forces_G_generic = M_symmetric_system_HS_Forces + G_generic 

sublocale M_symmetric_system_HS_Forces_G_generic \<subseteq> M_symmetric_system_G_generic
  unfolding M_symmetric_system_G_generic_def
  using M_symmetric_system_HS_M_axioms G_generic_axioms
  by auto

context M_symmetric_system_HS_Forces begin 

abbreviation ForcesHS :: "[i, i, i] \<Rightarrow> o"  ("_ \<tturnstile>HS _ _" [36,36,36] 60) where
  "p \<tturnstile>HS \<phi> env   \<equiv>   M, ([p,P,leq,one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env) \<Turnstile> forcesHS(\<phi>)"

lemma ren_forcesHS_forall_type : 
  fixes n 
  assumes "n \<in> nat" 
  shows "ren_forcesHS_forall(n) \<in> (6\<union>n) \<rightarrow> (6\<union>n)" 

  apply(rule Pi_memberI)
  unfolding relation_def ren_forcesHS_forall_def function_def 
     apply auto[2]
   apply(rule equality_iffI, rule iffI, simp)
    apply(rename_tac k, case_tac "6 \<le> k")
     apply(rule disjI2)+
     apply(rename_tac k, subgoal_tac "k \<notin> 6")
      apply(force)
     apply(rule ccontr, simp)
     apply(rename_tac k, subgoal_tac "k < 6", force)
  using not_le_iff_lt 
     apply force
    apply(rename_tac k, subgoal_tac "k < 6")
  using le_iff 
     apply force 
    apply(rename_tac k, subgoal_tac "k \<in> nat")
  using not_le_iff_lt lt_nat_in_nat ltI 
     apply force 
    apply(rule disjE, assumption)
  using not_le_iff_lt lt_nat_in_nat ltI assms
     apply force 
    apply(rule_tac n=n in lt_nat_in_nat, rule ltI)
  using assms
      apply auto[5]
  done

lemma sats_ren_forcesHS_forall_iff : 
  fixes \<phi> n a b c d e f env
  assumes "\<phi> \<in> formula" "arity(\<phi>) \<le> 6 \<union> n" "n \<in> nat" "a \<in> M" "b \<in> M" "c \<in> M" "d \<in> M" "e \<in> M" "f \<in> M" "env \<in> list(M)"
  shows "sats(M, \<phi>, [a, b, c, d, e, f] @ env) \<longleftrightarrow> sats(M, ren(\<phi>)`(6\<union>n)`(6\<union>n)`ren_forcesHS_forall(n), [f, a, b, c, d, e] @ env)"

  apply(rule sats_iff_sats_ren)
  using assms
         apply auto[5]
    apply(rule ren_forcesHS_forall_type)
  using assms 
    apply auto[2]
  apply(rename_tac k, subgoal_tac "k \<in> 6 \<or> k \<in> n")
   apply(rename_tac k, case_tac "k \<in> 6", simp)
    apply(rename_tac k, subgoal_tac "k < 6")
     apply(rename_tac k, subgoal_tac "k = 0 \<or> k = 1 \<or> k = 2 \<or> k = 3 \<or> k = 4 \<or> k = 5") 
      apply(subgoal_tac "function(ren_forcesHS_forall(n))")
  unfolding ren_forcesHS_forall_def
      apply(rule disjE, assumption, subst function_apply_equality, simp, assumption, simp, simp)
       apply(rule disjE, assumption, subst function_apply_equality, rule UnI1, simp, assumption, simp, simp)+
       apply(subst function_apply_equality, rule UnI1, simp, assumption, force)
  using ren_forcesHS_forall_type assms Pi_def ren_forcesHS_forall_def 
      apply force 
  using le_iff 
     apply force 
    apply(rule ltI, simp, simp)
  apply(rename_tac k, subgoal_tac "5 < k")
    apply(subst function_apply_equality, rule UnI2, force)
  using ren_forcesHS_forall_type assms Pi_def ren_forcesHS_forall_def 
     apply force 
    apply(subst nth_append)
  using assms lt_nat_in_nat assms
      apply auto[2]
    apply(subst (1) nth_append)
  using assms lt_nat_in_nat assms
      apply auto[2]
    apply(subst if_not_P, simp)
  apply(rule iffD2, rule not_le_iff_lt)
  using assms lt_nat_in_nat assms
       apply auto[3]
    apply(subst if_not_P, simp)
  apply(rule iffD2, rule not_le_iff_lt)
  using assms lt_nat_in_nat assms
       apply auto[4]
   apply(rule ccontr)
   apply(rename_tac k, subgoal_tac "k \<le> 5")
  using ltD 
    apply force
  apply(rule iffD1, rule not_lt_iff_le)
  using assms lt_nat_in_nat assms
     apply auto[3]
  apply(rename_tac k, subgoal_tac "k \<in> 6 \<union> n", force)
  apply(rule ltD, simp)
  done

lemma forcesHS'_type : 
  fixes \<phi>
  assumes "\<phi> \<in> formula" 
  shows "forcesHS'(\<phi>) \<in> formula" 
  using assms
  apply(induct)
     apply auto[3]
  apply simp
  apply(clarify, rule Implies_type)
   apply(rule is_HS_fm_type)
    apply auto[2]
  apply(rule ren_tc)
  using assms
     apply auto[3]
  apply(rule ren_forcesHS_forall_type)
  by simp

lemma forcesHS_type : 
  fixes \<phi>
  assumes "\<phi> \<in> formula" 
  shows "forcesHS(\<phi>) \<in> formula" 
  unfolding forcesHS_def
  apply(rule And_type, simp)
  using forcesHS'_type assms
  by auto

lemma arity_forcesHS' : 
  fixes \<phi>
  assumes "\<phi> \<in> formula" 
  shows "arity(forcesHS'(\<phi>)) \<le> arity(\<phi>) #+ 5" 
  using assms
  apply(induct)
  apply simp 
     apply(subst arity_incr_bv_lemma)
       apply(rule forces_mem_fm_type)
           apply auto[6]
     apply (subst if_P, subst arity_forces_mem_fm)
           apply auto[5]
      apply(rule ltI, simp, rule disjI1, rule ltD, simp, simp, simp)
     apply(subst arity_forces_mem_fm)
          apply auto[5]
     apply(subst succ_Un_distrib, simp, simp)+
     apply(rule Un_least_lt)+
         apply(rule ltI, simp, simp)+
       apply(rule ltI, simp, rule disjI1, rule ltD, simp, simp)+
  apply simp 
     apply(subst arity_incr_bv_lemma)
       apply(rule forces_eq_fm_type)
           apply auto[6]
     apply (subst if_P, subst arity_forces_eq_fm)
           apply auto[5]
      apply(rule ltI, simp, rule disjI1, rule ltD, simp, simp, simp)
     apply(subst arity_forces_eq_fm)
          apply auto[5]
     apply(subst succ_Un_distrib, simp, simp)+
     apply(rule Un_least_lt)+
         apply(rule ltI, simp, simp)+
      apply(rule ltI, simp, rule disjI1, rule ltD, simp, simp)+
   apply simp
   apply(rule pred_le)
     apply(rule union_in_nat, simp)+
     apply(rule union_in_nat, rule arity_type, rule ren_forces_nand_type, rule forcesHS'_type, simp)
     apply(rule arity_type, rule ren_forces_nand_type, rule forcesHS'_type, simp)
    apply simp
   apply(rule Un_least_lt)+
     apply auto[2]
   apply(rule Un_least_lt)+
    apply(subst arity_leq_fm)
       apply auto[3]
    apply(rule Un_least_lt)+
      apply auto[3]
   apply(rule Un_least_lt)+ 
    apply(rule le_trans, rule arity_ren_forces_nand, rule forcesHS'_type, simp, simp)
    apply(subst succ_Un_distrib, simp, simp)+
    apply(rule ltI, simp ,rule disjI1, rule ltD, simp, simp)
   apply(rule_tac le_trans, rule arity_ren_forces_nand, rule forcesHS'_type, simp, simp)
   apply(subst succ_Un_distrib, simp, simp)+
   apply(rule ltI, simp ,rule disjI2, rule ltD, simp, simp)
  apply simp
  apply(rename_tac p, subgoal_tac "forcesHS'(p) \<in> formula \<and> is_HS_fm(5, 0) \<in> formula \<and> ren(forcesHS'(p)) ` (6 \<union> arity(forcesHS'(p))) ` (6 \<union> arity(forcesHS'(p))) ` ren_forcesHS_forall(arity(forcesHS'(p))) \<in> formula")
   apply(rule pred_le, force, simp)
   apply(rule Un_least_lt)
    apply(rule le_trans, rule arity_is_HS_fm, simp, simp)
    apply(rule Un_least_lt, simp, simp)
   apply(rule le_trans, rule arity_ren, simp)
       apply(rule union_in_nat, simp, force)+
     apply(rule ren_forcesHS_forall_type)
     apply force
    apply(rule max_le2, simp, force)
   apply(rule Un_least_lt, simp)
   apply(rename_tac p, rule_tac n="arity(p)" in natE, simp, simp)
    apply(rule_tac j=5 in le_trans, simp, simp)
   apply force 
  apply(rule conjI, rule forcesHS'_type, simp, rule conjI, rule is_HS_fm_type, simp, simp)
  apply(rule ren_tc, rule forcesHS'_type, simp)
    apply(rule union_in_nat, simp, rule arity_type, rule forcesHS'_type, simp)+
  apply(rule ren_forcesHS_forall_type)
  apply(rule arity_type, rule forcesHS'_type, simp)
  done

lemma arity_forcesHS : 
  fixes \<phi>
  assumes "\<phi> \<in> formula" 
  shows "arity(forcesHS(\<phi>)) \<le> arity(\<phi>) #+ 5" 
  unfolding forcesHS_def 
  using forcesHS'_type assms 
  apply simp
  apply(rule Un_least_lt)+
    apply auto[2]
  using arity_forcesHS' assms
  by auto

lemma sats_forcesHS_Member :
  assumes  "x\<in>nat" "y\<in>nat" "env\<in>list(M)" "A \<in> M" "q\<in>M"
  shows "sats(M,forcesHS(Member(x,y)),[q,P,leq,one,A]@env) \<longleftrightarrow>
         sats(M,forces(Member(x,y)),[q,P,leq,one]@env)" 
  apply(subgoal_tac "P \<in> M \<and> leq \<in> M \<and> one \<in> M")
  unfolding forcesHS_def forces_def 
  using assms
   apply simp
   apply(rule iff_conjI2, simp)
   apply(rule_tac Q="M, [q, P, leq, one] @ Cons(A, env) \<Turnstile> 
                      incr_bv(forces_mem_fm(1, 2, 0, succ(succ(succ(succ(x)))), succ(succ(succ(succ(y)))))) ` length([q, P, leq, one])" in iff_trans)
  apply force 
   apply(rule iff_trans, rule sats_incr_bv_iff)
       apply auto[5]
  using P_in_M leq_in_M one_in_M
  by auto

lemma ForcesHS_Member : 
  fixes x y env p
  assumes "x\<in>nat" "y\<in>nat" "env\<in>list(M)" "p \<in> M"
  shows "p \<tturnstile> Member(x, y) env \<longleftrightarrow> p \<tturnstile>HS Member(x, y) env" 
  apply(rule iff_flip, rule sats_forcesHS_Member)
  using assms
      apply auto[2]
  using assms \<F>_in_M \<G>_in_M P_auto_in_M P_in_M pair_in_M_iff
  by auto

lemma sats_forcesHS_Equal :
  assumes  "x\<in>nat" "y\<in>nat" "env\<in>list(M)" "A \<in> M" "q\<in>M"
  shows "sats(M,forcesHS(Equal(x,y)),[q,P,leq,one,A]@env) \<longleftrightarrow>
         sats(M,forces(Equal(x,y)),[q,P,leq,one]@env)"
  apply(subgoal_tac "P \<in> M \<and> leq \<in> M \<and> one \<in> M")
  unfolding forcesHS_def forces_def 
  using assms
   apply simp
   apply(rule iff_conjI2, simp)
   apply(rule_tac Q="M, [q, P, leq, one] @ Cons(A, env) \<Turnstile> 
                      incr_bv(forces_eq_fm(1, 2, 0, succ(succ(succ(succ(x)))), succ(succ(succ(succ(y)))))) ` length([q, P, leq, one])" in iff_trans)
    apply force 
   apply(rule iff_trans, rule sats_incr_bv_iff)
       apply auto[5]
  using P_in_M leq_in_M one_in_M
  by auto

lemma ForcesHS_Equal : 
  fixes x y env p
  assumes "x\<in>nat" "y\<in>nat" "env\<in>list(M)" "p \<in> M"
  shows "p \<tturnstile> Equal(x, y) env \<longleftrightarrow> p \<tturnstile>HS Equal(x, y) env" 
  apply(rule iff_flip, rule sats_forcesHS_Equal)
  using assms
      apply auto[2]
  using assms \<F>_in_M \<G>_in_M P_auto_in_M P_in_M pair_in_M_iff
  by auto

lemma sats_forcesHS_Nand :
  assumes  "\<phi>\<in>formula" "\<psi>\<in>formula" "env\<in>list(M)" "p\<in>M" "A \<in> M" 
  shows "sats(M,forcesHS(Nand(\<phi>,\<psi>)),[p,P,leq,one,A]@env) \<longleftrightarrow>
         (p\<in>P \<and> \<not>(\<exists>q\<in>M. q\<in>P \<and> is_leq(##M,leq,q,p) \<and>
               (sats(M,forcesHS'(\<phi>),[q,P,leq,one,A]@env) \<and> sats(M,forcesHS'(\<psi>),[q,P,leq,one,A]@env))))"
  unfolding forcesHS_def using sats_leq_fm assms P_in_M leq_in_M one_in_M
  apply simp 
  apply(rule iff_conjI2, simp)
  apply(rule ball_iff, rule iff_disjI, simp, rule iff_disjI, simp, rule iff_disjI)
   apply(rule notnot_iff)
  apply(rename_tac x, subgoal_tac "M, [x, p, P, leq, one] @ ([A] @ env) \<Turnstile> ren_forces_nand(forcesHS'(\<phi>)) \<longleftrightarrow>
                                   M, [x, P, leq, one] @ ([A] @ env) \<Turnstile> forcesHS'(\<phi>)")
    apply force 
   apply(rule sats_ren_forces_nand, force, rule forcesHS'_type, simp)
   apply(rule notnot_iff)
  apply(rename_tac x, subgoal_tac "M, [x, p, P, leq, one] @ ([A] @ env) \<Turnstile> ren_forces_nand(forcesHS'(\<psi>)) \<longleftrightarrow>
                                   M, [x, P, leq, one] @ ([A] @ env) \<Turnstile> forcesHS'(\<psi>)")
    apply force 
  apply(rule sats_ren_forces_nand, force, rule forcesHS'_type, simp)
  done

lemma sats_forcesHS_Nand':
  assumes
    "p\<in>P" "\<phi>\<in>formula" "\<psi>\<in>formula" "env \<in> list(M)" 
  shows
    "M, [p,P,leq,one,<\<F>, \<G>, P, P_auto>] @ env \<Turnstile> forcesHS(Nand(\<phi>,\<psi>)) \<longleftrightarrow> 
     \<not>(\<exists>q\<in>M. q\<in>P \<and> is_leq(##M,leq,q,p) \<and> 
           M, [q,P,leq,one,<\<F>, \<G>, P, P_auto>] @ env \<Turnstile> forcesHS(\<phi>) \<and> 
           M, [q,P,leq,one,<\<F>, \<G>, P, P_auto>] @ env \<Turnstile> forcesHS(\<psi>))"
  apply(subgoal_tac "P \<in> M \<and> leq \<in> M \<and> one \<in> M \<and> <\<F>, \<G>, P, P_auto> \<in> M")
  using assms sats_forcesHS_Nand[OF assms(2-4) transitivity[OF \<open>p\<in>P\<close>]] P_in_M leq_in_M one_in_M 
  unfolding forcesHS_def
   apply simp
  using P_in_M leq_in_M one_in_M \<F>_in_M \<G>_in_M P_auto_in_M pair_in_M_iff
  by auto

lemma ForcesHS_Nand:
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula"
  shows
    "(p \<tturnstile>HS Nand(\<phi>,\<psi>) env) \<longleftrightarrow> \<not>(\<exists>q\<in>M. q\<in>P \<and> q\<preceq>p \<and> (q \<tturnstile>HS \<phi> env) \<and> (q \<tturnstile>HS \<psi> env))"
  using assms sats_forcesHS_Nand' transitivity P_in_M pair_in_M_iff leq_in_M leq_abs 
  by simp

lemma ForcesHS_Neg:
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula" 
  shows
    "(p \<tturnstile>HS Neg(\<phi>) env) \<longleftrightarrow> \<not>(\<exists>q\<in>M. q\<in>P \<and> q\<preceq>p \<and> (q \<tturnstile>HS \<phi> env))"
  unfolding Neg_def
  using assms sats_forcesHS_Nand' transitivity P_in_M pair_in_M_iff leq_in_M leq_abs
  by simp

lemma sats_forcesHS_Forall :
  assumes  "\<phi>\<in>formula" "env\<in>list(M)" "p\<in>M"  
  shows "sats(M,forcesHS(Forall(\<phi>)),[p,P,leq,one,<\<F>, \<G>, P, P_auto>]@env) \<longleftrightarrow>
         p\<in>P \<and> (\<forall>x\<in>HS. sats(M,forcesHS'(\<phi>),[p,P,leq,one,<\<F>, \<G>, P, P_auto>,x]@env))"
  unfolding forcesHS_def 
  using assms P_in_M leq_in_M one_in_M
  apply(subgoal_tac "<\<F>, \<G>, P, P_auto> \<in> M")
  apply simp
   apply(rule iff_conjI2, simp, rule iffI, rule ballI)
    apply(rename_tac x, subgoal_tac "M, [p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>, x] @ env \<Turnstile> forcesHS'(\<phi>)", force)
    apply(rule iffD2, rule_tac n="arity(forcesHS'(\<phi>))" in sats_ren_forcesHS_forall_iff)
              apply(rule forcesHS'_type, simp, rule max_le2, simp)
  using forcesHS'_type arity_type pair_in_M_iff HS_iff P_name_in_M
             apply auto[9]
    apply(rename_tac x, subgoal_tac "M, Cons(x, Cons(p, Cons(P, Cons(leq, Cons(one, Cons(\<langle>\<F>, \<G>, P, P_auto\<rangle>, env)))))) \<Turnstile> is_HS_fm(5, 0)")
  using HS_iff P_name_in_M 
     apply force  
    apply(rule iffD2, rule sats_is_HS_fm_iff)
  using HS_iff P_name_in_M 
         apply auto[6]
   apply(rule ballI, rule impI)
  apply(rename_tac x, 
        subgoal_tac " M, [x, p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env \<Turnstile> 
                        ren(forcesHS'(\<phi>)) ` (6 \<union> arity(forcesHS'(\<phi>))) ` (6 \<union> arity(forcesHS'(\<phi>))) ` ren_forcesHS_forall(arity(forcesHS'(\<phi>)))")
    apply force
   apply(rule iffD1, rule_tac n="arity(forcesHS'(\<phi>))" in sats_ren_forcesHS_forall_iff)
             apply(rule forcesHS'_type, simp, rule max_le2, simp)
  using forcesHS'_type arity_type pair_in_M_iff HS_iff P_name_in_M
            apply auto[9]
   apply(rename_tac x, subgoal_tac "x \<in> HS", force)
   apply(rename_tac x, rule_tac P="M, Cons(x, Cons(p, Cons(P, Cons(leq, Cons(one, Cons(\<langle>\<F>, \<G>, P, P_auto\<rangle>, env)))))) \<Turnstile> is_HS_fm(5, 0)" in iffD1, rule sats_is_HS_fm_iff)
        apply auto[6]
  using \<F>_in_M \<G>_in_M P_auto_in_M pair_in_M_iff
  by auto

lemma sats_forcesHS_Forall':
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula"
  shows
    "M,[p,P,leq,one,\<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env \<Turnstile> forcesHS(Forall(\<phi>)) \<longleftrightarrow> (\<forall>x\<in>HS. M, [p,P,leq,one,\<langle>\<F>, \<G>, P, P_auto\<rangle>,x] @ env \<Turnstile> forcesHS(\<phi>))"
  apply(rule iff_trans, rule sats_forcesHS_Forall)
  using assms P_in_M transM 
     apply auto[3]
  using assms
  apply simp
  apply(rule ball_iff)
  unfolding forcesHS_def 
  apply(subgoal_tac "P \<in> M \<and> leq \<in> M \<and> one \<in> M \<and> \<langle>\<F>, \<G>, P, P_auto\<rangle> \<in> M \<and> p \<in> M \<and> HS \<subseteq> M")
   apply force 
  using \<F>_in_M \<G>_in_M P_auto_in_M pair_in_M_iff P_in_M leq_in_M one_in_M HS_iff P_name_in_M assms transM
  by auto

lemma ForcesHS_Forall:
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula"
  shows
    "(p \<tturnstile>HS Forall(\<phi>) env) \<longleftrightarrow> (\<forall>x\<in>HS. (p \<tturnstile>HS \<phi> ([x] @ env)))"
   using sats_forcesHS_Forall' assms by simp

lemma HS_strengthening_lemma:
  assumes 
    "p\<in>P" "\<phi>\<in>formula" "r\<in>P" "r\<preceq>p"
  shows
    "\<And>env. env\<in>list(M) \<Longrightarrow> arity(\<phi>)\<le>length(env) \<Longrightarrow> p \<tturnstile>HS \<phi> env \<Longrightarrow> r \<tturnstile>HS \<phi> env"
  using assms(2)
proof (induct)
  case (Member n m)
  then have assms1 : 
    "n \<in> nat" "m \<in> nat" "env \<in> list(M)"
    "arity(Member(n, m)) \<le> length(env)" "M, [p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env \<Turnstile> forcesHS(Member(n, m))" 
    by auto
  then have "p \<tturnstile> (Member(n, m)) env" 
    apply(rule_tac iffD2)
     apply(rule ForcesHS_Member)
    using P_in_M transM assms
    by auto
  then have "r \<tturnstile> (Member(n, m)) env" 
    apply(rule_tac strengthening_lemma)
    using assms assms1 
    by auto
  then show "r \<tturnstile>HS (Member(n, m)) env" 
    apply(rule_tac iffD1)
     apply(rule ForcesHS_Member)
    using P_in_M transM assms assms1
    by auto
next
  case (Equal n m)
  then have assms1 : 
    "n \<in> nat" "m \<in> nat" "env \<in> list(M)"
    "arity(Member(n, m)) \<le> length(env)" "M, [p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env \<Turnstile> forcesHS(Equal(n, m))" 
    by auto
  then have "p \<tturnstile> (Equal(n, m)) env" 
    apply(rule_tac iffD2)
     apply(rule ForcesHS_Equal)
    using P_in_M transM assms
    by auto
  then have "r \<tturnstile> (Equal(n, m)) env" 
    apply(rule_tac strengthening_lemma)
    using assms assms1 
    by auto
  then show "r \<tturnstile>HS (Equal(n, m)) env" 
    apply(rule_tac iffD1)
     apply(rule ForcesHS_Equal)
    using P_in_M transM assms assms1
    by auto
next
  case (Nand \<phi> \<psi>)
  with assms
  show ?case 
    using ForcesHS_Nand transitivity[OF _ P_in_M] pair_in_M_iff 
      transitivity[OF _ leq_in_M] leq_transD by auto
next
  case (Forall \<phi>)
  with assms
  have "p \<tturnstile>HS \<phi> ([x] @ env)" if "x\<in>HS" for x
    using that ForcesHS_Forall by simp
  
  with Forall 
  have "r \<tturnstile>HS \<phi> ([x] @ env)" if "x\<in>HS" for x
    using that pred_le2 HS_iff P_name_in_M by simp
  with assms Forall
  show ?case 
    using ForcesHS_Forall by simp
qed



lemma ForcesHS_separation : 
  assumes "\<phi>\<in>formula" "arity(\<phi>)\<le>length(env)" "env\<in>list(M)" "forcesHS(\<phi>) \<in> \<Phi>"
  shows "separation(##M, \<lambda>p. p \<tturnstile>HS \<phi> env)" 
proof - 
  have "z\<in>P \<Longrightarrow> z\<in>M" for z
    using P_in_M transitivity[of z P] by simp
  moreover
  have "separation(##M, \<lambda>p. (M, [p] @ [P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env \<Turnstile> forcesHS(\<phi>)))"
    apply(rule separation_ax)
      apply(rule forcesHS_type, simp add:assms, simp add:assms)
    using P_in_M leq_in_M one_in_M \<F>_in_M \<G>_in_M P_auto_in_M pair_in_M_iff assms 
     apply force 
    apply simp
    apply(rule le_trans, rule arity_forcesHS, simp add:assms)
    using assms 
    by auto
  then show ?thesis by auto
qed

lemma Collect_ForcesHS :
  assumes 
    fty: "\<phi>\<in>formula" and
    far: "arity(\<phi>)\<le>length(env)" and
    envty: "env\<in>list(M)" and
    "forcesHS(\<phi>) \<in> \<Phi>" 
  shows
    "{p\<in>P . p \<tturnstile>HS \<phi> env} \<in> M"
proof -
  have "z\<in>P \<Longrightarrow> z\<in>M" for z
    using P_in_M transitivity[of z P] by simp
  moreover
  have "separation(##M,\<lambda>p. (p \<tturnstile>HS \<phi> env))"
    apply(rule ForcesHS_separation)
    using assms
    by auto
  then 
  have "Collect(P,\<lambda>p. (p \<tturnstile>HS \<phi> env))\<in>M"
    using separation_closed P_in_M by simp
  then show ?thesis by simp
qed

lemma ForcesHS_And_aux:
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula"
  shows
    "p \<tturnstile>HS And(\<phi>,\<psi>) env   \<longleftrightarrow> 
    (\<forall>q\<in>M. q\<in>P \<and> q\<preceq>p \<longrightarrow> (\<exists>r\<in>M. r\<in>P \<and> r\<preceq>q \<and> (r \<tturnstile>HS \<phi> env) \<and> (r \<tturnstile>HS \<psi> env)))"
  unfolding And_def using assms ForcesHS_Neg ForcesHS_Nand by (auto simp only:)

lemma ForcesHS_And_iff_dense_below:
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula"
  shows
    "(p \<tturnstile>HS And(\<phi>,\<psi>) env) \<longleftrightarrow> dense_below({r\<in>P. (r \<tturnstile>HS \<phi> env) \<and> (r \<tturnstile>HS \<psi> env) },p)"
  unfolding dense_below_def using ForcesHS_And_aux assms
    by (auto dest:transitivity[OF _ P_in_M]; rename_tac q; drule_tac x=q in bspec)+

lemma dense_below_imp_forcesHS:
  assumes 
    "p\<in>P" "\<phi>\<in>formula"
  shows
    "\<And>env. env\<in>list(M) \<Longrightarrow> arity(\<phi>)\<le>length(env) \<Longrightarrow>
     dense_below({q\<in>P. (q \<tturnstile>HS \<phi> env)},p) \<Longrightarrow> (p \<tturnstile>HS \<phi> env)"
  using assms(2)
proof (induct)
  case (Member n m)
  then have "{q\<in>P. (q \<tturnstile>HS (Member(n, m)) env)} = {q\<in>P. (q \<tturnstile> (Member(n, m)) env)}" 
    apply(rule_tac iff_eq)
    apply(rule iff_flip)
    apply(rule ForcesHS_Member)
    using transM P_in_M
    by auto
  then have "dense_below({q\<in>P. (q \<tturnstile> (Member(n, m)) env)}, p)" 
    using Member 
    by auto
  then have "p \<tturnstile> Member(n, m) env" 
    apply(rule_tac dense_below_imp_forces)
    using Member assms
    by auto
  then show "p \<tturnstile>HS Member(n, m) env" 
    apply(rule_tac iffD1)
    apply(rule ForcesHS_Member)
    using Member transM P_in_M assms 
    by auto
next
  case (Equal n m)
  then have "{q\<in>P. (q \<tturnstile>HS (Equal(n, m)) env)} = {q\<in>P. (q \<tturnstile> (Equal(n, m)) env)}" 
    apply(rule_tac iff_eq)
    apply(rule iff_flip)
    apply(rule ForcesHS_Equal)
    using transM P_in_M
    by auto
  then have "dense_below({q\<in>P. (q \<tturnstile> (Equal(n, m)) env)}, p)" 
    using Equal 
    by auto
  then have "p \<tturnstile> Equal(n, m) env" 
    apply(rule_tac dense_below_imp_forces)
    using Equal assms
    by auto
  then show "p \<tturnstile>HS Equal(n, m) env" 
    apply(rule_tac iffD1)
    apply(rule ForcesHS_Equal)
    using Equal transM P_in_M assms 
    by auto
next
case (Nand \<phi> \<psi>)
  {  
    fix q
    assume "q\<in>M" "q\<in>P" "q\<preceq> p" "q \<tturnstile>HS \<phi> env"
    moreover 
    note Nand
    moreover from calculation
    obtain d where "d\<in>P" "d \<tturnstile>HS Nand(\<phi>, \<psi>) env" "d\<preceq> q"
      using dense_belowI by auto
    moreover from calculation
    have "\<not>(d\<tturnstile>HS \<psi> env)" if "d \<tturnstile>HS \<phi> env"
      using that ForcesHS_Nand leq_reflI transitivity[OF _ P_in_M, of d] by auto
    moreover 
    note arity_Nand_le[of \<phi> \<psi>]
    moreover from calculation
    have "d \<tturnstile>HS \<phi> env" 
       using HS_strengthening_lemma[of q \<phi> d env] Un_leD1 by auto
    ultimately
    have "\<not> (q \<tturnstile>HS \<psi> env)"
      using HS_strengthening_lemma[of q \<psi> d env] by auto
  }
  with \<open>p\<in>P\<close>
  show ?case
    using ForcesHS_Nand[symmetric, OF _ Nand(5,1,3)] by blast
next
  case (Forall \<phi>)

  then have H : "\<And>env. env \<in> list(M) \<Longrightarrow>
            arity(\<phi>) \<le> length(env) \<Longrightarrow>
            local.dense_below({q \<in> P . M, [q, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env \<Turnstile> forcesHS(\<phi>)}, p) \<Longrightarrow>
            M, Cons(p, Cons(P, Cons(leq, Cons(one, Cons(\<langle>\<F>, \<G>, P, P_auto\<rangle>, env))))) \<Turnstile> forcesHS(\<phi>)" by auto

  have "dense_below({q\<in>P. q \<tturnstile>HS \<phi> ([a]@env)},p)" if "a\<in>HS" for a
  proof
    fix r
    assume "r\<in>P" "r\<preceq>p"
    with \<open>dense_below(_,p)\<close>
    obtain q where "q\<in>P" "q\<preceq>r" "q \<tturnstile>HS Forall(\<phi>) env"
      by blast
    moreover
    note Forall \<open>a\<in>HS\<close>
    moreover from calculation
    have "q \<tturnstile>HS \<phi> ([a]@env)"
      using ForcesHS_Forall by simp
    ultimately
    show "\<exists>d \<in> {q\<in>P. q \<tturnstile>HS \<phi> ([a]@env)}. d \<in> P \<and> d\<preceq>r"
      by auto
  qed

  moreover
  note Forall(2)[of "Cons(_,env)"] Forall(1,3-5)
  ultimately
  have "p \<tturnstile>HS \<phi> ([a]@env)" if "a\<in>HS" for a
    apply simp
    apply(rule H)
    using that HS_iff P_name_in_M pred_le
      apply force
    using that HS_iff P_name_in_M pred_le
     apply simp
     apply(rule_tac n="arity(\<phi>)" in natE, simp, force, force)
    using that pred_le2 
    by simp
  with assms Forall
  show ?case using ForcesHS_Forall by simp
qed

lemma HS_density_lemma:
  assumes
    "p\<in>P" "\<phi>\<in>formula" "env\<in>list(M)" "arity(\<phi>)\<le>length(env)"
  shows
    "p \<tturnstile>HS \<phi> env   \<longleftrightarrow>   dense_below({q\<in>P. (q \<tturnstile>HS \<phi> env)},p)"
proof
  assume "dense_below({q\<in>P. (q \<tturnstile>HS \<phi> env)},p)"
  with assms
  show  "(p \<tturnstile>HS \<phi> env)"
    using dense_below_imp_forcesHS by simp
next
  assume "p \<tturnstile>HS \<phi> env"
  with assms
  show "dense_below({q\<in>P. q \<tturnstile>HS \<phi> env},p)"
    using HS_strengthening_lemma leq_reflI by auto
qed

lemma ForcesHS_And:
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula" 
    "arity(\<phi>) \<le> length(env)" "arity(\<psi>) \<le> length(env)"
  shows
    "p \<tturnstile>HS And(\<phi>,\<psi>) env   \<longleftrightarrow>  (p \<tturnstile>HS \<phi> env) \<and> (p \<tturnstile>HS \<psi> env)"
proof
  assume "p \<tturnstile>HS And(\<phi>, \<psi>) env"
  with assms
  have "dense_below({r \<in> P . (r \<tturnstile>HS \<phi> env) \<and> (r \<tturnstile>HS \<psi> env)}, p)"
    using ForcesHS_And_iff_dense_below by simp
  then
  have "dense_below({r \<in> P . (r \<tturnstile>HS \<phi> env)}, p)" "dense_below({r \<in> P . (r \<tturnstile>HS \<psi> env)}, p)"
    by blast+
  with assms
  show "(p \<tturnstile>HS \<phi> env) \<and> (p \<tturnstile>HS \<psi> env)"
    using HS_density_lemma[symmetric] by simp
next
  assume "(p \<tturnstile>HS \<phi> env) \<and> (p \<tturnstile>HS \<psi> env)"
  have "dense_below({r \<in> P . (r \<tturnstile>HS \<phi> env) \<and> (r \<tturnstile>HS \<psi> env)}, p)"
  proof (intro dense_belowI bexI conjI, assumption)
    fix q
    assume "q\<in>P" "q\<preceq> p"
    with assms \<open>(p \<tturnstile>HS \<phi> env) \<and> (p \<tturnstile>HS \<psi> env)\<close>
    show "q\<in>{r \<in> P . (r \<tturnstile>HS \<phi> env) \<and> (r \<tturnstile>HS \<psi> env)}" "q\<preceq> q"
      using HS_strengthening_lemma leq_reflI by auto
  qed
  with assms
  show "p \<tturnstile>HS And(\<phi>,\<psi>) env"
    using ForcesHS_And_iff_dense_below by simp
qed

lemma ForcesHS_Nand_alt:
  assumes
    "p\<in>P" "env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula" 
    "arity(\<phi>) \<le> length(env)" "arity(\<psi>) \<le> length(env)"
  shows
    "(p \<tturnstile>HS Nand(\<phi>,\<psi>) env) \<longleftrightarrow> (p \<tturnstile>HS Neg(And(\<phi>,\<psi>)) env)"
  using assms ForcesHS_Nand ForcesHS_And ForcesHS_Neg by auto

lemma HS_truth_lemma_Neg:
  assumes 
    "\<phi>\<in>formula" "M_generic(G)" "env\<in>list(HS)" "arity(\<phi>)\<le>length(env)" "forcesHS(\<phi>) \<in> \<Phi>" "forcesHS(Neg(\<phi>)) \<in> \<Phi>" and
    IH: "(\<exists>p\<in>G. p \<tturnstile>HS \<phi> env) \<longleftrightarrow> SymExt(G), map(val(G),env) \<Turnstile> \<phi>" 
  shows
    "(\<exists>p\<in>G. p \<tturnstile>HS Neg(\<phi>) env)  \<longleftrightarrow>  SymExt(G), map(val(G),env) \<Turnstile> Neg(\<phi>)"
proof (intro iffI, elim bexE, rule ccontr) 
  (* Direct implication by contradiction *)
  fix p 
  assume assms1 : "p\<in>G" "p \<tturnstile>HS Neg(\<phi>) env" "\<not>(SymExt(G),map(val(G),env) \<Turnstile> Neg(\<phi>))"

  have envin : "env \<in> list(M)" 
    apply(rule_tac A="list(HS)" in subsetD, rule list_mono)
    using HS_iff P_name_in_M assms
    by auto
  have mapin : "map(val(G), env) \<in> list(SymExt(G))" 
    apply(rule map_type)
    using assms SymExt_def
    by auto
 
  note assms envin mapin assms1
  moreover from calculation
  have "SymExt(G), map(val(G),env) \<Turnstile> \<phi>"
    by auto
  with IH
  obtain r where "r \<tturnstile>HS \<phi> env" "r\<in>G" by auto
  moreover from this and \<open>M_generic(G)\<close> \<open>p\<in>G\<close>
  obtain q where "q\<preceq>p" "q\<preceq>r" "q\<in>G"
    by blast
  moreover from calculation 
  have "q \<tturnstile>HS \<phi> env"
    using HS_strengthening_lemma[where \<phi>=\<phi>] by blast
  ultimately
  show "False"
    using ForcesHS_Neg[where \<phi>=\<phi>] transitivity[OF _ P_in_M] by blast
next
  have envin : "env \<in> list(M)" 
    apply(rule_tac A="list(HS)" in subsetD, rule list_mono)
    using HS_iff P_name_in_M assms
    by auto
  have mapin : "map(val(G), env) \<in> list(SymExt(G))" 
    apply(rule map_type)
    using assms SymExt_def
    by auto

  assume "SymExt(G), map(val(G),env) \<Turnstile> Neg(\<phi>)"
  with assms 
  have "\<not> (SymExt(G), map(val(G),env) \<Turnstile> \<phi>)"
    using mapin by simp
  let ?D="{p\<in>P. (p \<tturnstile>HS \<phi> env) \<or> (p \<tturnstile>HS Neg(\<phi>) env)}"
  have "separation(##M,\<lambda>p. (p \<tturnstile>HS \<phi> env))" 
    apply(rule ForcesHS_separation)
    using assms envin
    by auto
  moreover
  have "separation(##M,\<lambda>p. (p \<tturnstile>HS Neg(\<phi>) env))"
    apply(rule ForcesHS_separation)
    using assms envin
    by auto
  ultimately
  have "separation(##M,\<lambda>p. (p \<tturnstile>HS \<phi> env) \<or> (p \<tturnstile>HS Neg(\<phi>) env))" 
    using separation_disj by simp
  then 
  have "?D \<in> M" 
    using separation_closed P_in_M by simp
  moreover
  have "?D \<subseteq> P" by auto
  moreover
  have "dense(?D)"
  proof
    fix q
    assume "q\<in>P"
    show "\<exists>d\<in>{p \<in> P . (p \<tturnstile>HS \<phi> env) \<or> (p \<tturnstile>HS Neg(\<phi>) env)}. d\<preceq> q"
    proof (cases "q \<tturnstile>HS Neg(\<phi>) env")
      case True
      with \<open>q\<in>P\<close>
      show ?thesis using leq_reflI by blast
    next
      case False
      with \<open>q\<in>P\<close> and assms
      show ?thesis using ForcesHS_Neg envin by auto
    qed
  qed
  moreover
  note \<open>M_generic(G)\<close>
  ultimately
  obtain p where "p\<in>G" "(p \<tturnstile>HS \<phi> env) \<or> (p \<tturnstile>HS Neg(\<phi>) env)"
    by blast
  then
  consider (1) "p \<tturnstile>HS \<phi> env" | (2) "p \<tturnstile>HS Neg(\<phi>) env" by blast
  then
  show "\<exists>p\<in>G. (p \<tturnstile>HS Neg(\<phi>) env)"
  proof (cases)
    case 1
    with \<open>\<not> (SymExt(G),map(val(G),env) \<Turnstile> \<phi>)\<close> \<open>p\<in>G\<close> IH
    show ?thesis
      by blast
  next
    case 2
    with \<open>p\<in>G\<close> 
    show ?thesis by blast
  qed
qed 

lemma HS_truth_lemma_And:
  assumes 
    "env\<in>list(HS)" "\<phi>\<in>formula" "\<psi>\<in>formula"
    "arity(\<phi>)\<le>length(env)" "arity(\<psi>) \<le> length(env)" "M_generic(G)"
    and
    IH: "(\<exists>p\<in>G. p \<tturnstile>HS \<phi> env)  \<longleftrightarrow>   SymExt(G), map(val(G),env) \<Turnstile> \<phi>"
        "(\<exists>p\<in>G. p \<tturnstile>HS \<psi> env)  \<longleftrightarrow>   SymExt(G), map(val(G),env) \<Turnstile> \<psi>"
  shows
    "(\<exists>p\<in>G. (p \<tturnstile>HS And(\<phi>,\<psi>) env)) \<longleftrightarrow> SymExt(G) , map(val(G),env) \<Turnstile> And(\<phi>,\<psi>)"
 
proof (intro iffI, elim bexE)
  have envin : "env \<in> list(M)" 
    apply(rule_tac A="list(HS)" in subsetD, rule list_mono)
    using HS_iff P_name_in_M assms
    by auto
  have mapin : "map(val(G), env) \<in> list(SymExt(G))" 
    apply(rule map_type)
    using assms SymExt_def
    by auto

  fix p
  assume "p\<in>G" "p \<tturnstile>HS And(\<phi>,\<psi>) env"
  with assms
  show "SymExt(G), map(val(G),env) \<Turnstile> And(\<phi>,\<psi>)" 
    using ForcesHS_And[OF M_genericD, of _ _ _ \<phi> \<psi>] mapin envin by auto
next 
  have envin : "env \<in> list(M)" 
    apply(rule_tac A="list(HS)" in subsetD, rule list_mono)
    using HS_iff P_name_in_M assms
    by auto
  have mapin : "map(val(G), env) \<in> list(SymExt(G))" 
    apply(rule map_type)
    using assms SymExt_def
    by auto

  assume "SymExt(G), map(val(G),env) \<Turnstile> And(\<phi>,\<psi>)"
  moreover
  note assms
  moreover from calculation
  obtain q r where "q \<tturnstile>HS \<phi> env" "r \<tturnstile>HS \<psi> env" "q\<in>G" "r\<in>G"
    using mapin envin ForcesHS_And by auto
  moreover from calculation
  obtain p where "p\<preceq>q" "p\<preceq>r" "p\<in>G"
    by blast
  moreover from calculation
  have "(p \<tturnstile>HS \<phi> env) \<and> (p \<tturnstile>HS \<psi> env)"
    using HS_strengthening_lemma envin by (blast)
  ultimately
  show "\<exists>p\<in>G. (p \<tturnstile>HS And(\<phi>,\<psi>) env)"
    apply(rule_tac x=p in bexI)
     apply(rule iffD2, rule ForcesHS_And)
    using assms M_genericD envin 
    by auto
qed 

end

definition 
  ren_HS_truth_lemma :: "i\<Rightarrow>i" where
  "ren_HS_truth_lemma(\<phi>) \<equiv> 
    Exists(Exists(Exists(Exists(Exists(Exists(
    And(Equal(0,6),And(Equal(1,9),And(Equal(2,10),And(Equal(3,11),And(Equal(4,12),And(Equal(5,7),
    iterates(\<lambda>p. incr_bv(p)`6 , 7, \<phi>)))))))))))))"

context M_symmetric_system_HS_Forces begin

lemma ren_HS_truth_lemma_type[TC] :
  "\<phi>\<in>formula \<Longrightarrow> ren_HS_truth_lemma(\<phi>) \<in>formula" 
  unfolding ren_HS_truth_lemma_def
  by simp

lemma sats_ren_HS_truth_lemma:
  "[q,b,d,a1,a2,a3,a4] @ env \<in> list(M) \<Longrightarrow> \<phi> \<in> formula \<Longrightarrow>
   (M, [q,b,d,a1,a2,a3,a4] @ env \<Turnstile> ren_HS_truth_lemma(\<phi>) ) \<longleftrightarrow>
   (M, [q,a1,a2,a3,a4,b] @ env \<Turnstile> \<phi>)"
  unfolding ren_HS_truth_lemma_def
  by (insert sats_incr_bv_iff [of _ _ M _ "[q,a1,a2,a3,a4,b]"], simp)

lemma arity_incr_bv_le : 
  assumes "\<phi> \<in> formula" "m \<in> nat" "n \<in> nat"
  shows "arity((\<lambda>p. incr_bv(p) ` n)^m (\<phi>) ) \<le> m #+ arity(\<phi>)" 
  using \<open>m \<in> nat\<close>
proof(induct)
  case 0
  then show ?case using assms by auto
next
  case (succ x)
  then show ?case 
    apply simp
    apply(subst arity_incr_bv_lemma)
      apply(rule iterates_type, simp, simp add:assms)
      apply(rule function_value_in)
       apply(rule incr_bv_type)
    using assms
       apply auto[3]
    apply(cases "n < arity((\<lambda>p. incr_bv(p) ` n)^x (\<phi>))")
     apply simp
    apply simp
    apply(rule_tac j="x #+ arity(\<phi>)" in le_trans, simp, simp)
    done
qed

lemma arity_ren_HS_truth_lemma : 
  assumes "\<phi>\<in>formula"
  shows "arity(ren_HS_truth_lemma(\<phi>)) \<le> 7 \<union> succ(arity(\<phi>))"

  unfolding ren_HS_truth_lemma_def 
  apply(subgoal_tac "(\<lambda>p. incr_bv(p) ` 6)^7 (\<phi>) \<in> formula")
  using assms 
   apply simp
   apply(rule pred_le, simp, simp)+
   apply(subst succ_Un_distrib, simp, simp)+
   apply(simp add:nat_union_abs1)
   apply(rule Un_least_lt, rule ltI, simp, rule disjI1, rule ltD, simp, simp)+
   apply(rule Un_least_lt, rule ltI, simp, simp)
   apply(rule Un_least_lt, rule ltI, simp, rule disjI1, rule ltD, simp, simp)
   apply(rule_tac b="arity((\<lambda>p. incr_bv(p) ` 6)^7 (\<phi>))" in le_lt_lt, force)
   apply(rule le_lt_lt, rule arity_incr_bv_le)
      apply auto[3]
   apply simp
   apply(rule ltI, simp, simp)
  apply(rule iterates_type, simp, simp add:assms)
  apply(rule function_value_in)
   apply(rule incr_bv_type)
  by auto

end 

definition HS_truth_lemma'_helper_fm where "HS_truth_lemma'_helper_fm(\<phi>) \<equiv>
  Exists(And(is_HS_fm(5, 0), Forall(Implies(And(Member(0, 3), leq_fm(4, 0, 2)), Neg(ren_HS_truth_lemma(forcesHS(\<phi>)))))))" 

context M_symmetric_system_HS_Forces 
begin

lemma HS_truth_lemma' :
  assumes
    "\<phi>\<in>formula" "env\<in>list(M)" "arity(\<phi>) \<le> succ(length(env))" "HS_truth_lemma'_helper_fm(\<phi>) \<in> \<Phi>" 
  shows
    "separation(##M,\<lambda>d. \<exists>b\<in>HS. \<forall>q\<in>P. q\<preceq>d \<longrightarrow> \<not>(q \<tturnstile>HS \<phi> ([b]@env)))"
proof -

  have iff_lemma: "\<And>P Q R. (\<And>x. x \<in> M \<Longrightarrow> x \<in> HS \<longleftrightarrow> P(x)) \<Longrightarrow> (\<And>x. x \<in> HS \<Longrightarrow> Q(x) \<longleftrightarrow> R(x)) \<Longrightarrow> (\<exists>x \<in> M. P(x) \<and> Q(x)) \<longleftrightarrow> (\<exists>x \<in> HS. R(x))"
    apply(rule iffI)
     apply clarify 
     apply(rename_tac x, rule_tac x=x in bexI)
      apply(rename_tac x, subgoal_tac "x \<in> HS", force, force, force)
    apply clarify 
    apply(rename_tac x, rule_tac x=x in bexI)
    using HS_iff P_name_in_M
     apply force 
    using HS_iff P_name_in_M
     apply force 
    done

  let ?rel_pred="\<lambda>M x a1 a2 a3 a4. \<exists>b\<in>HS. \<forall>q\<in>M. q\<in>a1 \<and> is_leq(##M,a2,q,x) \<longrightarrow> 
                  \<not>(M, [q,a1,a2,a3,a4,b] @ env \<Turnstile> forcesHS(\<phi>))" 
  let ?\<psi>="Exists(And(
            is_HS_fm(5, 0), 
            Forall(Implies(And(Member(0,3),leq_fm(4,0,2)),
            Neg(ren_HS_truth_lemma(forcesHS(\<phi>)))))))"
  have "q\<in>M" if "q\<in>P" for q using that transitivity[OF _ P_in_M] by simp
  then
  have 1:"\<forall>q\<in>M. q\<in>P \<and> R(q) \<longrightarrow> Q(q) \<Longrightarrow> (\<forall>q\<in>P. R(q) \<longrightarrow> Q(q))" for R Q 
    by auto
  then
  have "\<lbrakk>b \<in> HS; \<forall>q\<in>M. q \<in> P \<and> q \<preceq> d \<longrightarrow> \<not>(q \<tturnstile>HS \<phi> ([b]@env))\<rbrakk> \<Longrightarrow>
         \<exists>c\<in>HS. \<forall>q\<in>P. q \<preceq> d \<longrightarrow> \<not>(q \<tturnstile>HS \<phi> ([c]@env))" for b d
    by (rule bexI,simp_all)
  then
  have "?rel_pred(M,d,P,leq,one,\<langle>\<F>, \<G>, P, P_auto\<rangle>) \<longleftrightarrow> (\<exists>b\<in>HS. \<forall>q\<in>P. q\<preceq>d \<longrightarrow> \<not>(q \<tturnstile>HS \<phi> ([b]@env)))" if "d\<in>M" for d
    using that leq_abs leq_in_M P_in_M one_in_M assms \<F>_in_M \<G>_in_M P_auto_in_M pair_in_M_iff 
    by auto
  moreover
  have "?\<psi>\<in>formula" 
    apply(subgoal_tac "is_HS_fm(5, 0) \<in> formula \<and> ren_HS_truth_lemma(forcesHS(\<phi>)) \<in> formula", force)
    unfolding ren_HS_truth_lemma_def 
    apply(rule conjI, rule is_HS_fm_type, simp, simp)
    apply(rule Exists_type)+
    apply(rule And_type, simp)+
    apply(rule iterates_type, simp, rule forcesHS_type, simp add:assms)
    apply(rule function_value_in)
     apply(rule incr_bv_type)
    by auto
  moreover
  have H: "(M, [d,P,leq,one,\<langle>\<F>, \<G>, P, P_auto\<rangle>]@env \<Turnstile> ?\<psi>) \<longleftrightarrow> ?rel_pred(M,d,P,leq,one,\<langle>\<F>, \<G>, P, P_auto\<rangle>)" if "d\<in>M" for d
    apply(subgoal_tac "\<langle>\<F>, \<G>, P, P_auto\<rangle> \<in> M")
    using assms that P_in_M leq_in_M one_in_M sats_leq_fm  
     apply simp
     apply(rule iff_lemma)
      apply(rule iff_flip, rule sats_is_HS_fm_iff, force, force, force, force, force)
     apply(rule ball_iff, rule imp_iff, simp, rule notnot_iff)
     apply(rename_tac x y, rule_tac Q="M, [y, x, d, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env \<Turnstile> ren_HS_truth_lemma(forcesHS(\<phi>))" in iff_trans)
      apply force
     apply(rule iff_trans, rule sats_ren_HS_truth_lemma)
    using HS_iff P_name_in_M
       apply force
      apply(rule forcesHS_type, simp, force)
    using \<F>_in_M \<G>_in_M P_in_M P_auto_in_M pair_in_M_iff
    by auto

  have I1: "separation(##M,\<lambda>d. \<exists>b\<in>HS. \<forall>q\<in>P. q\<preceq>d \<longrightarrow> \<not>(q \<tturnstile>HS \<phi> ([b]@env))) \<longleftrightarrow> 
        separation(##M,\<lambda>d. ?rel_pred(M,d,P,leq,one,\<langle>\<F>, \<G>, P, P_auto\<rangle>))" 
    apply(rule separation_cong)
    using P_in_M leq_in_M transM 
    by auto
  have I2: "... \<longleftrightarrow> separation(##M,\<lambda>d. (M, [d,P,leq,one,\<langle>\<F>, \<G>, P, P_auto\<rangle>]@env \<Turnstile> ?\<psi>))"
    apply(rule separation_cong)
    apply(rule iff_flip, rule H, force)
    done
  have I3: "... \<longleftrightarrow> separation(##M,\<lambda>d. (M, [d] @ [P,leq,one,\<langle>\<F>, \<G>, P, P_auto\<rangle>]@env \<Turnstile> ?\<psi>))" by auto

  have "separation(##M,\<lambda>d. (M, [d] @ [P,leq,one,\<langle>\<F>, \<G>, P, P_auto\<rangle>]@env \<Turnstile> ?\<psi>))"
    apply(subgoal_tac "is_HS_fm(5, 0) \<in> formula")
    apply(rule separation_ax)
    apply(rule Exists_type, rule And_type, rule is_HS_fm_type, simp, simp)
    using assms forcesHS_type is_HS_fm_type 
        apply force
    using assms HS_truth_lemma'_helper_fm_def
       apply force
    using P_in_M leq_in_M one_in_M \<F>_in_M \<G>_in_M P_auto_in_M pair_in_M_iff assms
     apply force 
    using assms
    apply simp
    apply(rule pred_le)
    using forcesHS_type assms
      apply force 
      apply force 
     apply(rule Un_least_lt, rule le_trans, rule arity_is_HS_fm, simp, simp)
      apply(rule Un_least_lt, simp ,simp)
    apply(rule pred_le)
    using forcesHS_type assms
      apply force 
     apply force 
    apply(rule Un_least_lt)+
       apply auto[2]
     apply(subst arity_leq_fm)
        apply auto[3]
     apply(rule Un_least_lt)+
       apply auto[3]
    apply(rule le_trans, rule arity_ren_HS_truth_lemma)
    using forcesHS_type 
     apply force 
    apply(rule Un_least_lt, simp, simp)
    apply(rule le_trans, rule arity_forcesHS, simp)
     apply simp
    apply(rule is_HS_fm_type)
    by auto
  then show "separation(##M, \<lambda>d. \<exists>b\<in>HS. \<forall>q\<in>P. q \<preceq> d \<longrightarrow> satisfies(M, forcesHS(\<phi>)) ` ([q, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ [b] @ env) \<noteq> 1)" 
    using I1 I2 I3 
    by auto
qed
 
end

consts forcesHS_fms :: "i\<Rightarrow>i"
primrec
  "forcesHS_fms(Member(x, y)) = 0" 
  "forcesHS_fms(Equal(x, y)) = 0" 
  "forcesHS_fms(Nand(\<phi>, \<psi>)) = forcesHS_fms(\<phi>) \<union> forcesHS_fms(\<psi>) \<union> { forcesHS(And(\<phi>, \<psi>)), forcesHS(Neg(And(\<phi>, \<psi>))) }" 
  "forcesHS_fms(Forall(\<phi>)) = forcesHS_fms(\<phi>) \<union> { forcesHS(\<phi>), forcesHS(Forall(\<phi>)), HS_truth_lemma'_helper_fm(\<phi>) }" 

context M_symmetric_system_HS_Forces
begin 

lemma HS_truth_lemma:
  assumes 
    "\<phi>\<in>formula" "M_generic(G)"
  shows 
     "\<And>env. env\<in>list(HS) \<Longrightarrow> arity(\<phi>)\<le>length(env) \<Longrightarrow> forcesHS_fms(\<phi>) \<subseteq> \<Phi> \<Longrightarrow> 
      (\<exists>p\<in>G. p \<tturnstile>HS \<phi> env) \<longleftrightarrow> SymExt(G), map(val(G),env) \<Turnstile> \<phi>"
  using assms(1)
proof (induct)
  case (Member x y)
  then have assms1: "x \<in> nat" "y \<in> nat" "env \<in> list(HS)" "arity(Member(x, y)) \<le> length(env)" by auto

  have GsubsetM : "G \<subseteq> M" 
    apply(rule_tac B=P in subset_trans)
    using assms M_generic_def filter_def P_in_M transM 
    by auto

  have envin : "env \<in> list(M)" 
    apply(rule_tac A="list(HS)" in subsetD)
     apply(rule list_mono)
    using assms1 HS_iff P_name_in_M 
    by auto

  have envmaptype : "map(val(G), env) \<in> list(SymExt(G))"
    apply(rule map_type)
    using assms1 SymExt_def
    by auto 

  interpret "M_symmetric_system_G_generic" P leq one M \<Phi> enum \<G> \<F> G 
    unfolding M_symmetric_system_G_generic_def
    using M_symmetric_system_HS_M_axioms G_generic_def forcing_data_axioms G_generic_axioms_def assms 
    by auto

  have I1: "(\<exists>p\<in>G. M, [p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env \<Turnstile> forcesHS(Member(x, y))) \<longleftrightarrow> 
             (\<exists>p\<in>G. M, [p, P, leq, one] @ env \<Turnstile> forces(Member(x, y)))" 
    apply(rule bex_iff, rule sats_forcesHS_Member)
    using assms1 \<F>_in_M \<G>_in_M P_in_M P_auto_in_M pair_in_M_iff envin GsubsetM
    by auto
  have I2: "... \<longleftrightarrow> (\<exists>p \<in> G. p \<tturnstile> Member(x, y) env)" by auto
  have I3: "... \<longleftrightarrow> M[G], map(val(G), env) \<Turnstile> Member(x, y)" 
    apply(rule truth_lemma_mem)
    using assms1 assms envin 
    apply auto[4]
    apply(rule_tac b="arity(Member(x, y))" in lt_le_lt)
    using assms1 assms envin ltI
    apply auto[2]
    apply(rule_tac b="arity(Member(x, y))" in lt_le_lt)
    using assms1 assms envin ltI
    apply auto[2]
    done
  have I4 : "... \<longleftrightarrow> SymExt(G), map(val(G), env) \<Turnstile> Member(x, y)" 
    apply(rule iff_flip, rule \<Delta>0_sats_iff)
    using SymExt_subset_GenExt envmaptype Member_\<Delta>0 assms1 Transset_SymExt length_map  
    by auto
  show "(\<exists>p\<in>G. M, [p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env \<Turnstile> forcesHS(Member(x, y))) \<longleftrightarrow>
          SymExt(G), map(val(G), env) \<Turnstile> Member(x, y)"
    using I1 I2 I3 I4 
    by auto

next
  case (Equal x y)
  then have assms1: "x \<in> nat" "y \<in> nat" "env \<in> list(HS)" "arity(Equal(x, y)) \<le> length(env)" by auto
                    
  have GsubsetM : "G \<subseteq> M" 
    apply(rule_tac B=P in subset_trans)
    using assms M_generic_def filter_def P_in_M transM 
    by auto

  have envin : "env \<in> list(M)" 
    apply(rule_tac A="list(HS)" in subsetD)
     apply(rule list_mono)
    using assms1 HS_iff P_name_in_M 
    by auto

  have envmaptype : "map(val(G), env) \<in> list(SymExt(G))"
    apply(rule map_type)
    using assms1 SymExt_def
    by auto

  interpret "M_symmetric_system_G_generic" P leq one M \<Phi> enum \<G> \<F> G 
    unfolding M_symmetric_system_G_generic_def
    using M_symmetric_system_HS_M_axioms G_generic_def forcing_data_axioms G_generic_axioms_def assms 
    by auto

  have I1: "(\<exists>p\<in>G. M, [p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env \<Turnstile> forcesHS(Equal(x, y))) \<longleftrightarrow> 
             (\<exists>p\<in>G. M, [p, P, leq, one] @ env \<Turnstile> forces(Equal(x, y)))" 
    apply(rule bex_iff, rule sats_forcesHS_Equal)
    using assms1 \<F>_in_M \<G>_in_M P_in_M P_auto_in_M pair_in_M_iff envin GsubsetM
    by auto
  have I2: "... \<longleftrightarrow> (\<exists>p \<in> G. p \<tturnstile> Equal(x, y) env)" by auto
  have I3: "... \<longleftrightarrow> M[G], map(val(G), env) \<Turnstile> Equal(x, y)" 
    apply(rule truth_lemma_eq)
    using assms1 assms envin 
    apply auto[4]
    apply(rule_tac b="arity(Equal(x, y))" in lt_le_lt)
    using assms1 assms envin ltI
    apply auto[2]
    apply(rule_tac b="arity(Equal(x, y))" in lt_le_lt)
    using assms1 assms envin ltI
    apply auto[2]
    done
  have I4 : "... \<longleftrightarrow> SymExt(G), map(val(G), env) \<Turnstile> Equal(x, y)" 
    apply(rule iff_flip, rule \<Delta>0_sats_iff)
    using SymExt_subset_GenExt envmaptype Member_\<Delta>0 assms1 Transset_SymExt length_map 
    by auto
  show "(\<exists>p\<in>G. M, [p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env \<Turnstile> forcesHS(Equal(x, y))) \<longleftrightarrow>
          SymExt(G), map(val(G), env) \<Turnstile> Equal(x, y)"
    using I1 I2 I3 I4 
    by auto
next
  case (Nand \<phi> \<psi>)

  have envin : "env \<in> list(M)" 
    apply(rule_tac A="list(HS)" in subsetD, rule list_mono)
    using HS_iff P_name_in_M assms Nand
    by auto
  have mapin : "map(val(G), env) \<in> list(SymExt(G))" 
    apply(rule map_type)
    using assms SymExt_def Nand
    by auto
  have arityle : "arity(\<phi>) \<le> length(env) \<and> arity(\<psi>) \<le> length(env)"
    apply(rule conjI)
      apply(rule_tac j="arity(\<phi>) \<union> arity(\<psi>)" in le_trans)
    using Nand max_le1
       apply auto[2]
      apply(rule_tac j="arity(\<phi>) \<union> arity(\<psi>)" in le_trans)
    using Nand max_le2
     apply auto[2]
    done

  have "forcesHS_fms(\<phi>) \<subseteq> \<Phi> \<and> forcesHS_fms(\<psi>) \<subseteq> \<Phi>" 
    using Nand 
    by force

  moreover 
  note \<open>M_generic(G)\<close>
  ultimately
  show ?case 
    apply(rule_tac iff_trans) 
     apply(rule bex_iff, rule ForcesHS_Nand_alt)
    using M_genericD assms envin Nand arityle
          apply auto[6]
    apply(rule iff_trans, rule HS_truth_lemma_Neg) 
    using Nand
         apply auto[6]
     apply(rule HS_truth_lemma_And)
    using Nand arityle 
            apply auto[8]
    using mapin Nand
    by auto
next
  case (Forall \<phi>)

  have envin : "env \<in> list(M)" 
    apply(rule_tac A="list(HS)" in subsetD, rule list_mono)
    using HS_iff P_name_in_M assms Forall
    by auto
  have mapin : "map(val(G), env) \<in> list(SymExt(G))" 
    apply(rule map_type)
    using assms SymExt_def Forall
    by auto

  have ihE : "\<And>env. env \<in> list(HS) \<Longrightarrow> arity(\<phi>) \<le> length(env) \<Longrightarrow>
    (\<exists>p\<in>G. M, [p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env \<Turnstile> forcesHS(\<phi>)) \<longleftrightarrow> SymExt(G), map(\<lambda>a. val(G, a), env) \<Turnstile> \<phi>"
    using Forall 
    by auto

  with \<open>M_generic(G)\<close>
  show ?case
  proof (intro iffI)
    assume "\<exists>p\<in>G. (p \<tturnstile>HS Forall(\<phi>) env)"
    with \<open>M_generic(G)\<close>
    obtain p where pH: "p\<in>G" "p\<in>M" "p\<in>P" "p \<tturnstile>HS Forall(\<phi>) env"
      using transitivity[OF _ P_in_M] by auto
    with \<open>env\<in>list(HS)\<close> \<open>\<phi>\<in>formula\<close>
    have "p \<tturnstile>HS \<phi> (Cons(x, env))" if "x\<in>HS" for x
      using that ForcesHS_Forall envin by simp
    then have "SymExt(G), map(\<lambda>a. val(G, a), Cons(x, env)) \<Turnstile> \<phi>" if "x \<in> HS" for x 
      using that ForcesHS_Forall envin Forall pH 
      apply(rule_tac iffD1, rule_tac ihE)
        apply auto[1]
       apply(rule_tac n="arity(\<phi>)" in natE, simp, force, force)
      apply(rule_tac x=p in bexI)
      by auto
    then show "SymExt(G), map(val(G),env) \<Turnstile> Forall(\<phi>)" 
      using mapin 
      apply simp
      apply(rule ballI)
      apply(rename_tac x, subgoal_tac "\<exists>x' \<in> HS. val(G, x') = x", force)
      unfolding SymExt_def
      by auto
  next
    assume satsforall : "SymExt(G), map(val(G),env) \<Turnstile> Forall(\<phi>)"

    let ?D1="{d\<in>P. (d \<tturnstile>HS Forall(\<phi>) env)}"
    let ?D2="{d\<in>P. \<exists>b\<in>HS. \<forall>q\<in>P. q\<preceq>d \<longrightarrow> \<not>(q \<tturnstile>HS \<phi> ([b]@env))}"
    define D where "D \<equiv> ?D1 \<union> ?D2"
    have ar\<phi>:"arity(\<phi>)\<le>succ(length(env))" 
      using assms \<open>arity(Forall(\<phi>)) \<le> length(env)\<close> \<open>\<phi>\<in>formula\<close> \<open>env\<in>list(M)\<close> pred_le2 
      by simp
    then
    have "arity(Forall(\<phi>)) \<le> length(env)" 
      using pred_le \<open>\<phi>\<in>formula\<close> \<open>env\<in>list(M)\<close> by simp
    then
    have "?D1\<in>M" 
      using Collect_ForcesHS ar\<phi> \<open>\<phi>\<in>formula\<close> \<open>env\<in>list(M)\<close> Forall
      by auto
    moreover
    have "?D2\<in>M" 
      apply(rule_tac separation_notation)
      apply(rule HS_truth_lemma')
      using \<open>env\<in>list(M)\<close> \<open>\<phi>\<in>formula\<close>  HS_truth_lemma' separation_closed ar\<phi>
                        P_in_M Forall
          apply auto[3]
      using Forall 
       apply force
      using P_in_M
      by auto
    ultimately
    have "D\<in>M" unfolding D_def using Un_closed by simp
    moreover
    have "D \<subseteq> P" unfolding D_def by auto
    moreover
    have "dense(D)" 
    proof
      fix p
      assume "p\<in>P"
      show "\<exists>d\<in>D. d\<preceq> p"
      proof (cases "p \<tturnstile>HS Forall(\<phi>) env")
        case True
        with \<open>p\<in>P\<close> 
        show ?thesis unfolding D_def using leq_reflI by blast
      next
        case False

        have "(M, [p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env \<Turnstile> forcesHS(Forall(\<phi>))) \<longleftrightarrow> 
              (\<forall>x\<in>HS. M, [p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ [x] @ env \<Turnstile> forcesHS(\<phi>))" 
          apply(rule ForcesHS_Forall)
          using \<open>p \<in> P\<close> Forall envin
          by auto
        then have "\<not> (\<forall>x\<in>HS. M, [p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ [x] @ env \<Turnstile> forcesHS(\<phi>))" using False by auto
        then obtain b where "b\<in>HS" "\<not>(p \<tturnstile>HS \<phi> ([b]@env))" by auto
        moreover from this \<open>p\<in>P\<close> Forall
        have "\<not>dense_below({q\<in>P. q \<tturnstile>HS \<phi> ([b]@env)},p)"
          apply(rule_tac iffD1)
           apply(rule notnot_iff, rule HS_density_lemma, simp, simp)
          using envin HS_iff P_name_in_M
            apply force 
           apply simp
           apply(rule_tac n="arity(\<phi>)" in natE, simp, simp, force)
          using HS_density_lemma pred_le2 
          by auto
        moreover from this
        obtain d where "d\<preceq>p" "\<forall>q\<in>P. q\<preceq>d \<longrightarrow> \<not>(q \<tturnstile>HS \<phi> ([b] @ env))"
          "d\<in>P" by blast
        ultimately
        show ?thesis 
          unfolding D_def
          apply(rule_tac x=d in bexI, simp)
          apply simp
          apply(rule disjI2, rule_tac x=b in bexI, force)
          using HS_iff P_name_in_M
          by auto
      qed
    qed
    moreover
    note \<open>M_generic(G)\<close>
    ultimately
    obtain d where "d \<in> D"  "d \<in> G" by blast
    then
    consider (1) "d\<in>?D1" | (2) "d\<in>?D2" unfolding D_def by blast
    then
    show "\<exists>p\<in>G. (p \<tturnstile>HS Forall(\<phi>) env)"
    proof (cases)
      case 1
      with \<open>d\<in>G\<close>
      show ?thesis by blast
    next
      case 2
      then
      obtain b where "b\<in>HS" "\<forall>q\<in>P. q\<preceq>d \<longrightarrow>\<not>(q \<tturnstile>HS \<phi> ([b] @ env))"
        by blast
      then 

      have "\<And>x. x \<in> SymExt(G) \<Longrightarrow> sats(SymExt(G), \<phi>, Cons(x, map(val(G), env)))" 
        using satsforall mapin by simp 
      then have "sats(SymExt(G), \<phi>, map(val(G), Cons(b, env)))" 
        apply(subgoal_tac "val(G, b) \<in> SymExt(G)") 
         apply force 
        unfolding SymExt_def 
        using \<open>b \<in> HS\<close> 
        by auto
      then have "\<exists>p \<in> G. p \<tturnstile>HS \<phi> ([b] @ env)"  
        apply(rule_tac iffD2)
         apply(rule ihE)
        using \<open>b \<in> HS\<close> Forall
          apply force 
        apply(rule_tac n="arity(\<phi>)" in natE)
        using Forall 
        by auto
      then obtain p where "p\<in>G" "p\<in>P" "p \<tturnstile>HS \<phi> ([b] @ env)" 
        using M_genericD assms 
        by auto
      moreover
      note \<open>d\<in>G\<close> \<open>M_generic(G)\<close>
      ultimately
      obtain q where "q\<in>G" "q\<in>P" "q\<preceq>d" "q\<preceq>p" by blast
      moreover from this and  \<open>p \<tturnstile>HS \<phi> ([b] @ env)\<close> 
        Forall  \<open>b\<in>HS\<close> \<open>p\<in>P\<close>
      have "q \<tturnstile>HS \<phi> ([b] @ env)"
        apply(rule_tac p=p in HS_strengthening_lemma)
        using \<open>b\<in>HS\<close> HS_iff P_name_in_M envin
              apply auto[5]
         apply(rule_tac n="arity(\<phi>)" in natE, simp, simp, force, force)
        done
      moreover 
      note \<open>\<forall>q\<in>P. q\<preceq>d \<longrightarrow>\<not>(q \<tturnstile>HS \<phi> ([b] @ env))\<close>
      ultimately
      show ?thesis by simp
    qed
  qed
qed

lemma definition_of_forcing_HS:
  assumes
    "p\<in>P" "\<phi>\<in>formula" "env\<in>list(HS)" "arity(\<phi>)\<le>length(env)" "forcesHS_fms(\<phi>) \<subseteq> \<Phi>"
  shows
    "(p \<tturnstile>HS \<phi> env) \<longleftrightarrow>
     (\<forall>G. M_generic(G) \<and> p\<in>G  \<longrightarrow>  SymExt(G), map(val(G),env) \<Turnstile> \<phi>)"
proof (intro iffI allI impI, elim conjE)
  fix G
  assume assms1:"(p \<tturnstile>HS \<phi> env)" "M_generic(G)" "p \<in> G" 
  with assms 
  show "SymExt(G), map(val(G),env) \<Turnstile> \<phi>"
    apply(rule_tac iffD1)
     apply(rule HS_truth_lemma)
    using assms
    by auto    
next 
  have envin : "env \<in> list(M)" 
    apply(rule_tac A="list(HS)" in subsetD, rule list_mono)
    using HS_iff P_name_in_M assms Forall
    by auto

  assume 1: "\<forall>G.(M_generic(G)\<and> p\<in>G)\<longrightarrow> SymExt(G) , map(val(G),env) \<Turnstile> \<phi>"
  {
    fix r 
    assume 2: "r\<in>P" "r\<preceq>p"
    then 
    obtain G where "r\<in>G" "M_generic(G)"
      using generic_filter_existence by auto

    moreover from calculation 2 \<open>p\<in>P\<close> 
    have "p\<in>G" 
      unfolding M_generic_def using filter_leqD by simp
    moreover note 1
    ultimately
    have satsphi : "SymExt(G), map(val(G),env) \<Turnstile> \<phi>"
      by simp

    have "\<exists>s \<in> G. s \<tturnstile>HS \<phi> env"
      apply(rule iffD2)
       apply(rule HS_truth_lemma)
      using assms satsphi \<open>M_generic(G)\<close>
      by auto
    then obtain s where "s\<in>G" "(s \<tturnstile>HS \<phi> env)"
      using satsphi by blast
    moreover from this and  \<open>M_generic(G)\<close> \<open>r\<in>G\<close> 
    obtain q where "q\<in>G" "q \<preceq> s" "q \<preceq> r"
      by blast
    moreover from calculation \<open>s\<in>G\<close> \<open>M_generic(G)\<close> 
    have "s\<in>P" "q\<in>P" 
      unfolding M_generic_def filter_def by auto
    moreover 
    note assms
    ultimately 
    have "\<exists>q\<in>P. q\<preceq>r \<and> (q \<tturnstile>HS \<phi> env)"
      apply(rule_tac x=q in bexI)
       apply(rule conjI) 
      using \<open>q \<preceq> r\<close> 
        apply simp
       apply(rule_tac p=s in HS_strengthening_lemma)
      using M_genericD \<open>M_generic(G)\<close> \<open>s\<in>G\<close> envin 
      by auto
  }
  then
  have "dense_below({q\<in>P. (q \<tturnstile>HS \<phi> env)},p)"
    unfolding dense_below_def by blast
  with assms
  show "(p \<tturnstile>HS \<phi> env)"
    apply(rule_tac iffD2)
     apply(rule HS_density_lemma) 
    using envin
    by auto
qed


end
end
