theory SymExt_Replacement
  imports  
    SymExt_Separation
    SymExt_Separation_Base
begin 

context M_symmetric_system_SymExt_Separation_Base
begin
 

definition is_MVset_fm where "is_MVset_fm(a, V) \<equiv> And(ordinal_fm(a), Exists(And(empty_fm(0), is_transrec_fm(is_HVfrom_fm(8, 2, 1, 0), succ(a), succ(V)))))" 

lemma is_MVset_fm_type : 
  fixes i j 
  assumes "i \<in> nat" "j \<in> nat" 
  shows "is_MVset_fm(i, j) \<in> formula"
  unfolding is_MVset_fm_def
  using assms 
  by auto

lemma arity_is_MVset_fm : 
  fixes i j 
  assumes "i \<in> nat" "j \<in> nat" 
  shows "arity(is_MVset_fm(i, j)) \<le> succ(i) \<union> succ(j)" 
  unfolding is_MVset_fm_def 
  apply simp
  apply(subst arity_ordinal_fm, simp add:assms)
  using assms
  apply(rule_tac Un_least_lt, simp, rule_tac ltI, simp_all)
  apply(rule pred_le, simp, simp, rule_tac Un_least_lt, subst arity_empty_fm, simp_all)
  unfolding is_transrec_fm_def
  apply simp
  apply(rule pred_le, simp_all)+
  apply(subst arity_upair_fm, simp_all)
  apply(subst arity_is_eclose_fm, simp_all)
  apply(subst arity_Memrel_fm, simp_all)
  apply(subst arity_is_wfrec_fm, simp_all)
  apply(rule Un_least_lt)+
    apply(subst succ_Un_distrib, simp_all)+
   apply(rule ltI, simp, simp)
  apply(rule Un_least_lt)+
    apply simp_all
  apply(rule Un_least_lt)+
    apply simp_all       
  apply(rule Un_least_lt)+
     apply simp_all
    apply(rule ltI, simp_all)+
  apply(rule ltD)
  apply(rule pred_le, simp_all)+
  unfolding is_HVfrom_fm_def is_powapply_fm_def
  apply(simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union) 
  done

lemma sats_is_MVset_fm_iff : 
  fixes a V i j env  
  assumes "env \<in> list(M)" "nth(i, env) = a" "nth(j, env) = V" "i < length(env)" "j < length(env)"
  shows "sats(M, is_MVset_fm(i, j), env) \<longleftrightarrow> (a \<in> M \<and> Ord(a)) \<and> V = MVset(a)" 

  unfolding is_MVset_fm_def 
  apply(rule iff_trans, rule sats_And_iff, simp add:assms,rule iff_conjI2) 
   apply(rule iff_trans, rule sats_ordinal_fm)
  using assms trans_M
      apply auto[4]
  apply(rule iff_trans, rule iff_flip, rule is_Vset_iff_sats)
  using assms zero_in_M lt_nat_in_nat
          apply auto[8]
  apply(rule iff_trans, rule Vset_abs)
  using assms 
     apply auto[3]
  unfolding MVset_def
  by auto

definition ren_least_index where "ren_least_index(\<phi>) \<equiv>
    Exists(Exists(Exists(Exists(Exists(Exists(
      And(Equal(0, 11), 
      And(Equal(1, 14), 
      And(Equal(2, 14#+1), 
      And(Equal(3, 14#+2), 
      And(Equal(4, 14#+3), 
      And(Equal(5, 10), 
          iterates(\<lambda>p. incr_bv(p)`7, 11, \<phi>)))))))))))))" 

lemma sats_ren_least_index_iff : 
  assumes "\<phi> \<in> formula" "[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] @ env \<in> list(M)"
  shows "sats(M, ren_least_index(\<phi>), [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] @ env) \<longleftrightarrow> 
         sats(M, \<phi>, [a5, a8, a9, a10, a11, a4, a0] @ env)" 
  unfolding ren_least_index_def
  using assms
  apply simp
  apply (insert sats_incr_bv_iff [of _ _ M _ "[a5, a8, a9, a10, a11, a4, a0]"])
  by simp

lemma ren_least_index_type : 
  "\<phi> \<in> formula \<Longrightarrow> ren_least_index(\<phi>) \<in> formula" 
  unfolding ren_least_index_def 

  apply(subgoal_tac " (\<lambda>p. incr_bv(p) ` 7)^11 (\<phi>) \<in> formula")
   apply force 
  apply(rule iterates_type)
  by auto

lemma arity_ren_least_index : 
  fixes \<phi>
  assumes "\<phi> \<in> formula" "0 < arity(\<phi>)" 
  shows "arity(ren_least_index(\<phi>)) \<le> 12 \<union> (5 #+ arity(\<phi>))" 

  unfolding ren_least_index_def 
  apply(subgoal_tac "(\<lambda>p. incr_bv(p) ` 7)^11 (\<phi>) \<in> formula") 
  using assms
   apply simp
   apply(rule pred_le, simp, simp)+
   apply(subst succ_Un_distrib, simp, simp)+
   apply(rule Un_least_lt, rule Un_least_lt, rule union_lt1, simp, simp, simp, simp, rule union_lt1, simp, simp, simp, simp)+
   apply(rule_tac b="arity((\<lambda>p. incr_bv(p) ` 7)^11 (\<phi>))" in le_lt_lt, simp)
   apply(rule_tac le_lt_lt)
    apply(rule arity_incr_bv_le)
      apply auto[3]
  apply(rule union_lt2, simp, simp, simp, simp)
  apply(rule iterates_type)
  using assms
  by auto

definition is_least_index_of_Vset_contains_witness_fm where
  "is_least_index_of_Vset_contains_witness_fm(p) \<equiv> 
    Exists(Exists(Exists(
      And(fst_fm(3, 1), 
      And(snd_fm(3, 2), 
      And(least_fm(
        Exists(Exists(
          And(is_MVset_fm(2, 1),
          And(Member(0, 1), 
          And(is_HS_fm(11, 0), ren_least_index(forcesHS(p))))))), 
      0),
      pair_fm(3, 0, 4) 
  ))))))"

(* 
z MVset(a), a, least, y, p, <y, p>, pair, P, leq, one, <\<F>, \<G>, P, P_auto>, ...env

p, P, leq, one, <\<F>, \<G>, P, P_auto>, y, z ...env
 *)


lemma sats_is_least_index_of_Vset_contains_witness_fm_iff : 
  fixes \<phi> u v env
  assumes "\<phi> \<in> formula" "u \<in> M" "v \<in> M" "env \<in> list(M)" 
  shows "sats(M, is_least_index_of_Vset_contains_witness_fm(\<phi>), [u, v, P, leq, one, <\<F>, \<G>, P, P_auto>] @ env) 
        \<longleftrightarrow> v = <u, \<mu> a. a \<in> M \<and> Ord(a) \<and> (\<exists>z \<in> MVset(a) \<inter> HS. snd(u) \<tturnstile>HS \<phi> ([fst(u), z] @ env))>"  

  apply(subgoal_tac "P \<in> M \<and> leq \<in> M \<and> one \<in> M \<and> <\<F>, \<G>, P, P_auto> \<in> M")
  unfolding is_least_index_of_Vset_contains_witness_fm_def
  apply(rule_tac Q=
      "\<exists>p \<in> M.  \<exists>y \<in> M. \<exists>a \<in> M.
          y = fst(u) \<and> p = snd(u) \<and> 
          a = (\<mu> a . \<exists>z \<in> M. \<exists>V \<in> M. a \<in> M \<and> Ord(a) \<and> V = MVset(a) \<and> z \<in> V \<and> z \<in> HS \<and> p \<tturnstile>HS \<phi> [y, z] @ env) \<and> 
          v = <u, a>" in iff_trans) 
    apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)+
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
     apply(rule iff_trans, rule sats_fst_fm, simp, simp, simp add:assms)
  using assms
     apply simp
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
     apply(rule iff_trans, rule sats_snd_fm, simp, simp, simp add:assms)
  using assms  
     apply simp
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
     apply(rule iff_trans, rule sats_least_fm, simp, simp, simp add:assms, simp add:zero_in_M) 
     apply(rule iff_flip, rule iff_trans, rule iff_flip, rule least_abs)
       apply auto[2]
     apply simp 
     apply(rule least_cong, simp, rule iff_flip)
     apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule iff_trans, rule bex_iff)+
       apply(rule sats_And_iff, simp add:assms, rule bex_iff, rule iff_conjI2, rule sats_is_MVset_fm_iff, simp add:assms)
  using assms
          apply auto[5]
     apply(rule iff_trans, rule bex_iff, rule bex_iff, rule iff_conjI2, simp, rule iff_conjI2, simp, rule iff_conjI2)
       apply(rule sats_is_HS_fm_iff, simp add:assms)
  using assms
          apply auto[5]
  using MVset_in_M
     apply simp
     apply(rule bex_iff, rule iff_conjI2, simp, rule iff_conjI2, simp)
  apply(rename_tac p y l a z, rule_tac b="Cons(z, Cons(MVset(a), Cons(a, Cons(l, Cons(fst(u), Cons(snd(u), Cons(u, Cons(v, Cons(P, Cons(leq, Cons(one, Cons(\<langle>\<F>, \<G>, P, P_auto\<rangle>, env))))))))))))" 
                                   and a="[z, MVset(a), a, l, fst(u), snd(u), u, v, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env" in ssubst, simp)
     apply(rule iff_trans, rule sats_ren_least_index_iff)
       apply(rule forcesHS_type)
  using assms fst_snd_closed 
       apply auto[4]
  using pair_in_M_iff fst_snd_closed assms
   apply(rule_tac Q="(\<exists>p\<in>M. \<exists>y\<in>M. \<exists>a\<in>M. y = fst(u) \<and> p = snd(u) \<and> a = (\<mu> a. a \<in> M \<and> Ord(a) \<and> (\<exists>z \<in> MVset(a) \<inter> HS. M, [p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ [y, z] @ env \<Turnstile> forcesHS(\<phi>))) \<and> v = \<langle>u, a\<rangle>)" in iff_trans)
    apply(rule bex_iff)+
    apply(rule iff_conjI2, simp)+
     apply(rule eq_cong, simp)
     apply(rule Least_cong)
     apply(rule iff_conjI2, simp)+
  using MVset_in_M
     apply simp
     apply(rule iffI, force)
     apply clarify 
     apply(rename_tac p y a b z, rule_tac x=z in bexI, force)
  using MVset_in_M transM 
     apply auto[3]
  using P_in_M leq_in_M one_in_M \<F>_in_M \<G>_in_M P_auto_in_M pair_in_M_iff
  by auto

lemma is_least_index_of_Vset_contains_witness_fm_type : 
  fixes \<phi>  
  assumes "\<phi> \<in> formula"
  shows "is_least_index_of_Vset_contains_witness_fm(\<phi>) \<in> formula" 

  unfolding is_least_index_of_Vset_contains_witness_fm_def
  apply(subgoal_tac "fst_fm(3, 1) \<in> formula \<and> snd_fm(3, 2) \<in> formula \<and> is_MVset_fm(2, 1) \<in> formula \<and> is_HS_fm(11, 0) \<in> formula \<and> ren_least_index(forcesHS(\<phi>)) \<in> formula")
   apply force
  apply(rule conjI, simp add:fst_fm_def)
  apply(rule conjI, simp add:snd_fm_def)
  apply(rule conjI, rule is_MVset_fm_type, simp, simp, rule conjI)
   apply(rule is_HS_fm_type, simp, simp)
  unfolding ren_least_index_def 
  apply(rule Exists_type)+
  apply(rule And_type, simp)+
  apply(rule iterates_type)
  using assms forcesHS_type 
    apply auto[2]
  apply(rule function_value_in)
  using incr_bv_type 
  by auto

lemma arity_least_fm : 
  fixes p i
  assumes "p \<in> formula" "i \<in> nat" 
  shows "arity(least_fm(p, i)) \<le> pred(arity(p)) \<union> succ(i)" 
  unfolding least_fm_def 
  apply simp
  apply(subst arity_ordinal_fm, simp add:assms)
  apply(subst arity_empty_fm, simp add:assms) 
  using assms
  apply(rule_tac Un_least_lt, simp, rule_tac ltI, simp, simp)+
    apply(rule ltD, rule Un_least_lt, simp, rule_tac ltI, simp, simp)
    apply(rule pred_le, simp, simp, rule Un_least_lt, simp)
    apply(rule_tac n="arity(p)" in natE, simp, simp)
    apply(subst succ_Un_distrib, simp, simp)
    apply(subst succ_pred_eq, simp, simp)
    apply(subst succ_Un_distrib, simp, simp)
    apply(rule ltI, simp, simp, simp)
  apply(rule Un_least_lt)
   apply(rule pred_le, simp_all)
   apply(rule Un_least_lt)
    apply(subst succ_Un_distrib, simp, simp)
    apply(rule_tac n="arity(p)" in natE, simp, simp)
    apply(subst succ_Un_distrib, simp, simp)
    apply(subst succ_pred_eq, simp, simp)
    apply(rule ltI, simp, simp)
   apply(rule Un_least_lt, simp, simp)
   apply(rule ltI, simp, simp)
  apply(rule pred_le, simp, simp)
  apply(rule Un_least_lt)+
    apply(simp)                 
   apply(rule Un_least_lt)+
    apply (simp, simp, rule ltI, simp, simp)
    apply(rule_tac n="arity(p)" in natE, simp, simp)
    apply(subst succ_Un_distrib, simp, simp)
    apply(subst succ_pred_eq, simp, simp)
    apply(rule ltI)
   apply(subst succ_Un_distrib, simp, simp, simp, simp)
  done

lemma arity_is_least_index_of_Vset_contains_witness_fm : 
  fixes \<phi>  
  assumes "\<phi> \<in> formula"
  shows "arity(is_least_index_of_Vset_contains_witness_fm(\<phi>)) \<le> 4 #+ (2 \<union> arity(\<phi>))" 

  apply(subgoal_tac "fst_fm(3, 1) \<in> formula \<and> snd_fm(3, 2) \<in> formula \<and> is_MVset_fm(2, 1) \<in> formula \<and> is_HS_fm(11, 0) \<in> formula \<and> ren_least_index(forcesHS(\<phi>)) \<in> formula")
  unfolding is_least_index_of_Vset_contains_witness_fm_def
   apply simp
   apply(rule pred_le, force, force)+
   apply(subst arity_fst_fm, simp, simp)
   apply(subst arity_snd_fm, simp, simp)
   apply(rule Un_least_lt)+
     apply auto[2]
   apply(rule Un_least_lt)+
     apply auto[2]
   apply(rule Un_least_lt, rule le_trans) 
     apply(subst arity_least_fm, force, simp, simp)
    apply(rule Un_least_lt, rule pred_le, force, force, simp)
     apply(rule pred_le, force, force)
     apply(rule pred_le, force, force)+
     apply(rule Un_least_lt, rule le_trans, rule arity_is_MVset_fm, simp, simp)
      apply(rule Un_least_lt, simp, simp)+
     apply(rule Un_least_lt)+
       apply (simp, simp)
     apply(rule Un_least_lt)+
      apply(rule le_trans,rule arity_is_HS_fm, simp, simp)
      apply(rule Un_least_lt)+
  using assms
       apply auto[2]
  apply(rule union_lt1, simp, simp, simp, simp)
     apply(rule le_trans, rule arity_ren_least_index)
  using assms forcesHS_type  
       apply auto[1]
  using forcesHS_def
      apply simp
      apply(rule ltI, simp)
  using assms forcesHS'_type 
      apply force
     apply simp
     apply(rule Un_least_lt)
  using assms
      apply simp
      apply(rule union_lt1, simp, simp, simp, simp, simp)
     apply(insert forcesHS_type[where \<phi>=\<phi>])
  using assms
     apply simp
     apply(rule le_trans, rule arity_forcesHS)
  using assms
      apply auto[2]
     apply(rule max_le2, simp, simp, simp)
   apply(subst arity_pair_fm, simp, simp, simp, simp)
   apply(rule Un_least_lt, simp)+
   apply simp
  using fst_fm_def snd_fm_def is_MVset_fm_type is_HS_fm_type ren_least_index_type forcesHS_type assms
  apply auto
  done

definition least_indexes_of_Vset_contains_witness where 
  "least_indexes_of_Vset_contains_witness(\<phi>, env, x) \<equiv> { <<y, p>, (\<mu> a. a \<in> M \<and> Ord(a) \<and> (\<exists>z \<in> MVset(a) \<inter> HS. p \<tturnstile>HS \<phi> ([y, z] @ env)))>. <y, p> \<in> domain(x) \<times> P }"

lemma least_indexes_of_Vset_contains_witness_in_M : 
  fixes \<phi> env x 
  assumes "\<phi> \<in> formula" "env \<in> list(M)" "arity(\<phi>) \<le> 2 #+ length(env)" "x \<in> M" "is_least_index_of_Vset_contains_witness_fm(\<phi>) \<in> \<Phi>"
  shows "least_indexes_of_Vset_contains_witness(\<phi>, env, x) \<in> M" 
proof -
  have strep : "strong_replacement(##M, \<lambda>u v. sats(M, is_least_index_of_Vset_contains_witness_fm(\<phi>), [u, v] @ [P, leq, one, <\<F>, \<G>, P, P_auto>] @ env))" 
    apply(rule replacement_ax, rule is_least_index_of_Vset_contains_witness_fm_type)
    using assms \<F>_in_M \<G>_in_M P_in_M P_auto_in_M leq_in_M one_in_M pair_in_M_iff
      apply auto[3]
    apply(rule le_trans, rule arity_is_least_index_of_Vset_contains_witness_fm)
    using assms Un_least_lt
      apply simp_all
    done

  have strep' : "strong_replacement(##M, \<lambda>u v. v = <u, (\<mu> a. a \<in> M \<and> Ord(a) \<and> (\<exists>z \<in> MVset(a) \<inter> HS. snd(u) \<tturnstile>HS \<phi> ([fst(u), z] @ env)))>)" 
    apply(rule iffD1, rule strong_replacement_cong)
     apply(rule sats_is_least_index_of_Vset_contains_witness_fm_iff)
    using assms strep 
    by auto

  have H : "{ <u, (\<mu> a. a \<in> M \<and> Ord(a) \<and> (\<exists>z \<in> MVset(a) \<inter> HS. snd(u) \<tturnstile>HS \<phi> ([fst(u), z] @ env)))> . u \<in> domain(x) \<times> P } \<in> M" (is "?A \<in> M")
    apply(subgoal_tac "domain(x) \<times> P \<in> M")
    apply(rule to_rin, rule RepFun_closed, rule strep', simp)
    apply(rule ballI, rule pair_in_MI, rule conjI)
    using transM 
      apply auto[1]
     apply(rule Least_closed, simp)
    using domain_closed cartprod_closed P_in_M assms
    by auto

  have "?A = least_indexes_of_Vset_contains_witness(\<phi>, env, x)" 
    unfolding least_indexes_of_Vset_contains_witness_def
    apply(rule equality_iffI, rule iffI)
     apply force
    apply force
    done

  then show ?thesis using H by auto
qed

lemma ex_hs_subset_contains_witnesses : 
  fixes \<phi> env x 
  assumes "\<phi> \<in> formula" "env \<in> list(M)" "arity(\<phi>) \<le> 2 #+ length(env)" "x \<in> M" "is_least_index_of_Vset_contains_witness_fm(\<phi>) \<in> \<Phi>"
  shows "\<exists>S. S \<in> M \<and> S \<subseteq> HS \<and> (\<forall>p \<in> G. \<forall>y \<in> domain(x). (\<exists>z \<in> HS. p \<tturnstile>HS \<phi> ([y, z] @ env)) \<longleftrightarrow> (\<exists>z \<in> S. p \<tturnstile>HS \<phi> ([y, z] @ env)))" 
proof-  
  define A where "A \<equiv> least_indexes_of_Vset_contains_witness(\<phi>, env, x)" 
  define contains_witness where "contains_witness \<equiv> \<lambda>y p a. a \<in> M \<and> Ord(a) \<and> (\<exists>z \<in> MVset(a) \<inter> HS. p \<tturnstile>HS \<phi> ([y, z] @ env))" 

  have contains_witness_mono : 
    "\<And>a b y p. Ord(a) \<Longrightarrow> Ord(b) \<Longrightarrow> b \<in> M \<Longrightarrow> a \<le> b \<Longrightarrow> contains_witness(y, p, a) \<Longrightarrow> contains_witness(y, p, b)" 
    unfolding contains_witness_def MVset_def 
    apply(rename_tac a b y p, subgoal_tac "Vset(a) \<subseteq> Vset(b)")
     apply force 
    apply(rule subsetI)
    apply(rename_tac a b y p x, subgoal_tac "rank(x) < a")
    apply(rule VsetI)
     apply(rename_tac a b y p x, rule_tac b=a in lt_le_lt, simp, simp)
    using Vset_Ord_rank_iff
    by auto

  have Aeq: "A = { <<y, p>, (\<mu> a. contains_witness(y, p, a))> . <y, p> \<in> domain(x) \<times> P }" 
    unfolding contains_witness_def A_def least_indexes_of_Vset_contains_witness_def
    by auto

  have "A \<in> M" 
    unfolding A_def 
    apply(rule least_indexes_of_Vset_contains_witness_in_M)
    using assms
    by auto

  then have "range(A) \<in> M" 
    using range_closed 
    by auto

  define \<alpha> where "\<alpha> \<equiv> \<Union>range(A)" 

  have "\<And>a. a \<in> range(A) \<Longrightarrow> Ord(a)" 
    unfolding A_def least_indexes_of_Vset_contains_witness_def
    by auto

  then have "Ord(\<alpha>)" 
    using Ord_Union \<alpha>_def
    by simp

  have "\<alpha> \<in> M" using \<open>range(A) \<in> M\<close> Union_closed \<alpha>_def by auto

  have H : "\<And>y p. y \<in> domain(x) \<Longrightarrow> p \<in> P \<Longrightarrow> (\<exists>z \<in> HS. p \<tturnstile>HS \<phi> ([y, z] @ env)) \<Longrightarrow> (\<exists>z \<in> MVset(\<alpha>) \<inter> HS. p \<tturnstile>HS \<phi> ([y, z] @ env))"
  proof - 
    fix y p 
    assume assms1 : "y \<in> domain(x)" "p \<in> P" "\<exists>z \<in> HS. p \<tturnstile>HS \<phi> ([y, z] @ env)" 

    then obtain z where zH : "z \<in> HS" "p \<tturnstile>HS \<phi> ([y, z] @ env)" by auto
    have "contains_witness(y, p, succ(rank(z)))" 
      unfolding contains_witness_def 
      apply(insert HS_iff P_name_in_M rank_closed succ_in_MI Ord_rank zH)
      apply(rule_tac conjI, force)+
      apply(rule_tac x=z in bexI)
       apply simp 
      apply simp
      apply(rule MVsetI)
      by auto
    then have H: "contains_witness(y, p, \<mu> a. contains_witness(y, p, a))" 
      apply(rule_tac LeastI)
      using Ord_rank
      by auto

    have "<<y, p>, (\<mu> a. contains_witness(y, p, a))> \<in> A" 
      unfolding A_def contains_witness_def least_indexes_of_Vset_contains_witness_def
      using assms1 
      by auto
    then have "(\<mu> a. contains_witness(y, p, a)) \<in> range(A)" by auto 
    then have "(\<mu> a. contains_witness(y, p, a)) \<le> \<alpha>" 
      using \<open>Ord(\<alpha>)\<close>
      unfolding \<alpha>_def
      apply(rule_tac Union_upper_le)
      by auto
    then have H' : "contains_witness(y, p, \<alpha>)" 
      apply(rule_tac contains_witness_mono[of "(\<mu> a. contains_witness(y, p, a))"])
      using \<open>Ord(\<alpha>)\<close> \<open>\<alpha> \<in> M\<close> H
      by auto

    then show "(\<exists>z \<in> MVset(\<alpha>) \<inter> HS. p \<tturnstile>HS \<phi> ([y, z] @ env))" 
      unfolding contains_witness_def 
      by auto
  qed

  show ?thesis 
    apply(rule_tac x="MVset(\<alpha>) \<inter> HS" in exI)
    apply(rule conjI, rule HS_separation)
    apply(rule MVset_in_M)
    using \<open>Ord(\<alpha>)\<close> \<open>\<alpha> \<in> M\<close>
      apply auto[2]
    apply(rule conjI, force)
    apply(rule ballI)+
    apply(rule iffI)
     apply(rule H)
    using generic M_genericD 
    by auto
qed

lemma ex_SymExt_elem_contains_witnesses : 
  fixes \<phi> env x 
  assumes "\<phi> \<in> formula" "env \<in> list(SymExt(G))" "arity(\<phi>) \<le> 2 #+ length(env)" "x \<in> SymExt(G)" 
          "is_least_index_of_Vset_contains_witness_fm(\<phi>) \<in> \<Phi>" "forcesHS_fms(\<phi>) \<subseteq> \<Phi>"
  shows "\<exists>S \<in> SymExt(G). \<forall>y \<in> x. ((\<exists>z \<in> SymExt(G). sats(SymExt(G), \<phi>, [y, z] @ env)) \<longleftrightarrow> (\<exists>z \<in> S. sats(SymExt(G), \<phi>, [y, z] @ env)))"
proof - 
  obtain x' where x'H : "x' \<in> HS" "val(G, x') = x" using SymExt_def assms by auto
  have "\<exists>env' \<in> list(HS). map(val(G), env') = env" 
    apply(rule ex_HS_name_list)
    using assms
    by auto
  then obtain env' where env'H: "env' \<in> list(HS)" "map(val(G), env') = env" using assms by auto
  then have leneq : "length(env') = length(env)" by auto
  have env'in : "env' \<in> list(M)" 
    apply(rule_tac A="list(HS)" in subsetD, rule list_mono)
    using HS_iff P_name_in_M env'H
    by auto

  have "\<exists>S. S \<in> M \<and> S \<subseteq> HS \<and> (\<forall>p \<in> G. \<forall>y \<in> domain(x'). (\<exists>z \<in> HS. p \<tturnstile>HS \<phi> ([y, z] @ env')) \<longleftrightarrow> (\<exists>z \<in> S. p \<tturnstile>HS \<phi> ([y, z] @ env')))" 
    apply(rule ex_hs_subset_contains_witnesses)
    using assms env'in HS_iff P_name_in_M app_type x'H leneq
    by auto
  then obtain S where SH: "S \<in> M" "S \<subseteq> HS" "(\<forall>p \<in> G. \<forall>y \<in> domain(x'). (\<exists>z \<in> HS. p \<tturnstile>HS \<phi> ([y, z] @ env')) \<longleftrightarrow> (\<exists>z \<in> S. p \<tturnstile>HS \<phi> ([y, z] @ env')))" by auto
  then have "\<exists>T \<in> SymExt(G). { val(G, x). x \<in> S } \<subseteq> T" 
    apply(rule_tac ex_separation_base)
    by auto
  then obtain T where TH: "T \<in> SymExt(G)" "{ val(G, x). x \<in> S } \<subseteq> T" by auto 

  show ?thesis
  proof(rule_tac x=T in bexI, rule ballI)
    fix y assume yin : "y \<in> x" 
    have "\<exists>y' \<in> domain(x') . \<exists>p \<in> G. val(G, y') = y \<and> <y', p> \<in> x'" 
      apply(rule_tac P="y \<in> val(G, x')" in mp)
       apply(subst def_val, force)
      using yin x'H 
      by auto
    then obtain y' p where y'pH: "y' \<in> domain(x')" "val(G, y') = y" "p \<in> G" by auto
    then have y'inHS : "y' \<in> HS" using x'H HS_iff by auto

    have "(\<exists>z\<in>SymExt(G). SymExt(G), [y, z] @ env \<Turnstile> \<phi>) \<longleftrightarrow> (\<exists>z'\<in>HS. SymExt(G), map(val(G), [y', z'] @ env') \<Turnstile> \<phi>)"
      unfolding SymExt_def 
      using y'pH env'H 
      by auto
    also have "... \<longleftrightarrow> (\<exists>z'\<in>HS. \<exists>q \<in> G. q \<tturnstile>HS \<phi> [y', z'] @ env')"
      apply(rule bex_iff, rule iff_flip)
      apply(rule HS_truth_lemma)
      using assms generic y'pH x'H env'H y'inHS leneq
      by auto
    also have "... \<longleftrightarrow> (\<exists>q \<in> G. \<exists>z'\<in>HS. q \<tturnstile>HS \<phi> [y', z'] @ env')" by auto
    also have "... \<longleftrightarrow> (\<exists>q \<in> G. \<exists>z' \<in> S. q \<tturnstile>HS \<phi> ([y', z'] @ env'))" 
      apply(rule bex_iff)
      using y'pH SH
      by auto
    also have "... \<longleftrightarrow> (\<exists>z' \<in> S. \<exists>q \<in> G. q \<tturnstile>HS \<phi> ([y', z'] @ env'))" by auto
    also have "... \<longleftrightarrow> (\<exists>z' \<in> S. sats(SymExt(G), \<phi>, map(val(G), [y', z'] @ env')))" 
      apply(rule bex_iff, rule HS_truth_lemma)
      using assms generic SH env'H y'inHS
      by auto
    also have "... \<longleftrightarrow> (\<exists>z' \<in> S. sats(SymExt(G), \<phi>, [y, val(G, z')] @ env))" using y'pH env'H by auto
    finally have "(\<exists>z\<in>SymExt(G). SymExt(G), [y, z] @ env \<Turnstile> \<phi>) \<longleftrightarrow> (\<exists>z'\<in>S. SymExt(G), [y, val(G, z')] @ env \<Turnstile> \<phi>) " by auto

    then show "(\<exists>z\<in>SymExt(G). SymExt(G), [y, z] @ env \<Turnstile> \<phi>) \<longleftrightarrow> (\<exists>z\<in>T. SymExt(G), [y, z] @ env \<Turnstile> \<phi>)"
      using TH SymExt_trans
      by auto
  next 
    show "T \<in> SymExt(G)" using TH by auto
  qed
qed

definition SymExt_replacement_fms where 
  "SymExt_replacement_fms(\<phi>, l) \<equiv> 
      forcesHS_fms(\<phi>) \<union> {is_least_index_of_Vset_contains_witness_fm(\<phi>)} 
      \<union> SymExt_separation_fms(Exists(And(Member(0, 2 #+ l), \<phi>)), succ(l))" 

lemma SymExt_replacement :
  fixes \<phi> env
  assumes "\<phi> \<in> formula" "arity(\<phi>) \<le> 2 #+ length(env)" "env \<in> list(SymExt(G))" "SymExt_replacement_fms(\<phi>, length(env)) \<subseteq> \<Phi>"
  shows "strong_replacement(##SymExt(G), \<lambda>x y. sats(SymExt(G), \<phi>, [x, y] @ env))" 

  unfolding strong_replacement_def 
proof(rule rallI, rule impI)

  fix X
  assume assms1 : "(##SymExt(G))(X)" "univalent(##SymExt(G), X, \<lambda>x y. (SymExt(G), [x, y] @ env \<Turnstile> \<phi>))"

  have "\<exists>Y \<in> SymExt(G). \<forall>x \<in> X. ((\<exists>y \<in> SymExt(G). sats(SymExt(G), \<phi>, [x, y] @ env)) \<longleftrightarrow> (\<exists>y \<in> Y. sats(SymExt(G), \<phi>, [x, y] @ env)))"
    apply(rule ex_SymExt_elem_contains_witnesses)
    using assms assms1 SymExt_replacement_fms_def
    by auto
  then obtain Y where YH : "Y \<in> SymExt(G)" "\<forall>x \<in> X. ((\<exists>y \<in> SymExt(G). sats(SymExt(G), \<phi>, [x, y] @ env)) \<longleftrightarrow> (\<exists>y \<in> Y. sats(SymExt(G), \<phi>, [x, y] @ env)))" by auto

  define \<psi> where "\<psi> \<equiv> Exists(And(Member(0, 2 #+ length(env)), \<phi>))" 

  have \<psi>_type : "\<psi> \<in> formula" 
    unfolding \<psi>_def 
    using assms
    by auto

  have arity_\<psi> : "arity(\<psi>) \<le> 2 #+ length(env)" 
    unfolding \<psi>_def
    using assms
    apply simp
    apply(rule pred_le)
    using assms
    apply auto[2]
    apply(rule Un_least_lt)+
      apply auto[2]
    apply(rule_tac j="2 #+ length(env)" in le_trans) 
    by auto

  define U where "U \<equiv> { y \<in> Y . \<exists>x \<in> X. sats(SymExt(G), \<phi>, [x, y] @ env) }" 

  have "U = { y \<in> Y. \<exists>x \<in> X. sats(SymExt(G), \<phi>, ([x, y] @ env) @ [X]) }" 
    unfolding U_def 
    apply(rule iff_eq, rule bex_iff, rule iff_flip)
    apply(rule arity_sats_iff)
    using assms assms1 SymExt_trans YH
    by auto 
  also have "... = { y \<in> Y . sats(SymExt(G), \<psi>, [y] @ env @ [X]) }" (is "_ = ?A") 
    unfolding U_def \<psi>_def
    apply(rule iff_eq)
    apply(rename_tac y, subgoal_tac "y \<in> SymExt(G)")
    using assms assms1 
     apply simp 
     apply(subst nth_append, simp, simp, subst if_not_P, force)
    using SymExt_trans YH 
    by auto
  finally have "U = { y \<in> Y . sats(SymExt(G), \<psi>, [y] @ env @ [X]) }" (is "_ = ?A") by simp

  have "?A \<in> SymExt(G)" 
    apply(rule SymExt_separation)
    using YH assms assms1 \<psi>_type arity_\<psi> SymExt_replacement_fms_def \<psi>_def
    by auto
  then have "U \<in> SymExt(G)" using \<open>U = ?A\<close> by simp

  have "\<And>y. y \<in> SymExt(G) \<Longrightarrow> y \<in> U \<longleftrightarrow> (\<exists>x \<in> X. sats(SymExt(G), \<phi>, [x, y] @ env))" 
    unfolding U_def 
  proof(rule iffI, force)
    fix y 
    assume assms2: "y \<in> SymExt(G)" "y \<in> SymExt(G)" "\<exists>x\<in>X. SymExt(G), [x, y] @ env \<Turnstile> \<phi>" 
    then obtain x where xH: "x \<in> X" "SymExt(G), [x, y] @ env \<Turnstile> \<phi>" by auto

    then have "\<exists>y \<in> SymExt(G). sats(SymExt(G), \<phi>, [x, y] @ env)" using assms2 xH by auto
    then have "\<exists>y \<in> Y. sats(SymExt(G), \<phi>, [x, y] @ env)" using YH xH by auto
    then obtain z where zH: "z \<in> Y" "z \<in> SymExt(G)" "sats(SymExt(G), \<phi>, [x, z] @ env)" using YH SymExt_trans by auto

    have univalentE : "\<And>x y z. x \<in> X \<Longrightarrow> y \<in> SymExt(G) \<Longrightarrow> z \<in> SymExt(G) \<Longrightarrow> (SymExt(G), [x, y] @ env \<Turnstile> \<phi>) \<Longrightarrow> (SymExt(G), [x, z] @ env \<Turnstile> \<phi>) \<Longrightarrow> y = z"
      using assms1 SymExt_trans 
      unfolding univalent_def 
      by auto

    have "y = z" 
      apply(rule univalentE)
      using assms1 xH assms2 zH 
      by auto
    then have "y \<in> Y" using zH by auto
    then show "y \<in> {y \<in> Y . \<exists>x\<in>X. SymExt(G), [x, y] @ env \<Turnstile> \<phi>}" 
      using assms2 
      by auto
  qed
  then show "\<exists>Y[##SymExt(G)]. \<forall>b[##SymExt(G)]. b \<in> Y \<longleftrightarrow> (\<exists>x[##SymExt(G)]. x \<in> X \<and> SymExt(G), [x, b] @ env \<Turnstile> \<phi>)" 
    apply(rule_tac x=U in rexI)
     apply(rule rallI)
    using assms1 SymExt_trans
     apply force 
    using \<open>U \<in> SymExt(G)\<close>
    by simp
qed


end
end