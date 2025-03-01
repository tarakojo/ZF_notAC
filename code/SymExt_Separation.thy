theory SymExt_Separation
  imports 
    "Forcing/Forcing_Main" 
    HS_Forces
    Symmetry_Lemma
begin 

context M_symmetric_system_G_generic
begin


definition INTsym where "INTsym(l) \<equiv> (\<Inter>H \<in> set_of_list(map(sym, l)). H)"

lemma INT_set_of_list_of_\<F>_lemma : 
  fixes l 
  assumes "l \<in> list(HS)" "l \<noteq> Nil"
  shows "INTsym(l) \<in> \<F> \<and> (\<forall>\<pi> \<in> INTsym(l). map(\<lambda>x. Pn_auto(\<pi>)`x, l) = l)"

  unfolding INTsym_def
  using assms 
proof (induct)
  case Nil
  then show ?case by auto 
next 
  case (Cons a l)
  then show ?case
  proof - 
    assume assms : "a \<in> HS" "l \<in> list(HS)"
      "(l \<noteq> [] \<Longrightarrow> (\<Inter>H\<in>set_of_list(map(sym, l)). H) \<in> \<F> \<and> (\<forall>\<pi>\<in>\<Inter>H\<in>set_of_list(map(sym, l)). H. map(\<lambda>a. Pn_auto(\<pi>) ` a, l) = l))" 
    show ?thesis 
      using \<open>l \<in> list(HS)\<close> 
    proof(cases)
      case Nil
      then have lnil : "l = Nil" by simp
      then have "(\<Inter>H\<in>set_of_list(Cons(a, l)). H) = a" using assms by auto 
      then show ?thesis using lnil assms HS_iff symmetric_def sym_def by auto
    next
      case (Cons b l')

      then have bl'H : "l = Cons(b, l')" "b \<in> HS" "l' \<in> list(HS)" by auto
      then have neq0 : "set_of_list(l) \<noteq> 0" by auto

      have "(\<Inter>H\<in>set_of_list(map(sym, Cons(a, l))). H) = (\<Inter>H\<in>{sym(a)} \<union> set_of_list(map(sym, l)). H)" by auto 
      also have "... = (\<Inter>H\<in>{sym(a)}. H) \<inter> (\<Inter>H\<in>set_of_list(map(sym, l)). H)" 
        apply (subst INT_Un) 
        using bl'H 
        by auto
      finally have eq: "(\<Inter>H\<in>set_of_list(map(sym, Cons(a, l))). H) = sym(a) \<inter> (\<Inter>H\<in>set_of_list(map(sym, l)). H)" by auto

      have " (\<Inter>H\<in>set_of_list(map(sym, l)). H) \<in> \<F>" using assms bl'H by auto
      then have in\<F> : "(\<Inter>H\<in>set_of_list(map(sym, Cons(a, l))). H) \<in> \<F>" 
        apply(subst eq)
        using \<F>_closed_under_intersection assms HS_iff symmetric_def bl'H 
        by auto

      have "\<forall>\<pi>\<in>\<Inter>H\<in>set_of_list(map(sym, Cons(a, l))). H. map(\<lambda>a. Pn_auto(\<pi>) ` a, Cons(a, l)) = Cons(a, l)"
      proof (rule ballI)
        fix \<pi> assume piH : "\<pi>\<in>(\<Inter>H\<in>set_of_list(map(sym, Cons(a, l))). H)"
        then have fixa : "Pn_auto(\<pi>)`a = a" using eq sym_def by auto 
        have "map(\<lambda>a. Pn_auto(\<pi>)`a, l) = l" using assms bl'H piH eq by auto
        then show "map(\<lambda>a. Pn_auto(\<pi>) ` a, Cons(a, l)) = Cons(a, l)" using fixa by auto
      qed
      then show ?thesis using in\<F> by auto
    qed
  qed
qed

definition ren_sep_forces where
  "ren_sep_forces(\<phi>) \<equiv> Exists(Exists(Exists(Exists(Exists(
      And(Equal(0, 6), And(Equal(1, 8), And(Equal(2, 9), And(Equal(3, 10), And(Equal(4, 11), 
      iterates(\<lambda>p. incr_bv(p)`6 , 6, \<phi>)))))))))))" 

lemma ren_sep_forces_type : "\<phi> \<in> formula \<Longrightarrow> ren_sep_forces(\<phi>) \<in> formula" 
  unfolding ren_sep_forces_def 
  apply(subgoal_tac "(\<lambda>p. incr_bv(p) ` 6)^6 (\<phi>) \<in> formula")
   apply force 
  apply(rule iterates_type, simp, simp)
  apply(rule function_value_in, rule incr_bv_type)
  by auto

lemma arity_ren_sep_forces : 
  fixes \<phi> 
  assumes "\<phi> \<in> formula" 
  shows "arity(ren_sep_forces(\<phi>)) \<le> succ(arity(\<phi>)) \<union> 7" 

  unfolding ren_sep_forces_def 
  apply(subgoal_tac "(\<lambda>p. incr_bv(p) ` 6)^6 (\<phi>) \<in> formula")
  using assms
   apply simp
   apply(rule pred_le, simp, simp)+
   apply(rule Un_least_lt, rule Un_least_lt, simp, simp, rule union_lt2, simp, simp, simp, simp)+
   apply(rule_tac j="arity((\<lambda>p. incr_bv(p) ` 6)^6 (\<phi>))" in le_trans, force)
   apply(rule le_trans, rule arity_incr_bv_le)
  using assms
      apply auto[4]
   apply(rule union_lt1, simp, simp, simp, simp)
  apply(rule iterates_type, simp, simp add:assms)
  apply(rule function_value_in)
  using incr_bv_type 
  by auto

lemma sats_ren_sep_forces_fm_iff  : 
  fixes \<phi> a b c d e f g env 
  assumes "\<phi> \<in> formula" "[a, b, c, d, e, f, g] @ env \<in> list(M)" 
  shows "sats(M, ren_sep_forces(\<phi>), [a, b, c, d, e, f, g] @ env) \<longleftrightarrow> sats(M, \<phi>, [b, d, e, f, g, a] @ env)" 
  unfolding ren_sep_forces_def 
   apply (insert sats_incr_bv_iff [of _ _ M _ "[b,  d, e, f, g, a]"])
  using assms
  by simp

definition sep_forces_pair_fm where 
  "sep_forces_pair_fm(\<phi>) \<equiv> Exists(Exists(And(pair_fm(0, 1, 2), ren_sep_forces(forcesHS(\<phi>)))))" 

lemma sats_sep_forces_pair_fm_iff : 
  fixes \<phi> y p env
  assumes "\<phi> \<in> formula" "y \<in> HS" "p \<in> P" "env \<in> list(HS)"  
  shows "sats(M, sep_forces_pair_fm(\<phi>), [<y, p>, P, leq, one, <\<F>, \<G>, P, P_auto>] @ env) \<longleftrightarrow> p \<tturnstile>HS \<phi> [y] @ env" 

  unfolding sep_forces_pair_fm_def 
  apply(subgoal_tac "y \<in> M \<and> p \<in> M \<and> <y, p> \<in> M \<and> env \<in> list(M) \<and> P \<in> M \<and> leq \<in> M \<and> one \<in> M \<and> <\<F>, \<G>, P, P_auto> \<in> M")
   apply simp
   apply(rule_tac Q="sats(M, ren_sep_forces(forcesHS(\<phi>)), [y, p, <y, p>, P, leq, one, <\<F>, \<G>, P, P_auto>] @ env)" in iff_trans)
    apply force 
   apply(rule iff_trans, rule sats_ren_sep_forces_fm_iff)
  using forcesHS_type assms 
     apply auto[3]
  using assms HS_iff P_in_M transM pair_in_M_iff leq_in_M one_in_M \<F>_in_M \<G>_in_M P_auto_in_M P_name_in_M 
  apply simp
  apply(rule_tac A="list(HS)" in subsetD, rule list_mono)
  using assms HS_iff P_name_in_M
  by auto

lemma sep_forces_pair_in_HS : 
  fixes x env \<phi>
  assumes "x \<in> HS" "env \<in> list(HS)" "\<phi> \<in> formula" "arity(\<phi>) \<le> succ(length(env))" 
  shows "{ <y, p> \<in> domain(x) \<times> P. p \<tturnstile>HS \<phi> [y] @ env } \<in> HS"
proof - 
  define X where "X \<equiv> { <y, p> \<in> domain(x) \<times> P. p \<tturnstile>HS \<phi> [y] @ env }" 

  have envin : "env \<in> list(M)" 
    apply(rule_tac A="list(HS)" in subsetD)
     apply(rule list_mono)
    using HS_iff assms P_name_in_M 
    by auto

  have XinM : "X \<in> M" 
  proof - 
    have inM : "{ z \<in> domain(x) \<times> P. sats(M, sep_forces_pair_fm(\<phi>), [z] @ [P, leq, one, <\<F>, \<G>, P, P_auto>] @ env) } \<in> M" 
      apply(rule separation_notation)
       apply(rule separation_ax)
      unfolding sep_forces_pair_fm_def
      using forcesHS_type ren_sep_forces_type assms 
         apply force 
      using pair_in_M_iff P_in_M leq_in_M one_in_M \<F>_in_M \<G>_in_M P_auto_in_M assms envin 
        apply force 
       apply simp
      using forcesHS_type ren_sep_forces_type assms 
       apply(rule_tac pred_le, force, force)+
       apply(rule Un_least_lt)                                                          
        apply (subst arity_pair_fm)
           apply auto[3]
        apply simp
        apply(rule Un_least_lt, simp)+
        apply simp
       apply(rule le_trans, rule arity_ren_sep_forces)
      using forcesHS_type assms 
        apply force 
       apply(rule Un_least_lt, simp)
        apply(rule_tac le_trans, rule arity_forcesHS, simp, simp, simp)
      using domain_closed P_in_M cartprod_closed assms HS_iff P_name_in_M
      by auto

    have "X = { <y, p> \<in> domain(x) \<times> P. sats(M, sep_forces_pair_fm(\<phi>), [<y, p>, P, leq, one, <\<F>, \<G>, P, P_auto>] @ env) }" 
      unfolding X_def 
      apply(rule iff_eq)
      apply clarsimp
      apply(rename_tac y p q, subgoal_tac "y \<in> HS")
      using sats_sep_forces_pair_fm_iff assms 
       apply force 
      using HS_iff assms 
      by auto
    also have "... = { z \<in> domain(x) \<times> P. sats(M, sep_forces_pair_fm(\<phi>), [z, P, leq, one, <\<F>, \<G>, P, P_auto>] @ env) }" 
      by auto
    finally show "X \<in> M" using inM by auto
  qed

  have Xpname : "X \<in> P_names"
    apply(rule iffD2, rule P_name_iff, rule conjI, rule XinM)
    unfolding X_def 
    using assms HS_iff 
    by auto

  define S where "S \<equiv> INTsym(Cons(x, env))" 
  have SH : "S \<in> \<F> \<and> (\<forall>\<pi> \<in> S. map(\<lambda>x. Pn_auto(\<pi>)`x, Cons(x, env)) = Cons(x, env))" 
    unfolding S_def
    apply(rule INT_set_of_list_of_\<F>_lemma) 
    using assms 
    by auto
  then have "\<forall>\<pi> \<in> S. Pn_auto(\<pi>)`x = x" by auto
  then have Ssubsetsymx : "S \<subseteq> sym(x)" unfolding sym_def using \<F>_subset SH P_auto_subgroups_def by auto 
  then have envmapeq : "\<forall>\<pi> \<in> S. map(\<lambda>x. Pn_auto(\<pi>)`x, env) = env" using SH by auto

  have "S \<subseteq> sym(X)" 
  proof(rule subsetI)
    fix \<pi> 
    assume piin : "\<pi> \<in> S" 
    then have piin\<G> : "\<pi> \<in> \<G>" using S_def SH \<F>_subset P_auto_subgroups_def by force

    have "Pn_auto(\<pi>)`X = { <Pn_auto(\<pi>)`y, \<pi>`p> . <y, p> \<in> X }" 
      apply(subst Pn_auto)
      using Xpname
      by auto
    also have "... = X" 
    proof (rule equality_iffI, rule iffI)
      fix v assume "v \<in> {\<langle>Pn_auto(\<pi>) ` y, \<pi> ` p\<rangle> . \<langle>y,p\<rangle> \<in> X}"  
      then have "\<exists>y p. <y, p> \<in> X \<and> v = \<langle>Pn_auto(\<pi>) ` y, \<pi> ` p\<rangle>" 
        apply(rule_tac pair_rel_arg)
        using Xpname relation_def P_name_iff
        by auto
      then obtain y p where ypH: "<y, p> \<in> X" "v = \<langle>Pn_auto(\<pi>) ` y, \<pi> ` p\<rangle>" "p \<in> P"
        using Xpname P_name_iff 
        by auto
      then have yindom : "y \<in> domain(x)" using ypH X_def assms by force 
      then have yinHS : "y \<in> HS" using HS_iff assms by auto

      have indom :  "Pn_auto(\<pi>)`y \<in> domain(x)"
        apply(rule iffD1, rule Pn_auto_domain_closed)
        using assms HS_iff piin yindom Ssubsetsymx
        by auto

      have "\<pi>`p \<tturnstile>HS \<phi> [Pn_auto(\<pi>)`y] @ env \<longleftrightarrow> \<pi>`p \<tturnstile>HS \<phi> [Pn_auto(\<pi>)`y] @ map(\<lambda>x. Pn_auto(\<pi>)`x, env)" (is "?A \<longleftrightarrow> _") 
        apply(subst envmapeq)
        using piin 
        by auto
      also have "... \<longleftrightarrow>  \<pi>`p \<tturnstile>HS \<phi> map(\<lambda>x. Pn_auto(\<pi>)`x, Cons(y, env)) "
        by auto
      also have "... \<longleftrightarrow> p \<tturnstile>HS \<phi> Cons(y, env)" 
        apply(rule iff_flip)
        apply(rule symmetry_lemma)
        using assms piin\<G> \<G>_P_auto_group is_P_auto_group_def yinHS ypH 
        by auto
      finally have "?A" 
        using ypH X_def 
        by auto
      then have "<Pn_auto(\<pi>)`y, \<pi>`p> \<in> X" 
        unfolding X_def 
        using indom P_auto_value ypH piin\<G> \<G>_P_auto_group is_P_auto_group_def
        by auto
      then show "v \<in> X" using ypH by auto
    next 
      fix v 
      assume "v \<in> X" 
      then have "\<exists>y p. y \<in> domain(x) \<and> p \<in> P \<and> <y, p> = v \<and> p \<tturnstile>HS \<phi> [y]@env" 
        unfolding X_def by auto
      then obtain y p where ypH : "<y, p> = v" "y \<in> domain(x)" "p \<in> P" "p \<tturnstile>HS \<phi> [y]@env" 
        unfolding X_def by blast
      then have yinHS : "y \<in> HS" using HS_iff assms by auto

      have "Pn_auto(\<pi>) \<in> bij(P_names, P_names)" 
        apply(rule Pn_auto_bij)
        using assms piin\<G> \<G>_P_auto_group is_P_auto_group_def yinHS ypH 
        by auto
      then have "Pn_auto(\<pi>) \<in> surj(P_names, P_names)" using bij_is_surj by auto
      then obtain y' where y'H : "Pn_auto(\<pi>)`y' = y" "y' \<in> P_names" unfolding surj_def using yinHS HS_iff by auto
      then have y'inHS : "y' \<in> HS" 
        apply(rule_tac iffD2, rule_tac HS_Pn_auto)
        using piin\<G> yinHS 
        by auto
      then have y'indom : "y' \<in> domain(x)" 
        apply(rule_tac iffD2)
         apply(rule Pn_auto_domain_closed)
        using assms HS_iff piin Ssubsetsymx y'H ypH 
        by auto

      have "\<pi> \<in> bij(P, P)" using piin\<G> \<G>_P_auto_group is_P_auto_group_def is_P_auto_def by auto
      then have "\<pi> \<in> surj(P, P)" using bij_is_surj by auto
      then obtain p' where p'H : "p' \<in> P" "\<pi>`p' = p" using ypH surj_def by auto

      then have "\<pi>`p' \<tturnstile>HS \<phi> [Pn_auto(\<pi>)`y']@env" using ypH y'H p'H by auto 
      then have "\<pi>`p' \<tturnstile>HS \<phi> [Pn_auto(\<pi>)`y']@map(\<lambda>x. Pn_auto(\<pi>)`x, env)" using envmapeq piin by auto
      then have "\<pi>`p' \<tturnstile>HS \<phi> map(\<lambda>x. Pn_auto(\<pi>)`x, Cons(y', env))" by auto
      then have "p' \<tturnstile>HS \<phi> Cons(y', env)" 
        apply(rule_tac iffD2, rule_tac symmetry_lemma)
        using assms piin\<G> \<G>_P_auto_group is_P_auto_group_def p'H y'inHS
        by auto
      then have "<y', p'> \<in> X" 
        unfolding X_def 
        using y'indom p'H 
        by auto
      then have "<Pn_auto(\<pi>)`y', \<pi>`p'> \<in> {\<langle>Pn_auto(\<pi>) ` y, \<pi> ` p\<rangle> . \<langle>y,p\<rangle> \<in> X}" 
        apply(rule_tac pair_relI)
        by simp
      then show "v \<in> {\<langle>Pn_auto(\<pi>) ` y, \<pi> ` p\<rangle> . \<langle>y,p\<rangle> \<in> X}" using ypH y'H p'H by auto
    qed
    finally show "\<pi> \<in> sym(X)"  
      unfolding sym_def 
      using piin\<G>
      by auto
  qed

  have "sym(X) \<in> P_auto_subgroups(\<G>)" 
    apply(rule sym_P_auto_subgroup)
    using Xpname 
    by auto
    
  then have "sym(X) \<in> \<F>" 
    using \<F>_closed_under_supergroup SH \<open>S \<subseteq> sym(X)\<close>
    by auto

  then have "X \<in> HS" 
    using X_def HS_iff assms sym_def symmetric_def Xpname 
    by auto
  
  then show ?thesis 
    unfolding X_def 
    by simp
qed

lemma SymExt_separation : 
  fixes x env \<phi> 
  assumes "x \<in> SymExt(G)" "env \<in> list(SymExt(G))" "\<phi> \<in> formula" "arity(\<phi>) \<le> succ(length(env))" 
  shows "{ y \<in> x. sats(SymExt(G), \<phi>, [y] @ env) } \<in> SymExt(G)"
proof - 
  have "\<exists>env'\<in>list(HS). map(val(G), env') = env" 
    apply(rule ex_HS_name_list)
    using assms
    by auto
  then obtain env' where env'H: "env' \<in> list(HS)" "map(val(G), env') = env" by auto

  have env'in : "env' \<in> list(M)" 
    apply(rule_tac A="list(HS)" in subsetD, rule list_mono)
    using HS_iff P_name_in_M env'H 
    by auto

  have leneq : "length(env') = length(env)" using env'H length_map by auto

  obtain x' where x'H : "val(G, x') = x" "x' \<in> HS" using assms SymExt_def by auto 

  define X where "X \<equiv> { <y, p> \<in> domain(x') \<times> P. p \<tturnstile>HS And(Member(0, succ(length(env'))), \<phi>) [y] @ env' @ [x'] }"  
  have "X \<in> HS" 
    unfolding X_def 
    apply(rule sep_forces_pair_in_HS)
    using assms x'H env'H leneq
       apply auto[3]
    apply simp
    apply(rule Un_least_lt)+
    using assms x'H env'H leneq
      apply auto[2]
    apply(rule_tac j="succ(length(env))" in le_trans)
    using assms x'H env'H leneq
    by auto
  then have "val(G, X) \<in> SymExt(G)" using SymExt_def by auto

  define Y where "Y \<equiv> { y \<in> x. sats(SymExt(G), \<phi>, [y] @ env) }" 

  have "val(G, X) = Y" 
  proof (rule equality_iffI)
    fix y

    have "y \<in> val(G, X) \<longleftrightarrow> (\<exists>y' \<in> domain(x'). val(G, y') = y \<and> (\<exists>p \<in> G. <y', p> \<in> X))"
      apply(subst def_val, rule iffI)
      using X_def
       apply force
      apply clarsimp
      apply(rename_tac y' p q, rule_tac x=y' in bexI, rule conjI, simp)
       apply(rename_tac y' p q, rule_tac x=q in bexI, simp)
      using M_genericD generic 
      by auto
    also have "... \<longleftrightarrow> (\<exists>y' \<in> domain(x'). val(G, y') = y \<and> (\<exists>p \<in> G. p \<tturnstile>HS And(Member(0, succ(length(env'))), \<phi>) [y'] @ env' @ [x']))" 
      unfolding X_def
      using M_genericD generic 
      by auto
    also have "... \<longleftrightarrow> (\<exists>y' \<in> domain(x'). val(G, y') = y \<and> sats(SymExt(G), And(Member(0, succ(length(env'))), \<phi>), map(val(G), [y'] @ env' @ [x'])))"
      apply(rule bex_iff, rule iff_conjI2, simp) 
      apply(rule HS_truth_lemma)
      using env'H assms generic x'H HS_iff
         apply auto[2] 
      using env'H assms generic x'H 
       apply simp
       apply(rule conjI)
      using HS_iff 
        apply blast
       apply(rule app_type)
        apply auto[2]
       apply simp
      apply(rule Un_least_lt)+
      using env'H x'H length_app 
        apply auto[2]
      apply(rule_tac j="succ(length(env))" in le_trans)
      using assms env'H x'H 
      by auto
    also have "... \<longleftrightarrow> (\<exists>y' \<in> domain(x'). val(G, y') = y \<and> y \<in> x \<and> sats(SymExt(G), \<phi>, [y] @ map(val(G), env' @ [x'])))"
      apply(rule bex_iff, rule iff_conjI2, simp)
      apply(rename_tac y', subgoal_tac "map(val(G), [y'] @ env' @ [x']) \<in> list(SymExt(G))") 
       apply simp
       apply (rule iff_conjI2)
      using env'H 
        apply simp
        apply(subst nth_map)
      using env'H x'H 
           apply auto[3]
        apply(subst nth_append)
      using env'H x'H
          apply auto[4]
      apply(rule_tac A=HS in map_type)
       apply simp
       apply(rule conjI)
      using HS_iff x'H env'H
        apply blast
       apply(rule app_type)
      using env'H x'H SymExt_def 
      by auto
    also have "... \<longleftrightarrow> (\<exists>y' \<in> domain(x'). val(G, y') = y \<and> y \<in> x \<and> sats(SymExt(G), \<phi>, [y] @ env @ [x]))"
      apply(rule bex_iff)
      apply(rule iff_conjI2, simp)+
      apply(subst map_app_distrib[where A=HS])
      using env'H x'H 
      by auto
    also have "... \<longleftrightarrow> y \<in> x \<and> sats(SymExt(G), \<phi>, ([y] @ env) @ [x])"
      apply(rule iffI, force, simp)
      apply(rule_tac P="y \<in> val(G, x')" in mp) 
       apply(subst def_val, force)
      using x'H 
      by auto
    also have "... \<longleftrightarrow> y \<in> x \<and> sats(SymExt(G), \<phi>, [y] @ env)"
      apply(rule iff_conjI2, simp) 
      apply(rule arity_sats_iff)
      using assms SymExt_trans
      by auto
    also have "... \<longleftrightarrow> y \<in> Y" 
      unfolding Y_def 
      by auto
    finally show "y \<in> val(G, X) \<longleftrightarrow> y \<in> Y " by auto
  qed

  then have "Y \<in> SymExt(G)" 
    using \<open>X \<in> HS\<close> SymExt_def
    by auto
  then show ?thesis 
    unfolding Y_def
    by auto
qed

end
end
