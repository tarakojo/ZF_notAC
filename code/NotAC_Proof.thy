theory NotAC_Proof 
  imports 
    NotAC_Binmap 
    NotAC_Inj
begin 

context M_ctm begin 

interpretation M_symmetric_system "Fn" "Fn_leq" "0" "M" "enum" "Fn_perms" "Fn_perms_filter"
  using Fn_M_symmetric_system
  by auto

lemma no_injection : 
  fixes F' p0
  assumes "F' \<in> HS" "p0 \<in> Fn"  
          "ForcesHS(p0, injection_fm(0, 1, 2), [check(nat), binmap', F'])" 
  shows False
proof - 

  define \<phi> where "\<phi> \<equiv> Exists(And(fun_apply_fm(1, 2, 0), Equal(0, 3)))" 

  have sats_\<phi>_iff : "\<And>G a b c. M_generic(G) \<Longrightarrow> {a, b, c} \<subseteq> SymExt(G) \<Longrightarrow> (SymExt(G), [a, b, c] \<Turnstile> \<phi>) \<longleftrightarrow> a`b = c"
  proof - 
    fix G a b c 
    assume assms1: "M_generic(G)" "{a, b, c} \<subseteq> SymExt(G)" 
  
    interpret M_symmetric_system_G_generic  "Fn" "Fn_leq" "0" "M" "enum" "Fn_perms" "Fn_perms_filter" G 
      unfolding M_symmetric_system_G_generic_def
      apply(rule conjI)
      using M_symmetric_system_axioms 
       apply force
      unfolding G_generic_def
      apply(rule conjI)
      using forcing_data_axioms
       apply force
      unfolding G_generic_axioms_def
      using assms1
      by auto

    show "(SymExt(G), [a, b, c] \<Turnstile> \<phi>) \<longleftrightarrow> a`b = c"
      apply(rule_tac Q="\<exists>d \<in> SymExt(G). a`b = d \<and> d = c" in iff_trans)
      unfolding \<phi>_def
       apply(rule iff_trans, rule sats_Exists_iff)
      using assms1
        apply force
       apply(rule bex_iff)
       apply(rule iff_trans, rule sats_And_iff)
      using assms1
        apply force
       apply(rule iff_conjI)
        apply(rule iff_trans, rule sats_fun_apply_fm)
      using assms1
            apply auto[4]
        apply simp
        apply(rule M_basic.apply_abs)
      using M_ZF_trans.mbasic SymExt_M_ZF_trans assms1
           apply auto[6]
      done
  qed

  obtain G where GH: "M_generic(G)" "p0 \<in> G" 
    using assms generic_filter_existence
    by auto

  interpret M_symmetric_system_G_generic  "Fn" "Fn_leq" "0" "M" "enum" "Fn_perms" "Fn_perms_filter" G 
    unfolding M_symmetric_system_G_generic_def
    apply(rule conjI)
    using M_symmetric_system_axioms 
     apply force
    unfolding G_generic_def
    apply(rule conjI)
    using forcing_data_axioms
     apply force
    unfolding G_generic_axioms_def
    using assms GH
    by auto

  have Un_subset : "\<And>A B C. A \<subseteq> C \<Longrightarrow> B \<subseteq> C \<Longrightarrow> A \<union> B \<subseteq> C" by auto

  define F where "F \<equiv> val(G, F')" 

  have p0inFn :"p0 \<in> Fn" using M_genericD assms by auto

  obtain e where eH: "Fix(e) \<subseteq> sym(F')" "e \<subseteq> nat" "finite_M(e)"  
    using assms HS_iff symmetric_def Fn_perms_filter_def 
    by force
  then have e_Finite : "Finite(e)" 
    using finite_M_implies_Finite
    by auto

  have listin : "[check(nat), binmap', F'] \<in> list(HS)" 
    using check_in_HS nat_in_M assms binmap'_HS
    by auto
  then have mapin : "map(val(G), [check(nat), binmap', F']) \<in> list(SymExt(G))" 
    apply simp
    using SymExt_def
    by auto

  have "SymExt(G), map(val(G), [check(nat), binmap', F']) \<Turnstile> injection_fm(0, 1, 2)" 
    apply(rule iffD1, rule HS_truth_lemma)
    using assms GH check_in_HS nat_in_M binmap'_HS
        apply auto[3]
     apply(subst injection_fm_def)
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    using assms GH
    by auto
  then have "injection(##SymExt(G), val(G, check(nat)), val(G, binmap'), F)" 
    using sats_bijection_fm mapin F_def
    by auto
  then have "injection(##SymExt(G), nat, binmap(G), F)" 
    apply(subgoal_tac "val(G, check(nat)) = nat \<and> val(G, binmap') = binmap(G)")
     apply force
    apply(rule conjI)
     apply(rule valcheck)
    using generic_filter_contains_max assms GH zero_in_Fn binmap_eq
    by auto
  then have Finj: "F \<in> inj(nat, binmap(G))"
    apply(rule_tac iffD1)
     apply(rule M_basic.injection_abs)
    using SymExt_M_ZF_trans M_ZF_trans.mbasic
        apply force
    using GH M_subset_SymExt nat_in_M binmap_eq assms SymExt_def binmap'_HS F_def
    by auto

  have "F \<in> bij(nat, range(F))" 
    apply(rule inj_bij_range)
    using Finj 
    by auto
  then have rangeinfinite: "\<not>Finite(range(F))" 
    apply(rule_tac ccontr)
    apply(subgoal_tac "Finite(nat)")
    using nat_not_Finite
     apply simp
    apply(rule iffD2, rule_tac B="range(F)" in eqpoll_imp_Finite_iff)
    using eqpoll_def 
    by auto
  have "\<not>Finite({ n \<in> nat. binmap_row(G, n) \<in> range(F) })" (is "\<not>Finite(?RangeIndexes)")
  proof (rule ccontr)
    assume "\<not> \<not> Finite(?RangeIndexes)" 
    then have H: "Finite({ binmap_row(G, n). n \<in> ?RangeIndexes })" 
      apply(rule_tac Finite_RepFun)
      by auto
    have "{ binmap_row(G, n). n \<in> ?RangeIndexes } = range(F)" 
    proof(rule equality_iffI, rule iffI, force, clarsimp)
      fix n x 
      assume "<n, x> \<in> F" 
      then obtain m where "m \<in> nat" "x = binmap_row(G, m)" using Finj inj_def Pi_def binmap_def by auto
      then show "\<exists>m\<in>nat. binmap_row(G, m) \<in> range(F) \<and> x = binmap_row(G, m)"
        using \<open><n, x> \<in> F\<close>
        by auto
    qed
    then have "Finite(range(F))" 
      using H by auto
    then show False using rangeinfinite by auto
  qed

  then have "?RangeIndexes - e \<noteq> 0" 
    apply(subgoal_tac "\<not>Finite(?RangeIndexes - e)")
     apply(rule ccontr)
    using Finite_0
     apply force
    apply(rule ccontr, simp)
    apply(insert Diff_Finite [of e ?RangeIndexes])
    using e_Finite 
    by auto
  then obtain n where nH: "n \<notin> e" "n \<in> ?RangeIndexes" "n \<in> nat" using e_Finite eH by blast
  then obtain i where iH: "<i, binmap_row(G, n)> \<in> F" "i \<in> nat" using Finj inj_def Pi_def by auto
  then have iH': "F`i = binmap_row(G, n)" 
    apply(rule_tac function_apply_equality)
    using Finj inj_def Pi_def
    by auto

  have binmapin : "binmap(G) \<in> SymExt(G)" 
      apply(subst binmap_eq)
    using assms mapin GH
    by auto

  have rowin : "binmap_row(G, n) \<in> SymExt(G)" 
    unfolding SymExt_def 
    apply(subst binmap_row_eq)
    using nH assms GH
      apply auto[2]
    apply simp
    apply(rule_tac x="binmap_row'(n)" in bexI)
    using binmap_row'_HS nH
    by auto

  then have listin' : "[F, i, binmap_row(G, n)] \<in> list(SymExt(G))" 
    apply auto
    using F_def SymExt_def assms
     apply force
    using iH transM nat_in_M M_subset_SymExt
    by force

  have mapeq: "map(val(G), [F', check(i), binmap_row'(n)]) = [F, i, binmap_row(G, n)]"
    using F_def
    apply auto
     apply(rule valcheck)
    using generic_filter_contains_max assms zero_in_Fn binmap_row_eq nH GH
    by auto

  have "F`i \<in> binmap(G)" 
    apply(rule function_value_in)
    using Finj bij_def inj_def iH
    by auto
  then have appin : "F`i \<in> SymExt(G)" 
    using mapin binmapin SymExt_trans
    by auto

  have "sats(SymExt(G), \<phi>, [F, i, binmap_row(G, n)])"
    apply(rule iffD2 , rule sats_\<phi>_iff)
    using GH listin' iH iH'
    by auto
  then have "\<exists>q \<in> G. ForcesHS(q, \<phi>, [F', check(i), binmap_row'(n)])" 
    apply(rule_tac iffD2)
     apply(rule HS_truth_lemma)
    unfolding \<phi>_def
    using assms GH
        apply auto[2]
    using iH nat_in_M transM check_in_HS binmap_row'_HS nH assms GH
      apply force
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    using mapeq GH
    by auto
  then obtain p where pH: "p \<in> G" "ForcesHS(p, \<phi>, [F', check(i), binmap_row'(n)])" by auto

  have pinFn : "p \<in> Fn" using Fn_def M_genericD pH assms GH by blast 

  have domain_Finite : "Finite(domain(p))" 
    using pinFn Fn_def finite_M_implies_Finite
    by auto

  have "{ fst(x). x \<in> domain(p) } = domain(domain(p))" (is "?A = _")
    apply(rule equality_iffI, rule iffI)
    using assms Fn_def pinFn GH
     apply force
    apply clarsimp
    apply(rename_tac a b c, rule_tac x="<a, b>" in bexI)
    by auto
  have "Finite(?A)" 
    apply(rule Finite_RepFun, rule domain_Finite)
    done
  then have "Finite(domain(domain(p)))" using \<open>?A = domain(domain(p))\<close> by auto
  then have "Finite(e \<union> domain(domain(p)) \<union> {n})" (is "Finite(?B)")
    using Finite_Un e_Finite 
    by auto

  have "?B \<subseteq> nat" 
    using eH assms pinFn Fn_def nH
    by force  

  have ex_remain: "\<And>A. A \<subseteq> nat \<Longrightarrow> Finite(A) \<Longrightarrow> \<exists>a \<in> nat. a \<notin> A" 
    apply(rule ccontr)
    apply(rename_tac A, subgoal_tac "A = nat")
    using nat_not_Finite 
     apply force 
    apply(rule equalityI)
    by auto
  obtain n' where n'H: "n' \<notin> ?B" "n' \<in> nat" 
    apply(insert ex_remain [of ?B])
    using \<open>?B \<subseteq> nat\<close> \<open>Finite(?B)\<close>
    by blast

  define f where "f \<equiv> { <x, x> .. x \<in> nat, x \<noteq> n \<and> x \<noteq> n'} \<union> { <n, n'>, <n', n> }" 

  have fn : "f`n = n'" 
    apply(rule function_apply_equality)
    using f_def function_def
    by auto
  have fn' : "f`n' = n" 
    apply(rule function_apply_equality)
    using f_def function_def
    by auto
  have fx : "\<And>x. x \<in> nat \<Longrightarrow> x \<noteq> n \<Longrightarrow> x \<noteq> n' \<Longrightarrow> f`x = x" 
    apply(rule function_apply_equality)
    using f_def function_def 
    by auto

  have finj : "\<And>a b. a \<in> nat \<Longrightarrow> b \<in> nat \<Longrightarrow> a \<noteq> b \<Longrightarrow> f`a \<noteq> f`b" 
    apply(rename_tac a b, case_tac "a \<in> {n, n'}") 
     apply(rename_tac a b, case_tac "b \<in> {n, n'}")
    using fn fn' 
      apply force
    using fn fn' fx
      apply force 
     apply(rename_tac a b, case_tac "b \<in> {n, n'}")
    using fn fn' fx
      apply force
    using fn fn' fx
    apply force
    done

  define \<psi> where "\<psi> \<equiv> Exists(Exists(And(pair_fm(0, 1, 2), 
                        Or(Exists(And(Member(0, 4), And(Equal(0, 1), And(Equal(0, 2), And(Neg(Equal(0, 5)), Neg(Equal(0, 6))))))), 
                        Or(And(Equal(0, 4), Equal(1, 5)), 
                           And(Equal(0, 5), Equal(1, 4)))))))" 

  have "\<And>v. v \<in> M \<Longrightarrow> sats(M, \<psi>, [v, nat, n, n']) \<longleftrightarrow> v \<in> f" 
    
    apply(rule_tac Q=
      "(\<exists>b \<in> M. \<exists>a \<in> M. (<a, b> = v \<and> 
        ((\<exists>x \<in> M. x \<in> nat \<and> x = a \<and> x = b \<and> x \<noteq> n \<and> x \<noteq> n') \<or> 
         (a = n \<and> b = n') \<or> 
         (a = n' \<and> b = n))))" in iff_trans)
    unfolding \<psi>_def
    apply(subgoal_tac "[nat, n, n'] \<in> list(M)")
    apply(rule iff_trans, rule sats_Exists_iff, simp, rule bex_iff)+
    apply(rule iff_trans, rule sats_And_iff, simp, rule iff_conjI, force)
    apply(rule iff_trans, rule sats_Or_iff, simp, rule iff_disjI)
      apply(rule iff_trans, rule sats_Exists_iff, simp, rule bex_iff)
      apply(rule iff_trans, rule sats_And_iff, simp, rule iff_conjI, simp)+
      apply simp
     apply(rule iff_trans, rule sats_Or_iff, simp, rule iff_disjI)
      apply(rule iff_trans, rule sats_And_iff, simp, rule iff_conjI, simp)+
      apply simp
     apply(rule iff_trans, rule sats_And_iff, simp, rule iff_conjI, simp)+
    using nat_in_M transM nH n'H 
      apply auto[2]
    unfolding f_def
    apply(rule iffI)
     apply force
    using pair_in_M_iff
    by auto
  then have "f \<in> M" 
    apply(rule_tac a="{ x \<in> nat \<times> nat. x \<in> f }" and b=f in ssubst)
    using f_def nH n'H
     apply auto[1]
    apply(rule_tac a="{ x \<in> nat \<times> nat. sats(M, \<psi>, [x] @ [nat, n, n']) }" and b="{ x \<in> nat \<times> nat. x \<in> f }" in ssubst)
     apply(rule iff_eq)
    using nat_in_M cartprod_closed transM
     apply force
    apply(rule separation_notation, rule separation_ax)
    unfolding \<psi>_def
       apply force
    using nat_in_M transM nH n'H 
      apply auto[1]
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    using nat_in_M cartprod_closed transM
     apply force
    done
  then have fin: "f \<in> nat_perms" 
    unfolding nat_perms_def bij_def inj_def surj_def
    apply simp
    apply(rule conjI)
     apply(rule Pi_memberI)
    using f_def relation_def function_def
        apply auto[2]
      apply(rule equality_iffI, rule iffI)
    using f_def nH n'H
       apply auto[3]
    apply(rule conjI)
     apply clarsimp
    using finj
     apply force
    apply(rule ballI)
    apply(rename_tac x, case_tac "x \<in> {n, n'}")
    using fx fn fn' nH n'H
    by auto
 
  define \<pi> where "\<pi> \<equiv> Fn_perm'(f)" 

  have "\<And>a b c. <a, b> \<in> p \<Longrightarrow> <a, c> \<in> Fn_perm(f, p) \<Longrightarrow> b = c" 
  proof - 
    fix a b c 
    assume assms1 : "<a, b> \<in> p" "<a, c> \<in> Fn_perm(f, p)" 

    have "\<exists>n\<in>nat. \<exists>m\<in>nat. \<exists>l\<in>2. \<langle>\<langle>n, m\<rangle>, l\<rangle> \<in> p \<and> <a, c> = \<langle>\<langle>f ` n, m\<rangle>, l\<rangle>"
      apply(rule Fn_permE)
      using assms1 pinFn fin 
      by auto
    then obtain x y z where xyzH: "a = <x, y>" "x = f`z" "<<z, y>, c> \<in> p" "x \<in> nat" "y \<in> nat" "z \<in> nat" 
      using assms1 pinFn Fn_def 
      by auto

    show "b = c" 
    proof(cases "z = n")
      case True 
      then have "x = n'" using xyzH fn by auto
      then have "n' \<in> domain(domain(p))" using xyzH assms1 by auto     
      then show ?thesis using n'H by auto
    next
      case False
      then show ?thesis
      proof(cases "z = n'")
        case True
        then have "n' \<in> domain(domain(p))" using xyzH assms1 by auto     
        then show ?thesis using n'H by auto
      next
        case False
        then have "z \<noteq> n \<and> z \<noteq> n'" using \<open>z \<noteq> n\<close> by auto
        then have "f`z = z" using fx xyzH by auto
        then have "x = z" using xyzH by auto
        then have "<a, b> \<in> p \<and> <a, c> \<in> p" using xyzH assms1 by auto
        then show ?thesis using assms1 pinFn Fn_def function_def by auto
      qed
    qed
  qed
  then have compatH : "compat(p, Fn_perm(f, p))" 
    unfolding compat_def compat_in_def 
    apply(subgoal_tac "p \<union> Fn_perm(f, p) \<in> Fn")
     apply(rule_tac x="p \<union> Fn_perm(f, p)" in bexI)
    unfolding Fn_leq_def
    using pinFn Fn_perm_in_Fn fin 
      apply force
     apply force
    unfolding Fn_def 
    apply simp
    apply(rule conjI)
     apply(rule subsetI, clarsimp)
     apply auto[1]
    using pinFn Fn_def
      apply force
    apply(insert Fn_perm_subset [of f p])
    using pinFn Fn_def fin
     apply force
    apply(rule conjI)
    using Un_closed pinFn Fn_def Fn_perm_in_M fin 
     apply force 
    apply(rule conjI)
     apply(simp add:function_def, clarsimp)
     apply auto[1]
    using pinFn Fn_def function_def
      apply force
     apply(insert function_Fn_perm [of f p])
    using function_def fin pinFn
     apply force 
    apply(rule conjI)
     apply auto[1]
    using Fn_def pinFn fin
      apply (force, blast)
    apply(rule conjI)
     apply(rule finite_M_union)
    using Fn_in_M transM domain_closed Fn_perm_in_M pinFn fin Fn_def Fn_perm_in_Fn
        apply auto[4]
    apply(rule Un_subset)
    using pinFn Fn_def fin 
     apply auto[1]
    using pinFn fin Fn_perm_subset 
    apply blast
    done

  have piinfix : "\<pi> \<in> Fix(e)" 
    unfolding Fix_def
    apply clarsimp
    apply(rule_tac x=f in bexI, rule conjI)
    using \<pi>_def 
      apply simp
     apply clarsimp
     apply(rule function_apply_equality)
    apply(rename_tac x, case_tac "x \<in> {n, n'}")
    using f_def nH n'H eH 
       apply auto[2]
    using fin nat_perms_def bij_def inj_def Pi_def
    by auto

  have fnneq : "f`n \<noteq> n"
    apply(rule ccontr, simp)
    using fn n'H
    by auto

  have pi_preserves_F' : "Pn_auto(\<pi>)`F' = F'" 
    using piinfix eH sym_def 
    by auto

  have mapeq : "map(\<lambda>x. Pn_auto(\<pi>)`x, [F', check(i), binmap_row'(n)]) = [F', check(i), binmap_row'(f`n)]" 
    apply auto
      apply(rule pi_preserves_F')
     apply(rule check_fixpoint)
    using \<pi>_def fin Fn_perm'_is_P_auto iH nat_in_M transM
      apply auto[2]
    unfolding \<pi>_def
    apply(rule binmap_row'_pauto)
    using nH fin
    by auto

  have "ForcesHS(\<pi>`p, \<phi>, map(\<lambda>x. Pn_auto(\<pi>)`x, [F', check(i), binmap_row'(n)]))" 
    apply(rule iffD1, rule symmetry_lemma)
    using \<phi>_def \<pi>_def Fn_perms_def fin Fn_perm'_is_P_auto 
          apply auto[3]
       apply auto[1]
    using listin check_in_HS iH nat_in_M transM 
         apply auto[2]
       apply(rule binmap_row'_HS)
    using nH 
       apply simp
      apply(simp add:\<phi>_def)
      apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    using pinFn pH 
    by auto
  then have piForces: "ForcesHS(\<pi>`p, \<phi>, [F', check(i), binmap_row'(f`n)])"  
    using mapeq 
    by auto

  obtain q where qH : "<q, p> \<in> Fn_leq" "<q, \<pi>`p> \<in> Fn_leq" "q \<in> Fn" 
    using compatH compat_def \<pi>_def Fn_perm'_eq fin pinFn 
    by force

  have listin'' : "[F', check(i), binmap_row'(n)] \<in> list(HS)" 
    apply auto[1]
    using assms HS_iff P_name_in_M 
      apply auto[1]
     apply(rule check_in_HS)
    using iH nat_in_M transM 
     apply force
    apply(rule binmap_row'_HS)
    using nH
    by auto

  have listin''' : "[F', check(i), binmap_row'(f`n)] \<in> list(HS)" 
    apply auto[1]
    using assms HS_iff P_name_in_M 
      apply auto[1]
     apply(rule check_in_HS)
    using iH nat_in_M transM 
     apply force
    apply(rule binmap_row'_HS)
    apply(rule function_value_in)
    using nH fin nat_perms_def bij_def inj_def
    by auto

  have "ForcesHS(q, \<phi>, [F', check(i), binmap_row'(n)])"
    apply(rule_tac p="p" in HS_strengthening_lemma)
    using pinFn qH \<phi>_def 
          apply auto[4]
      apply(rule_tac A="list(HS)" in subsetD, rule list_mono)
    using HS_iff P_name_in_M listin''
       apply (force, force)
    using \<phi>_def
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    using pH
    by auto
  then have ForcesH1: "(\<forall>H. M_generic(H) \<and> q\<in>H  \<longrightarrow>  SymExt(H), map(val(H),[F', check(i), binmap_row'(n)]) \<Turnstile> \<phi>)"
    apply(rule_tac iffD1)
     apply(rule definition_of_forcing_HS)
    using pinFn \<phi>_def listin'' qH
        apply auto[3]
     apply(simp add:\<phi>_def)
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    by auto

  have "ForcesHS(q, \<phi>, [F', check(i), binmap_row'(f`n)])"
    apply(rule_tac p="\<pi>`p" in HS_strengthening_lemma)
          apply(rule P_auto_value)
    using \<pi>_def Fn_perm'_is_P_auto fin 
           apply force
    using pinFn qH \<phi>_def 
          apply auto[4]
      apply auto[1]
    using assms HS_iff P_name_in_M check_in_M iH nat_in_M transM
        apply auto[2]
      apply(rule binmap_row'_in_M)
      apply(rule function_value_in)
    using fin nat_perms_def bij_def inj_def nH
       apply (force, force)
    using \<phi>_def
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    using piForces
    by auto
  then have ForcesH2: "(\<forall>H. M_generic(H) \<and> q\<in>H  \<longrightarrow>  SymExt(H), map(val(H),[F', check(i), binmap_row'(f`n)]) \<Turnstile> \<phi>)"
    apply(rule_tac iffD1)
     apply(rule definition_of_forcing_HS)
    using Fn_perm'_is_P_auto \<pi>_def fin qH \<phi>_def listin'''
         apply auto[4]
     apply(simp add:\<phi>_def)
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    by auto

  obtain H where HH: "M_generic(H)" "q \<in> H" 
    using generic_filter_existence qH 
    by auto
  (* redefine *)
  define F where "F \<equiv> val(H, F')" 

  have "SymExt(H), map(val(H), [F', check(i), binmap_row'(n)]) \<Turnstile> \<phi>" 
    using ForcesH1 HH
    by auto
  then have "val(H, F')`val(H, check(i)) = val(H, binmap_row'(n))" (is ?A)
    apply(rule_tac iffD1, rule_tac sats_\<phi>_iff)
    using HH 
      apply simp
     apply auto[1]
    using SymExt_def listin''
    by auto
  then have Fieq1: "F`i = binmap_row(H, n)" 
    apply(rule_tac P="?A" in iffD1)
     apply(subst F_def, subst valcheck)
    using HH generic_filter_contains_max zero_in_Fn
       apply auto[2]
     apply(subst binmap_row_eq)
    using nH HH 
    by auto

  have "SymExt(H), map(val(H), [F', check(i), binmap_row'(f`n)]) \<Turnstile> \<phi>"
    using ForcesH2 HH 
    by auto
  then have "val(H, F')`val(H, check(i)) = val(H, binmap_row'(f`n))" (is ?A)
    apply(rule_tac iffD1, rule_tac sats_\<phi>_iff)
    using HH 
      apply simp
     apply auto[1]
    using SymExt_def listin'''
    by auto
  then have Fieq2: "F`i = binmap_row(H, f`n)" 
    apply(rule_tac P="?A" in iffD1)
     apply(subst F_def, subst valcheck)
    using HH generic_filter_contains_max zero_in_Fn
       apply auto[2]
     apply(subst binmap_row_eq)
       apply(rule function_value_in)
    using fin nat_perms_def nH HH bij_def inj_def
    by auto
    
  have roweq : "binmap_row(H, n) = binmap_row(H, f`n)" using Fieq1 Fieq2 by auto

  have rowneq: "binmap_row(H, n) \<noteq> binmap_row(H, f`n)" 
    apply(rule binmap_row_distinct)
    using HH nH 
       apply auto[2]
     apply(rule function_value_in)
    using HH nH fin nat_perms_def bij_def inj_def 
      apply auto[2]
    using fnneq
    by auto

  show False
    using roweq rowneq
    by auto
qed

lemma no_wellorder : 
  fixes r G
  assumes "M_generic(G)" "wellordered(##SymExt(G), binmap(G), r)" "r \<in> SymExt(G)" 
  shows False
proof - 

  interpret M_symmetric_system_G_generic  "Fn" "Fn_leq" "0" "M" "enum" "Fn_perms" "Fn_perms_filter" G 
    unfolding M_symmetric_system_G_generic_def
    apply(rule conjI)
    using M_symmetric_system_axioms 
     apply force
    unfolding G_generic_def
    apply(rule conjI)
    using forcing_data_axioms
     apply force
    unfolding G_generic_axioms_def
    using assms
    by auto


  define f where "f \<equiv> { <n, binmap_row(G, n)>. n \<in> nat }" 
  have fpi: "f \<in> nat \<rightarrow> binmap(G)" 
    apply(rule Pi_memberI)
    using f_def relation_def function_def binmap_def
    by auto
  have "\<And>m n. m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> m \<noteq> n \<Longrightarrow> f`m \<noteq> f`n" 
  proof- 
    fix m n 
    assume assms1: "m \<in> nat" "n \<in> nat" "m \<noteq> n" 
    have fm: "f`m = binmap_row(G, m)" 
      apply(rule function_apply_equality)
      using f_def assms1 fpi Pi_def
      by auto

    have fn: "f`n = binmap_row(G, n)" 
      apply(rule function_apply_equality)
      using f_def assms1 fpi Pi_def
      by auto

    have "binmap_row(G, m) \<noteq> binmap_row(G, n)" 
      apply(rule binmap_row_distinct)
      using assms assms1
      by auto
    then show "f`m \<noteq> f`n" 
      using fm fn 
      by auto
  qed
  then have "f \<in> inj(nat, binmap(G))" 
    unfolding inj_def 
    using fpi
    by auto
  then have natle: "nat \<lesssim> binmap(G)" using lepoll_def by auto
  
  have "\<exists>g\<in>SymExt(G). g \<in> inj(nat, binmap(G))"
    apply(rule M_ZF_trans.wellorder_induces_injection)
    using SymExt_M_ZF_trans natle assms 
        apply auto[4]
    apply(subst binmap_eq, simp add:assms)
    unfolding SymExt_def
    using binmap'_HS
    by auto
  then obtain g where gH : "g \<in> SymExt(G)" "g \<in> inj(nat, binmap(G))" by auto

  then obtain g' where g'H: "val(G, g') = g" "g' \<in> HS" using SymExt_def by auto
  have checknatH: "val(G, check(nat)) = nat" 
    apply(rule valcheck)
    using generic_filter_contains_max assms zero_in_Fn
    by auto
  have binmap'H : "val(G, binmap') = binmap(G)" 
    using assms binmap_eq
    by auto

  have mapeq : "map(val(G), [check(nat), binmap', g']) = [nat, binmap(G), g]" 
    using g'H checknatH binmap'H
    by auto

  have "SymExt(G), [nat, binmap(G), g] \<Turnstile> injection_fm(0,1,2)" 
    apply(rule iffD2, rule sats_injection_fm)
        apply auto[4]
    using nat_in_M M_subset_SymExt binmap'_HS SymExt_def gH binmap_eq assms
       apply auto[3]
    apply simp
    apply(rule iffD2, rule M_basic.injection_abs)
    using nat_in_M M_subset_SymExt gH binmap'_HS SymExt_def gH binmap_eq assms M_ZF_trans.mbasic SymExt_M_ZF_trans
    by auto
  then have "\<exists>p \<in> G. (ForcesHS(p, injection_fm(0,1,2), [check(nat), binmap', g']))" 
    apply(rule_tac iffD2)
     apply(rule HS_truth_lemma)
    using assms check_in_HS nat_in_M binmap'_HS g'H
        apply auto[3]
     apply(simp add:injection_fm_def)
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    using mapeq
    by auto
  then obtain p where "p \<in> G" "ForcesHS(p, injection_fm(0,1,2), [check(nat), binmap', g'])" by auto
  then show False 
    apply(rule_tac F'=g' in no_injection)
    using g'H M_genericD assms 
    by auto
qed




  


end
end