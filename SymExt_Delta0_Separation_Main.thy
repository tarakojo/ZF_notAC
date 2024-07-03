theory SymExt_Delta0_Separation_Main
  imports 
    SymExt_Delta0_Separation_Base
    SymExt_Delta0_Separation_Forces
    Symmetry_Lemma
    Delta0
begin 

context M_symmetric_system_G_generic
begin

definition MGsep where "MGsep(x, \<phi>, env) \<equiv> { u \<in> x. sats(M[G], \<phi>, [u] @ env) }" 
definition MGsep' where "MGsep'(x', \<phi>, env') \<equiv> { <u', p> \<in> delta0sep_Base(x') \<times> P. p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u'] @ env' @ [x'] }" 

lemma MGsep'_in_M : "x' \<in> M \<Longrightarrow> \<phi> \<in> formula \<Longrightarrow> arity(\<phi>) = 1 #+ length(env') \<Longrightarrow> env' \<in> list(M) \<Longrightarrow> MGsep'(x', \<phi>, env') \<in> M" 
  unfolding MGsep'_def 
  apply(rule delta0sep_forces_pair_in_M) 
      apply(rule delta0sep_Base_in_M, auto)
  done

lemma MGsep'_P_name : 
  fixes x' \<phi> env'
  assumes "x' \<in> M" "\<phi> \<in> formula" "arity(\<phi>) = 1 #+ length(env')" "env' \<in> list(M)"
  shows "MGsep'(x', \<phi>, env') \<in> P_names" 
proof - 
  have "MGsep'(x', \<phi>, env') \<subseteq> P_names \<times> P" 
  proof (rule subsetI) 
    fix v assume vin : "v \<in> MGsep'(x', \<phi>, env')" 
    then obtain u' p where u'pH : "u' \<in> delta0sep_Base(x')" "p \<in> P" "v = <u', p>" 
      unfolding MGsep'_def 
      by auto 
    then have "u' \<in> P_names" 
      unfolding delta0sep_Base_def 
      using HS_iff 
      by auto
    then show "v \<in> P_names \<times> P" 
      using vin u'pH 
      by auto 
  qed
  then show ?thesis 
    using P_name_iff MGsep'_in_M assms
    by auto
qed

lemma MGsep_eq : 
  fixes x x' env env' \<phi> 
  assumes "x \<in> SymExt(G)" "x' \<in> HS" "env \<in> list(SymExt(G))" "env' \<in> list(HS)" "val(G, x') = x" "map(val(G), env') = env" "\<phi> \<in> formula" "arity(\<phi>) = 1 #+ length(env)" 
  shows "val(G, MGsep'(x', \<phi>, env')) = MGsep(x, \<phi>, env)" 
proof (rule equality_iffI, rule iffI) 

  have env'inMlist : "env' \<in> list(M)" 
    apply(rule_tac A="list(HS)" in subsetD)
     apply(rule list_mono)
    using assms HS_iff P_name_in_M
    by auto

  have envinMGlist : "env \<in> list(M[G])" 
    by(rule subsetD, rule list_mono, rule SymExt_subset_GenExt, simp add:assms)

  have sats_iff : "\<And>u x. u \<in> M[G] \<Longrightarrow> x \<in> M[G]  \<Longrightarrow>  sats(M[G], \<phi>, [u] @ env) \<longleftrightarrow> sats(M[G], \<phi>, [u] @ env @ [x])"  
    apply(simp, rule iff_flip) 
    apply(rename_tac u x; rule_tac x=u and extra="[x]" in arity_sats1_iff)
    using assms envinMGlist
    by auto

  have leneq : "length(env) = length(env')" 
    using assms length_map 
    by auto

  fix u assume uH : "u \<in> val(G, MGsep'(x', \<phi>, env'))" 
  define y' where "y' \<equiv>  MGsep'(x', \<phi>, env')"

  have "val(G, y') = { val(G, u').. u' \<in> domain(y'), \<exists>p \<in> P. <u', p> \<in> y' \<and> p \<in> G }" 
    by(rule def_val)
  then obtain u' p where u'pH : "u' \<in> domain(y')" "u = val(G, u')" "<u', p> \<in> y'" "p \<in> G" 
    using SepReplace_iff uH y'_def
    by auto 
    
  have u'inM : "u' \<in> M" 
    apply(rule to_rin, rule_tac x="domain(y')" in transM, simp add:u'pH, rule domain_closed)
    unfolding y'_def 
    apply(simp, rule MGsep'_in_M)
    using assms leneq HS_iff P_name_in_M env'inMlist
    by auto

  define L where "L \<equiv> [u'] @ env' @ [x']"  

  have Ltype : "L \<in> list(M)" 
    unfolding L_def 
    using u'inM
    apply simp
    apply(rule app_type, simp add:env'inMlist)
    using assms HS_iff P_name_in_M
    by auto

  have Lmaptype : "map(val(G), L) \<in> list(M[G])" 
    by(rule map_type, rule Ltype, simp add:GenExt_def, force)

  have forceH: "p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) L" 
    using u'pH
    unfolding y'_def L_def MGsep'_def
    by auto

  have "(\<forall>G. M_generic(G) \<and> p \<in> G \<longrightarrow> sats(M[G], And(Member(0, arity(\<phi>)), \<phi>), map(val(G), L)))" 
    apply(rule_tac iffD1)
     apply(rule definition_of_forcing) 
        apply(rule_tac G=G in M_genericD, simp add:generic, simp add:u'pH)
    using assms L_def Ltype
       apply (simp, simp)
     apply(subst and_member_phi_arity) 
    using le_refl assms HS_iff P_name_in_M leneq forceH L_def
    by auto

  then have satsH: "sats(M[G], And(Member(0, arity(\<phi>)), \<phi>), map(val(G), L))" using assms u'pH generic by auto

  have "nth(arity(\<phi>), map(val(G), L)) = val(G, nth(arity(\<phi>), [u'] @ env' @ [x']))"
    unfolding L_def
    apply(rule_tac A=M in nth_map) 
    using Ltype  L_def assms leneq le_refl 
    by auto
  
  also have "... = val(G, nth(length(env'), env' @ [x']))" using assms leneq by auto
  also have "... = val(G, nth(length(env') #- length(env'), [x']))" 
    apply(subst nth_append) 
    using assms
      apply(simp, simp)
    apply(subst if_not_P) 
    using lt_irrefl 
    by auto
  also have "... = x" using assms by auto
  finally have uinx : "u \<in> x" 
    using satsH u'pH Lmaptype
    unfolding L_def 
    by auto 

  have "map(val(G), ([u'] @ env') @ [x']) = map(val(G), ([u'] @ env')) @ map(val(G), [x'])"
    apply(rule map_app_distrib)
    using u'inM assms env'inMlist
    by auto
  also have "... = map(val(G), [u']) @ map(val(G), env') @ map(val(G), [x'])" by auto
  finally have eq: "map(val(G), ([u'] @ env') @ [x']) = [u] @ env @ [x]" 
    using u'pH assms  
    by auto

  have "sats(M[G], \<phi>, map(val(G), ([u'] @ env') @ [x']))"
    using satsH Lmaptype app_assoc 
    unfolding L_def 
    by auto
  then have "sats(M[G], \<phi>, [u] @ env @ [x])"
    using eq 
    by auto
  then have "sats(M[G], \<phi>, [u] @ env)" 
    apply(rule_tac iffD2, rule_tac sats_iff)
      apply(simp add:u'pH, rule GenExtI, simp add:u'inM)
    using assms SymExt_subset_GenExt 
    by auto
    
  then show "u \<in> MGsep(x, \<phi>, env)" 
    unfolding MGsep_def 
    using uinx 
    by auto
next
  have env'inMlist : "env' \<in> list(M)" 
    apply(rule_tac A="list(HS)" in subsetD)
     apply(rule list_mono)
    using assms HS_iff P_name_in_M
    by auto

  have envinMGlist : "env \<in> list(M[G])" 
    by(rule subsetD, rule list_mono, rule SymExt_subset_GenExt, simp add:assms)

  have sats_iff : "\<And>u x. u \<in> M[G] \<Longrightarrow> x \<in> M[G]  \<Longrightarrow>  sats(M[G], \<phi>, [u] @ env) \<longleftrightarrow> sats(M[G], \<phi>, [u] @ env @ [x])"  
    apply(simp, rule iff_flip) 
    apply(rename_tac u x; rule_tac x=u and extra="[x]" in arity_sats1_iff)
    using assms envinMGlist
    by auto

  have leneq : "length(env) = length(env')" 
    using assms length_map 
    by auto

  fix u assume uH : "u \<in>  MGsep(x, \<phi>, env)" 
  
  then have uinx : "u \<in> x" unfolding MGsep_def by auto
  then have "u \<in> val(G, x')" using assms by auto
  then have "val(G, x') = { val(G, u').. u' \<in> domain(x'), \<exists>p \<in> P. <u', p> \<in> x' \<and> p \<in> G }" by (rule_tac def_val) 
  then have "\<exists>u' \<in> domain(x'). u = val(G, u') \<and> ( \<exists>p \<in> P. <u', p> \<in> x' \<and> p \<in> G)" using \<open>u \<in> val(G, x')\<close> by auto 
  then obtain u' p where u'pH:  "u' \<in> domain(x')" "u = val(G, u')" "<u', p> \<in> x'" "p \<in> G" by auto

  have u'inM : "u' \<in> M" 
    apply(rule to_rin, rule_tac x="domain(x')" in transM, simp add:u'pH, rule domain_closed)
    using assms HS_iff P_name_in_M 
    by auto
  then have uinMG : "u \<in> M[G]" using GenExtI assms u'pH by auto

  then have argtype : "[u] @ env @ [x] \<in> list(M[G])" 
    using assms 
    apply simp 
    apply(rule app_type, rule subsetD, rule list_mono, rule SymExt_subset_GenExt, simp add:assms)
    using SymExt_subset_GenExt 
    by auto

  have ntheq : "nth(length(env), env @ [x]) = x" 
    apply(subst nth_append)
    using assms 
      apply (simp, simp)
    apply(subst if_not_P)
    using lt_irrefl 
    by auto

  have "map(val(G), [u'] @ env' @ [x']) = map(val(G), ([u'] @ env') @ [x'])"
    apply(subst app_assoc) 
    using u'inM
    by auto
  also have "... = map(val(G), ([u'] @ env')) @ map(val(G), [x'])"
    apply(rule map_app_distrib)
    using u'inM assms env'inMlist
    by auto
  also have "... = map(val(G), [u']) @ map(val(G), env') @ map(val(G), [x'])" by auto
  finally have mapeq: "map(val(G), [u'] @ env' @ [x']) = [u] @ env @ [x]" 
    using u'pH assms
    by auto

  have "sats(M[G], \<phi>, [u] @ env)" 
    using uH 
    unfolding MGsep_def
    by auto
  then have "sats(M[G], \<phi>, [u] @ env @ [x])" 
    apply(rule_tac iffD1, rule_tac sats_iff)
    using Transset_MG assms uinx SymExt_subset_GenExt
    unfolding Transset_def
    by auto
  then have "sats(M[G], And(Member(0, arity(\<phi>)), \<phi>), map(val(G), [u'] @ env' @ [x']))" 
    using argtype assms ntheq uinx mapeq
    by auto
  then have "\<exists>p \<in> G. p \<tturnstile> (And(Member(0, arity(\<phi>)), \<phi>)) ([u'] @ env' @ [x'])" 
    using assms length_app assms HS_iff P_name_in_M leneq and_member_phi_arity app_type u'inM truth_lemma env'inMlist generic
    by auto 
  then obtain q where pH : "q \<in> G" " q \<tturnstile> (And(Member(0, arity(\<phi>)), \<phi>)) ([u'] @ env' @ [x'])" by auto 

  have u'inB : "u' \<in> delta0sep_Base(x')"
    apply(rule domain_in_delta0sep_Base) 
    using assms HS_iff P_name_iff u'pH 
    apply(force, auto)
    done

  then have "<u', q> \<in> MGsep'(x', \<phi>, env')" 
    unfolding MGsep'_def  
    using assms M_genericD pH generic
    by auto

  then show "u \<in> val(G, MGsep'(x', \<phi>, env'))" 
    apply(rule_tac elem_of_valI)
    apply(rule_tac x=u' in exI, rule_tac x=q in bexI)
    using pH assms M_genericD u'pH generic
    by auto
qed


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

lemma symmetric_MGsep'_helper : 
  fixes x' env' \<phi> \<pi>
  assumes 
    "x' \<in> HS" 
    "env' \<in> list(HS)" 
    "\<phi> \<in> formula" 
    "arity(\<phi>) = 1 #+ length(env')"
    "\<pi> \<in> sym(x')"
    "env' = Nil \<or> \<pi> \<in> INTsym(env')" 
  shows "MGsep'(x', \<phi>, env') = { <Pn_auto(\<pi>)`u', \<pi>`p>.. <u', p> \<in> delta0sep_Base(x') \<times> P, p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u'] @ env' @ [x'] }" 
proof -
  have pi_in_\<G> : "\<pi> \<in> \<G>" using sym_def assms by auto
  then have pi_pauto : "\<pi> \<in> P_auto" using assms \<G>_P_auto_group P_auto_subgroups_def is_P_auto_group_def P_auto_def by auto 
  then have pnautopi_surj : "Pn_auto(\<pi>) \<in> surj(P_names, P_names)" using Pn_auto_bij bij_is_surj P_auto_def by auto

  have mapeq : "map(\<lambda>x. Pn_auto(\<pi>)`x, env' @ [x']) = env' @ [x']" 
    apply(subst map_app_distrib)
    using assms 
     apply simp
    apply(cases "env' = Nil") 
     apply simp 
    using INT_set_of_list_of_\<F>_lemma assms sym_def
    by auto

  have env'inPnamelist : "env' \<in> list(P_names)" 
    apply(rule_tac A="list(HS)" in subsetD, rule list_mono)
    using HS_iff assms
    by auto

  show ?thesis 
  proof (rule equality_iffI, rule iffI)
  
    fix v assume viny' : "v \<in> MGsep'(x', \<phi>, env')" 
    then obtain u' p where u'pH : "v = <u', p>" "u' \<in> delta0sep_Base(x')" "p \<in> P" "p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u'] @ env' @ [x']"
      unfolding MGsep'_def 
      by auto
  
    have u'inHS : "u' \<in> HS" using u'pH unfolding delta0sep_Base_def by auto
    then have u'Pname :  "u' \<in> P_names" using HS_iff by auto
  
    then obtain u'' where u''H : "u'' \<in> P_names"  "u' = Pn_auto(\<pi>)`u''" 
      using pnautopi_surj surj_def 
      by auto 
  
    then have u''inHS : "u'' \<in> HS"
      using HS_Pn_auto pi_in_\<G> u'inHS HS_iff by blast
  
    have u''inBase : "u'' \<in> delta0sep_Base(x')" 
      using delta0sep_Base_Pn_auto assms HS_iff pi_in_\<G> u''H u'pH 
      by auto
  
    have "\<pi> \<in> surj(P, P)" 
      apply(rule bij_is_surj)
      using pi_pauto P_auto_def is_P_auto_def
      by auto
    then obtain q where qH: "q \<in> P" "\<pi>`q = p" using u'pH surj_def by auto
  
    have mapeq': "map(\<lambda>x. Pn_auto(\<pi>)`x, [u''] @ env' @ [x']) = [u'] @ env' @ [x']" 
      using u''H mapeq 
      by auto
  
    have "\<pi>`q \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) map(\<lambda>x. Pn_auto(\<pi>)`x, [u''] @ env' @ [x'])"
      using mapeq' qH u'pH 
      by auto
    then have "q \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u''] @ env' @ [x']" 
      apply(rule_tac iffD2, rule_tac symmetry_lemma)
           apply (simp add:u''H, rule app_type)
            apply(rule env'inPnamelist)
      using assms HS_iff
             apply (force, simp)
         apply(subst and_member_phi_arity)
      using assms qH pi_pauto P_auto_def 
      by auto
  
    then have "<u', p> \<in> { <Pn_auto(\<pi>)`u', \<pi>`p>.. <u', p> \<in> delta0sep_Base(x') \<times> P, p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u'] @ env' @ [x'] }" 
      apply(simp, rule_tac x="u''" in bexI)
       apply(rule conjI, simp add:u''H) 
       apply(rule_tac x=q in bexI)
      using qH u''inBase by auto
      
    then show "v \<in> { <Pn_auto(\<pi>)`u', \<pi>`p>.. <u', p> \<in> delta0sep_Base(x') \<times> P, p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u'] @ env' @ [x'] }" 
      using u'pH by auto
  next
    
    fix v assume "v \<in> { <Pn_auto(\<pi>)`u', \<pi>`p>.. <u', p> \<in> delta0sep_Base(x') \<times> P, p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u'] @ env' @ [x'] }" 
    then obtain u'' p where u''pH :
      "v = <Pn_auto(\<pi>)`u'', \<pi>`p>" 
      "u'' \<in> delta0sep_Base(x')" 
      "p \<in> P" 
      "p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u''] @ env' @ [x']" 
      by auto

    have u''HS : "u'' \<in> HS" 
      using u''pH delta0sep_Base_def by auto

    define u' where "u' \<equiv> Pn_auto(\<pi>)`u''" 

    have u'inBase: "u' \<in> delta0sep_Base(x')" 
      unfolding u'_def
      using delta0sep_Base_Pn_auto pi_in_\<G> assms HS_iff u''HS u''pH 
      by auto

    have pipinP: "\<pi>`p \<in> P" 
      apply(rule P_auto_value)
      using pi_pauto P_auto_def u''pH 
      by auto

    have forcesH : "\<pi>`p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) map(\<lambda>x. Pn_auto(\<pi>)`x, [u''] @ env' @ [x'])"
      apply(rule iffD1, rule symmetry_lemma, simp)
           apply(rule conjI)
      using u''HS HS_iff
            apply force
           apply(rule app_type, rule env'inPnamelist, simp)
      using assms HS_iff
           apply (force, simp)
         apply(subst and_member_phi_arity)
      using assms u''pH pi_pauto P_auto_def
      by auto

    have "map(\<lambda>x. Pn_auto(\<pi>)`x, [u''] @ env' @ [x']) = [u'] @ env' @ [x']" 
      unfolding u'_def
      apply(subst map_app_distrib, simp)
      apply(subst mapeq, simp)
      done
    then have "\<pi>`p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u'] @ env' @ [x']" 
      using forcesH 
      by auto

    then show "v \<in> MGsep'(x', \<phi>, env')" 
      unfolding MGsep'_def 
      using u''pH u'inBase pipinP u'_def 
      by auto
  qed
qed

lemma symmetric_MGsep' : 
  fixes x' env' \<phi>
  assumes 
    "x' \<in> HS" 
    "env' \<in> list(HS)" 
    "\<phi> \<in> formula" 
    "arity(\<phi>) = 1 #+ length(env')"
  shows "symmetric(MGsep'(x', \<phi>, env'))" 
proof -

  have env'inMlist : "env' \<in> list(M)" 
    apply(rule_tac A="list(HS)" in subsetD, rule list_mono)
    using HS_iff P_name_in_M assms
    by auto

  define S where "S \<equiv> if env' = [] then sym(x') else sym(x') \<inter> INTsym(env')" 
  have Sin : "S \<in> \<F>" 
    unfolding S_def
    apply(cases "env' = []")
    using assms HS_iff symmetric_def INT_set_of_list_of_\<F>_lemma \<F>_closed_under_intersection 
    by auto

  then have Ssubset : "S \<subseteq> \<G>" 
    using \<F>_subset P_auto_subgroups_def 
    by auto

  have "\<And>\<pi>. \<pi> \<in> S \<Longrightarrow> Pn_auto(\<pi>)`MGsep'(x', \<phi>, env') = MGsep'(x', \<phi>, env')" 
  proof - 
    fix \<pi> assume assm : "\<pi> \<in> S" 

    have "Pn_auto(\<pi>)`MGsep'(x', \<phi>, env') = { <Pn_auto(\<pi>)`u', \<pi>`p>. <u', p> \<in> MGsep'(x', \<phi>, env') }" 
      apply(rule Pn_auto, rule MGsep'_P_name)
      using assms HS_iff env'inMlist P_name_in_M
      by auto
    also have "... = { <Pn_auto(\<pi>)`u', \<pi>`p>.. <u', p> \<in> delta0sep_Base(x') \<times> P, p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u'] @ env' @ [x'] }" 
      unfolding MGsep'_def 
      apply(rule equality_iffI)
      by auto
    also have "... = MGsep'(x', \<phi>, env')" 
      apply(rule eq_flip, rule symmetric_MGsep'_helper)
      using assms 
           apply(simp, simp, simp, simp)
      using assm 
      unfolding S_def 
       apply(cases "env' = []", simp, simp)
      using assm 
      unfolding S_def 
      apply(cases "env' = []", simp, simp)
      done
    finally show "Pn_auto(\<pi>)`MGsep'(x', \<phi>, env') = MGsep'(x', \<phi>, env')" by auto 
  qed

  then have Ssubsetsym : "S \<subseteq> sym(MGsep'(x', \<phi>, env'))" 
    unfolding sym_def 
    using Ssubset 
    by auto 

  have "sym(MGsep'(x', \<phi>, env')) \<in> P_auto_subgroups(\<G>)" 
    apply(rule sym_P_auto_subgroup, rule MGsep'_P_name)
    using assms HS_iff P_name_in_M env'inMlist
    by auto

  then show "symmetric(MGsep'(x', \<phi>, env'))" 
    unfolding symmetric_def 
    using \<F>_closed_under_supergroup Ssubsetsym Sin 
    by auto
qed   

lemma MGsep'_in_HS : 
  fixes x' env' \<phi>
  assumes 
    "x' \<in> HS" 
    "env' \<in> list(HS)" 
    "\<phi> \<in> formula" 
    "arity(\<phi>) = 1 #+ length(env')"
  shows "MGsep'(x', \<phi>, env') \<in> HS" 

  apply(rule iffD2, rule HS_iff)
  apply(rule conjI, rule MGsep'_P_name)
  using assms HS_iff P_name_in_M
      apply(simp, simp, force)
   apply(rule_tac A="list(HS)" in subsetD, rule list_mono)
  using HS_iff P_name_in_M assms
    apply (force, simp)
  apply(rule conjI)
   apply(simp add: MGsep'_def delta0sep_Base_def)
   apply blast
  apply(rule symmetric_MGsep')
  using assms
  by auto

lemma MGsep_in_SymExt : 
  fixes x env \<phi>
  assumes 
    "x \<in> SymExt(G)" 
    "env \<in> list(SymExt(G))" 
    "\<phi> \<in> formula" 
    "arity(\<phi>) = 1 #+ length(env)"
  shows "MGsep(x, \<phi>, env) \<in> SymExt(G)"
proof - 

  have xinMG : "x \<in> M[G]" 
    using SymExt_subset_GenExt assms by auto

  have envinMGlist : "env \<in> list(M[G])" 
    by(rule subsetD, rule list_mono, rule SymExt_subset_GenExt, simp add:assms)

  obtain x' where x'H : "val(G, x') = x" "x' \<in> HS"
    using assms unfolding SymExt_def by auto 
  
  have "\<exists>env' \<in> list(HS). map(\<lambda>v. val(G, v), env') = env" 
    using \<open>env \<in> list(SymExt(G))\<close> 
  proof (induct)
    case Nil
    then show ?case 
      apply(rule_tac x=Nil in bexI)
      by auto
  next
    case (Cons a l)
    then obtain a' l' where "a' \<in> HS" "val(G, a') = a" "l' \<in> list(HS)" "map(\<lambda>v. val(G, v), l') = l" using SymExt_def by auto
    then show ?case 
      apply(rule_tac x="Cons(a', l')" in bexI)
      by auto
  qed 
  then obtain env' where env'H : "env' \<in> list(HS)" "map(\<lambda>v. val(G, v), env') = env" by auto 

  have eq : "val(G, MGsep'(x', \<phi>, env')) = MGsep(x, \<phi>, env)" 
    apply(rule MGsep_eq)
    using assms x'H env'H 
    by auto 

  have "MGsep'(x', \<phi>, env') \<in> HS" 
    apply(rule MGsep'_in_HS)
    using x'H assms env'H length_map 
    by auto

  then show ?thesis 
    unfolding SymExt_def 
    apply simp
    apply(rule_tac x="MGsep'(x', \<phi>, env')" in bexI)
    using eq 
    by auto
qed  


lemma SymExt_delta0_separation : 
  fixes x env \<phi>
  assumes "x \<in> SymExt(G)" "env \<in> list(SymExt(G))" "\<phi> \<in> \<Delta>0" "arity(\<phi>) \<le> 1 #+ length(env)" 
  shows "{ u \<in> x. sats(SymExt(G), \<phi>, [u] @ env) } \<in> SymExt(G)" 
proof (cases "arity(\<phi>) = 0")
  case True
  then have H : "\<And>u. u \<in> SymExt(G) \<Longrightarrow> sats(SymExt(G), \<phi>, [u] @ env) \<longleftrightarrow> sats(SymExt(G), \<phi>, [])" 
    apply(rename_tac u, rule_tac Q="sats(SymExt(G), \<phi>, [] @ [u] @ env)" in iff_trans, simp)
    apply(rule arity_sats_iff)
    using assms \<Delta>0_subset le_refl 
    by auto
  
  then show ?thesis
  proof(cases "sats(SymExt(G), \<phi>, [])")
    case True
    then have "\<And>u. u \<in> SymExt(G) \<Longrightarrow> sats(SymExt(G), \<phi>, [u] @ env)" using H by auto 
    then have "{ u \<in> x. sats(SymExt(G), \<phi>, [u] @ env) } = x" 
      apply(rule_tac equality_iffI, rule_tac iffI, simp)
      apply(rename_tac u, subgoal_tac "u \<in> SymExt(G)", force)
      using Transset_SymExt assms
      unfolding Transset_def 
      by blast
    then show ?thesis using assms by auto
  next
    case False
    then have "\<And>u. u \<in> SymExt(G) \<Longrightarrow> \<not>sats(SymExt(G), \<phi>, [u] @ env)" using H by auto 
    then have "{ u \<in> x. sats(SymExt(G), \<phi>, [u] @ env) } = 0" 
      apply(rule_tac equality_iffI, rule_tac iffI)
       apply(rename_tac u, subgoal_tac "u \<in> SymExt(G)", force)
      using Transset_SymExt assms
      unfolding Transset_def 
       apply blast
      by simp
    then show ?thesis 
      using M_subset_SymExt zero_in_M generic 
      by auto
  qed 
next
  case False
  then have arityle : "1 \<le> arity(\<phi>)" 
    apply(rule_tac not_lt_imp_le, simp)
    using assms \<Delta>0_subset 
    by auto

  have "succ(arity(\<phi>) #- 1) = 1 #+ (arity(\<phi>) #- 1)" by simp
  also have "... = arity(\<phi>)" 
    apply(rule add_diff_inverse)
    using assms \<Delta>0_subset arityle 
    by auto
  finally have eq : "succ(arity(\<phi>) #- 1) = arity(\<phi>)" by simp

  have "\<exists>e \<in> list(SymExt(G)). \<exists>extra \<in> list(SymExt(G)). length(e) = arity(\<phi>) #- 1 \<and> env = e @ extra" 
    apply(rule append_notation)
    using assms
      apply (simp, simp, simp)
    apply(subgoal_tac "succ(arity(\<phi>) #- 1) \<le> succ(length(env))", simp)
    apply(subst eq)
    by simp

  then obtain e extra where eH: "e \<in> list(SymExt(G))" "extra \<in> list(SymExt(G))" "length(e) = arity(\<phi>) #- 1" "env = e @ extra" by auto 

  have eq' : "succ(length(e)) = arity(\<phi>)"
    apply(rule_tac b="arity(\<phi>)" and a="succ(arity(\<phi>) #- 1)" in ssubst)
    by(rule eq_flip, rule eq, simp, simp add:eH)
  
  have inSymExt: "MGsep(x, \<phi>, e) \<in> SymExt(G)"
    apply(rule_tac MGsep_in_SymExt)
    using assms \<Delta>0_subset eH eq' 
    by auto

  have "MGsep(x, \<phi>, e) = { u \<in> x. sats(SymExt(G), \<phi>, [u] @ e) }" 
    unfolding MGsep_def
    apply(rule iff_eq, rule iff_flip)
    apply(rule \<Delta>0_sats_iff, rule SymExt_subset_GenExt)
       apply (rule app_type, simp)
    using Transset_SymExt Transset_def assms eH
        apply (force, force, simp, simp, simp)
    apply(subst eq, rule le_refl)
    using assms \<Delta>0_subset
    by auto
  also have "... = { u \<in> x. sats(SymExt(G), \<phi>, ([u] @ e) @ extra) }" 
    apply(rule iff_eq, rule iff_flip)
    apply(rule arity_sats_iff)
    using assms eH \<Delta>0_subset
       apply(force, simp, simp)
    using Transset_SymExt Transset_def assms eH
    using le_refl assms \<Delta>0_subset eq'
    by auto
  also have "... = { u \<in> x. sats(SymExt(G), \<phi>, [u] @ env) }"
    apply(rule iff_eq)
    apply(rename_tac u, rule_tac b="([u] @ e) @ extra" and a="[u] @ env" in ssubst)
    using eH app_assoc 
    by auto

  finally show "{u \<in> x . SymExt(G), [u] @ env \<Turnstile> \<phi>} \<in> SymExt(G)"
    using inSymExt by auto
qed


end 
end 













