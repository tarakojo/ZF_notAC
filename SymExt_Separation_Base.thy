theory SymExt_Separation_Base
  imports 
    "Forcing/Forcing_Main" 
    SymExt_Definition
begin 

context M_symmetric_system_G_generic
begin


definition cartprod' where "cartprod'(A, B, Z) \<equiv> \<forall>u \<in> M. u \<in> Z \<longleftrightarrow> (\<exists>x \<in> M. x \<in> A \<and> (\<exists>y \<in> M. y \<in> B \<and> pair(##M, x, y, u)))" 
definition powerset' where "powerset'(A, Z) \<equiv> \<forall>x \<in> M. x \<in> Z \<longleftrightarrow> subset(##M, x, A)"
definition is_singleton' where "is_singleton'(x, Z) \<equiv> \<forall>a \<in> M. a \<in> Z \<longleftrightarrow> a = x"
lemma is_singleton'_iff : "x \<in> M \<Longrightarrow> Z \<in> M \<Longrightarrow> is_singleton'(x, Z) \<longleftrightarrow> is_singleton(##M, x, Z)" 
  unfolding is_singleton'_def 
  apply(simp, rule iffI, rule equality_iffI, rule iffI)
  using transM 
  by auto

definition Hsep_base_M where "Hsep_base_M(xP, g) \<equiv> { v \<in> M. \<exists>x. \<exists>P. xP = <x, P> \<and> v \<in> Pow((\<Union>(g``(domain(x) \<times> {P}))) \<times> P) \<inter> M }" 
definition Hsep_base_M_cond where "Hsep_base_M_cond(v, xP, g) \<equiv>
   \<exists>x \<in> M. \<exists>P \<in> M. \<exists>domx \<in> M. \<exists>Ps \<in> M. \<exists>dPs \<in> M. \<exists>gi \<in> M. \<exists>gu \<in> M. \<exists>guP \<in> M. \<exists>PguP \<in> M. 
  pair(##M, x, P, xP) \<and> is_domain(##M, x, domx) \<and> is_singleton'(P, Ps) \<and> cartprod'(domx, Ps, dPs) \<and> image(##M, g, dPs, gi) \<and> big_union(##M, gi, gu) \<and> cartprod'(gu, P, guP) \<and> powerset'(guP, PguP) \<and> v \<in> PguP" 

lemma Hsep_base_M_eq : 
  "xP \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> Hsep_base_M(xP, g) = { v \<in> M. Hsep_base_M_cond(v, xP, g) }" 
  unfolding Hsep_base_M_def Hsep_base_M_cond_def
  apply(rule iff_eq, rule iff_flip) 
  apply(rule_tac Q="\<exists>x \<in> M. \<exists>P \<in> M. \<exists>domx \<in> M. \<exists>Ps \<in> M. \<exists>dPs \<in> M. \<exists>gi \<in> M. \<exists>gu \<in> M. \<exists>guP \<in> M. \<exists>PguP \<in> M. 
                pair(##M, x, P, xP) \<and> is_domain(##M, x, domx) \<and> is_singleton(##M, P, Ps) \<and> cartprod(##M, domx, Ps, dPs) \<and> image(##M, g, dPs, gi) \<and> big_union(##M, gi, gu) \<and> cartprod(##M, gu, P, guP) \<and> powerset(##M, guP, PguP) \<and> v \<in> PguP" in iff_trans)
  apply(simp add: cartprod_def cartprod'_def powerset_def powerset'_def is_singleton'_iff)
  apply simp
  apply(rule iffI, clarsimp)
  apply clarsimp 
  using pair_in_M_iff 
   apply simp
  using pair_in_M_iff domain_closed singleton_in_M_iff cartprod_closed image_closed Union_closed
  apply clarsimp 
  apply(rename_tac v x P, rule_tac b="{a \<in> Pow((\<Union>(g `` (domain(x) \<times> {P}))) \<times> P) . a \<in> M}" and a="Pow((\<Union>(g `` (domain(x) \<times> {P}))) \<times> P) \<inter> M" in ssubst)
   apply force
  apply(rule M_powerset)
  using pair_in_M_iff domain_closed singleton_in_M_iff cartprod_closed image_closed Union_closed
  by clarsimp 
  
schematic_goal Hsep_base_M_fm_auto:
  assumes
    "s \<in> M" "g \<in> M" "xP \<in> M"
    "nth(0,env) = s"    
    "nth(1,env) = g"    
    "nth(2,env) = xP"    
    "env \<in> list(M)" 
 shows 
    "s = Hsep_base_M(xP, g) \<longleftrightarrow> sats(M,?fm(0,1,2),env)"

  apply(rule_tac Q="\<forall>v \<in> M. v \<in> s \<longleftrightarrow> Hsep_base_M_cond(v, xP, g)" in iff_trans) 
   apply(rule iffI, rule ballI, simp)
  using Hsep_base_M_eq assms 
    apply force
  apply(rule equality_iffI, rule iffI)  
  using Hsep_base_M_eq assms transM
    apply (force, force)
  unfolding  Hsep_base_M_cond_def cartprod'_def powerset'_def is_singleton'_def subset_def
  by (insert assms ; (rule sep_rules | simp)+) 

definition Hsep_base_M_fm where 
  "Hsep_base_M_fm \<equiv> Forall
             (Iff(Member(0, 1),
                  Exists
                   (Exists
                     (Exists
                       (Exists
                         (Exists
                           (Exists
                             (Exists
                               (Exists
                                 (Exists
                                   (And(pair_fm(8, 7, 12),
                                        And(domain_fm(8, 6),
                                            And(Forall(Iff(Member(0, 6), Equal(0, 8))),
                                                And(Forall
                                                     (Iff(Member(0, 5),
                                                          Exists(And(Member(0, 8), Exists(And(Member(0, 8), pair_fm(1, 0, 2))))))),
                                                    And(image_fm(11, 4, 3),
                                                        And(big_union_fm(3, 2),
                                                            And(Forall
                                                                 (Iff(Member(0, 2),
                                                                      Exists
                                                                       (And(Member(0, 4), Exists(And(Member(0, 10), pair_fm(1, 0, 2))))))),
                                                                And(Forall(Iff(Member(0, 1), Forall(Implies(Member(0, 1), Member(0, 3))))),
                                                                    Member(9, 0))))))))))))))))))))  " 

lemma Hsep_base_M_in_M : "xP \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> Hsep_base_M(xP, g) \<in> M" 
proof (cases "\<exists>x. \<exists>P. xP = <x, P>")
  case False
  then have "Hsep_base_M(xP, g) = 0" unfolding Hsep_base_M_def by auto
  then show ?thesis using zero_in_M by auto
next
  assume assms : "xP \<in> M" "g \<in> M" "function(g)" 

  case True
  then obtain x P where xPH: "xP = <x, P>" by auto 

  have H: "Hsep_base_M(xP, g) = Pow((\<Union>(g``(domain(x) \<times> {P}))) \<times> P) \<inter> M"
    unfolding Hsep_base_M_def 
    using xPH 
    by auto

  have "Pow((\<Union>(g``(domain(x) \<times> {P}))) \<times> P) \<inter> M \<in> M" 
    apply(rule M_powerset)
    using xPH assms pair_in_M_iff singleton_in_M_iff domain_closed cartprod_closed image_closed Union_closed
    by auto  

  then show ?thesis 
    using H zero_in_M singleton_in_M_iff by force
qed

definition Hsep_base where "Hsep_base(x, g) \<equiv> Pow((\<Union>(g``domain(x))) \<times> P) \<inter> M"

definition sep_base where "sep_base(x) \<equiv> wftrec(Memrel(M)^+, x, Hsep_base)" 

lemma def_sep_base : 
  fixes x 
  assumes "x \<in> M" 
  shows "sep_base(x) = Pow((\<Union>{ sep_base(y). y \<in> domain(x) }) \<times> P) \<inter> M" 
proof - 

  define F where "F \<equiv> \<lambda>y \<in> Memrel(M)^+ -`` {x}. sep_base(y)"
  define S where "S \<equiv> { sep_base(y). y \<in> domain(x) }" 

  have H1: "sep_base(x) = Pow((\<Union>(F``domain(x))) \<times> P) \<inter> M" 
    unfolding sep_base_def 
    apply(subst wftrec)
      apply(rule wf_trancl,rule wf_Memrel, rule trans_trancl)
    unfolding Hsep_base_def F_def sep_base_def
    by simp

  have H2: "F``domain(x) = S" 
  proof(rule equality_iffI, rule iffI)
    fix v assume "v \<in> F``domain(x)"
    then obtain u where uH: "<u, v> \<in> F" "u \<in> domain(x)" by auto 
    have Fu : "F`u = v" 
      apply(rule function_apply_equality)
      apply(simp add:uH)
      unfolding F_def
      apply(rule function_lam)
      done
    have "u \<in> Memrel(M)^+ -``{x}" using uH domain_elem_Memrel_trancl assms by auto
    then have "v = sep_base(u)" using Fu unfolding F_def by auto 
    then show "v \<in> S" 
      unfolding S_def 
      using uH 
      by auto
  next 
    fix v assume "v \<in> S" 
    then obtain u where uH : "u \<in> domain(x)" "v = sep_base(u)" unfolding S_def by auto 
    then have uin : "u \<in> Memrel(M)^+ -`` {x}" using assms domain_elem_Memrel_trancl uH by auto 
    have Fu: "F`u = v" 
      unfolding F_def 
      using uin uH 
      by auto 
    have "<u, F`u> \<in> F" 
      apply(rule function_apply_Pair)
      unfolding F_def
       apply(rule function_lam, subst domain_lam, simp add:uin)
      done
    then show "v \<in> F``domain(x)" 
      using uin uH Fu by auto
  qed

  show ?thesis 
    using H1 H2 
    unfolding F_def S_def 
    by auto
qed

definition is_sep_base_fm where "is_sep_base_fm(x, p, s) \<equiv> is_memrel_wftrec_fm(Hsep_base_M_fm, x, p, s)" 

lemma Hsep_base_eq : 
  fixes h g x 
  assumes "h \<in> eclose(x) \<rightarrow> M" "g \<in> eclose(x) \<times> {P} \<rightarrow> M" "g \<in> M" "x \<in> M" 
          "\<And>y. y \<in> eclose(x) \<Longrightarrow> h ` y = g ` \<langle>y, P\<rangle>" 
  shows "Hsep_base(x, h) = Hsep_base_M(\<langle>x, P\<rangle>, g)"
proof - 

  have iff_lemma : "\<And>a b c. b = c \<Longrightarrow> a = b \<longleftrightarrow> a = c" by auto

  have image_lemma : "\<And>f d v. function(f) \<Longrightarrow> d \<subseteq> domain(f) \<Longrightarrow> v \<in> f``d \<longleftrightarrow> (\<exists>a \<in> d. v = f`a)" 
  proof(rule iffI)
    fix f d v assume assms1: "function(f)" "v \<in> f``d" 
    then obtain a where aH : "<a, v> \<in> f" "a \<in> d" by auto 
    have "f`a = v" by(rule function_apply_equality, simp add:aH, simp add:assms1)
    then show "\<exists>a\<in>d. v = f ` a" using aH by auto 
  next 
    fix f d v assume assms1: "function(f)" "d \<subseteq> domain(f)" "\<exists>a\<in>d. v = f ` a" 
    then obtain a where aH : "a \<in> d" "v = f`a" by auto 
    have "<a, f`a> \<in> f" 
      apply(rule function_apply_Pair) 
      using assms1 aH 
      by auto
    then show "v \<in> f `` d" 
      using aH 
      by auto
  qed

  have "h `` domain(x) = g `` (domain(x) \<times> {P})" 
  proof(rule equality_iffI)
    fix v
    have "v \<in> h `` domain(x) \<longleftrightarrow> (\<exists>y \<in> domain(x). v = h`y)"
      apply(rule image_lemma)
      using assms Pi_def 
       apply simp
      apply(rule_tac b="domain(h)" and a="eclose(x)" in ssubst) 
       apply(rule_tac B=M in domain_Pi, simp add:assms)
      apply(rule subsetI)
      using domain_elem_in_eclose 
      by auto
    also have "... \<longleftrightarrow> (\<exists>y \<in> domain(x). v = g`<y, P>)" 
      apply(rule bex_iff, rule iff_lemma)
      apply(rename_tac y, subgoal_tac "y \<in> eclose(x)") 
      using assms 
       apply force
      using domain_elem_in_eclose assms 
      by auto
    also have "... \<longleftrightarrow> (\<exists>yP \<in> domain(x) \<times> {P}. v = g`yP)" by auto 
    also have "... \<longleftrightarrow> v \<in> g `` (domain(x) \<times> {P})" 
      apply(rule iff_flip, rule image_lemma)
      using assms Pi_def 
       apply simp
      apply(rule_tac b="domain(g)" and a="eclose(x) \<times> {P}" in ssubst) 
      apply(rule_tac B=M in domain_Pi)
      using assms domain_elem_in_eclose 
      by auto 
    finally show "v \<in> h `` domain(x) \<longleftrightarrow> v \<in> g `` (domain(x) \<times> {P}) " by simp
  qed

  then show ?thesis 
    unfolding Hsep_base_def Hsep_base_M_def
    apply simp
    apply(subgoal_tac "h `` domain(x) = g `` (domain(x) \<times> {P})", force)
    by simp
qed

lemma sats_is_sep_base_fm_iff : 
  fixes env i j k x s 
  assumes "env \<in> list(M)" "i < length(env)" "j < length(env)" "k < length(env)"
          "nth(i, env) = x" "nth(j, env) = P" "nth(k, env) = s" 
  shows "sats(M, is_sep_base_fm(i, j, k), env) \<longleftrightarrow> s = sep_base(x)" 

  unfolding sep_base_def is_sep_base_fm_def
  apply(rule_tac a=P and G=Hsep_base_M in sats_is_memrel_wftrec_fm_iff)
  using assms 
               apply auto[9]
      apply(simp add:Hsep_base_M_fm_def)
     apply(simp add:Hsep_base_M_fm_def)
     apply(simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)  
    apply(rule Hsep_base_M_in_M)
      apply auto[3]
   apply(rule Hsep_base_eq)
       apply auto[5]
  unfolding Hsep_base_M_fm_def
  apply(rule Hsep_base_M_fm_auto)
  by auto

lemma sep_base_in_M : 
  fixes x 
  assumes "x \<in> M" 
  shows "sep_base(x) \<in> M" 

  unfolding sep_base_def 
  apply(rule_tac a=P and G = Hsep_base_M and Gfm = Hsep_base_M_fm in  memrel_wftrec_in_M)
  using assms P_in_M 
        apply auto[2]
      apply(simp add:Hsep_base_M_fm_def)+
     apply(simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    apply(rule Hsep_base_M_in_M)
      apply auto[3]
   apply(rule Hsep_base_eq)
       apply auto[5]
  unfolding Hsep_base_M_fm_def
  apply(rule Hsep_base_M_fm_auto)
  by auto

lemma sep_base_in : 
  fixes x 
  assumes "x \<in> P_names" 
  shows "x \<in> sep_base(x)" 
proof - 
  have main : "\<And>x. x \<in> P_names \<longrightarrow> x \<in> sep_base(x)"
  proof (rule_tac Q="\<lambda>x. x \<in> P_names \<longrightarrow> x \<in> sep_base(x)" in ed_induction, rule impI)
    fix x assume assms: "(\<And>y. ed(y, x) \<Longrightarrow> y \<in> P_names \<longrightarrow> y \<in> sep_base(y))" "x \<in> P_names" 

    have domH: "domain(x) \<subseteq> \<Union>RepFun(domain(x), sep_base)" 
      apply(rule subsetI, simp)
      using assms P_name_domain_P_name 
      by blast

    have ranH: "range(x) \<subseteq> P" 
      using P_name_iff assms 
      by auto

    have H : "x \<subseteq> \<Union>RepFun(domain(x), sep_base) \<times> P" 
    proof (rule subsetI)
      fix v assume vin : "v \<in> x" 
      then obtain y p where ypH : "v = <y, p>" using assms P_name_iff by blast
      have "y \<in> domain(x)" using vin ypH by auto 
      then have yin : "y \<in> \<Union>RepFun(domain(x), sep_base)" using domH by auto
      have "p \<in> range(x)" using vin ypH by auto 
      then have pin : "p \<in> P" using ranH by auto
      show "v \<in> \<Union>RepFun(domain(x), sep_base) \<times> P" using ypH yin pin by auto
    qed
    then show "x \<in> sep_base(x)"
      apply(subst def_sep_base)
      using assms P_name_in_M 
      by auto
  qed

  then show ?thesis using assms by auto
qed

lemma sep_base_subset : 
  fixes x 
  assumes "x \<in> P_names" 
  shows "sep_base(x) \<subseteq> P_names"
proof- 
  have main : "\<And>x. x \<in> P_names \<longrightarrow> sep_base(x) \<subseteq> P_names" 
  proof(rule_tac Q="\<lambda> x. x \<in> P_names \<longrightarrow> sep_base(x) \<subseteq> P_names" in ed_induction, rule impI)
    fix x 
    assume assms : "(\<And>y. ed(y, x) \<Longrightarrow> y \<in> P_names \<longrightarrow> sep_base(y) \<subseteq> P_names)" "x \<in> P_names"
    have "\<Union>RepFun(domain(x), sep_base) \<subseteq> P_names" 
      apply(rule subsetI, simp, clarify)
      apply(rename_tac z y p, subgoal_tac "y \<in> P_names")
      using assms P_name_domain_P_name
      by auto
    then have "sep_base(x) \<subseteq> Pow(P_names \<times> P) \<inter> M" 
      apply(subst def_sep_base)
      using assms P_name_in_M 
       apply force
      apply force
      done
    then show "sep_base(x) \<subseteq> P_names" 
      using P_name_iff by auto
  qed
  then show ?thesis using assms by auto
qed
  
lemma sep_base_closed_under_Pn_auto : 
  fixes x0 x \<pi> 
  assumes "x0 \<in> P_names" "x \<in> sep_base(x0)" "\<pi> \<in> P_auto"   
  shows "Pn_auto(\<pi>)`x \<in> sep_base(x0)" 
proof - 
  have main : "\<And>x0 . x0 \<in> P_names \<longrightarrow> (\<forall> x \<in> sep_base(x0). Pn_auto(\<pi>)`x \<in> sep_base(x0))" 
  proof(rule_tac Q="\<lambda>x0 . x0 \<in> P_names \<longrightarrow> (\<forall> x \<in> sep_base(x0). Pn_auto(\<pi>)`x \<in> sep_base(x0))" in ed_induction, rule impI, rule ballI, rename_tac a x0 x)
    fix x0 x assume assms1: "x0 \<in> P_names" "x \<in> sep_base(x0)" "\<And>y0. ed(y0, x0) \<Longrightarrow> y0 \<in> P_names \<longrightarrow> ( \<forall> y \<in> sep_base(y0). Pn_auto(\<pi>) ` y \<in> sep_base(y0))"

    have xpname : "x \<in> P_names" using sep_base_subset assms1 by auto 
    have pnautoeq : "Pn_auto(\<pi>)`x = { <Pn_auto(\<pi>)`y, \<pi>`p> . <y, p> \<in> x }" using Pn_auto xpname by auto
    have deleq : "sep_base(x0) = Pow(\<Union>RepFun(domain(x0), sep_base) \<times> P) \<inter> M"
      using def_sep_base P_name_in_M assms1 by auto 
    have xsubset : "x \<subseteq> \<Union>RepFun(domain(x0), sep_base) \<times> P" using deleq assms1 by auto  

    have domH: "\<And>y. y \<in> domain(x) \<Longrightarrow> Pn_auto(\<pi>)`y \<in> \<Union>RepFun(domain(x0), sep_base)" 
    proof - 
      fix y assume yindom : "y \<in> domain(x)" 
      then obtain y0 where y0H : "y0 \<in> domain(x0)" "y \<in> sep_base(y0)" using assms xsubset by blast
      then have "Pn_auto(\<pi>)`y \<in> sep_base(y0)" using assms1 P_name_domain_P_name ed_def by auto
      then show "Pn_auto(\<pi>)`y \<in> \<Union>RepFun(domain(x0), sep_base)" using y0H by auto 
    qed

    have H: "Pn_auto(\<pi>)`x \<subseteq> (\<Union>RepFun(domain(x0), sep_base) \<times> P)"
    proof(rule subsetI)
      fix v assume "v \<in> Pn_auto(\<pi>)`x" 
      then have "\<exists>y p. <y, p> \<in> x \<and> v = <Pn_auto(\<pi>)`y, \<pi>`p>" 
        apply(rule_tac pair_rel_arg)
        using xpname relation_P_name pnautoeq 
        by auto
      then obtain y p where ypH: "v = <Pn_auto(\<pi>)`y, \<pi>`p>" "<y, p> \<in> x" using pnautoeq by blast
      then have H : "Pn_auto(\<pi>)`y \<in> \<Union>RepFun(domain(x0), sep_base)" using ypH domH by auto
      have "p \<in> P" using xpname P_name_iff ypH by auto 
      then have "\<pi>`p \<in> P" using assms P_auto_value P_auto_def by auto 
      then show "v \<in> (\<Union>RepFun(domain(x0), sep_base) \<times> P)" using H ypH by auto
    qed

    show "Pn_auto(\<pi>) ` x \<in> sep_base(x0)"
      apply(subst deleq)
      using H 
      apply simp
      apply(rule Pn_auto_value_in_M)
      using assms P_auto_def xpname
      by auto
  qed

  then show ?thesis using assms by auto
qed

lemma sep_base_closed_under_Pn_auto' : 
  fixes x x0 \<pi>
  assumes "x \<in> P_names" "x0 \<in> P_names" "\<pi> \<in> P_auto" 
  shows "x \<in> sep_base(x0) \<longleftrightarrow> Pn_auto(\<pi>)`x \<in> sep_base(x0)" 
proof (rule iffI) 
  assume "x \<in> sep_base(x0)" 
  then show "Pn_auto(\<pi>)`x \<in> sep_base(x0)" 
    apply(rule_tac sep_base_closed_under_Pn_auto)
    using assms 
    by auto 
next 
  assume assm1 : "Pn_auto(\<pi>) ` x \<in> sep_base(x0)" 
  have "converse(\<pi>) \<in> bij(P, P)" 
    apply(rule bij_converse_bij) 
    using assms P_auto_def is_P_auto_def 
    by auto
  then have H: "converse(\<pi>) \<in> P_auto" 
    unfolding P_auto_def
    apply simp
    apply(rule conjI)
    using bij_def inj_def 
     apply force
    using P_auto_converse assms P_auto_def
    by auto 
  have H1: "Pn_auto(converse(\<pi>)) ` (Pn_auto(\<pi>)`x) \<in> sep_base(x0)" 
    apply(rule sep_base_closed_under_Pn_auto)
    using assms assm1 H 
    by auto 
  
  have "Pn_auto(converse(\<pi>)) ` (Pn_auto(\<pi>)`x) = converse(Pn_auto(\<pi>)) ` (Pn_auto(\<pi>)`x)" 
    apply(subst Pn_auto_converse)
    using assms P_auto_def 
    by auto
  also have "... = (converse(Pn_auto(\<pi>)) O Pn_auto(\<pi>)) ` x" 
    apply(rule eq_flip, rule comp_fun_apply)
     apply(rule Pn_auto_type)
    using assms P_auto_def
    by auto 
  also have "... = id(P_names)`x" 
    apply(subst left_comp_inverse)
    using assms Pn_auto_bij bij_is_inj P_auto_def 
    by auto
  also have "... = x" using assms by auto 

  finally show "x \<in> sep_base(x0)" using H1 by auto
qed

lemma strong_replacement_sep_base : 
  shows "strong_replacement(##M, \<lambda>x y. y = sep_base(x))" 
proof -
  have H: "strong_replacement(##M, \<lambda>x y. sats(M, is_sep_base_fm(0, 2, 1), [x, y] @ [P]))" 
    apply(rule replacement_ax)
      apply(simp add: is_sep_base_fm_def, rule is_memrel_wftrec_fm_type, simp add: Hsep_base_M_fm_def)
    using P_in_M 
        apply auto[4]
    apply simp
    apply(simp add:is_sep_base_fm_def, rule le_trans, rule arity_is_memrel_wftrec_fm)
         apply(simp add: Hsep_base_M_fm_def, simp add:Hsep_base_M_fm_def)
        apply(simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
       apply auto[3]
    apply(rule Un_least_lt)+
    by auto
  show ?thesis
    apply(rule iffD1, rule strong_replacement_cong)
     apply(rename_tac x y, rule_tac env = "[x, y] @ [P]" and i=0 and j=2 and k=1 in sats_is_sep_base_fm_iff)
    using P_in_M
           apply auto[8]
    using H 
    by auto
qed

lemma sep_base_repfun_in_M : 
  fixes A 
  assumes "A \<in> M" 
  shows "{ sep_base(x). x \<in> A } \<in> M"

  apply(rule to_rin, rule RepFun_closed, rule strong_replacement_sep_base, simp add:assms)
  apply(rule ballI, simp, rule sep_base_in_M)
  using assms transM 
  by auto

definition sep_Base where "sep_Base(x)  \<equiv> \<Union>{ sep_base(y). y \<in> domain(x) } \<inter> HS" 

lemma sep_Base_in_M : 
  fixes x 
  assumes "x \<in> M" 
  shows "sep_Base(x) \<in> M" 

  unfolding sep_Base_def 
  apply(rule HS_separation, rule to_rin, rule Union_closed, simp)
  apply(rule sep_base_repfun_in_M)
  using assms domain_closed 
  by auto

lemma domain_in_sep_Base : "x \<subseteq> HS \<times> P \<Longrightarrow> y \<in> domain(x) \<Longrightarrow> y \<in> sep_Base(x)" 
  unfolding sep_Base_def 
  apply(simp, rule conjI)
   apply(rule_tac x="y" in bexI) 
    apply(rule sep_base_in)
  using HS_iff P_name_domain_P_name
    apply force
   apply simp
  using HS_iff 
  by auto

lemma in_sep_Base_iff : "v \<in> sep_Base(x) \<longleftrightarrow> (v \<in> HS \<and> (\<exists>u \<in> domain(x). v \<in> sep_base(u)))" 
  unfolding sep_Base_def 
  by auto

lemma sep_Base_Pn_auto : 
  fixes x0 \<pi> x 
  assumes "x0 \<in> P_names" "\<pi> \<in> \<G>" "x \<in> P_names" 
  shows "x \<in> sep_Base(x0) \<longleftrightarrow> Pn_auto(\<pi>)`x \<in> sep_Base(x0)"
proof -
  have "x \<in> sep_Base(x0) \<longleftrightarrow> (x \<in> HS \<and> (\<exists>u \<in> domain(x0). x \<in> sep_base(u)))" 
    using in_sep_Base_iff assms by auto
  also have "... \<longleftrightarrow> (Pn_auto(\<pi>)`x \<in> HS \<and> (\<exists>u \<in> domain(x0). Pn_auto(\<pi>)`x \<in> sep_base(u)))" 
    apply(rule iff_conjI)
     apply(rule HS_Pn_auto, simp add:assms, simp add:assms)
    apply(rule bex_iff)
    apply(rule sep_base_closed_under_Pn_auto')
    using assms P_name_domain_P_name \<G>_P_auto_group is_P_auto_group_def P_auto_def 
    by auto
  also have "... \<longleftrightarrow> Pn_auto(\<pi>)`x \<in> sep_Base(x0)" 
    apply(rule iff_flip, rule in_sep_Base_iff)
    done
  finally show "x \<in> sep_Base(x0) \<longleftrightarrow> Pn_auto(\<pi>) ` x \<in> sep_Base(x0) " by simp
qed

lemma ex_separation_base : 
  fixes X 
  assumes "X \<subseteq> HS" "X \<in> M" 
  shows "\<exists>S \<in> SymExt(G). { val(G, x). x \<in> X } \<subseteq> S" 
proof - 
  define A where "A \<equiv> X \<times> P" 
  define B where "B \<equiv> sep_Base(A) \<times> P" 

  have Apname : "A \<in> P_names" 
    apply(rule iffD2, rule P_name_iff)
    unfolding A_def
    apply(rule conjI, rule to_rin, rule cartprod_closed)
    using assms P_in_M HS_iff
    by auto

  then have "sep_Base(A) \<in> M" 
    by(rule_tac sep_Base_in_M, simp add:assms P_name_in_M)

  then have pname : "sep_Base(A) \<times> P \<in> P_names" 
    apply(rule_tac iffD2)
     apply(rule P_name_iff)
    apply(rule conjI, rule to_rin, rule cartprod_closed, simp, simp add:P_in_M)
    unfolding sep_Base_def 
    using HS_iff 
    by auto 

  have "\<And>\<pi>. \<pi> \<in> \<G> \<Longrightarrow> Pn_auto(\<pi>)`(sep_Base(A) \<times> P) = sep_Base(A) \<times> P" 
  proof - 
    fix \<pi>
    assume piin : "\<pi> \<in> \<G>"
    then have pipauto : "\<pi> \<in> P_auto" 
      using \<G>_P_auto_group is_P_auto_group_def P_auto_def
      by auto 

    have "Pn_auto(\<pi>)`(sep_Base(A) \<times> P) = {\<langle>Pn_auto(\<pi>) ` y, \<pi> ` p\<rangle> . \<langle>y,p\<rangle> \<in> sep_Base(A) \<times> P}" 
      apply(subst Pn_auto)
      using pname
      by auto 
    also have "... = sep_Base(A) \<times> P" 
    proof(rule equality_iffI, rule iffI)
      fix v assume "v \<in> {\<langle>Pn_auto(\<pi>) ` y, \<pi> ` p\<rangle> . \<langle>y,p\<rangle> \<in> sep_Base(A) \<times> P}" 
      then obtain y p where ypH : "y \<in> sep_Base(A)" "p \<in> P" "v = \<langle>Pn_auto(\<pi>) ` y, \<pi> ` p\<rangle>" by auto

      have H1: "Pn_auto(\<pi>) ` y \<in> sep_Base(A)" 
        apply(rule iffD1, rule sep_Base_Pn_auto)
        using assms piin sep_Base_def HS_iff ypH Apname
        by auto
      have H2: "\<pi>`p \<in> P" 
        apply(rule P_auto_value)
        using pipauto P_auto_def ypH
        by auto 
      show "v \<in> sep_Base(A) \<times> P" 
        using H1 H2 ypH 
        by auto
    next 
      fix v assume "v \<in> sep_Base(A) \<times> P" 
      then obtain y p where ypH : "y \<in> sep_Base(A)" "p \<in> P" "v = \<langle>y, p\<rangle>" by auto

      have ypname : "y \<in> P_names" using ypH sep_Base_def HS_iff by auto

      have "Pn_auto(\<pi>) \<in> surj(P_names, P_names)" 
        apply(rule bij_is_surj, rule Pn_auto_bij)
        using pipauto P_auto_def
        by auto 
      then obtain y' where y'H : "y = Pn_auto(\<pi>)`y'" "y' \<in> P_names" 
        unfolding surj_def using ypname by auto 
      have y'in : "y' \<in> sep_Base(A)" 
        apply(rule iffD2, rule_tac \<pi>=\<pi> in sep_Base_Pn_auto)
        using y'H ypH piin assms Apname
        by auto

      have "\<pi> \<in> surj(P, P)" 
        apply(rule bij_is_surj)
        using pipauto P_auto_def is_P_auto_def
        by auto
      then obtain p' where p'H : "p' \<in> P" "p = \<pi>`p'" 
        unfolding surj_def using ypH by auto 

      have "<Pn_auto(\<pi>)`y', \<pi>`p'> \<in> {\<langle>Pn_auto(\<pi>) ` y, \<pi> ` p\<rangle> . \<langle>y,p\<rangle> \<in> sep_Base(A) \<times> P}"
        using y'H p'H y'in by auto 
      then show "v \<in> {\<langle>Pn_auto(\<pi>) ` y, \<pi> ` p\<rangle> . \<langle>y,p\<rangle> \<in> sep_Base(A) \<times> P}" 
        using p'H y'H ypH by auto
    qed

    finally show "Pn_auto(\<pi>) ` (sep_Base(A) \<times> P) = sep_Base(A) \<times> P " by simp
  qed

  then have "sym(sep_Base(A) \<times> P) = \<G>" 
    unfolding sym_def
    by blast

  then have symH : "symmetric(sep_Base(A) \<times> P)" 
    unfolding symmetric_def
    using \<G>_in_\<F>
    by auto

  have "sep_Base(A) \<times> P \<in> HS" 
    apply(rule iffD2, rule HS_iff)
    using pname symH sep_Base_def
    by auto 

  then have insymext : "val(G, sep_Base(A) \<times> P) \<in> SymExt(G)" 
    unfolding SymExt_def by auto 

  have Xsubset: "X \<subseteq> sep_Base(A)" 
    unfolding A_def
    apply(rule subsetI, rule domain_in_sep_Base)
    using assms
     apply force
    apply(rule_tac b=one in domainI)
    using one_in_P
    by auto 

  have subsetH: "{ val(G, x). x \<in> X } \<subseteq> val(G, sep_Base(A) \<times> P)" 
  proof(rule subsetI)
    fix v assume "v \<in> { val(G, x). x \<in> X }"
    then obtain x where xH : "v = val(G, x)" "x \<in> X" by auto 
    then have "val(G, x) \<in> val(G, sep_Base(A) \<times> P)" 
      apply(subst (2) def_val, simp)
      apply(rule_tac x=x in bexI, simp, rule conjI)
      using Xsubset 
        apply force
       apply(rule_tac x=one in bexI)
      using one_in_G one_in_P generic Xsubset
      by auto
    then show "v \<in> val(G, sep_Base(A) \<times> P)" 
      using xH 
      by auto 
  qed

  show ?thesis 
    apply(rule_tac x="val(G, sep_Base(A) \<times> P)" in bexI)
     apply(rule subsetH, rule insymext)
    done
qed

end
end