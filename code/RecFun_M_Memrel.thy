theory RecFun_M_Memrel
  imports 
    ZF 
    RecFun_M
begin 

definition InEclose where "InEclose(y, x) \<equiv> y \<in> eclose(x)"  
definition InEclose_fm where "InEclose_fm \<equiv> Exists(And(is_eclose_fm(2, 0), Member(1, 0)))"

context M_ctm 
begin 

lemma Relation_fm_InEclose : 
  "Relation_fm(InEclose, InEclose_fm)" 
  unfolding Relation_fm_def 
  apply(rule conjI, simp add:InEclose_fm_def, rule conjI, simp add:InEclose_fm_def)
  apply(subst arity_is_eclose_fm, simp, simp)
   apply(simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union) 
  apply clarify
  unfolding InEclose_def InEclose_fm_def
  apply simp
  using eclose_closed 
  by auto

lemma eclose_M : "eclose(M) = M" 
proof(rule equality_iffI, rule iffI)
  have H: "\<And>n. n \<in> nat \<Longrightarrow> \<forall>x. x \<in> Union^n(M) \<longrightarrow> x \<in> M"
  proof(rule_tac P="\<lambda>n. \<forall>x. x \<in> Union^n(M) \<longrightarrow> x \<in> M" in nat_induct, assumption, force, rule allI, rule impI)
    fix n x assume assms1: "n \<in> nat" "\<forall>x. x \<in> Union^n (M) \<longrightarrow> x \<in> M" "x \<in> Union^succ(n) (M)" 
    then have "x \<in> Union(Union^n(M))" by auto 
    then obtain y where yH: "x \<in> y" "y \<in> Union^n(M)" by auto 
    then have "y \<in> M" using assms1 by auto 
    then show "x \<in> M" using yH transM by auto 
  qed
  fix x assume "x \<in> eclose(M)" 
  then obtain n where "n \<in> nat" "x \<in> Union^n(M)" using eclose_eq_Union by auto 
  then show "x \<in> M" using H by auto 
next 
  fix x assume "x \<in> M" 
  then show "x \<in> eclose(M)" 
    apply(subst eclose_eq_Union, simp)
    apply(rule_tac x=0 in bexI, auto)
    done
qed

lemma Rrel_InEclose : 
  "Rrel(InEclose, M) = Memrel(M)^+" 
proof (rule equality_iffI, rule iffI)
  fix v assume "v \<in> Rrel(InEclose, M)" 
  then obtain y x where yxH : "v = <y, x>" "y \<in> eclose(x)" "y \<in> M" "x \<in> M" unfolding InEclose_def Rrel_def by auto
  then have "y \<in> (\<Union>n\<in>nat. Union^n (x))" using eclose_eq_Union by auto
  then obtain n where nH: "n \<in> nat" "y \<in> Union^n(x)" by auto

  have "\<And>n. n \<in> nat \<Longrightarrow> \<forall>y. y \<in> Union^n(x) \<longrightarrow> <y, x> \<in> Memrel(M)^+" 
  proof(rule_tac P="\<lambda>n. \<forall>y. y \<in> Union^n(x) \<longrightarrow> <y, x> \<in> Memrel(M)^+" in nat_induct, assumption)
    fix n assume nnat : "n \<in> nat" 
    show "\<forall>y. y \<in> Union^0 (x) \<longrightarrow> <y, x> \<in> Memrel(M)^+"
    proof(rule allI, rule impI)
      fix z assume "z \<in> Union^0(x)" 
      then have rel : "z \<in> x" by auto 
      then have zin : "z \<in> M" using yxH transM by auto 

      show "<z, x> \<in> Memrel(M)^+" 
        apply(rule r_into_trancl)
        unfolding Memrel_def 
        using rel zin yxH 
        by auto
    qed
  next 
    fix n 
    assume assms1 : "n \<in> nat" "\<forall>y. y \<in> Union^n (x) \<longrightarrow> \<langle>y, x\<rangle> \<in> Memrel(M)^+"
    show "\<forall>y. y \<in> Union^succ(n) (x) \<longrightarrow> \<langle>y, x\<rangle> \<in> Memrel(M)^+" 
    proof(rule allI, rule impI)
      fix z assume "z \<in> Union^succ(n) (x)" 
      then have "z \<in> Union(Union^n(x))" by auto 
      then obtain w where wH : "z \<in> w" "w \<in> Union^n(x)" by auto 
      then have rel : "<w, x> \<in> Memrel(M)^+" using assms1 by auto 
      then have "w \<in> field(Memrel(M)^+)" by auto 
      then have "w \<in> field(Memrel(M))" using field_trancl by auto 
      then have win : "w \<in> M" by auto 
      then have zin : "z \<in> M" using transM wH by auto 
      show "<z, x> \<in> Memrel(M)^+" 
        apply(rule_tac b=w in rtrancl_into_trancl2)
        using win zin wH 
         apply force
        apply(rule trancl_into_rtrancl, simp add:rel)
        done
    qed
  qed

  then show "v \<in> Memrel(M)^+" using yxH nH by auto
next 
  fix v assume vin: "v \<in> Memrel(M)^+" 
  then obtain y x where yxH: "v = <y, x>" unfolding trancl_def comp_def by auto 
  then have "<y, x> \<in> Rrel(InEclose, M)" 
  proof(rule_tac P="\<lambda>x. <y, x> \<in> Rrel(InEclose, M)" and r="Memrel(M)" and a=y in trancl_induct)
    show "<y, x> \<in> Memrel(M)^+" using yxH vin by auto 
  next 
    fix z assume "<y, z> \<in> Memrel(M)"
    then have "y \<in> M" "z \<in> M" "y \<in> z" by auto
    then show "<y, z> \<in> Rrel(InEclose, M)" 
      unfolding Rrel_def InEclose_def 
      apply simp
      apply(subst eclose_eq_Union, simp, rule_tac x=0 in bexI)
      by auto 
  next 

    have H : "\<And>A B n. n \<in> nat \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Union^n(A) \<subseteq> Union^n(B)" 
      apply(rename_tac A B n, rule_tac P="\<lambda>n. Union^n(A) \<subseteq> Union^n(B)" in nat_induct)
        apply auto[2]
      apply simp 
      apply(rule Union_mono)
      by auto

    fix z w 
    assume assms1: "<y, z> \<in> Memrel(M)^+" "<z, w> \<in> Memrel(M)" "<y, z> \<in> Rrel(InEclose, M)" 

    have yinM : "y \<in> M" using assms1 Rrel_def by auto 
    have winM : "w \<in> M" using assms1 by auto
    have zinw : "z \<in> w" using assms1 by auto

    have "y \<in> eclose(z)" using assms1 Rrel_def InEclose_def by auto 
    then obtain n where nH: "n \<in> nat" "y \<in> Union^n(z)" using eclose_eq_Union by auto 
    then have "y \<in> Union^n(Union(w))" 
      apply(rule_tac A="Union^n(z)" in subsetD)
       apply(rule H, simp)
      using zinw 
      by auto 
    then have "y \<in> Union(Union^n(w))" using iterates_commute nH by auto 
    then have "y \<in> Union^(succ(n))(w)" by auto 
    then have "y \<in> eclose(w)" 
      apply(subst eclose_eq_Union, simp, rule_tac x="succ(n)" in bexI)
      using nH 
      by auto
    then show "<y, w> \<in> Rrel(InEclose, M)" 
      unfolding Rrel_def InEclose_def
      using yinM winM 
      by auto
  qed
  then show "v \<in> Rrel(InEclose,M)" using yxH by auto
qed

lemma preds_InEclose_eq : "x \<in> M \<Longrightarrow> preds(InEclose, x) = eclose(x)"
  unfolding preds_def InEclose_def 
  apply(rule equality_iffI, rule iffI, simp, simp)
  apply(subgoal_tac "eclose(x) \<in> M")
  using transM 
   apply force 
  using eclose_closed 
  by auto

lemma field_Rrel_InEclose : "field(Rrel(InEclose, M)) = M" 
  apply(rule equality_iffI, rule iffI)
   apply(simp add:field_def Rrel_def, force)
  apply(simp add:field_def, rule disjI1)
  apply(rename_tac x, rule_tac b="{x}" in domainI)
  unfolding Rrel_def InEclose_def 
  using singleton_in_M_iff
  apply simp
  apply(subst eclose_eq_Union, simp)
  apply(rule_tac x=0 in bexI)
  by auto

lemma Rrel_InEclose_vimage_eq : "\<And>y. y \<in> M \<Longrightarrow> Rrel(InEclose, M) -`` {y} = eclose(y)"
  apply(rule equality_iffI, rule iffI)
   apply(simp add:Rrel_def InEclose_def, force)
  apply(rename_tac y z, rule_tac b=y in vimageI, simp add:Rrel_def InEclose_def)
   apply(rename_tac y z, subgoal_tac "eclose(y) \<in> M")
  using transM eclose_closed
  by auto

end

definition is_memrel_wftrec_fm where "is_memrel_wftrec_fm(Gfm, i, j, k) \<equiv> is_wftrec_fm(Gfm, InEclose_fm, i, j, k)" 

context M_ctm 
begin 

lemma is_memrel_wftrec_fm_type : 
  fixes Gfm i j k 
  assumes "Gfm \<in> formula" "i \<in> nat" "j \<in> nat" "k \<in> nat" 
  shows "is_memrel_wftrec_fm(Gfm, i, j, k) \<in> formula" 
 
  unfolding is_memrel_wftrec_fm_def InEclose_fm_def 
  apply(rule is_wftrec_fm_type)
  using assms
  by auto

lemma arity_is_memrel_wftrec_fm : 
  fixes Gfm i j k 
  assumes "Gfm \<in> formula" "arity(Gfm) \<le> 3" "i \<in> nat" "j \<in> nat" "k \<in> nat" 
  shows "arity(is_memrel_wftrec_fm(Gfm, i, j, k)) \<le> succ(i) \<union> succ(j) \<union> succ(k)"

  unfolding is_memrel_wftrec_fm_def
  apply(rule le_trans, rule arity_is_wftrec_fm)
  unfolding InEclose_fm_def 
  using assms
         apply auto[3]
      apply simp
      apply(subst arity_is_eclose_fm, simp, simp)
      apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union) 
  using assms le_refl 
  by auto  

lemma sats_is_memrel_wftrec_fm_iff :
  fixes H G Gfm x v i j k env a
  assumes "env \<in> list(M)" "a \<in> M" "x \<in> M" 
          "i < length(env)" "j < length(env)" "k < length(env)" 
          "nth(i, env) = x" "nth(j, env) = a" "nth(k, env) = v"
          "Gfm \<in> formula" 
          "arity(Gfm) \<le> 3" 
          "\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> G(x, g) \<in> M" 
  and HGeq: "\<And>h g x. h \<in> eclose(x) \<rightarrow> M \<Longrightarrow> g \<in> (eclose(x) \<times> {a}) \<rightarrow> M \<Longrightarrow> g \<in> M  
               \<Longrightarrow> x \<in> M \<Longrightarrow> (\<And>y. y \<in> eclose(x) \<Longrightarrow> h`y = g`<y, a>) \<Longrightarrow> H(x, h) = G(<x, a>, g)"  
  and sats_Gfm_iff : " (\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = G(a2, a1) \<longleftrightarrow> sats(M, Gfm, [a0, a1, a2] @ env))"  
          
  shows "sats(M, is_memrel_wftrec_fm(Gfm, i, j, k), env) \<longleftrightarrow> v = wftrec(Memrel(M)^+, x, H)" 
proof - 

  have prelvimageeq : "\<And>y. y \<in> M \<Longrightarrow> prel(Rrel(InEclose, M), {a}) -`` {\<langle>y, a\<rangle>} = eclose(y) \<times> {a}" 
  proof(rule equality_iffI, rule iffI)
    fix y v assume "y \<in> M" "v \<in> prel(Rrel(InEclose, M), {a}) -`` {\<langle>y, a\<rangle>}"
    then have "<v, <y, a>> \<in> prel(Rrel(InEclose, M), {a})" by auto 
    then obtain z where zH : "v = <z, a>" "<z, y> \<in> Rrel(InEclose, M)" unfolding prel_def by auto 
    then have "z \<in> eclose(y)" unfolding Rrel_def InEclose_def by auto 
    then show "v \<in> eclose(y) \<times> {a}" using zH by auto 
  next 
    fix y v assume assms1: "y \<in> M" "v \<in> eclose(y) \<times> {a}" 
    then obtain z where zH : "v = <z, a>" "z \<in> eclose(y)" by auto 
    then have "z \<in> M" 
      apply(subgoal_tac "eclose(y) \<in> M")
      using transM zH assms1 eclose_closed 
      by auto 
    then have H : "<z, y> \<in> Rrel(InEclose, M)" 
      unfolding Rrel_def InEclose_def 
      using assms1 zH 
      by auto 
    have "<z, a> \<in> prel(Rrel(InEclose, M), {a}) -`` {\<langle>y, a\<rangle>}" 
      apply(rule_tac b="<y, a>" in vimageI)
       apply(rule prelI, simp add:H)
      using assms
      by auto 
    then show "v \<in> prel(Rrel(InEclose, M), {a}) -`` {\<langle>y, a\<rangle>}" 
      using zH by auto
  qed

  have "sats(M, is_wftrec_fm(Gfm, InEclose_fm, i, j, k), env) \<longleftrightarrow> v = wftrec(Rrel(InEclose, M), x, H)" 
    apply(rule_tac 
      a = a and 
      G = G
      in sats_is_Rrel_wftrec_fm_iff)
    using assms field_Rrel_InEclose 
                      apply auto[10]
            apply(subst Rrel_InEclose, rule wf_trancl, rule wf_Memrel)
           apply(subst Rrel_InEclose, rule trans_trancl)
          apply(subst preds_InEclose_eq, simp add:assms, rule to_rin, rule eclose_closed, simp add:assms)
    using assms Relation_fm_InEclose
        apply auto[4]
     apply(rule sats_Gfm_iff)
        apply auto[4]
    apply(rename_tac h g x, subgoal_tac "x \<in> M")
    apply(rule HGeq)
        apply(rename_tac h g x, rule_tac b="eclose(x)" and a="Rrel(InEclose, M) -`` {x}" in ssubst)
          apply(rule eq_flip, rule Rrel_InEclose_vimage_eq, simp, simp)
        apply(rename_tac h g x, rule_tac b="eclose(x)" and a="Rrel(InEclose, M) -`` {x}" in ssubst)
          apply(rule eq_flip, rule Rrel_InEclose_vimage_eq, simp, simp, simp, simp)
    apply(rename_tac h g x y, subgoal_tac "y \<in> Rrel(InEclose, M) -`` {x}", force)
    using Rrel_InEclose_vimage_eq
     apply force
    apply(rule_tac a="field(Rrel(InEclose, M))" and b=M in ssubst, rule eq_flip, rule field_Rrel_InEclose, simp)
    done

  then show ?thesis unfolding is_memrel_wftrec_fm_def  using Rrel_InEclose by auto
qed

lemma memrel_wftrec_in_M : 
  fixes H G Gfm x a
  assumes "a \<in> M" "x \<in> M" 
          "Gfm \<in> formula" 
          "arity(Gfm) \<le> 3" 
          "\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> G(x, g) \<in> M" 
  and HGeq: "\<And>h g x. h \<in> eclose(x) \<rightarrow> M \<Longrightarrow> g \<in> (eclose(x) \<times> {a}) \<rightarrow> M \<Longrightarrow> g \<in> M  
               \<Longrightarrow> x \<in> M \<Longrightarrow> (\<And>y. y \<in> eclose(x) \<Longrightarrow> h`y = g`<y, a>) \<Longrightarrow> H(x, h) = G(<x, a>, g)"  
  and sats_Gfm_iff : " (\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = G(a2, a1) \<longleftrightarrow> sats(M, Gfm, [a0, a1, a2] @ env))" 

  shows "wftrec(Memrel(M)^+, x, H) \<in> M"

  apply(rule_tac b="Memrel(M)^+" in ssubst, rule eq_flip, rule Rrel_InEclose)
  apply(rule_tac a=a and Gfm=Gfm in Rrel_wftrec_in_M) 
  using assms
             apply auto[2]
           apply(subst field_Rrel_InEclose, simp add:assms)
          apply(subst Rrel_InEclose, rule wf_trancl, rule wf_Memrel)
         apply(subst Rrel_InEclose, rule trans_trancl)
        apply(rule Relation_fm_InEclose)
       apply(subst preds_InEclose_eq, simp add:assms, rule to_rin, rule eclose_closed, simp add:assms)
  using assms
      apply auto[2]
    apply(rule sats_Gfm_iff)
       apply auto[4]
  using assms 
   apply auto[1]
  apply(rename_tac h g x, subgoal_tac "x \<in> M")
  apply(rule HGeq)
       apply(rename_tac h g x, rule_tac b="eclose(x)" and a="Rrel(InEclose, M) -`` {x}" in ssubst)
      apply(rule eq_flip, rule Rrel_InEclose_vimage_eq, simp, simp)
      apply(rename_tac h g x, rule_tac b="eclose(x)" and a="Rrel(InEclose, M) -`` {x}" in ssubst)
       apply(rule eq_flip, rule Rrel_InEclose_vimage_eq, simp, simp, simp, simp)
   apply(rename_tac h g x y, subgoal_tac "y \<in> Rrel(InEclose, M) -`` {x}", force)
  using Rrel_InEclose_vimage_eq
   apply force
  apply(rule_tac a="field(Rrel(InEclose, M))" and b=M in ssubst, rule eq_flip, rule field_Rrel_InEclose, simp)
  done
  
lemma domain_elem_Memrel_trancl : 
  fixes x y 
  assumes "x \<in> M" "y \<in> domain(x)" 
  shows "<y, x> \<in> Memrel(M)^+" 
proof - 
  obtain z where zH : "<y, z> \<in> x" using assms by auto 
  have singin : "{y} \<in> <y, z>" using Pair_def by auto 
  have yinM : "y \<in> M" using domain_elem_in_M assms by auto
  have yzinM : "<y, z> \<in> M" using zH assms transM by auto 
  then have zinM : "z \<in> M" using pair_in_M_iff by auto 
  show ?thesis
    apply(rule_tac b="<y, z>" in rtrancl_into_trancl1)
     apply(rule_tac b="{y}" in rtrancl_into_rtrancl)
      apply(rule r_into_rtrancl)
    unfolding Memrel_def 
    using yinM singleton_in_M_iff 
      apply force
    using yinM singleton_in_M_iff pair_in_M_iff zH singin zinM 
     apply force
    apply simp
    using zH yzinM assms 
    by auto
qed

lemma domain_elem_in_eclose : 
  fixes x y 
  assumes "y \<in> domain(x)" 
  shows "y \<in> eclose(x)"
proof - 
  obtain z where zH : "<y, z> \<in> x" using assms by auto 
  show ?thesis 
    apply(subst eclose_eq_Union, simp, rule_tac x=2 in bexI, simp)
     apply(rule_tac x="<y, z>" in bexI)
      apply(rule_tac x="{y}" in bexI, simp)
      apply(subst Pair_def, simp)
    using zH 
    by auto
qed

end
end