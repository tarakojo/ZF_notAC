theory P_Names_M
  imports 
    "Forcing/Forcing_Main"
    RecFun_M
    P_Names
begin 

context forcing_data
begin 

schematic_goal edrel_fm_auto:
  assumes
    "nth(0,env) = p"    
    "env \<in> list(M)" 
 shows 
    "(\<exists>x \<in> M. \<exists>y \<in> M. \<exists>d \<in> M. pair(##M, y, x, p) \<and> is_domain(##M, x, d) \<and> y \<in> d) \<longleftrightarrow> sats(M,?fm(0),env)" 
  by (insert assms ; (rule sep_rules | simp)+) 

definition edrel_fm where "edrel_fm \<equiv> Exists(Exists(Exists(And(pair_fm(1, 2, 3), And(domain_fm(2, 0), Member(1, 0)))))) " 

lemma edrel_closed : "Transset(A) \<Longrightarrow> A \<in> M \<Longrightarrow> edrel(A) \<in> M" 
proof - 
  assume assms : "Transset(A)" "A \<in> M"

  then have H : "\<And>p. p \<in> A \<times> A \<Longrightarrow> sats(M,edrel_fm,[p]@[]) \<longleftrightarrow> p \<in> edrel(A)"
    unfolding edrel_def Rrel_def 
    apply(rule_tac Q="(\<exists>x \<in> M. \<exists>y \<in> M. \<exists>d \<in> M. pair(##M, y, x, p) \<and> is_domain(##M, x, d) \<and> y \<in> d)" in iff_trans) 
    apply(rule iff_flip) unfolding edrel_fm_def apply(rule_tac edrel_fm_auto) apply simp
    apply(rule_tac P="p \<in> M" in mp) apply clarify using transM cartprod_closed apply simp
    using domain_closed pair_in_M_iff transM by auto

  then have "separation(##M, \<lambda>p. sats(M, edrel_fm, [p] @ []))"
    apply(rule_tac separation_ax) unfolding edrel_fm_def apply auto
    by (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)  

  then show "edrel(A) \<in> M" 
    using H apply(rule_tac b="edrel(A)" and a="{ p \<in> A\<times>A. sats(M, edrel_fm, [p]@[]) }" in ssubst) 
    apply simp unfolding edrel_def Rrel_def apply simp 
    apply(rule_tac separation_notation) using assms cartprod_closed by auto 
qed

definition His_P_name_M where 
  "His_P_name_M(x', g) \<equiv> (if \<exists>x \<in> M. \<exists>P \<in> M. x' = <x, P> \<and> relation(x) \<and> range(x) \<subseteq> P \<and> (\<forall>y \<in> domain(x). g`<y, P> = 1) then 1 else 0)" 

definition His_P_name_M_cond where 
  "His_P_name_M_cond(x', g) \<equiv> 
      (\<exists>x \<in> M. \<exists>P \<in> M. \<exists>xrange \<in> M. \<exists>xdomain \<in> M.
      pair(##M, x, P, x') \<and> is_relation(##M, x) \<and> is_range(##M, x, xrange) \<and> is_domain(##M, x, xdomain) 
      \<and> subset(##M, xrange, P) \<and> (\<forall>y \<in> M. y \<in> xdomain \<longrightarrow> (\<exists>y_P \<in> M. \<exists>gy \<in> M. pair(##M, y, P, y_P) \<and> fun_apply(##M, g, y_P, gy) \<and> (\<forall>z \<in> M. z \<in> gy \<longleftrightarrow> empty(##M, z)))))"

lemma is_1 : "A \<in> M \<Longrightarrow> \<forall>x \<in> M. x \<in> A \<longleftrightarrow> x = 0 \<Longrightarrow> A = 1" 
  apply(rule equality_iffI; rule iffI) using transM by auto

lemma His_P_name_M_cond_iff : 
  "\<And>x' g. x' \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> 
    (\<exists>x \<in> M. \<exists>P \<in> M. x' = <x, P> \<and> relation(x) \<and> range(x) \<subseteq> P \<and> (\<forall>y \<in> domain(x). g`<y, P> = 1)) \<longleftrightarrow> His_P_name_M_cond(x', g)" 
  unfolding His_P_name_M_cond_def using domain_closed range_closed pair_in_M_iff apply auto  
  apply(rule_tac is_1) apply(rule_tac to_rin) apply(rule_tac apply_closed) apply simp apply simp 
  apply(rule_tac x=x in domain_elem_in_M) apply simp apply simp apply(rule_tac P="y \<in> M \<and> y \<in> domain(x)" in mp) 
  apply simp using domain_elem_in_M by auto 

schematic_goal His_P_name_M_fm_auto:
  assumes
    "nth(0,env) = v" 
    "nth(1,env) = g" 
    "nth(2,env) = x'"   
    "env \<in> list(M)" 
 shows 
    "(\<forall>e \<in> M. e \<in> v \<longleftrightarrow> (empty(##M, e) \<and> His_P_name_M_cond(x', g))) \<longleftrightarrow> sats(M,?fm(0,1,2),env)" 
  unfolding His_P_name_M_cond_def subset_def 
  by (insert assms ; (rule sep_rules | simp)+) 

definition His_P_name_M_fm where "His_P_name_M_fm \<equiv> 
       Forall
             (Iff(Member(0, 1),
                  And(empty_fm(0),
                      Exists
                       (Exists
                         (Exists
                           (Exists
                             (And(pair_fm(3, 2, 7),
                                  And(relation_fm(3),
                                      And(range_fm(3, 1),
                                          And(domain_fm(3, 0),
                                              And(Forall(Implies(Member(0, 2), Member(0, 3))),
                                                  Forall
                                                   (Implies
                                                     (Member(0, 1),
                                                      Exists
                                                       (Exists
                                                         (And(pair_fm(2, 5, 1),
                                                              And(fun_apply_fm(9, 1, 0),
                                                                  Forall(Iff(Member(0, 1), empty_fm(0)))))))))))))))))))))   "

lemma His_P_name_M_fm_iff_sats : 
  "v \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> x' \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> sats(M, His_P_name_M_fm, [v, g, x'] @ env) \<longleftrightarrow> v = His_P_name_M(x', g)" 

  apply(rule_tac Q="\<forall>e \<in> M. e \<in> v \<longleftrightarrow> (empty(##M, e) \<and> His_P_name_M_cond(x', g))" in iff_trans)
  apply(rule_tac iff_flip) unfolding His_P_name_M_fm_def apply(rule_tac v=v in His_P_name_M_fm_auto) apply simp_all   
  unfolding His_P_name_M_def apply(rule_tac iffD2) 
  apply(rule_tac P="\<lambda>X. ((\<forall>e\<in>M. e \<in> v \<longleftrightarrow> e = 0 \<and> His_P_name_M_cond(x', g))) \<longleftrightarrow> v = X" in split_if) apply(rule conjI) 
  apply(rule impI) apply(rule_tac P="His_P_name_M_cond(x', g)" in mp) apply (rule impI; simp) 
  apply(rule iffI) apply(rule_tac is_1) apply simp apply simp apply(clarify) apply blast 
  using His_P_name_M_cond_iff apply blast apply clarify
  apply(rule_tac P="\<not>His_P_name_M_cond(x', g)" in mp) using empty_abs empty_def apply simp 
  using His_P_name_M_cond_iff apply blast done 

definition is_P_name_M where "is_P_name_M(a) \<equiv> { <x_P, wftrec(prel(edrel(MVset(a))^+, {P}), x_P, His_P_name_M)>. x_P \<in> MVset(a) \<times> {P} }" 

lemma is_P_name_M_in_M : "a \<in> M \<Longrightarrow> Ord(a) \<Longrightarrow> is_P_name_M(a) \<in> M" 
  unfolding is_P_name_M_def
  apply(rule_tac p="His_P_name_M_fm" in recfun_in_M) 
  apply(rule_tac prel_closed; rule_tac to_rin) apply(rule_tac trancl_closed) apply simp apply(rule_tac edrel_closed) 
  unfolding Transset_def using MVset_trans apply blast using MVset_in_M apply simp using singleton_in_M_iff P_in_M apply simp
  apply(rule_tac wf_prel; rule_tac wf_trancl; rule_tac wf_edrel; rule_tac prel_trans) 
  apply(rule_tac prel_trans; rule_tac trans_trancl) using MVset_in_M singleton_in_M_iff P_in_M cartprod_closed apply simp  
  apply(simp add:His_P_name_M_fm_def) apply(simp add:His_P_name_M_fm_def) apply(simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)  
  apply(rule iff_flip) apply(rule_tac His_P_name_M_fm_iff_sats) apply simp_all 
  unfolding His_P_name_M_def using zero_in_M apply simp done 


lemma is_P_name_M : "\<And>a. Ord(a) \<Longrightarrow> a \<in> M \<Longrightarrow> x \<in> MVset(a) \<Longrightarrow> is_P_name_M(a)`<x, P> = 1 \<longleftrightarrow> x \<in> P_names" 
  apply(rule_tac P="x \<in> MVset(a) \<longrightarrow> is_P_name_M(a)`<x, P> = 1 \<longleftrightarrow> x \<in> P_names" in mp) apply simp 
  apply(rule_tac Q="\<lambda>x. x \<in> MVset(a) \<longrightarrow> is_P_name_M(a)`<x, P> = 1 \<longleftrightarrow> x \<in> P_names" in ed_induction) apply clarify
proof - 
  fix a x assume assms : "Ord(a)" "a \<in> M" "x \<in> MVset(a)" "(\<And>y. ed(y, x) \<Longrightarrow> y \<in> MVset(a) \<longrightarrow> is_P_name_M(a) ` \<langle>y, P\<rangle> = 1 \<longleftrightarrow> y \<in> P_names) " 

  define R where "R \<equiv> prel(edrel(MVset(a))^+, {P})"
  have wfR : "wf(R)" 
    unfolding R_def apply(rule_tac wf_prel; rule_tac wf_trancl; rule_tac wf_edrel) done 
  have transR : "trans(R)" 
    unfolding R_def apply(rule_tac prel_trans) using trans_trancl by auto

  have eq : "\<And>y. y \<in> domain(x) \<Longrightarrow> the_recfun(R, \<langle>x, P\<rangle>, His_P_name_M) ` \<langle>y, P\<rangle> = is_P_name_M(a) ` \<langle>y, P\<rangle> "
  proof - 
    fix y assume yindomx: "y \<in> domain(x)"

    have rel : "<<y, P> , <x, P>> \<in> R" 
      unfolding R_def apply(rule_tac prelI) apply(rule_tac r_into_trancl) 
      unfolding edrel_def Rrel_def using assms yindomx apply auto 
      apply(rule_tac MVset_domain) by auto

    have restrict_eq : "restrict(the_recfun(R, <x, P>, His_P_name_M), R-``{<y, P>}) = the_recfun(R, <y, P>, His_P_name_M)" 
      apply(rule_tac the_recfun_cut) using wfR transR rel by auto 

    have "the_recfun(R, <x, P>, His_P_name_M)`<y, P> = His_P_name_M(<y, P>, restrict(the_recfun(R, <x, P>, His_P_name_M), R-``{<y, P>}))"
      apply(rule_tac a="<x, P>" in apply_recfun) apply(rule_tac unfold_the_recfun) using wfR transR rel by auto

    also have "... = wftrec(R, <y, P>, His_P_name_M)" 
      unfolding wftrec_def using restrict_eq by auto 

    also have "... = is_P_name_M(a)`<y, P>" 
      apply(rule eq_flip) apply(rule_tac function_apply_equality) unfolding is_P_name_M_def R_def function_def using yindomx apply auto 
      using MVset_domain assms by auto

    finally show "the_recfun(R, \<langle>x, P\<rangle>, His_P_name_M) ` \<langle>y, P\<rangle> = is_P_name_M(a) ` \<langle>y, P\<rangle> " by auto
  qed

  have eq' : 
    "(if \<exists>xx \<in> M. \<exists>PP \<in> M. <x, P> = <xx, PP> \<and> relation(xx) \<and> range(xx) \<subseteq> PP \<and> (\<forall>y \<in> domain(xx). the_recfun(R, <x, P>, His_P_name_M)`<y, PP> = 1) then 1 else 0) = is_P_name_M(a) ` \<langle>x, P\<rangle>"
    apply(rule_tac eq_flip) apply(rule_tac function_apply_equality) unfolding is_P_name_M_def wftrec_def R_def function_def His_P_name_M_def using assms by auto 
  
  show "is_P_name_M(a) ` \<langle>x, P\<rangle> = 1 \<longleftrightarrow> x \<in> P_names"
    apply(rule iffI) 
  proof - 
    assume assm1 : "is_P_name_M(a) ` \<langle>x, P\<rangle> = 1" 

    then have "(if \<exists>xx \<in> M. \<exists>PP \<in> M. <x, P> = <xx, PP> \<and> relation(xx) \<and> range(xx) \<subseteq> PP \<and> (\<forall>y \<in> domain(xx). the_recfun(R, <x, P>, His_P_name_M)`<y, PP> = 1) then 1 else 0) = 1" 
      using eq' by auto
    then have "\<exists>xx \<in> M. \<exists>PP \<in> M. <x, P> = <xx, PP> \<and> relation(xx) \<and> range(xx) \<subseteq> PP \<and> (\<forall>y \<in> domain(xx). the_recfun(R, <x, P>, His_P_name_M)`<y, PP> = 1)" 
      apply(rule_tac ifT_eq) by auto 
    then have H: "relation(x) \<and> range(x) \<subseteq> P \<and> (\<forall>y \<in> domain(x). the_recfun(R, <x, P>, His_P_name_M)`<y, P> = 1)" by auto

    then have "\<And>y. y \<in> domain(x) \<Longrightarrow> y \<in> P_names"
    proof - 
      fix y assume assm2: "y \<in> domain(x)"
 
      have "is_P_name_M(a) ` \<langle>y, P\<rangle> = 1" using H assm2 eq by auto 
      then show "y \<in> P_names" using assms assm2 MVset_domain unfolding ed_def by auto 
    qed

    then obtain b where bH: "Limit(b)" "(\<forall>y \<in> domain(x). y \<in> P_set(b))" 
      using set_of_P_names_in_P_set by blast 

    then have "x \<in> Pow(P_set(b) \<times> P)" 
    proof (auto) 
      fix v assume vinx: "v \<in> x" then obtain y p where ypH: "v = <y, p>" using H unfolding relation_def by blast
      then show "v \<in> P_set(b) \<times> P" using bH vinx H by auto 
    qed

    then show "x \<in> P_names" 
      apply(rule_tac a="succ(b)" in P_namesI) using bH Limit_is_Ord apply simp 
      apply(simp add:P_set_succ) using assms unfolding MVset_def by auto 

  next
    assume xpname : "x \<in> P_names" 

    have "(if \<exists>xx \<in> M. \<exists>PP \<in> M. <x, P> = <xx, PP> \<and> relation(xx) \<and> range(xx) \<subseteq> PP \<and> (\<forall>y \<in> domain(xx). the_recfun(R, <x, P>, His_P_name_M)`<y, PP> = 1) then 1 else 0) = 1" 
      apply(rule_tac if_P) 
      apply simp using xpname P_names_in_M P_in_M relation_P_name P_name_range apply auto 
    proof -
      fix y p assume ypH : "<y, p> \<in> x" 
      then have "is_P_name_M(a)`<y, P> = 1" 
        using assms MVset_domain P_name_domain_P_name xpname unfolding ed_def by blast
      then show "the_recfun(R, \<langle>x, P\<rangle>, His_P_name_M) ` \<langle>y, P\<rangle> = 1"
        using eq ypH by force 
    qed
    then show "is_P_name_M(a) ` \<langle>x, P\<rangle> = 1" using eq' by auto 
  qed
qed


schematic_goal fun_apply_1_fm_auto:
  assumes
    "nth(0,env) = x" 
    "nth(1,env) = P" 
    "nth(2,env) = F" 
    "env \<in> list(M)" 
 shows 
    "((\<exists>x_P \<in> M. \<exists>v \<in> M. pair(##M, x, P, x_P) \<and> fun_apply(##M, F, x_P, v) \<and> (\<forall>y \<in> M. y \<in> v \<longleftrightarrow> empty(##M, y)))) \<longleftrightarrow> sats(M,?fm(0,1),env)" 
  unfolding empty_def
  by (insert assms ; (rule sep_rules | simp)+) 

definition fun_apply_1_fm where "fun_apply_1_fm \<equiv> Exists(Exists(And(pair_fm(2, 3, 1), And(fun_apply_fm(4, 1, 0), Forall(Iff(Member(0, 1), Forall(Neg(Member(0, 1)))))))))"

lemma fun_apply_1_fm_sats_iff : 
  "x \<in> M \<Longrightarrow> P \<in> M \<Longrightarrow> F \<in> M \<Longrightarrow> F`<x, P> = 1 \<longleftrightarrow> sats(M, fun_apply_1_fm, [x]@[P, F])" 
  apply(rule iff_flip)
  apply(rule_tac Q="(\<exists>x_P \<in> M. \<exists>v \<in> M. pair(##M, x, P, x_P) \<and> fun_apply(##M, F, x_P, v) \<and> (\<forall>y \<in> M. y \<in> v \<longleftrightarrow> empty(##M, y)))" in iff_trans) 
  apply(rule iff_flip) unfolding fun_apply_1_fm_def apply(rule_tac fun_apply_1_fm_auto) using pair_in_M_iff is_1 by auto 

lemma MVset_int_P_names_in_M : "Ord(a) \<Longrightarrow> a \<in> M \<Longrightarrow> MVset(a) \<inter> P_names \<in> M" 
proof - 
  assume assms : "Ord(a)" "a \<in> M" 
  have "separation(##M, \<lambda>x. sats(M, fun_apply_1_fm, [x]@[P, is_P_name_M(a)]))" 
    apply(rule_tac separation_ax) unfolding fun_apply_1_fm_def using P_in_M is_P_name_M_in_M assms apply auto
    by(simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)  
  then have H: "{ x \<in> MVset(a). sats(M,fun_apply_1_fm, [x]@[P, is_P_name_M(a)]) } \<in> M" 
    apply(rule_tac separation_notation) using assms MVset_in_M by auto 
  then have "{ x \<in> MVset(a). sats(M,fun_apply_1_fm, [x]@[P, is_P_name_M(a)]) } = { x \<in> MVset(a). is_P_name_M(a)`<x, P> = 1 }" 
    apply(rule_tac iff_eq) apply(rule iff_flip) apply(rule_tac fun_apply_1_fm_sats_iff) 
    unfolding MVset_def using P_in_M is_P_name_M_in_M assms by auto 
  also have "... = { x \<in> MVset(a). x \<in> P_names }" 
    apply(rule_tac iff_eq) using is_P_name_M assms by auto 
  also have "... = MVset(a) \<inter> P_names" by auto 
  finally show "MVset(a) \<inter> P_names \<in> M" using H by auto
qed


definition HP_rank_M where
  "HP_rank_M(x, g) \<equiv> 
    if x = 0 then 0 
    else if (\<exists>y \<in> domain(x). g`y = (\<Union>(g``domain(x)))) then succ(\<Union>(g``domain(x))) 
    else (\<Union>(g``domain(x)))"

definition HP_rank_M_cond where
  "HP_rank_M_cond(v, x, g) \<equiv> 
    \<not>empty(##M, x) \<and> 
    (\<exists>domx \<in> M. \<exists>gi \<in> M. \<exists>gu \<in> M. is_domain(##M, x, domx) \<and> image(##M, g, domx, gi) \<and> big_union(##M, gi, gu) \<and>
      (v \<in> gu \<or> (v = gu \<and> (\<exists>y \<in> M. \<exists>gy \<in> M. y \<in> domx \<and> fun_apply(##M, g, y, gy) \<and> gy = gu))))" 

lemma HP_rank_M_cond_iff : 
  "v \<in> M \<Longrightarrow> x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow>  HP_rank_M_cond(v, x, g) \<longleftrightarrow> v \<in> HP_rank_M(x, g)" 
  apply(rule_tac Q="(x \<noteq> 0 \<and> (v \<in> (\<Union>(g``domain(x))) \<or> (v = (\<Union>(g``domain(x))) \<and> (\<exists>y \<in> domain(x). g`y = (\<Union>(g``domain(x)))))))" in iff_trans)
   apply(simp add: HP_rank_M_cond_def)
  apply(cases "(\<exists>z\<in>g `` domain(x). v \<in> z)") 
    apply(rule iffI, rule conjI, simp, simp, rule conjI, simp)
  using domain_closed 
    apply simp
   apply(rule conjI)
  using image_closed domain_closed 
     apply simp
  using image_closed domain_closed Union_closed 
    apply force
   apply(rule iffI, rule conjI, simp, rule disjI2, simp)
    apply force
  apply(rule conjI, simp, rule conjI)
  using domain_closed 
    apply simp
   apply(rule conjI)
  using image_closed domain_closed 
    apply simp
   apply(rule conjI)
  using image_closed domain_closed Union_closed 
    apply force
   apply(rule disjI2)
   apply(subgoal_tac "\<forall>y \<in> domain(x). y \<in> M \<and> g`y \<in> M")
    apply blast
   apply(rule ballI, rule conjI)
    apply(rule to_rin, rule transM, simp, rule domain_closed, simp)
   apply(rule to_rin, rule apply_closed, simp, simp, rule to_rin, rule transM, simp, rule domain_closed, simp)
  unfolding HP_rank_M_def
  by auto

lemma HP_rank_M_in_M : 
  fixes x g 
  assumes "x \<in> M" "g \<in> M" 
  shows "HP_rank_M(x, g) \<in> M" 
proof -
  have "HP_rank_M(x, g) = 0 \<or> HP_rank_M(x, g) = succ(\<Union>(g``domain(x))) \<or> HP_rank_M(x, g) = (\<Union>(g``domain(x)))"
    unfolding HP_rank_M_def
    apply(cases "x=0", simp)
    apply(rule disjI2)
    apply(cases "\<exists>y\<in>domain(x). g ` y = (\<Union>(g `` domain(x)))")
     apply(rule disjI1, subst if_not_P, simp, subst if_P, simp, simp)
    apply(rule disjI2, subst if_not_P, simp, subst if_not_P, auto)
    done

  then show ?thesis 
    apply(rule disjE, simp add:zero_in_M)
    using assms succ_in_MI image_closed domain_closed Union_closed
    by auto
qed

lemma HP_rank_M_eq : 
  fixes x g 
  assumes "x \<in> M" "g \<in> M"  
  shows "HP_rank_M(x, g) = { v \<in> M. HP_rank_M_cond(v, x, g) }"  

  using HP_rank_M_cond_iff assms HP_rank_M_in_M transM 
  by auto


schematic_goal HP_rank_M_fm_auto:
  assumes
    "s \<in> M" "g \<in> M" "x \<in> M"
    "nth(0,env) = s" 
    "nth(1,env) = g" 
    "nth(2,env) = x" 
    "env \<in> list(M)" 
 shows 
    "s = HP_rank_M(x, g) \<longleftrightarrow> sats(M,?fm(0, 1, 2),env)"
  apply(rule_tac Q="\<forall>v \<in> M. v \<in> s \<longleftrightarrow> HP_rank_M_cond(v, x, g)" in iff_trans)
   apply(subst HP_rank_M_eq, simp add:assms, simp add:assms)
   apply(rule iffI, force)
   apply(rule equality_iffI)
  using transM assms 
   apply force
  unfolding HP_rank_M_cond_def  
  by (insert assms ; (rule sep_rules | simp)+) 

definition HP_rank_M_fm where "HP_rank_M_fm \<equiv> Forall(Iff(Member(0, 1), And(Neg(empty_fm(3)), Exists(Exists(Exists(And(domain_fm(6, 2), And(image_fm(5, 2, 1), And(big_union_fm(1, 0), Or(Member(3, 0), And(Equal(3, 0), Exists(Exists(And(Member(1, 4), And(fun_apply_fm(7, 1, 0), Equal(0, 2))))))))))))))))  " 

definition P_rank_M where "P_rank_M(a) \<equiv> { <x, wftrec(edrel(MVset(a))^+, x, HP_rank_M)> . x \<in> MVset(a) \<inter> P_names }" 

lemma P_rank_M_in_M : "Ord(a) \<Longrightarrow> a \<in> M \<Longrightarrow> P_rank_M(a) \<in> M" 
  unfolding P_rank_M_def 
  apply(rule_tac p="HP_rank_M_fm" in recfun_in_M)
         apply(rule to_rin, rule trancl_closed, simp, rule edrel_closed)
  unfolding Transset_def 
  using MVset_trans
          apply force
         apply(simp add:MVset_in_M)
        apply(rule wf_trancl, rule wf_edrel, rule trans_trancl)
      apply(rule MVset_int_P_names_in_M, simp, simp)
  unfolding HP_rank_M_fm_def
     apply(simp)
    apply(simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)  
  apply(rule HP_rank_M_fm_auto)
  using HP_rank_M_in_M 
  by auto

lemma P_rank_M_domain : "a \<in> M \<Longrightarrow> Ord(a) \<Longrightarrow> domain(P_rank_M(a)) = MVset(a) \<inter> P_names" 
  unfolding P_rank_M_def by auto

lemma P_rank_M : 
  fixes a x
  assumes "Ord(a)" "a \<in> M" "x \<in> MVset(a) \<inter> P_names"  
  shows "P_rank_M(a)`x = HP_rank_M(x, P_rank_M(a))" 
proof - 
  define F where "F \<equiv> the_recfun(edrel(MVset(a))^+, x, HP_rank_M)"

  have relhelper : "wf(edrel(MVset(a))^+) \<and> trans(edrel(MVset(a))^+)"
    apply(rule conjI, rule wf_trancl, rule wf_edrel, rule trans_trancl)
    done

  have yhelper: "\<And>y. y \<in> domain(x) \<Longrightarrow> 
     \<langle>y, x\<rangle> \<in> edrel(MVset(a))^+ \<and> y \<in> MVset(a) \<inter> P_names"
    apply(rule conjI, rule r_into_trancl, simp add:edrel_def Rrel_def ed_def)
    using assms MVset_domain ed_def P_name_domain_P_name 
    by auto

  have Fy : "\<And>y. y \<in> domain(x) \<Longrightarrow> F ` y = P_rank_M(a)`y" 
  proof -
    fix y assume yin : "y \<in> domain(x)" 
    have "F`y = HP_rank_M(y, restrict(F, edrel(MVset(a))^+ -``{y}))" 
      apply(rule apply_recfun)
       apply(simp add:F_def, rule unfold_the_recfun)
      using yin yhelper relhelper
      by auto
    also have "... = HP_rank_M(y, the_recfun(edrel(MVset(a))^+, y, HP_rank_M))" 
      unfolding F_def 
      apply(subst the_recfun_cut)
      using yin yhelper relhelper
      by auto
    also have "... = wftrec(edrel(MVset(a))^+, y, HP_rank_M)" unfolding wftrec_def by auto
    also have "... = P_rank_M(a)`y" 
      apply(rule eq_flip, rule function_apply_equality)
      unfolding P_rank_M_def function_def 
      using yin yhelper 
      by auto
    finally show "F`y = P_rank_M(a)`y" 
      by simp 
  qed

  have "is_recfun(edrel(MVset(a))^+, x, HP_rank_M, F)" 
    unfolding F_def 
    apply(rule unfold_the_recfun)
    using relhelper 
    by auto
  then have eq : "F = (\<lambda>x \<in> edrel(MVset(a))^+ -``{x}. HP_rank_M(x, restrict(F, edrel(MVset(a))^+ -`` {x})))" unfolding is_recfun_def by simp
    
  have funcF : "function(F)"
    apply(subst eq)
    apply(rule function_lam)
    done

  have imdom : "F``domain(x) = P_rank_M(a)``domain(x)" 
    apply(rule equality_iffI)
    apply(rename_tac v, rule_tac Q="\<exists>y \<in> domain(x). <y, v> \<in> F" in iff_trans, blast)
    apply(rename_tac v, rule_tac Q="\<exists>y \<in> domain(x). F`y = v" in iff_trans)
     apply(rule ex_iff, rule iffI) 
    using funcF function_apply_equality 
      apply blast
     apply(rename_tac v y, rule_tac b=v and a="F`y" in ssubst, simp)
     apply(rule function_apply_Pair, simp add:funcF)
     apply(subst eq, subst domain_lam, rule_tac b=x in vimageI, rule r_into_trancl)
      apply(simp add:edrel_def Rrel_def)
    using assms edrel_def ed_def yhelper 
      apply simp
     apply simp 
    apply(rename_tac v, rule_tac Q="\<exists>y \<in> domain(x). P_rank_M(a)`y = v" in iff_trans)
     apply(rule ex_iff) 
    using Fy 
     apply force
    apply(rename_tac v, rule_tac Q="\<exists>y \<in> domain(x). <y, v> \<in>  P_rank_M(a)" in iff_trans)
     apply(rule ex_iff, rule iffI)
      apply(rename_tac v y, rule_tac b=v and a="P_rank_M(a)`y" in ssubst)
       apply simp
      apply(rule function_apply_Pair)
       apply(simp add:P_rank_M_def function_def)
    using P_rank_M_def yhelper 
      apply force
    apply(rule function_apply_equality, simp, simp add:P_rank_M_def function_def)
    by auto
   
  have "P_rank_M(a) ` x = HP_rank_M(x, F)" 
    apply(rule function_apply_equality)
    unfolding F_def P_rank_M_def function_def wftrec_def 
    using assms 
    by auto 
  also have "... = HP_rank_M(x, P_rank_M(a))" 
    unfolding HP_rank_M_def
    using Fy imdom by auto

  finally show "P_rank_M(a)`x = HP_rank_M(x, P_rank_M(a))" by simp
qed


lemma P_rank_eq : 
  "Ord(a) \<Longrightarrow> a \<in> M \<Longrightarrow> x \<in> MVset(a) \<inter> P_names \<Longrightarrow> P_rank(x) = P_rank_M(a)`x" 
proof - 
  have main : "\<And>x. x \<in> MVset(a) \<inter> P_names \<longrightarrow> P_rank(x) = P_rank_M(a)`x" 
  proof (rule_tac Q="\<lambda>x. x \<in> MVset(a) \<inter> P_names \<longrightarrow> P_rank(x) = P_rank_M(a)`x" in ed_induction, rule impI)
    fix x assume assms : "(\<And>y. ed(y, x) \<Longrightarrow> y \<in> MVset(a) \<inter> P_names \<longrightarrow> P_rank(y) = P_rank_M(a) ` y)" "x \<in> MVset(a) \<inter> P_names" "Ord(a)" "a \<in> M"

    have yH : "\<And>y. y \<in> domain(x) \<Longrightarrow> y \<in> MVset(a) \<inter> P_names" 
      apply (simp, rule conjI)
      using assms MVset_domain 
       apply force
      using assms P_name_domain_P_name 
      by auto
    then have ih : "\<And>y. y \<in> domain(x) \<Longrightarrow> P_rank(y) = P_rank_M(a) ` y"
      using assms by auto      
    
    have eq : "P_rank_M(a) ` x =
        (if x = 0 then 0 
         else if (\<exists>y \<in> domain(x) . P_rank_M(a)`y = (\<Union>(P_rank_M(a)``domain(x)))) then succ(\<Union>(P_rank_M(a)``domain(x)))
         else (\<Union>(P_rank_M(a)``domain(x))))"
      using P_rank_M assms HP_rank_M_def by auto

    have eq2 : "(\<Union>(P_rank_M(a)``domain(x))) = (\<Union>y \<in> domain(x). P_rank(y))" 
    proof - 
      have "P_rank_M(a)``domain(x) = { P_rank_M(a)`y . y \<in> domain(x) }"
        apply(rule image_function)
        apply(simp add: P_rank_M_def function_def)
        apply(subst P_rank_M_domain)
        using assms 
          apply (simp, simp)
        apply(rule subsetI, simp, rule conjI)
        using assms MVset_domain 
         apply force
        using assms P_name_domain_P_name 
        by auto

      also have "... = { P_rank(y). y \<in> domain(x) }" 
        using ih by auto

      finally show "(\<Union>(P_rank_M(a)``domain(x))) = (\<Union>y \<in> domain(x). P_rank(y))" by auto
    qed

    have "x = 0 \<Longrightarrow> P_rank_M(a)`x = P_rank(x)" 
      apply(subst eq, subst if_P)
      using P_rank_zero
      by auto

    have "(\<exists>y \<in> domain(x) . P_rank_M(a)`y = (\<Union>(P_rank_M(a)``domain(x)))) \<Longrightarrow> P_rank_M(a)`x = P_rank(x)" 
    proof - 
      assume assm1 : "\<exists>y \<in> domain(x) . P_rank_M(a)`y = P_rank_M(a)``domain(x)" 
      then obtain y where "y \<in> domain(x)" "P_rank_M(a)`y = P_rank_M(a)``domain(x)" by auto



end 
end













