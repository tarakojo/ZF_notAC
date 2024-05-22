theory RecFun_M 
  imports 
    ZF 
    Utilities_M
begin 

context M_ctm 
begin 

definition strongrep_for_recfun_fm where 
  "strongrep_for_recfun_fm(p, x, z, r) \<equiv> 
    Exists(Exists(And(pair_fm(x#+2, 0, z#+2), And(is_recfun_fm(p, r#+2, x#+2, 1), p))))" 

lemma strongrep_for_recfun_fm_sats_iff :
  "\<And>x z r p H. x \<in> M \<Longrightarrow> z \<in> M \<Longrightarrow> r \<in> M \<Longrightarrow> p \<in> formula \<Longrightarrow>
  (\<And>a0 a1 a2 a3 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> a3 \<in> M \<Longrightarrow> env \<in> list(M) 
    \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2, a3] @ env)) \<Longrightarrow>
  (\<forall>x[##M]. \<forall>g[##M]. function(g) \<longrightarrow> (##M)(H(x, g))) \<Longrightarrow>
  (\<exists>y[##M]. \<exists>g[##M]. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g))
   \<longleftrightarrow> sats(M, strongrep_for_recfun_fm(p, 0, 1, 2), [x, z, r])" 
proof - 
  fix x z r p H
  assume inM : "x \<in> M" "z \<in> M" "r \<in> M" 
  and pformula : "p \<in> formula"
  and ph : 
    "(\<And>a0 a1 a2 a3 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> a3 \<in> M \<Longrightarrow> env \<in> list(M) 
      \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2, a3] @ env))"
  and Hh : "(\<forall>x[##M]. \<forall>g[##M]. function(g) \<longrightarrow> (##M)(H(x, g)))" 

  have t1:
    "(\<exists>y[##M]. \<exists>g[##M]. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g))
      \<longleftrightarrow> (\<exists>y \<in> M. \<exists>g \<in> M. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g))" by simp 
  have t2 : 
    "... \<longleftrightarrow> (\<exists>g \<in> M. \<exists>y \<in> M. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g))" by auto 
  have t3 :   
    "... \<longleftrightarrow>(\<exists>g \<in> M. \<exists>y \<in> M. pair(##M, x, y, z) \<and> M_is_recfun(##M, \<lambda>a b c. c = H(a, b), r, x, g) \<and> y = H(x, g))"
    apply (auto)
    apply (rule_tac x="g" in bexI; auto)
    apply (rule_tac Q="is_recfun(r, x, H, g)" in iffD2)
    apply (rule_tac is_recfun_abs)
    using Hh inM apply simp_all
    unfolding relation2_def apply simp
    apply (rule_tac x="g" in bexI; auto)
    apply (rule_tac P="M_is_recfun(##M, \<lambda>a b c. c = H(a, b), r, x, g)" in iffD1)
    apply (rule_tac is_recfun_abs)
    using Hh inM apply simp_all
    unfolding relation2_def apply simp done 
  also have t4: 
    "... \<longleftrightarrow> sats(M, strongrep_for_recfun_fm(p, 0, 1, 2), [x, z, r])" 
    unfolding strongrep_for_recfun_fm_def 
    apply (rule_tac bex_iff_sats)
    apply (rule_tac bex_iff_sats)
    apply (rule_tac conj_iff_sats)
    apply (rule_tac pair_iff_sats)
    using inM apply (simp_all)
    apply (rule_tac conj_cong)
    apply (rule_tac is_recfun_iff_sats)
    using inM apply (simp_all)
    apply (rule_tac 
        Q="sats(M, p, [a0, a1, a2, a3] @ [y, g, x, z, r])" in iff_trans)
    apply (rule_tac ph)
    using inM apply (simp_all)
    apply (rule_tac Q="M, [y, g, x, z] @ [r] \<Turnstile> p" in iff_trans)
    apply (rule_tac ph) 
    using inM by auto
  show "(\<exists>y[##M]. \<exists>g[##M]. pair(##M, x, y, z) \<and>is_recfun(r, x, H, g) \<and> y = H(x, g))
   \<longleftrightarrow> sats(M, strongrep_for_recfun_fm(p, 0, 1, 2), [x, z, r])" 
    using t1 t2 t3 t4 by auto 
qed

lemma strep_iff : 
  "\<And>P Q. strong_replacement(##M, P) \<Longrightarrow> \<forall>x \<in> M. \<forall>z \<in> M. P(x, z) \<longleftrightarrow> Q(x, z) \<Longrightarrow> strong_replacement(##M, Q)"
  unfolding strong_replacement_def univalent_def by auto 

lemma recfun_strong_replacement_lemma :
  fixes r H p x 
  assumes 
    "wf(r)" 
    "trans(r)" 
    "r \<in> M" 
    "p \<in> formula"
    "arity(p) = 3"
    "x \<in> M" 
    "(\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> H(x, g) \<in> M)" 
    " (\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2] @ env))"  
   
  shows "strong_replacement(##M, \<lambda>x z. \<exists>y[##M]. \<exists>g[##M]. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g))"
proof - 

  have ph : 
      "(\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) 
        \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2] @ env))"
    using assms by auto

  have strep_sats : 
    "strong_replacement(##M, \<lambda>x. \<lambda>z. sats(M, strongrep_for_recfun_fm(p, 0, 1, 2), [x, z] @ [r]))"
    apply (rule_tac replacement_ax) 
    unfolding strongrep_for_recfun_fm_def 
    using assms apply auto
    unfolding is_recfun_fm_def pair_fm_def upair_fm_def pre_image_fm_def restriction_fm_def
    by (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union) 

  show "strong_replacement(##M, 
    \<lambda>x z. \<exists>y[##M]. \<exists>g[##M]. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g))"
    apply (rule_tac P=" \<lambda>x. \<lambda>z. sats(M, strongrep_for_recfun_fm(p, 0, 1, 2), [x, z] @ [r])" in strep_iff)
    apply (rule strep_sats)
    apply (rule ballI; rule ballI; rule iff_flip)
    apply (rule_tac Q="M, [x, z, r] \<Turnstile> strongrep_for_recfun_fm(p, 0, 1, 2)" in iff_trans) 
    apply (rule_tac strongrep_for_recfun_fm_sats_iff)
    using assms apply simp_all
    apply (rule_tac Q="a0 = H(a2, a1)" in iff_trans)
    apply simp
    apply (rule_tac Q="M, [a0, a1, a2] @ Cons(a3, env) \<Turnstile> p" in iff_trans)
    apply (rule_tac ph)
    by simp_all
qed

lemma recfun_wfrec_replacement_lemma : 
  fixes r H p x 
  assumes 
    "wf(r)" 
    "trans(r)" 
    "r \<in> M" 
    "p \<in> formula"
    "arity(p) = 3"
    "x \<in> M" 
    "(\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> H(x, g) \<in> M)" 
    " (\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2] @ env))"  
  
  shows "wfrec_replacement(##M, \<lambda>a b c. c = H(a, b), r)" 
  
  using assms
  unfolding wfrec_replacement_def
  apply(rule_tac P=" \<lambda>x z. \<exists>y[##M]. \<exists>g[##M]. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g)" in  strep_iff) 
  apply(rule_tac recfun_strong_replacement_lemma) apply simp_all
  apply clarify unfolding is_wfrec_def 
  apply(rule_tac P="\<forall>f \<in> M. M_is_recfun(##M, \<lambda>a b c. c = H(a, b), r, xa, f) \<longleftrightarrow> is_recfun(r, xa, H, f)" in mp) 
  apply simp apply clarify apply(rule_tac is_recfun_abs) unfolding relation2_def apply simp_all done 

lemma wf_exists_is_recfun' : 
  fixes r H p x 
  assumes 
    "wf(r)" 
    "trans(r)" 
    "r \<in> M" 
    "p \<in> formula"
    "arity(p) = 3"
    "x \<in> M" 
    "(\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> H(x, g) \<in> M)" 
    " (\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2] @ env))"  
  shows "\<exists>f \<in> M. is_recfun(r, x, H, f)"

  using assms 
  apply(rule_tac P="rex(##M, is_recfun(r, x, H))" in mp) apply simp 
  apply (rule_tac wf_exists_is_recfun) apply simp apply simp apply simp
  apply(rule_tac recfun_strong_replacement_lemma) apply simp_all done 

lemma the_recfun_in_M : 
  fixes r H p x 
  assumes 
    "wf(r)" 
    "trans(r)" 
    "r \<in> M" 
    "p \<in> formula"
    "arity(p) = 3"
    "x \<in> M" 
    "(\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> H(x, g) \<in> M)" 
    " (\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2] @ env))"  
  shows "the_recfun(r, x, H) \<in> M" 
proof - 
  have "\<exists>f \<in> M. is_recfun(r, x, H, f)" apply(rule_tac wf_exists_is_recfun') using assms by auto 
  then obtain f where fH : "f \<in> M" "is_recfun(r, x, H, f)" by auto 
  then have "the_recfun(r, x, H) = f" apply(rule_tac the_recfun_eq) using assms by auto 
  then show "the_recfun(r, x, H) \<in> M" using fH by auto 
qed

lemma recfun_in_M : 
  fixes r A p  
  assumes 
    "r \<in> M" 
    "wf(r)" 
    "trans(r)" 
    "A \<in> M"  
    "p \<in> formula" 
    "arity(p) = 3"
    "(\<And>a0 a1 a2 a3 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M  \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2] @ env))" 
    "\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> H(x, g) \<in> M" 
  
shows "{ <x, wftrec(r, x, H)>. x \<in> A } \<in> M" 

proof - 
  have get_rep : 
    "\<And>A P. A \<in> M \<Longrightarrow> strong_replacement(##M, P) \<Longrightarrow> univalent(##M, A, P) \<Longrightarrow> (\<exists>Y \<in> M. \<forall>b \<in> M. b \<in> Y \<longleftrightarrow> (\<exists>x \<in> M. x \<in> A \<and> P(x, b)))"
    using strong_replacement_def by auto 
  
  have "strong_replacement(##M, \<lambda>x z. \<exists>y[##M]. pair(##M,x,y,z) \<and> (\<exists>g[##M]. is_recfun(r,x,H,g) \<and> y = H(x,g)))"
    apply(rule_tac wfrec_replacement') 
    apply(rule_tac recfun_wfrec_replacement_lemma) 
    unfolding relation2_def using assms by simp_all 
  then have strep: "strong_replacement(##M, \<lambda>x z. \<exists>y[##M]. z = <x,y> \<and> (\<exists>g[##M]. is_recfun(r,x,H,g) \<and> y = H(x,g)))"
    apply(rule_tac P="\<lambda>x z. \<exists>y[##M]. pair(##M,x,y,z) \<and> (\<exists>g[##M]. is_recfun(r,x,H,g) \<and> y = H(x,g))" in strep_iff) by auto 
  then have "univalent(##M, A, \<lambda>x z. \<exists>y[##M]. z = <x,y> \<and> (\<exists>g[##M]. is_recfun(r,x,H,g) \<and> y = H(x,g)))" 
    apply(rule_tac univalent_is_recfun) apply(rule_tac wf_imp_relativized) using assms by simp_all thm strong_replacement_def
  then have "\<exists>Z \<in> M. \<forall>z \<in> M. z \<in> Z \<longleftrightarrow> (\<exists>x \<in> M. x \<in> A \<and> (\<exists>y[##M]. z = <x,y> \<and> (\<exists>g[##M]. is_recfun(r,x,H,g) \<and> y = H(x,g))))"
    apply(rule_tac get_rep) using assms strep by auto 
  then obtain Z where ZH : 
    "Z \<in> M" "\<forall>z \<in> M. z \<in> Z \<longleftrightarrow> (\<exists>x \<in> M. x \<in> A \<and> (\<exists>y[##M]. z = <x,y> \<and> (\<exists>g[##M]. is_recfun(r,x,H,g) \<and> y = H(x,g))))" by auto 

  have ex_recfun : "\<And>x. x \<in> M \<Longrightarrow> \<exists>f \<in> M. is_recfun(r, x, H, f)" 
    apply(rule_tac wf_exists_is_recfun') using assms apply simp_all done

  have "Z = { <x, wftrec(r, x, H)>. x \<in> A }" 
    apply(rule_tac equality_iffI; rule iffI) 
  proof - 
    fix z assume zin: "z \<in> Z" 
    then have "z \<in> M" using ZH transM by auto
    then have "(\<exists>x \<in> M. x \<in> A \<and> (\<exists>y[##M]. z = <x,y> \<and> (\<exists>g[##M]. is_recfun(r,x,H,g) \<and> y = H(x,g))))" using ZH zin by auto 
    then obtain x y g where H: "x \<in> A" "z = <x, y>" "is_recfun(r, x, H, g)" "y = H(x, g)" by auto 
    then have "the_recfun(r, x, H) = g" apply(rule_tac the_recfun_eq) using assms by auto 
    then have "z = \<langle>x, wftrec(r, x, H)\<rangle>" unfolding wftrec_def using H by auto 
    then show "z \<in> { <x, wftrec(r, x, H)>. x \<in> A }" using H by auto 
  next 
    fix z assume "z \<in> {\<langle>x, wftrec(r, x, H)\<rangle> . x \<in> A}"
    then obtain x where xH : "x \<in> A" "z = \<langle>x, wftrec(r, x, H)\<rangle>" by auto
    then have xin : "x \<in> M" using assms transM by auto
    then obtain g where gH : "g \<in> M" "is_recfun(r, x, H, g)" using ex_recfun by auto
    then have eq : "wftrec(r, x, H) = H(x, g)" 
      unfolding wftrec_def apply(rule_tac b="the_recfun(r, x, H)" and a=g in ssubst) 
      apply(rule_tac the_recfun_eq) using assms by auto 
    then have zin : "z \<in> M" using xH is_recfun_imp_function assms gH xin pair_in_M_iff by auto
    then have "(\<exists>x \<in> M. x \<in> A \<and> (\<exists>y[##M]. z = <x,y> \<and> (\<exists>g[##M]. is_recfun(r,x,H,g) \<and> y = H(x,g))))" 
      apply(rule_tac x=x in bexI) apply(rule conjI) using xH apply simp 
      apply(rule_tac x="H(x, g)" in rexI) apply(rule_tac conjI) using xH eq apply simp 
      apply(rule_tac x=g in rexI) using gH apply simp 
      using xin assms gH is_recfun_imp_function by auto 
    then show "z \<in> Z" using zin ZH by auto 
  qed

  then show "{\<langle>x, wftrec(r, x, H)\<rangle> . x \<in> A} \<in> M" using ZH by auto
qed



(* parameterized relation *) 
definition prel where "prel(r, A) \<equiv> { <x, y> \<in> ((field(r) \<times> A) \<times> (field(r) \<times> A)). \<exists> x' y' a. x = <x', a> \<and> y = <y', a> \<and> <x', y'> \<in> r }" 

lemma prelI : "<x, y> \<in> r \<Longrightarrow> a \<in> A \<Longrightarrow> <<x, a>, <y, a>> \<in> prel(r, A)" 
  unfolding prel_def by auto 

lemma prelD : "<x, y> \<in> prel(r, A) \<Longrightarrow> \<exists>x' y' a. a \<in> A \<and> x = <x', a> \<and> y = <y', a> \<and> <x', y'> \<in> r" 
  unfolding prel_def by auto 

schematic_goal prel_fm_auto:
  assumes
    "nth(0,env) = p" 
    "nth(1,env) = r" 
    "nth(2,env) = A"  
    "env \<in> list(M)"
 shows
    "(\<exists>x \<in> M. \<exists>y \<in> M. \<exists>x' \<in> M. \<exists>y' \<in> M. \<exists>a \<in> M. \<exists>x'_y' \<in> M.
      pair(##M, x, y, p) \<and> pair(##M, x', a, x) \<and> pair(##M, y', a, y) \<and> pair(##M, x', y', x'_y') \<and> x'_y' \<in> r)
     \<longleftrightarrow> sats(M,?fm(0,1,2),env)"
  by (insert assms ; (rule sep_rules | simp)+)

definition prel_fm where 
  "prel_fm \<equiv> Exists(Exists(Exists(Exists(Exists(Exists(And(pair_fm(5, 4, 6), And(pair_fm(3, 1, 5), And(pair_fm(2, 1, 4), And(pair_fm(3, 2, 0), Member(0, 7)))))))))))  " 

lemma prel_fm_sats_iff : 
  "p \<in> M \<Longrightarrow> r \<in> M \<Longrightarrow> A \<in> M \<Longrightarrow> 
  sats(M, prel_fm, [p, r, A]) \<longleftrightarrow> (\<exists> x y x' y' a. p = <x, y> \<and> x = <x', a> \<and> y = <y', a> \<and> <x', y'> \<in> r)" 

  apply(rule_tac Q="(\<exists>x \<in> M. \<exists>y \<in> M. \<exists>x' \<in> M. \<exists>y' \<in> M. \<exists>a \<in> M. \<exists>x'_y' \<in> M.
                    pair(##M, x, y, p) \<and> pair(##M, x', a, x) \<and> pair(##M, y', a, y) \<and> pair(##M, x', y', x'_y') \<and> x'_y' \<in> r) " in iff_trans)
  apply(rule iff_flip) unfolding prel_fm_def apply(rule_tac r=r and A=A in prel_fm_auto) apply simp_all 
  using pair_in_M_iff transM apply auto done 

lemma prel_closed : 
  "r \<in> M \<Longrightarrow> A \<in> M \<Longrightarrow> prel(r, A) \<in> M" 
proof - 
  assume assms: "r \<in> M" "A \<in> M" 

  have "field(r) \<in> M" using field_closed assms by auto 
  then have base: "((field(r) \<times> A) \<times> (field(r) \<times> A)) \<in> M" using assms cartprod_closed by auto 

  have "separation(##M, \<lambda>x. sats(M, prel_fm, [x]@[r, A]))" 
    apply(rule_tac separation_ax) unfolding prel_fm_def using assms apply auto 
    by (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)  
  then have H: "{ p \<in> ((field(r) \<times> A) \<times> (field(r) \<times> A)). sats(M, prel_fm, [p]@[r, A]) } \<in> M"
    apply(rule_tac separation_notation) using base by auto 

  have "{ p \<in> ((field(r) \<times> A) \<times> (field(r) \<times> A)). sats(M, prel_fm, [p]@[r, A]) } =
        { p \<in> ((field(r) \<times> A) \<times> (field(r) \<times> A)). (\<exists> x y x' y' a. p = <x, y> \<and> x = <x', a> \<and> y = <y', a> \<and> <x', y'> \<in> r) }"
    apply(rule_tac iff_eq) apply(rule_tac b="[p] @ [r, A]" and a = "[p, r, A]" in ssubst) 
    apply simp apply(rule_tac prel_fm_sats_iff) apply(rule to_rin) 
    apply(rule_tac x="(field(r) \<times> A) \<times> (field(r) \<times> A)" in transM) apply simp 
    using base transM assms by auto
  also have "... = prel(r, A)" 
    unfolding prel_def apply(rule_tac iff_eq) by auto 
  finally show "prel(r, A) \<in> M" using H by auto 
qed

lemma wf_prel : "wf(r) \<Longrightarrow> wf(prel(r, A))" 
  apply(rule_tac A="(field(r) \<times> A)" in wfI) 
  apply(simp add:prel_def field_def) apply blast 
proof(clarify) 
  fix B a x
  assume assms: "wf(r)" "x \<in> field(r)" "a \<in> A" "\<forall>x\<in>field(r) \<times> A. (\<forall>y\<in>field(r) \<times> A. \<langle>y, x\<rangle> \<in> prel(r, A) \<longrightarrow> y \<in> B) \<longrightarrow> x \<in> B" 

  then have ih : 
    "\<And>x a. <x, a> \<in> field(r) \<times> A \<Longrightarrow> (\<And> y b. <y, b> \<in> field(r) \<times> A \<Longrightarrow> \<langle><y, b>, <x, a>\<rangle> \<in> prel(r, A) \<Longrightarrow> <y, b> \<in> B) \<Longrightarrow> <x, a> \<in> B" by auto 

  have "<x, a> \<in> field(r) \<times> A \<longrightarrow> <x, a> \<in> B" 
    apply(rule_tac r=r and P="\<lambda>x. <x, a> \<in> field(r) \<times> A \<longrightarrow> <x, a> \<in> B" in wf_induct) using assms apply simp 
    apply clarify apply(rule_tac ih) using assms apply simp 
  proof -
    fix x y b assume assms1: "\<langle>\<langle>y, b\<rangle>, x, a\<rangle> \<in> prel(r, A)" "(\<And>y. \<langle>y, x\<rangle> \<in> r \<Longrightarrow> \<langle>y, a\<rangle> \<in> field(r) \<times> A \<longrightarrow> \<langle>y, a\<rangle> \<in> B)"
    then have H1:"b = a" unfolding prel_def by auto 
    then have H2: "<y, x> \<in> r" using assms1 unfolding prel_def by auto
    have "<y, a> \<in> field(r) \<times> A" using assms1 unfolding prel_def by auto
    then show "\<langle>y, b\<rangle> \<in> B" using assms1 H1 H2 by auto 
  qed
  then show "<x, a> \<in> B" using assms by auto 
qed 

lemma prel_trans : "trans(r) \<Longrightarrow> trans(prel(r, p))" 
  unfolding trans_def apply clarify
proof - 
  fix x y z assume assms: "\<forall>x y z. \<langle>x, y\<rangle> \<in> r \<longrightarrow> \<langle>y, z\<rangle> \<in> r \<longrightarrow> \<langle>x, z\<rangle> \<in> r" "\<langle>x, y\<rangle> \<in> prel(r, p)" "\<langle>y, z\<rangle> \<in> prel(r, p)"
  then have " \<exists>x' y' a. a \<in> p \<and> x = <x', a> \<and> y = <y', a> \<and> <x', y'> \<in> r"  apply(rule_tac prelD) by simp 
  then obtain x' y' a where H1: "a \<in> p" "x = <x', a>" "y = <y', a>" "<x', y'> \<in> r" by auto 
  then have " \<exists>y' z' b. b \<in> p \<and> y = <y', b> \<and> z = <z', b> \<and> <y', z'> \<in> r"  apply(rule_tac prelD) using assms by simp 
  then obtain y' z' b where H2: "y = <y', b>" "z = <z', b>" "<y', z'> \<in> r" by auto 
  have "a = b" using H1 H2 by auto 
  have "<x', z'> \<in> r" using H1 H2 assms by auto 
  then have "<<x', a>, <z', a>> \<in> prel(r, p)" 
    apply(rule_tac prelI) using H1 by auto 
  then show "<x, z> \<in> prel(r, p)" using H1 H2 by auto 
qed


end 
end