theory RecFun_M 
  imports 
    ZF 
    Utilities_M
begin 

definition rep_for_recfun_fm where 
  "rep_for_recfun_fm(p, x, z, r) \<equiv> 
    Exists(Exists(Exists(And(Equal(x #+ 3, 2), And(pair_fm(x#+3, 0, z#+3), And(is_recfun_fm(p, r#+3, x#+3, 1), p))))))" 

context M_ZF_Fragment_Utilities_M
begin 

lemma rep_for_recfun_fm_sats_iff :
  "\<And>x z r p H e i j k. x \<in> M \<Longrightarrow> z \<in> M \<Longrightarrow> r \<in> M \<Longrightarrow> p \<in> formula \<Longrightarrow>
    i \<in> nat \<Longrightarrow> j \<in> nat \<Longrightarrow> k \<in> nat \<Longrightarrow> e \<in> list(M) \<Longrightarrow> e \<noteq> [] \<Longrightarrow> 
    nth(i, e) = x \<Longrightarrow> nth(j, e) = z \<Longrightarrow> nth(k, e) = r \<Longrightarrow> 
  (\<And>a0 a1 a2 a3 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> a3 \<in> M \<Longrightarrow> env \<in> list(M) 
    \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2, a3] @ env)) \<Longrightarrow>
  (\<forall>x[##M]. \<forall>g[##M]. function(g) \<longrightarrow> (##M)(H(x, g))) \<Longrightarrow>

  (\<exists>y[##M]. \<exists>g[##M]. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g))
   \<longleftrightarrow> sats(M, rep_for_recfun_fm(p, i, j, k), e)" 
proof - 
  fix x z r p H e i j k
  assume inM : "x \<in> M" "z \<in> M" "r \<in> M" 
  and pformula : "p \<in> formula"
  and ph : 
    "(\<And>a0 a1 a2 a3 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> a3 \<in> M \<Longrightarrow> env \<in> list(M) 
      \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2, a3] @ env))"
  and Hh : "(\<forall>x[##M]. \<forall>g[##M]. function(g) \<longrightarrow> (##M)(H(x, g)))" 
  and envH : "i \<in> nat" "j \<in> nat" "k \<in> nat" "e \<in> list(M)" "nth(i, e) = x" "nth(j, e) = z" "nth(k, e) = r" "e \<noteq> []"

  have iff_conj_lemma : "\<And>P Q R S. P \<longleftrightarrow> Q \<Longrightarrow> (P \<Longrightarrow> (R \<longleftrightarrow> S)) \<Longrightarrow> (P \<and> R) \<longleftrightarrow> (Q \<and> S)" by auto

  have t1:
    "(\<exists>y[##M]. \<exists>g[##M]. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g))
      \<longleftrightarrow> (\<exists>y \<in> M. \<exists>g \<in> M. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g))" by simp 
  have t2 : 
    "... \<longleftrightarrow> (\<exists>g \<in> M. \<exists>y \<in> M. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g))" by auto 
  have t3 :   
    "... \<longleftrightarrow>(\<exists>g \<in> M. \<exists>y \<in> M. pair(##M, x, y, z) \<and> M_is_recfun(##M, \<lambda>a b c. c = H(a, b), r, x, g) \<and> y = H(x, g))"
    apply (auto)
    apply (rename_tac g, rule_tac x="g" in bexI; auto)
    apply (rename_tac g, rule_tac Q="is_recfun(r, x, H, g)" in iffD2)
    apply (rule_tac is_recfun_abs)
    using Hh inM 
          apply simp_all
    unfolding relation2_def 
     apply simp
    apply (rename_tac g, rule_tac x="g" in bexI; auto)
    apply (rename_tac g, rule_tac P="M_is_recfun(##M, \<lambda>a b c. c = H(a, b), r, x, g)" in iffD1)
     apply (rule_tac is_recfun_abs)
    using Hh inM 
         apply simp_all
    unfolding relation2_def 
    apply simp 
    done 
  have t4 :   
    "... \<longleftrightarrow>(\<exists>x' \<in> M. \<exists>g \<in> M. \<exists>y \<in> M. x = x' \<and> pair(##M, x, y, z) \<and> M_is_recfun(##M, \<lambda>a b c. c = H(a, b), r, x, g) \<and> y = H(x, g))"
    using inM 
    by auto
  also have t5: 
    "... \<longleftrightarrow> sats(M, rep_for_recfun_fm(p, i, j, k), e)" 
    unfolding rep_for_recfun_fm_def 
    apply (rule bex_iff_sats)
     apply (rule bex_iff_sats)
      apply (rule bex_iff_sats)
       apply(rule iff_flip)
       apply(rename_tac x' g y, rule_tac Q="(M, Cons(y, Cons(g, Cons(x', e))) \<Turnstile> Equal(i #+ 3, 2)) \<and> (M, Cons(y, Cons(g, Cons(x', e))) \<Turnstile> And(pair_fm(i #+ 3, 0, j #+ 3), And(is_recfun_fm(p, k #+ 3, i #+ 3, 1), p)))" in iff_trans)
    using inM envH 
        apply simp 
       apply(rule iff_flip, rule iff_conj_lemma)
         apply(rule equal_iff_sats)
    using envH 
           apply (simp, simp, simp)
       apply(rule conj_iff_sats) 
          apply (rule pair_iff_sats)
    using inM envH 
              apply (simp_all)
    apply (rule conj_cong)
     apply (rule is_recfun_iff_sats)
    using inM 
            apply (simp_all)
     apply (rename_tac x' g y a0 a1 a2 a3, rule_tac Q="sats(M, p, [a0, a1, a2, a3] @ ([y, g, x'] @ e))" in iff_trans)
      apply (rule_tac ph)
    using inM 
          apply (simp_all)
    using \<open>e \<in> list(M)\<close>
    apply(cases e, force)
     apply (rename_tac x' g y a l, rule_tac Q="M, [y, g, x', a] @ l \<Turnstile> p" in iff_trans)
     apply (rule_tac ph) 
    using inM 
    by auto    
  show "(\<exists>y[##M]. \<exists>g[##M]. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g))
   \<longleftrightarrow> sats(M, rep_for_recfun_fm(p, i, j, k), e)" 
    using t1 t2 t3 t4 t5 by auto 
qed

lemma strep_iff : 
  "\<And>P Q. strong_replacement(##M, P) \<Longrightarrow> \<forall>x \<in> M. \<forall>z \<in> M. P(x, z) \<longleftrightarrow> Q(x, z) \<Longrightarrow> strong_replacement(##M, Q)"
  unfolding strong_replacement_def univalent_def by auto 

lemma recfun_strong_replacement_lemma :
  fixes r H p 
  assumes 
    "wf(r)" 
    "trans(r)" 
    "r \<in> M" 
    "p \<in> formula"
    "arity(p) \<le> 3"
    "(\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> H(x, g) \<in> M)" 
    "(\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2] @ env))"  
    "rep_for_recfun_fm(p, 0, 1, 2) \<in> \<Phi>"
  shows "strong_replacement(##M, \<lambda>x z. \<exists>y[##M]. \<exists>g[##M]. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g))"
proof - 

  have ph : 
      "(\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) 
        \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2] @ env))"
    using assms by auto

  have strep_sats : 
    "strong_replacement(##M, \<lambda>x. \<lambda>z. sats(M, rep_for_recfun_fm(p, 0, 1, 2), [x, z] @ [r]))"
    apply (rule_tac replacement_ax) 
    apply(simp add:rep_for_recfun_fm_def )
    using assms 
      apply auto[3]
    apply(simp add:rep_for_recfun_fm_def)
    using assms
    apply(rule_tac pred_le, simp_all)+
    apply(rule Un_least_lt)+
      apply (simp, simp)
    apply(rule Un_least_lt, subst arity_pair_fm)
        apply auto[4]
     apply(rule Un_least_lt, simp)+
     apply simp
    apply(rule Un_least_lt, subst arity_is_recfun_fm[where i="arity(p)"]) 
    using assms
           apply auto[6]
     apply(rule Un_least_lt)+
    apply simp_all
     apply(rule pred_le, simp_all)+
     apply(rule_tac j=3 in le_trans)
    apply simp_all
     apply(rule_tac j=3 in le_trans)
     apply simp_all
    done
    
  show "strong_replacement(##M, 
    \<lambda>x z. \<exists>y[##M]. \<exists>g[##M]. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g))"
    apply (rule_tac P=" \<lambda>x. \<lambda>z. sats(M, rep_for_recfun_fm(p, 0, 1, 2), [x, z] @ [r])" in strep_iff)
    apply (rule strep_sats)
    apply (rule ballI; rule ballI; rule iff_flip)
    apply (rule_tac Q="M, [x, z, r] \<Turnstile> rep_for_recfun_fm(p, 0, 1, 2)" in iff_trans) 
    apply (rule_tac rep_for_recfun_fm_sats_iff)
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
    "arity(p) \<le> 3"
    "x \<in> M" 
    "(\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> H(x, g) \<in> M)" 
    "(\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2] @ env))"  
    "rep_for_recfun_fm(p, 0, 1, 2) \<in> \<Phi>"
  shows "wfrec_replacement(##M, \<lambda>a b c. c = H(a, b), r)" 
  
  using assms
  unfolding wfrec_replacement_def
  apply(rule_tac P=" \<lambda>x z. \<exists>y[##M]. \<exists>g[##M]. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g)" in  strep_iff) 
   apply(rule_tac recfun_strong_replacement_lemma) 
          apply simp_all
  apply clarify 
  unfolding is_wfrec_def 
  apply(rule_tac P="\<forall>f \<in> M. M_is_recfun(##M, \<lambda>a b c. c = H(a, b), r, xa, f) \<longleftrightarrow> is_recfun(r, xa, H, f)" in mp) 
   apply simp 
  apply clarify 
  apply(rule_tac is_recfun_abs) 
  unfolding relation2_def 
      apply simp_all 
  done 

lemma wf_exists_is_recfun' : 
  fixes r H p x 
  assumes 
    "wf(r)" 
    "trans(r)" 
    "r \<in> M" 
    "p \<in> formula"
    "arity(p) \<le> 3"
    "x \<in> M" 
    "(\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> H(x, g) \<in> M)" 
    " (\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2] @ env))"  
    "rep_for_recfun_fm(p, 0, 1, 2) \<in> \<Phi>"
shows "\<exists>f \<in> M. is_recfun(r, x, H, f)"

  using assms 
  apply(rule_tac P="rex(##M, is_recfun(r, x, H))" in mp) 
   apply simp 
  apply (rule_tac wf_exists_is_recfun) 
       apply simp 
      apply simp 
     apply simp
    apply(rule_tac recfun_strong_replacement_lemma) 
           apply simp_all 
  done 

lemma the_recfun_in_M : 
  fixes r H p x 
  assumes 
    "wf(r)" 
    "trans(r)" 
    "r \<in> M" 
    "p \<in> formula"
    "arity(p) \<le> 3"
    "x \<in> M" 
    "(\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> H(x, g) \<in> M)" 
    " (\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2] @ env))"  
    "rep_for_recfun_fm(p, 0, 1, 2) \<in> \<Phi>" 
  shows "the_recfun(r, x, H) \<in> M"
proof - 
  have "\<exists>f \<in> M. is_recfun(r, x, H, f)" 
    apply(rule_tac wf_exists_is_recfun') 
    using assms 
    by auto 
  then obtain f where fH : "f \<in> M" "is_recfun(r, x, H, f)" by auto 
  then have "the_recfun(r, x, H) = f" 
    apply(rule_tac the_recfun_eq) 
    using assms 
    by auto 
  then show "the_recfun(r, x, H) \<in> M" using fH by auto 
qed

lemma wftrec_in_M : 
  fixes r H p x 
  assumes 
    "wf(r)" 
    "trans(r)" 
    "r \<in> M" 
    "p \<in> formula"
    "arity(p) \<le> 3"
    "x \<in> M" 
    " (\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2] @ env))"  
    "rep_for_recfun_fm(p, 0, 1, 2) \<in> \<Phi>"  
    and HM : "(\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> H(x, g) \<in> M)"
  shows "wftrec(r, x, H) \<in> M" 
proof - 
  have recfuninM : "the_recfun(r, x, H) \<in> M" 
    apply(rule the_recfun_in_M)
    using assms 
    by auto

  have "is_recfun(r, x, H, the_recfun(r, x, H))" 
    apply(rule unfold_the_recfun)
    using assms
    by auto
  then have eq : "the_recfun(r, x, H) = (\<lambda>y\<in>r -`` {x}. H(y, restrict(the_recfun(r, x, H), r -`` {y})))" 
    unfolding is_recfun_def 
    by simp

  have "H(x, the_recfun(r, x, H)) \<in> M" 
    apply(rule HM)
    using assms recfuninM 
      apply auto[2]
    apply(subst eq, rule function_lam)
    done
  then show ?thesis 
    unfolding wftrec_def 
    by auto
qed


lemma wftrec_pair_closed : 
  fixes r H p A  
  assumes 
    "wf(r)" 
    "trans(r)" 
    "r \<in> M" 
    "p \<in> formula"
    "arity(p) \<le> 3"
    "A \<in> M" 
    "(\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> H(x, g) \<in> M)" 
    " (\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, p, [a0, a1, a2] @ env))"  
    "rep_for_recfun_fm(p, 0, 1, 2) \<in> \<Phi>" 
  shows "{ <x, wftrec(r, x, H)>. x \<in> A } \<in> M"
proof - 
  have H:"strong_replacement(##M, \<lambda>x z. \<exists>y[##M]. \<exists>g[##M]. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g))"
    using assms recfun_strong_replacement_lemma 
    by auto

  have H1: "strong_replacement(##M, \<lambda>x z. z = <x, wftrec(r, x, H)>)" 
    apply(rule iffD1, rule_tac P="\<lambda>x z. \<exists>y[##M]. \<exists>g[##M]. pair(##M, x, y, z) \<and> is_recfun(r, x, H, g) \<and> y = H(x, g)" in strong_replacement_cong)
     apply(rule iffI, clarify)
      apply(simp add:wftrec_def)
      apply(rename_tac x y g, rule_tac a=g and b="the_recfun(r, x, H)" in ssubst)
       apply(rule the_recfun_eq, simp)
    using assms
        apply auto[3]
     apply clarify
     apply(rename_tac x y, rule_tac x="wftrec(r, x, H)" in rexI)
      apply(rename_tac x y, rule_tac x="the_recfun(r, x, H)" in rexI)
       apply(rule conjI)
    using pair_abs using pair_in_M_iff 
        apply force
       apply(rule conjI, rule unfold_the_recfun)
    using assms 
         apply auto[2]
       apply(simp add:wftrec_def)
      apply(simp, rule the_recfun_in_M)
    using assms 
             apply auto[9]
     apply simp
    using H 
    by auto

  show ?thesis 
    apply(rule to_rin, rule RepFun_closed, rule H1)
    using assms 
     apply simp
    apply(rule ballI, rule iffD2, rule pair_in_M_iff, rule conjI)
    using transM assms
     apply force
    apply(simp, rule wftrec_in_M)
    using assms transM 
    by auto
qed

lemma sats_is_wfrec_fm_iff : 
  fixes H Hfm r x v i j k env 
  assumes "env \<in> list(M)" "nth(i, env) = r" "nth(j, env) = x" "nth(k, env) = v"  
          "i \<in> nat" "j \<in> nat" "k \<in> nat" 
          "i < length(env)" "j < length(env)" "k < length(env)" 
          "x \<in> M" "v \<in> M" "r \<in> M" 
          "Hfm \<in> formula" "arity(Hfm) \<le> 3"
          "(\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> H(x, g) \<in> M)"
          "wf(r)" "trans(r)" 
          "rep_for_recfun_fm(Hfm, 0, 1, 2) \<in> \<Phi>" 
  and HH: "(\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) 
              \<Longrightarrow> a0 = H(a2, a1) \<longleftrightarrow> sats(M, Hfm, [a0, a1, a2] @ env))"
  shows "sats(M, is_wfrec_fm(Hfm, i, j, k), env) \<longleftrightarrow> v = wftrec(r, x, H)"  
proof -
  have iff_helper : "(\<exists>g[##M]. is_recfun(r, x, H, g) \<and> v = H(x, g)) \<longleftrightarrow> v = wftrec(r, x, H)"
  proof (rule iffI)
    assume "\<exists>g[##M]. is_recfun(r, x, H, g) \<and> v = H(x, g)" 
    then obtain g where gH : "g \<in> M" "is_recfun(r, x, H, g)" "v = H(x, g)" by auto
    have "the_recfun(r, x, H) = g" 
      apply(rule the_recfun_eq)
      using assms gH 
      by auto
    then show "v = wftrec(r, x, H)" 
      unfolding wftrec_def 
      using gH 
      by auto 
  next 
    assume assms1: "v = wftrec(r, x, H)" 
    have "is_recfun(r, x, H, the_recfun(r, x, H))" 
      apply(rule unfold_the_recfun)
      using assms 
      by auto
    then show "(\<exists>g[##M]. is_recfun(r, x, H, g) \<and> v = H(x, g))" 
      apply simp 
      apply(rule_tac x="the_recfun(r, x, H)" in bexI, simp)
      using assms1 
      unfolding wftrec_def 
       apply simp
      apply(rule_tac p=Hfm in the_recfun_in_M)
      using assms assms1
      by simp_all
  qed

  show "sats(M, is_wfrec_fm(Hfm, i, j, k), env) \<longleftrightarrow> v = wftrec(r, x, H)" 
    apply(rule_tac Q="is_wfrec(##M, \<lambda>a0 a1 a2. a2 = H(a0, a1), r, x, v)" in iff_trans, rule iff_flip)
     apply(rule is_wfrec_iff_sats)
            apply(rename_tac a0 a1 a2 a3 a4, rule_tac b="Cons(a0, Cons(a1, Cons(a2, Cons(a3, Cons(a4, env)))))" and a="[a0, a1, a2] @ ([a3, a4] @ env)" in ssubst)
             apply simp
            apply(rule HH)
    using assms
               apply(simp_all)
    apply(rule iff_trans, rule_tac H=H in is_wfrec_abs)
    using assms 
         apply force
    unfolding relation2_def 
        apply (simp, simp, simp, simp)
    by(rule iff_helper)
qed 

definition preds where "preds(R, x) \<equiv> { y \<in> M. R(y, x) }" 
definition preds_rel where "preds_rel(R, x) \<equiv> { <z, y> \<in> preds(R, x) \<times> (preds(R, x) \<union> {x}). R(z, y) }" 

lemma preds_rel_subset : "x \<in> M \<Longrightarrow>  preds_rel(R, x) \<subseteq> Rrel(R, M)" 
  unfolding preds_rel_def Rrel_def preds_def by auto

lemma preds_rel_subset' : "x \<in> M \<Longrightarrow> <z, y> \<in> preds_rel(R, x) \<Longrightarrow> <z, y> \<in> Rrel(R, M)" 
  unfolding preds_rel_def Rrel_def preds_def by auto

definition Relation_fm where "Relation_fm(R, fm) \<equiv> fm \<in> formula \<and> arity(fm) = 2 \<and> (\<forall>env \<in> list(M). \<forall>x \<in> M. \<forall>y \<in> M. R(y, x) \<longleftrightarrow> sats(M, fm, [y, x] @ env))" 

lemma Relation_fmD : "\<And>R Rfm env a b. Relation_fm(R, Rfm) \<Longrightarrow> a \<in> M \<Longrightarrow> b \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow>  R(a, b) \<longleftrightarrow> M, [a, b] @ env \<Turnstile> Rfm" 
  using Relation_fm_def by auto

end

definition is_preds_fm_ren where "is_preds_fm_ren(x)  \<equiv> { <0, 0> , <1, x #+ 1> }" 
definition is_preds_fm_Rfm_ren where "is_preds_fm_Rfm_ren(Rfm, x) \<equiv> ren(Rfm) ` 2` (x #+ 2)` is_preds_fm_ren(x)" 

definition is_preds_fm where "is_preds_fm(Rfm, x, S) \<equiv> Forall(Iff(Member(0, S #+ 1), is_preds_fm_Rfm_ren(Rfm, x)))" 

context M_ZF_Fragment_Utilities_M 
begin 

lemma is_preds_fm_ren_type : 
  fixes x 
  assumes "x \<in> nat" 
  shows "is_preds_fm_ren(x) \<in> 2 \<rightarrow> (x #+ 2)" 
  apply(rule Pi_memberI)
  unfolding is_preds_fm_ren_def relation_def function_def domain_def range_def
     apply(force, force, force)
  using assms 
  apply auto
   apply(subgoal_tac "x \<le> 0") 
    apply force
  apply(subgoal_tac "\<not> 0 < x", rule not_lt_imp_le, simp, simp, simp add:assms)
  apply clarify 
  using ltD 
  by auto

lemma is_preds_fm_type : 
  fixes Rfm x S 
  assumes "x \<in> nat" "S \<in> nat" "Rfm \<in> formula" 
  shows "is_preds_fm(Rfm, x, S) \<in> formula"
proof -
  have "is_preds_fm_Rfm_ren(Rfm, x) \<in> formula" 
    unfolding is_preds_fm_Rfm_ren_def 
    apply(rule ren_tc)
    using assms 
       apply(simp, simp, simp)
    using is_preds_fm_ren_type assms 
    by auto
  then show "is_preds_fm(Rfm, x, S) \<in> formula"
    unfolding is_preds_fm_def 
    using assms 
    by auto
qed

lemma is_preds_fm_arity : 
  fixes Rfm x S 
  assumes "x \<in> nat" "S \<in> nat" "Rfm \<in> formula" "arity(Rfm) = 2"
  shows "arity(is_preds_fm(Rfm, x, S)) \<le> succ(x) \<union> succ(S)"
proof - 
  have H : "is_preds_fm_Rfm_ren(Rfm, x) \<in> formula" 
    unfolding is_preds_fm_Rfm_ren_def
    apply(rule ren_tc)
    using assms is_preds_fm_ren_type 
    by auto

  have "arity(is_preds_fm_Rfm_ren(Rfm, x)) \<le> x #+ 2" 
    unfolding is_preds_fm_Rfm_ren_def
    apply(rule arity_ren)
    using assms is_preds_fm_ren_type Relation_fm_def le_refl
    by auto

  then show ?thesis 
    using assms
    unfolding is_preds_fm_def
    apply simp 
    apply(subst pred_Un_distrib, simp, rule arity_type, simp add:H)
    apply(subst pred_Un_distrib, simp, simp add:assms)
    apply simp
    apply(rule Un_least_lt, simp, rule ltI, simp, simp)
    apply(rule_tac j = "pred(x #+ 2)" in le_trans, rule pred_le, rule arity_type, simp add:H)
    using ltI 
    by auto
qed 

lemma sats_is_preds_fm_iff :
  fixes R Rfm i j x S env
  assumes "Relation_fm(R, Rfm)" "i \<in> nat" "j \<in> nat" "nth(i, env) = x" "nth(j, env) = S" "env \<in> list(M)" "x \<in> M" "S \<in> M" 
  shows "sats(M, is_preds_fm(Rfm, i, j), env) \<longleftrightarrow> S = preds(R, x)"
proof - 
  have iff_lemma : "\<And>P Q R. (P \<longleftrightarrow> Q) \<Longrightarrow> (R \<longleftrightarrow> P) \<longleftrightarrow> (R \<longleftrightarrow> Q)" by auto

  have ren_iff:  "\<And>v. v \<in> M \<Longrightarrow> sats(M, is_preds_fm_Rfm_ren(Rfm, i), Cons(v, env)) \<longleftrightarrow> sats(M, Rfm, [v, nth(i, env) ])" 
    unfolding is_preds_fm_Rfm_ren_def 
    apply(rule iff_flip, rule sats_iff_sats_ren)
    using assms Relation_fm_def 
           apply simp_all
     apply(rule Pi_memberI)
    unfolding is_preds_fm_ren_def relation_def function_def
        apply(simp, simp, force, force, simp)
     apply(rule ltD, simp)
    apply(rename_tac v k, case_tac "k=1")
     apply simp
     apply(subst function_apply_equality, simp)
    unfolding function_def  
      apply force
     apply simp
    apply(rename_tac v k, subgoal_tac "k=0")
     apply(subst function_apply_equality, simp)
    unfolding function_def  
      apply force
     apply simp
    using le_iff 
    by auto
  have RH : "\<And>v. v \<in> M \<Longrightarrow> R(v, nth(i, env)) \<longleftrightarrow> sats(M, is_preds_fm_Rfm_ren(Rfm, i), Cons(v, env))"
    apply(rule iff_trans, rule_tac R=R and Rfm = Rfm and env = "[]" in  Relation_fmD)
    using assms 
        apply(simp ,simp ,simp ,simp)
    using ren_iff 
    by auto

  have I1 : "sats(M, is_preds_fm(Rfm, i, j), env) \<longleftrightarrow> (\<forall>v \<in> M. (v \<in> S \<longleftrightarrow> sats(M, is_preds_fm_Rfm_ren(Rfm, i), Cons(v, env))))" 
    unfolding is_preds_fm_def 
    using assms
    by simp
  have I2 : "... \<longleftrightarrow> (\<forall>v \<in> M. (v \<in> S \<longleftrightarrow> R(v, x)))"
    apply(rule ball_iff, rule iff_lemma)
    using assms RH
    by auto
  have I3 : "... \<longleftrightarrow> S = preds(R, x)"
    unfolding preds_def
    apply(rule iffI, rule equality_iffI, rule iffI)
      apply(rename_tac y, subgoal_tac "y \<in> M", force)
    using assms transM 
    by auto   

  show ?thesis using I1 I2 I3 by auto
qed

end

definition is_preds_rel_fm where 
  "is_preds_rel_fm(Rfm, x, S) \<equiv> 
    Exists(And(is_preds_fm(Rfm, x #+ 1, 0), Forall(Iff(Member(0, S #+ 2), Exists(Exists(And(pair_fm(0, 1, 2), And(Member(0, 3), And(Or(Member(1, 3), Equal(1, x #+ 4)), Rfm)))))))))"

context M_ZF_Fragment_Utilities_M 
begin 

lemma is_preds_rel_fm_type : 
  fixes Rfm x S 
  assumes "x \<in> nat" "S \<in> nat" "Rfm \<in> formula" 
  shows "is_preds_rel_fm(Rfm, x, S) \<in> formula"

  unfolding is_preds_rel_fm_def
  apply(subgoal_tac "is_preds_fm(Rfm, x #+ 1, 0) \<in> formula")
  using assms 
   apply simp
  apply(rule is_preds_fm_type)
  using assms
  by auto

lemma is_preds_rel_fm_arity : 
  fixes Rfm x S 
  assumes "x \<in> nat" "S \<in> nat" "Rfm \<in> formula" "arity(Rfm) = 2"
  shows "arity(is_preds_rel_fm(Rfm, x, S)) \<le> succ(x) \<union> succ(S)"

  unfolding is_preds_rel_fm_def 
  using assms 
  apply simp
  apply(subst pred_Un_distrib, rule arity_type, rule is_preds_fm_type, simp_all)
  apply(rule Un_least_lt)
   apply(rule_tac j="pred(succ(succ(x)) \<union> succ(0))" in le_trans, rule pred_le')
      apply(rule arity_type, rule is_preds_fm_type, simp_all)
    apply(rule is_preds_fm_arity)
  using assms 
       apply simp_all
   apply(subst Ord_un_eq1, simp_all, rule ltI, simp, simp)
  apply(rule_tac a=2 and  b = "arity(Rfm)" in ssubst)
  using assms 
  unfolding Relation_fm_def 
   apply simp
  apply(simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)  
  apply(clarify, rule lt_succ_lt, simp)
  using not_le_iff_lt 
  by auto

lemma sats_is_preds_rel_fm_iff :
  fixes R Rfm i j x S env
  assumes "Relation_fm(R, Rfm)" "i \<in> nat" "j \<in> nat" "nth(i, env) = x" "nth(j, env) = S" "env \<in> list(M)" "x \<in> M" "S \<in> M" "preds(R, x) \<in> M"
  shows "sats(M, is_preds_rel_fm(Rfm, i, j), env) \<longleftrightarrow> S = preds_rel(R, x)" 
proof - 
  have iff_lemma : "\<And>P Q R S. (P \<longleftrightarrow> Q) \<Longrightarrow> (Q \<Longrightarrow> R \<longleftrightarrow> S) \<Longrightarrow> (P \<and> R) \<longleftrightarrow> (Q \<and> S)" by auto
  have iff_lemma2 : "\<And>P Q R S. (P \<longleftrightarrow> Q) \<Longrightarrow> (R \<longleftrightarrow> S) \<Longrightarrow> (P \<longleftrightarrow> R) \<longleftrightarrow> (Q \<longleftrightarrow> S)" by auto
  have I1 : "sats(M, is_preds_rel_fm(Rfm, i, j), env) \<longleftrightarrow> (\<exists>P \<in> M. P = preds(R, x) \<and> (\<forall>v \<in> M. v \<in> S \<longleftrightarrow> (\<exists>y \<in> M. \<exists>z \<in> M. v = <z, y> \<and> z \<in> P \<and> (y \<in> P \<or> y = x) \<and> R(z, y))))"
    unfolding is_preds_rel_fm_def 
    apply(rule iff_trans, rule sats_Exists_iff, simp add:assms)
    apply(rule bex_iff, rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_lemma)
    apply(rule sats_is_preds_fm_iff)
    using assms 
           apply(simp, simp, simp, simp, simp, simp, simp, simp)
    apply(rule iff_trans, rule sats_Forall_iff, simp add:assms, rule ball_iff, rule iff_trans, rule sats_Iff_iff, simp add:assms)
    apply(rule iff_lemma2, simp add:assms, rule iff_trans, rule sats_Exists_iff, simp add:assms)
    apply(rule bex_iff, rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff, simp add:assms, rule iff_conjI, simp)
    apply(rule iff_trans, rule sats_And_iff, simp add:assms)
    using pair_in_M_iff 
     apply force
    apply(rule iff_conjI)
    using pair_in_M_iff assms 
     apply simp
    apply(rule iff_trans, rule sats_And_iff, simp add:assms)
    using pair_in_M_iff 
     apply force
    apply(rule iff_conjI, rule iff_trans, rule sats_Or_iff, simp add:assms)
    using pair_in_M_iff 
      apply force
    apply(rule iff_disjI)
    using pair_in_M_iff assms 
      apply (simp, simp)
    apply(rename_tac a b c d , rule iff_flip, rule iff_trans, rule_tac R=R and Rfm = Rfm and env = "Cons(\<langle>d, c\<rangle>, Cons(preds(R, x), env))" in Relation_fmD)
    using assms pair_in_M_iff 
    by auto
  have I2 : "... \<longleftrightarrow> (\<forall>v \<in> M. v \<in> S \<longleftrightarrow> (\<exists>y \<in> M. \<exists>z \<in> M. v = <z, y> \<and> z \<in> preds(R, x) \<and> (y \<in> preds(R, x) \<or> y = x) \<and> R(z, y)))"
    using assms 
    by auto
  have I3 : "... \<longleftrightarrow> S = preds_rel(R, x)" 
    unfolding preds_rel_def
  proof(rule iffI, rule equality_iffI, rule iffI)
    fix v assume assms1 : "\<forall>v\<in>M. v \<in> S \<longleftrightarrow> (\<exists>y\<in>M. \<exists>z\<in>M. v = \<langle>z, y\<rangle> \<and> z \<in> preds(R, x) \<and> (y \<in> preds(R, x) \<or> y = x) \<and> R(z, y))" "v \<in> S" 
    then have "v \<in> M" using assms transM by auto
    then have "(\<exists>y\<in>M. \<exists>z\<in>M. v = \<langle>z, y\<rangle> \<and> z \<in> preds(R, x) \<and> (y \<in> preds(R, x) \<or> y = x) \<and> R(z, y))" using assms1 by auto 
    then obtain y z where yzH :"y \<in> M" "z \<in> M" "v = <z, y>" "z \<in> preds(R, x)" "y \<in> preds(R, x) \<or> y = x" "R(z, y)" by auto 
    then show "v \<in> { <z, y> \<in> preds(R, x) \<times> (preds(R, x) \<union> {x}). R(z, y) }" by auto 
  next 
    fix v assume assms1 : 
      "\<forall>v\<in>M. v \<in> S \<longleftrightarrow> (\<exists>y\<in>M. \<exists>z\<in>M. v = \<langle>z, y\<rangle> \<and> z \<in> preds(R, x) \<and> (y \<in> preds(R, x) \<or> y = x) \<and> R(z, y))" 
      "v \<in> { <z, y> \<in> preds(R, x) \<times> (preds(R, x) \<union> {x}). R(z, y) }"
    then obtain y z where yzH : "v = <z, y>" "z \<in> preds(R, x)" "y \<in> preds(R, x) \<or> y = x" "R(z, y)" by auto
    then have zinM : "z \<in> M" unfolding preds_def by auto 
    have yinM : "y \<in> M" using yzH assms unfolding preds_def by auto 
    then have "(\<exists>y\<in>M. \<exists>z\<in>M. v = \<langle>z, y\<rangle> \<and> z \<in> preds(R, x) \<and> (y \<in> preds(R, x) \<or> y = x) \<and> R(z, y))" using zinM yinM yzH by auto 
    then show "v \<in> S" using yzH pair_in_M_iff zinM yinM assms1 by auto
  next 
    assume assms1:"S = {\<langle>z,y\<rangle> \<in> preds(R, x) \<times> (preds(R, x) \<union> {x}) . R(z, y)}" 
    then show "\<forall>v\<in>M. v \<in> S \<longleftrightarrow> (\<exists>y\<in>M. \<exists>z\<in>M. v = \<langle>z, y\<rangle> \<and> z \<in> preds(R, x) \<and> (y \<in> preds(R, x) \<or> y = x) \<and> R(z, y))" 
      unfolding preds_def
      using assms
      by auto
  qed

  show ?thesis using I1 I2 I3 by auto
qed

definition preds_rel_sep_fm where "preds_rel_sep_fm(Rfm) \<equiv> Exists(Exists(And(pair_fm(0, 1, 2), Rfm)))"

lemma preds_rel_in_M : 
  fixes R Rfm x
  assumes "Relation_fm(R, Rfm)" "x \<in> M" "preds(R, x) \<in> M" "preds_rel_sep_fm(Rfm) \<in> \<Phi>"
  shows "preds_rel(R, x) \<in> M"
proof - 
  define fm where "fm \<equiv> preds_rel_sep_fm(Rfm) "
  have sats_iff :  "\<And>v. v \<in> M \<Longrightarrow> sats(M, fm, [v]) \<longleftrightarrow> v \<in> Rrel(R, M)" 
    unfolding fm_def preds_rel_sep_fm_def
    apply(rule_tac Q="\<exists>y \<in> M. \<exists>z \<in> M. v = <z, y> \<and> R(z, y)" in iff_trans)
    using assms 
    apply simp
    apply(rule bex_iff, rule bex_iff, rule iff_conjI, simp)
    apply(rule iff_flip, rule iff_trans, rename_tac v a b, rule_tac Rfm=Rfm and R=R in Relation_fmD)
    using assms pair_in_M_iff
    unfolding Rrel_def 
    by auto
  
  have "separation(##M, \<lambda>v. sats(M, fm, [v] @ []))" 
    apply(rule separation_ax)
    unfolding fm_def
    using assms Relation_fm_def
       apply(simp add:preds_rel_sep_fm_def, force, force, force, simp add:preds_rel_sep_fm_def)
    by(simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)  

  then have H : "{ v \<in> preds(R, x) \<times> (preds(R, x) \<union> {x}). sats(M, fm, [v] @ []) } \<in> M"
    apply(rule_tac separation_notation, simp)
    using assms cartprod_closed Un_closed singleton_in_M_iff 
    by auto

  have "{ v \<in> preds(R, x) \<times> (preds(R, x) \<union> {x}). sats(M, fm, [v] @ []) } = { v \<in> preds(R, x) \<times> (preds(R, x) \<union> {x}). v \<in> Rrel(R, M) }" 
    apply(rule iff_eq, simp, rule sats_iff)
    using assms cartprod_closed Un_closed singleton_in_M_iff transM
    by auto

  also have "... = preds_rel(R, x)"
    unfolding preds_rel_def Rrel_def
    using assms transM 
    by auto

  finally show ?thesis using H by auto
qed
   
lemma trans_preds_rel : "t \<in> M \<Longrightarrow> trans(Rrel(R, M)) \<Longrightarrow> trans(preds_rel(R, t))" 
  unfolding trans_def 
proof(clarify)
  fix x y z assume assms : "t \<in> M" "\<forall>x y z. \<langle>x, y\<rangle> \<in> Rrel(R, M) \<longrightarrow> \<langle>y, z\<rangle> \<in> Rrel(R, M) \<longrightarrow> \<langle>x, z\<rangle> \<in> Rrel(R, M)" "<x, y> \<in> preds_rel(R, t)" "<y, z> \<in> preds_rel(R, t)" 
  then have xin : "x \<in> preds(R, t)" using assms unfolding preds_rel_def by auto 
  have zin : "z \<in> preds(R, t) \<union> {t}" using assms unfolding preds_rel_def by auto
  have H1:"<x, y> \<in> Rrel(R, M)" apply(rule subsetD) using preds_rel_subset assms by auto
  have H2: "<y, z> \<in> Rrel(R, M)" apply(rule subsetD) using preds_rel_subset assms by auto
  have "<x, z> \<in> Rrel(R, M)" using H1 H2 assms by auto 
  then have "R(x, z)" unfolding Rrel_def by auto 
  then show "\<langle>x, z\<rangle> \<in> preds_rel(R, t)" 
    unfolding preds_rel_def 
    using xin zin by auto
qed

lemma wf_preds_rel : "x \<in> M \<Longrightarrow> wf(Rrel(R, M)) \<Longrightarrow> wf(preds_rel(R, x))" 
  apply(rule_tac s="Rrel(R, M)" in  wf_subset)
  using preds_rel_subset 
  by auto

lemma preds_rel_vimage_eq : 
  "trans(Rrel(R, M)) \<Longrightarrow> <y, x> \<in> Rrel(R, M) \<Longrightarrow> preds_rel(R, x) -`` {y} = Rrel(R, M) -`` {y}" 
proof(rule equality_iffI, rule iffI)
  fix z assume assms : "z \<in> preds_rel(R, x) -`` {y}" "<y, x> \<in> Rrel(R, M)"
  then have "<z, y> \<in> preds_rel(R, x)" by auto 
  then have "<z, y> \<in> Rrel(R, M)" 
    apply(rule_tac x=x in preds_rel_subset')
    using assms 
    unfolding Rrel_def 
    by auto
  then show "z \<in> Rrel(R, M) -`` {y}" by auto 
next 
  fix z assume assms : "<y, x> \<in> Rrel(R, M)"  "z \<in> Rrel(R, M) -`` {y}" "trans(Rrel(R, M))" 
  then have rel : "<z, y> \<in> Rrel(R, M)" by auto 
  then have rel' : "<z, x> \<in> Rrel(R, M)" using assms trans_def by auto 

  have yin : "y \<in> preds(R, x)" 
    unfolding preds_def
    using Rrel_def assms 
    by auto
  have zin: "z \<in> preds(R, x)"
    unfolding preds_def 
    using rel' assms Rrel_def 
    by auto

  then have "<z, y> \<in> preds_rel(R, x)" 
    unfolding preds_rel_def 
    using yin zin rel Rrel_def 
    by auto
  then show "z \<in> preds_rel(R, x) -`` {y}" by auto
qed

lemma preds_rel_vimage_eq' : 
  "x \<in> M \<Longrightarrow> preds_rel(R, x) -`` {x} = Rrel(R, M) -`` {x}" 
proof (rule equality_iffI, rule iffI)
  fix y assume assms : "y \<in> preds_rel(R, x) -`` {x}" "x \<in> M" 
  then have "<y, x> \<in> preds_rel(R, x)" by auto
  then show "y \<in> Rrel(R, M) -`` {x}" 
    apply(rule_tac b=x in vimageI)
     apply(rule_tac x=x in preds_rel_subset')
    using assms 
    by auto
next 
  fix y assume assms : "y \<in> Rrel(R, M) -`` {x}" 
  then have "<y, x> \<in> Rrel(R, M)" by auto 
  then have "<y, x> \<in> preds_rel(R, x)" 
    unfolding preds_rel_def 
    apply simp
    apply(rule conjI)
    unfolding preds_def Rrel_def 
    by auto
  then show "y \<in> preds_rel(R, x) -`` {x}" by auto
qed

lemma the_recfun_preds_rel_eq : 
  fixes x y R H
  assumes "x \<in> M" "trans(Rrel(R, M))" "wf(Rrel(R, M))" "y \<in> preds(R, x) \<union> {x}" 
  shows "the_recfun(preds_rel(R, x), y, H) = the_recfun(Rrel(R, M), y, H)" 
proof - 
  have eq : "\<And>y. y \<in> preds(R, x) \<union> {x} \<longrightarrow> the_recfun(preds_rel(R, x), y, H) = the_recfun(Rrel(R, M), y, H)"
  proof (rule_tac P="\<lambda>y. y \<in> preds(R, x) \<union> {x} \<longrightarrow> the_recfun(preds_rel(R, x), y, H) = the_recfun(Rrel(R, M), y, H)" and r="Rrel(R, M)" in wf_induct, simp add:assms, rule impI)
    fix y  
    assume assms1 : "y \<in> preds(R, x) \<union> {x}" "(\<And>z. \<langle>z, y\<rangle> \<in> Rrel(R, M) \<Longrightarrow> z \<in> preds(R, x) \<union> {x} \<longrightarrow> the_recfun(preds_rel(R, x), z, H) = the_recfun(Rrel(R, M), z, H))"

    have ih : "\<And>z. \<langle>z, y\<rangle> \<in> Rrel(R, M) \<Longrightarrow> z \<in> preds(R, x) \<union> {x} \<Longrightarrow> the_recfun(preds_rel(R, x), z, H) = the_recfun(Rrel(R, M), z, H)"
      using assms1 by auto

    have vimage_preds : "\<And>z. z \<in> Rrel(R, M) -`` {y} \<Longrightarrow> z \<in> preds(R, x)" 
    proof - 
      fix z assume "z \<in> Rrel(R, M) -`` {y}" 
      then have H: "<z, y> \<in> Rrel(R, M)" by auto 
      have "<z, x> \<in> Rrel(R, M)" 
      proof (cases "y=x")
        case True
        then show ?thesis using H by auto
      next
        case False
        then have "y \<in> preds(R, x)" using assms1 by auto 
        then have "<y, x> \<in> Rrel(R, M)" unfolding preds_def Rrel_def using assms by auto 
        then show ?thesis using assms H unfolding trans_def by auto
      qed
      then show "z \<in> preds(R, x)" unfolding preds_def Rrel_def by auto 
    qed
  
    have recfun : "is_recfun(preds_rel(R, x), y, H, the_recfun(preds_rel(R, x), y, H))" 
      apply(rule unfold_the_recfun)
      using assms wf_preds_rel trans_preds_rel 
      by auto
    have recfun' : "is_recfun(Rrel(R, M), y, H, the_recfun(Rrel(R, M), y, H))" 
      apply(rule unfold_the_recfun)
      using assms 
      by auto

    have "the_recfun(preds_rel(R, x), y, H) = (\<lambda>z\<in>preds_rel(R, x) -`` {y}. H(z, restrict(the_recfun(preds_rel(R, x), y, H), preds_rel(R, x) -`` {z})))"
      using recfun
      unfolding is_recfun_def
      by auto
    also have "... = (\<lambda>z\<in>preds_rel(R, x) -`` {y}. H(z, the_recfun(preds_rel(R, x), z, H)))"
      apply(rule lam_cong, simp)
      apply(subst the_recfun_cut)
      using assms wf_preds_rel trans_preds_rel
      by auto
    also have "... = (\<lambda>z\<in>Rrel(R, M) -`` {y}. H(z, the_recfun(preds_rel(R, x), z, H)))"
      apply(rule lam_cong)
       apply(cases "y = x", simp)
        apply(rule preds_rel_vimage_eq', simp add:assms)
       apply(subgoal_tac "y \<in> preds(R, x)")
        apply(rule preds_rel_vimage_eq, simp add:assms)
      using assms assms1
      unfolding Rrel_def preds_def 
      by auto 
    also have "... = (\<lambda>z\<in>Rrel(R, M) -`` {y}. H(z, the_recfun(Rrel(R, M), z, H)))"
      apply(rule lam_cong, simp, subst ih)
        apply force 
       apply (simp, rule disjI1, rule vimage_preds, simp, simp)
      done
    also have "... = (\<lambda>z\<in>Rrel(R, M) -`` {y}. H(z, restrict(the_recfun(Rrel(R, M), y, H), Rrel(R, M) -`` {z})))"
      apply(rule lam_cong, simp)
      apply(subst the_recfun_cut)
      using assms 
      by auto
    also have "... = the_recfun(Rrel(R, M), y, H)"   
      using recfun'
      unfolding is_recfun_def
      by auto
    finally show "the_recfun(preds_rel(R, x), y, H) = the_recfun(Rrel(R, M), y, H)" by simp
  qed
  then show ?thesis using assms by auto
qed

lemma wftrec_preds_rel_eq : 
  fixes x R H
  assumes "x \<in> M" "trans(Rrel(R, M))" "wf(Rrel(R, M))"
  shows "wftrec(Rrel(R, M), x, H) = wftrec(preds_rel(R, x), x, H)" 
proof -
  have "the_recfun(preds_rel(R, x), x, H) = the_recfun(Rrel(R, M), x, H)" 
    apply(rule the_recfun_preds_rel_eq)
    using assms 
    by auto
  then show "wftrec(Rrel(R, M), x, H) = wftrec(preds_rel(R, x), x, H)" 
    unfolding wftrec_def by auto
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

end

definition prel_fm where 
  "prel_fm \<equiv> Exists(Exists(Exists(Exists(Exists(Exists(And(pair_fm(5, 4, 6), And(pair_fm(3, 1, 5), And(pair_fm(2, 1, 4), And(pair_fm(3, 2, 0), Member(0, 7)))))))))))  " 

definition is_preds_prel_elem_fm where 
  "is_preds_prel_elem_fm(Rfm, x, a, v) \<equiv> Exists(And(is_preds_rel_fm(Rfm, x #+ 1, 0), Exists(Exists(Exists(Exists(Exists(And(pair_fm(2, 3, v #+ 6), And(pair_fm(0, a #+ 6, 2), And(pair_fm(1, a #+ 6, 3), And(pair_fm(0, 1, 4), Member(4, 5))))))))))))" 

definition is_preds_prel_fm where 
  "is_preds_prel_fm(Rfm, x, a, S) \<equiv> Forall(Iff(Member(0, S #+ 1), is_preds_prel_elem_fm(Rfm, x #+ 1, a #+ 1, 0)))" 

definition is_wftrec_fm where "is_wftrec_fm(Gfm, Rfm, x, a, v) \<equiv> Exists(Exists(And(is_preds_prel_fm(Rfm, x#+2, a#+2, 0), And(pair_fm(x #+ 2, a #+ 2, 1), is_wfrec_fm(Gfm, 0, 1, v #+ 2)))))" 

locale M_ZF_Fragment_RecFun_M = M_ZF_Fragment_Utilities_M + 
  assumes recfun_M_prel_fm : "prel_fm \<in> \<Phi>" 
begin 

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
    apply(rule_tac separation_ax) 
       apply(simp add:prel_fm_def)
      apply(simp add:recfun_M_prel_fm)
    unfolding prel_fm_def
    using assms  
      apply auto 
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
 

lemma is_preds_prel_elem_fm_type : 
  fixes Rfm x a v 
  assumes "x \<in> nat" "a \<in> nat" "v \<in> nat" "Rfm \<in> formula"
  shows "is_preds_prel_elem_fm(Rfm, x, a, v) \<in> formula" 

  unfolding is_preds_prel_elem_fm_def
  apply (subgoal_tac "is_preds_rel_fm(Rfm, x #+ 1, 0) \<in> formula")
   apply simp
  apply(rule is_preds_rel_fm_type)
  using assms
  by auto

lemma is_preds_prel_elem_fm_arity : 
  fixes Rfm x a v 
  assumes "x \<in> nat" "a \<in> nat" "v \<in> nat" "Rfm \<in> formula" "arity(Rfm) = 2"
  shows "arity(is_preds_prel_elem_fm(Rfm, x, a, v)) \<le> succ(x) \<union> succ(a) \<union> succ(v)"
  unfolding is_preds_prel_elem_fm_def pair_fm_def upair_fm_def
  using assms 
  apply simp
  apply(subgoal_tac "is_preds_rel_fm(Rfm, succ(x), 0) \<in> formula")
   apply(subst pred_Un_distrib, simp_all)+
   apply(rule Un_least_lt)
    apply(rule_tac j = "pred(succ(succ(x)) \<union> 1)" in le_trans, rule pred_le', simp_all)
     apply(rule is_preds_rel_fm_arity, simp_all)
    apply(subst Ord_un_eq1, simp_all)
    apply(rule ltI, simp_all)
  apply(rule Un_least_lt, simp add:ltI, simp add:ltI)
  apply(rule is_preds_rel_fm_type)
  using assms 
  by auto

lemma sats_is_preds_prel_elem_fm_iff : 
  fixes R Rfm i j k x a v env p
  assumes "Relation_fm(R, Rfm)" "preds(R, x) \<in> M"  "env \<in> list(M)" "i \<in> nat" "j \<in> nat" "k \<in> nat" "nth(i, env) = x" "nth(j, env) = a" "nth(k, env) = v" 
          "v \<in> M" "x \<in> M" "a \<in> M" "p \<in> M" "a \<in> p" "preds_rel_sep_fm(Rfm) \<in> \<Phi>"
  shows "sats(M, is_preds_prel_elem_fm(Rfm, i, j, k), env) \<longleftrightarrow> v \<in> preds_rel(\<lambda>a b. <a, b> \<in> prel(Rrel(R, M), p), <x, a>)" 
proof - 
  have iff_lemma : "\<And>P Q R S. (P \<longleftrightarrow> Q) \<Longrightarrow> (Q \<Longrightarrow> R \<longleftrightarrow> S) \<Longrightarrow> (P \<and> R) \<longleftrightarrow> (Q \<and> S)" by auto
  have iff_lemma2 : "\<And>P Q R S. (P \<longleftrightarrow> Q) \<Longrightarrow> (R \<longleftrightarrow> S) \<Longrightarrow> (P \<longleftrightarrow> R) \<longleftrightarrow> (Q \<longleftrightarrow> S)" by auto
  have iff_lemma3 : "\<And>A B C. B = C \<Longrightarrow> (A = B) \<longleftrightarrow> (A = C)" by auto

  have I1 : "sats(M, is_preds_prel_elem_fm(Rfm, i, j, k), env) \<longleftrightarrow> (\<exists>A \<in> M. A = preds_rel(R, x) \<and> (\<exists>zy \<in> M. \<exists>ya \<in> M. \<exists>za \<in> M. \<exists>y \<in> M. \<exists>z \<in> M. v = <za, ya> \<and> za = <z, a> \<and> ya = <y, a> \<and> zy = <z, y> \<and> zy \<in> A))" 
    unfolding is_preds_prel_elem_fm_def
    apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff, rule iff_trans, rule sats_And_iff, simp add:assms)
    apply(rule iff_lemma, rule sats_is_preds_rel_fm_iff)
    using assms 
             apply auto[9]
    apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)+
    using assms 
    apply (simp, rule_tac iff_lemma, simp)+
    using pair_in_M_iff preds_rel_in_M assms
    by auto
  have I2 : "... \<longleftrightarrow>(\<exists>y \<in> M. \<exists>z \<in> M. v = <<z, a>, <y, a>> \<and> <z, y> \<in> preds_rel(R, x))" 
    using assms preds_rel_in_M pair_in_M_iff 
    by auto
  have I3 : "... \<longleftrightarrow> v \<in> preds_rel(\<lambda>a b. <a, b> \<in> prel(Rrel(R, M), p), <x, a>)" 
  proof(rule iffI)
    assume "\<exists>y\<in>M. \<exists>z\<in>M. v = \<langle>\<langle>z, a\<rangle>, y, a\<rangle> \<and> \<langle>z, y\<rangle> \<in> preds_rel(R, x)" 
    then obtain y z where yzH : "y \<in> M" "z \<in> M" "v = <<z, a>, <y, a>>" "<z, y> \<in> preds_rel(R, x)" by auto 

    have "z \<in> preds(R, x)" using yzH unfolding preds_rel_def by auto 
    then have "<<z, a>, <x, a>> \<in> prel(Rrel(R, M), p)" 
      unfolding prel_def preds_def Rrel_def 
      using assms
      by auto 
    then have H1: "\<langle>z, a\<rangle> \<in> preds(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>)" 
      unfolding preds_def using assms yzH pair_in_M_iff by simp

    have "y \<in> preds(R, x) \<union> {x}" using yzH preds_rel_def by auto 
    then have "<<y, a>, <x, a>> \<in> prel(Rrel(R, M), p) \<or> y = x" 
      unfolding preds_def prel_def Rrel_def
      using assms 
      by auto
    then have H2: "<y, a> \<in> preds(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>) \<or> y = x" 
      unfolding preds_def using assms yzH pair_in_M_iff by simp

    have H3 : "<<z, a>, <y, a>> \<in> prel(Rrel(R, M), p)"
      apply(rule prelI)
      using yzH preds_rel_def Rrel_def assms 
      by auto

    show "v \<in> preds_rel(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>)" 
      unfolding preds_rel_def 
      apply simp
      apply(rule conjI)
      using yzH H1 H2 H3
      by auto
  next 
    assume "v \<in> preds_rel(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>)" 

    then obtain za ya where zyH : 
      "v = <za, ya>" 
      "\<langle>za, ya\<rangle> \<in> prel(Rrel(R, M), p)" 
      "za \<in> preds(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>)"
      "ya \<in> preds(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>) \<union> {\<langle>x, a\<rangle>}"
      unfolding preds_rel_def 
      by auto
    
    obtain z where zaeq : "za = <z, a>" using zyH unfolding preds_def prel_def by auto
    obtain y where yaeq : "ya = <y, a>" using zyH unfolding preds_def prel_def by auto

    have rel : "<z, y> \<in> Rrel(R, M)" using zyH zaeq yaeq unfolding prel_def by auto 

    have zinM : "z \<in> M" using zaeq zyH unfolding prel_def Rrel_def by auto 
    have yinM : "y \<in> M" using yaeq zyH unfolding prel_def Rrel_def by auto

    have "<<z, a>, <x, a>> \<in> prel(Rrel(R, M), p)" using zyH zaeq unfolding preds_def by auto
    then have H1: "z \<in> preds(R, x)" unfolding preds_def prel_def Rrel_def by auto 

    have "<<y, a>, <x, a>> \<in> prel(Rrel(R, M), p) \<or> y = x" using zyH yaeq unfolding preds_def by auto
    then have H2: "y \<in> preds(R, x) \<union> {x}" unfolding preds_def prel_def Rrel_def by auto 

    have rel' : "<z, y> \<in> preds_rel(R, x)" 
      unfolding preds_rel_def 
      using H1 H2 rel Rrel_def 
      by auto

    show "\<exists>y\<in>M. \<exists>z\<in>M. v = \<langle>\<langle>z, a\<rangle>, y, a\<rangle> \<and> \<langle>z, y\<rangle> \<in> preds_rel(R, x)" 
      apply(rule_tac x=y in bexI, rule_tac x=z in bexI)
      using zyH zaeq yaeq rel' yinM zinM 
      by auto
  qed

  show ?thesis using I1 I2 I3 by auto
qed

lemma preds_prel_in_M : 
  fixes R Rfm x a p
  assumes "Relation_fm(R, Rfm)" "preds(R, x) \<in> M"  
          "x \<in> M" "a \<in> M" "p \<in> M" "a \<in> p" "is_preds_prel_elem_fm(Rfm, 1, 2, 0) \<in> \<Phi>" "preds_rel_sep_fm(Rfm) \<in> \<Phi>"
  shows "preds_rel(\<lambda>a b. <a, b> \<in> prel(Rrel(R, M), p), <x, a>) \<in> M"
proof - 
  define A where "A \<equiv> { v \<in> (preds(R, x) \<times> {a}) \<times> ((preds(R, x) \<times> {a}) \<union> {<x, a>}). sats(M, is_preds_prel_elem_fm(Rfm, 1, 2, 0), [v] @ [x, a]) }"

  have "separation(##M, \<lambda>v. sats(M, is_preds_prel_elem_fm(Rfm, 1, 2, 0), [v] @ [x, a]))" 
    apply(rule separation_ax)
      apply(rule is_preds_prel_elem_fm_type)
    using assms 
    unfolding Relation_fm_def
         apply simp_all
    apply(rule le_trans, rule is_preds_prel_elem_fm_arity)
    using assms
         apply simp_all
    apply(rule Un_least_lt)+
    by auto

  then have AinM :  "A \<in> M" 
    unfolding A_def 
    apply(rule separation_notation)
    using singleton_in_M_iff assms cartprod_closed pair_in_M_iff Un_closed
    by auto 

  have "A = { v \<in> (preds(R, x) \<times> {a}) \<times> ((preds(R, x) \<times> {a}) \<union> {<x, a>}). v \<in> preds_rel(\<lambda>a b. <a, b> \<in> prel(Rrel(R, M), p), <x, a>) }" 
    unfolding A_def
    apply(rule iff_eq, rule sats_is_preds_prel_elem_fm_iff)
    using assms pair_in_M_iff transM 
    by auto

  also have "... = preds_rel(\<lambda>a b. <a, b> \<in> prel(Rrel(R, M), p), <x, a>)" 
  proof (rule equality_iffI, rule iffI, simp)
    have H : "\<And>X Y P x. x \<in> { <a, b> \<in> X \<times> Y. P(a, b) } \<Longrightarrow> \<exists>a b. a \<in> X \<and> b \<in> Y \<and> P(a, b) \<and> x = <a, b>" 
      by auto

    fix s assume sin : "s \<in> preds_rel(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>)"
    then have "\<exists>za ya. 
      za \<in> preds(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>)
      \<and> ya \<in> preds(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>) \<union> { <x, a> }
      \<and> \<langle>za, ya\<rangle> \<in> prel(Rrel(R, M), p)
      \<and> s = <za, ya>" 
      unfolding preds_rel_def 
      by(rule H)
    then obtain za ya where zayaH:
      "za \<in> preds(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>)" 
      "ya \<in> preds(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>) \<union> { <x, a> }" 
      "\<langle>za, ya\<rangle> \<in> prel(Rrel(R, M), p)" "s = <za, ya>" by auto
    obtain z where zaeq : "za = <z, a>" using zayaH unfolding preds_def prel_def by auto 
    obtain y where yaeq : "ya = <y, a>" using zayaH unfolding preds_def prel_def by auto 

    have "<<z, a>, <x, a>> \<in> prel(Rrel(R, M), p)" 
      using zayaH zaeq unfolding preds_def by auto 
    then have "<z, x> \<in> Rrel(R, M)" 
      unfolding prel_def by auto
    then have H1 : "z \<in> preds(R, x)" 
      unfolding preds_def Rrel_def by auto

    have "<<y, a>, <x, a>> \<in> prel(Rrel(R, M), p) \<or> y = x" 
      using zayaH yaeq unfolding preds_def by auto
    then have "<y, x> \<in> Rrel(R, M) \<or> y = x" 
      unfolding prel_def by auto 
    then have H2: "y \<in> preds(R, x) \<union> {x}" 
      unfolding preds_def Rrel_def by auto 

    show "s \<in> {v \<in> (preds(R, x) \<times> {a}) \<times> (preds(R, x) \<times> {a} \<union> {\<langle>x, a\<rangle>}) . v \<in> preds_rel(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>)}" 
      using sin 
      apply simp
      using zaeq yaeq zayaH H1 H2 
      by auto
  qed

  finally show ?thesis using AinM by auto
qed

lemma is_preds_prel_fm_type :
  fixes Rfm x a S 
  assumes "Rfm \<in> formula" "x \<in> nat" "a \<in> nat" "S \<in> nat" 
  shows "is_preds_prel_fm(Rfm, x, a, S) \<in> formula" 
  unfolding is_preds_prel_fm_def 
  apply(subgoal_tac "is_preds_prel_elem_fm(Rfm, x #+ 1, a #+ 1, 0) \<in> formula", simp)
  apply(rule is_preds_prel_elem_fm_type)
  using assms 
  by auto 

lemma is_preds_prel_fm_arity : 
  fixes R Rfm x a S 
  assumes "Rfm \<in> formula" "arity(Rfm) = 2" "x \<in> nat" "a \<in> nat" "S \<in> nat" 
  shows "arity(is_preds_prel_fm(Rfm, x, a, S)) \<le> succ(x) \<union> succ(a) \<union> succ(S)"
  unfolding is_preds_prel_fm_def 
  using assms 
  apply(subgoal_tac "is_preds_prel_elem_fm(Rfm, succ(x), succ(a), 0) \<in> formula")
  apply simp 
   apply(subst pred_Un_distrib, simp_all)+
   apply(rule Un_least_lt, simp, rule ltI, simp, simp, rule pred_le, simp_all)
   apply(rule_tac b="succ(succ(x) \<union> succ(a) \<union> succ(S))" and a="succ(succ(x)) \<union> succ(succ(a)) \<union> succ(succ(S))" in ssubst)
    apply(subst succ_Un_distrib, simp_all)
    apply(subst succ_Un_distrib, simp_all)
   apply(rule_tac j="succ(succ(x)) \<union> succ(succ(a)) \<union> 1" in le_trans)
    apply(rule is_preds_prel_elem_fm_arity)
  using assms 
        apply simp_all
   apply(rule Un_least_lt, rule Un_least_lt)
     apply(simp, rule ltI, simp, simp)+
   apply (rule_tac j="succ(succ(S))" in le_trans, simp, rule Un_upper2_le, simp_all)
  apply(rule is_preds_prel_elem_fm_type)
  using assms
  by auto

lemma sats_is_preds_prel_fm_iff : 
  fixes R Rfm i j k x a S env p
  assumes "Relation_fm(R, Rfm)" "preds(R, x) \<in> M"  "env \<in> list(M)" "i \<in> nat" "j \<in> nat" "k \<in> nat" "nth(i, env) = x" "nth(j, env) = a" "nth(k, env) = S" 
          "S \<in> M" "x \<in> M" "a \<in> M" "p \<in> M" "a \<in> p" "is_preds_prel_elem_fm(Rfm, 1, 2, 0) \<in> \<Phi>" "preds_rel_sep_fm(Rfm) \<in> \<Phi>"
  shows "sats(M, is_preds_prel_fm(Rfm, i, j, k), env) \<longleftrightarrow> S = preds_rel(\<lambda>a b. <a, b> \<in> prel(Rrel(R, M), p), <x, a>)" 
proof- 
  have iff_lemma : "\<And>P Q R S. (P \<longleftrightarrow> Q) \<Longrightarrow> (R \<longleftrightarrow> S) \<Longrightarrow> (P \<longleftrightarrow> R) \<longleftrightarrow> (Q \<longleftrightarrow> S)" by auto
  have iff_lemma2 : "\<And>A B C. B = C \<Longrightarrow> (A = B) \<longleftrightarrow> (A = C)" by auto

  have "preds_rel(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>) \<in> M"
    apply(rule preds_prel_in_M)
    using assms 
    by auto
  then have H: "preds_rel(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>) \<subseteq> M" 
    using transM by auto
 
  have I1 : "sats(M, is_preds_prel_fm(Rfm, i, j, k), env) \<longleftrightarrow> (\<forall>v \<in> M. v \<in> S \<longleftrightarrow> v \<in> preds_rel(\<lambda>a b. <a, b> \<in> prel(Rrel(R, M), p), <x, a>))"
    unfolding is_preds_prel_fm_def 
    apply(rule iff_trans, rule sats_Forall_iff, simp add:assms, rule ball_iff)
    apply(rule iff_trans, rule sats_Iff_iff, simp add:assms, rule iff_lemma)
    using assms 
     apply simp
    apply(rule sats_is_preds_prel_elem_fm_iff)
    using assms 
    by simp_all
  have I2 : "... \<longleftrightarrow> S = preds_rel(\<lambda>a b. <a, b> \<in> prel(Rrel(R, M), p), <x, a>)" 
    apply(rule iffI, rule equality_iffI, rule iffI)
      apply(rename_tac v, subgoal_tac "v \<in> M", simp)
    using assms transM 
      apply force
     apply(rename_tac v, subgoal_tac "v \<in> M", simp)
    using H 
     apply force
    by auto

  then show ?thesis using I1 I2 by auto
qed


lemma is_wftrec_fm_type : 
  fixes Gfm Rfm x a v 
  assumes "Gfm \<in> formula" "Rfm \<in> formula" "x \<in> nat" "a \<in> nat" "v \<in> nat" 
  shows "is_wftrec_fm(Gfm, Rfm, x, a, v) \<in> formula" 

  unfolding is_wftrec_fm_def 
  apply(subgoal_tac "is_preds_prel_fm(Rfm, x #+ 2, a #+ 2, 0) \<in> formula") 
  using assms
   apply simp
  apply(rule is_preds_prel_fm_type)
  using assms
  by auto

lemma arity_is_wftrec_fm : 
  fixes Gfm Rfm x a v 
  assumes "Gfm \<in> formula" "Rfm \<in> formula" "arity(Gfm) \<le> 3" "arity(Rfm) = 2" "x \<in> nat" "a \<in> nat" "v \<in> nat" 
  shows "arity(is_wftrec_fm(Gfm, Rfm, x, a, v)) \<le> succ(x) \<union> succ(a) \<union> succ(v)" 

  unfolding is_wftrec_fm_def 
  apply(subgoal_tac "is_preds_prel_fm(Rfm, x #+ 2, a #+ 2, 0) \<in> formula")  
  using assms
   apply simp
   apply(subst pred_Un_distrib, simp_all)+
   apply(rule Un_least_lt, rule pred_le, simp_all, rule pred_le, simp_all)
    apply(rule_tac j="succ(succ(succ(x))) \<union> succ(succ(succ(a))) \<union> 1" in le_trans)
     apply(rule is_preds_prel_fm_arity, simp_all)
    apply(subst succ_Un_distrib, simp_all)+
    apply(rule Un_least_lt)+
      apply(rule ltI, simp_all)+
    apply(rule disjI1, rule ltD, simp)
   apply(rule Un_least_lt, rule pred_le, simp_all, rule pred_le, simp_all)
  unfolding pair_fm_def upair_fm_def
    apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union) 
   apply(rule pred_le, simp_all)+
   apply(subst arity_is_wfrec_fm, simp_all)
   apply(rule Un_least_lt)+
      apply (simp, simp, simp)
    apply(rule ltI, simp, simp add:assms)
   apply(rule pred_le, simp_all)+
  apply(rule_tac j=3 in le_trans, simp, simp)
  apply(rule is_preds_prel_fm_type)
  using assms 
  by auto
  

lemma wftrec_prel_eq : 
  fixes r x a G Gfm H p
  assumes "wf(r)" "r \<in> M" "trans(r)" "a \<in> p" "p \<in> M" "x \<in> field(r)" "Gfm \<in> formula" "arity(Gfm) \<le> 3" 
  and satsGfm: " (\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = G(a2, a1) \<longleftrightarrow> sats(M, Gfm, [a0, a1, a2] @ env))" 
  and GM : "\<And>x g. x \<in> M \<Longrightarrow> function(g) \<Longrightarrow> g \<in> M \<Longrightarrow> G(x, g) \<in> M"  
  and HGeq: "\<And>h g x. h \<in> r -`` {x} \<rightarrow> M \<Longrightarrow> g \<in> (r -`` {x} \<times> {a}) \<rightarrow> M \<Longrightarrow> g \<in> M  
               \<Longrightarrow> x \<in> field(r) \<Longrightarrow> (\<And>y. y \<in> r -`` {x} \<Longrightarrow> h`y = g`<y, a>) \<Longrightarrow> H(x, h) = G(<x, a>, g)"  
  and "rep_for_recfun_fm(Gfm, 0, 1, 2) \<in> \<Phi>"

  shows "wftrec(r, x, H) = wftrec(prel(r, p), <x, a>, G)" 
proof - 
  have "\<And>x. x \<in> field(r) \<longrightarrow> wftrec(r, x, H) = wftrec(prel(r, p), <x, a>, G)"
  proof (rule_tac P="\<lambda>x. x \<in> field(r) \<longrightarrow> wftrec(r, x, H) = wftrec(prel(r, p), <x, a>, G)" and r=r in wf_induct, simp add:assms, rule impI)
    fix x 
    assume assms1: "(\<And>y. \<langle>y, x\<rangle> \<in> r \<Longrightarrow> y \<in> field(r) \<longrightarrow> wftrec(r, y, H) = wftrec(prel(r, p), \<langle>y, a\<rangle>, G))" "x \<in> field(r)" 

    have "field(r) \<in> M" using field_closed assms by auto
    then have xinM : "x \<in> M" using transM assms1 by auto

    have recfun : "is_recfun(r, x, H, the_recfun(r, x, H))" 
      apply(rule unfold_the_recfun)
      using assms 
      by auto 
    then have eq1: "the_recfun(r, x, H) = (\<lambda>y\<in>r -`` {x}. H(y, restrict(the_recfun(r, x, H), r -`` {y})))" 
      unfolding is_recfun_def 
      by simp

    have recfun2 : "is_recfun(prel(r, p), <x, a>, G, the_recfun(prel(r, p), <x, a>, G))" 
      apply(rule unfold_the_recfun)
      using assms wf_prel prel_trans
      by auto 
    then have eq2: "the_recfun(prel(r, p), <x, a>, G) = (\<lambda>y\<in>prel(r, p) -`` {<x, a>}. G(y, restrict(the_recfun(prel(r, p), <x, a>, G), prel(r, p) -`` {y})))" 
      unfolding is_recfun_def 
      by simp

    have app_eq: "\<And>y. y \<in> r -`` {x} \<Longrightarrow> the_recfun(r, x, H)`y = the_recfun(prel(r, p), <x, a>, G)`<y, a>" 
    proof - 
      fix y assume assms2: "y \<in> r -`` {x}" 
      have "the_recfun(r, x, H)`y = H(y, restrict(the_recfun(r, x, H), r -`` {y}))"
        apply(subst eq1)
        using assms2 
        by simp
      also have "... = H(y, the_recfun(r, y, H))" 
        apply(subst the_recfun_cut)
        using assms assms2 
        by auto
      also have "... = wftrec(r, y, H)" 
        unfolding wftrec_def 
        by simp
      finally have H : "the_recfun(r, x, H)`y = wftrec(r, y, H)" by simp

      have "<y, x> \<in> r" using assms2 by auto
      then have rel : "<<y, a>, <x, a>> \<in> prel(r, p)"
        by(rule prelI, simp add:assms)
      then have "<y, a> \<in> prel(r, p) -`` {<x, a>}" by auto 
      then have "the_recfun(prel(r, p), <x, a>, G)`<y, a> = G(<y, a>, restrict(the_recfun(prel(r, p), <x, a>, G), prel(r, p) -`` {<y, a>}))"
        by(subst eq2, simp)
      also have "... = G(<y, a>, the_recfun(prel(r, p), <y, a>, G))" 
        apply(subst the_recfun_cut)
        using assms rel prel_trans wf_prel
        by auto 
      also have "... = wftrec(prel(r, p), <y, a>, G)" 
        unfolding wftrec_def
        by simp 
      finally have "the_recfun(prel(r, p), <x, a>, G)`<y, a> = wftrec(prel(r, p), <y, a>, G)" by simp

      then show "the_recfun(r, x, H)`y = the_recfun(prel(r, p), <x, a>, G)`<y, a>" 
        using H assms1 assms2 
        by auto
    qed

    have recfun2inM : "the_recfun(prel(r, p), \<langle>x, a\<rangle>, G) \<in> M" 
      apply(rule_tac p=Gfm in the_recfun_in_M)
             apply(rule wf_prel, simp add:assms)
            apply(rule prel_trans, simp add:assms)
           apply(rule prel_closed)
      using assms pair_in_M_iff xinM transM 
            apply auto[5]
       apply(rule GM)
         apply auto[3]
       apply(rule satsGfm)
      using assms
      by auto

    then have "range(the_recfun(prel(r, p), \<langle>x, a\<rangle>, G)) \<in> M" using range_closed by auto
    then have rangesubset2 : "range(the_recfun(prel(r, p), \<langle>x, a\<rangle>, G)) \<subseteq> M" using transM by auto

    have rangesubset : "range(the_recfun(r, x, H)) \<subseteq> M" 
    proof (rule subsetI) 
      fix v assume "v \<in> range(the_recfun(r, x, H))" 
      then obtain u where uH: "<u, v> \<in> the_recfun(r, x, H)" by auto 

      have eq : "domain(the_recfun(r, x, H)) = r -`` {x}" 
        by(subst eq1, subst domain_lam, simp)
      have "u \<in> domain(the_recfun(r, x, H))" by(rule_tac b=v in domainI, simp add:uH) 
      then have uin : "u \<in> r -`` {x}" using eq by auto 

      have rxinM : "r -`` {x} \<in> M" 
        apply(rule to_rin, rule vimage_closed)
        using xinM singleton_in_M_iff assms 
        by auto
      have uinM : "u \<in> M" 
        apply(rule to_rin, rule_tac x="r -`` {x}" in transM)
        using uin rxinM 
        by auto

      have "the_recfun(prel(r, p), <x, a>, G)`<u, a> = the_recfun(r, x, H)`u" 
        by(rule eq_flip, rule app_eq, simp add:uin)
      also have "... = v" 
        apply(rule function_apply_equality, simp add:uH)
        apply(subst eq1, rule function_lam)
        done
      finally have veq: "v = the_recfun(prel(r, p), <x, a>, G)`<u, a>" by simp
    
      show "v \<in> M" 
        apply(subst veq, rule to_rin, rule apply_closed, simp add:recfun2inM)
        using uinM assms transM pair_in_M_iff 
        by auto
    qed


    have vimageeq : "r -`` {x} \<times> {a} = prel(r, p) -`` {\<langle>x, a\<rangle>}" 
    proof(rule equality_iffI, rule iffI)
      fix v assume "v \<in> r -`` {x} \<times> {a}" 
      then obtain u where uH : "v = <u, a>" "u \<in> r -`` {x}" by auto 
      then have "<u, x> \<in> r" by auto 
      then have "<<u, a>, <x, a>> \<in> prel(r, p)" by(rule prelI, simp add:assms) 
      then show "v \<in> prel(r, p) -`` {\<langle>x, a\<rangle>}" using uH by auto 
    next 
      fix v assume "v \<in> prel(r, p) -`` {\<langle>x, a\<rangle>}" 
      then have "<v, <x, a>> \<in> prel(r, p)" by auto 
      then obtain u where uH : "v = <u, a>" "<u, x> \<in> r" unfolding prel_def by auto 
      then have "u \<in> r -`` {x}" by auto 
      then show "v \<in> r -`` {x} \<times> {a}" using uH by auto
    qed

    have "H(x, the_recfun(r, x, H)) = G(<x, a>, the_recfun(prel(r, p), <x, a>, G))" 
      apply(rule HGeq)
          apply(rule Pi_memberI)
             apply(subst eq1, rule relation_lam)
            apply(subst eq1, rule function_lam)
           apply(subst eq1, subst domain_lam, simp)
          apply(rule rangesubset)
         apply(rule Pi_memberI)
            apply(subst eq2, rule relation_lam)
           apply(subst eq2, rule function_lam)
          apply(subst eq2, subst domain_lam, rule vimageeq)
         apply(rule rangesubset2)
        apply(rule recfun2inM)
      using assms assms1 app_eq 
      by auto
    then show "wftrec(r, x, H) = wftrec(prel(r, p), \<langle>x, a\<rangle>, G)"
      unfolding wftrec_def 
      by simp
  qed

  then show ?thesis using assms by auto
qed

lemma wftrec_prel_preds_rel_eq : 
  fixes R Rfm G H x a
  assumes "x \<in> M" "a \<in> M" "x \<in> field(Rrel(R, M))" "wf(Rrel(R, M))" "trans(Rrel(R, M))"
          "Relation_fm(R, Rfm)" "preds(R, x) \<in> M"  "Gfm \<in> formula" "arity(Gfm) \<le> 3" 
          "\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> G(x, g) \<in> M" 
          "\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = G(a2, a1) \<longleftrightarrow> sats(M, Gfm, [a0, a1, a2] @ env)"  
  and HGeq: "\<And>h g x. h \<in> Rrel(R, M) -`` {x} \<rightarrow> M \<Longrightarrow> g \<in> (Rrel(R, M) -`` {x} \<times> {a}) \<rightarrow> M \<Longrightarrow> g \<in> M  
               \<Longrightarrow> x \<in> field(Rrel(R, M)) \<Longrightarrow> (\<And>y. y \<in> Rrel(R, M) -`` {x} \<Longrightarrow> h`y = g`<y, a>) \<Longrightarrow> H(x, h) = G(<x, a>, g)"  
  and "preds_rel_sep_fm(Rfm) \<in> \<Phi>" "rep_for_recfun_fm(Gfm, 0, 1, 2) \<in> \<Phi>"
  shows "wftrec(prel(preds_rel(R, x), {a}), <x, a>, G) = wftrec(Rrel(R, M), x, H)" 
proof - 

  have E1: "wftrec(prel(preds_rel(R, x), {a}), <x, a>, G) = wftrec(preds_rel(R, x), x, H)" 
  proof(cases "preds_rel(R, x) -`` {x} = 0")
    case True
    then have eq0 : "preds_rel(R, x) -`` {x} = 0" by auto 
    then have eqH : "wftrec(preds_rel(R, x), x, H) = H(x, 0)" 
      apply(subst wftrec)
        apply(rule wf_preds_rel, simp add:assms, simp add:assms)
       apply(rule trans_preds_rel, simp add:assms, simp add:assms)
      by simp
    have eq0': "prel(preds_rel(R, x), {a}) -`` {<x, a>} = 0" 
    proof(rule ccontr)
      assume "prel(preds_rel(R, x), {a}) -`` {\<langle>x, a\<rangle>} \<noteq> 0" 
      then obtain y where "<y, a> \<in> prel(preds_rel(R, x), {a}) -`` {\<langle>x, a\<rangle>}" unfolding prel_def by blast
      then have "<y, x> \<in> preds_rel(R, x)" unfolding prel_def by auto 
      then have "y \<in> preds_rel(R, x) -`` {x}" by auto 
      then have "preds_rel(R, x) -`` {x} \<noteq> 0" by auto 
      then show "False" using eq0 by auto
    qed
    then have eqG : "wftrec(prel(preds_rel(R, x), {a}), <x, a>, G) = G(<x, a>, 0)" 
      apply(subst wftrec)
        apply(rule wf_prel, rule wf_preds_rel, simp add:assms, simp add:assms)
       apply(rule prel_trans, rule trans_preds_rel, simp add:assms, simp add:assms)
      by(subst eq0', simp)

    have eq0'' : "Rrel(R, M) -`` {x} = preds_rel(R, x) -`` {x}" 
      apply(rule eq_flip, rule preds_rel_vimage_eq')
      using assms
      by auto

    show "wftrec(prel(preds_rel(R, x), {a}), \<langle>x, a\<rangle>, G) = wftrec(preds_rel(R, x), x, H)" 
      apply(subst eqH, subst eqG, rule eq_flip)
      apply(rule HGeq)
      apply(subst eq0'', subst eq0, simp)
      apply(subst eq0'', subst eq0, simp)
      using assms zero_in_M
             apply auto[2]
      apply(subst apply_0, simp)+
      by simp
  next
    case False
    then obtain y where "<y, x> \<in> preds_rel(R, x)" by blast 
    then have xinfield : "x \<in> field(preds_rel(R, x))" by auto 

    have subsetH: "preds_rel(R, x) \<subseteq> Rrel(R, M)" 
      unfolding preds_rel_def Rrel_def preds_def
      using assms
      by auto

    have fieldsubset : "field(preds_rel(R, x)) \<subseteq> field(Rrel(R, M))" 
    proof(rule subsetI)
      fix w assume "w \<in> field(preds_rel(R, x))" 
      then obtain u where "<w, u> \<in> preds_rel(R, x) \<or> <u, w> \<in> preds_rel(R, x)" by auto 
      then have "<w, u> \<in> Rrel(R, M) \<or> <u, w> \<in> Rrel(R, M)" using subsetH by auto 
      then show "w \<in> field(Rrel(R, M))" by auto 
    qed 

    have fieldcase : "\<And>t. t \<in> field(preds_rel(R, x)) \<Longrightarrow> <t, x> \<in> Rrel(R, M) \<or> t = x" 
    proof - 
      fix t assume "t \<in> field(preds_rel(R, x))" 
      then have "t \<in> preds(R, x) \<or> t = x" unfolding preds_rel_def by auto 
      then show "<t, x> \<in> Rrel(R, M) \<or> t = x" 
        unfolding preds_def Rrel_def 
        using assms 
        by auto
    qed

    have H: "\<And>t z. t \<in> field(preds_rel(R, x)) \<Longrightarrow> z \<in> Rrel(R, M) -`` {t} \<Longrightarrow> z \<in> preds_rel(R, x) -`` {t}"
    proof - 
      fix t z 
      assume assms2 : "t \<in> field(preds_rel(R, x))" "z \<in> Rrel(R, M) -`` {t}" 
      have tin : "t \<in> preds(R, x) \<union> {x}" using assms2 unfolding preds_rel_def field_def by auto 
      have ztin : "<z, t> \<in> Rrel(R, M)" using assms2 by auto 
      then have "<z, x> \<in> Rrel(R, M)" 
        apply(cases "t = x", simp)
        apply(subgoal_tac "<t, x> \<in> Rrel(R, M)")
         apply(rule transD)
        using assms 
           apply auto[3]
        using tin assms
        unfolding preds_def Rrel_def 
        by auto
      then have "z \<in> preds(R, x)" unfolding Rrel_def preds_def by auto
      then show "z \<in> preds_rel(R, x) -`` {t}" 
        using tin ztin
        unfolding preds_rel_def Rrel_def 
        by auto
    qed

    show "wftrec(prel(preds_rel(R, x), {a}), \<langle>x, a\<rangle>, G) = wftrec(preds_rel(R, x), x, H)"  
      apply(rule eq_flip, rule_tac Gfm = Gfm in wftrec_prel_eq)
                apply(rule wf_preds_rel, simp add:assms)
                apply(simp add:assms)
               apply(rule_tac Rfm = Rfm in preds_rel_in_M)
                 apply(simp add:assms)+
              apply(rule trans_preds_rel, simp add:assms, simp add:assms, simp)
      using singleton_in_M_iff xinfield assms
            apply auto[6]
      apply(rule HGeq)
          apply(rename_tac h g u, case_tac "u = x", simp)
      using preds_rel_vimage_eq' assms 
           apply force
          apply(rename_tac h g u, rule_tac b="Rrel(R, M) -`` {u}" and a="preds_rel(R, x) -`` {u}" in ssubst)
           apply(rule eq_flip, rule preds_rel_vimage_eq, simp add:assms)
      using fieldcase 
           apply force
          apply simp
          apply(rename_tac h g u, case_tac "u = x", simp)
      using preds_rel_vimage_eq' assms 
           apply force
         apply(rename_tac h g u, rule_tac b="Rrel(R, M) -`` {u}" and a="preds_rel(R, x) -`` {u}" in ssubst)
           apply(rule eq_flip, rule preds_rel_vimage_eq, simp add:assms)
      using fieldcase 
           apply force
         apply simp
        apply simp
      using fieldsubset 
       apply force      
      using fieldsubset H assms
      by auto
  qed 
  also have E2: "... = wftrec(Rrel(R, M), x, H)" 
    apply(rule eq_flip)
    apply(rule wftrec_preds_rel_eq)
    using assms 
    by auto
  finally show ?thesis by simp
qed

lemma sats_is_Rrel_wftrec_fm_iff :
  fixes H G Gfm R Rfm x v i j k env a
  assumes "env \<in> list(M)" "a \<in> M" "x \<in> field(Rrel(R, M))" 
          "i < length(env)" "j < length(env)" "k < length(env)" 
          "nth(i, env) = x" "nth(j, env) = a" "nth(k, env) = v" 
          "wf(Rrel(R, M))" "trans(Rrel(R, M))"
          "preds(R, x) \<in> M" 
          "Relation_fm(R, Rfm)"
          "Gfm \<in> formula" 
          "arity(Gfm) \<le> 3" 
          "\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> G(x, g) \<in> M" 
          " (\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = G(a2, a1) \<longleftrightarrow> sats(M, Gfm, [a0, a1, a2] @ env))"  
  and HGeq: "\<And>h g x. h \<in> Rrel(R, M) -`` {x} \<rightarrow> M \<Longrightarrow> g \<in> (Rrel(R, M) -`` {x} \<times> {a}) \<rightarrow> M \<Longrightarrow> g \<in> M  
               \<Longrightarrow> x \<in> field(Rrel(R, M)) \<Longrightarrow> (\<And>y. y \<in> Rrel(R, M) -`` {x} \<Longrightarrow> h`y = g`<y, a>) \<Longrightarrow> H(x, h) = G(<x, a>, g)"  
  and "is_preds_prel_elem_fm(Rfm, 1, 2, 0) \<in> \<Phi>" "preds_rel_sep_fm(Rfm) \<in> \<Phi>" "rep_for_recfun_fm(Gfm, 0, 1, 2) \<in> \<Phi>" 
  shows "sats(M, is_wftrec_fm(Gfm, Rfm, i, j, k), env) \<longleftrightarrow> v = wftrec(Rrel(R, M), x, H)" 
proof - 

  have iff_lemma1 : "\<And>P Q R S. P \<longleftrightarrow> Q \<Longrightarrow> (Q \<Longrightarrow> R \<longleftrightarrow> S) \<Longrightarrow> (P \<and> R \<longleftrightarrow> Q \<and> S)" by auto 
  have iff_lemma2 : "\<And>a b c. b = c \<Longrightarrow> a = b \<longleftrightarrow> a = c" by auto

  define p where "p \<equiv> {a}" 
  have pinM : "p \<in> M" using singleton_in_M_iff assms p_def by auto
  have ainp : "a \<in> p" using p_def by auto

  have vinM : "v \<in> M" using assms nth_type by auto
  have xinM : "x \<in> M" using assms nth_type by auto
  have ainM : "a \<in> M" using assms nth_type by auto
  have inat : "i \<in> nat" using lt_nat_in_nat assms length_type by auto
  have jnat : "j \<in> nat" using lt_nat_in_nat assms length_type by auto
  have knat : "k \<in> nat" using lt_nat_in_nat assms length_type by auto

  have eq1 : "Rrel(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), M) = prel(Rrel(R, M), p)"
  proof (rule equality_iffI, rule iffI)
    fix v assume "v \<in> Rrel(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), M)"
    then show "v \<in> prel(Rrel(R, M), p)"
      unfolding Rrel_def prel_def 
      using pair_in_M_iff 
      by auto
  next 
    fix v assume vin: "v \<in> prel(Rrel(R, M), p) "
    then obtain a b q where abqH: "<a, b> \<in> Rrel(R, M)" "q \<in> p" "v = <<a, q>, <b, q>>" unfolding prel_def by auto
    then have "q \<in> M" using transM assms pinM by auto
    then have aqinM : "<a, q> \<in> M" using abqH pair_in_M_iff unfolding Rrel_def by auto
    then have bqinM : "<b, q> \<in> M" using abqH pair_in_M_iff unfolding Rrel_def by auto

    show "v \<in> Rrel(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), M)" 
      unfolding Rrel_def 
      apply (simp, rule conjI)
      using pair_in_M_iff aqinM bqinM abqH 
       apply force
      apply(rule_tac x="<a, q>" in exI, rule_tac x="<b, q>" in exI, rule conjI, simp add:abqH)
      using abqH vin 
      unfolding Rrel_def
      by auto
  qed

  have eq2 : "prel(preds_rel(R, x), {a}) = preds_rel(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>)" 
  proof(rule equality_iffI, rule iffI)
    fix s assume assms1 : "s \<in> prel(preds_rel(R, x), {a})" 
    then obtain b c where bcH : "s = <<b, a>, <c, a>>" "<b, c> \<in> preds_rel(R, x)" unfolding prel_def by auto 

    then have "b \<in> preds(R, x)" unfolding preds_rel_def by auto 
    then have H1:"\<langle>b, a\<rangle> \<in> preds(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>)" 
      unfolding preds_def 
      apply simp
      apply(rule conjI)
      using pair_in_M_iff assms transM 
       apply force
      apply(rule prelI)
      unfolding Rrel_def p_def
      using assms 
      by auto
    then have "c \<in> preds(R, x) \<union> {x}" using bcH unfolding preds_rel_def by auto 
    then have H2:"\<langle>c, a\<rangle> \<in> preds(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>) \<or> c = x"
      apply auto[1]
      unfolding preds_def
      apply simp
      apply(rule conjI)
      using pair_in_M_iff assms transM 
       apply force
      apply(rule prelI)
      unfolding Rrel_def 
      using assms p_def
      by auto      

    have H3 : "<b, c> \<in> Rrel(R, M)" 
      unfolding Rrel_def 
      apply simp
      using bcH pair_in_M_iff assms
      unfolding preds_rel_def preds_def 
      by auto

    have "<<b, a>, <c, a>> \<in> preds_rel(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>)" 
      unfolding preds_rel_def 
      using H1 H2 
      apply simp
      apply(rule prelI)
      using H3 assms p_def
      by auto

    then show "s \<in> preds_rel(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>)" using bcH by auto 
  next 
    fix s assume "s \<in> preds_rel(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>)" 
    then obtain ba ca where bacaH:
      "s = <ba, ca>" 
      "<ba, ca> \<in> prel(Rrel(R, M), p)" 
      "ba \<in> preds(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>)" 
      "ca \<in> (preds(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>) \<union> {\<langle>x, a\<rangle>})" 
      unfolding preds_rel_def by auto
    
    obtain b where baeq: "ba = <b, a>" using bacaH unfolding preds_def prel_def by auto
    obtain c where caeq: "ca = <c, a>" using bacaH unfolding preds_def prel_def by auto 

    have "ba \<in> M" using bacaH unfolding preds_def prel_def by auto 
    then have binM : "b \<in> M" using baeq pair_in_M_iff by auto 
    have "ca \<in> M" using bacaH assms transM pair_in_M_iff unfolding preds_def prel_def by auto 
    then have cinM : "c \<in> M" using caeq pair_in_M_iff by auto 

    have bin : "b \<in> preds(R, x)" 
      unfolding preds_def 
      apply (simp add:binM)
      using bacaH baeq 
      unfolding preds_def prel_def Rrel_def 
      by force
      
    have cin : "c \<in> preds(R, x) \<or> c = x" 
      unfolding preds_def 
      apply (simp add:cinM)
      using bacaH caeq 
      unfolding preds_def prel_def Rrel_def 
      by force

    have "<<b, a>, <c, a>> \<in> prel(preds_rel(R, x), {a})" 
      apply(rule prelI)
      unfolding preds_rel_def 
       apply (simp add:bin cin)
      using bacaH baeq caeq 
      unfolding prel_def Rrel_def 
      by auto 
    then show "s \<in> prel(preds_rel(R, x), {a})" using bacaH baeq caeq by auto 
  qed

  have I1: "sats(M, is_wftrec_fm(Gfm, Rfm, i, j, k), env) \<longleftrightarrow> (\<exists>xa \<in> M. \<exists>S \<in> M. S = preds_rel(\<lambda>a b. \<langle>a, b\<rangle> \<in> prel(Rrel(R, M), p), \<langle>x, a\<rangle>) \<and> xa = <x, a> \<and> v = wftrec(S, xa, G))" 
    unfolding is_wftrec_fm_def

    apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)
    apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_lemma1)
     apply(rule sats_is_preds_prel_fm_iff)
    using assms inat jnat knat xinM ainp pinM
                  apply simp_all
    apply(rule iff_lemma1, simp, rule sats_is_wfrec_fm_iff)
    using assms inat jnat knat xinM ainM vinM 
                      apply simp_all
     apply(rule wf_preds_rel)
    using pair_in_M_iff 
      apply simp
     apply(subst eq1, rule wf_prel, simp add:assms)
    apply(rule trans_preds_rel)
    using pair_in_M_iff 
      apply simp
     apply(subst eq1, rule prel_trans, simp add:assms)
    done    

  have I2: "... \<longleftrightarrow> v = wftrec(preds_rel(\<lambda>a b. <a, b> \<in> prel(Rrel(R, M), p), <x, a>), <x, a>, G)" 
    apply(rule iffI, simp, simp)
    apply(rule conjI, rule preds_prel_in_M)
    using assms pair_in_M_iff xinM ainM pinM ainp
    by auto

  have I3: "... \<longleftrightarrow> v = wftrec(prel(preds_rel(R, x), {a}), <x, a>, G)" using eq2 by auto 

  have I4: "... \<longleftrightarrow>  v = wftrec(Rrel(R, M), x, H)"  
    apply(rule iff_lemma2, rule_tac Gfm=Gfm in wftrec_prel_preds_rel_eq)
    using assms 
    by auto
  show ?thesis using I1 I2 I3 I4 by auto
qed

lemma function_the_recfun : 
  assumes "wf(r)" "trans(r)" 
  shows"function(the_recfun(r, x, H))"
  (is "function(?f)")
proof- 
  have "is_recfun(r, x, H, ?f)"
    using unfold_the_recfun assms
    by auto
  then have eq:  "?f = (\<lambda>y\<in>r-``{x}. H(y, restrict(?f, r-``{y})))" (is "?f = ?g")
    using is_recfun_def
    by auto
  have "function(?g)" using function_lam by auto
  then show ?thesis using eq by auto
qed

lemma Rrel_wftrec_in_M : 
  fixes R Rfm G H x a
  assumes "x \<in> M" "a \<in> M" "x \<in> field(Rrel(R, M))" "wf(Rrel(R, M))" "trans(Rrel(R, M))"
          "Relation_fm(R, Rfm)" "preds(R, x) \<in> M"  "Gfm \<in> formula" "arity(Gfm) \<le> 3" 
          "\<And>a0 a1 a2 env. a0 \<in> M \<Longrightarrow> a1 \<in> M \<Longrightarrow> a2 \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> a0 = G(a2, a1) \<longleftrightarrow> sats(M, Gfm, [a0, a1, a2] @ env)" 
  and GM: "\<And>x g. x \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> G(x, g) \<in> M"  
  and HGeq: "\<And>h g x. h \<in> Rrel(R, M) -`` {x} \<rightarrow> M \<Longrightarrow> g \<in> (Rrel(R, M) -`` {x} \<times> {a}) \<rightarrow> M \<Longrightarrow> g \<in> M  
               \<Longrightarrow> x \<in> field(Rrel(R, M)) \<Longrightarrow> (\<And>y. y \<in> Rrel(R, M) -`` {x} \<Longrightarrow> h`y = g`<y, a>) \<Longrightarrow> H(x, h) = G(<x, a>, g)"  
  and "preds_rel_sep_fm(Rfm) \<in> \<Phi>" "rep_for_recfun_fm(Gfm, 0, 1, 2) \<in> \<Phi>" "rep_for_recfun_fm(Gfm, 0, 1, 2) \<in> \<Phi>" 
  shows "wftrec(Rrel(R, M), x, H) \<in> M"

  apply(rule_tac b="wftrec(Rrel(R, M), x, H)" in ssubst) 
   apply(rule eq_flip, rule_tac G=G and a=a in wftrec_prel_preds_rel_eq) 
  using assms 
              apply auto[14]
  unfolding wftrec_def
   apply(rule GM)
  using pair_in_M_iff assms
    apply force
   apply(rule_tac p=Gfm in the_recfun_in_M)
           apply(rule wf_prel, rule wf_preds_rel)
  using assms
            apply auto[2]
          apply(rule prel_trans, rule trans_preds_rel)
  using assms
          apply auto[2]
        apply(rule prel_closed, rule_tac Rfm=Rfm in preds_rel_in_M)
  using assms singleton_in_M_iff pair_in_M_iff
           apply auto[9]
  apply(rule_tac a="(\<lambda>y\<in>prel(preds_rel(R, x), {a}) -`` {\<langle>x, a\<rangle>}. G(y, restrict(the_recfun(prel(preds_rel(R, x), {a}), \<langle>x, a\<rangle>, G), prel(preds_rel(R, x), {a}) -`` {y})))"
             and b = "the_recfun(prel(preds_rel(R, x), {a}), \<langle>x, a\<rangle>, G)" in ssubst) 
   apply(subgoal_tac "is_recfun(prel(preds_rel(R, x), {a}), <x, a>, G, the_recfun(prel(preds_rel(R, x), {a}), \<langle>x, a\<rangle>, G))") 
    apply (simp add:is_recfun_def)
   apply(rule unfold_the_recfun)
      apply(rule wf_prel, rule wf_preds_rel)
  using assms
       apply auto[2]
     apply(rule prel_trans, rule trans_preds_rel)
  using assms
      apply auto[4]
  apply(rule function_the_recfun)
      apply(rule wf_prel, rule wf_preds_rel)
  using assms
       apply auto[2]
     apply(rule prel_trans, rule trans_preds_rel)
  using assms
      apply auto[2]
  done              

end
end





































