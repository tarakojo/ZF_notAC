theory Automorphism_M
  imports 
    "Forcing/Forcing_Main" 
    P_Names_M
    Automorphism_Definition
begin 


context forcing_data_partial 
begin 

schematic_goal is_P_auto_fm_auto:
  assumes
    "nth(0,env) = \<pi>" 
    "nth(1,env) = P" 
    "nth(2,env) = leq"  
    "env \<in> list(M)"
 shows 
    "(bijection(##M, P, P, \<pi>) \<and> 
      (\<forall>p \<in> M. \<forall>q \<in> M. \<forall>p_q \<in> M. \<forall>\<pi>p \<in> M. \<forall>\<pi>q \<in> M. \<forall>\<pi>p_\<pi>q \<in> M. 
        p \<in> P \<longrightarrow> q \<in> P \<longrightarrow> fun_apply(##M, \<pi>, p, \<pi>p) \<longrightarrow> fun_apply(##M, \<pi>, q, \<pi>q) \<longrightarrow>
        pair(##M, p, q, p_q) \<longrightarrow> pair(##M, \<pi>p, \<pi>q, \<pi>p_\<pi>q) \<longrightarrow> (p_q \<in> leq  \<longleftrightarrow> \<pi>p_\<pi>q \<in> leq)))
     \<longleftrightarrow> sats(M,?fm(0,1,2),env)"
  by (insert assms ; (rule sep_rules | simp)+)

definition is_P_auto_fm where 
  "is_P_auto_fm \<equiv>  
          And(bijection_fm(1, 1, 0),
                Forall
                 (Forall
                   (Forall
                     (Forall
                       (Forall
                         (Forall
                           (Implies
                             (Member(5, 7),
                              Implies
                               (Member(4, 7),
                                Implies
                                 (fun_apply_fm(6, 5, 2),
                                  Implies
                                   (fun_apply_fm(6, 4, 1),
                                    Implies(pair_fm(5, 4, 3), Implies(pair_fm(2, 1, 0), Iff(Member(3, 8), Member(0, 8)))))))))))))))  " 

lemma is_P_auto_fm_sats_iff : 
  "\<pi> \<in> M \<Longrightarrow> sats(M, is_P_auto_fm, [\<pi>, P, leq]) \<longleftrightarrow> is_P_auto(\<pi>)" 

  unfolding is_P_auto_def
  apply(rule_tac Q="bijection(##M, P, P, \<pi>) \<and> (\<forall>p \<in> M. \<forall>q \<in> M. \<forall>p_q \<in> M. \<forall>\<pi>p \<in> M. \<forall>\<pi>q \<in> M. \<forall>\<pi>p_\<pi>q \<in> M. 
        p \<in> P \<longrightarrow> q \<in> P \<longrightarrow> fun_apply(##M, \<pi>, p, \<pi>p) \<longrightarrow> fun_apply(##M, \<pi>, q, \<pi>q) \<longrightarrow>
        pair(##M, p, q, p_q) \<longrightarrow> pair(##M, \<pi>p, \<pi>q, \<pi>p_\<pi>q) \<longrightarrow> (p_q \<in> leq  \<longleftrightarrow> \<pi>p_\<pi>q \<in> leq))" in iff_trans) 
  apply(rule iff_flip) unfolding is_P_auto_fm_def apply(rule_tac is_P_auto_fm_auto) 
  using P_in_M leq_in_M apply simp_all apply(rule_tac iffI) apply clarify 
  apply(rename_tac p q)
  apply(rule_tac P="\<pi> ` p \<in> M" in mp) apply(rule_tac P="\<pi> ` q \<in> M" in mp) apply clarify 
  using pair_in_M_iff P_in_M transM apply auto using apply_closed by auto

lemma P_auto_in_M : "P_auto \<in> M" 
proof - 
  have "separation(##M, \<lambda>\<pi>. sats(M, is_P_auto_fm, [\<pi>]@[P, leq]))" 
    apply(rule_tac separation_ax) unfolding is_P_auto_fm_def
    using P_in_M leq_in_M apply simp_all 
    unfolding bijection_fm_def injection_fm_def surjection_fm_def 
    by (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)  
  then have "separation(##M, \<lambda>\<pi>. is_P_auto(\<pi>))"
    apply(rule_tac P="separation(##M, \<lambda>\<pi>. sats(M, is_P_auto_fm, [\<pi>]@[P, leq]))" in iffD1)
    apply(rule_tac separation_cong) using is_P_auto_fm_sats_iff by auto
  then have "{ \<pi> \<in> Pow(P \<times> P) \<inter> M. is_P_auto(\<pi>) } \<in> M" 
    apply(rule_tac separation_notation) apply simp 
    apply(rule_tac M_powerset) using P_in_M cartprod_closed by auto 
  then show "P_auto \<in> M" 
    apply(rule_tac b=P_auto and a = "{ \<pi> \<in> Pow(P \<times> P) \<inter> M. is_P_auto(\<pi>) } " in ssubst) 
    apply(rule equality_iffI; rule iffI) unfolding P_auto_def apply auto 
    using Pi_iff apply force using P_auto_type apply auto unfolding is_P_auto_def by auto
qed

definition HPn_auto_M_cond where 
  "HPn_auto_M_cond(x_pi, g, elem) \<equiv> 
     (\<exists>g_app_y_pi \<in> M. \<exists>pi_app_p \<in> M. \<exists>y_p \<in> M. \<exists>y_pi \<in> M. 
       \<exists>y \<in> M. \<exists>p \<in> M. \<exists>x \<in> M. \<exists>pi \<in> M. 
        pair(##M, g_app_y_pi, pi_app_p, elem) \<and> 
        pair(##M, x, pi, x_pi) \<and> 
        pair(##M, y, pi, y_pi) \<and> 
        pair(##M, y, p, y_p) \<and> 
        y_p \<in> x \<and> 
        is_function(##M, pi) \<and>
        fun_apply(##M, pi, p, pi_app_p) \<and> 
        fun_apply(##M, g, y_pi, g_app_y_pi)
     )"

lemma HPn_auto_M_cond_iff : 
  "x_pi \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> elem \<in> M \<Longrightarrow> 
    HPn_auto_M_cond(x_pi, g, elem) \<longleftrightarrow> 
      (\<exists>y \<in> M. \<exists>p \<in> M. \<exists>x \<in> M. \<exists>pi \<in> M. 
        x_pi = <x, pi> \<and>
        elem = <g`<y,pi>, pi`p> \<and> 
        <y, p> \<in> x \<and> 
        function(pi)
     )"
  apply (rule iffI)
proof -
  assume "HPn_auto_M_cond(x_pi, g, elem)"
  and inM : "x_pi \<in> M" "g \<in> M" "elem \<in> M"
  then obtain g_app_y_pi pi_app_p y_p y_pi y p x pi where 
      H : 
        "g_app_y_pi \<in> M" "pi_app_p \<in> M" "y_p \<in> M" "y_pi \<in> M" 
        "pair(##M, g_app_y_pi, pi_app_p, elem)"
        "pair(##M, x, pi, x_pi)" 
        "pair(##M, y, pi, y_pi)" 
        "pair(##M, y, p, y_p)" 
        "y_p \<in> x" 
        "is_function(##M, pi)"
        "fun_apply(##M, pi, p, pi_app_p)" 
        "fun_apply(##M, g, y_pi, g_app_y_pi)"
    unfolding HPn_auto_M_cond_def by blast
  have elemeq: "elem = <g_app_y_pi, pi_app_p>" using H pair_abs inM by auto 
  have x_pi_eq :"x_pi = <x, pi>" using H pair_abs inM by auto
  have y_pi_eq : "y_pi = <y, pi>" using H pair_abs inM by auto
  have y_p_eq : "y_p = <y, p>" using H pair_abs inM by auto
  have xin : "x \<in> M" using x_pi_eq inM pair_in_M_iff by auto 
  have yin : "y \<in> M" using y_pi_eq H pair_in_M_iff by auto 
  have pin : "p \<in> M" using y_pi_eq H pair_in_M_iff by auto 
  have piin : "pi \<in> M" using y_pi_eq H pair_in_M_iff by auto 
  have pifun : "function(pi)" using function_abs piin H by auto 
  have pi_app_p_val : "pi`p = pi_app_p" using apply_abs piin pin H by auto
  have g_app_val : "g`<y,pi> = g_app_y_pi"    
    apply (rule_tac P="fun_apply(##M, g, y_pi, g_app_y_pi)" in iffD1)
    apply (rule_tac Q="g`y_pi=g_app_y_pi" in iff_trans)
    apply (rule_tac apply_abs) using H inM by auto
  show "(\<exists>y \<in> M. \<exists>p \<in> M. \<exists>x \<in> M. \<exists>pi \<in> M. 
        x_pi = <x, pi> \<and>
        elem = <g`<y,pi>, pi`p> \<and> 
        <y, p> \<in> x \<and> 
        function(pi)
     )"
    apply (rule_tac x=y in bexI)  apply (rule_tac x=p in bexI) 
    apply (rule_tac x=x in bexI)  apply (rule_tac x=pi in bexI)
    using g_app_val pi_app_p_val H elemeq pifun piin xin pin yin y_p_eq H x_pi_eq by auto
next 
  assume "\<exists>y\<in>M. \<exists>p\<in>M. \<exists>x\<in>M. \<exists>pi\<in>M. 
      x_pi = <x, pi> \<and> elem = \<langle>g ` \<langle>y, pi\<rangle>, pi ` p\<rangle> \<and> \<langle>y, p\<rangle> \<in> x \<and> function(pi)"
  and inM : "x_pi \<in> M" "g \<in> M" "elem \<in> M"

  then obtain y p x pi where H : 
    "y \<in> M" "p \<in> M" "x \<in> M" "pi \<in> M" 
    "x_pi = <x, pi>" "elem = \<langle>g ` \<langle>y, pi\<rangle>, pi ` p\<rangle>" "\<langle>y, p\<rangle> \<in> x" "function(pi)"
    by auto 

  show "HPn_auto_M_cond(x_pi, g, elem)"
    unfolding HPn_auto_M_cond_def 
    apply (rule_tac x="g`<y, pi>" in bexI) 
    apply (rule_tac x="pi`p" in bexI) 
    apply (rule_tac x="<y,p>" in bexI) 
    apply (rule_tac x="<y,pi>" in bexI) 
    apply (rule_tac x="y" in bexI) 
    apply (rule_tac x="p" in bexI) 
    apply (rule_tac x="x" in bexI) 
    apply (rule_tac x="pi" in bexI) 
    using inM pair_in_M_iff H by simp_all
qed

lemma HPn_auto_M_cond_elem_in : 
  "x_pi \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> 
   \<exists>A \<in> M. \<forall> elem \<in> M. HPn_auto_M_cond(x_pi, g, elem) \<longrightarrow> elem \<in> A" 
  apply (rule_tac x="MVset(succ(rank(g))) \<times> MVset(succ(rank(x_pi)))" in bexI) 
proof (clarify) 
  fix elem 
  assume inM : "x_pi \<in> M" "g \<in> M" "elem \<in> M" 
  and gfun : "function(g)" 
  and cond : "HPn_auto_M_cond(x_pi, g, elem)" 

  then have " (\<exists>y \<in> M. \<exists>p \<in> M. \<exists>x \<in> M. \<exists>pi \<in> M. 
        x_pi = <x, pi> \<and>
        elem = <g`<y,pi>, pi`p> \<and> 
        <y, p> \<in> x \<and> 
        function(pi)
     )" using HPn_auto_M_cond_iff by auto 
  then obtain y p x pi where H : 
    "y \<in> M" "p \<in> M" "x \<in> M" "pi \<in> M" 
    "x_pi = <x, pi>" "elem = \<langle>g ` \<langle>y, pi\<rangle>, pi ` p\<rangle>" "\<langle>y, p\<rangle> \<in> x" "function(pi)"
     by auto 

   have P1: "g`<y, pi> \<in> MVset(succ(rank(g)))" 
     apply (rule_tac P="\<lambda>x. x \<in> MVset(succ(rank(g)))" and F=g and x="<y, pi>" in in_dom_or_not)
     using gfun apply simp 
     using zero_in_MVset Ord_rank apply simp 
   proof - 
     assume assm : "\<langle>y, pi\<rangle> \<in> domain(g)" 
     then obtain w where wh : "<<y, pi>, w> \<in> g" by auto 
     then have "<<y, pi>, w> \<in> M" using transM inM by auto
     then have winM : "w \<in> M" using pair_in_M_iff by auto 
     have weq : "g`<y, pi> = w" apply (rule_tac function_apply_equality) using wh gfun by auto
     then have "g`<y,pi> \<in> M" using winM by auto
     then show "g`<y, pi> \<in> MVset(succ(rank(g)))" 
       apply (rule_tac MVsetI; simp) 
       apply (rule lt_succ_lt) using Ord_rank apply simp 
       apply (rule_tac j="rank(<<y, pi>, w>)" in lt_trans)
       using weq rank_pair2 apply simp
       using wh rank_lt by simp
   qed

   have "pi ` p \<in> MVset(succ(rank(x_pi)))" 
     apply (rule_tac P="\<lambda>x. x \<in> MVset(succ(rank(x_pi)))" in in_dom_or_not) 
     using H apply simp
     using zero_in_MVset Ord_rank apply simp 
   proof - 
     assume "p \<in> domain(pi)" 
     then obtain w where wh : "<p, w> \<in> pi" by auto 
     then have weq : "pi`p = w" using function_apply_equality H by auto 
     have "<p, w> \<in> M" using transM wh H by auto 
     then have "w \<in> M" using pair_in_M_iff by auto 
     then show "pi ` p \<in> MVset(succ(rank(x_pi)))"
       apply (rule_tac MVsetI)
       using weq apply simp
       apply (rule_tac lt_succ_lt) using Ord_rank apply simp
       apply (rule_tac j="rank(pi)" in lt_trans) 
       apply (rule_tac P="\<lambda>x. rank(x) < rank(pi)" and a=w in ssubst)
       using weq apply simp
       apply (rule_tac j="rank(<p, w>)" in lt_trans)
       apply (rule_tac rank_pair2)
       using rank_lt wh apply simp 
       using H rank_pair2 by auto
   qed

   then show "elem \<in> MVset(succ(rank(g))) \<times> MVset(succ(rank(x_pi)))"
     using P1 H by auto 
 next
   assume "x_pi \<in> M" "g \<in> M"
   then have "(##M)(MVset(succ(rank(g))) \<times> MVset(succ(rank(x_pi))))" 
     apply (rule_tac cartprod_closed)
     apply simp_all 
     apply (rule_tac MVset_in_M) 
     using rank_closed Ord_rank succ_in_MI Ord_succ apply simp_all
     apply (rule_tac MVset_in_M) 
     using rank_closed Ord_rank succ_in_MI Ord_succ apply simp_all
     done
   then show "(MVset(succ(rank(g))) \<times> MVset(succ(rank(x_pi)))) \<in> M" by auto
 qed

schematic_goal HPn_auto_M_fm_auto:
  assumes
    "nth(0,env) = elem" 
    "nth(1,env) = x_pi" 
    "nth(2,env) = g"  
    "env \<in> list(M)"
 shows
    "HPn_auto_M_cond(x_pi, g, elem)
     \<longleftrightarrow> sats(M,?fm(0,1,2),env)"
  unfolding HPn_auto_M_cond_def
  by (insert assms ; (rule sep_rules | simp)+)

definition HPn_auto_M_fm where 
  "HPn_auto_M_fm =  Exists
             (Exists
               (Exists
                 (Exists
                   (Exists
                     (Exists
                       (Exists
                         (Exists
                           (And(pair_fm(7, 6, 8),
                                And(pair_fm(1, 0, 9),
                                    And
(pair_fm(3, 0, 4),
 And(pair_fm(3, 2, 5),
     And(Member(5, 1),
         And(function_fm(0),
             And(fun_apply_fm(0, 2, 6),
                 fun_apply_fm(10, 4, 7))))))))))))))))"

schematic_goal HPn_auto_M_fm'_auto:
  assumes
    "nth(0,env) = z" 
    "nth(1,env) = g" 
    "nth(2,env) = x_pi"  
    "env \<in> list(M)"
 shows
    "(\<forall>elem \<in> M. elem \<in> z \<longleftrightarrow> HPn_auto_M_cond(x_pi, g, elem))
     \<longleftrightarrow> sats(M,?fm(0,1,2),env)"
  unfolding HPn_auto_M_cond_def
  by (insert assms ; (rule sep_rules | simp)+)

definition HPn_auto_M_fm' where 
  "HPn_auto_M_fm' \<equiv> 
  Forall
             (Iff(Member(0, 1),
                  Exists
                   (Exists
                     (Exists
                       (Exists
                         (Exists
                           (Exists
                             (Exists
                               (Exists
                                 (And(pair_fm(7, 6, 8),
                                      And(pair_fm(1, 0, 11),
                                          And(pair_fm(3, 0, 4),
                                              And(pair_fm(3, 2, 5),
 And(Member(5, 1),
     And(function_fm(0), And(fun_apply_fm(0, 2, 6), fun_apply_fm(10, 4, 7)))))))))))))))))) " 

definition HPn_auto_M where 
  "HPn_auto_M(x_pi, g) \<equiv> { elem \<in> M. HPn_auto_M_cond(x_pi, g, elem) }"

lemma HPn_auto_M_fm_sats_iff : 
  "elem \<in> M \<Longrightarrow> x_pi \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> 
  sats(M, HPn_auto_M_fm, [elem, x_pi, g]) \<longleftrightarrow> HPn_auto_M_cond(x_pi, g, elem)" 
  apply (rule iff_flip) 
  unfolding HPn_auto_M_fm_def apply (rule_tac HPn_auto_M_fm_auto)
  by auto

lemma HPn_auto_M_fm'_sats_iff : 
  "x_pi \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> z \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> 
  sats(M, HPn_auto_M_fm', [z, g, x_pi] @ env) \<longleftrightarrow> z = HPn_auto_M(x_pi, g)" 
  apply (rule_tac Q="\<forall>elem \<in> M. elem \<in> z \<longleftrightarrow> HPn_auto_M_cond(x_pi, g, elem)" in iff_trans) 
  apply (rule iff_flip) 
  unfolding HPn_auto_M_fm'_def apply (rule_tac HPn_auto_M_fm'_auto)
  apply simp_all unfolding HPn_auto_M_def using transM by auto

lemma HPn_auto_M_in_M : 
  "\<And>x_pi g. x_pi \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> function(g) \<Longrightarrow> HPn_auto_M(x_pi, g) \<in> M" 
proof - 
  fix x_pi g 
  assume assms : "x_pi \<in> M" "g \<in> M" "function(g)" 

  then have "\<exists>A\<in>M. \<forall>elem\<in>M. HPn_auto_M_cond(x_pi, g, elem) \<longrightarrow> elem \<in> A" 
   using HPn_auto_M_cond_elem_in by auto
  then obtain A where Ah: "A \<in> M" "\<forall> elem \<in> M. HPn_auto_M_cond(x_pi, g, elem) \<longrightarrow> elem \<in> A" by auto

  define S where "S \<equiv> { elem \<in> A. sats(M, HPn_auto_M_fm, [elem] @ [x_pi, g]) }" 

  have "separation(##M, \<lambda>elem . sats(M, HPn_auto_M_fm, [elem] @ [x_pi, g]))" 
    apply (rule_tac separation_ax) 
    apply (simp add : HPn_auto_M_fm_def) 
    apply (simp add : assms) 
    unfolding HPn_auto_M_fm_def apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union) 
    done 
  then have sinM : "S \<in> M" 
    unfolding S_def apply (rule_tac separation_notation) using Ah by auto
  
  have "S = { elem \<in> A. HPn_auto_M_cond(x_pi, g, elem) }" 
    using HPn_auto_M_fm_sats_iff assms Ah transM Ah unfolding S_def by simp 
  also have "... = {  elem \<in> M. HPn_auto_M_cond(x_pi, g, elem) }" 
    apply (rule equality_iffI; rule iffI)
    using transM Ah by auto 
  also have "... = HPn_auto_M(x_pi, g)" 
    unfolding HPn_auto_M_def by simp 
  finally have "S = HPn_auto_M(x_pi, g)"  by simp

  then show "HPn_auto_M(x_pi, g) \<in> M" 
    using sinM by simp 
qed

definition Pn_auto_M where "Pn_auto_M(a) \<equiv> { <x_pi, wftrec(prel(edrel(MVset(a))^+, P_auto), x_pi, HPn_auto_M)> . x_pi \<in> MVset(a) \<times> P_auto }" 

lemma Pn_auto_M_in_M : "Ord(a) \<Longrightarrow> a \<in> M \<Longrightarrow> Pn_auto_M(a) \<in> M"
  unfolding Pn_auto_M_def apply(rule_tac p=HPn_auto_M_fm' in recfun_in_M) apply(rule_tac prel_closed) apply(rule_tac to_rin) 
  apply(rule_tac trancl_closed) apply simp apply(rule_tac edrel_closed) 
  unfolding Transset_def using MVset_trans apply blast apply(rule_tac MVset_in_M) apply simp apply simp 
  using P_auto_in_M apply simp apply(rule_tac wf_prel; rule_tac wf_trancl; rule_tac wf_edrel) 
  apply(rule_tac prel_trans; rule_tac trans_trancl) using MVset_in_M P_auto_in_M cartprod_closed apply simp 
  apply(simp add: HPn_auto_M_fm'_def) apply (simp add: HPn_auto_M_fm'_def)
  apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union) apply(rule iff_flip) apply(rule_tac HPn_auto_M_fm'_sats_iff)
  apply simp_all apply(rule_tac HPn_auto_M_in_M) by auto 


lemma Pn_auto_M: 
  "a \<in> M \<Longrightarrow> Ord(a) \<Longrightarrow> \<pi> \<in> P_auto \<Longrightarrow> x \<in> P_names \<inter> MVset(a) \<Longrightarrow>
   Pn_auto_M(a)`<x, \<pi>> = { <Pn_auto_M(a)`<y, \<pi>>, \<pi>`p>. <y, p> \<in> x }"   
proof - 
  assume assms : "a \<in> M" "Ord(a)" "\<pi> \<in> P_auto" "x \<in> P_names \<inter> MVset(a)"

  define R where "R \<equiv> prel(edrel(MVset(a))^+, P_auto)" 
  have wfR : "wf(R)" 
    unfolding R_def apply(rule_tac wf_prel; rule_tac wf_trancl; rule_tac wf_edrel) done 
  have transR : "trans(R)" 
    unfolding R_def apply(rule_tac prel_trans) using trans_trancl by auto

  have inM: "x \<in> M \<and> \<pi> \<in> M" 
    using assms unfolding P_auto_def is_P_auto_def P_names_def by simp 

  have recfuninM : "the_recfun(R, \<langle>x, \<pi>\<rangle>, HPn_auto_M) \<in> M" 
    apply(rule_tac p=HPn_auto_M_fm' in the_recfun_in_M) using wfR apply simp using transR apply simp 
    unfolding R_def apply(rule_tac prel_closed; rule_tac to_rin) apply(rule_tac trancl_closed) apply simp apply(rule_tac edrel_closed) 
    unfolding Transset_def using MVset_trans assms apply blast using MVset_in_M assms apply simp
    using P_auto_in_M apply simp  apply(simp add: HPn_auto_M_fm'_def) apply (simp add: HPn_auto_M_fm'_def)
    apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union) using pair_in_M_iff inM apply simp  
    using assms P_names_in_M unfolding P_auto_def is_P_auto_def apply simp 
    using HPn_auto_M_in_M apply simp apply (rule iff_flip) apply(rule_tac HPn_auto_M_fm'_sats_iff) by auto 

  have H : "\<And>y p. <y, p> \<in> x \<Longrightarrow> Pn_auto_M(a)`<y, \<pi>> = the_recfun(R, \<langle>x, \<pi>\<rangle>, HPn_auto_M) ` \<langle>y, \<pi>\<rangle>" 
  proof - 
    fix y p assume assm1: "<y, p> \<in> x" 

    have yin : "y \<in> MVset(a)" using MVset_domain assm1 assms by auto

    have rel : "<<y, \<pi>>, <x, \<pi>>> \<in> R" 
      unfolding R_def apply(rule_tac prelI) apply(rule_tac r_into_trancl) unfolding edrel_def Rrel_def ed_def using assms assm1 yin apply auto done 

    have "the_recfun(R, \<langle>x, \<pi>\<rangle>, HPn_auto_M) ` \<langle>y, \<pi>\<rangle> = (\<lambda>v\<in>R -`` {<x, \<pi>>}. HPn_auto_M(v, restrict(the_recfun(R, \<langle>x, \<pi>\<rangle>, HPn_auto_M), R -`` {v}))) ` <y, \<pi>>" 
      apply(rule_tac P="is_recfun(R, <x, \<pi>>, HPn_auto_M, the_recfun(R, \<langle>x, \<pi>\<rangle>, HPn_auto_M))" in mp) 
      apply(simp add:is_recfun_def) apply(rule_tac unfold_the_recfun) using wfR transR by auto 
    also have "... = HPn_auto_M(<y, \<pi>>, restrict(the_recfun(R, \<langle>x, \<pi>\<rangle>, HPn_auto_M), R -`` {<y, \<pi>>}))" 
      apply(rule_tac P="<y, \<pi>> \<in> R -`` {<x, \<pi>>}" in mp) apply simp apply(rule_tac b="<x, \<pi>>" in vimageI) using rel by auto
    also have "... = HPn_auto_M(<y, \<pi>>, the_recfun(R, <y, \<pi>>, HPn_auto_M))" 
      apply(rule_tac b="restrict(the_recfun(R, \<langle>x, \<pi>\<rangle>, HPn_auto_M), R -`` {<y, \<pi>>})" and a="the_recfun(R, <y, \<pi>>, HPn_auto_M)" in ssubst) 
      apply(rule_tac the_recfun_cut) using wfR transR rel apply simp_all done 
    also have "... = Pn_auto_M(a)`<y, \<pi>>" 
      unfolding R_def apply(rule eq_flip) 
      apply(rule_tac function_apply_equality) using assms unfolding Pn_auto_M_def function_def apply auto unfolding wftrec_def using yin by simp_all
    finally show "Pn_auto_M(a) ` \<langle>y, \<pi>\<rangle> = the_recfun(R, \<langle>x, \<pi>\<rangle>, HPn_auto_M) ` \<langle>y, \<pi>\<rangle>" by simp
  qed

  have "Pn_auto_M(a)`<x, \<pi>> = { elem \<in> M. HPn_auto_M_cond(<x, \<pi>>, the_recfun(R, <x, \<pi>>, HPn_auto_M), elem) }"  
    apply(rule_tac function_apply_equality) unfolding Pn_auto_M_def R_def function_def wftrec_def HPn_auto_M_def using assms by auto
  also have "... = { elem \<in> M. (\<exists>y \<in> M. \<exists>p \<in> M. \<exists>xx \<in> M. \<exists>pi \<in> M. 
                                <x, \<pi>> = <xx, pi> \<and> elem = <the_recfun(R, <x, \<pi>>, HPn_auto_M)`<y,pi>, pi`p> \<and>  <y, p> \<in> xx \<and> function(pi)) }"
    apply(rule_tac iff_eq) apply(rule_tac HPn_auto_M_cond_iff) using pair_in_M_iff inM apply simp using recfuninM by auto
  also have "... = { elem \<in> M. (\<exists>y \<in> M. \<exists>p \<in> M. elem = <the_recfun(R, <x, \<pi>>, HPn_auto_M)`<y,\<pi>>, \<pi>`p> \<and>  <y, p> \<in> x) }" 
    apply(rule_tac P="function(\<pi>)" in mp) apply clarify
    apply(rule_tac iff_eq) using assms inM apply auto
    using assms unfolding P_auto_def is_P_auto_def Pi_def apply auto done 
  also have "... = { <the_recfun(R, <x, \<pi>>, HPn_auto_M)`<y,\<pi>>, \<pi>`p> .  <y, p> \<in> x }"
    apply(rule equality_iffI; rule iffI) apply force
  proof - 
    fix v assume assm1: "v \<in> {\<langle>the_recfun(R, \<langle>x, \<pi>\<rangle>, HPn_auto_M) ` \<langle>y, \<pi>\<rangle>, \<pi> ` p\<rangle> . \<langle>y,p\<rangle> \<in> x}"
    then obtain y p where ypH: "v = \<langle>the_recfun(R, \<langle>x, \<pi>\<rangle>, HPn_auto_M) ` \<langle>y, \<pi>\<rangle>, \<pi> ` p\<rangle>" "<y, p> \<in> x"
      using relation_P_name assms unfolding relation_def by force 
    then show "v \<in> {v \<in> M . \<exists>y\<in>M. \<exists>p\<in>M. v = \<langle>the_recfun(R, \<langle>x, \<pi>\<rangle>, HPn_auto_M) ` \<langle>y, \<pi>\<rangle>, \<pi> ` p\<rangle> \<and> \<langle>y, p\<rangle> \<in> x}" 
      apply auto using pair_in_M_iff apply auto apply(rule_tac to_rin; rule_tac apply_closed) 
      using recfuninM apply simp apply auto apply(rule_tac x=x in domain_elem_in_M) using assms P_names_in_M apply simp apply simp
      using assms unfolding P_auto_def is_P_auto_def apply simp 
      apply(rule_tac P="\<pi>`p \<in> P" in mp) using transM P_in_M apply simp apply(rule_tac P_auto_value) 
      using assms unfolding P_auto_def apply simp apply(rule_tac x=x in P_name_range) using assms apply simp_all 
      apply(rule_tac x=y in bexI) apply simp apply(rule_tac x=p in bexI) 
      using inM pair_in_M_iff transM by auto
  qed
  also have "... = { <Pn_auto_M(a)`<y, \<pi>>, \<pi>`p>. <y, p> \<in> x }"   
    apply(rule_tac pair_rel_eq) using assms relation_P_name apply simp apply clarify 
    using H by auto 
  finally show "Pn_auto_M(a) ` \<langle>x, \<pi>\<rangle> = {\<langle>Pn_auto_M(a) ` \<langle>y, \<pi>\<rangle>, \<pi> ` p\<rangle> . \<langle>y,p\<rangle> \<in> x} " by auto 
qed

lemma Pn_auto_M_eq : 
  "a \<in> M \<Longrightarrow> Ord(a) \<Longrightarrow> \<pi> \<in> P_auto \<Longrightarrow> x \<in> MVset(a) \<inter> P_names \<Longrightarrow> Pn_auto_M(a)`<x, \<pi>> = Pn_auto(\<pi>)`x" 
  apply(rule_tac P=" x \<in> MVset(a) \<inter> P_names \<longrightarrow> Pn_auto_M(a)`<x, \<pi>> = Pn_auto(\<pi>)`x" in mp) apply simp
  apply(rule_tac Q="\<lambda>x. x \<in> MVset(a) \<inter> P_names \<longrightarrow> Pn_auto_M(a)`<x, \<pi>> = Pn_auto(\<pi>)`x" in ed_induction) 
proof (clarify)
  fix x assume assms: "a \<in> M" "Ord(a)" "\<pi> \<in> P_auto" "\<And>y. ed(y, x) \<Longrightarrow> y \<in> MVset(a) \<inter> P_names \<longrightarrow> Pn_auto_M(a) ` \<langle>y, \<pi>\<rangle> = Pn_auto(\<pi>) ` y" "x \<in> MVset(a)" "x \<in> P_names" 
  have "Pn_auto_M(a) ` \<langle>x, \<pi>\<rangle> = { <Pn_auto_M(a)`<y, \<pi>>, \<pi>`p>. <y, p> \<in> x }"   
    apply(rule_tac Pn_auto_M) using assms by auto 
  also have "... = { <Pn_auto(\<pi>) `y, \<pi>`p>. <y, p> \<in> x }"   
    apply(rule_tac pair_rel_eq) using assms relation_P_name apply simp apply clarify 
    apply(rule_tac P="ed(y, x) \<and> y \<in> MVset(a) \<inter> P_names" in mp) using assms apply simp 
    unfolding ed_def using assms P_name_domain_P_name MVset_domain apply auto done
  also have "... = Pn_auto(\<pi>)`x" 
    using Pn_auto assms by auto 
  finally show "Pn_auto_M(a) ` \<langle>x, \<pi>\<rangle> = Pn_auto(\<pi>) ` x" by auto 
qed

lemma Pn_auto_value_in_M : 
  "\<And>x. is_P_auto(\<pi>) \<Longrightarrow> x \<in> P_names \<Longrightarrow> Pn_auto(\<pi>)`x \<in> M" 
proof - 
  fix x assume assms : "is_P_auto(\<pi>)" "x \<in> P_names"
  have "x \<in> MVset(succ(rank(x)))"
    apply(rule_tac MVset_succ_rank_in) using P_names_in_M assms by auto 
  then have "x \<in> MVset(succ(rank(x))) \<inter> P_names" using assms by auto 
  then have H : "Pn_auto_M(succ(rank(x)))`<x, \<pi>> \<in> M" 
    apply(rule_tac to_rin; rule_tac apply_closed) apply simp apply(rule_tac Pn_auto_M_in_M) using Ord_rank apply simp 
    using succ_in_MI rank_closed assms P_names_in_M apply auto 
    using P_names_in_M pair_in_M_iff unfolding is_P_auto_def by auto
  then have "Pn_auto_M(succ(rank(x)))`<x, \<pi>> = Pn_auto(\<pi>) ` x " 
    apply(rule_tac Pn_auto_M_eq) using succ_in_MI rank_closed assms P_names_in_M unfolding P_auto_def apply auto 
    using P_auto_type apply simp apply(rule_tac MVsetI) using P_names_in_M le_refl by auto 
  then show "Pn_auto(\<pi>) ` x \<in> M" using H by auto
qed


end
end