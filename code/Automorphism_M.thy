theory Automorphism_M
  imports 
    Automorphism_Definition
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


locale forcing_data_Automorphism_M = forcing_data_partial + 
  assumes is_P_auto_fm : "is_P_auto_fm \<in> \<Phi>" 
  and HPn_auto_fm : "HPn_auto_fm \<in> \<Phi>" 
  and Automorphism_M_rep_for_recfun_fm : "rep_for_recfun_fm(HPn_auto_M_fm', 0, 1, 2) \<in> \<Phi>" 
begin 

lemma is_P_auto_fm_sats_iff : 
  "\<pi> \<in> M \<Longrightarrow> sats(M, is_P_auto_fm, [\<pi>, P, leq]) \<longleftrightarrow> is_P_auto(\<pi>)" 

  unfolding is_P_auto_def
  apply(rule_tac Q="bijection(##M, P, P, \<pi>) \<and> (\<forall>p \<in> M. \<forall>q \<in> M. \<forall>p_q \<in> M. \<forall>\<pi>p \<in> M. \<forall>\<pi>q \<in> M. \<forall>\<pi>p_\<pi>q \<in> M. 
        p \<in> P \<longrightarrow> q \<in> P \<longrightarrow> fun_apply(##M, \<pi>, p, \<pi>p) \<longrightarrow> fun_apply(##M, \<pi>, q, \<pi>q) \<longrightarrow>
        pair(##M, p, q, p_q) \<longrightarrow> pair(##M, \<pi>p, \<pi>q, \<pi>p_\<pi>q) \<longrightarrow> (p_q \<in> leq  \<longleftrightarrow> \<pi>p_\<pi>q \<in> leq))" in iff_trans) 
   apply(rule iff_flip) 
  unfolding is_P_auto_fm_def 
   apply(rule_tac is_P_auto_fm_auto) 
  using P_in_M leq_in_M 
      apply simp_all 
  apply(rule_tac iffI) 
   apply clarify 
  apply(rename_tac p q)
   apply(rule_tac P="\<pi> ` p \<in> M" in mp) 
    apply(rule_tac P="\<pi> ` q \<in> M" in mp) 
     apply clarify 
  using pair_in_M_iff P_in_M transM 
     apply auto 
  using apply_closed 
  by auto

lemma P_auto_in_M : "P_auto \<in> M" 
proof - 
  have "separation(##M, \<lambda>\<pi>. sats(M, is_P_auto_fm, [\<pi>]@[P, leq]))" 
    apply(rule_tac separation_ax) 
    using is_P_auto_fm
    unfolding is_P_auto_fm_def
    using P_in_M leq_in_M 
      apply simp_all 
    unfolding bijection_fm_def injection_fm_def surjection_fm_def 
    by (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)  
  then have "separation(##M, \<lambda>\<pi>. is_P_auto(\<pi>))"
    apply(rule_tac P="separation(##M, \<lambda>\<pi>. sats(M, is_P_auto_fm, [\<pi>]@[P, leq]))" in iffD1)
     apply(rule_tac separation_cong) 
    using is_P_auto_fm_sats_iff 
    by auto
  then have "{ \<pi> \<in> Pow(P \<times> P) \<inter> M. is_P_auto(\<pi>) } \<in> M" 
    apply(rule_tac separation_notation) 
     apply simp 
    apply(rule_tac M_powerset) 
    using P_in_M cartprod_closed 
    by auto 
  then show "P_auto \<in> M" 
    apply(rule_tac b=P_auto and a = "{ \<pi> \<in> Pow(P \<times> P) \<inter> M. is_P_auto(\<pi>) } " in ssubst) 
     apply(rule equality_iffI; rule iffI) 
    unfolding P_auto_def 
      apply auto 
    using Pi_iff 
      apply force 
    using P_auto_type 
     apply auto 
    unfolding is_P_auto_def 
    by auto
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
proof (rule iffI)
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
     using gfun 
       apply simp 
     using zero_in_MVset Ord_rank 
      apply simp 
   proof - 
     assume assm : "\<langle>y, pi\<rangle> \<in> domain(g)" 
     then obtain w where wh : "<<y, pi>, w> \<in> g" by auto 
     then have "<<y, pi>, w> \<in> M" using transM inM by auto
     then have winM : "w \<in> M" using pair_in_M_iff by auto 
     have weq : "g`<y, pi> = w" apply (rule_tac function_apply_equality) using wh gfun by auto
     then have "g`<y,pi> \<in> M" using winM by auto
     then show "g`<y, pi> \<in> MVset(succ(rank(g)))" 
       apply (rule_tac MVsetI; simp) 
       apply (rule lt_succ_lt) 
       using Ord_rank 
        apply simp 
       apply (rule_tac j="rank(<<y, pi>, w>)" in lt_trans)
       using weq rank_pair2 
        apply simp
       using wh rank_lt by simp
   qed

   have "pi ` p \<in> MVset(succ(rank(x_pi)))" 
     apply (rule_tac P="\<lambda>x. x \<in> MVset(succ(rank(x_pi)))" in in_dom_or_not) 
     using H 
       apply simp
     using zero_in_MVset Ord_rank
      apply simp 
   proof - 
     assume "p \<in> domain(pi)" 
     then obtain w where wh : "<p, w> \<in> pi" by auto 
     then have weq : "pi`p = w" using function_apply_equality H by auto 
     have "<p, w> \<in> M" using transM wh H by auto 
     then have "w \<in> M" using pair_in_M_iff by auto 
     then show "pi ` p \<in> MVset(succ(rank(x_pi)))"
       apply (rule_tac MVsetI)
       using weq 
        apply simp
       apply (rule_tac lt_succ_lt) 
       using Ord_rank 
        apply simp
       apply (rule_tac j="rank(pi)" in lt_trans) 
       apply (rule_tac P="\<lambda>x. rank(x) < rank(pi)" and a=w in ssubst)
       using weq 
         apply simp
       apply (rule_tac j="rank(<p, w>)" in lt_trans)
       apply (rule_tac rank_pair2)
       using rank_lt wh 
        apply simp 
       using H rank_pair2 
       by auto
   qed

   then show "elem \<in> MVset(succ(rank(g))) \<times> MVset(succ(rank(x_pi)))"
     using P1 H by auto 
 next
   assume "x_pi \<in> M" "g \<in> M"
   then have "(##M)(MVset(succ(rank(g))) \<times> MVset(succ(rank(x_pi))))" 
     apply (rule_tac cartprod_closed)
     apply simp_all 
     apply (rule_tac MVset_in_M) 
     using rank_closed Ord_rank succ_in_MI Ord_succ 
       apply simp_all
     apply (rule_tac MVset_in_M) 
     using rank_closed Ord_rank succ_in_MI Ord_succ 
      apply simp_all
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

end



context forcing_data_Automorphism_M
begin 

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

end

context forcing_data_Automorphism_M
begin 

definition HPn_auto_M where 
  "HPn_auto_M(x_pi, g) \<equiv> { elem \<in> M. HPn_auto_M_cond(x_pi, g, elem) }"

lemma HPn_auto_M_fm_sats_iff : 
  "elem \<in> M \<Longrightarrow> x_pi \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> 
  sats(M, HPn_auto_M_fm, [elem, x_pi, g]) \<longleftrightarrow> HPn_auto_M_cond(x_pi, g, elem)" 
  apply (rule iff_flip) 
  unfolding HPn_auto_M_fm_def 
  apply (rule_tac HPn_auto_M_fm_auto)
  by auto

lemma HPn_auto_M_fm'_sats_iff : 
  "x_pi \<in> M \<Longrightarrow> g \<in> M \<Longrightarrow> z \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> 
  sats(M, HPn_auto_M_fm', [z, g, x_pi] @ env) \<longleftrightarrow> z = HPn_auto_M(x_pi, g)" 
  apply (rule_tac Q="\<forall>elem \<in> M. elem \<in> z \<longleftrightarrow> HPn_auto_M_cond(x_pi, g, elem)" in iff_trans) 
  apply (rule iff_flip) 
  unfolding HPn_auto_M_fm'_def 
   apply (rule_tac HPn_auto_M_fm'_auto)
      apply simp_all 
  unfolding HPn_auto_M_def 
  using transM 
  by auto

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
    apply (simp add : HPn_auto_M_fm_def, simp add:HPn_auto_fm) 
    apply (simp add : assms) 
    unfolding HPn_auto_M_fm_def 
    apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union) 
    done 
  then have sinM : "S \<in> M" 
    unfolding S_def 
    apply (rule_tac separation_notation) 
    using Ah 
    by auto
  
  have "S = { elem \<in> A. HPn_auto_M_cond(x_pi, g, elem) }" 
    using HPn_auto_M_fm_sats_iff assms Ah transM Ah 
    unfolding S_def 
    by simp 
  also have "... = {  elem \<in> M. HPn_auto_M_cond(x_pi, g, elem) }" 
    apply (rule equality_iffI; rule iffI)
    using transM Ah 
    by auto 
  also have "... = HPn_auto_M(x_pi, g)" 
    unfolding HPn_auto_M_def by simp 
  finally have "S = HPn_auto_M(x_pi, g)"  by simp

  then show "HPn_auto_M(x_pi, g) \<in> M" 
    using sinM by simp 
qed

lemma HPn_auto_M_eq :  "\<And>h g x \<pi>. \<pi> \<in> P_auto \<Longrightarrow> h \<in> eclose(x) \<rightarrow> M \<Longrightarrow> g \<in> eclose(x) \<times> {\<pi>} \<rightarrow> M \<Longrightarrow> g \<in> M  
               \<Longrightarrow> x \<in> M \<Longrightarrow> (\<And>y. y \<in> eclose(x) \<Longrightarrow> h`y = g`<y, \<pi>>) \<Longrightarrow> HPn_auto(\<pi>, x, h) = HPn_auto_M(<x, \<pi>>, g)"
proof - 
  fix h g x \<pi>
  assume assms1 : "x \<in> M" "\<pi> \<in> P_auto" "h \<in> eclose(x) \<rightarrow> M" "g \<in> eclose(x) \<times> {\<pi>} \<rightarrow> M" "g \<in> M" 
    "(\<And>y. y \<in> eclose(x) \<Longrightarrow> h ` y = g ` \<langle>y, \<pi>\<rangle>)"

  have piinM : "\<pi> \<in> M" 
    using pair_in_M_iff assms1 P_auto_def is_P_auto_def 
    by auto  

  have "HPn_auto_M(<x, \<pi>>, g) \<in> M" 
    apply(rule HPn_auto_M_in_M)
    using assms1 pair_in_M_iff P_auto_def is_P_auto_def Pi_def
    by auto

  show "HPn_auto(\<pi>, x, h) = HPn_auto_M(<x, \<pi>>, g)" 
  proof(rule equality_iffI, rule iffI)
    fix u assume "u \<in> HPn_auto(\<pi>, x, h)" 
    then obtain y p where ueq : "u = <h`y, \<pi>`p>" and ypin : "<y, p> \<in> x" unfolding HPn_auto_def by auto
    have "y \<in> eclose(x)" 
      apply(rule domain_elem_in_eclose) 
      using ypin 
      by auto
    then have hyeq : "h`y = g`<y, \<pi>>" using assms1 by auto

    have yinM : "y \<in> M"
      apply(rule_tac x=x in domain_elem_in_M)
      using assms1 ypin 
      by auto

    have pinM : "p \<in> M" 
      apply(rule to_rin, rule_tac x="range(x)" in transM)
      using assms1 ypin range_closed 
      by auto

    have uinM : "u \<in> M" 
      apply(subst ueq)
      apply(subst hyeq)
      apply(rule to_rin, rule iffD2, rule pair_in_M_iff)
      apply(rule conjI, rule apply_closed)
      using assms1 pair_in_M_iff yinM piinM 
        apply auto[2]
      apply(rule apply_closed)
      using piinM pinM
      by auto

    have "HPn_auto_M_cond(<x, \<pi>>, g, <h`y, \<pi>`p>)" 
      apply(rule iffD2, rule HPn_auto_M_cond_iff)
      using assms1 piinM pair_in_M_iff 
         apply auto[2]
       apply(rule to_rin, rule iffD2, rule pair_in_M_iff, rule conjI, subst hyeq)
        apply(rule apply_closed)
      using assms1 yinM piinM pair_in_M_iff 
         apply auto[2]
       apply(rule apply_closed)
      using piinM pinM 
        apply auto[2]
      apply(rule_tac x=y in bexI, rule_tac x=p in bexI, rule_tac x=x in bexI, rule_tac x=\<pi> in bexI)
          apply(subst hyeq)
      using ypin
          apply simp
      using assms1 piinM yinM pinM
      unfolding P_auto_def Pi_def 
      by auto

    then show "u \<in> HPn_auto_M(<x, \<pi>>, g)"
      unfolding HPn_auto_M_def 
      using ueq uinM 
      by auto
  next 
    fix u assume "u \<in> HPn_auto_M(\<langle>x, \<pi>\<rangle>, g)" 
    then have uH: "u \<in> M" "HPn_auto_M_cond(<x, \<pi>>, g, u)" unfolding HPn_auto_M_def by auto 
    have "(\<exists>y \<in> M. \<exists>p \<in> M. \<exists>xx \<in> M. \<exists>pi \<in> M. 
      <x, \<pi>> = <xx, pi> \<and>
      u = <g`<y,pi>, pi`p> \<and> 
      <y, p> \<in> xx \<and> 
      function(pi)
    )" 
      apply(rule iffD1, rule_tac HPn_auto_M_cond_iff)
      using pair_in_M_iff assms1 piinM uH
      by auto
    then obtain y p where ueq : "u = <g`<y, \<pi>>, \<pi>`p>" and ypin : "<y, p> \<in> x" by auto 
    then show "u \<in> HPn_auto(\<pi>, x, h)" 
      unfolding HPn_auto_def
      apply simp
      apply(rule_tac x="<y, p>" in bexI)
       apply(subgoal_tac "y \<in> eclose(x)")
      using assms1 
        apply force
       apply(rule domain_elem_in_eclose)
      by auto
  qed
qed

end

definition is_Pn_auto_fm where "is_Pn_auto_fm(p, pi, x, v) \<equiv> And(is_P_name_fm(p, x), is_memrel_wftrec_fm(HPn_auto_M_fm', x, pi, v))" 


context forcing_data_Automorphism_M
begin 

lemma is_Pn_auto_fm_type : 
  fixes p pi x v 
  assumes "p \<in> nat" "pi \<in> nat" "x \<in> nat" "v \<in> nat" 
  shows "is_Pn_auto_fm(p, pi, x, v) \<in> formula" 
  unfolding is_Pn_auto_fm_def 
  apply(rule And_type, rule is_P_name_fm_type, simp add:assms, simp add:assms)
  apply(rule is_memrel_wftrec_fm_type) 
  unfolding HPn_auto_M_fm'_def 
  using assms
  by auto

lemma arity_is_Pn_auto_fm : 
  fixes p pi x v 
  assumes "p \<in> nat" "pi \<in> nat" "x \<in> nat" "v \<in> nat" 
  shows "arity(is_Pn_auto_fm(p, pi, x, v)) \<le> succ(p) \<union> succ(pi) \<union> succ(x) \<union> succ(v)"

  unfolding is_Pn_auto_fm_def 
  apply simp
  apply(rule Un_least_lt, rule le_trans, rule arity_is_P_name_fm)
  using assms 
     apply auto[2]
   apply(rule Un_least_lt, simp, rule ltI, simp, simp add:assms)
   apply(simp, rule ltI, simp, simp add:assms)
  apply(rule le_trans, rule arity_is_memrel_wftrec_fm)
  unfolding HPn_auto_M_fm'_def
  using assms 
       apply simp
      apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  using assms 
     apply auto[3]
  apply(rule Un_least_lt)+
    apply(simp, rule ltI, simp, simp add:assms)+
  done

lemma sats_is_Pn_auto_fm_iff :
  fixes x \<pi> v env i j k l
  assumes "i < length(env)" "j < length(env)" "k < length(env)" "l < length(env)" 
          "nth(i, env) = P" "nth(j, env) = \<pi>" "nth(k, env) = x" "nth(l, env) = v" 
          "env \<in> list(M)" "\<pi> \<in> P_auto" 
  shows "sats(M, is_Pn_auto_fm(i, j, k, l), env) \<longleftrightarrow> x \<in> P_names \<and> v = Pn_auto(\<pi>)`x" 
proof - 

  have piinM : "\<pi> \<in> M" 
    using pair_in_M_iff assms P_auto_def is_P_auto_def 
    by auto  

  have "sats(M, is_Pn_auto_fm(i, j, k, l), env) \<longleftrightarrow> x \<in> P_names \<and> v = wftrec(Memrel(M)^+, x, HPn_auto(\<pi>))"
    unfolding is_Pn_auto_fm_def 
    apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI)
     apply(rule sats_is_P_name_fm_iff)
    using assms 
         apply auto[5]
    apply(rule_tac a=\<pi> and G=HPn_auto_M in sats_is_memrel_wftrec_fm_iff)
    using assms P_auto_in_M
                  apply auto[10]
        apply(simp add:HPn_auto_M_fm'_def)+
    apply(subst arity_pair_fm, simp_all)+
    apply(subst arity_function_fm, simp_all)
    apply(subst arity_fun_apply_fm, simp_all)+
       apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union) 
      apply(rule HPn_auto_M_in_M)
        apply auto[3]
     apply(rule HPn_auto_M_eq)
    using assms 
            apply auto[6]
    apply(rule iff_trans, rule iff_flip)
      apply(rule HPn_auto_M_fm'_sats_iff)
    using Automorphism_M_rep_for_recfun_fm
    by auto
  also have "... \<longleftrightarrow> x \<in> P_names \<and> v = Pn_auto(\<pi>)`x" 
    apply(rule iff_conjI2, simp)
    unfolding Pn_auto_def 
    apply(subst function_apply_equality)
    unfolding function_def
    by auto 
  finally show ?thesis by simp
qed

lemma Pn_auto_value_in_M : 
  "\<And>x. is_P_auto(\<pi>) \<Longrightarrow> x \<in> P_names \<Longrightarrow> Pn_auto(\<pi>)`x \<in> M" 

  apply(rename_tac x, rule_tac b="Pn_auto(\<pi>)`x" and a="wftrec(Memrel(M)^+, x, HPn_auto(\<pi>))" in ssubst)
   apply(rule function_apply_equality)
    apply(simp add:Pn_auto_def)
   apply(simp add:Pn_auto_def function_def)
  apply(rule_tac G=HPn_auto_M and Gfm = HPn_auto_M_fm' and a=\<pi> in memrel_wftrec_in_M)
  using P_name_in_M is_P_auto_def 
        apply auto[2]
      apply(simp add:HPn_auto_M_fm'_def)+
     apply(subst arity_pair_fm, simp_all)+
     apply(subst arity_function_fm, simp_all)
     apply(subst arity_fun_apply_fm, simp_all)+
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union) 
    apply(rule HPn_auto_M_in_M)
      apply auto[3]
   apply(rule HPn_auto_M_eq)
           apply(simp add:P_auto_def)
  unfolding is_P_auto_def bij_def inj_def 
  apply auto[6]
   apply(rule iff_trans, rule iff_flip, rule HPn_auto_M_fm'_sats_iff)
  using Automorphism_M_rep_for_recfun_fm
      apply auto
  done

end
end