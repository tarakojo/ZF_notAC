theory Automorphism
  imports 
    "Forcing/Forcing_Main" 
    P_Names
begin 

context forcing_data  
begin 
definition separative1 where 
  "separative1(p, q) \<equiv> q \<preceq> p \<and> \<not> q \<preceq> p" 
definition separative2 where 
  "separative2(p, q) \<equiv> \<exists>r \<in> P. r \<preceq> q \<and> r \<bottom> p"
end 

thm separative_notion_axioms_def
locale forcing_data_separative = 
  forcing_data + 
  assumes leq_relation_on_P : "leq \<in> Pow(P \<times> P)" 
  and P_separative : "\<forall>p \<in> P. \<forall>q \<in> P. p \<noteq> q \<longrightarrow> (separative1(p, q) \<longleftrightarrow> \<not>separative2(p, q))" 

context forcing_data_separative
begin

lemma leq_antisym : "antisym(leq)" 
  unfolding antisym_def 
  apply clarify
  apply(rename_tac x y)
  apply(rule_tac P="x=y" and Q="x\<noteq>y" in disjE) apply simp_all 
  apply(rule_tac P="x \<in> P \<and> y \<in> P" in mp) apply clarify 
  apply(rule_tac P="separative1(x, y)" and Q="separative2(x, y)" in disjE) 
  using P_separative apply simp 
  unfolding separative1_def apply simp 
  unfolding separative2_def apply(rule_tac A=P and P="\<lambda>r. r \<preceq> y \<and> r \<bottom> x " in bexE) apply simp 
  apply(rename_tac xa)
  apply(rule_tac P="compat(xa, x)" in mp) apply simp  
  apply(rule_tac d=xa in compatI) apply simp using leq_reflI apply simp 
  apply(rule_tac b=y in leq_transD) apply simp_all 
  using leq_relation_on_P by auto 

lemma one_is_unique_max : "x \<in> P \<Longrightarrow> one \<preceq> x \<Longrightarrow> x = one" 
proof- 
  assume assms : "x \<in> P" "one \<preceq> x"
  then have "x \<preceq> one" using one_max by auto 
  then show "x = one" using leq_in_M assms leq_antisym unfolding antisym_def by auto
qed

definition is_P_auto :: "i \<Rightarrow> o" where
  "is_P_auto(\<pi>) \<equiv> \<pi> \<in> M \<and> \<pi> \<in> bij(P, P) \<and> (\<forall> p \<in> P. \<forall>q \<in> P. p \<preceq> q \<longleftrightarrow> \<pi>`p \<preceq> \<pi>`q)"  

definition P_auto where "P_auto \<equiv> { \<pi> \<in> P \<rightarrow> P. is_P_auto(\<pi>) }" 

lemma P_auto_type : "is_P_auto(\<pi>) \<Longrightarrow> \<pi> \<in> P \<rightarrow> P" unfolding is_P_auto_def bij_def surj_def by auto

lemma P_auto_is_function : "is_P_auto(\<pi>) \<Longrightarrow> function(\<pi>)" 
  unfolding is_P_auto_def 
  using bij_is_fun bij_is_fun Pi_def by auto

lemma P_auto_domain : "is_P_auto(\<pi>) \<Longrightarrow> domain(\<pi>) = P" 
proof - 
  assume assms : "is_P_auto(\<pi>)" 
  have "\<pi> \<in> P \<rightarrow> P" using assms unfolding is_P_auto_def using bij_is_fun by auto 
  then show "domain(\<pi>) = P" unfolding Pi_def by auto 
qed

lemma P_auto_value : "is_P_auto(\<pi>) \<Longrightarrow> p \<in> P \<Longrightarrow> \<pi>`p \<in> P" 
proof - 
  assume "is_P_auto(\<pi>)" "p \<in> P "
  then have "\<pi> \<in> P \<rightarrow> P"
    unfolding is_P_auto_def using bij_is_fun by auto 
  then show "\<pi>`p \<in> P" using function_value_in \<open>p \<in> P\<close> by auto 
qed 
  
lemma P_auto_preserves_leq : 
   "is_P_auto(\<pi>) \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> P \<Longrightarrow> p \<preceq> q \<Longrightarrow> \<pi>`p \<preceq> \<pi>`q" 
  unfolding is_P_auto_def by auto 

lemma P_auto_preserves_leq' : 
  "is_P_auto(\<pi>) \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> P \<Longrightarrow> \<pi>`p \<preceq> \<pi>`q \<Longrightarrow> p \<preceq> q" 
  unfolding is_P_auto_def by auto 

lemma P_auto_idP : "is_P_auto(id(P))"
  unfolding is_P_auto_def 
  apply (rule conjI) using id_closed P_in_M apply simp apply (rule conjI) 
  using id_bij apply simp apply simp done 

lemma P_auto_converse : "is_P_auto(\<pi>) \<Longrightarrow> is_P_auto(converse(\<pi>))" 
  unfolding is_P_auto_def apply (rule_tac conjI) using converse_closed apply simp 
  apply (rule_tac conjI) using bij_converse_bij apply simp apply (clarify) 
proof -
  fix p q 
  assume assms : "\<pi> \<in> bij(P, P)" "p \<in> P" "q \<in> P" "\<forall>p\<in>P. \<forall>q\<in>P. p \<preceq> q \<longleftrightarrow> \<pi> ` p \<preceq> \<pi> ` q" 
  then have pisurj : "\<pi> \<in> surj(P,P)" using bij_def by auto
  then obtain p' where p'h : "p' \<in> P" "\<pi>`p' = p" using assms unfolding surj_def by auto 
  then obtain q' where q'h : "q' \<in> P" "\<pi>`q' = q" using assms pisurj unfolding surj_def by auto 
  have H1: "converse(\<pi>) ` p = p'" using converse_apply assms p'h by auto
  have H2: "converse(\<pi>) ` q = q'" using converse_apply assms q'h by auto
  show "p \<preceq> q \<longleftrightarrow> converse(\<pi>) ` p \<preceq> converse(\<pi>) ` q" 
    apply (rule iffI) 
  proof - 
    assume assms' : " p \<preceq> q" 
    have H3: "p' \<preceq> q'" using p'h q'h assms assms' by auto
    show " converse(\<pi>) ` p \<preceq> converse(\<pi>) ` q" using H1 H2 H3 by auto 
  next 
    assume assms' : "converse(\<pi>) ` p \<preceq> converse(\<pi>) ` q " 
    have H3: "p' \<preceq> q'" using p'h q'h assms assms' H1 H2 by auto 
    then show "p \<preceq> q" using assms p'h q'h by auto 
  qed
qed

lemma P_auto_preserves_one : "is_P_auto(\<pi>) \<Longrightarrow> \<pi>`one = one" 
proof - 
  assume assm : "is_P_auto(\<pi>)" 
  obtain p where pp : "p \<in> P" "\<pi>`p=one" 
    using one_in_P surj_def assm unfolding is_P_auto_def bij_def by auto 
  then have p1: "p \<preceq> one" using one_max by auto 
  then have "\<pi>`p \<preceq> \<pi>`one" 
    using P_auto_preserves_leq pp one_in_P p1 assm by auto 
  then have "one \<preceq> \<pi>`one" using pp by auto 
  then show "\<pi>`one = one" using assm P_auto_value one_in_P one_is_unique_max by auto
qed

lemma P_auto_preserves_density : 
  "is_P_auto(\<pi>) \<Longrightarrow> D \<subseteq> P \<Longrightarrow> q \<in> P \<Longrightarrow> dense_below(D, q) \<Longrightarrow> dense_below(\<pi>``D, \<pi>`q)" 
  unfolding dense_below_def apply auto 
proof - 
  fix p
  assume assms : "is_P_auto(\<pi>)" "\<forall>p\<in>P. p \<preceq> q \<longrightarrow> (\<exists>d\<in>D. d \<in> P \<and> d \<preceq> p)" 
                 "p \<in> P" "p \<preceq> \<pi>`q" "q \<in> P" "D \<subseteq> P" 
  have "\<pi> \<in> surj(P, P)" using assms unfolding is_P_auto_def bij_def by auto 
  then obtain p' where p'h: "p' \<in> P" "\<pi>`p' = p" using assms unfolding surj_def by auto 
  then have "p' \<preceq> q" apply (rule_tac \<pi>=\<pi> in P_auto_preserves_leq') using assms apply auto done
  then obtain d where dh: "d \<in> D" "d \<preceq> p'" using p'h assms by auto 
  then have H: "\<pi>`d \<in> \<pi>``D" apply (rule_tac a=d in imageI) 
    apply (rule_tac function_apply_Pair) 
    using P_auto_is_function assms P_auto_domain apply auto done
  have H2 : "\<pi>`d \<preceq> p" using P_auto_preserves_leq dh p'h assms apply auto done 
  have "\<pi>`d \<in> P" using P_auto_value assms dh by auto 
  then show "\<exists>d\<in>\<pi> `` D. d \<in> P \<and> d \<preceq> p" using H H2 by auto 
qed

lemma P_auto_preserves_density' : 
  "is_P_auto(\<pi>) \<Longrightarrow> D \<subseteq> P \<Longrightarrow> q \<in> P \<Longrightarrow> dense_below(D, q) \<longleftrightarrow> dense_below(\<pi>``D, \<pi>`q)" 
  apply (rule iffI) using P_auto_preserves_density apply simp 
  apply (rule_tac P="dense_below(converse(\<pi>) `` (\<pi> `` D), converse(\<pi>) ` (\<pi> ` q))" in mp)
  apply (rule_tac a=D and b="converse(\<pi>) `` (\<pi> `` D)" in ssubst)
  apply (rule_tac A=P and B=P in image_converse_image) apply (simp add : is_P_auto_def) 
  apply simp 
  apply (rule_tac a=q and b="converse(\<pi>) ` (\<pi> ` q)" in ssubst)
  apply (rule_tac A=P and B=P in converse_apply)   apply (simp add : is_P_auto_def) 
  apply (simp_all)
proof - 
  assume assms :  "is_P_auto(\<pi>)" " D \<subseteq> P"  "q \<in> P" "dense_below(\<pi> `` D, \<pi> ` q) "
  show "dense_below(converse(\<pi>) `` (\<pi> `` D), converse(\<pi>) ` (\<pi> ` q))" 
    apply (rule_tac P_auto_preserves_density) using assms P_auto_converse apply simp
    apply (rule_tac A=P in image_subset) using assms bij_is_fun unfolding is_P_auto_def Pi_def apply auto 
    using assms local.P_auto_value by auto 
qed

definition HPn_auto :: "[i, i, i] \<Rightarrow> i" where 
  "HPn_auto(\<pi>, x, H) \<equiv> { <H`y, \<pi>`p> . <y, p> \<in> x }" 

definition Pn_auto :: "i \<Rightarrow> i" where 
  "Pn_auto(\<pi>) \<equiv> 
    { <x, wfrec(edrel(eclose({x})), x, HPn_auto(\<pi>))> . x \<in> P_names }" 

lemma Pn_auto_function : "function(Pn_auto(\<pi>))" 
  unfolding Pn_auto_def function_def by auto
lemma Pn_auto_domain : "domain(Pn_auto(\<pi>)) = P_names"
  unfolding Pn_auto_def domain_def by auto 

text\<open>
  This proof is a modified copy of Names.thy 
  by Emmanuel Gunther, Miguel Pagano, and Pedro Sánchez Terraf,
  with only minor alterations.
\<close>
lemma aux_def_val_generalized:
  assumes "z \<in> domain(x)"
  shows "wfrec(edrel(eclose({x})),z,F) = wfrec(edrel(eclose({z})),z,F)"
proof -
  let ?r="\<lambda>x . edrel(eclose({x}))"
  have "z\<in>eclose({z})" using arg_in_eclose_sing .
  moreover
  have "relation(?r(x))" using relation_edrel .
  moreover
  have "wf(?r(x))" using wf_edrel .
  moreover from assms
  have "tr_down(?r(x),z) \<subseteq> eclose({z})" using tr_edrel_subset by simp
  ultimately
  have "wfrec(?r(x),z,F) = wfrec[eclose({z})](?r(x),z,F)"
    using wfrec_restr by simp
  also from \<open>z\<in>domain(x)\<close>
  have "... = wfrec(?r(z),z,F)"
    using restrict_edrel_eq wfrec_restr_eq by simp
  finally show ?thesis .
qed

lemma Pn_auto : "x \<in> P_names \<Longrightarrow> Pn_auto(\<pi>)`x = { <Pn_auto(\<pi>)`y, \<pi>`p> . <y, p> \<in> x}"  
proof -
  assume assm : "x \<in> P_names"
  then have xin: "x \<subseteq> P_set(P_rank(x)) \<times> P" using P_names_in by auto 
  then have "Pn_auto(\<pi>) ` x = wfrec(edrel(eclose({x})), x, HPn_auto(\<pi>))" 
    using function_value assm  unfolding Pn_auto_def by auto 
  also have 
    "... = HPn_auto(\<pi>, x, \<lambda>y \<in> edrel(eclose({x}))-``{x}. wfrec(edrel(eclose({x})), y, HPn_auto(\<pi>)))"
    apply (rule_tac wfrec)
    using wf_edrel by auto 
  also have 
    "... = { <( \<lambda>y \<in> edrel(eclose({x}))-``{x}. wfrec(edrel(eclose({x})), y, HPn_auto(\<pi>)))`y, \<pi>`p>.
     <y, p> \<in> x }" unfolding HPn_auto_def by auto 
  also have 
    "... = { <( \<lambda>y \<in> domain(x). wfrec(edrel(eclose({x})), y, HPn_auto(\<pi>)))`y, \<pi>`p>.
     <y, p> \<in> x }" using dom_under_edrel_eclose by auto 
  also have 
    "... = { <wfrec(edrel(eclose({x})), y, HPn_auto(\<pi>)), \<pi>`p>. <y, p> \<in> x }"
    apply (rule_tac pair_rel_eq)  using xin assm relation_P_name by auto
  also have "... = { <wfrec(edrel(eclose({y})), y, HPn_auto(\<pi>)), \<pi>`p>. <y, p> \<in> x }"
    apply (rule_tac pair_rel_eq)  using xin assm relation_P_name apply auto 
    apply(rule_tac aux_def_val_generalized)
    by auto 
  also have "... = { <Pn_auto(\<pi>)`y, \<pi>`p>. <y, p> \<in> x }"
    apply (rule_tac pair_rel_eq) using xin assm relation_P_name apply auto
    apply (rule_tac eq_flip)
    unfolding Pn_auto_def
    apply (rule_tac function_value)
    using P_name_domain_P_name assm by auto 
  finally show " Pn_auto(\<pi>)`x = { <Pn_auto(\<pi>)`y, \<pi>`p> . <y, p> \<in> x}" by auto 
qed 

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



lemma Pn_auto_value_in_P_set : 
  "is_P_auto(\<pi>) \<Longrightarrow> Ord(a) \<Longrightarrow> x \<in> P_names \<Longrightarrow> (x \<in> P_set(a) \<longleftrightarrow> Pn_auto(\<pi>)`x \<in> P_set(a))" 
proof - 
  assume assms : "is_P_auto(\<pi>)" "x \<in> P_names" "Ord(a)"
  define Q where "Q \<equiv> \<lambda>x a. x \<in> P_names \<longrightarrow> (x \<in> P_set(a) \<longleftrightarrow> Pn_auto(\<pi>)`x \<in> P_set(a))" 
  have main : 
    "\<And>x. (\<forall>a. Ord(a) \<longrightarrow> Q(x, a))" 
    apply (rule_tac Q="\<lambda>x. (\<forall>a. Ord(a) \<longrightarrow> Q(x, a))" in ed_induction)
    apply (clarify) 
    apply (rule_tac trans_induct3_raw)
    unfolding Q_def
    apply simp apply (simp add : Q_def P_set_0) 
  proof (clarify)
    fix b x 
    assume bord : "Ord(b)" 
    and ih : "\<And>y. ed(y, x) \<Longrightarrow> \<forall>a. Ord(a) \<longrightarrow> (y \<in> P_names \<longrightarrow> y \<in> P_set(a) \<longleftrightarrow> Pn_auto(\<pi>) ` y \<in> P_set(a))" 
    and xpname : "x \<in> P_names" 

    have xinM : "x \<in> M" using P_names_in_M xpname by auto 

    have pinP : "\<forall><y, p> \<in> x. p \<in> P" 
      apply (rule_tac pair_forallI) 
      using P_names_in xpname relation_P_name by auto 

    have ih : "\<And>y a. ed(y, x) \<Longrightarrow> Ord(a) \<Longrightarrow> y \<in> P_names \<Longrightarrow> (y \<in> P_set(a) \<longleftrightarrow> Pn_auto(\<pi>) ` y \<in> P_set(a))"
      using ih by auto

    have "x \<in> P_set(succ(b)) \<longleftrightarrow> x \<in> Pow(P_set(b) \<times> P) \<inter> M" using bord P_set_succ by auto 
    also have "... \<longleftrightarrow> x \<subseteq> P_set(b) \<times> P" using xinM by auto 
    also have "... \<longleftrightarrow> (\<forall><y, p> \<in> x. y \<in> P_set(b))" 
      apply (rule iffI) 
      apply (rule_tac pair_forallI) using relation_P_name xpname apply simp apply blast 
      apply (rule_tac x=x and A="\<lambda>y p. y \<in> P_set(b)" in pair_forallE)  
      using relation_P_name xpname apply simp apply simp
      apply (rule subsetI)
    proof - 
      fix v assume assms : "v \<in> x" "(\<And>y p. \<langle>y, p\<rangle> \<in> x \<Longrightarrow> y \<in> P_set(b))" 
      have xrel : "relation(x)" using relation_P_name xpname by auto 
      then obtain y p where yph: "v = <y, p>" unfolding relation_def using assms by auto 
      then have H : " y \<in> P_set(b)" using assms by auto 
      have "p \<in> P" using assms yph pinP by auto 
      then show "v \<in> P_set(b) \<times> P" using yph H by auto 
    qed
    also have "... \<longleftrightarrow> (\<forall><y, p> \<in> x. Pn_auto(\<pi>)`y \<in> P_set(b))" 
      apply (rule iffI) 
      apply (rule_tac pair_forallI)
      using relation_P_name xpname apply simp 
      apply (rule_tac x=x and A="\<lambda>y p. y \<in> P_set(b)" in pair_forallE)
      using relation_P_name xpname apply simp apply simp 
      apply (rename_tac y p)
      apply (rule_tac P="y \<in> P_set(b)" in iffD1)
      apply (rule_tac ih) unfolding ed_def domain_def apply blast 
      using bord apply simp using P_name_domain_P_name xpname apply simp 
      apply simp 
      apply (rule_tac pair_forallI)
      using relation_P_name xpname apply simp 
      apply (rule_tac x=x and A="\<lambda>y p. Pn_auto(\<pi>)`y \<in> P_set(b)" in pair_forallE) 
      using relation_P_name xpname apply simp 
      apply simp 
      apply (rule_tac Q="Pn_auto(\<pi>)`y \<in> P_set(b)" in iffD2)
      apply (rule_tac ih) unfolding ed_def domain_def apply blast 
      using bord apply simp using P_name_domain_P_name xpname apply simp 
      apply simp
      done 
    also have "... \<longleftrightarrow> Pn_auto(\<pi>)`x \<in> P_set(succ(b))" 
      apply (rule iffI) 
      apply (rule_tac x=x and A="\<lambda>y p. Pn_auto(\<pi>) ` y \<in> P_set(b)" in pair_forallE) 
      using relation_P_name xpname apply simp apply simp 
    proof - 
      assume assm : "(\<And>y p. \<langle>y, p\<rangle> \<in> x \<Longrightarrow> Pn_auto(\<pi>) ` y \<in> P_set(b))" 
      have "\<And>y p. \<langle>y, p\<rangle> \<in> x \<Longrightarrow> \<pi>`p \<in> P" 
        using pinP P_auto_value assms by auto 
      then have H: "\<And>y p. \<langle>y, p\<rangle> \<in> x \<Longrightarrow> <Pn_auto(\<pi>)`y, \<pi>`p> \<in> P_set(b) \<times> P" using assm by auto
      then have "{ <Pn_auto(\<pi>)`y, \<pi>`p> . <y, p> \<in> x } \<subseteq> P_set(b) \<times> P" 
        apply (rule_tac subsetI) 
      proof - 
        fix v
        assume assm1 : "v \<in> {\<langle>Pn_auto(\<pi>) ` y, \<pi> ` p\<rangle> . \<langle>y,p\<rangle> \<in> x}" 
        have "relation(x)" using relation_P_name xpname by auto 
        then have "\<exists>y p. \<langle>y, p\<rangle> \<in> x \<and> v = \<langle>Pn_auto(\<pi>) ` y, \<pi> ` p\<rangle>" 
          using pair_rel_arg assm1 by auto 
        then obtain y p where yph : "<y, p> \<in> x" "v = \<langle>Pn_auto(\<pi>) ` y, \<pi> ` p\<rangle>" by auto 
        then have H : "Pn_auto(\<pi>) ` y \<in> P_set(b)" using yph assm by auto 
        have "p \<in> P" using pinP yph by auto 
        then have "\<pi>`p \<in> P" using P_auto_value assms by auto 
        then show  "v \<in> P_set(b) \<times> P" using H yph by auto 
      qed     
      then have H: "Pn_auto(\<pi>) ` x \<in> Pow(P_set(b) \<times> P)" using xpname Pn_auto by auto 
      have "Pn_auto(\<pi>) ` x  \<in> M" using Pn_auto_value_in_M assms xpname by auto 
      then have "Pn_auto(\<pi>) ` x \<in> Pow(P_set(b) \<times> P) \<inter> M" using H by auto 
      then show "Pn_auto(\<pi>) ` x \<in> P_set(succ(b))" using P_set_succ by auto 
    next 
      assume assm : "Pn_auto(\<pi>) ` x \<in> P_set(succ(b))" 
      show "\<forall>\<langle>y,p\<rangle>\<in>x. Pn_auto(\<pi>) ` y \<in> P_set(b)" 
        apply (rule_tac pair_forallI) 
        using relation_P_name xpname apply auto 
      proof - 
        fix y p assume ypin : "<y, p> \<in> x"
        then have "<Pn_auto(\<pi>)`y, \<pi>`p> \<in> { <Pn_auto(\<pi>) ` y, \<pi>`p> . <y, p> \<in> x }" 
          apply auto apply(rule_tac x="<y, p>" in bexI) by auto
        then have H:"<Pn_auto(\<pi>)`y, \<pi>`p> \<in> Pn_auto(\<pi>) ` x " 
          using xpname Pn_auto by auto

        have "P_set(succ(b)) = Pow(P_set(b) \<times> P) \<inter> M" using P_set_succ by auto 
        then have "Pn_auto(\<pi>) ` x \<in> Pow(P_set(b) \<times> P) \<inter> M" using assm by auto 
        then show " Pn_auto(\<pi>) ` y \<in> P_set(b)" using H by auto 
      qed
    qed
    finally show "x \<in> P_set(succ(b)) \<longleftrightarrow> Pn_auto(\<pi>) ` x \<in> P_set(succ(b))" by auto
  next 
    fix b x assume blim : "Limit(b)"
    and ih : "\<forall>a\<in>b. x \<in> P_names \<longrightarrow> x \<in> P_set(a) \<longleftrightarrow> Pn_auto(\<pi>) ` x \<in> P_set(a)"

    have psetb : "P_set(b) = (\<Union>a<b. P_set(a))" using P_set_lim blim by auto

    show "x \<in> P_names \<longrightarrow> x \<in> P_set(b) \<longleftrightarrow> Pn_auto(\<pi>) ` x \<in> P_set(b)"
    proof (rule impI; rule iffI)
      assume assm : "x \<in> P_names" "x \<in> P_set(b)" 
      then obtain a where ah : "a < b" "x \<in> P_set(a)"  using psetb by auto
      then have "Pn_auto(\<pi>) ` x \<in> P_set(a)" using ih ltD assm by auto 
      then have "Pn_auto(\<pi>) ` x \<in> (\<Union>a<b. P_set(a))" using ah by auto 
      then show "Pn_auto(\<pi>) ` x \<in> P_set(b)" using psetb by auto
    next 
      assume assm : "x \<in> P_names" "Pn_auto(\<pi>) ` x \<in> P_set(b)" 
      then obtain a where ah : "a < b" "Pn_auto(\<pi>) ` x \<in> P_set(a)"  using psetb by auto
      then have "x \<in> P_set(a)" using ih ltD assm by auto 
      then have "x \<in> (\<Union>a<b. P_set(a))" using ah by auto 
      then show "x \<in> P_set(b)" using psetb by auto
    qed
  qed
  then show "x \<in> P_set(a) \<longleftrightarrow> Pn_auto(\<pi>)`x \<in> P_set(a)" 
    using assms main unfolding Q_def by auto 
qed

lemma Pn_auto_value : "is_P_auto(\<pi>) \<Longrightarrow> x \<in> P_names \<Longrightarrow> Pn_auto(\<pi>)`x \<in> P_names" 
proof - 
  assume assms : "is_P_auto(\<pi>)" "x \<in> P_names" 
  then obtain a where ah :"Ord(a)" "x \<in> P_set(succ(a))" using P_names_in_P_set_succ by auto
  then have "Pn_auto(\<pi>)`x \<in> P_set(succ(a))" using Pn_auto_value_in_P_set assms by auto 
  then show "Pn_auto(\<pi>)`x \<in> P_names" 
    unfolding P_names_def using ah Pn_auto_value_in_M assms by auto 
qed

lemma Pn_auto_type : "is_P_auto(\<pi>) \<Longrightarrow> Pn_auto(\<pi>) \<in> P_names \<rightarrow> P_names" 
  unfolding Pi_def apply auto using Pn_auto_function Pn_auto_domain apply simp_all
proof - 
  fix x assume assm : "x \<in> Pn_auto(\<pi>)" "is_P_auto(\<pi>)"
  then obtain a b where abH: "x = <a, b>" unfolding Pn_auto_def by auto 
  have H: "a \<in> P_names" using abH assm unfolding Pn_auto_def by auto 
  have "b = Pn_auto(\<pi>)`a" using function_apply_equality abH assm Pn_auto_function by auto 
  then have "b \<in> P_names" using Pn_auto_value H assm by auto 
  then show "x \<in> P_names \<times> P_names" using H abH by auto
qed

lemma Pn_auto_comp : "is_P_auto(\<pi>) \<Longrightarrow> is_P_auto(\<tau>) \<Longrightarrow> Pn_auto(\<pi> O \<tau>) = Pn_auto(\<pi>) O Pn_auto(\<tau>)" 
proof - 
  assume assms : "is_P_auto(\<pi>)" "is_P_auto(\<tau>)"
  have main : "\<And>x. x \<in> P_names \<longrightarrow> Pn_auto(\<pi> O \<tau>)`x = (Pn_auto(\<pi>) O Pn_auto(\<tau>))`x"
    apply (rule_tac Q="\<lambda>x. x \<in> P_names \<longrightarrow> Pn_auto(\<pi> O \<tau>)`x = (Pn_auto(\<pi>) O Pn_auto(\<tau>))`x" in ed_induction)
  proof (clarify)
    fix x assume "\<And>y. ed(y, x) \<Longrightarrow> y \<in> P_names \<longrightarrow> Pn_auto(\<pi> O \<tau>) ` y = (Pn_auto(\<pi>) O Pn_auto(\<tau>)) ` y"
    and xpname : "x \<in> P_names" 

    then have ih: "\<And>y. ed(y, x) \<Longrightarrow> y \<in> P_names \<Longrightarrow> Pn_auto(\<pi> O \<tau>) ` y = (Pn_auto(\<pi>) O Pn_auto(\<tau>)) ` y" by auto

    have "Pn_auto(\<pi> O \<tau>) ` x = { <Pn_auto(\<pi> O \<tau>)`y, (\<pi> O \<tau>)` p> . <y, p> \<in> x }" 
      using Pn_auto xpname by auto 
    also have "... = { <(Pn_auto(\<pi>) O Pn_auto(\<tau>)) ` y, (\<pi> O \<tau>)` p> . <y, p> \<in> x }"
      apply (rule_tac pair_rel_eq) using xpname relation_P_name apply simp 
      apply auto apply (rule_tac ih) unfolding ed_def apply auto using xpname P_name_domain_P_name by auto 
    also have "... = { <Pn_auto(\<pi>) ` (Pn_auto(\<tau>) ` y), \<pi> ` (\<tau> ` p)> . <y, p> \<in> x }"
      apply (rule_tac pair_rel_eq) using xpname relation_P_name apply auto 
      apply (rule_tac A=P_names and B=P_names in comp_fun_apply) using assms Pn_auto_type apply simp 
      using P_name_domain_P_name apply simp 
      apply (rule_tac A=P and B=P in comp_fun_apply) using assms unfolding is_P_auto_def bij_def inj_def apply simp 
      using P_name_range by auto
    also have "... = { <Pn_auto(\<pi>) ` y', \<pi> ` p'> . <y', p'> \<in> Pn_auto(\<tau>)`x }" 
      apply (rule_tac equality_iffI; rule iffI) 
    proof - 
      fix v assume vin : "v \<in> {\<langle>Pn_auto(\<pi>) ` (Pn_auto(\<tau>) ` y), \<pi> ` (\<tau> ` p)\<rangle> . \<langle>y,p\<rangle> \<in> x}"
      then have "\<exists>y p. <y, p> \<in> x \<and> v = \<langle>Pn_auto(\<pi>) ` (Pn_auto(\<tau>) ` y), \<pi> ` (\<tau> ` p)\<rangle>" 
        apply (rule_tac pair_rel_arg) using xpname relation_P_name apply simp by simp 
      then obtain y p where yph : "<y, p> \<in> x" "v = \<langle>Pn_auto(\<pi>) ` (Pn_auto(\<tau>) ` y), \<pi> ` (\<tau> ` p)\<rangle>" by auto 
      then have "\<langle>Pn_auto(\<pi>) ` (Pn_auto(\<tau>) ` y), \<pi> ` (\<tau> ` p)\<rangle> \<in> { <Pn_auto(\<pi>) ` y', \<pi> ` p'> . <y', p'> \<in> Pn_auto(\<tau>)`x }"  
        apply (rule_tac pair_relI) 
        apply (rule_tac a="{ <Pn_auto(\<tau>)`y, \<tau>`p> . <y, p> \<in> x }" and b = "Pn_auto(\<tau>)`x" in ssubst) 
        using Pn_auto xpname apply simp 
        apply (rule_tac pair_relI) by simp 
      then show "v \<in> { <Pn_auto(\<pi>) ` y', \<pi> ` p'> . <y', p'> \<in> Pn_auto(\<tau>)`x }"  using yph by auto 
    next 
      fix v assume vin : "v \<in> {\<langle>Pn_auto(\<pi>) ` y', \<pi> ` p'\<rangle> . \<langle>y',p'\<rangle> \<in> Pn_auto(\<tau>) ` x}"
      then have "\<exists>y' p'. <y', p'> \<in> Pn_auto(\<tau>)`x \<and> v = <Pn_auto(\<pi>)`y', \<pi>`p'>" 
        apply (rule_tac pair_rel_arg) apply(rule_tac relation_P_name) 
        using Pn_auto_value xpname assms by auto 
      then obtain y' p' where y'p'H : "<y', p'> \<in> Pn_auto(\<tau>)`x" "v = <Pn_auto(\<pi>)`y', \<pi>`p'>" by auto 
      then have "<y', p'> \<in> { <Pn_auto(\<tau>)`y, \<tau>`p> . <y, p> \<in> x }" using Pn_auto assms xpname by auto
      then have "\<exists>y p. <y, p> \<in> x \<and> <y', p'> = <Pn_auto(\<tau>)`y, \<tau>`p>" 
        apply (rule_tac pair_rel_arg) using xpname relation_P_name by auto 
      then obtain y p where ypH : "<y, p> \<in> x" "y' = Pn_auto(\<tau>)`y" "p' = \<tau>`p" by auto 
      then have "<Pn_auto(\<pi>) ` (Pn_auto(\<tau>) ` y), \<pi> ` (\<tau> ` p)> \<in> {\<langle>Pn_auto(\<pi>) ` (Pn_auto(\<tau>) ` y), \<pi> ` (\<tau> ` p)\<rangle> . \<langle>y,p\<rangle> \<in> x}" 
        apply (rule_tac pair_relI) by auto 
      then show "v \<in> {\<langle>Pn_auto(\<pi>) ` (Pn_auto(\<tau>) ` y), \<pi> ` (\<tau> ` p)\<rangle> . \<langle>y,p\<rangle> \<in> x}"
        using y'p'H ypH by auto 
    qed
    also have "... = Pn_auto(\<pi>) ` (Pn_auto(\<tau>) ` x)" 
      thm Pn_auto 
      apply (rule_tac eq_flip)
      apply (rule_tac Pn_auto) using Pn_auto_value assms xpname by auto 
    also have "... = (Pn_auto(\<pi>) O Pn_auto(\<tau>)) ` x" 
      apply (rule eq_flip) apply(rule_tac A=P_names and B=P_names in comp_fun_apply) 
      using assms xpname Pn_auto_type by auto 
    finally show " Pn_auto(\<pi> O \<tau>) ` x = (Pn_auto(\<pi>) O Pn_auto(\<tau>)) ` x " by simp 
  qed

  have "is_P_auto(\<pi> O \<tau>)" 
    using assms
    unfolding is_P_auto_def apply (rule_tac conjI) 
    using comp_closed apply simp apply (rule_tac conjI) 
    using comp_bij apply blast apply clarify apply (rule_tac Q="\<pi>`(\<tau>`p) \<preceq> \<pi>`(\<tau>`q)" in iff_trans) 
    apply (rule_tac Q="(\<tau>`p) \<preceq> (\<tau>`q)" in iff_trans) apply simp 
    apply (rule_tac P="\<tau>`p \<in> P \<and> \<tau>`q \<in> P" in mp) apply simp using assms P_auto_value apply simp
    apply (rule_tac P="(\<pi> O \<tau>)` p = \<pi> ` (\<tau> ` p) \<and> (\<pi> O \<tau>)` q = \<pi> ` (\<tau> ` q)" in mp) apply simp
    apply (rule conjI)
    apply (rule_tac A=P and B=P in comp_fun_apply) using assms is_P_auto_def bij_def inj_def apply simp_all 
    apply (rule_tac A=P and B=P in comp_fun_apply) using assms is_P_auto_def bij_def inj_def apply simp_all done 
  then have "Pn_auto(\<pi> O \<tau>) \<in> P_names \<rightarrow> P_names" using Pn_auto_type by auto 

  then show "Pn_auto(\<pi> O \<tau>) = Pn_auto(\<pi>) O Pn_auto(\<tau>)" 
    apply (rule_tac A=P_names and  B=P_names and C = P_names in function_eq)
    apply simp apply (rule_tac B=P_names in comp_fun) using assms Pn_auto_type apply simp_all
    using main by auto 
qed

lemma Pn_auto_id : "Pn_auto(id(P)) = id(P_names)" 
proof -
  have main : "\<And>x. x \<in> P_names \<longrightarrow> Pn_auto(id(P))`x = id(P_names) ` x" 
    apply (rule_tac Q="\<lambda>x. x \<in> P_names \<longrightarrow> Pn_auto(id(P))`x = id(P_names) `  x" in ed_induction)
  proof (clarify)
    fix x assume ih : "(\<And>y. ed(y, x) \<Longrightarrow> y \<in> P_names \<longrightarrow> Pn_auto(id(P)) ` y = id(P_names) ` y)"
    and xpname : "x \<in> P_names" 

    have " Pn_auto(id(P))`x = { <Pn_auto(id(P))`y, id(P)`p>. <y, p> \<in> x }" 
      using Pn_auto xpname by auto 
    also have "... = { <y, p> . <y, p> \<in> x }" 
      apply (rule_tac pair_rel_eq) using xpname relation_P_name apply simp 
      apply auto apply(rule_tac P="y \<in> P_names \<and> ed(y, x)" in mp) 
      using ih apply simp apply (rule conjI) using xpname P_name_domain_P_name apply simp 
      unfolding ed_def domain_def apply auto unfolding id_def using xpname P_name_range apply simp done 
    also have "... = x"   
      apply (rule equality_iffI; rule iffI)
    proof - 
      fix v assume "v \<in> { <y, p>. <y, p> \<in> x }" 
      then have "\<exists>y p. <y, p> \<in> x \<and> v = <y, p>" apply (rule_tac pair_rel_arg) using xpname relation_P_name by auto 
      then obtain y p where "v = <y, p>" "<y, p> \<in> x" by auto 
      then show "v \<in> x" by auto 
    next 
      fix v assume assm : "v \<in> x" then obtain y p where ypH: "v = <y, p>" 
        using xpname relation_P_name unfolding relation_def by blast
      then have "<y, p> \<in> { <y, p> . <y, p> \<in> x }" apply (rule_tac pair_relI) using assm by auto 
      then show "v \<in> { <y, p> . <y, p> \<in> x }" using ypH by auto 
    qed
    also have "... = id(P_names)`x" unfolding id_def using xpname by auto
    finally show "Pn_auto(id(P)) ` x = id(P_names)`x" by simp 
  qed

  show "Pn_auto(id(P)) = id(P_names)" 
    apply (rule_tac A=P_names and B=P_names and C=P_names in function_eq) 
    using P_auto_idP Pn_auto_type id_type main by auto 
qed

lemma Pn_auto_bij : "is_P_auto(\<pi>) \<Longrightarrow> Pn_auto(\<pi>) \<in> bij(P_names, P_names)"
  apply (rule_tac P="\<pi> \<in> bij(P, P)" in mp) apply(rule impI)
  apply (rule_tac g="Pn_auto(converse(\<pi>))" in fg_imp_bijective) 
  using Pn_auto_type P_auto_converse apply simp_all 
  apply (rule_tac b="Pn_auto(\<pi>) O Pn_auto(converse(\<pi>))" and a="Pn_auto(\<pi> O converse(\<pi>))" in ssubst) 
  using Pn_auto_comp P_auto_converse apply simp 
  apply (rule_tac b="\<pi> O converse(\<pi>)" and a = "id(P)" in ssubst) 
  apply (rule_tac A=P and B=P in right_comp_inverse) using bij_is_surj apply simp 
  using Pn_auto_id apply simp 
  apply (rule_tac b="Pn_auto(converse(\<pi>)) O Pn_auto(\<pi>)" and a="Pn_auto(converse(\<pi>) O \<pi>)" in ssubst) 
  using Pn_auto_comp P_auto_converse apply simp 
  apply (rule_tac b="converse(\<pi>) O \<pi>" and a = "id(P)" in ssubst) 
  apply (rule_tac A=P and B=P in left_comp_inverse) using bij_is_inj apply simp 
  using Pn_auto_id apply simp 
proof - 
  assume assm : "is_P_auto(\<pi>)" 
  then show "\<pi> \<in> bij(P, P)" unfolding is_P_auto_def by auto 
qed


lemma Pn_auto_preserves_P_rank : 
  "is_P_auto(\<pi>) \<Longrightarrow> x \<in> P_names \<Longrightarrow> P_rank(x) = P_rank(Pn_auto(\<pi>)`x)" 
proof-
  assume assms : "is_P_auto(\<pi>)" "x \<in> P_names" 
  have least_iff : "\<And>P Q. \<forall>x. P(x) \<longleftrightarrow> Q(x) \<Longrightarrow> (\<mu> x. P(x)) = (\<mu> x. Q(x))" by auto
  have iff_lemma : "\<And>P Q R. (P \<Longrightarrow> Q \<longleftrightarrow> R) \<Longrightarrow> P \<and> Q \<longleftrightarrow> P \<and> R" by auto 
  show "P_rank(x) = P_rank(Pn_auto(\<pi>) ` x)" 
    unfolding P_rank_def 
    apply (rule_tac least_iff; rule allI; rule_tac iff_lemma)
    apply (rule_tac Pn_auto_value_in_P_set) using assms by auto
qed

lemma check_fixpoint : 
  "is_P_auto(\<pi>) \<Longrightarrow> x \<in> M \<Longrightarrow> Pn_auto(\<pi>)`(check(x)) = check(x)"
proof - 
  assume piauto: "is_P_auto(\<pi>)" 
  have mainlemma: "\<And>v. v \<in> P_names \<Longrightarrow> \<forall>x \<in> M. (check(x) = v \<longrightarrow> Pn_auto(\<pi>)`(v) = v)" 
    thm P_name_induct
    apply (rule_tac Q="\<lambda>v. \<forall>x \<in> M. (check(x) = v \<longrightarrow> Pn_auto(\<pi>)`(v) = v)" in P_name_induct) 
    apply (auto)
  proof -
    fix x assume assms : 
           "\<forall>y. (\<exists>p. \<langle>y, p\<rangle> \<in> check(x)) \<longrightarrow> (\<exists>x\<in>M. check(x) = y) \<longrightarrow> Pn_auto(\<pi>) ` y = y"
           "x \<in> M"
    have "check(x) \<in> Pow(P_set(P_rank(check(x))) \<times> P) \<inter> M" 
      using P_names_in check_P_name assms by auto 
    then have p1 : "check(x) \<subseteq> P_set(P_rank(check(x))) \<times> P" by auto 
    have p2 : "check(x) = { <check(y), one> . y \<in> x }" 
      by (rule_tac def_check)
    have "Pn_auto(\<pi>) ` check(x) = { <Pn_auto(\<pi>)`y, \<pi>`p> . <y, p> \<in> check(x) }"
      using Pn_auto check_P_name assms by auto 
    also have "... =  { <Pn_auto(\<pi>)`y, \<pi>`one> . <y, p> \<in> check(x) }"
      apply (rule_tac pair_rel_eq)
      using p1 apply auto 
      using check_P_name assms relation_P_name apply simp
    proof - 
      fix y p assume "<y, p> \<in> check(x)" 
      then have "p = one" using p2 by auto 
      then show "\<pi>`p = \<pi>`one" by auto 
    qed 
    also have "... =  { <Pn_auto(\<pi>)`y, one> . <y, p> \<in> check(x) }" 
      using piauto P_auto_preserves_one by auto 
    also have "... =  { <y, one> .  <y, p> \<in> check(x) }"
      apply (rule_tac pair_rel_eq)
      using p1 apply auto 
      using check_P_name assms relation_P_name apply simp
    proof -
      fix y p assume assm1:  "\<langle>y, p\<rangle> \<in> check(x)" 
      then obtain yy where p0: "yy \<in> x" "<y, p> = <check(yy), one>" using p2 by auto 
      then have p1: "y = check(yy)" by auto 
      have p2 : "yy \<in> M" using transM assms p0 by auto 
      then show "Pn_auto(\<pi>) ` y = y" using assms assm1 p1 p2 by auto 
    qed 
    also have"... = { <check(y), one> . y \<in> x }" 
      apply (rule_tac RepFun_eq; auto)
    proof - 
      fix v assume "v \<in> check(x)" 
      then have "v \<in> { <check(y), one> . y \<in> x }" using p2 by auto 
      then obtain y where yp : "y \<in> x" "v = <check(y), one>" by auto 
      then show "\<exists> y \<in> x. (\<lambda>\<langle>y,p\<rangle>. \<langle>y, one\<rangle>)(v) = <check(y), one>" by auto 
    next 
      fix y assume "y \<in> x" 
      then show "\<exists>v \<in> check(x). \<langle>check(y), one\<rangle> = (\<lambda>\<langle>y,p\<rangle>. \<langle>y, one\<rangle>)(v)"
        apply (rule_tac x="<check(y), one>" in bexI)
        using p2 by auto
    qed
    also have " ... = check(x)" using p2 by auto 
    finally show "Pn_auto(\<pi>) ` check(x) = check(x)" by auto 
  qed
  assume "is_P_auto(\<pi>)" "x \<in> M"
  then show "Pn_auto(\<pi>) ` check(x) = check(x)"
    using mainlemma check_P_name by auto
qed

end 
end