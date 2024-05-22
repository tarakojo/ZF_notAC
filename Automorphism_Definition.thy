theory Automorphism_Definition
  imports 
    "Forcing/Forcing_Main" 
    P_Names_M
begin 

locale forcing_data_partial = 
  forcing_data + 
  assumes leq_relation_on_P : "leq \<in> Pow(P \<times> P)" 
  and leq_partial_order : "partial_order_on(P, leq)" 
begin

lemma leq_antisym : "antisym(leq)" 
  using leq_partial_order 
  unfolding partial_order_on_def 
  by auto

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

end
end