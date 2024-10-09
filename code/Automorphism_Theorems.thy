theory Automorphism_Theorems
  imports 
    Automorphism_M
begin 

context forcing_data_Automorphism_M
begin 

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

    have xinM : "x \<in> M" using P_name_in_M xpname by auto 

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
  then have comp_type: "Pn_auto(\<pi> O \<tau>) \<in> P_names \<rightarrow> P_names" using Pn_auto_type by auto 

  have range_subset: "range(Pn_auto(\<tau>)) \<subseteq> domain(Pn_auto(\<pi>))" 
  proof(rule subsetI)
    fix v assume "v \<in> range(Pn_auto(\<tau>))" 
    then obtain x where xH: "<x, v> \<in> Pn_auto(\<tau>)" by auto 
    then have veq: "Pn_auto(\<tau>)`x = v" 
      apply(rule function_apply_equality)
      apply(rule Pn_auto_function)
      done
    have "Pn_auto(\<tau>)`x \<in> P_names" 
      apply(rule Pn_auto_value)
      using assms xH Pn_auto_def 
      by auto
    then have "v \<in> P_names" using veq by auto 
    then show "v \<in> domain(Pn_auto(\<pi>))" using Pn_auto_domain by auto
  qed

  show "Pn_auto(\<pi> O \<tau>) = Pn_auto(\<pi>) O Pn_auto(\<tau>)" thm function_eq
    apply (rule_tac function_eq)
    unfolding relation_def
    using Pi_def comp_type
         apply force
        apply(simp add:comp_def)
    using Pi_def comp_type 
       apply simp
      apply(rule comp_function)
       apply(rule Pn_auto_function)+
     apply(subst domain_comp_eq, rule range_subset)
     apply(subst Pn_auto_domain)+
     apply simp
    apply(rule mp, rule main)
    using Pn_auto_domain 
    by auto 
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
    apply (rule function_eq) 
         apply(simp add:relation_def Pn_auto_def)
    using relation_def id_def relation_lam 
        apply force
       apply(rule Pn_auto_function)
      apply(simp add:id_def, rule function_lam)
     apply(subst Pn_auto_domain, simp add:id_def)
    apply(rule mp, rule main)
    using Pn_auto_domain 
    by auto
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

lemma Pn_auto_converse : "is_P_auto(\<pi>) \<Longrightarrow> Pn_auto(converse(\<pi>)) = converse(Pn_auto(\<pi>))" 
proof - 
  assume assms: "is_P_auto(\<pi>)" 
  have "Pn_auto(\<pi>) O Pn_auto(converse(\<pi>)) = Pn_auto(\<pi> O converse(\<pi>))" 
    apply(subst Pn_auto_comp)
    using assms P_auto_converse 
    by auto
  also have "... = Pn_auto(id(P))" 
    apply(subst right_comp_inverse)
    using assms is_P_auto_def bij_is_surj 
    by auto
  also have "... = id(P_names)"
    using Pn_auto_id 
    by auto
  finally have eq: "Pn_auto(\<pi>) O Pn_auto(converse(\<pi>)) = id(P_names) " by simp

  have "Pn_auto(converse(\<pi>)) = id(P_names) O Pn_auto(converse(\<pi>))" 
    apply(rule eq_flip, rule_tac A=P_names in left_comp_id)
    using Pn_auto_type assms P_auto_converse Pi_def 
    by force
  also have "... = (converse(Pn_auto(\<pi>)) O Pn_auto(\<pi>)) O Pn_auto(converse(\<pi>))" 
    apply(rule eq_flip)
    apply(subst left_comp_inverse)
    using Pn_auto_bij assms bij_is_inj 
    by auto
  also have "... = converse(Pn_auto(\<pi>)) O (Pn_auto(\<pi>) O Pn_auto(converse(\<pi>)))" 
    using comp_assoc by auto
  also have "... = converse(Pn_auto(\<pi>)) O Pn_auto(\<pi> O converse(\<pi>))" 
    apply(subst Pn_auto_comp)
    using assms P_auto_converse   
    by auto 
  also have "... = converse(Pn_auto(\<pi>)) O Pn_auto(id(P))" 
    apply(subst right_comp_inverse)
    using assms is_P_auto_def bij_is_surj 
    by auto
  also have "... = converse(Pn_auto(\<pi>)) O id(P_names)" 
    using Pn_auto_id 
    by auto 
  also have "... = converse(Pn_auto(\<pi>))" 
    apply(rule right_comp_id, rule converse_type)
    using Pn_auto_type Pi_def assms 
    by auto
  finally show "Pn_auto(converse(\<pi>)) = converse(Pn_auto(\<pi>)) " by simp
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