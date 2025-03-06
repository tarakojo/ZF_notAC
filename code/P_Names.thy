theory P_Names
  imports 
    "Forcing/Forcing_Main"
    Utilities_M
begin 

context forcing_data
begin 

definition HP_set_succ :: "[i, i] \<Rightarrow> i" where 
  "HP_set_succ(a, X) \<equiv> Pow(X \<times> P) \<inter> M" 

definition P_set :: "i \<Rightarrow> i" where 
  "P_set(a) \<equiv> transrec2(a, 0, HP_set_succ)" 

lemma P_set_0 : "P_set(0) = 0" unfolding P_set_def using transrec2_0 by auto

lemma P_set_succ : 
  "P_set(succ(a)) = Pow(P_set(a) \<times> P) \<inter> M" 
  using transrec2_succ
proof - 
  have "P_set(succ(a)) = HP_set_succ(a, P_set(a))" unfolding P_set_def using transrec2_succ by auto
  then show ?thesis unfolding HP_set_succ_def by auto
qed
  
lemma P_set_lim : 
  "Limit(a) \<Longrightarrow> P_set(a) = (\<Union> b < a. P_set(b))" 
  using transrec2_Limit unfolding P_set_def by auto 
    
definition P_names :: "i" where "P_names \<equiv> { x \<in> M . \<exists> a. Ord(a) \<and> x \<in> P_set(a) }" 

definition P_rank :: "i \<Rightarrow> i" where 
  "P_rank(x) \<equiv> \<mu> a. Ord(a) \<and> x \<in> P_set(succ(a))" 

lemma P_rank_ord : "Ord(P_rank(x))" 
  unfolding P_rank_def by auto 

lemma P_set_elems_in_P_set_succ : 
  "Ord(a) \<Longrightarrow> x \<in> P_set(a) \<Longrightarrow> (\<exists>b < a. x \<in> P_set(succ(b)))" 
proof - 
  assume assms : "Ord(a)" "x \<in> P_set(a)"
  then have helper : "x \<in> P_set(a) \<longrightarrow> (\<exists>b < a. x \<in> P_set(succ(b)))"  
    apply (rule_tac P="\<lambda>a. x \<in> P_set(a) \<longrightarrow> (\<exists>b < a. x \<in> P_set(succ(b)))" 
          in trans_induct3_raw)
    apply simp 
    using P_set_0 apply simp 
    apply auto 
  proof - 
    fix a assume 
    assms : "Limit(a)"
            "x \<in> P_set(a)"
            "\<forall>y\<in>a. x \<in> P_set(y) \<longrightarrow> (\<exists>b<y. x \<in> P_set(succ(b)))" 
    then have "x \<in> (\<Union> b < a . P_set(b))" using P_set_lim assms by auto 
    then obtain b where p1 : "b < a" "x \<in> P_set(b)" by auto 
    then have "b \<in> a" using ltD p1 by auto 
    then obtain c where p2 : "c < b" "x \<in> P_set(succ(c))" using assms p1 by auto
    then have "c < a" using p1 lt_trans by auto 
    then show "(\<exists>c<a. x \<in> P_set(succ(c)))" using p2 by auto 
  qed
  then show ?thesis using assms by auto 
qed

lemma P_names_in_P_set_succ : "x \<in> P_names \<Longrightarrow> \<exists>a. Ord(a) \<and>  x \<in> P_set(succ(a))" 
proof - 
  assume "x \<in> P_names" 
  then obtain a where "Ord(a)" "x \<in> P_set(a)" unfolding P_names_def by auto
  then obtain b where bp : "b < a" "x \<in> P_set(succ(b))" using P_set_elems_in_P_set_succ by auto 
  then have "Ord(b)" using lt_Ord by auto 
  then show ?thesis using bp by auto 
qed   
  
lemma P_rank_works : 
  "x \<in> P_names \<Longrightarrow> x \<in> P_set(succ(P_rank(x)))"
proof - 
  assume "x \<in> P_names" 
  then obtain a where ah : "Ord(a)" "x \<in> P_set(succ(a))" using P_names_in_P_set_succ by auto 

  define Q where "Q \<equiv> \<lambda>a. Ord(a) \<and> x \<in> P_set(succ(a))" 
  then have "Q(a)" using ah by auto
  then have "Q(\<mu> a. Q(a))" 
    apply (rule_tac i=a in LeastI) using ah by auto 
  then have "x \<in> P_set(succ(\<mu> a. Q(a)))" unfolding Q_def by auto 
  then show "x \<in> P_set(succ(P_rank(x)))" unfolding P_rank_def Q_def by auto 
qed

lemma P_set_elems_in_M : "Ord(a) \<Longrightarrow> x \<in> P_set(a) \<Longrightarrow> x \<in> M" 
proof - 
  assume "x \<in> P_set(a)" "Ord(a)"
  then have "\<exists>b < a. x \<in> P_set(succ(b))" using P_set_elems_in_P_set_succ by auto 
  then obtain b where bp : "b < a" "x \<in> P_set(succ(b))" by auto
  then have "Ord(b)" using lt_Ord by auto 
  then have "x \<in> Pow(P_set(b) \<times> P) \<inter> M" using bp P_set_succ by auto 
  then show "x \<in> M" by auto 
qed

lemma P_namesI : "Ord(a) \<Longrightarrow> x \<in> P_set(a) \<Longrightarrow> x \<in> P_names" 
  unfolding P_names_def using P_set_elems_in_M by auto

lemma P_names_in : "x \<in> P_names \<Longrightarrow> x \<in> Pow(P_set(P_rank(x)) \<times> P) \<inter> M" 
proof - 
  assume "x \<in> P_names" 
  then have "x \<in> P_set(succ(P_rank(x)))" using P_rank_works by auto 
  then show "x \<in> Pow(P_set(P_rank(x)) \<times> P) \<inter> M"  
    using P_set_succ by auto 
qed

lemma relation_P_name : "x \<in> P_names \<Longrightarrow> relation(x)" 
  using P_names_in unfolding relation_def by blast 

lemma P_name_in_M : "x \<in> P_names \<Longrightarrow> x \<in> M" 
proof - 
  assume "x \<in> P_names" 
  then obtain a where "Ord(a)" "x \<in> P_set(a)" unfolding P_names_def by auto 
  then show "x \<in> M" using P_set_elems_in_M by auto 
qed 

lemma P_set_domain_P_set : 
  "Ord(a) \<Longrightarrow> x \<in> P_set(a) \<Longrightarrow> <y, p> \<in> x \<Longrightarrow> \<exists>b < a. Ord(b) \<and> y \<in> P_set(b)" 
proof -
  have helper :  "Ord(a) \<Longrightarrow> <y, p> \<in> x \<Longrightarrow> (x \<in> P_set(a) \<longrightarrow> (\<exists>b < a. Ord(b) \<and> y \<in> P_set(b)))" 
    apply (rule_tac 
        P="\<lambda>a . (x \<in> P_set(a) \<longrightarrow> (\<exists>b < a. Ord(b) \<and> y \<in> P_set(b)))" in trans_induct3_raw)
    apply simp
    using P_set_0 apply simp 
  proof (clarify)
    fix b
    assume assms :"x \<in> P_set(succ(b))" "Ord(b)" "\<langle>y, p\<rangle> \<in> x "
    then have p1 : "x \<in>  Pow(P_set(b) \<times> P) \<inter> M" using P_set_succ by auto 
    then have p2 : "x \<subseteq> P_set(b) \<times> P" by auto 
    then have p21 : "<y, p> \<in> P_set(b) \<times> P" using assms by auto 
    then have p22 : "y \<in> P_set(b)" by auto 
    have p3 : "x \<in> M" using p1 by auto 
    then have "<y, p> \<in> M" using transM assms by auto 
    then have p4 : "y \<in> M" using pair_in_M_iff  by auto 
    then show "\<exists>b<succ(b). Ord(b) \<and> y \<in> P_set(b)" 
      using p22 assms by auto 
  next
    fix a assume assms : "Limit(a)" "\<langle>y, p\<rangle> \<in> x" 
      "\<forall>b\<in>a. x \<in> P_set(b) \<longrightarrow> (\<exists>c<b. Ord(c) \<and> y \<in> P_set(c))"
    show "x \<in> P_set(a) \<longrightarrow> (\<exists>b<a. Ord(b) \<and> y \<in> P_set(b))"
    proof (clarify) 
      assume assms1 : "x \<in> P_set(a)" 
      then have "x \<in> (\<Union> b < a . P_set(b))" using P_set_lim assms by auto 
      then obtain b where p1 : "b < a" "x \<in> P_set(b)" by auto 
      then have "b \<in> a" using ltD p1 by auto 
      then obtain c where cp : "c < b" "Ord(c) \<and> y \<in> P_set(c)" using assms p1 by auto 
      then have "c < a" using p1 lt_trans by auto 
      then show "\<exists>b<a. Ord(b) \<and> y \<in> P_set(b)" using cp by auto 
    qed
  qed
  assume "Ord(a)" "x \<in> P_set(a)" "<y, p> \<in> x"
  then show ?thesis using helper by auto 
qed 

lemma P_name_domain_P_name : 
  "x \<in> P_names \<Longrightarrow> <y, p> \<in> x \<Longrightarrow> y \<in> P_names" 
proof - 
  assume assms : "x \<in> P_names" "<y, p> \<in> x"
  then obtain a where "Ord(a)" "x \<in> P_set(a)" unfolding P_names_def by auto 
  then have "\<exists>b < a. Ord(b) \<and> y \<in> P_set(b)" using P_set_domain_P_set assms by auto 
  then obtain b where bp :  "Ord(b)" "y \<in> P_set(b)" unfolding oex_def by auto 
  then have "y \<in> M" using P_set_elems_in_M by auto 
  then show "y \<in> P_names" unfolding P_names_def using bp by auto 
qed

lemma P_name_domain_P_name' : 
  "x \<in> P_names \<Longrightarrow> y \<in> domain(x) \<Longrightarrow> y \<in> P_names" 
proof - 
  assume assms : "x \<in> P_names" "y \<in> domain(x)" 
  then obtain p where "<y, p> \<in> x" by auto 
  then show "y \<in> P_names " using assms P_name_domain_P_name by auto 
qed

lemma P_name_range : 
  "x \<in> P_names \<Longrightarrow> <y, p> \<in> x \<Longrightarrow> p \<in> P" 
proof - 
  assume assms : "x \<in> P_names" "<y, p> \<in> x"
  then have "x \<in> Pow(P_set(P_rank(x)) \<times> P) \<inter> M" using P_names_in by auto
  then show "p \<in> P" using assms by auto
qed

lemma domain_P_rank_lt : 
  "x \<in> P_names \<Longrightarrow> <y, p> \<in> x \<Longrightarrow> P_rank(y) < P_rank(x)" 
  thm Least_le
proof - 
  assume assms :  "x \<in> P_names" "<y, p> \<in> x"
  then have p1 : "x \<in> P_set(succ(P_rank(x)))" using P_rank_works by auto 
  have "Ord(succ(P_rank(x)))" unfolding P_rank_def by auto 
  then have "\<exists>b < succ(P_rank(x)). Ord(b) \<and> y \<in> P_set(b)"
    apply (rule_tac x=x and a="succ(P_rank(x))" in P_set_domain_P_set)
    using assms p1 by auto 
  then obtain b where bp : "b < succ(P_rank(x))" "Ord(b)" "y \<in> P_set(b)" unfolding oex_def by auto 
  then have "\<exists>c < b. y \<in> P_set(succ(c))"
    apply (rule_tac  P_set_elems_in_P_set_succ) by auto 
  then obtain c where cp : "c < b" "y \<in> P_set(succ(c))" using oex_def by auto 
  have p3 : "c < P_rank(x)" using lt_le_lt cp bp by auto 
  have "P_rank(y) \<le> c" 
    unfolding P_rank_def 
    apply (rule Least_le) 
    using cp lt_Ord by auto 
  then show "P_rank(y) < P_rank(x)" using p3 le_lt_lt by auto 
qed

lemma P_rank_induct : 
  "(\<forall>x \<in> P_names. ((\<forall> y \<in> P_names. P_rank(y) < P_rank(x) \<longrightarrow> Q(y)) \<longrightarrow> Q(x)))
    \<Longrightarrow> x \<in> P_names \<Longrightarrow> Q(x)" 
proof - 
  fix x 
  assume assms : "x \<in> P_names" "\<forall>x\<in>P_names. (\<forall>y\<in>P_names. P_rank(y) < P_rank(x) \<longrightarrow> Q(y)) \<longrightarrow> Q(x)"
  define R :: "i\<Rightarrow>o" where "R \<equiv> \<lambda>a. \<forall>y \<in> P_names. P_rank(y) = a \<longrightarrow> Q(y)" 
  have "(\<And>a. (\<forall>b \<in> a. R(b)) \<Longrightarrow> R(a))"
    unfolding R_def
    apply clarify 
  proof - 
    fix y 
    assume assms1 : "\<forall>b\<in>P_rank(y). \<forall>z\<in>P_names. P_rank(z) = b \<longrightarrow> Q(z)" "y \<in> P_names" 
    then have "\<forall>z \<in> P_names. P_rank(z) < P_rank(y) \<longrightarrow> Q(z)" 
    proof (clarify) 
      fix z assume assms2 :  "z \<in> P_names" "P_rank(z) < P_rank(y)" 
      then have "P_rank(z) \<in> P_rank(y)" using ltD by auto 
      then show "Q(z)" using assms1 assms2 by auto 
    qed
    then show "Q(y)" using assms assms1 by auto 
  qed
  then have "R(P_rank(x))"
    apply (rule_tac eps_induct) by auto
  then show "Q(x)" unfolding R_def using assms by auto 
qed

lemma set_of_P_names_in_P_set :
  "A \<subseteq> P_names \<Longrightarrow> (\<exists>a. (Limit(a) \<and> (\<forall>x \<in> A. x \<in> P_set(a))))"
  apply(cases "A=0") apply blast
proof - 
  assume assm : "A \<subseteq> P_names" "A \<noteq> 0"
  define F where "F \<equiv> \<lambda>x. (\<mu> a. x \<in> P_set(a) \<and> Limit(a))" 
  then have p1 : "\<And>x. x \<in> A \<Longrightarrow> x \<in> P_set(F(x)) \<and> Limit(F(x))"
  proof - 
    fix x assume "x \<in> A" 
    then have "x \<in> P_names" using assm by auto 
    then obtain a where ap : "Ord(a)" "x \<in> P_set(a)" unfolding P_names_def by auto
    then obtain b where bp : "a < b" "Limit(b)" using ex_larger_limit by auto 
    then have p1 : "P_set(b) = (\<Union>c < b. P_set(c))" using P_set_lim by auto
    have "x \<in> (\<Union>c < b. P_set(c))" 
      apply (rule_tac a=a in OUN_RepFunI) using ap bp by auto
    then have "x \<in> P_set(b)" using p1 by auto 
    then show "x \<in> P_set(F(x)) \<and> Limit(F(x))"
      unfolding F_def 
      apply (rule_tac i=b in LeastI)
      using bp Limit_is_Ord by auto 
  qed
  define I where "I \<equiv> \<Union>{ F(x). x \<in> A }" 
  then have ilim : "Limit(I)" 
    unfolding I_def
    apply (rule_tac Limit_Union)
    using assm p1 by auto
  then have "\<forall> x \<in> A. F(x) \<le> I" 
    apply clarify
    unfolding I_def
    apply (rule_tac a=x and b=F in UN_upper_le) 
    using Limit_is_Ord p1 by auto
  then have "\<forall>x \<in> A. x \<in> P_set(I)"
    apply clarify
    apply (rule_tac i="F(x)" and j=I in leE)
  proof (auto)
    fix x assume "x \<in> A" "F(x) < I" 
    then have "x \<in> (\<Union>c < I. P_set(c))" 
      apply (rule_tac a="F(x)" in OUN_RepFunI)
      using p1 by auto 
    then show "x \<in> P_set(I) " using P_set_lim ilim by auto
  next 
    fix x assume "x \<in> A"
    then show "x \<in> P_set(F(x))" using p1 by auto 
  qed
  then show ?thesis   
    apply (rule_tac x=I in exI)
    using ilim by auto
qed

lemma P_name_iff : "x \<in> P_names \<longleftrightarrow> (x \<in> M \<and> x \<subseteq> P_names \<times> P)" 
proof (rule iffI)
  assume assm : "x \<in> P_names" 
  then obtain a where aH: "Ord(a)" "x \<in> P_set(succ(a))" 
    using P_names_in_P_set_succ 
    by auto 
  then have xsubset : "x \<subseteq> P_set(a) \<times> P" 
    using P_set_succ 
    by auto 
  have "x \<subseteq> P_names \<times> P" 
  proof (rule subsetI)
    fix v assume "v \<in> x" 
    then obtain y p where ypH : "v = <y, p>" "y \<in> P_set(a)" "p \<in> P" using xsubset by auto
    then have "y \<in> P_names" using P_namesI aH by auto
    then show "v \<in> P_names \<times> P" using ypH by auto
  qed
  then show "x \<in> M \<and> x \<subseteq> P_names \<times> P" using P_name_in_M assm by auto
next 
  assume assms : " x \<in> M \<and> x \<subseteq> P_names \<times> P " 
  then have "domain(x) \<subseteq> P_names" by auto 
  then obtain a where aH : "Limit(a)" "\<forall>y \<in> domain(x). y \<in> P_set(a)" 
    using set_of_P_names_in_P_set by blast
  have "x \<subseteq> P_set(a) \<times> P" 
  proof (rule subsetI)
    fix v assume vin : "v \<in> x" 
    then obtain y p where ypH : "y \<in> P_names" "p \<in> P" "v = <y, p>" using assms by auto 
    then have "y \<in> P_set(a)" using vin ypH aH by auto 
    then show "v \<in> P_set(a) \<times> P" using ypH vin by auto
  qed
  then have "x \<in> P_set(succ(a))" using P_set_succ assms by auto
  then show "x \<in> P_names" 
    apply(rule_tac P_namesI)
    using Limit_is_Ord aH 
    by auto
qed

lemma zero_is_P_name : "0 \<in> P_names" 
proof - 
  have p1 : "0 \<in> Pow(0) \<inter> M" using zero_in_M by auto
  have p2 : "Pow(0) \<inter> M = P_set(1)" using P_set_0 P_set_succ by auto 
  then have "0 \<in> P_set(1)" using p1 by auto 
  then show "0 \<in> P_names"
    unfolding P_names_def apply auto  
    using zero_in_M by auto 
qed 

lemma P_rank_zero : "P_rank(0) = 0" 
proof - 
  have p1 : "0 \<in> Pow(0) \<inter> M" using zero_in_M by auto
  have p2 : "Pow(0) \<inter> M = P_set(1)" using P_set_0 P_set_succ by auto 
  then have "0 \<in> P_set(1)" using p1 by auto 
  then show "P_rank(0) = 0" 
    unfolding P_rank_def 
    apply(rule_tac Least_equality, auto)
    done
qed
  
lemma P_name_induct : 
  "\<forall>x \<in> P_names. (\<forall>y. \<forall> p. <y, p> \<in> x \<longrightarrow> Q(y)) \<longrightarrow> Q(x) \<Longrightarrow> x \<in> P_names \<Longrightarrow> Q(x)"
proof (rule_tac P_rank_induct, clarify)
  fix x assume assms: 
    "x \<in> P_names" "\<forall>y\<in>P_names. P_rank(y) < P_rank(x) \<longrightarrow> Q(y)"
    "\<forall>x\<in>P_names. (\<forall>y p. \<langle>y, p\<rangle> \<in> x \<longrightarrow> Q(y)) \<longrightarrow> Q(x)" 
  then have p1 :  "(\<forall>y p. \<langle>y, p\<rangle> \<in> x \<longrightarrow> Q(y)) \<longrightarrow> Q(x)" by auto 
  have p2 : "\<forall>y p. <y, p> \<in> x \<longrightarrow> P_rank(y) < P_rank(x)" 
    using domain_P_rank_lt assms by auto
  
  then have "\<forall>y p. <y, p> \<in> x \<longrightarrow> Q(y)" 
  proof (clarify)
    fix y p assume p30 : "<y, p> \<in> x"
    then have p3 : "P_rank(y) < P_rank(x)" using p2 by auto 
    then have "y \<in> P_names" using P_name_domain_P_name p30 assms by auto 
    then show "Q(y)" using assms p3 by auto 
  qed 
  then show "Q(x)" using assms by auto 
qed
  

lemma check_P_name : "x \<in> M \<longrightarrow> check(x) \<in> P_names" 
  apply (rule_tac P = "\<lambda>x. x \<in> M \<longrightarrow> check(x) \<in> P_names" in eps_induct) 
  apply (clarify)
proof-
  fix x assume assm : "\<forall>y\<in>x. y \<in> M \<longrightarrow> check(y) \<in> P_names" "x \<in> M"
  have p1: "check(x) = { <check(y), one> . y \<in> x }" using def_check by assumption
  then show "check(x) \<in> P_names" 
  proof (cases "x = 0")
    case True
    then have "check(x) = 0" using p1 by auto 
    then show ?thesis using zero_is_P_name by auto 
  next
    case False
    define A where "A \<equiv> { check(y). y \<in> x }" 
    then have asubset:  "A \<subseteq> P_names"
      apply (rule_tac subsetI) 
      using assm transM by auto
    have "A \<noteq> 0" using \<open>x \<noteq> 0\<close> unfolding A_def by auto 
    then have "\<exists> a. (Limit(a) \<and> (\<forall> z \<in> A. z \<in> P_set(a)))"
      using set_of_P_names_in_P_set asubset by auto
    then obtain a where ap : "Limit(a)" "(\<forall> z \<in> A. z \<in> P_set(a))" by auto 
    then have p1:  "check(x) \<in> Pow(P_set(a) \<times> P)" 
      using A_def p1 one_in_P check_in_M by auto 
    then have p2 : "check(x) \<in> Pow(P_set(a) \<times> P) \<inter> M" 
      using check_in_M assm by auto 
    then have "check(x) \<in> P_set(succ(a))" 
      using P_set_succ by auto 
    then show "check(x) \<in> P_names"
      unfolding P_names_def using p2 apply simp 
      apply (rule_tac x="succ(a)" in exI)
      apply simp 
      using ap Limit_is_Ord by auto 
  qed
qed

end
end 