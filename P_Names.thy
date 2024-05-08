theory P_Names
  imports 
    "Forcing/Forcing_Main"
    M_RecFun
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

lemma P_names_in_M : "x \<in> P_names \<Longrightarrow> x \<in> M" 
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

lemma zero_is_P_name : "0 \<in> P_names" 
proof - 
  have p1 : "0 \<in> Pow(0) \<inter> M" using zero_in_M by auto
  have p2 : "Pow(0) \<inter> M = P_set(1)" using P_set_0 P_set_succ by auto 
  then have "0 \<in> P_set(1)" using p1 by auto 
  then show "0 \<in> P_names"
    unfolding P_names_def apply auto  
    using zero_in_M by auto 
qed 
  
lemma P_name_induct : 
  "\<forall>x \<in> P_names. (\<forall>y. \<forall> p. <y, p> \<in> x \<longrightarrow> Q(y)) \<longrightarrow> Q(x) \<Longrightarrow> x \<in> P_names \<Longrightarrow> Q(x)"
  apply (rule_tac P_rank_induct)
proof (clarify)
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

end
end 