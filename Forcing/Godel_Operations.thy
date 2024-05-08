theory Godel_Operations 
  imports 
    ZF 
    "Forcing/Forcing_Main"
    Utilities
begin 

definition BExists where "BExists(x, p) \<equiv> Exists(And(Member(0, x), p))" 

definition \<Delta>0_base where "\<Delta>0_base \<equiv> { p \<in> formula. \<exists> x \<in> nat. \<exists>y \<in> nat. p = Member(x, y) \<or> p = Equal(x, y) }" 
definition \<Delta>0_from where 
  "\<Delta>0_from(X) \<equiv> { p \<in> formula. \<exists>q \<in> X. \<exists>r \<in> X. p = Nand(q, r) } 
               \<union> { p \<in> formula. \<exists>q \<in> X. \<exists>x \<in> nat. p = BExists(x, q) }"
definition \<Delta>0' where "\<Delta>0'(n) \<equiv> nat_rec(n, \<Delta>0_base, \<lambda>m. \<Delta>0_from)" 
definition \<Delta>0 where "\<Delta>0 \<equiv> \<Union>n \<in> nat. \<Delta>0'(n)" 

consts godel_op :: i 
datatype 
  "godel_op" = Var ("x \<in> nat") 
             | G1 ("x \<in> godel_op", "y \<in> godel_op") 
             | G2 ("x \<in> godel_op", "y \<in> godel_op") 
             | G3 ("x \<in> godel_op", "y \<in> godel_op") 
             | G4 ("x \<in> godel_op", "y \<in> godel_op") 
             | G5 ("x \<in> godel_op", "y \<in> godel_op") 
             | G6 ("x \<in> godel_op") 
             | G7 ("x \<in> godel_op") 
             | G8 ("x \<in> godel_op") 
             | G9 ("x \<in> godel_op") 
             | G10 ("x \<in> godel_op") 

consts gop_arity' :: "i \<Rightarrow> i" 
primrec 
  "gop_arity'(Var(x)) = x" 
  "gop_arity'(G1(x, y)) = gop_arity'(x) \<union> gop_arity'(y)" 
  "gop_arity'(G2(x, y)) = gop_arity'(x) \<union> gop_arity'(y)" 
  "gop_arity'(G3(x, y)) = gop_arity'(x) \<union> gop_arity'(y)" 
  "gop_arity'(G4(x, y)) = gop_arity'(x) \<union> gop_arity'(y)" 
  "gop_arity'(G5(x, y)) = gop_arity'(x) \<union> gop_arity'(y)" 
  "gop_arity'(G6(x)) = gop_arity'(x) " 
  "gop_arity'(G7(x)) = gop_arity'(x) " 
  "gop_arity'(G8(x)) = gop_arity'(x) " 
  "gop_arity'(G9(x)) = gop_arity'(x) " 
  "gop_arity'(G10(x)) = gop_arity'(x)"

definition gop_arity where "gop_arity(G) \<equiv> succ(gop_arity'(G))" 
lemma gop_arity [simp] : "gop_arity(G) = succ(gop_arity'(G))" unfolding gop_arity_def by simp

consts gop_eval:: "[i, i] \<Rightarrow> i" 
primrec 
  "gop_eval(Var(x), env) = nth(length(env) #- x #- 1, env)" (* using indices from the end of env, not from the beginning. *)
  "gop_eval(G1(x, y), env) = { gop_eval(x, env), gop_eval(y, env) }" 
  "gop_eval(G2(x, y), env) = gop_eval(x, env) \<times> gop_eval(y, env)" 
  "gop_eval(G3(x, y), env) = { <u, v> \<in> gop_eval(x, env) \<times> gop_eval(y, env). u \<in> v }" 
  "gop_eval(G4(x, y), env) = gop_eval(x, env) - gop_eval(y, env)"
  "gop_eval(G5(x, y), env) = gop_eval(x, env) \<inter> gop_eval(y, env)"
  "gop_eval(G6(x), env) = \<Union>(gop_eval(x, env))" 
  "gop_eval(G7(x), env) = domain(gop_eval(x, env))"
  "gop_eval(G8(x), env) = { <u, v> . <v, u> \<in> gop_eval(x, env) }"
  "gop_eval(G9(x), env) = { <u, w, v> . <u, v, w> \<in> gop_eval(x, env) }"
  "gop_eval(G10(x), env) = { <u, v, w> . <v, w, u> \<in> gop_eval(x, env) }"

lemma gop_arity_nat : 
  fixes G assumes "G \<in> godel_op" 
  shows "gop_arity(G) \<in> nat"
  using assms apply(induct) by auto 

lemma gop_arity'_lt_lemma :
  "\<And>L x y. x \<in> godel_op \<Longrightarrow> y \<in> godel_op \<Longrightarrow> gop_arity'(x) \<union> gop_arity'(y) < L \<Longrightarrow> gop_arity'(x) < L \<and> gop_arity'(y) < L" 
  apply auto apply(rule_tac b="gop_arity'(x) \<union> gop_arity'(y)" in le_lt_lt) apply(rule_tac max_le1) 
  using gop_arity_nat Ord_nat apply simp_all
  apply(rule_tac b="gop_arity'(x) \<union> gop_arity'(y)" in le_lt_lt) apply(rule_tac max_le2) 
  using gop_arity_nat Ord_nat apply simp_all done 

lemma gop_eval_cons : 
  fixes X G M a
  assumes "X \<in> list(M)" "G \<in> godel_op" "gop_arity(G) \<le> length(X)" 
  shows "gop_eval(G, X) = gop_eval(G, Cons(a, X))" 

  apply(rule_tac P = "gop_arity(G) \<le> length(X) \<longrightarrow> gop_eval(G, X) = gop_eval(G, Cons(a, X))" in mp)
  using assms apply simp 
  using \<open>G \<in> godel_op\<close> apply induct 
  apply clarify apply simp using nth_Cons 
  apply(rule_tac b="succ(length(X)) #- x" and a="succ(length(X) #- x)" in ssubst) 
  apply(rule_tac diff_succ) apply (rule_tac lt_succ_lt) 
  using length_type Ord_nat assms apply simp using length_type Ord_nat assms apply simp using length_type Ord_nat assms apply simp
  apply(rule_tac b="succ(length(X) #- x) #- 1" and a = "succ(length(X) #- x #- 1)" in ssubst) 
  apply(rule_tac diff_succ) apply simp apply(rule_tac Q="x < length(X)" in iffD2) apply(rule_tac zero_less_diff) apply simp
  using length_type Ord_nat assms apply simp apply simp using diff_type apply simp apply simp
  apply(simp; rule impI) apply(rule_tac P="gop_arity'(x) < length(X) \<and> gop_arity'(y) < length(X)" in mp) apply simp apply(rule_tac gop_arity'_lt_lemma) apply simp apply simp apply simp
  apply(simp; rule impI) apply(rule_tac P="gop_arity'(x) < length(X) \<and> gop_arity'(y) < length(X)" in mp) apply simp apply(rule_tac gop_arity'_lt_lemma) apply simp apply simp apply simp
  apply(simp; rule impI) apply(rule_tac P="gop_arity'(x) < length(X) \<and> gop_arity'(y) < length(X)" in mp) apply simp apply(rule_tac gop_arity'_lt_lemma) apply simp apply simp apply simp
  apply(simp; rule impI) apply(rule_tac P="gop_arity'(x) < length(X) \<and> gop_arity'(y) < length(X)" in mp) apply simp apply(rule_tac gop_arity'_lt_lemma) apply simp apply simp apply simp
  apply(simp; rule impI) apply(rule_tac P="gop_arity'(x) < length(X) \<and> gop_arity'(y) < length(X)" in mp) apply simp apply(rule_tac gop_arity'_lt_lemma) apply simp apply simp apply simp
  apply simp_all done 

consts list_tuple :: "i \<Rightarrow> i" 
primrec 
  "list_tuple(Nil) = 0"
  "list_tuple(Cons(a, l)) = (if l = Nil then a else <a, list_tuple(l)>)" 

consts list_pi :: "i \<Rightarrow> i" 
primrec 
  "list_pi(Nil) = 0"
  "list_pi(Cons(a, l)) = (if l = Nil then a else a \<times> list_pi(l))" 

lemma list_pi_elem_notation : 
  fixes M X v assumes "Transset(M)" "X \<in> list(M)" "v \<in> list_pi(X)"  
  shows "\<exists>! Y. Y  \<in> list(M) \<and> length(Y) = length(X) \<and> v = list_tuple(Y)" 

  apply(rule_tac P="\<forall>v \<in> list_pi(X). \<exists>! Y. Y \<in> list(M) \<and> length(Y) = length(X) \<and> v = list_tuple(Y)" in mp)
  using assms apply simp 
  using \<open>X \<in> list(M)\<close> apply(induct) apply simp 
proof - 
  fix a l assume assms1 : "a \<in> M" "l \<in> list(M)" "\<forall>v\<in>list_pi(l). \<exists>! Y. Y \<in>list(M) \<and> length(Y) = length(l) \<and> v = list_tuple(Y)" 
  show "\<forall>v\<in>list_pi(Cons(a, l)). \<exists>! Y. Y \<in>list(M) \<and> length(Y) = length(Cons(a, l)) \<and> v = list_tuple(Y)" 
    using \<open>l \<in> list(M)\<close> apply cases 
    apply clarify apply(rule_tac a="[v]" in ex1I) apply simp using assms assms1 unfolding Transset_def apply blast
  proof- 
    fix v x assume assms2: "v \<in> list_pi([a])" "x \<in> list(M) \<and> length(x) = length([a]) \<and> v = list_tuple(x)"
    then have "\<exists>b \<in> M. x = [b]" apply(rule_tac length1_notation) by auto 
    then obtain b where bH : "b \<in> M" "x = [b]" by auto 
    then have "v = b" using assms2 by auto 
    then show "x = [v]" using bH by auto 
  next  
    fix hd tl assume assms2 : "l = Cons(hd, tl)" "hd \<in> M" "tl \<in> list(M)"
    show " \<forall>v\<in>list_pi(Cons(a, l)). \<exists>!Y. Y \<in> list(M) \<and> length(Y) = length(Cons(a, l)) \<and> v = list_tuple(Y)" 
      apply clarify 
    proof - 
      fix v assume vin : "v \<in> list_pi(Cons(a, l))"  
      then have "list_pi(Cons(a, l)) = a \<times> list_pi(l)" using assms2 apply simp done 
      then obtain x y where xyH : "v = <x, y>" "x \<in> a" "y \<in> list_pi(l)" using vin by auto 
      then obtain Y where YH : "Y \<in> list(M)" "length(Y) = length(l)" "y = list_tuple(Y)" using assms1 by auto 

      define Z where "Z \<equiv> Cons(x, Y)" 
      then have ZH: "Z \<in> list(M) \<and> length(Z) = length(Cons(a, l)) \<and> v = list_tuple(Z)" 
        using YH apply auto
        using assms2 apply simp using assms2 apply simp using assms2 apply simp
        using xyH assms assms1 unfolding Transset_def apply blast 
        using xyH YH by auto 

      then show "\<exists>!Z. Z \<in> list(M) \<and> length(Z) = length(Cons(a, l)) \<and> v = list_tuple(Z)" 
        apply(rule_tac a=Z in ex1I) apply simp 
      proof - 
        fix W assume WH: "W \<in> list(M) \<and> length(W) = length(Cons(a, l)) \<and> v = list_tuple(W)"
        then have "\<exists> Wh \<in> M. \<exists> Wt \<in> list(M). W = Cons(Wh, Wt)" 
          apply(rule_tac not_nil_obtain_hd_tl) by auto 
        then obtain Wh Wt where WhtH : "Wh \<in> M" "Wt \<in> list(M)" "W = Cons(Wh, Wt)" by auto 
        then have H1: "length(Wt) = length(l)" using WH by auto 
        then have "Wt \<noteq> Nil" using assms2 by auto 
        then have "v = <Wh, list_tuple(Wt)>" using WH WhtH by auto 
        then have H2: "x = Wh" "y = list_tuple(Wt)" using xyH YH apply auto done 
        then have "Wt = Y" 
          apply(rule_tac P="\<lambda>Y. Y \<in> list(M) \<and> length(Y) = length(l) \<and> y = list_tuple(Y)" in ex1_equalsE)  
          using assms1 xyH H1 WhtH YH apply simp_all done 
        then show "W=Z" unfolding Z_def using WhtH H2 by auto
      qed
    qed
  qed
qed

definition gop where 
  "gop(M, \<phi>, n, F) \<equiv>  
    0 < n \<and> arity(\<phi>) \<le> n \<and>
    (\<forall>X \<in> list(M). length(X) = n \<longrightarrow> gop_eval(F, X) = { list_tuple(Y) .. Y \<in> list(M), length(Y) = length(X) \<and> list_tuple(Y) \<in> list_pi(X) \<and>  M, Y \<Turnstile> \<phi> })"

lemma gop_pi :
  fixes M n
  assumes transM : "Transset(M)" and nin : "n \<in> nat" and nnonzero : "n \<noteq> 0" 
  shows "\<exists>G \<in> godel_op. gop_arity(G) = n \<and> (\<forall>X \<in> list(M). length(X) = n \<longrightarrow> gop_eval(G, X) = list_pi(X))" 

  apply(rule_tac P="\<forall>n \<in> nat. n \<noteq> 0 \<longrightarrow> (\<exists>G \<in> godel_op. gop_arity(G) = n \<and> (\<forall> X \<in> list(M). length(X) = n \<longrightarrow> gop_eval(G, X) = list_pi(X)))" in mp)  
  using nin nnonzero apply simp 
  apply(rule ballI)
  apply(rule_tac P="\<lambda>n. n \<noteq> 0 \<longrightarrow> ( \<exists>G\<in>godel_op. gop_arity(G) = n \<and> (\<forall>X\<in>list(M). length(X) = n \<longrightarrow> gop_eval(G, X) = list_pi(X)))" in nat_induct)
  apply simp apply simp
  apply(rule_tac n=x in natE) apply simp apply (rule impI)
  apply(rule_tac x="Var(0)" in bexI) apply simp  apply(clarify)
  apply(rule_tac A=M and P="\<lambda>a. X = [a]" in bexE) using length1_notation apply simp apply simp using Var apply simp
  apply(rule_tac P="x \<noteq> 0" in mp) apply simp_all
proof -
  fix n'
  assume n'in : "n' \<in> nat"
  and ih: "\<exists>F\<in>godel_op. gop_arity'(F) = n' \<and> (\<forall>X\<in>list(M). length(X) = succ(n') \<longrightarrow> gop_eval(F, X) = list_pi(X))"
       
  define n where "n \<equiv> succ(n')" 
  obtain F where FH : "F \<in> godel_op" "gop_arity(F) = n" "(\<forall>X\<in>list(M). length(X) = n \<longrightarrow> gop_eval(F, X) = list_pi(X))" using ih n_def by auto 
  define G where "G \<equiv> G2(Var(n), F)" 

  have Garity : "gop_arity(G) = succ(n)" 
    unfolding G_def apply simp apply(rule_tac equality_iffI; rule iffI) apply auto using FH by auto 

  have "\<forall>X\<in>list(M). length(X) = succ(n) \<longrightarrow> gop_eval(G, X) = list_pi(X)"  
  proof (clarify)
    fix X assume Xin : "X \<in> list(M)" and Xlen : "length(X) = succ(n)"
    show "gop_eval(G, X) = list_pi(X)" 
      using Xin apply(cases) using length_is_0_iff Xlen apply simp 
    proof - 
      fix a X' assume H : "X = Cons(a, X')" "a \<in> M" "X' \<in> list(M)" 
      then have X'len : "length(X') = n" using Xlen by auto 
      then have "list_pi(X') = gop_eval(F, X')" using FH H n_def by auto 
      also have "... = gop_eval(F, Cons(a, X'))" apply(rule_tac gop_eval_cons) using H X'len FH by auto 
      finally have evalF : "gop_eval(F, X) = list_pi(X')" using H by auto 

      have H1 : "length(X) = n #+ 1" using Xlen add_0 n_def n'in  by auto
      have "length(X) #- n #- 1 = length(X) #- (n #+ 1)" using diff_diff_left by auto
      also have "... = length(X) #- length(X)" using H1 by auto 
      also have "... = 0" by auto 
      finally have eq0 :  "length(X) #- n #- 1 = 0 " by simp

      have "gop_eval(G, X) = nth(length(X) #- n #- 1, X) \<times> list_pi(X')" unfolding G_def using evalF by simp 
      also have "... = a \<times> list_pi(X')" using eq0 H by auto  
      also have "... = list_pi(X)" 
        using H apply simp apply clarify apply (rule_tac P="X' \<noteq> []" in mp) apply simp 
        using X'len unfolding n_def apply simp done 
      finally show "gop_eval(G, X) = list_pi(X)" by auto 
    qed
  qed

  then show "\<exists>G\<in>godel_op. gop_arity'(G) = succ(n') \<and> (\<forall>X\<in>list(M). length(X) = succ(succ(n')) \<longrightarrow> gop_eval(G, X) = list_pi(X))" 
    apply(rule_tac x=G in bexI) 
    using Garity unfolding n_def apply simp unfolding G_def n_def using FH n'in by auto
qed

lemma equivalent_gop : 
  fixes M \<phi> \<psi> a n F 
  assumes "Transset(M)" "F \<in> godel_op" "gop(M, \<phi>, n, F)" "\<phi> \<in> formula" "\<psi> \<in> formula" "arity(\<phi>) = arity(\<psi>)" "n \<in> nat"
          "\<forall>env \<in> list(M). arity(\<phi>) \<le> length(env) \<longrightarrow> (M, env \<Turnstile> \<phi> \<longleftrightarrow> M, env \<Turnstile> \<psi>)" 
  shows "gop(M, \<psi>, n, F)" 
  unfolding gop_def 
  apply auto using assms gop_def apply simp using assms gop_def apply simp 
proof -
  fix X assume assms1 : "X \<in> list(M)" "n = length(X)" 
  then have H: "arity(\<phi>) \<le> length(X)" using assms gop_def by auto 
  then have "gop_eval(F, X) = {list_tuple(Y) .. Y \<in> list(M), length(Y) = length(X) \<and> list_tuple(Y) \<in> list_pi(X) \<and>  M, Y \<Turnstile> \<phi> }" 
    using assms assms1 unfolding gop_def by auto 
  also have "... = {list_tuple(Y) .. Y \<in> list(M),  length(Y) = length(X) \<and> list_tuple(Y) \<in> list_pi(X) \<and>  M, Y \<Turnstile> \<psi>}" 
    apply(rule equality_iffI; rule iffI) apply auto 
    apply(rule_tac x=Y in bexI) apply auto using assms H apply auto done 
  finally show "gop_eval(F, X) = {list_tuple(Y) .. Y \<in> list(M),  length(Y) = length(X) \<and> list_tuple(Y) \<in> list_pi(X) \<and>  M, Y \<Turnstile> \<psi>}"  by simp 
qed

lemma gop_neg : 
  fixes M \<phi> n F
  assumes "Transset(M)" "F \<in> godel_op" "gop(M, \<phi>, n, F)" "\<phi> \<in> formula" "n \<in> nat" 
  shows "\<exists>G \<in> godel_op. gop(M, Neg(\<phi>), n, G)" 
proof -
  have "n \<noteq> 0" using assms gop_def by auto
  then have " \<exists>G\<in>godel_op. gop_arity(G) = n \<and> (\<forall>X\<in>list(M). length(X) = n \<longrightarrow> gop_eval(G, X) = list_pi(X))" 
    apply(rule_tac gop_pi) using assms by auto
  then obtain P where PH: "P \<in> godel_op" "gop_arity(P) = n" "(\<forall>X \<in> list(M). length(X) = n \<longrightarrow> gop_eval(P, X) = list_pi(X))" 
    using gop_pi assms by auto 

  define G where "G \<equiv> G4(P, F)" 
  show ?thesis 
    apply(rule_tac x=G in bexI) 
    unfolding gop_def apply (rule_tac P="0 < n \<and> arity(\<phi>) \<le> n" in mp) apply simp apply clarify 
    apply(rule_tac equality_iffI)
    unfolding G_def
  proof -
    fix v X assume XH : "n = length(X)" "X \<in> list(M)"
    have p1:"v \<in> gop_eval(G4(P, F), X) \<longleftrightarrow> v \<in> gop_eval(P, X) \<and> v \<notin> gop_eval(F, X)" apply simp done 
    have p2: "... \<longleftrightarrow> v \<in> list_pi(X) \<and> v \<notin> gop_eval(F, X)" using PH XH by auto 
    have p3: "... \<longleftrightarrow> (v \<in> list_pi(X) \<and> v \<notin> SepReplace(list(M), list_tuple, \<lambda>Y. (length(Y) = length(X) \<and> list_tuple(Y) \<in> list_pi(X) \<and> M, Y \<Turnstile> \<phi>)))"
      using assms XH unfolding gop_def by auto thm SepReplace_iff 
    have p4: "... \<longleftrightarrow> v \<in> list_pi(X) \<and> \<not>(\<exists>Y \<in> list(M). v=list_tuple(Y)\<and>length(Y) = length(X) \<and> list_tuple(Y) \<in> list_pi(X) \<and> M, Y \<Turnstile> \<phi>)" 
      using SepReplace_iff by auto 
    have p5: "... \<longleftrightarrow> v \<in> list_pi(X) \<and> (\<forall>Y \<in> list(M). v=list_tuple(Y) \<longrightarrow> length(Y) = length(X) \<longrightarrow> list_tuple(Y) \<in> list_pi(X) \<longrightarrow> \<not>( M, Y \<Turnstile> \<phi>))" 
      by auto 
    have p6: "... \<longleftrightarrow> v \<in> list_pi(X) \<and> (\<exists>Y \<in> list(M). v=list_tuple(Y)\<and>length(Y) = length(X) \<and> list_tuple(Y) \<in> list_pi(X) \<and> \<not>(M, Y \<Turnstile> \<phi>))" 
      using list_pi_elem_notation assms XH by blast  
    have p7: "... \<longleftrightarrow> v \<in> SepReplace(list(M), list_tuple, \<lambda>Y. (length(Y) = length(X) \<and> list_tuple(Y) \<in> list_pi(X) \<and> M, Y \<Turnstile> Neg(\<phi>)))"
      by auto  
    show "v \<in> gop_eval(G4(P, F), X) \<longleftrightarrow>
          v \<in> SepReplace(list(M), list_tuple, \<lambda>Y. (length(Y) = length(X) \<and> list_tuple(Y) \<in> list_pi(X) \<and> M, Y \<Turnstile> Neg(\<phi>)))"
      using p1 p2 p3 p4 p5 p6 p7 by auto 
  next show "0 < n \<and> arity(\<phi>) \<le> n" using assms gop_def by auto 
  next show "G4(P, F) \<in> godel_op" using PH assms G4 by auto 
  qed
qed

lemma gop_and : 
  fixes M \<phi> \<psi> n F G
  assumes "Transset(M)" "F \<in> godel_op" "G \<in> godel_op"  "gop(M, \<phi>, n, F)" "gop(M, \<psi>, n, G)" "n \<in> nat" "\<phi> \<in> formula" "\<psi> \<in> formula"
  shows "\<exists>H \<in> godel_op. gop(M, And(\<phi>, \<psi>), n, H)" 
  apply(rule_tac x="G5(F, G)" in bexI)  
  unfolding gop_def apply(rule_tac P="0 < n \<and> arity(And(\<phi>, \<psi>)) \<le> n" in mp) apply simp apply clarify
  apply(rule_tac b="gop_eval(F, X)" and a="{ list_tuple(Y) .. Y \<in> list(M), length(Y) = length(X) \<and> list_tuple(Y) \<in> list_pi(X) \<and>  M, Y \<Turnstile> \<phi> }" in ssubst) 
  using assms gop_def apply simp
  apply(rule_tac b="gop_eval(G, X)" and a="{ list_tuple(Y) .. Y \<in> list(M), length(Y) = length(X) \<and> list_tuple(Y) \<in> list_pi(X) \<and>  M, Y \<Turnstile> \<psi> }" in ssubst) 
  using assms gop_def apply simp 
  apply(rule_tac b="{ list_tuple(Y) .. Y \<in> list(M), length(Y) = length(X) \<and> list_tuple(Y) \<in> list_pi(X) \<and>  M, Y \<Turnstile> \<phi> } 
                  \<inter> { list_tuple(Y) .. Y \<in> list(M), length(Y) = length(X) \<and> list_tuple(Y) \<in> list_pi(X) \<and>  M, Y \<Turnstile> \<psi> }" 
    and a="{list_tuple(Y) .. Y \<in> list(M), length(Y) = length(X) \<and> list_tuple(Y) \<in> list_pi(X) \<and>  M, Y \<Turnstile> \<phi> \<and>  M, Y \<Turnstile> \<psi> }" in ssubst)
  apply(rule equality_iffI) using SepReplace_iff list_pi_elem_notation  apply auto 
  apply(rule_tac x=Y in bexI) apply(rule_tac P="Y = Ya" in mp) apply blast
  apply(rule_tac P="\<lambda>Y. Y \<in> list(M) \<and> length(Y) = length(X) \<and> list_tuple(Ya) = list_tuple(Y)" in ex1_equalsE)
  apply(rule_tac list_pi_elem_notation) using assms apply simp_all 
  using gop_def apply simp 
proof - 
  have H1: "arity(\<phi>) \<le> n" "arity(\<psi>) \<le> n" using assms gop_def by auto
  have H2: " Ord(arity(\<phi>))" " Ord(arity(\<psi>))" using assms Ord_nat arity_type by auto
  show "arity(\<phi>) \<union> arity(\<psi>) \<le> n" thm Ord_Un_if
    apply(rule_tac b="arity(\<phi>) \<union> arity(\<psi>)" and a = "(if arity(\<psi>) < arity(\<phi>) then arity(\<phi>) else arity(\<psi>))" in ssubst)
    apply(rule_tac Ord_Un_if) using H2 apply simp_all 
    using assms H1 by auto 
qed

lemma gop_nand : 
  fixes M \<phi> \<psi> n F G
  assumes "Transset(M)" "F \<in> godel_op" "G \<in> godel_op"  "gop(M, \<phi>, n, F)" "gop(M, \<psi>, n, G)" "\<phi> \<in> formula" "\<psi> \<in> formula" "n \<in> nat"
  shows "\<exists>H \<in> godel_op. gop(M, Nand(\<phi>, \<psi>), n, H)" 
proof - 
  have "\<exists>A \<in> godel_op. gop(M, And(\<phi>, \<psi>), n, A)" apply(rule_tac gop_and) using assms by auto 
  then obtain A where "A \<in> godel_op" "gop(M, And(\<phi>, \<psi>), n, A)" by auto 
  then have "\<exists>B \<in> godel_op. gop(M, Neg(And(\<phi>, \<psi>)), n, B)"  apply(rule_tac F=A in gop_neg) using assms by auto 
  then obtain B where "B \<in> godel_op" "gop(M, Neg(And(\<phi>, \<psi>)), n, B)" by auto 
  then show ?thesis 
    apply(rule_tac x=B in bexI) apply(rule_tac \<phi>="Neg(And(\<phi>, \<psi>))" in equivalent_gop) 
    using assms by auto
qed 

(*
lemma gop_bexists :
  fixes M \<phi> F n 
  assumes "Transset(M)" "F \<in> godel_op" "gop(M, \<phi>, succ(n), F)" "\<phi> \<in> formula" "n \<in> nat" 
  shows "\<exists>G \<in> godel_op. gop(M, BExists(x, \<phi>), G)" *)

lemma gop_mem : 
  fixes M a b n
  assumes "Transset(M)" "a \<in> nat" "b \<in> nat" "n \<in> nat" "a < n" "b < n"  
  shows "\<exists>G \<in> godel_op. gop(M, Member(a, b), n, G)"
proof- 
  define G where "G \<equiv> G3(Var(n #- a #- 1), Var(n #- b #- 1))"

  



theorem godel_normal_form_theorem : 
  fixes \<phi>
  assumes "\<phi> \<in> \<Delta>0" "1 \<le> arity(\<phi>)"
  shows "\<exists>F \<in> godel_op. \<forall>A \<in> M. \<forall>env \<in> list(M). arity(\<phi>) \<le> succ(env) \<longrightarrow> gop_eval(F, env) = { x \<in> A. M, [x] @ env \<Turnstile> \<phi> }"  
  thm nat_induct

end
end
