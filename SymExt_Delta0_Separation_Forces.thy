theory SymExt_Delta0_Separation_Forces
  imports 
    "Forcing/Forcing_Main" 
    SymExt_Definition
    HS_M
begin 

context M_symmetric_system 
begin


definition delta0sep_forces_fm_ren where 
  "delta0sep_forces_fm_ren(n) \<equiv> { <0, 0>, <1,4#+n>, <2, 5#+n>, <3, 6#+n>, <4,1>, <5#+n,3#+n>, <6#+n, 2> } \<union> { <5#+k, 3#+k> . k \<in> n }" 

lemma delta0sep_forces_fm_ren_function : "n \<in> nat \<Longrightarrow> function(delta0sep_forces_fm_ren(n))" 
  unfolding function_def delta0sep_forces_fm_ren_def 
  apply clarify 
  apply auto[1]
   apply(rename_tac xa; rule_tac P= "natify(xa) < succ(n)" in mp) 
    apply simp 
  using lt_irrefl 
    apply blast 
   apply(rename_tac xa; rule_tac b="natify(xa)" and a=xa in ssubst) 
    apply(rule natify_ident) 
  using lt_nat_in_nat ltI nat_into_Ord 
    apply blast 
   apply(rule lt_succ_lt) 
  using nat_into_Ord ltI 
    apply simp_all 
  apply(rename_tac xa; subgoal_tac "natify(xa) < succ(n)",  simp)
  using lt_irrefl 
   apply blast 
  apply(rename_tac xa; rule_tac b="natify(xa)" and a=xa in ssubst)
   apply(rule natify_ident, rule lt_nat_in_nat) 
  using ltI nat_into_Ord lt_succ_lt 
  by auto

lemma delta0sep_forces_fm_ren_domain_case : 
  "n \<in> nat \<Longrightarrow> x \<in> domain(delta0sep_forces_fm_ren(n)) \<longleftrightarrow> x = 0 \<or> x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4 \<or> x = 5 #+ n \<or> x = 6 #+ n \<or> (\<exists>k \<in> n. x = 5 #+ k)" 
  unfolding delta0sep_forces_fm_ren_def 
  by auto

lemma delta0sep_forces_fm_ren_range_case : 
  "n \<in> nat \<Longrightarrow> x \<in> range(delta0sep_forces_fm_ren(n)) \<longleftrightarrow> x = 0 \<or> x = 4 #+ n \<or> x = 5 #+ n \<or> x = 6 #+ n \<or> x = 1 \<or> x = 3 #+ n \<or> x = 2 \<or> (\<exists>k \<in> n. x = 3 #+ k)" 
  unfolding delta0sep_forces_fm_ren_def 
  by auto
  
lemma delta0sep_forces_fm_ren_domain : "n \<in> nat \<Longrightarrow> n #+ 7 = domain(delta0sep_forces_fm_ren(n)) "
  apply(rule equality_iffI, rule iff_flip) 
  apply(rename_tac x; rule_tac Q="x = 0 \<or> x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4 \<or> x = 5 #+ n \<or> x = 6 #+ n \<or> (\<exists>k \<in> n. x = 5 #+ k)" in iff_trans)
  using delta0sep_forces_fm_ren_domain_case 
   apply simp 
  apply(rule iffI) 
   apply(erule disjE; simp; rule ltD) 
    apply simp 
   apply(erule disjE; auto) 
   apply(rename_tac k; subgoal_tac "k \<in> nat", simp, rule lt_succ_lt)
     apply simp 
    apply(rule lt_succ_lt) 
     apply simp 
    apply (simp add:ltI)
   apply(rule_tac n=n in lt_nat_in_nat) 
    apply(rule ltI; simp) 
   apply simp 
  apply clarify
proof - 
  fix x assume assms: "n \<in> nat" "x \<in> n #+ 7" "x \<noteq> 0" "x \<noteq> 1" "x \<noteq> 2" "x \<noteq> 3" "x \<noteq> 4" "x \<noteq> 5 #+ n" " \<not> (\<exists>k\<in>n. x = 5 #+ k)"
  then have "7 #+ n \<in> nat" by auto
  then have xnat : "x \<in> nat" 
    apply(rule_tac n="7 #+ n" in lt_nat_in_nat) 
     apply(rule ltI) using assms apply simp_all done 
  then have H: "5 \<le> x \<Longrightarrow> x < 5 #+ n \<Longrightarrow> \<exists>k \<in> n. x = 5 #+ k" 
    apply(rule_tac x="x #- 5" in bexI) 
     apply(rule_tac b = "5 #+ (x #- 5)" and a = "x #- 5 #+ 5" in ssubst) 
      apply simp 
     apply(rule eq_flip)
     apply(rule add_diff_inverse2) 
      apply simp 
     apply simp 
    apply(rule ltD) 
    apply(rule_tac k = 5 in add_lt_elim1) 
      apply(rule_tac b="5 #+ (x #- 5)" and a="x #- 5 #+ 5" in ssubst) 
       apply simp 
      apply(rule_tac b="x #- 5 #+ 5" and a="x" in ssubst) 
       apply(rule add_diff_inverse2) 
        apply (simp_all add:assms) done 
  have "x < 7 #+ n" 
    apply(rule ltI) 
    using assms 
    by auto  
  then have "x < 5 #+ n \<or> x = 5 #+ n \<or> x = 6 #+ n" 
    using le_iff 
    by auto  
  then show "x = 6 #+ n" 
    apply(subgoal_tac "(x < 5 #+ n \<longrightarrow> False) \<and> (x = 5 #+ n \<longrightarrow> False)") 
     apply force 
    apply(rule conjI) 
     apply clarify 
     apply(case_tac "5 \<le> x") 
    using H assms 
      apply (simp add: H assms)
     apply(rule_tac P="x \<le> 4" in mp) 
      apply clarify 
      apply(simp add:le_iff) 
      apply(simp add:assms) 
    using not_le_iff_lt xnat 
     apply force 
    using assms 
    by auto 
qed

lemma delta0sep_forces_fm_ren_range : "n \<in> nat \<Longrightarrow> range(delta0sep_forces_fm_ren(n)) \<subseteq> n #+ 7"
  apply(rule subsetI) 
  apply(rename_tac x; rule_tac P="x = 0 \<or> x = 4 #+ n \<or> x = 5 #+ n \<or> x = 6 #+ n \<or> x = 1 \<or> x = 3 #+ n \<or> x = 2 \<or> (\<exists>k \<in> n. x = 3 #+ k)" in mp) 
   apply(clarify) 
   apply(erule disjE) 
    apply simp 
    apply(rule ltD; simp) 
   apply(erule disjE, force)
   apply(erule disjE, force) 
   apply(erule disjE, force) 
   apply(erule disjE, simp, rule ltD, simp)+
   apply clarify 
   apply(rule_tac ltD) 
   apply(rule_tac j="n #+ 3" in lt_trans) 
    apply(rename_tac k, subgoal_tac "k < n", simp)
     apply(rename_tac k, subgoal_tac "k \<in> nat", force) 
     apply(rule_tac n=n in lt_nat_in_nat) 
      apply (simp add:ltI, simp, simp add:ltI, simp)
  using delta0sep_forces_fm_ren_range_case 
  by auto

lemma delta0sep_forces_fm_ren_type : "n \<in> nat \<Longrightarrow> delta0sep_forces_fm_ren(n) \<in> n #+ 7 \<rightarrow> n #+ 7" 
  apply(rule Pi_memberI) 
  unfolding relation_def 
     apply(simp add:delta0sep_forces_fm_ren_def) 
     apply blast 
  using delta0sep_forces_fm_ren_function 
    apply simp 
   apply(rule delta0sep_forces_fm_ren_domain) 
   apply simp 
  using delta0sep_forces_fm_ren_range 
  apply simp 
  done   

definition delta0sep_forces_fm where 
  "delta0sep_forces_fm(\<phi>) \<equiv> ren(forces(And(Member(0, arity(\<phi>)), \<phi>)))`(arity(\<phi>) #+ 6)`(arity(\<phi>) #+ 6)`delta0sep_forces_fm_ren(arity(\<phi>) #- 1)" 

lemma delta0sep_forces_fm_type : 
  "\<phi> \<in> formula \<Longrightarrow> 1 \<le> arity(\<phi>) \<Longrightarrow> delta0sep_forces_fm(\<phi>) \<in> formula" 
  unfolding delta0sep_forces_fm_def 
  apply(rule ren_tc)
     apply simp_all
  apply(rule_tac b="succ(succ(succ(succ(succ(succ(arity(\<phi>)))))))" and a="(arity(\<phi>) #- 1) #+ 7" in ssubst) 
  apply simp
   apply(rule_tac b="succ(arity(\<phi>) #- 1)" and a="arity(\<phi>) #- 1 #+ 1" in ssubst, simp, rule eq_flip)
   apply(rule add_diff_inverse2, simp, simp)
  apply(rule delta0sep_forces_fm_ren_type, simp)
  done

lemma delta0sep_forces_fm_sats_iff : 
  "\<phi> \<in> formula \<Longrightarrow> env \<in> list(M) \<Longrightarrow> succ(length(env)) = arity(\<phi>) \<Longrightarrow> x \<in> M \<Longrightarrow> v \<in> M \<Longrightarrow> u \<in> M \<Longrightarrow> p \<in> M \<Longrightarrow>
  p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u] @ env @ [x] \<longleftrightarrow> sats(M, delta0sep_forces_fm(\<phi>), [p, u, v] @ env @ [x, P, leq, one])"
proof - 
  assume assms: "\<phi> \<in> formula" "env \<in> list(M)" "succ(length(env)) = arity(\<phi>)" "x \<in> M" "v \<in> M" "u \<in> M" "p \<in> M"

  have arity_sats_iff' : 
    "\<And>p extra env. p \<in> formula \<Longrightarrow> extra \<in> list(M) \<Longrightarrow> env \<in> list(M) \<Longrightarrow> arity(p) \<le> length(env) \<Longrightarrow> sats(M, p, env @ extra) \<longleftrightarrow> sats(M, p, env)"
    using arity_sats_iff by auto 
  
  define n where "n \<equiv> length(env)" 
  have nnat : "n \<in> nat" using n_def length_type assms by auto 

  have neq : "arity(\<phi>) #- 1 = n" 
  proof - 
    have "arity(\<phi>) #- 1 = succ(n) #- 1" 
      using assms n_def by auto
    also have "... = n" 
      using nnat by auto
    finally show "arity(\<phi>) #- 1 = n" by simp
  qed

  have delta0sep_forces_fm_ren_0 : "n \<in> nat \<Longrightarrow> delta0sep_forces_fm_ren(n)`0 = 0"
    apply(rule function_apply_equality) 
    using delta0sep_forces_fm_ren_function delta0sep_forces_fm_ren_def  by auto 
  have delta0sep_forces_fm_ren_1 : "n \<in> nat \<Longrightarrow> delta0sep_forces_fm_ren(n)`1 = 4#+n" 
    apply(rule function_apply_equality) 
    using delta0sep_forces_fm_ren_function delta0sep_forces_fm_ren_def  by auto 
  have delta0sep_forces_fm_ren_2 : "n \<in> nat \<Longrightarrow> delta0sep_forces_fm_ren(n)`2 = 5#+n" 
    apply(rule function_apply_equality) 
    using delta0sep_forces_fm_ren_function delta0sep_forces_fm_ren_def  by auto 
  have delta0sep_forces_fm_ren_3 : "n \<in> nat \<Longrightarrow> delta0sep_forces_fm_ren(n)`3 = 6#+n" 
    apply(rule function_apply_equality) 
    using delta0sep_forces_fm_ren_function delta0sep_forces_fm_ren_def  by auto 
  have delta0sep_forces_fm_ren_4 : "n \<in> nat \<Longrightarrow> delta0sep_forces_fm_ren(n)`4 = 1" 
    apply(rule function_apply_equality) 
    using delta0sep_forces_fm_ren_function delta0sep_forces_fm_ren_def  by auto 
  have delta0sep_forces_fm_ren_5_plus_n : "n \<in> nat \<Longrightarrow> delta0sep_forces_fm_ren(n)`(5#+n) = 3#+n" 
    apply(rule function_apply_equality) 
    using delta0sep_forces_fm_ren_function delta0sep_forces_fm_ren_def  by auto 
  have delta0sep_forces_fm_ren_6_plus_n : "n \<in> nat \<Longrightarrow> delta0sep_forces_fm_ren(n)`(6#+n) = 2" 
    apply(rule function_apply_equality) 
    using delta0sep_forces_fm_ren_function delta0sep_forces_fm_ren_def  by auto 
  have delta0sep_forces_fm_ren_5_plus_k : "\<And>k. n \<in> nat \<Longrightarrow> k \<in> n \<Longrightarrow> delta0sep_forces_fm_ren(n)`(5#+k) = 3#+k" 
    apply(rule function_apply_equality) 
    using delta0sep_forces_fm_ren_function delta0sep_forces_fm_ren_def  by auto 

  define L where "L \<equiv> Cons(p, Cons(P, Cons(leq, Cons(one, Cons(u, env @ [x, v])))))" 
  define L' where "L' \<equiv> Cons(p, Cons(u, Cons(v, env @ [x, P, leq, one])))"

  have nth_env_extra : "\<And>k extra. k \<in> nat \<Longrightarrow> extra \<in> list(M) \<Longrightarrow> nth(n #+ k, env @ extra) = nth(k, extra)" 
  proof - 
    fix k extra assume assms1 : "k \<in> nat" "extra \<in> list(M)"

    have eq : "n #+ k #- n = k" using nnat assms1 by auto

    then have "nth(n #+ k, env @ extra) = (if n #+ k < length(env) then nth(n #+ k, env) else nth(n #+ k #- length(env), extra))"
      using nth_append assms nnat assms1 by auto
    also have "... = nth(n #+ k #- length(env), extra)" 
    proof (rule if_not_P; rule le_imp_not_lt) 
      have "n \<le> n #+ k" using nnat assms1 by auto 
      then show "length(env) \<le> n #+ k" 
        using n_def by auto 
    qed
    also have "... = nth(n #+ k #- n, extra)" 
      using nnat assms1 n_def by auto
    finally show "nth(n #+ k, env @ extra) = nth(k, extra) " 
      using eq by auto
  qed
  have L_nth_5_plus_n : "nth(succ(succ(succ(succ(succ(n))))), L) = x" 
  proof - 
    have "nth(5 #+ n, L) = nth(n #+ 0, env @ [x, v])" 
      unfolding L_def using nnat by auto 
    also have "... = nth(0, [x, v])" 
      apply(rule nth_env_extra) 
      using assms by auto
    finally show "nth(succ(succ(succ(succ(succ(n))))), L) = x" using nnat by auto
  qed
  have L_nth_6_plus_n : "nth(succ(succ(succ(succ(succ(succ(n)))))), L) = v" 
  proof - 
    have "nth(6 #+ n, L) = nth(n #+ 1, env @ [x, v])" 
      unfolding L_def using nnat by auto 
    also have "... = nth(1, [x, v])" 
      apply(rule nth_env_extra) using assms by auto
    finally show "nth(succ(succ(succ(succ(succ(succ(n)))))), L) = v" using nnat by auto
  qed
  have L_nth_5_plus_k : "\<And>k. k \<in> n \<Longrightarrow> nth(5 #+ k, L) = nth(k, env)" 
  proof - 
    fix k assume assms1: "k \<in> n" 
    then have knat: "k \<in> nat" 
      using nat_in_nat nnat by auto
    then have "nth(5 #+ k, L) = nth(k, env @ [x, v])" 
      unfolding L_def by auto 
    also have "... = (if k < length(env) then nth(k, env) else nth(k #- length(env), [x, v]))"
      apply(rule nth_append) 
      using assms knat 
      by auto
    also have "... = nth(k, env)"
      apply(rule if_P;rule ltI) 
      using n_def assms1 nat_in_nat nnat
      by auto
    finally show "nth(5 #+ k, L) = nth(k, env)"
      by auto
  qed
  have L'_nth_3_plus_n : "nth(succ(succ(succ(n))), L') = x" 
  proof - 
    have "nth(3 #+ n, L') = nth(n #+ 0, env @ [x, P, leq, one])" 
      unfolding L'_def using nnat by auto 
    also have "... = nth(0, [x, P, leq, one])" 
      apply(rule nth_env_extra) using assms P_in_M leq_in_M one_in_M by auto
    finally show "nth(succ(succ(succ(n))), L') = x" 
      using nnat by auto
  qed
  have L'_nth_4_plus_n : "nth(succ(succ(succ(succ(n)))), L') = P" 
  proof - 
    have "nth(4 #+ n, L') = nth(n #+ 1, env @ [x, P, leq, one])" 
      unfolding L'_def using nnat by auto 
    also have "... = nth(1, [x, P, leq, one])" 
      apply(rule nth_env_extra) using assms P_in_M leq_in_M one_in_M by auto
    finally show "nth(succ(succ(succ(succ(n)))), L') = P" 
      using nnat by auto
  qed
  have L'_nth_5_plus_n : "nth(succ(succ(succ(succ(succ(n))))), L') = leq" 
  proof - 
    have "nth(5 #+ n, L') = nth(n #+ 2, env @ [x, P, leq, one])" 
      unfolding L'_def using nnat by auto 
    also have "... = nth(2, [x, P, leq, one])" 
      apply(rule nth_env_extra) using assms P_in_M leq_in_M one_in_M by auto
    finally show "nth(succ(succ(succ(succ(succ(n))))), L') = leq" 
      using nnat by auto
  qed
  have L'_nth_6_plus_n : "nth(succ(succ(succ(succ(succ(succ(n)))))), L') = one" 
  proof - 
    have "nth(6 #+ n, L') = nth(n #+ 3, env @ [x, P, leq, one])" 
      unfolding L'_def using nnat by auto 
    also have "... = nth(3, [x, P, leq, one])" 
      apply(rule nth_env_extra) using assms P_in_M leq_in_M one_in_M by auto
    finally show "nth(succ(succ(succ(succ(succ(succ(n)))))), L') = one" 
      using nnat by auto
  qed
  have L'_nth_3_plus_k : "\<And>k. k \<in> n \<Longrightarrow> nth(3 #+ k, L') = nth(k, env)" 
  proof - 
    fix k assume assms1: "k \<in> n" 
    then have knat: "k \<in> nat" 
      using nat_in_nat nnat by auto
    then have "nth(3 #+ k, L') = nth(k, env @ [x, P, leq, one])" 
      unfolding L'_def by auto 
    also have "... = (if k < length(env) then nth(k, env) else nth(k #- length(env), [x, P, leq, one]))"
      apply(rule nth_append) 
      using assms knat 
      by auto
    also have "... = nth(k, env)"
      apply(rule if_P;rule ltI) 
      using n_def assms1 nat_in_nat nnat
      by auto
    finally show "nth(3 #+ k, L') = nth(k, env)"
      by auto
  qed
    
  have "p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u] @ env @ [x] \<longleftrightarrow> sats(M, forces(And(Member(0, arity(\<phi>)), \<phi>)), [p, P, leq, one, u] @ env @ [x])" 
    by auto
  also have "... \<longleftrightarrow> sats(M, forces(And(Member(0, arity(\<phi>)), \<phi>)), [p, P, leq, one, u] @ env @ [ x, v ])" 
    apply(rule_tac b="[p, P, leq, one, u] @ env @ [x, v]" and a="([p, P, leq, one, u] @ env @ [x]) @ [v]" in ssubst)
    using app_assoc assms 
     apply force 
    apply(rule iff_flip) 
    apply(rule arity_sats_iff')
    using assms forces_type P_in_M leq_in_M one_in_M 
       apply simp_all 
    apply(rule_tac j="4 #+ arity(And(Member(0, arity(\<phi>)), \<phi>))" in le_trans) 
     apply(rule arity_forces) 
    apply simp+
    apply(rule Un_least_lt)+
      apply simp_all  
    apply(rule lt_succ_lt) 
    using Ord_nat arity_type 
    by auto 
  also have "... \<longleftrightarrow> sats(M, delta0sep_forces_fm(\<phi>), [p, u, v] @ env @ [x, P, leq, one])" 
    unfolding delta0sep_forces_fm_def 
    apply(rule sats_iff_sats_ren) 
    using assms P_in_M leq_in_M one_in_M 
           apply (simp, simp, simp, simp, simp)
      apply(rule_tac a="(arity(\<phi>) #- 1) #+ 7" and b = "arity(\<phi>) #+ 6" in ssubst)
       apply(rule_tac a="succ(length(env))" and b="arity(\<phi>)" in ssubst) 
    using assms 
        apply simp 
       apply simp 
    using length_type assms 
       apply simp 
      apply(rule delta0sep_forces_fm_ren_type) 
      apply simp 
     apply(rule_tac j="4 #+ arity(And(Member(0, arity(\<phi>)), \<phi>))" in le_trans) 
      apply(rule arity_forces) 
    using assms 
      apply simp 
     apply simp 
    using assms arity_type 
     apply simp 
     apply(rule_tac j="succ(arity(\<phi>))" in le_trans) 
      apply(rule Un_least_lt, rule Un_least_lt, simp_all)
      apply(rule lt_succ_lt, simp_all)+
    using arity_type assms 
    apply simp_all
  proof - 
    fix i assume ileq : "i \<le> succ(succ(succ(succ(succ(arity(\<phi>))))))"
  
    then have inat : "i \<in> nat" 
      apply(rule_tac n = "7 #+ n" in lt_nat_in_nat) using ileq n_def assms by auto 
    then have "i \<in> 7 #+ n" 
      apply(rule_tac ltD) using n_def assms ileq by auto 
    then have "i \<in> domain(delta0sep_forces_fm_ren(n))" 
      using delta0sep_forces_fm_ren_domain assms nnat by auto
    then have H: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5 #+ n \<or> i = 6 #+ n \<or> (\<exists>k \<in> n. i = 5 #+ k)" 
      using delta0sep_forces_fm_ren_domain_case nnat by auto 
  
    have nth_eq : "nth(i, L) = nth(delta0sep_forces_fm_ren(arity(\<phi>) #- 1)`i, L')" 
      apply (subst neq)
      apply(subgoal_tac "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5 #+ n \<or> i = 6 #+ n \<or> (\<exists>k \<in> n. i = 5 #+ k)")
       apply(erule disjE, simp add:L_def L'_def delta0sep_forces_fm_ren_0 nnat) 
       apply(erule disjE, simp add:delta0sep_forces_fm_ren_1 nnat; simp add:L'_nth_4_plus_n nnat)
        apply(simp add:L_def)
       apply(erule disjE, simp add:delta0sep_forces_fm_ren_2 nnat) 
        apply (simp add:L'_nth_5_plus_n nnat L_def)
       apply(erule disjE, simp add:delta0sep_forces_fm_ren_3 nnat) 
        apply (simp add:L'_nth_6_plus_n nnat L_def)
       apply(erule disjE, simp add:delta0sep_forces_fm_ren_4 nnat) 
        apply (simp add: L_def L'_def)
       apply(erule disjE, simp)
        apply(simp add:L_nth_5_plus_n nnat)
      using delta0sep_forces_fm_ren_5_plus_n nnat
        apply simp 
        apply(simp add:delta0sep_forces_fm_ren_5_plus_n L'_nth_3_plus_n nnat) 
       apply(erule disjE, simp)
        apply(simp add:L_nth_6_plus_n nnat)
      using delta0sep_forces_fm_ren_6_plus_n nnat
        apply simp 
        apply(simp add: L'_def nnat) 
       apply clarify 
       apply(rename_tac k; subgoal_tac "k \<in> nat") 
        apply simp 
        apply(rename_tac k; rule_tac b="succ(succ(succ(succ(succ(k)))))" and a="5 #+ k" in ssubst) 
         apply simp
        apply(rename_tac k; rule_tac b="delta0sep_forces_fm_ren(n) ` (5 #+ k)" and a="3 #+ k" in ssubst)
         apply(rule delta0sep_forces_fm_ren_5_plus_k)
          apply(simp add:nnat, simp)
      using L_nth_5_plus_k L'_nth_3_plus_k  nat_in_nat nnat H
      by auto
    then show " nth(i, Cons(p, Cons(P, Cons(leq, Cons(one, Cons(u, env @ [x, v])))))) =
           nth(delta0sep_forces_fm_ren(arity(\<phi>) #- 1) ` i, Cons(p, Cons(u, Cons(v, env @ [x, P, leq, one]))))" 
      unfolding L_def L'_def by simp
  qed
  finally show ?thesis by simp
qed

definition delta0sep_forces_pair_fm where 
  "delta0sep_forces_pair_fm(\<phi>) \<equiv> Exists(Exists(And(pair_fm(1, 0, 2), delta0sep_forces_fm(\<phi>))))" 

lemma delta0sep_forces_pair_fm_iff : 
  "\<phi> \<in> formula \<Longrightarrow> env \<in> list(M) \<Longrightarrow> succ(length(env)) = arity(\<phi>) \<Longrightarrow> x \<in> M \<Longrightarrow> v \<in> M \<Longrightarrow>
  (\<exists>p \<in> M. \<exists>u \<in> M. v = <u, p> \<and> p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u] @ env @ [x]) \<longleftrightarrow> sats(M, delta0sep_forces_pair_fm(\<phi>), [v] @ env @ [x, P, leq, one])" 
  apply(rule iff_flip) 
  unfolding delta0sep_forces_pair_fm_def 
  apply(rule_tac Q="\<exists>p \<in> M. \<exists>u \<in> M. M, [p, u, v] @ env @ [x, P, leq, one] \<Turnstile> And(pair_fm(1, 0, 2), delta0sep_forces_fm(\<phi>))" in iff_trans)
  using P_in_M leq_in_M one_in_M sats_Exists_iff 
   apply force
  using delta0sep_forces_fm_sats_iff
  apply(rule_tac ex_iff; rule_tac ex_iff) 
  apply(rename_tac p u; rule_tac Q="(M, [p, u, v] @ env @ [x, P, leq, one] \<Turnstile> pair_fm(1, 0, 2)) \<and>  (M, [p, u, v] @ env @ [x, P, leq, one] \<Turnstile> delta0sep_forces_fm(\<phi>))" in iff_trans) 
   apply(rule sats_And_iff)
  using P_in_M leq_in_M one_in_M  
   apply simp
  apply(rule iff_conjI)
   apply(rename_tac p u; rule_tac Q="pair(##M, u, p, v)" in iff_trans)
    apply(rule iff_flip; rule pair_iff_sats)
          apply (simp+)
  using P_in_M leq_in_M one_in_M  
    apply simp
  using pair_abs 
   apply simp
  apply(rule iff_flip; rule delta0sep_forces_fm_sats_iff) 
  by auto

lemma and_member_phi_arity : " env \<in> list(A) \<Longrightarrow> \<phi> \<in> formula \<Longrightarrow> arity(\<phi>) = succ(length(env)) \<Longrightarrow> arity(And(Member(0, arity(\<phi>)), \<phi>)) = 1 #+ arity(\<phi>)" 
  apply simp
  apply(rule_tac b="1 \<union> succ(succ(length(env)))" and a = "succ(succ(length(env)))" in ssubst) 
   apply(rule Ord_un_eq2,simp, simp, simp)
  by(rule Ord_un_eq1, auto)

lemma delta0sep_forces_pair_in_M : 
  "A \<in> M \<Longrightarrow> x \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> \<phi> \<in> formula \<Longrightarrow> arity(\<phi>) = succ(length(env)) \<Longrightarrow> 
  { <u, p> \<in> A \<times> P. p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u] @ env @ [x] } \<in> M" 
proof - 
  assume assms : "A \<in> M" "x \<in> M" "env \<in> list(M)" "\<phi> \<in> formula" "arity(\<phi>) = succ(length(env))" 

  then have arityeq: "arity(\<phi>) #+ 6 = arity(\<phi>) #- 1 #+ 7" by auto

  have "arity(delta0sep_forces_fm(\<phi>)) \<le> arity(\<phi>) #+ 6"  
    unfolding delta0sep_forces_fm_def 
    apply(rule_tac arity_ren) 
        apply(simp add:assms, rule forces_type)
    using assms 
        apply (simp, simp, simp)
     apply(subst arityeq, subst arityeq, rule delta0sep_forces_fm_ren_type, simp)
    apply(rule le_trans, rule arity_forces)
    using assms
     apply simp
    apply(subst and_member_phi_arity)
    using assms 
    by auto

  then have H : "arity(delta0sep_forces_pair_fm(\<phi>)) \<le> 4 #+ arity(\<phi>)"
    unfolding delta0sep_forces_pair_fm_def 
    apply simp
    apply(simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
    apply(subgoal_tac "3 \<union> arity(delta0sep_forces_fm(\<phi>)) \<in> nat") 
     apply(rule pred_le, simp, simp)
     apply(rule pred_le, simp, simp)
     apply(rule_tac j="arity(\<phi>) #+ 6" in le_trans, rule Un_least_lt)
       apply simp_all
    apply(rule Un_nat_type, simp)
    apply(rule arity_type, rule delta0sep_forces_fm_type)
    using assms
    by auto

  have "delta0sep_forces_fm(\<phi>) \<in> formula" 
    apply(rule delta0sep_forces_fm_type)
    using assms by auto

  then have sep : "separation(##M, \<lambda>v. sats(M, delta0sep_forces_pair_fm(\<phi>), [v] @ env @ [x, P, leq, one]))"
    apply(rule_tac separation_ax) 
      apply (simp add:delta0sep_forces_pair_fm_def)
    using P_in_M leq_in_M one_in_M assms 
     apply force
    apply(rule le_trans, rule H) 
    using assms P_in_M leq_in_M one_in_M 
    by auto

  define S where "S \<equiv> { v \<in> A \<times> P. sats(M, delta0sep_forces_pair_fm(\<phi>), [v] @ env @ [x, P, leq, one]) }"

  have SinM : "S \<in> M"  
    unfolding S_def 
    apply(rule separation_notation, rule sep)
    using cartprod_closed assms P_in_M
    by auto

  have "S = { v \<in> A \<times> P. \<exists>p \<in> M. \<exists>u \<in> M. v = <u, p> \<and> p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u] @ env @ [x] }"
    unfolding S_def 
    apply(rule iff_eq, rule iff_flip, rule delta0sep_forces_pair_fm_iff) 
    using assms cartprod_closed P_in_M transM pair_in_M_iff 
    by auto 

  also have "... = { <u, p> \<in> A \<times> P.  p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u] @ env @ [x] }"
    apply(rule equality_iffI, rule iffI)
    using assms P_in_M transM 
    by auto

  finally show "{ <u, p> \<in> A \<times> P.  p \<tturnstile> And(Member(0, arity(\<phi>)), \<phi>) [u] @ env @ [x] } \<in> M" 
    using SinM 
    by auto
qed

end
end
