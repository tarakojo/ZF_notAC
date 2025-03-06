theory Wellord_AC 
  imports NotAC_Proof 
begin 

schematic_goal in_vim_fm_auto:
  assumes
    "a \<in> M" "f \<in> M" "x \<in> M"
    "i \<in> nat" "j \<in> nat" "k \<in> nat" 
    "nth(i,env) = a"    
    "nth(j,env) = f"    
    "nth(k,env) = x"    
    "env \<in> list(M)" 
  shows 
    "(\<exists>sx \<in> M. \<exists>cf \<in> M. \<exists>vim \<in> M. is_singleton(##M, x, sx) \<and> is_converse(##M, f, cf) \<and> image(##M, cf, sx, vim) \<and> a \<in> vim)  \<longleftrightarrow> sats(M,?fm(i,j,k),env)"
  unfolding is_converse_def is_singleton_def
  by (insert assms ; (rule sep_rules | simp)+)

context M_ZF_trans begin

definition in_vim_fm where "in_vim_fm(i,j,k) \<equiv> 
             Exists
              (Exists
                (Exists
                  (And(Exists(And(empty_fm(0), cons_fm(succ(succ(succ(succ(k)))), 0, 3))),
                       And(Forall
                            (Iff(Member(0, 2),
                                 Exists
                                  (And(Member(0, succ(succ(succ(succ(succ(j)))))),
                                       Exists(Exists(And(pair_fm(1, 0, 2), pair_fm(0, 1, 3)))))))),
                           And(image_fm(1, 2, 0), Member(succ(succ(succ(i))), 0))))))) "

lemma in_vim_fm_type :
  "i \<in> nat \<Longrightarrow> j \<in> nat \<Longrightarrow> k \<in> nat \<Longrightarrow> in_vim_fm(i,j,k) \<in> formula" 
  unfolding in_vim_fm_def
  by auto

lemma arity_in_vim_fm : 
  "i \<in> nat \<Longrightarrow> j \<in> nat \<Longrightarrow> k \<in> nat \<Longrightarrow> arity(in_vim_fm(i,j,k)) \<le> succ(i) \<union> succ(j) \<union> succ(k)" 
  unfolding in_vim_fm_def
  apply (simp del:FOL_sats_iff add: fm_defs nat_simp_union) 
  apply auto
  using not_le_iff_lt
        apply simp_all
        apply(rule le_trans, simp, simp)
       apply(rule lt_succ_lt, simp, simp)+
     apply(rule lt_succ_lt, simp, rule lt_le_lt, simp, simp)
    apply(rule lt_asym)
     apply auto[2]
  using lt_succ_lt
  by auto

lemma in_vim_fm_sats_iff : 
  fixes a f x
  assumes
    "a \<in> M" "f \<in> M" "x \<in> M"
    "i < length(env)" "j < length(env)" "k < length(env)" 
    "nth(i,env) = a"    
    "nth(j,env) = f"    
    "nth(k,env) = x"    
    "env \<in> list(M)" 
  shows "a \<in> f -`` {x} \<longleftrightarrow> sats(M,in_vim_fm(i,j,k),env)"
proof - 
  have "a \<in> f -`` {x} \<longleftrightarrow> (\<exists>sx \<in> M. \<exists>cf \<in> M. \<exists>vim \<in> M. is_singleton(##M, x, sx) \<and> is_converse(##M, f, cf) \<and> image(##M, cf, sx, vim) \<and> a \<in> vim)" (is "_ \<longleftrightarrow> ?P")
    using image_abs singleton_abs vimage_def converse_abs pair_abs singleton_in_MI assms nth_closed converse_closed image_closed
    by auto
  also have "?P \<longleftrightarrow> sats(M,in_vim_fm(i,j,k),env)" 
    unfolding in_vim_fm_def 
    apply(rule in_vim_fm_auto)
    using in_vim_fm_auto assms nth_closed lt_nat_in_nat length_type
    by auto
  ultimately show ?thesis by auto
qed

definition in_vim_least_rel_fm where 
  "in_vim_least_rel_fm(f, x) \<equiv> 
    Exists(Exists(Exists(Exists(
      And(pair_fm(2,3,succ(succ(succ(succ(x))))), 
      And(least_fm(in_vim_fm(0, succ(succ(succ(succ(succ(f))))), 3), 0), 
      And(least_fm(in_vim_fm(0, succ(succ(succ(succ(succ(f))))), 4), 1),
          Member(0, 1))))))))"

lemma in_vim_least_rel_fm_type : 
  fixes f x 
  assumes "f \<in> nat" "x \<in> nat" 
  shows "in_vim_least_rel_fm(f, x) \<in> formula" 
  unfolding in_vim_least_rel_fm_def
  apply(subgoal_tac "in_vim_fm(0, succ(succ(succ(succ(succ(f))))), 3) \<in> formula")
   apply(subgoal_tac "in_vim_fm(0, succ(succ(succ(succ(succ(f))))), 4) \<in> formula")
  using assms
    apply force
  using in_vim_fm_def assms
  by auto

lemma union_le1 : 
  fixes i j k
  assumes "Ord(j)" "Ord(k)" "i \<le> j" 
  shows "i \<le> j \<union> k" 
  apply(rule_tac j=j in le_trans)
  using assms max_le1 
  by auto

lemma union_le2 : 
  fixes i j k
  assumes "Ord(j)" "Ord(k)" "i \<le> k" 
  shows "i \<le> j \<union> k" 
  apply(rule_tac j=k in le_trans)
  using assms max_le2 
  by auto

lemma arity_least_fm : 
  fixes p i 
  assumes "p \<in> formula" "i \<in> nat" 
  shows "arity(least_fm(p, i)) \<le> succ(i) \<union> pred(arity(p))" 

  unfolding least_fm_def
  using assms
  apply simp
  apply(subst arity_empty_fm, simp add:assms)
  apply(rule Un_least_lt)
   apply simp
   apply(rule union_lt1)
  apply auto[4]
  apply(rule Un_least_lt)+
    apply(rule max_le1)
     apply auto[2]
   apply(rule pred_le)
     apply auto[2]
   apply(rule Un_least_lt)
    apply auto[1]
     apply(subst succ_Un_distrib)
     apply auto[2]
     apply(subst succ_Un_distrib)
     apply auto[2]
  apply(rule union_lt2)
      apply auto[4]
   apply(case_tac "arity(p) = 0")
    apply auto[1]
  using succ_pred_eq 
   apply auto[1]
   apply(rule Un_least_lt)
   apply(rule pred_le)
     apply auto[2]
   apply(rule Un_least_lt)
     apply(subst succ_Un_distrib)
      apply auto[3]
    apply(rule union_le2)
      apply auto[3]
   apply(case_tac "arity(p) = 0")
    apply auto[1]
  using succ_pred_eq 
   apply auto[1]
   apply(rule Un_least_lt, simp)
    apply auto[1]
   apply(rule union_lt1)
  apply auto[4]
   apply(rule pred_le)
     apply auto[2]
   apply(rule Un_least_lt)+
    apply auto[1]
   apply(rule Un_least_lt)+
    apply auto[1]
   apply simp
   apply(rule union_lt1)
      apply auto[4]
     apply(subst succ_Un_distrib)
      apply auto[3]
  apply(rule union_le2)
    apply auto[2]
   apply(case_tac "arity(p) = 0")
    apply auto[1]
  using succ_pred_eq
  by auto

lemma arity_vim_least_rel_fm : 
  fixes f x 
  assumes "f \<in> nat" "x \<in> nat" 
  shows "arity(in_vim_least_rel_fm(f, x)) \<le> succ(f) \<union> succ(x)"
  unfolding in_vim_least_rel_fm_def
  apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union) 
  apply(subgoal_tac "least_fm(in_vim_fm(0, succ(succ(succ(succ(succ(f))))), 3), 0) \<in> formula")
   apply(subgoal_tac "least_fm(in_vim_fm(0, succ(succ(succ(succ(succ(f))))), 4), 1) \<in> formula")
   apply(subgoal_tac "in_vim_fm(0, succ(succ(succ(succ(succ(f))))), 3) \<in> formula")
   apply(subgoal_tac "in_vim_fm(0, succ(succ(succ(succ(succ(f))))), 4) \<in> formula")
  using assms arity_type
    apply(rule_tac pred_le, simp, simp)+
  apply(rule Un_least_lt)
    apply(rule_tac pred_le, simp, simp)+
  apply(rule Un_least_lt, simp)
    apply(rule_tac pred_le, simp, simp)+
     apply(rule Un_least_lt, simp)+
      apply(simp, rule union_lt2, simp, simp, simp, simp)
     apply(rule Un_least_lt, simp)+
      apply(simp, rule union_lt2, simp, simp, simp, simp)
    apply(rule_tac pred_le, simp, simp)+
     apply(rule Un_least_lt, simp)+
      apply(simp, rule union_lt2, simp, simp, simp, simp)
     apply simp
    apply(rule Un_least_lt, simp)+
     apply(subst succ_Un_distrib, simp, simp)+
     apply(rule union_lt1, simp, simp, simp)
     apply(rule le_trans, rule arity_least_fm, rule in_vim_fm_type, simp, simp, simp, simp)
     apply(rule Un_least_lt, simp)+
     apply(rule pred_le, simp, simp)
     apply(rule le_trans, rule arity_in_vim_fm, simp, simp, simp)
     apply(rule Un_least_lt)+
       apply (simp, simp, simp)
     apply(rule Un_least_lt)+
     apply(rule le_trans, rule arity_least_fm, rule in_vim_fm_type, simp, simp, simp, simp)
     apply(rule Un_least_lt, simp)+
     apply(rule pred_le, simp, simp)
     apply(rule le_trans, rule arity_in_vim_fm, simp, simp, simp)
     apply(rule Un_least_lt, simp)+
      apply(subst succ_Un_distrib, simp, simp)+
        apply(rule union_lt1, simp, simp, simp, simp, simp)+
      apply simp
  using assms in_vim_fm_type least_fm_type
  apply auto
  done 

definition vim_least where "vim_least(f, x) \<equiv> \<mu> a. a \<in> (f -`` {x})" 

lemma vim_least_closed : 
  fixes f x 
  assumes "f \<in> M" "x \<in> M" 
  shows "vim_least(f, x) \<in> M" 
  apply(rule to_rin)
  unfolding vim_least_def 
  apply(rule Least_closed, rule transM, simp)
  using assms vimage_closed singleton_in_M_iff 
  by auto
  
lemma in_vim_least_rel_fm_sats_iff : 
  fixes f x 
  assumes 
    "f \<in> M" "x \<in> M" "s \<in> M" "t \<in> M" "env \<in> list(M)"
    "i < length(env)" "j < length(env)"
    "nth(i,env) = f"    
    "nth(j,env) = x"
    "x = <s, t>" 
  shows "vim_least(f, s) < vim_least(f, t) \<longleftrightarrow> sats(M, in_vim_least_rel_fm(i, j), env)"

  apply(rule_tac Q="(\<exists>t' \<in> M. \<exists>s' \<in> M. \<exists>b \<in> M. \<exists>a \<in> M. x = <s', t'> \<and> a = vim_least(f, s) \<and> b = vim_least(f, t) \<and> a < b)" in iff_trans)
  using assms
   apply simp
  using vim_least_closed
  apply force
  apply(rule iff_flip)
  unfolding in_vim_least_rel_fm_def
  apply(rule iff_trans, rule sats_Exists_iff, simp add:assms, rule bex_iff)+
  apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
   apply(rule iff_trans, rule sats_pair_fm, simp, simp)
  using assms lt_nat_in_nat length_type
     apply auto[3]
  apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
   apply(rule iff_trans, rule_tac P="\<lambda>a. a \<in> f -`` {s}" in sats_least_fm)
  apply(rule in_vim_fm_sats_iff)
  using assms lt_nat_in_nat length_type zero_in_M
                apply auto[13]
   apply (simp add:vim_least_def)
   apply(rule_tac Q="\<lambda>a. a \<in> f -`` {s}" in least_abs)
    apply(rule transM, simp)
  using assms vimage_closed singleton_in_M_iff
    apply auto[2]
  apply(rule iff_trans, rule sats_And_iff, simp add:assms, rule iff_conjI2)
   apply(rule iff_trans, rule_tac P="\<lambda>b. b \<in> f -`` {t}" in sats_least_fm)
  apply(rule in_vim_fm_sats_iff)
  using assms lt_nat_in_nat length_type zero_in_M
                apply auto[13]
   apply (simp add:vim_least_def)
   apply(rule_tac Q="\<lambda>b. b \<in> f -`` {t}" in least_abs)
    apply(rule transM, simp)
  using assms vimage_closed singleton_in_M_iff
    apply auto[2]
  apply(rule iff_trans, rule sats_Member_iff, simp add:assms, simp)
  apply(rule iffI, rule ltI, simp)
  unfolding vim_least_def
   apply force
  apply(rule ltD, simp)
  done

lemma function_restrict : 
  fixes f A
  assumes "function(f)"
  shows "function(restrict(f, A))" 
  using assms
  unfolding restrict_def function_def
  by auto

lemma restrict_apply_eq : 
  fixes f A x
  assumes "function(f)" "x \<in> A" 
  shows "restrict(f, A)`x = f`x" 
proof (cases "x \<in> domain(f)")
  case True
  then obtain y where yH: "<x, y> \<in> f" using assms by auto
  then have H: "f`x = y" using function_apply_equality assms by auto 
  have "<x, y> \<in> restrict(f, A)" unfolding restrict_def using assms yH by auto
  have "restrict(f, A)`x = y" using function_apply_equality function_restrict yH assms by auto
  then show ?thesis using H by auto
next
  case False
  have "domain(restrict(f, A)) \<subseteq> domain(f)" unfolding restrict_def by auto
  then have "x \<notin> domain(restrict(f, A))" using \<open>x \<notin> domain(f)\<close> by auto
  then show ?thesis using apply_0 \<open>x \<notin> domain(f)\<close> by auto
qed
  
lemma ac_implies_wellordering :  
  assumes "choice_ax(##M)" 
  shows "\<forall>A \<in> M. \<exists>r \<in> M. well_ord(A, r)" 
proof(rule ballI)

  fix A
  assume AinM : "A \<in> M" 

  obtain a f where afH : "a \<in> M" "Ord(a)" "f \<in> M" "f \<in> surj(a, A)"
    using assms ordinal_abs choice_ax_def surjection_abs AinM
    by force

  have eq: "{ p \<in> A \<times> A. sats(M, in_vim_least_rel_fm(1, 0), [p] @ [f]) } \<in> M" (is "?r \<in> _")
    apply(rule to_rin, rule separation_closed, rule separation_ax)
       apply(rule in_vim_least_rel_fm_type)
    using afH 
        apply auto[3]
     apply(rule le_trans, rule arity_vim_least_rel_fm)
    using assms AinM cartprod_closed
       apply auto
    apply(rule Un_least_lt, simp , simp)
    done

  define r where "r \<equiv> { <x, y>  \<in> A \<times> A. vim_least(f, x) < vim_least(f, y) }" 
  have "r = ?r" 
    unfolding r_def
    apply(rule iff_eq, clarsimp)
    apply(rule in_vim_least_rel_fm_sats_iff)
    using AinM afH assms transM pair_in_M_iff
    by auto
  then have rinM : "r \<in> M" using r_def eq by auto

  define L where "L \<equiv> { b \<in> a. \<exists>x \<in> A. b \<in> f -`` {x} \<and> b = vim_least(f, x) }" 
  define g where "g \<equiv> restrict(f, L)"

  have gtype : "g \<in> L \<rightarrow> A" 
    unfolding g_def
    apply(rule_tac C=a in restrict_type2)
    using afH surj_is_fun Pi_def L_def
    by auto

  have domf : "domain(f) = a" 
    using afH surj_def Pi_def by auto

  have vimH : "\<And>x. x \<in> A \<Longrightarrow> vim_least(f, x) \<in> L \<and>  g`vim_least(f, x) = x" 
  proof - 
    fix x assume xinA : "x \<in> A" 
    then obtain b where bH: "b \<in> a" "f ` b = x" using afH surj_def by auto
    define l where "l \<equiv> (\<mu> b. b \<in> f -`` {x})"
    then have "b \<in> f -`` {x}"
      apply(rule_tac b = "f`b" in vimageI)
       apply(rule function_apply_Pair)
      using vimageI function_apply_Pair afH surj_is_fun Pi_def xinA bH domf
      by auto 
    then have H: "l \<in> f -`` {x}" 
      unfolding l_def
      apply(rule_tac i=b in LeastI)
      using bH afH Ord_in_Ord
      by auto          
    then have "<l, x> \<in> f"
      unfolding vimage_def converse_def image_def
      by auto
    then have H2: "f`l = x" 
      using function_apply_equality afH surj_is_fun Pi_def
      by auto
    then have "f -`` {x} \<subseteq> domain(f)" 
      unfolding vimage_def converse_def domain_def image_def
      by auto
    then have "f -`` {x} \<subseteq> a" using domf by auto
    then have "l \<in> a" using H by auto
    then have H3: "l \<in> L" using H unfolding l_def L_def vim_least_def using xinA by auto
    then have "g`l = x" 
      unfolding g_def
      apply(subst restrict_apply_eq)
      using gtype Pi_def H2 afH surj_def
      by auto
    then show " vim_least(f, x) \<in> L \<and> g`vim_least(f, x) = x" 
      using H3 unfolding vim_least_def l_def by auto
  qed

  have gsurj : "g \<in> surj(L, A)"
    using surj_def vimH gtype 
    by auto

  have ginj : "g \<in> inj(L, A)" 
  proof - 
    have "\<And>b c. b \<in> L \<Longrightarrow> c \<in> L \<Longrightarrow> b \<noteq> c \<Longrightarrow> g`b = g`c \<Longrightarrow> b = c" 
    proof - 
      fix b c 
      assume bcH : "b \<in> L" "c \<in> L" "g`b = g`c"
      then obtain bx cx where H : "bx \<in> A" "cx \<in> A" "vim_least(f, bx) = b" "vim_least(f, cx) = c" "b \<in> f -`` {bx}" "c \<in> f -`` {cx}"
        using L_def
        by auto
      then have "g`vim_least(f, bx) = bx \<and> g`vim_least(f, cx) = cx" 
        using vimH by auto
      then have eq:"bx = cx" using H bcH by auto
      then have H2: "b \<in> f -`` {cx} \<and> c \<in> f -`` {bx}" using H eq by auto 
    
      have H3 : "vim_least(f, cx) \<le> b" 
        unfolding vim_least_def
        apply(rule Least_le)
        using H2 L_def Ord_in_Ord afH bcH
        by auto
      have H4 : "vim_least(f, bx) \<le> c" 
        unfolding vim_least_def
        apply(rule Least_le)
        using H2 L_def Ord_in_Ord afH bcH
        by auto
      show "b = c" 
        using le_anti_sym H3 H4 H by auto
    qed
    then show "g \<in> inj(L, A)" unfolding inj_def using gtype by auto
  qed

  have gbij : "g \<in> bij(L, A)" 
    using bij_def gsurj ginj by auto

  have "\<And>b c. b \<in> L \<Longrightarrow> c \<in> L \<Longrightarrow> b \<in> c \<longleftrightarrow> <g ` b, g ` c> \<in> r" 
  proof- 
    fix b c assume bcH : "b\<in>L" "c\<in>L"
    then obtain bx cx where H : "bx \<in> A" "cx \<in> A" "vim_least(f, bx) = b" "vim_least(f, cx) = c" "b \<in> f -`` {bx}" "c \<in> f -`` {cx}" 
      using L_def by auto
    then have eq: "g`b = bx \<and> g`c = cx" 
      using bcH vimH by auto
    have "b \<in> c \<longleftrightarrow> b < c"  
      apply(rule iffI, rule ltI, simp)
      using afH Ord_in_Ord bcH L_def apply force
      apply(rule ltD, simp)
      done
    then have "b \<in> c \<longleftrightarrow> vim_least(f, g`b) < vim_least(f, g`c)" using H bcH eq by auto
    then have "b \<in> c \<longleftrightarrow> <g ` b, g ` c> \<in> r" using r_def H eq by auto
    then show "b \<in> c \<longleftrightarrow> <g ` b, g ` c> \<in> r" by auto
  qed

  then have "g \<in> ord_iso(L, Memrel(L), A, r)" 
    apply(rule_tac ord_isoI)
    using gbij Memrel_def
    by auto
  then have iso: "converse(g) \<in> ord_iso(A, r, L, Memrel(L))" 
    using ord_iso_sym
    by auto

  have "well_ord(a, Memrel(a))" using well_ord_Memrel afH by auto
  then have "well_ord(L, Memrel(a))" using L_def well_ord_subset by force
  then have "well_ord(L, Memrel(a) \<inter> (L \<times> L))" using well_ord_Int_iff by auto
  then have "well_ord(L, Memrel(L))"
    apply(subgoal_tac "Memrel(a) \<inter> (L \<times> L) = Memrel(L)", simp)
    unfolding Memrel_def L_def 
    by auto
  then have "well_ord(A, r)" using well_ord_ord_iso iso by auto
  then show "\<exists>r \<in> M. well_ord(A, r)" using rinM by auto
qed

end

schematic_goal Hnext_ord_fm_auto:
  assumes
    "x \<in> M" "g \<in> M" "y \<in> M"
    "i \<in> nat" "j \<in> nat" "k \<in> nat" 
    "nth(i,env) = x"    
    "nth(j,env) = g"    
    "nth(k,env) = y"    
    "env \<in> list(M)" 
  shows "(\<exists>rang \<in> M. \<exists>urang \<in> M. is_range(##M, g, rang) \<and> big_union(##M, rang, urang) \<and> successor(##M, urang, y)) \<longleftrightarrow> sats(M,?fm(i,j,k),env)"
  by (insert assms ; (rule sep_rules | simp)+)

definition Hnext_ord_fm where "Hnext_ord_fm(i,j,k) \<equiv>
   Exists(Exists(And(range_fm(succ(succ(j)), 1), And(big_union_fm(1, 0), succ_fm(0, succ(succ(k)))))))  " 

context M_ZF_trans begin 

definition Hnext_ord where "Hnext_ord(x, g) \<equiv> succ(\<Union>range(g))" 

lemma sats_Hnext_ord_fm_iff : 
  fixes i j k x g y env 
  assumes "i < length(env)" "j < length(env)" "k < length(env)"
    "nth(i, env) = x" "nth(j, env) = g" "nth(k, env) = y"
          "env \<in> list(M)" "x \<in> M" "g \<in> M" "y \<in> M" 
  shows "y = Hnext_ord(x, g) \<longleftrightarrow> sats(M, Hnext_ord_fm(i,j,k), env)" 
  apply(rule_tac Q="\<exists>rang \<in> M. \<exists>urang \<in> M. is_range(##M, g, rang) \<and> big_union(##M, rang, urang) \<and> successor(##M, urang, y)" in iff_trans)
  unfolding Hnext_ord_def
  using image_closed Union_closed successor_abs Union_abs image_abs succ_in_M_iff assms transM range_abs range_closed
  apply simp
  unfolding Hnext_ord_fm_def
  apply(rule Hnext_ord_fm_auto)
  using assms nth_type lt_nat_in_nat 
  by auto

lemma Hnext_ord_fm_type : 
  fixes i j k 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat"
  shows "Hnext_ord_fm(i,j,k) \<in> formula" 
  unfolding Hnext_ord_fm_def 
  using assms
  by auto

lemma arity_Hnext_ord_fm :   
  fixes i j k 
  assumes "i \<in> nat" "j \<in> nat" "k \<in> nat"
  shows "arity(Hnext_ord_fm(i,j,k)) \<le> succ(i) \<union> succ(j) \<union> succ(k)" 
  unfolding Hnext_ord_fm_def
  apply (simp del:FOL_sats_iff pair_abs add: assms not_le_iff_lt fm_defs nat_simp_union) 
  using assms lt_succ_lt
  apply auto
   apply(rule le_trans)
    apply auto[2]
  done

definition next_ord where "next_ord(r, x) \<equiv> wftrec(r^+, x, Hnext_ord)" 

lemma next_ord_in_M : 
  fixes r A
  assumes "wf(r)" "r \<in> M" "A \<in> M" 
  shows "{ <x, next_ord(r, x)>. x \<in> A } \<in> M" 
  unfolding next_ord_def
  apply(rule_tac p="Hnext_ord_fm(2,1,0)" in wftrec_pair_closed)
  using wf_trancl assms trans_trancl trancl_closed Hnext_ord_fm_type 
         apply auto[4]
     apply(rule le_trans, rule arity_Hnext_ord_fm, simp, simp, simp)
     apply(rule Un_least_lt)+
  using assms
       apply auto[4]
   apply(simp add:Hnext_ord_def)
  using succ_in_MI Union_closed image_closed assms transM range_closed
   apply force
  apply(rule sats_Hnext_ord_fm_iff)
  using assms
  by auto

lemma next_ord : 
  fixes r A x
  assumes "wf(r)" "x \<in> A" 
  shows "next_ord(r, x) = succ(\<Union>{ next_ord(r, y). y \<in> (r^+ -`` {x}) })"
proof-
  have eq1:"next_ord(r, x) = wftrec(r^+, x, Hnext_ord)" using next_ord_def by auto
  also have eq2:"... = Hnext_ord(x, \<lambda>y \<in> r^+ -`` {x}. next_ord(r, y))" (is "_ = Hnext_ord(_, ?g)")
    unfolding next_ord_def
    apply(subst wftrec)
    using wf_trancl trans_trancl assms 
    by auto
  also have eq3: "... = succ(\<Union>range(?g))" (is "_ = ?x")
    apply(subst Hnext_ord_def, simp)
    done
  have "range(?g) = { next_ord(r, y). y \<in> (r^+ -`` {x}) }"
    unfolding lam_def
    by auto
  then have eq4: "?x = succ(\<Union>{ next_ord(r, y). y \<in> (r^+ -`` {x}) })"
    using eq3 by auto 
  show ?thesis using eq1 eq2 eq3 eq4 by auto
qed

lemma Ord_next_ord : 
  fixes r A x
  assumes "wf(r)" "x \<in> A" 
  shows "Ord(next_ord(r, x))" 
proof (rule_tac r="r^+" and P="\<lambda>x. Ord(next_ord(r, x))" in wf_induct, rule wf_trancl, simp add:assms)
  fix x 
  assume "(\<And>y. \<langle>y, x\<rangle> \<in> r^+ \<Longrightarrow> Ord(next_ord(r, y)))" 
  then have "\<And>y. y \<in> r^+ -`` {x} \<Longrightarrow> Ord(next_ord(r, y))" by auto
  then have "Ord(\<Union>{ next_ord(r, y). y \<in> (r^+ -`` {x}) })" 
    apply(rule_tac Ord_Union)
    by auto
  then have "Ord(succ(\<Union>{ next_ord(r, y). y \<in> (r^+ -`` {x}) }))" by auto
  then show "Ord(next_ord(r, x))" 
    apply(subst next_ord)
    using assms wf_trancl
    by auto
qed

lemma wellordering_imp_ac : 
  assumes "\<forall>A \<in> M. \<exists>r \<in> M. well_ord(A, r)" 
  shows "choice_ax(##M)" 
proof - 
  have "\<And>A. A \<in> M \<Longrightarrow> \<exists>a \<in> M. \<exists>f \<in> M. Ord(a) \<and> f \<in> surj(a, A)" 
  proof - 
    fix A x0 assume AinM: "A \<in> M" "x0 \<in> A" 
    then obtain r where rH: "r \<in> M" "well_ord(A, r)" using assms by auto
    define s where "s \<equiv> r \<inter> A \<times> A" 
    then have wfs:  "wf(s)" using well_ord_def wf_on_def s_def rH by auto
    have sinM : "s \<in> M" using AinM cartprod_closed rH Int_closed s_def by auto
    then have "{ <x, next_ord(s, x)>. x \<in> A } \<in> M" (is "?S \<in> _")
      using next_ord_in_M AinM wfs by auto
    then have "range(?S) \<in> M" using range_closed by auto
    have "range(?S) = { next_ord(s, x). x \<in> A }" by auto
    have "Ord(\<Union>{ next_ord(s, x). x \<in> A })" (is "Ord(?a)")
      apply(rule_tac Ord_Union)
      using Ord_next_ord wfs AinM sinM
      by auto

    define f where "f \<equiv> { <a, if (\<exists> x \<in> A. a = next_ord(s, x)) then THE x. a = next_ord(s, x) else x0> . a \<in> A }" 
    have "f \<in> ?a \<rightarrow> A" 
      

  




  


end 
end 