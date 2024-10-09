theory Fn_Perm_Automorphism 
  imports Fn_Perm_Definition 

begin
context M_ctm begin 

lemma converse_in_nat_perms : 
  fixes f 
  assumes "f \<in> nat_perms" 
  shows "converse(f) \<in> nat_perms" 
  unfolding nat_perms_def 
  using bij_converse_bij assms nat_perms_def nat_perms_in_M transM converse_closed
  by auto

lemma composition_in_nat_perms : 
  fixes f g 
  assumes "f \<in> nat_perms" "g \<in> nat_perms" 
  shows "f O g \<in> nat_perms" 
  using assms comp_closed comp_bij
  unfolding nat_perms_def 
  by auto

lemma Fn_perm_subset : 
  fixes f p 
  assumes "f \<in> nat_perms" "p \<in> Fn" 
  shows "Fn_perm(f, p) \<subseteq> (nat \<times> nat) \<times> 2" 
proof(rule subsetI)
  fix v assume vin : "v \<in> Fn_perm(f, p)" 
  have "\<exists>n\<in>nat. \<exists>m\<in>nat. \<exists>l\<in>2. \<langle>\<langle>n, m\<rangle>, l\<rangle> \<in> p \<and> v = \<langle>\<langle>f ` n, m\<rangle>, l\<rangle>"
    apply(rule Fn_permE)
    using assms vin 
    by auto
  then obtain n m l where H: "n \<in> nat" "m \<in> nat" "l \<in> 2" "<<n, m>, l> \<in> p" "v = <<f`n, m>, l>" by auto
  have "f`n \<in> nat"
    apply(rule function_value_in)
    using nat_perms_def bij_def inj_def H assms
    by auto
  then show "v \<in> (nat \<times> nat) \<times> 2" 
    using H 
    by auto
qed

lemma function_Fn_perm : 
  fixes f p 
  assumes "f \<in> nat_perms" "p \<in> Fn" 
  shows "function(Fn_perm(f, p))"
  unfolding function_def
proof(rule allI, rule allI, rule impI, rule allI, rule impI)
  fix x y y' 
  assume assms1 : "<x, y> \<in> Fn_perm(f, p)" "<x, y'> \<in> Fn_perm(f, p)"
  have "\<exists>n \<in> nat. \<exists>m \<in> nat. \<exists>l \<in> 2. <<n, m>, l> \<in> p \<and> <x, y> = <<f`n, m>, l>" 
    apply(rule Fn_permE)
    using assms assms1 
    by auto
  then obtain n m l where H: "n \<in> nat" "<<n, m>, l> \<in> p" "<x, y> = <<f`n, m>, l>" by auto

  have "\<exists>n' \<in> nat. \<exists>m' \<in> nat. \<exists>l' \<in> 2. <<n', m'>, l'> \<in> p \<and> <x, y'> = <<f`n', m'>, l'>" 
    apply(rule Fn_permE)
    using assms assms1 
    by auto
  then obtain n' m' l' where H': "n' \<in> nat" "<<n', m'>, l'> \<in> p" "<x, y'> = <<f`n', m'>, l'>" by auto

  have eq: "f`n = f`n' \<and> m = m'" using H H' by auto

  have "f \<in> inj(nat, nat)" 
    using assms nat_perms_def bij_is_inj 
    by auto
  then have eq': "n = n'" using H H' eq inj_def by auto

  have "function(p)" using assms Fn_def by auto
  then have "l = l'" using function_def H H' eq eq' by auto
  then show "y = y'" using H H' by auto
qed

lemma domain_Fn_perm : 
  fixes f p 
  assumes "f \<in> nat_perms" "p \<in> Fn" 
  shows "domain(Fn_perm(f, p)) = { <f`n, m>. <n, m> \<in> domain(p) }" 
proof (rule equality_iffI, rule iffI) 
  fix v assume vin : "v \<in> domain(Fn_perm(f, p))" 
  then obtain u where uH: "<v, u> \<in> Fn_perm(f, p)" by auto
  then have "\<exists>n \<in> nat. \<exists>m \<in> nat. \<exists>l \<in> 2. <<n, m>, l> \<in> p \<and> <v, u> = <<f`n, m>, l>" 
    apply(rule_tac Fn_permE)
    using assms  
    by auto
  then obtain n m where "n \<in> nat" "m \<in> nat" "<<n, m>, u> \<in> p" "v = <f`n, m>" by auto
  then show "v \<in> { <f`n, m>. <n, m> \<in> domain(p) }" by force
next
  fix v assume "v \<in> { <f`n, m>. <n, m> \<in> domain(p) }" 
  then have "\<exists>n m. \<langle>n, m\<rangle> \<in> domain(p) \<and> v = <f`n, m>"  
    apply(rule_tac pair_rel_arg)
    using assms Fn_def relation_def
     apply force
    by auto
  then obtain n m where H: "<n, m> \<in> domain(p)" "v = <f`n, m>" by auto
  then obtain l where "<<n, m>, l> \<in> p" by auto
  then have "<<f`n, m>, l> \<in> Fn_perm(f, p)" 
    unfolding Fn_perm_def
    by force
  then show "v \<in> domain(Fn_perm(f, p))" using H by auto
qed

lemma Fn_perm_in_Fn : 
  fixes f p 
  assumes "f \<in> nat_perms" "p \<in> Fn" 
  shows "Fn_perm(f, p) \<in> Fn" 
proof - 

  have "domain(Fn_perm(f, p)) \<subseteq> nat \<times> nat" (is ?A)
  proof(rule subsetI)
    fix v assume "v \<in> domain(Fn_perm(f, p))" 
    then obtain u where "<v, u> \<in> Fn_perm(f, p)" by auto
    then have "\<exists>n \<in> nat. \<exists>m \<in> nat. \<exists>l \<in> 2. <<n, m>, l> \<in> p \<and> <v, u> = <<f`n, m>, l>" 
      apply(rule_tac Fn_permE)
      using assms  
      by auto
    then obtain n m where H: "n \<in> nat" "m \<in> nat" "<<n, m>, u> \<in> p" "<v, u> = <<f`n, m>, u>" by auto
    then have "v = <f`n, m>" by auto
    have "f`n \<in> nat" 
      apply(rule function_value_in)
      using assms nat_perms_def bij_is_inj inj_def H
      by auto
    then show "v \<in> nat \<times> nat" using H by auto
  qed
 
  have "finite_M(domain(Fn_perm(f, p)))" (is ?B)
  proof - 
    have "finite_M(domain(p))" using assms Fn_def by auto
    then obtain g N where gNH: "g \<in> inj(domain(p), N)" "g \<in> M" "N \<in> nat" unfolding finite_M_def by force

    define h where "h \<equiv> { <<f`n, m>, g`<n, m>>. <n, m> \<in> domain(p) }"

    have hinM : "h \<in> M" 
    proof - 
      (* n m f`n <f`n, m> <n, m> g`<n, m> v domain(p) f g*)
      define \<phi> where "\<phi> \<equiv> Exists(Exists(Exists(Exists(Exists(Exists(
                            And(pair_fm(0, 1, 4), 
                            And(Member(4, 7),
                            And(fun_apply_fm(8, 0, 2), 
                            And(pair_fm(2, 1, 3), 
                            And(fun_apply_fm(9, 4, 5), 
                                pair_fm(3, 5, 6))))))))))))"  
      define X where "X \<equiv> { v \<in> (nat \<times> nat) \<times> N. sats(M, \<phi>, [v] @ [domain(p), f, g]) }"

      have XinM: "X \<in> M" 
        unfolding X_def
        apply(rule separation_notation, rule separation_ax)
        unfolding \<phi>_def 
           apply simp
        using domain_closed gNH assms Fn_in_M nat_perms_in_M transM 
          apply force 
        apply simp
         apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
        using cartprod_closed gNH nat_in_M transM 
        by auto

      have "X = { v \<in> (nat \<times> nat) \<times> N. 
                    \<exists>gnm \<in> M. \<exists>nm \<in> M. \<exists>fnm \<in> M. \<exists>fn \<in> M. \<exists>m \<in> M. \<exists>n \<in> M. 
                    <n, m> = nm \<and> nm \<in> domain(p) \<and> f`n = fn \<and> fnm = <fn, m> \<and> gnm = g`nm \<and> v = <fnm, gnm> }" 

        unfolding X_def \<phi>_def
        apply(rule iff_eq)
        apply(rename_tac v, subgoal_tac "v \<in> M \<and> domain(p) \<in> M \<and> f \<in> M \<and> g \<in> M \<and> N \<in> M")
        using pair_in_M_iff zero_in_M succ_in_MI gNH domain_closed assms transM nat_perms_in_M Fn_in_M nat_in_M
         apply simp
         apply(rule bex_iff)+
        using pair_in_M_iff zero_in_M succ_in_MI gNH domain_closed assms transM nat_perms_in_M Fn_in_M nat_in_M
        by auto
      also have "... = { v \<in> (nat \<times> nat) \<times> N. \<exists>n m. <n, m> \<in> domain(p) \<and> v = <<f`n, m>, g`<n, m>> }" 
        apply(rule iff_eq, rule iffI, force, clarsimp)
        apply(rename_tac n m l, subgoal_tac "<<n, m>, l> \<in> M")
         apply(rename_tac n m l, rule_tac x="g`<n, m>" in bexI)
          apply(rename_tac n m l, rule_tac x="<n, m>" in bexI)
           apply(rename_tac n m l, rule_tac x="<f`n, m>" in bexI)  
            apply(rename_tac n m l, rule_tac x="f`n" in bexI)
             apply(rename_tac n m l, rule_tac x="m" in bexI)
              apply(rename_tac n m l, rule_tac x="n" in bexI, force)
        using pair_in_M_iff zero_in_M succ_in_MI gNH domain_closed assms transM nat_perms_in_M Fn_in_M nat_in_M
              apply auto[6]
        using assms Fn_in_M transM
        by auto
      also have "... = h" 
      proof - 
        have H: "h \<subseteq> {v \<in> (nat \<times> nat) \<times> N . \<exists>n m. \<langle>n, m\<rangle> \<in> domain(p) \<and> v = \<langle>\<langle>f ` n, m\<rangle>, g ` \<langle>n, m\<rangle>\<rangle>}" 
        proof(rule subsetI) 
          fix v assume "v \<in> h" 
          then obtain n m where nmH: "<n, m> \<in> domain(p)" "v = <<f`n, m>, g`<n, m>>" "n \<in> nat" "m \<in> nat"  
            unfolding h_def
            apply(subgoal_tac "domain(p) \<subseteq> nat \<times> nat", force)
            using assms Fn_def
            by auto
          have fnin: "f`n \<in> nat" 
            apply(rule function_value_in)
            using assms nmH nat_perms_def bij_def inj_def 
            by auto
          then have "g`<n, m> \<in> N" 
            apply(rule_tac function_value_in)
            using gNH nmH inj_def
            by auto
          then show "v \<in> {v \<in> (nat \<times> nat) \<times> N . \<exists>n m. \<langle>n, m\<rangle> \<in> domain(p) \<and> v = \<langle>\<langle>f ` n, m\<rangle>, g ` \<langle>n, m\<rangle>\<rangle>}" 
            using nmH fnin 
            by auto
        qed
        show "{v \<in> (nat \<times> nat) \<times> N . \<exists>n m. \<langle>n, m\<rangle> \<in> domain(p) \<and> v = \<langle>\<langle>f ` n, m\<rangle>, g ` \<langle>n, m\<rangle>\<rangle>} = h" 
          apply(rule_tac equality_iffI, rule_tac iffI)
           apply(subst h_def, force)
          using H 
          by blast 
      qed
      finally show "h \<in> M" using XinM by auto
    qed
        
    have htype: "h \<in> domain(Fn_perm(f, p)) \<rightarrow> N"
    proof(rule Pi_memberI)
      show "relation(h)" 
        unfolding relation_def h_def
        apply(subgoal_tac "domain(p) \<subseteq> nat \<times> nat", force)
        using assms Fn_def 
        by auto
    next
      show "function(h)" 
        unfolding function_def 
      proof(rule allI, rule allI, rule impI, rule allI, rule impI)
        fix x y y' 
        assume assms1: "<x, y> \<in> h" "<x, y'> \<in> h" 
        obtain n m where H: "n \<in> nat" "m \<in> nat" "x = <f`n, m>" "y = g`<n, m>" 
          using h_def assms1 
          apply(subgoal_tac "domain(p) \<subseteq> nat \<times> nat", force)
          using assms Fn_def 
          by auto
        obtain n' m' where H': "n' \<in> nat" "m' \<in> nat" "x = <f`n', m'>" "y' = g`<n', m'>"
          using h_def assms1 
          apply(subgoal_tac "domain(p) \<subseteq> nat \<times> nat", force)
          using assms Fn_def 
          by auto
        
        have "f \<in> inj(nat, nat)" 
          using assms nat_perms_def bij_is_inj 
          by auto
        then have "n = n'" using H H' inj_def by auto
        then show "y = y'" using H H' by auto
      qed
    next 
      have "domain(Fn_perm(f, p)) = { <f`n, m>. <n, m> \<in> domain(p) }" 
        apply(subst domain_Fn_perm)
        using assms
        by auto
      also have "... = domain(h)" 
        unfolding h_def 
        apply(subgoal_tac "domain(p) \<subseteq> nat \<times> nat", force)
        using assms Fn_def 
        by auto
      finally show "domain(Fn_perm(f, p)) = domain(h)" by auto
    next 
      show "range(h) \<subseteq> N" 
      proof (rule subsetI)
        fix v assume "v \<in> range(h)" 
        then obtain a b where abH: "v = g`<a, b>" "a \<in> nat" "b \<in> nat" "<a, b> \<in> domain(p)" 
          using h_def 
          apply(subgoal_tac "domain(p) \<subseteq> nat \<times> nat", force)
          using assms Fn_def 
          by auto
        then have "g`<a, b> \<in> N" 
          apply(rule_tac function_value_in)
          using gNH inj_def 
          by auto
        then show "v \<in> N" using abH by auto
      qed
    qed

    have "\<forall>x\<in>domain(Fn_perm(f, p)). \<forall>y\<in>domain(Fn_perm(f, p)). h ` x = h ` y \<longrightarrow> x = y"
    proof(rule ballI, rule ballI, rule impI)
      fix x y 
      assume assms1: "x \<in> domain(Fn_perm(f, p))" "y \<in> domain(Fn_perm(f, p))" "h ` x = h ` y"
      obtain vx where vxH: "<x, vx> \<in> h" "vx \<in> N" using assms1 htype Pi_def by force
      obtain vy where vyH: "<y, vy> \<in> h" "vy \<in> N" using assms1 htype Pi_def by force

      have hxeq: "h`x = vx" 
        apply(rule function_apply_equality)
        using vxH htype Pi_def
        by auto
      have hyeq: "h`y = vy" 
        apply(rule function_apply_equality)
        using vyH htype Pi_def
        by auto

      obtain n m where nmH: "vx = g`<n, m>" "n \<in> nat" "m \<in> nat" "<n, m> \<in> domain(p)" "x = <f`n, m>" 
        using vxH unfolding h_def 
        apply(subgoal_tac "domain(p) \<subseteq> nat \<times> nat", force)
        using assms Fn_def 
        by auto
      obtain n' m' where n'm'H: "vy = g`<n', m'>" "n' \<in> nat" "m' \<in> nat" "<n', m'> \<in> domain(p)" "y = <f`n', m'>" 
        using vyH unfolding h_def 
        apply(subgoal_tac "domain(p) \<subseteq> nat \<times> nat", force)
        using assms Fn_def 
        by auto

      have "<n, m> = <n', m'>" 
        apply(rule inj_apply_equality)
        using gNH assms1 nmH n'm'H hxeq hyeq 
        by auto
      then show "x = y" using nmH n'm'H by auto
    qed

    then show "finite_M(domain(Fn_perm(f, p)))" 
      unfolding finite_M_def 
      apply(rule_tac x=N in bexI)
       apply(rule_tac a=h in not_emptyI)
      unfolding inj_def 
      using hinM htype gNH transM
      by auto
  qed

  have "range(Fn_perm(f, p)) \<subseteq> 2" (is ?C)
  proof (rule subsetI)
    fix v assume "v \<in> range(Fn_perm(f, p))" 
    then obtain u where "<u, v> \<in> Fn_perm(f, p)" by auto thm Fn_permE
    then have "\<exists>n\<in>nat. \<exists>m\<in>nat. \<exists>l\<in>2. \<langle>\<langle>n, m\<rangle>, l\<rangle> \<in> p \<and> <u, v> = \<langle>\<langle>f ` n, m\<rangle>, l\<rangle>" 
      apply(rule_tac Fn_permE)
      using assms
      by auto
    then show "v \<in> 2" by auto
  qed

  then show ?thesis 
    unfolding Fn_def 
    using Fn_perm_in_M Fn_perm_subset function_Fn_perm \<open>?A\<close> \<open>?B\<close> \<open>?C\<close> assms
    by auto
qed

lemma Fn_perm_comp : 
  fixes f f' p 
  assumes "f \<in> nat_perms" "f' \<in> nat_perms" "p \<in> Fn" 
  shows "Fn_perm(f', Fn_perm(f, p)) = Fn_perm(f' O f, p)" 
proof (rule equality_iffI)
  fix v
  have I1: "v \<in> Fn_perm(f', Fn_perm(f, p)) \<longleftrightarrow> (\<exists>n \<in> nat. \<exists>m \<in> nat. \<exists>l \<in> 2. <<n, m>, l> \<in> Fn_perm(f, p) \<and> v = <<f'`n, m>, l>)" 
    apply(rule iffI) 
     apply(rule Fn_permE, rule Fn_perm_in_Fn)
    using assms
        apply auto[4]
    apply(subst Fn_perm_def, force)
    done
  have I2: "... \<longleftrightarrow> (\<exists>n \<in> nat. \<exists>m \<in> nat. \<exists>l \<in> 2. (\<exists>n' \<in> nat. \<exists>m' \<in> nat. \<exists>l' \<in> 2. <<n', m'>, l'> \<in> p \<and> <<n, m>, l> = <<f`n', m'>, l'>) \<and> v = <<f'`n, m>, l>)" 
    apply(rule bex_iff)+
    apply(rule iff_conjI2, rule iffI, rule Fn_permE)
    using assms 
        apply auto[3]
     apply(subst Fn_perm_def, force)
    by auto
  have I3: "... \<longleftrightarrow> (\<exists>m \<in> nat. \<exists>l \<in> 2. \<exists>n' \<in> nat. \<exists>n \<in> nat. f`n' = n \<and> <<n', m>, l> \<in> p \<and> v = <<f'`n, m>, l>)" by auto
  have I4: "... \<longleftrightarrow> (\<exists>m \<in> nat. \<exists>l \<in> 2. \<exists>n \<in> nat. <<n, m>, l> \<in> p \<and> v = <<f'`(f`n), m>, l>)" 
    apply(rule bex_iff)+
    apply(rule iffI, force, clarsimp)
    apply(rule function_value_in)
    using assms nat_perms_def bij_is_inj inj_def 
    by auto
  have I5: "... \<longleftrightarrow> (\<exists>n \<in> nat. \<exists>m \<in> nat. \<exists>l \<in> 2. <<n, m>, l> \<in> p \<and> v = <<f'`(f`n), m>, l>)" by auto
  have I6: "... \<longleftrightarrow> (\<exists>n \<in> nat. \<exists>m \<in> nat. \<exists>l \<in> 2. <<n, m>, l> \<in> p \<and> v = <<(f' O f)`n, m>, l>)"  
    apply(rule bex_iff)+
    apply(subst comp_fun_apply)
    using assms nat_perms_def bij_is_inj inj_def 
      apply force
    by auto
  have I7: "... \<longleftrightarrow> v \<in> Fn_perm(f' O f, p)" 
    apply(rule iffI, subst Fn_perm_def, force)
    apply(rule Fn_permE)
    using assms
      apply simp
    unfolding nat_perms_def
     apply (simp, rule conjI, rule comp_bij)
    using assms nat_perms_def bij_is_inj inj_def comp_closed
    by auto
  show "v \<in> Fn_perm(f', Fn_perm(f, p)) \<longleftrightarrow> v \<in> Fn_perm(f' O f, p)" using I1 I2 I3 I4 I5 I6 I7 by auto
qed

lemma Fn_perm'_eq : 
  fixes f p 
  assumes "f \<in> nat_perms" "p \<in> Fn"  
  shows "Fn_perm'(f)`p = Fn_perm(f, p)" 
  apply(rule function_apply_equality)
  unfolding Fn_perm'_def 
  using assms function_def
  by auto

lemma Fn_perm'_value_in : 
  fixes f p 
  assumes "f \<in> nat_perms" "p \<in> Fn" 
  shows "Fn_perm'(f)`p \<in> Fn" 

  using Fn_perm_in_Fn Fn_perm'_eq assms
  by auto

lemma Fn_perm'_type : 
  fixes f
  assumes "f \<in> nat_perms" 
  shows "Fn_perm'(f) \<in> Fn \<rightarrow> Fn" 
  apply(rule Pi_memberI)
  using relation_def function_def Fn_perm'_def Fn_perm_in_Fn assms
  by auto

lemma domain_Fn_perm' : 
  fixes f 
  assumes "f \<in> nat_perms" 
  shows "domain(Fn_perm'(f)) = Fn" 
  unfolding Fn_perm'_def
  by auto

lemma Fn_perm_id : 
  fixes p 
  assumes "p \<in> Fn" 
  shows "Fn_perm(id(nat), p) = p" 
  unfolding Fn_perm_def 
  apply(subgoal_tac "p \<subseteq> (nat \<times> nat) \<times> 2", force)
  using assms Fn_def
  by auto

lemma Fn_perm'_id : 
  shows "Fn_perm'(id(nat)) = id(Fn)" 
  apply(subgoal_tac "id(nat) \<in> nat_perms")
   apply(rule function_eq)
  using relation_def Fn_perm'_def function_def
        apply auto[5]
   apply(rename_tac x, rule_tac P="x \<in> domain(Fn_perm'(id(nat)))" in mp)
    apply(subst domain_Fn_perm', simp)
    apply(rule impI, subst Fn_perm'_eq, simp, simp)
    apply(subst Fn_perm_id, simp, rule sym)
    apply(rule function_apply_equality, rule idI, simp)
    apply(insert id_type Pi_def, force, simp)
  unfolding nat_perms_def
  apply(simp, rule conjI, rule id_bij, rule id_closed)
  using nat_in_M
  by auto

lemma Fn_perm'_comp :  
  fixes f f'
  assumes "f \<in> nat_perms" "f' \<in> nat_perms" 
  shows "Fn_perm'(f) O Fn_perm'(f') = Fn_perm'(f O f')" 
  apply(subgoal_tac "domain(Fn_perm'(f) O Fn_perm'(f')) = Fn")
   apply(rule function_eq)
  using relation_def Fn_perm'_def comp_def function_def
        apply auto[4]
    apply(subst domain_Fn_perm', subst nat_perms_def, simp, rule conjI)
      apply(rule comp_bij)
  using assms nat_perms_def comp_closed 
      apply auto[4]
   apply(subst comp_fun_apply, rule Fn_perm'_type)
  using assms 
     apply auto[2]
   apply(subst Fn_perm'_eq, simp add:assms, rule function_value_in, rule Fn_perm'_type, simp add:assms, simp)
   apply(subst Fn_perm'_eq, simp add:assms, simp)
   apply(subst Fn_perm'_eq, subst nat_perms_def, simp ,rule conjI)
      apply(rule comp_bij)
  using assms nat_perms_def comp_closed 
       apply auto[4]
   apply(rule Fn_perm_comp)
  using assms
     apply auto[3]
  apply(subst domain_comp_eq, subst domain_Fn_perm', simp add:assms)
  using Fn_perm'_type assms Pi_def 
   apply force 
  using domain_Fn_perm' assms
  by auto

lemma Fn_perm'_bij : 
  fixes f 
  assumes "f \<in> nat_perms"
  shows "Fn_perm'(f) \<in> bij(Fn, Fn)" 
  apply(rule_tac g="Fn_perm'(converse(f))" in fg_imp_bijective)
     apply(rule Fn_perm'_type, simp add:assms)
    apply(rule Fn_perm'_type, rule converse_in_nat_perms, simp add:assms)
   apply(subst Fn_perm'_comp, simp add:assms, rule converse_in_nat_perms, simp add:assms)
   apply(subst right_comp_inverse, rule bij_is_surj)
  using assms nat_perms_def Fn_perm_id Fn_perm'_id 
    apply auto[2]
  apply(subst Fn_perm'_comp, rule converse_in_nat_perms)
  using assms
    apply auto[2]
  apply(subst left_comp_inverse, rule bij_is_inj)
  using assms nat_perms_def Fn_perm_id Fn_perm'_id 
   apply auto[2]
  done

lemma Fn_perm'_converse : 
  fixes f 
  assumes "f \<in> nat_perms"
  shows "converse(Fn_perm'(f)) = Fn_perm'(converse(f))" 
proof (rule equality_iffI)
  fix v

  have "Fn_perm'(converse(f)) \<in> surj(Fn, Fn)" 
    using Fn_perm'_bij assms bij_is_surj converse_in_nat_perms
    by force 
  then have surjE: "\<And>p. p \<in> Fn \<Longrightarrow> \<exists>p' \<in> Fn. Fn_perm'(converse(f))`p' = p" using surj_def Fn_perm_in_Fn assms by auto

  have eq: "\<And>p. p \<in> Fn \<Longrightarrow> Fn_perm'(f)`(Fn_perm'(converse(f))`p) = p" 
    apply(subst comp_fun_apply[symmetric])
      apply(rule Fn_perm'_type)
    using assms converse_in_nat_perms 
      apply auto[2]
    apply(subst Fn_perm'_comp)
    using assms converse_in_nat_perms 
      apply auto[2]
    apply(subst right_comp_inverse)
    using nat_perms_def assms bij_is_surj 
     apply auto[1]
    apply(subst Fn_perm'_id)
    apply(rule function_apply_equality, simp)
    using id_bij bij_def inj_def Pi_def
    by auto

  have I1: "v \<in> converse(Fn_perm'(f)) \<longleftrightarrow> (\<exists>p \<in> Fn. v = <Fn_perm(f, p), p>)"
    using Fn_perm'_type assms Pi_def Fn_perm'_def
    by force
  have I2: "... \<longleftrightarrow> (\<exists>p \<in> Fn. v = <Fn_perm'(f)`p, p>)"
    using assms Fn_perm'_eq 
    by auto
  have I3: "... \<longleftrightarrow> (\<exists>p' \<in> Fn. v = <Fn_perm'(f)`(Fn_perm'(converse(f))`p'), Fn_perm'(converse(f))`p'>)"
    using converse_in_nat_perms assms Fn_perm_in_Fn Fn_perm'_eq surjE
    by force
  have I4: "... \<longleftrightarrow> (\<exists>p' \<in> Fn. v = <p', Fn_perm'(converse(f))`p'>)"
    apply(rule bex_iff)
    apply(subst comp_fun_apply [symmetric])
      apply(rule Fn_perm'_type, rule converse_in_nat_perms, simp add:assms, simp)
    apply(subst Fn_perm'_comp, simp add:assms, rule converse_in_nat_perms, simp add:assms)
    apply(subst right_comp_inverse)
    using assms nat_perms_def bij_is_surj 
     apply force
    apply(subst Fn_perm'_id, subst function_apply_equality, rule idI, simp)
    using id_bij bij_def inj_def Pi_def 
    by auto
  have I5: "... \<longleftrightarrow> (\<exists>p' \<in> Fn. v = <p', Fn_perm(converse(f), p')>)"
    using Fn_perm'_type assms Pi_def Fn_perm'_def converse_in_nat_perms Fn_perm'_eq
    by force
  have I6: "... \<longleftrightarrow> v \<in> Fn_perm'(converse(f))" 
    using Fn_perm'_type assms Pi_def Fn_perm'_def converse_in_nat_perms
    by force
  show "v \<in> converse(Fn_perm'(f)) \<longleftrightarrow> v \<in> Fn_perm'(converse(f))" 
    using I1 I2 I3 I4 I5 I6 
    by auto
qed

lemma Fn_perm'_preserves_order : 
  fixes f p p' 
  assumes "f \<in> nat_perms" "p \<in> Fn" "p' \<in> Fn" "<p, p'> \<in> Fn_leq"
  shows "<Fn_perm'(f)`p, Fn_perm'(f)`p'> \<in> Fn_leq" 
proof - 
  have "p' \<subseteq> p" using assms Fn_leq_def by auto

  have "Fn_perm'(f)`p' \<subseteq> Fn_perm'(f)`p" 
  proof(rule subsetI)
    fix v 
    assume "v \<in> Fn_perm'(f)`p'" 
    then have "v \<in> Fn_perm(f, p')" using Fn_perm'_eq assms by auto
    then have "\<exists>n \<in> nat. \<exists>m \<in> nat. \<exists>l \<in> 2. <<n, m>, l> \<in> p' \<and> v = <<f`n, m>, l>" 
      apply(rule_tac Fn_permE)
      using assms
      by auto
    then obtain n m l where H: "n \<in> nat" "m \<in> nat" "l \<in> 2" "<<n, m>, l> \<in> p'" "v = <<f`n, m>, l>" by auto
    then have "<<n, m>, l> \<in> p" using \<open>p' \<subseteq> p\<close> by auto
    then have "<<f`n, m>, l> \<in> Fn_perm(f, p)" 
      unfolding Fn_perm_def
      by force
    then have "<<f`n, m>, l> \<in> Fn_perm'(f)`p" 
      apply(subst Fn_perm'_eq)
      using assms
      by auto
    then show "v \<in> Fn_perm'(f)`p" using H by auto
  qed
  then show ?thesis 
    unfolding Fn_leq_def 
    apply simp 
    apply(rule conjI, rule function_value_in)
      apply(rule Fn_perm'_type, simp add:assms, simp add:assms)
    apply(rule function_value_in, rule Fn_perm'_type, simp add:assms, simp add:assms)
    done
qed

lemma Fn_perm'_preserves_order' : 
  fixes f p p' 
  assumes "f \<in> nat_perms" "p \<in> Fn" "p' \<in> Fn" "<Fn_perm'(f)`p, Fn_perm'(f)`p'> \<in> Fn_leq"
  shows "<p, p'> \<in> Fn_leq" 
proof - 
  have "f \<in> inj(nat, nat)" using assms nat_perms_def bij_is_inj by auto
  then have injE: "\<And> n m. n \<in> nat \<Longrightarrow> m \<in> nat \<Longrightarrow> f`n = f`m \<Longrightarrow> n = m" 
    using inj_def 
    by auto

  have subsetH: "Fn_perm'(f)`p' \<subseteq> Fn_perm'(f)`p" 
    using assms Fn_leq_def
    by auto
  have "p' \<subseteq> p" 
  proof (rule subsetI)
    fix v assume vin : "v \<in> p'" 
    then have "p' \<subseteq> (nat \<times> nat) \<times> 2"
      using assms Fn_def 
      by auto
    then have "\<exists>n \<in> nat. \<exists>m \<in> nat. \<exists>l \<in> 2. v = <<n, m>, l>" 
      using vin 
      by auto
    then obtain n m l where H: "n \<in> nat" "m \<in> nat" "l \<in> 2" "v = <<n, m>, l>" 
      using assms Fn_def vin 
      by force
    then have "<<f`n, m>, l> \<in> Fn_perm(f, p')" 
      unfolding Fn_perm_def
      using vin H 
      by force
    then have "<<f`n, m>, l> \<in> Fn_perm'(f)`p'"
      apply(subst Fn_perm'_eq)
      using assms 
      by auto
    then have "<<f`n, m>, l> \<in> Fn_perm'(f)`p" 
      using subsetH
      by auto
    then have "<<f`n, m>, l> \<in> Fn_perm(f, p)"
      using Fn_perm'_eq assms
      by auto
    then have "\<exists>n' \<in> nat. \<exists>m' \<in> nat. \<exists>l' \<in> 2. <<n', m'>, l'> \<in> p \<and> <<f`n, m>, l> = <<f`n', m'>, l'>" 
      apply(rule_tac Fn_permE)
      using assms
      by auto
    then have "<<n, m>, l> \<in> p" 
      using injE H 
      by auto
    then show "v \<in> p" 
      using H by auto
  qed
  then show ?thesis 
    unfolding Fn_leq_def 
    using assms
    by auto
qed

lemma Fn_perm'_is_P_auto : 
  fixes f 
  assumes "f \<in> nat_perms" 
  shows "forcing_data_partial.is_P_auto(Fn, Fn_leq, M, Fn_perm'(f))"

  apply(subst forcing_data_partial.is_P_auto_def)
   apply(rule Fn_forcing_data_partial)
  apply(rule conjI, rule Fn_perm'_in_M, simp add:assms, rule conjI, rule Fn_perm'_bij, simp add:assms)
  apply(rule ballI)+
  apply(rule iffI)
   apply(rule Fn_perm'_preserves_order)
  using assms
      apply auto[4]
    apply(rule Fn_perm'_preserves_order')
  using assms
  by auto


end
end