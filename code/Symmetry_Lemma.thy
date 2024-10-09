theory Symmetry_Lemma
  imports 
    HS_Forces
begin 

context M_symmetric_system_HS_Forces
begin

lemma symmetry_lemma_base : 
  "\<And>\<pi> p x y. is_P_auto(\<pi>) \<Longrightarrow> p \<in> P \<Longrightarrow> x \<in> P_names \<Longrightarrow> y \<in> P_names 
    \<Longrightarrow> (forces_mem(p, x, y) \<longleftrightarrow> forces_mem(\<pi>`p, Pn_auto(\<pi>)`x, Pn_auto(\<pi>)`y))
      \<and> (forces_eq(p, x, y) \<longleftrightarrow> forces_eq(\<pi>`p, Pn_auto(\<pi>)`x, Pn_auto(\<pi>)`y))"
proof - 
  fix \<pi> 
  assume piauto : "is_P_auto(\<pi>)"

  define MEM where "MEM \<equiv> \<lambda> p x y . (forces_mem(p, x, y) \<longleftrightarrow> forces_mem(\<pi>`p, Pn_auto(\<pi>)`x, Pn_auto(\<pi>)`y))"
  define EQ where "EQ \<equiv> \<lambda> p x y . (forces_eq(p, x, y) \<longleftrightarrow> forces_eq(\<pi>`p, Pn_auto(\<pi>)`x, Pn_auto(\<pi>)`y))"
  define Q where "Q \<equiv> \<lambda> Q a b. \<forall>x \<in> P_names. \<forall>y \<in> P_names. \<forall>p \<in> P. P_rank(x) \<le> a \<longrightarrow> P_rank(y) \<le> b \<longrightarrow> Q(p, x, y)" 

  have MEM_step: "\<And>a. Ord(a) \<Longrightarrow> \<forall>b \<in> a. Q(EQ, b, b) \<Longrightarrow> \<forall>b \<in> a. Q(MEM, b, a)"  
    unfolding Q_def 
    apply (clarify) 
  proof - 
    fix a b x y p 
    assume xrank: "P_rank(x) \<le> b" and yrank:"P_rank(y) \<le> a" and bina : "b \<in> a" 
    and orda : "Ord(a)" and pinP : "p \<in> P" and xpname : "x \<in> P_names" and ypname : "y \<in> P_names" 
    and "\<forall>b\<in>a. \<forall>x\<in>P_names. \<forall>y\<in>P_names. \<forall>p\<in>P. P_rank(x) \<le> b \<longrightarrow> P_rank(y) \<le> b \<longrightarrow> EQ(p, x, y) "

    then have EQH : "\<And>b x y p. b \<in> a \<Longrightarrow> x \<in> P_names \<Longrightarrow> y \<in> P_names \<Longrightarrow> p \<in> P \<Longrightarrow> P_rank(x) \<le> b \<Longrightarrow> P_rank(y) \<le> b \<Longrightarrow> EQ(p,x,y)" by auto  

    have "forces_mem(p, x, y) \<longleftrightarrow>  dense_below({ q\<in>P. \<exists>s. \<exists>r. r\<in>P \<and> \<langle>s,r\<rangle> \<in> y \<and> q\<preceq>r \<and> forces_eq(q,x,s)}, p)"
      using forces_mem_iff_dense_below pinP 
      apply auto 
      done 
    also have "... \<longleftrightarrow> dense_below(\<pi>``{ q\<in>P. \<exists>s. \<exists>r. r\<in>P \<and> \<langle>s,r\<rangle> \<in> y \<and> q\<preceq>r \<and> forces_eq(q,x,s)}, \<pi>`p)" 
      apply (rule_tac P_auto_preserves_density') 
      using piauto pinP 
      by auto 
    also have "... \<longleftrightarrow> dense_below({ q\<in>P. \<exists>s. \<exists>r. r\<in>P \<and> \<langle>s,r\<rangle> \<in> Pn_auto(\<pi>)`y \<and> q\<preceq>r \<and> forces_eq(q,Pn_auto(\<pi>)`x,s)}, \<pi>`p)" 
    proof - 
      define X where "X \<equiv> { q\<in>P. \<exists>s. \<exists>r. r\<in>P \<and> \<langle>s,r\<rangle> \<in> y \<and> q\<preceq>r \<and> forces_eq(q,x,s)} "
      define Y where "Y \<equiv> { q\<in>P. \<exists>s. \<exists>r. r\<in>P \<and> \<langle>s,r\<rangle> \<in> Pn_auto(\<pi>)`y \<and> q\<preceq>r \<and> forces_eq(q,Pn_auto(\<pi>)`x,s)} "
      have "\<pi>``X = Y" 
        apply (rule equality_iffI; rule iffI)
         apply (rule_tac A=X and r=\<pi> and b=x in imageE) 
          apply simp 
        apply (simp add:Y_def; rule conjI)
        using piauto bij_is_fun 
        unfolding is_P_auto_def Pi_def 
          apply blast 
      proof - 
        fix q piq assume assms : "<q, piq> \<in> \<pi>"  "q \<in> X" 
        then obtain s r where srH :  "r \<in> P" "<s, r> \<in> y" "q\<preceq>r" "forces_eq(q,x,s)" unfolding X_def by auto 
        have H: "q \<in> P \<and> \<pi>`q = piq" 
          apply (rule_tac B="\<lambda>_.P" in apply_fun) 
          using bij_is_fun piauto 
          unfolding is_P_auto_def assms 
           apply blast 
          using assms 
          by simp 
        then have H2:"\<pi>`q = piq" by auto 
        then have H3:"\<pi>`q \<preceq> \<pi> ` r"
          apply (rule_tac P_auto_preserves_leq)
          using piauto H srH 
          by auto 
        show "\<exists>s r. r \<in> P \<and> \<langle>s, r\<rangle> \<in> Pn_auto(\<pi>) ` y \<and> piq \<preceq> r \<and> forces_eq(piq, Pn_auto(\<pi>)`x, s)"
          apply (rule_tac x="Pn_auto(\<pi>)`s" in exI) 
          apply (rule_tac x="\<pi>`r" in exI) 
          apply (auto) 
          using P_auto_value piauto srH 
             apply simp 
          apply (rule_tac a="{<Pn_auto(\<pi>)`z, \<pi>`v>. <z, v> \<in> y}" and b="Pn_auto(\<pi>) ` y" in ssubst)
          using Pn_auto ypname 
             apply simp 
            apply (rule_tac pair_relI) 
          using srH H H2 H3 
            apply simp_all
          apply (rule_tac a="\<pi>`q" and b = "piq" in ssubst) 
          using H 
           apply simp 
          apply (rule_tac P="EQ(q, x, s)" in mp) 
          apply (simp add: EQ_def) 
          apply (cases "P_rank(s) \<le> b") 
           apply (rule_tac EQH[of b]) using bina xpname ypname H xrank 
                apply simp_all 
          using ypname srH P_name_domain_P_name 
           apply simp 
          apply (rule_tac P="b \<le> P_rank(s)" in mp) 
           apply (rule impI) 
           apply (rule_tac EQH[of "P_rank(s)"]) 
                apply (rule_tac ltD) 
                apply(rule_tac b="P_rank(y)" in lt_le_lt) 
          using ypname domain_P_rank_lt yrank P_name_domain_P_name P_rank_ord 
                 apply simp_all   
           apply (rule_tac j=b in le_trans) 
          using xrank 
            apply simp_all 
          apply(rule_tac P="b < P_rank(s)" in mp) 
          using lt_succ_lt 
           apply simp 
          using not_le_iff_lt orda Ord_in_Ord P_rank_ord 
          apply auto 
          done
      next 
        fix q' assume qinY : "q' \<in> Y" 
        then have q'inP : "q' \<in> P" unfolding Y_def by auto 
        obtain s' r' 
          where s'r'H : "r' \<in> P" "<s', r'> \<in> Pn_auto(\<pi>)`y" "q'\<preceq>r'" "forces_eq(q',Pn_auto(\<pi>)`x,s')" 
          using qinY unfolding Y_def by auto 
        have "\<exists>s r. <s, r> \<in> y \<and>  <s', r'> = <Pn_auto(\<pi>)`s, \<pi>`r>" 
          apply (rule_tac pair_rel_arg) 
          using relation_P_name ypname s'r'H Pn_auto 
          by auto
        then obtain s r where srH : "<s, r>\<in> y" "s' = Pn_auto(\<pi>)`s" "r' = \<pi>`r" by auto 

        have "\<pi> \<in> surj(P, P)" 
          using piauto bij_is_surj unfolding is_P_auto_def by auto 
        then obtain q where qH: "q \<in> P" "\<pi>`q = q'" unfolding surj_def using q'inP by auto

        have rinP : "r \<in> P" 
          apply (rule_tac x=y and y=s in P_name_range) 
          using ypname srH qH 
           apply simp_all 
          done 
        then have qr : "q\<preceq>r" using s'r'H srH qH P_auto_preserves_leq' piauto by auto

        have fH: "forces_eq(\<pi>`q,Pn_auto(\<pi>)`x, Pn_auto(\<pi>)`s)" using s'r'H srH qH by auto 

        have spname : "s \<in> P_names" using ypname srH P_name_domain_P_name by auto 
        
        then show "q' \<in> \<pi>``X" 
          apply (rule_tac a=q in imageI) 
           apply (rule_tac a="\<pi>`q" and b=q' in ssubst)
          using qH 
            apply simp 
           apply (rule_tac function_apply_Pair) 
          using P_auto_is_function P_auto_domain qH piauto 
            apply simp_all
          unfolding X_def 
          apply simp 
          apply (rule_tac x=s in exI)
          apply (rule_tac x=r in exI)
          apply (rule conjI) 
          using rinP 
           apply simp 
          apply (rule conjI) 
          using srH qH 
           apply simp_all 
          apply (rule conjI) 
          using qr 
           apply simp 
          apply (rule_tac P="EQ(q, x, s)" in mp) 
          using fH 
           apply (simp add: EQ_def) 
          apply (cases "P_rank(s) \<le> b") 
           apply (rule_tac EQH[of b]) 
          using bina xpname ypname qH xrank 
                apply simp_all 
          using ypname srH P_name_domain_P_name 
          apply simp 
          apply (rule_tac P="b \<le> P_rank(s)" in mp) 
           apply (rule impI) 
          apply (rule EQH [of "P_rank(s)"]) 
                apply (rule_tac ltD) 
                apply(rule_tac b="P_rank(y)" in lt_le_lt) 
          using ypname domain_P_rank_lt yrank P_name_domain_P_name P_rank_ord 
                 apply simp_all   
           apply (rule_tac j=b in le_trans) 
          using xrank 
            apply simp_all 
          apply(rule_tac P="b < P_rank(s)" in mp) 
          using lt_succ_lt 
           apply simp 
          using not_le_iff_lt orda Ord_in_Ord P_rank_ord 
          apply auto 
          done
      qed
      then show ?thesis unfolding X_def Y_def by simp 
      qed
      also have "... \<longleftrightarrow> forces_mem(\<pi>`p, Pn_auto(\<pi>)`x, Pn_auto(\<pi>)`y)" 
        apply (rule iff_flip)
        apply (rule_tac forces_mem_iff_dense_below)
        using P_auto_value pinP piauto 
        by auto 
      finally show "MEM(p, x, y)" unfolding MEM_def by simp 
    qed

    have EQ_step : "\<And>a. Ord(a) \<Longrightarrow> \<forall>b \<in> a. Q(MEM, b, a) \<Longrightarrow> Q(EQ, a, a)"   
      unfolding Q_def apply clarify 
    proof - 
      fix a x y p 
      assume orda : "Ord(a)" 
      and "\<forall>b\<in>a. \<forall>x\<in>P_names. \<forall>y\<in>P_names. \<forall>p\<in>P. P_rank(x) \<le> b \<longrightarrow> P_rank(y) \<le> a \<longrightarrow> MEM(p, x, y)" 
      and xpname : "x \<in> P_names" and ypname : "y \<in> P_names" 
      and pinP : "p \<in> P" and xrank : "P_rank(x) \<le> a" and yrank : "P_rank(y) \<le> a" 

      then have MEMH : 
        "\<And>b x y p. b \<in> a \<Longrightarrow> x \<in> P_names \<Longrightarrow> y \<in> P_names \<Longrightarrow> p \<in> P \<Longrightarrow> P_rank(x) \<le> b \<Longrightarrow> P_rank(y) \<le> a \<Longrightarrow> MEM(p,x,y)" 
        by auto 

      have srank_lemma : "\<And>s. s \<in> domain(x) \<union> domain(y) \<Longrightarrow> P_rank(s) < a" 
        apply (rule_tac A="domain(x)" and B="domain(y)" and c=s in UnE)
          apply simp 
         apply (rule_tac b="P_rank(x)" in lt_le_lt) 
          apply (rule_tac P="\<exists>p. <s, p> \<in> x" in mp) 
           apply clarify 
        using xpname domain_P_rank_lt 
           apply simp 
          apply (simp add:domain_def) 
          apply blast 
        using xrank 
         apply simp 
        apply (rule_tac b="P_rank(y)" in lt_le_lt) 
         apply (rule_tac P="\<exists>p. <s, p> \<in> y" in mp) 
          apply clarify 
        using ypname domain_P_rank_lt 
          apply simp 
         apply (simp add:domain_def) 
         apply blast 
        using yrank 
        apply simp 
        done 

      have "forces_eq(p, x, y) \<longleftrightarrow> (\<forall>s\<in>domain(x) \<union> domain(y). \<forall>q. q\<in>P \<and> q \<preceq> p \<longrightarrow> (forces_mem(q,s,x) \<longleftrightarrow> forces_mem(q,s,y)))" 
        using def_forces_eq pinP by auto
      also have "... \<longleftrightarrow> 
        (\<forall>s\<in>domain(Pn_auto(\<pi>)`x) \<union> domain(Pn_auto(\<pi>)`y). \<forall>q. q\<in>P \<and> q \<preceq> \<pi>`p 
          \<longrightarrow> (forces_mem(q,s,Pn_auto(\<pi>)`x) \<longleftrightarrow> forces_mem(q,s,Pn_auto(\<pi>)`y)))" 
        apply (rule iffI; clarify)
      proof - 
        fix s' q'  assume assm:  "\<forall>s\<in>domain(x) \<union> domain(y). \<forall>q. q \<in> P \<and> q \<preceq> p \<longrightarrow> forces_mem(q, s, x) \<longleftrightarrow> forces_mem(q, s, y)" 
        and s'in : "s' \<in> domain(Pn_auto(\<pi>)`x) \<union> domain(Pn_auto(\<pi>)`y)" 
        and q'inP : "q' \<in> P" and q'le : "q' \<preceq> \<pi>`p" 

        obtain q where qH : "q \<in> P" "q' = \<pi>`q" 
          using piauto unfolding is_P_auto_def using bij_is_surj  q'inP unfolding surj_def by blast 
        then have qlep : "q \<preceq> p"   
          apply (rule_tac \<pi>=\<pi> in P_auto_preserves_leq') 
          using piauto pinP q'le 
          by auto 

        have s'pname : "s' \<in> P_names" 
          apply (rule_tac A="domain(Pn_auto(\<pi>)`x)" and B="domain(Pn_auto(\<pi>)`y)" and c=s' in UnE)
          using s'in 
            apply simp 
           apply (rule_tac x="(Pn_auto(\<pi>) ` x)" in P_name_domain_P_name') 
          using xpname Pn_auto_value piauto 
            apply simp_all
          apply (rule_tac x="(Pn_auto(\<pi>) ` y)" in P_name_domain_P_name') 
          using ypname Pn_auto_value piauto 
           apply simp_all 
          done 
        then obtain s where sH : "s \<in> P_names" "s' = Pn_auto(\<pi>)`s" 
          using piauto Pn_auto_bij bij_is_surj unfolding surj_def by blast 

        have domain_lemma : "\<And>x. x \<in> P_names \<Longrightarrow> s' \<in> domain(Pn_auto(\<pi>)`x) \<Longrightarrow> s \<in> domain(x)" 
        proof - 
          fix x assume xpname : "x \<in> P_names" and s'in : "s' \<in> domain(Pn_auto(\<pi>)`x)" 
          then obtain p' where "<s', p'> \<in> Pn_auto(\<pi>)`x" by auto 
          then have "<s', p'> \<in> { <Pn_auto(\<pi>)`s, \<pi>`p>. <s, p> \<in> x }" 
            using Pn_auto xpname by auto
          then have "\<exists>t p. <t, p> \<in> x \<and> <s', p'> = <Pn_auto(\<pi>)`t, \<pi>`p>" 
            apply (rule_tac pair_rel_arg) 
            using xpname relation_P_name 
             apply simp_all 
            done 
          then obtain t p where tpH : "<t, p> \<in> x" "s' = Pn_auto(\<pi>)`t" by auto 
          then have "s = t" 
            apply (rule_tac f="Pn_auto(\<pi>)" and b="s'" and A= P_names and B=P_names in inj_equality)
            apply (rule_tac a="Pn_auto(\<pi>)`s" and b=s' in ssubst) 
            using sH 
               apply simp 
              apply (rule_tac function_apply_Pair) 
            using piauto Pn_auto_function 
               apply simp 
            using sH Pn_auto_domain 
              apply simp 
            apply (rule_tac a="Pn_auto(\<pi>)`t" and b=s' in ssubst) 
            using tpH 
              apply simp 
             apply (rule_tac function_apply_Pair) 
            using piauto Pn_auto_function 
              apply simp 
            using sH Pn_auto_domain 
             apply simp 
            using Pn_auto_bij piauto bij_is_inj 
             apply auto 
            using tpH xpname P_name_domain_P_name 
            by simp 
          then have "<s, p> \<in> x" using tpH by auto 
          then show "s \<in> domain(x)" by auto 
        qed
        
        have sin : "s \<in> domain(x) \<union> domain(y)" 
          using s'in apply simp 
          using domain_lemma s'pname xpname ypname by auto 

        then have srank : "P_rank(s) < a" 
          using srank_lemma by auto 

        have "forces_mem(q', s', Pn_auto(\<pi>) ` x) 
            \<longleftrightarrow> forces_mem(\<pi>`q, Pn_auto(\<pi>) ` s, Pn_auto(\<pi>) ` x)" using sH qH by auto
        also have "... \<longleftrightarrow> forces_mem(q, s, x)" 
          apply (rule_tac P="MEM(q,s,x)" in mp) 
           apply (simp add:MEM_def) 
          apply(rule MEMH [of "P_rank(s)"]) 
          using srank ltD sH xpname qH le_refl xrank P_rank_ord 
          by auto        
        also have "... \<longleftrightarrow> forces_mem(q, s, y)" 
          using qH qlep assm sin by auto 
        also have "... \<longleftrightarrow> forces_mem(\<pi>`q, Pn_auto(\<pi>) ` s, Pn_auto(\<pi>) ` y)" 
          apply (rule_tac P="MEM(q,s,y)" in mp) 
           apply (simp add:MEM_def) 
          apply(rule MEMH[of "P_rank(s)"]) 
          using srank ltD sH ypname qH le_refl yrank P_rank_ord 
          by auto  
        also have "... \<longleftrightarrow> forces_mem(q', s', Pn_auto(\<pi>) ` y)" using sH qH by auto
        finally show "forces_mem(q', s', Pn_auto(\<pi>) ` x) \<longleftrightarrow> forces_mem(q', s', Pn_auto(\<pi>) ` y) " by auto 
      next
        fix s q 
        assume assm: "\<forall>s'\<in>domain(Pn_auto(\<pi>) ` x) \<union> domain(Pn_auto(\<pi>) ` y).
              \<forall>q'. q' \<in> P \<and> q' \<preceq> \<pi> ` p \<longrightarrow> forces_mem(q', s', Pn_auto(\<pi>) ` x) \<longleftrightarrow> forces_mem(q', s', Pn_auto(\<pi>) ` y)" 
        and sin : "s \<in> domain(x) \<union> domain(y)" 
        and qinP : "q \<in> P" and qlep : "q \<preceq> p" 

        have srank : "P_rank(s) < a" using srank_lemma sin by auto 

        have domain_lemma : "\<And>x. x \<in> P_names \<Longrightarrow>  s\<in>domain(x) \<Longrightarrow> Pn_auto(\<pi>)`s \<in> domain(Pn_auto(\<pi>)`x)" 
        proof - 
          fix x assume assms : "s \<in> domain(x)" "x \<in> P_names" 
          then obtain p where "<s, p> \<in> x" unfolding domain_def by auto 
          then have "<Pn_auto(\<pi>)`s, \<pi>`p> \<in> { <Pn_auto(\<pi>)`s, \<pi>`p>. <s, p> \<in> x }" 
            apply (rule_tac pair_relI) 
            by auto 
          then have "<Pn_auto(\<pi>)`s, \<pi>`p> \<in> Pn_auto(\<pi>)`x" 
            using assms piauto Pn_auto 
            by auto 
          then show "Pn_auto(\<pi>)`s \<in> domain(Pn_auto(\<pi>)`x)" by auto 
        qed

        have s'in : "Pn_auto(\<pi>)`s \<in> domain(Pn_auto(\<pi>)`x) \<union> domain(Pn_auto(\<pi>) ` y)" 
          apply (rule_tac A="domain(x)" and B="domain(y)" and c=s in UnE)  
          using sin 
            apply simp 
           apply (rule_tac UnI1) 
           apply (rule_tac domain_lemma) 
          using xpname 
            apply simp 
           apply simp 
          apply (rule_tac UnI2) 
          apply (rule_tac domain_lemma) 
          using ypname 
           apply simp_all 
          done 

        have q'H : "\<pi>`q \<in> P \<and> \<pi>`q \<preceq> \<pi>`p" 
          using qinP qlep P_auto_value piauto P_auto_preserves_leq pinP by auto 

        have "forces_mem(q, s, x) \<longleftrightarrow> forces_mem(\<pi>`q, Pn_auto(\<pi>)`s, Pn_auto(\<pi>) ` x)" 
          apply (rule_tac P="MEM(q,s,x)" in mp) 
          apply (simp add:MEM_def) 
          apply (rule MEMH[of "P_rank(s)"])
          using srank ltD 
               apply simp 
          using P_name_domain_P_name' sin xpname ypname 
              apply blast 
          using xpname qinP le_refl xrank P_rank_ord 
             apply simp_all 
          done 
        also have "... \<longleftrightarrow> forces_mem(\<pi>`q, Pn_auto(\<pi>)`s, Pn_auto(\<pi>) ` y)" 
          using assm q'H s'in by auto 
        also have "... \<longleftrightarrow> forces_mem(q, s, y)" 
          apply (rule_tac P="MEM(q,s,y)" in mp) 
          apply (simp add:MEM_def) 
          apply (rule MEMH[of "P_rank(s)"])
          using srank ltD 
               apply simp 
          using P_name_domain_P_name' sin xpname ypname 
              apply blast 
          using ypname qinP le_refl yrank P_rank_ord 
             apply simp_all 
          done 
        finally show "forces_mem(q, s, x) \<longleftrightarrow> forces_mem(q, s, y) " by simp 
      qed
      also have "... \<longleftrightarrow> forces_eq(\<pi>`p, Pn_auto(\<pi>)`x, Pn_auto(\<pi>)`y)" 
        apply(rule iff_flip)
        apply(rule_tac def_forces_eq) 
        using pinP piauto P_auto_value 
        by auto 
      finally show "EQ(p,x,y)"
        unfolding EQ_def by auto 
    qed

    have main : "\<And>a. Ord(a) \<longrightarrow> Q(MEM, a, a) \<and> Q(EQ, a, a)" 
      apply (rule_tac eps_induct) 
      apply (rule impI)
    proof - 
      fix a assume ih: "\<forall>b \<in> a. Ord(b) \<longrightarrow> Q(MEM, b,b) \<and> Q(EQ, b,b)" 
      and orda : "Ord(a)" 
      then have "\<forall>b \<in> a. Q(MEM, b, a)" 
        apply (rule_tac MEM_step) 
         apply simp 
        using orda Ord_in_Ord 
        by auto 
      then have H : "Q(EQ, a,a)" 
        apply (rule_tac EQ_step) 
        using orda 
         apply auto 
        done 
      then have "\<forall>b \<in> succ(a). Q(EQ, b, b)" 
        apply clarify 
        apply (rule_tac i=b and j=a in leE) 
        using ltI orda 
          apply simp 
        using ltD ih orda lt_Ord 
         apply auto 
        done 
      then have "\<forall>b \<in> succ(a). Q(MEM, b, succ(a))"
        apply (rule_tac MEM_step) 
        using orda 
         apply auto 
        done 
      then have "Q(MEM, a, succ(a))" by auto 
      then have "Q(MEM, a, a)" 
        unfolding Q_def 
        apply clarify 
        apply (rule_tac P="P_rank(y) \<le> succ(a)" in mp) 
         apply auto 
        apply (rule_tac j=a in le_trans) 
         apply simp 
        apply (rule_tac j="succ(a)" in lt_trans) 
        using le_refl orda 
        by auto 
      then show " Q(\<lambda>a b c. MEM(a, b, c), a, a) \<and> Q(\<lambda>a b c. EQ(a, b, c), a, a)" 
        using H by auto 
    qed
      
    fix x y p assume pinP : "p \<in> P" and xpname : "x \<in> P_names" and ypname: "y \<in> P_names" 

    define r where "r \<equiv> if P_rank(x) \<le> P_rank(y) then P_rank(y) else P_rank(x)" 
    have roed : "Ord(r)" 
      apply (cases "P_rank(x) \<le> P_rank(y)")  
      using r_def P_rank_ord by auto 

    have rle: "P_rank(x) \<le> r \<and> P_rank(y) \<le> r" 
      apply (cases "P_rank(x) \<le> P_rank(y)") 
      apply (rule_tac P="r = P_rank(y)" in mp) 
        apply simp 
      using P_rank_ord 
        apply simp 
       apply (simp add:r_def) 
      apply (rule_tac P="r = P_rank(x)" in mp) 
      using P_rank_ord 
       apply simp 
      apply (rule_tac P="P_rank(y) < P_rank(x)" in mp) 
      using lt_succ_lt 
        apply simp 
      using not_le_iff_lt P_rank_ord 
       apply simp 
      apply (simp add:r_def) 
      done 
    
    have H : "Q(MEM, r,r) \<and> Q(EQ, r,r)" 
      using roed main by auto
    have H1: "MEM(p, x, y)" 
      using H unfolding Q_def using xpname ypname pinP rle apply auto done 
    have H2: "EQ(p, x, y)" 
      using H unfolding Q_def using xpname ypname pinP rle apply auto done 
    
    show "(forces_mem(p, x, y) \<longleftrightarrow> forces_mem(\<pi> ` p, Pn_auto(\<pi>) ` x, Pn_auto(\<pi>) ` y)) \<and>
       (forces_eq(p, x, y) \<longleftrightarrow> forces_eq(\<pi> ` p, Pn_auto(\<pi>) ` x, Pn_auto(\<pi>) ` y))" 
      using H1 H2 unfolding MEM_def EQ_def by auto 
  qed


lemma symmetry_lemma_mem : 
  fixes \<pi> p i j env
  assumes "is_P_auto(\<pi>)" "p \<in> P" "env \<in> list(HS)" "i < length(env)" "j < length(env)" 
  shows "p \<tturnstile>HS Member(i, j) env \<longleftrightarrow> \<pi>`p \<tturnstile>HS Member(i, j) map(\<lambda>x. Pn_auto(\<pi>)`x, env)" 
proof - 
  have H: "\<And>\<pi> p x y. is_P_auto(\<pi>) \<Longrightarrow> p \<in> P \<Longrightarrow> x \<in> HS \<Longrightarrow> y \<in> HS 
            \<Longrightarrow> (forces_mem(p, x, y) \<longleftrightarrow> forces_mem(\<pi>`p, Pn_auto(\<pi>)`x, Pn_auto(\<pi>)`y))" 
    using symmetry_lemma_base HS_iff by auto 

  have envin : "env \<in> list(M)" 
    apply(rule_tac A= "list(HS)" in subsetD, rule list_mono)
    using HS_iff P_name_in_M assms 
    by auto

  have mapin : "map(\<lambda>x. Pn_auto(\<pi>) ` x, env) \<in> list(M)"  
    apply(rule map_type)
    using assms 
     apply simp
    apply(rule Pn_auto_value_in_M)
    using assms HS_iff
    by auto

  have mapnthin : "\<And>i. i < length(env) \<Longrightarrow> nth(i, map(\<lambda>x. Pn_auto(\<pi>) ` x, env)) \<in> M" 
    apply(rule nth_type)
    using assms mapin length_map 
    by auto

  have "p \<tturnstile>HS Member(i, j) env \<longleftrightarrow> p \<tturnstile> Member(i, j) env" 
    apply(rule iff_flip, rule ForcesHS_Member)
    using assms envin P_in_M transM lt_nat_in_nat
    by auto
  also have "... \<longleftrightarrow> forces_mem(p, nth(i, env), nth(j, env))" 
    apply(rule Forces_Member)
    using assms envin Forces_Member nth_type HS_iff lt_nat_in_nat
    by auto
  also have "... \<longleftrightarrow> forces_mem(\<pi>`p, Pn_auto(\<pi>)`nth(i, env), Pn_auto(\<pi>)`nth(j, env))" 
    using assms nth_type H
    by auto
  also have "... \<longleftrightarrow> forces_mem(\<pi>`p, nth(i, map(\<lambda>x. Pn_auto(\<pi>)`x, env)), nth(j, map(\<lambda>x. Pn_auto(\<pi>)`x, env)))" 
    using assms lt_nat_in_nat nth_map
    by auto
  also have "... \<longleftrightarrow> \<pi>`p \<tturnstile> Member(i, j) map(\<lambda>x. Pn_auto(\<pi>)`x, env)"
    apply(rule iff_flip, rule Forces_Member)
    using assms mapin lt_nat_in_nat nth_type mapnthin P_auto_value
    by auto
  also have "... \<longleftrightarrow> \<pi>`p \<tturnstile>HS Member(i, j) map(\<lambda>x. Pn_auto(\<pi>)`x, env)"
    apply(rule ForcesHS_Member)
    using assms lt_nat_in_nat mapin P_auto_value
       apply auto[3]
    apply(rule_tac A=P in subsetD)
    using P_in_M transM 
     apply force 
    apply(rule P_auto_value)
    using assms 
    by auto
  finally show ?thesis 
    by auto
qed

lemma symmetry_lemma_eq : 
  fixes \<pi> p i j env
  assumes "is_P_auto(\<pi>)" "p \<in> P" "env \<in> list(HS)" "i < length(env)" "j < length(env)" 
  shows "p \<tturnstile>HS Equal(i, j) env \<longleftrightarrow> \<pi>`p \<tturnstile>HS Equal(i, j) map(\<lambda>x. Pn_auto(\<pi>)`x, env)" 
proof - 
  have H: "\<And>\<pi> p x y. is_P_auto(\<pi>) \<Longrightarrow> p \<in> P \<Longrightarrow> x \<in> HS \<Longrightarrow> y \<in> HS 
            \<Longrightarrow> (forces_eq(p, x, y) \<longleftrightarrow> forces_eq(\<pi>`p, Pn_auto(\<pi>)`x, Pn_auto(\<pi>)`y))" 
    using symmetry_lemma_base HS_iff by auto 

  have envin : "env \<in> list(M)" 
    apply(rule_tac A= "list(HS)" in subsetD, rule list_mono)
    using HS_iff P_name_in_M assms 
    by auto

  have mapin : "map(\<lambda>x. Pn_auto(\<pi>) ` x, env) \<in> list(M)"  
    apply(rule map_type)
    using assms 
     apply simp
    apply(rule Pn_auto_value_in_M)
    using assms HS_iff
    by auto

  have mapnthin : "\<And>i. i < length(env) \<Longrightarrow> nth(i, map(\<lambda>x. Pn_auto(\<pi>) ` x, env)) \<in> M" 
    apply(rule nth_type)
    using assms mapin length_map 
    by auto

  have "p \<tturnstile>HS Equal(i, j) env \<longleftrightarrow> p \<tturnstile> Equal(i, j) env" 
    apply(rule iff_flip, rule ForcesHS_Equal)
    using assms envin P_in_M transM lt_nat_in_nat
    by auto
  also have "... \<longleftrightarrow> forces_eq(p, nth(i, env), nth(j, env))" 
    apply(rule Forces_Equal)
    using assms envin Forces_Member nth_type HS_iff lt_nat_in_nat
    by auto
  also have "... \<longleftrightarrow> forces_eq(\<pi>`p, Pn_auto(\<pi>)`nth(i, env), Pn_auto(\<pi>)`nth(j, env))" 
    using assms nth_type H
    by auto
  also have "... \<longleftrightarrow> forces_eq(\<pi>`p, nth(i, map(\<lambda>x. Pn_auto(\<pi>)`x, env)), nth(j, map(\<lambda>x. Pn_auto(\<pi>)`x, env)))" 
    using assms lt_nat_in_nat nth_map
    by auto
  also have "... \<longleftrightarrow> \<pi>`p \<tturnstile> Equal(i, j) map(\<lambda>x. Pn_auto(\<pi>)`x, env)"
    apply(rule iff_flip, rule Forces_Equal)
    using assms mapin lt_nat_in_nat nth_type mapnthin P_auto_value
    by auto
  also have "... \<longleftrightarrow> \<pi>`p \<tturnstile>HS Equal(i, j) map(\<lambda>x. Pn_auto(\<pi>)`x, env)"
    apply(rule ForcesHS_Equal)
    using assms lt_nat_in_nat mapin P_auto_value
       apply auto[3]
    apply(rule_tac A=P in subsetD)
    using P_in_M transM 
     apply force 
    apply(rule P_auto_value)
    using assms 
    by auto
  finally show ?thesis 
    by auto
qed

lemma symmetry_lemma:
  fixes \<phi> \<pi>  
  assumes "\<phi> \<in> formula" "is_P_auto(\<pi>)" "\<pi> \<in> \<G>" 
  shows "\<And>env p. env \<in> list(HS) \<Longrightarrow> arity(\<phi>) \<le> length(env) \<Longrightarrow> p \<in> P \<Longrightarrow> p \<tturnstile>HS \<phi> env \<longleftrightarrow> \<pi>`p \<tturnstile>HS \<phi> map(\<lambda>x. Pn_auto(\<pi>)`x, env)" 
  using \<open>\<phi> \<in> formula\<close>
proof(induct)
  case (Member x y)
  then show ?case 
    apply(rule_tac symmetry_lemma_mem)
    using assms
        apply auto[3]
     apply simp
     apply(rule_tac b="succ(x) \<union> succ(y)" in lt_le_lt, rule ltI, simp, simp, simp)+
    done
next
  case (Equal x y)
  then show ?case
    apply(rule_tac symmetry_lemma_eq)
    using assms
        apply auto[3]
     apply simp
     apply(rule_tac b="succ(x) \<union> succ(y)" in lt_le_lt, rule ltI, simp, simp, simp)+
    done
next
  case (Nand \<phi> \<psi>)

  have envin : "env \<in> list(M)" 
    apply(rule_tac A= "list(HS)" in subsetD, rule list_mono)
    using HS_iff P_name_in_M assms Nand
    by auto
  have mapin : "map(\<lambda>x. Pn_auto(\<pi>) ` x, env) \<in> list(M)"  
    apply(rule map_type)
    using assms Nand
     apply simp
    apply(rule Pn_auto_value_in_M)
    using assms HS_iff
    by auto

  have arityle : "arity(\<phi>) \<le> length(env) \<and> arity(\<psi>) \<le> length(env)"
    apply(rule conjI, rule_tac j="arity(\<phi>) \<union> arity(\<psi>)" in le_trans, rule max_le1)
    using Nand
       apply auto[3]
     apply(rule_tac j="arity(\<phi>) \<union> arity(\<psi>)" in le_trans)
    using Nand max_le2
    by auto

  then show ?case
  proof - 
    have "p \<tturnstile>HS Nand(\<phi>, \<psi>) env \<longleftrightarrow> \<not>(\<exists>q\<in>M. q\<in>P \<and> q\<preceq>p \<and> (q \<tturnstile>HS \<phi> env) \<and> (q \<tturnstile>HS \<psi> env))"
      using ForcesHS_Nand Nand envin arityle 
      by auto
    also have "... \<longleftrightarrow> \<not>(\<exists>q\<in>M. q\<in>P \<and> q\<preceq>p \<and> (\<pi>`q \<tturnstile>HS \<phi> map(\<lambda>x. Pn_auto(\<pi>) ` x, env)) \<and> (\<pi>`q \<tturnstile>HS \<psi> map(\<lambda>x. Pn_auto(\<pi>) ` x, env)))"
      using Nand arityle by auto
    also have "... \<longleftrightarrow> \<not>(\<exists>q\<in>M. q\<in>P \<and> \<pi>`q\<preceq>\<pi>`p \<and> (\<pi>`q \<tturnstile>HS \<phi> map(\<lambda>x. Pn_auto(\<pi>) ` x, env)) \<and> (\<pi>`q \<tturnstile>HS \<psi> map(\<lambda>x. Pn_auto(\<pi>) ` x, env)))"
      using is_P_auto_def assms Nand by auto
    also have "... \<longleftrightarrow> \<not>(\<exists>q\<in>M. q\<in>P \<and> q\<preceq>\<pi>`p \<and> (q \<tturnstile>HS \<phi> map(\<lambda>x. Pn_auto(\<pi>) ` x, env)) \<and> (q \<tturnstile>HS \<psi> map(\<lambda>x. Pn_auto(\<pi>) ` x, env)))"
      apply(subgoal_tac "P \<subseteq> M")
       apply(rule notnot_iff, rule iffI, clarify)
        apply(rename_tac q, rule_tac x="\<pi>`q" in bexI)
      using assms P_auto_value 
         apply auto[2]
       apply clarify 
       apply(rename_tac q, subgoal_tac "\<exists>r \<in> P. \<pi>`r = q") 
        apply force
       apply(subgoal_tac "\<pi> \<in> surj(P, P)")
      using surj_def 
        apply force 
      using assms is_P_auto_def bij_is_surj transM P_in_M
      by auto
    also have "... \<longleftrightarrow> \<pi>`p \<tturnstile>HS Nand(\<phi>, \<psi>) map(\<lambda>x. Pn_auto(\<pi>) ` x, env)" 
      apply(rule iff_flip, rule ForcesHS_Nand)
      using Nand mapin P_auto_value assms
      by auto
    finally show "M, [p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env \<Turnstile> forcesHS(Nand(\<phi>, \<psi>)) \<longleftrightarrow>
                  M, [\<pi> ` p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ map(\<lambda>a. Pn_auto(\<pi>) ` a, env) \<Turnstile> forcesHS(Nand(\<phi>, \<psi>))" 
      by simp
  qed
next
  case (Forall \<phi>)

  have envin : "env \<in> list(M)" 
    apply(rule_tac A= "list(HS)" in subsetD, rule list_mono)
    using HS_iff P_name_in_M assms Forall
    by auto
  have mapin : "map(\<lambda>x. Pn_auto(\<pi>) ` x, env) \<in> list(M)"  
    apply(rule map_type)
    using assms Forall
     apply simp
    apply(rule Pn_auto_value_in_M)
    using assms HS_iff
    by auto

  have arityle : "arity(\<phi>) \<le> succ(length(env))"
    apply(rule_tac n="arity(\<phi>)" in natE)
    using Forall 
    by auto

  then show ?case 
  proof - 
    have "p \<tturnstile>HS Forall(\<phi>) env \<longleftrightarrow> (\<forall>x \<in> HS. p \<tturnstile>HS \<phi> [x] @ env)"
      using Forall ForcesHS_Forall envin by auto
    also have "... \<longleftrightarrow> (\<forall>x \<in> HS. \<pi>`p \<tturnstile>HS \<phi> map(\<lambda>x. Pn_auto(\<pi>)`x, [x] @ env))"
      using Forall arityle by auto
    also have "... \<longleftrightarrow> (\<forall>x \<in> HS. \<pi>`p \<tturnstile>HS \<phi> [Pn_auto(\<pi>)`x] @ map(\<lambda>x. Pn_auto(\<pi>)`x, env))"
      by auto
    also have "... \<longleftrightarrow> (\<forall>x \<in> HS. \<pi>`p \<tturnstile>HS \<phi> [x] @ map(\<lambda>x. Pn_auto(\<pi>)`x, env))"
      apply(rule iffI, rule ballI)
       apply(rename_tac x, subgoal_tac "\<exists>y \<in> P_names. Pn_auto(\<pi>)`y = x")
      apply clarify
      using HS_Pn_auto assms 
        apply force 
       apply(rename_tac x, subgoal_tac "Pn_auto(\<pi>) \<in> bij(P_names, P_names)") 
      using bij_is_surj surj_def HS_iff 
        apply force 
       apply(rule Pn_auto_bij)
      using assms 
       apply simp
      apply(rule ballI)
      apply(rename_tac x, subgoal_tac "Pn_auto(\<pi>)`x \<in> HS")
      using assms HS_iff
       apply force 
      apply(rule iffD1, rule HS_Pn_auto)
      using assms HS_iff
      by auto
    also have "... \<longleftrightarrow> \<pi>`p \<tturnstile>HS Forall(\<phi>) map(\<lambda>x. Pn_auto(\<pi>)`x, env)" 
      apply(rule iff_flip, rule ForcesHS_Forall)
      using P_auto_value Forall assms mapin 
      by auto
    finally show "M, [p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ env \<Turnstile> forcesHS(Forall(\<phi>)) \<longleftrightarrow>
                  M, [\<pi> ` p, P, leq, one, \<langle>\<F>, \<G>, P, P_auto\<rangle>] @ map(\<lambda>x. Pn_auto(\<pi>) ` x, env) \<Turnstile> forcesHS(Forall(\<phi>))"
      by simp
  qed
qed 

end
end















