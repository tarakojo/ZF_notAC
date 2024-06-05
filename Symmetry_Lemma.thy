theory Symmetry_Lemma
  imports 
    "Forcing/Forcing_Main" 
    Automorphism_Theorems
    Namification
begin 

context forcing_data_partial
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
  "\<And>\<pi> p x y. is_P_auto(\<pi>) \<Longrightarrow> p \<in> P \<Longrightarrow> x \<in> P_names \<Longrightarrow> y \<in> P_names 
    \<Longrightarrow> (forces_mem(p, x, y) \<longleftrightarrow> forces_mem(\<pi>`p, Pn_auto(\<pi>)`x, Pn_auto(\<pi>)`y))" 
  using symmetry_lemma_base by auto 

lemma symmetry_lemma_eq : 
  "\<And>\<pi> p x y. is_P_auto(\<pi>) \<Longrightarrow> p \<in> P \<Longrightarrow> x \<in> P_names \<Longrightarrow> y \<in> P_names 
    \<Longrightarrow> (forces_eq(p, x, y) \<longleftrightarrow> forces_eq(\<pi>`p, Pn_auto(\<pi>)`x, Pn_auto(\<pi>)`y))" 
  using symmetry_lemma_base by auto   

lemma symmetry_lemma':
  fixes env \<phi> \<pi> p 
  assumes envin : "env \<in> list(M)" and phiin : "\<phi> \<in> formula" and phiarity : "arity(\<phi>) \<le> length(env)" 
  and pin : "p \<in> P" and piauto : "is_P_auto(\<pi>)" 
  shows "p \<tturnstile> \<phi> env \<longleftrightarrow> \<pi>`p \<tturnstile> \<phi> map(\<lambda>x. Pn_auto(\<pi>)`x, map(P_namify, env))" 
  apply (rule_tac P = "\<forall> env \<in> list(M). \<forall> p \<in> P.  arity(\<phi>) \<le> length(env) \<longrightarrow> ( p \<tturnstile> \<phi> env \<longleftrightarrow> \<pi>`p \<tturnstile> \<phi> map(\<lambda>x. Pn_auto(\<pi>)`x, map(P_namify, env)))" in mp)
   apply (rule impI) 
  using envin phiin phiarity pin 
   apply blast  
  using phiin 
proof(induct)
  case (Member x y)
  then show ?case 
    apply clarify
    apply(rule_tac Q="p \<tturnstile> Member(x, y) map(P_namify, env)" in iff_trans)   
     apply(rule_tac forces_P_namify) 
        apply simp 
       apply simp 
      apply simp 
     apply simp
    apply (rule_tac P="x < length(env)" in mp) 
     apply (rule_tac P="y < length(env)" in mp)
      apply clarify 
      apply (rule_tac P="nth(x, map(P_namify, env)) \<in> P_names" in mp)
       apply (rule_tac P="nth(y, map(P_namify, env)) \<in> P_names" in mp)   
        apply clarify 
        apply(rule_tac Q="forces_mem(p, nth(x, map(P_namify, env)), nth(y, map(P_namify, env)))" in iff_trans) 
         apply(rule_tac Forces_Member) 
                apply simp
    using P_name_in_M 
               apply simp 
    using P_name_in_M 
              apply simp 
             apply(rule_tac A=M in map_type) 
              apply simp 
    using P_namify_value_in_M 
             apply simp 
            apply simp 
           apply simp 
          apply simp 
         apply simp 
        apply(rule_tac Q="forces_mem(\<pi>`p, Pn_auto(\<pi>)`nth(x, map(P_namify, env)), Pn_auto(\<pi>)`nth(y, map(P_namify, env)))" in iff_trans) 
         apply(rule_tac symmetry_lemma_mem) 
    using piauto 
            apply simp 
           apply simp 
          apply simp 
         apply simp 
        apply(rule iff_flip) 
        apply(rule_tac Forces_Member) 
    using P_auto_value piauto 
               apply simp 
    using piauto Pn_auto_value_in_M 
              apply simp 
    using piauto Pn_auto_value_in_M 
             apply simp 
            apply(rule_tac A=M in map_type) 
             apply(rule_tac A=M in map_type) 
              apply simp 
    using P_namify_value_in_M 
             apply simp 
            apply(rule_tac P="xa \<in> P_names" and Q="xa \<notin> P_names" in disjE) 
              apply simp 
    using P_name_in_M Pn_auto_value_in_M piauto 
             apply simp 
            apply(rule_tac a="0" and b="Pn_auto(\<pi>)`xa" in ssubst) 
             apply(rule_tac apply_0) 
    using Pn_auto_domain 
             apply simp 
    using zero_in_M 
            apply simp 
    using nth_map 
           apply simp 
    using nth_map 
          apply simp 
         apply simp 
        apply simp_all
       apply(rule_tac P_namify_value_in_P_names) 
       apply(rule_tac nth_type) 
        apply simp 
       apply simp 
      apply(rule_tac P_namify_value_in_P_names) 
      apply(rule_tac nth_type) 
       apply simp 
      apply simp 
     apply (rule_tac b="succ(x) \<union> succ(y)" in lt_le_lt) 
    using ltD ltI 
      apply simp_all
    apply (rule_tac b="succ(x) \<union> succ(y)" in lt_le_lt) 
    using ltD ltI 
     apply simp_all 
    done
next
  case (Equal x y)
  then show ?case
    apply (clarify) 
    apply (rule_tac Q="p \<tturnstile> Equal(x, y) map(P_namify, env)" in iff_trans) 
     apply (rule_tac forces_P_namify) 
        apply simp 
       apply simp 
      apply simp 
     apply simp
    apply (rule_tac P="x < length(env)" in mp) 
     apply (rule_tac P="y < length(env)" in mp)
      apply clarify 
      apply (rule_tac P="nth(x, map(P_namify, env)) \<in> P_names" in mp)
       apply (rule_tac P="nth(y, map(P_namify, env)) \<in> P_names" in mp)
        apply clarify 
        apply (rule_tac Q="forces_eq(p, nth(x, map(P_namify, env)), nth(y, map(P_namify, env)))" in iff_trans)
         apply (rule_tac Forces_Equal) 
                apply simp 
    using P_name_in_M 
               apply simp 
    using P_name_in_M 
              apply simp 
             apply(rule_tac A=M in map_type) 
              apply simp 
    using P_namify_value_in_M 
             apply simp 
            apply simp 
           apply simp 
          apply simp 
         apply simp 
        apply(rule_tac Q="forces_eq(\<pi>`p, Pn_auto(\<pi>)`nth(x, map(P_namify, env)), Pn_auto(\<pi>)`nth(y, map(P_namify, env)))" in iff_trans) 
         apply(rule_tac symmetry_lemma_eq) 
    using piauto 
            apply simp 
           apply simp 
          apply simp 
         apply simp 
        apply(rule iff_flip) 
        apply(rule_tac Forces_Equal) 
    using P_auto_value piauto 
               apply simp 
    using piauto Pn_auto_value_in_M 
              apply simp 
    using piauto Pn_auto_value_in_M 
             apply simp 
            apply(rule_tac A=M in map_type) 
             apply(rule_tac A=M in map_type) 
              apply simp 
    using P_namify_value_in_M 
             apply simp 
            apply(rule_tac P="xa \<in> P_names" and Q="xa \<notin> P_names" in disjE) 
              apply simp 
    using P_name_in_M Pn_auto_value_in_M piauto 
             apply simp 
            apply(rule_tac a="0" and b="Pn_auto(\<pi>)`xa" in ssubst) 
             apply(rule_tac apply_0) 
    using Pn_auto_domain 
             apply simp 
    using zero_in_M 
            apply simp 
    using nth_map 
           apply simp 
    using nth_map 
          apply simp 
         apply simp 
        apply simp_all
       apply(rule_tac P_namify_value_in_P_names) 
       apply(rule_tac nth_type) 
        apply simp 
       apply simp 
      apply(rule_tac P_namify_value_in_P_names) 
      apply(rule_tac nth_type) 
       apply simp 
      apply simp 
     apply (rule_tac b="succ(x) \<union> succ(y)" in lt_le_lt) 
    using ltD ltI 
      apply simp_all
    apply (rule_tac b="succ(x) \<union> succ(y)" in lt_le_lt) 
    using ltD ltI 
     apply simp_all 
    done
next
  have ex_lemma : "\<And>A B. (\<And>q. q \<in> M \<Longrightarrow> A(q) \<Longrightarrow> B(q)) \<Longrightarrow> (\<And>q. q \<in> M \<Longrightarrow> B(q) \<Longrightarrow> A(q)) \<Longrightarrow> (\<exists>q \<in> M. A(q)) \<longleftrightarrow> (\<exists>q \<in> M. B(q))" 
    by auto 
  have ex_lemma2 : "\<And>A. (\<exists>q \<in> M. q \<in> P \<and> A(q)) \<longleftrightarrow> (\<exists>q \<in> M. q \<in> P \<and> A(\<pi>`q))"
    apply (rule iffI; auto) 
    apply (rule_tac P="\<exists>q' \<in> P. \<pi>`q'=q" in mp) 
    using transM P_in_M 
      apply auto 
    using piauto 
    unfolding is_P_auto_def 
    using bij_is_surj 
    unfolding surj_def 
     apply auto 
    apply (rule_tac P="\<pi>`q \<in> P" in mp) 
     apply auto 
    using P_auto_value piauto 
    by auto 
    
  case (Nand \<phi> \<psi>)
  then show ?case
    apply clarify 
    apply (rule_tac P=" arity(\<phi>) \<le> length(env) " in mp)
     apply (rule_tac P=" arity(\<psi>) \<le> length(env) " in mp)
      apply (clarify)
      apply (rule_tac Q="\<not> (\<exists>q\<in>M. q \<in> P \<and> q \<preceq> p \<and> q \<tturnstile> \<phi> env \<and> q \<tturnstile> \<psi> env)" in iff_trans)
       apply (rule_tac Forces_Nand) 
    using pin 
          apply simp 
         apply simp 
        apply simp 
       apply simp
      apply (rule_tac Q="\<not> (\<exists>q\<in>M. q \<in> P \<and> \<pi>`q \<preceq> \<pi>`p \<and> \<pi>`q \<tturnstile> \<phi> map(\<lambda>x. Pn_auto(\<pi>)`x, map(P_namify, env)) \<and> \<pi>`q \<tturnstile> \<psi> map(\<lambda>x. Pn_auto(\<pi>)`x, map(P_namify, env)))" in iff_trans)
       apply (rule not_cong) 
       apply(rule_tac ex_lemma) 
    using piauto P_auto_preserves_leq P_auto_preserves_leq' 
        apply blast 
    using piauto P_auto_preserves_leq P_auto_preserves_leq' 
       apply blast 
      apply (rule_tac Q="\<not> (\<exists>q\<in>M. q \<in> P \<and> q \<preceq> \<pi>`p \<and> q \<tturnstile> \<phi> map(\<lambda>x. Pn_auto(\<pi>)`x, map(P_namify, env)) \<and> q \<tturnstile> \<psi> map(\<lambda>x. Pn_auto(\<pi>)`x, map(P_namify, env)))" in iff_trans)
       apply (rule not_cong) 
       apply(rule iff_flip) 
       apply(rule_tac ex_lemma2) 
      apply(rule iff_flip) 
      apply (rule_tac Forces_Nand)
         apply (rule_tac P_auto_value) 
    using piauto 
          apply simp_all 
      apply(rule_tac A=M in map_type) 
       apply(rule_tac A=M in map_type) 
        apply simp 
    using P_namify_value_in_M 
       apply simp
      apply(rule_tac P="x \<in> P_names" and Q="x \<notin> P_names" in disjE) 
        apply simp 
    using P_name_in_M Pn_auto_value_in_M piauto 
       apply simp 
      apply(rule_tac a="0" and b="Pn_auto(\<pi>)`x" in ssubst) 
       apply(rule_tac apply_0) 
    using Pn_auto_domain 
       apply simp 
    using zero_in_M 
      apply simp 
     apply (cases "arity(\<phi>) \<le> arity(\<psi>)")  
      apply (rule_tac b="arity(\<psi>)" and a="arity(\<phi>) \<union> arity(\<psi>)" in ssubst) 
       apply (rule eq_flip) 
       apply (rule_tac nat_union_abs1) 
    using arity_type Ord_nat 
         apply simp_all
     apply (rule_tac P="arity(\<psi>) < arity(\<phi>)" in mp) 
      apply (rule impI)
      apply (rule_tac j="arity(\<phi>) \<union> arity(\<psi>)" in lt_trans) 
    using ltD ltI 
       apply simp_all
    using not_le_iff_lt arity_type Ord_nat 
     apply simp 
    apply (cases "arity(\<psi>) \<le> arity(\<phi>)")  
     apply (rule_tac b="arity(\<phi>)" and a="arity(\<phi>) \<union> arity(\<psi>)" in ssubst) 
      apply (rule eq_flip) 
      apply (rule_tac nat_union_abs2) 
    using arity_type Ord_nat 
        apply simp_all
    apply (rule_tac P="arity(\<phi>) < arity(\<psi>)" in mp) 
     apply (rule impI)
     apply (rule_tac j="arity(\<phi>) \<union> arity(\<psi>)" in lt_trans) 
    using ltD ltI 
      apply simp_all
    using not_le_iff_lt arity_type Ord_nat 
    apply simp 
    done 
next
  have forall_lemma : "\<And>A P Q. (\<And>x. x \<in> A \<Longrightarrow> P(x) \<longleftrightarrow> Q(x)) \<Longrightarrow> (\<forall>x \<in> A. P(x)) \<longleftrightarrow> (\<forall>x \<in> A. Q(x))" by auto 
  have iff_lemma : "\<And>Q. (\<forall>x \<in> M. Q(P_namify(x))) \<longleftrightarrow> (\<forall>x \<in> M. Q(Pn_auto(\<pi>)`P_namify(x)))" 
    apply (rule iffI) 
     apply auto 
  proof - 
    fix Q x assume assms : "\<forall>x\<in>M. Q(P_namify(x))" "x \<in> M" 
    have H:"Pn_auto(\<pi>) ` P_namify(x) \<in> P_names" 
      using assms P_namify_value_in_P_names Pn_auto_value piauto 
      apply auto 
      done 
    then have "Q(P_namify(Pn_auto(\<pi>) ` P_namify(x)))" using P_name_in_M assms by auto 
    then show "Q(Pn_auto(\<pi>) ` P_namify(x))" using H P_namify_P_name by auto 
  next 
    fix Q x assume assms : "\<forall>x\<in>M. Q(Pn_auto(\<pi>) ` P_namify(x))" "x \<in> M"
    then have H:"P_namify(x) \<in> P_names" using P_namify_value_in_P_names by auto

    have "Pn_auto(\<pi>) \<in> surj(P_names, P_names)" 
      using piauto Pn_auto_bij bij_is_surj by auto 
    then obtain y where yH : "y \<in> P_names" "Pn_auto(\<pi>)`y=P_namify(x)" 
      unfolding surj_def using H by auto 
    then have "Q(Pn_auto(\<pi>) ` P_namify(y))" 
      using P_name_in_M assms by auto 
    then have "Q(Pn_auto(\<pi>)`y)" using P_namify_P_name yH by auto  
    then show "Q(P_namify(x))" using yH by auto 
  qed

  have eq_lemma : 
    "\<And>l. l \<in> list(M) \<Longrightarrow> map(P_namify, map(\<lambda>x. Pn_auto(\<pi>) ` x, map(P_namify, l))) = map(\<lambda>x. Pn_auto(\<pi>) ` x, map(P_namify, l))"
  proof - 
    fix l assume lin : "l \<in> list(M)" 
    show "map(P_namify, map(\<lambda>x. Pn_auto(\<pi>) ` x, map(P_namify, l))) = map(\<lambda>x. Pn_auto(\<pi>) ` x, map(P_namify, l))" 
      using lin
      proof(induct)
        case Nil
        then show ?case by simp
      next
        case (Cons a l)
        then show ?case 
          apply auto 
          apply(rule_tac P=" Pn_auto(\<pi>) ` P_namify(a) \<in> P_names" in mp) 
          using P_namify_P_name 
           apply simp 
          apply(rule_tac Pn_auto_value) 
          using piauto P_namify_value_in_P_names 
          by auto 
    qed 
  qed

  case (Forall \<phi>)

  then show ?case 
    apply clarify 
    apply (rule_tac Q="(\<forall>x\<in>M. p \<tturnstile> \<phi> [x] @ env)" in iff_trans)
     apply (rule_tac Forces_Forall) 
       apply simp 
      apply simp 
     apply simp 
    apply (rule_tac Q="(\<forall>x\<in>M. \<pi>`p \<tturnstile> \<phi> map(\<lambda>x. Pn_auto(\<pi>) ` x, map(P_namify, [x] @ env)))" in iff_trans) 
     apply (rule_tac forall_lemma) 
     apply(rule_tac P="arity(\<phi>) \<le> length([x] @ env)" in mp) 
      apply simp
     apply (rule_tac n="arity(\<phi>)" in natE) 
    using arity_type 
       apply simp
      apply simp 
    using succ_pred_eq 
     apply simp
    apply (rule_tac Q="(\<forall>x\<in>M. \<pi> ` p \<tturnstile> \<phi> map(\<lambda>x. Pn_auto(\<pi>) ` x, [P_namify(x)] @ map(P_namify, env)))" in iff_trans) 
     apply simp
    apply (rule_tac Q="(\<forall>x\<in>M. \<pi> ` p \<tturnstile> \<phi> [Pn_auto(\<pi>) ` P_namify(x)] @ map(\<lambda>x. Pn_auto(\<pi>) ` x, map(P_namify, env)))" in iff_trans) 
     apply simp
    apply (rule_tac Q="(\<forall>x\<in>M. \<pi> ` p \<tturnstile> \<phi> [P_namify(x)] @ map(\<lambda>x. Pn_auto(\<pi>) ` x, map(P_namify, env)))" in iff_trans)
     apply(rule iff_flip) 
     apply (rule_tac iff_lemma) 
    apply (rule_tac Q=" (\<forall>x\<in>M. \<pi> ` p \<tturnstile> \<phi> map(P_namify, [x] @ map(\<lambda>x. Pn_auto(\<pi>) ` x, map(P_namify, env))))" in iff_trans)
    apply (rule_tac forall_lemma) 
    apply (rule_tac a=" [P_namify(x)] @ map(\<lambda>x. Pn_auto(\<pi>) ` x, map(P_namify, env))" and b="map(P_namify, [x] @ map(\<lambda>x. Pn_auto(\<pi>) ` x, map(P_namify, env)))" in ssubst) 
    apply (rule_tac a="map(P_namify, [x]) @ map(P_namify, map(\<lambda>x. Pn_auto(\<pi>) ` x, map(P_namify, env)))"  
              and b = "map(P_namify, [x] @ map(\<lambda>x. Pn_auto(\<pi>) ` x, map(P_namify, env)))" in ssubst) 
       apply (rule_tac A=M in map_app_distrib) 
       apply simp  
    apply (rule_tac b=" map(P_namify, map(\<lambda>x. Pn_auto(\<pi>) ` x, map(P_namify, env))) " 
                and a = "map(\<lambda>x. Pn_auto(\<pi>) ` x, map(P_namify, env))" in ssubst) 
       apply(rule_tac eq_lemma) 
       apply simp 
      apply simp 
     apply simp 
    apply(rule_tac Q="(\<forall>x\<in>M. \<pi> ` p \<tturnstile> \<phi> [x] @ map(\<lambda>x. Pn_auto(\<pi>) ` x, map(P_namify, env)))" in iff_trans)
     apply(rule iff_flip) 
     apply(rule_tac forall_lemma) 
     apply(rule_tac forces_P_namify) 
    using P_auto_value piauto 
        apply simp 
       apply(rule_tac A=M in app_type) 
        apply simp 
       apply(rule_tac A=M in map_type) 
        apply(rule_tac A=M in map_type) 
         apply simp 
    using P_namify_value_in_M 
        apply simp 
       apply(rule_tac P="xa \<in> P_names"and Q="xa \<notin> P_names" in disjE) 
         apply simp 
    using Pn_auto_value_in_M piauto 
        apply simp 
    using Pn_auto_domain apply_0 zero_in_M 
       apply simp 
      apply simp 
      apply(rule_tac P="arity(\<phi>) = 0"and Q="arity(\<phi>) \<noteq> 0" in disjE) 
        apply blast 
       apply simp 
      apply (rule_tac P="succ(Arith.pred(arity(\<phi>))) \<le> succ(length(env))" in mp) 
    using succ_pred_eq 
       apply simp 
      apply simp 
     apply simp 
    apply(rule iff_flip) 
    apply (rule_tac Forces_Forall) 
    using P_auto_value piauto 
      apply simp 
     apply(rule_tac A=M in map_type) 
      apply(rule_tac A=M in map_type)
       apply simp 
    using P_namify_value_in_M 
      apply simp 
     apply(rule_tac P="x \<in> P_names"and Q="x \<notin> P_names" in disjE) 
       apply simp 
    using Pn_auto_value_in_M piauto 
      apply simp 
    using Pn_auto_domain apply_0 zero_in_M 
     apply simp 
    by simp     
qed 

lemma P_name_list_is_M_list : 
  fixes l assumes "l \<in> list(P_names)" shows "l \<in> list(M)" using assms
proof (induct)
  case Nil
  then show ?case by auto 
next
  case (Cons a l)
  then show ?case 
    apply simp 
    using P_name_in_M 
    by auto
qed

lemma P_namify_P_name_list : 
  fixes l assumes "l \<in> list(P_names)" shows "map(P_namify, l) = l" using assms
proof (induct)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case 
    apply auto 
    using P_namify_P_name 
    by auto
qed

theorem symmetry_lemma:
  fixes env \<phi> \<pi> p 
  assumes envin : "env \<in> list(P_names)" and "\<phi> \<in> formula" "arity(\<phi>) \<le> length(env)" "p \<in> P" "is_P_auto(\<pi>)" 
  shows "p \<tturnstile> \<phi> env \<longleftrightarrow> \<pi>`p \<tturnstile> \<phi> map(\<lambda>x. Pn_auto(\<pi>)`x, env)" 

  apply (rule_tac Q = "\<pi>`p \<tturnstile> \<phi> map(\<lambda>x. Pn_auto(\<pi>)`x, map(P_namify, env))" in iff_trans)
   apply (rule_tac symmetry_lemma') 
  using P_name_list_is_M_list assms 
       apply simp_all 
  apply (rule_tac b="map(P_namify, env)" and a=env in ssubst) 
  using P_namify_P_name_list 
   apply auto 
  done 
 
    
end
end















