theory NotAC_Inj 
  imports Utilities
begin

context M_ZF_trans begin


schematic_goal well_ord_iso_separation_fm_auto:
  assumes
    "x \<in> M" "A \<in> M" "f \<in> M" "r \<in> M" 
  shows
    "(x\<in>A \<longrightarrow> (\<exists>y \<in> M. (\<exists>p \<in> M. fun_apply(##M,f,x,y) \<and> pair(##M,y,x,p) \<and> p \<in> r)) \<and> order_isomorphism(##M, x, x,x,x,x) ) \<longleftrightarrow> sats(M,?fm,[x, A, f, r])" 
  by (insert assms ; (rule sep_rules | simp)+) 

definition well_ord_iso_separation_fm where "well_ord_iso_separation_fm \<equiv> Implies(Member(0, 1), Exists(Exists(And(fun_apply_fm(4, 2, 1), And(pair_fm(1, 2, 0), Member(0, 5))))))"

lemma well_ord_iso_separation : 
  fixes A f r 
  assumes "A \<in> M" "f \<in> M" "r \<in> M" 
  shows "separation(##M, \<lambda>x. x\<in>A \<longrightarrow> (\<exists>y[##M]. (\<exists>p[##M]. fun_apply(##M,f,x,y) \<and> pair(##M,y,x,p) \<and> p \<in> r)))"

  apply(rule_tac P="separation(##M, \<lambda>x. x\<in>A \<longrightarrow> (\<exists>y \<in> M. (\<exists>p \<in> M. fun_apply(##M,f,x,y) \<and> pair(##M,y,x,p) \<and> p \<in> r)))" in iffD1)
   apply(rule separation_cong)
  using assms
   apply force
  apply(rule_tac P="separation(##M, \<lambda>x. sats(M, well_ord_iso_separation_fm, [x] @ [A, f, r]))" in iffD1)
  apply(rule separation_cong)
  unfolding well_ord_iso_separation_fm_def
   apply(rule iff_flip)
  using well_ord_iso_separation_fm_auto assms
   apply force
  apply(rule separation_ax)
  using assms
  apply auto[2]
  apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  done

schematic_goal obase_separation_fm_auto:
  assumes
    "a \<in> M" "A \<in> M" "r \<in> M" 
  shows
    "(\<exists>x \<in> M. \<exists>g \<in> M. \<exists>mx \<in> M. \<exists>par \<in> M.
             ordinal(##M,x) \<and> membership(##M,x,mx) \<and> pred_set(##M,A,a,r,par) \<and>
             order_isomorphism(##M,par,r,x,mx,g)) \<longleftrightarrow> sats(M,?fm,[a, A, r])" 
  by (insert assms ; (rule sep_rules | simp)+) 

definition obase_separation_fm where "obase_separation_fm \<equiv> Exists
             (Exists
               (Exists
                 (Exists
                   (And(ordinal_fm(3), And(Memrel_fm(3, 1), And(pred_set_fm(5, 4, 6, 0), order_isomorphism_fm(0, 6, 3, 1, 2))))))))"

lemma obase_separation : 
  fixes A r 
  assumes "A \<in> M" "r \<in> M" 
  shows "separation(##M, \<lambda>a. \<exists>x[##M]. \<exists>g[##M]. \<exists>mx[##M]. \<exists>par[##M].
             ordinal(##M,x) \<and> membership(##M,x,mx) \<and> pred_set(##M,A,a,r,par) \<and>
             order_isomorphism(##M,par,r,x,mx,g))"

  apply(rule_tac P="separation(##M, \<lambda>a. (\<exists>x \<in> M. \<exists>g \<in> M. \<exists>mx \<in> M. \<exists>par \<in> M.
             ordinal(##M,x) \<and> membership(##M,x,mx) \<and> pred_set(##M,A,a,r,par) \<and>
             order_isomorphism(##M,par,r,x,mx,g)))" in iffD1)
   apply(rule separation_cong)
  using assms
   apply force
  apply(rule_tac P="separation(##M, \<lambda>a. sats(M, obase_separation_fm, [a] @ [A, r]))" in iffD1)
  apply(rule separation_cong)
  unfolding obase_separation_fm_def
   apply(rule iff_flip)
  using obase_separation_fm_auto assms
   apply force
  apply(rule separation_ax)
  using assms
    apply auto[2]
  unfolding order_isomorphism_fm_def pred_set_fm_def Memrel_fm_def bijection_fm_def
  apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  unfolding injection_fm_def surjection_fm_def
  apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  done


schematic_goal obase_equals_separation_fm_auto:
  assumes
    "x \<in> M" "A \<in> M" "r \<in> M" 
  shows
    "(x\<in>A \<longrightarrow> \<not>(\<exists>y \<in> M. \<exists>g \<in> M.
        ordinal(##M,y) \<and> (\<exists>my \<in> M. \<exists>pxr \<in> M.
        membership(##M,y,my) \<and> pred_set(##M,A,x,r,pxr) \<and>
        order_isomorphism(##M,pxr,r,y,my,g)))) \<longleftrightarrow> sats(M,?fm,[x, A, r])" 
  by (insert assms ; (rule sep_rules | simp)+) 

definition obase_equals_separation_fm where "obase_equals_separation_fm \<equiv> 
          Implies
             (Member(0, 1),
              Neg(Exists
                   (Exists
                     (And(ordinal_fm(1),
                          Exists(Exists(And(Memrel_fm(3, 1), And(pred_set_fm(5, 4, 6, 0), order_isomorphism_fm(0, 6, 3, 1, 2))))))))))"

lemma obase_equals_separation : 
  fixes A r 
  assumes "A \<in> M" "r \<in> M" 
  shows "separation (##M, \<lambda>x. x\<in>A \<longrightarrow> \<not>(\<exists>y[##M]. \<exists>g[##M].
                              ordinal(##M,y) \<and> (\<exists>my[##M]. \<exists>pxr[##M].
                              membership(##M,y,my) \<and> pred_set(##M,A,x,r,pxr) \<and>
                              order_isomorphism(##M,pxr,r,y,my,g))))"

  apply(rule_tac P="separation(##M, \<lambda>x. (x\<in>A \<longrightarrow> \<not>(\<exists>y \<in> M. \<exists>g \<in> M.
        ordinal(##M,y) \<and> (\<exists>my \<in> M. \<exists>pxr \<in> M.
        membership(##M,y,my) \<and> pred_set(##M,A,x,r,pxr) \<and>
        order_isomorphism(##M,pxr,r,y,my,g)))))" in iffD1)
   apply(rule separation_cong)
  using assms
   apply force
  apply(rule_tac P="separation(##M, \<lambda>a. sats(M, obase_equals_separation_fm, [a] @ [A, r]))" in iffD1)
  apply(rule separation_cong)
  unfolding obase_equals_separation_fm_def
   apply(rule iff_flip)
  using obase_equals_separation_fm_auto assms
   apply force
  apply(rule separation_ax)
  using assms
    apply auto[2]
  unfolding order_isomorphism_fm_def pred_set_fm_def Memrel_fm_def bijection_fm_def
  apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  unfolding injection_fm_def surjection_fm_def
  apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  done

schematic_goal omap_replacement_fm_auto:
  assumes
    "a \<in> M" "z \<in> M" "A \<in> M" "r \<in> M" 
  shows
    "(\<exists>x \<in> M. \<exists>g \<in> M. \<exists>mx \<in> M. \<exists>par \<in> M.
             ordinal(##M,x) \<and> pair(##M,a,x,z) \<and> membership(##M,x,mx) \<and>
             pred_set(##M,A,a,r,par) \<and> order_isomorphism(##M,par,r,x,mx,g)) \<longleftrightarrow> sats(M,?fm,[a, z, A, r])" 
  by (insert assms ; (rule sep_rules | simp)+) 

definition omap_replacement_fm where "omap_replacement_fm \<equiv> Exists
             (Exists
               (Exists
                 (Exists
                   (And(ordinal_fm(3),
                        And(pair_fm(4, 3, 5),
                            And(Memrel_fm(3, 1), And(pred_set_fm(6, 4, 7, 0), order_isomorphism_fm(0, 7, 3, 1, 2))))))))) " 

lemma omap_replacement : 
  fixes A r 
  assumes "A \<in> M" "r \<in> M" 
  shows "strong_replacement(##M,
             \<lambda>a z. \<exists>x[##M]. \<exists>g[##M]. \<exists>mx[##M]. \<exists>par[##M].
             ordinal(##M,x) \<and> pair(##M,a,x,z) \<and> membership(##M,x,mx) \<and>
             pred_set(##M,A,a,r,par) \<and> order_isomorphism(##M,par,r,x,mx,g))"

  apply(rule_tac P="strong_replacement(##M, \<lambda>a z. \<exists>x \<in> M. \<exists>g \<in> M. \<exists>mx \<in> M. \<exists>par \<in> M.
             ordinal(##M,x) \<and> pair(##M,a,x,z) \<and> membership(##M,x,mx) \<and>
             pred_set(##M,A,a,r,par) \<and> order_isomorphism(##M,par,r,x,mx,g))" in iffD1)
   apply(rule strong_replacement_cong)
  using assms
   apply force
  apply(rule_tac P="strong_replacement(##M, \<lambda>a z. sats(M, omap_replacement_fm, [a, z] @ [A, r]))" in iffD1)
  apply(rule strong_replacement_cong)
  unfolding omap_replacement_fm_def
   apply(rule iff_flip)
  using omap_replacement_fm_auto assms
   apply force
  apply(rule replacement_ax)
  using assms
    apply auto[2]
  unfolding omap_replacement_fm_def pred_set_fm_def Memrel_fm_def bijection_fm_def
  apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  unfolding order_isomorphism_fm_def bijection_fm_def injection_fm_def surjection_fm_def
  apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
  done

lemma mordertype : "M_ordertype(##M)" 
  unfolding M_ordertype_def
  using mbasic
  apply simp
  unfolding M_ordertype_axioms_def
  using well_ord_iso_separation obase_separation obase_equals_separation omap_replacement
  by auto

lemma wellorder_induces_injection : 
  fixes r A
  assumes "nat \<lesssim> A" "wellordered(##M, A, r)" "r \<in> M" "A \<in> M" 
  shows "\<exists>f \<in> M. f \<in> inj(nat, A)" 
proof - 
  have "\<exists>f[##M]. (\<exists>i[##M]. Ord(i) \<and> f \<in> ord_iso(A, r, i, Memrel(i)))"
    apply(rule M_ordertype.ordertype_exists)
    using mordertype assms
    by auto
  then obtain f i where fiH: "f \<in> M" "i \<in> M" "Ord(i)" "f \<in> ord_iso(A, r, i, Memrel(i))"
    by auto
  then have fbij: "f \<in> bij(A, i)" using ord_iso_def by auto
  then have "A \<approx> i" using eqpoll_def by auto
  then have "A \<lesssim> i" using eqpoll_imp_lepoll by auto
  then have "nat \<lesssim> i" 
    apply(rule_tac Y="A" in lepoll_trans)
    using assms
    by auto
  then have "|nat| \<le> i" 
    apply(rule_tac lepoll_cardinal_le)
    using fiH 
    by auto
  then have "nat \<le> i" 
    using Card_nat Card_def
    by auto
  then have "nat \<subseteq> i" 
    apply(rule_tac subsetI)
    apply(rule ltD)
    apply(rule_tac b=nat in lt_le_lt)
     apply(rule ltI)
    by auto

  have "converse(f) \<in> M" using converse_closed fiH by auto
  have "converse(f) \<in> bij(i, A)" using bij_converse_bij fbij by auto 

  then have "restrict(converse(f), nat) \<in> inj(nat, A)" 
    apply(rule_tac A=i in restrict_inj)
    using fbij bij_is_inj \<open>nat \<subseteq> i\<close>
    by auto
  then show ?thesis 
    apply(rule_tac x="restrict(converse(f), nat)" in bexI, simp)
    apply(subgoal_tac "(##M)(restrict(converse(f), nat))")
    apply(force, rule restrict_closed)
    using \<open>converse(f) \<in> M\<close> nat_in_M
    by auto
qed
      
end 
end
