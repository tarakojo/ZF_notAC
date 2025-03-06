theory ZF_notAC 
  imports NotAC_Proof Wellord_AC
begin


theorem ZF_notAC_main_theorem :
  fixes M 
  assumes "nat \<approx> M" "M \<Turnstile> ZF" "Transset(M)" 
  shows "\<exists>N. nat \<approx> N \<and> N \<Turnstile> ZF \<and> Transset(N) 
          \<and> \<not>(\<forall>A \<in> N. \<exists>r \<in> N. wellordered(##N, A, r))" 
proof - 

  obtain enum where "enum \<in> bij(nat, M)" using assms eqpoll_def by auto
  then interpret M_ctm M enum 
    unfolding M_ctm_def M_ctm_axioms_def
    using M_ZF_iff_M_satT assms 
    by auto
  interpret M_symmetric_system Fn Fn_leq 0 M enum Fn_perms Fn_perms_filter  
    using Fn_M_symmetric_system
    by auto

  obtain G where GH: "M_generic(G)" 
    using generic_filter_existence zero_in_Fn 
    by auto
  then interpret M_symmetric_system_G_generic Fn Fn_leq 0 M enum Fn_perms Fn_perms_filter G
    unfolding M_symmetric_system_G_generic_def
    using M_symmetric_system_axioms G_generic_def forcing_data_axioms G_generic_axioms_def 
    by auto

  define N where "N \<equiv> SymExt(G)" 

  have N_ZF : "N \<Turnstile> ZF" 
    using N_def SymExt_M_ZF M_ZF_iff_M_satT 
    by auto

  have "\<exists>A \<in> N. \<forall>R \<in> N. \<not>wellordered(##N, A, R)"
    apply(rule_tac x="binmap(G)" in bexI)
     apply(rule ballI, rule ccontr)
     apply(rule no_wellorder)
    using GH N_def SymExt_def binmap_eq binmap'_HS
    by auto 
  then show ?thesis using N_ZF N_def Transset_SymExt SymExt_countable
    by auto
qed



 






  thm wf_def
      wf_on_def 
      well_ord_def
      choice_ax_def 
      ordinal_def
      surjection_def
      transitive_set_def
      subset_def
      wellordered_def
      wellfounded_on_def
      M_ZF_trans.ac_implies_wellordering





end 