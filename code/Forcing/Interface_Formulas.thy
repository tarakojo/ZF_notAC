theory Interface_Formulas 
  imports "../ZF_Fragment" 
begin 

  
(* Inter_separation: "M(A) \<Longrightarrow> separation(M, \<lambda>x. \<forall> y[M]. y\<in>A \<Longrightarrow> x\<in>y)" *)
schematic_goal inter_fm_auto:
  assumes
    "nth(i,env) = x" "nth(j,env) = B"
    "i \<in> nat" "j \<in> nat" "env \<in> list(A)"
  shows
    "(\<forall>y\<in>A . y\<in>B \<longrightarrow> x\<in>y) \<longleftrightarrow> sats(A,?ifm(i,j),env)"
  by (insert assms ; (rule sep_rules | simp)+)

definition interface_inter_fm where "interface_inter_fm \<equiv>  \<lambda>i j. Forall(Implies(Member(0, succ(j)), Member(succ(i), 0)))" 

definition interface_diff_fm where "interface_diff_fm \<equiv> \<lambda>a b. Neg(Member(a, b))" 

schematic_goal comp_fm_auto:
  assumes
    "nth(i,env) = xz" "nth(j,env) = S" "nth(h,env) = R"
    "i \<in> nat" "j \<in> nat" "h \<in> nat" "env \<in> list(A)"
  shows
    "(\<exists>x\<in>A. \<exists>y\<in>A. \<exists>z\<in>A. \<exists>xy\<in>A. \<exists>yz\<in>A.
              pair(##A,x,z,xz) & pair(##A,x,y,xy) & pair(##A,y,z,yz) & xy\<in>S & yz\<in>R)
  \<longleftrightarrow> sats(A,?cfm(i,j,h),env)"
  by (insert assms ; (rule sep_rules | simp)+)

definition interface_comp_fm where 
  "interface_comp_fm \<equiv> \<lambda>a b c.
       Exists
        (Exists
          (Exists
            (Exists
              (Exists
                (And(pair_fm(4, 2, succ(succ(succ(succ(succ(a)))))),
                     And(pair_fm(4, 3, 1),
                         And(pair_fm(3, 2, 0),
                             And(Member(1, succ(succ(succ(succ(succ(b)))))), Member(0, succ(succ(succ(succ(succ(c)))))))))))))))"

schematic_goal pred_fm_auto:
  assumes
    "nth(i,env) = y" "nth(j,env) = R" "nth(h,env) = X"
    "i \<in> nat" "j \<in> nat" "h \<in> nat" "env \<in> list(A)"
  shows
    "(\<exists>p\<in>A. p\<in>R & pair(##A,y,X,p)) \<longleftrightarrow> sats(A,?pfm(i,j,h),env)"
  by (insert assms ; (rule sep_rules | simp)+)

definition interface_pred_fm where 
  "interface_pred_fm \<equiv> \<lambda>a b c. Exists(And(Member(0, succ(b)), pair_fm(succ(a), succ(c), 0)))" 
 
schematic_goal mem_fm_auto:
  assumes
    "nth(i,env) = z" "i \<in> nat" "env \<in> list(A)"
  shows
    "(\<exists>x\<in>A. \<exists>y\<in>A. pair(##A,x,y,z) & x \<in> y) \<longleftrightarrow> sats(A,?mfm(i),env)"
  by (insert assms ; (rule sep_rules | simp)+)

definition "interface_mem_fm" where "interface_mem_fm \<equiv> \<lambda>a. Exists(Exists(And(pair_fm(1, 0, succ(succ(a))), Member(1, 0))))" 

schematic_goal recfun_fm_auto:
  assumes
    "nth(i1,env) = x" "nth(i2,env) = r" "nth(i3,env) = f" "nth(i4,env) = g" "nth(i5,env) = a"
    "nth(i6,env) = b" "i1\<in>nat" "i2\<in>nat" "i3\<in>nat" "i4\<in>nat" "i5\<in>nat" "i6\<in>nat" "env \<in> list(A)"
  shows
    "(\<exists>xa\<in>A. \<exists>xb\<in>A. pair(##A,x,a,xa) & xa \<in> r & pair(##A,x,b,xb) & xb \<in> r &
                  (\<exists>fx\<in>A. \<exists>gx\<in>A. fun_apply(##A,f,x,fx) & fun_apply(##A,g,x,gx) & fx \<noteq> gx))
    \<longleftrightarrow> sats(A,?rffm(i1,i2,i3,i4,i5,i6),env)"
  by (insert assms ; (rule sep_rules | simp)+)

synthesize "interface_recfun_fm" from_schematic "recfun_fm_auto"

schematic_goal funsp_fm_auto:
  assumes
    "nth(i,env) = p" "nth(j,env) = z" "nth(h,env) = n"
    "i \<in> nat" "j \<in> nat" "h \<in> nat" "env \<in> list(A)"
  shows
    "(\<exists>f\<in>A. \<exists>b\<in>A. \<exists>nb\<in>A. \<exists>cnbf\<in>A. pair(##A,f,b,p) & pair(##A,n,b,nb) & is_cons(##A,nb,f,cnbf) &
    upair(##A,cnbf,cnbf,z)) \<longleftrightarrow> sats(A,?fsfm(i,j,h),env)"
  by (insert assms ; (rule sep_rules | simp)+)

synthesize "interface_funsp_fm" from_schematic "funsp_fm_auto" 

(* rtran_closure_mem *)
schematic_goal rtran_closure_mem_auto:
  assumes
    "nth(i,env) = p" "nth(j,env) = r"  "nth(k,env) = B"
    "i \<in> nat" "j \<in> nat" "k \<in> nat" "env \<in> list(A)"
  shows
    "rtran_closure_mem(##A,B,r,p) \<longleftrightarrow> sats(A,?rcfm(i,j,k),env)"
  unfolding rtran_closure_mem_def
  by (insert assms ; (rule sep_rules | simp)+)

synthesize "interface_rtran_closure_mem_fm" from_schematic "rtran_closure_mem_auto" 

schematic_goal rtran_closure_fm_auto:
  assumes
    "nth(i,env) = r" "nth(j,env) = rp"
    "i \<in> nat" "j \<in> nat" "env \<in> list(A)"
  shows
    "rtran_closure(##A,r,rp) \<longleftrightarrow> sats(A,?rtc(i,j),env)"
  unfolding rtran_closure_def
  by (insert assms ; (rule sep_rules rtran_closure_mem_auto | simp)+)

synthesize "interface_rtran_closure_fm" from_schematic rtran_closure_fm_auto

schematic_goal trans_closure_fm_auto:
  assumes
    "nth(i,env) = r" "nth(j,env) = rp"
    "i \<in> nat" "j \<in> nat" "env \<in> list(A)"
  shows
    "tran_closure(##A,r,rp) \<longleftrightarrow> sats(A,?tc(i,j),env)"
  unfolding tran_closure_def
  by (insert assms ; (rule sep_rules rtran_closure_fm_auto | simp))+

synthesize "trans_closure_fm" from_schematic trans_closure_fm_auto

definition
  wellfounded_trancl :: "[i=>o,i,i,i] => o" where
  "wellfounded_trancl(M,Z,r,p) \<equiv>
      \<exists>w[M]. \<exists>wx[M]. \<exists>rp[M].
               w \<in> Z & pair(M,w,p,wx) & tran_closure(M,r,rp) & wx \<in> rp"

schematic_goal wellfounded_trancl_fm_auto:
  assumes
    "nth(i,env) = p" "nth(j,env) = r"  "nth(k,env) = B"
    "i \<in> nat" "j \<in> nat" "k \<in> nat" "env \<in> list(A)"
  shows
    "wellfounded_trancl(##A,B,r,p) \<longleftrightarrow> sats(A,?wtf(i,j,k),env)"
  unfolding  wellfounded_trancl_def
  by (insert assms ; (rule sep_rules trans_closure_fm_iff_sats | simp)+)

synthesize "interface_wellfounded_trancl_fm" from_schematic wellfounded_trancl_fm_auto

definition interface_list_repl1_intf_fm where 
  "interface_list_repl1_intf_fm \<equiv> Exists(And(pair_fm(1,0,2),
               is_wfrec_fm(iterates_MH_fm(list_functor_fm(13,1,0),10,2,1,0),3,1,0)))"

definition interface_iterates_repl_intf_fm where 
  "interface_iterates_repl_intf_fm(is_F_fm) \<equiv> Exists(And(pair_fm(1,0,2),
               is_wfrec_fm(iterates_MH_fm(is_F_fm,9,2,1,0),3,1,0)))" 

definition interface_list_repl2_intf_fm where 
  "interface_list_repl2_intf_fm \<equiv> And(Member(0,4),is_iterates_fm(list_functor_fm(13,1,0),3,0,1))" 

definition interface_formula_functor2_fm where 
  "interface_formula_functor2_fm \<equiv> And(Member(0,3),is_iterates_fm(formula_functor_fm(1,0),2,0,1))"

definition interface_iter_eclose2_fm where 
  "interface_iter_eclose2_fm \<equiv> And(Member(0,3),is_iterates_fm(big_union_fm(1,0),2,0,1))" 

definition
  is_powapply_fm :: "[i,i,i] \<Rightarrow> i" where
  "is_powapply_fm(f,y,z) \<equiv>
      Exists(And(fun_apply_fm(succ(f), succ(y), 0),
            Forall(Iff(Member(0, succ(succ(z))),
            Forall(Implies(Member(0, 1), Member(0, 2)))))))"

definition
  PHrank_fm :: "[i,i,i] \<Rightarrow> i" where
  "PHrank_fm(f,y,z) \<equiv> Exists(And(fun_apply_fm(succ(f),succ(y),0)
                                 ,succ_fm(0,succ(z))))"

definition
  is_Hrank_fm :: "[i,i,i] \<Rightarrow> i" where
  "is_Hrank_fm(x,f,hc) \<equiv> Exists(And(big_union_fm(0,succ(hc)),
                                Replace_fm(succ(x),PHrank_fm(succ(succ(succ(f))),0,1),0)))"

definition 
  interface_wfrec_fm where "interface_wfrec_fm \<equiv> Exists(And(pair_fm(1,0,2),is_wfrec_fm(is_Hrank_fm(2,1,0),3,1,0)))" 

definition
  is_HVfrom_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "is_HVfrom_fm(A,x,f,h) \<equiv> Exists(Exists(And(union_fm(A #+ 2,1,h #+ 2),
                            And(big_union_fm(0,1),
                            Replace_fm(x #+ 2,is_powapply_fm(f #+ 4,0,1),0)))))"

locale M_ZF_Fragment_Interface = M_ZF_Fragment + 
    assumes interface_inter_fm : "Forall(Implies(Member(0, succ(1)), Member(succ(0), 0))) \<in> \<Phi>"
    and interface_diff_fm : "Neg(Member(0, 1)) \<in> \<Phi>" 
    and interface_cpfm : "Exists(And(Member(0, succ(1)), Exists(And(Member(0, succ(succ(2))), pair_fm(1, 0, succ(succ(0))))))) \<in> \<Phi>"
    and interface_imfm : "Exists(And(Member(0, succ(1)), Exists(And(Member(0, succ(succ(2))), pair_fm(0, succ(succ(0)), 1))))) \<in> \<Phi>"
    and interface_cfm : "Exists(And(Member(0, succ(1)), Exists(Exists(And(pair_fm(1, 0, 2), pair_fm(0, 1, succ(succ(succ(0))))))))) \<in> \<Phi>"
    and interface_rfm : "Exists(And(Member(0, succ(1)), Exists(pair_fm(1, 0, 2)))) \<in> \<Phi>" 
    and interface_comp_fm : "interface_comp_fm(0,1,2) \<in> \<Phi>" 
    and interface_pred_fm : "interface_pred_fm(0,1,2) \<in> \<Phi>" 
    and interface_mem_fm : "interface_mem_fm(0) \<in> \<Phi>" 
    and interface_recfun_fm : "interface_recfun_fm(0,1,2,3,4,5) \<in> \<Phi>" 
    and interface_funsp_fm : "interface_funsp_fm(0,1,2) \<in> \<Phi>" 
    and interface_rtran_closure_mem_fm : "interface_rtran_closure_mem_fm(0, 1, 2) \<in> \<Phi>" 
    and interface_wellfounded_trancl_fm : "interface_wellfounded_trancl_fm(0,1,2) \<in> \<Phi>" 
    and interface_list_repl1_intf_fm : "interface_list_repl1_intf_fm \<in> \<Phi>"
    and interface_list_repl2_intf_fm : "interface_list_repl2_intf_fm \<in> \<Phi>"
    and interface_iter_formula_functor_fm : "interface_iterates_repl_intf_fm(formula_functor_fm(1, 0)) \<in> \<Phi>"
    and interface_iter_formula_functor2_fm : "interface_formula_functor2_fm \<in> \<Phi>"
    and interface_iter_nth_fm : "interface_iterates_repl_intf_fm(tl_fm(1,0)) \<in> \<Phi>"
    and interface_iter_eclose_fm : "interface_iterates_repl_intf_fm(big_union_fm(1,0)) \<in> \<Phi>" 
    and interface_iter_eclose2_fm : "interface_iter_eclose2_fm \<in> \<Phi>" 
    and interface_powapply_fm : "is_powapply_fm(2,0,1) \<in> \<Phi>" 
    and interface_PHrank_fm : "PHrank_fm(2,0,1) \<in> \<Phi>" 
    and interface_wfrec_fm : "interface_wfrec_fm \<in> \<Phi>" 
    and interface_HVfrom_fm : "Exists(And(pair_fm(1,0,2),is_wfrec_fm(is_HVfrom_fm(8,2,1,0),4,1,0))) \<in> \<Phi>"


    and finite_ordinal_fm : "finite_ordinal_fm(0) \<in> \<Phi>" 
end
