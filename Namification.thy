theory Namification
  imports 
    P_Names
    Automorphism_Theorems
begin 

context forcing_data
begin 


definition HP_namify where "HP_namify(x, H) \<equiv> { v \<in> M. \<exists>y p. <y, p> \<in> x \<and> p \<in> P \<and> v = <H`y, p> }" 

definition P_namify where "P_namify(x) \<equiv> wftrec(Memrel(M)^+, x, HP_namify)"

lemma P_namify : "\<And>x. x \<in> M \<Longrightarrow> P_namify(x) = { v \<in> M. \<exists>y p. <y,p> \<in> x \<and> p \<in> P \<and> v = <P_namify(y), p> }" 
proof - 
  fix x assume xinM : "x \<in> M" 
  have "P_namify(x) = wftrec(Memrel(M)^+, x, HP_namify)" 
    unfolding P_namify_def 
    by simp 
  also have "... = HP_namify(x, \<lambda>v \<in> Memrel(M)^+ -`` {x}. wftrec(Memrel(M)^+, v, HP_namify))" 
    apply(rule wftrec)
     apply(rule wf_trancl, rule wf_Memrel)
    apply(rule trans_trancl)
    done
  also have "... = { v \<in> M. \<exists>y p. <y,p> \<in> x \<and> p \<in> P \<and> v = <(\<lambda>v \<in> Memrel(M)^+ -`` {x}. wftrec(Memrel(M)^+, v, HP_namify))`y, p> }"
    by (simp add: HP_namify_def)
  also have "... = { v \<in> M. \<exists>y p. <y,p> \<in> x \<and> p \<in> P \<and> v = <wftrec(Memrel(M)^+, y, HP_namify), p> }"
  proof - 
    have "\<And>y p. <y, p> \<in> x \<Longrightarrow> (\<lambda>v \<in> Memrel(M)^+ -`` {x}. wftrec(Memrel(M)^+, v, HP_namify))`y = wftrec(Memrel(M)^+, y, HP_namify)"
      apply(rename_tac y p; subgoal_tac "y\<in>Memrel(M)^+ -`` {x}", simp) 
      apply(rule_tac b=x in vimageI) 
       apply(rule domain_elem_Memrel_trancl)
      using xinM 
      by auto
    then show ?thesis by auto
  qed
  also have "... = { v \<in> M. \<exists>y p. <y,p> \<in> x \<and> p \<in> P \<and> v = <P_namify(y), p> }"
    unfolding P_namify_def by simp 
  finally show "P_namify(x) = { v \<in> M. \<exists>y p. <y,p> \<in> x \<and> p \<in> P \<and> v = <P_namify(y), p> }" by simp 
qed

definition HP_namify_M_cond where 
  "HP_namify_M_cond(v, x', H) \<equiv> \<exists>y \<in> M. \<exists>p \<in> M. \<exists>x \<in> M. \<exists>P \<in> M. \<exists>x_P \<in> M. \<exists>y_p \<in> M. \<exists>y_P \<in> M. \<exists>Hy_P \<in> M.  
    pair(##M, x, P, x') \<and> pair(##M, y, p, y_p) \<and> y_p \<in> x \<and> pair(##M, y, P, y_P) \<and> p \<in> P \<and> fun_apply(##M, H, y_P, Hy_P) \<and> pair(##M, Hy_P, p, v)" 

definition HP_namify_M where "HP_namify_M(x', H) \<equiv> { v \<in> M. HP_namify_M_cond(v,x',H) }" 

lemma HP_namify_M_cond_iff : 
  "\<And>v x' H. v \<in> M \<Longrightarrow> x' \<in> M \<Longrightarrow> H \<in> M \<Longrightarrow> 
     HP_namify_M_cond(v, x', H) \<longleftrightarrow> (\<exists>y p P x. x' = <x, P> \<and> <y, p> \<in> x \<and> p \<in> P \<and> v = <H`<y, P>, p>)"  
  unfolding HP_namify_M_cond_def 
  apply(rule iffI) 
   apply auto[2]
  using pair_in_M_iff 
     apply simp_all 
  apply(rule_tac x=y in bexI) 
   apply simp 
  using pair_in_M_iff transM 
  by auto 

schematic_goal HP_namify_M_cond_fm_auto:
  assumes
    "nth(0,env) = v" 
    "nth(1,env) = x'" 
    "nth(2,env) = H" 
    "env \<in> list(M)"
 shows
    "HP_namify_M_cond(v, x', H)  \<longleftrightarrow> sats(M,?fm(0,1,2),env)"
  unfolding HP_namify_M_cond_def by (insert assms ; (rule sep_rules | simp)+)

definition HP_namify_M_cond_fm where 
  "HP_namify_M_cond_fm \<equiv>Exists
             (Exists
               (Exists
                 (Exists
                   (Exists
                     (Exists
                       (Exists
                         (Exists
                           (And(pair_fm(5, 4, 9),
                                And(pair_fm(7, 6, 2), And(Member(2, 5), And(pair_fm(7, 4, 1), And(Member(6, 4), And(fun_apply_fm(10, 1, 0), pair_fm(0, 6, 8)))))))))))))))  " 

lemma HP_namify_M_in_M : "\<And>x' H. x' \<in> M \<Longrightarrow> H \<in> M \<Longrightarrow> function(H) \<Longrightarrow> HP_namify_M(x', H) \<in> M" 
proof - 
  fix x' H assume assms : "x' \<in> M" "H \<in> M" "function(H)" 
  define V where "V \<equiv> MVset(succ(rank((range(H) \<union> { 0 }) \<times> snd(x'))))" 
  have VinM : "V \<in> M" 
    unfolding V_def 
    apply(rule MVset_in_M) 
     apply(rule to_rin; rule succ_in_MI;rule rank_closed;rule cartprod_closed) 
    using assms range_closed zero_in_M Un_closed singleton_in_M_iff Ord_rank assms pair_in_M_iff 
      apply simp_all
    apply(cases "(\<exists>!b. \<exists>a. x' = \<langle>a, b\<rangle>)",subgoal_tac "\<exists>a. x' = <a, snd(x')>", force)
    unfolding snd_def
     apply(rule theI; simp)
    apply(subst the_0; assumption)
    done

  have "separation(##M, \<lambda>v. sats(M, HP_namify_M_cond_fm, [v]@[x', H]))" 
    apply(rule separation_ax)
    unfolding HP_namify_M_cond_fm_def 
      apply (simp_all add: assms) 
    by (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)   
  then have H : "{ v \<in> V. sats(M, HP_namify_M_cond_fm, [v]@[x', H]) } \<in> M" 
    apply(rule separation_notation) 
    by (simp add:VinM) 
    
  have eq_lemma : "\<And>A P Q. \<forall>x \<in> A. P(x) \<longleftrightarrow> Q(x) \<Longrightarrow> { x \<in> A. P(x) } = { x \<in> A. Q(x) }" by auto  
  have "{ v \<in> V. sats(M, HP_namify_M_cond_fm, [v]@[x', H]) } = { v \<in> V. HP_namify_M_cond(v,x',H) }" 
    apply(rule eq_lemma; simp; rule ballI; rule iff_flip)
    apply(simp add: HP_namify_M_cond_fm_def; rule HP_namify_M_cond_fm_auto) 
    using VinM transM assms by auto 
  also have "... = { v \<in> M. HP_namify_M_cond(v, x', H) }" 
    apply (rule equality_iffI; rule iffI) 
    using VinM transM 
     apply force 
    unfolding V_def 
    apply (simp; rule MVsetI, simp) 
    apply (rename_tac x; subgoal_tac "(\<exists>y p P z. x' = <z, P> \<and> <y, p> \<in> z \<and> p \<in> P \<and> x = <H`<y, P>, p>)") 
     apply clarify 
     apply(rule lt_succ_lt; simp; rule rank_lt; simp) 
     apply(rename_tac y p P z; case_tac "<y, P> \<in> domain(H)") 
      apply (rule disjI1; rule rangeI; rule function_apply_Pair) 
       apply (simp_all add:assms apply_0)
      apply (rule iffD1; simp_all add:HP_namify_M_cond_iff assms) done 
  also have "... = HP_namify_M(x', H)" unfolding HP_namify_M_def by simp 
  finally have "{v \<in> V . M, [v] @ [x', H] \<Turnstile> HP_namify_M_cond_fm} = HP_namify_M(x', H)" by simp 
  then show "HP_namify_M(x', H) \<in> M" using H by simp 
qed

schematic_goal HP_namify_M_fm_auto:
  assumes
    "nth(0,env) = s" 
    "nth(1,env) = H" 
    "nth(2,env) = x'" 
    "env \<in> list(M)"
 shows
    "(\<forall>v \<in> M. (v \<in> s \<longleftrightarrow> HP_namify_M_cond(v, x', H))) \<longleftrightarrow> sats(M,?fm(0,1,2),env)"
  unfolding HP_namify_M_cond_def by (insert assms ; (rule sep_rules | simp)+)

definition HP_namify_M_fm where 
  "HP_namify_M_fm \<equiv> Forall
             (Iff(Member(0, 1),
                  Exists
                   (Exists
                     (Exists
                       (Exists
                         (Exists
                           (Exists
                             (Exists
                               (Exists
                                 (And(pair_fm(5, 4, 11),
                                      And(pair_fm(7, 6, 2),
                                          And(Member(2, 5), And(pair_fm(7, 4, 1), And(Member(6, 4), And(fun_apply_fm(10, 1, 0), pair_fm(0, 6, 8)))))))))))))))))"

lemma HP_namify_M_fm_sats_iff : 
  "\<And>s x' H env. s \<in> M \<Longrightarrow> x' \<in> M \<Longrightarrow> H \<in> M \<Longrightarrow> env \<in> list(M) \<Longrightarrow> 
    s = HP_namify_M(x', H) \<longleftrightarrow> sats(M, HP_namify_M_fm, [s, H, x'] @ env)" 
  apply(rename_tac s x' H env; rule_tac Q="\<forall>v \<in> M . v \<in> s \<longleftrightarrow> HP_namify_M_cond(v, x', H)" in iff_trans) 
  unfolding HP_namify_M_def 
   apply(rule iffI, simp, rule equality_iffI, rule iffI) 
    apply simp 
    apply(rename_tac x; subgoal_tac "x \<in> M", blast)
  using transM 
    apply (simp, simp)
  unfolding HP_namify_M_fm_def 
  apply(rule HP_namify_M_fm_auto; auto) 
  done

lemma P_namify_value_in_M : "x \<in> M \<Longrightarrow> P_namify(x) \<in> M" 
  unfolding P_namify_def 
  apply(rule_tac a = P and Gfm = HP_namify_M_fm in memrel_wftrec_in_M) 
        apply(simp add:P_in_M, simp)
      apply(simp add:HP_namify_M_fm_def)
     apply(simp add:HP_namify_M_fm_def)
     apply (simp del:FOL_sats_iff pair_abs add: fm_defs nat_simp_union)
      apply(rename_tac y g, rule_tac x'=y and H=g in HP_namify_M_in_M)
      apply auto[3]
   apply (simp add: HP_namify_M_def)
   apply(rename_tac h g y, rule_tac b="{v \<in> M . HP_namify_M_cond(v, \<langle>y, P\<rangle>, g)}" and a="{v \<in> M. \<exists>yy p PP xx. <y, P> = <xx, PP> \<and> <yy, p> \<in> xx \<and> p \<in> PP \<and> v = <g`<yy, PP>, p>}" in ssubst)
    apply(rule iff_eq, rule HP_namify_M_cond_iff)
  using P_in_M pair_in_M_iff
      apply auto[3]
  unfolding HP_namify_def
   apply(rule iff_eq)
   apply(rule iffI, clarify)
    apply(rename_tac h g y v z p, simp, rule_tac x=z in exI, simp)
    apply(rename_tac h g y z p, subgoal_tac "z \<in> eclose(y)", force)
    apply(rule domain_elem_in_eclose, force) 
   apply(rule exE, simp, clarify)
   apply(rename_tac h g y v yy p pp PP xx, rule_tac x=yy in exI, rule_tac x=pp in exI, simp)
   apply(rename_tac h g v yy pp xx, subgoal_tac "yy \<in> eclose(xx)", force)
   apply(rule domain_elem_in_eclose, force)
  apply(rule HP_namify_M_fm_sats_iff)
  by auto

lemma P_namify_value_in_P_names : "x \<in> M \<Longrightarrow> P_namify(x) \<in> P_names" 
  apply(subgoal_tac "\<forall>x. x \<in> M \<longrightarrow> P_namify(x) \<in> P_names", simp) 
  apply(rule allI, rule_tac Q="\<lambda>x. x \<in> M \<longrightarrow> P_namify(x) \<in> P_names" in ed_induction, rule impI) 
proof - 
  fix x assume ih : "(\<And>y. ed(y, x) \<Longrightarrow> y \<in> M \<longrightarrow> P_namify(y) \<in> P_names)" and xinM : "x \<in> M" 

  define D where "D \<equiv> { v \<in> M . \<exists>y p. <y, p> \<in> x \<and> p \<in> P \<and> v = P_namify(y) }" 
  have "D \<subseteq> P_names" 
  proof (rule subsetI)
    fix z assume "z \<in> D" 
    then obtain y p where ypH : "<y, p> \<in> x" "z = P_namify(y)" unfolding D_def by auto 
    then have "y \<in> M \<and> ed(y, x)" using ypH domain_elem_in_M xinM by force
    then show "z \<in> P_names" using ypH ih by auto  
  qed 
  then have "\<exists>a. Limit(a) \<and> (\<forall>x \<in> D. x \<in> P_set(a))" 
    using set_of_P_names_in_P_set by auto 
  then obtain a where aH : "Ord(a)" "D \<subseteq> P_set(a)" using Limit_is_Ord by auto 

  then have "P_namify(x) \<subseteq> P_set(a) \<times> P" 
    apply(subst P_namify, simp add:xinM)
    apply clarify
    apply(rename_tac x y p; subgoal_tac "P_namify(y) \<in> D", blast) 
    unfolding D_def 
    apply auto[1] 
    apply(rename_tac y p, subgoal_tac "y\<in>M", simp add:P_namify_value_in_M )
    using domain_elem_in_M xinM 
    by auto
  then have "P_namify(x) \<in> Pow(P_set(a) \<times> P) \<inter> M" 
    using xinM P_namify_value_in_M 
    by auto 
  then have "P_namify(x) \<in> P_set(succ(a))" using P_set_succ by auto 
  then show "P_namify(x) \<in> P_names" 
    using P_namesI aH by auto
qed
  
lemma P_namify_P_name : "x \<in> P_names \<Longrightarrow> P_namify(x) = x" 
  apply(subgoal_tac "x \<in> P_names \<longrightarrow> P_namify(x) = x", simp, rule ed_induction, rule impI) 
proof - 
  fix x assume xpname : "x \<in> P_names" 
  and ih : "(\<And>y. ed(y, x) \<Longrightarrow> y \<in> P_names \<longrightarrow> P_namify(y) = y)"

  have xinM : "x \<in> M" using P_name_in_M xpname by auto

  have "P_namify(x) = { v \<in> M. \<exists>y p. <y,p> \<in> x \<and> p \<in> P \<and> v = <P_namify(y), p> }" using xinM P_namify by blast 
  also have "... = { v \<in> M. \<exists>y p. <y,p> \<in> x \<and> p \<in> P \<and> v = <y, p> }"
  proof - 
    have "\<And>y p. <y, p> \<in> x \<Longrightarrow> P_namify(y) = y" using ih P_name_domain_P_name xpname unfolding ed_def by auto 
    then show ?thesis by auto 
  qed
  also have "... = x" 
    apply(rule equality_iffI; rule iffI) 
    using xpname P_name_in_M transM 
     apply auto[2]
  proof - 
    fix v assume vin : "v \<in> x" 
    obtain a where "x \<in> Pow(P_set(a) \<times> P)" 
      using P_names_in xpname 
      by blast  
    then obtain y p where "y \<in> P_set(a)" "p \<in> P" "v = <y, p>" 
      using vin 
      by auto 
    then show "\<exists>y p. \<langle>y, p\<rangle> \<in> x \<and> p \<in> P \<and> v = \<langle>y, p\<rangle>" 
      using vin 
      by auto 
  qed
  finally show " P_namify(x) = x" by simp 
qed

lemma val_P_namify : "x \<in> M \<Longrightarrow> M_generic(G) \<Longrightarrow> val(G, x) = val(G, P_namify(x))" 
  apply(subgoal_tac "x \<in> M \<longrightarrow> val(G, x) = val(G, P_namify(x))", simp)
  apply(rule_tac Q="\<lambda>x. x \<in> M \<longrightarrow> val(G, x) = val(G, P_namify(x))" in ed_induction, clarify) 
proof -
  fix x assume mg : "M_generic(G)" and xinM : "x \<in> M"  
  and ih : "(\<And>y. ed(y, x) \<Longrightarrow> y \<in> M \<longrightarrow> val(G, y) = val(G, P_namify(y)))"

  have "val(G, x) = { val(G, y) .. y \<in> domain(x) , \<exists> p \<in> P . <y, p> \<in> x \<and> p \<in> G }" 
    using def_val apply blast done 
  also have "... = { val(G, P_namify(y)) .. y \<in> domain(x) , \<exists> p \<in> P . <y, p> \<in> x \<and> p \<in> G }"  
  proof - 
    have "\<And>y. y \<in> domain(x) \<Longrightarrow> y \<in> M" using xinM domain_closed transM by auto 
    then have "\<And>y. y \<in> domain(x) \<Longrightarrow> val(G, y) =  val(G, P_namify(y))" using ih unfolding ed_def by auto
    then show ?thesis by auto
  qed
  also have "... = { val(G, y') .. y' \<in> domain(P_namify(x)) , \<exists> p \<in> P . <y', p> \<in> P_namify(x) \<and> p \<in> G }"  
  proof (rule equality_iffI)  
    fix v 

    have yinM : "\<And>y p. <y, p> \<in> x \<Longrightarrow> y \<in> M"
     using xinM domain_elem_in_M by auto

    have "v \<in> SepReplace(domain(x), \<lambda>y. val(G, P_namify(y)), \<lambda>y. \<exists>p\<in>P. \<langle>y, p\<rangle> \<in> x \<and> p \<in> G) \<longleftrightarrow> (\<exists>y \<in> domain(x) . v = val(G, P_namify(y)) \<and> (\<exists>p\<in>P. \<langle>y, p\<rangle> \<in> x \<and> p \<in> G))" 
      by(rule SepReplace_iff) 
    also have "... \<longleftrightarrow> (\<exists>y' \<in> domain(P_namify(x)) . v = val(G, y') \<and> (\<exists>p\<in>P. \<langle>y', p\<rangle> \<in> P_namify(x) \<and> p \<in> G))" 
      apply(rule_tac a=" { v \<in> M. \<exists>y p. <y,p> \<in> x \<and> p \<in> P \<and> v = <P_namify(y), p> }" and b="P_namify(x)" in ssubst) 
       apply auto[2]
       apply (simp add:P_namify xinM) 
      apply(rename_tac y ya p; rule_tac x="P_namify(y)" in bexI, clarsimp)
       apply(rename_tac y ya p; rule_tac x=p in bexI, clarsimp) 
      using transM P_in_M yinM pair_in_M_iff P_namify_value_in_M 
        apply auto[3] 
      apply(rename_tac y ya p; rule_tac b=p in  domainI) 
      by auto 
    also have "... \<longleftrightarrow> v \<in> SepReplace(domain(P_namify(x)), \<lambda>y'. val(G, y'), \<lambda>y'.(\<exists>p\<in>P. \<langle>y', p\<rangle> \<in> P_namify(x) \<and> p \<in> G))" 
      apply(rule iff_flip) 
      apply(rule SepReplace_iff) 
      done 
    finally show "v \<in> SepReplace(domain(x), \<lambda>y. val(G, P_namify(y)), \<lambda>y. \<exists>p\<in>P. \<langle>y, p\<rangle> \<in> x \<and> p \<in> G) \<longleftrightarrow> 
          v \<in> SepReplace(domain(P_namify(x)), \<lambda>y'. val(G, y'), \<lambda>y'. \<exists>p\<in>P. \<langle>y', p\<rangle> \<in> P_namify(x) \<and> p \<in> G)" 
      by simp 
  qed
  also have "... = val(G, P_namify(x))" 
    apply(rule eq_flip) 
    apply(rule def_val) 
    done 

  finally show "val(G, x) = val(G, P_namify(x))" by simp 
qed

lemma val_namify_map_eq :
  fixes env G
  assumes envin : "env \<in> list(M)" and mg: "M_generic(G)" 
  shows "map(val(G), env) = map(val(G), map(P_namify, env))" 
  apply(rule_tac b="map(val(G), map(P_namify, env))" and a="map(\<lambda>x. val(G, P_namify(x)), env)" in ssubst)  
  using map_compose envin 
   apply simp 
  using envin
proof(induct)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case apply simp using val_P_namify mg by auto
qed

lemma forces_P_namify : 
  fixes env \<phi> p 
  shows "p \<in> P \<Longrightarrow> env \<in> list(M) \<Longrightarrow> arity(\<phi>) \<le> length(env) \<Longrightarrow>  \<phi> \<in> formula \<Longrightarrow> p \<tturnstile> \<phi> env \<longleftrightarrow> p \<tturnstile> \<phi> (map(P_namify, env))" 
  thm definition_of_forcing
  apply(rule_tac Q="(\<forall>G. M_generic(G) \<and> p \<in> G \<longrightarrow> M[G], map(val(G), env) \<Turnstile> \<phi>)" in iff_trans)
  apply(rule definition_of_forcing; simp; simp; simp)
  apply(rule_tac Q="(\<forall>G. M_generic(G) \<and> p \<in> G \<longrightarrow> M[G], map(val(G), map(P_namify, env)) \<Turnstile> \<phi>)" in iff_trans)
   apply(subgoal_tac "\<forall>G. M_generic(G) \<longrightarrow> map(val(G), env) = map(val(G), map(P_namify, env))")
    apply force 
   apply clarify 
  using val_namify_map_eq 
   apply simp 
  apply(rule iff_flip)
  apply(rule definition_of_forcing) 
     apply simp_all 
  apply(rule_tac A=M in map_type) 
   apply simp 
  using P_namify_value_in_M 
  by auto 

end
end 

