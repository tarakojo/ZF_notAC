theory SymExt_Definition
  imports 
    "Forcing/Forcing_Main" 
    HS
begin 

context M_symmetric_system 
begin 

definition SymExt where "SymExt(G) \<equiv> { val(G, x). x \<in> HS }" 

lemma M_subset_SymExt : "M_generic(G) \<Longrightarrow> M \<subseteq> SymExt(G)" 
proof (rule subsetI)
  fix x assume assms : "M_generic(G)" "x \<in> M" 
  then have "check(x) \<in> HS" using check_in_HS by auto 
  then have "val(G, check(x)) \<in> SymExt(G)" unfolding SymExt_def by auto 
  then show "x \<in> SymExt(G)" using valcheck one_in_G assms one_in_P by auto 
qed

lemma SymExt_subset_GenExt : "SymExt(G) \<subseteq> GenExt(G)" 
  apply(rule subsetI)
  unfolding SymExt_def GenExt_def 
  using HS_iff P_names_in_M 
  by auto

lemma Transset_SymExt : " Transset(SymExt(G))" 
  unfolding Transset_def 
proof (rule ballI; rule subsetI)
  fix x y assume assms : "x \<in> SymExt(G)" "y \<in> x" 
  then obtain x' where x'H : "x = val(G, x')" "x' \<in> HS" unfolding SymExt_def by auto
  then have "\<exists>y' \<in> domain(x') . y = val(G, y')" using assms elem_of_val by blast 
  then obtain y' where y'H : "y' \<in> domain(x')" "y = val(G, y')" using elem_of_val assms by auto
  then have y'inHS : "y' \<in> HS" using HS_iff x'H by auto 
  then show "y \<in> SymExt(G)" unfolding SymExt_def y'H by auto
qed

end
end 