theory Test 
  imports ZF_notAC 
begin 

lemma test_lemma : 
  fixes A B 
  assumes "A = { 0 }" "B = { 1 }" 
  shows "A \<union> B \<subseteq> { 0, 1, 2 }" 
proof(rule subsetI) 
  fix x 
  assume x_in_A_union_B : "x \<in> A \<union> B" 
  show "x \<in> { 0, 1, 2 }" 
  proof (cases "x \<in> A")
    case True
    then have "x = 0" using assms by simp
    then show "x \<in> { 0, 1, 2 }" by simp
  next
    case False
    then have "x \<in> B" using x_in_A_union_B by simp
    then show "x \<in> { 0, 1, 2 }" using assms by simp 
  qed
qed

lemma test_lemma2 : 
  fixes A B 
  assumes "A = { 0 }" "B = { 1 }" 
  shows "A \<union> B \<subseteq> { 0, 1, 2 }" 
  using assms 
  by auto
end