
theory Test 
  imports Delta0 

begin 

consts satisfiesCl :: "[i\<Rightarrow>o] \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i"
primrec 
  "satisfiesCl(Cl, env, Member(x, y)) = bool_of_o(nth(x, env) \<in> nth(y, env))"
  "satisfiesCl(Cl, env, Equal(x, y)) = bool_of_o(nth(x, env) = nth(y, env))"
  "satisfiesCl(Cl, env, Nand(\<phi>, \<psi>)) = bool_of_o(\<not>(satisfiesCl(Cl, env, \<phi>) = 1 \<and> satisfiesCl(Cl, env, \<psi>) = 1))"
  "satisfiesCl(Cl, env, Forall(\<phi>)) = bool_of_o(\<forall>x. Cl(x) \<longrightarrow> satisfiesCl(Cl, Cons(x, env), \<phi>) = 1)" 

end 