theory ZF_Fragment 
  imports
    "Forcing/Nat_Miscellanea"
    "Forcing/Relative_Univ"
    "Forcing/Synthetic_Definition"
begin 

syntax
  "_sats"  :: "[i, i, i] \<Rightarrow> o"  ("(_, _ \<Turnstile> _)" [36,36,36] 60)
translations
  "(M,env \<Turnstile> \<phi>)" \<rightleftharpoons> "CONST sats(M,\<phi>,env)"

abbreviation
  dec10  :: i   ("10") where "10 \<equiv> succ(9)"

abbreviation
  dec11  :: i   ("11") where "11 \<equiv> succ(10)"

abbreviation
  dec12  :: i   ("12") where "12 \<equiv> succ(11)"

abbreviation
  dec13  :: i   ("13") where "13 \<equiv> succ(12)"

abbreviation
  dec14  :: i   ("14") where "14 \<equiv> succ(13)"

definition
  infinity_ax :: "(i \<Rightarrow> o) \<Rightarrow> o" where
  "infinity_ax(M) \<equiv>
      (\<exists>I[M]. (\<exists>z[M]. empty(M,z) \<and> z\<in>I) \<and> (\<forall>y[M]. y\<in>I \<longrightarrow> (\<exists>sy[M]. successor(M,y,sy) \<and> sy\<in>I)))"

locale M_ZF_Fragment = 
  fixes M \<Phi> enum
  assumes 
    upair_ax:         "upair_ax(##M)"
    and Union_ax:         "Union_ax(##M)"
    and power_ax:         "power_ax(##M)"
    and extensionality:   "extensionality(##M)"
    and foundation_ax:    "foundation_ax(##M)"
    and infinity_ax:      "infinity_ax(##M)"
    and separation_ax:    "\<phi>\<in>formula \<Longrightarrow> \<phi> \<in> \<Phi> \<Longrightarrow> env\<in>list(M) \<Longrightarrow> arity(\<phi>) \<le> 1 #+ length(env) \<Longrightarrow>
                    separation(##M,\<lambda>x. sats(M,\<phi>,[x] @ env))" 
    and replacement_ax:   "\<phi>\<in>formula \<Longrightarrow>  \<phi> \<in> \<Phi> \<Longrightarrow> env\<in>list(M) \<Longrightarrow> arity(\<phi>) \<le> 2 #+ length(env) \<Longrightarrow> 
                    strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,[x,y] @ env))" 
    and trans_M:          "Transset(M)"  
    and M_countable:      "enum \<in> bij(nat, M)" 
  
begin 

lemma separation_consI : 
  "separation(##M,\<lambda>x. sats(M, \<phi>, [x] @ env)) \<Longrightarrow> separation(##M,\<lambda>x. sats(M,\<phi>,Cons(x, env)))" by auto

lemma strong_replacement_consI : 
  "strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,[x,y] @ env)) \<Longrightarrow> strong_replacement(##M,\<lambda>x y. sats(M,\<phi>,Cons(x, Cons(y, env))))" by auto

end
end