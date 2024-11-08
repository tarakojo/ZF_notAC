
このセクションでは、c.t.m.アプローチの正当性を説明します。
notACのZF上の相対的無矛盾性とは、ZFが無矛盾ならば、ZF+notACも無矛盾であることを意味します。
ZFが無矛盾であるとき、完全性定理より、ZFのモデルが存在することは証明できます。
しかし、ZFのc.t.m.が存在することは、この仮定からは証明できません。
ZFのc.t.m.が存在するという主張は、ZFのモデルが存在するという主張より、真に強いのです。
しかし、ZFのc.t.m.の存在を仮定したうえで、その上で強制法を用いてZF+notACのモデルを構成することにより、
元の理論上での相対的無矛盾性を証明することができます。

そのことを説明するため、いくつかの命題を紹介します。

...

これらを用いて、次の命題が証明できます。

命題A.
与えられた任意のZFの有限部分Deltaに対して、
ZFが無矛盾ならば、
Deltaのc.t.m.は存在する。


では、これを用いて、c.t.m.アプローチの正当性を説明します。
なお、notACのZF上での相対的無矛盾性に限らず、
任意の文phiの、ZFを含む任意の理論上での相対的無矛盾性についても同様の議論が成り立ちます。


まず、ZFのc.t.m.の存在を仮定すると、ZF+notACのc.t.m.の存在が証明できるとしましょう。
このとき、その証明を修正することで、以下のことも証明できるはずです。

命題B.
任意のZFの有限部分Gammaに対して、ZF+notACの有限部分Deltaが存在して、
Tの有限部分のc.t.m.が存在するならば、Sの有限部分のc.t.m.が存在する。

なぜなら、元の証明の議論中で強制法を定式化するために使うZFの公理は有限個ですし、
ZF+notACのc.t.m.が、ZF+notACの各公理を満たすことの証明には、
それぞれZFの公理を有限個しか使わないはずだからです。

また、以下のことが言えます。


注釈 : これはDeltaに対する定理図式なので、コンパクト性定理からZFのc.t.m.の存在を導くことはありません。

以上のことより、以下のことが言えます。
命題3. 
与えられたZF+notACの有限部分Gammaに対して、
ZFが無矛盾ならば、
Gammaのc.t.m.は存在する。つまり、Gammaは無矛盾である。

さて、では、notACの相対的無矛盾性を背理法によって証明しましょう。
ZFが無矛盾であり、ZF+notACが矛盾すると仮定します。
すると、ZF+notACからbottomが証明できるので、
ZF+notACの有限部分Gammaが存在して、Gammaからbottomが証明できます。
つまり、Gammaは矛盾しているということです。
しかし、命題3より、Gammaは無矛盾であるので、矛盾します。
したがって、ZF+notACは無矛盾です。



skolem theorem (ZF) 
T : consistent theory of a countable language
then T has a countable model

note that not elementary submodel when without assuming AC


reflection principle (ZF)

For given formula phi(x), 
there exists a set M such that phi(x) <--> phi^M(x) for all x in M

i.e. phi(x) <--> "M |= phi(x)" for all x in M



RがA上整礎 :<--> Aの任意の非空部分集合がRの極小元を持つ
pred(a) := {x in A | x R a}
RがA上外延的 :<--> pred(a) = pred(b) -> a = b
RがA上set-like :<--> pred(a) is a set for all a in A

mostowski collapse 
A : set 
R : binary relation on A, A上整礎、A上外延的
then there exists a transitive set M such that
(A, R) ~~ (M, ∈)


