#import "@preview/touying:0.7.1": *
#import themes.stargazer: *

#show: stargazer-theme.with(
  aspect-ratio: "16-9",
  config-common(show-bibliography-as-footnote: bibliography("real.yaml")),
  config-info(
    title: [From Integration to Measure],
    subtitle: [RMK theorem and the Daniell integral],
    author: [Casper Dong],
    date: datetime(day: 14, month: 4, year: 2026),
    institution: [NYU Shanghai],
    contact: [casper.dong\@nyu.edu],
  ),
)

#set heading(numbering: "1.A.I")

#let lsc=$op("LSC")$

#let usc=$op("USC")$

#let rp=$RR_(>=0)$

#title-slide()

#magic.bibliography(title: none)

= Radon measure and its construction

== Useful results on LCH space

Let $(X, cal(T)_X)$ denote a locally compact Hausdorff (LCH) topological space. 

#tblock(title: [Urysohn’s lemma])[
  Let $K subset X$ be compact. Then there exists $f in C_c (X, [0, 1])$ such that $f|_K = 1$. 
]

#tblock(title: [Tietze extension theorem])[
  Let $K subset X$ be compact, $f in C(K, RR)$. Then there exists $tilde(f) in C_c (X, RR)$ such that $tilde(f)|_K = f$, and that $norm(tilde(f))_(l^oo (X, RR)) = norm(f)_(l^oo (K, RR))$.
]

== Radon measure

#tblock(title: [Definition])[
  A _Radon measure_ $mu$ is a Borel measure $cal(B)_X->[0,oo]$ on a LCH space $(X, cal(T)_X)$ satisfying

  1. Outer regularity on Borel sets
  $ mu(E)=inf_(U supset E, U "open") mu(U), forall E in cal(B)_X $

  2. Inner regularity on open sets
  $ mu(U)=sup_(K subset U, K "compact") mu(K), forall U in cal(T)_X $

  3. Finiteness on compact sets
  $ mu(K)<oo, forall K "compact" $
]

#pagebreak()
#tblock(title: [Alternative formulation])[
  Inner regularity: For open $U subset X$,
  $ sup { mu(K) : K subset U, K "is compact" } = sup { integral_X f d mu : f in C_c (U, [0, 1]) } $

  Finiteness on compact sets:
  $ mu(K) < oo, forall "compact" K subset X <=> integral_X f d mu < +oo, forall f in C_c (X, RR_(>= 0)) $
]

== Constructing measure on topology

Let $(X, cal(T)_X)$ denote a Hausdorff topological space. Let $mu : cal(T)_X arrow [0, oo]$. 

#tblock(title: [Definition])[
$
"(outer measure)" & mu^*: 2^X->[0,oo], E mapsto inf_(U supset E, U "open") mu(U)
$
$
"(inner measure)" & mu_*: 2^X->[0,oo], E mapsto sup_(K subset E, K "compact") mu^*(K)
$
]

#pagebreak()
#tblock(title: [Assumptions])[
  1. $mu(emptyset) = 0$

  2. (Monotonicity) If $U subset V subset X$ and $U, V$ are open, then $mu(U) <= mu(V)$

  3. (Countable subadditivity) For a countable family of open subsets ${U_n}_(n in NN)$ of $X$, 
  $ mu(union_n U_n) <= sum_n mu(U_n) $

  4. (Additivity) For disjoint open subsets $U_1, U_2$ of $X$,
  $ mu(U_1 union U_2) = mu(U_1) + mu(U_2) $

  5. (Regularity on open sets) If $U subset X$ is open, then $mu(U) = mu_* (U)$
]

#pagebreak()
#tblock(title: [Strategy])[
  $mu^*$ satisfies countable subadditivity and $mu_*$ satisfies countable superadditivity.

  $=> mu^*=mu_*$ yields coutable additivity. It suffices to show such sets form a $sigma$-algebra.
]

#tblock(title: [Definition])[
  $E subset X$ is regular if $mu^* (E)=mu_* (E)$.

  $E subset X$ is locally regular if $mu^* (E inter F)=mu_* (E inter F)$ for open $F subset X$, $mu(F)<oo$.
]

#pagebreak()
#tblock(title: [Theorem @gba])[
  Let $cal(M)_mu $ be the set of locally regular subsets of $X$. Then $cal(M)_mu $ is a $sigma$-algebra containing $cal(B)_X$ i.e. the Borel $sigma$-algebra, and $mu^*$ is a complete measure on $cal(M)_mu$. 
]

= Riesz–Markov–Kakutani representation theorem

== Statement

#tblock(title: [Theorem])[
  Let $(X, cal(T)_X)$ denote a LCH space. For positive linear functional $Lambda$ on $C_c (X, RR)$ i.e. 
  $ Lambda(f) >= 0, forall f in C_c (X, rp) $

  There exists a unique Radon measure $mu$ such that
  $ Lambda(f) = integral_X f dif mu, forall f in C_c (X, RR) $
]

== Nets and LSC Functions

A *directed set* is a set $I$ with a preorder $<=$ such that for every $a, b in I$, there exists $c in I$ satisfying $a <= c$ and $b <= c$.

A *net* in a topological space $X$ is a function from a directed set $I$ into $X$, denoted by $(x_alpha)_(alpha in I)$. We say $x_alpha arrow x$ if for every neighborhood $U$ of $x$, there exists $alpha_0 in I$ such that $x_alpha in U$ for all $alpha >= alpha_0$.

#pagebreak()
A function $f: X arrow [-oo, +oo]$ is *lower semi-continuous (LSC)* at $x in X$ if for every net $(x_alpha)_(alpha in I)$ in $X$ such that $x_alpha arrow x$, we have:

$ f(x) <= liminf_alpha f(x_alpha) $

Equivalently, $f$ is LSC on $X$ if ${x in X : f(x) > a}$ are open for $a in RR$. Consequently, the family of LSC functions is closed under taking supremum i.e. $sup_(alpha in I) f_alpha in lsc (X)$.

== Extension to $lsc_+ (X, RR)$

We extend $Lambda$ from $C_c (X, rp)$ to $lsc (X, rp)$.

#tblock(title: [Extension of positive linear functional])[
  1. For each $f in cal(F)$, define $Lambda (f) = sup { Lambda (h) : h in cal(H), h <= f }$

  2. Prove the *monotone convergence theorem*: If $(f_alpha)$ is an increasing net converging pointwise to $f$, then $f in cal(L)$ and $Lambda (f) = lim_alpha Lambda (f_alpha)$

  3. Prove that every $f in cal(F)$ is the pointwise limit of an increasing net in $cal(H)$

  Conclude with the linearity of the extended $Lambda$.
]

Details on the blackboard.

== Proof of RMK

Define $ mu: cal(T) -> [0,oo], U |-> sup_(f in C_c (U, [0,1])) Lambda(f) $

Check the *assumptions* on $mu$.

Show that $ Lambda(f) = integral_X f dif mu, forall f in lsc (X, rp) $

Details on the blackboard.

= Daniell integral

The Daniell integral is constructed directly from $C_c (X)^*$, without mention of the underlying measure. The approach heavily utilizes the extension of positive linear functionals. 

#pagebreak()
Let $Lambda$ denote a positive linear functional on $C_c (X, RR)$. Let $f: X->rp$ be any positive function.

#tblock(title: [Upper integral])[
  $ overline(integral) f := inf_(g>=f, g in lsc(X, rp)) overline(Lambda) (f) $

  where $overline(Lambda)$ denotes the aforementioned extension onto $lsc(X, rp)$.
]

#pagebreak()
Similarly, one can extend $Lambda$ to $usc_c (X, rp)$, the class of positive upper semi-continuous functions with compact support, and check linearity. Let $f: X->rp$ be any positive function.

#tblock(title: [Lower integral])[
  $ underline(integral) f := sup_(g<=f, g in usc_c (X, rp)) underline(Lambda) (f) $

  where $underline(Lambda)$ denotes the extension onto $usc_c (X, rp)$, where

  $ underline(Lambda) (g) = inf_(h>=g, h in C_c (X, rp)) Lambda (h), forall g in usc_c (X, rp) $
]

#pagebreak()
Finally, $f$ is Daniell integrable if $overline(integral) f=underline(integral) f$. Thus, one can define integrability for real or complex valued functions.

#tblock(title: [Theorem @ped])[
  Let $(X, cal(T)_X)$ denote a LCH space. Given a positive linear functional $Lambda$ on $C_c (X, RR)$, the class of integrable functions $L^1 (X, RR)$ is a vector space containing $C_c (X, RR)$, which is closed under lattice operations $and$ and $or$. Moreover, $integral: L^1 (X, RR)->RR$ is a positive functional that extends $Lambda$ on $C_c (X, RR)$.
]

#focus-slide[
  "On appelle mesure sur X un élément du dual de l'espace de Banach $C_c (X) dots$"

  --- _Éléments de mathématique_, Nicolas Bourbaki
]

