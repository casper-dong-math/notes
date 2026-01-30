#import "lib.typ":*
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#show heading.where(level: 1): title => { pagebreak(weak: true); title }

= Towards Lebesgue measure

We work towards _Lebesgue measure_, motivating the discussion on measure and integration theory. This section largely follows the first five sections in _Chapter 1: Measure theory_ of @tmt.
#state(type: "def", title: "Jordan measure")[
  For $E subset RR^d$, define its _Jordan inner measure_ $ m_(*,(J)) (E):=sup_(A subset E, A "elementary") m(A) $

  and _Jordan outer measure_ $ m^(*,(J)) (E):=inf_(B supset E, B "elementary") m(B) $

  When $m_(*,(J)) (E)=m^(*,(J)) (E)=:m(E)$, $E$ is _Jordan measurable_, and $m(E)$ denotes the _Jordan measure_ of $E$.
]
#remark[
  Jordan measurable sets form a boolean algebra, and the measure is finitely additive.
]
#alert[
  Unbounded sets are by definition not Jordan measurable.
]
#state(type: "prop", title: "equivalent formulation of Jordan measurability")[
  $E subset RR^d$ is Jordan measurable $<=> partial E$ is a Jordan null set.
]
#state(type: "prop", title: "connection with Riemann integral")[
  $f: RR^d -> RR$ with bounded support $D in RR^d$ is Riemann integrable if and only if
  $ E_+:={(x,t):x in D and t in [0,f(x)]} quad E_-:={(x,t):x in D and t in [-f(x),0]} $
  are Jordan measurable in $RR^(d+1)$. In this case, $integral f(x) dif x = m(E_+)-m(E_-)$.
]
#state(type: "def", title: "Lebesgue outer measure")[
  For $E subset RR^d$, define its _Lebesgue outer measure_ $ m^*(E):=inf_(union_(n in NN) B_n supset E, B_n "boxes") sum_(n in NN) abs(B_n) $
]
#remark[
  1. For bounded $E in RR^d$, $m^(*,(J)) (E)<=m^*(E)$. The inequality is strict when e.g. $E=QQ inter [0,1]$
  2. The Lebesgue outer measure is countably subadditive. (use the $epsilon\/2^n$ trick)
]
#state(type: "def", title: "Littlewood's first principle")[
  $E subset RR^d$ is _Lebesgue measurable_, if for $epsilon>0$, there exists open set $O subset RR^d$ such that $O supset E$ and $m^*(O-E)<epsilon$. Define $m(E):=m^*(E)$ as its _Lebesgue measure_.
]
#remark[
  Open set $O subset RR^d$ is the countable union of _almost disjoint_ boxes. (use dyadic mesh).\ As a precursor, the Lebesgue outer measure is outer regular c.f. Radon measure.
]
#state(title: "measurable sets")[
  Lebesgue measurable sets in $RR^d$ form a $sigma$-algebra containing the topology of $RR^d$.
]
#sketch[
  1. Use the $epsilon \/ 2^n$ trick to establish closure under countable union.
  2. Use outer regularity and Littlewood's first principle (by definition) to establish measurability of compact sets, and thus for closed sets.
  3. Deduce that Lebesgue measurable sets are closed under complement.
]
#state(type: "cor", title: "inner regularity")[
  The Lebesgue measure is inner regular i.e. for Lebesgue measurable $E$,
  $ m(E)=sup_(B subset E, B "compact")m(B) $
]
#sketch[
  1. Approximate closed sets from below with compact sets.
  2. Take complement and invoke outer regularity.
]
#state(type: "prop", title: "countable additivity")[
  The Lebesgue measure is countably additive i.e. for disjoint Lebesgue measurable $E_n, n in NN$,
  $ sum_(n in NN) m(E_n)=m(union_(n in NN) E_n) $
]
#sketch[
  Outer regularity $=>$ countable subadditivity, Inner regularity $=>$ countable superadditivity\ (c.f. Radon measure @gba)
]
#state(type: "prop", title: "monotone convergence theorem for sets")[
  1. If $E_n arrow.t E$, then $lim_(n->oo) m(E_n)=m(E)$.
  2. If $E_n arrow.b E$ and $exists n in NN: m(E_n)<oo$, then $lim_(n->oo) m(E_n)=m(E)$.
]
#alert[
  In case 2, when $m(E_n)=oo, n in NN$ e.g. $E_n:=(n BB)^C$, the equality may be violated.
]
#state(type: "prop", title: "approximation of measurable sets")[
  The following are equivalent:
  1. $E$ is Lebesgue measurable
  2. $E=G-N$ where $G$ is a $G_delta$ set, where $N subset G$ is a null set
  3. $E=F union N$ where $F$ is a $F_sigma$ set, where $N$ is a null set
  4. For $epsilon>0, exists "open" A$ where $E subset A$ s.t. $m^*(A-E)<=epsilon$
  5. For $epsilon>0, exists "closed" B$ where $B subset E$ s.t. $m^*(U-E)<=epsilon$
  6. For $epsilon>0, exists "elementary" C$ s.t. $m^*(E Delta C)<=epsilon$
]
#state(type: "def", title: "simple function")[
  Complex-valued simple functions form a a complex vector space
  $ "Simp"(RR^d)="Vect"_CC {1_E: E "measurable"} $
  For $f=sum_(n=0)^N c_n 1_E_n in "Simp"(RR^d)$, define its simple integral
  $ integral_(RR^d) f=sum_(n=0)^N c_n m(E_n) $
]
#remark[
  It's trivial to show that integration of simple functions is well-defined.
]
#state(type: "def", title: "measurable function")[
  A function between measure spaces $f: (X, cal(M)_X) -> (Y, cal(M)_Y)$ is measurable (morphism) if
  $ f^(-1)(E_Y) in cal(M)_X, quad forall E_Y in cal(M)_Y $
]
#remark[
  When the codomain is $RR$ equipped with the Borel $sigma$-algebra $cal(B)(RR)$, it suffices to check that $f^(-1)(a,b)$ is measurable in $X$ for $a < b in RR$, thanks to the fact that ${(a,b):a < b in RR}$ contains a countable basis of the real topology. This simplification can be generalized to second countable topolgies equipped with the Borel $sigma$-algebra, including Euclidean spaces.
]
#state(type: "prop", title: "closure under pointwise limit")[
  The space of measurable function is closed under pointwise a.e. limit, as well as limsup, liminf, supremum/infimum envelope.
]
#state(type: "def", title: "unsigned Lebesgue integral")[
  Let $f:(RR^d,cal(L)) -> ([0,oo],cal(B))$ be a measurable function. Define its unsigned Lebesgue integral
  $ integral_(RR^d) f:=sup_(0<=g<=f, g "simple") integral_(RR^d) g $
]
#remark[
  Although the definition should apply to arbitrary function, we restrict the definition to measurable function.
]
#state(type: "prop", title: "approximation by truncation")[
  For unsigned measurable function $f$,
  $
  integral_(RR^d) f and n arrow.t integral_(RR^d) f "as" n->oo "(horizontal)"\
  integral_(norm(x)<n) f arrow.t integral_(RR^d) f "as" n->oo "(vertical)"
  $
]
#sketch[
  Horizontal truncation follows from definition directly.
  Vertical truncation follows from the fact that $m(x in E: norm(x)<n) arrow.t m(E)$ as $n->oo$.
]
#state(type: "def", title: "absolute integrability")[
  $f: RR^d->CC$ is _absolutely integrable_ if
  $ norm(f)_(L^1 (RR^d)):=integral_(RR^d) abs(f) $
  is finite. In this case, if $f$ is real-valued, define
  $ integral_(RR^d) f:=integral_(RR^d) f or 0 - integral_(RR^d) (-f) or 0 $
  Generally, if $f$ is complex-valued, define
  $ integral_(RR^d) f:=integral_(RR^d) frak(R)(f) + i integral_(RR^d) frak(I)(f) $
]
#remark[
  $L^1 (RR^d)$ is the space of absolutely integrable functions quotient the a.e. equivalence relation. Thus $L^1 (RR^d)$ becomes a normed vector space. In fact, the $L^1$ Riesz-Fischer theorem guarentees completeness, upgrading it to a Banach space.
]
#intuit[
  The construction of the Lebesgue integral from Lebesgue measure can be summarized in the following: Given $integral$, a _positive linear functional_ on the space of simple functions Simp,
  1. Define $integral f=sup_(g in "Simp", g <= f) integral g$ for nonnegative measurable functions.
  2. Prove the _monotone convergence theorem_: if $f_n arrow.t f$ pointwise, then $integral f_n arrow.t integral f$.
  3. Show that every nonnegative measurable function is the pointwise limit of an increasing sequence of simple functions.
  4. Conclude that the extended $integral$ is $RR_(>=0)$ linear.
  5. Extend the positive linear functional to linear functional on real/complex measurable functions.
  This approach is more applicable than the traditional upper/lower integral approach, as it can integrate unbounded functions with support of infinite measure.
]
#state(type: "prop", title: "approximation of absolutely integrable functions")[
  The space of 1. simple functions 2. step functions 3. continuous functions with compact support are dense in $L^1$.
]
#sketch[
  1. Approximation by simple functions follows from the definition of unsigned Lebesgue integral.
  2. Approximation by step functions follows from the approximation of a Lebesgue measurable set by an elementary set.
  3. Approximation by continuous functions with compact support follows from the Urysohn lemma.
]
#state(title: "Egorov")[
  Let $f_n: RR^d->CC, n in NN$ be a sequence of measurable functions converging pointwise a.e. to $f$. Then for $epsilon>0$, there exists $A subset RR^d: m(A)<=epsilon$ such that $f_n$ converges locally uniformly to $f$ on $A^C$.
]
#sketch[
  First work with the case of finite measure. Define $ E_(N,delta):={x in RR^d: exists n>=N, abs(f_n (x)-f(x))>epsilon} $Observe that for fixed $delta>0$, $E_(N, delta) arrow.b emptyset$. By lower continuity of measure, there exists $N(delta) in NN: m(E_(N(delta)), delta)<epsilon$. With the $epsilon \/ 2^n$ argument, $A:=union_(m=1)^oo E_(N(1\/m),1\/m)$ has arbitrarily small measure. Check that $f_n$ converges uniformly to $f$.

  In general, for $r in NN$, there exists $A_r$ with arbitrarily small measure such that $f_n|r BB$ converges locally uniformly to $f|r BB$ outside of $r BB$. Conclude by $A:=union_(r in NN) A_r$.
]
#remark[
  When the measure space is finite, local uniform convergence can be upgraded to uniform convergence as claimed in the sketch.

  In general, Egorov's theorem states that for any $A subset X$ with finite measure, there exists $E subset A$ of arbitrarily small measure such that the convergence is uniform on $A-E$.
]
#state(title: "Lusin")[
  Let $f in L^1 (RR^d)$. For $epsilon>0$, there exists $A subset RR^d: m(A)<=epsilon$ such that $f | A^C$ is continuous.
]
#sketch[
  We exploit the density of continuous functions with compact support in $L^1$. Let such $g$ be sufficiently closed to $f$ in $L^1$ norm. With _Markov inequality_, $f$ and $g$ are pointwise adjacent outside of an arbitrarily small set. We conclude with uniform continuity of $g$.
]
#remark[
  In fact, the $L^1$ requirement can be relaxed to local absolute integrability, and further relaxed to measurability (but finite a.e.).
]
#sketch[
  Partition $RR^d$ into countable finite measure sets $E_n, n in NN$. By inner regularity, apply the original Lusin theorem to $C_n subset E_n$, where compact $C_n$ take up $E_n$ sufficiently. Conclude with $A:=(union_(n in NN) E_n - C_n) union (A_n)$. Extension to measurable, finite a.e. case proceeds similarly. Note that for each $E_n$, ${x in E_n: abs(f(x)) > N}$ is arbitrarily small by a.e. finiteness.
]
#remark[
  The general Lusin's theorem works for _Radon measure_. Let $(X, cal(X), mu)$ be a Radon measure space. For $A subset X$ with finite measure, there exists compact $C subset A$ with $mu(A-C)<epsilon$ such that $f|C$ is continuous. One can deduce the Lesbesgue version by partitioning $RR^n$ in the annular rings with sufficiently small gaps.
]
#state(type: "cor", title: "Lusin")[
  Let real-valued, measurable $f$ be finite a.e. For $epsilon>0$, there exists continuous $g:RR^d -> RR$ s.t. $m(f!=g)<epsilon$.
]
#sketch[
  First work with the case of finite measure. $f|A^C$ is continuous for $m(A)<epsilon$. By outer regularity of measure, there exists closed $B subset A^C: m(A^C-B)<epsilon$. Since $f|C$ is continuous, by _Tietze extension theorem_, there exists continuous extension $tilde(g)$. Observe that $f$ and $tilde(g)$ agrees outside of $B^C$ with measure $<2epsilon$. 
]
The following convergence theorems are of vital importance in the theory of integration. 
#state(title: "monotone convergence")[
  Let $(f_n)_(n in NN)$ denote an increasing sequence of measurable functions from $(X,cal(M),mu)$ to $[0,oo]$. Then $sup_(n in NN) f_n$ is measurable, and
  $ sup_(n in NN) integral f_n = integral sup_(n in NN) f_n $
]
#sketch[
  Trivially $<=$. To establish $>=$, it suffice to show $forall g<=sup_(n in NN) f_n, forall epsilon>0, exists n in NN: integral f_n >= (1-epsilon) g$. The rest follows from lower continuity of measure.
]
#state(title: "Fatou's lemma")[
  Let $(f_n)_(n in NN)$ denote a sequence of measurable functions from $(X,cal(M),mu)$ to $[0,oo]$. Then 
  $ integral liminf f_n <= liminf integral f_n $
]
#sketch[
  Rewrite the statement with $liminf=sup inf$, and invoke the monotone convergence theorem.
]
#state(title: "dominated convergence")[
  Let $(f_n)_(n in NN)$ denote a sequence of integrable functions on $(X,cal(M),mu)$ converging pointwise to $f$. If moreover, $abs(f_n)_(n in NN)$ is bounded a.e. by integrable $g: X->[0,oo]$, then
  $ lim integral f_n=integral f $
]
#sketch[
  If $(f_n)_(n in NN)$ is real-valued, then apply Fatou's lemma to $-f_n+g$ and $f_n+g$ and conclude. In general when $(f_n)_(n in NN)$ are complex-valued, apply the real-valued case to the real/imaginary part.
]
#remark[
  The above convergence results apply to *general* measure space.
]
We draw the big picture for the relation between modes of convergence. Check out 1.5 _Modes of convergence_ @tmt for a detailed treatment of the topic.
#state(title: "relation between modes of convergence")[
  In general, 
#align(center, diagram({
	node((-1, 0), [$L^oo$])
	node((0, 0), [$"a. unf."$])
	node((-1, 1), [$L^1$])
	node((0, 1), [$"measure"$])
	node((1, 0), [$"(ptw.) a.e."$])
	edge((-1, 0), (0, 0), "=>")
	edge((-1, 1), (0, 1), "=>")
	edge((0, 0), (0, 1), "=>")
	edge((0, 0), (1, 0), "=>")
}))

  When the measure space is finite e.g. probability measure,
#align(center, diagram({
	node((0, 0), [$L^oo$])
	node((0, 1), [$L^1$])
	node((1, 1), [$"probability"$])
	node((1, 0), [$"a. unf."$])
	node((2, 0), [$"(ptw.) a.s."$])
	edge((0, 0), (0, 1), "=>")
	edge((0, 1), (1, 1), "=>")
	edge((0, 0), (1, 0), "=>")
	edge((1, 0), (1, 1), "=>")
	edge((1, 0), (2, 0), "<=>")
}))
]
#remark[
  There is two additional derivation in the case of finite measure. Trivially $L^oo => L^1$; $"ptw. a.s."=>"a. unf."$ is a special case of Egorov's theorem. The reader is encouraged to find examples that demonstrates non-equivalence.
]
#state(title: [fast $L^1$ convergence])[
  Let $f_n, f:X->CC$ be measurable such that $sum_(n=0)^oo norm(f_n -f)_(L^1)<oo$. Then $f_n$ converges almost uniformly to $f$. Therefore for $f_n$ converging to $f$ in $L^1$, there exists a subsequence converging almost uniformly to $f$.
]
#state(type: "def", title: "uniform integrability")[
  A sequence $f_n: X-> CC$ in $L^1$ is _uniformly integrable_ if
  + (uniformly bounded in $L^1$) $norm(f_n)_(L^1)<M, forall n in NN$
  + (no escape to vertical infinity) $sup_(n in NN) integral_(abs(f_n)>M) abs(f_n) dif mu->0$ as $M->oo$.
  + (no escape to width infinity) $sup_(n in NN) integral_(abs(f_n)<m) abs(f_n) dif mu->0$ as $m->0$.
]
#remark[
  If $X$ is a finite measure space, $3$ is automatically satisfied, and $2$ implies $1$.

  In fact, a uniform $L^p$ bound ($1<p<=oo$) implies $2$, thereby uniform integrability.
]
#state(title: "uniformly integrable convergence in measure")[
  Let $f_n: X->CC$ be uniformly integrable, and $f: X->CC$ measurable. Then $f_n -> f$ in $L^1$ if and only if $f_n->f$ in measure.
]
For the proof, please refer to Theorem 1.5.13 @tmt. The result is of significance in probability theory.

= Radon measure: generalizing Lebesgue measure

The previous section on Lebesgue measure turns out to be a special case of a _Radon measure_ on the Euclidean space, which we will introduce in this section. We present selected results from Chapter 23 to 25 of @gba.

#state(type: "def", title: "Radon measure")[
  A _Radon measure_ $mu$ is a Borel measure $cal(B)_X->[0,oo]$ on a Hausdorff topology $X$ satisfying
  1. Outer regularity on Borel sets i.e. $mu(E)=inf_(U supset E, U "open") mu(U), forall E in cal(B)_X$
  2. Inner regularity on open sets i.e. $mu(U)=sup_(K subset U, K "compact") mu(K), forall U in cal(T)_X$
  3. Finiteness on compact sets i.e. $mu(K)<oo, forall K "compact"$
]

== Constructing measure from premeasure on topology

#state(type: "def", title: "premeasure")[
  A premeasure is a function $mu_0: cal(R)->[0,oo]$ where $cal(R)$ is a ring of subsets. In addition, a premeasure is finitely additive, countably subadditive, and maps $emptyset$ to $0$.
]
#remark[
  A premeasure is automatically countablely additive when $union_(n in NN) E_n in cal(R)$.
]
#state(type: "def", title: "outer & inner measure")[
  Let $mu$ be a premeasure defined on $cal(T)_X$, where $X$ is a Hausdorff topology, and assume that $mu$ is regular on open sets i.e.$mu(U)=mu^*(U), forall U in cal(T)_X$. Define
  $
  "(outer measure)" & mu^*: 2^X->[0,oo], E mapsto inf_(U supset E, U "open") mu(U)\
  "(inner measure)" & mu_*: 2^X->[0,oo], E mapsto sup_(K subset E, K "compact") mu^*(U)
  $
]
#remark[
  1. Note that $mu$ is defined on the topology, which isn't a ring of subsets per se. In fact, $mu$ can be extended to $chevron.l cal(T)_X chevron.r_"bool"$ (the Boolean algebra generated by $cal(T)_X$), upgrading it to a premeasure.\ Hint: every set in $chevron.l cal(T)_X chevron.r_"bool"$ is a finite union of _locally closed_ sets.
  2. $mu^*>=mu_*$ are monotone. Therefore $mu^*(E)=mu_*(E)$ for open/compact $E in X$.
]
#state(type: "def", title: "regular sets")[
  $E subset X$ is $mu$-_regular_ if $mu^*(E)=mu_*(E)$.
]
#intuit[
  Similar to the construction of Jordan measure, we want to claim that the Radon premeasure $mu$ extends to a measure on the $sigma$-algebra of regular sets. Countable additivity follows from the countable subadditivity of the outer measure and the countable superadditivity of the inner measure. However, as we shall see later, the regular sets need _not_ form a $sigma$-algebra. To reconcile this discrepancy, we consider _locally regular_ sets, which in fact constitute a $sigma$-algebra.
]
#remark[
  Countable subadditivity of the outer measure is trivial. As of the countable superadditivity of the inner measure, the proof relies on the following lemma similar to a property of the Lebesgue measure c.f. Lemma 1.2.5 and Exercise 1.2.4 of @tmt. 
]
#state(type: "lem", title: "finite additivity on disjoint compact sets")[
  $K_1, K_2 subset X$ are disjoint compact sets. Then $mu(K_1 union K_2)=mu(K_1)+mu(K_2)$
]
#state(type: "prop", title: "regular sets with finite outer measure")[
  $mu$ defines a premeasure on ring of rugular sets with finite outer measure measure.
]
#remark[
  It suffices to check when $E_1, E_2$ are regular with finite measure, $E_1-E_2$ is regular. For details, check Lemma 23.50 @gba. This observation inspires the following definition.
]
#state(type: "def", title: "local regularity")[
  $E subset X$ is _locally $mu$-regular_ if $E inter O$ is regular for all open $O subset X$ with finite measure.
]
#state(title: "complete measure on locally regular sets")[
  Let $mu$ be a premeasure defined previously. Then $mu$ defines a complete measure on the $cal(M)_mu$, the $sigma$-algebra of locally regular sets, which contains the Borels sets $cal(B)_X$.
]
#remark[
  1. This is the main result of this section. We refer interested readers to Theorem 23.53 @gba for a complete proof, which naturally follows from the previous ideas.
  2. When $mu$ is $sigma$-finite, $cal(M)_mu=cal(M)_X$ where $cal(M)_X=overline(cal(B)_X)$ i.e. the completion of the Borel $sigma$-algebra, see Proposition 23.56 @gba.\ In general, $cal(M)_mu$ is finer than $cal(M)_X$, and is referred to as the _saturation_ of $cal(M)_X$.
  3. With this powerful theorem, Lebesgue measure can be constructed from $m^*|cal(T)_X$, after checking its inner regularity on open sets.
]
#remark[
  The restriction of $mu$ to $cal(B)_X$ is a _Radon measure_ on $X$ if the space is LCH (_locally compact Hausdorff_) and compact sets have finite measure.
]

== Riesz-Markov representation

As in the remark, we primarily work with Radon measures on LCH space $X$ towards the Riesz-Markov representation of positive linear functionals on $C_c (X)$. To this end, we reformulate the Radon conditions:

#state(type: "lem", title: "inner regularity on open sets")[
  $mu$ is inner regular on open sets iff.
  $ mu(U)=sup_(f in C_c (U,[0,1])) integral_X f dif mu $
]
#state(type: "lem", title: "finiteness on compact sets")[
  $mu$ is finite on compact sets iff.
  $ integral_X f dif mu < oo, forall f in C_c (X,[0,1]) $
]
Naturally, given $Lambda$ a positive linear functional on $C_c (X)$, we define

#state(type: "def", title: "premeasure on open sets")[
  Given a positive linear functional $Lambda: C_c (X,[0,oo))->[0,oo)$, let
  $ mu(U):=sup_(f in C_c (U,[0,1])) Lambda(f), forall U in cal(T)_X $
]
To prove the Riesz-Markov representation theorem, we aim to construct a Radon measure associated to $Lambda$. We first extend $Lambda$ to a larger class of functions, namely positive _lower semi-continuous_ functions $"LSC"^+(X)$. The extension follows the protocol of _positive linear functional extension_, albeit sequences are not sufficient in this case, and nets are called up.

#state(type: "def")[
  Define the extension of $Lambda$ as
  $ tilde(Lambda): "LSC"^+(X)->[0,oo], f |-> sup_(g <= f, g in C_c (X,[0,oo))) Lambda(g) $
]
In fact, one can restrict the support of $g$ to the support of $f$ denoted as $"supp"(f):=f^(-1) (0,oo)$, which is open by lower semi-continuity.

#state(type: "lem")[
  $ tilde(Lambda)(f)=sup_(g <= f, g in C_c ("supp"(f),[0,oo))) Lambda(g) $
]
#sketch[
  Trivially $>=$. To show $<=$, let $g_epsilon:=g or 0$. Check that $g_epsilon in C_c ("supp"(f),[0,oo))$, and $tilde(Lambda)(g-g_epsilon)<=tilde(Lambda)(epsilon dot chi_("supp"(g)))<=epsilon Lambda(h)=o(epsilon), epsilon ->0$ where $h in C_c (X,[0,1]): h|"supp"(g)=1$, which exists by Urysohn's lemma.
]
#state(title: [monotone convergence for $"LSC"^+$ functions])[
  Let $(f_alpha)_(alpha in I)$ denote an increasing net in $"LSC"^+(X)$, then $sup_(alpha in I) f_alpha in "LSC"^+(X)$ and
  $ Lambda(sup_(alpha in I) f_alpha) = sup_(alpha in I) Lambda(f_alpha) $
]
#state(title: [approximation of $"LSC"^+$ from below with $C_c$])[
  Let $f in "LSC"^+(X)$. Then there exists an increasing net $(f_alpha)_(alpha in I)$ that converges pointwise to $f$.
]
#remark[
  The sequencial approximation from below isn't true in general. Therefore, we need the net version of monotone convergence. For the details, see Theorem 25.19 and Lemma 25.20 @gba. We conclude that the extension $tilde(Lambda)$ is $overline(RR)_(>=0)$ linear.
]
With the above machinery, we can now prove the main theorem:

#state(title: "Riesz-Markov representation")[
  For every positive linear functional $Lambda$ on $C_c (X)$, there exists a unique Radon measure $mu:cal(B)_X->[0,oo]$ such that
  $ Lambda(f) = integral_X f dif mu, forall f in C_c (X, [0,oo)) $
]
#remark[
  By defining the premeasure with $mu(U):=Lambda(chi_U), forall U in cal(T)_X$ and checking the premeasure axioms with inner regularity on open sets, we obain a Borel measure with both inner and outer regularitys. To demonstrate that the positive linear functional on $C_c (X)$ agrees with the integral, we applying the monotone convergence theorem to indicator functions on open set. Finiteness on compact sets follows. For the details, see Theorem 25.23 @gba.
]

== Signed measure

We introduce signed measure and some elementary results, in order to generalize the Riesz-Markov representation theorem to a larger class of linear functionals on $C_c (X)$.
#state(type: "def", title: "signed measure")[
  $mu:cal(X)->overline(RR)$ is a _signed measure_ if
  1. $mu(emptyset)=0$
  2. $im(mu)$ either contain $-oo$ or $oo$, but not both
  3. For disjoint $E_n, n in NN$, $sum_(n=1)^oo mu(E_n)=mu(union_(n=1)^oo E_n)$
]
#state(type: "def", title: "mutually singular measure")[
  Let $mu_1$ and $mu_2$ be two measures on $cal(X)$. They are _mutually singular_ if they are _supported_ on disjoint $E_1, E_2$ i.e.
  $ mu_1|E_1^C = mu_2|E_2^C =0 $
]
#state(title: "Jordan decomposition & total variation of signed measure")[
  Every signed measure $mu$ can be uniquely decomposed uniquely into the difference of two mutually singular unsigned measures $mu_+ - mu_-$.\ $abs(mu):=mu_+ + mu_-$ is called the _total variation_ of the signed measure.
]
#remark[
  This is the foundamental result about signed measure. For the details, see Exercise 1.2.5 @tra. The generalization of the Riesz-Markov representation theorem is similar to this result in spirit, decomposing a linear functional into positive and negative part.
]
#state(title: "Jordan decomposition of bounded linear functionals")[
  Let $C_c (X; RR)$ be a subspace of $L^oo (X)$ i.e. equipped with the supremum norm. Then a bounded linear functional $Lambda$ can be decomposed uniquely into the difference of two positive linear functionals with disjoint support $Lambda_+ - Lambda_-$.
]
#intuit[
  We extract the maximum positive portion of $Lambda$, defining $Lambda_+:f mapsto sup_(0<=g<=f) Lambda(g)$, and check that it is indeed linear. $Lambda_-:=Lambda_+ - Lambda$. The idea is similar to the Jordan decomposition of signed measure, where one find the maximal support on which the measure is positive.
]
Apply the Riesz-Markov representation theorem to $Lambda_+$ and $Lambda_-$ to obtain the following result:
#state(title: "finite signed Radon measure")[
  The dual of $C_c (X)$ equipped with supremum norm i.e. $(C_c (X), norm(dot)_oo)^*$ is isomorphic to the space of finite signed Radon measures.
]
By embedding $C_c (X)$ densely into $C_0 (X)$, the space of continuous functions vanishing at infinity, we obtain the representation for linear functionals on a larger space.
#state(type: "def", title: "vanishing at infinity")[
  $X$ is a LCH space. Let $C_0 (X)$ denote the space of continuous functions vanishing at infinity, such that
  $ K_epsilon := {x in X; abs(f(x)) >= epsilon} "is compact", forall epsilon>0 $
]
#remark[
  In fact, $C_c (X)$ is dense in $C_0 (X)$ with the supremum norm. Therefore $C_c (X)^* tilde.eq C_0 (X)^*$, and thus $C_0 (X)^*$ is represented by the space of finite signed Radon measures.
]
We state an even more general result on the representation of signed Radon measure, which lays the foundation of distribution theory.
#state(title: "Riesz-Markov representation for signed Radon measure")[
  Let $ C_K (X):={f in C_c (X); "supp"(f) in K} $
  Equip $C_c (X)$ with the final topology w.r.t. the injections $C_K (X) subset L^oo arrow.r.hook C_c (X), K "compact"$. Then its dual is isomorphic to the space of all signed Radon measure.
]
#remark[
  Unlike abstract signed measure, signed Radon measure is defined on the ring of Borel sets with compact closure to ensure finiteness. The proof essentially decomposes the functional.
]
Before concluding this section, we present an useful criterion for a Borel measure to be Radon. For the proof, see Theorem 25.37 @gba.

#state[
  Let $X$ be a second countable LCH space, and $mu$ be a Borel measure that is finite on compact sets. Then $mu$ is a Radon measure.
]

= Outer measures, pre-measures, and product measures

In this section, we present foundational results in measure theory. We omit most proofs, since their ideas are somewhat deviates from the previous discussion, referring the readers to section 1.7 and 2.4 of @tmt. 
#state(title: "Carathéodory extension")[
  Let $mu^*:2^X->[0,oo]$ be an outer measure (null, monotone, and countably subadditive) on $X$. $E subset X$ is _Carathéodory measurable_ if
  $ mu^* (A)=mu^* (A inter E)+mu^* (A-E), forall A subset X $
  Let $cal(X)$ denote the _Carathéodory measurable_ sets. Then $cal(X)$ is a $sigma$-algebra, and $mu$ is a complete measure.
]
#state(title: "Hahn-Kolmogorov extension")[
  Let $mu_0$ be a premeasure (Boolean measure that is countably additive) on a Boolean algebra $cal(B)_0$ in $X$. Then there exists an extension to a measure $mu:cal(B)->[0,oo]$ on the $sigma$-algebra generated by $cal(B)_0$. If in addition, $mu_0$ is $sigma$-finite, then the extension is unique on $cal(B)$.
]
We use the _Hahn-Kolmogorov extension_ theorem to construct product measure of $sigma$-finite spaces. In the following, we assume that $(X, cal(X), mu_X)$ and $(Y, cal(Y), mu_Y)$ are $sigma$-finite spaces.

#state(title: "product measure")[
  There exists a unique measure $mu:=mu_X times mu_Y$ on $cal(X) times cal(Y)$ such that $mu(E times F)=mu_X (E) mu_Y (F), forall E in cal(X), F in cal(Y)$.
]
We moreover require completeness of $mu_X$ and $mu_Y$.
#state(title: "Tonelli")[
  Let $f: X times Y->[0,oo]$ be measurable w.r.t. $overline(cal(X) times cal(Y))$. Then
  + For $mu_X$-a.e. $x in X$, $y|->f(x,y)$ is $cal(Y)$-measurable. Furthermore, $x|->integral_Y f(x,y) dif mu_Y$ is $cal(X)$-measurable. (resp. $dots$)
  + $ integral _ ( X times Y ) f ( x, y ) dif overline( mu _ ( X ) times mu _ ( Y ) ) ( x, y ) = integral _ ( X ) ( integral _ ( Y ) f ( x, y ) dif mu _ ( Y ) ( y ) ) dif mu _ ( X ) ( x ) = "resp." dots $
]
#state(title: "Fubini")[
  Let $f: X times Y->CC$ be absolutely integrable on $overline(cal(X) times cal(Y))$. Then
  + For $mu_X$-a.e. $x in X$, $y|->f(x,y)$ is absolutely integrable on $cal(Y)$. Furthermore, $x|->integral_Y f(x,y) dif mu_Y$ is absolutely integrable on $cal(X)$. (resp. $dots$)
  + $ integral _ ( X times Y ) f ( x, y ) dif overline( mu _ ( X ) times mu _ ( Y ) ) ( x, y ) = integral _ ( X ) ( integral _ ( Y ) f ( x, y ) dif mu _ ( Y ) ( y ) ) dif mu _ ( X ) ( x ) = "resp." dots $
]
Combining the two theorems, we obtain the celebrated _Fubini-Tonelli theorem_.
#state(type: "cor", title: "Fubini-Tonelli")[
  Let $f: X times Y->CC$ be measurable w.r.t. $overline(cal(X) times cal(Y))$. If
  $ integral _ ( X ) ( integral _ ( Y ) abs( f ( x, y )) dif mu _ ( Y ) ( y ) ) dif mu _ ( X ) ( x ) < oo "or resp." dots $
  Then $f$ is absolutely integrable on $overline(cal(X) times cal(Y))$. 
]
We end the section on a climax: the _Kolmogorov extension theorem_.
#state(title: "Kolmogorov extension")[
  Let $(X_alpha,cal(X)_alpha)$ be a family of measure spaces with topology $cal(T)_alpha$. For each finite $B subset Alpha$, let $mu_B$ be an inner regular probability measure on $product_(alpha in B) cal(X)_alpha$ w.r.t. $product_(alpha in B) cal(T)_alpha$ obeying compatibility i.e. $mu_C$ is the pushforward of $mu_B$ by the projection when $C subset B subset Alpha$. Then there exists a unique probability measure $mu_Alpha$ on $product_(alpha in A) cal(X)_alpha$ compatible with $mu_B$ for any finite $B subset Alpha$.
]
#bibliography("ref.yaml")
