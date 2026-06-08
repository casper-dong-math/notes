#import "lib.typ":*
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#let rp=$RR_(>=0)$

#show title: set text(size: 18pt)
#show title: set align(center)

#title[
  An Introduction to Brownian Motion and Stochastic Calculus
]

#align(center)[
    Casper Dong, Xialei Huang, Hans Wang \
    NYU Shanghai \
    {casper.dong, xialei.huang, sw6630}\@nyu.edu
]
\

#align(center)[
  #set par(justify: false)
  *Abstract* \
]
Brownian motion (BM) provides the canonical mathematical framework for modeling the continuous and erratic motion of a particle suspended in a fluid. Historically rooted in the 1827 observations of botanist Robert Brown, the phenomenon arises from the cumulative effect of incessant collisions with the surrounding medium's molecules. The primary objective of this report is to move beyond heuristic descriptions and establish a rigorous mathematical formulation of this stochastic process. 

The construction of a Brownian motion presented here follows a standard measure-theoretic approach. While Lévy’s construction remains celebrated for its geometric elegance, the standard method is preferred here because it allows the fundamental properties of the process, such as its martingale and the Markov property, to be derived as direct consequences.

The second half aims to introduce the subject of stochastic analysis. Local martingales and semimartingales are defined, laying the groundwork for quadratic variation and the chevron bracket process. Armed with these tools, the stochastic integral for semimartingales is constructed via Itô isometry. This development culminates in the proof of Itô’s formula, the cornerstone of stochastic analysis. As a direct consequence, Lévy’s characterization of Brownian motion is demonstrated. The notes conclude with an alternative proof of the reflection principle, offering a glimpse into the profound depth of stochastic calculus.

To ensure that the exposition remains concise and focused on the conceptual architecture of the theory, exhaustive technical proofs are frequently omitted in favor of intuitive sketches. For the full rigorous treatments, the reader is encouraged to consult the main reference @lg. The numbering of results in this note corresponds directly to the that of the reference.

#pagebreak()
= Brownian Motion

== Gaussian spaces

#state(type: "def", title: [Centered Gaussian variable])[
A real random variable $X$ is said to be a _centered Gaussian variable_ with $cal(N) (0,sigma^2)$-distribution if its law has density

$ p_X (x) = 1 / (sqrt(2 pi sigma^2)) exp(-x^2 / (2 sigma^2)) $
]

#state(type: "def", title: [Centered Gaussian space])[
A _centered Gaussian space_ is a closed linear subspace of $L^2(Omega, cal(F), P)$ which contains only centered Gaussian variables.
]

Note that the $L^2$ limit of centered Gaussian variables is still centered Gaussian, since $L^2$ convergence implies pointwise convergence of characteristic functions, and the result follows from computation. Therefore the space of centered Gaussian variables is closed in $L^2$, though generally not linear.

#state(title: [Orthogonality $<=>$ Independence])[
Let $H$ be a centered Gaussian space and let $(H_i)_(i in I)$ be a collection of linear subspaces of $H$. Then the subspaces $H_i, i in I$, are (pairwise) orthogonal in $L^2$ if and only the $sigma$-fields $sigma(H_i), i in I$, are independent.
]

#sketch[
The non-trivial direction reduces to verifying that, if $xi_j^i in H_i, j=1, dots, n_i$ are fixed for $i in F$, where $F subset I$ is of finite cardinality, then the vectors ${(xi_j^i)_(j=1)^(n_i)}_(i in F)$ are independent. Perform the Gram Schmidt process to ${xi_j^i}_(j=1)^(n_i)$, we obtain orthogonal lists ${eta_j^i}_(j=1)^(m_i)$. Observe that the covariance matrix of the vector $(eta_1^1, dots, eta_(m_1)^1, dots, eta_1^f, dots, eta_(m_f)^f)$ is identity. Therefore the vectors $(eta_j^i)_(j=1)^(m_i)$ are independent, i.e. $(xi_j^i)_(j=1)^(n_i)$ are independent.
]

#alert[
  When $(H_i)_(i in I)$ are not subspaces of an overarching centered Gaussian space, orthogonality generally _doesn't_ imply independence. Let $X tilde cal(N) (0,1)$, $c$ independent of $X$ with $P(c=-1)=P(c=1)=1\/2$. Then $X'=c X tilde cal(N) (0,1)$, and $chevron.l X, X' chevron.r_(L^2)=E[X X']=E[c] E[X^2]=0$. Nonetheless $X$ and $X'$ are not independent.
]

== Gaussian white noise

#state(type: "def", title: [Gaussian white noise])[
Let $(E, cal(E))$ be a measure space, and let $mu$ be a $sigma$-finite measure on $(E, cal(E))$. A _Gaussian white noise with intensity_ $mu$ is an isometry $G$ from $L^2(E, cal(E), mu)$ into a centered Gaussian space.
]

Note that, although Gaussian white noise is defined for arbitrary $f in L^2 (E, cal(E), mu)$, we are mostly interested in its behavior on sets of finite measure $A in cal(E)$, or more precisely, their indicator functions. Denote $G(A) := G(II_A)$. Then $G(A) tilde cal(N) (0, mu(A))$, justifying the notion of "intensity" in the definition. For disjoint ${A_i}_(i in I)$ of finite measure, ${G (A_i)}_(i in I)$ is a family of independent Gaussian random variables. 

#state(title: [Existence of Gaussian white noise])[
Let $(E, cal(E))$ be a measure space, and let $mu$ be a $sigma$-finite measure on $(E, cal(E))$. There exists, on an appropriate probability space $(Omega, cal(F), P)$, a Gaussian white noise with intensity $mu$.
]

#sketch[
  Let $(f_i)_(i in I)$ denote an orthonormal basis for $L^2 (E, cal(E), mu)$. On an appropriate probability space $(Omega, cal(F), P)$, we can construct a collection of independent $cal(N) (0,1)$-distributed random variables $(X_i)_(i in I)$. Then
  $ G(f)=sum_(i in I) chevron.l f, f_i chevron.r X_i $
  is a valid Gaussian white noise.
]

== Pre-Brownian motion

#state(type: "def", title: [Pre-Brownian motion])[
Let $G$ be a Gaussian white noise on $rp$ whose intensity is the Lebesgue measure. The random process $(B_t)_(t in bb(R)_+)$ defined by

$ B_t = G(II_[0,t]) $

is called _pre-Brownian motion_.
]

The term _pre-Brownian motion_ is non-standard. The definition provides a model that focuses on the distributional properties, serving as the foundation before we impose the requirement of sample path continuity.

*Remark:* One can recover $G$ through $(B_t)_(t>=0)$, by density of step functions in $L^2$.

#state(title: [Equivalent formulations of pre-Brownian motion])[
Let $(X_t)_(t >= 0)$ be a (real-valued) random process. The following properties are equivalent:

1. $(X_t)_(t >= 0)$ is a pre-Brownian motion; \
2. $X_0 = 0$ a.s., and, for every $0 <= s < t$, the random variable $X_t - X_s$ is independent of $sigma(X_r, r <= s)$ and distributed according to $cal(N)(0, t - s)$; \
3. $X_0 = 0$ a.s., and, for every choice of $0 = t_0 < t_1 < dots < t_p$, the variables $X_(t_i) - X_(t_(i-1)), 1 <= i <= p$ are independent, and, for every $1 <= i <= p$, the variable $X_(t_i) - X_(t_(i-1))$ is distributed according to $cal(N)(0, t_i - t_(i-1))$.
]

The second property is referred to as the _simple Markov property_, distinguishing it from the _strong Markov property_ which will be discussed later. The third property, after a change of variables, characterizes the _finite dimensional marginal distribution_ of the pre-Brownian motion.

#sketch[
  $1=>2=>3$ trivially. For $3=>1$, let $H$ denote the Gaussian space spanned by $(X_t)_(t >= 0)$. By the density of step functions in $L^2 (rp, cal(B) (rp), lambda)$, it suffice to define $G$ on step functions
  $ G(sum_(i=1)^n c_i II_((t_(i-1), t_i]))=sum_(i=1)^n c_i (X_t_i - X_t_(i-1)) $
  Check that it is indeed an isometry, therefore $G$ can be continuously extended to $L^2(rp)$.
]

== Continuity of Sample Path

#state(type: "def", title: [Sample path])[
Let $(X_t)_(t in T)$ be a random process with values in $E$. The _sample paths_ of $X$ are the mappings $t |-> X_t (omega)$ obtained when fixing $omega in Omega$. The sample paths of $X$ thus form a collection of mappings from $T$ into $E$ indexed by $omega in Omega$.
]

Vaguely speaking, Brownian motion is a version pre-Brownian motion such that sample paths are continuous. The next two definitions makes the claim precise.

#state(type: "def", title: [Modification])[
Let $(X_t)_(t in T)$ and $(tilde(X)_t)_(t in T)$ be two random processes indexed by the same index set $T$ and with values in the same metric space $E$. We say that $tilde(X)$ is a _modification_ of $X$ if

$ forall t in T, quad P(tilde(X)_t = X_t) = 1 $
]

#state(type: "def", title: [Indistinguishability])[
The process $tilde(X)$ is said to be _indistinguishable_ from $X$ if there exists a negligible subset $N$ of $Omega$ such that

$ forall omega in Omega \\ N, forall t in T, quad tilde(X)_t (omega) = X_t (omega). $
]

Indistinguishability is a strictly stronger criterion than being a modification. In fact, Brownian motion is a modification of pre-Brownian motion such that the sample paths are continuous, unique up to indistinguishability.

To demonstrate existence of such a modification, we make use of the following analytical lemma, whose proof is omitted.

#state(type: "def", title: [Kolmogorov's lemma])[
Let $X = (X_t)_(t in I)$ be a random process indexed by a bounded interval $I$ of $bb(R)$. Assume that there exist three reals $q, epsilon, C > 0$ such that, for every $s, t in I$,

$ E[abs(X_s-X_t)^q] <= C |t - s|^(1+epsilon). $

Then, there is a modification $tilde(X)$ of $X$ whose sample paths are Hölder continuous with exponent $alpha$ for every $alpha in (0, epsilon/q)$ i.e. for every $omega in Omega$ and every $alpha in (0, epsilon/q)$, there exists a finite constant $C(alpha, omega)$ such that, for every $s, t in I$,

$ abs(tilde(X)_s (omega) - tilde(X)_t (omega)) <= C(alpha, omega) |t - s|^alpha. $

In particular, $tilde(X)$ is a modification of $X$ with continuous sample path, which is unique up to indistinguishability.
]

== Brownian motion

We apply Kolmogorov's lemma to obtain a continuous modification of pre-Brownian motion. Therefore Brownian motion inherits the distributional properties established for pre-Brownian motion, whilst enjoying continuity of sample paths.

#state(type: "def", title: [Existence of continuous modification of pre-Brownian motion])[
Let $B = (B_t)_(t >= 0)$ be a pre-Brownian motion. The process $B$ has a modification whose sample paths are continuous, and even locally Hölder continuous with exponent $1/2 - delta$ for every $delta in (0, 1/2)$. 
]

#proof[
If $s < t$, the random variable $B_t - B_s tilde cal(N)(0, t - s) tilde sqrt(t-s) X$ where $X tilde cal(N)(0, 1)$. Consequently, for every $q > 0$,

$ E[abs(B_t - B_s)^q] = E[abs(X)^q] (t - s)^(q/2) $

where $E[abs(X)^q] < oo$. Taking $q > 2$, we can apply Kolmogorov's lemma with $epsilon = q/2 - 1$. It follows that $B$ has a modification whose sample paths are locally Hölder continuous with exponent $alpha$ for every $alpha < (q - 2)/(2q)$. If $q$ is large we can take $alpha$ arbitrarily close to $1/2$. 
]

#state(type: "def", title: [Brownian motion])[
A process $(B_t)_(t >= 0)$ is a _Brownian motion_ if:
1. $(B_t)_(t >= 0)$ is a pre-Brownian motion.
2. All sample paths of $B$ are continuous.
]

Brownian motion is unique up to indistinguishability. To see this, suppose $X_0$ and $X_1$ are two modifications of $X$ with continuous sample path. Then $X_0=X_1$ a.s. on $rp inter QQ$, by taking countable union of null sets. By continuity, $X_0=X_1$ a.s.

== The Wiener measure

The Wiener measure provides a canonical construction of Brownian motion. Equip $C(rp, RR)$ with the pullback $sigma$-algebra of ${w mapsto w(t)}_(t >=0)$, denoted as $cal(C)$.

#state(type: "def", title: [Wiener measure])[
The Wiener measure on $C(rp, RR)$ is the pushforward of $P$ under \

$ (B_t)_(t>=0): omega mapsto [t mapsto B_t (omega)] $

the sample path at $omega$. Check that the map is indeed measurable.
]

The uniqueness of Wiener measure follows from the uniqueness of finite dimensional marginal distribution of Brownian motion.

#state(type: "def", title: [Canonical construction of Brownian motion])[
Let the probability space be the Wiener measure $(C(rp, RR), cal(C), W)$. Then the canonical process

$ X_t (w)=w(t), t>=0, w in C(rp, RR) $

is a Brownian motion, called the _canonical construction_.
]

== Reflection principle \#1

#state(title: [Strong Markov property])[
Let $T$ be a stopping time. We assume that $P(T < oo) > 0$ and we set, for every $t >= 0$,

$ B_t^((T)) = II_({T < oo}) (B_(T+t) - B_T). $

Then under the probability measure $P(dot.c | T < oo)$, the process $(B_t^((T)))_(t >= 0)$ is a Brownian motion independent of $cal(F)_T$.
]

The strong Markov property extends the simple Markov property, replacing deterministic $t$ with a random stopping time $T$.

As an application, we present the first proof of the reflection principle.

#state(title: [Reflection principle \#1])[
For every $t > 0$, set $S_t = sup_(s <= t) B_s$. Then, if $a >= 0$ and $b in (-oo, a]$, we have

$ P(S_t >= a, B_t <= b) = P(B_t >= 2a - b) $
]


#figure(
  image("reflection.png", width: 50%),
  caption: [Illustration of the reflection principle.]
)

*Proof* Apply the strong Markov property at the stopping time

$ tau = inf \{t >= 0 : B_t = a\}. $

which is finite a.s. then $B^((tau))$ is a Brownian motion independent of $cal(F)_(tau) in.rev tau$. Therefore $(tau, B^((tau))) tilde (tau, -B^((tau)))$ in $rp times C(rp, RR)$ with the product measure. We obtain

$
P(S_t >= a, B_t <= b) &= P(tau <= t, B_(t-tau)^((tau)) <= b - a) \
&= P(tau <= t, -B_(t-tau)^((tau)) <= b - a) \
&= P(tau <= t, B_t >= 2a - b) \
&= P(B_t >= 2a - b)
$

#pagebreak()
= Stochastic Integration

We aim to construct a general stochastic integral $integral H dif W$, where integrand $H$ is the class of _progressive processes_, and $W$ the class of semimartingales. We first define both class of processes.

== Progressive processes
#state(type: "def", title: [Progressive measurability])[
A random process $X = (X_t)_(t >= 0): rp times Omega -> RR$ is _progressively measurable_ with respect to a filtration $(cal(F)_t)_(t >= 0)$ if, for every $t >= 0$, the restriction $X | [0, t] times Omega$ is $cal(B)([0, t]) times.o cal(F)_t$-measurable. 
]

#state(type: "def", title: [Progressive $sigma$-algebra])[
The _progressive $sigma$-algebra_ on $rp times Omega$, denoted as $cal(P)$, is the $sigma$-algebra formed by all subsets $A subset bb(R)_+ times Omega$ such that, for every $t >= 0$,
$ A inter ([0, t] times Omega) in cal(B)([0, t]) times.o cal(F)_t. $
]

We note that $(X_t)_(t>=0)$ being progressively measurable is equivalent to $X$ being $cal(P)$-measurable.

== Semimartingales

Before defining semimartingales, we first introduce finite variation processes and continuous local martingales. 

#state(type: "def", title: [Finite variation processes])[
An adapted process $A = (A_t)_(t >= 0)$ is called a _finite variation process_ if all its sample paths are continuous functions of finite variation on $rp$ starting at $0$. If in addition the sample paths are nondecreasing functions, the process $A$ is called an increasing process.
]

Integrating against a finite variation process reduces to the Riemann-Stieltjes integral. The following definition generalizes martingales.

#state(type: "def", title: [Continuous local martingale])[
An adapted process $M = (M_t)_(t >= 0)$ with continuous sample paths is called a _continuous local martingale_ if there exists a nondecreasing sequence $(T_n)_(n >= 0)$ of stopping times such that $T_n arrow.t oo$ (i.e. $T_n(omega) arrow.t oo$ for every $omega$) and, for every $n$, the stopped process $(M-M_0)^(T_n)$ is a uniformly integrable martingale.
]

The next theorem on quadratic variation will play a very important role in forthcoming developments.

#state(number: "4.9", title: [Quadratic variation])[
  Let $M=(M_t)_(t >= 0)$ be a continuous local martingale. There exists an increasing process denoted by $(chevron.l M, M chevron.r_t)_(t >= 0)$, which is unique up to indistinguishability, such that $M_t^2 - chevron.l M, M chevron.r_t$ is a continuous local martingale. 
  
  Furthermore, for every fixed $t > 0$, if $0 = t_0^n < t_1^n < dots < t_(p_n)^n = t$ is an increasing sequence of subdivisions of $[0, t]$ with mesh tending to $0$, we have
  
  $ chevron.l M, M chevron.r_t = lim_(n arrow infinity) sum_(i=1)^(p_n) (M_(t_i^n) - M_(t_(i-1)^n))^2 $
  
  in probability. The process $chevron.l M, M chevron.r$ is called the quadratic variation of $M$.
]

#sketch[
  To demonstrate niqueness, assume two such processes $A$ and $A'$ exist. The difference $A - A' = (M^2 - A') - (M^2 - A)$ is then a continuous local martingale of finite variation, which must be 0 a.s. 
  
  For existence, when $M$ is bounded and $M_0=0$, apply the discrete martingale identity
  $ M_(t_j)^2 - 2 sum_(i=1)^j M_(t_(i-1))(M_(t_i) - M_(t_(i-1))) = sum_(i=1)^j (M_(t_i) - M_(t_(i-1)))^2 n$
  Doob's maximal inequality in $L^2$ is then extracts a uniformly convergent subsequence of the martingale, whose limit is denoted $chevron.l M, M chevron.r$. The general case follows by localization via the stopping times $T_n = inf {t >= 0 : |M_t| >= n}$ and taking limit as $n->oo$.
]

== The Bracket of Two Continuous Local Martingales

#state(type: "def", number: "4.14", title: [The bracket process])[
  If $M$ and $N$ are two continuous local martingales, the bracket $chevron.l M, N chevron.r$ is the finite variation process defined by setting, for every $t >= 0$,
  
  $ chevron.l M, N chevron.r_t = 1/2 (chevron.l M + N, M + N chevron.r_t - chevron.l M, M chevron.r_t - chevron.l N, N chevron.r_t). $
]

As one would expect,

$ chevron.l M, N chevron.r_t = lim_(n arrow infinity) sum_(i=1)^(p_n) (M_(t_i^n) - M_(t_(i-1)^n))(N_(t_i^n) - N_(t_(i-1)^n)) $

in probability. We also note the _Kunita--Watanabe inequality_, whose proof follows from the Cauchy-Schwartz inequality for simple functions $H, K$, then an arguement by density.

#state(number: "4.18", title: [Kunita--Watanabe])[
  Let $M$ and $N$ be two continuous local martingales and let $H$ and $K$ be two measurable processes. Then, a.s.,
  $ integral_0^infinity |H_s| |K_s| |dif chevron.l M, N chevron.r_s| <= (integral_0^infinity H_s^2 dif chevron.l M, M chevron.r_s)^(1/2) (integral_0^infinity K_s^2 dif chevron.l N, N chevron.r_s)^(1/2). $
]

== Continuous Semimartingales

#state(type: "def", number: "4.19", title: [Continuous semimartingale])[
  A process $X=(X_t)_(t >= 0)$ is a continuous semimartingale if it can be written in the form
  
  $ X_t = M_t + A_t $
  
  where $M$ is a continuous local martingale and $A$ is a finite variation process.
]

The construction of the stochastic integral proceeds in three stages: first for continuous martingales bounded in $L^2$, then extended to continuous local martingales via localization, and finally to semimartingales.

== Stochastic Integrals for Martingales Bounded in $L^2$

We write $bb(H)^2$ for the space of all continuous martingales $M$ which are bounded in $L^2$ and such that $M_0 = 0$. For $M in bb(H)^2$, we let $L^2(M)$ be the set of all progressive processes $H$ such that
$ E[integral_0^infinity H_s^2 dif chevron.l M, M chevron.r_s] < infinity $

#state(type: "def", number: "5.2", title: [Elementary process])[
  An elementary process is a progressive process of the form
  $ H_s(omega) = sum_(i=0)^(p-1) H_((i))(omega) II_((t_i, t_(i+1)])(s), $
  where $0 = t_0 < t_1 < t_2 < dots < t_p$ and for every $i in {0, 1, dots, p-1}$, $H_((i))$ is a bounded $cal(F)_(t_i)$-measurable random variable.
]

Elementary process is the analogue of step functions. We define its integral, then extend the operator onto $L^2 (M)$.

#state(number: "5.4", title: [Construction of stochastic integral])[
  Let $M in bb(H)^2$. For every elementary process $H$ of the form
  $ H_s(omega) = sum_(i=0)^(p-1) H_((i))(omega) II_((t_i, t_(i+1)])(s), $
  the formula
  $ (H dot M)_t = sum_(i=0)^(p-1) H_((i)) (M_(t_(i+1) and t) - M_(t_i and t)) $
  defines a process $H dot M in bb(H)^2$. The mapping $H mapsto H dot M$ extends to an isometry from $L^2(M)$ into $bb(H)^2$. Furthermore, $H dot M$ is the unique martingale of $bb(H)^2$ that satisfies the property
  $ chevron.l H dot M, N chevron.r = H dot chevron.l M, N chevron.r, quad forall N in bb(H)^2. $
  If $T$ is a stopping time, we have
  $ (II_[0,T] H) dot M = (H dot M)^T = H dot M^T. $
]

#sketch[
  For $H in cal(E)$, the integral $H dot M$ is a linear combination of orthogonal martingales in $HH$. Direct computation of their quadratic variations yields $chevron.l H dot M, H dot M chevron.r_t = integral_0^t H_s^2 dif chevron.l M, M chevron.r_s$, establishing the isometry
  $ norm(H dot M)_(bb(H)^2) = norm(H)_(L^2(M)) $
  Because $cal(E)$ is dense in $L^2(M)$ and $bb(H)^2$ is a Hilbert space, this linear isometry uniquely extends to the entirety of $L^2(M)$.

  To verify the characteristic property, fix $N in bb(H)^2$. For $H in cal(E)$, check that 
  $ chevron.l H dot M, N chevron.r_t = integral_0^t H_s dif chevron.l M, N chevron.r_s $
  For a general $H in L^2(M)$, we take a sequence $H^n in cal(E)$ converging to $H$. The Kunita-Watanabe inequality analytically bounds the total variation, guaranteeing that both sides of the identity converge in $L^1$. Finally, the identity for stopping times follows from the bracket relation
  $ chevron.l (H dot M)^T, N chevron.r_t = chevron.l H dot M, N chevron.r_(t and T) = (II_[0,T] H dot chevron.l M, N chevron.r)_t $
]

== Stochastic Integrals for Local Martingales

For a continuous local martingale $M$, we define $L_("loc")^2(M)$ as the set of progressive processes $H$ such that $integral_0^t H_s^2 dif chevron.l M, M chevron.r_s < infinity$ a.s. for all $t >= 0$.

#state(number: "5.6", title: [Stochastic Integrals for Local Martingales])[
  Let $M$ be a continuous local martingale. For every $H in L_("loc")^2(M)$, there exists a unique continuous local martingale with initial value 0, which is denoted by $H dot M$, such that, for every continuous local martingale $N$,
  $ chevron.l H dot M, N chevron.r = H dot chevron.l M, N chevron.r. $
  If $T$ is a stopping time, we have
  $ (II_[0,T] H) dot M = (H dot M)^T = H dot M^T. $
  If $H in L_("loc")^2(M)$ and $K$ is a progressive process, we have $K in L_("loc")^2(H dot M)$ if and only if $H K in L_("loc")^2(M)$ and then
  $ H dot (K dot M) = (H K) dot M. $
]

#sketch[
  We localize the integral by defining the stopping times
  $ T_n = inf {t >= 0 : integral_0^t (1 + H_s^2) dif chevron.l M, M chevron.r_s >= n} $
  The stopped martingales $M^(T_n)$ belong to $bb(H)^2$ and $H in L^2(M^(T_n))$, and thus $H dot M^(T_n)$ is well-defined. For any $m > n$, mote that
  $ (H dot M^(T_m))^(T_n) = H dot M^(T_n) $
  holds almost surely. Because $T_n arrow.t infinity$, there exists a unique process $H dot M$ whose sample path extends $H dot M^(T_n)$ for every $n$. Since these stopped processes are martingales in $bb(H)^2$, $H dot M$ is a well-defined continuous local martingale. The characteristic and associativity properties are inherited by applying reducing stopping times and passing to the limit.
]

== Stochastic Integrals for Semimartingales

#state(type: "def", number: "5.7", title: [Stochastic integrals for semimartingales])[
  Let $X$ be a continuous semimartingale and let $X = M + V$ be its canonical decomposition. If $H$ is a locally bounded progressive process, the stochastic integral $H dot X$ is the continuous semimartingale with canonical decomposition
  $ H dot X = H dot M + H dot V, $
  and we write
  $ (H dot X)_t = integral_0^t H_s dif X_s. $
]

== Itô's Formula

Itô's formula is the fundamental chain rule of stochastic calculus. Unlike the deterministic chain rule, it adds a second-order term to account for the non-zero quadratic variation of continuous semimartingales.

#state(number: "5.10", title: [Itô's formula])[
  Let $X$ be a continuous semimartingale, and let $F$ be a twice continuously differentiable real function on $RR$. Then, for every $t >= 0$,
  $ F(X_t) = F(X_0) + integral_0^t F'(X_s) dif X_s + 1/2 integral_0^t F''(X_s) dif chevron.l X, X chevron.r_s. $
]

#proof[
  Fix a time $t > 0$ and consider a sequence of subdivisions $0 = t_0^n < dots < t_(p_n)^n = t$ whose mesh tends to $0$. Applying the deterministic Taylor-Lagrange formula to the increments of $F(X_t)$ yields

$ F(X_(t_(i+1)^n)) - F(X_(t_i^n)) = F'(X_(t_i^n))(X_(t_(i+1)^n) - X_(t_i^n)) + 1/2 f_(n,i) (X_(t_(i+1)^n) - X_(t_i^n))^2 $

where the quantity $f_(n,i)$ can be written as $F''(X_(t_i^n) + c(X_(t_(i+1)^n) - X_(t_i^n)))$ for some $c in [0,1]$. By the approximation of stochastic integrals for continuous integrands, setting $H_s = F'(X_s)$, we have

$ lim_(n arrow infinity) sum_(i=0)^(p_n-1) F'(X_(t_i^n))(X_(t_(i+1)^n) - X_(t_i^n)) = integral_0^t F'(X_s) dif X_s, $

in probability. To complete the proof, it is therefore enough to verify that the second-order term converges to the quadratic variation integral

$ lim_(n arrow infinity) sum_(i=0)^(p_n-1) f_(n,i) (X_(t_(i+1)^n) - X_(t_i^n))^2 = integral_0^t F''(X_s) dif chevron.l X, X chevron.r_s $

in probability. We observe that

$ sup_(0 <= i <= p_n-1) abs(f_(n,i) - F''(X_(t_i^n))) <= sup_(0 <= i <= p_n-1) (sup_(x in [X_(t_i^n) and X_(t_(i+1)^n), X_(t_i^n) or X_(t_(i+1)^n}]) abs(F''(x) - F''(X_(t_i^n)))). $

The right-hand side vanishes almost surely as $n arrow infinity$,by the uniform continuity of $F''$ and that of the sample paths of $X$ over a compact interval. Since the sum of the squared increments $sum_(i=0)^(p_n-1)(X_(t_(i+1)^n) - X_(t_i^n))^2$ converges in probability to the total quadratic variation $chevron.l X, X chevron.r_t$, 
$ lim_(n arrow infinity) abs(sum_(i=0)^(p_n-1) f_(n,i)(X_(t_(i+1)^n) - X_(t_i^n))^2 - sum_(i=0)^(p_n-1) F''(X_(t_i^n))(X_(t_(i+1)^n) - X_(t_i^n))^2) = 0 $
in probability. So the convergence of the second-order term will follow if
$ lim_(n arrow infinity) sum_(i=0)^(p_n-1) F''(X_(t_i^n))(X_(t_(i+1)^n) - X_(t_i^n))^2 = integral_0^t F''(X_s) dif chevron.l X, X chevron.r_s $
in probability. It suffices to show that convergence holds almost surely along a suitable sequence of values of $n$. Note that the sum can be written as an integral against a discrete measure
$ sum_(i=0)^(p_n-1) F''(X_(t_i^n))(X_(t_(i+1)^n) - X_(t_i^n))^2 = integral_[0,t] F''(X_s) mu_n (dif s), $
where $mu_n$ is the measure on $[0,t]$ defined by
$ mu_n (dif r) := sum_(i=0)^(p_n-1) (X_(t_(i+1)^n) - X_(t_i^n))^2 delta_(t_i^n)(dif r). $

Let $D= QQ inter [0,t] union {t_i^n}_(n>=1,0<=i<=p_n)$. As a consequence of quadratic variation, for every $r in D$,
$ mu_n ([0,r]) arrow chevron.l X, X chevron.r_r $
in probability. With a diagonal argument, there exists a subsequence of values of $n$ such that for every $r in D$, $mu_n([0,r]) arrow chevron.l X, X chevron.r_r$ almost surely. This implies that the sequence of measures $mu_n$ converges almost surely to the measure $II_[0,t](r) dif chevron.l X, X chevron.r_r$ in distribution.

Because $F''(X_s)$ is a continuous function of $s$, 
$ integral_[0,t] F''(X_s) mu_n (dif s) arrow integral_0^t F''(X_s) dif chevron.l X, X chevron.r_s $
almost surely along the chosen subsequence. $qed$
]

== Lévy's Characterization of Brownian Motion

#state(number: "5.12", title: [Lévy's theorem])[
  Let $X$ be an adapted process with continuous sample paths. The following are equivalent:
  
  1. $X$ is a one-dimensional $(cal(F)_t)$-Brownian motion.
  
  2. $X$ is a continuous local martingale, and $chevron.l X, X chevron.r_t = t$ for every $t >= 0$.
]

#proof[
For the non-trivial direction, let $xi in RR$. Define the exponential process

$ cal(E)(i xi X)_t = exp(i xi X_t + 1/2 xi^2 t) $

By Itô's formula, $cal(E)$ is a complex continuous local martingale. Note that $abs(exp(i xi X_t))<=1$, it is therefore a true martingale. Hence, for every $0 <= s < t$,

$ E[exp(i xi X_t + 1/2 xi^2 t) | cal(F)_s] = exp(i xi X_s + 1/2 xi^2 s). $

Rearranging yields

$ E[exp(i xi (X_t - X_s)) | cal(F)_s] = exp(-1/2 xi^2 (t - s)). $

It follows that, for measurable $A in cal(F)_s$,

$ E[II_A exp(i xi (X_t - X_s))] = P(A) exp(-1/2 xi^2 (t - s)). $

When $A = Omega$, we have that the characteristic function of $X_t - X_s$ is that of a centered Gaussian variable with variance $t - s$. 

Furthermore, fix $A in cal(F)_s$ with $P(A) > 0$. Let $P_A$ denote the conditional probability on $A$. Then
$ P_A [exp(i xi (X_t - X_s))] = exp(-1/2 xi^2 (t - s)), $
Therefore, for any $f in C(RR, rp)$, we have $P_A [f(X_t - X_s)] = E[f(X_t - X_s)]$, or equivalently
$ E[II_A f(X_t - X_s)] = P(A) E[f(X_t - X_s)]. $
implying that $X_t - X_s$ is independent of the past filtration $cal(F)_s$.

It follows that, $X$ has stationary, independent Gaussian increments adapted to the filtration, and thus a $(cal(F)_t)$-Brownian motion starting at 0. $qed$
]

== Reflection principle \#2

With Lévy’s Characterization of Brownian Motion at hand, we present an alternate proof of the reflection principle, using stochastic integration.

#state(title: [Reflection principle \#2])[
Let $B_t$ be a standard Brownian motion and $T_a = inf{t >= 0 : B_t = a}$ for $a > 0$. The reflected process
$ W_t = cases(
  B_t &"if" t <= T_a,
  2a - B_t quad &"if" t > T_a
) $
is also a standard Brownian motion.
]

#proof[
Define the predictable process $X_s = II_({s <= T_a}) - II_({s > T_a})$. Note that the Itô integral
$ integral_0^t X_s d B_s = W_t $

Then $W_t$ is a continuous local martingale with quadratic variation $chevron.l W, W chevron.r_t = integral_0^t theta_s^2 d s = t$. By Lévy's characterization, $W_t$ is a standard Brownian motion. 
]

#bibliography("prob.yaml")

