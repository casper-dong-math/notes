#import "@preview/touying:0.7.1": *
#import themes.stargazer: *

#show: stargazer-theme.with(
  aspect-ratio: "16-9",
  config-common(show-bibliography-as-footnote: bibliography("prob.yaml")),
  config-info(
    title: [Introduction to Brownian Motion and Itô Calculus],
    subtitle: [Course project for Honors Theory of Probability, Spring 2026],
    author: [Casper Dong, Xialei Huang, Hans Wang],
    date: datetime(day: 6, month: 5, year: 2026),
    institution: [NYU Shanghai],
    contact: [{casper.dong, xialei.huang, sw6630}\@nyu.edu],
  ),
)

#set heading(numbering: "1.A.I")

#let rp=$RR_(>=0)$

#title-slide()

#magic.bibliography(title: none)

= Brownian Motion

== Gaussian spaces

#tblock(title: [Centered Gaussian variable])[
A real random variable $X$ is said to be a _centered Gaussian variable_ with $cal(N) (0,sigma^2)$-distribution if its law has density

$ p_X (x) = 1 / (sqrt(2 pi sigma^2)) exp(-x^2 / (2 sigma^2)) $
]

#tblock(title: [Centered Gaussian space])[
A _centered Gaussian space_ is a closed linear subspace of $L^2(Omega, cal(F), P)$ which contains only centered Gaussian variables.
]

#pagebreak()
#tblock(title: [Orthogonality $<=>$ Independence])[
Let $H$ be a centered Gaussian space and let $(H_i)_(i in I)$ be a collection of linear subspaces of $H$. Then the subspaces $H_i, i in I$, are (pairwise) orthogonal in $L^2$ if and only the $sigma$-fields $sigma(H_i), i in I$, are independent.
]

_Example_ : Finite linear combination of independent centered Gaussian variable.

_Counter-example_ : Let $X tilde cal(N) (0,1)$, $c$ independent of $X$ with $P(c=-1)=P(c=1)=1\/2$. Then $X'=c X tilde cal(N) (0,1)$, and $chevron.l X, X' chevron.r_(L^2)=E[X X']=E[c] E[X^2]=0$. Nonetheless $X$ and $X'$ are not independent.

== Gaussian white noise

#tblock(title: [Gaussian white noise])[
Let $(E, cal(E))$ be a measure space, and let $mu$ be a $sigma$-finite measure on $(E, cal(E))$. A _Gaussian white noise with intensity_ $mu$ is an isometry $G$ from $L^2(E, cal(E), mu)$ into a centered Gaussian space.
]

#tblock(title: [Existence of Gaussian White Noise])[
Let $(E, cal(E))$ be a measure space, and let $mu$ be a $sigma$-finite measure on $(E, cal(E))$. There exists, on an appropriate probability space $(Omega, cal(F), P)$, a Gaussian white noise with intensity $mu$.
]

== Pre-Brownian motion

#tblock(title: [Pre-Brownian motion])[
Let $G$ be a Gaussian white noise on $bb(R)_+$ whose intensity is Lebesgue measure. The random process $(B_t)_(t in bb(R)_+)$ defined by

$ B_t = G(II_[0,t]) $

is called _pre-Brownian motion_.
]

#pagebreak()
#tblock(title: [Equivalent formulations of pre-Brownian motion])[
Let $(X_t)_(t >= 0)$ be a (real-valued) random process. The following properties are equivalent:

1. $(X_t)_(t >= 0)$ is a pre-Brownian motion; \
2. $X_0 = 0$ a.s., and, for every $0 <= s < t$, the random variable $X_t - X_s$ is independent of $sigma(X_r, r <= s)$ and distributed according to $cal(N)(0, t - s)$; \
3. $X_0 = 0$ a.s., and, for every choice of $0 = t_0 < t_1 < dots < t_p$, the variables $X_(t_i) - X_(t_(i-1)), 1 <= i <= p$ are independent, and, for every $1 <= i <= p$, the variable $X_(t_i) - X_(t_(i-1))$ is distributed according to $cal(N)(0, t_i - t_(i-1))$.
]

== Continuity of Sample Path

#tblock(title: [Sample path])[
Let $(X_t)_(t in T)$ be a random process with values in $E$. The _sample paths_ of $X$ are the mappings $t |-> X_t (omega)$ obtained when fixing $omega in Omega$. The sample paths of $X$ thus form a collection of mappings from $T$ into $E$ indexed by $omega in Omega$.
]

#pagebreak()
#tblock(title: [Modification])[
Let $(X_t)_(t in T)$ and $(tilde(X)_t)_(t in T)$ be two random processes indexed by the same index set $T$ and with values in the same metric space $E$. We say that $tilde(X)$ is a _modification_ of $X$ if

$ forall t in T, quad P(tilde(X)_t = X_t) = 1. $
]

#tblock(title: [Indistinguishablity])[
The process $tilde(X)$ is said to be _indistinguishable_ from $X$ if there exists a negligible subset $N$ of $Omega$ such that

$ forall omega in Omega \\ N, forall t in T, quad tilde(X)_t (omega) = X_t (omega). $
]

#pagebreak()
#tblock(title: [Kolmogorov's lemma])[
Let $X = (X_t)_(t in I)$ be a random process indexed by a bounded interval $I$ of $bb(R)$. Assume that there exist three reals $q, epsilon, C > 0$ such that, for every $s, t in I$,

$ E[abs(X_s-X_t)^q] <= C |t - s|^(1+epsilon). $

Then, there is a modification $tilde(X)$ of $X$ whose sample paths are Hölder continuous with exponent $alpha$ for every $alpha in (0, epsilon/q)$ i.e. for every $omega in Omega$ and every $alpha in (0, epsilon/q)$, there exists a finite constant $C(alpha, omega)$ such that, for every $s, t in I$,

$ abs(tilde(X)_s (omega) - tilde(X)_t (omega)) <= C(alpha, omega) |t - s|^alpha. $

In particular, $tilde(X)$ is a modification of $X$ with continuous sample path, which is unique up to indistinguishability.
]

== Brownian motion

#tblock(title: [Existence of continuous modification of pre-Brownian motion])[
Let $B = (B_t)_(t >= 0)$ be a pre-Brownian motion. The process $B$ has a modification whose sample paths are continuous, and even locally Hölder continuous with exponent $1/2 - delta$ for every $delta in (0, 1/2)$. 
]
*Proof* on the board.

#tblock(title: [Brownian motion @lg])[
A process $(B_t)_(t >= 0)$ is a _Brownian motion_ if:
1. $(B_t)_(t >= 0)$ is a pre-Brownian motion.
2. All sample paths of $B$ are continuous.
]

/*
If $s < t$, the random variable $B_t - B_s tilde cal(N)(0, t - s) tilde sqrt(t-s) X$ where $X tilde cal(N)(0, 1)$. Consequently, for every $q > 0$,

$ E[abs(B_t - B_s)^q] = E[abs(X)^q] (t - s)^(q/2) $

where $E[abs(X)^q] < oo$. Taking $q > 2$, we can apply Theorem 2.9 with $epsilon = q/2 - 1$. It follows that $B$ has a modification whose sample paths are locally Hölder continuous with exponent $alpha$ for every $alpha < (q - 2)/(2q)$. If $q$ is large we can take $alpha$ arbitrarily close to $1/2$. 
*/

== The Wiener measure

Equip $C(rp, RR)$ with the pullback $sigma$-algebra of ${w mapsto w(t)}_(t >=0)$, denoted as $cal(C)$.

#tblock(title: [Wiener measure])[
The Wiener measure on $C(rp, RR)$ is the pushforward of $P$ under \

$ (B_t)_(t>=0): omega mapsto [t mapsto B_t (omega)] $

the sample path at $omega$. Check that the map is indeed measurable.
]

The uniqueness of Wiener measure follows from the finite dimensional marginal distribution of (pre)-Brownian motion.

#pagebreak()
#tblock(title: [Canonical construction of Brownian motion])[
Let the probability space be the Wiener measure $(C(rp, RR), cal(C), W)$. Then the canonical process

$ X_t (w)=w(t), t>=0, w in C(rp, RR) $

is a Brownian motion, called the _canonical construction_.
]

== Reflection principle \#1

#tblock(title: [Strong Markov property])[
Let $T$ be a stopping time. We assume that $P(T < oo) > 0$ and we set, for every $t >= 0$,

$ B_t^((T)) = II_({T < oo}) (B_(T+t) - B_T). $

Then under the probability measure $P(dot.c | T < oo)$, the process $(B_t^((T)))_(t >= 0)$ is a Brownian motion independent of $cal(F)_T$.
]

#pagebreak()
#tblock(title: [Reflection principle \#1])[
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

= Itô Calculus

== Progressive processes
#tblock(title: [Progressive measurability])[
A random process $X = (X_t)_(t >= 0): rp times Omega -> RR$ is _progressively measurable_ with respect to a filtration $(cal(F)_t)_(t >= 0)$ if, for every $t >= 0$, the restriction $X | [0, t] times Omega$ is $cal(B)([0, t]) times.o cal(F)_t$-measurable. 
]

#tblock(title: [Progressive $sigma$-algebra])[
The _progressive $sigma$-algebra_ on $rp times Omega$, denoted as $cal(P)$, is the $sigma$-algebra formed by all subsets $A subset bb(R)_+ times Omega$ such that, for every $t >= 0$,
$ A inter ([0, t] times Omega) in cal(B)([0, t]) times.o cal(F)_t. $
]

*Fact* $(X_t)_(t>=0)$ is progressively measurable $<=>$ $X$ is $cal(P)$-measurable.

== Itô Integral

Let $L^2 (Omega, (cal(F)_t)_(t>=0), P)$ be the space of progressively measurable processes $X$ such that 
$ norm(X)^2_(L^2 (Omega, (cal(F)_t)_(t>=0), P)) := E[integral_0^oo X_s^2 dif s] < oo. $

Formally, the space is $L^2 (rp times Omega, cal(P), m times.o P)$, where $cal(P)$ is the progressive $sigma$-algebra. 

For step process $sum_(i=0)^(n-1) X_i II_((t_i, t_(i+1)])(t)$ where $X_i$ is $cal(F)_t_i$-measurable, the Itô integral reads
$ integral_0^oo sum_(i=0)^(n-1) X_i II_((t_i, t_(i+1)])(t) dif B_s := sum_(i=0)^(n-1) X_i (B_(t_(i+1)) - B_(t_i)). $

*Fact* The space of step processes is dense in $L^2 (Omega, (cal(F)_t)_(t>=0), P)$.

#pagebreak()
By independent increments, the integral satisfies the _Itô isometry_
$ E[integral_0^oo H^2 dif s] = E[(integral_0^oo H dif B_s)^2] $

for step process $H$. Therefore, the integral on step processes uniquely extends to a continuous linear isometry from $L^2 (Omega, (cal(F)_t)_(t>=0), P)$ into $L^2(Omega, cal(F), P)$, which defines the Itô Integral. The Itô isometry thus holds for any $H in L^2 (Omega, (cal(F)_t)_(t>=0), P)$.

*Fact* $integral_0^t H dif B_s$ is a martingale. Moreover, there exists a continuous modification of it, unique up to indistinguishablity.

== Itô's Lemma
#tblock(title: [Itô's Lemma, first version @pm])[
Let $f in C^2 (RR)$. Then for all $t>=0$, 

$ f(B_t) - f(B_0) = integral_0^t f'(B_s) dif B_s + 1/2 integral_0^t f''(B_s) dif s $
]

*Sketch* For partition $Pi_n$ of $[0,t]$,

$ f(B_t) - f(B_0) = sum_(i=0)^(n-1) f(B_(t_(i+1))) - f(B_t_i) = sum_(i=0)^(n-1) f'(B_(t_i)) Delta B_i + 1/2 f''(B_(t_i)) (Delta B_i)^2 + R_i $

where $Delta B_i=B_t_(i+1)-B_t_i$, $R_i = 1/2 (f''(xi_i) - f''(B_(t_i))) (Delta B_i)^2$ for some $xi_i in (B_t_i, B_t_(i+1))$.


== Reflection principle \#2

#tblock(title: [Lévy’s Characterization of Brownian Motion])[
Let $(X_t)_(t>=0)$ be a continuous local martingale with $X_0=0$ a.s. If $X$ has quadratic variation $chevron.l X, X chevron.r_t=t$, then $(X_t)_(t>=0)$ is a Brownian motion starting from $0$.
]

#tblock(title: [Reflection principle \#2])[
Let $B_t$ be a standard Brownian motion and $T_a = inf{t >= 0 : B_t = a}$ for $a > 0$. The reflected process
$ W_t = cases(
  B_t &"if" t <= T_a,
  2a - B_t quad &"if" t > T_a
) $
is also a standard Brownian motion.
]

#pagebreak()
*Proof* Define the predictable process $X_s = II_({s <= T_a}) - II_({s > T_a})$. Note that the Itô integral
$ integral_0^t X_s d B_s = W_t $

Then $W_t$ is a continuous local martingale with quadratic variation $chevron.l W, W chevron.r_t = integral_0^t theta_s^2 d s = t$. By Lévy's characterization, $W_t$ is a standard Brownian motion. 
