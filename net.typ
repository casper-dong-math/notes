#import "lib.typ":*
#show title: set text(size: 18pt)
#show title: set align(center)

#title[
  Notes on Universal Nets in Functional Analysis
]

#let dist=$op("d")$

\
In the field of functional analysis, the proofs of many classical compactness theorems such as Banach-Alaoglu, Arzelà-Ascoli, and Helly's selection theorem are traditionally quite daunting. There is this crucial step of embedding the space into a massive product space, invoking Tychonoff's theorem, and showing compatibility between the original topology and the subspace topology. However, there is a powerful alternative framework that completely bypasses this topological scaffolding: the theory of *universal nets* (or ultranets). This viewpoint is analogous to the usage of sequences and nets in analysis: a topology, viewed dynamically, corresponds to the convergence behavior of sequences/nets, contrary to the usual static defintion of open sets.

In this note, we will define universal nets, state their remarkable properties, and see how they simplify several some classical proofs.

= Definitions and Core Properties

Recall that a *net* is a generalization of a sequence, defined as a map from a directed set $A$ into a topological space $X$, denoted $(x_alpha )_(alpha in A)$.

#state(type: "def", title: "Universal Net")[
  A net $(x_alpha )$ in a set $X$ is called a *universal net* if, for every subset $E subset X$, the net is either eventually in $E$ or eventually in $X - E$.
]

Intuitively, a universal net is "decisive." It never oscillates back and forth between two disjoint sets. This maximal decisiveness grants universal nets desirable convergence properties.

#state(type: "thm", title: "Existence")[
  Every net in $X$ has a universal subnet. 
]

#remark[
  Proof omitted, see @ped Theorem 1.3.8. Note that the statement is equivalent to the Axiom of Choice. 
]

#state(type: "prop")[
If $(x_alpha )$ is a universal net in $X$ and $f : X -> Y$ is any map, then $(f (x_alpha ))$ is a universal net in $Y$.
]

#proof[
Consider preimage of $U$ and $Y - U$ in $X$. $(x_alpha )$ is eventually in either preimages, therefore $(f (x_alpha ))$ is eventually in either $U$ or $Y-U$.
]

#state(type: "prop")[
If a universal net $(x_alpha )$ has a cluster point $x in X$, it must converge to $x$.
]

#proof[
If the net frequently visits a neighborhood $U$ of $x$, it cannot be eventually in $X - U$. By universality, it must therefore be eventually in $U$.
]

#state(type: "thm", title: "Compactness formulation")[
A topological space $X$ is compact if and only if every universal net in $X$ converges.
]

#proof[
$X$ compact $<=>$ Every net in $X$ has a cluster point $<=>$ Every universal net in $X$ converges \ (by existence of universal subnet).
]

#state(type: "cor")[
A subspace $Y$ of $X$ is relatively compact if and only if every universal net in $Y$ converges in $X$.
]

= Applications

Let us now apply this machinery. Notice how in each proof, the strategy is identical: pass to a universal subnet, evaluate it pointwise in a compact space where it is forced to converge, and observe that algebraic and/or topological properties trivially survive the limit.

#state(title: "Tychonoff's Theorem", number: "0")[
$X = Pi_(i in I) X_i$, the product of compact topologies $(X_i)_(i in I)$ is compact.
]

#proof[
Let $(x_alpha )$ be a universal net in the product space $X$. We wish to show it converges. For each index $i in I$, the projection map $pi_i : X -> X_i$ yields a net $pi_i (x_alpha )$ in $X_i$ which is a universal. Because $X_i$ is compact Hausdorff, this universal net converges unique to $c_i in X_i$. Thus, the original net $(x_alpha )$ converges pointwise to the $c = (c_i )_(i in I)$ in $X$ i.e. in product topology. Hence $X$ is compact. $qed$
]

#state(title: "The Banach-Alaoglu Theorem", number: "1")[
Let $V$ be a normed vector space. The closed unit ball $overline(BB)_(V^*)$ of the topological dual space $V^*$ is compact in the weak-\* topology.
]

#proof[
Let $(f_alpha )$ be a net in $overline(BB)_(V^*)$. Pass to a universal subnet $(f_beta )$. For any vector $v in V$, the scalar net $(f_beta (v))$ is a universal net in the compact disk $norm(v) overline(BB)$. Then $(f_beta (v))$ converges uniquely to, say, $c (v)$.

It suffice to check that $c: V->FF$ belongs to $overline(BB)_(V^*)$. Trivially $c$ is linear. In addition, $abs(c (v)) <= norm(v)$ is preserved by the limit. Thus $c in B^*$. Then the subnet converges to $f$ in the weak-\* topology. $qed$
]

#state(title: "Arzelà-Ascoli Theorem", number: "2")[
Let $X$ be an LCH and $Y$ metrizable. If a family of continuous maps $F subset C (X, Y)$ satisfies

1. Pointwise relatively compact i.e. ${f(x): f in F}$ is relatively compact, $forall x in X$;

2. Equicontinuous i.e. Given $x in X$ and $epsilon>0$, there exists $U_x$ an open neighborhood of $x$ such that $dist(f(x), f(y)) < epsilon$, $forall y in U_x, forall f in F$.

Then $F$ is relatively compact in the compact-open topology of $C (X,Y)$.
]

#proof[
Let $(f_alpha )$ be a universal net in $F$. For each $x in X$, the net $f_alpha (x)$ is a universal net in its relatively compact image, and therefore converges uniquely to some limit $f (x)$ in $Y$. This gives us a pointwise limit $f : X -> Y$.

By equicontinuity of $F$, for any $x in X$ and $epsilon > 0$, there exists a neighborhood $U_x$ of $x$ such that $d (f_alpha (x), f_alpha (y)) < epsilon$ for all $y in U_x$ and all $alpha$. Taking the limit on $alpha$ yields $d (f (x), f (y)) <= epsilon$, and thus $f$ is continuous.

Furthermore, on any compact set $K subset X$, equicontinuity along with the pointwise convergence of the universal net upgrades the convergence to uniform convergence via a standard finite subcover argument (check!). Thus $f_alpha -> f$ uniformly on compact sets i.e. in the compact-open topology. $qed$
]

#state(title: "Generalized Helly's Selection Theorem", number: "3")[
Let $X$ be a partially ordered set, and $Y$ a compact space equipped with a closed partial order. Then a net of increasing (resp. decreasing) functions $f_alpha : X -> Y$ possesses a pointwise convergent subnet whose limit is increasing (resp. decreasing).
]

#proof[
Pass to a universal subnet $(f_beta )$. For each $x in X$, $f_beta (x)$ is a universal net in the compact space $Y$, so it converges to some $f (x) in Y$. Check that $f$ is monotone. Let $x <= y$ in $X$. For all $beta$, we have $f_beta (x) <= f_beta (y)$. Because the order relation in $Y$ is a closed subset of $Y times Y$, taking limit preserves the relation, yielding $f (x) <= f (y)$. $qed$
]

#remark[
In the classical Helly's Selection theorem, we take $X=RR$ and $Y=[-M,M]$, both with total order. The theorem claims the existence of a monotone pointwise convergent subsequence from a sequence, rather than that of a subnet from a net. To reduce the subnet to a subsequence, consider convergence on $J union QQ$ where $J$ is the set of discontinuity of $f$, which is countable. Thus $[-M,M]^(J union QQ)$ is metrizable, and there exists a subsequence converging pointwise on $J union QQ$. To conclude, exploit the density of $J union QQ$ to demonstrate pointwise convergence on $RR$.
]

= The Stone-Čech Compactification

The connection between universal nets and the Stone-Čech compactification $beta X$ of a completely regular topological space $X$ is profound. Usually, $beta X$ is constructed by embedding $X$ into the massive product space of the form $[0,1]^(C (X))$.

However, we can explicitly construct $beta X$ using only universal nets. If a universal net in $X$ diverge, we define the points of the boundary $beta X - X$ as the equivalence classes of divergent universal nets, where two universal nets are equivalent if they assign the same limit to every bounded continuous function on $X$.

In the case where $X$ is a discrete space (like the natural numbers $NN$), universal nets are entirely synonymous with *ultrafilters*. The points of the Stone-Čech compactification $beta NN$ are exactly the ultrafilters on $NN$. The original points in $NN$ correspond to principal (convergent) ultrafilters, while the uncountably infinite points in the corona $beta NN - NN$ correspond exactly to the non-principal (divergent) universal subnets.

#bibliography("real.yaml")
