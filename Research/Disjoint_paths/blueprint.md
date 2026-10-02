Let $d\ge 3$ and $0<\delta\le (8d)^{-1}$. There exists $n_0=n_0(d,\delta)$ such that, for every $n\ge n_0$, every

$$
x_n\in\partial D_n,\qquad x_{n+1}\in\partial D_{n+1},
$$

there are

$$
2d-|\{i:x_n(i)\ne0\}|-1
$$

paths starting at $x_n$ if $x_n\notin{\pm n e_i}_{i=1}^d$,

$$
2d-3
$$

paths starting at $x_n$ if $x_n=\pm n e_i$,

$$
|\{j:x_{n+1}(j)\ne0\}|-1
$$

paths starting at $x_{n+1}$ if $x_{n+1}\notin{\pm(n+1)e_j}_{j=1}^d$,

and one path starting at $x_{n+1}$ if $x_{n+1}=\pm(n+1)e_j$,

such that all these paths are edge-disjoint, are contained in

$$
\partial D_n\cup\partial D_{n+1},
$$

have lengths between

$$
\lfloor\delta^2(n+1)\rfloor
\quad\text{and}\quad
\lfloor2d\delta^2(n+1)\rfloor,
$$

and the endpoint of every path has distance at least

$$
\delta^3(n+1)
$$

from the union of all the other paths.

Proof.

Put

$$
N=n+1,\qquad L=\lfloor\delta^2N\rfloor.
$$

Since

$$
\frac{\delta^2N}{\delta^3N}=\delta^{-1}\ge 8d,
$$

we may choose $n_0$ so large that, for $n\ge n_0$,

$$
\frac{L}{3}-3\ge\delta^3N.
\tag{1}
$$

We also assume

$$
\frac nd\ge 16dL.
\tag{2}
$$

This follows from

$$
\delta^2\le \frac1{64d^2}.
$$

In particular, every point of $\partial D_n$ or $\partial D_{n+1}$ has a coordinate whose modulus is much larger than $L$.

Every path constructed below has length at most $6L$. Since $d\ge3$,

$$
6L
\le
\lfloor 6\delta^2N\rfloor
\le
\lfloor2d\delta^2N\rfloor.
\tag{3}
$$

We first record two elementary constructions.

For $z\in\partial D_n$, suppose, after reflections if necessary, that $z(p)>0$ and

$$
z(p)\ge 4L.
$$

An outward unit direction from $z$ is one of

$$
e_i\quad (z(i)>0),\qquad \pm e_i\quad (z(i)=0).
$$

For every outward direction $u\ne e_p$, define

$$
\gamma^u
=
z,\,
z+u,\,
z+u-e_p,\,
z+2u-e_p,\,
z+2u-2e_p,\ldots,
z+Lu-Le_p.
\tag{4}
$$

Thus the successive increments are

$$
u,-e_p,u,-e_p,\ldots,u,-e_p.
$$

The path has length $2L$ and stays in

$$
\partial D_n\cup\partial D_{n+1}.
$$

The coordinate in the direction $u$ moves monotonically by $L$, whereas every path corresponding to another outward direction either leaves that coordinate unchanged or moves it in the opposite direction. Hence

$$
\operatorname{dist}
\bigl(\gamma^u_{2L},\gamma^v\bigr)\ge L
\qquad (u\ne v).
\tag{5}
$$

The paths in (4) are edge-disjoint.

If $z$ has $s\ge2$ nonzero coordinates, the number of outward directions different from $e_p$ is

$$
(s-1)+2(d-s)=2d-s-1.
\tag{6}
$$

If $z$ is an axis point, this number is $2d-2$; in that case we simply discard one further path and retain $2d-3$ paths.

We shall refer to (4) as the inner fan.

There is an analogous outer fan. Let $y\in\partial D_{n+1}$ have at least two positive coordinates, let

$$
T=\{i:y(i)>0\},
$$

and choose $q\in T$ with

$$
y(q)=\max_i y(i).
$$

For $j\in T\setminus{q}$ we choose distinct outward directions $v_j$, none of which equals $e_j$ or $e_q$.

This can always be done. Indeed, if

$$
T\setminus\{q\}=\{j_1,\ldots,j_m\},\qquad m\ge2,
$$

take cyclically

$$
v_{j_\ell}=e_{j_{\ell+1}},
\qquad
v_{j_m}=e_{j_1}.
\tag{7}
$$

If $m=1$, then $|T|=2$, and since $d\ge3$ we may choose $h\notin T$ and put

$$
v_j=e_h.
$$

Define

$$
\eta^j:
\qquad
-e_j,\,
v_j,\,
-e_q,\,
v_j,\,
-e_q,\ldots,
v_j,\,
-e_q,
\tag{8}
$$

with $L$ occurrences of $v_j$. Thus $\eta^j$ has length $1+2L$.

The $v_j$-coordinate of the endpoint of $\eta^j$ exceeds its initial value by $L$, whereas every other path has that coordinate at most at its initial value. Therefore

$$
\operatorname{dist}
\bigl(\eta^j_{\rm end},\eta^k\bigr)\ge L
\qquad(j\ne k),
\tag{9}
$$

and the paths are edge-disjoint.

If

$$
y=Ne_q,
$$

we use the single path

$$
-e_q,\,
e_h,\,
-e_q,\,
e_h,\ldots,
e_h,\,
-e_q
\tag{10}
$$

for any $h\ne q$.

All statements remain true, with the obvious changes of signs, in an arbitrary orthant.

We shall also need a fan whose first coordinate moves downward.

Let $z\in\partial D_n$ have nonnegative coordinates. There is a family having precisely the required number of paths from $z$ such that

$$
\gamma(t)(1)\le z(1)
\qquad\text{for every vertex of every path},
\tag{11}
$$

and

$$
\gamma_{\rm end}(1)\le z(1)-L.
\tag{12}
$$

Moreover,

$$
\operatorname{dist}
\bigl(\gamma_{\rm end},\gamma'\bigr)
\ge \frac L3-2
\tag{13}
$$

for every two different paths in the family, and all lengths are at most $6L$.

If $z(1)\ge L$, this is immediate: discard the outward direction $e_1$, and for every remaining outward direction $u$ use

$$
(u,-e_1)^L.
\tag{14}
$$

For an axis point discard one additional direction.

Suppose now

$$
s:=z(1)<L.
$$

Choose

$$
p\in\{2,\ldots,d\}
$$

with $z(p)$ maximal. By (2),

$$
z(p)\gg L.
\tag{15}
$$

For an outward direction $u\ne e_1,e_p$, first repeat

$$
(u,-e_1)
$$

$s$ times. The first coordinate is then $0$. Continue with

$$
u,-e_p,-e_1,-e_p
\tag{16}
$$

repeated $L-s$ times. Thus the endpoint has first coordinate

$$
-(L-s)=z(1)-L,
$$

and the signed $u$-coordinate has changed by exactly $L$.

When $s=0$ and $u=-e_1$, the word (16) decreases the first coordinate twice in each block, which only improves the separation.

There remains the outward direction $e_p$. If $z$ is an axis point, it may be taken as the one additional discarded direction. Otherwise choose

$$
r\ne p,\qquad z(r)>0,
$$

and choose

$$
h\notin\{1,p\}.
$$

If $s=0$, begin this exceptional path by

$$
e_p,-e_r.
$$

If $s>0$, begin with $(e_p,-e_1)^s$. Once the first coordinate has reached $0$, repeat

$$
e_h,-e_p,-e_1,-e_p,-e_1,-e_p
\tag{17}
$$

$L-s$ times.

The exceptional path has length at most $6L$. Its first coordinate decreases twice as fast as that of the ordinary paths in the last part of the construction. Comparing either the first coordinate, the $h$-coordinate, or the $p$-coordinate gives

$$
\operatorname{dist}
\bigl(\gamma_{\rm end},\gamma'\bigr)
\ge \frac L3-2.
\tag{18}
$$

For example, against the ordinary $e_h$-path, the endpoint differences in the first and $h$ coordinates are respectively

$$
L-s,\qquad s,
$$

so their maximum is at least $L/2$. Against every other ordinary path one obtains

$$
\max\{L-s,|2s-L|\}\ge L/3.
$$

The same coordinate comparisons, with the time parameter left free on the other path, prove separation from the whole other path, not merely from its endpoint.

This proves (11)--(13).

We now construct the two collections simultaneously.

Case A: $x_n$ and $x_{n+1}$ lie in different orthants.

There is a coordinate $r$ such that

$$
x_n(r)x_{n+1}(r)<0.
$$

After reflection suppose

$$
x_n(r)>0>x_{n+1}(r).
\tag{19}
$$

Construct an inner fan from $x_n$ and an outer fan from $x_{n+1}$.

If

$$
x_n(r)+|x_{n+1}(r)|\ge5L,
\tag{20}
$$

then throughout both ordinary fans each $r$-coordinate can move toward $0$ by at most $L+1$. Hence every point of an $x_n$-path and every point of an $x_{n+1}$-path differ in their $r$-coordinates by at least

$$
3L-2.
\tag{21}
$$

Thus the two families are mutually disjoint and mutually separated.

Suppose instead

$$
x_n(r)+|x_{n+1}(r)|<5L.
\tag{22}
$$

The maximal coordinates $p$ of $x_n$ and $q$ of $x_{n+1}$ then satisfy

$$
p\ne r,\qquad q\ne r
$$

by (2). After each inner-fan path append

$$
(e_r,-\operatorname{sgn}(x_n(p))e_p)^L,
\tag{23}
$$

and after each outer-fan path append

$$
(-e_r,-\operatorname{sgn}(x_{n+1}(q))e_q)^L.
\tag{24}
$$

Consequently every endpoint from $x_n$ has $r$-coordinate at least

$$
x_n(r)+L,
$$

whereas every point of every path from $x_{n+1}$ has negative $r$-coordinate. Conversely every endpoint from $x_{n+1}$ has $r$-coordinate at most

$$
x_{n+1}(r)-L,
$$

whereas every point of every $x_n$-path has positive $r$-coordinate.

Hence the cross-family endpoint separation is at least $L$.

The private coordinates in the two ordinary fans still give separation inside each family. Thus Case A is complete.

Henceforth the points lie in the same orthant. After a common reflection we assume

$$
x_n(i),x_{n+1}(i)\ge0
\qquad(1\le i\le d).
\tag{25}
$$

Case B: $x_{n+1}$ is an axis point.

After permuting coordinates,

$$
x_{n+1}=Ne_1.
\tag{26}
$$

Suppose first that $x_n$ has a coordinate $p\ne1$ satisfying

$$
x_n(p)\ge4L.
\tag{27}
$$

Use $p$ as the reservoir coordinate in the inner fan. For the path from $x_{n+1}$ use

$$
-e_1,\,
-e_p,\,
-e_1,\,
-e_p,\ldots,
-e_p,\,
-e_1.
\tag{28}
$$

Its $p$-coordinate is negative, while every $x_n$-path has $p$-coordinate at least

$$
x_n(p)-L\ge3L.
$$

Thus all cross-family separations are at least $3L$.

This covers, in particular,

$$
x_n(1)<2L,
$$

because then a maximal coordinate outside the first coordinate satisfies (27), and it also covers an axis point $x_n=ne_p$ with $p\ne1$.

It remains to consider

$$
x_n(1)\ge2L.
\tag{29}
$$

If $x_n$ is not an axis point, choose a positive coordinate $h\ne1$ and use the inner fan with reservoir $1$. The path from $Ne_1$ is

$$
-e_1,\,
-e_h,\,
-e_1,\,
-e_h,\ldots.
\tag{30}
$$

Its endpoint has $h$-coordinate $-L$. Every $x_n$-path has nonnegative $h$-coordinate.

Conversely, the endpoint of an $x_n$-path whose private direction is $e_h$ has $h$-coordinate at least $x_n(h)+L$. Every other $x_n$-path has a private direction $u$ different from $e_1,e_h$, and the path (30) leaves the $u$-coordinate unchanged. Hence its endpoint is at distance at least $L$ from (30).

Finally, if

$$
x_n=ne_1,
$$

use the axis version of the inner fan with reservoir $1$ and take $-e_2$ to be the additional discarded direction. The surviving directions are

$$
e_2,\qquad \pm e_i\quad(3\le i\le d),
$$

together with one of the two directions in each remaining zero coordinate, giving exactly $2d-3$ paths. Use (30) with $h=2$. The same coordinate argument applies.

Thus all configurations with an axis point $x_{n+1}$ are covered.

Case C: $x_n$ and $x_{n+1}$ are neighbors.

After permuting coordinates,

$$
x_{n+1}=x_n+e_1.
\tag{31}
$$

The case $x_n=ne_1$ has already been covered, so assume otherwise.

Choose a positive coordinate $p$ of $x_n$ as follows. If

$$
x_n(1)\ge2L,
$$

put $p=1$. Otherwise choose a maximal positive coordinate among

$$
\{2,\ldots,d\}.
$$

Then

$$
x_n(p)\gg L.
\tag{32}
$$

First suppose $x_n(1)>0$. Construct the ordinary inner fan from $x_n$ with reservoir $p$.

Let

$$
T=\{j:x_{n+1}(j)>0\}.
$$

For each

$$
j\in T\setminus\{p\},
$$

construct a path from $x_{n+1}$ which decreases its $j$-coordinate by exactly $L$.

If

$$
s:=x_{n+1}(j)\ge L,
$$

use

$$
(-e_j,e_p)^L.
\tag{33}
$$

If $s<L$, first use

$$
(-e_j,e_p)^s
$$

and then

$$
(-e_p,-e_j)^{L-s}.
\tag{34}
$$

Because of (32), the $p$-coordinate remains positive. In either case,

$$
\eta^j_{\rm end}(j)=x_{n+1}(j)-L.
\tag{35}
$$

The path has length $2L$.

For $j\ne k$, the $j$-coordinate of $\eta^k$ is constant, whereas the endpoint of $\eta^j$ is lower by $L$. Thus

$$
\operatorname{dist}
(\eta^j_{\rm end},\eta^k)\ge L.
\tag{36}
$$

Now compare an inner-fan path $\gamma^u$ with $\eta^j$. If the private coordinate of $\gamma^u$ is $j$, then necessarily $x_n(j)>0$ and $u=e_j$, so

$$
\gamma^u_{\rm end}(j)=x_n(j)+L,
$$

whereas $\eta^j$ never has $j$-coordinate exceeding $x_{n+1}(j)$. The difference is at least $L-1$.

If the private coordinate is not $j$ or $p$, then $\eta^j$ leaves it unchanged, while the endpoint of $\gamma^u$ differs from its initial value by $L$.

Conversely, by (35), the endpoint of $\eta^j$ is at $j$-coordinate distance at least $L-1$ from every inner-fan path.

Thus all cross-family endpoint separations are at least $L-1$.

It remains to treat

$$
x_n(1)=0.
\tag{37}
$$

Then

$$
x_{n+1}(1)=1.
$$

If $x_n$ is an axis point $ne_p$, use the axis inner fan with reservoir $p$, and take $-e_1$ to be the additional discarded direction.

Suppose $x_n$ has at least two positive coordinates. In the ordinary inner fan with reservoir $p$, discard the direction $-e_1$. To keep the required number of paths, add one path whose first edge is $e_p$.

Choose

$$
r\ne p,\qquad x_n(r)>0,
$$

and

$$
h\notin\{1,p\}.
$$

Begin the exceptional path with

$$
e_p,-e_r
$$

and then repeat

$$
e_1,-e_p,e_h,-e_p
\tag{38}
$$

$L$ times.

Its endpoint has gained $L$ in both the first and $h$ coordinates. It is therefore at distance at least $L-1$ from every ordinary inner-fan path. Conversely, an ordinary $e_1$-path is separated from (38) by the $h$-coordinate, an ordinary $e_h$-path by the first coordinate, and every other ordinary path by its own private coordinate.

Now construct the $x_{n+1}$-paths by (33)--(34), indexed by

$$
T\setminus\{p\}.
$$

The path corresponding to $j=1$ ends at first coordinate

$$
1-L<0,
$$

whereas every $x_n$-path has nonnegative first coordinate. The remaining comparisons are exactly as above.

Thus the neighboring case is complete.

Case D: $x_{n+1}$ has at least two positive coordinates and

$$
\|x_{n+1}-x_n\|_1\ge2.
\tag{39}
$$

Some coordinate increases from $x_n$ to $x_{n+1}$. Permuting coordinates,

$$
x_{n+1}(1)>x_n(1).
\tag{40}
$$

Because the points are not neighbors, there also exists

$$
r\in\{2,\ldots,d\}
$$

such that

$$
x_n(r)>x_{n+1}(r).
\tag{41}
$$

Indeed,

$$
\sum_i\bigl(x_{n+1}(i)-x_n(i)\bigr)=1,
$$

and if all differences outside coordinate $1$ were nonnegative, equality could hold only for

$$
x_{n+1}=x_n+e_1.
$$

Put

$$
J=\{j\ge2:x_{n+1}(j)>0\}.
\tag{42}
$$

Since $x_{n+1}(1)>0$,

$$
|J|=|\{i:x_{n+1}(i)>0\}|-1,
$$

which is exactly the required number of paths from $x_{n+1}$.

We first consider

$$
x_{n+1}(1)\le N-4dL.
\tag{43}
$$

Then

$$
\sum_{j=2}^d x_{n+1}(j)\ge4dL.
$$

Hence there exists

$$
p\in J
$$

such that

$$
x_{n+1}(p)>4L.
\tag{44}
$$

Use the downward fan (11)--(13) at $x_n$. Thus every $x_n$-path satisfies

$$
\gamma(t)(1)\le x_n(1),
\qquad
\gamma_{\rm end}(1)\le x_n(1)-L.
\tag{45}
$$

For every $j\in J$ construct a path $\eta^j$ from $x_{n+1}$.

If

$$
x_{n+1}(j)\ge2L,
$$

use

$$
(-e_j,e_1)^{2L}.
\tag{46}
$$

Its length is $4L$, its first coordinate increases by $2L$, and its $j$-coordinate decreases by $2L$.

Suppose instead

$$
s:=x_{n+1}(j)<2L.
$$

Then $j\ne p$. Use

$$
(-e_j,e_1)^s
$$

until the $j$-coordinate becomes $0$. Put

$$
t=\left\lceil L-\frac s2\right\rceil.
$$

Continue with

$$
-e_p,-e_j,-e_p,e_1
\tag{47}
$$

repeated $t$ times.

By (44), the $p$-coordinate remains positive. The total length is

$$
2s+4t\le4L+4\le6L,
$$

and both the increase of the first coordinate and the decrease of the $j$-coordinate are at least

$$
s+t\ge L.
\tag{48}
$$

For $j,k\ne p$, $j\ne k$, the path $\eta^k$ does not change coordinate $j$, whereas the endpoint of $\eta^j$ has lowered that coordinate by at least $L$. Hence their endpoints are separated from the whole other path by at least $L$.

The only possible exception is the path indexed by $p$. By (44), it is of type (46). If $\eta^k$ is of type (47), the discrepancies in coordinates $1,p,k$ give

$$
\operatorname{dist}
\bigl(\eta^p_{\rm end},\eta^k\bigr)\ge L-2.
\tag{49}
$$

Indeed, if the differences in coordinates $1$ and $p$ become small, then (48) gives a difference at least $L$ in coordinate $k$. The reverse separation follows directly from coordinate $k$.

Thus the $x_{n+1}$-paths are edge-disjoint and mutually endpoint-separated.

Finally, every point of every $\eta^j$ satisfies

$$
\eta^j(t)(1)\ge x_{n+1}(1),
$$

while (45) gives

$$
\gamma_{\rm end}(1)\le x_n(1)-L.
$$

Since $x_{n+1}(1)\ge x_n(1)+1$,

$$
\operatorname{dist}
(\gamma_{\rm end},\eta^j)\ge L+1.
\tag{50}
$$

On the other hand, (48) gives

$$
\eta^j_{\rm end}(1)\ge x_{n+1}(1)+L-2,
$$

whereas every point of every downward-fan path has first coordinate at most $x_n(1)$. Hence

$$
\operatorname{dist}
(\eta^j_{\rm end},\gamma)\ge L-1.
\tag{51}
$$

This proves the result under (43).

It remains to consider

$$
x_{n+1}(1)>N-4dL.
\tag{52}
$$

If

$$
x_{n+1}(1)-x_n(1)\ge4L,
\tag{53}
$$

use an ordinary inner fan from $x_n$ and an outer fan from $x_{n+1}$ with reservoir coordinate $1$.

Every point of the inner fan has first coordinate at most

$$
x_n(1)+L,
$$

and every point of the outer fan has first coordinate at least

$$
x_{n+1}(1)-L.
$$

By (53),

$$
x_{n+1}(1)-L-(x_n(1)+L)\ge2L.
\tag{54}
$$

Thus the two families are separated by at least $2L$.

We are left with

$$
x_{n+1}(1)-x_n(1)<4L.
\tag{55}
$$

Combining (52) and (55),

$$
x_n(1)>N-(4d+4)L.
\tag{56}
$$

In particular, both first coordinates are much larger than all modifications below.

Take $r$ from (41).

Construct from $x_n$ the inner fan with reservoir coordinate $1$, omitting $e_1$. After every path append

$$
(e_r,-e_1)^L.
\tag{57}
$$

Because $x_n(r)>0$, the $r$-coordinate never decreases along any $x_n$-path, and every endpoint satisfies

$$
\gamma_{\rm end}(r)\ge x_n(r)+L.
\tag{58}
$$

The ordinary private directions still give mutual separation inside this family.

For every $j\in J$, first decrease coordinate $j$ by exactly $L$.

If

$$
s:=x_{n+1}(j)\ge L,
$$

use

$$
(-e_j,e_1)^L.
\tag{59}
$$

If $s<L$, use

$$
(-e_j,e_1)^s
$$

followed by

$$
(-e_1,-e_j)^{L-s}.
\tag{60}
$$

In either case the path is again on $\partial D_{n+1}$ after this part and its $j$-coordinate has decreased by exactly $L$.

Now append $2L$ two-step moves which decrease the $r$-coordinate by exactly $2L$: while the $r$-coordinate is positive use

$$
-e_r,e_1,
$$

and once it reaches $0$ use

$$
-e_1,-e_r.
\tag{61}
$$

Condition (56) guarantees that the first coordinate remains positive throughout.

Thus, for $j\ne r$,

$$
\eta^j_{\rm end}(r)=x_{n+1}(r)-2L,
$$

and, if $r\in J$,

$$
\eta^r_{\rm end}(r)=x_{n+1}(r)-3L.
\tag{62}
$$

Moreover every point of every $\eta^j$ satisfies

$$
\eta^j(t)(r)\le x_{n+1}(r).
\tag{63}
$$

The private $j$-coordinate created by (59)--(60) separates two paths with indices $j,k\ne r$. If one of the paths is $\eta^r$, its additional $L$ displacement in coordinate $r$ separates its endpoint from every other path; in the reverse direction the other path's private coordinate gives the separation. Hence all the $\eta^j$ are edge-disjoint and mutually endpoint-separated by at least $L$.

Finally, using (41), (58), and (63),

$$
\gamma_{\rm end}(r)
\ge x_n(r)+L
>
x_{n+1}(r)+L
\ge \eta^j(t)(r)+L,
$$

so every $x_n$-endpoint is at distance at least $L$ from every $x_{n+1}$-path.

Conversely, by (62),

$$
\eta^j_{\rm end}(r)
\le x_{n+1}(r)-2L
<
x_n(r)-2L,
$$

while every point of every $x_n$-path has $r$-coordinate at least $x_n(r)$. Hence every $x_{n+1}$-endpoint is at distance at least $2L$ from every $x_n$-path.

This completes Case D.

The four cases exhaust all possibilities:

$$
\begin{array}{ll}
\text{different orthants},\\
\text{same orthant and }x_{n+1}\text{ is an axis point},\\
\text{same orthant and }x_n,x_{n+1}\text{ are neighbors},\\
\text{same orthant, }x_{n+1}\text{ has at least two nonzero coordinates, and they are not neighbors}.
\end{array}
$$

The number of paths in every case is exactly the number stated in the lemma. Every path lies in

$$
\partial D_n\cup\partial D_{n+1},
$$

and every length lies between $L$ and $6L$, hence, by (3), between

$$
\lfloor\delta^2N\rfloor
\quad\text{and}\quad
\lfloor2d\delta^2N\rfloor.
$$

All same-family and cross-family endpoint separations obtained above are at least

$$
\frac L3-3.
$$

By (1),

$$
\frac L3-3\ge\delta^3N.
$$

Therefore the endpoint of every path is at least $\delta^3(n+1)$ away from the union of all the other paths.

This proves the lemma.
