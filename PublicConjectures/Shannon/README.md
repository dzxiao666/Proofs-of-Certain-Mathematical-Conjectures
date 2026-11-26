# Triple intersections in subdivided regular polygons

Orient the sides of a regular $n$-gon cyclically and divide each side into $k+1$ equal pieces. For each of the $k$ interior mark indices, join the corresponding marks on consecutive sides to draw an inscribed polygon. A triple intersection is a point in the relative interiors of three distinct drawn segments.

**Theorem.** For an integer $n\ge 3$, some choice of $k$ gives a triple intersection if and only if $n$ is 3, 4, or 6.

Scott R. Shannon posed the classification in 2022. [OEIS A357216](https://oeis.org/A357216) · [A357235](https://oeis.org/A357235) · [A357254](https://oeis.org/A357254) · [Lean theorem and proof](Proof.lean)

## Coordinates for a drawn segment

Put the vertices $v_i$ on the unit circle in cyclic order. Write $\theta=2\pi/n$ and $c=\cos\theta$, and read subscripts modulo $n$. At corner $i$ use the affine coordinates

```math
F_i(x,y)=v_i+x(v_{i+1}-v_i)+y(v_{i-1}-v_i).
```

The three vertices are noncollinear, so these coordinates are unique.

Let $t=j/(k+1)$ for $1\le j\le k$. Label by $(i,t)$ the segment with endpoints $F_i(0,t)$ and $F_i(1-t,0)$. In the cyclic orientation, both endpoints have fraction $1-t$ along their respective sides. As $t$ runs through the marks this describes all drawn segments.

A point at fraction $s$ along this segment from $F_i(0,t)$ has coordinates

```math
x=s(1-t),\qquad y=(1-s)t.
```

For $0<s<1$ these satisfy $x,y>0$ and $x+y<1$. Eliminating $s$ gives equation (1).

```math
x=1-t+y-\frac{y}{t}.
```

## Which corners can meet

Project onto the unit vector $v_i$. Its dot product with $v_i$ itself is $1$, with either adjacent vertex it is $c$, and with any other vertex it is at most $c$. Indeed, the smaller angular distance to any distinct vertex is at least $\theta$, and cosine decreases on $[0,\pi]$.

Every interior point of a segment at corner $i$ is a convex combination of $v_i$ and its two neighbors with positive weight $1-x-y$ at $v_i$. Its projection is therefore strictly greater than $c$. If $j$ is neither $i$ nor a neighbor of $i$, the triangle with vertices $v_{j-1},v_j,v_{j+1}$ does not contain $v_i$ among its vertices. All three project to at most $c$, so their triangle, including every segment at $j$, projects to at most $c$. Hence two segments that meet in their interiors belong to the same corner or to neighboring corners.

For $n\ge 5$, the cycle of corners has no three distinct pairwise adjacent vertices. So the three segments at any triple intersection lie at one corner or at two adjacent corners.

## Concurrence forces a rational cosine

The unit-circle vertices satisfy $v_{i-1}+v_{i+1}=2cv_i$. Substituting $v_{i+2}=2cv_{i+1}-v_i$ in $F_{i+1}(x,y)$ gives
$(y-x)v_i+(1+(2c-1)x-y)v_{i+1}$. Substituting $v_{i-1}=2cv_i-v_{i+1}$ in $F_i(1+2cx-y,x)$ gives the same expression. This yields the change of coordinates (2).

```math
F_{i+1}(x,y)=F_i(1+2cx-y,x).
```

Write the alleged common point as $F_i(X,Y)$, choosing $i,i+1$ to include all involved corners. A segment at $i$ imposes (1) on $(X,Y)$. A segment at $i+1$ with parameter $t$ has local coordinates $(Y,1+2cY-X)$ by (2). Substituting these coordinates into its line equation (1), and setting $q=1-t$, gives

```math
1+2cY-X=1-q+Y-Y/q.
```

Thus the segments from either corner impose equations of the same form

```math
U=1-q+Y-Y/q,
```

with $U=X$ and $q=t$ at $i$, or $U=1+2cY-X$ and $q=1-t$ at $i+1$. All these $q$ are rational numbers in $(0,1)$. Two distinct segments at one corner have distinct parameters, say $a$ and $b$. Subtracting their equations yields

```math
(a-b)\left(1-\frac{Y}{ab}\right)=0,
```

so $Y=ab$ and $U=(1-a)(1-b)$. Three distinct segments at a single corner would give $Y=ab=ad$ for three distinct parameters $a,b,d$, which is impossible since $a>0$.

It follows that two segments come from one corner and one from the other. The pair makes $Y=ab>0$ and its value of $U$ rational. The third segment, with rational parameter $d$, makes the other value of $U$ equal to $1-d+Y-Y/d$, which is rational as well. Adding the two values shows that $1+2cY$ is rational. Since $Y$ is positive and rational, $2c$ is rational.

## Restricting the number of sides

Let $z=e^{2\pi i/n}$ and let $w=z+z^{-1}=2c$. Define polynomials by $P_0(T)=2$, $P_1(T)=T$ and $P_{j+1}(T)=TP_j(T)-P_{j-1}(T)$. Induction gives $P_j(w)=z^j+z^{-j}$ and shows that $P_j$ is monic with integer coefficients for $j\ge1$. Since $z^n=1$, the rational number $w$ is a root of the monic integer polynomial $P_n(T)-2$, so the rational root theorem makes it an integer. For $n\ge5$ we have $0<\theta<\pi/2$ and hence $0<w<2$. Thus $w=1$, giving $\theta=\pi/3$ and $n=6$.

## Explicit intersections for three, four and six sides

In each row below, a pair $(t,s)$ specifies the mark parameter and the fraction along the segment. The first two segments are at corner $0$ and the third is at corner $1$. Their common point is reported in the coordinates of corner $0$.

| $n$ | $k$ | First $(t,s)$ | Second $(t,s)$ | Third $(t,s)$ | Common $(X,Y)$ |
| --- | --- | --- | --- | --- | --- |
| 3 | 5 | $(1/6,1/2)$ | $(1/2,5/6)$ | $(2/3,1/4)$ | $(5/12,1/12)$ |
| 4 | 5 | $(1/6,2/3)$ | $(1/3,5/6)$ | $(1/2,1/9)$ | $(5/9,1/18)$ |
| 6 | 9 | $(1/10,1/2)$ | $(1/2,9/10)$ | $(4/5,1/4)$ | $(9/20,1/20)$ |

To check each row, substitute into $(s(1-t),(1-s)t)$, then use (2) for the third segment with $2c=-1,0,1$, respectively. All the $t$ values are allowed marks, all the $s$ values lie strictly between zero and one, and the three segments in each row are distinct. This gives all three required examples. $\square$
