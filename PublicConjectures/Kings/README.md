# Threefold coverage by kings on a square board

On an $m\times m$ chessboard, a king covers its own square and every square it can reach in one move. Let $a(m)$ be the least number of kings needed so that every square is covered by at least three distinct kings, with at most one king per square.

**Theorem.** For every integer $r\ge 1$,

$$
a(3r+1)=a(3r+2)=3(r+1)^2.
$$

Dominic McCarty proposed the equality of the two chessboard minima in January 2025. [OEIS A379759](https://oeis.org/A379759) · [Lean theorem and proof](Proof.lean)

## Lower bound

Number the rows and columns from $0$ to $m-1$, where $m$ is either $3r+1$ or $3r+2$. Define

$$
A=\{0,3,6,\ldots,3r\}.
$$

Consider the $(r+1)^2$ test squares whose row and column both belong to $A$. Two distinct test squares differ by at least three in some coordinate. A king covering both would be within one of both coordinates, which would force them to differ by at most two. Thus no king can cover two test squares. Each test square needs three distinct kings, so any valid placement uses at least $3(r+1)^2$ kings.

## Placement attaining the bound

Define a second set of coordinates $B$ by shifting each member of $A$ up by one. When $m=3r+1$, the last shifted coordinate would fall off the board, so use $3r-1$ in its place. Explicitly,

$$
B=
\begin{cases}
\{3i+1:0\le i<r\}\cup\{3r-1\},&m=3r+1,\\
\{3i+1:0\le i\le r\},&m=3r+2.
\end{cases}
$$

Both sets have $r+1$ elements. They are disjoint because every member of $A$ is divisible by three, while every member of $B$ has remainder one or two. Every board coordinate lies within one of some element of $A$ and within one of some element of $B$. To see this, each set starts at $0$ or $1$, ends at $m-1$ or $m-2$, and has gaps of at most three between consecutive elements. Two integers at distance at most three cover all integers between them with their radius-one neighborhoods.

Place a king in each square in

$$
(A\times A)\ \cup\ (A\times B)\ \cup\ (B\times A).
$$

The three products are disjoint and each contains $(r+1)^2$ squares. For any target square, choose a nearby value in $A$ and a nearby value in $B$ for each of its two coordinates. Combining these values gives one king from each of the three products within one step in both coordinates. Thus every target square is covered by three distinct kings, and the total matches the lower bound. $\square$
