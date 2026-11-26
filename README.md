# Two OEIS conjectures in Lean 4

This repository gives machine-checked proofs of Scott R. Shannon’s classification of non-simple intersections and Dominic McCarty’s equality for threefold coverage by kings.

## Shannon’s regular polygons

Start with a regular polygon with $n \ge 3$ sides. Orient its sides cyclically and put $k$ equally spaced interior marks on each side. For each mark index, join the corresponding marks on consecutive sides. This draws $k$ inscribed polygons. A non-simple intersection is a point in the relative interiors of at least three distinct drawn segments.

`Shannon.classification` proves that **some subdivision has a non-simple intersection if and only if the number of sides is 3, 4, or 6**. The three witness theorems use 5, 5, and 9 marks per side respectively. Shannon recorded the conjecture in 2022. The OEIS entries also discuss counts of regions, vertices and edges. The formal theorem addresses the classification. [A357216](https://oeis.org/A357216) · [A357235](https://oeis.org/A357235) · [A357254](https://oeis.org/A357254)

The definitions in [Shannon.lean](PublicConjectures/Shannon.lean) start with Cartesian vertices on the real unit circle and affine interpolation along each segment. [Geometry.lean](PublicConjectures/Geometry.lean) uses projections to restrict which corners can contribute to an intersection. [Incidence.lean](PublicConjectures/Incidence.lean) turns concurrence in adjacent corner frames into the rationality of the cosine of the exterior angle. [Angle.lean](PublicConjectures/Angle.lean) uses roots of unity and algebraic integrality to restrict the angle. The converse is verified by explicit intersections.

## McCarty’s chessboards

Let $a(m)$ be the smallest number of kings on an $m \times m$ board such that every square is occupied or attacked by at least three distinct kings. Each square holds at most one king. Matthew Scroggs contributed the sequence, and Dominic McCarty proposed the equality for consecutive board sizes in January 2025. [A379759](https://oeis.org/A379759)

`Kings.mccarty` proves **a(3r + 1) = a(3r + 2) = 3(r + 1)²** for every integer $r \ge 1$. Cells with both zero-based coordinates in `A = {0, 3, …, 3r}` have pairwise disjoint closed king neighbourhoods. This forces at least three kings per such cell. To attain the lower bound, shift each coordinate of A one step to the right, moving its last element one step left if the right shift would leave the board. The resulting set B is disjoint from A, and each of A and B comes within one step of every coordinate. Place kings on the three disjoint products A × A, A × B, and B × A. Every square sees a king from each product. [Kings.lean](PublicConjectures/Kings.lean)

## Reproduce the verification

With Git and the Lean toolchain manager Elan installed, run the following in the project root. The first run needs network access for dependencies. The project pins Lean 4.19.0 and commits the Lake manifest for mathlib and its dependencies.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

[Audit.lean](Audit.lean) checks the expected transitive axiom lists of both main theorems and the three explicit geometric witnesses. Each list consists of propositional extensionality, classical choice and quotient soundness.

## Public-proof search

Search reviewed on 2026-11-26. The original records still describe Shannon’s classification as conjectural and McCarty’s equality as an observation. The search found no earlier public proof of either full statement or a Lean formalization of it. Priority remains undetermined. [Shannon’s source record](https://github.com/oeis/oeisdata/blob/571197984aeda7b8b680fe3a1f6a43f9898cd441/seq/A357/A357216.seq) · [McCarty’s source record](https://github.com/oeis/oeisdata/blob/30c383550c8059b1712df8e32827d3b203765933/seq/A379/A379759.seq)

Searches used the sequence identifiers, author names, regular polygon subdivision and triple concurrence, and threefold or k-tuple domination of king graphs and strong products of paths. GitHub repository searches used the identifiers in the name, description and README fields. Related public work includes the following.

- Talmon Silver gives a classification of intersections and a region count for the equilateral triangle instance. [OEIS A356984](https://oeis.org/A356984) · [Silver’s note](https://oeis.org/A356984/a356984.rtf)
- Matthew Scroggs treats the corresponding twofold chessboard coverage problem. [Friendly squares](https://www.mscroggs.co.uk/blog/114)
- Brešar, Henning and Klavžar give a related packing lower bound for integer domination. Their setting permits integer weights at one vertex. Here each square has capacity one, and the matching construction uses three distinct kings per covered square. [On Integer Domination in Graphs and Vizing-like Problems](https://users.fmf.uni-lj.si/klavzar/preprints/taiwan-2006.pdf)
