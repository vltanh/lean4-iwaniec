# Kinderlehrer and Stampacchia: the projection on a closed convex set

## Source

D. Kinderlehrer and G. Stampacchia, *An introduction to variational inequalities and their
applications*, SIAM Classics in Applied Mathematics 31, 2000 (reprint of Academic Press, 1980),
Chapter I, Lemma 2.1 and Theorem 2.3. The source is not freely available and has not been read; the
numbering is the paper's (arXiv:2609.28311, TeX line 412).

## Statements (`Projection.lean`)

- `External.KinderlehrerStampacchia.lemma2_1`: in a real Hilbert space, the projection of a point on
  a nonempty closed convex set exists and is unique.
- `External.KinderlehrerStampacchia.theorem2_3`: `y ∈ K` is the projection of `x` on the convex `K`
  if and only if `⟪x − y, v − y⟫ ≤ 0` for every `v ∈ K` (no completeness needed).

## How the paper uses them

In Lemma 4, in `L² (Q)`, with the constraint set `𝒞`: the projection `ζ` of `η` exists and is
unique, and `∫_Q (η − ζ)(ξ − ζ) ≤ 0` for every `ξ ∈ 𝒞` (`Agazzi.lemma4_exists`,
`Agazzi.lemma4_unique`, `Agazzi.lemma4_variationalInequality`).

## Arguments used

Mathlib: `exists_norm_eq_iInf_of_complete_convex` for existence, the sum of the two variational
inequalities for uniqueness, and `norm_eq_iInf_iff_real_inner_le_zero` for the characterization.
These are the standard arguments; whether they are the book's was not checked.
