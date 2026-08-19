import Formalization.Books.Algebra.Unit72.Depth
import Formalization.Books.Algebra.Unit109.FiniteGlobalDimension

/-!
# Commutative Algebra, Chapter 111: Auslander--Buchsbaum

The source's depth values are represented by `Unit72.localDepth`, with values
in `ℕ∞`.  The projective dimension is Mathlib's canonical
`CategoryTheory.projectiveDimension`, whose values lie in `WithBot ℕ∞`; the
depths are therefore cast to that same ordered type in the formula below.
The finite-free resolution, short-exact-sequence depth inequalities, and
depth-drop interfaces used in the source proof are supplied by Chapters 71,
72, and 109.
-/

namespace Formalization.Books.Algebra.Unit111

open CategoryTheory
open Formalization.Books.Algebra.Unit72
open Formalization.Books.Algebra.Unit109

universe u

noncomputable section

/-! ## The Auslander--Buchsbaum formula -/

/-- **Auslander--Buchsbaum formula.**  For a nonzero finite module of finite
projective dimension over a Noetherian local ring, the depth of the ring is
the sum of the module's projective dimension and its depth. -/
/-
Proof roadmap:

* Keep the statement as written.
  `Formalization.Books.Algebra.Unit72.localDepth_eq_min_ext` in
  `Unit72/Depth.lean` requires exactly the local, Noetherian, finite, and
  nontrivial hypotheses present here, and
  `Formalization.Books.Algebra.Unit109.HasFiniteProjectiveDimension` in
  `Unit109/FiniteGlobalDimension.lean` is stated for the same
  `ModuleCat.{u} R`.  The two depths live in `ℕ∞`; the displayed casts put
  them in the canonical projective-dimension type `WithBot ℕ∞`.

* First prove a local depth-zero helper.  Convert `hpd` to
  `∃ d : ℕ, CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) d`
  with
  `Formalization.Books.Algebra.Unit109.hasFiniteProjectiveDimension_iff_exists_projective_dimension_bound`,
  choose the least `d` with `Nat.find`, and package minimality as
  `Formalization.Books.Algebra.Unit109.HasProjectiveDimensionExactly
  (ModuleCat.of R M) d`.  Also prove
  the small conversion lemma
  `projectiveDimension (ModuleCat.of R M) = (d : WithBot ℕ∞)` from
  `CategoryTheory.projectiveDimension_le_iff` and
  `CategoryTheory.projectiveDimension_ge_iff` (split `d = 0` to rule out a
  zero module).

* The depth-zero helper needs a minimal finite-free resolution of exact
  length `d`, together with the two inequalities
  `localDepth R M ≥ localDepth R R - d` and
  `(d : ℕ∞) ≤ localDepth R R`.  The complete construction to port locally is
  the block-commented section `Minimal finite free resolutions and depth` in
  `Unit109/FiniteGlobalDimension.lean`: its intended intermediate objects are
  `MinimalFiniteFreeResolution`,
  `MinimalFiniteFreeResolutionDepthInterface`,
  `exists_minimal_finite_free_cover`,
  `prependMinimalFiniteFreeResolution`,
  `exists_minimalFiniteFreeResolution`,
  `exists_minimalFiniteFreeResolutionDepthInterface`, and
  `MinimalFiniteFreeResolution.length_le_localDepth`.  These names are only
  text inside that block comment, not reusable declarations, so reproduce
  the helpers before this theorem (or first expose them in Unit109 in a
  separately authorized repair); do not try `exact
  Formalization.Books.Algebra.Unit109.auslander_buchsbaum_of_finite_projective_dimension`.
  Porting this block requires the focused import
  `Formalization.Books.Algebra.Unit102.WhatMakesAComplexExact` and opening
  `Formalization.Books.Algebra.Unit102`; Chapter 109 could not import that
  later chapter, but Chapter 111 can.

* For the minimal-resolution construction, lift a basis of
  `IsLocalRing.ResidueField R ⊗[R] M`; use
  `IsLocalRing.span_eq_top_of_tmul_eq_basis` for surjectivity and
  `LinearMap.ker_tensorProductMk` to put the kernel in the maximal ideal.
  Induct on exact projective dimension, using
  `Formalization.Books.Algebra.Unit109.projective_dimension_zero_iff_projective`
  and
  `Formalization.Books.Algebra.Unit85.projective_free_over_local_ring` at
  zero, and the
  `ShortComplex.ShortExact.hasProjectiveDimensionLT_X₁`/`X₃` lemmas for the
  exact dimension of the next syzygy.  Use
  `Formalization.Books.Algebra.Unit72.localDepth_shortExact` for
  the `depth_lower` induction and the finite-free-complex declarations
  `Formalization.Books.Algebra.Unit102.proposition_what_exact` and
  `Formalization.Books.Algebra.Unit102.ContainsRegularSequence` for the
  terminal rank-ideal argument.  The auxiliary fact that a nonzero finite
  free module has depth at least `localDepth R R` follows by induction on its
  positive rank, using `Fin.consLinearEquiv` and the same short-exact depth
  theorem.
  At module depth zero, `depth_lower` gives `localDepth R R ≤ d`, while
  `length_le_localDepth` gives the reverse inequality; convert their equality
  with the projective-dimension lemma from the preceding step.

* Prove the general formula by induction on the natural `e` supplied by
  `localDepth_eq_min_ext (R := R) (M := M)`.  The zero case is the
  preceding helper.  In the successor case, apply
  `regular_sequence_extend_to_localDepth` to `[]`; its positive length
  lets one write the sequence as `x :: xs`.  Extract
  `hxreg : IsSMulRegular M x` with
  `RingTheory.Sequence.isRegular_cons_iff`, and prove
  `hxmax : x ∈ IsLocalRing.maximalIdeal R` by observing that a unit `x` would
  make `Ideal.ofList (x :: xs) = ⊤`, contradicting the regular sequence's
  `top_ne_smul` field.

* Put `Q : Type u := QuotSMulTop x M`.  Install `Module.Finite R Q` by
  inference and
  `Nontrivial Q` with `nontrivial_quotSMulTop_of_mem_maximalIdeal M hxmax`
  from Mathlib's `RingTheory/Regular/RegularSequence.lean`.
  `localDepth_drops_by_one` and the known successor value give
  `localDepth R Q = (e : ℕ∞)`.  Mathlib's
  `ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular`
  (`RingTheory/Regular/ProjectiveDimension.lean`) gives
  `projectiveDimension (ModuleCat.of R Q) =
  projectiveDimension (ModuleCat.of R M) + 1`; use
  `hasFiniteProjectiveDimension_iff_projectiveDimension_ne_top` and a
  case split on the extended-natural value to deduce finite projective
  dimension for `Q`.  Apply the induction hypothesis to `Q`, rewrite the two
  depth/projective-dimension equalities, and finish with `Nat.cast_add` plus
  associativity and commutativity of addition.

The Unit110 theorem `regular_local_finite_free_resolution` is not a shortcut:
it assumes `IsRegularLocalRing R` (which is neither present nor implied by one
finite-PD module) and returns only a resolution-length upper bound.  Likewise
`regular_local_iff_finite_global_dimension` concerns the ring's global
dimension.  `Unit109.projective_dimension_resolution_criteria_noetherian_local`
does produce a nonminimal finite-free resolution, but does not supply the
minimality needed by the terminal rank-ideal argument.  Adding Unit110's
hypotheses here would improperly weaken the Auslander--Buchsbaum theorem.
-/
theorem auslander_buchsbaum
    {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hpd : HasFiniteProjectiveDimension (ModuleCat.of R M)) :
    ((localDepth R R : ℕ∞) : WithBot ℕ∞) =
      CategoryTheory.projectiveDimension (ModuleCat.of R M) +
        ((localDepth R M : ℕ∞) : WithBot ℕ∞) := by
  sorry

end

end Formalization.Books.Algebra.Unit111
