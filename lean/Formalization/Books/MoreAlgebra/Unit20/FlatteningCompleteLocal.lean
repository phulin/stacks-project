import Formalization.Books.MoreAlgebra.Unit18.FlatteningLocalBase
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# More on Algebra, Chapter 20: Flattening over a Noetherian complete local ring

The local flattening ideal is expressed using the canonical stalkwise
flatness predicate from Chapter 18.  The first lemma applies that predicate to
the quotient triple `R / I → S / IS`; the two base-change lemmas use the
unquotiented predicate directly, as in the source's condition
`M_q` flat over the base.
-/

namespace Formalization.Books.MoreAlgebra.Unit20

open scoped TensorProduct

universe u

noncomputable section

/-! ## Quotient form of the stalkwise condition -/

/-- The source's flatness condition for the quotient triple
`R / I → S / IS`, along the image of an ideal `J` of `R`.

The quotient ring map and quotient module are Mathlib's canonical ones.  The
module quotient is taken by `IS • M` as an `S`-submodule, so it carries the
canonical `S / IS`-action needed by `flatAtPrimesOver`.
-/
def flatAtPrimesOverQuotient
    {R S M : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (I J : Ideal R) : Prop :=
  letI : Algebra R S := f.toAlgebra
  letI : Module R M := Module.compHom M f
  letI : IsScalarTower R S M := SMul.comp.isScalarTower f
  Formalization.Books.MoreAlgebra.Unit18.flatAtPrimesOver
    (M := M ⧸ ((I.map f) • (⊤ : Submodule S M)))
    (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)
    (J.map (Ideal.Quotient.mk I))

/-- An ideal satisfying the existence and minimality conclusion of the first
complete-local flattening lemma. -/
def IsCompleteLocalFlatteningIdeal
    {R S M : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [AddCommGroup M] [Module S M]
    (f : R →+* S) (I : Ideal R) : Prop :=
  I ≤ IsLocalRing.maximalIdeal R ∧
    flatAtPrimesOverQuotient (M := M) f (IsLocalRing.maximalIdeal R) I ∧
      ∀ J : Ideal R,
        flatAtPrimesOverQuotient (M := M) f (IsLocalRing.maximalIdeal R) J → I ≤ J

/-! ## Flattening over a complete local Noetherian ring -/

/-- A finite module over a Noetherian algebra over a complete local Noetherian
ring has a smallest quotient ideal whose closed-fibre stalks are flat. -/
theorem exists_isCompleteLocalFlatteningIdeal
    {R S M : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [AddCommGroup M] [Module S M]
    [IsNoetherianRing S] [Module.Finite S M]
    (f : R →+* S) :
    ∃ I : Ideal R, IsCompleteLocalFlatteningIdeal (M := M) f I := by
  sorry

/-- For a Noetherian local target, the closed-subset flatness condition after
base change is equivalent to annihilating the complete-local flattening ideal. -/
theorem completeLocalFlatteningIdeal_property_by_noetherian_local_base_change
    {R S R' M : Type u} [CommRing R] [CommRing S] [CommRing R']
    [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [AddCommGroup M] [Module S M]
    [IsNoetherianRing S] [Module.Finite S M]
    (f : R →+* S) (I : Ideal R)
    (hI : IsCompleteLocalFlatteningIdeal (M := M) f I)
    (φ : R →+* R') [IsLocalRing R'] [IsNoetherianRing R'] [IsLocalHom φ] :
    Formalization.Books.MoreAlgebra.Unit18.flatAtPrimesOver
        (M := Formalization.Books.Algebra.Unit14.baseChangeModule
          (M := M) f φ)
        (Formalization.Books.Algebra.Unit14.baseChangeRingMap f φ)
        (IsLocalRing.maximalIdeal R') ↔
      I.map φ = ⊥ := by
  sorry

/-- For a finite-type algebra map, the same universal property holds after
arbitrary local base change; the target need not be Noetherian. -/
theorem completeLocalFlatteningIdeal_universal_property
    {R S R' M : Type u} [CommRing R] [CommRing S] [CommRing R']
    [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [AddCommGroup M] [Module S M]
    [IsNoetherianRing S] [Module.Finite S M]
    (f : R →+* S) (hf : RingHom.FiniteType f) (I : Ideal R)
    (hI : IsCompleteLocalFlatteningIdeal (M := M) f I)
    (φ : R →+* R') [IsLocalRing R'] [IsLocalHom φ] :
    Formalization.Books.MoreAlgebra.Unit18.flatAtPrimesOver
        (M := Formalization.Books.Algebra.Unit14.baseChangeModule
          (M := M) f φ)
        (Formalization.Books.Algebra.Unit14.baseChangeRingMap f φ)
        (IsLocalRing.maximalIdeal R') ↔
      I.map φ = ⊥ := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit20
