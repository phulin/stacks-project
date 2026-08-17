import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Commutative Algebra, Chapter 84: Transfinite dévissage of modules

The source indexes a continuous increasing filtration by an ordinal.  The
filtration is represented by submodules, direct summands by Mathlib's
`IsComplemented`, and successive quotients by the canonical submodule
quotient.  Countable generation is exposed as the existence of a countable
set whose span is the whole module.
-/

namespace Formalization.Books.Algebra.Unit84

open DirectSum

universe u v w

noncomputable section

/-! ## Countable generation and ordinal filtrations -/

/-- A module is countably generated when it has a countable spanning set. -/
def Module.IsCountablyGenerated
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤

/-- The indices of the successive quotients in a filtration indexed by `S`. -/
def SuccessorIndex (S : Ordinal.{w}) :=
  {α : Ordinal.{w} // α + 1 < S}

/- The ordinal successor is definitionally the operation `α + 1` in the
ordinal API, but the generic `lt_add_one` lemma requires a monotonicity
instance which ordinal addition does not provide. -/
theorem ordinal_lt_add_one (α : Ordinal.{w}) : α < α + 1 := by
  simpa only [Order.succ_eq_add_one] using (Order.lt_succ α)

/-- The data of an increasing, continuous ordinal filtration of a module. -/
structure IncreasingDevissage
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Ordinal.{w}) where
  /-- The submodule at each ordinal strictly below `S`. -/
  stage : Set.Iio S → Submodule R M
  /-- The filtration is increasing. -/
  monotone : Monotone stage
  /-- The index set contains the initial stage. -/
  zero_lt : 0 < S
  /-- The initial stage is zero. -/
  zero : stage ⟨0, zero_lt⟩ = ⊥
  /-- The union of the stages is the whole module. -/
  union_eq_top : ⨆ α : Set.Iio S, stage α = ⊤
  /-- A limit stage is the union of its earlier stages. -/
  limit :
    ∀ (α : Set.Iio S), Order.IsSuccLimit α.1 →
      stage α = ⨆ β : Set.Iio α.1,
        stage ⟨β.1, by
          change β.1 < S
          exact β.2.trans α.2⟩

/-- The submodule of the successor stage corresponding to its predecessor. -/
def IncreasingDevissage.successorSubmodule
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {S : Ordinal.{w}}
    (D : IncreasingDevissage (R := R) (M := M) S)
    (α : SuccessorIndex S) : Submodule R (D.stage ⟨α.1 + 1, α.2⟩) :=
  (D.stage ⟨α.1, (ordinal_lt_add_one α.1).trans α.2⟩).comap
    (D.stage ⟨α.1 + 1, α.2⟩).subtype

/-- The successive quotient at a successor index. -/
abbrev IncreasingDevissage.successorQuotient
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {S : Ordinal.{w}}
    (D : IncreasingDevissage (R := R) (M := M) S)
    (α : SuccessorIndex S) : Type _ :=
  (D.stage ⟨α.1 + 1, α.2⟩) ⧸ D.successorSubmodule α

/-- All successor inclusions in an increasing dévissage split. -/
def IncreasingDevissage.isSuccessorComplemented
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {S : Ordinal.{w}}
    (D : IncreasingDevissage (R := R) (M := M) S) : Prop :=
  ∀ α : SuccessorIndex S, IsComplemented (D.successorSubmodule α)

/-- Every stage is a direct summand of the ambient module. -/
def IncreasingDevissage.isAmbientlyComplemented
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {S : Ordinal.{w}}
    (D : IncreasingDevissage (R := R) (M := M) S) : Prop :=
  ∀ α : Set.Iio S, IsComplemented (D.stage α)

/-- For a continuous filtration, splitting at every successor is equivalent to
every stage being a direct summand of the ambient module. -/
theorem IncreasingDevissage.isSuccessorComplemented_iff_isAmbientlyComplemented
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {S : Ordinal.{w}}
    (D : IncreasingDevissage (R := R) (M := M) S) :
    D.isSuccessorComplemented ↔ D.isAmbientlyComplemented := by
  sorry

/-! ## Direct sum and Kaplansky dévissages -/

/-- A direct sum dévissage is an increasing continuous filtration whose
successive inclusions split. -/
structure DirectSumDevissage
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Ordinal.{w}) : Type (max (max u v) (w + 2))
    extends IncreasingDevissage (R := R) (M := M) S where
  /-- Each predecessor is a direct summand of the corresponding successor. -/
  successor : toIncreasingDevissage.isSuccessorComplemented

/-- A Kaplansky dévissage is a direct sum dévissage with countably generated
successive quotients. -/
structure KaplanskyDevissage
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Ordinal.{w}) : Type (max (max u v) (w + 2))
    extends DirectSumDevissage (R := R) (M := M) S where
  /-- Every successive quotient is countably generated. -/
  countablyGenerated :
    ∀ α : SuccessorIndex S,
      Module.IsCountablyGenerated R
        (toDirectSumDevissage.toIncreasingDevissage.successorQuotient α)

/-- A module admits a Kaplansky dévissage. -/
def HasKaplanskyDevissage
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R) : Prop :=
  ∃ S : Ordinal.{v},
    Nonempty (KaplanskyDevissage (R := R) (M := (M : Type v)) S)

/-- A bundled module is a direct sum of countably generated modules. -/
def IsDirectSumOfCountablyGeneratedModules
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R) : Prop :=
  ∃ (ι : Type v) (N : ι → ModuleCat.{v} R),
    (∀ i, Module.IsCountablyGenerated R (N i)) ∧
      Nonempty ((M : Type v) ≃ₗ[R] (⨁ i, (N i : Type v)))

/-- A bundled module is a direct sum of countably generated projective modules. -/
def IsDirectSumOfCountablyGeneratedProjectiveModules
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R) : Prop :=
  ∃ (ι : Type v) (N : ι → ModuleCat.{v} R),
    (∀ i,
      Module.IsCountablyGenerated R (N i) ∧ Module.Projective R (N i)) ∧
      Nonempty ((M : Type v) ≃ₗ[R] (⨁ i, (N i : Type v)))

/-! ## The decomposition lemma and Kaplansky's theorem -/

/-- The successive quotients of a direct sum dévissage give a direct-sum
decomposition of the ambient module. -/
theorem directSumDevissage_decomposition
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {S : Ordinal.{w}}
    (D : DirectSumDevissage (R := R) (M := M) S) :
    Nonempty
      (M ≃ₗ[R]
        (⨁ α : SuccessorIndex S,
          D.toIncreasingDevissage.successorQuotient α)) := by
  sorry

/-- A module is a direct sum of countably generated modules exactly when it
admits a Kaplansky dévissage. -/
theorem isDirectSumOfCountablyGeneratedModules_iff_hasKaplanskyDevissage
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R) :
    IsDirectSumOfCountablyGeneratedModules M ↔ HasKaplanskyDevissage M := by
  sorry

/-! ## Direct summands and projective modules -/

/-- A direct summand of a direct sum of countably generated modules is again a
direct sum of countably generated modules. -/
theorem isDirectSumOfCountablyGeneratedModules_of_isComplemented
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (hM : IsDirectSumOfCountablyGeneratedModules (ModuleCat.of R M))
    (P : Submodule R M) (hP : IsComplemented P) :
    IsDirectSumOfCountablyGeneratedModules (ModuleCat.of R P) := by
  sorry

/-- Every projective module is a direct sum of countably generated projective
modules. -/
theorem projective_isDirectSumOfCountablyGeneratedProjectiveModules
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Projective R M] :
    IsDirectSumOfCountablyGeneratedProjectiveModules (ModuleCat.of R M) := by
  sorry

end

end Formalization.Books.Algebra.Unit84
