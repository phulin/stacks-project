/-
# More on Algebra, Chapter 121: the residue-field multiplication formula
-/

import Formalization.Books.MoreAlgebra.Unit121.ShortExact
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.Norm.Basic

namespace Formalization.Books.MoreAlgebra.Unit121

noncomputable section

universe u v

/-! ## Residue-field extensions and scalar restriction -/

/-- The canonical algebra structure on residue fields induced by a local ring homomorphism. -/
@[instance_reducible] def residueAlgebra
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] :
    Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
  (IsLocalRing.ResidueField.map f).toAlgebra

/-- The module structure underlying an explicitly supplied algebra. -/
@[instance_reducible] def fieldExtensionModule
    {K L : Type*} [Field K] [Field L] (A : Algebra K L) : Module K L := by
  letI := A
  exact inferInstance

/-- A finite residue-field extension, with its canonical algebra structure fixed by the local
ring map. -/
structure FiniteResidueExtension
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] where
  finite :
    @Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
      _ _ (fieldExtensionModule (residueAlgebra f))

noncomputable def residueNorm
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (_E : FiniteResidueExtension f) (u : IsLocalRing.ResidueField S) :
    IsLocalRing.ResidueField R := by
  letI : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    residueAlgebra f
  letI : Module (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    fieldExtensionModule (residueAlgebra f)
  letI : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := _E.finite
  exact Algebra.norm (IsLocalRing.ResidueField R) u

/-- The residue-field degree of a finite local extension. -/
noncomputable def residueFieldDegree
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (_E : FiniteResidueExtension f) : ℕ := by
  letI : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    residueAlgebra f
  letI : Module (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    fieldExtensionModule (residueAlgebra f)
  letI : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := _E.finite
  exact Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)

/-- Finite length is preserved when scalars are restricted along a local map with finite residue
field extension. -/
theorem finiteLength_restrictScalars
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (E : FiniteResidueExtension f)
    {M : Type v} [AddCommGroup M] [Module S M]
    (hM : IsFiniteLength S M) :
    @IsFiniteLength R _ M _ (Module.compHom M f) := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Module R M := Module.restrictScalars R S M
  let _ : IsScalarTower R S M := IsScalarTower.restrictScalars R S M
  apply Module.length_ne_top_iff.mp
  rw [IsLocalRing.length_restrictScalars R S M]
  apply WithTop.mul_ne_top
  · exact Module.length_ne_top_iff.mpr hM
  · have hmodule : fieldExtensionModule (residueAlgebra f) =
        (inferInstance : Module (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) := by
      apply Module.ext'
      intro c x
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
      rfl
    have hfiniteCustom :
        @Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
          _ _ (fieldExtensionModule (residueAlgebra f)) := E.finite
    have hfinite : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
      change @Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
        _ _ (inferInstance : Module (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
      exact hmodule ▸ hfiniteCustom
    have hlen :
        @Module.length (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
          _ _ (inferInstance : Module (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)) =
          Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
      exact @Module.length_eq_finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
        _ _ _ hfinite
    rw [hlen]
    exact ENat.natCast_ne_top _

/-- The scalar-restriction length is the residue-field degree times the original length. -/
theorem finiteLength_restrictScalars_length
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (E : FiniteResidueExtension f)
    {M : Type v} [AddCommGroup M] [Module S M]
    (hM : IsFiniteLength S M) :
    @finiteLengthNat R M _ _ (Module.compHom M f)
        (finiteLength_restrictScalars f E hM) =
      finiteLengthNat S M hM * residueFieldDegree f E := by
  sorry

/-- The `R`-linear endomorphism given by multiplication by an element of `S`, on an `S`-module
viewed through `f`. -/
def scalarMultiplicationEnd
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (u : S) :
    @Module.End R M _ _ (Module.compHom M f) := by
  letI : Module R M := Module.compHom M f
  exact
    { toFun := fun x => u • x
      map_add' := fun x y => smul_add u x y
      map_smul' := by
        intro r x
        change u • (f r • x) = f r • (u • x)
        rw [smul_comm] }

noncomputable def determinantAfterRestriction
    {R S M : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [AddCommGroup M] [Module S M]
    (f : R →+* S) (hR : @IsFiniteLength R _ M _ (Module.compHom M f))
    (u : S) : IsLocalRing.ResidueField R := by
  letI : Module R M := Module.compHom M f
  exact determinantOf hR (scalarMultiplicationEnd f u)

/-! ## Lemma `lemma-multiplication` -/

theorem lemma_multiplication
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (E : FiniteResidueExtension f) (u : S)
    {M : Type v} [AddCommGroup M] [Module S M]
    (hM : IsFiniteLength S M) :
    determinantAfterRestriction f (finiteLength_restrictScalars f E hM) u =
      residueNorm f E (IsLocalRing.residue S u) ^ finiteLengthNat S M hM := by
  sorry

end
