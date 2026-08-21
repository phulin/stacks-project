import Formalization.Books.Algebra.Unit66.PureTransLocal
import Mathlib.RingTheory.Localization.BaseChange

namespace Formalization.Books.Algebra.Unit66
open Set
open scoped TensorProduct
noncomputable section

set_option linter.style.haveILetI false

/-- An element outside an extended prime remains outside the corresponding
extended maximal ideal after localization at that prime. -/
theorem pureTrans_tensorMap_notMem_local_max
    {k F R : Type*} [Field k] [Field F] [Algebra k F]
    [CommRing R] [Algebra k R] (p : PrimeSpectrum R)
    (hdom : IsDomain ((R ⧸ p.asIdeal) ⊗[k] F))
    (b : R ⊗[k] F)
    (hb : b ∉ p.asIdeal.map
      (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] F)) :
    let A := Localization.AtPrime p.asIdeal
    let g := Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom k R A) (AlgHom.id k F)
    g b ∉ (IsLocalRing.maximalIdeal A).map
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[k] F) := by
  let S := p.asIdeal.primeCompl
  let A := Localization S
  let B := R ⊗[k] F
  let C := A ⊗[k] F
  let g := Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom k R A) (AlgHom.id k F)
  letI : Algebra B C := g.toRingHom.toAlgebra
  letI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' (by
    ext r
    change algebraMap R A r ⊗ₜ[k] (1 : F) = g (r ⊗ₜ[k] (1 : F))
    simp [g])
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B S) C := by
    apply IsLocalization.tensorProduct_tensorProduct k F S A
    ext x
    simp [g, RingHom.algebraMap_toAlgebra]
  have hmapideal :
      (p.asIdeal.map
          (Algebra.TensorProduct.includeLeftRingHom : R →+* B)).map g.toRingHom =
        (IsLocalRing.maximalIdeal A).map
          (Algebra.TensorProduct.includeLeftRingHom : A →+* C) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal),
      Ideal.map_map, Ideal.map_map]
    congr 1
  dsimp only
  rw [← hmapideal]
  intro hbmap
  have hpBprime :
      (p.asIdeal.map
        (Algebra.TensorProduct.includeLeftRingHom : R →+* B)).IsPrime :=
    ideal_map_includeLeft_isPrime_of_isDomain_tensorProduct_quotient p.asIdeal hdom
  have hpBdisj : Disjoint
      (Algebra.algebraMapSubmonoid B S : Set B)
      (p.asIdeal.map
        (Algebra.TensorProduct.includeLeftRingHom : R →+* B) : Set B) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsp
    apply hs
    have hscomap : s ∈ (p.asIdeal.map
        (Algebra.TensorProduct.includeLeftRingHom : R →+* B)).comap
          (Algebra.TensorProduct.includeLeftRingHom : R →+* B) := hsp
    have heq :
        (Algebra.TensorProduct.includeLeftRingHom : R →+* B) = algebraMap R B := rfl
    rw [heq, Ideal.comap_map_eq_self_of_faithfullyFlat (B := B)] at hscomap
    exact hscomap
  apply hb
  have hunder := IsLocalization.under_map_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid B S) C hpBprime hpBdisj
  rw [← hunder]
  exact hbmap

end
end Formalization.Books.Algebra.Unit66
