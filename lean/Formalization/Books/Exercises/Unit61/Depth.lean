import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.RingHom.Flat

import Formalization.Books.Algebra.Unit72.Depth

/-!
# Exercises, Chapter 61: Depth goes up

Flatness is expressed by Mathlib's `RingHom.Flat`, while locality is the
canonical `IsLocalHom` instance on the ring homomorphism.  The depth values
are the established `Formalization.Books.Algebra.Unit72.localDepth` of each
ring viewed as its regular module.
-/

namespace Formalization.Books.Exercises.Unit61

universe u v

noncomputable section

/-- A flat local homomorphism of Noetherian local rings cannot decrease the
depth of the ring. -/
theorem depth_goes_up_of_flat_local_hom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f] (hflat : RingHom.Flat f)
    (k : ℕ∞)
    (hdepth : Formalization.Books.Algebra.Unit72.localDepth A A = k) :
    k ≤ Formalization.Books.Algebra.Unit72.localDepth B B := by
  letI : Algebra A B := f.toAlgebra
  letI : IsLocalHom (algebraMap A B) := by
    change IsLocalHom f
    infer_instance
  obtain ⟨xs, hregA, hlen⟩ :=
    Formalization.Books.Algebra.Unit72.regular_sequence_extend_to_localDepth
      (R := A) (M := A) []
      (@RingTheory.Sequence.IsRegular.nil A A _ _ _ inferInstance)
  letI : Module.Flat A B := RingHom.flat_algebraMap_iff.mp (by
    simpa [RingHom.algebraMap_toAlgebra] using hflat)
  letI : Module.FaithfullyFlat A B :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hregB : RingTheory.Sequence.IsRegular B
      (xs.map (algebraMap A B)) :=
    RingTheory.Sequence.IsRegular.of_faithfullyFlat hregA
  have hmemA : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal A := by
    intro x hx
    by_contra hxmax
    have hxunit : IsUnit x := IsLocalRing.notMem_maximalIdeal.mp hxmax
    have hxideal : x ∈ Ideal.ofList xs := Ideal.subset_span hx
    have htop : Ideal.ofList xs = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ hxideal hxunit
    have htop' : (⊤ : Submodule A A) =
        Ideal.ofList xs • (⊤ : Submodule A A) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top, htop]
    exact hregA.top_ne_smul htop'
  have hmemB : ∀ x ∈ xs.map (algebraMap A B),
      x ∈ IsLocalRing.maximalIdeal B := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    exact map_nonunit (algebraMap A B) x (hmemA x hx)
  have hBmax : IsLocalRing.maximalIdeal B • (⊤ : Submodule B B) ≠ ⊤ :=
    Formalization.Books.Algebra.Unit72.smul_top_ne_top_of_le_ring_jacobson
      (IsLocalRing.maximalIdeal B) B
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal B))
  have hdepthB :
      ((xs.map (algebraMap A B)).length : ℕ∞) ≤
        Formalization.Books.Algebra.Unit72.localDepth B B := by
    unfold Formalization.Books.Algebra.Unit72.localDepth
      Formalization.Books.Algebra.Unit72.depth
    rw [dif_neg hBmax]
    apply le_sSup
    exact ⟨xs.map (algebraMap A B), by simp, hmemB, hregB⟩
  calc
    k = Formalization.Books.Algebra.Unit72.localDepth A A := hdepth.symm
    _ = (xs.length : ℕ∞) := hlen
    _ = ((xs.map (algebraMap A B)).length : ℕ∞) := by simp
    _ ≤ Formalization.Books.Algebra.Unit72.localDepth B B := hdepthB

end

end Formalization.Books.Exercises.Unit61
