import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Formalization.Books.Algebra.Unit12.TensorProducts

/-!
# Commutative Algebra, Chapter 39: Flat modules and flat ring maps

This file records the definitions and theorem interfaces from the flatness chapter.  The
canonical predicates are Mathlib's `Module.Flat`, `Module.FaithfullyFlat`, `RingHom.Flat`, and
`RingHom.FaithfullyFlat`; no parallel predicates are introduced here.
-/

namespace Formalization.Books.Algebra.Unit39

open Function
open scoped BigOperators TensorProduct

noncomputable section

universe u v w z

/- The introductory facts that tensor commutes with colimits and is right exact are already
   represented by `Formalization.Books.Algebra.Unit12.tensorProductColimitIso` and
   `Formalization.Books.Algebra.Unit12.tensorProduct_right_exact`, so no parallel declarations
   are introduced here. -/

section Definitions

theorem flat_module_iff_tensor_exact
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ {N N' N'' : Type (max u v)} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
        [Module R N] [Module R N'] [Module R N'']
        {f : N →ₗ[R] N'} {g : N' →ₗ[R] N''},
        Exact f g → Exact (f.lTensor M) (g.lTensor M) :=
  Module.Flat.iff_lTensor_exact

theorem faithfullyFlat_module_iff_tensor_exact
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.FaithfullyFlat R M ↔
      ∀ {N : Type (max u v)} [AddCommGroup N] [Module R N]
        {N' : Type (max u v)} [AddCommGroup N'] [Module R N']
        {N'' : Type (max u v)} [AddCommGroup N''] [Module R N'']
        (f : N →ₗ[R] N') (g : N' →ₗ[R] N''),
        Exact f g ↔ Exact (f.lTensor M) (g.lTensor M) :=
  Module.FaithfullyFlat.iff_exact_iff_lTensor_exact R M

theorem ringHom_flat_iff_module_flat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    RingHom.Flat (algebraMap R S) ↔ Module.Flat R S :=
  RingHom.flat_algebraMap_iff

theorem ringHom_faithfullyFlat_iff_module_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    RingHom.FaithfullyFlat (algebraMap R S) ↔ Module.FaithfullyFlat R S :=
  RingHom.faithfullyFlat_algebraMap_iff

end Definitions

section Flatness

theorem flat_intersect_ideals
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Flat R M]
    (I J : Ideal R) :
    (I • (⊤ : Submodule R M)) ⊓ (J • (⊤ : Submodule R M)) =
      (I ⊓ J) • (⊤ : Submodule R M) := by
  sorry

theorem directLimit_flat
    {R : Type u} [CommRing R] {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] {G : ι → Type w} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
    [DirectedSystem G (f · · ·)]
    (hflat : ∀ i, Module.Flat R (G i)) :
    Module.Flat R (DirectLimit G f) := by
  sorry

theorem module_flat_trans
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Flat R S] [Module.Flat S M] : Module.Flat R M :=
  Module.Flat.trans R S M

theorem module_faithfullyFlat_trans
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.FaithfullyFlat R S] [Module.FaithfullyFlat S M] :
    Module.FaithfullyFlat R M :=
  Module.FaithfullyFlat.trans R S M

theorem ringHom_flat_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {g : S →+* T} (hf : RingHom.Flat f) (hg : RingHom.Flat g) :
    RingHom.Flat (g.comp f) :=
  RingHom.Flat.comp hf hg

theorem ringHom_faithfullyFlat_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {g : S →+* T}
    (hf : RingHom.FaithfullyFlat f) (hg : RingHom.FaithfullyFlat g) :
    RingHom.FaithfullyFlat (g.comp f) := by
  sorry

theorem flat_criteria
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    List.TFAE [
      Module.Flat R M,
      ∀ {N N' : Type (max u v)} [AddCommGroup N] [AddCommGroup N']
        [Module R N] [Module R N'] (f : N →ₗ[R] N'),
        Injective f → Injective (f.rTensor M),
      ∀ (I : Ideal R), Injective (I.subtype.rTensor M),
      ∀ (I : Ideal R), I.FG → Injective (I.subtype.rTensor M)] := by
  sorry

end Flatness

section ColimitsOfRings

theorem directLimit_ring_flat
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {A : ι → Type v} [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (f · · ·)]
    {M : Type w} [AddCommGroup M] [Module (DirectLimit A f) M]
    (hflat : ∀ i,
      letI : Module (A i) M := Module.compHom M (DirectLimit.Ring.of A f i)
      Module.Flat (A i) M) :
    Module.Flat (DirectLimit A f) M := by
  sorry

theorem directLimit_ring_baseChange_flat
    {R : Type u} [CommRing R] {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] {A : ι → Type w} [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (f · · ·)]
    [∀ i, Algebra (A i) R]
    {M : ι → Type z} [∀ i, AddCommGroup (M i)] [∀ i, Module (A i) (M i)]
    (φ : ∀ i j (h : i ≤ j), M i →ₛₗ[f i j h] M j)
    (g : ∀ i j, i ≤ j → (R ⊗[A i] M i) →ₗ[R] (R ⊗[A j] M j))
    [DirectedSystem (fun i => R ⊗[A i] M i) (g · · ·)]
    (hcanonical : ∀ i j (h : i ≤ j) (r : R) (x : M i),
      g i j h (r ⊗ₜ[A i] x) = r ⊗ₜ[A j] φ i j h x)
    (hflat : ∀ i, Module.Flat (A i) (M i)) :
    Module.Flat R (DirectLimit (fun i => R ⊗[A i] M i) g) := by
  sorry

end ColimitsOfRings

section BaseChangeAndDescent

theorem flat_base_change
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (hflat : Module.Flat R M) :
    Module.Flat S (S ⊗[R] M) := by
  sorry

theorem faithfullyFlat_base_change
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (hflat : Module.FaithfullyFlat R M) :
    Module.FaithfullyFlat S (S ⊗[R] M) := by
  sorry

theorem flatness_descends
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R S] :
    Module.Flat R M ↔ Module.Flat S (S ⊗[R] M) := by
  exact (Module.Flat.iff_flat_tensorProduct (R := R) (M := M) S).symm

theorem flatness_descends_more_general
    {R S S' M : Type*} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (hflat : Module.Flat S S') :
    (Module.Flat R M → Module.Flat R (S' ⊗[S] M)) ∧
      (Module.FaithfullyFlat S S' →
        (Module.Flat R M ↔ Module.Flat R (S' ⊗[S] M))) := by
  sorry

theorem flat_permanence
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (hflat : Module.Flat R M) (hfaithful : Module.FaithfullyFlat S M) :
    Module.Flat R S := by
  sorry

end BaseChangeAndDescent

section EquationalCriterion

theorem equational_criterion
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ {l : ℕ} {f : Fin l → R} {x : Fin l → M},
        (∑ i, f i • x i = 0) → Module.IsTrivialRelation f x :=
  Module.Flat.iff_forall_isTrivialRelation

end EquationalCriterion

section ExactSequences

theorem flat_tensor_short_exact
    {R M'' M' M N : Type*} [CommRing R]
    [AddCommGroup M''] [AddCommGroup M'] [AddCommGroup M] [AddCommGroup N]
    [Module R M''] [Module R M'] [Module R M] [Module R N] [Module.Flat R M]
    (f : M'' →ₗ[R] M') (g : M' →ₗ[R] M)
    (hexact : Exact f g) (hinjective : Injective f) (hsurjective : Surjective g) :
    Injective (f.lTensor N) ∧ Exact (f.lTensor N) (g.lTensor N) ∧
      Surjective (g.lTensor N) := by
  sorry

theorem flat_short_exact
    {R M' M M'' : Type*} [CommRing R]
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M'']
    [Module R M'] [Module R M] [Module R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hexact : Exact f g)
    (hinjective : Injective f) (hsurjective : Surjective g) :
    (Module.Flat R M' → Module.Flat R M'' → Module.Flat R M) ∧
      (Module.Flat R M → Module.Flat R M'' → Module.Flat R M') := by
  sorry

end ExactSequences

section FaithfulFlatness

theorem faithfullyFlat_iff_flat_and_tensor_zero
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.FaithfullyFlat R M ↔
      (Module.Flat R M ∧
        ∀ {N N' : Type (max u v)} [AddCommGroup N] [AddCommGroup N']
          [Module R N] [Module R N'] (α : N →ₗ[R] N'),
          α = 0 ↔ α.rTensor M = 0) := by
  sorry

theorem faithfullyFlat_criteria
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] :
    List.TFAE [
      Module.FaithfullyFlat R M,
      ∀ (N : Type (max u v)) [AddCommGroup N] [Module R N],
        Nontrivial N → Nontrivial (M ⊗[R] N),
      ∀ (p : PrimeSpectrum R),
        Nontrivial (M ⊗[R] p.asIdeal.ResidueField),
      ∀ (m : Ideal R) [m.IsMaximal],
        Nontrivial (M ⊗[R] m.ResidueField)] := by
  sorry

noncomputable def tensor_quotient_equiv_smul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (m : Ideal R) :
    M ⊗[R] (R ⧸ m) ≃ₗ[R] M ⧸ (m • (⊤ : Submodule R M)) :=
  TensorProduct.tensorQuotEquivQuotSMul M m

theorem faithfullyFlat_ringHom_criteria
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hflat : RingHom.Flat f) :
    List.TFAE [
      RingHom.FaithfullyFlat f,
      Function.Surjective (PrimeSpectrum.comap f),
      ∀ p : PrimeSpectrum R, p.asIdeal.IsMaximal →
        ∃ q : PrimeSpectrum S, PrimeSpectrum.comap f q = p] := by
  sorry

theorem faithfullyFlat_of_localRingHom
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hflat : RingHom.Flat f) :
    RingHom.FaithfullyFlat f := by
  sorry

end FaithfulFlatness

section Localization

theorem localization_flat
    {R : Type*} [CommRing R] (S : Submonoid R) :
    RingHom.Flat (algebraMap R (Localization S)) := by
  sorry

theorem flat_localization_iff
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) [Module (Localization S) M]
    [IsScalarTower R (Localization S) M] :
    Module.Flat R M ↔ Module.Flat (Localization S) M := by
  sorry

theorem flat_iff_localized_at_primes
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ p : PrimeSpectrum R,
        Module.Flat (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M) := by
  sorry

theorem flat_iff_localized_at_maximals
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ (m : Ideal R) [m.IsMaximal],
        Module.Flat (Localization.AtPrime m)
          (LocalizedModule m.primeCompl M) := by
  sorry

theorem flat_iff_localized_on_generators
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    {n : ℕ} (g : Fin n → A) (hg : Ideal.span (Set.range g) = ⊤) :
    Module.Flat R M ↔
      ∀ i : Fin n,
        Module.Flat R (LocalizedModule (Submonoid.powers (g i)) M) := by
  sorry

noncomputable def flat_at_prime_over
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (P : Ideal A) [P.IsPrime] : Prop :=
  let p := P.comap (algebraMap R A)
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver p P
  letI : Module (Localization.AtPrime p) (LocalizedModule P.primeCompl M) :=
    Module.compHom _ (algebraMap (Localization.AtPrime p) (Localization.AtPrime P))
  Module.Flat (Localization.AtPrime p) (LocalizedModule P.primeCompl M)

theorem flat_iff_localized_over_primes
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] :
    Module.Flat R M ↔
      ∀ (P : Ideal A) [P.IsPrime], flat_at_prime_over (R := R) (A := A) (M := M) P := by
  sorry

theorem flat_iff_localized_over_maximals
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] :
    Module.Flat R M ↔
      ∀ (P : Ideal A) [P.IsMaximal], flat_at_prime_over (R := R) (A := A) (M := M) P := by
  sorry

end Localization

section GoingDown

theorem flat_going_down
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    {p p' : Ideal R} [p.IsPrime] [p'.IsPrime] (hpp : p ≤ p')
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver p'] :
    ∃ P : Ideal S, P ≤ Q ∧ P.IsPrime ∧ P.LiesOver p := by
  sorry

end GoingDown

section FaithfullyFlatColimits

theorem directLimit_faithfullyFlat
    {R : Type u} [CommRing R] {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] {S : ι → Type w} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (f : ∀ i j, i ≤ j → S i →ₐ[R] S j)
    [DirectedSystem S (f · · ·)]
    (hff : ∀ i, Module.FaithfullyFlat R (S i)) :
    Module.FaithfullyFlat R (DirectLimit S f) := by
  sorry

end FaithfullyFlatColimits

end
end Formalization.Books.Algebra.Unit39
