import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.Algebra.Category.Ring.Instances
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.Tactic.TFAE

/-!
# Commutative Algebra, Chapter 107: Epimorphisms of rings

Ring epimorphisms are represented by the canonical categorical predicate
`Epi` on `CommRingCat` morphisms.  Tensor-product statements use the
canonical algebra structure induced by a ring homomorphism through
`RingHom.toAlgebra`.
-/

namespace Formalization.Books.Algebra.Unit107

open CategoryTheory
open scoped BigOperators TensorProduct

universe u

noncomputable section

/-! ## Basic properties of epimorphisms -/

/-- The four standard characterizations of an epimorphism of commutative rings.

The second item is the equality of the two canonical maps into the self-tensor
product, the third says that either of those maps is an isomorphism, and the
fourth uses the multiplication map from the self-tensor product.
-/
theorem epimorphism_iff_tensorProduct
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    List.TFAE
      [ Epi (CommRingCat.ofHom f),
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S) =
          (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom,
        IsIso (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S)) ∨
          IsIso (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom),
        IsIso (CommRingCat.ofHom
          ((Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toRingHom)) ] := by
  exact (letI : Algebra R S := f.toAlgebra
    (show List.TFAE
      [ Epi (CommRingCat.ofHom f),
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S) =
          (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom,
        IsIso (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S)) ∨
          IsIso (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom),
        IsIso (CommRingCat.ofHom
          ((Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toRingHom)) ] from by
      let H := CommRingCat.isPushout_tensorProduct R S S
      let m : S ⊗[R] S →+* S := (Algebra.TensorProduct.lmul' R).toRingHom
      tfae_have h12 : 1 ↔ 2 := by
        change Epi (CommRingCat.ofHom f) ↔ H.cocone.inl.hom = H.cocone.inr.hom
        exact ⟨fun h => congrArg (fun q => q.hom)
            ((CategoryTheory.epi_iff_inl_eq_inr H.isColimit).mp h),
          fun h => (CategoryTheory.epi_iff_inl_eq_inr H.isColimit).mpr
            (CommRingCat.hom_ext h)⟩
      tfae_have h13 : 1 ↔ 3 := by
        change Epi (CommRingCat.ofHom f) ↔ IsIso H.cocone.inl ∨ IsIso H.cocone.inr
        constructor
        · intro h
          exact Or.inl ((CategoryTheory.epi_iff_isIso_inl H.isColimit).mp h)
        · rintro (hl | hr)
          · exact (CategoryTheory.epi_iff_isIso_inl H.isColimit).mpr hl
          · exact (CategoryTheory.epi_iff_isIso_inr H.isColimit).mpr hr
      tfae_have h34 : 3 → 4 := by
        change (IsIso H.cocone.inl ∨ IsIso H.cocone.inr) →
          IsIso (CommRingCat.ofHom m)
        rintro (hl | hr)
        · rcases hl.out with ⟨j, hij, hji⟩
          have hepi : Epi H.cocone.inl :=
            ⟨fun a b hab => by
              calc
                a = 𝟙 H.cocone.pt ≫ a := (Category.id_comp _).symm
                _ = (j ≫ H.cocone.inl) ≫ a := by rw [hji]
                _ = j ≫ (H.cocone.inl ≫ a) := Category.assoc _ _ _
                _ = j ≫ (H.cocone.inl ≫ b) := by rw [hab]
                _ = (j ≫ H.cocone.inl) ≫ b := (Category.assoc _ _ _).symm
                _ = b := by rw [hji]; exact Category.id_comp _⟩
          have hleft := @Algebra.TensorProduct.lmul'_comp_includeLeft R S _ _ f.toAlgebra
          have hcomp : H.cocone.inl ≫ CommRingCat.ofHom m = 𝟙 _ := by
            apply CommRingCat.hom_ext
            exact congrArg (fun q => q.toRingHom) hleft
          refine ⟨⟨H.cocone.inl, ?_, ?_⟩⟩
          · apply hepi.left_cancellation
            exact calc
              H.cocone.inl ≫ (CommRingCat.ofHom m ≫ H.cocone.inl) =
                  (H.cocone.inl ≫ CommRingCat.ofHom m) ≫ H.cocone.inl :=
                (Category.assoc _ _ _).symm
              _ = (𝟙 _) ≫ H.cocone.inl := by rw [hcomp]
              _ = H.cocone.inl := Category.id_comp _
              _ = H.cocone.inl ≫ 𝟙 _ := (Category.comp_id _).symm
          · exact hcomp
        · rcases hr.out with ⟨j, hij, hji⟩
          have hepi : Epi H.cocone.inr :=
            ⟨fun a b hab => by
              calc
                a = 𝟙 H.cocone.pt ≫ a := (Category.id_comp _).symm
                _ = (j ≫ H.cocone.inr) ≫ a := by rw [hji]
                _ = j ≫ (H.cocone.inr ≫ a) := Category.assoc _ _ _
                _ = j ≫ (H.cocone.inr ≫ b) := by rw [hab]
                _ = (j ≫ H.cocone.inr) ≫ b := (Category.assoc _ _ _).symm
                _ = b := by rw [hji]; exact Category.id_comp _⟩
          have hright := @Algebra.TensorProduct.lmul'_comp_includeRight R S _ _ f.toAlgebra
          have hcomp : H.cocone.inr ≫ CommRingCat.ofHom m = 𝟙 _ := by
            apply CommRingCat.hom_ext
            exact congrArg (fun q => q.toRingHom) hright
          refine ⟨⟨H.cocone.inr, ?_, ?_⟩⟩
          · apply hepi.left_cancellation
            exact calc
              H.cocone.inr ≫ (CommRingCat.ofHom m ≫ H.cocone.inr) =
                  (H.cocone.inr ≫ CommRingCat.ofHom m) ≫ H.cocone.inr :=
                (Category.assoc _ _ _).symm
              _ = (𝟙 _) ≫ H.cocone.inr := by rw [hcomp]
              _ = H.cocone.inr := Category.id_comp _
              _ = H.cocone.inr ≫ 𝟙 _ := (Category.comp_id _).symm
          · exact hcomp
      tfae_have h41 : 4 → 1 := by
        change IsIso (CommRingCat.ofHom m) → Epi (CommRingCat.ofHom f)
        intro hm
        have hmono : Mono (CommRingCat.ofHom m) :=
          ⟨fun a b hab => by
            rcases hm.out with ⟨k, hmk, hkm⟩
            calc
              a = a ≫ 𝟙 _ := (Category.comp_id _).symm
              _ = a ≫ (CommRingCat.ofHom m ≫ k) := by rw [hmk]
              _ = (a ≫ CommRingCat.ofHom m) ≫ k := (Category.assoc _ _ _).symm
              _ = (b ≫ CommRingCat.ofHom m) ≫ k := by rw [hab]
              _ = b ≫ (CommRingCat.ofHom m ≫ k) := Category.assoc _ _ _
              _ = b ≫ 𝟙 _ := by rw [hmk]
              _ = b := Category.comp_id _⟩
        have hleft := @Algebra.TensorProduct.lmul'_comp_includeLeft R S _ _ f.toAlgebra
        have hright := @Algebra.TensorProduct.lmul'_comp_includeRight R S _ _ f.toAlgebra
        have hcat :
            CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
              S →+* S ⊗[R] S) ≫ CommRingCat.ofHom m =
            CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R)
              (A := S) (B := S)).toRingHom ≫ CommRingCat.ofHom m := by
          apply CommRingCat.hom_ext
          exact (congrArg (fun q => q.toRingHom) hleft).trans
            (congrArg (fun q => q.toRingHom) hright).symm
        have heq := hmono.right_cancellation _ _ hcat
        exact h12.mpr (congrArg (fun q => q.hom) heq)
      exact List.tfae_of_cycle
        (List.IsChain.cons_cons h12.mp
          (List.IsChain.cons_cons (h13.mp ∘ h12.mpr)
            (List.IsChain.cons_cons h34 (List.IsChain.singleton _))))
        h41))

/-- Epimorphisms are closed under composition. -/
theorem epimorphism_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : Epi (CommRingCat.ofHom f)) (hg : Epi (CommRingCat.ofHom g)) :
    Epi (CommRingCat.ofHom (g.comp f)) := by
  exact CategoryTheory.epi_comp' hf hg

/-- Base change preserves epimorphisms.

The displayed map is the left inclusion
`R' → R' ⊗[R] S`, which is the source's map `R' → S_{R'}`.
-/
theorem epimorphism_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R')
    (hf : Epi (CommRingCat.ofHom f)) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    Epi (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom :
        R' →+* R' ⊗[R] S)) := by
  exact (@CommRingCat.isPushout_tensorProduct R R' S _ _ _ g.toAlgebra f.toAlgebra).epi_inl_of_epi hf

/-- If a composite is an epimorphism, then its second map is an epimorphism. -/
theorem epimorphism_of_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hcomp : Epi (CommRingCat.ofHom (g.comp f))) :
    Epi (CommRingCat.ofHom g) := by
  exact @CategoryTheory.epi_of_epi _ _ _ _ _ (CommRingCat.ofHom f) (CommRingCat.ofHom g) hcomp

/-- The map from the image subring of an epimorphism is again an epimorphism. -/
theorem epimorphism_range_subtype
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Epi (CommRingCat.ofHom f)) :
    Epi (CommRingCat.ofHom f.range.subtype) := by
  apply epimorphism_of_comp f.rangeRestrict f.range.subtype
  change Epi (CommRingCat.ofHom f)
  exact hf

/-- Every localization map is an epimorphism, as used in the local criterion. -/
theorem localization_epimorphism
    {R : Type u} [CommRing R] (M : Submonoid R) :
    Epi (CommRingCat.ofHom (algebraMap R (Localization M))) := by
  infer_instance

/-- Epimorphisms can be checked after localizing at every prime of the base.

Here `Sₚ` is represented by the canonical base-change model
`Rₚ ⊗[R] S`, as in the source text.
-/
theorem epimorphism_iff_localization_at_prime
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Epi (CommRingCat.ofHom f) ↔
      ∀ p : PrimeSpectrum R,
        letI : Algebra R S := f.toAlgebra
        Epi (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom :
            Localization.AtPrime p.asIdeal →+*
              Localization.AtPrime p.asIdeal ⊗[R] S)) := by
  letI : Algebra R S := f.toAlgebra
  constructor
  · intro hf p
    let A := Localization.AtPrime p.asIdeal
    exact (@CommRingCat.isPushout_tensorProduct R A S _ _ _
      (inferInstance : Algebra R A) f.toAlgebra).epi_inl_of_epi hf
  · intro h
    apply ((epimorphism_iff_tensorProduct f).out 0 1).mpr
    apply RingHom.ext
    intro s
    apply Module.eq_of_localization_maximal
      (fun (P : Ideal R) [hP : P.IsMaximal] =>
        letI : P.IsPrime := hP.isPrime
        Localization.AtPrime P ⊗[R] (S ⊗[R] S))
      (fun (P : Ideal R) [hP : P.IsMaximal] =>
        letI : P.IsPrime := hP.isPrime
        let A := Localization.AtPrime P
        let N := S ⊗[R] S
        letI : Algebra N (A ⊗[R] N) := Algebra.TensorProduct.rightAlgebra
        (IsScalarTower.toAlgHom R N
          (A ⊗[R] N)).toLinearMap)
    intro P hP
    let A := Localization.AtPrime P
    let N := S ⊗[R] S
    letI : Algebra N (A ⊗[R] N) := Algebra.TensorProduct.rightAlgebra
    let a : (A ⊗[R] S) →+* (A ⊗[R] N) :=
      (Algebra.TensorProduct.map (AlgHom.id R A)
        ((Algebra.TensorProduct.includeLeft (R := R) (S := S) (A := S) (B := S)).restrictScalars R)).toRingHom
    let b : (A ⊗[R] S) →+* (A ⊗[R] N) :=
      (Algebra.TensorProduct.map (AlgHom.id R A)
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S))).toRingHom
    have hab_cat : CommRingCat.ofHom a = CommRingCat.ofHom b := by
      apply (h ⟨P, hP.isPrime⟩).left_cancellation (CommRingCat.ofHom a)
        (CommRingCat.ofHom b)
      apply CommRingCat.hom_ext
      change a.comp (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] S) =
        b.comp (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] S)
      simp [a, b]
    have hab : a = b := congrArg (fun g => g.hom) hab_cat
    have hab' := congrArg (fun g => g (1 ⊗ₜ[R] s)) hab
    change (1 ⊗ₜ[R] (s ⊗ₜ[R] 1)) = (1 ⊗ₜ[R] (1 ⊗ₜ[R] s))
    exact hab'

/-- A ring map is surjective exactly when it is both finite and epic. -/
theorem finite_epimorphism_iff_surjective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (Epi (CommRingCat.ofHom f) ∧ RingHom.Finite f) ↔
      Function.Surjective f := by
  simpa using
    (RingHom.surjective_iff_epi_and_finite
      (f := CommRingCat.ofHom f)).symm

/-- A faithfully flat epimorphism is an isomorphism. -/
theorem isIso_of_faithfullyFlat_of_epimorphism
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Epi (CommRingCat.ofHom f)) (hff : RingHom.FaithfullyFlat f) :
    IsIso (CommRingCat.ofHom f) := by
  letI : Algebra R S := f.toAlgebra
  change Module.FaithfullyFlat R S at hff
  letI : Module.FaithfullyFlat R S := hff
  have hleft_or : IsIso (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S)) ∨
      IsIso (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom) :=
    ((epimorphism_iff_tensorProduct f).out 0 2).mp hf
  have heq :
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S) =
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom :=
    ((epimorphism_iff_tensorProduct f).out 0 1).mp hf
  have hleft : IsIso (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S)) := by
    rcases hleft_or with hl | hr
    · exact hl
    · rw [heq]
      exact hr
  have hleft' : Function.Bijective
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S) :=
    (ConcreteCategory.isIso_iff_bijective _).mp hleft
  apply (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom f)).mpr
  apply Module.FaithfullyFlat.bijective_of_tensorProduct (R := R) (S := S) (T := S)
  simpa [Algebra.TensorProduct.algebraMap_def, RingHom.algebraMap_toAlgebra] using hleft'

/-- An epimorphism out of a field has either a field target isomorphic to the
source or a subsingleton target ring. -/
theorem epimorphism_from_field
    {k S : Type u} [Field k] [CommRing S] (f : k →+* S)
    (hf : Epi (CommRingCat.ofHom f)) :
    IsIso (CommRingCat.ofHom f) ∨ Subsingleton S := by
  by_cases hS : Nontrivial S
  · letI : Nontrivial S := hS
    letI : Algebra k S := f.toAlgebra
    apply Or.inl
    apply isIso_of_faithfullyFlat_of_epimorphism f hf
    change Module.FaithfullyFlat k S
    infer_instance
  · exact Or.inr (not_nontrivial_iff_subsingleton.mp hS)

/-- An epimorphism induces an injective map on spectra and bijections on the
corresponding residue fields. -/
theorem epimorphism_comap_injective_residueField_bijective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Epi (CommRingCat.ofHom f)) :
    Function.Injective (PrimeSpectrum.comap f) ∧
      ∀ q : PrimeSpectrum S,
        Function.Bijective
          (Ideal.ResidueField.map (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl) := by
  letI : Algebra R S := f.toAlgebra
  have hfiber : ∀ p : PrimeSpectrum R,
      Subsingleton (PrimeSpectrum (p.asIdeal.Fiber S)) := by
    intro p
    let A := p.asIdeal.ResidueField
    let B := p.asIdeal.Fiber S
    let e : A →+* B :=
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] S)
    have he : Epi (CommRingCat.ofHom e) := by
      change Epi (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] S))
      exact (@CommRingCat.isPushout_tensorProduct R A S _ _ _
        (inferInstance : Algebra R A) f.toAlgebra).epi_inl_of_epi hf
    rcases epimorphism_from_field e he with hIso | hsub
    · have hsurj : Function.Surjective e :=
        (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom e)).mp hIso |>.surjective
      refine ⟨fun q₁ q₂ => PrimeSpectrum.comap_injective_of_surjective e hsurj ?_⟩
      apply PrimeSpectrum.ext
      have h₁ : (PrimeSpectrum.comap e q₁).asIdeal = (⊥ : Ideal A) :=
        Ideal.eq_bot_of_prime (I := (PrimeSpectrum.comap e q₁).asIdeal)
      have h₂ : (PrimeSpectrum.comap e q₂).asIdeal = (⊥ : Ideal A) :=
        Ideal.eq_bot_of_prime (I := (PrimeSpectrum.comap e q₂).asIdeal)
      exact h₁.trans h₂.symm
    · letI : Subsingleton B := hsub
      exact ⟨fun _ _ => Subsingleton.elim _ _⟩
  refine ⟨?_, ?_⟩
  · intro q₁ q₂ hq
    let p : PrimeSpectrum R := PrimeSpectrum.comap f q₁
    have hq₁ : q₁ ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} := by
      change PrimeSpectrum.comap f q₁ = p
      rfl
    have hq₂ : q₂ ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} := by
      change PrimeSpectrum.comap f q₂ = p
      rw [← hq]
    let e := PrimeSpectrum.preimageEquivFiber R S p
    letI : Subsingleton (PrimeSpectrum (p.asIdeal.Fiber S)) := hfiber p
    have heq : e ⟨q₁, hq₁⟩ = e ⟨q₂, hq₂⟩ :=
      Subsingleton.elim _ _
    simpa using congrArg e.symm heq
  · intro q
    let p : PrimeSpectrum R := PrimeSpectrum.comap f q
    let A := p.asIdeal.ResidueField
    let K := q.asIdeal.ResidueField
    have hp : p.asIdeal = q.asIdeal.comap f := by
      rfl
    let ρ : A →+* K :=
      Ideal.ResidueField.map p.asIdeal q.asIdeal f hp
    let l : S →+* Localization.AtPrime q.asIdeal :=
      algebraMap S (Localization.AtPrime q.asIdeal)
    let r : Localization.AtPrime q.asIdeal →+* K := IsLocalRing.residue _
    have hl : Epi (CommRingCat.ofHom l) := by
      exact localization_epimorphism q.asIdeal.primeCompl
    have hr : Epi (CommRingCat.ofHom r) :=
      ConcreteCategory.epi_of_surjective _ IsLocalRing.residue_surjective
    have hres : Epi (CommRingCat.ofHom (r.comp l)) := epimorphism_comp l r hl hr
    let ta : A →ₐ[R] K :=
      Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId R S) rfl
    let tb : S →ₐ[R] K := IsScalarTower.toAlgHom R S K
    let t : A ⊗[R] S →+* K :=
      (Algebra.TensorProduct.lift ta tb (fun _ _ => Commute.all _ _)).toRingHom
    have htcomp : t.comp Algebra.TensorProduct.includeRight.toRingHom = r.comp l := by
      change ((Algebra.TensorProduct.lift ta tb (fun _ _ => Commute.all _ _)).comp
        Algebra.TensorProduct.includeRight).toRingHom = r.comp l
      rw [Algebra.TensorProduct.lift_comp_includeRight']
      rfl
    have ht : Epi (CommRingCat.ofHom t) := by
      apply epimorphism_of_comp Algebra.TensorProduct.includeRight.toRingHom t
      rw [htcomp]
      exact hres
    have he : Epi (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] S)) := by
      exact (@CommRingCat.isPushout_tensorProduct R A S _ _ _
        (inferInstance : Algebra R A) f.toAlgebra).epi_inl_of_epi hf
    have hte : Epi (CommRingCat.ofHom
        (t.comp (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] S))) :=
      epimorphism_comp
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] S) t he ht
    have hleftcomp :
        t.comp (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] S) =
          ta.toRingHom := by
      change ((Algebra.TensorProduct.lift ta tb (fun _ _ => Commute.all _ _)).comp
        Algebra.TensorProduct.includeLeft).toRingHom = ta.toRingHom
      rw [Algebra.TensorProduct.lift_comp_includeLeft]
    have hρ₀ : Epi (CommRingCat.ofHom ta.toRingHom) := by
      rw [hleftcomp] at hte
      exact hte
    rcases epimorphism_from_field ta.toRingHom hρ₀ with hIso | hsub
    · have hb : Function.Bijective ta.toRingHom :=
        (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom ta.toRingHom)).mp hIso
      have hmap : ta.toRingHom = ρ := by
        apply Ideal.ResidueField.ringHom_ext
        ext z
        change ta (algebraMap R A z) =
          Ideal.ResidueField.map p.asIdeal q.asIdeal f hp
            (algebraMap R A z)
        rw [ta.commutes]
        rw [Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal f hp]
        simpa [RingHom.algebraMap_toAlgebra] using
          (IsScalarTower.algebraMap_apply R S K z)
      rw [hmap] at hb
      change Function.Bijective ρ
      exact hb
    · exact ((not_nontrivial_iff_subsingleton.mpr hsub) inferInstance).elim

/-! ## Relations in tensor products and the epicenter -/

/-- The source's generator-and-relation criterion for a finite tensor sum.

`m` and `a` are finitely supported functions, so their supports encode the
finite-support hypotheses on the families `mⱼ` and `aᵢⱼ`.
-/
theorem tensor_sum_eq_zero_iff_relations
    {R M N I J : Type u} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (x : I → M) (y : J → N)
    (hx : Submodule.span R (Set.range x) = ⊤)
    (hy : Submodule.span R (Set.range y) = ⊤)
    (m : J →₀ M) :
    letI : DecidableEq I := Classical.decEq I
    letI : DecidableEq J := Classical.decEq J
    (∑ j ∈ m.support, (m j) ⊗ₜ[R] y j = 0) ↔
      ∃ a : (I × J) →₀ R,
        (∀ j : J,
          m j = ∑ ij ∈ a.support,
            if ij.2 = j then a ij • x ij.1 else 0) ∧
        (∀ i : I,
          (0 : N) = ∑ ij ∈ a.support,
            if ij.1 = i then a ij • y ij.2 else 0) := by
  classical
  constructor
  · intro hm
    let G : (J →₀ R) →ₗ[R] N := Finsupp.linearCombination R y
    have hG : Function.Surjective G := by
      apply LinearMap.range_eq_top.mp
      rw [Finsupp.range_linearCombination, ← hy]
    let en : (J →₀ R) ⊗[R] M :=
      ∑ j ∈ m.support, Finsupp.single j 1 ⊗ₜ[R] m j
    have hcomm : ∑ j ∈ m.support, y j ⊗ₜ[R] m j = 0 := by
      have := congrArg (TensorProduct.comm R M N) hm
      simpa [TensorProduct.comm_tmul] using this
    have hen : en ∈ LinearMap.ker (LinearMap.rTensor M G) := by
      simp [en, G, hcomm]
    have hexact := rTensor_exact (R := R) (M := LinearMap.ker G)
      (N := J →₀ R) (P := N) (f := (LinearMap.ker G).subtype) (g := G) M
      (LinearMap.exact_subtype_ker_map G) hG
    have hen_range : en ∈ LinearMap.range (LinearMap.rTensor M (LinearMap.ker G).subtype) := by
      rw [← hexact.linearMap_ker_eq]
      exact hen
    obtain ⟨kn, hkn⟩ : ∃ kn : (LinearMap.ker G) ⊗[R] M,
        LinearMap.rTensor M (LinearMap.ker G).subtype kn = en :=
      hen_range
    obtain ⟨ma, hma⟩ := TensorProduct.exists_finset kn
    obtain ⟨c, hc⟩ : ∃ c : (LinearMap.ker G) × M → I →₀ R,
        ∀ kj ∈ ma, Finsupp.linearCombination R x (c kj) = kj.2 := by
      choose c hc using fun kj : (LinearMap.ker G) × M =>
        (LinearMap.range_eq_top.mp (by rw [Finsupp.range_linearCombination, ← hx])) kj.2
      exact ⟨c, fun kj _ => hc kj⟩
    let b : I →₀ (J →₀ R) :=
      ∑ kj ∈ ma,
        (c kj).sum (fun i r => Finsupp.single i (r • (kj.1 : J →₀ R)))
    let a : (I × J) →₀ R := b.uncurry
    have hcoeff (j : J) : m j = ∑ kj ∈ ma, (kj.1 : J →₀ R) j • kj.2 := by
      have hknj := hkn
      rw [hma] at hknj
      apply_fun TensorProduct.finsuppScalarLeft R M J at hknj
      apply_fun (· j) at hknj
      symm at hknj
      simp only [map_sum, TensorProduct.finsuppScalarLeft_apply_tmul, zero_smul,
        Finsupp.single_zero, Finsupp.sum_single_index, one_smul,
        Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq',
        Finset.mem_coe, ↓reduceIte, LinearMap.rTensor_tmul,
        Finsupp.sum_apply, Finsupp.mem_support_iff, ne_eq, ite_not, en] at hknj
      have hright :
          (∑ kj ∈ ma,
            (kj.1 : J →₀ R).sum (fun a₁ b =>
              if a₁ = j then b • kj.2 else 0)) =
            ∑ kj ∈ ma, (kj.1 : J →₀ R) j • kj.2 := by
        apply Finset.sum_congr rfl
        intro kj hkj
        by_cases h : (kj.1 : J →₀ R) j = 0
        · have h' : j ∉ (kj.1 : J →₀ R).support :=
            Finsupp.notMem_support_iff.mpr h
          simp [Finsupp.sum, h', h]
        · have h' : j ∈ (kj.1 : J →₀ R).support :=
            Finsupp.mem_support_iff.mpr h
          simp only [Finsupp.sum]
          rw [Finset.sum_ite_eq' (kj.1 : J →₀ R).support j]
          simp [h']
      have hif : (if m j = 0 then 0 else m j) = m j := by
        by_cases h : m j = 0 <;> simp [h]
      exact hif.symm.trans (hknj.trans hright)
    refine ⟨a, ?_, ?_⟩
    · intro j
      change m j = b.uncurry.sum (fun ij c => if ij.2 = j then c • x ij.1 else 0)
      rw [Finsupp.sum_uncurry_index' b
        (fun i j' c => if j' = j then c • x i else 0)]
      simp only [Finsupp.sum]
      have hsum :
          (∑ i ∈ b.support, ∑ j' ∈ (b i).support,
            if j' = j then (b i) j' • x i else 0) =
            b.sum (fun i r => r j • x i) := by
        simp only [Finsupp.sum]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hj' : j ∈ (b i).support
        · rw [Finset.sum_ite_eq' (b i).support j]
          simp [hj']
        · have hj0 : b i j = 0 := Finsupp.notMem_support_iff.mp hj'
          simp [hj', hj0]
      rw [hsum, hcoeff j]
      let B : (I →₀ (J →₀ R)) →ₗ[R] M :=
        (Finsupp.linearCombination R x).comp
          (Finsupp.mapRange.linearMap (Finsupp.lapply j))
      have hB (q : I →₀ (J →₀ R)) :
          B q = q.sum (fun i r => r j • x i) := by
        simp [B, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index]
      rw [← hB b]
      rw [show b = ∑ kj ∈ ma, (c kj).sum
          (fun i r => Finsupp.single i (r • (kj.1 : J →₀ R))) by rfl]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro kj hkj
      rw [← hc kj hkj]
      have hq :
          ((c kj).sum
            (fun i r => Finsupp.single i (r • (kj.1 : J →₀ R)))).sum
              (fun a b => b j • x a) =
            (kj.1 : J →₀ R) j • Finsupp.linearCombination R x (c kj) := by
        rw [← hB]
        change B (∑ i ∈ (c kj).support,
          Finsupp.single i ((c kj) i • (kj.1 : J →₀ R))) = _
        rw [map_sum]
        rw [Finsupp.linearCombination_apply]
        simp only [Finsupp.sum]
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp [B, Finsupp.mapRange.linearMap_apply,
          Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index,
          smul_smul, mul_comm, mul_left_comm, mul_assoc]
      exact hq.symm.trans (hB _).symm
    · intro i
      change 0 = b.uncurry.sum (fun ij c => if ij.1 = i then c • y ij.2 else 0)
      rw [Finsupp.sum_uncurry_index' b
        (fun i' j' c => if i' = i then c • y j' else 0)]
      simp only [Finsupp.sum]
      by_cases hi : i ∈ b.support
      · have hsum :
            (∑ a ∈ b.support, ∑ j ∈ (b a).support,
              if a = i then (b a) j • y j else 0) =
              (b i).sum (fun j r => r • y j) := by
          have hout :
              (∑ a ∈ b.support, ∑ j ∈ (b a).support,
                if a = i then (b a) j • y j else 0) =
                ∑ j ∈ (b i).support, if i = i then (b i) j • y j else 0 :=
            Finset.sum_eq_single i
              (fun a ha hai => by
                apply Finset.sum_eq_zero
                intro j hj
                simp [hai])
              (fun hnot => (hnot hi).elim)
          rw [hout]
          simp only [if_pos rfl]
          rfl
        rw [hsum]
        rw [show b = ∑ kj ∈ ma,
          (c kj).sum
            (fun i' r => Finsupp.single i' (r • (kj.1 : J →₀ R))) by rfl]
        simp only [Finsupp.finsetSum_apply]
        change 0 = G (∑ kj ∈ ma,
          (c kj).sum
            (fun i' r => Finsupp.single i' (r • (kj.1 : J →₀ R))) i)
        rw [map_sum]
        symm
        apply Finset.sum_eq_zero
        intro kj hkj
        change G ((c kj).sum
          (fun i' r => Finsupp.single i' (r • (kj.1 : J →₀ R))) i) = 0
        by_cases hi' : i ∈ (c kj).support
        · have hci :
              (c kj).sum
                (fun i' r => Finsupp.single i' (r • (kj.1 : J →₀ R))) i =
                (c kj) i • kj.1 := by
            simp only [Finsupp.sum]
            rw [Finsupp.finsetSum_apply]
            simp only [Finsupp.single_apply]
            rw [Finset.sum_ite_eq' (c kj).support i]
            simp [hi']
          rw [hci]
          simp [G, Finsupp.linearCombination_apply, kj.1.2]
        · have hci :
              (c kj).sum
                (fun i' r => Finsupp.single i' (r • (kj.1 : J →₀ R))) i = 0 := by
            simp [Finsupp.sum_apply, Finsupp.single_apply, hi']
          rw [hci]
          simp
      · simp [hi]
  · rintro ⟨a, hm, hy'⟩
    let s : Finset J := a.support.image Prod.snd
    have hms : m.support ⊆ s := by
      intro j hj
      by_contra hj'
      have hz : (∑ ij ∈ a.support,
          if ij.2 = j then a ij • x ij.1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro ij hij
        simp only [ite_eq_right_iff]
        intro heq
        exact (hj' (Finset.mem_image.mpr ⟨ij, hij, heq⟩)).elim
      have hj0 : m j = 0 := by
        rw [hm j]
        exact hz
      exact (Finsupp.mem_support_iff.mp hj) hj0
    calc
      ∑ j ∈ m.support, m j ⊗ₜ[R] y j = ∑ j ∈ s, m j ⊗ₜ[R] y j := by
        rw [Finset.sum_subset hms]
        intro j hj hj'
        have hj0 : m j = 0 := Finsupp.notMem_support_iff.mp hj'
        simp [hj0]
      _ = ∑ j ∈ s,
          (∑ ij ∈ a.support,
            if ij.2 = j then a ij • x ij.1 else 0) ⊗ₜ[R] y j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hm]
      _ = ∑ j ∈ s, ∑ ij ∈ a.support,
          if ij.2 = j then a ij • (x ij.1 ⊗ₜ[R] y j) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [TensorProduct.sum_tmul]
        apply Finset.sum_congr rfl
        intro ij hij
        split_ifs <;> simp [TensorProduct.smul_tmul]
      _ = ∑ ij ∈ a.support, a ij • (x ij.1 ⊗ₜ[R] y ij.2) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro ij hij
        rw [Finset.sum_eq_single ij.2]
        · simp
        · intro j hj hne
          simp [eq_comm, hne]
        · intro hnot
          exact (hnot (Finset.mem_image.mpr ⟨ij, hij, rfl⟩)).elim
      _ = a.curry.sum (fun i ci => x i ⊗ₜ[R] ci.sum (fun j r => r • y j)) := by
        change a.sum (fun ij c => c • (x ij.1 ⊗ₜ[R] y ij.2)) = _
        rw [← Finsupp.sum_curry_index a (fun i j c => c • (x i ⊗ₜ[R] y j))]
        simp only [Finsupp.sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [TensorProduct.tmul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
      _ = 0 := by
        simp only [Finsupp.sum]
        apply Finset.sum_eq_zero
        intro i hi
        have hyi := hy' i
        have hyi : (a.curry i).sum (fun j r => r • y j) = 0 := by
          change (∑ j ∈ (a.curry i).support, (a.curry i) j • y j) = 0
          have hφinj : ∀ (ij₁ ij₂ : I × J) (b : J),
              b ∈ (if ij₁.1 = i then some ij₁.2 else none) →
              b ∈ (if ij₂.1 = i then some ij₂.2 else none) → ij₁ = ij₂ := by
            intro ij₁ ij₂ b hb₁ hb₂
            by_cases h₁ : ij₁.1 = i <;> by_cases h₂ : ij₂.1 = i
            · simp [h₁, h₂] at hb₁ hb₂
              apply Prod.ext
              · exact h₁.trans h₂.symm
              · exact hb₁.trans hb₂.symm
            · simp [h₂] at hb₂
            · simp [h₁] at hb₁
            · simp [h₁, h₂] at hb₁
          calc
            ∑ j ∈ (a.curry i).support, (a.curry i) j • y j =
                ∑ ij ∈ a.support.filter (fun ij => ij.1 = i), a ij • y ij.2 := by
              apply Finset.sum_bij (fun j _ => (i, j))
              · intro j hj
                change j ∈ a.support.filterMap
                  (fun ij => if ij.1 = i then some ij.2 else none) hφinj at hj
                apply Finset.mem_filter.mpr
                refine ⟨?_, rfl⟩
                rcases (Finset.mem_filterMap
                  (fun ij : I × J => if ij.1 = i then some ij.2 else none)
                  (s := a.support) (f_inj := hφinj)).mp hj with ⟨ij, hij, hmap⟩
                have hfst : ij.1 = i := by
                  by_contra hne
                  simp [hne] at hmap
                have hsnd : ij.2 = j := by
                  simpa [hfst] using hmap
                have heq : ij = (i, j) := by
                  apply Prod.ext <;> assumption
                simpa [heq] using hij
              · intro j₁ hj₁ j₂ hj₂ heq
                exact congrArg Prod.snd heq
              · intro ij hij
                refine ⟨ij.2, ?_, ?_⟩
                · apply (Finset.mem_filterMap
                    (fun ij : I × J => if ij.1 = i then some ij.2 else none)
                    (s := a.support) (f_inj := hφinj)).mpr
                  refine ⟨ij, (Finset.mem_filter.mp hij).1, ?_⟩
                  simp [Finset.mem_filter.mp hij |>.2]
                · apply Prod.ext
                  · exact (Finset.mem_filter.mp hij).2.symm
                  · rfl
              · intro j hj
                simp [Finsupp.curry_apply]
            _ = ∑ ij ∈ a.support, if ij.1 = i then a ij • y ij.2 else 0 := by
              rw [Finset.sum_filter]
            _ = 0 := hyi.symm
        change x i ⊗ₜ[R] (a.curry i).sum (fun j r => r • y j) = 0
        simp [hyi]

/-- The finite matrix-factorization criterion for an element equalized by the
two maps into a self-tensor product. -/
theorem tensor_equalizer_iff_matrix_factorization
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (g : S) :
    letI : Algebra R S := f.toAlgebra
    (g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g) ↔
      ∃ n : ℕ, ∃ y z : Fin n → S,
        ∃ x : Matrix (Fin n) (Fin n) R,
          g = ∑ i : Fin n, ∑ j : Fin n, f (x i j) * y i * z j ∧
          (∀ j : Fin n, ∃ r : R,
            ∑ i : Fin n, f (x i j) * y i = f r) ∧
          (∀ i : Fin n, ∃ r : R,
            ∑ j : Fin n, f (x i j) * z j = f r) := by
  letI : Algebra R S := f.toAlgebra
  constructor
  · intro h
    classical
    let w : Option S → S := fun q => q.elim 1 id
    have hw : Submodule.span R (Set.range w) = ⊤ := by
      have hrange : Set.range w = Set.univ := by
        apply Set.eq_univ_of_forall
        intro s
        exact ⟨some s, by simp [w]⟩
      rw [hrange]
      simp
    let m : Option S →₀ S :=
      Finsupp.single none g - Finsupp.single (some g) 1
    have hmrel : (∑ j ∈ m.support, m j ⊗ₜ[R] w j) = 0 := by
      change (Finsupp.single none g - Finsupp.single (some g) 1).sum
        (fun j c => c ⊗ₜ[R] w j) = 0
      rw [Finsupp.sum_sub_index]
      simp [Finsupp.sum_single_index, w, sub_eq_add_neg, h]
      intro a b₁ b₂
      simp [TensorProduct.sub_tmul]
    obtain ⟨a, hm, ha⟩ :=
      (tensor_sum_eq_zero_iff_relations w w hw hw m).mp hmrel
    let q : Finset (Option S) :=
      insert none (a.support.image Prod.fst ∪ a.support.image Prod.snd)
    let K := q
    let n' := Fintype.card K
    let e : K ≃ Fin n' := Fintype.equivFin K
    let ev : Option S → S := fun v => v.elim 1 id
    let yK : K → S := fun i => ev i.1
    let zK : K → S := fun j => ev j.1
    let pK : K → K → R := fun i j =>
      if i.1 = none then
        if j.1 = none then a (none, none) else 0
      else if j.1 = none then 0 else -a (i.1, j.1)
    have hcol_sum (v : Option S) :
        (∑ i : K, if i.1 = none then 0 else f (a (i.1, v)) * ev i.1) =
          ∑ ij ∈ a.support,
            if ij.2 = v ∧ ij.1 ≠ none then f (a ij) * ev ij.1 else 0 := by
      let qv : Finset (Option S) :=
        a.support.filter (fun ij => ij.2 = v ∧ ij.1 ≠ none) |>.image Prod.fst
      let qvK : Finset K := Finset.univ.filter (fun i => i.1 ∈ qv)
      have hsub : qvK ⊆ (Finset.univ : Finset K) := by
        exact Finset.filter_subset _ _
      rw [← Finset.sum_subset hsub]
      · rw [← Finset.sum_filter]
        apply Finset.sum_bij (fun b _ => (b.1, v))
        · intro b hb
          have hbq : b.1 ∈ qv := Finset.mem_filter.mp hb |>.2
          rcases Finset.mem_image.mp hbq with ⟨ij, hij, heq⟩
          apply Finset.mem_filter.mpr
          refine ⟨?_, ?_, ?_⟩
          · have heq' : (b.1, v) = ij := by
              apply Prod.ext
              · exact heq.symm
              · exact (Finset.mem_filter.mp hij).2.1.symm
            rw [heq']
            exact (Finset.mem_filter.mp hij).1
          · rfl
          · simpa [heq] using (Finset.mem_filter.mp hij).2.2
        · intro b₁ hb₁ b₂ hb₂ heq
          apply Subtype.ext
          exact congrArg Prod.fst heq
        · intro ij hij
          have hqij : ij.1 ∈ qv := by
            apply Finset.mem_image.mpr
            exact ⟨ij, hij, rfl⟩
          refine ⟨⟨ij.1, ?_⟩, ?_, ?_⟩
          · exact Finset.mem_insert_of_mem
              (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨ij, (Finset.mem_filter.mp hij).1, rfl⟩))
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqij⟩
          · apply Prod.ext
            · rfl
            · exact (Finset.mem_filter.mp hij).2.1.symm
        · intro b hb
          have hbq : b.1 ∈ qv := Finset.mem_filter.mp hb |>.2
          rcases Finset.mem_image.mp hbq with ⟨ij, hij, heq⟩
          have hbne : b.1 ≠ none := by
            simpa [heq] using (Finset.mem_filter.mp hij).2.2
          simp [heq, hbne]
      · intro b hb hbn
        by_cases hb0 : b.1 = none
        · simp [hb0]
        · have hab : a (b.1, v) = 0 := by
            by_contra hab
            apply hbn
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_univ _, by
              apply Finset.mem_image.mpr
              refine ⟨(b.1, v), ?_, rfl⟩
              apply Finset.mem_filter.mpr
              exact ⟨Finsupp.mem_support_iff.mpr hab, rfl, hb0⟩⟩
          simp [hb0, hab]
    have hrow_sum (u : Option S) :
        (∑ j : K, if j.1 = none then 0 else f (a (u, j.1)) * ev j.1) =
          ∑ ij ∈ a.support,
            if ij.1 = u ∧ ij.2 ≠ none then f (a ij) * ev ij.2 else 0 := by
      let qu : Finset (Option S) :=
        a.support.filter (fun ij => ij.1 = u ∧ ij.2 ≠ none) |>.image Prod.snd
      let quK : Finset K := Finset.univ.filter (fun j => j.1 ∈ qu)
      have hsub : quK ⊆ (Finset.univ : Finset K) := by
        exact Finset.filter_subset _ _
      rw [← Finset.sum_subset hsub]
      · rw [← Finset.sum_filter]
        apply Finset.sum_bij (fun b _ => (u, b.1))
        · intro b hb
          have hbq : b.1 ∈ qu := Finset.mem_filter.mp hb |>.2
          rcases Finset.mem_image.mp hbq with ⟨ij, hij, heq⟩
          apply Finset.mem_filter.mpr
          refine ⟨?_, ?_, ?_⟩
          · have heq' : (u, b.1) = ij := by
              apply Prod.ext
              · exact (Finset.mem_filter.mp hij).2.1.symm
              · exact heq.symm
            rw [heq']
            exact (Finset.mem_filter.mp hij).1
          · rfl
          · simpa [heq] using (Finset.mem_filter.mp hij).2.2
        · intro b₁ hb₁ b₂ hb₂ heq
          apply Subtype.ext
          exact congrArg Prod.snd heq
        · intro ij hij
          have hquij : ij.2 ∈ qu := by
            apply Finset.mem_image.mpr
            exact ⟨ij, hij, rfl⟩
          refine ⟨⟨ij.2, ?_⟩, ?_, ?_⟩
          · exact Finset.mem_insert_of_mem
              (Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨ij, (Finset.mem_filter.mp hij).1, rfl⟩))
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hquij⟩
          · apply Prod.ext
            · exact (Finset.mem_filter.mp hij).2.1.symm
            · rfl
        · intro b hb
          have hbq : b.1 ∈ qu := Finset.mem_filter.mp hb |>.2
          rcases Finset.mem_image.mp hbq with ⟨ij, hij, heq⟩
          have hbne : b.1 ≠ none := by
            simpa [heq] using (Finset.mem_filter.mp hij).2.2
          simp [heq, hbne]
      · intro b hb hbn
        by_cases hb0 : b.1 = none
        · simp [hb0]
        · have hab : a (u, b.1) = 0 := by
            by_contra hab
            apply hbn
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_univ _, by
              apply Finset.mem_image.mpr
              refine ⟨(u, b.1), ?_, rfl⟩
              apply Finset.mem_filter.mpr
              exact ⟨Finsupp.mem_support_iff.mpr hab, rfl, hb0⟩⟩
          simp [hb0, hab]
    have hsplit (v : Option S) :
        (∑ ij ∈ a.support, if ij.2 = v then f (a ij) * ev ij.1 else 0) =
          f (a (none, v)) +
            ∑ ij ∈ a.support,
              if ij.2 = v ∧ ij.1 ≠ none then f (a ij) * ev ij.1 else 0 := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := a.support)
        (p := fun ij => ij.1 = none)]
      have hfirst :
          (∑ ij ∈ a.support with ij.1 = none,
            if ij.2 = v then f (a ij) * ev ij.1 else 0) =
            f (a (none, v)) := by
        by_cases hmem : (none, v) ∈ a.support.filter (fun ij => ij.1 = none)
        · rw [Finset.sum_eq_single (none, v)]
          · simp [ev]
          · intro ij hij hne
            by_cases h2 : ij.2 = v
            · exact (hne (by
                apply Prod.ext
                · exact (Finset.mem_filter.mp hij).2
                · exact h2)).elim
            · simp [h2]
          · intro hnot
            exact (hnot hmem).elim
        · have hmem' : (none, v) ∉ a.support := by
            intro hmem'
            apply hmem
            exact Finset.mem_filter.mpr ⟨hmem', rfl⟩
          have hz : a (none, v) = 0 := Finsupp.notMem_support_iff.mp hmem'
          rw [hz]
          simp only [map_zero]
          apply Finset.sum_eq_zero
          intro ij hij
          by_cases h2 : ij.2 = v
          · have heq : ij = (none, v) := by
              apply Prod.ext
              · exact (Finset.mem_filter.mp hij).2
              · exact h2
            have haij : a ij = 0 := by
              by_contra haij
              apply hmem'
              rw [← heq]
              exact (Finset.mem_filter.mp hij).1
            simp [h2, haij]
          · simp [h2]
      rw [hfirst]
      rw [← Finset.sum_filter (s := a.support.filter (fun ij => ij.1 ≠ none))
        (p := fun ij => ij.2 = v)]
      rw [← Finset.sum_filter (s := a.support)
        (p := fun ij => ij.2 = v ∧ ij.1 ≠ none)]
      have hfin :
          (a.support.filter (fun ij => ij.1 ≠ none)).filter (fun ij => ij.2 = v) =
            a.support.filter (fun ij => ij.2 = v ∧ ij.1 ≠ none) := by
        ext ij
        simp [and_assoc, and_left_comm, and_comm]
      rw [hfin]
    have hsplit_row (u : Option S) :
        (∑ ij ∈ a.support, if ij.1 = u then f (a ij) * ev ij.2 else 0) =
          f (a (u, none)) +
            ∑ ij ∈ a.support,
              if ij.1 = u ∧ ij.2 ≠ none then f (a ij) * ev ij.2 else 0 := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := a.support)
        (p := fun ij => ij.2 = none)]
      have hfirst :
          (∑ ij ∈ a.support with ij.2 = none,
            if ij.1 = u then f (a ij) * ev ij.2 else 0) =
            f (a (u, none)) := by
        by_cases hmem : (u, none) ∈ a.support.filter (fun ij => ij.2 = none)
        · rw [Finset.sum_eq_single (u, none)]
          · simp [ev]
          · intro ij hij hne
            by_cases h1 : ij.1 = u
            · exact (hne (by
                apply Prod.ext
                · exact h1
                · exact (Finset.mem_filter.mp hij).2)).elim
            · simp [h1]
          · intro hnot
            exact (hnot hmem).elim
        · have hmem' : (u, none) ∉ a.support := by
            intro hmem'
            apply hmem
            exact Finset.mem_filter.mpr ⟨hmem', rfl⟩
          have hz : a (u, none) = 0 := Finsupp.notMem_support_iff.mp hmem'
          rw [hz]
          simp only [map_zero]
          apply Finset.sum_eq_zero
          intro ij hij
          by_cases h1 : ij.1 = u
          · have heq : ij = (u, none) := by
              apply Prod.ext
              · exact h1
              · exact (Finset.mem_filter.mp hij).2
            have haij : a ij = 0 := by
              by_contra haij
              apply hmem'
              rw [← heq]
              exact (Finset.mem_filter.mp hij).1
            simp [h1, haij]
          · simp [h1]
      rw [hfirst]
      rw [← Finset.sum_filter (s := a.support.filter (fun ij => ij.2 ≠ none))
        (p := fun ij => ij.1 = u)]
      rw [← Finset.sum_filter (s := a.support)
        (p := fun ij => ij.1 = u ∧ ij.2 ≠ none)]
      have hfin :
          (a.support.filter (fun ij => ij.2 ≠ none)).filter (fun ij => ij.1 = u) =
            a.support.filter (fun ij => ij.1 = u ∧ ij.2 ≠ none) := by
        ext ij
        simp [and_assoc, and_left_comm, and_comm]
      rw [hfin]
    have hmall (v : Option S) :
        (∑ ij ∈ a.support, if ij.2 = v then f (a ij) * ev ij.1 else 0) = m v := by
      simpa [w, ev, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using (hm v).symm
    have hm_source (v : Option S) (hv : v ≠ none) :
        ∃ r : R, m v = f r := by
      by_cases hvg : v = some g
      · refine ⟨-1, ?_⟩
        simp [m, hvg]
      · refine ⟨0, ?_⟩
        simp [m, hv, hvg]
    have hcolK (j : K) :
        ∃ r : R, ∑ i : K, f (pK i j) * yK i = f r := by
      by_cases hj : j.1 = none
      · refine ⟨a (none, none), ?_⟩
        let i₀ : K := ⟨none, by simp [K, q]⟩
        rw [Finset.sum_eq_single i₀]
        · simp [i₀, pK, yK, ev, hj]
        · intro i hi hne
          have hi0 : i.1 ≠ none := by
            intro hi0
            apply hne
            apply Subtype.ext
            exact hi0
          simp [pK, yK, ev, hj, hi0]
        · simp
      · obtain ⟨rj, hrj⟩ := hm_source j.1 hj
        refine ⟨a (none, j.1) - rj, ?_⟩
        have hp :
            (∑ i : K, f (pK i j) * yK i) =
              -∑ i : K, if i.1 = none then 0 else
                f (a (i.1, j.1)) * ev i.1 := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hi0 : i.1 = none
          · simp [pK, yK, ev, hj, hi0]
          · simp [pK, yK, ev, hj, hi0]
        have hc :
            (∑ i : K, if i.1 = none then 0 else
              f (a (i.1, j.1)) * ev i.1) = f (rj - a (none, j.1)) := by
          rw [hcol_sum j.1]
          calc
            (∑ ij ∈ a.support,
                if ij.2 = j.1 ∧ ij.1 ≠ none then
                  f (a ij) * ev ij.1 else 0) =
                ((∑ ij ∈ a.support,
                  if ij.2 = j.1 then f (a ij) * ev ij.1 else 0) -
                    f (a (none, j.1))) := by
              rw [hsplit j.1]
              ring
            _ = m j.1 - f (a (none, j.1)) := by rw [hmall j.1]
            _ = f (rj - a (none, j.1)) := by rw [hrj, map_sub]
        rw [hp, hc]
        simp [map_sub]
    have hrowK (i : K) :
        ∃ r : R, ∑ j : K, f (pK i j) * zK j = f r := by
      by_cases hi : i.1 = none
      · refine ⟨a (none, none), ?_⟩
        let j₀ : K := ⟨none, by simp [K, q]⟩
        rw [Finset.sum_eq_single j₀]
        · simp [j₀, pK, zK, ev, hi]
        · intro j hj hne
          have hj0 : j.1 ≠ none := by
            intro hj0
            apply hne
            apply Subtype.ext
            exact hj0
          simp [pK, zK, ev, hi, hj0]
        · simp
      · refine ⟨a (i.1, none), ?_⟩
        have hp :
            (∑ j : K, f (pK i j) * zK j) =
              -∑ j : K, if j.1 = none then 0 else
                f (a (i.1, j.1)) * ev j.1 := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hj0 : j.1 = none
          · simp [pK, zK, ev, hi, hj0]
          · simp [pK, zK, ev, hi, hj0]
        have hall :
            (∑ ij ∈ a.support,
              if ij.1 = i.1 then f (a ij) * ev ij.2 else 0) = 0 := by
          simpa [w, ev, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using
            (ha i.1).symm
        have hc :
            (∑ j : K, if j.1 = none then 0 else
              f (a (i.1, j.1)) * ev j.1) = -f (a (i.1, none)) := by
          rw [hrow_sum i.1]
          calc
            (∑ ij ∈ a.support,
                if ij.1 = i.1 ∧ ij.2 ≠ none then
                  f (a ij) * ev ij.2 else 0) =
                ((∑ ij ∈ a.support,
                  if ij.1 = i.1 then f (a ij) * ev ij.2 else 0) -
                    f (a (i.1, none))) := by
              rw [hsplit_row i.1]
              ring
            _ = -f (a (i.1, none)) := by rw [hall]; ring
        rw [hp, hc]
        ring
    have hT_curry :
        (∑ ij ∈ a.support,
          if ij.1 ≠ none ∧ ij.2 ≠ none then
            f (a ij) * ev ij.1 * ev ij.2 else 0) =
          a.curry.sum (fun i ci =>
            if i = none then 0 else
              ev i * ci.sum (fun j r =>
                if j = none then 0 else f r * ev j)) := by
      change a.sum (fun ij c =>
        if ij.1 ≠ none ∧ ij.2 ≠ none then
          f c * ev ij.1 * ev ij.2 else 0) = _
      rw [← Finsupp.sum_curry_index a (fun i j c =>
        if i ≠ none ∧ j ≠ none then f c * ev i * ev j else 0)]
      simp only [Finsupp.sum]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hi0 : i = none
      · simp [hi0]
      · simp only [hi0, true_and, ↓reduceIte]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hj0 : j = none
        · simp [hi0, hj0]
        · simp [hi0, hj0, mul_assoc, mul_left_comm, mul_comm]
    have hcur (u : Option S) :
        (a.curry u).sum (fun j r => if j = none then 0 else f r * ev j) =
          ∑ ij ∈ a.support,
            if ij.1 = u then
              if ij.2 ≠ none then f (a ij) * ev ij.2 else 0 else 0 := by
      change (∑ j ∈ (a.curry u).support,
        if j = none then 0 else f ((a.curry u) j) * ev j) = _
      rw [← Finset.sum_filter (s := a.support)
        (p := fun ij => ij.1 = u)]
      have hφinj : ∀ (ij₁ ij₂ : Option S × Option S) (b : Option S),
          b ∈ (if ij₁.1 = u then some ij₁.2 else none) →
          b ∈ (if ij₂.1 = u then some ij₂.2 else none) → ij₁ = ij₂ := by
        intro ij₁ ij₂ b hb₁ hb₂
        by_cases h₁ : ij₁.1 = u <;> by_cases h₂ : ij₂.1 = u
        · simp [h₁, h₂] at hb₁ hb₂
          apply Prod.ext
          · exact h₁.trans h₂.symm
          · exact hb₁.trans hb₂.symm
        · simp [h₂] at hb₂
        · simp [h₁] at hb₁
        · simp [h₁, h₂] at hb₁
      apply Finset.sum_bij (fun j _ => (u, j))
      · intro j hj
        have hj' : j ∈ a.support.filterMap
          (fun ij => if ij.1 = u then some ij.2 else none) hφinj := by
            simpa [Finsupp.curry] using hj
        rcases (Finset.mem_filterMap
          (fun ij : Option S × Option S => if ij.1 = u then some ij.2 else none)
          (s := a.support) (f_inj := hφinj)).mp hj' with ⟨ij, hij, hmap⟩
        apply Finset.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · have hfst : ij.1 = u := by
            by_contra hne
            simp [hne] at hmap
          have hsnd : ij.2 = j := by simpa [hfst] using hmap
          have heq : ij = (u, j) := by
            apply Prod.ext <;> assumption
          simpa [heq] using hij
        · rfl
      · intro j₁ hj₁ j₂ hj₂ heq
        exact congrArg Prod.snd heq
      · intro ij hij
        refine ⟨ij.2, ?_, ?_⟩
        · have htmp : ij.2 ∈ a.support.filterMap
              (fun ij => if ij.1 = u then some ij.2 else none) hφinj := by
            apply (Finset.mem_filterMap
              (fun ij : Option S × Option S => if ij.1 = u then some ij.2 else none)
              (s := a.support) (f_inj := hφinj)).mpr
            refine ⟨ij, (Finset.mem_filter.mp hij).1, ?_⟩
            simp [Finset.mem_filter.mp hij |>.2]
          simpa [Finsupp.curry] using htmp
          
        · apply Prod.ext
          · exact (Finset.mem_filter.mp hij).2.symm
          · rfl
      · intro j hj
        by_cases hj0 : j = none
        · simp [hj0]
        · simp [Finsupp.curry_apply, hj0]
    have hcur_all (u : Option S) :
        (a.curry u).sum (fun j r => f r * ev j) =
          ∑ ij ∈ a.support,
            if ij.1 = u then f (a ij) * ev ij.2 else 0 := by
      change (∑ j ∈ (a.curry u).support,
        f ((a.curry u) j) * ev j) = _
      rw [← Finset.sum_filter (s := a.support) (p := fun ij => ij.1 = u)]
      have hφinj : ∀ (ij₁ ij₂ : Option S × Option S) (b : Option S),
          b ∈ (if ij₁.1 = u then some ij₁.2 else none) →
          b ∈ (if ij₂.1 = u then some ij₂.2 else none) → ij₁ = ij₂ := by
        intro ij₁ ij₂ b hb₁ hb₂
        by_cases h₁ : ij₁.1 = u <;> by_cases h₂ : ij₂.1 = u
        · simp [h₁, h₂] at hb₁ hb₂
          apply Prod.ext
          · exact h₁.trans h₂.symm
          · exact hb₁.trans hb₂.symm
        · simp [h₂] at hb₂
        · simp [h₁] at hb₁
        · simp [h₁, h₂] at hb₁
      apply Finset.sum_bij (fun j _ => (u, j))
      · intro j hj
        have hj' : j ∈ a.support.filterMap
            (fun ij => if ij.1 = u then some ij.2 else none) hφinj := by
          simpa [Finsupp.curry] using hj
        rcases (Finset.mem_filterMap
          (fun ij : Option S × Option S => if ij.1 = u then some ij.2 else none)
          (s := a.support) (f_inj := hφinj)).mp hj' with ⟨ij, hij, hmap⟩
        apply Finset.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · have hfst : ij.1 = u := by
            by_contra hne
            simp [hne] at hmap
          have hsnd : ij.2 = j := by simpa [hfst] using hmap
          have heq : ij = (u, j) := by
            apply Prod.ext <;> assumption
          simpa [heq] using hij
        · rfl
      · intro j₁ hj₁ j₂ hj₂ heq
        exact congrArg Prod.snd heq
      · intro ij hij
        refine ⟨ij.2, ?_, ?_⟩
        · have htmp : ij.2 ∈ a.support.filterMap
              (fun ij => if ij.1 = u then some ij.2 else none) hφinj := by
            apply (Finset.mem_filterMap
              (fun ij : Option S × Option S => if ij.1 = u then some ij.2 else none)
              (s := a.support) (f_inj := hφinj)).mpr
            refine ⟨ij, (Finset.mem_filter.mp hij).1, ?_⟩
            simp [Finset.mem_filter.mp hij |>.2]
          simpa [Finsupp.curry] using htmp
        · apply Prod.ext
          · exact (Finset.mem_filter.mp hij).2.symm
          · rfl
      · intro j hj
        simp [Finsupp.curry_apply]
    have hrowC (u : Option S) (hu : u ≠ none) :
        (a.curry u).sum (fun j r => if j = none then 0 else f r * ev j) =
          -f (a (u, none)) := by
      have hall :
          (∑ ij ∈ a.support,
            if ij.1 = u then f (a ij) * ev ij.2 else 0) = 0 := by
        simpa [w, ev, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using
          (ha u).symm
      have hsplit' :
          (∑ ij ∈ a.support,
            if ij.1 = u then f (a ij) * ev ij.2 else 0) =
            f (a (u, none)) +
              ∑ ij ∈ a.support,
                if ij.1 = u ∧ ij.2 ≠ none then
                  f (a ij) * ev ij.2 else 0 := by
        simpa [and_assoc, and_left_comm, and_comm] using hsplit_row u
      rw [hcur u]
      calc
        (∑ ij ∈ a.support,
            if ij.1 = u then
              if ij.2 ≠ none then f (a ij) * ev ij.2 else 0 else 0) =
            (∑ ij ∈ a.support,
              if ij.1 = u then f (a ij) * ev ij.2 else 0) -
                f (a (u, none)) := by
          have hcond :
              (∑ ij ∈ a.support,
                if ij.1 = u then
                  if ij.2 ≠ none then f (a ij) * ev ij.2 else 0 else 0) =
                ∑ ij ∈ a.support,
                  if ij.1 = u ∧ ij.2 ≠ none then
                    f (a ij) * ev ij.2 else 0 := by
            apply Finset.sum_congr rfl
            intro ij hij
            by_cases h1 : ij.1 = u <;> by_cases h2 : ij.2 = none
            · simp [h1, h2]
            · simp [h1, h2]
            · simp [h1, h2]
            · simp [h1, h2]
          rw [hcond, hsplit']
          ring
        _ = -f (a (u, none)) := by rw [hall]; ring
    have hfull_curry :
        (∑ ij ∈ a.support,
          if ij.1 ≠ none then f (a ij) * ev ij.1 * ev ij.2 else 0) =
          a.curry.sum (fun i ci =>
            if i = none then 0 else
              ev i * ci.sum (fun j r => f r * ev j)) := by
      change a.sum (fun ij c =>
        if ij.1 ≠ none then f c * ev ij.1 * ev ij.2 else 0) = _
      rw [← Finsupp.sum_curry_index a (fun i j c =>
        if i ≠ none then f c * ev i * ev j else 0)]
      simp only [Finsupp.sum]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hi0 : i = none
      · simp [hi0]
      · simp only [hi0, ↓reduceIte]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp [hi0, mul_assoc, mul_left_comm, mul_comm]
    have hweighted :
        (∑ ij ∈ a.support,
          if ij.1 ≠ none then f (a ij) * ev ij.1 * ev ij.2 else 0) = 0 := by
      rw [hfull_curry]
      simp only [Finsupp.sum]
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hi0 : i = none
      · simp [hi0]
      · have hzero :
            (a.curry i).sum (fun j r => f r * ev j) = 0 := by
          rw [hcur_all i]
          simpa [w, ev, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using
            (ha i).symm
        simp only [hi0, ↓reduceIte]
        have hzero' :
            (∑ x ∈ (a.curry i).support, f ((a.curry i) x) * ev x) = 0 := by
          simpa only [Finsupp.sum] using hzero
        rw [hzero']
        simp
    have hB :
        (∑ ij ∈ a.support,
          if ij.2 = none ∧ ij.1 ≠ none then f (a ij) * ev ij.1 else 0) =
            g - f (a (none, none)) := by
      have hsplit0 :
          (∑ ij ∈ a.support,
            if ij.2 = none then f (a ij) * ev ij.1 else 0) =
              f (a (none, none)) +
                ∑ ij ∈ a.support,
                  if ij.2 = none ∧ ij.1 ≠ none then
                    f (a ij) * ev ij.1 else 0 := by
        simpa using hsplit none
      calc
        (∑ ij ∈ a.support,
            if ij.2 = none ∧ ij.1 ≠ none then f (a ij) * ev ij.1 else 0) =
            (∑ ij ∈ a.support,
              if ij.2 = none then f (a ij) * ev ij.1 else 0) -
                f (a (none, none)) := by
          rw [hsplit0]
          ring
        _ = m none - f (a (none, none)) := by rw [hmall none]
        _ = g - f (a (none, none)) := by simp [m]
    have hsplit_weight :
        (∑ ij ∈ a.support,
          if ij.1 ≠ none then f (a ij) * ev ij.1 * ev ij.2 else 0) =
          (∑ ij ∈ a.support,
            if ij.2 = none ∧ ij.1 ≠ none then
              f (a ij) * ev ij.1 else 0) +
            (∑ ij ∈ a.support,
              if ij.1 ≠ none ∧ ij.2 ≠ none then
                f (a ij) * ev ij.1 * ev ij.2 else 0) := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := a.support)
        (p := fun ij => ij.2 = none)]
      apply congrArg₂ (· + ·)
      · rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro ij hij
        by_cases h2 : ij.2 = none
        · by_cases h1 : ij.1 = none <;> simp [h1, h2, ev]
        · simp [h2]
      · rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro ij hij
        by_cases h2 : ij.2 = none
        · by_cases h1 : ij.1 = none <;> simp [h1, h2, ev]
        · simp [h2]
    have hT :
        (∑ ij ∈ a.support,
          if ij.1 ≠ none ∧ ij.2 ≠ none then
            f (a ij) * ev ij.1 * ev ij.2 else 0) =
            f (a (none, none)) - g := by
      have hTrel :
          (∑ ij ∈ a.support,
            if ij.1 ≠ none ∧ ij.2 ≠ none then
              f (a ij) * ev ij.1 * ev ij.2 else 0) =
            (∑ ij ∈ a.support,
              if ij.1 ≠ none then f (a ij) * ev ij.1 * ev ij.2 else 0) -
              (∑ ij ∈ a.support,
                if ij.2 = none ∧ ij.1 ≠ none then
                  f (a ij) * ev ij.1 else 0) := by
        calc
          (∑ ij ∈ a.support,
              if ij.1 ≠ none ∧ ij.2 ≠ none then
                f (a ij) * ev ij.1 * ev ij.2 else 0) =
              ((∑ ij ∈ a.support,
                if ij.2 = none ∧ ij.1 ≠ none then
                  f (a ij) * ev ij.1 else 0) +
                ∑ ij ∈ a.support,
                  if ij.1 ≠ none ∧ ij.2 ≠ none then
                    f (a ij) * ev ij.1 * ev ij.2 else 0) -
                (∑ ij ∈ a.support,
                  if ij.2 = none ∧ ij.1 ≠ none then
                    f (a ij) * ev ij.1 else 0) := by ring
          _ = (∑ ij ∈ a.support,
              if ij.1 ≠ none then f (a ij) * ev ij.1 * ev ij.2 else 0) -
              (∑ ij ∈ a.support,
                if ij.2 = none ∧ ij.1 ≠ none then
                  f (a ij) * ev ij.1 else 0) := by rw [hsplit_weight]
      calc
        (∑ ij ∈ a.support,
            if ij.1 ≠ none ∧ ij.2 ≠ none then
              f (a ij) * ev ij.1 * ev ij.2 else 0) =
            (∑ ij ∈ a.support,
              if ij.1 ≠ none then f (a ij) * ev ij.1 * ev ij.2 else 0) -
              (∑ ij ∈ a.support,
                if ij.2 = none ∧ ij.1 ≠ none then
                  f (a ij) * ev ij.1 else 0) := hTrel
        _ = f (a (none, none)) - g := by rw [hweighted, hB]; ring
    have hdouble :
        (∑ i : K with i.1 ≠ none,
          ∑ j : K with j.1 ≠ none,
            f (a (i.1, j.1)) * ev i.1 * ev j.1) =
          ∑ ij ∈ a.support,
            if ij.1 ≠ none ∧ ij.2 ≠ none then
              f (a ij) * ev ij.1 * ev ij.2 else 0 := by
      let qN : Finset K := Finset.univ.filter (fun i => i.1 ≠ none)
      change (∑ i ∈ qN, ∑ j ∈ qN,
        f (a (i.1, j.1)) * ev i.1 * ev j.1) = _
      rw [← Finset.sum_product']
      have hrestrict :
          (∑ p ∈ qN ×ˢ qN,
            f (a (p.1.1, p.2.1)) * ev p.1.1 * ev p.2.1) =
            ∑ p ∈ (qN ×ˢ qN).filter
                (fun p => a (p.1.1, p.2.1) ≠ 0),
              f (a (p.1.1, p.2.1)) * ev p.1.1 * ev p.2.1 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hz : a (p.1.1, p.2.1) = 0
        · simp [hz]
        · simp [hz]
      rw [hrestrict]
      conv_rhs =>
        rw [← Finset.sum_filter (s := a.support)
          (p := fun ij => ij.1 ≠ none ∧ ij.2 ≠ none)]
      apply Finset.sum_bij (fun p _ => (p.1.1, p.2.1))
      · intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hpq := Finset.mem_product.mp hp'.1
        apply Finset.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · exact Finsupp.mem_support_iff.mpr hp'.2
        · exact ⟨(Finset.mem_filter.mp hpq.1).2,
            (Finset.mem_filter.mp hpq.2).2⟩
      · intro p₁ hp₁ p₂ hp₂ heq
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg Prod.fst heq
        · apply Subtype.ext
          exact congrArg Prod.snd heq
      · intro ij hij
        have hij' := Finset.mem_filter.mp hij
        let p : K × K :=
          (⟨ij.1, by
              apply Finset.mem_insert_of_mem
              exact Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨ij, hij'.1, rfl⟩)⟩,
            ⟨ij.2, by
              apply Finset.mem_insert_of_mem
              exact Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨ij, hij'.1, rfl⟩)⟩)
        refine ⟨p, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          constructor
          · dsimp [p]
            apply Finset.mem_product.mpr
            constructor
            · apply Finset.mem_filter.mpr
              exact ⟨Finset.mem_univ _, by
                change ij.1 ≠ none
                exact hij'.2.1⟩
            · apply Finset.mem_filter.mpr
              exact ⟨Finset.mem_univ _, by
                change ij.2 ≠ none
                exact hij'.2.2⟩
          · dsimp [p]
            exact Finsupp.mem_support_iff.mp hij'.1
        · dsimp [p]
      · intro p hp
        rfl
    have hmatrixK :
        (∑ i : K, ∑ j : K, f (pK i j) * yK i * zK j) =
          f (a (none, none)) -
            ∑ ij ∈ a.support,
              if ij.1 ≠ none ∧ ij.2 ≠ none then
                f (a ij) * ev ij.1 * ev ij.2 else 0 := by
      let i₀ : K := ⟨none, by simp [K, q]⟩
      let j₀ : K := ⟨none, by simp [K, q]⟩
      have hfirst :
          (∑ i : K with i.1 = none,
            ∑ j : K, f (pK i j) * yK i * zK j) = f (a (none, none)) := by
        rw [Finset.sum_eq_single i₀]
        · rw [Finset.sum_eq_single j₀]
          · simp [i₀, j₀, pK, yK, zK, ev]
          · intro j hj hne
            have hj0 : j.1 ≠ none := by
              intro hj0
              apply hne
              apply Subtype.ext
              exact hj0
            simp [i₀, j₀, pK, yK, zK, ev, hj0]
          · simp [j₀, K, q]
        · intro i hi hne
          have hi0 : i.1 ≠ none := by
            intro hi0
            apply hne
            apply Subtype.ext
            exact hi0
          exact False.elim (hi0 (Finset.mem_filter.mp hi).2)
        · simp [i₀, K, q]
      have hnormal :
          (∑ i : K with i.1 ≠ none,
            ∑ j : K, f (pK i j) * yK i * zK j) =
            -∑ i : K with i.1 ≠ none,
              ∑ j : K with j.1 ≠ none,
                f (a (i.1, j.1)) * ev i.1 * ev j.1 := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        have hi0 : i.1 ≠ none := (Finset.mem_filter.mp hi).2
        have hzero :
            (∑ j : K with j.1 = none,
              f (pK i j) * yK i * zK j) = 0 := by
          rw [Finset.sum_eq_single j₀]
          · simp [i₀, j₀, pK, yK, zK, ev, hi0]
          · intro j hj hne
            have hj0 : j.1 ≠ none := by
              intro hj0
              apply hne
              apply Subtype.ext
              exact hj0
            exact False.elim (hj0 (Finset.mem_filter.mp hj).2)
          · simp [j₀, K, q]
        have hneg :
            (∑ j : K with j.1 ≠ none,
              f (pK i j) * yK i * zK j) =
                -∑ j : K with j.1 ≠ none,
                  f (a (i.1, j.1)) * ev i.1 * ev j.1 := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          have hj0 : j.1 ≠ none := (Finset.mem_filter.mp hj).2
          simp [pK, yK, zK, ev, hi0, hj0, map_neg]
        calc
          (∑ j : K, f (pK i j) * yK i * zK j) =
              (∑ j : K with j.1 = none,
                f (pK i j) * yK i * zK j) +
                ∑ j : K with j.1 ≠ none,
                  f (pK i j) * yK i * zK j := by
            rw [← Finset.sum_filter_add_sum_filter_not
              (s := (Finset.univ : Finset K))
              (p := fun j => j.1 = none)]
          _ = -∑ j : K with j.1 ≠ none,
                f (a (i.1, j.1)) * ev i.1 * ev j.1 := by
            rw [hzero, hneg]
            simp
      have hsplit_matrix :
          (∑ i : K, ∑ j : K, f (pK i j) * yK i * zK j) =
            (∑ i : K with i.1 = none,
              ∑ j : K, f (pK i j) * yK i * zK j) +
              ∑ i : K with i.1 ≠ none,
                ∑ j : K, f (pK i j) * yK i * zK j := by
        rw [← Finset.sum_filter_add_sum_filter_not
          (s := (Finset.univ : Finset K))
          (p := fun i => i.1 = none)]
      rw [hsplit_matrix, hfirst, hnormal, hdouble]
      ring
    have hsum (F : K → S) :
        (∑ i : Fin n', F (e.symm i)) = ∑ k : K, F k := by
      exact (Fintype.sum_equiv e F (fun i => F (e.symm i))
        (fun x => by simp)).symm
    let Y : Fin n' → S := fun i => yK (e.symm i)
    let Z : Fin n' → S := fun j => zK (e.symm j)
    let X : Matrix (Fin n') (Fin n') R := fun i j => pK (e.symm i) (e.symm j)
    have hmainFin :
        (∑ i : Fin n', ∑ j : Fin n', f (X i j) * Y i * Z j) = g := by
      have houter :
          (∑ i : Fin n', ∑ j : Fin n',
            f (pK (e.symm i) (e.symm j)) * yK (e.symm i) * zK (e.symm j)) =
              ∑ i : K, ∑ j : K, f (pK i j) * yK i * zK j := by
        calc
          (∑ i : Fin n', ∑ j : Fin n',
              f (pK (e.symm i) (e.symm j)) * yK (e.symm i) * zK (e.symm j)) =
              ∑ i : Fin n',
                (∑ j : K,
                  f (pK (e.symm i) j) * yK (e.symm i) * zK j) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hsum (fun j =>
              f (pK (e.symm i) j) * yK (e.symm i) * zK j)
          _ = ∑ i : K, ∑ j : K, f (pK i j) * yK i * zK j := by
            exact hsum (fun i =>
              ∑ j : K, f (pK i j) * yK i * zK j)
      calc
        (∑ i : Fin n', ∑ j : Fin n', f (X i j) * Y i * Z j) =
            ∑ i : Fin n', ∑ j : Fin n',
              f (pK (e.symm i) (e.symm j)) * yK (e.symm i) * zK (e.symm j) := by
                rfl
        _ = ∑ i : K, ∑ j : K, f (pK i j) * yK i * zK j := houter
        _ = f (a (none, none)) -
            ∑ ij ∈ a.support,
              if ij.1 ≠ none ∧ ij.2 ≠ none then
                f (a ij) * ev ij.1 * ev ij.2 else 0 := hmatrixK
        _ = g := by rw [hT]; ring
    refine ⟨n', Y, Z, X, ?_, ?_, ?_⟩
    · exact hmainFin.symm
    · intro j
      obtain ⟨rj, hrj⟩ := hcolK (e.symm j)
      refine ⟨rj, ?_⟩
      calc
        (∑ i : Fin n', f (X i j) * Y i) =
            ∑ i : Fin n', f (pK (e.symm i) (e.symm j)) * yK (e.symm i) := by
              rfl
        _ = ∑ i : K, f (pK i (e.symm j)) * yK i := by
              exact hsum (fun i => f (pK i (e.symm j)) * yK i)
        _ = f rj := hrj
    · intro i
      obtain ⟨ri, hri⟩ := hrowK (e.symm i)
      refine ⟨ri, ?_⟩
      calc
        (∑ j : Fin n', f (X i j) * Z j) =
            ∑ j : Fin n', f (pK (e.symm i) (e.symm j)) * zK (e.symm j) := by
              rfl
        _ = ∑ j : K, f (pK (e.symm i) j) * zK j := by
              exact hsum (fun j => f (pK (e.symm i) j) * zK j)
        _ = f ri := hri
  · rintro ⟨n, y, z, x, hg, hcol, hrow⟩
    let r : Fin n → R := fun j => Classical.choose (hcol j)
    let s : Fin n → R := fun i => Classical.choose (hrow i)
    have hr (j : Fin n) :
        ∑ i : Fin n, f (x i j) * y i = f (r j) :=
      Classical.choose_spec (hcol j)
    have hs (i : Fin n) :
        ∑ j : Fin n, f (x i j) * z j = f (s i) :=
      Classical.choose_spec (hrow i)
    have hmove (r : R) (a b : S) :
        (f r * a) ⊗ₜ[R] b = a ⊗ₜ[R] (f r * b) := by
      change (r • a) ⊗ₜ[R] b = a ⊗ₜ[R] (r • b)
      exact TensorProduct.smul_tmul (R := R) r a b
    have hrow_mul (i : Fin n) :
        (∑ j : Fin n, f (x i j) * y i * z j) = f (s i) * y i := by
      calc
        (∑ j : Fin n, f (x i j) * y i * z j) =
            (∑ j : Fin n, f (x i j) * z j) * y i := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = f (s i) * y i := by rw [hs i]
    have hcol_mul (j : Fin n) :
        (∑ i : Fin n, f (x i j) * y i * z j) = f (r j) * z j := by
      calc
        (∑ i : Fin n, f (x i j) * y i * z j) =
            (∑ i : Fin n, f (x i j) * y i) * z j := by
          rw [Finset.sum_mul]
        _ = f (r j) * z j := by rw [hr j]
    have hleft :
        g ⊗ₜ[R] (1 : S) =
          ∑ i : Fin n, y i ⊗ₜ[R] f (s i) := by
      rw [hg]
      rw [TensorProduct.sum_tmul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hrow_mul i]
      simpa using hmove (s i) (y i) (1 : S)
    have hright :
      (1 : S) ⊗ₜ[R] g =
          ∑ j : Fin n, f (r j) ⊗ₜ[R] z j := by
      rw [hg]
      rw [Finset.sum_comm]
      rw [TensorProduct.tmul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hcol_mul j]
      simpa using (hmove (r j) (1 : S) (z j)).symm
    calc
      g ⊗ₜ[R] (1 : S) = ∑ i : Fin n, y i ⊗ₜ[R] f (s i) := hleft
      _ = ∑ i : Fin n, ∑ j : Fin n, y i ⊗ₜ[R] (f (x i j) * z j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hs i]
        rw [TensorProduct.tmul_sum]
      _ = ∑ i : Fin n, ∑ j : Fin n, (f (x i j) * y i) ⊗ₜ[R] z j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact (hmove (x i j) (y i) (z j)).symm
      _ = ∑ j : Fin n, ∑ i : Fin n, (f (x i j) * y i) ⊗ₜ[R] z j := by
        rw [Finset.sum_comm]
      _ = ∑ j : Fin n, f (r j) ⊗ₜ[R] z j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← TensorProduct.sum_tmul, hr j]
      _ = (1 : S) ⊗ₜ[R] g := hright.symm

/-- The epicenter of a ring map, equipped with its canonical subalgebra
structure over the source. -/
def epicenter
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    Subalgebra R S := by
  letI : Algebra R S := f.toAlgebra
  exact
    { carrier := {g : S | g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change (x + y) ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] (x + y)
        simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]
        rw [hx, hy]
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change (x * y) ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] (x * y)
        calc
          (x * y) ⊗ₜ[R] (1 : S) =
              (x ⊗ₜ[R] (1 : S)) * (y ⊗ₜ[R] (1 : S)) := by simp
          _ = ((1 : S) ⊗ₜ[R] x) * ((1 : S) ⊗ₜ[R] y) := by rw [hx, hy]
          _ = (1 : S) ⊗ₜ[R] (x * y) := by simp
      algebraMap_mem' := by
        intro r
        change algebraMap R S r ⊗ₜ[R] (1 : S) =
          (1 : S) ⊗ₜ[R] algebraMap R S r
        exact Algebra.TensorProduct.tmul_one_eq_one_tmul r }

@[simp]
theorem mem_epicenter
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (g : S) :
    letI : Algebra R S := f.toAlgebra
    g ∈ epicenter f ↔ g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g := by
  rfl

/-- A finite matrix triple over `f` records the three matrices `(P,U,V)`
in the source's matrix-factorization remark. -/
structure MatrixTriple
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) where
  P : Matrix (Fin n) (Fin n) R
  U : Matrix (Fin 1) (Fin n) R
  V : Matrix (Fin n) (Fin 1) R

/-- A matrix triple is associated to `g` when it comes from a factorization
`g = Y X Z`, with `U = YX` and `V = XZ` after applying `f` coefficientwise. -/
def matrixTripleAssociated
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (g : S) (t : MatrixTriple f n) : Prop :=
  ∃ y z : Fin n → S,
    g = ∑ i : Fin n, ∑ j : Fin n, f (t.P i j) * y i * z j ∧
    (∀ j : Fin n,
      f (t.U 0 j) = ∑ i : Fin n, f (t.P i j) * y i) ∧
    (∀ i : Fin n,
      f (t.V i 0) = ∑ j : Fin n, f (t.P i j) * z j)

/-! ## Cardinality and modules -/

/-- Every element of the epicenter admits an associated finite matrix triple. -/
theorem exists_matrixTriple_associated_of_mem_epicenter
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) {g : S}
    (hg : g ∈ epicenter f) :
    ∃ n : ℕ, ∃ t : MatrixTriple f n, matrixTripleAssociated f g t := by
  letI : Algebra R S := f.toAlgebra
  have htensor :
      g ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] g :=
    (mem_epicenter f g).mp hg
  obtain ⟨n, y, z, x, hfac, hcol, hrow⟩ :=
    (tensor_equalizer_iff_matrix_factorization f g).mp htensor
  let t : MatrixTriple f n :=
    { P := x
      U := fun _ j => Classical.choose (hcol j)
      V := fun i _ => Classical.choose (hrow i) }
  refine ⟨n, t, y, z, hfac, ?_, ?_⟩
  · intro j
    simpa [t] using (Classical.choose_spec (hcol j)).symm
  · intro i
    simpa [t] using (Classical.choose_spec (hrow i)).symm

/-- An epimorphism cannot increase the cardinality of the underlying ring. -/
theorem cardinality_target_le_source_of_epimorphism
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Epi (CommRingCat.ofHom f)) :
    Cardinal.mk S ≤ Cardinal.mk R := by
  sorry

/-- The finite-source case in the cardinality argument is in fact surjective. -/
theorem surjective_of_finite_source_of_epimorphism
    {R S : Type u} [CommRing R] [CommRing S] [Finite R] (f : R →+* S)
    (hf : Epi (CommRingCat.ofHom f)) :
    Function.Surjective f := by
  sorry

/-- The ring-epimorphism criterion in terms of restriction of scalars on
module categories. -/
theorem epimorphism_iff_restrictScalars_fullyFaithful
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    let F := ModuleCat.restrictScalars f
    List.TFAE
      [ Epi (CommRingCat.ofHom f),
        ∀ (M N : ModuleCat S),
          Function.Bijective
            (F.map : (M ⟶ N) → (F.obj M ⟶ F.obj N)),
        Nonempty F.FullyFaithful ] := by
  sorry

end

end Formalization.Books.Algebra.Unit107
