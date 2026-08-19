import Formalization.Books.Algebra.Unit155.Henselization
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 156: Henselization and quasi-finite ring maps

This file records the functorial localization descriptions of henselizations
and strict henselizations, quotient compatibility, the local tensor-product
lemma, and the strict-henselization base-change theorem from the source.
-/

namespace Formalization.Books.Algebra.Unit156

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit153
open Formalization.Books.Algebra.Unit154
open Formalization.Books.Algebra.Unit155
open scoped TensorProduct

noncomputable section

universe u v

/-! ## Canonical maps used by the source statements -/

/-- The map on localizations induced by a map of rings and a prime above a
prime.  This is Mathlib's `Localization.localRingHom`, with the prime
equality expressed in the direction used by the source. -/
noncomputable def localPrimeMap
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) :
    Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
  Localization.localRingHom p.asIdeal q.asIdeal f (by
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal hq).symm)

/-- The map on quotients induced by extending an ideal along a ring map. -/
noncomputable def quotientHenselizationMap
    {R Rh : Type u} [CommRing R] [CommRing Rh]
    (ι : R →+* Rh) (I : Ideal R) :
    R ⧸ I →+* Rh ⧸ Ideal.map ι I :=
  Ideal.quotientMap (Ideal.map ι I) ι Ideal.le_comap_map

/- A quotient of a local ring is local; the instance is not global in the
Mathlib API, so the chapter's quotient statements install it explicitly. -/
noncomputable def quotientLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≠ ⊤) :
    IsLocalRing (R ⧸ I) :=
  letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

noncomputable def quotientLocalRingOfLeMax
    {R : Type u} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ IsLocalRing.maximalIdeal R) :
    IsLocalRing (R ⧸ I) :=
  quotientLocalRing I (by
    intro htop
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (top_unique (by simpa [htop] using hI)))

noncomputable def quotientLocalRingOfHenselization
    {R Rh : Type u} [CommRing R] [IsLocalRing R]
    [CommRing Rh] [IsLocalRing Rh]
    (ι : R →+* Rh) (hι : IsHenselizationMap R Rh ι)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) :
    IsLocalRing (Rh ⧸ Ideal.map ι I) := by
  apply quotientLocalRingOfLeMax (Ideal.map ι I)
  calc
    Ideal.map ι I ≤ Ideal.map ι (IsLocalRing.maximalIdeal R) :=
      Ideal.map_mono hI
    _ = IsLocalRing.maximalIdeal Rh := hι.2.2.2.1

noncomputable def quotientLocalRingOfStrictHenselization
    {R Rsh : Type u} [CommRing R] [IsLocalRing R]
    [CommRing Rsh] [IsLocalRing Rsh]
    (ι : R →+* Rsh) (hι : IsStrictHenselization R Rsh ι)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) :
    IsLocalRing (Rsh ⧸ Ideal.map ι I) := by
  rcases hι with ⟨K, hField, hAlg, hK, hmap⟩
  apply quotientLocalRingOfLeMax (Ideal.map ι I)
  calc
    Ideal.map ι I ≤ Ideal.map ι (IsLocalRing.maximalIdeal R) :=
      Ideal.map_mono hI
    _ = IsLocalRing.maximalIdeal Rsh := hmap.2.2.2.2.1

/-- The residue-field map associated to a local ring homomorphism, made
explicit so it can be used with a proof rather than a typeclass argument. -/
noncomputable def residueFieldMapOfLocal
    {R S : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    (f : R →+* S) (hf : IsLocalHom f) :
    IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField S := by
  letI : IsLocalHom f := hf
  exact IsLocalRing.ResidueField.map f

/-- A purely inseparable field extension specified by its ring map. -/
def IsPurelyInseparableExtension
    (K L : Type u) [Field K] [Field L] (f : K →+* L) : Prop :=
  letI : Algebra K L := f.toAlgebra
  IsPurelyInseparable K L

/-! ## Filtered colimits of quasi-finite algebras -/

/-- Filtered-colimit data whose stages are quasi-finite ring maps.  The
underlying filtered-colimit presentation is reused from Chapter 154. -/
structure FilteredQuasiFiniteColimit
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) extends FilteredColimitData f where
  quasiFinite : ∀ i, RingHom.QuasiFinite (diagram.obj i).hom.hom

/-- A ring map is a filtered colimit of quasi-finite algebras. -/
def IsFilteredColimitOfQuasiFinite
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) : Prop :=
  Nonempty (FilteredQuasiFiniteColimit f)

/-! ## Tensor-product maps and prime conditions -/

/-- The tensor product attached to two ring maps out of the same base. -/
abbrev tensorOfMaps
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : R →+* T) :=
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R T := g.toAlgebra
  S ⊗[R] T

/-- The two canonical maps into `tensorOfMaps f g`. -/
noncomputable def tensorLeftMap
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : R →+* T) :
    S →+* tensorOfMaps f g := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R T := g.toAlgebra
  exact Algebra.TensorProduct.includeLeftRingHom

noncomputable def tensorRightMap
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : R →+* T) :
    T →+* tensorOfMaps f g := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R T := g.toAlgebra
  exact Algebra.TensorProduct.includeRight.toRingHom

/-- A prime of a ring obtained as the kernel of a map to a field. -/
def kernelPrime
    {R K : Type u} [CommRing R] [Field K] (f : R →+* K) : PrimeSpectrum R :=
  ⟨RingHom.ker f, RingHom.ker_isPrime f⟩

/-- The condition that a tensor-product prime is the prime lying over a
specified prime of the right factor and the maximal ideal of the local left
factor. -/
def IsTensorPrimeOver
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [IsLocalRing A]
    (q : PrimeSpectrum B) (q' : PrimeSpectrum (A ⊗[R] B)) : Prop :=
  q'.asIdeal.comap Algebra.TensorProduct.includeLeftRingHom =
      IsLocalRing.maximalIdeal A ∧
    q'.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = q.asIdeal

/-- The maps from the two tensor factors to the localization at a tensor
prime. -/
noncomputable def tensorLocalizationMapFromLeft
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (q' : PrimeSpectrum (A ⊗[R] B)) :
    A →+* Localization.AtPrime q'.asIdeal :=
  (algebraMap (A ⊗[R] B) (Localization.AtPrime q'.asIdeal)).comp
    Algebra.TensorProduct.includeLeftRingHom

noncomputable def tensorLocalizationMapFromRight
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (q' : PrimeSpectrum (A ⊗[R] B)) :
    B →+* Localization.AtPrime q'.asIdeal :=
  (algebraMap (A ⊗[R] B) (Localization.AtPrime q'.asIdeal)).comp
    Algebra.TensorProduct.includeRight.toRingHom

/-! ## Tensor maps to a common field -/

/-- Tensor two maps to a common field when they agree on the base. -/
noncomputable def tensorMapToField
    {R A B K : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Field K] [Algebra R A] [Algebra R B]
    (a : A →+* K) (b : B →+* K)
    (h : a.comp (algebraMap R A) = b.comp (algebraMap R B)) :
    A ⊗[R] B →+* K := by
  letI : Algebra R K := (a.comp (algebraMap R A)).toAlgebra
  let a' : A →ₐ[R] K :=
    { toRingHom := a
      commutes' := fun r => rfl }
  let b' : B →ₐ[R] K :=
    { toRingHom := b
      commutes' := fun r => by
        calc
          b (algebraMap R B r) = a (algebraMap R A r) :=
            (congrArg (fun z : R →+* K => z r) h).symm
          _ = algebraMap R K r := rfl }
  exact (Algebra.TensorProduct.lift a' b' (fun _ _ => Commute.all _ _)).toRingHom

/-! ## Henselization and strict henselization at a quasi-finite prime -/

/-- The localization description in the quasi-finite henselization lemma.
The returned ring equivalence commutes with both tensor-factor maps, while
the first factor is the henselization map from the preceding chapter. -/
theorem quasiFinite_henselization
    {R S Rh Sh : Type u} [CommRing R] [CommRing S]
    [CommRing Rh] [IsLocalRing Rh] [CommRing Sh] [IsLocalRing Sh]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    (hquasi : RingHom.QuasiFiniteAt f q.asIdeal)
    (ιR : Localization.AtPrime p.asIdeal →+* Rh)
    (hιR : IsHenselizationMap (Localization.AtPrime p.asIdeal) Rh ιR)
    (ιS : Localization.AtPrime q.asIdeal →+* Sh)
    (hιS : IsHenselizationMap (Localization.AtPrime q.asIdeal) Sh ιS) :
    letI : Algebra (Localization.AtPrime p.asIdeal) Rh := ιR.toAlgebra
    letI : Algebra (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) :=
      (localPrimeMap f p q hq).toAlgebra
    ∃ (ψ : Rh →+* Sh) (hψ : IsLocalHom ψ),
      ψ.comp ιR = ιS.comp (localPrimeMap f p q hq) ∧
      ∃ q' : PrimeSpectrum
          (Rh ⊗[Localization.AtPrime p.asIdeal]
            Localization.AtPrime q.asIdeal),
        IsTensorPrimeOver (maximalPrime (Localization.AtPrime q.asIdeal)) q' ∧
        ∃ e : Sh ≃+* Localization.AtPrime q'.asIdeal,
          e.toRingHom.comp ιS = tensorLocalizationMapFromRight q' ∧
          e.toRingHom.comp ψ = tensorLocalizationMapFromLeft q' ∧
          RingHom.Finite ψ := by
  sorry

/-- Henselization commutes with quotienting by an ideal contained in the
maximal ideal. -/
theorem quotient_henselization
    {R Rh : Type u} [CommRing R] [IsLocalRing R]
    [CommRing Rh] [IsLocalRing Rh]
    (ι : R →+* Rh) (hι : IsHenselizationMap R Rh ι)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) :
    letI : IsLocalRing (R ⧸ I) := quotientLocalRingOfLeMax I hI
    letI : IsLocalRing (Rh ⧸ Ideal.map ι I) :=
      quotientLocalRingOfHenselization ι hι I hI
    IsHenselizationMap (R ⧸ I) (Rh ⧸ Ideal.map ι I)
      (quotientHenselizationMap ι I) := by
  sorry

/-- The finite-local description of strict henselization at a
quasi-finite prime.  The residue-field equivalences make the asserted
extension `K₂/K₁` explicit. -/
theorem quasiFinite_strict_henselization
    {R S Rsh Ssh K₁ K₂ : Type u}
    [CommRing R] [CommRing S] [CommRing Rsh] [IsLocalRing Rsh]
    [CommRing Ssh] [IsLocalRing Ssh]
    [Field K₁] [Field K₂]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    (hquasi : RingHom.QuasiFiniteAt f q.asIdeal)
    [Algebra p.asIdeal.ResidueField K₁]
    [Algebra q.asIdeal.ResidueField K₂]
    [Algebra K₁ K₂]
    (hK₁ : IsSeparableAlgebraicClosure p.asIdeal.ResidueField K₁)
    (hK₂ : IsSeparableAlgebraicClosure q.asIdeal.ResidueField K₂)
    (ιR : Localization.AtPrime p.asIdeal →+* Rsh)
    (hιR : IsStrictHenselizationMap
      (Localization.AtPrime p.asIdeal) Rsh K₁ ιR hK₁)
    (ιS : Localization.AtPrime q.asIdeal →+* Ssh)
    (hιS : IsStrictHenselizationMap
      (Localization.AtPrime q.asIdeal) Ssh K₂ ιS hK₂)
    (eR : K₁ ≃+* IsLocalRing.ResidueField Rsh)
    (eS : K₂ ≃+* IsLocalRing.ResidueField Ssh)
    (hres :
      (((algebraMap K₁ K₂).comp
        (eR.symm.toRingHom.comp (IsLocalRing.residue Rsh))).comp ιR) =
      ((algebraMap q.asIdeal.ResidueField K₂).comp
        (IsLocalRing.residue (Localization.AtPrime q.asIdeal))).comp
        (localPrimeMap f p q hq)) :
    letI : Algebra (Localization.AtPrime p.asIdeal) Rsh := ιR.toAlgebra
    letI : Algebra (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) :=
      (localPrimeMap f p q hq).toAlgebra
    ∃ (ψ : Rsh →+* Ssh) (hψ : IsLocalHom ψ),
      ψ.comp ιR = ιS.comp (localPrimeMap f p q hq) ∧
      ∃ q' : PrimeSpectrum
          (Rsh ⊗[Localization.AtPrime p.asIdeal]
            Localization.AtPrime q.asIdeal),
        q' = kernelPrime (tensorMapToField
          (((algebraMap K₁ K₂).comp eR.symm.toRingHom).comp
            (IsLocalRing.residue Rsh))
          ((algebraMap q.asIdeal.ResidueField K₂).comp
            (IsLocalRing.residue (Localization.AtPrime q.asIdeal))) hres) ∧
        IsTensorPrimeOver (maximalPrime (Localization.AtPrime q.asIdeal)) q' ∧
        ∃ e : Ssh ≃+* Localization.AtPrime q'.asIdeal,
          e.toRingHom.comp ιS = tensorLocalizationMapFromRight q' ∧
          e.toRingHom.comp ψ = tensorLocalizationMapFromLeft q' ∧
          RingHom.Finite ψ ∧
          (residueFieldMapOfLocal ψ hψ).comp eR.toRingHom =
              eS.toRingHom.comp (algebraMap K₁ K₂) ∧
            Module.Finite K₁ K₂ ∧
            IsPurelyInseparable K₁ K₂ := by
  sorry

/-- Strict henselization is compatible with quotients. -/
theorem quotient_strict_henselization
    {R Rsh : Type u} [CommRing R] [IsLocalRing R]
    [CommRing Rsh] [IsLocalRing Rsh]
    (ι : R →+* Rsh)
    (hι : IsStrictHenselization R Rsh ι)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) :
    letI : IsLocalRing (R ⧸ I) := quotientLocalRingOfLeMax I hI
    letI : IsLocalRing (Rsh ⧸ Ideal.map ι I) :=
      quotientLocalRingOfStrictHenselization ι hι I hI
    IsStrictHenselization (R ⧸ I) (Rsh ⧸ Ideal.map ι I)
      (quotientHenselizationMap ι I) := by
  sorry


/-! ## The local tensor-product lemma -/

/-- If one local map is integral and one of the residue extensions is purely
inseparable, the tensor product is local and both factor maps are local. -/
theorem local_tensor_with_integral
    {A B C : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
    (f : A →+* B) (g : A →+* C)
    (hf : IsLocalHom f) (hg : IsLocalHom g)
    (hintegral : RingHom.IsIntegral g)
    (hpure :
      IsPurelyInseparableExtension
          (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C)
          (residueFieldMapOfLocal g hg) ∨
      IsPurelyInseparableExtension
          (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
          (residueFieldMapOfLocal f hf)) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A C := g.toAlgebra
    IsLocalRing (B ⊗[A] C) ∧
      IsLocalHom (Algebra.TensorProduct.includeLeftRingHom :
        B →+* B ⊗[A] C) ∧
      IsLocalHom (Algebra.TensorProduct.includeRight.toRingHom :
        C →+* B ⊗[A] C) := by
  sorry

/-! ## Strict henselization after base change -/

/-- The four alternatives in the final base-change lemma. -/
def BaseChangeQuasiFiniteCondition
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (pA : PrimeSpectrum A) (pB : PrimeSpectrum B)
    (hp : PrimeSpectrum.comap f pB = pA) : Prop :=
  RingHom.QuasiFiniteAt f pB.asIdeal ∨
    IsFilteredColimitOfQuasiFinite f ∨
    IsFilteredColimitOfQuasiFinite (localPrimeMap f pA pB hp) ∨
    RingHom.IsIntegral f

/-- The map from a strict-henselization tensor product to the strict
henselization of the tensor product, assembled from the two functorial maps
to the target. -/
noncomputable def strictHenselizationBaseChangeMap
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C]
    [CommRing D] [Algebra A B] [Algebra A C] [Algebra A D]
    (f : B →+* D) (g : C →+* D)
    (hf : f.comp (algebraMap A B) = algebraMap A D)
    (hg : g.comp (algebraMap A C) = algebraMap A D) :
    B ⊗[A] C →+* D := by
  let f' : B →ₐ[A] D :=
    { toRingHom := f
      commutes' := fun r => by
        exact congrArg (fun z : A →+* D => z r) hf }
  let g' : C →ₐ[A] D :=
    { toRingHom := g
      commutes' := fun r => by
        exact congrArg (fun z : A →+* D => z r) hg }
  exact (Algebra.TensorProduct.lift f' g' (fun _ _ => Commute.all _ _)).toRingHom

/-- Under any of the four source hypotheses, the corresponding strict
henselization base-change map is an isomorphism.  The prime kernels, the
localization maps, and the compatible strict-henselization functorial maps
are all explicit parameters of the interface. -/
theorem base_change_strict_henselization
    {A B C κ Ash Bsh Csh Dsh : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Field κ]
    [CommRing Ash] [IsLocalRing Ash]
    [CommRing Bsh] [IsLocalRing Bsh]
    [CommRing Csh] [IsLocalRing Csh]
    [CommRing Dsh] [IsLocalRing Dsh]
    [IsSepClosed κ]
    [Algebra Ash Bsh] [Algebra Ash Csh] [Algebra Ash Dsh]
    (f : A →+* B) (g : A →+* C)
    (χ : tensorOfMaps f g →+* κ)
    (pA : PrimeSpectrum A) (pB : PrimeSpectrum B)
    (pC : PrimeSpectrum C) (pD : PrimeSpectrum (tensorOfMaps f g))
    (hpA : pA = kernelPrime (χ.comp ((tensorLeftMap f g).comp f)))
    (hpB : pB = kernelPrime (χ.comp (tensorLeftMap f g)))
    (hpC : pC = kernelPrime (χ.comp (tensorRightMap f g)))
    (hpD : pD = kernelPrime χ)
    (hAB : PrimeSpectrum.comap f pB = pA)
    (hAC : PrimeSpectrum.comap g pC = pA)
    (hBD : PrimeSpectrum.comap (tensorLeftMap f g) pD = pB)
    (hCD : PrimeSpectrum.comap (tensorRightMap f g) pD = pC)
    (ιA : Localization.AtPrime pA.asIdeal →+* Ash)
    (hιA : IsStrictHenselization
      (Localization.AtPrime pA.asIdeal) Ash ιA)
    (ιB : Localization.AtPrime pB.asIdeal →+* Bsh)
    (hιB : IsStrictHenselization
      (Localization.AtPrime pB.asIdeal) Bsh ιB)
    (ιC : Localization.AtPrime pC.asIdeal →+* Csh)
    (hιC : IsStrictHenselization
      (Localization.AtPrime pC.asIdeal) Csh ιC)
    (ιD : Localization.AtPrime pD.asIdeal →+* Dsh)
    (hιD : IsStrictHenselization
      (Localization.AtPrime pD.asIdeal) Dsh ιD)
    (hAtoB : (algebraMap Ash Bsh).comp ιA =
      ιB.comp (localPrimeMap f pA pB hAB))
    (hAtoC : (algebraMap Ash Csh).comp ιA =
      ιC.comp (localPrimeMap g pA pC hAC))
    (bD : Bsh →+* Dsh) (cD : Csh →+* Dsh)
    (hbD : IsLocalHom bD) (hcD : IsLocalHom cD)
    (hbD_comm : bD.comp ιB =
      ιD.comp (localPrimeMap (tensorLeftMap f g) pB pD hBD))
    (hcD_comm : cD.comp ιC =
      ιD.comp (localPrimeMap (tensorRightMap f g) pC pD hCD))
    (hbD_base : bD.comp (algebraMap Ash Bsh) = algebraMap Ash Dsh)
    (hcD_base : cD.comp (algebraMap Ash Csh) = algebraMap Ash Dsh)
    (hcondition : BaseChangeQuasiFiniteCondition f pA pB hAB) :
    ∃ e : Bsh ⊗[Ash] Csh ≃+* Dsh,
      e.toRingHom = strictHenselizationBaseChangeMap bD cD
        hbD_base hcD_base := by
  sorry

end
end Formalization.Books.Algebra.Unit156
