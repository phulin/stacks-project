import Formalization.Books.Algebra.Unit154.FilteredColimitsEtale
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 155: Henselization and strict henselization

This file records source-facing interfaces for the construction and
functoriality of henselizations and strict henselizations.
-/

namespace Formalization.Books.Algebra.Unit155

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit153
open Formalization.Books.Algebra.Unit154
open scoped TensorProduct

noncomputable section

universe u v

/-! ## The two constructions -/

/-- A separable algebraic closure used to define a strict henselization. -/
def IsSeparableAlgebraicClosure
    (k K : Type u) [Field k] [Field K] [Algebra k K] : Prop :=
  Algebra.IsAlgebraic k K ∧ Algebra.IsSeparable k K ∧ IsSepClosed K

/-- The four properties in the source definition of a henselization map. -/
def IsHenselizationMap
    (R A : Type u) [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] (f : R →+* A) : Prop :=
  IsLocalHom f ∧ HenselianLocalRing A ∧
    IsFilteredColimitOfEtale f ∧
      Ideal.map f (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal A ∧
        Nonempty
          (IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField A)

/-- The source-facing property of a strict henselization with a specified
separable algebraic closure of the residue field. -/
def IsStrictHenselizationMap
    (R A K : Type u) [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    (f : R →+* A) (_hK : IsSeparableAlgebraicClosure
      (IsLocalRing.ResidueField R) K) : Prop :=
  IsSeparableAlgebraicClosure (IsLocalRing.ResidueField R) K ∧
    IsLocalHom f ∧ StrictlyHenselianLocalRing A ∧
    IsFilteredColimitOfEtale f ∧
      Ideal.map f (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal A ∧
        Nonempty (K ≃+* IsLocalRing.ResidueField A)

/-- Two maps over `R` are isomorphic as maps from `R`. -/
def IsomorphicOver
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) : Prop :=
  ∃ e : A ≃+* B, e.toRingHom.comp f = g

/-- The source construction of the henselization, bundled with all four
properties of its local ring and residue field. -/
structure HenselizationData
    (R : Type u) [CommRing R] [IsLocalRing R] where
  carrier : Type u
  [commRingCarrier : CommRing carrier]
  [localRingCarrier : IsLocalRing carrier]
  map : R →+* carrier
  localMap : IsLocalHom map
  flat : RingHom.Flat map
  henselian : HenselianLocalRing carrier
  etaleColimit : IsFilteredColimitOfEtale map
  maximalIdeal_eq :
    Ideal.map map (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal carrier
  residueEquiv :
    IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField carrier

/-- The diagram `R → Rʰ → Rˢʰ` and the properties asserted for its two
targets in the strict henselization lemma. -/
structure StrictHenselizationData
    (R K : Type u) [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K] where
  henselization : Type u
  [commRingHenselization : CommRing henselization]
  [localRingHenselization : IsLocalRing henselization]
  strictHenselization : Type u
  [commRingStrictHenselization : CommRing strictHenselization]
  [localRingStrictHenselization : IsLocalRing strictHenselization]
  henselizationMap : R →+* henselization
  henselizationLocal : IsLocalHom henselizationMap
  henselian : HenselianLocalRing henselization
  henselizationEtaleColimit :
    IsFilteredColimitOfEtale henselizationMap
  strictMap : R →+* strictHenselization
  strictLocal : IsLocalHom strictMap
  strictHenselian : StrictlyHenselianLocalRing strictHenselization
  strictEtaleColimit : IsFilteredColimitOfEtale strictMap
  mapFromHenselization : henselization →+* strictHenselization
  mapFromHenselizationLocal : IsLocalHom mapFromHenselization
  commutes : mapFromHenselization.comp henselizationMap = strictMap
  henselizationMaximalIdeal_eq :
    Ideal.map henselizationMap (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal henselization
  strictMaximalIdeal_eq :
    Ideal.map strictMap (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal strictHenselization
  henselizationResidueEquiv :
    IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField henselization
  strictResidueEquiv : K ≃+* IsLocalRing.ResidueField strictHenselization
  henselizationFlat : RingHom.Flat henselizationMap
  mapFromHenselizationFlat : RingHom.Flat mapFromHenselization
  closure : IsSeparableAlgebraicClosure
    (IsLocalRing.ResidueField R) K

theorem exists_henselization
    (R : Type u) [CommRing R] [IsLocalRing R] :
    Nonempty (HenselizationData R) := by
  sorry

theorem exists_strict_henselization
    (R : Type u) [CommRing R] [IsLocalRing R]
    (K : Type u) [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    (hK : IsSeparableAlgebraicClosure
      (IsLocalRing.ResidueField R) K) :
    Nonempty (StrictHenselizationData R K) := by
  sorry

/-! ## The definition and the uniqueness assertion -/

/-- A strict henselization in the sense of the source, allowing a choice of
the separable algebraic closure of the residue field. -/
def IsStrictHenselization
    (R A : Type u) [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] (f : R →+* A) : Prop :=
  ∃ (K : Type u) (_ : Field K)
    (_ : Algebra (IsLocalRing.ResidueField R) K)
    (hK : IsSeparableAlgebraicClosure
      (IsLocalRing.ResidueField R) K),
    IsStrictHenselizationMap R A K f hK

/-- The henselization map named by the source definition. -/
def henselizationMap
    {R : Type u} [CommRing R] [IsLocalRing R]
    (D : HenselizationData R) :=
  D.map

/-- A strict henselization map named by the source definition. -/
def strictHenselizationMap
    {R A : Type u} [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] (f : R →+* A)
    (_h : IsStrictHenselization R A f) : R →+* A :=
  f

theorem henselization_unique_up_to_unique_iso
    {R A B : Type u} [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : R →+* A) (g : R →+* B)
    (hf : IsHenselizationMap R A f)
    (hg : IsHenselizationMap R B g) :
    ∃! e : A ≃+* B, e.toRingHom.comp f = g := by
  sorry

theorem strict_henselization_unique_up_to_unique_iso
    {R A B : Type u} [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : R →+* A) (g : R →+* B)
    (hf : IsStrictHenselization R A f)
    (hg : IsStrictHenselization R B g) :
    ∃ e : A ≃+* B, e.toRingHom.comp f = g := by
  sorry

theorem strict_henselization_unique_up_to_unique_iso_fixed_residue_field
    {R A B K : Type u} [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (hK : IsSeparableAlgebraicClosure
      (IsLocalRing.ResidueField R) K)
    (f : R →+* A) (g : R →+* B)
    (hf : IsStrictHenselizationMap R A K f hK)
    (hg : IsStrictHenselizationMap R B K g hK) :
    ∃! e : A ≃+* B, e.toRingHom.comp f = g := by
  sorry

/-! ## The alternative construction from finite residue extensions -/

/-- A finite separable intermediate extension of a chosen separable algebraic
closure. -/
structure FiniteSeparableSubextension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    where
  intermediate : Type u
  [fieldIntermediate : Field intermediate]
  [algebraIntermediate : Algebra k intermediate]
  [algebraIntoClosure : Algebra intermediate K]
  [tower : IsScalarTower k intermediate K]
  finite : Module.Finite k intermediate
  separable : Algebra.IsSeparable k intermediate
  embedding : intermediate →ₐ[k] K
  closure : IsSeparableAlgebraicClosure k K

/-- A finite étale local lift of a finite separable residue-field extension. -/
structure FiniteEtaleLocalExtensionData
    (H K K' : Type u) [CommRing H] [IsLocalRing H]
    [Field K] [CommRing K'] [Field K'] [Algebra K K'] where
  carrier : Type u
  [commRingCarrier : CommRing carrier]
  [localRingCarrier : IsLocalRing carrier]
  map : H →+* carrier
  localMap : IsLocalHom map
  finiteEtale : RingHom.Etale map
  finite : RingHom.Finite map
  residueEquiv : K' ≃+* IsLocalRing.ResidueField carrier

theorem exists_unique_finite_etale_local_extension
    {H K K' : Type u} [CommRing H] [IsLocalRing H]
    [Field K] [Field K'] [Algebra K K']
    (hH : IsHenselian H)
    (E : FiniteSeparableSubextension K K') :
    Nonempty (FiniteEtaleLocalExtensionData H K K') := by
  sorry

/-- The directed family of finite étale local extensions used in the
alternative construction of the strict henselization. -/
structure StrictHenselizationExtensionFamily
    (R H K : Type u) [CommRing R] [IsLocalRing R]
    [CommRing H] [IsLocalRing H] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] where
  index : Type u
  [indexCategory : Category index]
  [indexFiltered : IsFiltered index]
  extension : index → Type u
  [extensionCommRing : ∀ i, CommRing (extension i)]
  [extensionLocalRing : ∀ i, IsLocalRing (extension i)]
  map : ∀ i, H →+* extension i
  localMap : ∀ i, IsLocalHom (map i)
  finiteEtale : ∀ i, RingHom.Etale (map i)
  finite : ∀ i, RingHom.Finite (map i)
  transition : ∀ {i j : index}, (i ⟶ j) → extension i →+* extension j
  transition_comm : ∀ {i j : index} (α : i ⟶ j),
    (transition α).comp (map i) = map j
  colimitCarrier : Type u
  [commRingColimit : CommRing colimitCarrier]
  [localRingColimit : IsLocalRing colimitCarrier]
  colimitMap : H →+* colimitCarrier
  colimitLocal : IsLocalHom colimitMap
  colimitStrict : StrictlyHenselianLocalRing colimitCarrier
  colimitEtale : IsFilteredColimitOfEtale colimitMap
  colimitResidueEquiv : K ≃+* IsLocalRing.ResidueField colimitCarrier
  unionMap : ∀ i, extension i →+* colimitCarrier
  union_comm : ∀ i, (unionMap i).comp (map i) = colimitMap

theorem alternative_strict_henselization
    {R H : Type u} [CommRing R] [IsLocalRing R]
    [CommRing H] [IsLocalRing H]
    (f : R →+* H) (hH : IsHenselizationMap R H f)
    (K : Type u) [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    (hK : IsSeparableAlgebraicClosure
      (IsLocalRing.ResidueField R) K) :
    Nonempty (StrictHenselizationExtensionFamily R H K) ∧
      IsSeparableAlgebraicClosure (IsLocalRing.ResidueField R) K := by
  sorry

/-! ## Functoriality for local maps -/

theorem henselian_functorial_prepare
    {R S A Sh : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [CommRing A]
    [CommRing Sh] [IsLocalRing Sh]
    (φ : R →+* S) (hφ : IsLocalHom φ)
    (f : R →+* A) (hf : RingHom.Etale f)
    (q : PrimeSpectrum A)
    (hq : q.asIdeal.comap f = IsLocalRing.maximalIdeal R)
    (hκ : Nonempty (q.asIdeal.ResidueField ≃+*
      IsLocalRing.ResidueField R))
    (ι : S →+* Sh) (hι : IsHenselizationMap S Sh ι) :
    ∃! g : A →+* Sh,
      g.comp f = ι.comp φ ∧
        PrimeSpectrum.comap g (maximalPrime Sh) = q := by
  sorry

theorem henselian_functorial
    {R S Rh Sh : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [CommRing Rh] [IsLocalRing Rh]
    [CommRing Sh] [IsLocalRing Sh]
    (φ : R →+* S) (hφ : IsLocalHom φ)
    (ιR : R →+* Rh) (hιR : IsHenselizationMap R Rh ιR)
    (ιS : S →+* Sh) (hιS : IsHenselizationMap S Sh ιS) :
    ∃! ψ : Rh →+* Sh,
      IsLocalHom ψ ∧ ψ.comp ιR = ιS.comp φ := by
  sorry

/-- A map between chosen separable residue-field closures together with the
compatibility required over the residue fields of a local map. -/
structure CompatibleResidueFieldMap
    {R S K₁ K₂ : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Field K₁] [Field K₂]
    [Algebra (IsLocalRing.ResidueField R) K₁]
    [Algebra (IsLocalRing.ResidueField S) K₂]
    (φ : R →+* S) where
  underlying : R →+* S
  underlying_eq : underlying = φ
  map : K₁ →+* K₂
  baseMap : IsLocalRing.ResidueField R →+*
    IsLocalRing.ResidueField S
  commutes :
    map.comp (algebraMap (IsLocalRing.ResidueField R) K₁) =
      (algebraMap (IsLocalRing.ResidueField S) K₂).comp baseMap

/-! ## Henselization at a prime -/

/-- The two colimit presentations occurring in the alternative construction
at a prime. -/
structure HenselizationAtPrimeData
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) where
  carrier : Type u
  [commRingCarrier : CommRing carrier]
  [localRingCarrier : IsLocalRing carrier]
  map : Localization.AtPrime p.asIdeal →+* carrier
  localMap : IsLocalHom map
  henselian : HenselianLocalRing carrier
  localizedHenselization : IsFilteredColimitOfEtale map
  pairColimit :
    IsFilteredColimitOfEtale
      (map.comp
        (algebraMap R (Localization.AtPrime p.asIdeal)))
  maximalIdeal_eq :
    Ideal.map map (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) =
      IsLocalRing.maximalIdeal carrier

/-- The strict version of the two colimit presentations at a prime. -/
structure StrictHenselizationAtPrimeData
    (R K : Type u) [CommRing R] (p : PrimeSpectrum R)
    [Field K] [Algebra (p.asIdeal.ResidueField) K] where
  carrier : Type u
  [commRingCarrier : CommRing carrier]
  [localRingCarrier : IsLocalRing carrier]
  map : Localization.AtPrime p.asIdeal →+* carrier
  localMap : IsLocalHom map
  strictHenselian : StrictlyHenselianLocalRing carrier
  localizedStrictHenselization : IsFilteredColimitOfEtale map
  pairColimit :
    IsFilteredColimitOfEtale
      (map.comp (algebraMap R (Localization.AtPrime p.asIdeal)))
  residueEquiv : K ≃+* IsLocalRing.ResidueField carrier
  closure : IsSeparableAlgebraicClosure p.asIdeal.ResidueField K

theorem henselization_at_prime_colimit
    (R : Type u) [CommRing R] (p : PrimeSpectrum R) :
    Nonempty (HenselizationAtPrimeData R p) := by
  sorry

theorem henselian_functorial_improve
    {R S Rh Sh : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    [CommRing Rh] [IsLocalRing Rh] [CommRing Sh] [IsLocalRing Sh]
    [Algebra R Rh] [Algebra R S]
    (φ : R →+* S) (q : PrimeSpectrum S) (p : PrimeSpectrum R)
    (hq : q.asIdeal.comap φ = p.asIdeal)
    (ιR : R →+* Rh) (hιR : IsHenselizationMap R Rh ιR)
    (ιS : S →+* Sh) (hιS : IsHenselizationMap S Sh ιS) :
    ∃ q' : PrimeSpectrum (Rh ⊗[R] S),
      q'.asIdeal.comap
          (Algebra.TensorProduct.includeLeftRingHom :
            Rh →+* Rh ⊗[R] S) =
          IsLocalRing.maximalIdeal Rh ∧
        q'.asIdeal.comap
            (Algebra.TensorProduct.includeRight.toRingHom :
              S →+* Rh ⊗[R] S) = q.asIdeal := by
  sorry

/-! ## Strict functoriality -/

theorem strictly_henselian_functorial_prepare
    {R S A Ssh K : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [CommRing A]
    [CommRing Ssh] [IsLocalRing Ssh] [Field K]
    [Algebra (IsLocalRing.ResidueField S) K]
    (φ : R →+* S) (hφ : IsLocalHom φ)
    (ι : S →+* Ssh)
    (hι : IsStrictHenselizationMap S Ssh K ι (by sorry))
    (f : R →+* A) (hf : RingHom.Etale f) (q : PrimeSpectrum A)
    (hq : q.asIdeal.comap f = IsLocalRing.maximalIdeal R)
    (residueMap : q.asIdeal.ResidueField →+* K)
    (e : K ≃+* IsLocalRing.ResidueField Ssh) :
    ∃! g : A →+* Ssh,
      g.comp f = ι.comp φ ∧
        PrimeSpectrum.comap g (maximalPrime Ssh) = q ∧
        ∀ a : A,
          residueMap
              (algebraMap (A ⧸ q.asIdeal) q.asIdeal.ResidueField
                (Ideal.Quotient.mk q.asIdeal a)) =
            e.symm (IsLocalRing.residue Ssh (g a)) := by
  sorry

theorem strictly_henselian_functorial
    {R S Rh Sh K₁ K₂ : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [CommRing Rh] [IsLocalRing Rh]
    [CommRing Sh] [IsLocalRing Sh] [Field K₁] [Field K₂]
    [Algebra (IsLocalRing.ResidueField R) K₁]
    [Algebra (IsLocalRing.ResidueField S) K₂]
    (φ : R →+* S) (hφ : IsLocalHom φ)
    (ιR : R →+* Rh) (hιR : IsStrictHenselizationMap R Rh K₁ ιR (by sorry))
    (ιS : S →+* Sh) (hιS : IsStrictHenselizationMap S Sh K₂ ιS (by sorry))
    (residueData : CompatibleResidueFieldMap φ)
    (eR : K₁ ≃+* IsLocalRing.ResidueField Rh)
    (eS : K₂ ≃+* IsLocalRing.ResidueField Sh) :
    ∃! ψ : Rh →+* Sh,
      IsLocalHom ψ ∧ ψ.comp ιR = ιS.comp φ ∧
        ∀ x : Rh,
          residueData.map (eR.symm (IsLocalRing.residue Rh x)) =
            eS.symm (IsLocalRing.residue Sh (ψ x)) := by
  sorry

theorem strict_henselization_at_prime_colimit
    (R : Type u) [CommRing R] (p : PrimeSpectrum R)
    (K : Type u) [Field K]
    [Algebra (p.asIdeal.ResidueField) K]
    (hK : IsSeparableAlgebraicClosure p.asIdeal.ResidueField K) :
    Nonempty (StrictHenselizationAtPrimeData R K p) := by
  sorry

theorem strictly_henselian_functorial_improve
    {R S Rh Sh K₁ K₂ : Type u} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    [CommRing Rh] [IsLocalRing Rh] [CommRing Sh] [IsLocalRing Sh]
    [Field K₁] [Field K₂]
    [Algebra (IsLocalRing.ResidueField R) K₁]
    [Algebra (IsLocalRing.ResidueField S) K₂]
    [Algebra R Rh] [Algebra R S]
    (φ : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : q.asIdeal.comap φ = p.asIdeal)
    (ιR : R →+* Rh) (ιS : S →+* Sh)
    (residueMap : K₁ →+* K₂) :
    ∃ q' : PrimeSpectrum (Rh ⊗[R] S),
      q'.asIdeal.comap
          (Algebra.TensorProduct.includeLeftRingHom :
            Rh →+* Rh ⊗[R] S) = IsLocalRing.maximalIdeal Rh ∧
        q'.asIdeal.comap
          (Algebra.TensorProduct.includeRight.toRingHom :
            S →+* Rh ⊗[R] S) = q.asIdeal ∧
        ∃ j : Localization.AtPrime q'.asIdeal →+* Sh,
          IsStrictHenselization (Localization.AtPrime q'.asIdeal)
            Sh j := by
  sorry

/-! ## Strict henselization after a residue-field-preserving map -/

theorem strict_henselization_from_henselization_map
    {R S Rh Sh Rsh Ssh : Type u} [CommRing R] [CommRing S]
    [CommRing Rh] [IsLocalRing Rh] [CommRing Sh] [IsLocalRing Sh]
    [CommRing Rsh] [IsLocalRing Rsh]
    [CommRing Ssh] [IsLocalRing Ssh]
    [Algebra Rh Sh] [Algebra Rh Rsh]
    (φ : R →+* S) (q : PrimeSpectrum S) (p : PrimeSpectrum R)
    (hq : q.asIdeal.comap φ = p.asIdeal)
    (hκ : Nonempty (p.asIdeal.ResidueField ≃+* q.asIdeal.ResidueField))
    (ιRh : Localization.AtPrime p.asIdeal →+* Rh)
    (ιSh : Localization.AtPrime q.asIdeal →+* Sh)
    (ιRsh : Localization.AtPrime p.asIdeal →+* Rsh)
    (ιSsh : Localization.AtPrime q.asIdeal →+* Ssh)
    (hιRh : IsHenselizationMap (Localization.AtPrime p.asIdeal) Rh ιRh)
    (hιSh : IsHenselizationMap (Localization.AtPrime q.asIdeal) Sh ιSh)
    (hιRsh : IsStrictHenselization
      (Localization.AtPrime p.asIdeal) Rsh ιRsh)
    (hιSsh : IsStrictHenselization
      (Localization.AtPrime q.asIdeal) Ssh ιSsh) :
    Nonempty (Ssh ≃+* (Sh ⊗[Rh] Rsh)) := by
  sorry

/-! ## Flatness and locality of the two canonical maps -/

end
end Formalization.Books.Algebra.Unit155
