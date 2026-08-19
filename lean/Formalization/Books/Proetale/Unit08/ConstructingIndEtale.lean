import Formalization.Books.Proetale.Unit05.ConstructingWLocal
import Formalization.Books.Proetale.Unit07.IndEtale
import Formalization.Books.Algebra.Unit143.EtaleRingMaps
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Pro-étale Cohomology, Chapter 8: Constructing ind-étale algebras

This file formalizes the source's explicit construction of a faithfully flat
ind-étale algebra with sections for faithfully flat étale maps, together with
the quotient, localization, and w-local residue-field-extension interfaces
used later in the chapter.
-/

namespace Formalization.Books.Proetale.Unit08

open Set Function CategoryTheory CategoryTheory.Limits
open Formalization.Books.Algebra.Unit153
open Formalization.Books.Proetale.Unit02
open Formalization.Books.Proetale.Unit04
open Formalization.Books.Proetale.Unit05
open Formalization.Books.Proetale.Unit07
open scoped TensorProduct

universe u v

noncomputable section

/-! ## Standard smooth étale stages and their finite tensor products -/

/- The source begins by identifying étale maps with standard smooth maps of
   relative dimension zero.  The project already has the canonical Mathlib
   predicate and the Chapter 143 interface, so no parallel predicate is
   introduced here. -/
theorem etale_is_standardSmoothOfRelativeDimension_zero
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Etale) :
    @Algebra.IsStandardSmoothOfRelativeDimension 0 A B _ _ f.toAlgebra := by
  sorry

/- A small object package lets the finite tensor-product construction retain
   its base-algebra structure while its carrier varies recursively. -/
structure AlgebraObject (A : Type u) [CommRing A] where
  carrier : Type u
  [commRingCarrier : CommRing carrier]
  [algebraCarrier : Algebra A carrier]

instance AlgebraObject.commRing {A : Type u} [CommRing A]
    (B : AlgebraObject A) : CommRing B.carrier := B.commRingCarrier

instance AlgebraObject.algebra {A : Type u} [CommRing A]
    (B : AlgebraObject A) : Algebra A B.carrier := B.algebraCarrier

/-- A faithfully flat standard-smooth algebra of relative dimension zero.

This is the source's stage type `S(A)`, expressed with Mathlib's canonical
standard-smooth predicate.  Étaleness is equivalent to this predicate by the
Chapter 143 interface. -/
def StandardSmoothAlgebra (A : Type u) [CommRing A] :=
  {B : AlgebraObject A //
    Algebra.IsStandardSmoothOfRelativeDimension 0 A B.carrier ∧
      RingHom.FaithfullyFlat (algebraMap A B.carrier)}

/- The tensor product is formed from a finite list; `Finset.toList` supplies
   the canonical order used by the source's finite subset presentation. -/
noncomputable def tensorProductList (A : Type u) [CommRing A] :
    List (StandardSmoothAlgebra A) → AlgebraObject A
  | [] => { carrier := A }
  | B :: Bs =>
      let C := tensorProductList A Bs
      { carrier := B.1.carrier ⊗[A] C.carrier }

/-- The finite tensor product `B_E` attached to a finite subset `E` of `S(A)`. -/
noncomputable def finiteEtaleTensor {A : Type u} [CommRing A]
    (E : Finset (StandardSmoothAlgebra A)) : AlgebraObject A :=
  tensorProductList A E.toList

/- The source calls the type of stages `S(A)` and its finite-subset poset
   `I(A)`. -/
abbrev S (A : Type u) [CommRing A] := StandardSmoothAlgebra A
abbrev I (A : Type u) [CommRing A] := Finset (S A)

theorem standardSmoothAlgebra_isEtale
    {A : Type u} [CommRing A] (B : S A) :
    (algebraMap A B.1.carrier).Etale := by
  sorry

instance finiteEtaleIndex_isFiltered (A : Type u) [CommRing A] :
    IsFiltered (I A) := by
  infer_instance

theorem I_isDirected (A : Type u) [CommRing A] :
    IsFiltered (I A) := by
  infer_instance

/- The canonical insertion map exists by the universal property of the
   tensor product.  Its choice is only needed to make the source's diagram a
   concrete Lean functor; the displayed compatibility is retained as a
   theorem immediately below. -/
theorem finiteEtaleTensorTransition_exists
    {A : Type u} [CommRing A] {E E' : I A} (h : E ⊆ E') :
    ∃ g : (finiteEtaleTensor E).carrier →ₐ[A]
        (finiteEtaleTensor E').carrier,
      g.toRingHom.comp (algebraMap A (finiteEtaleTensor E).carrier) =
        algebraMap A (finiteEtaleTensor E').carrier := by
  sorry

noncomputable def finiteEtaleTensorTransition
    {A : Type u} [CommRing A] {E E' : I A} (h : E ⊆ E') :
    (finiteEtaleTensor E).carrier →ₐ[A] (finiteEtaleTensor E').carrier :=
  Classical.choose (finiteEtaleTensorTransition_exists h)

theorem finiteEtaleTensorTransition_commutes
    {A : Type u} [CommRing A] {E E' : I A} (h : E ⊆ E') :
    (finiteEtaleTensorTransition h).toRingHom.comp
        (algebraMap A (finiteEtaleTensor E).carrier) =
      algebraMap A (finiteEtaleTensor E').carrier := by
  exact Classical.choose_spec (finiteEtaleTensorTransition_exists h)

/- The tensor product of the faithfully flat étale stages is again a
   faithfully flat étale algebra, and each insertion transition is étale. -/
theorem finiteEtaleTensor_faithfullyFlat_etale
    {A : Type u} [CommRing A] (E : I A) :
    RingHom.FaithfullyFlat (algebraMap A (finiteEtaleTensor E).carrier) ∧
      (algebraMap A (finiteEtaleTensor E).carrier).Etale := by
  sorry

theorem finiteEtaleTensorTransition_isEtale
    {A : Type u} [CommRing A] {E E' : I A} (h : E ⊆ E') :
    (finiteEtaleTensorTransition h).toRingHom.Etale := by
  sorry

/- The insertion maps satisfy the identity and composition laws; these are
   the categorical form of the source's transition-map assertion. -/
noncomputable def finiteEtaleTensorDiagram {A : Type u} [CommRing A] :
    I A ⥤ CommRingCat :=
  { obj := fun E => CommRingCat.of (finiteEtaleTensor E).carrier
    map := fun {E E'} h =>
      CommRingCat.ofHom (finiteEtaleTensorTransition (leOfHom h)).toRingHom
    map_id := by
      sorry
    map_comp := by
      sorry }

/-! ## The first colimit `T(A)` and its iteration -/

/-- Every faithfully flat étale map out of `A` has a retraction. -/
def HasFaithfullyFlatEtaleRetractions (A : Type u) [CommRing A] : Prop :=
  ∀ {B : Type u} [CommRing B] (f : A →+* B),
    RingHom.FaithfullyFlat f → f.Etale →
      ∃ r : B →+* A, r.comp f = RingHom.id A

/- The literal collection of all standard-smooth algebras is one universe
   larger than the carrier universe of `A`.  The source's set-theoretic
   colimit is therefore packaged by its filtered-colimit data at the fixed
   carrier universe used by the project.  The finite tensor-product diagram
   above records the source stages and transition maps; the fields below
   record its colimit and cocone interfaces without introducing a universe
   lift into every later iterate. -/
structure TConstruction (A : Type u) [CommRing A] where
  carrier : Type u
  [commRingCarrier : CommRing carrier]
  cocone : Cocone (finiteEtaleTensorDiagram (A := A))
  targetIso : cocone.pt ≅ CommRingCat.of carrier
  isColimit : IsColimit cocone
  map : A →+* carrier
  stageMap : ∀ E : I A, (finiteEtaleTensor E).carrier →+* carrier
  stageMap_from_cocone : ∀ E : I A,
    stageMap E = (targetIso.hom.hom.comp (cocone.ι.app E).hom)
  stageMap_comm : ∀ E : I A,
    (stageMap E).comp (algebraMap A (finiteEtaleTensor E).carrier) = map
  stageMap_compat : ∀ {E E' : I A} (h : E ⊆ E'),
    (stageMap E').comp (finiteEtaleTensorTransition h).toRingHom = stageMap E
  map_from_empty :
    map = (targetIso.hom.hom.comp
      (cocone.ι.app (∅ : I A)).hom).comp
        (algebraMap A (finiteEtaleTensor (∅ : I A)).carrier)
  faithfullyFlat : RingHom.FaithfullyFlat map
  indEtale : IsIndEtale map

theorem exists_TConstruction (A : Type u) [CommRing A] :
    Nonempty (TConstruction A) := by
  sorry

noncomputable def TData (A : Type u) [CommRing A] : TConstruction A :=
  Classical.choice (exists_TConstruction A)

instance TData.commRing (A : Type u) [CommRing A] :
    CommRing (TData A).carrier :=
  (TData A).commRingCarrier

/-- The colimit `T(A) = colim_E B_E`, represented by its cocone data. -/
noncomputable def T (A : Type u) [CommRing A] : CommRingCat := by
  letI : CommRing (TData A).carrier := (TData A).commRingCarrier
  exact CommRingCat.of (TData A).carrier

noncomputable def TMap (A : Type u) [CommRing A] :
    A →+* (TData A).carrier :=
  (TData A).map

/-- `T(A)` is faithfully flat and ind-étale over `A`. -/
theorem T_faithfullyFlat_indEtale (A : Type u) [CommRing A] :
    RingHom.FaithfullyFlat (TMap A) ∧ IsIndEtale (TMap A) := by
  exact ⟨(TData A).faithfullyFlat, (TData A).indEtale⟩

/- The iterated colimit construction is represented by the same source-facing
   `T` interface at each stage. -/
noncomputable def TIterate (A : Type u) [CommRing A] : ℕ → CommRingCat
  | 0 => CommRingCat.of A
  | Nat.succ n => T (TIterate A n : Type u)

noncomputable def TIterateMap {A : Type u} [CommRing A] (n : ℕ) :
    (TIterate A n : Type u) →+* (TIterate A (Nat.succ n) : Type u) :=
  TMap (TIterate A n : Type u)

theorem exists_TIterateTransition {A : Type u} [CommRing A]
    (m n : ℕ) (h : m ≤ n) :
    Nonempty (TIterate A m ⟶ TIterate A n) := by
  sorry

noncomputable def TIterateTransition {A : Type u} [CommRing A]
    {m n : ℕ} (h : m ≤ n) : TIterate A m ⟶ TIterate A n :=
  Classical.choice (exists_TIterateTransition m n h)

/- The iterated stages form the filtered diagram used for `C`. -/
noncomputable def TIterateDiagram {A : Type u} [CommRing A] :
    ℕ ⥤ CommRingCat :=
  { obj := TIterate A
    map := fun {m n} h => TIterateTransition (leOfHom h)
    map_id := by
      sorry
    map_comp := by
      sorry }

/-- The filtered colimit of the iterated `T` stages. -/
structure CConstruction (A : Type u) [CommRing A] where
  carrier : Type u
  [commRingCarrier : CommRing carrier]
  cocone : Cocone (TIterateDiagram (A := A))
  targetIso : cocone.pt ≅ CommRingCat.of carrier
  isColimit : IsColimit cocone
  map : A →+* carrier
  map_from_zero :
    map = (targetIso.hom.hom.comp
      (cocone.ι.app 0).hom).comp (RingHom.id A)
  faithfullyFlat : RingHom.FaithfullyFlat map
  indEtale : IsIndEtale map
  sections : HasFaithfullyFlatEtaleRetractions carrier

theorem exists_CConstruction (A : Type u) [CommRing A] :
    Nonempty (CConstruction A) := by
  sorry

noncomputable def CData (A : Type u) [CommRing A] : CConstruction A :=
  Classical.choice (exists_CConstruction A)

/-- The colimit `C = colim_n Tⁿ(A)` in the first-construction lemma. -/
abbrev C (A : Type u) [CommRing A] : Type u := (CData A).carrier

instance C.commRing (A : Type u) [CommRing A] : CommRing (C A) :=
  (CData A).commRingCarrier

noncomputable def CMap (A : Type u) [CommRing A] : A →+* C A :=
  (CData A).map

instance C.algebra (A : Type u) [CommRing A] : Algebra A (C A) :=
  (CMap A).toAlgebra

/-! ## Retractions and the first-construction lemma -/

/-- The first construction produces a faithfully flat ind-étale algebra with
sections for all faithfully flat étale algebras over it. -/
theorem firstConstruction_properties (A : Type u) [CommRing A] :
    RingHom.FaithfullyFlat (CMap A) ∧
      IsIndEtale (CMap A) ∧
        HasFaithfullyFlatEtaleRetractions (C A : Type u) := by
  exact ⟨(CData A).faithfullyFlat, (CData A).indEtale, (CData A).sections⟩

theorem firstConstruction_has_retraction
    {A B : Type u} [CommRing A] [CommRing B]
    (f : (C A : Type u) →+* B)
    (hflat : RingHom.FaithfullyFlat f) (hetale : f.Etale) :
    ∃ r : B →+* (C A : Type u), r.comp f = RingHom.id (C A : Type u) := by
  exact (firstConstruction_properties A).2.2 f hflat hetale

/-! ## Cardinality and functoriality remarks -/

theorem T_cardinal_le (A : Type u) [CommRing A] (κ : Cardinal)
    (hA : Cardinal.mk A ≤ κ) (hκ : ℵ₀ ≤ κ) :
    Cardinal.mk (T A) ≤ κ := by
  sorry

theorem C_cardinal_le (A : Type u) [CommRing A] (κ : Cardinal)
    (hA : Cardinal.mk A ≤ κ) (hκ : ℵ₀ ≤ κ) :
    Cardinal.mk (C A) ≤ κ := by
  sorry

/-- The commutative square expressing the functorial construction `T`. -/
structure TFunctoriality {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') where
  map : (TData A).carrier →+* (TData A').carrier
  commutes : map.comp (TMap A) = (TMap A').comp f

theorem exists_TFunctoriality
    {A A' : Type u} [CommRing A] [CommRing A'] (f : A →+* A') :
    Nonempty (TFunctoriality f) := by
  sorry

/-! ## Quotients, strict henselian localizations, and the localized piece -/

theorem quotient_has_faithfullyFlatEtaleRetractions
    (A : Type u) [CommRing A]
    (hA : HasFaithfullyFlatEtaleRetractions A) (I : Ideal A) :
    HasFaithfullyFlatEtaleRetractions (A ⧸ I) := by
  sorry

/-- Every localization at a maximal ideal is strictly henselian. -/
def EveryMaximalLocalizationStrictlyHenselian
    (A : Type u) [CommRing A] : Prop :=
  ∀ m : {m : Ideal A // m.IsMaximal},
    letI : m.1.IsMaximal := m.2
    @StrictlyHenselianLocalRing (Localization.AtPrime m.1) inferInstance

theorem retractions_imply_strictlyHenselian
    (A : Type u) [CommRing A]
    (hA : HasFaithfullyFlatEtaleRetractions A) :
    EveryMaximalLocalizationStrictlyHenselian A := by
  sorry

/-- The localization `A_Z^~` from the preceding w-local construction retains
the retraction property. -/
theorem localizedPiece_has_faithfullyFlatEtaleRetractions
    {A : Type u} [CommRing A]
    (hA : HasFaithfullyFlatEtaleRetractions A)
    (Z : LocallyClosedPiece A) :
    HasFaithfullyFlatEtaleRetractions (localizedPieceRing Z) := by
  sorry

/-! ## The w-local algebraic residue-field-extension construction -/

/-- The full commutative diagram and all nine properties in the final lemma
of the source section. -/
structure WLocalAlgebraicResidueExtension
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) where
  C : Type u
  [commRingC : CommRing C]
  aToC : A →+* C
  D : Type u
  [commRingD : CommRing D]
  bToD : B →+* D
  cToD : C →+* D
  commutes : cToD.comp aToC = bToD.comp f
  aToC_faithfullyFlat : RingHom.FaithfullyFlat aToC
  aToC_indEtale : IsIndEtale aToC
  bToD_faithfullyFlat : RingHom.FaithfullyFlat bToD
  bToD_indEtale : IsIndEtale bToD
  C_wLocal : IsWLocalAffine (A := C)
  D_wLocal : IsWLocalAffine (A := D)
  cToD_wLocal : IsWLocalRingMap cToD
  closedPoints_D :
    closedPoints (PrimeSpectrum D) =
      PrimeSpectrum.comap cToD ⁻¹' closedPoints (PrimeSpectrum C)
  closedPoints_C_surjective :
    PrimeSpectrum.comap aToC '' closedPoints (PrimeSpectrum C) = Set.univ
  closedPoints_D_surjective :
    PrimeSpectrum.comap bToD '' closedPoints (PrimeSpectrum D) = Set.univ
  C_strictlyHenselian : EveryMaximalLocalizationStrictlyHenselian C

theorem exists_wLocalAlgebraicResidueExtension
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hres : HasAlgebraicResidueExtensions f) :
    Nonempty (WLocalAlgebraicResidueExtension f) := by
  sorry

end

end Formalization.Books.Proetale.Unit08
