import Formalization.Books.Cohomology.Unit03.DerivedFunctors
import Formalization.Books.Modules.Unit17.FlatModules
import Formalization.Books.Derived.Unit10.DistinguishedTriangles
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.Derived.Unit29.UnboundedComplexes
import Formalization.Books.MoreAlgebra.Unit58.TensorProductsOfComplexes
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Cohomology of Sheaves, Chapter 19: flat resolutions

This file formalizes the precise statements in the source section
`Flat resolutions`.  The commutative sheaf-of-rings model is the canonical
tensor-compatible model used by the earlier module chapters.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit09
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit29
open Formalization.Books.Homology.Unit15
open Formalization.Books.Modules.Unit16
open Formalization.Books.Modules.Unit17
open Formalization.Books.Sheaves.Unit24
open Formalization.Books.Sheaves.Unit20
open Formalization.Books.Sheaves.Unit22
open TopologicalSpace
open HomologicalComplex
open ComplexShape

universe u v

namespace Formalization.Books.Cohomology.Unit19

/-! ## Complexes and total tensor products -/

abbrev SheafModule (X : TopCat.{v}) (O : CommRingSheaf X) :=
  CommRingSheafModule O

abbrev SheafComplex {X : TopCat.{v}} {O : CommRingSheaf X} :=
  CochainComplex (SheafModule X O) ℤ

abbrev SheafK {X : TopCat.{v}} {O : CommRingSheaf X} :=
  HomotopyCategory (SheafModule X O) (.up ℤ)

noncomputable instance commRingSheafModule_hasDerivedCategory
    {X : TopCat.{v}} (O : CommRingSheaf X) :
    HasDerivedCategory (SheafModule X O) :=
  HasDerivedCategory.standard _

abbrev SheafD {X : TopCat.{v}} {O : CommRingSheaf X} :=
  DerivedCategory (SheafModule X O)

noncomputable abbrev sheafDerivedQuotient
    {X : TopCat.{v}} (O : CommRingSheaf X) :
    SheafComplex (O := O) ⥤ SheafD (O := O) :=
  DerivedCategory.Q

noncomputable def sheafTensorBifunctor
    {X : TopCat.{v}} (O : CommRingSheaf X) :
    SheafModule X O ⥤ SheafModule X O ⥤ SheafModule X O where
  obj F := tensorLeftFunctor O F
  map f :=
    { app := fun G => tensorProductMap f (𝟙 G)
      naturality := by
        sorry
    }
  map_id F := by
    sorry
  map_comp f g := by
    sorry

noncomputable instance sheafTensorBifunctor_preservesZeroMorphisms
    {X : TopCat.{v}} (O : CommRingSheaf X) :
    (sheafTensorBifunctor O).PreservesZeroMorphisms := by
  sorry

noncomputable instance sheafTensorBifunctor_additive
    {X : TopCat.{v}} (O : CommRingSheaf X) :
    (sheafTensorBifunctor O).Additive := by
  sorry

noncomputable instance sheafTensorBifunctor_obj_additive
    {X : TopCat.{v}} (O : CommRingSheaf X) (F : SheafModule X O) :
    ((sheafTensorBifunctor O).obj F).Additive := by
  sorry

noncomputable instance sheafTensor_hasMapBifunctor
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (K L : SheafComplex (O := O)) :
    HomologicalComplex.HasMapBifunctor K L (sheafTensorBifunctor O) (.up ℤ) := by
  sorry

noncomputable abbrev sheafTensorComplex
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (K L : SheafComplex (O := O)) : SheafComplex (O := O) :=
  HomologicalComplex.mapBifunctor K L (sheafTensorBifunctor O) (.up ℤ)

noncomputable abbrev tensorLeftSheafComplexFunctor
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (K : SheafComplex (O := O)) : SheafComplex (O := O) ⥤ SheafComplex (O := O) :=
  ((sheafTensorBifunctor O).map₂CochainComplex).obj K

noncomputable abbrev tensorRightSheafComplexFunctor
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (K : SheafComplex (O := O)) : SheafComplex (O := O) ⥤ SheafComplex (O := O) :=
  ((sheafTensorBifunctor O).map₂CochainComplex).flip.obj K

/-! ## K-flat complexes -/

abbrev IsAcyclic {X : TopCat.{v}} {O : CommRingSheaf X}
    (K : SheafComplex (O := O)) : Prop :=
  AcyclicComplex K

def IsKFlat {X : TopCat.{v}} {O : CommRingSheaf X}
    (K : SheafComplex (O := O)) : Prop :=
  ∀ F : SheafComplex (O := O), IsAcyclic F →
    IsAcyclic (sheafTensorComplex F K)

def TermwiseFlat {X : TopCat.{v}} {O : CommRingSheaf X}
    (K : SheafComplex (O := O)) : Prop :=
  ∀ n : ℤ, Formalization.Books.Modules.Unit17.IsFlat O (K.X n)

def TermwiseSurjective {X : TopCat.{v}} {O : CommRingSheaf X}
    {K L : SheafComplex (O := O)} (f : K ⟶ L) : Prop :=
  ∀ n : ℤ, Epi (f.f n)

structure BoundedAboveFlatResolution
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (G : SheafComplex (O := O)) where
  complex : SheafComplex (O := O)
  map : complex ⟶ G
  boundedAbove : IsBoundedAbove complex
  flat : TermwiseFlat complex
  quasiIso : QuasiIso map

theorem exists_boundedAbove_flat_resolution
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (G : SheafComplex (O := O)) (hG : IsBoundedAbove G) :
    Nonempty (BoundedAboveFlatResolution G) := by
  sorry

theorem exists_flat_epi
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : SheafModule X O) :
    ∃ P : SheafModule X O, ∃ q : P ⟶ F,
      Epi q ∧ Formalization.Books.Modules.Unit17.IsFlat O P :=
  Formalization.Books.Modules.Unit17.exists_epi_from_isFlat O F

theorem tensor_right_preserves_homotopy
    {X : TopCat.{v}} {O : CommRingSheaf X}
  (K : SheafComplex (O := O)) {L M : SheafComplex (O := O)}
    (f g : L ⟶ M) (h : Homotopy f g) :
    Nonempty (Homotopy
      ((tensorRightSheafComplexFunctor O K).map f)
      ((tensorRightSheafComplexFunctor O K).map g)) := by
  sorry

theorem tensor_left_preserves_homotopy
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (K : SheafComplex (O := O)) {L M : SheafComplex (O := O)}
    (f g : L ⟶ M) (h : Homotopy f g) :
    Nonempty (Homotopy
      ((tensorLeftSheafComplexFunctor O K).map f)
      ((tensorLeftSheafComplexFunctor O K).map g)) := by
  sorry

theorem kFlat_tensor_preserves_quasiIso
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (K : SheafComplex (O := O)) (hK : IsKFlat K)
    {L M : SheafComplex (O := O)} (f : L ⟶ M) (hf : QuasiIso f) :
    QuasiIso ((tensorRightSheafComplexFunctor O K).map f) := by
  sorry

noncomputable abbrev tensorRightSheafHomotopyFunctor
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (K : SheafComplex (O := O)) : SheafK (O := O) ⥤ SheafK (O := O) :=
  CategoryTheory.Quotient.lift
    (homotopic (SheafModule X O) (.up ℤ))
    (tensorRightSheafComplexFunctor O K ⋙
      HomotopyCategory.quotient (SheafModule X O) (.up ℤ))
    (by
      intro A B f g h
      obtain ⟨h⟩ := h
      exact HomotopyCategory.eq_of_homotopy _ _
        (Classical.choice (tensor_right_preserves_homotopy K f g h)))

noncomputable abbrev tensorLeftSheafHomotopyFunctor
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (K : SheafComplex (O := O)) : SheafK (O := O) ⥤ SheafK (O := O) :=
  CategoryTheory.Quotient.lift
    (homotopic (SheafModule X O) (.up ℤ))
    (tensorLeftSheafComplexFunctor O K ⋙
      HomotopyCategory.quotient (SheafModule X O) (.up ℤ))
    (by
      intro A B f g h
      obtain ⟨h⟩ := h
      exact HomotopyCategory.eq_of_homotopy _ _
        (Classical.choice (tensor_left_preserves_homotopy K f g h)))

theorem tensor_complex_functors_exact
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (K : SheafComplex (O := O)) :
    Nonempty (Formalization.Books.Derived.Unit10.ExactTriangulatedFunctorData
      (tensorRightSheafHomotopyFunctor O K)) ∧
      Nonempty (Formalization.Books.Derived.Unit10.ExactTriangulatedFunctorData
      (tensorLeftSheafHomotopyFunctor O K)) := by
  sorry

abbrev StalkRing {X : TopCat.{v}} (O : CommRingSheaf X) (x : X) :=
  TopCat.Presheaf.stalk (C := CommRingCat) O.obj x

abbrev StalkModule {X : TopCat.{v}} (O : CommRingSheaf X) (x : X) :=
  ModuleCat (StalkRing O x)

abbrev StalkComplex {X : TopCat.{v}} (O : CommRingSheaf X) (x : X) :=
  CochainComplex (StalkModule O x) ℤ

noncomputable def stalkModuleFunctor
    {X : TopCat.{v}} (O : CommRingSheaf X) (x : X) :
    SheafModule X O ⥤ StalkModule O x where
  obj F := Formalization.Books.Modules.Unit17.moduleStalk F x
  map f := by
    sorry
  map_id F := by
    sorry
  map_comp f g := by
    sorry

noncomputable instance stalkModuleFunctor_additive
    {X : TopCat.{v}} (O : CommRingSheaf X) (x : X) :
    (stalkModuleFunctor O x).Additive := by
  sorry

noncomputable abbrev stalkComplex
    {X : TopCat.{v}} (O : CommRingSheaf X) (x : X)
    (K : SheafComplex (O := O)) : StalkComplex O x :=
  ((stalkModuleFunctor O x).mapHomologicalComplex (.up ℤ)).obj K

def IsStalkKFlat
    {X : TopCat.{v}} (O : CommRingSheaf X) (x : X)
    (K : SheafComplex (O := O)) : Prop :=
  ∀ F : StalkComplex O x,
    AcyclicComplex F →
      AcyclicComplex
        (Formalization.Books.MoreAlgebra.Unit58.tensorProductComplex
          (StalkRing O x) F (stalkComplex O x K))

def StalkwiseKFlat
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (K : SheafComplex (O := O)) : Prop :=
  ∀ x : X, IsStalkKFlat O x K

theorem isKFlat_iff_stalkwise
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (K : SheafComplex (O := O)) :
    IsKFlat K ↔ StalkwiseKFlat O K := by
  sorry

theorem tensor_product_isKFlat
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (K L : SheafComplex (O := O)) (hK : IsKFlat K) (hL : IsKFlat L) :
    IsKFlat (sheafTensorComplex K L) := by
  sorry

def IsKFlatObject {X : TopCat.{v}} {O : CommRingSheaf X}
    (K : SheafK (O := O)) : Prop :=
  ∃ P : SheafComplex (O := O),
    Nonempty ((HomotopyCategory.quotient (SheafModule X O) (.up ℤ)).obj P ≅ K) ∧
      IsKFlat P

theorem kFlat_two_out_of_three_triangle₁₂
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (T : Triangle (SheafK (O := O))) (hT : T ∈ distTriang (SheafK (O := O)))
    (h : IsKFlatObject T.obj₁ ∧ IsKFlatObject T.obj₂) :
    IsKFlatObject T.obj₃ := by
  sorry

theorem kFlat_two_out_of_three_triangle₂₃
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (T : Triangle (SheafK (O := O))) (hT : T ∈ distTriang (SheafK (O := O)))
    (h : IsKFlatObject T.obj₂ ∧ IsKFlatObject T.obj₃) :
    IsKFlatObject T.obj₁ := by
  sorry

theorem kFlat_two_out_of_three_triangle₁₃
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (T : Triangle (SheafK (O := O))) (hT : T ∈ distTriang (SheafK (O := O)))
    (h : IsKFlatObject T.obj₁ ∧ IsKFlatObject T.obj₃) :
    IsKFlatObject T.obj₂ := by
  sorry

theorem kFlat_two_out_of_three_shortExact
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {S : ShortComplex (SheafComplex (O := O))}
    (hS : S.ShortExact) (hflat : TermwiseFlat S.X₃)
    (h : IsKFlat S.X₁ ∧ IsKFlat S.X₂) : IsKFlat S.X₃ := by
  sorry

theorem kFlat_two_out_of_three_shortExact_left
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {S : ShortComplex (SheafComplex (O := O))}
    (hS : S.ShortExact) (hflat : TermwiseFlat S.X₃)
    (h : IsKFlat S.X₂ ∧ IsKFlat S.X₃) : IsKFlat S.X₁ := by
  sorry

theorem kFlat_two_out_of_three_shortExact_middle
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {S : ShortComplex (SheafComplex (O := O))}
    (hS : S.ShortExact) (hflat : TermwiseFlat S.X₃)
    (h : IsKFlat S.X₁ ∧ IsKFlat S.X₃) : IsKFlat S.X₂ := by
  sorry

noncomputable instance pullbackModule_preservesZeroMorphisms
    {X Y : TopCat.{v}} {OX : CommRingSheaf X} {OY : CommRingSheaf Y}
    (f : X ⟶ Y)
    (α : commRingSheafToRingSheaf OY ⟶
      (sheafRingPushforward f).obj (commRingSheafToRingSheaf OX))
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)] :
    (pullbackModule f α).PreservesZeroMorphisms := by
  sorry

theorem pullback_isKFlat
    {X Y : TopCat.{v}} {OX : CommRingSheaf X} {OY : CommRingSheaf Y}
    (f : X ⟶ Y)
    (α : commRingSheafToRingSheaf OY ⟶
      (sheafRingPushforward f).obj (commRingSheafToRingSheaf OX))
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)]
    (K : SheafComplex (O := OY)) (hK : IsKFlat K) :
    IsKFlat (((pullbackModule f α).mapHomologicalComplex (.up ℤ)).obj K) := by
  sorry

theorem boundedAbove_termwiseFlat_isKFlat
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (K : SheafComplex (O := O)) (hK : IsBoundedAbove K)
    (hflat : TermwiseFlat K) : IsKFlat K := by
  sorry

theorem filteredColimit_isKFlat
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {J : Type v} [Category.{v} J] [IsFilteredOrEmpty J]
    (F : J ⥤ SheafComplex (O := O)) [HasColimit F]
    (hF : ∀ j, IsKFlat (F.obj j)) : IsKFlat (colimit F) := by
  sorry

/-! ## Resolution by direct sums of extension-by-zero modules -/

def IsDirectSumOfOpenExtensions
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (M : SheafModule X O) : Prop :=
  ∃ I : Type v, ∃ U : I → Opens X,
    Nonempty (M ≅ directSum (fun i => openExtensionUnit O (U i)))

structure OpenExtensionResolution
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (G : SheafComplex (X := X) (O := O)) where
  stage : ℕ → SheafComplex (O := O)
  augmentation : ∀ n,
    stage n ⟶
      Formalization.Books.Homology.Unit15.CochainComplex.canonicalTruncLE G
        ((n : ℤ) + 1)
  stage_quasiIso : ∀ n, QuasiIso (augmentation n)
  stage_surjective : ∀ n, TermwiseSurjective (augmentation n)
  boundedAbove : ∀ n, IsBoundedAbove (stage n)
  stage_terms_are_open_extensions : ∀ (n : ℕ) (i : ℤ),
    IsDirectSumOfOpenExtensions O ((stage n).X i)
  transition : ∀ n : ℕ, stage n ⟶ stage (n + 1)
  transition_comm : ∀ n : ℕ,
    transition n ≫ augmentation (n + 1) =
      augmentation n ≫ canonicalTruncLETransition G n
  transition_split : ∀ n : ℕ, termwiseSplitInjection (transition n)
  transition_cokernel_is_open_extension_sum : ∀ (n : ℕ) (i : ℤ),
    IsDirectSumOfOpenExtensions O (cokernel ((transition n).f i))
  hasColimit : HasColimit (Functor.ofSequence transition)
  colimit_map : colimit (Functor.ofSequence transition) ⟶ G
  colimit_compatibility : ∀ n : ℕ,
    (colimit.ι (Functor.ofSequence transition) n) ≫ colimit_map =
      augmentation n ≫
        Formalization.Books.Homology.Unit15.CochainComplex.canonicalTruncLEι G
          ((n : ℤ) + 1)
  colimit_quasiIso : QuasiIso colimit_map

theorem exists_openExtensionResolution
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (G : SheafComplex (X := X) (O := O)) :
    Nonempty (OpenExtensionResolution G) := by
  sorry

structure KFlatResolution
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (G : SheafComplex (O := O)) where
  complex : SheafComplex (O := O)
  map : complex ⟶ G
  kFlat : IsKFlat complex
  flat : TermwiseFlat complex
  quasiIso : QuasiIso map
  surjective : TermwiseSurjective map

theorem exists_kFlatResolution
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (G : SheafComplex (O := O)) : Nonempty (KFlatResolution G) := by
  sorry

theorem tensor_other_side_quasiIso
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {P Q : SheafComplex (O := O)} (α : P ⟶ Q) (hα : QuasiIso α)
    (hP : IsKFlat P) (hQ : IsKFlat Q) (L : SheafComplex (O := O)) :
    QuasiIso ((tensorLeftSheafComplexFunctor O L).map α) := by
  sorry

/-! ## Derived tensor product -/

def tensorSlice {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : (SheafD (O := O) × SheafD (O := O)) ⥤ SheafD (O := O))
    (M : SheafD (O := O)) : SheafD (O := O) ⥤ SheafD (O := O) where
  obj A := F.obj (A, M)
  map f := F.map (f, 𝟙 M)
  map_id A := by rw [← F.map_id]; rfl
  map_comp f g := by
    rw [← F.map_comp]
    congr 1

structure DerivedTensorProductData
    {X : TopCat.{v}} (O : CommRingSheaf X) where
  functor : (SheafD (O := O) × SheafD (O := O)) ⥤ SheafD (O := O)
  exact_in_first : ∀ M : SheafD (O := O),
    Nonempty (Formalization.Books.Derived.Unit10.ExactTriangulatedFunctorData
      (tensorSlice functor M))
  represented : ∀ A B : SheafD (O := O), ∃ K L : SheafComplex (O := O),
    Nonempty ((sheafDerivedQuotient O).obj K ≅ A) ∧
    Nonempty ((sheafDerivedQuotient O).obj L ≅ B) ∧
    IsKFlat K ∧ IsKFlat L ∧
    Nonempty (functor.obj (A, B) ≅ (sheafDerivedQuotient O).obj
      (sheafTensorComplex K L))
  computed_on_kFlat : ∀ K L : SheafComplex (O := O), IsKFlat K → IsKFlat L →
    Nonempty (functor.obj ((sheafDerivedQuotient O).obj K,
      (sheafDerivedQuotient O).obj L) ≅
      (sheafDerivedQuotient O).obj (sheafTensorComplex K L))

theorem exists_derivedTensorProductData
    {X : TopCat.{v}} (O : CommRingSheaf X) :
    Nonempty (DerivedTensorProductData O) := by
  sorry

noncomputable def derivedTensorProductData
    {X : TopCat.{v}} (O : CommRingSheaf X) : DerivedTensorProductData O :=
  Classical.choice (exists_derivedTensorProductData O)

noncomputable abbrev derivedTensorProductFunctor
    {X : TopCat.{v}} (O : CommRingSheaf X) :
    (SheafD (O := O) × SheafD (O := O)) ⥤ SheafD (O := O) :=
  (derivedTensorProductData O).functor

noncomputable abbrev derivedTensor
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (A B : SheafD (O := O)) : SheafD (O := O) :=
  (derivedTensorProductFunctor O).obj (A, B)

noncomputable abbrev derivedTensorFunctor
    {X : TopCat.{v}} (O : CommRingSheaf X) (M : SheafD (O := O)) :
    SheafD (O := O) ⥤ SheafD (O := O) :=
  tensorSlice (derivedTensorProductFunctor O) M

theorem derivedTensor_exact
    {X : TopCat.{v}} (O : CommRingSheaf X) (M : SheafD (O := O)) :
    Nonempty (Formalization.Books.Derived.Unit10.ExactTriangulatedFunctorData
      (derivedTensorFunctor O M)) :=
  (derivedTensorProductData O).exact_in_first M

theorem derivedTensor_of_kFlat
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (K L : SheafComplex (O := O)) (hK : IsKFlat K) (hL : IsKFlat L) :
    Nonempty (derivedTensor O ((sheafDerivedQuotient O).obj K)
      ((sheafDerivedQuotient O).obj L) ≅
      (sheafDerivedQuotient O).obj (sheafTensorComplex K L)) := by
  exact (derivedTensorProductData O).computed_on_kFlat K L hK hL

noncomputable def derivedTensorSymmetry
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (A B : SheafD (O := O)) : derivedTensor O A B ≅ derivedTensor O B A := by
  sorry

noncomputable def derivedTensorAssociativity
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (A B C : SheafD (O := O)) :
    derivedTensor O (derivedTensor O A B) C ≅
      derivedTensor O A (derivedTensor O B C) := by
  sorry

/-! ## Tor and the long exact sequence -/

structure ExactPair {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) : Prop where
  zero : f ≫ g = 0
  exact : (ShortComplex.mk f g zero).Exact

noncomputable abbrev derivedModuleObject
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : SheafModule X O) : SheafD (O := O) :=
  (DerivedCategory.singleFunctor (SheafModule X O) 0).obj F

noncomputable abbrev sheafTor
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (F G : SheafModule X O) (p : ℕ) : SheafModule X O :=
  (DerivedCategory.homologyFunctor (SheafModule X O) (-(p : ℤ))).obj
    (derivedTensor O (derivedModuleObject F) (derivedModuleObject G))

structure TorLongExactSequenceData
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₁ F₂ F₃ : SheafModule X O} (G : SheafModule X O)
    (S : ShortComplex (SheafModule X O)) where
  identifies : S.X₁ = F₁ ∧ S.X₂ = F₂ ∧ S.X₃ = F₃
  tensor_right_exact : RightExactSequence
    (tensorProductMap S.f (𝟙 G)) (tensorProductMap S.g (𝟙 G))
  tor_one_map₁ : sheafTor O S.X₁ G 1 ⟶ sheafTor O S.X₂ G 1
  tor_one_map₂ : sheafTor O S.X₂ G 1 ⟶ sheafTor O S.X₃ G 1
  connecting : sheafTor O S.X₃ G 1 ⟶ tensorProductSheaf O S.X₁ G
  tor_one_exact_at_F₂ : ExactPair tor_one_map₁ tor_one_map₂
  tor_one_exact_at_F₃ : ExactPair tor_one_map₂ connecting
  tensor_exact_at_F₁ : ExactPair connecting (tensorProductMap S.f (𝟙 G))

theorem tor_long_exact_sequence
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₁ F₂ F₃ G : SheafModule X O} (S : ShortComplex (SheafModule X O))
    (hS : S.ShortExact)
    (hident : S.X₁ = F₁ ∧ S.X₂ = F₂ ∧ S.X₃ = F₃) :
    Nonempty (TorLongExactSequenceData (F₁ := F₁) (F₂ := F₂) (F₃ := F₃) G S) := by
  sorry

theorem flat_iff_tor_one_vanishes
    {X : TopCat.{v}} (O : CommRingSheaf X) (F : SheafModule X O) :
    Formalization.Books.Modules.Unit17.IsFlat O F ↔
      ∀ G : SheafModule X O, IsZero (sheafTor O F G 1) := by
  sorry

/-! ## Factorization through K-flat complexes -/

theorem factor_through_kFlat
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {K L : SheafComplex (O := O)} (a : K ⟶ L) (hK : IsKFlat K) :
    ∃ (N : SheafComplex (O := O)) (b : K ⟶ N) (c : N ⟶ L),
      IsKFlat N ∧ QuasiIso c ∧ Nonempty (Homotopy a (b ≫ c)) ∧
      (TermwiseFlat K →
        ∃ (N' : SheafComplex (O := O)) (b' : K ⟶ N') (c' : N' ⟶ L),
          IsKFlat N' ∧ TermwiseFlat N' ∧ QuasiIso c' ∧
            Nonempty (Homotopy a (b' ≫ c'))) := by
  sorry

end Formalization.Books.Cohomology.Unit19
