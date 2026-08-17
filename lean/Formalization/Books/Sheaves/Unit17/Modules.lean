import Formalization.Books.Sheaves.Unit04.AbelianPresheaves
import Formalization.Books.Sheaves.Unit06.PresheavesOfModules
import Formalization.Books.Sheaves.Unit14.StalksOfPresheavesOfModules
import Formalization.Books.Sheaves.Unit15.AlgebraicStructures
import Formalization.Books.Sheaves.Unit16.ExactnessAndPoints
import Formalization.Books.Sheaves.Unit17.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Sheaves on Spaces, Chapter 17, Section 4: Sheafification of presheaves of
modules

The source span is `books/sheaves.tex:1822-1983`.  The ring and module
sheafifications below use Mathlib's canonical `SheafOfModules` construction.
The earlier presheaf change-of-rings and stalk APIs are reused for the
source-facing tensor, restriction, adjunction, and stalk statements.
-/

namespace Formalization.Books.Sheaves.Unit17

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit05
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit14
open Formalization.Books.Sheaves.Unit16
open Formalization.Books.Sheaves.Unit15
open Formalization.Books.Sheaves.Unit03

universe v

noncomputable section

/-! ## Ring and module sheafification -/

/-- The canonical sheafification of a presheaf of rings. -/
noncomputable def ringSheafification {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) :
    Sheaf (Opens.grothendieckTopology X) RingCat.{v} :=
  (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X)
    RingCat).obj O

/-- The canonical map from a presheaf of rings to its sheafification. -/
noncomputable def ringSheafificationUnit {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) :
    O ⟶ (ringSheafification O).obj :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology X) O

/-- The ring sheafification unit is locally injective. -/
theorem ringSheafificationUnit_isLocallyInjective {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) :
      Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := by
  change Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) O)
  infer_instance

/-- The ring sheafification unit is locally surjective. -/
theorem ringSheafificationUnit_isLocallySurjective {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) :
      Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := by
  change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) O)
  infer_instance

/-- The sheaf of modules obtained by sheafifying an `O`-module presheaf. -/
noncomputable def moduleSheafification {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    SheafOfModules.{v} (ringSheafification O) := by
  letI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallyInjective O
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallySurjective O
  exact (PresheafOfModules.sheafification (ringSheafificationUnit O)).obj F

/-- The unit of module sheafification, with its natural restricted-scalar
target made explicit. -/
noncomputable def moduleSheafificationUnit {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    F ⟶ (PresheafOfModules.restrictScalars (ringSheafificationUnit O)).obj
      ((SheafOfModules.forget (ringSheafification O)).obj
        (moduleSheafification F)) := by
  letI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallyInjective O
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallySurjective O
  exact (PresheafOfModules.sheafificationAdjunction
    (ringSheafificationUnit O)).unit.app F

/-- The underlying set presheaf of an `O`-module presheaf. -/
abbrev moduleUnderlyingSetPresheaf {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) : TopCat.Presheaf (Type v) X :=
  Formalization.Books.Sheaves.Unit05.underlyingPresheaf
    (CategoryTheory.forget AddCommGrpCat) F.presheaf

/-- The underlying set presheaf of the sheafified module. -/
abbrev moduleSheafificationSetPresheaf {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) : TopCat.Presheaf (Type v) X :=
  Formalization.Books.Sheaves.Unit05.underlyingPresheaf
    (CategoryTheory.forget AddCommGrpCat)
    ((SheafOfModules.toSheaf (ringSheafification O)).obj
      (moduleSheafification F)).obj

/-- The underlying set presheaf of the module sheafification is isomorphic to
the ordinary set-valued sheafification. -/
theorem moduleSheafification_underlying_iso {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    Nonempty
      (moduleSheafificationSetPresheaf F ≅
        (sheafification (moduleUnderlyingSetPresheaf F)).presheaf) := by
  let : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallyInjective O
  let : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallySurjective O
  let eM := (PresheafOfModules.sheafificationCompForgetCompToPresheaf
    (ringSheafificationUnit O)).app F
  let eMSet :=
    ((Functor.whiskeringRight (Opens X)ᵒᵖ AddCommGrpCat (Type v)).obj
      (CategoryTheory.forget AddCommGrpCat)).mapIso eM
  let eM' : moduleSheafificationSetPresheaf F ≅
      Formalization.Books.Sheaves.Unit05.underlyingPresheaf
        (CategoryTheory.forget AddCommGrpCat)
        ((CategoryTheory.sheafToPresheaf
          (Opens.grothendieckTopology X) AddCommGrpCat).obj
          ((CategoryTheory.presheafToSheaf
            (Opens.grothendieckTopology X) AddCommGrpCat).obj F.presheaf)) := by
    change
      @Iso ((Opens X)ᵒᵖ ⥤ Type v) Functor.category
        (moduleSheafificationSetPresheaf F)
        (Formalization.Books.Sheaves.Unit05.underlyingPresheaf
          (CategoryTheory.forget AddCommGrpCat)
          ((CategoryTheory.sheafToPresheaf
            (Opens.grothendieckTopology X) AddCommGrpCat).obj
            ((CategoryTheory.presheafToSheaf
              (Opens.grothendieckTopology X) AddCommGrpCat).obj F.presheaf)))
    change
      @Iso ((Opens X)ᵒᵖ ⥤ Type v) Functor.category
        (((PresheafOfModules.toPresheaf (ringSheafification O).obj).obj
          ((PresheafOfModules.sheafification
            (ringSheafificationUnit O)).obj F).val) ⋙
            CategoryTheory.forget AddCommGrpCat)
        (((CategoryTheory.presheafToSheaf
            (Opens.grothendieckTopology X) AddCommGrpCat).obj
          ((PresheafOfModules.toPresheaf O).obj F)).obj ⋙
            CategoryTheory.forget AddCommGrpCat)
    exact eMSet
  let J := Opens.grothendieckTopology X
  let P := moduleUnderlyingSetPresheaf F
  let G : TopCat.Sheaf (Type v) X :=
    ⟨moduleSheafificationSetPresheaf F,
      (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
        (CategoryTheory.forget AddCommGrpCat)
        ((SheafOfModules.toSheaf (ringSheafification O)).obj
          (moduleSheafification F)).obj).mp
        ((SheafOfModules.toSheaf (ringSheafification O)).obj
          (moduleSheafification F)).property⟩
  let H : TopCat.Sheaf (Type v) X :=
    (CategoryTheory.presheafToSheaf J (Type v)).obj P
  let p := CategoryTheory.sheafifyLift J (sheafificationUnit P)
    (sheafification_isSheaf P)
  let q := sheafificationLift P H (CategoryTheory.toSheafify J P)
  have hp : CategoryTheory.toSheafify J P ≫ p = sheafificationUnit P := by
    exact CategoryTheory.toSheafify_sheafifyLift _ _ _
  have hq : sheafificationUnit P ≫ q = CategoryTheory.toSheafify J P := by
    exact sheafificationUnit_comp_lift P H (CategoryTheory.toSheafify J P)
  have hqp : q ≫ p = 𝟙 _ := by
    have h₁ : q ≫ p =
        sheafificationLift P (sheafification P) (sheafificationUnit P) := by
      apply sheafificationLift_unique P (sheafification P) (sheafificationUnit P)
      rw [← Category.assoc, hq, hp]
    have h₂ : (𝟙 _) =
        sheafificationLift P (sheafification P) (sheafificationUnit P) :=
      sheafificationLift_unique P (sheafification P) (sheafificationUnit P) (𝟙 _)
        (by simp)
    exact h₁.trans h₂.symm
  have hpq : p ≫ q = 𝟙 _ := by
    apply CategoryTheory.sheafify_hom_ext J (p ≫ q) (𝟙 _) H.property
    rw [← Category.assoc, hp, hq]
    simp
  let eLocal : H.presheaf ≅ (sheafification P).presheaf :=
    { hom := p, inv := q, hom_inv_id := hpq, inv_hom_id := hqp }
  let S : TopCat.Sheaf (Type v) X :=
    ⟨Formalization.Books.Sheaves.Unit05.underlyingPresheaf
        (CategoryTheory.forget AddCommGrpCat)
        ((CategoryTheory.presheafToSheaf J AddCommGrpCat).obj F.presheaf).obj,
      (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
        (CategoryTheory.forget AddCommGrpCat)
        ((CategoryTheory.presheafToSheaf J AddCommGrpCat).obj F.presheaf).obj).mp
        ((CategoryTheory.presheafToSheaf J AddCommGrpCat).obj F.presheaf).property⟩
  let e := CategoryTheory.presheafToSheafCompComposeAndSheafifyIso J
    (CategoryTheory.forget AddCommGrpCat)
  let eF := e.app F.presheaf
  let eK0 := (CategoryTheory.sheafToPresheaf J (Type v)).mapIso eF
  let iS := CategoryTheory.isoSheafify J S.property
  let iS' : S.presheaf ≅
      (CategoryTheory.sheafToPresheaf J (Type v)).obj
        ((CategoryTheory.presheafToSheaf J (Type v)).obj S.presheaf) := by
    exact iS
  let eGH : moduleSheafificationSetPresheaf F ≅ H.presheaf := by
    simpa [P, G, H, S, moduleSheafificationSetPresheaf,
      moduleUnderlyingSetPresheaf,
      Formalization.Books.Sheaves.Unit05.underlyingPresheaf,
      CategoryTheory.Sheaf.composeAndSheafify] using
      (eM'.trans (iS'.trans eK0))
  let eFinal : moduleSheafificationSetPresheaf F ≅
      (sheafification P).presheaf := eGH ≪≫ eLocal
  exact ⟨eFinal⟩

/-- The universal property of the module sheafification, in the canonical
restricted-scalar form used by Mathlib. -/
noncomputable def moduleSheafificationHomEquiv {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O)
    (G : SheafOfModules.{v} (ringSheafification O)) :
    (moduleSheafification F ⟶ G) ≃
      (F ⟶ (PresheafOfModules.restrictScalars (ringSheafificationUnit O)).obj
        ((SheafOfModules.forget (ringSheafification O)).obj G)) := by
  letI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallyInjective O
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallySurjective O
  exact PresheafOfModules.sheafificationHomEquiv (ringSheafificationUnit O)

/-! The source packages the preceding object construction as an adjoint
functor. -/

/-- The sheafification functor on presheaves of `O`-modules. -/
noncomputable def moduleSheafificationFunctor {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) :
    PMod O ⥤ SheafOfModules.{v} (ringSheafification O) := by
  letI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallyInjective O
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallySurjective O
  exact PresheafOfModules.sheafification (ringSheafificationUnit O)

/-- The object part of the module sheafification functor is the source's
`F#`. -/
theorem moduleSheafificationFunctor_obj {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) (F : PMod O) :
    (moduleSheafificationFunctor O).obj F = moduleSheafification F := by
  rfl

/-- The functor from sheaves of `O#`-modules to presheaves of `O`-modules. -/
noncomputable def sheafModuleRestriction {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) :
    SheafOfModules.{v} (ringSheafification O) ⥤ PMod O :=
  (SheafOfModules.forget (ringSheafification O)) ⋙
    PresheafOfModules.restrictScalars (ringSheafificationUnit O)

/-- The module sheafification and restriction functors form the source's
adjunction. -/
noncomputable def moduleSheafificationAdjunction {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) :
    moduleSheafificationFunctor O ⊣ sheafModuleRestriction O := by
  letI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallyInjective O
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (ringSheafificationUnit O) := ringSheafificationUnit_isLocallySurjective O
  exact PresheafOfModules.sheafificationAdjunction (ringSheafificationUnit O)

/-- The adjunction in the source's direction, from presheaf-module maps to
sheaf-module maps. -/
noncomputable def moduleSheafificationAdjunctionHomEquiv {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) (F : PMod O)
    (G : SheafOfModules.{v} (ringSheafification O)) :
    (F ⟶ (sheafModuleRestriction O).obj G) ≃
      (moduleSheafification F ⟶ G) :=
  (moduleSheafificationHomEquiv F G).symm

/-- A chosen factorization of a presheaf-module map through the module
sheafification. -/
noncomputable def moduleSheafificationLift {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} {F : PMod O}
    (G : SheafOfModules.{v} (ringSheafification O))
    (φ : F ⟶ (sheafModuleRestriction O).obj G) :
    moduleSheafification F ⟶ G :=
  (moduleSheafificationHomEquiv F G).symm φ

/-- The chosen module-sheafification lift has the required universal image. -/
theorem moduleSheafificationLift_spec {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} {F : PMod O}
    (G : SheafOfModules.{v} (ringSheafification O))
    (φ : F ⟶ (sheafModuleRestriction O).obj G) :
    moduleSheafificationHomEquiv F G (moduleSheafificationLift G φ) = φ := by
  exact (moduleSheafificationHomEquiv F G).apply_symm_apply φ

/-! The explicit factorization form is retained in addition to the Hom
equivalence because it is the formulation used in the source. -/

/-- Every presheaf-module map into a sheaf of `O#`-modules factors uniquely
through the module sheafification by an `O#`-linear map. -/
theorem existsUnique_moduleSheafificationFactorization {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} {F : PMod O}
    (G : SheafOfModules.{v} (ringSheafification O))
    (φ : F ⟶ (sheafModuleRestriction O).obj G) :
    ∃! ψ : moduleSheafification F ⟶ G,
  moduleSheafificationUnit F ≫
          (PresheafOfModules.restrictScalars (ringSheafificationUnit O)).map ψ.val =
        φ := by
  let e := moduleSheafificationHomEquiv F G
  refine ⟨e.symm φ, ?_, ?_⟩
  · exact e.apply_symm_apply φ
  · intro ψ hψ
    apply e.injective
    have hψ' : e ψ = φ := by
      change moduleSheafificationUnit F ≫
        (PresheafOfModules.restrictScalars (ringSheafificationUnit O)).map ψ.val = φ
      exact hψ
    exact hψ'.trans (e.apply_symm_apply φ).symm

/-! ## The induced action and its universal property -/

/-- The underlying set presheaf of the sheafified ring. -/
abbrev ringSheafificationSetPresheaf {X : TopCat.{v}}
    (O : RingPresheaf.{v, v} X) : TopCat.Presheaf (Type v) X :=
  Formalization.Books.Sheaves.Unit05.underlyingPresheaf
    (CategoryTheory.forget RingCat) (ringSheafification O).obj

/-- The pointwise scalar action on sections of the sheafified module. -/
noncomputable def moduleSheafificationActionAt {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) (U : Opens X) :
    ((ringSheafification O).obj.obj (op U) : Type v) →
      ((moduleSheafification F).val.obj (op U) : Type v) →
      ((moduleSheafification F).val.obj (op U) : Type v) :=
  fun r m => r • m

/-- The scalar action is compatible with restrictions. -/
theorem moduleSheafificationActionAt_natural {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O)
    {U V : Opens X} (h : V ≤ U)
    (r : (ringSheafification O).obj.obj (op U))
    (m : (moduleSheafification F).val.obj (op U)) :
    moduleSheafificationActionAt F V
        ((ringSheafification O).obj.map (homOfLE h).op r)
        ((moduleSheafification F).val.map (homOfLE h).op m) =
      (moduleSheafification F).val.map (homOfLE h).op
        (moduleSheafificationActionAt F U r m) := by
  simp [moduleSheafificationActionAt]

/-- The scalar action as a morphism of sheaves of sets, written on the
underlying presheaves.  The corresponding morphism in the sheaf category is
`moduleSheafificationActionSheaf` below. -/
noncomputable def moduleSheafificationAction {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    presheafProduct (ringSheafificationSetPresheaf O)
        (moduleSheafificationSetPresheaf F) ⟶
      moduleSheafificationSetPresheaf F :=
  { app := fun U => TypeCat.ofHom (fun st =>
      let p := (presheafProductSectionsEquiv
        (ringSheafificationSetPresheaf O) (moduleSheafificationSetPresheaf F)
        U.unop) st
      moduleSheafificationActionAt F U.unop p.1 p.2)
    naturality := by
      intro U V f
      ext st
      let p := (presheafProductSectionsEquiv
        (ringSheafificationSetPresheaf O) (moduleSheafificationSetPresheaf F)
        U.unop) st
      change moduleSheafificationActionAt F V.unop
          (restriction (F := ringSheafificationSetPresheaf O) f.unop.le p.1)
          (restriction (F := moduleSheafificationSetPresheaf F) f.unop.le p.2) =
        restriction (F := moduleSheafificationSetPresheaf F) f.unop.le
          (moduleSheafificationActionAt F U.unop p.1 p.2)
      exact moduleSheafificationActionAt_natural F f.unop.le p.1 p.2 }

/-! The source's action is a map of sheaves of sets.  The presheaf product
above is the underlying presheaf of a sheaf because finite products of
sheaves are sheaves; keeping this carrier explicit makes the map available
at the same underlying sections used in the preceding definition. -/

/-- The underlying set sheaf of the categorical module sheafification. -/
noncomputable abbrev moduleSheafificationSetSheaf {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) : TopCat.Sheaf (Type v) X :=
  letI : AlgebraicStructureType AddCommGrpCat (CategoryTheory.forget AddCommGrpCat) :=
    standardAlgebraicStructureTypes.{v, v, v}.2.1
  underlyingSheaf (CategoryTheory.forget AddCommGrpCat)
    ((SheafOfModules.toSheaf (ringSheafification O)).obj
      (moduleSheafification F))

/-- The presheaf product used by the scalar action is a sheaf. -/
theorem moduleSheafificationActionDomain_isSheaf {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    TopCat.Presheaf.IsSheaf (presheafProduct
      (ringSheafificationSetPresheaf O)
      (moduleSheafificationSetPresheaf F)) := by
  let R : TopCat.Sheaf (Type v) X :=
    ⟨ringSheafificationSetPresheaf O,
      (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
        (CategoryTheory.forget RingCat) (ringSheafification O).obj).mp
        (ringSheafification O).property⟩
  let M : TopCat.Sheaf (Type v) X :=
    ⟨moduleSheafificationSetPresheaf F,
      (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
        (CategoryTheory.forget AddCommGrpCat)
        ((SheafOfModules.toSheaf (ringSheafification O)).obj
          (moduleSheafification F)).obj).mp
        ((SheafOfModules.toSheaf (ringSheafification O)).obj
          (moduleSheafification F)).property⟩
  change TopCat.Presheaf.IsSheaf (presheafProduct R.presheaf M.presheaf)
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types]
  intro ι U sf hsf
  let e := fun i : ι =>
    presheafProductSectionsEquiv R.presheaf M.presheaf (U i)
  have hInfLeft (i j : ι) :
      Opens.infLELeft (U i) (U j) =
        homOfLE (show U i ⊓ U j ≤ U i from inf_le_left) := by
    apply Subsingleton.elim
  have hInfRight (i j : ι) :
      Opens.infLERight (U i) (U j) =
        homOfLE (show U i ⊓ U j ≤ U j from inf_le_right) := by
    apply Subsingleton.elim
  have hLeSupr (i : ι) :
      Opens.leSupr U i =
        homOfLE (show U i ≤ iSup U from le_iSup U i) := by
    apply Subsingleton.elim
  have hR : TopCat.Presheaf.IsCompatible R.presheaf U
      (fun i => (e i (sf i)).1) := by
    intro i j
    have h := hsf i j
    rw [← (e i).symm_apply_apply (sf i),
      ← (e j).symm_apply_apply (sf j), hInfLeft i j, hInfRight i j] at h
    dsimp [e] at h
    rw [presheafProduct_restriction, presheafProduct_restriction] at h
    exact congrArg Prod.fst h
  have hM : TopCat.Presheaf.IsCompatible M.presheaf U
      (fun i => (e i (sf i)).2) := by
    intro i j
    have h := hsf i j
    rw [← (e i).symm_apply_apply (sf i),
      ← (e j).symm_apply_apply (sf j), hInfLeft i j, hInfRight i j] at h
    dsimp [e] at h
    rw [presheafProduct_restriction, presheafProduct_restriction] at h
    exact congrArg Prod.snd h
  obtain ⟨sR, hsR, hsR_unique⟩ :=
    TopCat.Presheaf.IsSheaf.isSheafUniqueGluing_types R.property
      (fun i => (e i (sf i)).1) hR
  obtain ⟨sM, hsM, hsM_unique⟩ :=
    TopCat.Presheaf.IsSheaf.isSheafUniqueGluing_types M.property
      (fun i => (e i (sf i)).2) hM
  refine ⟨(presheafProductSectionsEquiv R.presheaf M.presheaf (iSup U)).symm
      (sR, sM), ?_, ?_⟩
  · intro i
    have h := hsR i
    have h' := hsM i
    rw [← (e i).symm_apply_apply (sf i),
      hLeSupr i]
    dsimp [e] at ⊢
    rw [presheafProduct_restriction]
    simp only [Equiv.symm_apply_apply]
    apply (presheafProductSectionsEquiv R.presheaf M.presheaf (U i)).injective
    simpa [e, presheafProductSectionsEquiv] using (Prod.ext h h')
  · intro t ht
    let p := presheafProductSectionsEquiv R.presheaf M.presheaf (iSup U) t
    have hpR : TopCat.Presheaf.IsGluing R.presheaf U
        (fun i => (e i (sf i)).1) p.1 := by
      intro i
      have h := ht i
      rw [← (presheafProductSectionsEquiv R.presheaf M.presheaf (iSup U)).symm_apply_apply t,
        ← (e i).symm_apply_apply (sf i), hLeSupr i] at h
      dsimp [e] at h
      rw [presheafProduct_restriction] at h
      exact congrArg Prod.fst h
    have hpM : TopCat.Presheaf.IsGluing M.presheaf U
        (fun i => (e i (sf i)).2) p.2 := by
      intro i
      have h := ht i
      rw [← (presheafProductSectionsEquiv R.presheaf M.presheaf (iSup U)).symm_apply_apply t,
        ← (e i).symm_apply_apply (sf i), hLeSupr i] at h
      dsimp [e] at h
      rw [presheafProduct_restriction] at h
      exact congrArg Prod.snd h
    apply (presheafProductSectionsEquiv R.presheaf M.presheaf (iSup U)).injective
    change p = (sR, sM)
    have hpR' := hsR_unique p.1 hpR
    have hpM' := hsM_unique p.2 hpM
    exact Prod.ext hpR' hpM'

/-- The scalar action as an actual morphism of sheaves of sets. -/
noncomputable def moduleSheafificationActionSheaf {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) :
    (⟨presheafProduct (ringSheafificationSetPresheaf O)
        (moduleSheafificationSetPresheaf F),
      moduleSheafificationActionDomain_isSheaf F⟩ : TopCat.Sheaf (Type v) X) ⟶
      moduleSheafificationSetSheaf F :=
  ⟨by
    change presheafProduct (ringSheafificationSetPresheaf O)
        (moduleSheafificationSetPresheaf F) ⟶
      moduleSheafificationSetPresheaf F
    exact moduleSheafificationAction F⟩

/-- The action map makes the sheafification unit a map of module presheaves;
this is the source's commutative square on sections. -/
theorem moduleSheafificationUnit_action_compatibility {X : TopCat.{v}}
    {O : RingPresheaf.{v, v} X} (F : PMod O) (U : Opens X)
    (r : O.obj (op U)) (m : F.obj (op U)) :
    moduleSheafificationActionAt F U
        ((ringSheafificationUnit O).app (op U) r)
      ((moduleSheafificationUnit F).app (op U) m) =
      (moduleSheafificationUnit F).app (op U) (r • m) := by
  dsimp [moduleSheafificationActionAt]
  have h := (((moduleSheafificationUnit F).app (op U)).hom.map_smul r m).symm
  exact h

/-! ## Restriction, tensor product sheaves, and change of rings -/

/-- Restriction of scalars for sheaves of modules. -/
noncomputable abbrev sheafRestrictionOfScalars {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂) :
    SheafOfModules.{v} O₂ ⥤ SheafOfModules.{v} O₁ :=
  SheafOfModules.restrictScalars α

/-- The presheaf-level extension of scalars underlying the tensor product
sheaf. -/
noncomputable abbrev sheafTensorProductPresheaf {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    (α : O₁ ⟶ O₂) (G : SheafOfModules.{v} O₁) : PMod O₂.obj :=
  tensorProductPresheaf α.hom G.val

/-- The presheaf tensor product need not be a sheaf. -/
theorem tensorProductPresheaf_not_always_isSheaf :
    ¬ ∀ {X : TopCat.{v}}
      {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂) (G : SheafOfModules.{v} O₁),
      Presheaf.IsSheaf (Opens.grothendieckTopology X)
        (sheafTensorProductPresheaf α G).presheaf := by
  sorry

/-- The tensor product sheaf in the source is module sheafification of the
presheaf-level extension of scalars. -/
noncomputable def tensorProductSheaf {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
    (α : O₁ ⟶ O₂) (G : SheafOfModules.{v} O₁) :
    SheafOfModules.{v} O₂ := by
  exact (PresheafOfModules.sheafification (𝟙 O₂.obj)).obj
    (sheafTensorProductPresheaf α G)

/-- The sheaf change-of-rings functor. -/
noncomputable def sheafChangeOfRings {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂) :
    SheafOfModules.{v} O₁ ⥤ SheafOfModules.{v} O₂ where
  obj G := tensorProductSheaf α G
  map f := (PresheafOfModules.sheafification (𝟙 O₂.obj)).map
    ((changeOfRings α.hom).map f.val)

/-! ## Adjunction and stalks -/

/-- Change of rings is left adjoint to restriction of scalars on sheaves. -/
theorem exists_sheafChangeOfRingsAdjunction {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂) :
    Nonempty (sheafChangeOfRings α ⊣ sheafRestrictionOfScalars α) := by
  let hR : ∀ F : SheafOfModules.{v} O₂,
      (restrictionOfScalars α.hom).obj F.val ≅
        ((sheafRestrictionOfScalars α).obj F).val := fun F => by
    refine PresheafOfModules.isoMk
      (fun U => (ModuleCat.restrictScalarsCongr
        (f := (asIdentityRingPresheafMorphism α.hom).app U |>.hom)
        (g := (α.hom.app U).hom) (by
          ext x
          simp [asIdentityRingPresheafMorphism])).app (F.val.obj U)) ?_
    intro U V f
    ext x
    change F.val.map f x = F.val.map f x
    rfl
  let ePost (G : SheafOfModules.{v} O₁) (F : SheafOfModules.{v} O₂) :
      (G.val ⟶ (restrictionOfScalars α.hom).obj F.val) ≃
        (G.val ⟶ ((sheafRestrictionOfScalars α).obj F).val) :=
    { toFun := fun f => f ≫ (hR F).hom
      invFun := fun f => f ≫ (hR F).inv
      left_inv := by intro f; simp
      right_inv := by intro f; simp }
  let eFF (G : SheafOfModules.{v} O₁) (F : SheafOfModules.{v} O₂) :
      (G.val ⟶ ((sheafRestrictionOfScalars α).obj F).val) ≃
        (G ⟶ (sheafRestrictionOfScalars α).obj F) :=
    (SheafOfModules.fullyFaithfulForget O₁).homEquiv
      (X := G) (Y := (sheafRestrictionOfScalars α).obj F) |>.symm
  let eSh (G : SheafOfModules.{v} O₁) (F : SheafOfModules.{v} O₂) :
      ((sheafChangeOfRings α).obj G ⟶ F) ≃
        ((changeOfRings α.hom).obj G.val ⟶ F.val) :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 O₂.obj)).homEquiv
      ((changeOfRings α.hom).obj G.val) F
  let eHom :
      ∀ (G : SheafOfModules.{v} O₁) (F : SheafOfModules.{v} O₂),
        ((sheafChangeOfRings α).obj G ⟶ F) ≃
          (G ⟶ (sheafRestrictionOfScalars α).obj F) :=
    fun G F =>
      (eSh G F).trans
        (((changeOfRingsAdjunction α.hom).homEquiv G.val F.val).trans
          ((ePost G F).trans
            (eFF G F)))
  let adj : sheafChangeOfRings α ⊣ sheafRestrictionOfScalars α :=
    Adjunction.mkOfHomEquiv
      { homEquiv := eHom
        homEquiv_naturality_left_symm := by sorry
        homEquiv_naturality_right := by sorry }
  exact Nonempty.intro adj

/-- A chosen adjunction between sheaf extension and restriction of scalars. -/
noncomputable def sheafChangeOfRingsAdjunction {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂) :
    sheafChangeOfRings α ⊣ sheafRestrictionOfScalars α :=
  Classical.choice (exists_sheafChangeOfRingsAdjunction α)

/-- The source-facing Hom bijection for tensor product sheaves and
restriction of scalars. -/
noncomputable def sheafChangeOfRingsHomEquiv {X : TopCat.{v}}
    {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}
      (α : O₁ ⟶ O₂)
    (G : SheafOfModules.{v} O₁) (F : SheafOfModules.{v} O₂) :
    (G ⟶ (sheafRestrictionOfScalars α).obj F) ≃
      ((sheafChangeOfRings α).obj G ⟶ F) :=
  (sheafChangeOfRingsAdjunction α).homEquiv G F |>.symm

/-- The stalk tensor-product comparison from the preceding module-stalk
chapter, stated in the source's module-isomorphism form. -/
theorem sheafification_stalk_tensorProduct_iso {X : TopCat.{v}}
    {O O' : CommRingPresheaf X} (α : O ⟶ O')
    (F : CommRingPresheafModule O) (x : X) :
    Nonempty (stalkTensorProduct α F x ≅
      ModuleCat.of (O'.stalk x)
        (↑(TopCat.Presheaf.stalk
          (tensorProductPresheaf (commRingPresheafMorphismToRingPresheaf α) F).presheaf x))) := by
  exact stalk_tensorProductPresheaf_iso α F x

/-! ## Stalks of tensor product sheaves -/

/-- A sheaf of commutative rings, matching the source's tensor notation. -/
abbrev CommRingSheaf (X : TopCat.{v}) :=
  Sheaf (Opens.grothendieckTopology X) CommRingCat.{v}

/-- Forgetting commutativity on a sheaf of rings. -/
noncomputable abbrev commRingSheafToRingSheaf {X : TopCat.{v}}
    (O : CommRingSheaf X) :
    Sheaf (Opens.grothendieckTopology X) RingCat.{v} :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat)).obj O

/-- The underlying sheaf of modules over a commutative-ring sheaf. -/
abbrev CommRingSheafModule {X : TopCat.{v}} (O : CommRingSheaf X) :=
  SheafOfModules.{v} (commRingSheafToRingSheaf O)

/-- The underlying `RingCat` morphism of a commutative sheaf-ring morphism. -/
noncomputable abbrev commRingSheafMorphismToRingSheaf {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (α : O₁ ⟶ O₂) :
    commRingSheafToRingSheaf O₁ ⟶ commRingSheafToRingSheaf O₂ :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat)).map α

/-- The stalk module of a sheaf of modules over a commutative sheaf of rings. -/
noncomputable def commRingSheafModuleStalk {X : TopCat.{v}}
    {O : CommRingSheaf X} (G : CommRingSheafModule O) (x : X) :
    ModuleCat (↑(TopCat.Presheaf.stalk O.obj x)) := by
  letI : Module (↑(TopCat.Presheaf.stalk O.obj x))
      (↑(TopCat.Presheaf.stalk G.val.presheaf x)) :=
    Formalization.Books.Sheaves.Unit14.stalkModule O.obj G.val x
  exact ModuleCat.of (↑(TopCat.Presheaf.stalk O.obj x))
    (↑(TopCat.Presheaf.stalk G.val.presheaf x))

/-- The stalk-level extension of scalars in the source's tensor statement. -/
noncomputable def sheafStalkTensorProduct {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (α : O₁ ⟶ O₂)
    (G : CommRingSheafModule O₁) (x : X) :
    ModuleCat (↑(TopCat.Presheaf.stalk O₂.obj x)) := by
  exact (ModuleCat.extendScalars
      ((TopCat.Presheaf.stalkFunctor (CommRingCat.{v}) x).map α.hom).hom).obj
    (commRingSheafModuleStalk G x)

/-- The tensor product sheaf for commutative sheaves of rings. -/
noncomputable abbrev commRingTensorProductSheaf {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (α : O₁ ⟶ O₂)
    (G : CommRingSheafModule O₁) : CommRingSheafModule O₂ :=
  tensorProductSheaf (commRingSheafMorphismToRingSheaf α) G

/-- The source's stalk comparison for the sheafified tensor product. -/
theorem stalk_tensorProductSheaf_statement {X : TopCat.{v}}
    {O₁ O₂ : CommRingSheaf X} (α : O₁ ⟶ O₂)
    (G : CommRingSheafModule O₁) (x : X) :
    Nonempty (sheafStalkTensorProduct α G x ≅
      commRingSheafModuleStalk (commRingTensorProductSheaf α G) x) := by
  sorry

end

end Formalization.Books.Sheaves.Unit17
