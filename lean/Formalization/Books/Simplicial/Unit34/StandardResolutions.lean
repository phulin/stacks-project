import Formalization.Books.Simplicial.Unit33.Godement
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Simplicial Methods, Chapter 34: Standard resolutions

The standard resolution is the Godement construction attached to an
adjunction. The definitions below retain the source's notation while using
the canonical functor-category and simplicial-object interfaces from Chapter
33. The iterated functors in Chapter 33 contain the harmless identity functor
at the right; the displayed source formulas are represented after canonical
unitor transports.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit34

open CategoryTheory
open CategoryTheory.SimplicialObject
open Opposite
open Formalization.Books.Simplicial.Unit33

universe uA vA uS vS u

/-! ## The adjunction and the comonad-like endofunctor -/

/-- The data in Situation 34.1: `U` is left adjoint to `V`. -/
structure StandardResolutionSituation (A : Type uA) (S : Type uS)
    [Category.{vA} A] [Category.{vS} S] where
  U : S ⥤ A
  V : A ⥤ S
  adjunction : U ⊣ V

/-- The endofunctor `U ∘ V` on `A` used in the standard resolution. -/
def standardResolutionBase {A : Type uA} {S : Type uS}
    [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) : A ⥤ A :=
  T.V ⋙ T.U

/-- The source's counit `d : U ∘ V ⟶ id_A`. -/
abbrev standardResolutionCounit {A : Type uA} {S : Type uS}
    [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    standardResolutionBase T ⟶ 𝟭 A :=
  T.adjunction.counit

/-- The source's unit `η : id_S ⟶ V ∘ U`. -/
abbrev standardResolutionUnit {A : Type uA} {S : Type uS}
    [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    𝟭 S ⟶ T.U ⋙ T.V :=
  T.adjunction.unit

/-- The unit-insertion map `U V ⟶ U V U V`, with associators and unitors
made explicit so that it is a morphism between the chosen functors. -/
def standardResolutionComultiplication {A : Type uA} {S : Type uS}
    [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    standardResolutionBase T ⟶ standardResolutionBase T ⋙
      standardResolutionBase T := by
  let raw :
      (T.V ⋙ 𝟭 S) ⋙ T.U ⟶ (T.V ⋙ (T.U ⋙ T.V)) ⋙ T.U :=
    Functor.whiskerRight
      (Functor.whiskerLeft T.V T.adjunction.unit) T.U
  exact
    Functor.whiskerRight (Functor.rightUnitor T.V).inv T.U ≫ raw ≫
      (Functor.associator T.V (T.U ⋙ T.V) T.U).hom ≫
      Functor.whiskerLeft T.V (Functor.associator T.U T.V T.U).hom ≫
      (Functor.associator T.V T.U (T.V ⋙ T.U)).inv

/-! ## Degrees, faces, degeneracies, and the augmentation -/

/-- The index set `{-1, 0, 1, ...}` used by the source. -/
abbrev StandardResolutionIndex := Option ℕ

/-- Addition of resolution indices, with `none` denoting `-1`. -/
def standardResolutionIndexAdd : StandardResolutionIndex →
    StandardResolutionIndex → StandardResolutionIndex
  | none, j => j
  | some i, none => some i
  | some i, some j => some (i + j + 1)

/-- The functor `X_n`; `none` denotes the source's `X_{-1} = id_A`. -/
def standardResolutionDegree {A : Type uA} {S : Type uS}
    [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    StandardResolutionIndex → A ⥤ A
  | none => 𝟭 A
  | some n => godementDegree (standardResolutionBase T) n

/-- The composition formula `X_{n+m+1} = X_n ∘ X_m`, including the cases in
which one of the indices is `-1`. The equalities use canonical functor
identity and associativity normalizations. -/
theorem standardResolutionDegree_comp {A : Type uA} {S : Type uS}
    [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S)
    (i j : StandardResolutionIndex) :
    standardResolutionDegree T (standardResolutionIndexAdd i j) =
      standardResolutionDegree T i ⋙ standardResolutionDegree T j := by
  cases i <;> cases j <;>
    simp only [standardResolutionIndexAdd, standardResolutionDegree,
      godementDegree_add, Functor.id_comp, Functor.comp_id]

/-- The degreewise boundary maps, including the degree-zero counit. -/
def standardResolutionBoundary {A : Type uA} {S : Type uS}
    [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) (n : ℕ) (j : Fin (n + 1)) :
    standardResolutionDegree T (some n) ⟶
      match n with
      | 0 => standardResolutionDegree T none
      | k + 1 => standardResolutionDegree T (some k) := by
  cases n with
  | zero =>
      simpa [standardResolutionDegree, standardResolutionBase,
        godementDegree, iteratedEndofunctor] using
        (godementFace (standardResolutionBase T)
          (standardResolutionCounit T) (n := 0) j)
  | succ n =>
      simpa [standardResolutionDegree, standardResolutionBase,
        godementDegree, iteratedEndofunctor] using
        (godementFace (standardResolutionBase T)
          (standardResolutionCounit T) (n := n + 1) j)

/-- The source's face maps in positive simplicial degrees. -/
def standardResolutionFace {A : Type uA} {S : Type uS}
    [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) (n : ℕ) (j : Fin (n + 2)) :
    standardResolutionDegree T (some (n + 1)) ⟶
      standardResolutionDegree T (some n) := by
  simpa [standardResolutionDegree, standardResolutionBase,
    godementDegree, iteratedEndofunctor] using
    (godementFace (standardResolutionBase T)
      (standardResolutionCounit T) (n := n + 1) j)

/-- The source's degeneracy maps. -/
def standardResolutionDegeneracy {A : Type uA} {S : Type uS}
    [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) (n : ℕ) (j : Fin (n + 1)) :
    standardResolutionDegree T (some n) ⟶
      standardResolutionDegree T (some (n + 1)) := by
  simpa [standardResolutionDegree, standardResolutionBase,
    godementDegree, iteratedEndofunctor] using
    (godementDegeneracy (standardResolutionBase T)
      (standardResolutionComultiplication T) j)

/-- The adjunction triangle identities imply the Godement equations. -/
theorem standardResolution_godementEquations
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    GodementEquations (standardResolutionBase T)
      (standardResolutionCounit T) (standardResolutionComultiplication T) := by
  refine { left_unit := ?_, right_unit := ?_, coassoc := ?_ }
  · dsimp [standardResolutionBase, standardResolutionCounit,
      standardResolutionComultiplication]
    ext X
    simp
    rw [← T.U.map_comp, T.adjunction.right_triangle_components]
    simp
  · dsimp [standardResolutionBase, standardResolutionCounit,
      standardResolutionComultiplication]
    ext X
    simp
  · dsimp [standardResolutionBase, standardResolutionCounit,
      standardResolutionComultiplication]
    ext X
    simp
    rw [← T.U.map_comp, ← T.U.map_comp]
    exact congrArg T.U.map
      (T.adjunction.unit_naturality (T.adjunction.unit.app (T.V.obj X)))

/-- The chosen simplicial object supplied by the standard-resolution
construction. -/
noncomputable def standardResolutionData
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    GodementSimplicialData (standardResolutionBase T)
      (standardResolutionCounit T) (standardResolutionComultiplication T) :=
  (godement_simplicial_data (standardResolutionBase T)
    (standardResolutionCounit T) (standardResolutionComultiplication T)
    (standardResolution_godementEquations T)).some

/-- The augmentation data for the standard resolution. -/
noncomputable def standardResolutionAugmentationData
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    GodementAugmentationData (standardResolutionBase T)
      (standardResolutionCounit T) (standardResolutionComultiplication T) :=
  (godement_augmentation_condition (standardResolutionBase T)
    (standardResolutionCounit T) (standardResolutionComultiplication T)
    (standardResolution_godementEquations T)).some

/-! ## The actual simplicial object and its formulas -/

abbrev standardResolutionObject
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) : SimplicialObject (A ⥤ A) :=
  (standardResolutionAugmentationData T).simplicial.object

abbrev standardResolutionAugmentation
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    standardResolutionObject T ⟶ (SimplicialObject.const (A ⥤ A)).obj (𝟭 A) :=
  (standardResolutionAugmentationData T).augmentation

theorem standardResolution_object_degree
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) (n : ℕ) :
    (standardResolutionObject T).obj (op (SimplexCategory.mk n)) =
      standardResolutionDegree T (some n) := by
  exact (standardResolutionAugmentationData T).simplicial.object_obj n

theorem standardResolution_face_formula
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) (n : ℕ) (j : Fin (n + 2)) :
    eqToHom (standardResolution_object_degree T (n + 1)).symm ≫
        (standardResolutionObject T).δ j ≫
    eqToHom (standardResolution_object_degree T n) =
      standardResolutionFace T n j := by
  change _ = godementFace (standardResolutionBase T)
    (standardResolutionCounit T) j
  exact (standardResolutionAugmentationData T).simplicial.face_def n j

theorem standardResolution_degeneracy_formula
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) (n : ℕ) (j : Fin (n + 1)) :
    eqToHom (standardResolution_object_degree T n).symm ≫
        (standardResolutionObject T).σ j ≫
        eqToHom (standardResolution_object_degree T (n + 1)) =
      standardResolutionDegeneracy T n j := by
  exact (standardResolutionAugmentationData T).simplicial.degeneracy_def n j

theorem standardResolution_augmentation_formula
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) (n : ℕ) :
    eqToHom (standardResolution_object_degree T n).symm ≫
        (standardResolutionAugmentation T).app (op (SimplexCategory.mk n)) =
      (standardResolutionAugmentationData T).component n := by
  exact (standardResolutionAugmentationData T).component_formula n

/-- The standard resolution is a simplicial object with the counit
augmentation. -/
theorem standardResolution_is_simplicial_and_augmented
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    Nonempty (GodementAugmentationData (standardResolutionBase T)
      (standardResolutionCounit T) (standardResolutionComultiplication T)) := by
  exact ⟨standardResolutionAugmentationData T⟩
/-! ## The two homotopy equivalences -/

/- Chapter 33 also packages these maps in
`GodementWhiskeredAugmentationData`. Its universe parameters identify some
object and morphism universes, which is narrower than Situation 34.1. The
explicit whiskering below retains the source's maps for arbitrary category
universes without weakening their source or target. -/

/-- The simplicial object obtained by postcomposing the standard resolution
with `V`. -/
abbrev standardResolutionOuterObject
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) : SimplicialObject (A ⥤ S) :=
  ((SimplicialObject.whiskering (A ⥤ A) (A ⥤ S)).obj
    ((Functor.whiskeringRight A A S).obj T.V)).obj (standardResolutionObject T)

/-- The source's outer augmentation `1_V ⋆ ε`, with its canonical functor
unitor transport made explicit. -/
noncomputable def standardResolutionOuterRawAugmentation
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    standardResolutionOuterObject T ⟶
      (SimplicialObject.const (A ⥤ S)).obj (𝟭 A ⋙ T.V) := by
  refine { app := fun n => (Functor.whiskerRight
      ((standardResolutionAugmentation T).app n) T.V), naturality := ?_ }
  intro n m f
  dsimp [standardResolutionOuterObject]
  simp
  have h0 := (standardResolutionAugmentation T).naturality f
  have hconst : ((SimplicialObject.const (A ⥤ A)).obj (𝟭 A)).map f =
      𝟙 (𝟭 A) := by
    simp
  rw [hconst] at h0
  have h := congrArg (fun k => Functor.whiskerRight k T.V) h0
  rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp] at h
  have hid : Functor.whiskerRight (𝟙 (𝟭 A)) T.V =
      𝟙 (𝟭 A ⋙ T.V) := by
    ext X
    simp
  rw [hid] at h
  exact h

abbrev standardResolutionOuterAugmentation
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :=
  standardResolutionOuterRawAugmentation T ≫
    (SimplicialObject.const (A ⥤ S)).map (Functor.leftUnitor T.V).hom

/-! The inner object uses precomposition by `U`, represented by the standard
functor-category whiskering API. -/
abbrev standardResolutionInnerObject
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) : SimplicialObject (S ⥤ A) :=
  ((SimplicialObject.whiskering (A ⥤ A) (S ⥤ A)).obj
    ((Functor.whiskeringLeft S A A).obj T.U)).obj (standardResolutionObject T)

noncomputable def standardResolutionInnerRawAugmentation
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    standardResolutionInnerObject T ⟶
      (SimplicialObject.const (S ⥤ A)).obj (T.U ⋙ 𝟭 A) := by
  refine { app := fun n => (Functor.whiskerLeft T.U
      ((standardResolutionAugmentation T).app n)), naturality := ?_ }
  intro n m f
  dsimp [standardResolutionInnerObject]
  simp
  have h0 := (standardResolutionAugmentation T).naturality f
  have hconst : ((SimplicialObject.const (A ⥤ A)).obj (𝟭 A)).map f =
      𝟙 (𝟭 A) := by
    simp
  rw [hconst] at h0
  have h := congrArg (fun k => Functor.whiskerLeft T.U k) h0
  rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp] at h
  have hid : Functor.whiskerLeft T.U (𝟙 (𝟭 A)) =
      𝟙 (T.U ⋙ 𝟭 A) := by
    ext X
    simp
  rw [hid] at h
  exact h

abbrev standardResolutionInnerAugmentation
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :=
  standardResolutionInnerRawAugmentation T ≫
    (SimplicialObject.const (S ⥤ A)).map (Functor.rightUnitor T.U).hom

/-- The degreewise-unit section used as the inverse in the source's two
homotopy-equivalence constructions. -/
noncomputable def standardResolutionOuterDegreeZeroSectionRaw
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    T.V ⟶ (standardResolutionObject T).obj
      (op (SimplexCategory.mk 0)) ⋙ T.V := by
  let transport :
      T.V ⋙ (T.U ⋙ T.V) ⟶
        (standardResolutionDegree T (some 0)) ⋙ T.V :=
    (Functor.associator T.V T.U T.V).inv ≫
      Functor.whiskerRight
        (Functor.rightUnitor (standardResolutionBase T)).inv T.V ≫
      Functor.whiskerRight
        (eqToHom (show standardResolutionBase T ⋙ 𝟭 A =
          standardResolutionDegree T (some 0) from rfl)) T.V
  let degree_to_object :
      (standardResolutionDegree T (some 0)) ⋙ T.V ⟶
        (standardResolutionObject T).obj (op (SimplexCategory.mk 0)) ⋙ T.V :=
    Functor.whiskerRight
      (eqToHom (standardResolution_object_degree T 0).symm) T.V
  exact (Functor.rightUnitor T.V).inv ≫
    Functor.whiskerLeft T.V T.adjunction.unit ≫ transport ≫ degree_to_object

/-- The raw degree-zero section regarded as a component of the outer
whiskered simplicial object. -/
noncomputable def standardResolutionOuterDegreeZeroSection
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    T.V ⟶ (standardResolutionOuterObject T).obj
      (op (SimplexCategory.mk 0)) :=
  standardResolutionOuterDegreeZeroSectionRaw T

noncomputable def standardResolutionOuterHomotopyInverse
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    (SimplicialObject.const (A ⥤ S)).obj T.V ⟶
      standardResolutionOuterObject T := by
  let h0 : T.V ⟶
      (standardResolutionOuterObject T).obj (op (SimplexCategory.mk 0)) := by
    exact standardResolutionOuterDegreeZeroSection T
  let q : ∀ n : SimplexCategoryᵒᵖ, op (SimplexCategory.mk 0) ⟶ n :=
    fun n => (SimplexCategory.const n.unop (SimplexCategory.mk 0) 0).op
  let app : ∀ n : SimplexCategoryᵒᵖ, T.V ⟶
      (standardResolutionOuterObject T).obj n := fun n =>
    h0 ≫ (standardResolutionOuterObject T).map (q n)
  refine { app := app, naturality := ?_ }
  intro X Y f
  let qX := q X
  let qY := q Y
  have hq : qY = qX ≫ f := by
    dsimp [q, qX, qY]
    apply Quiver.Hom.unop_inj
    change SimplexCategory.const Y.unop (SimplexCategory.mk 0) 0 =
      f.unop ≫ SimplexCategory.const X.unop (SimplexCategory.mk 0) 0
    exact (SimplexCategory.eq_const_to_zero _).symm
  have hconst : ((SimplicialObject.const (A ⥤ S)).obj T.V).map f = 𝟙 T.V := by
    simp
  change ((SimplicialObject.const (A ⥤ S)).obj T.V).map f ≫
      (h0 ≫ (standardResolutionOuterObject T).map qY) =
    (h0 ≫ (standardResolutionOuterObject T).map qX) ≫
      (standardResolutionOuterObject T).map f
  rw [hconst, hq]
  rw [Functor.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫
      (standardResolutionOuterObject T).map qX ≫
      (standardResolutionOuterObject T).map f)
      (Category.id_comp h0)

theorem standardResolutionOuterHomotopyInverse_app
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) (n : SimplexCategoryᵒᵖ) :
    (standardResolutionOuterHomotopyInverse T).app n =
      standardResolutionOuterDegreeZeroSection T ≫
        (standardResolutionOuterObject T).map
          (SimplexCategory.const n.unop (SimplexCategory.mk 0) 0).op := by
  rfl

/-- The degree-zero unit section for the inner whiskered resolution, with all
associator and unitor transports exposed. -/
noncomputable def standardResolutionInnerDegreeZeroSectionRaw
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    T.U ⟶ T.U ⋙ (standardResolutionObject T).obj
      (op (SimplexCategory.mk 0)) := by
  let raw : (𝟭 S) ⋙ T.U ⟶ (T.U ⋙ T.V) ⋙ T.U :=
    Functor.whiskerRight T.adjunction.unit T.U
  exact (Functor.leftUnitor T.U).inv ≫ raw ≫
    (Functor.associator T.U T.V T.U).hom ≫
    Functor.whiskerLeft T.U
      (Functor.rightUnitor (standardResolutionBase T)).inv ≫
    Functor.whiskerLeft T.U
      (eqToHom (show standardResolutionBase T ⋙ 𝟭 A =
        standardResolutionDegree T (some 0) from rfl)) ≫
    Functor.whiskerLeft T.U
      (eqToHom (standardResolution_object_degree T 0).symm)

/-- The raw degree-zero section regarded as a component of the inner
whiskered simplicial object. -/
noncomputable def standardResolutionInnerDegreeZeroSection
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    T.U ⟶ (standardResolutionInnerObject T).obj
      (op (SimplexCategory.mk 0)) :=
  standardResolutionInnerDegreeZeroSectionRaw T

noncomputable def standardResolutionInnerHomotopyInverse
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    (SimplicialObject.const (S ⥤ A)).obj T.U ⟶
      standardResolutionInnerObject T := by
  let h0 : T.U ⟶
      (standardResolutionInnerObject T).obj (op (SimplexCategory.mk 0)) := by
    exact standardResolutionInnerDegreeZeroSection T
  let q : ∀ n : SimplexCategoryᵒᵖ, op (SimplexCategory.mk 0) ⟶ n :=
    fun n => (SimplexCategory.const n.unop (SimplexCategory.mk 0) 0).op
  let app : ∀ n : SimplexCategoryᵒᵖ, T.U ⟶
      (standardResolutionInnerObject T).obj n := fun n =>
    h0 ≫ (standardResolutionInnerObject T).map (q n)
  refine { app := app, naturality := ?_ }
  intro X Y f
  let qX := q X
  let qY := q Y
  have hq : qY = qX ≫ f := by
    dsimp [q, qX, qY]
    apply Quiver.Hom.unop_inj
    change SimplexCategory.const Y.unop (SimplexCategory.mk 0) 0 =
      f.unop ≫ SimplexCategory.const X.unop (SimplexCategory.mk 0) 0
    exact (SimplexCategory.eq_const_to_zero _).symm
  have hconst : ((SimplicialObject.const (S ⥤ A)).obj T.U).map f = 𝟙 T.U := by
    simp
  change ((SimplicialObject.const (S ⥤ A)).obj T.U).map f ≫
      (h0 ≫ (standardResolutionInnerObject T).map qY) =
    (h0 ≫ (standardResolutionInnerObject T).map qX) ≫
      (standardResolutionInnerObject T).map f
  rw [hconst, hq]
  rw [Functor.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫
      (standardResolutionInnerObject T).map qX ≫
      (standardResolutionInnerObject T).map f)
      (Category.id_comp h0)

theorem standardResolutionInnerHomotopyInverse_app
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) (n : SimplexCategoryᵒᵖ) :
    (standardResolutionInnerHomotopyInverse T).app n =
      standardResolutionInnerDegreeZeroSection T ≫
        (standardResolutionInnerObject T).map
          (SimplexCategory.const n.unop (SimplexCategory.mk 0) 0).op := by
  rfl

private theorem standardResolutionInnerDegreeZeroSectionRaw_comp_augmentation
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    standardResolutionInnerDegreeZeroSectionRaw T ≫
        (standardResolutionInnerRawAugmentation T).app
          (op (SimplexCategory.mk 0)) ≫
        (Functor.rightUnitor T.U).hom = 𝟙 T.U := by
  have haug := congrArg (fun k => Functor.whiskerLeft T.U k)
    (standardResolution_augmentation_formula T 0)
  rw [Functor.whiskerLeft_comp] at haug
  let p : T.U ⟶ T.U ⋙ standardResolutionDegree T (some 0) :=
    (Functor.leftUnitor T.U).inv ≫
      Functor.whiskerRight T.adjunction.unit T.U ≫
      (Functor.associator T.U T.V T.U).hom ≫
      Functor.whiskerLeft T.U
        (Functor.rightUnitor (standardResolutionBase T)).inv ≫
      Functor.whiskerLeft T.U
        (eqToHom (show standardResolutionBase T ⋙ 𝟭 A =
          standardResolutionDegree T (some 0) from rfl))
  have hsection : standardResolutionInnerDegreeZeroSectionRaw T =
      p ≫ Functor.whiskerLeft T.U
        (eqToHom (standardResolution_object_degree T 0).symm) := by
    unfold standardResolutionInnerDegreeZeroSectionRaw
    dsimp [p]
    simp only [Category.assoc]
  rw [hsection]
  dsimp [standardResolutionInnerRawAugmentation]
  rw [← Category.assoc]
  rw [Category.assoc p
    (Functor.whiskerLeft T.U
      (eqToHom (standardResolution_object_degree T 0).symm))
    (Functor.whiskerLeft T.U
      ((standardResolutionAugmentation T).app (op (SimplexCategory.mk 0)))), haug]
  rw [(standardResolutionAugmentationData T).component_zero]
  dsimp [godementAugmentationComponent, standardResolutionCounit]
  have hdeg :
      eqToHom (show standardResolutionBase T ⋙ 𝟭 A =
        standardResolutionDegree T (some 0) from rfl) =
        𝟙 (standardResolutionBase T ⋙ 𝟭 A) := by
    rfl
  dsimp only [p]
  rw [hdeg]
  dsimp [standardResolutionBase, standardResolutionDegree,
    godementDegree, iteratedEndofunctor]
  simp only [Category.assoc]
  ext X
  simp

private theorem standardResolutionInnerDegreeZeroSection_comp_augmentation
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    standardResolutionInnerDegreeZeroSection T ≫
        (standardResolutionInnerRawAugmentation T).app
          (op (SimplexCategory.mk 0)) ≫
        (Functor.rightUnitor T.U).hom = 𝟙 T.U := by
  change standardResolutionInnerDegreeZeroSectionRaw T ≫
      (standardResolutionInnerRawAugmentation T).app
        (op (SimplexCategory.mk 0)) ≫
      (Functor.rightUnitor T.U).hom = 𝟙 T.U
  exact standardResolutionInnerDegreeZeroSectionRaw_comp_augmentation T

private theorem standardResolutionOuterDegreeZeroSectionRaw_comp_augmentation
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    standardResolutionOuterDegreeZeroSectionRaw T ≫
        (standardResolutionOuterRawAugmentation T).app
          (op (SimplexCategory.mk 0)) ≫
        (Functor.leftUnitor T.V).hom = 𝟙 T.V := by
  have haug := congrArg (fun k => Functor.whiskerRight k T.V)
    (standardResolution_augmentation_formula T 0)
  rw [Functor.whiskerRight_comp] at haug
  let p : T.V ⟶ standardResolutionDegree T (some 0) ⋙ T.V :=
    (Functor.rightUnitor T.V).inv ≫
      Functor.whiskerLeft T.V T.adjunction.unit ≫
      (Functor.associator T.V T.U T.V).inv ≫
      Functor.whiskerRight
        (Functor.rightUnitor (standardResolutionBase T)).inv T.V ≫
      Functor.whiskerRight
        (eqToHom (show standardResolutionBase T ⋙ 𝟭 A =
          standardResolutionDegree T (some 0) from rfl)) T.V
  have hsection : standardResolutionOuterDegreeZeroSectionRaw T =
      p ≫ Functor.whiskerRight
        (eqToHom (standardResolution_object_degree T 0).symm) T.V := by
    unfold standardResolutionOuterDegreeZeroSectionRaw
    dsimp [p]
    simp only [Category.assoc]
  rw [hsection]
  dsimp [standardResolutionOuterRawAugmentation]
  rw [← Category.assoc]
  rw [Category.assoc p
    (Functor.whiskerRight
      (eqToHom (standardResolution_object_degree T 0).symm) T.V)
    (Functor.whiskerRight
      ((standardResolutionAugmentation T).app (op (SimplexCategory.mk 0))) T.V), haug]
  rw [(standardResolutionAugmentationData T).component_zero]
  dsimp [godementAugmentationComponent, standardResolutionCounit]
  have hdeg :
      eqToHom (show standardResolutionBase T ⋙ 𝟭 A =
        standardResolutionDegree T (some 0) from rfl) =
        𝟙 (standardResolutionBase T ⋙ 𝟭 A) := by
    rfl
  dsimp only [p]
  rw [hdeg]
  dsimp [standardResolutionBase, standardResolutionDegree,
    godementDegree, iteratedEndofunctor]
  simp only [Category.assoc]
  ext X
  simp

private theorem standardResolutionOuterDegreeZeroSection_comp_augmentation
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    standardResolutionOuterDegreeZeroSection T ≫
        (standardResolutionOuterRawAugmentation T).app
          (op (SimplexCategory.mk 0)) ≫
        (Functor.leftUnitor T.V).hom = 𝟙 T.V := by
  change standardResolutionOuterDegreeZeroSectionRaw T ≫
      (standardResolutionOuterRawAugmentation T).app
        (op (SimplexCategory.mk 0)) ≫
      (Functor.leftUnitor T.V).hom = 𝟙 T.V
  exact standardResolutionOuterDegreeZeroSectionRaw_comp_augmentation T

theorem standardResolution_outer_inverse_section
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    standardResolutionOuterHomotopyInverse T ≫
      standardResolutionOuterAugmentation T =
      𝟙 ((SimplicialObject.const (A ⥤ S)).obj T.V) := by
  apply SimplicialObject.hom_ext
  intro n
  let q : op (SimplexCategory.mk 0) ⟶ n :=
    (SimplexCategory.const n.unop (SimplexCategory.mk 0) 0).op
  rw [NatTrans.comp_app, standardResolutionOuterHomotopyInverse_app]
  change (standardResolutionOuterDegreeZeroSection T ≫
      (standardResolutionOuterObject T).map q) ≫
    ((standardResolutionOuterRawAugmentation T).app n ≫
      (Functor.leftUnitor T.V).hom) = 𝟙 T.V
  have hn := (standardResolutionOuterRawAugmentation T).naturality q
  have hn' : (standardResolutionOuterObject T).map q ≫
        (standardResolutionOuterRawAugmentation T).app n =
      (standardResolutionOuterRawAugmentation T).app
          (op (SimplexCategory.mk 0)) ≫
        ((SimplicialObject.const (A ⥤ S)).obj (𝟭 A ⋙ T.V)).map q := by
    exact hn
  have hconst :
      ((SimplicialObject.const (A ⥤ S)).obj (𝟭 A ⋙ T.V)).map q =
        𝟙 (𝟭 A ⋙ T.V) := by
    rfl
  rw [hconst] at hn'
  have hn0 : (standardResolutionOuterObject T).map q ≫
        (standardResolutionOuterRawAugmentation T).app n =
      (standardResolutionOuterRawAugmentation T).app
        (op (SimplexCategory.mk 0)) :=
    hn'.trans (Category.comp_id _)
  have hn'' := congrArg (fun k =>
    standardResolutionOuterDegreeZeroSection T ≫ k ≫
      (Functor.leftUnitor T.V).hom) hn0
  rw [Category.assoc ((standardResolutionOuterObject T).map q)
    ((standardResolutionOuterRawAugmentation T).app n)
    (Functor.leftUnitor T.V).hom] at hn''
  calc
    _ = standardResolutionOuterDegreeZeroSection T ≫
        (standardResolutionOuterRawAugmentation T).app
          (op (SimplexCategory.mk 0)) ≫
        (Functor.leftUnitor T.V).hom := by
      rw [Category.assoc (standardResolutionOuterDegreeZeroSection T)
        ((standardResolutionOuterObject T).map q)
        ((standardResolutionOuterRawAugmentation T).app n ≫
          (Functor.leftUnitor T.V).hom)]
      exact hn''
    _ = 𝟙 T.V :=
      standardResolutionOuterDegreeZeroSection_comp_augmentation T

theorem standardResolution_inner_inverse_section
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    standardResolutionInnerHomotopyInverse T ≫
        standardResolutionInnerAugmentation T =
      𝟙 ((SimplicialObject.const (S ⥤ A)).obj T.U) := by
  apply SimplicialObject.hom_ext
  intro n
  let q : op (SimplexCategory.mk 0) ⟶ n :=
    (SimplexCategory.const n.unop (SimplexCategory.mk 0) 0).op
  rw [NatTrans.comp_app, standardResolutionInnerHomotopyInverse_app]
  change (standardResolutionInnerDegreeZeroSection T ≫
      (standardResolutionInnerObject T).map q) ≫
    ((standardResolutionInnerRawAugmentation T).app n ≫
      (Functor.rightUnitor T.U).hom) = 𝟙 T.U
  have hn := (standardResolutionInnerRawAugmentation T).naturality q
  have hn' : (standardResolutionInnerObject T).map q ≫
        (standardResolutionInnerRawAugmentation T).app n =
      (standardResolutionInnerRawAugmentation T).app
          (op (SimplexCategory.mk 0)) ≫
        ((SimplicialObject.const (S ⥤ A)).obj (T.U ⋙ 𝟭 A)).map q := by
    exact hn
  have hconst :
      ((SimplicialObject.const (S ⥤ A)).obj (T.U ⋙ 𝟭 A)).map q =
        𝟙 (T.U ⋙ 𝟭 A) := by
    rfl
  rw [hconst] at hn'
  have hn0 : (standardResolutionInnerObject T).map q ≫
        (standardResolutionInnerRawAugmentation T).app n =
      (standardResolutionInnerRawAugmentation T).app
        (op (SimplexCategory.mk 0)) :=
    hn'.trans (Category.comp_id _)
  have hn'' := congrArg (fun k =>
    standardResolutionInnerDegreeZeroSection T ≫ k ≫
      (Functor.rightUnitor T.U).hom) hn0
  rw [Category.assoc ((standardResolutionInnerObject T).map q)
    ((standardResolutionInnerRawAugmentation T).app n)
    (Functor.rightUnitor T.U).hom] at hn''
  calc
    _ = standardResolutionInnerDegreeZeroSection T ≫
        (standardResolutionInnerRawAugmentation T).app
          (op (SimplexCategory.mk 0)) ≫
        (Functor.rightUnitor T.U).hom := by
      rw [Category.assoc (standardResolutionInnerDegreeZeroSection T)
        ((standardResolutionInnerObject T).map q)
        ((standardResolutionInnerRawAugmentation T).app n ≫
          (Functor.rightUnitor T.U).hom)]
      exact hn''
    _ = 𝟙 T.U :=
      standardResolutionInnerDegreeZeroSection_comp_augmentation T

/-- Both augmented whiskered resolutions are homotopy equivalences. The
proof route is the section from Chapter 33, followed by its two-map homotopy
and the definition of `Unit26.IsHomotopyEquivalence`. -/
private theorem standardResolutionAugmentation_component_eq
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) (n : ℕ) :
    (standardResolutionAugmentationData T).component n =
      godementAugmentationComponent (standardResolutionBase T)
        (standardResolutionCounit T) n := by
  have hcanonical : ∀ n,
      godementFace (standardResolutionBase T) (standardResolutionCounit T)
            (n := n + 1) (0 : Fin (n + 2)) ≫
          godementAugmentationComponent (standardResolutionBase T)
            (standardResolutionCounit T) n =
        godementAugmentationComponent (standardResolutionBase T)
          (standardResolutionCounit T) (n + 1) := by
    intro n
    have hraw :
        Functor.whiskerRight (standardResolutionCounit T)
              (godementDegree (standardResolutionBase T) n) ≫
            godementAugmentationComponent (standardResolutionBase T)
              (standardResolutionCounit T) n =
          Functor.whiskerLeft (standardResolutionBase T)
              (godementAugmentationComponent (standardResolutionBase T)
                (standardResolutionCounit T) n) ≫
            Functor.whiskerRight (standardResolutionCounit T) (𝟭 A) ≫
            (Functor.leftUnitor (𝟭 A)).hom := by
      ext X
      simp only [NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.leftUnitor_hom_app]
      change (godementDegree (standardResolutionBase T) n).map
            ((standardResolutionCounit T).app X) ≫
          (godementAugmentationComponent (standardResolutionBase T)
            (standardResolutionCounit T) n).app X =
        (godementAugmentationComponent (standardResolutionBase T)
            (standardResolutionCounit T) n).app
              ((standardResolutionBase T).obj X) ≫
          (𝟭 A).map ((standardResolutionCounit T).app X) ≫
          𝟙 ((𝟭 A).obj X)
      simpa only [Functor.id_obj, Functor.id_map, Category.comp_id] using
        (godementAugmentationComponent (standardResolutionBase T)
          (standardResolutionCounit T) n).naturality
            ((standardResolutionCounit T).app X)
    have hface_aug :
        godementFace (standardResolutionBase T) (standardResolutionCounit T)
              (n := n + 1) (0 : Fin (n + 2)) ≫
            godementAugmentationComponent (standardResolutionBase T)
              (standardResolutionCounit T) n =
          Functor.whiskerRight (standardResolutionCounit T)
              (godementDegree (standardResolutionBase T) n) ≫
            godementAugmentationComponent (standardResolutionBase T)
              (standardResolutionCounit T) n := by
      let hp := godementFace_domain_decomposition
        (standardResolutionBase T) (n + 1) (0 : Fin (n + 2))
      let hq := godementFace_codomain_decomposition
        (standardResolutionBase T) (n + 1) (0 : Fin (n + 2))
      let raw := Functor.whiskerLeft
        (iteratedEndofunctor (standardResolutionBase T) 0)
        (Functor.whiskerRight (standardResolutionCounit T)
          (iteratedEndofunctor (standardResolutionBase T) (n + 1 - 0)))
      have hconj : Functor.whiskerRight (standardResolutionCounit T)
            (godementDegree (standardResolutionBase T) n) =
          eqToHom hp ≫ raw ≫ eqToHom hq.symm := by
        apply (CategoryTheory.conj_eqToHom_iff_heq _ _ hp hq).2
        dsimp [raw, godementDegree, iteratedEndofunctor]
        rfl
      have hface : godementFace (standardResolutionBase T)
            (standardResolutionCounit T) (n := n + 1) (0 : Fin (n + 2)) =
          eqToHom hp ≫ raw ≫ eqToHom hq.symm := by
        dsimp [godementFace, hp, hq, raw]
        congr 1
      rw [hface, ← hconj]
      rfl
    exact hface_aug.trans hraw
  induction n with
  | zero => exact (standardResolutionAugmentationData T).component_zero
  | succ n ih =>
      rw [← (standardResolutionAugmentationData T).face_naturality
        (0 : Fin (n + 2)), ih, hcanonical n]

noncomputable def standardResolutionOuterCompositeDegreeRaw
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) (n : ℕ) :
    standardResolutionDegree T (some n) ⋙ T.V ⟶
      standardResolutionDegree T (some n) ⋙ T.V :=
  Functor.whiskerRight
      (eqToHom (standardResolution_object_degree T n).symm) T.V ≫
    (standardResolutionOuterAugmentation T ≫
      standardResolutionOuterHomotopyInverse T).app
        (op (SimplexCategory.mk n)) ≫
    Functor.whiskerRight
      (eqToHom (standardResolution_object_degree T n)) T.V

noncomputable def standardResolutionOuterCompositeDegree
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) (n : ℕ) :
    godementDegree (standardResolutionBase T) n ⋙ T.V ⟶
      godementDegree (standardResolutionBase T) n ⋙ T.V :=
  standardResolutionOuterCompositeDegreeRaw T n

private theorem standardResolutionOuterCompositeMorphism
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    GodementOuterMorphism (standardResolutionBase T)
      (standardResolutionCounit T) (standardResolutionComultiplication T)
      T.V T.V (𝟙 T.V) (standardResolutionOuterCompositeDegree T) := by
  let k := standardResolutionOuterAugmentation T ≫
    standardResolutionOuterHomotopyInverse T
  let kApp (m : ℕ) :
      (standardResolutionObject T).obj (op (SimplexCategory.mk m)) ⋙ T.V ⟶
        (standardResolutionObject T).obj (op (SimplexCategory.mk m)) ⋙ T.V :=
    k.app (op (SimplexCategory.mk m))
  constructor
  · intro n j
    change standardResolutionOuterCompositeDegreeRaw T (n + 1) ≫
        Functor.whiskerRight (standardResolutionFace T n j) T.V =
      Functor.whiskerRight (standardResolutionFace T n j) T.V ≫
        standardResolutionOuterCompositeDegreeRaw T n
    have hdegree (m : ℕ) : standardResolutionOuterCompositeDegreeRaw T m =
        Functor.whiskerRight
            (eqToHom (standardResolution_object_degree T m).symm) T.V ≫
          kApp m ≫
          Functor.whiskerRight
            (eqToHom (standardResolution_object_degree T m)) T.V := by
      rfl
    rw [hdegree, hdegree]
    let faceApp :
        (standardResolutionObject T).obj (op (SimplexCategory.mk (n + 1))) ⋙ T.V ⟶
          (standardResolutionObject T).obj (op (SimplexCategory.mk n)) ⋙ T.V :=
      (standardResolutionOuterObject T).δ j
    have hk0 := (k.naturality (SimplexCategory.δ j).op).symm
    change kApp (n + 1) ≫ faceApp = faceApp ≫ kApp n at hk0
    have hk := hk0
    have hface := congrArg (fun z => Functor.whiskerRight z T.V)
      (standardResolution_face_formula T n j)
    rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp] at hface
    change Functor.whiskerRight
          (eqToHom (standardResolution_object_degree T (n + 1)).symm) T.V ≫
        faceApp ≫
        Functor.whiskerRight
          (eqToHom (standardResolution_object_degree T n)) T.V =
      Functor.whiskerRight
        (standardResolutionFace T n j) T.V at hface
    rw [← hface]
    have hcancel (m : ℕ) :
        Functor.whiskerRight
            (eqToHom (standardResolution_object_degree T m)) T.V ≫
          Functor.whiskerRight
            (eqToHom (standardResolution_object_degree T m).symm) T.V =
          𝟙 ((standardResolutionObject T).obj
            (op (SimplexCategory.mk m)) ⋙ T.V) := by
      rw [← Functor.whiskerRight_comp]
      simp
    have hcancel_assoc (m : ℕ) (Z : A ⥤ S)
        (f : (standardResolutionObject T).obj
            (op (SimplexCategory.mk m)) ⋙ T.V ⟶ Z) :
        Functor.whiskerRight
              (eqToHom (standardResolution_object_degree T m)) T.V ≫
            (Functor.whiskerRight
              (eqToHom (standardResolution_object_degree T m).symm) T.V ≫ f) =
          f := by
      rw [← Category.assoc, hcancel, Category.id_comp]
    simp only [Category.assoc, hcancel_assoc]
    simpa only [Category.assoc] using congrArg (fun z =>
      Functor.whiskerRight
          (eqToHom (standardResolution_object_degree T (n + 1)).symm) T.V ≫
        z ≫
        Functor.whiskerRight
          (eqToHom (standardResolution_object_degree T n)) T.V) hk
  · intro n j
    change standardResolutionOuterCompositeDegreeRaw T n ≫
        Functor.whiskerRight (standardResolutionDegeneracy T n j) T.V =
      Functor.whiskerRight (standardResolutionDegeneracy T n j) T.V ≫
        standardResolutionOuterCompositeDegreeRaw T (n + 1)
    have hdegree (m : ℕ) : standardResolutionOuterCompositeDegreeRaw T m =
        Functor.whiskerRight
            (eqToHom (standardResolution_object_degree T m).symm) T.V ≫
          kApp m ≫
          Functor.whiskerRight
            (eqToHom (standardResolution_object_degree T m)) T.V := by
      rfl
    rw [hdegree, hdegree]
    let degeneracyApp :
        (standardResolutionObject T).obj (op (SimplexCategory.mk n)) ⋙ T.V ⟶
          (standardResolutionObject T).obj (op (SimplexCategory.mk (n + 1))) ⋙ T.V :=
      (standardResolutionOuterObject T).σ j
    have hk0 := (k.naturality (SimplexCategory.σ j).op).symm
    change kApp n ≫ degeneracyApp = degeneracyApp ≫ kApp (n + 1) at hk0
    have hk := hk0
    have hdeg := congrArg (fun z => Functor.whiskerRight z T.V)
      (standardResolution_degeneracy_formula T n j)
    rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp] at hdeg
    change Functor.whiskerRight
          (eqToHom (standardResolution_object_degree T n).symm) T.V ≫
        degeneracyApp ≫
        Functor.whiskerRight
          (eqToHom (standardResolution_object_degree T (n + 1))) T.V =
      Functor.whiskerRight
        (standardResolutionDegeneracy T n j) T.V at hdeg
    rw [← hdeg]
    have hcancel (m : ℕ) :
        Functor.whiskerRight
            (eqToHom (standardResolution_object_degree T m)) T.V ≫
          Functor.whiskerRight
            (eqToHom (standardResolution_object_degree T m).symm) T.V =
          𝟙 ((standardResolutionObject T).obj
            (op (SimplexCategory.mk m)) ⋙ T.V) := by
      rw [← Functor.whiskerRight_comp]
      simp
    have hcancel_assoc (m : ℕ) (Z : A ⥤ S)
        (f : (standardResolutionObject T).obj
            (op (SimplexCategory.mk m)) ⋙ T.V ⟶ Z) :
        Functor.whiskerRight
              (eqToHom (standardResolution_object_degree T m)) T.V ≫
            (Functor.whiskerRight
              (eqToHom (standardResolution_object_degree T m).symm) T.V ≫ f) =
          f := by
      rw [← Category.assoc, hcancel, Category.id_comp]
    simp only [Category.assoc, hcancel_assoc]
    simpa only [Category.assoc] using congrArg (fun z =>
      Functor.whiskerRight
          (eqToHom (standardResolution_object_degree T n).symm) T.V ≫
        z ≫
        Functor.whiskerRight
          (eqToHom (standardResolution_object_degree T (n + 1))) T.V) hk
  · intro n
    change standardResolutionOuterCompositeDegreeRaw T n ≫
        godementOuterAugmentationComponent (standardResolutionBase T)
          (standardResolutionCounit T) T.V n =
      godementOuterAugmentationComponent (standardResolutionBase T)
          (standardResolutionCounit T) T.V n ≫ 𝟙 T.V
    rw [Category.comp_id]
    have hdegree : standardResolutionOuterCompositeDegreeRaw T n =
        Functor.whiskerRight
            (eqToHom (standardResolution_object_degree T n).symm) T.V ≫
          kApp n ≫
          Functor.whiskerRight
            (eqToHom (standardResolution_object_degree T n)) T.V := by
      rfl
    rw [hdegree]
    let augmentationApp :
        (standardResolutionObject T).obj (op (SimplexCategory.mk n)) ⋙ T.V ⟶
          T.V :=
      (standardResolutionOuterRawAugmentation T).app
          (op (SimplexCategory.mk n)) ≫
        (Functor.leftUnitor T.V).hom
    have hkaug : k ≫ standardResolutionOuterAugmentation T =
        standardResolutionOuterAugmentation T := by
      dsimp only [k]
      rw [Category.assoc, standardResolution_outer_inverse_section,
        Category.comp_id]
    have hkaugApp := congrArg
      (fun z => z.app (op (SimplexCategory.mk n))) hkaug
    change kApp n ≫ augmentationApp = augmentationApp at hkaugApp
    have haug0 := congrArg (fun z => Functor.whiskerRight z T.V)
      (standardResolution_augmentation_formula T n)
    rw [Functor.whiskerRight_comp] at haug0
    have haug := congrArg (fun z => z ≫ (Functor.leftUnitor T.V).hom) haug0
    rw [standardResolutionAugmentation_component_eq T n] at haug
    have haug' : Functor.whiskerRight
            (eqToHom (standardResolution_object_degree T n).symm) T.V ≫
          augmentationApp =
        godementOuterAugmentationComponent (standardResolutionBase T)
          (standardResolutionCounit T) T.V n := by
      dsimp only [augmentationApp, standardResolutionOuterRawAugmentation,
        godementOuterAugmentationComponent]
      rw [← Category.assoc]
      exact haug
    rw [← haug']
    have hcancel :
        Functor.whiskerRight
            (eqToHom (standardResolution_object_degree T n)) T.V ≫
          Functor.whiskerRight
            (eqToHom (standardResolution_object_degree T n).symm) T.V =
          𝟙 ((standardResolutionObject T).obj
            (op (SimplexCategory.mk n)) ⋙ T.V) := by
      rw [← Functor.whiskerRight_comp]
      simp
    simp only [Category.assoc]
    rw [← Category.assoc
      (Functor.whiskerRight
        (eqToHom (standardResolution_object_degree T n)) T.V)
      (Functor.whiskerRight
        (eqToHom (standardResolution_object_degree T n).symm) T.V)
      augmentationApp, hcancel, Category.id_comp, hkaugApp]

noncomputable def standardResolutionInnerCompositeDegreeRaw
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) (n : ℕ) :
    T.U ⋙ standardResolutionDegree T (some n) ⟶
      T.U ⋙ standardResolutionDegree T (some n) :=
  Functor.whiskerLeft T.U
      (eqToHom (standardResolution_object_degree T n).symm) ≫
    (standardResolutionInnerAugmentation T ≫
      standardResolutionInnerHomotopyInverse T).app
        (op (SimplexCategory.mk n)) ≫
    Functor.whiskerLeft T.U
      (eqToHom (standardResolution_object_degree T n))

noncomputable def standardResolutionInnerCompositeDegree
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) (n : ℕ) :
    T.U ⋙ godementDegree (standardResolutionBase T) n ⟶
      T.U ⋙ godementDegree (standardResolutionBase T) n :=
  standardResolutionInnerCompositeDegreeRaw T n

private theorem standardResolutionInnerCompositeMorphism
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    GodementInnerMorphism T.U T.U (standardResolutionBase T)
      (standardResolutionCounit T) (standardResolutionComultiplication T)
      (𝟙 T.U) (standardResolutionInnerCompositeDegree T) := by
  let k := standardResolutionInnerAugmentation T ≫
    standardResolutionInnerHomotopyInverse T
  let kApp (m : ℕ) :
      T.U ⋙ (standardResolutionObject T).obj (op (SimplexCategory.mk m)) ⟶
        T.U ⋙ (standardResolutionObject T).obj (op (SimplexCategory.mk m)) :=
    k.app (op (SimplexCategory.mk m))
  refine { face := ?_, degeneracy := ?_, augmentation := ?_ }
  · intro n j
    change standardResolutionInnerCompositeDegreeRaw T (n + 1) ≫
        Functor.whiskerLeft T.U (standardResolutionFace T n j) =
      Functor.whiskerLeft T.U (standardResolutionFace T n j) ≫
        standardResolutionInnerCompositeDegreeRaw T n
    have hdegree (m : ℕ) : standardResolutionInnerCompositeDegreeRaw T m =
        Functor.whiskerLeft T.U
            (eqToHom (standardResolution_object_degree T m).symm) ≫
          kApp m ≫ Functor.whiskerLeft T.U
            (eqToHom (standardResolution_object_degree T m)) := by rfl
    rw [hdegree, hdegree]
    let faceApp :
        T.U ⋙ (standardResolutionObject T).obj
            (op (SimplexCategory.mk (n + 1))) ⟶
          T.U ⋙ (standardResolutionObject T).obj
            (op (SimplexCategory.mk n)) :=
      (standardResolutionInnerObject T).δ j
    have hk : kApp (n + 1) ≫ faceApp = faceApp ≫ kApp n := by
      exact (k.naturality (SimplexCategory.δ j).op).symm
    have hface := congrArg (fun z => Functor.whiskerLeft T.U z)
      (standardResolution_face_formula T n j)
    rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp] at hface
    change Functor.whiskerLeft T.U
          (eqToHom (standardResolution_object_degree T (n + 1)).symm) ≫
        faceApp ≫ Functor.whiskerLeft T.U
          (eqToHom (standardResolution_object_degree T n)) =
      Functor.whiskerLeft T.U (standardResolutionFace T n j) at hface
    rw [← hface]
    have hcancel_assoc (m : ℕ) (Z : S ⥤ A)
        (f : T.U ⋙ (standardResolutionObject T).obj
            (op (SimplexCategory.mk m)) ⟶ Z) :
        Functor.whiskerLeft T.U
              (eqToHom (standardResolution_object_degree T m)) ≫
            (Functor.whiskerLeft T.U
              (eqToHom (standardResolution_object_degree T m).symm) ≫ f) = f := by
      rw [← Category.assoc, ← Functor.whiskerLeft_comp]
      simp
    simp only [Category.assoc, hcancel_assoc]
    simpa only [Category.assoc] using congrArg (fun z =>
      Functor.whiskerLeft T.U
          (eqToHom (standardResolution_object_degree T (n + 1)).symm) ≫
        z ≫ Functor.whiskerLeft T.U
          (eqToHom (standardResolution_object_degree T n))) hk
  · intro n j
    change standardResolutionInnerCompositeDegreeRaw T n ≫
        Functor.whiskerLeft T.U (standardResolutionDegeneracy T n j) =
      Functor.whiskerLeft T.U (standardResolutionDegeneracy T n j) ≫
        standardResolutionInnerCompositeDegreeRaw T (n + 1)
    have hdegree (m : ℕ) : standardResolutionInnerCompositeDegreeRaw T m =
        Functor.whiskerLeft T.U
            (eqToHom (standardResolution_object_degree T m).symm) ≫
          kApp m ≫ Functor.whiskerLeft T.U
            (eqToHom (standardResolution_object_degree T m)) := by rfl
    rw [hdegree, hdegree]
    let degeneracyApp :
        T.U ⋙ (standardResolutionObject T).obj
            (op (SimplexCategory.mk n)) ⟶
          T.U ⋙ (standardResolutionObject T).obj
            (op (SimplexCategory.mk (n + 1))) :=
      (standardResolutionInnerObject T).σ j
    have hk : kApp n ≫ degeneracyApp = degeneracyApp ≫ kApp (n + 1) := by
      exact (k.naturality (SimplexCategory.σ j).op).symm
    have hdeg := congrArg (fun z => Functor.whiskerLeft T.U z)
      (standardResolution_degeneracy_formula T n j)
    rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp] at hdeg
    change Functor.whiskerLeft T.U
          (eqToHom (standardResolution_object_degree T n).symm) ≫
        degeneracyApp ≫ Functor.whiskerLeft T.U
          (eqToHom (standardResolution_object_degree T (n + 1))) =
      Functor.whiskerLeft T.U (standardResolutionDegeneracy T n j) at hdeg
    rw [← hdeg]
    have hcancel_assoc (m : ℕ) (Z : S ⥤ A)
        (f : T.U ⋙ (standardResolutionObject T).obj
            (op (SimplexCategory.mk m)) ⟶ Z) :
        Functor.whiskerLeft T.U
              (eqToHom (standardResolution_object_degree T m)) ≫
            (Functor.whiskerLeft T.U
              (eqToHom (standardResolution_object_degree T m).symm) ≫ f) = f := by
      rw [← Category.assoc, ← Functor.whiskerLeft_comp]
      simp
    simp only [Category.assoc, hcancel_assoc]
    simpa only [Category.assoc] using congrArg (fun z =>
      Functor.whiskerLeft T.U
          (eqToHom (standardResolution_object_degree T n).symm) ≫
        z ≫ Functor.whiskerLeft T.U
          (eqToHom (standardResolution_object_degree T (n + 1)))) hk
  · intro n
    change standardResolutionInnerCompositeDegreeRaw T n ≫
        godementInnerAugmentationComponent T.U (standardResolutionBase T)
          (standardResolutionCounit T) n =
      godementInnerAugmentationComponent T.U (standardResolutionBase T)
          (standardResolutionCounit T) n ≫ 𝟙 T.U
    rw [Category.comp_id]
    have hdegree : standardResolutionInnerCompositeDegreeRaw T n =
        Functor.whiskerLeft T.U
            (eqToHom (standardResolution_object_degree T n).symm) ≫
          kApp n ≫ Functor.whiskerLeft T.U
            (eqToHom (standardResolution_object_degree T n)) := by rfl
    rw [hdegree]
    let augmentationApp :
        T.U ⋙ (standardResolutionObject T).obj
            (op (SimplexCategory.mk n)) ⟶ T.U :=
      (standardResolutionInnerRawAugmentation T).app
          (op (SimplexCategory.mk n)) ≫ (Functor.rightUnitor T.U).hom
    have hkaug : k ≫ standardResolutionInnerAugmentation T =
        standardResolutionInnerAugmentation T := by
      dsimp only [k]
      rw [Category.assoc, standardResolution_inner_inverse_section,
        Category.comp_id]
    have hkaugApp := congrArg
      (fun z => z.app (op (SimplexCategory.mk n))) hkaug
    change kApp n ≫ augmentationApp = augmentationApp at hkaugApp
    have haug0 := congrArg (fun z => Functor.whiskerLeft T.U z)
      (standardResolution_augmentation_formula T n)
    rw [Functor.whiskerLeft_comp] at haug0
    have haug := congrArg (fun z => z ≫ (Functor.rightUnitor T.U).hom) haug0
    rw [standardResolutionAugmentation_component_eq T n] at haug
    have haug' : Functor.whiskerLeft T.U
            (eqToHom (standardResolution_object_degree T n).symm) ≫
          augmentationApp =
        godementInnerAugmentationComponent T.U (standardResolutionBase T)
          (standardResolutionCounit T) n := by
      dsimp only [augmentationApp, standardResolutionInnerRawAugmentation,
        godementInnerAugmentationComponent]
      rw [← Category.assoc]
      exact haug
    rw [← haug']
    have hcancel : Functor.whiskerLeft T.U
            (eqToHom (standardResolution_object_degree T n)) ≫
          Functor.whiskerLeft T.U
            (eqToHom (standardResolution_object_degree T n).symm) =
          𝟙 (T.U ⋙ (standardResolutionObject T).obj
            (op (SimplexCategory.mk n))) := by
      rw [← Functor.whiskerLeft_comp]
      simp
    simp only [Category.assoc]
    rw [← Category.assoc
      (Functor.whiskerLeft T.U
        (eqToHom (standardResolution_object_degree T n)))
      (Functor.whiskerLeft T.U
        (eqToHom (standardResolution_object_degree T n).symm))
      augmentationApp, hcancel, Category.id_comp, hkaugApp]

private theorem standardResolutionInnerIdentityMorphism
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    GodementInnerMorphism (𝟭 A) (𝟭 A)
      (standardResolutionBase T) (standardResolutionCounit T)
      (standardResolutionComultiplication T) (𝟙 (𝟭 A))
      (fun n => 𝟙 ((𝟭 A) ⋙ godementDegree
        (standardResolutionBase T) n)) := by
  refine { face := ?_, degeneracy := ?_, augmentation := ?_ }
  · intro n j
    change 𝟙 ((𝟭 A) ⋙ godementDegree
          (standardResolutionBase T) (n + 1)) ≫
        Functor.whiskerLeft (𝟭 A)
          (godementFace (standardResolutionBase T)
            (standardResolutionCounit T) (n := n + 1) j) =
      Functor.whiskerLeft (𝟭 A)
          (godementFace (standardResolutionBase T)
            (standardResolutionCounit T) (n := n + 1) j) ≫
        𝟙 ((𝟭 A) ⋙ godementDegree
          (standardResolutionBase T) n)
    rw [Category.id_comp]
    apply eq_of_heq
    exact heq_of_eq (Category.comp_id (Functor.whiskerLeft (𝟭 A)
      (godementFace (standardResolutionBase T)
        (standardResolutionCounit T) (n := n + 1) j))).symm
  · intro n j
    change 𝟙 ((𝟭 A) ⋙ godementDegree
          (standardResolutionBase T) n) ≫
        Functor.whiskerLeft (𝟭 A)
          (godementDegeneracy (standardResolutionBase T)
            (standardResolutionComultiplication T) (n := n) j) =
      Functor.whiskerLeft (𝟭 A)
          (godementDegeneracy (standardResolutionBase T)
            (standardResolutionComultiplication T) (n := n) j) ≫
        𝟙 ((𝟭 A) ⋙ godementDegree
          (standardResolutionBase T) (n + 1))
    ext X
    simp only [NatTrans.comp_app, Category.id_comp, Category.comp_id]
  · intro n
    change 𝟙 ((𝟭 A) ⋙ godementDegree
          (standardResolutionBase T) n) ≫
        godementInnerAugmentationComponent (𝟭 A)
          (standardResolutionBase T) (standardResolutionCounit T) n =
      godementInnerAugmentationComponent (𝟭 A)
          (standardResolutionBase T) (standardResolutionCounit T) n ≫
        𝟙 (𝟭 A)
    ext X
    simp only [NatTrans.comp_app, Category.id_comp, Category.comp_id]

private theorem standardResolutionOuterExplicitHomotopy
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    Nonempty (GodementWhiskeredHomotopy (𝟭 A) (𝟭 A)
      (standardResolutionBase T) T.V T.V
      (standardResolutionCounit T) (standardResolutionComultiplication T)
      (godementTwoMapLeft (𝟭 A) (𝟭 A)
        (standardResolutionBase T) T.V T.V (𝟙 T.V)
        (fun n => 𝟙 ((𝟭 A) ⋙ godementDegree
          (standardResolutionBase T) n)))
      (godementTwoMapRight (𝟭 A) (𝟭 A)
        (standardResolutionBase T) T.V T.V
        (standardResolutionOuterCompositeDegree T) (𝟙 (𝟭 A)))) := by
  exact godement_two_maps_homotopic (𝟭 A) (𝟭 A)
    (standardResolutionBase T) T.V T.V
    (standardResolutionCounit T) (standardResolutionComultiplication T)
    (standardResolution_godementEquations T) (𝟙 T.V)
    (standardResolutionOuterCompositeDegree T)
    (standardResolutionOuterCompositeMorphism T) (𝟙 (𝟭 A))
    (fun n => 𝟙 ((𝟭 A) ⋙ godementDegree
      (standardResolutionBase T) n))
    (standardResolutionInnerIdentityMorphism T)

private theorem standardResolutionOuterIdentityMorphism
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    GodementOuterMorphism (standardResolutionBase T)
      (standardResolutionCounit T) (standardResolutionComultiplication T)
      (𝟭 A) (𝟭 A) (𝟙 (𝟭 A))
      (fun n => 𝟙 (godementDegree (standardResolutionBase T) n ⋙ (𝟭 A))) := by
  refine { face := ?_, degeneracy := ?_, augmentation := ?_ }
  · intro n j
    change 𝟙 (godementDegree (standardResolutionBase T) (n + 1) ⋙ (𝟭 A)) ≫
        Functor.whiskerRight (godementFace (standardResolutionBase T)
          (standardResolutionCounit T) (n := n + 1) j) (𝟭 A) =
      Functor.whiskerRight (godementFace (standardResolutionBase T)
          (standardResolutionCounit T) (n := n + 1) j) (𝟭 A) ≫
        𝟙 (godementDegree (standardResolutionBase T) n ⋙ (𝟭 A))
    rw [Category.id_comp]
    apply eq_of_heq
    exact heq_of_eq (Category.comp_id _).symm
  · intro n j
    ext X
    simp only [Category.id_comp, Category.comp_id]
  · intro n
    ext X
    simp only [Category.id_comp, Category.comp_id]

private theorem standardResolutionInnerExplicitHomotopy
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    Nonempty (GodementWhiskeredHomotopy T.U T.U
      (standardResolutionBase T) (𝟭 A) (𝟭 A)
      (standardResolutionCounit T) (standardResolutionComultiplication T)
      (godementTwoMapLeft T.U T.U (standardResolutionBase T)
        (𝟭 A) (𝟭 A) (𝟙 (𝟭 A))
        (standardResolutionInnerCompositeDegree T))
      (godementTwoMapRight T.U T.U (standardResolutionBase T)
        (𝟭 A) (𝟭 A)
        (fun n => 𝟙 (godementDegree (standardResolutionBase T) n ⋙ (𝟭 A)))
        (𝟙 T.U))) := by
  exact godement_two_maps_homotopic T.U T.U
    (standardResolutionBase T) (𝟭 A) (𝟭 A)
    (standardResolutionCounit T) (standardResolutionComultiplication T)
    (standardResolution_godementEquations T) (𝟙 (𝟭 A))
    (fun n => 𝟙 (godementDegree (standardResolutionBase T) n ⋙ (𝟭 A)))
    (standardResolutionOuterIdentityMorphism T) (𝟙 T.U)
    (standardResolutionInnerCompositeDegree T)
    (standardResolutionInnerCompositeMorphism T)

private theorem standardResolutionOuterCompositeHomotopicIdentity
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    Unit26.Homotopic
      (standardResolutionOuterAugmentation T ≫
        standardResolutionOuterHomotopyInverse T)
      (𝟙 (standardResolutionOuterObject T)) := by
  rcases standardResolutionOuterExplicitHomotopy T with ⟨H⟩
  let k := standardResolutionOuterAugmentation T ≫
    standardResolutionOuterHomotopyInverse T
  let objectDegree (n : ℕ) :
      (standardResolutionObject T).obj (op (SimplexCategory.mk n)) =
        godementDegree (standardResolutionBase T) n :=
    standardResolution_object_degree T n
  let fromDegreeRaw (n : ℕ) :
      (standardResolutionObject T).obj (op (SimplexCategory.mk n)) ⋙ T.V ⟶
        ((𝟭 A) ⋙ godementDegree (standardResolutionBase T) n) ⋙ T.V :=
    Functor.whiskerRight
        (eqToHom (objectDegree n)) T.V ≫
      Functor.whiskerRight
        (Functor.leftUnitor
          (godementDegree (standardResolutionBase T) n)).inv T.V
  let fromDegree (n : ℕ) :
      (standardResolutionOuterObject T).obj (op (SimplexCategory.mk n)) ⟶
        godementWhiskeredDegree (𝟭 A) (standardResolutionBase T) T.V n :=
    fromDegreeRaw n
  let toDegreeRaw (n : ℕ) :
      ((𝟭 A) ⋙ godementDegree (standardResolutionBase T) n) ⋙ T.V ⟶
        (standardResolutionObject T).obj (op (SimplexCategory.mk n)) ⋙ T.V :=
    Functor.whiskerRight
        (Functor.leftUnitor
          (godementDegree (standardResolutionBase T) n)).hom T.V ≫
      Functor.whiskerRight
        (eqToHom (objectDegree n).symm) T.V
  let toDegree (n : ℕ) :
      godementWhiskeredDegree (𝟭 A) (standardResolutionBase T) T.V n ⟶
        (standardResolutionOuterObject T).obj (op (SimplexCategory.mk n)) :=
    toDegreeRaw n
  have from_to (n : ℕ) : fromDegree n ≫ toDegree n = 𝟙 _ := by
    change fromDegreeRaw n ≫ toDegreeRaw n = 𝟙 _
    dsimp [fromDegreeRaw, toDegreeRaw]
    simp only [Category.assoc]
    rw [← Category.assoc (Functor.whiskerRight
      (Functor.leftUnitor (godementDegree (standardResolutionBase T) n)).inv T.V)]
    rw [← Functor.whiskerRight_comp, Iso.inv_hom_id]
    have hwid : Functor.whiskerRight
          (𝟙 (godementDegree (standardResolutionBase T) n)) T.V =
        𝟙 (godementDegree (standardResolutionBase T) n ⋙ T.V) := by
      ext X
      simp
    rw [hwid, Category.id_comp]
    rw [← Functor.whiskerRight_comp]
    simp
  have to_from (n : ℕ) : toDegree n ≫ fromDegree n = 𝟙 _ := by
    change toDegreeRaw n ≫ fromDegreeRaw n = 𝟙 _
    dsimp [fromDegreeRaw, toDegreeRaw]
    have hcast_assoc (Z : A ⥤ S)
        (f : godementDegree (standardResolutionBase T) n ⋙ T.V ⟶ Z) :
        Functor.whiskerRight (eqToHom (objectDegree n).symm) T.V ≫
            (Functor.whiskerRight (eqToHom (objectDegree n)) T.V ≫ f) = f := by
      rw [← Category.assoc, ← Functor.whiskerRight_comp]
      simp
    simp only [Category.assoc, hcast_assoc]
    rw [← Functor.whiskerRight_comp, Iso.hom_inv_id]
    have hwid : Functor.whiskerRight
          (𝟙 ((𝟭 A) ⋙ godementDegree (standardResolutionBase T) n)) T.V =
        𝟙 (((𝟭 A) ⋙ godementDegree (standardResolutionBase T) n) ⋙ T.V) := by
      ext X
      simp
    exact hwid
  have from_face (n : ℕ) (j : Fin (n + 2)) :
      (standardResolutionOuterObject T).δ j ≫ fromDegree n =
        fromDegree (n + 1) ≫
          godementWhiskeredSimplicialFace (𝟭 A)
            (standardResolutionBase T) T.V
            (standardResolutionCounit T) n j := by
    dsimp only [fromDegree, fromDegreeRaw]
    have hface0 := congrArg (fun z => Functor.whiskerRight z T.V)
      (standardResolution_face_formula T n j)
    rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp] at hface0
    let outerFace :
        (standardResolutionObject T).obj (op (SimplexCategory.mk (n + 1))) ⋙ T.V ⟶
          (standardResolutionObject T).obj (op (SimplexCategory.mk n)) ⋙ T.V :=
      Functor.whiskerRight ((standardResolutionObject T).δ j) T.V
    let e (m : ℕ) := Functor.whiskerRight
      (eqToHom (objectDegree m)) T.V
    let eInv (m : ℕ) := Functor.whiskerRight
      (eqToHom (objectDegree m).symm) T.V
    have hface : eInv (n + 1) ≫ outerFace ≫ e n =
        Functor.whiskerRight
          (godementFace (standardResolutionBase T)
            (standardResolutionCounit T) (n := n + 1) j) T.V := by
      apply eq_of_heq
      exact heq_of_eq hface0
    have hcast : outerFace ≫ e n =
        e (n + 1) ≫ Functor.whiskerRight
          (godementFace (standardResolutionBase T)
            (standardResolutionCounit T) (n := n + 1) j) T.V := by
      have hc : e (n + 1) ≫ eInv (n + 1) = 𝟙 _ := by
        dsimp [e, eInv]
        rw [← Functor.whiskerRight_comp]
        simp
      have hx := congrArg (fun z => e (n + 1) ≫ z) hface
      rw [← Category.assoc, hc, Category.id_comp] at hx
      exact hx
    change outerFace ≫ e n ≫
        Functor.whiskerRight
          (Functor.leftUnitor
            (godementDegree (standardResolutionBase T) n)).inv T.V =
      (e (n + 1) ≫ Functor.whiskerRight
        (Functor.leftUnitor
          (godementDegree (standardResolutionBase T) (n + 1))).inv T.V) ≫
        godementWhiskeredSimplicialFace (𝟭 A)
          (standardResolutionBase T) T.V
          (standardResolutionCounit T) n j
    ext X
    have hcastX := congrArg (fun z => z.app X) hcast
    simp only [NatTrans.comp_app] at hcastX
    change outerFace.app X ≫ (e n).app X ≫
        (Functor.whiskerRight
          (Functor.leftUnitor
            (godementDegree (standardResolutionBase T) n)).inv T.V).app X =
      ((e (n + 1)).app X ≫ (Functor.whiskerRight
        (Functor.leftUnitor
          (godementDegree (standardResolutionBase T) (n + 1))).inv T.V).app X) ≫
        (godementWhiskeredSimplicialFace (𝟭 A)
          (standardResolutionBase T) T.V
          (standardResolutionCounit T) n j).app X
    rw [← Category.assoc, hcastX]
    simp [godementWhiskeredSimplicialFace, godementWhiskeredFace,
      Functor.whiskerLeft, Functor.whiskerRight]
    exact Category.comp_id _
  have to_face (n : ℕ) (j : Fin (n + 2)) :
      toDegree (n + 1) ≫ (standardResolutionOuterObject T).δ j =
        godementWhiskeredSimplicialFace (𝟭 A)
            (standardResolutionBase T) T.V
            (standardResolutionCounit T) n j ≫ toDegree n := by
    have hx := congrArg (fun z => toDegree (n + 1) ≫ z ≫ toDegree n)
      (from_face n j)
    simp only [Category.assoc, from_to, Category.comp_id] at hx
    rw [← Category.assoc (toDegree (n + 1)) (fromDegree (n + 1)),
      to_from, Category.id_comp] at hx
    exact hx
  have from_degeneracy (n : ℕ) (j : Fin (n + 1)) :
      (standardResolutionOuterObject T).σ j ≫ fromDegree (n + 1) =
        fromDegree n ≫
          godementWhiskeredSimplicialDegeneracy (𝟭 A)
            (standardResolutionBase T) T.V
            (standardResolutionComultiplication T) n j := by
    dsimp only [fromDegree, fromDegreeRaw]
    have hdeg0 := congrArg (fun z => Functor.whiskerRight z T.V)
      (standardResolution_degeneracy_formula T n j)
    rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp] at hdeg0
    let outerDeg :
        (standardResolutionObject T).obj (op (SimplexCategory.mk n)) ⋙ T.V ⟶
          (standardResolutionObject T).obj (op (SimplexCategory.mk (n + 1))) ⋙ T.V :=
      Functor.whiskerRight ((standardResolutionObject T).σ j) T.V
    let e (m : ℕ) := Functor.whiskerRight
      (eqToHom (objectDegree m)) T.V
    let eInv (m : ℕ) := Functor.whiskerRight
      (eqToHom (objectDegree m).symm) T.V
    have hdeg : eInv n ≫ outerDeg ≫ e (n + 1) =
        Functor.whiskerRight
          (godementDegeneracy (standardResolutionBase T)
            (standardResolutionComultiplication T) (n := n) j) T.V := by
      apply eq_of_heq
      exact heq_of_eq hdeg0
    have hcast : outerDeg ≫ e (n + 1) =
        e n ≫ Functor.whiskerRight
          (godementDegeneracy (standardResolutionBase T)
            (standardResolutionComultiplication T) (n := n) j) T.V := by
      have hc : e n ≫ eInv n = 𝟙 _ := by
        dsimp [e, eInv]
        rw [← Functor.whiskerRight_comp]
        simp
      have hx := congrArg (fun z => e n ≫ z) hdeg
      rw [← Category.assoc, hc, Category.id_comp] at hx
      exact hx
    change outerDeg ≫ e (n + 1) ≫
        Functor.whiskerRight
          (Functor.leftUnitor
            (godementDegree (standardResolutionBase T) (n + 1))).inv T.V =
      (e n ≫ Functor.whiskerRight
        (Functor.leftUnitor
          (godementDegree (standardResolutionBase T) n)).inv T.V) ≫
        godementWhiskeredSimplicialDegeneracy (𝟭 A)
          (standardResolutionBase T) T.V
          (standardResolutionComultiplication T) n j
    ext X
    have hcastX := congrArg (fun z => z.app X) hcast
    simp only [NatTrans.comp_app] at hcastX
    change outerDeg.app X ≫ (e (n + 1)).app X ≫
        (Functor.whiskerRight
          (Functor.leftUnitor
            (godementDegree (standardResolutionBase T) (n + 1))).inv T.V).app X =
      ((e n).app X ≫ (Functor.whiskerRight
        (Functor.leftUnitor
          (godementDegree (standardResolutionBase T) n)).inv T.V).app X) ≫
        (godementWhiskeredSimplicialDegeneracy (𝟭 A)
          (standardResolutionBase T) T.V
          (standardResolutionComultiplication T) n j).app X
    rw [← Category.assoc, hcastX]
    simp [godementWhiskeredSimplicialDegeneracy,
      godementWhiskeredDegeneracy, Functor.whiskerLeft, Functor.whiskerRight]
    rfl
  have to_degeneracy (n : ℕ) (j : Fin (n + 1)) :
      toDegree n ≫ (standardResolutionOuterObject T).σ j =
        godementWhiskeredSimplicialDegeneracy (𝟭 A)
            (standardResolutionBase T) T.V
            (standardResolutionComultiplication T) n j ≫ toDegree (n + 1) := by
    have hx := congrArg (fun z => toDegree n ≫ z ≫ toDegree (n + 1))
      (from_degeneracy n j)
    simp only [Category.assoc, from_to, Category.comp_id] at hx
    rw [← Category.assoc (toDegree n) (fromDegree n),
      to_from, Category.id_comp] at hx
    exact hx
  let K : Unit26.DegreewiseHomotopy k (𝟙 _) := {
    h := fun n i => fromDegree n ≫ H.h n i ≫ toDegree n
    h_zero := by
      intro n
      rw [H.endpoint_zero]
      have hleft : godementTwoMapLeft (𝟭 A) (𝟭 A)
            (standardResolutionBase T) T.V T.V (𝟙 T.V)
            (fun m => 𝟙 ((𝟭 A) ⋙ godementDegree
              (standardResolutionBase T) m)) n =
          𝟙 (godementWhiskeredDegree (𝟭 A)
            (standardResolutionBase T) T.V n) := by
        dsimp [godementTwoMapLeft]
        dsimp [godementWhiskeredDegree]
        ext X
        simp [Functor.whiskerRight]
      rw [hleft, Category.id_comp]
      change fromDegreeRaw n ≫ toDegreeRaw n =
        𝟙 ((standardResolutionObject T).obj
          (op (SimplexCategory.mk n)) ⋙ T.V)
      dsimp [fromDegreeRaw, toDegreeRaw]
      have hunit_assoc (Z : A ⥤ S)
          (f : godementDegree (standardResolutionBase T) n ⋙ T.V ⟶ Z) :
          Functor.whiskerRight
                (Functor.leftUnitor
                  (godementDegree (standardResolutionBase T) n)).inv T.V ≫
              (Functor.whiskerRight
                  (Functor.leftUnitor
                    (godementDegree (standardResolutionBase T) n)).hom T.V ≫ f) =
            f := by
        rw [← Category.assoc, ← Functor.whiskerRight_comp,
          Iso.inv_hom_id]
        have hwid : Functor.whiskerRight
              (𝟙 (godementDegree (standardResolutionBase T) n)) T.V =
            𝟙 (godementDegree (standardResolutionBase T) n ⋙ T.V) := by
          ext X
          simp
        rw [hwid, Category.id_comp]
      simp only [Category.assoc, hunit_assoc]
      rw [← Functor.whiskerRight_comp]
      simp
    h_last := by
      intro n
      rw [H.endpoint_last]
      have hright : godementTwoMapRight (𝟭 A) (𝟭 A)
            (standardResolutionBase T) T.V T.V
            (standardResolutionOuterCompositeDegree T) (𝟙 (𝟭 A)) n =
          Functor.whiskerLeft (𝟭 A)
            (standardResolutionOuterCompositeDegree T n) := by
        dsimp [godementTwoMapRight]
        have hid : Functor.whiskerRight (𝟙 (𝟭 A))
              (godementDegree (standardResolutionBase T) n ⋙ T.V) =
            𝟙 ((𝟭 A) ⋙ godementDegree
              (standardResolutionBase T) n ⋙ T.V) := by
          ext X
          simp
        rw [hid]
        apply eq_of_heq
        exact heq_of_eq (Category.comp_id _)
      rw [hright]
      change fromDegreeRaw n ≫
          Functor.whiskerLeft (𝟭 A)
            (standardResolutionOuterCompositeDegree T n) ≫
          toDegreeRaw n = k.app (op (SimplexCategory.mk n))
      dsimp only [fromDegreeRaw, toDegreeRaw]
      have hunit (f : godementDegree (standardResolutionBase T) n ⋙ T.V ⟶
          godementDegree (standardResolutionBase T) n ⋙ T.V) :
          Functor.whiskerRight
                (Functor.leftUnitor
                  (godementDegree (standardResolutionBase T) n)).inv T.V ≫
              Functor.whiskerLeft (𝟭 A) f ≫
              Functor.whiskerRight
                (Functor.leftUnitor
                  (godementDegree (standardResolutionBase T) n)).hom T.V = f := by
        ext X
        simp [Functor.whiskerLeft, Functor.whiskerRight]
      slice_lhs 2 4 => rw [hunit]
      let e := Functor.whiskerRight
        (eqToHom (standardResolution_object_degree T n)) T.V
      let eInv := Functor.whiskerRight
        (eqToHom (standardResolution_object_degree T n).symm) T.V
      let kApp :
          (standardResolutionObject T).obj (op (SimplexCategory.mk n)) ⋙ T.V ⟶
            (standardResolutionObject T).obj (op (SimplexCategory.mk n)) ⋙ T.V :=
        k.app (op (SimplexCategory.mk n))
      change e ≫ (eInv ≫ kApp ≫ e) ≫ eInv = kApp
      have he : e ≫ eInv =
          𝟙 ((standardResolutionObject T).obj
            (op (SimplexCategory.mk n)) ⋙ T.V) := by
        dsimp [e, eInv]
        rw [← Functor.whiskerRight_comp]
        simp
      have heInv : eInv ≫ e =
          𝟙 (standardResolutionDegree T (some n) ⋙ T.V) := by
        dsimp [e, eInv]
        rw [← Functor.whiskerRight_comp]
        simp
      simp only [Category.assoc]
      rw [← Category.assoc e eInv, he, Category.id_comp]
      exact Category.comp_id kApp
    face_of_gt := by
      intro n i j hji
      change (fromDegree (n + 1) ≫ H.h (n + 1) i ≫ toDegree (n + 1)) ≫
          (standardResolutionOuterObject T).δ j =
        (standardResolutionOuterObject T).δ j ≫
          (fromDegree n ≫ H.h n (i.pred hji.ne_zero) ≫ toDegree n)
      simp only [Category.assoc]
      rw [to_face]
      rw [← Category.assoc (H.h (n + 1) i), H.face_of_gt i j hji]
      rw [Category.assoc, ← Category.assoc (fromDegree (n + 1)), ← from_face]
      simp only [Category.assoc]
    face_of_le := by
      intro n i j hij
      change (fromDegree (n + 1) ≫ H.h (n + 1) i ≫ toDegree (n + 1)) ≫
          (standardResolutionOuterObject T).δ j =
        (standardResolutionOuterObject T).δ j ≫
          (fromDegree n ≫ H.h n
            (i.castPred (Fin.ne_last_of_lt
              (lt_of_le_of_lt hij j.castSucc_lt_succ))) ≫ toDegree n)
      simp only [Category.assoc]
      rw [to_face]
      rw [← Category.assoc (H.h (n + 1) i), H.face_of_le i j hij]
      rw [Category.assoc, ← Category.assoc (fromDegree (n + 1)), ← from_face]
      simp only [Category.assoc]
    degeneracy_of_gt := by
      intro n i j hji
      change (fromDegree n ≫ H.h n i ≫ toDegree n) ≫
          (standardResolutionOuterObject T).σ j =
        (standardResolutionOuterObject T).σ j ≫
          (fromDegree (n + 1) ≫ H.h (n + 1) i.succ ≫ toDegree (n + 1))
      simp only [Category.assoc]
      rw [to_degeneracy]
      rw [← Category.assoc (H.h n i), H.degeneracy_of_gt i j hji]
      rw [Category.assoc, ← Category.assoc (fromDegree n), ← from_degeneracy]
      simp only [Category.assoc]
    degeneracy_of_le := by
      intro n i j hij
      change (fromDegree n ≫ H.h n i ≫ toDegree n) ≫
          (standardResolutionOuterObject T).σ j =
        (standardResolutionOuterObject T).σ j ≫
          (fromDegree (n + 1) ≫ H.h (n + 1) i.castSucc ≫ toDegree (n + 1))
      simp only [Category.assoc]
      rw [to_degeneracy]
      rw [← Category.assoc (H.h n i), H.degeneracy_of_le i j hij]
      rw [Category.assoc, ← Category.assoc (fromDegree n), ← from_degeneracy]
      simp only [Category.assoc] }
  exact Relation.EqvGen.rel _ _ ⟨Unit26.degreewiseHomotopy_to_homotopy K⟩

theorem standardResolution_homotopy_equivalences
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    Unit26.IsHomotopyEquivalence (standardResolutionOuterAugmentation T) ∧
      Unit26.IsHomotopyEquivalence (standardResolutionInnerAugmentation T) := by
  sorry
/-! ## The module and polynomial-algebra examples -/

/-- The free/forgetful adjunction used in Example 34.4. -/
def moduleStandardResolutionSituation {R : Type u} [Ring R] :
    StandardResolutionSituation (ModuleCat.{u} R) (Type u) :=
  ⟨ModuleCat.free R, CategoryTheory.forget (ModuleCat.{u} R), ModuleCat.adj R⟩

/-- The degree `n` of the module example on a module `M₀`. -/
def moduleResolutionDegree {R : Type u} [Ring R]
    (M₀ : ModuleCat.{u} R) (n : ℕ) : ModuleCat.{u} R :=
  (standardResolutionDegree (moduleStandardResolutionSituation (R := R))
    (some n)).obj M₀

/-- The module example's degree-one face maps (the source's `d₀,d₁`). -/
def moduleResolutionFace {R : Type u} [Ring R]
    (M₀ : ModuleCat.{u} R) (j : Fin 2) :
    moduleResolutionDegree M₀ 1 ⟶ moduleResolutionDegree M₀ 0 :=
  (standardResolutionFace (moduleStandardResolutionSituation (R := R)) 0 j).app M₀

/-- The module example's degree-one degeneracy maps (the source's `s₀,s₁`). -/
def moduleResolutionDegeneracy {R : Type u} [Ring R]
    (M₀ : ModuleCat.{u} R) (j : Fin 2) :
    moduleResolutionDegree M₀ 1 ⟶ moduleResolutionDegree M₀ 2 :=
  (standardResolutionDegeneracy (moduleStandardResolutionSituation (R := R)) 1 j).app M₀

/-- The augmentation component in the module example. -/
def moduleResolutionAugmentation {R : Type u} [Ring R]
    (M₀ : ModuleCat.{u} R) (n : ℕ) : moduleResolutionDegree M₀ n ⟶ M₀ :=
  (standardResolutionAugmentationData
    (moduleStandardResolutionSituation (R := R))).component n |>.app M₀

theorem moduleResolution_augmentation_homotopy_equivalence
    {R : Type u} [Ring R] :
    Unit26.IsHomotopyEquivalence
      (standardResolutionOuterAugmentation
        (moduleStandardResolutionSituation (R := R))) := by
  exact (standardResolution_homotopy_equivalences
    (moduleStandardResolutionSituation (R := R))).1

/-- The free commutative polynomial-algebra functor on a type. -/
def commutativePolynomialFree {A : Type u} [CommRing A] :
    Type u ⥤ CommAlgCat.{u} A where
  obj X := CommAlgCat.of A (MvPolynomial X A)
  map f := CommAlgCat.ofHom (MvPolynomial.rename f)
  map_id X := by
    apply CommAlgCat.hom_ext
    change MvPolynomial.rename (id : X → X) = AlgHom.id A (MvPolynomial X A)
    exact MvPolynomial.rename_id
  map_comp f g := by
    apply CommAlgCat.hom_ext
    change MvPolynomial.rename (ConcreteCategory.hom g ∘ ConcreteCategory.hom f) =
      (MvPolynomial.rename (ConcreteCategory.hom g)).comp
        (MvPolynomial.rename (ConcreteCategory.hom f))
    exact (MvPolynomial.rename_comp_rename (R := A)
      (ConcreteCategory.hom f) (ConcreteCategory.hom g)).symm

/-- The free/forgetful adjunction for commutative `A`-algebras. -/
private noncomputable def commutativePolynomialHomEquiv {A : Type u} [CommRing A]
    (X : Type u) (Y : CommAlgCat.{u} A) :
    ((commutativePolynomialFree (A := A)).obj X ⟶ Y) ≃
      (X ⟶ (CategoryTheory.forget (CommAlgCat.{u} A)).obj Y) :=
  { toFun := fun f => TypeCat.ofHom (fun x => f.hom (MvPolynomial.X x))
    invFun := fun g =>
      CommAlgCat.ofHom (MvPolynomial.aeval (fun x => g x))
    left_inv := by
      intro f
      apply CommAlgCat.hom_ext
      apply MvPolynomial.algHom_ext
      intro x
      change MvPolynomial.aeval (R := A)
          (fun x : X => f.hom (MvPolynomial.X x)) (MvPolynomial.X x) =
        f.hom (MvPolynomial.X x)
      simp
    right_inv := by
      intro g
      apply ConcreteCategory.hom_ext
      intro x
      exact MvPolynomial.aeval_X (f := g) x }

/-- The free/forgetful adjunction for commutative `A`-algebras. -/
noncomputable def commutativePolynomialAdjunction {A : Type u} [CommRing A] :
    commutativePolynomialFree (A := A) ⊣ CategoryTheory.forget (CommAlgCat.{u} A) := by
  exact CategoryTheory.Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => by
        exact commutativePolynomialHomEquiv X Y
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply CommAlgCat.hom_ext
        apply MvPolynomial.algHom_ext
        intro x
        change MvPolynomial.aeval (R := A)
            (fun x : X' => g (f x)) (MvPolynomial.X x) =
          MvPolynomial.aeval (R := A) (fun x : X => g x)
            (MvPolynomial.rename (R := A) f (MvPolynomial.X x))
        simp
      homEquiv_naturality_right := by
        intro X Y Y' f g
        apply ConcreteCategory.hom_ext
        intro x
        rfl }

/-- The free/forgetful adjunction used in Example 34.5. -/
def polynomialAlgebraStandardResolutionSituation {A : Type u} [CommRing A] :
  StandardResolutionSituation (CommAlgCat.{u} A) (Type u) :=
  ⟨commutativePolynomialFree (A := A), CategoryTheory.forget (CommAlgCat.{u} A),
    commutativePolynomialAdjunction (A := A)⟩

/-- The degree `n` of the polynomial-algebra example on an algebra `B`. -/
def polynomialAlgebraResolutionDegree {A : Type u} [CommRing A]
    (B : CommAlgCat.{u} A) (n : ℕ) : CommAlgCat.{u} A :=
  (standardResolutionDegree
    (polynomialAlgebraStandardResolutionSituation (A := A)) (some n)).obj B

/-- The polynomial-algebra example's degree-one face maps. -/
def polynomialAlgebraResolutionFace {A : Type u} [CommRing A]
    (B : CommAlgCat.{u} A) (j : Fin 2) :
    polynomialAlgebraResolutionDegree B 1 ⟶ polynomialAlgebraResolutionDegree B 0 :=
  (standardResolutionFace
    (polynomialAlgebraStandardResolutionSituation (A := A)) 0 j).app B

/-- The polynomial-algebra example's degree-one degeneracy maps. -/
def polynomialAlgebraResolutionDegeneracy {A : Type u} [CommRing A]
    (B : CommAlgCat.{u} A) (j : Fin 2) :
    polynomialAlgebraResolutionDegree B 1 ⟶ polynomialAlgebraResolutionDegree B 2 :=
  (standardResolutionDegeneracy
    (polynomialAlgebraStandardResolutionSituation (A := A)) 1 j).app B

/-- The augmentation component in the polynomial-algebra example. -/
def polynomialAlgebraResolutionAugmentation {A : Type u} [CommRing A]
    (B : CommAlgCat.{u} A) (n : ℕ) :
    polynomialAlgebraResolutionDegree B n ⟶ B :=
  (standardResolutionAugmentationData
    (polynomialAlgebraStandardResolutionSituation (A := A))).component n |>.app B

theorem polynomialAlgebraResolution_augmentation_homotopy_equivalence
    {A : Type u} [CommRing A] :
    Unit26.IsHomotopyEquivalence
      (standardResolutionOuterAugmentation
        (polynomialAlgebraStandardResolutionSituation (A := A))) := by
  exact (standardResolution_homotopy_equivalences
    (polynomialAlgebraStandardResolutionSituation (A := A))).1

end Formalization.Books.Simplicial.Unit34
