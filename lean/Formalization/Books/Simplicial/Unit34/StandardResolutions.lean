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
  sorry

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
  sorry

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
  sorry

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
  sorry

abbrev standardResolutionInnerAugmentation
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :=
  standardResolutionInnerRawAugmentation T ≫
    (SimplicialObject.const (S ⥤ A)).map (Functor.rightUnitor T.U).hom

/-- The degreewise-unit section used as the inverse in the source's two
homotopy-equivalence constructions. -/
noncomputable def standardResolutionOuterHomotopyInverse
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    (SimplicialObject.const (A ⥤ S)).obj T.V ⟶
      standardResolutionOuterObject T := by
  sorry

noncomputable def standardResolutionInnerHomotopyInverse
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    (SimplicialObject.const (S ⥤ A)).obj T.U ⟶
      standardResolutionInnerObject T := by
  sorry

theorem standardResolution_outer_inverse_section
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    standardResolutionOuterHomotopyInverse T ≫
        standardResolutionOuterAugmentation T =
      𝟙 ((SimplicialObject.const (A ⥤ S)).obj T.V) := by
  sorry

theorem standardResolution_inner_inverse_section
    {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
    (T : StandardResolutionSituation A S) :
    standardResolutionInnerHomotopyInverse T ≫
        standardResolutionInnerAugmentation T =
      𝟙 ((SimplicialObject.const (S ⥤ A)).obj T.U) := by
  sorry

/-- Both augmented whiskered resolutions are homotopy equivalences. The
proof route is the section from Chapter 33, followed by its two-map homotopy
and the definition of `Unit26.IsHomotopyEquivalence`. -/
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
noncomputable def commutativePolynomialAdjunction {A : Type u} [CommRing A] :
    commutativePolynomialFree (A := A) ⊣ CategoryTheory.forget (CommAlgCat.{u} A) := by
  sorry

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
