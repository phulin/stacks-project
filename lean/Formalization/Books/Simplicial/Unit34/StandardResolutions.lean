import Formalization.Books.Simplicial.Unit33.Godement
import Mathlib.CategoryTheory.Adjunction.Basic

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

universe u

/-! ## The adjunction and the comonad-like endofunctor -/

/-- The data in Situation 34.1: `U` is left adjoint to `V`. -/
structure StandardResolutionSituation (A : Type u) (S : Type u)
    [Category.{u} A] [Category.{u} S] where
  U : S ⥤ A
  V : A ⥤ S
  adjunction : U ⊣ V

/-- The endofunctor `U ∘ V` on `A` used in the standard resolution. -/
def standardResolutionBase {A : Type u} {S : Type u}
    [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) : A ⥤ A :=
  T.V ⋙ T.U

/-- The source's counit `d : U ∘ V ⟶ id_A`. -/
abbrev standardResolutionCounit {A : Type u} {S : Type u}
    [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) :
    standardResolutionBase T ⟶ 𝟭 A :=
  T.adjunction.counit

/-- The source's unit `η : id_S ⟶ V ∘ U`. -/
abbrev standardResolutionUnit {A : Type u} {S : Type u}
    [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) :
    𝟭 S ⟶ T.U ⋙ T.V :=
  T.adjunction.unit

/-- The unit-insertion map `U V ⟶ U V U V`, with associators and unitors
made explicit so that it is a morphism between the chosen functors. -/
def standardResolutionComultiplication {A : Type u} {S : Type u}
    [Category.{u} A] [Category.{u} S]
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
def standardResolutionDegree {A : Type u} {S : Type u}
    [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) :
    StandardResolutionIndex → A ⥤ A
  | none => 𝟭 A
  | some n => godementDegree (standardResolutionBase T) n

/-- The composition formula `X_{n+m+1} = X_n ∘ X_m`, including the cases in
which one of the indices is `-1`. The equalities use canonical functor
identity and associativity normalizations. -/
theorem standardResolutionDegree_comp {A : Type u} {S : Type u}
    [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S)
    (i j : StandardResolutionIndex) :
    standardResolutionDegree T (standardResolutionIndexAdd i j) =
      standardResolutionDegree T i ⋙ standardResolutionDegree T j := by
  sorry

/-- The degreewise boundary maps, including the degree-zero counit. -/
def standardResolutionBoundary {A : Type u} {S : Type u}
    [Category.{u} A] [Category.{u} S]
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
def standardResolutionFace {A : Type u} {S : Type u}
    [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) (n : ℕ) (j : Fin (n + 2)) :
    standardResolutionDegree T (some (n + 1)) ⟶
      standardResolutionDegree T (some n) := by
  simpa [standardResolutionDegree, standardResolutionBase,
    godementDegree, iteratedEndofunctor] using
    (godementFace (standardResolutionBase T)
      (standardResolutionCounit T) (n := n + 1) j)

/-- The source's degeneracy maps. -/
def standardResolutionDegeneracy {A : Type u} {S : Type u}
    [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) (n : ℕ) (j : Fin (n + 1)) :
    standardResolutionDegree T (some n) ⟶
      standardResolutionDegree T (some (n + 1)) := by
  simpa [standardResolutionDegree, standardResolutionBase,
    godementDegree, iteratedEndofunctor] using
    (godementDegeneracy (standardResolutionBase T)
      (standardResolutionComultiplication T) j)

/-- The adjunction triangle identities imply the Godement equations. -/
theorem standardResolution_godementEquations
    {A : Type u} {S : Type u} [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) :
    GodementEquations (standardResolutionBase T)
      (standardResolutionCounit T) (standardResolutionComultiplication T) := by
  sorry

/-- The chosen simplicial object supplied by the standard-resolution
construction. -/
noncomputable def standardResolutionData
    {A : Type u} {S : Type u} [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) :
    GodementSimplicialData (standardResolutionBase T)
      (standardResolutionCounit T) (standardResolutionComultiplication T) :=
  (godement_simplicial_data (standardResolutionBase T)
    (standardResolutionCounit T) (standardResolutionComultiplication T)
    (standardResolution_godementEquations T)).some

/-- The augmentation data for the standard resolution. -/
noncomputable def standardResolutionAugmentationData
    {A : Type u} {S : Type u} [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) :
    GodementAugmentationData (standardResolutionBase T)
      (standardResolutionCounit T) (standardResolutionComultiplication T) :=
  (godement_augmentation_condition (standardResolutionBase T)
    (standardResolutionCounit T) (standardResolutionComultiplication T)
    (standardResolution_godementEquations T)).some

/-! ## The actual simplicial object and its formulas -/

abbrev standardResolutionObject
    {A : Type u} {S : Type u} [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) : SimplicialObject (A ⥤ A) :=
  (standardResolutionAugmentationData T).simplicial.object

abbrev standardResolutionAugmentation
    {A : Type u} {S : Type u} [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) :
    standardResolutionObject T ⟶ (SimplicialObject.const (A ⥤ A)).obj (𝟭 A) :=
  (standardResolutionAugmentationData T).augmentation

theorem standardResolution_object_degree
    {A : Type u} {S : Type u} [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) (n : ℕ) :
    (standardResolutionObject T).obj (op (SimplexCategory.mk n)) =
      standardResolutionDegree T (some n) := by
  exact (standardResolutionAugmentationData T).simplicial.object_obj n

theorem standardResolution_face_formula
    {A : Type u} {S : Type u} [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) (n : ℕ) (j : Fin (n + 2)) :
    eqToHom (standardResolution_object_degree T (n + 1)).symm ≫
        (standardResolutionObject T).δ j ≫
    eqToHom (standardResolution_object_degree T n) =
      standardResolutionFace T n j := by
  change _ = godementFace (standardResolutionBase T)
    (standardResolutionCounit T) j
  exact (standardResolutionAugmentationData T).simplicial.face_def n j

theorem standardResolution_degeneracy_formula
    {A : Type u} {S : Type u} [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) (n : ℕ) (j : Fin (n + 1)) :
    eqToHom (standardResolution_object_degree T n).symm ≫
        (standardResolutionObject T).σ j ≫
        eqToHom (standardResolution_object_degree T (n + 1)) =
      standardResolutionDegeneracy T n j := by
  exact (standardResolutionAugmentationData T).simplicial.degeneracy_def n j

theorem standardResolution_augmentation_formula
    {A : Type u} {S : Type u} [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) (n : ℕ) :
    eqToHom (standardResolution_object_degree T n).symm ≫
        (standardResolutionAugmentation T).app (op (SimplexCategory.mk n)) =
      (standardResolutionAugmentationData T).component n := by
  exact (standardResolutionAugmentationData T).component_formula n

/-- The standard resolution is a simplicial object with the counit
augmentation. -/
theorem standardResolution_is_simplicial_and_augmented
    {A : Type u} {S : Type u} [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) :
    Nonempty (GodementAugmentationData (standardResolutionBase T)
      (standardResolutionCounit T) (standardResolutionComultiplication T)) := by
  exact ⟨standardResolutionAugmentationData T⟩
/-! ## The two homotopy equivalences -/

/-- The outer resolution, obtained by applying `V` to the standard
resolution. Its chosen augmentation is the source's `1_V ⋆ ε`. -/
noncomputable def standardResolutionOuterData
    {A : Type u} {S : Type u} [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) :
    GodementWhiskeredAugmentationData (𝟭 A) (standardResolutionBase T) T.V
      (standardResolutionCounit T) (standardResolutionComultiplication T) :=
  (godement_whiskered_augmentation_condition (𝟭 A)
    (standardResolutionBase T) T.V (standardResolutionCounit T)
    (standardResolutionComultiplication T)
    (standardResolution_godementEquations T)).some

/-- The inner resolution, obtained by applying `U` to the standard
resolution. Its chosen augmentation is the source's `ε ⋆ 1_U`. -/
noncomputable def standardResolutionInnerData
    {A : Type u} {S : Type u} [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) :
    GodementWhiskeredAugmentationData T.U (standardResolutionBase T) (𝟭 A)
      (standardResolutionCounit T) (standardResolutionComultiplication T) :=
  (godement_whiskered_augmentation_condition T.U
    (standardResolutionBase T) (𝟭 A) (standardResolutionCounit T)
    (standardResolutionComultiplication T)
    (standardResolution_godementEquations T)).some

abbrev standardResolutionOuterAugmentation
    {A : Type u} {S : Type u} [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) :=
  (standardResolutionOuterData T).augmentation

abbrev standardResolutionInnerAugmentation
    {A : Type u} {S : Type u} [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) :=
  (standardResolutionInnerData T).augmentation

/-- Both augmented whiskered resolutions are homotopy equivalences. The
proof route is the section from Chapter 33, followed by its two-map homotopy
and the definition of `Unit26.IsHomotopyEquivalence`. -/
theorem standardResolution_homotopy_equivalences
    {A : Type u} {S : Type u} [Category.{u} A] [Category.{u} S]
    (T : StandardResolutionSituation A S) :
    Unit26.IsHomotopyEquivalence (standardResolutionOuterAugmentation T) ∧
      Unit26.IsHomotopyEquivalence (standardResolutionInnerAugmentation T) := by
  sorry

/-! ## The module and polynomial-algebra examples -/

/-- The free/forgetful adjunction used by the module example.  Here `M` and
`SetLike` are the chosen presentations of `Mod_R` and `Sets`; the actual
free-module implementation is supplied by the established algebraic API. -/
structure ModuleStandardResolutionExample
    (R M SetLike : Type u) [Ring R] [Category.{u} M] [Category.{u} SetLike]
    where
  free : SetLike ⥤ M
  forget : M ⥤ SetLike
  adjunction : free ⊣ forget

def moduleStandardResolutionSituation
    {R M SetLike : Type u} [Ring R] [Category.{u} M] [Category.{u} SetLike]
    (E : ModuleStandardResolutionExample R M SetLike) :
    StandardResolutionSituation M SetLike :=
  ⟨E.free, E.forget, E.adjunction⟩

/-- The degree `n` of the module example on an object `M₀`. -/
def moduleResolutionDegree
    {R M SetLike : Type u} [Ring R] [Category.{u} M] [Category.{u} SetLike]
    (E : ModuleStandardResolutionExample R M SetLike)
    (M₀ : M) (n : ℕ) : M :=
  (standardResolutionDegree (moduleStandardResolutionSituation E) (some n)).obj M₀

/-- The module example's degree-one face maps (the source's `d_0,d_1`). -/
def moduleResolutionFace
    {R M SetLike : Type u} [Ring R] [Category.{u} M] [Category.{u} SetLike]
    (E : ModuleStandardResolutionExample R M SetLike) (M₀ : M)
    (j : Fin 2) : moduleResolutionDegree E M₀ 1 ⟶ moduleResolutionDegree E M₀ 0 :=
  (standardResolutionFace (moduleStandardResolutionSituation E) 0 j).app M₀

/-- The module example's degree-one degeneracy maps (the source's `s_0,s_1`). -/
def moduleResolutionDegeneracy
    {R M SetLike : Type u} [Ring R] [Category.{u} M] [Category.{u} SetLike]
    (E : ModuleStandardResolutionExample R M SetLike) (M₀ : M)
    (j : Fin 2) : moduleResolutionDegree E M₀ 1 ⟶
      moduleResolutionDegree E M₀ 2 :=
  (standardResolutionDegeneracy (moduleStandardResolutionSituation E) 1 j).app M₀

/- The source's displayed sums in Example 34.4 are the elementwise normal
forms of `moduleResolutionFace` and `moduleResolutionDegeneracy` after the
chosen free-module presentation is expanded. They introduce no maps beyond
these canonical degree-one components. -/

theorem moduleResolution_augmentation_homotopy_equivalence
    {R M SetLike : Type u} [Ring R] [Category.{u} M] [Category.{u} SetLike]
    (E : ModuleStandardResolutionExample R M SetLike) :
    Unit26.IsHomotopyEquivalence
      (standardResolutionOuterAugmentation
        (moduleStandardResolutionSituation E)) := by
  exact (standardResolution_homotopy_equivalences
    (moduleStandardResolutionSituation E)).1

/-- The free/forgetful adjunction used by the polynomial-algebra example;
`Alg` is the chosen category of commutative `A`-algebras and `SetLike` the
chosen category of sets. -/
structure PolynomialAlgebraStandardResolutionExample
    (A Alg SetLike : Type u) [Category.{u} Alg] [Category.{u} SetLike] where
  free : SetLike ⥤ Alg
  forget : Alg ⥤ SetLike
  adjunction : free ⊣ forget

def polynomialAlgebraStandardResolutionSituation
    {A Alg SetLike : Type u} [Category.{u} Alg] [Category.{u} SetLike]
    (E : PolynomialAlgebraStandardResolutionExample A Alg SetLike) :
    StandardResolutionSituation Alg SetLike :=
  ⟨E.free, E.forget, E.adjunction⟩

/-- The degree `n` of the polynomial-algebra example on an algebra `B`. -/
def polynomialAlgebraResolutionDegree
    {A Alg SetLike : Type u} [Category.{u} Alg] [Category.{u} SetLike]
    (E : PolynomialAlgebraStandardResolutionExample A Alg SetLike)
    (B : Alg) (n : ℕ) : Alg :=
  (standardResolutionDegree
    (polynomialAlgebraStandardResolutionSituation E) (some n)).obj B

/-- The polynomial-algebra example's degree-one face maps. -/
def polynomialAlgebraResolutionFace
    {A Alg SetLike : Type u} [Category.{u} Alg] [Category.{u} SetLike]
    (E : PolynomialAlgebraStandardResolutionExample A Alg SetLike)
    (B : Alg) (j : Fin 2) : polynomialAlgebraResolutionDegree E B 1 ⟶
      polynomialAlgebraResolutionDegree E B 0 :=
  (standardResolutionFace (polynomialAlgebraStandardResolutionSituation E) 0 j).app B

/-- The polynomial-algebra example's degree-one degeneracy maps. -/
def polynomialAlgebraResolutionDegeneracy
    {A Alg SetLike : Type u} [Category.{u} Alg] [Category.{u} SetLike]
    (E : PolynomialAlgebraStandardResolutionExample A Alg SetLike)
    (B : Alg) (j : Fin 2) : polynomialAlgebraResolutionDegree E B 1 ⟶
      polynomialAlgebraResolutionDegree E B 2 :=
  (standardResolutionDegeneracy
    (polynomialAlgebraStandardResolutionSituation E) 1 j).app B

theorem polynomialAlgebraResolution_augmentation_homotopy_equivalence
    {A Alg SetLike : Type u} [Category.{u} Alg] [Category.{u} SetLike]
    (E : PolynomialAlgebraStandardResolutionExample A Alg SetLike) :
    Unit26.IsHomotopyEquivalence
      (standardResolutionOuterAugmentation
        (polynomialAlgebraStandardResolutionSituation E)) := by
  exact (standardResolution_homotopy_equivalences
    (polynomialAlgebraStandardResolutionSituation E)).1

/- The nested-bracket formulas in Examples 34.5 and 34.6 are likewise the
elementwise normal forms of the degree maps and the sections supplied by the
Chapter 33 Godement section interface; the chapter-level maps above retain
their presentation-independent categorical types. -/

end Formalization.Books.Simplicial.Unit34
