import Formalization.Books.Dga.Unit09.ConesAndDistinguishedTriangles
import Formalization.Books.Dga.Unit07.AdmissibleShortExactSequences

/-!
# Differential Graded Algebra, Chapter 10: The homotopy category is triangulated

This file records the triangulated-category interfaces used in the chapter.
The preceding chapter supplies the source-facing cone triangles and the
predicate for distinguished triangles.  The quotient category does not yet
carry a project-wide coherent shift instance, so the translation bridge below
keeps the canonical `dgmShift` representatives while exposing the quotient
functors needed for rotation and morphisms of triangles.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dga.Unit03
open Formalization.Books.Dga.Unit04
open Formalization.Books.Dga.Unit05
open Formalization.Books.Dga.Unit09

universe u

namespace Formalization.Books.Dga.Unit10

abbrev DgmHomotopyCategory {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :=
  DifferentialGradedModuleHomotopyCategory A

abbrev DgmHomotopyQuotient {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :
    DifferentialGradedModuleCategory A ⥤ DgmHomotopyCategory A :=
  differentialGradedModuleHomotopyQuotient A

abbrev DgmTriangle {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} :=
  Formalization.Books.Dga.Unit09.DgmTriangle (A := A)

abbrev DgmTriangleIsomorphism {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} :=
  Formalization.Books.Dga.Unit09.DgmTriangleIsomorphism (A := A)

abbrev DgmDistinguishedTriangle {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} :=
  Formalization.Books.Dga.Unit09.DgmDistinguishedTriangle (A := A)

/-! The module category has a categorical zero object, but its object type is
not itself equipped with a numeral-zero instance.  This is the concrete zero
module used in the split triangle. -/
noncomputable def dgmZero
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} : DifferentialGradedModule A where
  complex := HomologicalComplex.zero
  action := 0
  one_action := by
    apply HomologicalComplex.isZero_zero.eq_of_tgt
  assoc_action := by simp

/-! ## Translation and rotation -/

/-- A coherent family of translation functors on the homotopy category,
identified on objects with the canonical differential graded module shifts. -/
structure DgmTranslationData {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) where
  translation : HasShift (DgmHomotopyCategory A) ℤ
  objectIso : ∀ (k : ℤ) (M : DifferentialGradedModule A),
    (@CategoryTheory.shiftFunctor (DgmHomotopyCategory A) ℤ _ _ translation k).obj
        ((DgmHomotopyQuotient A).obj M) ≅
      (DgmHomotopyQuotient A).obj (dgmShift M k)

/-- Transport a quotient morphism through the object identifications supplied
by `DgmTranslationData`. -/
noncomputable def dgmTranslatedMap
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (τ : DgmTranslationData A) {M N : DifferentialGradedModule A}
    (f : (DgmHomotopyQuotient A).obj M ⟶
      (DgmHomotopyQuotient A).obj N) (k : ℤ) :
    (DgmHomotopyQuotient A).obj (dgmShift M k) ⟶
      (DgmHomotopyQuotient A).obj (dgmShift N k) :=
  (τ.objectIso k M).inv ≫
    (@CategoryTheory.shiftFunctor (DgmHomotopyCategory A) ℤ _ _ τ.translation k).map f ≫
      (τ.objectIso k N).hom

/-- The rotation of a triangle, with the sign convention in the source. -/
noncomputable def dgmRotateTriangle
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (τ : DgmTranslationData A) (T : DgmTriangle (A := A)) :
    DgmTriangle (A := A) where
  obj₁ := T.obj₂
  obj₂ := T.obj₃
  obj₃ := dgmShift T.obj₁ (1 : ℤ)
  mor₁ := T.mor₂
  mor₂ := T.mor₃
  mor₃ := -(dgmTranslatedMap τ T.mor₁ (1 : ℤ))

/-! ## The four triangulated-category axioms -/

/-- The zero triangle in TR1, represented by the split short exact sequence
`0 ⟶ M ⟶ M ⟶ 0`. -/
noncomputable def dgmSplitTriangle
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (M : DifferentialGradedModule A) : DgmTriangle (A := A) where
  obj₁ := M
  obj₂ := M
  obj₃ := dgmZero
  mor₁ := (DgmHomotopyQuotient A).map (𝟙 M)
  mor₂ := (DgmHomotopyQuotient A).map 0
  mor₃ := (DgmHomotopyQuotient A).map 0

/-- TR1 for the source-facing DGA triangle interface.  The cone clause is
included explicitly even though Chapter 9 already proves the stronger signed
cone statement, since it is one of the three clauses of TR1 in this section. -/
structure DgmTR1Data {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} where
  iso_closed : ∀ (T U : DgmTriangle (A := A)),
    Nonempty (DgmTriangleIsomorphism T U) →
      DgmDistinguishedTriangle T → DgmDistinguishedTriangle U
  split_triangle : ∀ (M : DifferentialGradedModule A),
    DgmDistinguishedTriangle (dgmSplitTriangle M)
  cone_triangle : ∀ {K L : DifferentialGradedModule A}
    (f : DifferentialGradedModuleHom K L),
    DgmDistinguishedTriangle (dgmSignedConeTriangle f)

/-- A morphism of source-facing triangles. -/
structure DgmTriangleMorphism
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (τ : DgmTranslationData A)
    (T U : DgmTriangle (A := A)) where
  first : (DgmHomotopyQuotient A).obj T.obj₁ ⟶
    (DgmHomotopyQuotient A).obj U.obj₁
  second : (DgmHomotopyQuotient A).obj T.obj₂ ⟶
    (DgmHomotopyQuotient A).obj U.obj₂
  third : (DgmHomotopyQuotient A).obj T.obj₃ ⟶
    (DgmHomotopyQuotient A).obj U.obj₃
  comm₁ : T.mor₁ ≫ second = first ≫ U.mor₁
  comm₂ : T.mor₂ ≫ third = second ≫ U.mor₂
  comm₃ : T.mor₃ ≫ dgmTranslatedMap τ first (1 : ℤ) =
    third ≫ U.mor₃

/-- TR2: a triangle is distinguished exactly when its rotation is. -/
structure DgmTR2Data
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (τ : DgmTranslationData A) where
  rotate_iff : ∀ T : DgmTriangle (A := A),
    DgmDistinguishedTriangle (dgmRotateTriangle τ T) ↔
      DgmDistinguishedTriangle T

/-- TR3: a commutative square between the first two maps of distinguished
triangles extends to a morphism of triangles. -/
structure DgmTR3Data
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (τ : DgmTranslationData A) where
  extend : ∀ (T U : DgmTriangle (A := A)),
    DgmDistinguishedTriangle T → DgmDistinguishedTriangle U →
    ∀ (a : (DgmHomotopyQuotient A).obj T.obj₁ ⟶
      (DgmHomotopyQuotient A).obj U.obj₁)
      (b : (DgmHomotopyQuotient A).obj T.obj₂ ⟶
        (DgmHomotopyQuotient A).obj U.obj₂),
      T.mor₁ ≫ b = a ≫ U.mor₁ →
      Nonempty (DgmTriangleMorphism τ T U)

/-! ## The octahedral witness used by the split-injection lemma -/

/-- The three distinguished triangles and their two compatible morphisms in
the TR4 configuration for composable admissible monomorphisms. -/
structure DgmTR4Witness
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (τ : DgmTranslationData A)
    {K L M : DifferentialGradedModule A}
    (α : DifferentialGradedModuleHom K L)
    (β : DifferentialGradedModuleHom L M) where
  Q₁ : DifferentialGradedModule A
  Q₂ : DifferentialGradedModule A
  Q₃ : DifferentialGradedModule A
  triangle₁ : DgmTriangle (A := A)
  triangle₂ : DgmTriangle (A := A)
  triangle₃ : DgmTriangle (A := A)
  triangle₁_obj₁ : triangle₁.obj₁ = K
  triangle₁_obj₂ : triangle₁.obj₂ = L
  triangle₁_obj₃ : triangle₁.obj₃ = Q₁
  triangle₂_obj₁ : triangle₂.obj₁ = K
  triangle₂_obj₂ : triangle₂.obj₂ = M
  triangle₂_obj₃ : triangle₂.obj₃ = Q₂
  triangle₃_obj₁ : triangle₃.obj₁ = L
  triangle₃_obj₂ : triangle₃.obj₂ = M
  triangle₃_obj₃ : triangle₃.obj₃ = Q₃
  triangle₁_distinguished : DgmDistinguishedTriangle triangle₁
  triangle₂_distinguished : DgmDistinguishedTriangle triangle₂
  triangle₃_distinguished : DgmDistinguishedTriangle triangle₃
  triangle₁_mor₁ : HEq triangle₁.mor₁
    ((DgmHomotopyQuotient A).map α)
  triangle₂_mor₁ : HEq triangle₂.mor₁
    ((DgmHomotopyQuotient A).map
      (differentialGradedModuleHomComp α β))
  triangle₃_mor₁ : HEq triangle₃.mor₁
    ((DgmHomotopyQuotient A).map β)
  first_morphism : DgmTriangleMorphism τ triangle₁ triangle₂
  second_morphism : DgmTriangleMorphism τ triangle₂ triangle₃
  cone_triangle : DgmTriangle (A := A)
  cone_triangle_distinguished : DgmDistinguishedTriangle cone_triangle
  cone_obj₁ : cone_triangle.obj₁ = Q₁
  cone_obj₂ : cone_triangle.obj₂ = Q₂
  cone_obj₃ : cone_triangle.obj₃ = Q₃

/-- The additional exact rows and splittings exhibited in the special TR4
lemma for admissible monomorphisms. -/
structure DgmSplitTR4Witness
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (τ : DgmTranslationData A)
    {K L M : DifferentialGradedModule A}
    (α : DifferentialGradedModuleHom K L)
    (β : DifferentialGradedModuleHom L M)
    extends DgmTR4Witness τ α β where
  sequence₁ : Formalization.Books.Dga.Unit09.DgmAdmissibleShortExact K L Q₁
  sequence₂ : Formalization.Books.Dga.Unit09.DgmAdmissibleShortExact K M Q₂
  sequence₃ : Formalization.Books.Dga.Unit09.DgmAdmissibleShortExact L M Q₃
  sequence₄ : Formalization.Books.Dga.Unit09.DgmAdmissibleShortExact Q₁ Q₂ Q₃
  sequence₁_f : sequence₁.f = α
  sequence₂_f : sequence₂.f = differentialGradedModuleHomComp α β
  sequence₃_f : sequence₃.f = β
  triangle₁_sequence : toDgmTR4Witness.triangle₁ =
    dgmAssociatedTriangle sequence₁
  triangle₂_sequence : toDgmTR4Witness.triangle₂ =
    dgmAssociatedTriangle sequence₂
  triangle₃_sequence : toDgmTR4Witness.triangle₃ =
    dgmAssociatedTriangle sequence₃
  cone_triangle_sequence : toDgmTR4Witness.cone_triangle =
    dgmAssociatedTriangle sequence₄
  connecting_map_formula : dgmConnectingMap sequence₄ =
    differentialGradedModuleHomComp (dgmConnectingMap sequence₃)
      (dgmShiftMap sequence₁.g (1 : ℤ))

/-- TR4 in the form needed by the chapter: every composable pair of
admissible monomorphisms has a distinguished octahedral configuration. -/
structure DgmTR4Data
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (τ : DgmTranslationData A) where
  octahedron : ∀ {K L M : DifferentialGradedModule A}
    (α : DifferentialGradedModuleHom K L)
    (β : DifferentialGradedModuleHom L M),
    Formalization.Books.Dga.Unit07.DgmAdmissibleMonomorphism α →
      Formalization.Books.Dga.Unit07.DgmAdmissibleMonomorphism β →
    Nonempty (DgmSplitTR4Witness τ α β)

/-- The full TR4 interface, stated for arbitrary composable differential
graded module maps, as used after the admissible factorization argument. -/
structure DgmTR4AllMapsData
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (τ : DgmTranslationData A) where
  octahedron : ∀ {K L M : DifferentialGradedModule A}
    (α : DifferentialGradedModuleHom K L)
    (β : DifferentialGradedModuleHom L M),
    Nonempty (DgmTR4Witness τ α β)

/-- The source's pre-triangulated conclusion, with TR1--TR4 exposed as
named data rather than hidden inside an unstructured proposition. -/
structure DgmPretriangulatedData
    {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) where
  translation : DgmTranslationData A
  tr₁ : DgmTR1Data (A := A)
  tr₂ : DgmTR2Data translation
  tr₃ : DgmTR3Data translation

/-! ## Source results -/

/-- The homotopy category of differential graded right `A`-modules is
pre-triangulated with its natural translations and distinguished triangles. -/
theorem dgm_homotopy_category_pretriangulated
    {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :
    Nonempty (DgmPretriangulatedData A) := by
  sorry

/-- The split-injection case of TR4 from the source. -/
theorem dgm_two_split_injections
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (τ : DgmTranslationData A)
    {K L M : DifferentialGradedModule A}
    (α : DifferentialGradedModuleHom K L)
    (β : DifferentialGradedModuleHom L M)
    (hα : Formalization.Books.Dga.Unit07.DgmAdmissibleMonomorphism α)
    (hβ : Formalization.Books.Dga.Unit07.DgmAdmissibleMonomorphism β) :
    Nonempty (DgmSplitTR4Witness τ α β) := by
  sorry

/-- The homotopy category of differential graded right `A`-modules is
triangulated. -/
structure DgmTriangulatedData
    {R : Type u} [CommRing R]
  (A : DifferentialGradedAlgebra R) where
  pretriangulated : DgmPretriangulatedData A
  tr₄ : DgmTR4AllMapsData pretriangulated.translation

theorem dgm_homotopy_category_triangulated
    {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :
    Nonempty (DgmTriangulatedData A) := by
  sorry

end Formalization.Books.Dga.Unit10
