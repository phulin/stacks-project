import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Groupoids in Algebraic Spaces, Chapter 29: shared interfaces

The current Mathlib snapshot has the scheme and morphism-property APIs used
below, but it does not yet contain algebraic spaces or internal groupoids in
algebraic spaces.  This file records the smallest chapter-local interface for
those notions.  `Scheme` is used as the available representable model of an
algebraic space; all products and fibre products are the chosen categorical
ones from Mathlib.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Formalization.Books.SpacesGroupoids.Unit29

/-- The representable model used for an algebraic space in this chapter. -/
abbrev AlgebraicSpace := Scheme

/-- The structural data of an internal groupoid over `B`. -/
structure GroupoidData (S B : AlgebraicSpace.{u}) where
  B_to_S : B ⟶ S
  obj : AlgebraicSpace.{u}
  arr : AlgebraicSpace.{u}
  obj_base : obj ⟶ B
  arr_base : arr ⟶ B
  s_map : arr ⟶ obj
  t_map : arr ⟶ obj
  comp_map : pullback s_map t_map ⟶ arr
  unit_map : obj ⟶ arr
  inv_map : arr ⟶ arr

variable {S B : AlgebraicSpace.{u}}

/-- The structure maps and groupoid operations are all over the base. -/
structure GroupoidBaseCompatibility (D : GroupoidData S B) : Prop where
  s_over_B : D.s_map ≫ D.obj_base = D.arr_base
  t_over_B : D.t_map ≫ D.obj_base = D.arr_base
  comp_over_B : D.comp_map ≫ D.arr_base =
    pullback.fst D.s_map D.t_map ≫ D.arr_base
  unit_over_B : D.unit_map ≫ D.arr_base = D.obj_base
  inv_over_B : D.inv_map ≫ D.arr_base = D.arr_base

variable {S B : AlgebraicSpace.{u}}

/-- Composition of two composable arrows after evaluating on a test scheme. -/
def internalComposition (D : GroupoidData S B) {T : AlgebraicSpace.{u}}
    (f g : T ⟶ D.arr)
    (hfg : f ≫ D.s_map = g ≫ D.t_map) : T ⟶ D.arr :=
  pullback.lift f g hfg ≫ D.comp_map

variable {S B : AlgebraicSpace.{u}}

/-- The internal groupoid identities, inverse, composition, and associativity. -/
structure GroupoidAxioms (D : GroupoidData S B) : Prop where
  identity_source : D.unit_map ≫ D.s_map = 𝟙 D.obj
  identity_target : D.unit_map ≫ D.t_map = 𝟙 D.obj
  inverse_source : D.inv_map ≫ D.s_map = D.t_map
  inverse_target : D.inv_map ≫ D.t_map = D.s_map
  composition_source : D.comp_map ≫ D.s_map =
    pullback.snd D.s_map D.t_map ≫ D.s_map
  composition_target : D.comp_map ≫ D.t_map =
    pullback.fst D.s_map D.t_map ≫ D.t_map
  left_unit : ∀ {T : AlgebraicSpace.{u}} (f : T ⟶ D.arr),
    internalComposition D (f ≫ D.t_map ≫ D.unit_map) f
        (by simp [Category.assoc, identity_source]) = f
  right_unit : ∀ {T : AlgebraicSpace.{u}} (f : T ⟶ D.arr),
    internalComposition D f (f ≫ D.s_map ≫ D.unit_map)
        (by simp [Category.assoc, identity_target]) = f
  left_inverse : ∀ {T : AlgebraicSpace.{u}} (f : T ⟶ D.arr),
    internalComposition D (f ≫ D.inv_map) f
        (by simp [Category.assoc, inverse_source]) =
      f ≫ D.s_map ≫ D.unit_map
  right_inverse : ∀ {T : AlgebraicSpace.{u}} (f : T ⟶ D.arr),
    internalComposition D f (f ≫ D.inv_map)
        (by simp [Category.assoc, inverse_target]) =
      f ≫ D.t_map ≫ D.unit_map
  associative : ∀ {T : AlgebraicSpace.{u}} (f g h : T ⟶ D.arr)
      (hfg : f ≫ D.s_map = g ≫ D.t_map)
      (hgh : g ≫ D.s_map = h ≫ D.t_map),
    internalComposition D
        (internalComposition D f g hfg) h
        (by
          simp only [internalComposition, Category.assoc, composition_source,
            pullback.lift_snd_assoc]
          exact hgh) =
      internalComposition D f
        (internalComposition D g h hgh)
        (by
          simp only [internalComposition, Category.assoc, composition_target,
            pullback.lift_fst_assoc]
          exact hfg)

namespace GroupoidData

variable {S B : AlgebraicSpace.{u}} (D : GroupoidData S B)

/-- The map `j = (t, s) : R ⟶ U ×_B U`. -/
def relation (H : GroupoidBaseCompatibility D) :
    D.arr ⟶ pullback D.obj_base D.obj_base :=
  pullback.lift D.t_map D.s_map (H.t_over_B.trans H.s_over_B.symm)

/-- The diagonal morphism `U ⟶ U ×_B U`. -/
def diagonal : D.obj ⟶ pullback D.obj_base D.obj_base :=
  pullback.lift (𝟙 D.obj) (𝟙 D.obj) (by simp)

/-- The stabilizer carrier, defined by the cartesian square with the diagonal. -/
def stabilizer (H : GroupoidBaseCompatibility D) : AlgebraicSpace.{u} :=
  pullback (D.relation H) D.diagonal

/-- The stabilizer's projection to the arrow space. -/
def stabilizerToArr (H : GroupoidBaseCompatibility D) :
    D.stabilizer H ⟶ D.arr :=
  pullback.fst (D.relation H) D.diagonal

/-- The stabilizer's structure morphism to the object space. -/
def stabilizerToObj (H : GroupoidBaseCompatibility D) :
    D.stabilizer H ⟶ D.obj :=
  pullback.snd (D.relation H) D.diagonal

end GroupoidData

/--
An internal groupoid in the representable model of algebraic spaces.  The
`inverseComposition` field is the canonical map sending `(f, g)` with the
same source and target to `(f⁻¹ ∘ g)` in the stabilizer; its compatibility
with the stabilizer's structure morphism is the only part needed to state the
chapter 29 diagram.
-/
structure GroupoidInAlgebraicSpaces (S B : AlgebraicSpace.{u}) where
  data : GroupoidData S B
  base_compatibility : GroupoidBaseCompatibility data
  axioms : GroupoidAxioms data
  inverseComposition :
    (pullback (data.relation base_compatibility) (data.relation base_compatibility)) ⟶
      (data.stabilizer base_compatibility)
  inverseComposition_source :
    pullback.fst (data.relation base_compatibility) (data.relation base_compatibility) ≫
        data.s_map =
      inverseComposition ≫ data.stabilizerToObj base_compatibility

namespace GroupoidInAlgebraicSpaces

variable {S B : AlgebraicSpace.{u}} (𝒢 : GroupoidInAlgebraicSpaces S B)

abbrev obj : AlgebraicSpace.{u} := 𝒢.data.obj
abbrev arr : AlgebraicSpace.{u} := 𝒢.data.arr
abbrev s_map : 𝒢.arr ⟶ 𝒢.obj := 𝒢.data.s_map
abbrev t_map : 𝒢.arr ⟶ 𝒢.obj := 𝒢.data.t_map
abbrev unit_map : 𝒢.obj ⟶ 𝒢.arr := 𝒢.data.unit_map

/-- The map `j = (t, s) : R ⟶ U ×_B U`. -/
abbrev relation : 𝒢.arr ⟶ pullback 𝒢.data.obj_base 𝒢.data.obj_base :=
  𝒢.data.relation 𝒢.base_compatibility

/-- The diagonal morphism `U ⟶ U ×_B U`. -/
abbrev diagonal : 𝒢.obj ⟶ pullback 𝒢.data.obj_base 𝒢.data.obj_base :=
  𝒢.data.diagonal

/-- The stabilizer carrier, defined by the cartesian square with the diagonal. -/
abbrev stabilizer : AlgebraicSpace.{u} := pullback 𝒢.relation 𝒢.diagonal

/-- The stabilizer's projection to the arrow space. -/
abbrev stabilizerToArr : (pullback 𝒢.relation 𝒢.diagonal) ⟶ 𝒢.arr :=
  pullback.fst 𝒢.relation 𝒢.diagonal

/-- The stabilizer's structure morphism to the object space. -/
abbrev stabilizerToObj : (pullback 𝒢.relation 𝒢.diagonal) ⟶ 𝒢.obj :=
  pullback.snd 𝒢.relation 𝒢.diagonal

@[simp]
lemma relation_fst :
    𝒢.relation ≫ pullback.fst 𝒢.data.obj_base 𝒢.data.obj_base =
      𝒢.t_map := by
  simpa [relation, GroupoidData.relation] using
    (pullback.lift_fst 𝒢.data.t_map 𝒢.data.s_map
      (𝒢.base_compatibility.t_over_B.trans
        𝒢.base_compatibility.s_over_B.symm))

@[simp]
lemma relation_snd :
    𝒢.relation ≫ pullback.snd 𝒢.data.obj_base 𝒢.data.obj_base =
      𝒢.s_map := by
  simpa [relation, GroupoidData.relation] using
    (pullback.lift_snd 𝒢.data.t_map 𝒢.data.s_map
      (𝒢.base_compatibility.t_over_B.trans
        𝒢.base_compatibility.s_over_B.symm))

@[simp]
lemma diagonal_fst :
    𝒢.diagonal ≫ pullback.fst 𝒢.data.obj_base 𝒢.data.obj_base =
      𝟙 𝒢.obj := by
  simpa [diagonal, GroupoidData.diagonal] using
    (pullback.lift_fst (𝟙 𝒢.obj) (𝟙 𝒢.obj)
      (by simp : (𝟙 𝒢.obj) ≫ 𝒢.data.obj_base =
        (𝟙 𝒢.obj) ≫ 𝒢.data.obj_base))

@[simp]
lemma diagonal_snd :
    𝒢.diagonal ≫ pullback.snd 𝒢.data.obj_base 𝒢.data.obj_base =
      𝟙 𝒢.obj := by
  simpa [diagonal, GroupoidData.diagonal] using
    (pullback.lift_snd (𝟙 𝒢.obj) (𝟙 𝒢.obj)
      (by simp : (𝟙 𝒢.obj) ≫ 𝒢.data.obj_base =
        (𝟙 𝒢.obj) ≫ 𝒢.data.obj_base))

lemma unit_pair : 𝒢.unit_map ≫ 𝒢.relation = 𝒢.diagonal := by
  apply pullback.hom_ext
  · rw [Category.assoc, relation_fst, 𝒢.axioms.identity_target, diagonal_fst]
  · rw [Category.assoc, relation_snd, 𝒢.axioms.identity_source, diagonal_snd]

/-- The identity section `e : U ⟶ G` of the stabilizer. -/
def stabilizerIdentity : 𝒢.obj ⟶ pullback 𝒢.relation 𝒢.diagonal :=
  pullback.lift 𝒢.unit_map (𝟙 𝒢.obj) (by simpa using 𝒢.unit_pair)

@[simp]
lemma stabilizerIdentity_toObj :
  𝒢.stabilizerIdentity ≫ 𝒢.stabilizerToObj = 𝟙 𝒢.obj := by
  simp only [stabilizerIdentity]
  rw [pullback.lift_snd]

@[simp]
lemma stabilizerIdentity_toArr :
  𝒢.stabilizerIdentity ≫ 𝒢.stabilizerToArr = 𝒢.unit_map := by
  simp only [stabilizerIdentity]
  rw [pullback.lift_fst]

/-- The upper-left horizontal arrow in the separation diagram. -/
def diagonalTopLeft : 𝒢.arr ⟶ pullback 𝒢.s_map (𝟙 𝒢.obj) :=
  pullback.lift (𝟙 𝒢.arr) 𝒢.s_map (by simp)

/-- The left vertical diagonal arrow in the separation diagram. -/
def diagonalLeft : 𝒢.arr ⟶ pullback 𝒢.relation 𝒢.relation :=
  pullback.lift (𝟙 𝒢.arr) (𝟙 𝒢.arr) (by simp)

/-- The lower-left arrow `(f, g) ↦ (f, f⁻¹ ∘ g)`. -/
def diagonalBottomLeft :
    (pullback 𝒢.relation 𝒢.relation) ⟶
      (pullback 𝒢.s_map 𝒢.stabilizerToObj) :=
  pullback.lift (pullback.fst 𝒢.relation 𝒢.relation) 𝒢.inverseComposition
    𝒢.inverseComposition_source

/-- The middle vertical arrow induced by the identity section of the stabilizer. -/
def diagonalMiddle :
    (pullback 𝒢.s_map (𝟙 𝒢.obj)) ⟶
      (pullback 𝒢.s_map 𝒢.stabilizerToObj) :=
  pullback.lift (pullback.fst 𝒢.s_map (𝟙 𝒢.obj))
    (pullback.snd 𝒢.s_map (𝟙 𝒢.obj) ≫ 𝒢.stabilizerIdentity) (by
      simpa [Category.assoc] using
        (pullback.condition :
          pullback.fst 𝒢.s_map (𝟙 𝒢.obj) ≫ 𝒢.s_map =
            pullback.snd 𝒢.s_map (𝟙 𝒢.obj) ≫ (𝟙 𝒢.obj)))

/-- The two right-hand projections in the separation diagram. -/
def diagonalTopRight :
    (pullback 𝒢.s_map (𝟙 𝒢.obj)) ⟶ 𝒢.obj :=
  pullback.snd 𝒢.s_map (𝟙 𝒢.obj)

def diagonalBottomRight :
    (pullback 𝒢.s_map 𝒢.stabilizerToObj) ⟶ 𝒢.stabilizer :=
  pullback.snd 𝒢.s_map 𝒢.stabilizerToObj

end GroupoidInAlgebraicSpaces

end Formalization.Books.SpacesGroupoids.Unit29
