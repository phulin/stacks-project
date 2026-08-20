import Formalization.Books.Dga.Unit26.Core

/-!
# Differential Graded Algebra, Chapter 27: Obtaining triangulated categories

This chapter packages the abstract axioms (A), (B), and (C) from the source
and records the construction and comparison interfaces used to prove that the
homotopy category of a differential graded category is triangulated.  The
proposition proofs are intentionally deferred to the proving stage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dga.Unit25
open Formalization.Books.Dga.Unit26

universe u v

namespace Formalization.Books.Dga.Unit27

/-! ## Axioms (A) and (B) -/

abbrev DgHomotopyCategory {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] :=
  DifferentialGradedCategory.DgHomotopyCategory.{u, v, v} A

abbrev DgHomotopyQuotient {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] :
    DifferentialGradedCategory.ComplexCategory A ⥤ DgHomotopyCategory (A := A) :=
  DifferentialGradedCategory.homotopyQuotient

abbrev DgComplexObject {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] :=
  DifferentialGradedCategory.ComplexCategory.{u, v, v} A

/-- A direct sum in `Comp(A)` whose structure maps are the closed degree-zero
morphisms of the differential graded category. -/
structure DgDirectSum {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    (X Y : DgComplexObject (A := A)) where
  carrier : DgComplexObject (A := A)
  data : DirectSumData X Y carrier
  differential_graded :
    DifferentialGradedCategory.IsDifferentialGradedDirectSum data

/-- A choice of zero object and binary differential graded direct sums. -/
structure DgAdditiveAxiom {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] where
  zero : DgComplexObject (A := A)
  zero_is_zero : IsZero zero
  directSum : ∀ (X Y : DgComplexObject (A := A)),
    Nonempty (DgDirectSum (A := A) X Y)

/-- The degreewise form of the source's isomorphism
`Hom(x,y[k]) = Hom(x,y)[k]`.  The `HEq` fields only reconcile the integer
indices `(n + 1) + k` and `(n + k) + 1`. -/
structure DgHomShiftIso {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    (shift : ℤ → DifferentialGradedFunctor A A)
    (X Y : A.Obj) (k : ℤ) where
  hom : ∀ n : ℤ,
    A.hom X ((shift k).obj Y) n ≃ₗ[R] A.hom X Y (n + k)
  map_differential : ∀ (n : ℤ) (f : A.hom X ((shift k).obj Y) n),
    HEq
      (hom (n + 1) ((A.differential X ((shift k).obj Y) n).hom f))
      ((A.differential X Y (n + k)).hom (hom n f))

/-- A strict family of differential graded shifts, together with the Hom
identifications and their compatibility with composition. -/
structure DgShiftAxiom {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] where
  shift : ℤ → DifferentialGradedFunctor A A
  shift_zero_obj : ∀ X : A.Obj, (shift 0).obj X = X
  shift_zero_map : ∀ (X Y : A.Obj) (n : ℤ) (f : A.hom X Y n),
    HEq ((shift 0).mapHom X Y n f) f
  shift_add_obj : ∀ (n m : ℤ) (X : A.Obj),
    (shift (n + m)).obj X = (shift n).obj ((shift m).obj X)
  shift_add_map : ∀ (n m : ℤ) (X Y : A.Obj) (i : ℤ) (f : A.hom X Y i),
    HEq
      ((shift (n + m)).mapHom X Y i f)
      ((shift n).mapHom ((shift m).obj X) ((shift m).obj Y) i
        ((shift m).mapHom X Y i f))
  homIso : ∀ (X Y : A.Obj) (k : ℤ), DgHomShiftIso shift X Y k
  homIso_comp : ∀ (X Y Z : A.Obj) (k i j : ℤ)
    (f : A.hom X ((shift k).obj Y) i) (g : A.hom Y Z j),
    HEq
      ((homIso X Z k).hom (i + j)
        (A.composition i j f ((shift k).mapHom Y Z j g)))
      (A.composition (i + k) j ((homIso X Y k).hom i f) g)
  homotopyShift : ∀ k : ℤ,
    DgHomotopyCategory (A := A) ⥤ DgHomotopyCategory (A := A)
  homotopyShift_obj : ∀ (k : ℤ) (X : DgComplexObject (A := A)),
    (homotopyShift k).obj ((DgHomotopyQuotient (A := A)).obj X) =
      (DgHomotopyQuotient (A := A)).obj
        ((DifferentialGradedFunctor.onComplexes (shift k)).obj X)

/-! ## Admissible sequences and triangles -/

/-- A split short exact sequence in `Comp(A)`.  The four maps in `data` are
the two inclusions and two projections for the underlying graded direct sum;
`f` and `g` select the displayed first inclusion and second projection. -/
structure DgAdmissibleShortExact {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    (X Y Z : DgComplexObject (A := A)) where
  f : X ⟶ Y
  g : Y ⟶ Z
  data : DirectSumData X Z Y
  f_eq : data.i = f
  g_eq : data.q = g

@[simp] theorem DgAdmissibleShortExact.zero
    {R : Type u} [CommRing R] [A : DifferentialGradedCategory R]
    {X Y Z : DgComplexObject (A := A)}
    (S : DgAdmissibleShortExact X Y Z) : S.f ≫ S.g = 0 := by
  rw [← S.f_eq, ← S.g_eq]
  exact S.data.i_q

/-- An admissible monomorphism is the first map of an admissible short exact
sequence. -/
def DgAdmissibleMonomorphism {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    {X Y : DgComplexObject (A := A)} (f : X ⟶ Y) : Prop :=
  ∃ (Z : DgComplexObject (A := A)),
    ∃ S : DgAdmissibleShortExact X Y Z, S.f = f

/-- An admissible epimorphism is the second map of an admissible short exact
sequence. -/
def DgAdmissibleEpimorphism {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    {Y Z : DgComplexObject (A := A)} (g : Y ⟶ Z) : Prop :=
  ∃ (X : DgComplexObject (A := A)),
    ∃ S : DgAdmissibleShortExact X Y Z, S.g = g

/-- A triangle in the homotopy category of a differential graded category. -/
structure DgTriangle {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (σ : DgShiftAxiom (A := A)) where
  obj₁ : DgComplexObject (A := A)
  obj₂ : DgComplexObject (A := A)
  obj₃ : DgComplexObject (A := A)
  mor₁ : (DgHomotopyQuotient (A := A)).obj obj₁ ⟶
    (DgHomotopyQuotient (A := A)).obj obj₂
  mor₂ : (DgHomotopyQuotient (A := A)).obj obj₂ ⟶
    (DgHomotopyQuotient (A := A)).obj obj₃
  mor₃ : (DgHomotopyQuotient (A := A)).obj obj₃ ⟶
    (σ.homotopyShift 1).obj
      ((DgHomotopyQuotient (A := A)).obj obj₁)

abbrev DgShiftFunctor {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    (σ : DgShiftAxiom (A := A)) (k : ℤ) :
    DgComplexObject (A := A) ⥤ DgComplexObject (A := A) :=
  DifferentialGradedFunctor.onComplexes (σ.shift k)

abbrev DgShiftObject {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    (σ : DgShiftAxiom (A := A))
    (X : DgComplexObject (A := A)) (k : ℤ) :=
  (DgShiftFunctor σ k).obj X

abbrev DgShiftMap {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    (σ : DgShiftAxiom (A := A))
    {X Y : DgComplexObject (A := A)} (f : X ⟶ Y) (k : ℤ) :
    DgShiftObject σ X k ⟶ DgShiftObject σ Y k :=
  (DgShiftFunctor σ k).map f

noncomputable def DgShiftHomotopyFunctor {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
  (σ : DgShiftAxiom (A := A)) (k : ℤ) :
    DgHomotopyCategory (A := A) ⥤ DgHomotopyCategory (A := A) :=
  σ.homotopyShift k

/-- A representative map is a homotopy equivalence precisely when its image
in the quotient category is an isomorphism. -/
def DgHomotopyEquivalence {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    {X Y : DgComplexObject (A := A)} (f : X ⟶ Y) : Prop :=
  IsIso ((DgHomotopyQuotient (A := A)).map f)

/-- The two consecutive compositions visible in the triangle produced by an
admissible short exact sequence vanish in the homotopy category. -/
def DgTriangleCompositionsZero {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    {σ : DgShiftAxiom (A := A)} (T : DgTriangle σ) : Prop :=
  T.mor₁ ≫ T.mor₂ = 0 ∧ T.mor₂ ≫ T.mor₃ = 0

/-! ## Connecting maps and axiom (C) -/

/-- The boundary map attached to a chosen graded splitting.  The shift Hom
isomorphism transports the degree-one formula `p d(s)` to a closed degree-zero
map into the shifted object. -/
def DgBoundaryFormula {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    {σ : DgShiftAxiom (A := A)}
    {X Y Z : DgComplexObject (A := A)}
    (S : DgAdmissibleShortExact X Y Z)
    (δ : Z ⟶ DgShiftObject σ X 1) : Prop :=
  (σ.homIso
      (DifferentialGradedCategory.ComplexCategoryObject.underlying A Z)
      (DifferentialGradedCategory.ComplexCategoryObject.underlying A X) 1).hom 0
      (δ.1 : A.hom
        (DifferentialGradedCategory.ComplexCategoryObject.underlying A Z)
        ((σ.shift 1).obj
          (DifferentialGradedCategory.ComplexCategoryObject.underlying A X)) 0) =
    A.composition 1 0
      ((A.differential
        (DifferentialGradedCategory.ComplexCategoryObject.underlying A Z)
        (DifferentialGradedCategory.ComplexCategoryObject.underlying A Y) 0).hom
        (S.data.j.1 : A.hom
          (DifferentialGradedCategory.ComplexCategoryObject.underlying A Z)
          (DifferentialGradedCategory.ComplexCategoryObject.underlying A Y) 0))
      (S.data.p.1 : A.hom
        (DifferentialGradedCategory.ComplexCategoryObject.underlying A Y)
        (DifferentialGradedCategory.ComplexCategoryObject.underlying A X) 0)

structure DgConnectingWitness {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    {σ : DgShiftAxiom (A := A)}
    {X Y Z : DgComplexObject (A := A)}
    (S : DgAdmissibleShortExact X Y Z) where
  delta : Z ⟶ DgShiftObject σ X 1
  formula : DgBoundaryFormula S delta

noncomputable def DgAssociatedTriangle {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    {σ : DgShiftAxiom (A := A)}
    {X Y Z : DgComplexObject (A := A)}
    {S : DgAdmissibleShortExact X Y Z}
    (w : DgConnectingWitness (σ := σ) S) : DgTriangle σ where
  obj₁ := X
  obj₂ := Y
  obj₃ := Z
  mor₁ := (DgHomotopyQuotient (A := A)).map S.f
  mor₂ := (DgHomotopyQuotient (A := A)).map S.g
  mor₃ := (DgHomotopyQuotient (A := A)).map w.delta ≫
    eqToHom (σ.homotopyShift_obj 1 X).symm

/-- The abstract form of Lemma `get-triangle`, including its boundary formula
and the vanishing of the consecutive compositions in `K(A)`. -/
theorem dgc_get_triangle {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    {σ : DgShiftAxiom (A := A)}
    {X Y Z : DgComplexObject (A := A)}
    (S : DgAdmissibleShortExact X Y Z) :
    Nonempty {w : DgConnectingWitness (σ := σ) S //
      DgTriangleCompositionsZero (DgAssociatedTriangle w)} := by
  sorry

/-- A cone witness for a closed degree-zero map.  The final equality is axiom
(C): the boundary map of `y ⟶ c(f) ⟶ x[1]` is the shifted map `f[1]`. -/
structure DgConeWitness {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    (σ : DgShiftAxiom (A := A))
    {X Y : DgComplexObject (A := A)} (f : X ⟶ Y) where
  cone : DgComplexObject (A := A)
  sequence : DgAdmissibleShortExact Y cone (DgShiftObject σ X 1)
  boundary : DgConnectingWitness (σ := σ) sequence
  boundary_is_shift :
    (DgHomotopyQuotient (A := A)).map boundary.delta =
      (DgHomotopyQuotient (A := A)).map (DgShiftMap σ f 1)

/-- Situation (A), (B), and (C) of the source. -/
structure DgABC (R : Type u) [CommRing R]
    [A : DifferentialGradedCategory R] where
  additive : @DgAdditiveAxiom R _ A
  shifts : DgShiftAxiom (A := A)
  cone : ∀ {X Y : DgComplexObject (A := A)} (f : X ⟶ Y),
    Nonempty (DgConeWitness shifts f)

noncomputable def dgcConeWitness {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X Y : DgComplexObject (A := A)} (f : X ⟶ Y) :
    DgConeWitness S.shifts f :=
  Classical.choice (S.cone f)

abbrev dgcCone {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X Y : DgComplexObject (A := A)} (f : X ⟶ Y) :
    DgComplexObject (A := A) :=
  (dgcConeWitness S f).cone

noncomputable def dgcConeTriangle {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X Y : DgComplexObject (A := A)} (f : X ⟶ Y) : DgTriangle S.shifts :=
  DgAssociatedTriangle (dgcConeWitness S f).boundary

/-- The source-facing cone triangle `X ⟶ Y ⟶ C(f) ⟶ X[1]`; the minus sign
is the convention used in TR1 and in the cone comparison lemma. -/
noncomputable def dgcMappingConeTriangle {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X Y : DgComplexObject (A := A)} (f : X ⟶ Y) : DgTriangle S.shifts where
  obj₁ := X
  obj₂ := Y
  obj₃ := dgcCone S f
  mor₁ := (DgHomotopyQuotient (A := A)).map f
  mor₂ := (DgHomotopyQuotient (A := A)).map
    (dgcConeWitness S f).sequence.f
  mor₃ := (DgHomotopyQuotient (A := A)).map
      (-(dgcConeWitness S f).sequence.g) ≫
    eqToHom (S.shifts.homotopyShift_obj 1 X).symm

/-- The split triangle from TR1, using the zero object supplied by axiom (A). -/
noncomputable def dgcSplitTriangle {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    (X : DgComplexObject (A := A)) : DgTriangle S.shifts where
  obj₁ := X
  obj₂ := X
  obj₃ := S.additive.zero
  mor₁ := (DgHomotopyQuotient (A := A)).map (𝟙 X)
  mor₂ := (DgHomotopyQuotient (A := A)).map 0
  mor₃ := (DgHomotopyQuotient (A := A)).map 0

/-! ## Morphisms of triangles and distinguished triangles -/

structure DgTriangleMorphism {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    {σ : DgShiftAxiom (A := A)} (T U : DgTriangle σ) where
  first : (DgHomotopyQuotient (A := A)).obj T.obj₁ ⟶
    (DgHomotopyQuotient (A := A)).obj U.obj₁
  second : (DgHomotopyQuotient (A := A)).obj T.obj₂ ⟶
    (DgHomotopyQuotient (A := A)).obj U.obj₂
  third : (DgHomotopyQuotient (A := A)).obj T.obj₃ ⟶
    (DgHomotopyQuotient (A := A)).obj U.obj₃
  comm₁ : T.mor₁ ≫ second = first ≫ U.mor₁
  comm₂ : T.mor₂ ≫ third = second ≫ U.mor₂
  comm₃ : T.mor₃ ≫ (DgShiftHomotopyFunctor σ 1).map first =
    third ≫ U.mor₃

structure DgTriangleIsomorphism {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    {σ : DgShiftAxiom (A := A)} (T U : DgTriangle σ) where
  e₁ : T.obj₁ ⟶ U.obj₁
  e₂ : T.obj₂ ⟶ U.obj₂
  e₃ : T.obj₃ ⟶ U.obj₃
  e₁_iso : DgHomotopyEquivalence e₁
  e₂_iso : DgHomotopyEquivalence e₂
  e₃_iso : DgHomotopyEquivalence e₃
  comm₁ : T.mor₁ ≫ (DgHomotopyQuotient (A := A)).map e₂ =
    (DgHomotopyQuotient (A := A)).map e₁ ≫ U.mor₁
  comm₂ : T.mor₂ ≫ (DgHomotopyQuotient (A := A)).map e₃ =
    (DgHomotopyQuotient (A := A)).map e₂ ≫ U.mor₂
  comm₃ : T.mor₃ ≫
      (DgShiftHomotopyFunctor σ 1).map
        ((DgHomotopyQuotient (A := A)).map e₁) =
    (DgHomotopyQuotient (A := A)).map e₃ ≫ U.mor₃

def DgTriangleIsomorphic {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    {σ : DgShiftAxiom (A := A)} (T U : DgTriangle σ) : Prop :=
  Nonempty (DgTriangleIsomorphism T U)

def DgDistinguishedTriangle {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    {σ : DgShiftAxiom (A := A)} (T : DgTriangle σ) : Prop :=
  ∃ (X Y Z : DgComplexObject (A := A))
    (S : DgAdmissibleShortExact X Y Z)
    (w : DgConnectingWitness (σ := σ) S),
    DgTriangleIsomorphic (DgAssociatedTriangle w) T

/-! ## The cone lemmas and the construction of the triangulation -/

theorem dgc_cone_functorial {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X₁ Y₁ X₂ Y₂ : DgComplexObject (A := A)}
    {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂)
    (h : (DgHomotopyQuotient (A := A)).map f₁ ≫
        (DgHomotopyQuotient (A := A)).map b =
      (DgHomotopyQuotient (A := A)).map a ≫
        (DgHomotopyQuotient (A := A)).map f₂) :
    Nonempty (DgTriangleMorphism
      (dgcMappingConeTriangle S f₁) (dgcMappingConeTriangle S f₂)) := by
  sorry

theorem dgc_cone_identity_null {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    (X : DgComplexObject (A := A)) :
    (DgHomotopyQuotient (A := A)).map
        (𝟙 (dgcCone S (𝟙 X))) =
      (0 : (DgHomotopyQuotient (A := A)).obj (dgcCone S (𝟙 X)) ⟶
        (DgHomotopyQuotient (A := A)).obj (dgcCone S (𝟙 X))) := by
  sorry

theorem dgc_homotopy_change {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X Y Z W : DgComplexObject (A := A)}
    {f : X ⟶ Y} {g : Z ⟶ W} (a : X ⟶ Z) (b : Y ⟶ W)
    (h : (DgHomotopyQuotient (A := A)).map f ≫
        (DgHomotopyQuotient (A := A)).map b =
      (DgHomotopyQuotient (A := A)).map a ≫
        (DgHomotopyQuotient (A := A)).map g) :
    (DgAdmissibleMonomorphism f →
      ∃ b' : Y ⟶ W,
        (DgHomotopyQuotient (A := A)).map b' =
          (DgHomotopyQuotient (A := A)).map b ∧ f ≫ b' = a ≫ g) ∧
    (DgAdmissibleEpimorphism g →
      ∃ a' : X ⟶ Z,
        (DgHomotopyQuotient (A := A)).map a' =
          (DgHomotopyQuotient (A := A)).map a ∧ a' ≫ g = f ≫ b) := by
  sorry

structure DgFactorization {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    {X Y : DgComplexObject (A := A)} (α : X ⟶ Y) where
  middle : DgComplexObject (A := A)
  inclusion : X ⟶ middle
  projection : middle ⟶ Y
  sectionMap : Y ⟶ middle
  inclusion_admissible : DgAdmissibleMonomorphism inclusion
  projection_inclusion : inclusion ≫ projection = α
  projection_section : sectionMap ≫ projection = 𝟙 Y
  section_projection_homotopic :
    (DgHomotopyQuotient (A := A)).map (projection ≫ sectionMap) =
      (DgHomotopyQuotient (A := A)).map (𝟙 middle)

theorem dgc_factor {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X Y : DgComplexObject (A := A)} (α : X ⟶ Y) :
    Nonempty (DgFactorization α) := by
  sorry

structure DgChain {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (n : ℕ) where
  obj : Fin (n + 1) → DgComplexObject (A := A)
  map : ∀ i : Fin n, obj ⟨i.1, by omega⟩ ⟶ obj ⟨i.1 + 1, by omega⟩

structure DgChainSplitWitness {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] {n : ℕ}
    (C : DgChain (A := A) n) where
  obj : Fin (n + 1) → DgComplexObject (A := A)
  vertical : ∀ i, obj i ⟶ C.obj i
  horizontal : ∀ i : Fin n,
    obj ⟨i.1, by omega⟩ ⟶ obj ⟨i.1 + 1, by omega⟩
  horizontal_admissible : ∀ i, DgAdmissibleMonomorphism (horizontal i)
  vertical_equivalence : ∀ i, DgHomotopyEquivalence (vertical i)
  squares_commute : ∀ i : Fin n,
    horizontal i ≫ vertical ⟨i.1 + 1, by omega⟩ =
      vertical ⟨i.1, by omega⟩ ≫ C.map i

theorem dgc_sequence_maps_split {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R) {n : ℕ}
    (C : DgChain (A := A) n) :
    Nonempty (DgChainSplitWitness C) := by
  sorry

theorem dgc_three_sequence {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ Z₁ Z₂ Z₃ : DgComplexObject (A := A)}
    {x₁ : X₁ ⟶ Y₁} {x₂ : X₂ ⟶ Y₂} {x₃ : X₃ ⟶ Y₃}
    {y₁ : Y₁ ⟶ Z₁} {y₂ : Y₂ ⟶ Z₂} {y₃ : Y₃ ⟶ Z₃}
    (middle : DgAdmissibleShortExact X₂ Y₂ Z₂)
    (b : Y₁ ⟶ Y₂) (b' : Y₂ ⟶ Y₃)
    (h₁ : (DgHomotopyQuotient (A := A)).map x₁ ≫
        (DgHomotopyQuotient (A := A)).map b = 0 ∧
      (DgHomotopyQuotient (A := A)).map b ≫
        (DgHomotopyQuotient (A := A)).map y₂ = 0)
    (h₂ : (DgHomotopyQuotient (A := A)).map x₂ ≫
        (DgHomotopyQuotient (A := A)).map b' = 0 ∧
      (DgHomotopyQuotient (A := A)).map b' ≫
        (DgHomotopyQuotient (A := A)).map y₃ = 0) :
    (DgHomotopyQuotient (A := A)).map (b ≫ b') = 0 := by
  sorry

theorem dgc_triangle_independent_of_splitting {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    {σ : DgShiftAxiom (A := A)}
    {X Y Z : DgComplexObject (A := A)}
    (S T : DgAdmissibleShortExact X Y Z)
    (hf : S.f = T.f) (hg : S.g = T.g)
    (wS : DgConnectingWitness (σ := σ) S)
    (wT : DgConnectingWitness (σ := σ) T) :
    Nonempty (DgTriangleIsomorphism
      (DgAssociatedTriangle wS) (DgAssociatedTriangle wT)) := by
  sorry

theorem dgc_restate_axiom_c {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X Y : DgComplexObject (A := A)} (f : X ⟶ Y) :
    DgDistinguishedTriangle (dgcConeTriangle S f) := by
  sorry

structure DgConeRotateWitness {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X Y Z : DgComplexObject (A := A)}
    (E : DgAdmissibleShortExact X Y Z)
    (w : DgConnectingWitness (σ := S.shifts) E) where
  zMinus : DgComplexObject (A := A)
  deltaMinus : zMinus ⟶ X
  shift_source : DgShiftObject S.shifts zMinus 1 = Z
  shifted_delta :
    (DgHomotopyQuotient (A := A)).map w.delta =
      eqToHom (congrArg (DgHomotopyQuotient (A := A)).obj
        shift_source).symm ≫
        (DgHomotopyQuotient (A := A)).map
          (DgShiftMap S.shifts deltaMinus 1)
  first_triangle : DgTriangle S.shifts
  first_obj₁ : first_triangle.obj₁ = zMinus
  first_obj₂ : first_triangle.obj₂ = X
  first_obj₃ : first_triangle.obj₃ = Y
  first_mor₁ : HEq first_triangle.mor₁
    ((DgHomotopyQuotient (A := A)).map deltaMinus)
  first_mor₂ : HEq first_triangle.mor₂
    ((DgHomotopyQuotient (A := A)).map E.f)
  first_mor₃ : HEq first_triangle.mor₃
    ((DgHomotopyQuotient (A := A)).map E.g)
  cone_triangle : DgTriangle S.shifts
  cone_triangle_eq : cone_triangle = dgcMappingConeTriangle S deltaMinus
  isomorphism : Nonempty (DgTriangleIsomorphism
    first_triangle cone_triangle)

theorem dgc_cone_rotate_isomorphism {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X Y Z : DgComplexObject (A := A)}
    (E : DgAdmissibleShortExact X Y Z)
    (w : DgConnectingWitness (σ := S.shifts) E) :
    Nonempty (DgConeRotateWitness S E w) := by
  sorry

theorem dgc_third_isomorphism {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {T U : DgTriangle S.shifts}
    (m : DgTriangleMorphism T U)
    (h₁ : IsIso m.first) (h₂ : IsIso m.second) : IsIso m.third := by
  sorry

/-! The preceding source lemma is most usefully consumed through the
following explicit cone-comparison interface. -/
structure DgConeHomotopyComparison {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X Y Z : DgComplexObject (A := A)}
    (E : DgAdmissibleShortExact X Y Z)
    (w : DgConnectingWitness (σ := S.shifts) E) where
  equivalence : dgcCone S E.f ⟶ Z
  inverse : Z ⟶ dgcCone S E.f
  equivalence_is_homotopy_equivalence :
    DgHomotopyEquivalence equivalence
  left_inverse :
    (DgHomotopyQuotient (A := A)).map (equivalence ≫ inverse) =
      (DgHomotopyQuotient (A := A)).map (𝟙 _) 
  right_inverse :
    (DgHomotopyQuotient (A := A)).map (inverse ≫ equivalence) =
      (DgHomotopyQuotient (A := A)).map (𝟙 _)
  triangle_isomorphism :
    Nonempty (DgTriangleIsomorphism
      (dgcMappingConeTriangle S E.f)
      (DgAssociatedTriangle w))

theorem dgc_cone_homotopy {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X Y Z : DgComplexObject (A := A)}
    (E : DgAdmissibleShortExact X Y Z)
    (w : DgConnectingWitness (σ := S.shifts) E) :
    Nonempty (DgConeHomotopyComparison S E w) := by
  sorry

theorem dgc_cone_homotopy_factorization {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X Y : DgComplexObject (A := A)} (α : X ⟶ Y)
    (F : DgFactorization α)
    {Z : DgComplexObject (A := A)}
    (E : DgAdmissibleShortExact X F.middle Z)
    (hf : E.f = F.inclusion)
    (w : DgConnectingWitness (σ := S.shifts) E) :
    Nonempty (DgTriangleIsomorphism
      (DgAssociatedTriangle w)
      (dgcMappingConeTriangle S α)) := by
  sorry

/-! ## TR1--TR4 and the final triangulation theorem -/

noncomputable def dgcRotateTriangle {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    {σ : DgShiftAxiom (A := A)} (T : DgTriangle σ) : DgTriangle σ where
  obj₁ := T.obj₂
  obj₂ := T.obj₃
  obj₃ := DgShiftObject σ T.obj₁ 1
  mor₁ := T.mor₂
  mor₂ := T.mor₃ ≫ eqToHom (σ.homotopyShift_obj 1 T.obj₁)
  mor₃ := eqToHom (σ.homotopyShift_obj 1 T.obj₁).symm ≫
    (-((DgShiftHomotopyFunctor σ 1).map T.mor₁))

/-- The octahedral configuration used for TR4.  The three displayed
triangles have first maps `f`, `f ≫ g`, and `g`, and the last triangle is the
triangle on the three cone objects. -/
structure DgTR4Witness {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X Y Z : DgComplexObject (A := A)}
    (f : X ⟶ Y) (g : Y ⟶ Z) where
  Q₁ : DgComplexObject (A := A)
  Q₂ : DgComplexObject (A := A)
  Q₃ : DgComplexObject (A := A)
  triangle₁ : DgTriangle S.shifts
  triangle₂ : DgTriangle S.shifts
  triangle₃ : DgTriangle S.shifts
  triangle₁_obj₁ : triangle₁.obj₁ = X
  triangle₁_obj₂ : triangle₁.obj₂ = Y
  triangle₁_obj₃ : triangle₁.obj₃ = Q₁
  triangle₂_obj₁ : triangle₂.obj₁ = X
  triangle₂_obj₂ : triangle₂.obj₂ = Z
  triangle₂_obj₃ : triangle₂.obj₃ = Q₂
  triangle₃_obj₁ : triangle₃.obj₁ = Y
  triangle₃_obj₂ : triangle₃.obj₂ = Z
  triangle₃_obj₃ : triangle₃.obj₃ = Q₃
  triangle₁_distinguished : DgDistinguishedTriangle triangle₁
  triangle₂_distinguished : DgDistinguishedTriangle triangle₂
  triangle₃_distinguished : DgDistinguishedTriangle triangle₃
  triangle₁_mor₁ : HEq triangle₁.mor₁
    ((DgHomotopyQuotient (A := A)).map f)
  triangle₂_mor₁ : HEq triangle₂.mor₁
    ((DgHomotopyQuotient (A := A)).map (f ≫ g))
  triangle₃_mor₁ : HEq triangle₃.mor₁
    ((DgHomotopyQuotient (A := A)).map g)
  first_morphism : DgTriangleMorphism triangle₁ triangle₂
  second_morphism : DgTriangleMorphism triangle₂ triangle₃
  cone_triangle : DgTriangle S.shifts
  cone_triangle_distinguished : DgDistinguishedTriangle cone_triangle
  cone_obj₁ : cone_triangle.obj₁ = Q₁
  cone_obj₂ : cone_triangle.obj₂ = Q₂
  cone_obj₃ : cone_triangle.obj₃ = Q₃

/-- The stronger TR4 witness for admissible monomorphisms records the four
admissible short exact sequences and the connecting-map formula for the last
one. -/
structure DgSplitTR4Witness {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X Y Z : DgComplexObject (A := A)}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    extends DgTR4Witness S f g where
  sequence₁ : DgAdmissibleShortExact X Y toDgTR4Witness.Q₁
  sequence₂ : DgAdmissibleShortExact X Z toDgTR4Witness.Q₂
  sequence₃ : DgAdmissibleShortExact Y Z toDgTR4Witness.Q₃
  sequence₄ : DgAdmissibleShortExact toDgTR4Witness.Q₁
    toDgTR4Witness.Q₂ toDgTR4Witness.Q₃
  sequence₁_f : sequence₁.f = f
  sequence₂_f : sequence₂.f = f ≫ g
  sequence₃_f : sequence₃.f = g
  w₁ : DgConnectingWitness (σ := S.shifts) sequence₁
  w₂ : DgConnectingWitness (σ := S.shifts) sequence₂
  w₃ : DgConnectingWitness (σ := S.shifts) sequence₃
  w₄ : DgConnectingWitness (σ := S.shifts) sequence₄
  triangle₁_sequence : toDgTR4Witness.triangle₁ = DgAssociatedTriangle w₁
  triangle₂_sequence : toDgTR4Witness.triangle₂ = DgAssociatedTriangle w₂
  triangle₃_sequence : toDgTR4Witness.triangle₃ = DgAssociatedTriangle w₃
  cone_triangle_sequence :
    toDgTR4Witness.cone_triangle = DgAssociatedTriangle w₄
  connecting_map_formula :
    w₄.delta = w₃.delta ≫ DgShiftMap S.shifts sequence₁.g 1

theorem dgc_analogue_tr4 {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    {X Y Z : DgComplexObject (A := A)}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : DgAdmissibleMonomorphism f)
    (hg : DgAdmissibleMonomorphism g) :
    Nonempty (DgSplitTR4Witness S f g) := by
  sorry

structure DgPretriangulatedData {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R]
    (S : DgABC R) where
  tr1_isomorphic : ∀ {T U : DgTriangle S.shifts},
    DgTriangleIsomorphic T U → DgDistinguishedTriangle T →
      DgDistinguishedTriangle U
  tr1_split : ∀ X : DgComplexObject (A := A),
    DgDistinguishedTriangle (dgcSplitTriangle S X)
  tr1_cone : ∀ {X Y : DgComplexObject (A := A)} (f : X ⟶ Y),
    DgDistinguishedTriangle (dgcMappingConeTriangle S f)
  tr2 : ∀ T : DgTriangle S.shifts,
    DgDistinguishedTriangle (dgcRotateTriangle T) ↔
      DgDistinguishedTriangle T
  tr3 : ∀ {T U : DgTriangle S.shifts},
    DgDistinguishedTriangle T → DgDistinguishedTriangle U →
    ∀ (a : (DgHomotopyQuotient (A := A)).obj T.obj₁ ⟶
        (DgHomotopyQuotient (A := A)).obj U.obj₁)
      (b : (DgHomotopyQuotient (A := A)).obj T.obj₂ ⟶
        (DgHomotopyQuotient (A := A)).obj U.obj₂),
      T.mor₁ ≫ b = a ≫ U.mor₁ →
      Nonempty (DgTriangleMorphism T U)

structure DgTriangulatedData {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (S : DgABC R)
    extends DgPretriangulatedData S where
  tr4 : ∀ {X Y Z : DgComplexObject (A := A)}
    (f : X ⟶ Y) (g : Y ⟶ Z),
    Nonempty (DgTR4Witness S f g)

theorem dgc_homotopy_category_pretriangulated {R : Type u}
    [CommRing R] [A : DifferentialGradedCategory R] (S : DgABC R) :
    Nonempty (DgPretriangulatedData S) := by
  sorry

theorem dgc_homotopy_category_triangulated {R : Type u}
    [CommRing R] [A : DifferentialGradedCategory R] (S : DgABC R) :
    Nonempty (DgTriangulatedData S) := by
  sorry

/-- The exact-functor interface used by the final source lemma.  The first
field is the quotient functor induced by the differential graded functor; the
other fields record shift compatibility and preservation of admissible short
exact sequences, which is the source-level reason distinguished triangles are
preserved. -/
structure DgExactFunctor {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] [B : DifferentialGradedCategory R]
    (SA : DgABC (A := A) R) (SB : DgABC (A := B) R)
    (F : DifferentialGradedFunctor A B) where
  homotopyFunctor : DgHomotopyCategory (A := A) ⥤
    DgHomotopyCategory (A := B)
  preserves_shift : ∀ (X : A.Obj),
    F.obj ((@DgShiftAxiom.shift R _ A (@DgABC.shifts R _ A SA) 1).obj X) =
      (@DgShiftAxiom.shift R _ B (@DgABC.shifts R _ B SB) 1).obj (F.obj X)
  maps_admissible_short_exact : ∀ {X Y Z : DgComplexObject (A := A)}
    (E : @DgAdmissibleShortExact R _ A X Y Z),
    Nonempty (@DgAdmissibleShortExact R _ B
      ((DifferentialGradedFunctor.onComplexes F).obj X)
      ((DifferentialGradedFunctor.onComplexes F).obj Y)
      ((DifferentialGradedFunctor.onComplexes F).obj Z))

theorem dgc_functor_between_ABC {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] [B : DifferentialGradedCategory R]
    (SA : @DgABC R _ A) (SB : @DgABC R _ B)
    (F : DifferentialGradedFunctor A B)
    (preserves_shift : ∀ (X : A.Obj),
      F.obj ((@DgShiftAxiom.shift R _ A (@DgABC.shifts R _ A SA) 1).obj X) =
        (@DgShiftAxiom.shift R _ B (@DgABC.shifts R _ B SB) 1).obj
          (F.obj X)) :
    Nonempty (@DgExactFunctor R _ A B SA SB F) := by
  sorry

/-! ## Source examples -/

/-- A sheaf of differential graded modules over a ringed space supplies the
abstract data required by the preceding theorem. -/
structure DgRingedSpaceExample (R : Type u) [CommRing R]
    [A : DifferentialGradedCategory R] where
  situation : DgABC R

theorem dgc_ringed_space_modules_triangulated {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (E : DgRingedSpaceExample R) :
    Nonempty (DgTriangulatedData E.situation) := by
  exact dgc_homotopy_category_triangulated E.situation

/-- A sheaf of differential graded modules on a ringed site has the same
abstract triangulated-category interface. -/
structure DgRingedSiteExample (R : Type u) [CommRing R]
    [A : DifferentialGradedCategory R] where
  situation : DgABC R

theorem dgc_ringed_site_modules_triangulated {R : Type u} [CommRing R]
    [A : DifferentialGradedCategory R] (E : DgRingedSiteExample R) :
    Nonempty (DgTriangulatedData E.situation) := by
  exact dgc_homotopy_category_triangulated E.situation

end Formalization.Books.Dga.Unit27
