import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Formal Deformation Theory, Chapter 1: Introduction

The source section is a roadmap for the formal deformation theory developed
in the rest of the book, but it also fixes the coefficient-ring setup and
states the main Schlessinger--Rim interfaces.  This file records those
interfaces in source order.  Later sections of the book supply the detailed
definitions of (H1)--(H4), (S1), (S2), and (RS); the introductory theorem
statements below keep those named conditions as explicit fields so that the
roadmap remains usable before those later definitions are imported.

The covariant cofibered convention is represented by Mathlib's
`Pseudofunctor.Grothendieck` construction.  Covariant representables use
Mathlib's `coyoneda`, rather than the contravariant Yoneda functor.
-/

namespace Formalization.Books.FormalDefos.Unit01

open CategoryTheory
open CategoryTheory.Limits
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe u v w

/-! ## Coefficient rings and the base category -/

/-- The classical coefficient-ring situation: a complete Noetherian local
ring together with a chosen identification of its residue field with `k`.

The chosen residue identification is represented by its quotient map to `k`,
with the kernel and surjectivity equations making the identification explicit.
-/
structure ClassicalCoefficientData (Λ k : Type u) [CommRing Λ] [Field k] where
  isLocal : IsLocalRing Λ
  noetherian : IsNoetherianRing Λ
  complete :
    @IsAdicComplete Λ _ (@IsLocalRing.maximalIdeal Λ _ isLocal) Λ _ _
  residueMap : Λ →+* k
  residueKernel :
    RingHom.ker residueMap = @IsLocalRing.maximalIdeal Λ _ isLocal
  residueSurjective : Function.Surjective residueMap

/-- The generalized coefficient data used throughout the chapter. -/
structure CoefficientData (Λ k : Type u) [CommRing Λ] [Field k] where
  noetherian : IsNoetherianRing Λ
  map : Λ →+* k
  finite : map.Finite

/-- A local `Λ`-algebra with a chosen residue-field identification with `k`.

The underlying commutative ring is bundled by Mathlib's `CommRingCat`; the
two ring maps record the `Λ`-algebra structure and the chosen residue map.
Compatibility with both maps is part of the morphism interface below.
-/
structure LocalLambdaAlgebra (Λ k : Type u) [CommRing Λ] [Field k] where
  toCommRing : CommRingCat.{u}
  algebraMap : Λ →+* (toCommRing : Type u)
  isLocal : IsLocalRing (toCommRing : Type u)
  residueMap : (toCommRing : Type u) →+* k
  residueKernel :
    RingHom.ker residueMap =
      @IsLocalRing.maximalIdeal (toCommRing : Type u) _ isLocal
  residueSurjective : Function.Surjective residueMap

namespace LocalLambdaAlgebra

variable {Λ k : Type u} [CommRing Λ] [Field k]

/-- Local `Λ`-algebra maps preserving the chosen residue identifications. -/
structure Hom (A B : LocalLambdaAlgebra Λ k) where
  hom : (A.toCommRing : Type u) →+* (B.toCommRing : Type u)
  algebra_compatibility : hom.comp A.algebraMap = B.algebraMap
  residue_compatibility : B.residueMap.comp hom = A.residueMap

@[ext]
theorem Hom.ext {A B : LocalLambdaAlgebra Λ k} {f g : Hom A B}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (LocalLambdaAlgebra Λ k) where
  Hom := Hom
  id A :=
    { hom := RingHom.id _
      algebra_compatibility := by simp
      residue_compatibility := by simp }
  comp f g :=
    { hom := g.hom.comp f.hom
      algebra_compatibility := by
        rw [RingHom.comp_assoc, f.algebra_compatibility, g.algebra_compatibility]
      residue_compatibility := by
        rw [← RingHom.comp_assoc, g.residue_compatibility, f.residue_compatibility] }
  id_comp := by
    intro A B f
    apply Hom.ext
    ext x
    rfl
  comp_id := by
    intro A B f
    apply Hom.ext
    ext x
    rfl
  assoc := by
    intro A B C D f g h
    apply Hom.ext
    ext x
    rfl

end LocalLambdaAlgebra

/- Artinian local algebras form the base category. -/
def artinianLocalAlgebraProperty (Λ k : Type u) [CommRing Λ] [Field k] :
    ObjectProperty (LocalLambdaAlgebra Λ k) :=
  fun A => IsArtinianRing (A.toCommRing : Type u)

/-- The base category `C_Λ` of Artinian local `Λ`-algebras with residue field
`k`. -/
abbrev BaseCategory (Λ k : Type u) [CommRing Λ] [Field k] :=
  (artinianLocalAlgebraProperty (Λ := Λ) (k := k)).FullSubcategory

/- The completion has the same local-algebra objects, restricted to the
   Noetherian adically complete ones. -/
def completeLocalAlgebraProperty (Λ k : Type u) [CommRing Λ] [Field k] :
    ObjectProperty (LocalLambdaAlgebra Λ k) :=
  fun A =>
    IsNoetherianRing (A.toCommRing : Type u) ∧
      IsAdicComplete
        (@IsLocalRing.maximalIdeal (A.toCommRing : Type u) _ A.isLocal)
        (A.toCommRing : Type u)

/-- The completion category `Ĉ_Λ`. -/
abbrev CompletionCategory (Λ k : Type u) [CommRing Λ] [Field k] :=
  (completeLocalAlgebraProperty (Λ := Λ) (k := k)).FullSubcategory

/-- A convenient strict-fullness interface for the two inclusions appearing
in the source.  Full faithfulness records the full hom sets and `replete`
records closure under isomorphism in the ambient category. -/
def IsStrictlyFullEmbedding {C : Type u} {D : Type v}
    [Category.{w, u} C] [Category.{w, v} D]
    (ι : C ⥤ D) : Prop :=
  Nonempty ι.FullyFaithful ∧
    ∀ X : D,
      (∃ Y : C, Nonempty (ι.obj Y ≅ X)) →
        ∃ Y : C, Nonempty (X ≅ ι.obj Y)

/-- The base category is strictly full in its completion category. -/
theorem baseCategory_strictlyFull_in_completion
    (Λ k : Type u) [CommRing Λ] [Field k] :
    ∃ ι : BaseCategory Λ k ⥤ CompletionCategory Λ k,
      IsStrictlyFullEmbedding (C := BaseCategory Λ k)
        (D := CompletionCategory Λ k) ι := by
  sorry

/-- The pro-category of a category, using Mathlib's canonical ind/op
construction. -/
abbrev ProObjects (C : Type u) [Category.{w, u} C] :=
  (Ind Cᵒᵖ)ᵒᵖ

/-- The completion is strictly full in the pro-category of the base. -/
theorem completion_strictlyFull_in_proObjects
    (Λ k : Type u) [CommRing Λ] [Field k] :
    ∃ ι : CompletionCategory Λ k ⥤ ProObjects (BaseCategory Λ k),
      IsStrictlyFullEmbedding (C := CompletionCategory Λ k)
        (D := ProObjects (BaseCategory Λ k)) ι := by
  sorry

/-! ## Representables and prorepresentability -/

/-- The covariant representable functor `Mor_D(R, -)`. -/
def covariantRepresentable {D : Type u} [Category.{u, u} D] (R : D) :
    D ⥤ Type u :=
  coyoneda.obj (op R)

/-- A functor on a full base category is prorepresentable along an inclusion
`ι : C ⥤ D` when it is naturally isomorphic to the restriction of the
covariant representable attached to an object of `D`. -/
def IsProrepresentable {C D : Type u} [Category.{u, u} C]
    [Category.{u, u} D] (ι : C ⥤ D) (F : C ⥤ Type u) : Prop :=
  ∃ R : D, Nonempty (F ≅ ι ⋙ covariantRepresentable R)

/-! ## Cofibered categories, groupoids, and trivial fibers -/

/-- A category cofibered in the source's covariant convention, represented by
a pseudofunctor `C → Cat`. -/
abbrev CofiberedCategory (C : Type u) [Category.{u, u} C] :=
  Pseudofunctor (LocallyDiscrete C) Cat.{u, u}

/-- Restriction of a covariant cofibered category along a functor. -/
def restrictCofiberedCategory {C D : Type u} [Category.{u, u} C]
    [Category.{u, u} D] (ι : C ⥤ D) (F : CofiberedCategory D) :
    CofiberedCategory C :=
  Pseudofunctor.comp ι.toPseudofunctor F

/-- The fiber categories of a cofibered category are groupoids. -/
def IsCofiberedInGroupoids {C : Type u} [Category.{u, u} C]
    (F : CofiberedCategory C) : Prop :=
  ∀ A : C, IsGroupoid (F.obj (.mk A))

/-- A groupoid in functors on `C`, presented in the equivalent cofibered
groupoid convention. -/
structure GroupoidInFunctors (C : Type u) [Category.{u, u} C] where
  cofibered : CofiberedCategory C
  groupoid : IsCofiberedInGroupoids cofibered

/-- Morphisms of cofibered categories are pseudonatural transformations. -/
abbrev CofiberedMorphism {C : Type u} [Category.{u, u} C]
    (F G : CofiberedCategory C) := F ⟶ G

/-- A groupoid equivalent to the terminal one has an object and a unique
morphism between any two objects. -/
def IsTrivialGroupoid (G : Type u) [Category.{u, u} G] : Prop :=
  Nonempty G ∧ ∀ X Y : G, Subsingleton (X ⟶ Y)

/-- The analogue of a singleton-valued deformation functor for a cofibered
category in groupoids. -/
def IsPredeformationCategory {C : Type u} [Category.{u, u} C]
    (F : CofiberedCategory C) (k : C) : Prop :=
  IsCofiberedInGroupoids F ∧ IsTrivialGroupoid (F.obj (.mk k))

/-- The isomorphism classes of objects in a category.  This is the
set-valued fiber used for the associated functor of isomorphism classes. -/
def isomorphismClassSetoid (G : Type u) [Category.{u, u} G] : Setoid G where
  r X Y := Nonempty (X ≅ Y)
  iseqv :=
    { refl := fun X => ⟨Iso.refl X⟩
      symm := by
        intro X Y h
        rcases h with ⟨e⟩
        exact ⟨e.symm⟩
      trans := by
        intro X Y Z hXY hYZ
        rcases hXY with ⟨eXY⟩
        rcases hYZ with ⟨eYZ⟩
        exact ⟨eXY.trans eYZ⟩ }

abbrev IsomorphismClasses (G : Type u) [Category.{u, u} G] :=
  Quotient (isomorphismClassSetoid G)

/-! ## Smoothness and formal objects -/

/-- A morphism in a category over `C` lies over `q`.  The equality is written
with `eqToHom` so the definition works with explicitly identified fibers. -/
structure MorphismOver {E C : Type u} [Category.{u, u} E]
    [Category.{u, u} C] (p : E ⥤ C) {B A : C} (q : B ⟶ A)
    (X Y : E) where
  source_base : p.obj X = B
  target_base : p.obj Y = A
  hom : X ⟶ Y
  commutes :
    p.map hom = eqToHom source_base ≫ q ≫ eqToHom target_base.symm

/-- The infinitesimal object-lifting criterion for a morphism of
set-valued functors.  `Surjective` is supplied by the base category; for
`C_Λ` it is surjectivity of the underlying algebra homomorphism. -/
def IsSmoothSetValuedMorphism {C : Type u} [Category.{u, u} C]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    {F G : C ⥤ Type u} (η : F ⟶ G) : Prop :=
  ∀ {B A : C} (q : B ⟶ A), Surjective q →
    ∀ (y : G.obj B) (x : F.obj A),
      G.map q y = η.app A x →
        ∃ x' : F.obj B, F.map q x' = x ∧ η.app B x' = y

/-- The same lifting criterion for categories cofibered in groupoids.  The
total categories and their projections are Mathlib's Grothendieck
constructions, so the displayed source lifting diagram is represented by
`MorphismOver` witnesses. -/
def IsSmoothCofiberedMorphism {C : Type u} [Category.{u, u} C]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    {F G : CofiberedCategory C} (η : F ⟶ G) : Prop :=
  ∀ {B A : C} (q : B ⟶ A), Surjective q →
    ∀ (y : Pseudofunctor.Grothendieck G)
      (x : Pseudofunctor.Grothendieck F)
      (g : MorphismOver (Pseudofunctor.Grothendieck.forget G) q y
        ((Pseudofunctor.Grothendieck.map η).obj x)),
      ∃ (x' : Pseudofunctor.Grothendieck F)
        (f : MorphismOver (Pseudofunctor.Grothendieck.forget F) q x' x)
        (g' : MorphismOver (Pseudofunctor.Grothendieck.forget G) (𝟙 B)
          ((Pseudofunctor.Grothendieck.map η).obj x') y),
        g'.hom ≫ g.hom = (Pseudofunctor.Grothendieck.map η).map f.hom

/-- A versal formal object together with the associated map from the
representable cofibered groupoid.  The source's canonical construction of
`associated` is supplied by the later completion and Yoneda sections; this
record keeps its typing and smoothness requirement explicit here. -/
structure VersalFormalObject {C D : Type u} [Category.{u, u} C]
    [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : CofiberedCategory C) (ι : C ⥤ D)
    (Fhat : CofiberedCategory D) (R : D)
    (Representable : CofiberedCategory C)
    (associated : Fhat.obj (.mk R) → (Representable ⟶ F)) where
  object : Fhat.obj (.mk R)
  smooth : IsSmoothCofiberedMorphism Surjective (associated object)

/-! ## Tangent spaces and the named conditions -/

/-- A tangent-space carrier together with its `k`-vector-space structure. -/
structure TangentSpace (k : Type u) [Field k] where
  carrier : Type u
  addCommGroup : AddCommGroup carrier
  module : Module k carrier

instance {k : Type u} [Field k] (T : TangentSpace k) :
    AddCommGroup T.carrier := T.addCommGroup

instance {k : Type u} [Field k] (T : TangentSpace k) :
    Module k T.carrier := T.module

/-- Finite-dimensionality of a tangent space, using Mathlib's canonical
`Module.Finite` predicate. -/
def tangentSpaceFiniteDimensional {k : Type u} [Field k]
    (T : TangentSpace k) : Prop :=
  Module.Finite k T.carrier

/-- The introductory section names (H1)--(H4) without defining them.  Their
later source section fills these proposition-valued fields; (H3) is recorded
directly by finite-dimensionality of the supplied tangent space. -/
structure SchlessingerConditions {C : Type u} [Category.{u, u} C]
    (F : C ⥤ Type u) (k : Type u) [Field k] (T : TangentSpace k) where
  H1 : Prop
  H2 : Prop
  H4 : Prop

def SchlessingerH3 {k : Type u} [Field k] (T : TangentSpace k) : Prop :=
  tangentSpaceFiniteDimensional T

def SatisfiesH123 {C : Type u} [Category.{u, u} C]
    {F : C ⥤ Type u} {k : Type u} [Field k]
    {T : TangentSpace k} (S : SchlessingerConditions F k T) : Prop :=
  S.H1 ∧ S.H2 ∧ SchlessingerH3 T

/-! ## Groupoid conditions and presentations -/

/-- The named groupoid conditions used by the introductory Rim--Schlessinger
roadmap.  Their detailed diagrammatic definitions occur in the later source
sections; the tangent and infinitesimal-automorphism spaces are explicit here
so the finiteness assertions have their Mathlib meaning. -/
structure GroupoidSchlessingerConditions {C : Type u}
    [Category.{u, u} C] (F : CofiberedCategory C) (k₀ : C)
    (k : Type u) [Field k] (T Inf : TangentSpace k) where
  S1 : Prop
  S2 : Prop
  RS : Prop

def SatisfiesS1S2 {C : Type u} [Category.{u, u} C]
    {F : CofiberedCategory C} {k₀ : C} {k : Type u} [Field k]
    {T Inf : TangentSpace k}
    (S : GroupoidSchlessingerConditions F k₀ k T Inf) : Prop :=
  S.S1 ∧ S.S2

def IsDeformationCategory {C : Type u} [Category.{u, u} C]
    {F : CofiberedCategory C} {k₀ : C} {k : Type u} [Field k]
    {T Inf : TangentSpace k}
    (S : GroupoidSchlessingerConditions F k₀ k T Inf) : Prop :=
  IsPredeformationCategory F k₀ ∧ S.RS

def hasFiniteTangentSpace {k : Type u} [Field k] (T : TangentSpace k) : Prop :=
  tangentSpaceFiniteDimensional T

def hasFiniteInfinitesimalAutomorphismSpace {k : Type u} [Field k]
    (Inf : TangentSpace k) : Prop :=
  tangentSpaceFiniteDimensional Inf

/-- The object and arrow types of the fibers of a groupoid in functors. -/
def groupoidFiberObjects {C : Type u} [Category.{u, u} C]
    (G : GroupoidInFunctors C) (A : C) : Type u :=
  G.cofibered.obj (.mk A)

def groupoidFiberArrows {C : Type u} [Category.{u, u} C]
    (G : GroupoidInFunctors C) (A : C) : Type u :=
  Σ X Y : (G.cofibered.obj (.mk A) : Type u), (X ⟶ Y)

/-- A prorepresentability certificate for the object and arrow functors of a
groupoid in functors.  The fiber identifications tie the two set-valued
functors to the underlying groupoid; the source/target and composition laws
remain in `G`. -/
structure ProrepresentableGroupoidInFunctors {C D : Type u}
    [Category.{u, u} C] [Category.{u, u} D] (ι : C ⥤ D) where
  groupoid : GroupoidInFunctors C
  objectFunctor : C ⥤ Type u
  arrowFunctor : C ⥤ Type u
  objectIdentification : ∀ A,
    Nonempty (objectFunctor.obj A ≃ groupoidFiberObjects groupoid A)
  arrowIdentification : ∀ A,
    Nonempty (arrowFunctor.obj A ≃ groupoidFiberArrows groupoid A)
  objectProrepresentable : IsProrepresentable ι objectFunctor
  arrowProrepresentable : IsProrepresentable ι arrowFunctor

/-- A smooth prorepresentable groupoid presentation of a cofibered groupoid.
The equivalence is expressed on Grothendieck total categories, while
`smooth` uses the infinitesimal lifting predicate already defined above. -/
structure SmoothProrepresentableGroupoidPresentation {C D : Type u}
    [Category.{u, u} C] [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : CofiberedCategory C) (ι : C ⥤ D) where
  presentation : ProrepresentableGroupoidInFunctors ι
  map : presentation.groupoid.cofibered ⟶ F
  smooth : IsSmoothCofiberedMorphism Surjective map
  equivalence :
    Functor.IsEquivalence (Pseudofunctor.Grothendieck.map map)

def HasSmoothProrepresentableGroupoidPresentation {C D : Type u}
    [Category.{u, u} C] [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : CofiberedCategory C) (ι : C ⥤ D) : Prop :=
  Nonempty (SmoothProrepresentableGroupoidPresentation Surjective F ι)

/-! The following two records make the source's hull terminology explicit for
set-valued functors.  The derivative is supplied by the tangent-space theory
developed later in the book. -/
structure VersalFunctorObject {C D : Type u} [Category.{u, u} C]
    [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : C ⥤ Type u) (ι : C ⥤ D) (R : D) where
  map : (ι ⋙ covariantRepresentable R) ⟶ F
  smooth : IsSmoothSetValuedMorphism Surjective map

structure HullWitness {C D : Type u} [Category.{u, u} C]
    [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : C ⥤ Type u) (ι : C ⥤ D) (R : D)
    {k : Type u} [Field k] (TR TF : TangentSpace k) where
  versal : VersalFunctorObject Surjective F ι R
  derivative : TR.carrier →ₗ[k] TF.carrier
  derivative_bijective : Function.Bijective derivative

def HasHull {C D : Type u} [Category.{u, u} C] [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : C ⥤ Type u) (ι : C ⥤ D)
    {k : Type u} [Field k] (TR TF : TangentSpace k) : Prop :=
  ∃ R : D, Nonempty (HullWitness Surjective F ι R TR TF)

def HasVersalFunctorObject {C D : Type u} [Category.{u, u} C]
    [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : C ⥤ Type u) (ι : C ⥤ D) : Prop :=
  ∃ R : D, Nonempty (VersalFunctorObject Surjective F ι R)

/-! ## Introductory Schlessinger--Rim theorem interfaces -/

theorem functor_has_hull_iff_H123
    {C D : Type u} [Category.{u, u} C] [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : C ⥤ Type u) (k₀ : C) {k : Type u} [Field k]
    (hF : Nonempty (F.obj k₀) ∧ Subsingleton (F.obj k₀))
    (ι : C ⥤ D) (TR TF : TangentSpace k)
    (S : SchlessingerConditions F k TF) :
    HasHull Surjective F ι TR TF ↔ SatisfiesH123 S := by
  sorry

theorem functor_is_prorepresentable_iff_H1234
    {C D : Type u} [Category.{u, u} C] [Category.{u, u} D]
    (F : C ⥤ Type u) (k₀ : C) (ι : C ⥤ D)
    {k : Type u} [Field k] (TF : TangentSpace k)
    (S : SchlessingerConditions F k TF)
    (hF : Nonempty (F.obj k₀) ∧ Subsingleton (F.obj k₀)) :
    IsProrepresentable ι F ↔
      S.H1 ∧ S.H2 ∧ SchlessingerH3 TF ∧ S.H4 := by
  sorry

end Formalization.Books.FormalDefos.Unit01
