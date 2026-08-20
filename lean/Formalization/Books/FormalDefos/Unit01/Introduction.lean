import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Grothendieck
import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Formal Deformation Theory, Chapter 1: Introduction

The source section is a roadmap for the formal deformation theory developed
in the rest of the book, but it also fixes the coefficient-ring setup and
names the main Schlessinger--Rim interfaces.  This file records those
interfaces in source order.  Later sections of the book supply the detailed
definitions of (H1)--(H4), (S1), (S2), and (RS); the introductory statements
below therefore expose those named conditions and theorem claims as typed
propositions without asserting them for arbitrary placeholder predicates.

The covariant cofibered convention is represented by Mathlib's
`Pseudofunctor.Grothendieck` construction.  Covariant representables use
Mathlib's `coyoneda`, rather than the contravariant Yoneda functor.

The introductory remarks that a versal object need not be a hull and that a
minimal versal object need not have a bijective tangent map are accounted for
by keeping `HasVersalFunctorObject`, `HasHull`, and the two miniversal
criteria separate.  The source points to examples in later sections rather
than giving a concrete counterexample in this section, so no standalone
existence-of-counterexample declaration is introduced here.  Likewise, the
remarks about minimal presentations and the practical converse from (H1)--(H2)
to (RS) are roadmap observations; the formal declarations record the precise
forward implications stated in the introduction.
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
structure LocalLambdaAlgebra (Λ k : Type u) [CommRing Λ] [Field k]
    (coefficientMap : Λ →+* k) where
  toCommRing : CommRingCat.{u}
  algebraMap : Λ →+* (toCommRing : Type u)
  isLocal : IsLocalRing (toCommRing : Type u)
  residueMap : (toCommRing : Type u) →+* k
  coefficient_compatibility : residueMap.comp algebraMap = coefficientMap
  residueKernel :
    RingHom.ker residueMap =
      @IsLocalRing.maximalIdeal (toCommRing : Type u) _ isLocal
  residueSurjective : Function.Surjective residueMap

namespace LocalLambdaAlgebra

variable {Λ k : Type u} [CommRing Λ] [Field k]
variable {coefficientMap : Λ →+* k}

/-- Local `Λ`-algebra maps preserving the chosen residue identifications. -/
structure Hom (A B : LocalLambdaAlgebra Λ k coefficientMap) where
  hom : (A.toCommRing : Type u) →+* (B.toCommRing : Type u)
  algebra_compatibility : hom.comp A.algebraMap = B.algebraMap
  residue_compatibility : B.residueMap.comp hom = A.residueMap

@[ext]
theorem Hom.ext {A B : LocalLambdaAlgebra Λ k coefficientMap} {f g : Hom A B}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (LocalLambdaAlgebra Λ k coefficientMap) where
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
def artinianLocalAlgebraProperty (Λ k : Type u) [CommRing Λ] [Field k]
    (coefficientMap : Λ →+* k) :
    ObjectProperty (LocalLambdaAlgebra Λ k coefficientMap) :=
  fun A => IsArtinianRing (A.toCommRing : Type u)

/-- The base category `C_Λ` of Artinian local `Λ`-algebras with residue field
`k`. -/
abbrev BaseCategory (Λ k : Type u) [CommRing Λ] [Field k]
    (coefficientMap : Λ →+* k) :=
  (artinianLocalAlgebraProperty (Λ := Λ) (k := k) coefficientMap).FullSubcategory

abbrev ClassicalBaseCategory {Λ k : Type u} [CommRing Λ] [Field k]
    (data : ClassicalCoefficientData Λ k) :=
  BaseCategory Λ k data.residueMap

/-- The surjective morphisms used in the infinitesimal lifting criteria on the
base category. -/
def BaseCategory.IsSurjective {Λ k : Type u} [CommRing Λ] [Field k]
    {coefficientMap : Λ →+* k} {B A : BaseCategory Λ k coefficientMap}
    (f : B ⟶ A) : Prop :=
  Function.Surjective f.hom.hom.toFun

/- The completion has the same local-algebra objects, restricted to the
   Noetherian adically complete ones. -/
def completeLocalAlgebraProperty (Λ k : Type u) [CommRing Λ] [Field k]
    (coefficientMap : Λ →+* k) :
    ObjectProperty (LocalLambdaAlgebra Λ k coefficientMap) :=
  fun A =>
    IsNoetherianRing (A.toCommRing : Type u) ∧
      IsAdicComplete
        (@IsLocalRing.maximalIdeal (A.toCommRing : Type u) _ A.isLocal)
        (A.toCommRing : Type u)

/-- The completion category `Ĉ_Λ`. -/
abbrev CompletionCategory (Λ k : Type u) [CommRing Λ] [Field k]
    (coefficientMap : Λ →+* k) :=
  (completeLocalAlgebraProperty (Λ := Λ) (k := k) coefficientMap).FullSubcategory

abbrev ClassicalCompletionCategory {Λ k : Type u} [CommRing Λ] [Field k]
    (data : ClassicalCoefficientData Λ k) :=
  CompletionCategory Λ k data.residueMap

/-- The base and completion categories attached to the generalized finite
coefficient-map setup. -/
abbrev CoefficientBaseCategory {Λ k : Type u} [CommRing Λ] [Field k]
    (data : CoefficientData Λ k) :=
  BaseCategory Λ k data.map

abbrev CoefficientCompletionCategory {Λ k : Type u} [CommRing Λ] [Field k]
    (data : CoefficientData Λ k) :=
  CompletionCategory Λ k data.map

/-- The inclusion of the Artinian objects into the complete objects is the
canonical full-subcategory map induced by the two object properties. -/
def baseCategoryToCompletion
    (Λ k : Type u) [CommRing Λ] [Field k]
    (coefficientMap : Λ →+* k) :
    BaseCategory Λ k coefficientMap ⥤ CompletionCategory Λ k coefficientMap :=
  ObjectProperty.ιOfLE (by
    intro A hA
    let _ : IsArtinianRing (A.toCommRing : Type u) := hA
    exact ⟨inferInstance, inferInstance⟩)

/-- The base category is strictly full in its completion category. -/
theorem baseCategory_strictlyFull_in_completion
    (Λ k : Type u) [CommRing Λ] [Field k]
    (coefficientMap : Λ →+* k) :
    Nonempty (baseCategoryToCompletion Λ k coefficientMap).FullyFaithful ∧
      ObjectProperty.IsClosedUnderIsomorphisms
        (artinianLocalAlgebraProperty Λ k coefficientMap) ∧
      ∀ X : CompletionCategory Λ k coefficientMap,
        (artinianLocalAlgebraProperty Λ k coefficientMap X.obj ↔
          ∃ Y : BaseCategory Λ k coefficientMap,
            Nonempty ((baseCategoryToCompletion Λ k coefficientMap).obj Y ≅ X)) := by
  have hartinian_of_iso {A B : LocalLambdaAlgebra Λ k coefficientMap}
      (e : A ≅ B) (hA : artinianLocalAlgebraProperty Λ k coefficientMap A) :
      artinianLocalAlgebraProperty Λ k coefficientMap B := by
    have hsurj : Function.Surjective e.hom.hom := by
      intro y
      refine ⟨e.inv.hom y, ?_⟩
      exact congrArg (fun f => f.hom y) e.inv_hom_id
    exact Function.Surjective.isArtinianRing (f := e.hom.hom) (H := hA) hsurj
  have hclosed :
      ObjectProperty.IsClosedUnderIsomorphisms
        (artinianLocalAlgebraProperty Λ k coefficientMap) :=
    ⟨hartinian_of_iso⟩
  refine ⟨⟨ObjectProperty.fullyFaithfulιOfLE _⟩, hclosed, ?_⟩
  intro X
  constructor
  · intro hX
    refine ⟨⟨X.obj, hX⟩, ?_⟩
    exact ⟨ObjectProperty.isoMk (P := completeLocalAlgebraProperty Λ k coefficientMap)
      (Iso.refl X.obj)⟩
  · intro h
    rcases h with ⟨Y, h⟩
    rcases h with ⟨e⟩
    have e' : Y.obj ≅ X.obj :=
      (completeLocalAlgebraProperty Λ k coefficientMap).ι.mapIso e
    exact hartinian_of_iso e' Y.property

/-- The pro-category of a category, using Mathlib's canonical ind/op
construction. -/
abbrev ProObjects (C : Type u) [Category.{w, u} C] :=
  (Ind Cᵒᵖ)ᵒᵖ

/-- A realization of the completion as a full, replete subcategory of the
pro-category of the base. -/
structure CompletionProObjectEmbedding
    (Λ k : Type u) [CommRing Λ] [Field k]
    (coefficientMap : Λ →+* k)
    (P : ObjectProperty (ProObjects (BaseCategory Λ k coefficientMap))) where
  inclusion : CompletionCategory Λ k coefficientMap ⥤
    ProObjects (BaseCategory Λ k coefficientMap)
  fullyFaithful : inclusion.FullyFaithful
  image_iff : ∀ Y,
    P Y ↔ ∃ X, Nonempty (inclusion.obj X ≅ Y)
theorem completion_strictlyFull_in_proObjects
    (Λ k : Type u) [CommRing Λ] [Field k]
    (coefficientMap : Λ →+* k) :
    ∃ P : ObjectProperty (ProObjects (BaseCategory Λ k coefficientMap)),
      ObjectProperty.IsClosedUnderIsomorphisms P ∧
        Nonempty (CompletionProObjectEmbedding Λ k coefficientMap P) := by
  sorry

/-! ## Representables and prorepresentability -/

/-- The covariant representable functor `Mor_D(R, -)`. -/
def covariantRepresentable {D : Type u} [Category.{u, u} D] (R : D) :
    D ⥤ Type u :=
  coyoneda.obj (op R)

/-- A functor on the base category is prorepresentable along an inclusion
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

def cofiberedFiberObjects {C : Type u} [Category.{u, u} C]
    (F : CofiberedCategory C) (A : C) : Type u :=
  F.obj (.mk A)

def cofiberedFiberArrows {C : Type u} [Category.{u, u} C]
    (F : CofiberedCategory C) (A : C) : Type u :=
  Σ X Y : (F.obj (.mk A) : Type u), (X ⟶ Y)

def cofiberedFiberArrowMap {C : Type u} [Category.{u, u} C]
    {F : CofiberedCategory C} {A B : C} (q : A ⟶ B) :
    cofiberedFiberArrows F A → cofiberedFiberArrows F B := by
  intro a
  exact ⟨(F.map q.toLoc).toFunctor.obj a.1,
    (F.map q.toLoc).toFunctor.obj a.2.1,
    (F.map q.toLoc).toFunctor.map a.2.2⟩

/-- A groupoid in functors on `C`, recorded together with the cofibered
groupoid that it presents.  The object and arrow functors are the source's
`U` and `R`; the displayed equivalences and their naturality keep them tied
to the fiberwise objects and arrows of the cofibered groupoid. -/
structure GroupoidInFunctors (C : Type u) [Category.{u, u} C] where
  cofibered : CofiberedCategory C
  groupoid : IsCofiberedInGroupoids cofibered
  objectFunctor : C ⥤ Type u
  arrowFunctor : C ⥤ Type u
  source : arrowFunctor ⟶ objectFunctor
  target : arrowFunctor ⟶ objectFunctor
  objectIdentification : ∀ A,
    objectFunctor.obj A ≃ cofiberedFiberObjects cofibered A
  arrowIdentification : ∀ A,
    arrowFunctor.obj A ≃ cofiberedFiberArrows cofibered A
  sourceIdentification : ∀ {A : C} (r : arrowFunctor.obj A),
    objectIdentification A (source.app A r) = (arrowIdentification A r).1
  targetIdentification : ∀ {A : C} (r : arrowFunctor.obj A),
    objectIdentification A (target.app A r) = (arrowIdentification A r).2.1
  objectIdentificationNaturality : ∀ {A B : C} (q : A ⟶ B)
      (x : objectFunctor.obj A),
    objectIdentification B (objectFunctor.map q x) =
      (cofibered.map q.toLoc).toFunctor.obj (objectIdentification A x)
  arrowIdentificationNaturality : ∀ {A B : C} (q : A ⟶ B)
      (x : arrowFunctor.obj A),
    arrowIdentification B (arrowFunctor.map q x) =
      cofiberedFiberArrowMap q (arrowIdentification A x)

/-- Morphisms of cofibered categories are pseudonatural transformations. -/
abbrev CofiberedMorphism {C : Type u} [Category.{u, u} C]
    (F G : CofiberedCategory C) := F ⟶ G

/-- A groupoid equivalent to the terminal one has an object and a unique
morphism between any two objects. -/
def IsTrivialGroupoid (G : Type u) [Category.{u, u} G] : Prop :=
  IsGroupoid G ∧ Nonempty G ∧
    ∀ X Y : G, Nonempty (X ⟶ Y) ∧ Subsingleton (X ⟶ Y)

/- A singleton-valued set is recorded by existence together with
   subsingletonhood.  This is the set-valued analogue of
   `IsTrivialGroupoid`. -/
def IsSingletonType (X : Type u) : Prop :=
  Nonempty X ∧ Subsingleton X

/- The source calls a set-valued functor with a singleton special fiber a
   predeformation functor. -/
def IsPredeformationFunctor {C : Type u} [Category.{u, u} C]
    (F : C ⥤ Type u) (k : C) : Prop :=
  IsSingletonType (F.obj k)

/-- The analogue of a singleton-valued deformation functor for a cofibered
category in groupoids. -/
def IsPredeformationCategory {C : Type u} [Category.{u, u} C]
    (F : CofiberedCategory C) (k : C) : Prop :=
  IsCofiberedInGroupoids F ∧ IsTrivialGroupoid (F.obj (.mk k))

/-- The isomorphism classes of objects in a category.  This is the
set-valued fiber used for the associated functor of isomorphism classes. -/
abbrev IsomorphismClasses (G : Type u) [Category.{u, u} G] :=
  Quotient (CategoryTheory.isIsomorphicSetoid G)

def associatedIsomorphismClassMap {C : Type u} [Category.{u, u} C]
    (F : CofiberedCategory C) {A B : C} (q : A ⟶ B) :
    IsomorphismClasses (F.obj (.mk A)) →
      IsomorphismClasses (F.obj (.mk B)) :=
  Quotient.map (fun X => (F.map q.toLoc).toFunctor.obj X) (by
    intro X Y h
    rcases h with ⟨e⟩
    exact ⟨(F.map q.toLoc).toFunctor.mapIso e⟩)

/-! The source's associated functor of isomorphism classes is canonical once
    the later cofibered-category pushforward API is in place.  This record
    exposes the functor, its fiberwise identifications, and the naturality
    obligation without duplicating that later construction here. -/
structure AssociatedIsomorphismClassFunctor {C : Type u}
    [Category.{u, u} C] (F : CofiberedCategory C) where
  toFunctor : C ⥤ Type u
  fiberIdentification : ∀ A,
    toFunctor.obj A ≃ IsomorphismClasses (F.obj (.mk A))
  identificationNaturality : ∀ {A B : C} (q : A ⟶ B) (x : toFunctor.obj A),
    fiberIdentification B (toFunctor.map q x) =
      associatedIsomorphismClassMap F q (fiberIdentification A x)

def canonicalAssociatedIsomorphismClassFunctor {C : Type u}
    [Category.{u, u} C] (F : CofiberedCategory C) :
    AssociatedIsomorphismClassFunctor F where
  toFunctor :=
    { obj A := IsomorphismClasses (F.obj (.mk A))
      map q := ↾(associatedIsomorphismClassMap F q)
      map_id := by
        intro X
        ext x
        change associatedIsomorphismClassMap F (𝟙 X) x = x
        refine Quotient.inductionOn x ?_
        intro Y
        apply Quotient.sound
        exact ⟨(Cat.Hom.toNatIso (F.mapId (.mk X))).app Y⟩
      map_comp := by
        intro X Y Z f g
        ext x
        change associatedIsomorphismClassMap F (f ≫ g) x =
          associatedIsomorphismClassMap F g (associatedIsomorphismClassMap F f x)
        refine Quotient.inductionOn x ?_
        intro W
        apply Quotient.sound
        exact ⟨(Cat.Hom.toNatIso (F.mapComp f.toLoc g.toLoc)).app W⟩ }
  fiberIdentification A := Equiv.refl _
  identificationNaturality := by
    intro A B q x
    rfl

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
  IsCofiberedInGroupoids F ∧ IsCofiberedInGroupoids G ∧
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

/- The representable cofibered groupoid is the discrete groupoid attached to
   the covariant representable `Mor(R, ι(-))`.  A later section introduces the
   separate set-valued presentation by groupoids in functors. -/
def representableCofiberedCategory {C D : Type u}
    [Category.{u, u} C] [Category.{u, u} D]
    (ι : C ⥤ D) (R : D) : CofiberedCategory C :=
  LocallyDiscrete.mkPseudofunctor
    (fun A => Cat.of (Discrete (R ⟶ ι.obj A)))
    (fun {A B} q =>
      (Discrete.functor
        (fun f : R ⟶ ι.obj A => Discrete.mk (f ≫ ι.map q))).toCatHom)
    (fun A => eqToIso (by
      apply Cat.Hom.ext
      apply Discrete.functor_ext
      intro X
      dsimp [Functor.toCatHom, CategoryTheory.Functor.id]
      simp))
    (fun f g => eqToIso (by
      apply Cat.Hom.ext
      apply Discrete.functor_ext
      intro X
      dsimp [Functor.toCatHom, CategoryTheory.Functor.comp]
      congr 1
      simp [Category.assoc]))
    (by
      intros
      simp [Bicategory.Strict.associator_eqToIso])
    (by
      intros
      simp [Bicategory.Strict.leftUnitor_eqToIso])
    (by
      intros
      simp [Bicategory.Strict.rightUnitor_eqToIso])

structure CofiberedRestrictionEquivalence {C D : Type u}
    [Category.{u, u} C] [Category.{u, u} D]
    (ι : C ⥤ D) (Fhat : CofiberedCategory D) (F : CofiberedCategory C) where
  map : restrictCofiberedCategory ι Fhat ⟶ F
  sourceGroupoid : IsCofiberedInGroupoids Fhat
  targetGroupoid : IsCofiberedInGroupoids F
  fiberwiseEquivalence : ∀ A : C,
    Functor.IsEquivalence (map.app (.mk A)).toFunctor

/-- A versal formal object together with the associated map from the
representable cofibered groupoid.  The source's canonical construction of
`associated` is supplied by the later completion and Yoneda sections; this
record keeps its typing and smoothness requirement explicit here. -/
structure VersalFormalObject {C D : Type u} [Category.{u, u} C]
    [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : CofiberedCategory C) (ι : C ⥤ D)
    (Fhat : CofiberedCategory D) (R : D)
    (associated : Fhat.obj (.mk R) →
      (representableCofiberedCategory ι R ⟶ F)) where
  completionRestriction : CofiberedRestrictionEquivalence ι Fhat F
  object : Fhat.obj (.mk R)
  smooth : IsSmoothCofiberedMorphism Surjective (associated object)

def HasVersalFormalObject {C D : Type u} [Category.{u, u} C]
    [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : CofiberedCategory C) (ι : C ⥤ D)
    (Fhat : CofiberedCategory D)
    (associated : ∀ R : D, Fhat.obj (.mk R) →
      (representableCofiberedCategory ι R ⟶ F)) : Prop :=
  ∃ R : D, Nonempty
    (VersalFormalObject Surjective F ι Fhat R (associated R))

/-! The next record is the typed part of the source's later formal-object
    theory that is needed to state minimality.  The completion source section
    supplies the actual type of formal objects, its morphisms, the underlying
    map of complete local rings, and its formal-object isomorphism relation. -/

structure FormalObjectTheory {C D : Type u} [Category.{u, u} C]
    [Category.{u, u} D] (F : CofiberedCategory C) (k₀ : C) where
  object : Type u
  formalCategory : Category object
  baseFunctor : @CategoryTheory.Functor object formalCategory D inferInstance
  versal : object → Prop
  surjective : ∀ {R' R : D}, (R' ⟶ R) → Prop
  predeformation : IsPredeformationCategory F k₀

def IsMinimalFormalObject {C D : Type u} [Category.{u, u} C]
    [Category.{u, u} D] {F : CofiberedCategory C} {k₀ : C}
    (T : FormalObjectTheory (D := D) F k₀) (ξ : T.object) : Prop :=
  letI := T.formalCategory
  ∀ (ξ' : T.object) (h : ξ' ⟶ ξ),
    T.surjective (T.baseFunctor.map h)

def IsMinimalVersalFormalObject {C D : Type u} [Category.{u, u} C]
    [Category.{u, u} D] {F : CofiberedCategory C} {k₀ : C}
    (T : FormalObjectTheory (D := D) F k₀) (ξ : T.object) : Prop :=
  T.versal ξ ∧ IsMinimalFormalObject T ξ

def HasMinimalVersalFormalObject {C D : Type u} [Category.{u, u} C]
    [Category.{u, u} D] {F : CofiberedCategory C} {k₀ : C}
    (T : FormalObjectTheory (D := D) F k₀) : Prop :=
  ∃ ξ : T.object, IsMinimalVersalFormalObject T ξ

def MinimalVersalObjectsUniqueUpToIsomorphism {C D : Type u}
    [Category.{u, u} C] [Category.{u, u} D]
    {F : CofiberedCategory C} {k₀ : C}
    (T : FormalObjectTheory (D := D) F k₀) : Prop :=
  letI := T.formalCategory
  ∀ {ξ η : T.object}, IsMinimalVersalFormalObject T ξ →
    IsMinimalVersalFormalObject T η → Nonempty (ξ ≅ η)

def minimal_versal_formal_object_exists_unique {C D : Type u}
    [Category.{u, u} C] [Category.{u, u} D]
    {F : CofiberedCategory C} {k₀ : C}
    (T : FormalObjectTheory (D := D) F k₀) : Prop :=
  (∃ ξ, T.versal ξ) →
    HasMinimalVersalFormalObject T ∧
      MinimalVersalObjectsUniqueUpToIsomorphism T

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

structure AssociatedFunctorSchlessingerData {C : Type u}
    [Category.{u, u} C] {F : CofiberedCategory C} {k₀ : C}
    {k : Type u} [Field k] {T Inf : TangentSpace k}
    (S : GroupoidSchlessingerConditions F k₀ k T Inf)
    (A : AssociatedIsomorphismClassFunctor F) where
  conditions : SchlessingerConditions A.toFunctor k T
  automorphismExtension : Prop

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

def versal_formal_object_exists_of_S1_S2_H3 {C D : Type u}
    [Category.{u, u} C] [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : CofiberedCategory C) (k₀ : C)
    (k : Type u) [Field k] (T Inf : TangentSpace k)
    (S : GroupoidSchlessingerConditions F k₀ k T Inf)
    (ι : C ⥤ D) (Fhat : CofiberedCategory D)
    (associated : ∀ R : D, Fhat.obj (.mk R) →
      (representableCofiberedCategory ι R ⟶ F)) : Prop :=
  IsPredeformationCategory F k₀ →
    SatisfiesS1S2 S →
      SchlessingerH3 T →
        HasVersalFormalObject Surjective F ι Fhat associated

def rimSchlessinger_implies_S1_S2 {C : Type u}
    [Category.{u, u} C] {F : CofiberedCategory C} {k₀ : C}
    {k : Type u} [Field k] {T Inf : TangentSpace k}
    (S : GroupoidSchlessingerConditions F k₀ k T Inf) : Prop :=
  S.RS → SatisfiesS1S2 S

def rimSchlessinger_implies_associated_functor_H1_H2 {C : Type u}
    [Category.{u, u} C] {F : CofiberedCategory C} {k₀ : C}
    {k : Type u} [Field k] {T Inf : TangentSpace k}
    (S : GroupoidSchlessingerConditions F k₀ k T Inf)
    (A : AssociatedIsomorphismClassFunctor F)
    (D : AssociatedFunctorSchlessingerData S A) : Prop :=
  IsPredeformationCategory F k₀ → S.RS → D.conditions.H1 ∧ D.conditions.H2

def associated_functor_H4_iff_automorphism_extension {C : Type u}
    [Category.{u, u} C] {F : CofiberedCategory C}
    {k₀ : C} {k : Type u} [Field k] {T Inf : TangentSpace k}
    (S : GroupoidSchlessingerConditions F k₀ k T Inf)
    (A : AssociatedIsomorphismClassFunctor F)
    (D : AssociatedFunctorSchlessingerData S A) : Prop :=
  S.RS →
    (D.conditions.H4 ↔ D.automorphismExtension)

/- The three alternatives in the miniversal theorem are recorded with
   explicit predicates for the differential and its derivation-orbit
   quotient.  Their concrete constructions belong to the later tangent-space
   and completion sections. -/
structure MiniversalCriterionData {C D : Type u}
    [Category.{u, u} C] [Category.{u, u} D]
    {F : CofiberedCategory C} {k₀ : C}
    {k : Type u} [Field k] {T Inf : TangentSpace k}
    (S : GroupoidSchlessingerConditions F k₀ k T Inf)
    (O : FormalObjectTheory (D := D) F k₀) where
  sourceTangent : O.object → TangentSpace k
  tangentMap : ∀ ξ : O.object,
    (sourceTangent ξ).carrier →ₗ[k] T.carrier
  tangentMapBijectiveOnDerivationOrbits : O.object → Prop
  residueExtensionSeparable : Prop

def tangentMapBijective {C D : Type u}
    [Category.{u, u} C] [Category.{u, u} D]
    {F : CofiberedCategory C} {k₀ : C}
    {k : Type u} [Field k] {T Inf : TangentSpace k}
    {S : GroupoidSchlessingerConditions F k₀ k T Inf}
    {O : FormalObjectTheory (D := D) F k₀}
    (Q : MiniversalCriterionData S O) (ξ : O.object) : Prop :=
  Function.Bijective (Q.tangentMap ξ)

def HasMinimalVersalWithBijectiveTangent {C D : Type u}
    [Category.{u, u} C] [Category.{u, u} D]
    {F : CofiberedCategory C} {k₀ : C}
    {k : Type u} [Field k] {T Inf : TangentSpace k}
    {S : GroupoidSchlessingerConditions F k₀ k T Inf}
  {O : FormalObjectTheory (D := D) F k₀}
    (Q : MiniversalCriterionData S O) : Prop :=
  ∃ ξ : O.object, IsMinimalVersalFormalObject O ξ ∧ tangentMapBijective Q ξ

def HasMinimalVersalWithBijectiveTangentOnOrbits {C D : Type u}
    [Category.{u, u} C] [Category.{u, u} D]
    {F : CofiberedCategory C} {k₀ : C}
    {k : Type u} [Field k] {T Inf : TangentSpace k}
    {S : GroupoidSchlessingerConditions F k₀ k T Inf}
    {O : FormalObjectTheory (D := D) F k₀}
    (Q : MiniversalCriterionData S O) : Prop :=
  ∃ ξ : O.object,
    IsMinimalVersalFormalObject O ξ ∧
      Q.tangentMapBijectiveOnDerivationOrbits ξ

def MiniversalFiniteConditions {C : Type u} [Category.{u, u} C]
    {F : CofiberedCategory C} {k₀ : C} {k : Type u} [Field k]
    {T Inf : TangentSpace k}
    (S : GroupoidSchlessingerConditions F k₀ k T Inf) : Prop :=
  SatisfiesS1S2 S ∧ hasFiniteTangentSpace T

def miniversal_formal_object_characterization {C D : Type u}
    [Category.{u, u} C] [Category.{u, u} D]
    {F : CofiberedCategory C} {k₀ : C} {k : Type u} [Field k]
    {T Inf : TangentSpace k}
    (S : GroupoidSchlessingerConditions F k₀ k T Inf)
    (O : FormalObjectTheory (D := D) F k₀)
    (Q : MiniversalCriterionData S O) : Prop :=
  IsPredeformationCategory F k₀ →
    ((HasMinimalVersalWithBijectiveTangent Q → MiniversalFiniteConditions S) ∧
      (MiniversalFiniteConditions S →
        HasMinimalVersalWithBijectiveTangentOnOrbits Q) ∧
      (Q.residueExtensionSeparable →
        (HasMinimalVersalWithBijectiveTangent Q ↔
          HasMinimalVersalWithBijectiveTangentOnOrbits Q) ∧
        (HasMinimalVersalWithBijectiveTangent Q ↔ MiniversalFiniteConditions S)))

/- The object and arrow types of the fibers of a groupoid in functors. -/
def groupoidFiberObjects {C : Type u} [Category.{u, u} C]
    (G : GroupoidInFunctors C) (A : C) : Type u :=
  G.objectFunctor.obj A

def groupoidFiberArrows {C : Type u} [Category.{u, u} C]
    (G : GroupoidInFunctors C) (A : C) : Type u :=
  G.arrowFunctor.obj A

/-- A prorepresentability certificate for the object and arrow functors of a
groupoid in functors, together with the cofibered groupoid obtained from its
quotient construction.  The source/target and composition laws remain in
`groupoid`; the quotient is the object that can be presented over `C`. -/
structure ProrepresentableGroupoidInFunctors {C D : Type u}
    [Category.{u, u} C] [Category.{u, u} D] (ι : C ⥤ D) where
  groupoid : GroupoidInFunctors C
  objectProrepresentable : IsProrepresentable ι groupoid.objectFunctor
  arrowProrepresentable : IsProrepresentable ι groupoid.arrowFunctor

/-- A smooth prorepresentable groupoid presentation of a cofibered groupoid.
Smoothness is imposed on the source and target maps of the groupoid in
functors, while the presentation itself is an equivalence of cofibered
groupoids. -/
structure SmoothProrepresentableGroupoidPresentation {C D : Type u}
    [Category.{u, u} C] [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : CofiberedCategory C) (ι : C ⥤ D) where
  presentation : ProrepresentableGroupoidInFunctors ι
  map : presentation.groupoid.cofibered ⟶ F
  sourceSmooth :
    IsSmoothSetValuedMorphism Surjective presentation.groupoid.source
  targetSmooth :
    IsSmoothSetValuedMorphism Surjective presentation.groupoid.target
  equivalence :
    Functor.IsEquivalence (Pseudofunctor.Grothendieck.map map)

def HasSmoothProrepresentableGroupoidPresentation {C D : Type u}
    [Category.{u, u} C] [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : CofiberedCategory C) (ι : C ⥤ D) : Prop :=
  Nonempty (SmoothProrepresentableGroupoidPresentation Surjective F ι)

def has_smooth_prorepresentable_groupoid_presentation_iff
    {C D : Type u} [Category.{u, u} C] [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : CofiberedCategory C) (k₀ : C) (ι : C ⥤ D)
    {k : Type u} [Field k] (T Inf : TangentSpace k)
    (S : GroupoidSchlessingerConditions F k₀ k T Inf) : Prop :=
    HasSmoothProrepresentableGroupoidPresentation Surjective F ι ↔
      IsDeformationCategory S ∧ hasFiniteTangentSpace T ∧
        hasFiniteInfinitesimalAutomorphismSpace Inf

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
    {k : Type u} [Field k] (TF : TangentSpace k) where
  versal : VersalFunctorObject Surjective F ι R
  representableTangent : TangentSpace k
  derivative : representableTangent.carrier →ₗ[k] TF.carrier
  derivative_bijective : Function.Bijective derivative

def HasHull {C D : Type u} [Category.{u, u} C] [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : C ⥤ Type u) (ι : C ⥤ D)
    {k : Type u} [Field k] (TF : TangentSpace k) : Prop :=
  ∃ R : D, Nonempty (HullWitness Surjective F ι R TF)

def HasVersalFunctorObject {C D : Type u} [Category.{u, u} C]
    [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : C ⥤ Type u) (ι : C ⥤ D) : Prop :=
  ∃ R : D, Nonempty (VersalFunctorObject Surjective F ι R)

/-! ## Introductory Schlessinger--Rim theorem interfaces -/

def functor_has_hull_iff_H123
    {C D : Type u} [Category.{u, u} C] [Category.{u, u} D]
    (Surjective : ∀ {B A : C}, (B ⟶ A) → Prop)
    (F : C ⥤ Type u) (k₀ : C) {k : Type u} [Field k]
    (ι : C ⥤ D) (TF : TangentSpace k)
    (S : SchlessingerConditions F k TF) : Prop :=
  IsPredeformationFunctor F k₀ →
    (HasHull Surjective F ι TF ↔ SatisfiesH123 S)

def functor_is_prorepresentable_iff_H1234
    {C D : Type u} [Category.{u, u} C] [Category.{u, u} D]
    (F : C ⥤ Type u) (k₀ : C) (ι : C ⥤ D)
    {k : Type u} [Field k] (TF : TangentSpace k)
    (S : SchlessingerConditions F k TF) : Prop :=
  IsPredeformationFunctor F k₀ →
    (IsProrepresentable ι F ↔ S.H1 ∧ S.H2 ∧ SchlessingerH3 TF ∧ S.H4)

end Formalization.Books.FormalDefos.Unit01
