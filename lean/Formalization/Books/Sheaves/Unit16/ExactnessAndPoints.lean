import Formalization.Books.Sheaves.Unit13.StalksOfPresheavesOfAlgebraicStructures
import Formalization.Books.Sheaves.Unit15.AlgebraicStructures
import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Stalks

/-!
# Sheaves on Spaces, Chapter 16: Exactness and points

The source span `books/sheaves.tex:1333--1457` is the section
`Exactness and points`.  The set-valued exactness criteria use Mathlib's
canonical sheaf and stalk APIs.  Subpresheaves are represented by
`CategoryTheory.Subfunctor`, and local surjectivity is Mathlib's canonical
`TopCat.Presheaf.IsLocallySurjective` predicate.

The final source lemma is stated for a category-valued sheaf and its
underlying sheaf of types.  The stalk maps are transported across the
canonical underlying-stalk isomorphisms from Chapter 13, so the hypothesis
that they are algebraic-structure morphisms has the source's precise type.
-/

namespace Formalization.Books.Sheaves.Unit16

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit05
open Formalization.Books.Sheaves.Unit13
open Formalization.Books.Sheaves.Unit15

universe u v

noncomputable section

/-! ## Points detect exactness for sheaves of sets -/

/-!
The following three statements are the three clauses of the source's first
lemma.  In each case the stalk map is the map induced by the canonical
`TopCat.Presheaf.stalkFunctor`.
-/

/-- A morphism of sheaves of sets is monic exactly when all stalk maps are injective. -/
theorem sheaf_mono_iff_stalk_injective
    {X : TopCat.{v}} {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) :
    Mono φ ↔
      ∀ x : X,
        Function.Injective
          ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ.hom) := by
  simpa only [mono_iff_injective] using (TopCat.Presheaf.mono_iff_stalk_mono φ)

/-- A morphism of sheaves of sets is epic exactly when all stalk maps are surjective. -/
theorem sheaf_epi_iff_stalk_surjective
    {X : TopCat.{v}} {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) :
    Epi φ ↔
      ∀ x : X,
        Function.Surjective
          ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ.hom) := by
  exact (TopCat.Sheaf.isLocallySurjective_iff_epi φ).symm.trans
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks φ.hom)

/-- A morphism of sheaves of sets is an isomorphism exactly when all stalk maps are bijective. -/
theorem sheaf_isIso_iff_stalk_bijective
    {X : TopCat.{v}} {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) :
    IsIso φ ↔
      ∀ x : X,
        Function.Bijective
          ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ.hom) := by
  simpa only [isIso_iff_bijective] using (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso φ)

/-! ## Injective, surjective, and subobject terminology -/

/-!
`Subfunctor` is Mathlib's literal family-of-subsets construction: its
`obj` fields are subsets of the ambient sections and its `map` field says
that restrictions preserve those subsets.  The relation below lets an
arbitrary presheaf be called a subpresheaf when it is naturally isomorphic
to such a subfunctor, which is invariant under the choice of section types.
-/

/-- A subpresheaf of a set-valued presheaf, represented by a subfunctor. -/
abbrev Subpresheaf {X : TopCat.{v}}
    (G : TopCat.Presheaf (Type v) X) : Type _ :=
  Subfunctor G

/-- A presheaf is a subpresheaf of another when it is isomorphic to a subfunctor of it. -/
def IsSubpresheaf {X : TopCat.{v}}
    (F G : TopCat.Presheaf (Type v) X) : Prop :=
  ∃ P : Subpresheaf G, Nonempty (F ≅ P.toFunctor)

/-- A subpresheaf whose source and ambient presheaves are sheaves is a subsheaf. -/
def IsSubsheaf {X : TopCat.{v}}
    (F G : TopCat.Presheaf (Type v) X) : Prop :=
  TopCat.Presheaf.IsSheaf F ∧ TopCat.Presheaf.IsSheaf G ∧ IsSubpresheaf F G

/-- A morphism of set-valued presheaves is injective on sections over every open. -/
def PresheafInjective {X : TopCat.{v}}
    {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) : Prop :=
  ∀ U : Opens X, Function.Injective (φ.app (op U))

/-- A morphism of set-valued presheaves is surjective on sections over every open. -/
def PresheafSurjective {X : TopCat.{v}}
    {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) : Prop :=
  ∀ U : Opens X, Function.Surjective (φ.app (op U))

/-- A morphism of sheaves of sets is injective in the source's sectionwise sense. -/
abbrev SheafInjective {X : TopCat.{v}}
    {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) : Prop :=
  PresheafInjective φ.hom

/-- A morphism of sheaves of sets is surjective in the source's local sense. -/
abbrev SheafSurjective {X : TopCat.{v}}
    {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) : Prop :=
  TopCat.Presheaf.IsLocallySurjective φ.hom

/-- The local-preimage formulation of the source's sheaf-surjectivity definition. -/
theorem sheafSurjective_iff_local_preimages
    {X : TopCat.{v}} {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) :
    SheafSurjective φ ↔
      ∀ (U : Opens X) (t : G.presheaf.obj (op U)), ∀ x ∈ U,
        ∃ (V : Opens X) (hVU : V ≤ U),
          (∃ s : F.presheaf.obj (op V),
            φ.hom.app (op V) s = G.presheaf.map (homOfLE hVU).op t) ∧ x ∈ V := by
  exact TopCat.Presheaf.isLocallySurjective_iff φ.hom

/-! ## Categorical epi/mono characterizations -/

/-- In the category of set-valued presheaves, epimorphisms are sectionwise surjective. -/
theorem presheaf_epi_iff_surjective
    {X : TopCat.{v}} {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) :
    Epi φ ↔ PresheafSurjective φ := by
  constructor
  · intro h U
    exact (epi_iff_surjective _).1 ((NatTrans.epi_iff_epi_app φ).1 h (op U))
  · intro h
    apply (NatTrans.epi_iff_epi_app φ).2
    intro U
    rw [epi_iff_surjective]
    exact h U.unop

/-- In the category of set-valued presheaves, monomorphisms are sectionwise injective. -/
theorem presheaf_mono_iff_injective
    {X : TopCat.{v}} {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) :
    Mono φ ↔ PresheafInjective φ := by
  constructor
  · intro h U
    exact (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app φ).1 h (op U))
  · intro h
    apply (NatTrans.mono_iff_mono_app φ).2
    intro U
    rw [mono_iff_injective]
    exact h U.unop

/-- In the category of sheaves of sets, epimorphisms are exactly the locally surjective maps. -/
theorem sheaf_epi_iff_surjective
    {X : TopCat.{v}} {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) :
    Epi φ ↔ SheafSurjective φ := by
  exact (TopCat.Sheaf.isLocallySurjective_iff_epi φ).symm

/-- In the category of sheaves of sets, monomorphisms are exactly the sectionwise injective maps. -/
theorem sheaf_mono_iff_injective
    {X : TopCat.{v}} {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) :
    Mono φ ↔ SheafInjective φ := by
  exact (Sheaf.Hom.mono_iff_presheaf_mono (Opens.grothendieckTopology X) (Type v) φ).trans
    (presheaf_mono_iff_injective φ.hom)

/-- Sectionwise injectivity of a sheaf map is equivalent to injectivity on all stalks. -/
theorem sheaf_injective_iff_stalk_injective
    {X : TopCat.{v}} {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) :
    SheafInjective φ ↔
      ∀ x : X,
        Function.Injective
          ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ.hom) := by
  exact (TopCat.Presheaf.app_injective_iff_stalkFunctor_map_injective φ.hom).symm

/-- Local surjectivity of a sheaf map is equivalent to surjectivity on all stalks. -/
theorem sheaf_surjective_iff_stalk_surjective
    {X : TopCat.{v}} {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) :
    SheafSurjective φ ↔
      ∀ x : X,
        Function.Surjective
          ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ.hom) := by
  exact TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks φ.hom

/-! ## Stalkwise algebraic-structure morphisms -/

/-!
For a category-valued sheaf, the stalk in `C` and the stalk of its
underlying presheaf of types are canonically isomorphic.  The next
definition transports an underlying stalk map to the categorical stalks.
-/

/-- The underlying sheaf of types associated to a `C`-valued sheaf. -/
noncomputable def underlyingSheaf
    {C : Type u} [Category.{v} C] (A : C ⥤ Type v)
    [AlgebraicStructureType C A] {X : TopCat.{v}}
    (F : TopCat.Sheaf C X) : TopCat.Sheaf (Type v) X :=
  ⟨underlyingPresheaf A F.presheaf,
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp A F.presheaf).mp F.property⟩

/-- The underlying sheaf morphism induced by a morphism of `C`-valued sheaves. -/
def underlyingSheafMorphism
    {C : Type u} [Category.{v} C] (A : C ⥤ Type v)
    [AlgebraicStructureType C A] {X : TopCat.{v}}
    {F G : TopCat.Sheaf C X} (φ : F ⟶ G) :
    underlyingSheaf A F ⟶ underlyingSheaf A G :=
  ⟨underlyingPresheafMorphism A φ.hom⟩

/-- The map between categorical stalks induced by an underlying sheaf map. -/
noncomputable def underlyingStalkMap
    {C : Type u} [Category.{v} C] (A : C ⥤ Type v)
    [AlgebraicStructureType C A] {X : TopCat.{v}}
    {F G : TopCat.Sheaf C X}
    (φ : underlyingSheaf A F ⟶ underlyingSheaf A G) (x : X) :
    A.obj (algebraicStalk F.presheaf x) →
      A.obj (algebraicStalk G.presheaf x) :=
  fun s =>
    (algebraicStalkUnderlyingIso A G.presheaf x).toEquiv.symm
      ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ.hom
        ((algebraicStalkUnderlyingIso A F.presheaf x).toEquiv s))

/-!
The displayed square in the source is represented by the following
section-to-stalks map and its naturality statement.  The codomain
`∀ x : U, ...` is the dependent product over the points of `U`.
-/

/-- The map from sections on an open to the product of the categorical stalks over its points. -/
noncomputable def algebraicSectionToStalks
    {C : Type u} [Category.{v} C] (A : C ⥤ Type v)
    [AlgebraicStructureType C A] {X : TopCat.{v}}
    (F : TopCat.Sheaf C X) (U : Opens X) :
    A.obj (F.presheaf.obj (op U)) →
      ∀ x : U, A.obj (algebraicStalk F.presheaf x.1) :=
  fun s x => A.map (algebraicStalkGerm F.presheaf U x.1 x.2) s

/-- Sections of a category-valued sheaf are determined by all their categorical stalks. -/
theorem algebraicSectionToStalks_injective
    {C : Type u} [Category.{v} C] (A : C ⥤ Type v)
    [AlgebraicStructureType C A] {X : TopCat.{v}}
    (F : TopCat.Sheaf C X) (U : Opens X) :
    Function.Injective (algebraicSectionToStalks A F U) := by
  intro s t h
  apply TopCat.Presheaf.section_ext (underlyingSheaf A F) U s t
  intro x hx
  have hx' := congrFun h ⟨x, hx⟩
  change A.map (algebraicStalkGerm F.presheaf U x hx) s =
    A.map (algebraicStalkGerm F.presheaf U x hx) t at hx'
  have hx'' := congrArg (fun z =>
    (algebraicStalkUnderlyingIso A F.presheaf x).hom z) hx'
  change (underlyingPresheaf A F.presheaf).germ U x hx s =
    (underlyingPresheaf A F.presheaf).germ U x hx t
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply] at hx''
  simp only [algebraicStalkGerm_underlying] at hx''
  exact hx''

/-- Naturality of the displayed section-to-stalks square. -/
theorem algebraicSectionToStalks_naturality
    {C : Type u} [Category.{v} C] (A : C ⥤ Type v)
    [AlgebraicStructureType C A] {X : TopCat.{v}}
    {F G : TopCat.Sheaf C X}
    (φ : underlyingSheaf A F ⟶ underlyingSheaf A G)
    (U : Opens X) (s : A.obj (F.presheaf.obj (op U))) :
    ∀ x : U,
      underlyingStalkMap A φ x.1
          (algebraicSectionToStalks A F U s x) =
        algebraicSectionToStalks A G U (φ.hom.app (op U) s) x := by
  intro x
  apply (algebraicStalkUnderlyingIso A G.presheaf x.1).toEquiv.injective
  change (algebraicStalkUnderlyingIso A G.presheaf x.1).toEquiv
      ((algebraicStalkUnderlyingIso A G.presheaf x.1).toEquiv.symm
        ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map φ.hom
          ((algebraicStalkUnderlyingIso A F.presheaf x.1).toEquiv
            (A.map (algebraicStalkGerm F.presheaf U x.1 x.2) s)))) =
    (algebraicStalkUnderlyingIso A G.presheaf x.1).toEquiv
      (A.map (algebraicStalkGerm G.presheaf U x.1 x.2)
        (φ.hom.app (op U) s))
  simp only [Iso.toEquiv_apply, Iso.toEquiv_symm_fun]
  change (ConcreteCategory.hom
      ((algebraicStalkUnderlyingIso A G.presheaf x.1).inv ≫
        (algebraicStalkUnderlyingIso A G.presheaf x.1).hom))
      ((ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map φ.hom))
        ((ConcreteCategory.hom (algebraicStalkUnderlyingIso A F.presheaf x.1).hom)
          ((ConcreteCategory.hom (A.map (algebraicStalkGerm F.presheaf U x.1 x.2))) s))) =
    (ConcreteCategory.hom (algebraicStalkUnderlyingIso A G.presheaf x.1).hom)
      ((ConcreteCategory.hom (A.map (algebraicStalkGerm G.presheaf U x.1 x.2)))
        ((ConcreteCategory.hom (φ.hom.app (op U))) s))
  rw [Iso.inv_hom_id]
  change (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map φ.hom))
      ((ConcreteCategory.hom (algebraicStalkUnderlyingIso A F.presheaf x.1).hom)
        ((ConcreteCategory.hom (A.map (algebraicStalkGerm F.presheaf U x.1 x.2))) s)) =
    (ConcreteCategory.hom (algebraicStalkUnderlyingIso A G.presheaf x.1).hom)
      ((ConcreteCategory.hom (A.map (algebraicStalkGerm G.presheaf U x.1 x.2)))
        ((ConcreteCategory.hom (φ.hom.app (op U))) s))
  have hF := congrArg (fun f => (ConcreteCategory.hom f) s)
    (algebraicStalkGerm_underlying A F.presheaf U x.1 x.2)
  rw [CategoryTheory.comp_apply] at hF
  rw [hF]
  change (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor (Type v) x.1).map φ.hom))
      ((ConcreteCategory.hom ((underlyingPresheaf A F.presheaf).germ U x.1 x.2)) s) =
    (ConcreteCategory.hom
      (A.map (algebraicStalkGerm G.presheaf U x.1 x.2) ≫
        (algebraicStalkUnderlyingIso A G.presheaf x.1).hom))
      ((ConcreteCategory.hom (φ.hom.app (op U))) s)
  rw [algebraicStalkGerm_underlying]
  change (TopCat.Presheaf.stalkFunctor (Type v) x.1).map φ.hom
      ((underlyingSheaf A F).presheaf.germ U x.1 x.2 s) =
    (underlyingSheaf A G).presheaf.germ U x.1 x.2 (φ.hom.app (op U) s)
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x.1 x.2 φ.hom s

/-- An underlying map is a morphism of sheaves of algebraic structures when it lifts to `C`. -/
def IsAlgebraicStructureSheafMorphism
    {C : Type u} [Category.{v} C] (A : C ⥤ Type v)
    [AlgebraicStructureType C A] {X : TopCat.{v}}
    {F G : TopCat.Sheaf C X}
    (φ : underlyingSheaf A F ⟶ underlyingSheaf A G) : Prop :=
  ∃ ψ : F ⟶ G, underlyingSheafMorphism A ψ = φ

/-- Stalkwise algebraic-structure morphisms lift an underlying sheaf map to `C`. -/
theorem isAlgebraicStructureSheafMorphism_of_stalkwise
    {C : Type u} [Category.{v} C] (A : C ⥤ Type v)
    [AlgebraicStructureType C A] {X : TopCat.{v}}
    {F G : TopCat.Sheaf C X}
    (φ : underlyingSheaf A F ⟶ underlyingSheaf A G)
    (hφ : ∀ x : X, IsAlgebraicStructureMorphism A (underlyingStalkMap A φ x)) :
    IsAlgebraicStructureSheafMorphism A φ := by
  unfold IsAlgebraicStructureSheafMorphism
  choose q hq using hφ
  have hU : ∀ U : Opens X,
      ∃ t : F.presheaf.obj (op U) ⟶ G.presheaf.obj (op U),
        A.map t = φ.hom.app (op U) := by
    intro U
    let D_G : Discrete U ⥤ C :=
      Discrete.functor (fun x : U => algebraicStalk G.presheaf x.1)
    let g : G.presheaf.obj (op U) ⟶
        pointwiseProductObject (F := A)
          (fun x : X => algebraicStalk G.presheaf x) U :=
      limit.lift D_G (Fan.mk _ fun x =>
        algebraicStalkGerm G.presheaf U x.1 x.2)
    let h : F.presheaf.obj (op U) ⟶
        pointwiseProductObject (F := A)
          (fun x : X => algebraicStalk G.presheaf x) U :=
      limit.lift D_G (Fan.mk _ fun x =>
        algebraicStalkGerm F.presheaf U x.1 x.2 ≫ q x.1)
    have hg : Function.Injective (A.map g) := by
      intro s t hst
      apply algebraicSectionToStalks_injective A G U
      apply funext
      intro x
      have hx := congrArg
        (fun z => A.map (limit.π D_G (Discrete.mk x)) z) hst
      change A.map (algebraicStalkGerm G.presheaf U x.1 x.2) s =
        A.map (algebraicStalkGerm G.presheaf U x.1 x.2) t
      simpa [g, ← ConcreteCategory.comp_apply, ← A.map_comp] using hx
    let eG := preservesLimitIso A D_G
    have hcoord : ∀ s : A.obj (F.presheaf.obj (op U)),
        A.map h s = A.map g (φ.hom.app (op U) s) := by
      intro s
      apply eG.toEquiv.injective
      apply Types.limit_ext
      intro j
      have hj₁ := congrArg (fun f => f (A.map h s))
        (preservesLimitIso_hom_π A D_G j)
      have hj₂ := congrArg (fun f => f (A.map g (φ.hom.app (op U) s)))
        (preservesLimitIso_hom_π A D_G j)
      calc
        limit.π (D_G ⋙ A) j (eG.hom (A.map h s)) =
            A.map (limit.π D_G j) (A.map h s) := by
              simpa only [ConcreteCategory.comp_apply] using hj₁
        _ = A.map (algebraicStalkGerm F.presheaf U j.as.1 j.as.2 ≫ q j.as.1) s := by
              rw [← ConcreteCategory.comp_apply, ← A.map_comp]
              dsimp [h]
              rw [limit.lift_π]
              rfl
        _ = underlyingStalkMap A φ j.as.1
              (algebraicSectionToStalks A F U s ⟨j.as.1, j.as.2⟩) := by
              rw [A.map_comp]
              change underlyingMap A (q j.as.1)
                  (underlyingMap A
                    (algebraicStalkGerm F.presheaf U j.as.1 j.as.2) s) = _
              rw [hq]
              rfl
        _ = algebraicSectionToStalks A G U
              (φ.hom.app (op U) s) ⟨j.as.1, j.as.2⟩ :=
              algebraicSectionToStalks_naturality A φ U s ⟨j.as.1, j.as.2⟩
        _ = A.map (limit.π D_G j)
              (A.map g (φ.hom.app (op U) s)) := by
              change A.map (algebraicStalkGerm G.presheaf U j.as.1 j.as.2)
                  (φ.hom.app (op U) s) = _
              symm
              change (ConcreteCategory.hom
                  (A.map g ≫ A.map (limit.π D_G j)))
                  (φ.hom.app (op U) s) = _
              rw [← A.map_comp]
              dsimp [g]
              rw [limit.lift_π]
              rfl
        _ = limit.π (D_G ⋙ A) j
              (eG.hom (A.map g (φ.hom.app (op U) s))) := by
              simpa only [ConcreteCategory.comp_apply] using hj₂.symm
    have himage : Set.range (A.map h) ⊆ Set.range (A.map g) := by
      rintro _ ⟨s, rfl⟩
      exact ⟨φ.hom.app (op U) s, (hcoord s).symm⟩
    obtain ⟨t, ht⟩ := factor_through_of_image_subset h g hg himage
    refine ⟨t, ?_⟩
    apply ConcreteCategory.hom_ext
    intro s
    apply hg
    calc
      A.map g (A.map t s) = A.map (t ≫ g) s := by
        rw [A.map_comp]
        rfl
      _ = A.map h s := by rw [ht]
      _ = A.map g (φ.hom.app (op U) s) := hcoord s
  choose ψapp hψapp using hU
  let ψhom : F.presheaf ⟶ G.presheaf :=
    { app := fun U => ψapp U.unop
      naturality := by
        intro U V f
        apply A.map_injective
        apply ConcreteCategory.hom_ext
        intro s
        have hn := congrArg (fun f => (ConcreteCategory.hom f) s)
          (φ.hom.naturality f)
        change A.map (F.presheaf.map f ≫ ψapp V.unop) s =
          A.map (ψapp U.unop ≫ G.presheaf.map f) s
        rw [A.map_comp, A.map_comp, hψapp, hψapp]
        exact hn }
  refine ⟨ObjectProperty.homMk ψhom, ?_⟩
  apply CategoryTheory.Sheaf.hom_ext
  change underlyingPresheafMorphism A ψhom = φ.hom
  apply NatTrans.ext
  exact funext (fun U => hψapp U.unop)

end

end Formalization.Books.Sheaves.Unit16
