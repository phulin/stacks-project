import Formalization.Books.Homology.Unit29.AdjointFunctors
import Formalization.Books.MoreAlgebra.Unit55.InjectiveModules
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Ring.ULift
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Injectives, Chapter 6: Abelian presheaves on a category

An abelian presheaf is modeled by a functor to a universe-lifted copy of
`ModuleCat ℤ`.  This is
equivalent to the usual category of abelian-group-valued presheaves, while
retaining the canonical abelian and injective-object APIs used in the earlier
chapters.  Restriction along the discrete-object inclusion is precomposition;
the functor called `u` in the source is its right Kan extension.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open Formalization.Books.Categories.Unit23
open Formalization.Books.Homology.Unit27
open Formalization.Books.Homology.Unit29
open Formalization.Books.MoreAlgebra.Unit55

universe u v w

namespace Formalization.Books.Injectives.Unit06

/-! ## Abelian presheaves and restriction to objects -/

/-- The category of objects of `C`, regarded as a discrete category. -/
abbrev objectCategory (C : Type u) [Category.{v} C] := Discrete C

/-- A universe-lifted copy of `ℤ`, used so the explicit injective-envelope
construction is available at the universe of the presheaf values. -/
abbrev abelianScalar (C : Type u) [Category.{v} C] := ULift.{max u v} ℤ

/-- The inclusion of the discrete category of objects into `C`. -/
def objectInclusion {C : Type u} [Category.{v} C] : objectCategory C ⥤ C :=
  Discrete.functor (fun X : C => X)

/-- Abelian presheaves on `C`, represented by abelian groups as ℤ-modules. -/
abbrev AbelianPresheaf (C : Type u) [Category.{v} C] :=
  Cᵒᵖ ⥤ ModuleCat.{max u v} (abelianScalar C)

/-- Abelian presheaves on the discrete category of objects of `C`. -/
abbrev ObjectAbelianPresheaf (C : Type u) [Category.{v} C] :=
  (objectCategory C)ᵒᵖ ⥤ ModuleCat.{max u v} (abelianScalar C)

/-- Restriction of an abelian presheaf to the objects of the category. -/
noncomputable def presheafRestriction {C : Type u} [Category.{v} C] :
    AbelianPresheaf C ⥤ ObjectAbelianPresheaf C :=
  (Functor.whiskeringLeft ((objectCategory C)ᵒᵖ) Cᵒᵖ
      (ModuleCat.{max u v} (abelianScalar C))).obj
    (objectInclusion (C := C)).op

/-! ## The product formula for `u` -/

/-- The indexing type of all arrows with fixed target `U`. -/
abbrev incomingMorphismIndex {C : Type u} [Category.{v} C] (U : C) :=
  Σ X : C, X ⟶ U

/-- The product appearing in the source's explicit formula for `u A U`. -/
noncomputable def incomingProduct {C : Type u} [Category.{v} C]
    (A : ObjectAbelianPresheaf C) (U : C) :
      ModuleCat.{max u v} (abelianScalar C) :=
  ∏ᶜ fun p : incomingMorphismIndex U =>
    A.obj (Opposite.op (Discrete.mk p.1))

/-! ## The right adjoint `u` -/

/-- The source's functor `u`, defined canonically as a right Kan extension. -/
noncomputable def presheafRightKanExtension {C : Type u} [Category.{v} C] :
    ObjectAbelianPresheaf C ⥤ AbelianPresheaf C :=
  (objectInclusion (C := C)).op.ran

/-- The adjunction `v ⊣ u` from the source. -/
noncomputable def presheafRestrictionAdjunction {C : Type u} [Category.{v} C] :
    presheafRestriction (C := C) ⊣ presheafRightKanExtension (C := C) := by
  simpa [presheafRestriction, presheafRightKanExtension] using
    ((objectInclusion (C := C)).op.ranAdjunction
      (ModuleCat.{max u v} (abelianScalar C)))

/-- The right Kan extension has the source's product description at every object. -/
theorem presheafRightKanExtension_obj_iso_incomingProduct
    {C : Type u} [Category.{v} C] (A : ObjectAbelianPresheaf C) (U : C) :
    Nonempty
      (((presheafRightKanExtension (C := C)).obj A).obj (Opposite.op U) ≅
        incomingProduct A U) := by
  sorry

/-- The component of the right Kan extension counit at an incoming arrow. -/
noncomputable def presheafRightKanExtensionProjection
    {C : Type u} [Category.{v} C] (A : ObjectAbelianPresheaf C)
    {X U : C} (φ : X ⟶ U) :
    ((presheafRightKanExtension (C := C)).obj A).obj (Opposite.op U) ⟶
      A.obj (Opposite.op (Discrete.mk X)) :=
  ((objectInclusion (C := C)).op.ranObjObjIsoLimit A (Opposite.op U)).hom ≫
    limit.π
      (StructuredArrow.proj (Opposite.op U) (objectInclusion (C := C)).op ⋙ A)
      (StructuredArrow.mk (Y := Opposite.op (Discrete.mk X)) φ.op)

/-- Restriction along `g : V ⟶ U` reindexes the family by composition. -/
theorem presheafRightKanExtension_map_projection
    {C : Type u} [Category.{v} C] (A : ObjectAbelianPresheaf C)
    {X V U : C} (g : V ⟶ U) (ψ : X ⟶ V) :
    ((presheafRightKanExtension (C := C)).obj A).map g.op ≫
        presheafRightKanExtensionProjection A ψ =
      presheafRightKanExtensionProjection A (ψ ≫ g) := by
  sorry

/-! ## Exactness and the canonical maps -/

/-- Restriction is exact because it is precomposition. -/
theorem presheafRestriction_isExact {C : Type u} [Category.{v} C] :
    IsExact (presheafRestriction (C := C)) := by
  constructor
  · change PreservesFiniteLimits
      ((Functor.whiskeringLeft ((objectCategory C)ᵒᵖ) Cᵒᵖ
        (ModuleCat.{max u v} (abelianScalar C))).obj
          (objectInclusion (C := C)).op)
    infer_instance
  · change PreservesFiniteColimits
      ((Functor.whiskeringLeft ((objectCategory C)ᵒᵖ) Cᵒᵖ
        (ModuleCat.{max u v} (abelianScalar C))).obj
          (objectInclusion (C := C)).op)
    infer_instance

/-- The right Kan extension is exact, as asserted in the source. -/
theorem presheafRightKanExtension_isExact {C : Type u} [Category.{v} C] :
    IsExact (presheafRightKanExtension (C := C)) := by
  sorry

/-- Restriction preserves monomorphisms. -/
theorem presheafRestriction_preservesMonomorphisms
    {C : Type u} [Category.{v} C] :
    PreservesMonomorphisms (presheafRestriction (C := C)) := by
  change PreservesMonomorphisms
    ((Functor.whiskeringLeft ((objectCategory C)ᵒᵖ) Cᵒᵖ
      (ModuleCat.{max u v} (abelianScalar C))).obj
        (objectInclusion (C := C)).op)
  infer_instance

instance presheafRestriction_additive
    {C : Type u} [Category.{v} C] :
    (presheafRestriction (C := C)).Additive := by
  change ((Functor.whiskeringLeft ((objectCategory C)ᵒᵖ) Cᵒᵖ
    (ModuleCat.{max u v} (abelianScalar C))).obj
      (objectInclusion (C := C)).op).Additive
  infer_instance

/-- The canonical map `v u A ⟶ A`, called the canonical surjection in the source. -/
noncomputable def presheafCanonicalCounit
    {C : Type u} [Category.{v} C] (A : ObjectAbelianPresheaf C) :
    (presheafRestriction (C := C)).obj
          ((presheafRightKanExtension (C := C)).obj A) ⟶ A :=
  (presheafRestrictionAdjunction (C := C)).counit.app A

/-- The canonical map `B ⟶ u v B`, called the canonical injection in the source. -/
noncomputable def presheafCanonicalUnit
    {C : Type u} [Category.{v} C] (B : AbelianPresheaf C) :
    B ⟶ (presheafRightKanExtension (C := C)).obj
      ((presheafRestriction (C := C)).obj B) :=
  (presheafRestrictionAdjunction (C := C)).unit.app B

theorem presheafCanonicalCounit_epi
    {C : Type u} [Category.{v} C] (A : ObjectAbelianPresheaf C) :
    Epi (presheafCanonicalCounit A) := by
  sorry

theorem presheafCanonicalUnit_mono
    {C : Type u} [Category.{v} C] (B : AbelianPresheaf C) :
    Mono (presheafCanonicalUnit B) := by
  sorry

/-! ## The adjunction hom equivalence -/

/-- The source's displayed hom-set equality, as the canonical adjunction equivalence. -/
def presheafHomEquiv {C : Type u} [Category.{v} C]
    (B : AbelianPresheaf C) (A : ObjectAbelianPresheaf C) :
    (B ⟶ (presheafRightKanExtension (C := C)).obj A) ≃
      ((presheafRestriction (C := C)).obj B ⟶ A) :=
  ((presheafRestrictionAdjunction (C := C)).homEquiv B A).symm

/-! ## Objectwise enough injectives -/

/-- The objectwise injective envelope functor from More on Algebra, Chapter 55. -/
noncomputable def objectPresheafInjectiveFunctor
    {C : Type u} [Category.{v} C] :
    ObjectAbelianPresheaf C ⥤ ObjectAbelianPresheaf C :=
  (Functor.whiskeringRight ((objectCategory C)ᵒᵖ)
      (ModuleCat.{max u v} (abelianScalar C))
      (ModuleCat.{max u v} (abelianScalar C))).obj
    (injectiveEnvelopeFunctor (abelianScalar C))

/-- The objectwise unit supplied by the arrow-valued injective-envelope
construction from More on Algebra, Chapter 55. -/
noncomputable def moduleInjectiveUnit {R : Type w} [CommRing R] :
    𝟭 (ModuleCat.{w} R) ⟶ injectiveEnvelopeFunctor R where
  app M := ((injectiveEmbeddingFunctor R).obj M).hom
  naturality := by
    intro X Y f
    change f ≫ ((injectiveEmbeddingFunctor R).obj Y).hom =
      ((injectiveEmbeddingFunctor R).obj X).hom ≫
        (injectiveEnvelopeFunctor R).map f
    exact ((injectiveEmbeddingFunctor R).map f).w

/-- The objectwise unit `A ⟶ J(A)`. -/
noncomputable def objectPresheafInjectiveUnit
    {C : Type u} [Category.{v} C] :
    𝟭 (ObjectAbelianPresheaf C) ⟶ objectPresheafInjectiveFunctor (C := C) := by
  simpa [objectPresheafInjectiveFunctor, Functor.whiskeringRight_obj_id] using
    ((Functor.whiskeringRight ((objectCategory C)ᵒᵖ)
      (ModuleCat.{max u v} (abelianScalar C))
      (ModuleCat.{max u v} (abelianScalar C))).map
        (moduleInjectiveUnit (R := abelianScalar C)))

/-- A functorial injective embedding in the objectwise presheaf category. -/
noncomputable def objectPresheafInjectiveEmbedding
    {C : Type u} [Category.{v} C] :
    ObjectAbelianPresheaf C ⥤ Arrow (ObjectAbelianPresheaf C) where
  obj A := Arrow.mk ((objectPresheafInjectiveUnit (C := C)).app A)
  map f := Arrow.homMk f
    ((objectPresheafInjectiveFunctor (C := C)).map f)
    (w := by simpa using (objectPresheafInjectiveUnit (C := C)).naturality f)
  map_id A := by
    apply Arrow.hom_ext <;> simp
  map_comp f g := by
    apply Arrow.hom_ext <;> simp

theorem objectPresheafInjectiveEmbedding_left
    {C : Type u} [Category.{v} C] :
    objectPresheafInjectiveEmbedding (C := C) ⋙ Arrow.leftFunc =
      𝟭 (ObjectAbelianPresheaf C) := by
  exact CategoryTheory.Functor.ext (fun A => rfl) (fun A B f => by rfl)

theorem objectPresheafInjectiveEmbedding_mono
    {C : Type u} [Category.{v} C] (A : ObjectAbelianPresheaf C) :
    Mono ((objectPresheafInjectiveEmbedding (C := C)).obj A).hom := by
  sorry

theorem objectPresheafInjectiveEmbedding_injective
    {C : Type u} [Category.{v} C] (A : ObjectAbelianPresheaf C) :
    Injective ((objectPresheafInjectiveEmbedding (C := C)).obj A).right := by
  sorry

theorem objectPresheaves_have_functorial_injective_embeddings
    {C : Type u} [Category.{v} C] :
    HasFunctorialInjectiveEmbeddings (C := ObjectAbelianPresheaf C) := by
  refine ⟨objectPresheafInjectiveEmbedding (C := C),
    objectPresheafInjectiveEmbedding_left, ?_, ?_⟩
  · exact objectPresheafInjectiveEmbedding_mono
  · exact objectPresheafInjectiveEmbedding_injective

theorem objectPresheaves_have_enough_injectives
    {C : Type u} [Category.{v} C] :
    EnoughInjectives (ObjectAbelianPresheaf C) := by
  sorry

/-! ## The construction `B ↦ u J(v B)` -/

/-- The right Kan extension preserves injective objects by the adjunction. -/
theorem presheafRightKanExtension_preservesInjectiveObjects
    {C : Type u} [Category.{v} C] :
    Functor.PreservesInjectiveObjects (presheafRightKanExtension (C := C)) := by
  let hMono : PreservesMonomorphisms (presheafRestriction (C := C)) :=
    presheafRestriction_preservesMonomorphisms
  exact @Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    _ _ _ _ _ _ (presheafRestrictionAdjunction (C := C)) hMono

instance presheafRightKanExtension_additive
    {C : Type u} [Category.{v} C] :
    (presheafRightKanExtension (C := C)).Additive := by
  sorry

/-- The unit followed by the image of the objectwise injective embedding. -/
noncomputable def presheafInjectiveEmbedding
    {C : Type u} [Category.{v} C] (B : AbelianPresheaf C) :
    B ⟶ (presheafRightKanExtension (C := C)).obj
      ((objectPresheafInjectiveFunctor (C := C)).obj
        ((presheafRestriction (C := C)).obj B)) :=
  presheafCanonicalUnit B ≫
    (presheafRightKanExtension (C := C)).map
      ((objectPresheafInjectiveUnit (C := C)).app
        ((presheafRestriction (C := C)).obj B))

theorem presheafInjectiveEmbedding_mono
    {C : Type u} [Category.{v} C] (B : AbelianPresheaf C) :
    Mono (presheafInjectiveEmbedding B) := by
  sorry

theorem presheafInjectiveEmbedding_target_injective
    {C : Type u} [Category.{v} C] (B : AbelianPresheaf C) :
    Injective ((presheafRightKanExtension (C := C)).obj
      ((objectPresheafInjectiveFunctor (C := C)).obj
        ((presheafRestriction (C := C)).obj B)) : AbelianPresheaf C) := by
  sorry

/-! ## Functorial injective embeddings -/

theorem abelianPresheaves_have_functorial_injective_embeddings
    {C : Type u} [Category.{v} C] :
    HasFunctorialInjectiveEmbeddings (C := AbelianPresheaf C) := by
  exact adjoint_functorial_injective_embeddings
    (presheafRightKanExtension (C := C)) (presheafRestriction (C := C))
    (presheafRestrictionAdjunction (C := C))
    (presheafRestriction_preservesMonomorphisms (C := C))
    (objectPresheaves_have_enough_injectives (C := C))
    (fun B hB => by sorry)
    (objectPresheaves_have_functorial_injective_embeddings (C := C))

end Formalization.Books.Injectives.Unit06
