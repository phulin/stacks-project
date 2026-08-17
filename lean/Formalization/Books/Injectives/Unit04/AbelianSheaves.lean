import Formalization.Books.Homology.Unit27.Injectives
import Formalization.Books.MoreAlgebra.Unit54.InjectiveAbelianGroups
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.SheafOfFunctions
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Injectives, Chapter 4: Abelian sheaves on a space

The source's construction is expressed with the canonical category of
`AddCommGrpCat`-valued sheaves.  The pointwise product sheaf and the
stalk/skyscraper adjunction are reused from the earlier Sheaves chapters.
The proposition-level injectivity arguments are theorem interfaces for the
prove stage; the object, product, and canonical map constructions have real
bodies here.
-/

namespace Formalization.Books.Injectives.Unit04

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Homology.Unit27

universe v

noncomputable section

/-! ## The canonical skyscraper interfaces -/

/-- The canonical functor sending an abelian group to its skyscraper sheaf.
The local classical choice packages Mathlib's decidability parameter. -/
noncomputable def abelianSkyscraperSheafFunctor {X : TopCat.{v}} (x : X) :
    AddCommGrpCat.{v} ⥤ TopCat.Sheaf AddCommGrpCat.{v} X := by
  classical
  exact skyscraperSheafFunctor x

/-- The stalk/skyscraper adjunction for abelian sheaves. -/
noncomputable def abelianStalkSkyscraperAdjunction {X : TopCat.{v}}
    (x : X) :
    (TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x) ⊣
      abelianSkyscraperSheafFunctor x := by
  letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
  exact stalkSkyscraperSheafAdjunction x

/-- The categorical stalk of an abelian sheaf at a point. -/
abbrev abelianSheafStalk {X : TopCat.{v}}
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) (x : X) : AddCommGrpCat.{v} :=
  (TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).obj F

/-! ## Injective envelopes of the stalks -/

/-- A chosen injective presentation of an abelian group.  This is the
canonical `EnoughInjectives.presentation` interface supplying the injective
object and monomorphism used in the pointwise construction. -/
noncomputable def abelianGroupInjectivePresentation (A : AddCommGrpCat.{v}) :
    InjectivePresentation A :=
  Classical.choice (EnoughInjectives.presentation A)

/-- The injective group `J(A)` chosen for an abelian group `A`. -/
noncomputable abbrev abelianGroupInjectiveObject (A : AddCommGrpCat.{v}) :
    AddCommGrpCat.{v} :=
  (abelianGroupInjectivePresentation A).J

/-- The canonical embedding `A ⟶ J(A)` associated to the chosen presentation. -/
noncomputable abbrev abelianGroupInjectiveMap (A : AddCommGrpCat.{v}) :
    A ⟶ abelianGroupInjectiveObject A :=
  (abelianGroupInjectivePresentation A).f

theorem abelianGroupInjectiveMap_mono (A : AddCommGrpCat.{v}) :
    Mono (abelianGroupInjectiveMap A) :=
  (abelianGroupInjectivePresentation A).mono

theorem abelianGroupInjectiveObject_injective (A : AddCommGrpCat.{v}) :
    Injective (abelianGroupInjectiveObject A) :=
  (abelianGroupInjectivePresentation A).injective

/-! ## The pointwise product sheaf -/

/-- The product of the fibres over the points of an open. -/
noncomputable def abelianSheafPointwiseProductObject {X : TopCat.{v}}
    (A : X → AddCommGrpCat.{v}) (U : Opens X) : AddCommGrpCat.{v} :=
  AddCommGrpCat.of (∀ x : U, A x)

/-- The presheaf whose sections over `U` are products of the fibres over the
points of `U`. -/
def abelianSheafPointwiseProductPresheaf {X : TopCat.{v}}
    (A : X → AddCommGrpCat.{v}) : TopCat.Presheaf AddCommGrpCat.{v} X where
  obj U := abelianSheafPointwiseProductObject A U.unop
  map {U V} f :=
    AddCommGrpCat.ofHom {
      toFun := fun s x => s (f.unop x)
      map_zero' := by
        ext x
        simp
      map_add' := by
        intro s t
        ext x
        simp }
  map_id U := by
    apply AddCommGrpCat.hom_ext
    ext s x
    rfl
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    ext s x
    rfl

/-- Restriction in the pointwise product presheaf is pointwise restriction. -/
@[simp]
theorem abelianSheafPointwiseProductPresheaf_restriction
    {X : TopCat.{v}} (A : X → AddCommGrpCat.{v})
    {U V : Opens X} (i : V ⟶ U) (s : ∀ x : U, A x) (x : V) :
    (abelianSheafPointwiseProductPresheaf A).map i.op s x =
    s (i x) :=
  rfl

/-- The pointwise product presheaf is a sheaf. -/
noncomputable def abelianSheafPointwiseProduct {X : TopCat.{v}}
    (A : X → AddCommGrpCat.{v}) :
    TopCat.Sheaf AddCommGrpCat.{v} X := by
  refine ⟨abelianSheafPointwiseProductPresheaf A, ?_⟩
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
    (CategoryTheory.forget AddCommGrpCat.{v})
    (abelianSheafPointwiseProductPresheaf A)).2
  change (TopCat.presheafToTypes X (fun x => A x)).IsSheaf
  exact TopCat.Presheaf.toTypes_isSheaf X (fun x => A x)

@[simp]
theorem abelianSheafPointwiseProduct_obj {X : TopCat.{v}}
    (A : X → AddCommGrpCat.{v}) (U : Opens X) :
    (abelianSheafPointwiseProduct A).presheaf.obj (op U) =
      abelianSheafPointwiseProductObject A U :=
  rfl

/-- The product of skyscraper sheaves with prescribed abelian-group fibres. -/
noncomputable def abelianSheafSkyscraperProduct {X : TopCat.{v}}
    (A : X → AddCommGrpCat.{v}) :
    TopCat.Sheaf AddCommGrpCat.{v} X :=
  limit (Discrete.functor (fun x : X =>
    (abelianSkyscraperSheafFunctor x).obj (A x)))

/- The source's fibrewise injective product, written as the product of the
   skyscraper sheaves `iₓ,* J(Fₓ)`. -/
noncomputable abbrev abelianSheafInjectiveProduct {X : TopCat.{v}}
    (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    TopCat.Sheaf AddCommGrpCat.{v} X :=
  abelianSheafSkyscraperProduct
    (fun x : X => abelianGroupInjectiveObject (abelianSheafStalk F x))

noncomputable def abelianSheafSkyscraperProduct_isProduct
    {X : TopCat.{v}} (A : X → AddCommGrpCat.{v}) :
    IsLimit (limit.cone (Discrete.functor (fun x : X =>
      (abelianSkyscraperSheafFunctor x).obj (A x)))) :=
  limit.isLimit _

/-- The product universal property of the source's injective product. -/
noncomputable def abelianSheafInjectiveProduct_isProduct
    {X : TopCat.{v}} (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    IsLimit (limit.cone (Discrete.functor (fun x : X =>
      (abelianSkyscraperSheafFunctor x).obj
        (abelianGroupInjectiveObject (abelianSheafStalk F x))))) :=
  abelianSheafSkyscraperProduct_isProduct
    (fun x : X => abelianGroupInjectiveObject (abelianSheafStalk F x))

/-- The pointwise description of the product of skyscraper sheaves. -/
theorem abelianSheafSkyscraperProduct_pointwise_formula
    {X : TopCat.{v}} (A : X → AddCommGrpCat.{v}) (U : Opens X) :
    Nonempty
      ((abelianSheafSkyscraperProduct A).presheaf.obj (op U) ≅
        abelianSheafPointwiseProductObject A U) := by
  sorry

/-! The pointwise product sheaf is the product of the skyscraper sheaves. -/
theorem abelianSheafPointwiseProduct_skyscraperProduct_iso
    {X : TopCat.{v}} (A : X → AddCommGrpCat.{v}) :
    Nonempty (abelianSheafPointwiseProduct A ≅
      abelianSheafSkyscraperProduct A) := by
  sorry

/-! The pointwise description of the selected injective product. -/
theorem abelianSheafInjectiveProduct_pointwise_formula
    {X : TopCat.{v}} (F : TopCat.Sheaf AddCommGrpCat.{v} X)
    (U : Opens X) :
    Nonempty
      ((abelianSheafInjectiveProduct F).presheaf.obj (op U) ≅
        abelianSheafPointwiseProductObject
          (fun x : X => abelianGroupInjectiveObject (abelianSheafStalk F x)) U) := by
  simpa [abelianSheafInjectiveProduct] using
    (abelianSheafSkyscraperProduct_pointwise_formula
      (fun x : X => abelianGroupInjectiveObject (abelianSheafStalk F x)) U)

/-! ## The canonical map into the product -/

/-- The map from a sheaf to the product of the skyscraper embeddings, with
component at `x` given by the unit of the stalk/skyscraper adjunction. -/
noncomputable def abelianSheafInjectiveEmbedding
    {X : TopCat.{v}} (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    F ⟶ abelianSheafInjectiveProduct F :=
  limit.lift
    (Discrete.functor (fun x : X =>
      (abelianSkyscraperSheafFunctor x).obj
        (abelianGroupInjectiveObject (abelianSheafStalk F x))))
    (Fan.mk F (fun x =>
      (abelianStalkSkyscraperAdjunction x).unit.app F ≫
        (abelianSkyscraperSheafFunctor x).map
          (abelianGroupInjectiveMap (abelianSheafStalk F x))))

theorem abelianSheafInjectiveEmbedding_projection
    {X : TopCat.{v}} (F : TopCat.Sheaf AddCommGrpCat.{v} X) (x : X) :
    abelianSheafInjectiveEmbedding F ≫
        limit.π (Discrete.functor (fun y : X =>
          (abelianSkyscraperSheafFunctor y).obj
            (abelianGroupInjectiveObject (abelianSheafStalk F y))))
          (Discrete.mk x) =
      (abelianStalkSkyscraperAdjunction x).unit.app F ≫
        (abelianSkyscraperSheafFunctor x).map
          (abelianGroupInjectiveMap (abelianSheafStalk F x)) := by
  unfold abelianSheafInjectiveEmbedding abelianSheafInjectiveProduct
    abelianSheafSkyscraperProduct
  rw [limit.lift_π]
  rfl

/-- The stalk/skyscraper Hom equivalence used to prove that each skyscraper
with injective fibre is injective. -/
noncomputable def abelianStalkSkyscraperHomEquiv
    {X : TopCat.{v}} (x : X) (F : TopCat.Sheaf AddCommGrpCat.{v} X)
    (I : AddCommGrpCat.{v}) :
    (abelianSheafStalk F x ⟶ I) ≃
      (F ⟶ (abelianSkyscraperSheafFunctor x).obj I) :=
  (abelianStalkSkyscraperAdjunction x).homEquiv F I

/-! ## Injectivity interfaces -/

/-- A skyscraper sheaf with injective stalk is injective. -/
theorem abelianSkyscraperSheaf_injective
    {X : TopCat.{v}} (x : X) (I : AddCommGrpCat.{v})
    (hI : Injective I) :
    Injective ((abelianSkyscraperSheafFunctor x).obj I) := by
  sorry

/-! The pointwise product of injective fibres is injective. -/
theorem abelianSheafPointwiseProduct_injective
    {X : TopCat.{v}} (A : X → AddCommGrpCat.{v})
    (hA : ∀ x : X, Injective (A x)) :
    Injective (abelianSheafPointwiseProduct A) := by
  sorry

/-! The product of skyscrapers with injective fibres is injective. -/
theorem abelianSheafSkyscraperProduct_injective
    {X : TopCat.{v}} (A : X → AddCommGrpCat.{v})
    (hA : ∀ x : X, Injective (A x)) :
    Injective (abelianSheafSkyscraperProduct A) := by
  have hSkyscraper : ∀ x : X, Injective
      ((abelianSkyscraperSheafFunctor x).obj (A x)) :=
    fun x => abelianSkyscraperSheaf_injective x (A x) (hA x)
  simpa [abelianSheafSkyscraperProduct] using
    (@product_injective
      (TopCat.Sheaf AddCommGrpCat.{v} X) _ _ X
      (fun x : X => (abelianSkyscraperSheafFunctor x).obj (A x)) _
      hSkyscraper)

/-- The product of the injective skyscraper sheaves is injective. -/
theorem abelianSheafInjectiveProduct_injective
    {X : TopCat.{v}} (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    Injective (abelianSheafInjectiveProduct F) := by
  apply abelianSheafSkyscraperProduct_injective
  intro x
  exact abelianGroupInjectiveObject_injective (abelianSheafStalk F x)

/-- The canonical map into the product is a monomorphism. -/
theorem abelianSheafInjectiveEmbedding_mono
    {X : TopCat.{v}} (F : TopCat.Sheaf AddCommGrpCat.{v} X) :
    Mono (abelianSheafInjectiveEmbedding F) := by
  sorry

/-! ## Enough injectives -/

/-- Abelian sheaves on a topological space have enough injectives. -/
theorem abelian_sheaves_have_enough_injectives {X : TopCat.{v}} :
    EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{v} X) := by
  sorry

/-- Abelian sheaves on a topological space have functorial injective
embeddings. -/
theorem abelian_sheaves_have_functorial_injective_embeddings
    {X : TopCat.{v}} :
    HasFunctorialInjectiveEmbeddings
      (C := TopCat.Sheaf AddCommGrpCat.{v} X) := by
  sorry

end

end Formalization.Books.Injectives.Unit04
