import Formalization.Books.Sites.Unit06.Sites
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Sites and Sheaves, Chapter 16: G-sets and morphisms

For a homomorphism `φ : G →* H`, Mathlib's `Action.res` is the canonical
restriction functor from `H`-actions to `G`-actions.  The remaining
declarations record the induced site/topos statements and the explicit
coinduced action described in the source.
-/

namespace Formalization.Books.Sites.Unit16

open CategoryTheory CategoryTheory.Limits
open Formalization.Books.Sites.Unit06

universe u

variable {G H : Type u} [Group G] [Group H]

/-! ## Restriction of actions and the associated sites -/

/-- The functor `u : 𝒯_H ⥤ 𝒯_G` attached to `φ : G →* H`. -/
abbrev restrictionFunctor (φ : G →* H) : GSet H ⥤ GSet G :=
  Action.res (Type u) φ

/-- Restriction of actions preserves finite limits. -/
theorem restrictionFunctor_preservesFiniteLimits (φ : G →* H) :
    PreservesFiniteLimits (restrictionFunctor φ) := by
  sorry

/-- The restriction functor is continuous for the jointly-surjective sites. -/
theorem restrictionFunctor_isContinuous (φ : G →* H) :
    Functor.IsContinuous (restrictionFunctor φ)
      (groupActionSite H).toGrothendieck (groupActionSite G).toGrothendieck := by
  sorry

/-! ## The sheaf-level direct image -/

/-- Sheaves of types on the site of `G`-sets. -/
abbrev GSetSheaf (G : Type u) [Group G] :=
  Sheaf (groupActionSite G).toGrothendieck (Type u)

/-- The direct-image functor on sheaves induced by restriction of actions. -/
noncomputable def toposDirectImage (φ : G →* H) :
    GSetSheaf G ⥤ GSetSheaf H := by
  letI : Functor.IsContinuous (restrictionFunctor φ)
      (groupActionSite H).toGrothendieck (groupActionSite G).toGrothendieck :=
    restrictionFunctor_isContinuous φ
  exact (restrictionFunctor φ).sheafPushforwardContinuous (Type u)
    (groupActionSite H).toGrothendieck (groupActionSite G).toGrothendieck

/-- The source's morphism of topoi, recorded by its inverse/direct-image adjunction. -/
theorem exists_associated_topos_morphism (φ : G →* H) :
    ∃ fInverse : GSetSheaf H ⥤ GSetSheaf G,
      Nonempty (fInverse ⊣ toposDirectImage φ) := by
  sorry

/-! ## The explicit direct image on G-sets -/

/-- The set of functions `H → S` satisfying `a (φ g * h) = g • a h`. -/
def EquivariantMap (φ : G →* H) (S : GSet G) : Type u :=
  {a : H → S.V // ∀ (g : G) (h : H), a (φ g * h) = S.ρ g (a h)}

/-- Right translation on equivariant maps, giving the H-action in the direct image. -/
def rightTranslate (φ : G →* H) (S : GSet G) (h : H)
    (a : EquivariantMap φ S) : EquivariantMap φ S :=
  ⟨fun h' => a.1 (h' * h), by
    intro g h'
    simpa [mul_assoc] using a.2 g (h' * h)⟩

/-- The right-translation action of `H` on the equivariant maps. -/
instance directImageMulAction (φ : G →* H) (S : GSet G) :
    MulAction H (EquivariantMap φ S) where
  smul h a := rightTranslate φ S h a
  one_smul a := by
    apply Subtype.ext
    funext h'
    change a.1 (h' * 1) = a.1 h'
    simp
  mul_smul h₁ h₂ a := by
    apply Subtype.ext
    funext h'
    change a.1 (h' * (h₁ * h₂)) = a.1 ((h' * h₁) * h₂)
    simp [mul_assoc]

/-- The H-set `Map_G(({}_H H)_φ, S)`. -/
def directImageObject (φ : G →* H) (S : GSet G) : GSet H :=
  Action.ofMulAction H (EquivariantMap φ S)

/-- Postcomposition sends equivariant maps to equivariant maps. -/
def directImageMap (φ : G →* H) {S T : GSet G} (f : S ⟶ T) :
    directImageObject φ S ⟶ directImageObject φ T :=
  { hom := ↾(fun a =>
      ⟨fun h => f.hom (a.1 h), by
        intro g h
        change f.hom (a.1 (φ g * h)) = T.ρ g (f.hom (a.1 h))
        rw [a.2 g h]
        simpa [ConcreteCategory.comp_apply] using
          ConcreteCategory.congr_hom (f.comm g) (a.1 h)⟩)
    comm := by
      intro h
      apply ConcreteCategory.hom_ext
      intro a
      apply Subtype.ext
      funext h'
      rfl }

/-- The direct-image functor on the categories of G-sets and H-sets. -/
def directImageFunctor (φ : G →* H) : GSet G ⥤ GSet H where
  obj S := directImageObject φ S
  map f := directImageMap φ f
  map_id S := by
    apply Action.Hom.ext
    apply ConcreteCategory.ext_apply
    intro a
    apply Subtype.ext
    funext h
    rfl
  map_comp f g := by
    apply Action.Hom.ext
    apply ConcreteCategory.ext_apply
    intro a
    apply Subtype.ext
    funext h
    rfl

/-- The displayed pointwise formula for the H-action on the direct image. -/
theorem directImageObject_action_formula (φ : G →* H) (S : GSet G)
    (h h' : H) (a : (directImageObject φ S).V) :
    (ConcreteCategory.hom ((directImageObject φ S).ρ h) a).1 h' = a.1 (h' * h) := by
  rfl

/-- The direct image is right adjoint to restriction. -/
theorem nonempty_restriction_directImage_adjunction (φ : G →* H) :
    Nonempty (restrictionFunctor φ ⊣ directImageFunctor φ) := by
  sorry

/-- A chosen adjunction witnessing the direct-image formula. -/
noncomputable def restriction_directImage_adjunction (φ : G →* H) :
    restrictionFunctor φ ⊣ directImageFunctor φ := by
  exact Classical.choice (nonempty_restriction_directImage_adjunction φ)

/-- The source's adjunction formula for morphisms of G-sets and H-sets. -/
noncomputable def restriction_directImage_homEquiv (φ : G →* H) (T : GSet H) (S : GSet G) :
    ((restrictionFunctor φ).obj T ⟶ S) ≃ (T ⟶ (directImageFunctor φ).obj S) :=
  (restriction_directImage_adjunction φ).homEquiv T S

/-! ## The inverse image and exactness -/

/-- Restriction leaves the underlying set unchanged. -/
theorem restrictionFunctor_obj_underlying (φ : G →* H) (T : GSet H) :
    ((restrictionFunctor φ).obj T).V = T.V := by
  rfl

/-- The restricted G-action is `g • x = φ(g) • x`. -/
theorem restrictionFunctor_obj_action (φ : G →* H) (T : GSet H) (g : G) (x : T.V) :
    ((restrictionFunctor φ).obj T).ρ g x = T.ρ (φ g) x := by
  rfl

/-- The inverse-image functor is exact, in the finite-limit sense. -/
theorem restrictionFunctor_exact (φ : G →* H) :
    PreservesFiniteLimits (restrictionFunctor φ) := by
  exact restrictionFunctor_preservesFiniteLimits φ

end Formalization.Books.Sites.Unit16
