import Formalization.Books.Homology.Unit27.Injectives
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Constructions

/-!
# Injectives, Chapter 3: G-modules

The source's `R-G`-modules are modules equipped with a continuous action of a
topological group, where the module is given the discrete topology.  The
bundled category below records the action by its homomorphism into linear
equivalences; this makes the requirement that the action be by `R`-linear maps
part of the object rather than an additional convention.
-/

noncomputable section

open CategoryTheory
open Formalization.Books.Homology.Unit27

universe u v

namespace Formalization.Books.Injectives.Unit03

section

variable (G : Type u) (R : Type v) [TopologicalSpace G] [Group G]
  [IsTopologicalGroup G] [Ring R]

/-! ## The category of discrete `R-G`-modules -/

/-- A discrete `R-G`-module: an `R`-module with a continuous left `G`-action
by `R`-linear maps. -/
structure RGModule where
  carrier : ModuleCat.{u} R
  action : G →* (carrier : Type u) ≃ₗ[R] (carrier : Type u)
  continuous_action :
    @Continuous (G × (carrier : Type u)) (carrier : Type u)
      (@instTopologicalSpaceProd G (carrier : Type u) inferInstance
        (⊥ : TopologicalSpace (carrier : Type u)))
      (⊥ : TopologicalSpace (carrier : Type u))
      (fun p : G × (carrier : Type u) => action p.1 p.2)

/-- Morphisms of `R-G`-modules are equivariant `R`-linear maps. -/
structure RGModuleHom (M N : RGModule G R) where
  hom : M.carrier ⟶ N.carrier
  equivariant : ∀ (g : G) (x : M.carrier),
    N.action g (hom x) = hom (M.action g x)

@[ext]
theorem RGModuleHom.ext
    {G : Type u} {R : Type v} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [Ring R]
    {M N : RGModule G R} {f g : RGModuleHom G R M N}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

variable {G R}

/-- The category structure on discrete `R-G`-modules. -/
instance : Category (RGModule G R) where
  Hom M N := RGModuleHom G R M N
  id M :=
    { hom := 𝟙 M.carrier
      equivariant := by
        intro g x
        simp }
  comp := fun {M N P} f₁ f₂ =>
    { hom := f₁.hom ≫ f₂.hom
      equivariant := by
        intro g x
        change P.action g (f₂.hom (f₁.hom x)) =
          f₂.hom (f₁.hom (M.action g x))
        rw [f₂.equivariant, f₁.equivariant] }
  id_comp f := by
    apply RGModuleHom.ext
    exact Category.id_comp f.hom
  comp_id f := by
    apply RGModuleHom.ext
    exact Category.comp_id f.hom
  assoc f₁ f₂ f₃ := by
    apply RGModuleHom.ext
    exact Category.assoc f₁.hom f₂.hom f₃.hom

/-! The source also calls the `R = ℤ` case the category of discrete
`G`-modules. -/

/-- The category of discrete `G`-modules, i.e. the `R = ℤ` specialization. -/
abbrev GModule (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] := RGModule G ℤ

/-! ## The source theorem -/

/-- The abelian category structure used by the canonical injective interface.

The kernels and cokernels are computed on the underlying modules, with the
equivariant action inherited from the given actions.  The construction is
standard; its proof is left as a theorem-stage interface. -/
instance rgModuleCategory_abelian : Abelian (RGModule G R) := by
  sorry

/-- The category of discrete `R-G`-modules has functorial injective embeddings. -/
theorem rgModule_has_functorial_injective_embeddings :
    HasFunctorialInjectiveEmbeddings (C := RGModule G R) := by
  sorry

/-- In particular, the category of discrete `G`-modules has functorial
injective embeddings. -/
theorem gModule_has_functorial_injective_embeddings :
    HasFunctorialInjectiveEmbeddings (C := GModule G) := by
  exact rgModule_has_functorial_injective_embeddings (G := G) (R := ℤ)

end

end Formalization.Books.Injectives.Unit03
