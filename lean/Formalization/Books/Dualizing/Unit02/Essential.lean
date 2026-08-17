import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Subobject

/-!
# Dualizing Complexes, Chapter 2: Essential surjections and injections

The source defines essential extensions and essential surjections in an
abelian category, records their elementary closure properties, and then
specializes the extension notion to modules.  Categorical subobjects,
intersections, images, kernels, and cokernels below are the canonical
Mathlib constructions.
-/

namespace Formalization.Books.Dualizing.Unit02

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

universe u v w

noncomputable section

/-! ## Essential morphisms in an abelian category -/

/-- A monomorphism is an essential extension when every nonzero subobject of
the target meets its image nontrivially. -/
def EssentialExtension {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B : 𝒜} (f : A ⟶ B) : Prop :=
  ∃ (hf : Mono f),
    letI := hf
    ∀ P : Subobject B, P ≠ ⊥ → Subobject.mk f ⊓ P ≠ ⊥

/-- An epimorphism is essential when no proper subobject of its source maps
onto the target. -/
def EssentialSurjection {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B : 𝒜} (f : A ⟶ B) : Prop :=
  Epi f ∧ ∀ P : Subobject A, P ≠ ⊤ → (Subobject.«exists» f).obj P ≠ ⊤

/-! The four assertions in the source's first elementary lemma. -/

/-- Essential extensions are transitive. -/
theorem essentialExtension_trans {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B D : 𝒜} (f : A ⟶ B) (g : B ⟶ D)
    (hf : EssentialExtension f) (hg : EssentialExtension g) :
    EssentialExtension (f ≫ g) := by
  sorry

/-- Pulling an essential extension back along a monomorphism gives an
essential intersection extension. -/
noncomputable def essentialIntersectionArrow
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B D : 𝒜} (f : A ⟶ B) [Mono f] (g : D ⟶ B) [Mono g] :
    ((Subobject.mk f ⊓ Subobject.mk g : Subobject B) : 𝒜) ⟶ D :=
  Subobject.ofLEMk (Subobject.mk f ⊓ Subobject.mk g) g (by simp)

/-- The intersection of an essential subobject with any subobject is
essential in that subobject. -/
theorem essentialExtension_intersection
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B D : 𝒜} (f : A ⟶ B) [Mono f] (g : D ⟶ B) [Mono g]
    (hf : EssentialExtension f) :
    EssentialExtension (essentialIntersectionArrow f g) := by
  sorry

/-- Essential surjections are closed under composition. -/
theorem essentialSurjection_comp {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B D : 𝒜} (f : A ⟶ B) (g : B ⟶ D)
    (hf : EssentialSurjection f) (hg : EssentialSurjection g) :
    EssentialSurjection (f ≫ g) := by
  sorry

/-! The quotient appearing in the fourth assertion. -/

/-- The quotient of `B` by the image of the kernel of `g` under `f`.
The cokernel of the displayed composite is canonically the quotient by that
image. -/
abbrev quotientByImageOfKernel
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B D : 𝒜} (f : A ⟶ B) (g : A ⟶ D) : 𝒜 :=
  cokernel (kernel.ι g ≫ f)

/-- The quotient projection `B → B / f(ker(g))`. -/
noncomputable def quotientByImageOfKernelProjection
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B D : 𝒜} (f : A ⟶ B) (g : A ⟶ D) :
    B ⟶ quotientByImageOfKernel f g :=
  cokernel.π (kernel.ι g ≫ f)

/-- The map induced from `g : A → D` to the quotient by `f(ker(g))`. -/
noncomputable def essentialQuotientMap
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B D : 𝒜} (f : A ⟶ B) (g : A ⟶ D) [Epi g] :
    D ⟶ quotientByImageOfKernel f g :=
  Abelian.epiDesc g (f ≫ quotientByImageOfKernelProjection f g) (by
    dsimp [quotientByImageOfKernelProjection]
    simpa only [Category.assoc] using (cokernel.condition (kernel.ι g ≫ f)))

/-- The quotient map in the fourth assertion of the source's lemma is an
essential surjection. -/
theorem essentialSurjection_quotient
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {A B D : 𝒜} (f : A ⟶ B) (g : A ⟶ D)
    (hf : EssentialSurjection f) [Epi g] :
    EssentialSurjection (essentialQuotientMap f g) := by
  sorry

/-! ## Filtered unions of essential extensions -/

/-- A compatible system of essential injections from `M` into a filtered
diagram of modules. -/
def CompatibleEssentialSystem
    {R : Type u} [Ring R] {I : Type v} [SmallCategory I] [IsFiltered I]
    (M : ModuleCat.{w} R) (F : I ⥤ ModuleCat.{w} R)
    (u : ∀ i : I, M ⟶ F.obj i) : Prop :=
  (∀ i : I, EssentialExtension (u i)) ∧
    ∀ {i j : I} (f : i ⟶ j), u i ≫ F.map f = u j

/-- The map from `M` to a chosen filtered-colimit cocone point induced by a
compatible system. -/
noncomputable def filteredColimitMap
    {R : Type u} [Ring R] {I : Type v} [SmallCategory I] [IsFiltered I]
    (M : ModuleCat.{w} R) (F : I ⥤ ModuleCat.{w} R)
    (t : Cocone F) (u : ∀ i : I, M ⟶ F.obj i) : M ⟶ t.pt :=
  let i : I := IsFiltered.nonempty.some
  u i ≫ t.ι.app i

/-- Every stage gives the same map to the filtered-colimit cocone point. -/
theorem filteredColimitMap_eq
    {R : Type u} [Ring R] {I : Type v} [SmallCategory I] [IsFiltered I]
    (M : ModuleCat.{w} R) (F : I ⥤ ModuleCat.{w} R)
    (t : Cocone F) (u : ∀ i : I, M ⟶ F.obj i)
    (hu : CompatibleEssentialSystem M F u) (i : I) :
    u i ≫ t.ι.app i = filteredColimitMap M F t u := by
  sorry

/-- A filtered colimit of a compatible system of essential extensions is an
essential extension. -/
theorem essentialExtension_filteredColimit
    {R : Type u} [Ring R] {I : Type v} [SmallCategory I] [IsFiltered I]
    (M : ModuleCat.{w} R) (F : I ⥤ ModuleCat.{w} R)
    (t : Cocone F) (ht : IsColimit t) (u : ∀ i : I, M ⟶ F.obj i)
    (hu : CompatibleEssentialSystem M F u) :
    EssentialExtension (filteredColimitMap M F t u) := by
  sorry

/-! ## The module criterion -/

/-- A submodule is essential in a module when it meets every nonzero
submodule nontrivially.  This is the module realization of an essential
extension `S ↪ N`. -/
def EssentialSubmodule {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    (S : Submodule R N) : Prop :=
  ∀ T : Submodule R N, T ≠ ⊥ → S ⊓ T ≠ ⊥

/-- The submodule formulation agrees with the categorical essential
extension predicate through the canonical `ModuleCat` subobject API. -/
theorem essentialSubmodule_iff_essentialExtension
    {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    (S : Submodule R N) :
    EssentialSubmodule S ↔
      EssentialExtension (ModuleCat.ofHom S.subtype) := by
  sorry

/-- Elementwise characterization of an essential submodule. -/
theorem essentialSubmodule_iff_smul
    {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    (S : Submodule R N) :
    EssentialSubmodule S ↔
      ∀ x : N, x ≠ 0 → ∃ r : R, r • x ∈ S ∧ r • x ≠ 0 := by
  sorry

end

end Formalization.Books.Dualizing.Unit02
