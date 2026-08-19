import Formalization.Books.Modules.Unit09.FiniteType
import Formalization.Books.Modules.Unit10.QuasiCoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Sheaves of Modules, Chapter 11: Modules of finite presentation

This file formalizes the source section `Modules of finite presentation`.
Finite presentation itself is Mathlib's canonical `SheafOfModules.IsFinitePresentation`
condition.  The local finite-cokernel formulation and the categorical forms of
the source's exact sequence, colimit, and stalk statements are retained as
usable interfaces below.
-/

namespace Formalization.Books.Modules.Unit11

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit09
open Formalization.Books.Modules.Unit10
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22

universe v

noncomputable section

local notation "Mod" => Formalization.Books.Sheaves.Unit10.Mod

/-! ## Definition `definition-finite-presentation` -/

/-- The source's finite-presentation condition, using Mathlib's canonical
finite local presentation class for sheaves of modules. -/
abbrev IsFinitePresentation {X : RingedSpace.{v}} (F : Mod X.structureSheaf) : Prop :=
  SheafOfModules.IsFinitePresentation F

/-- A finite free cokernel presentation on an open subspace.  The two finite
index sets are represented by `ULift (Fin m)` and `ULift (Fin n)`, matching the source's
finite direct sums. -/
def HasFinitePresentationOn {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (U : Opens X.carrier) : Prop :=
  ∃ (m n : ℕ)
    (φ : (SheafOfModules.free (ULift.{v} (Fin m)) :
      Mod (ringedOpenSubspace X U).structureSheaf) ⟶
      (SheafOfModules.free (ULift.{v} (Fin n)) :
        Mod (ringedOpenSubspace X U).structureSheaf)),
    Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ)

/-- The generators-and-relations form of a finite presentation on an open.

This is Mathlib's canonical packaging of the two clauses following the
source definition: finitely many sections generate the restriction, and
finitely many sections generate the kernel of the resulting epimorphism. -/
def HasFiniteGeneratorsAndRelationsOn {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (U : Opens X.carrier) : Prop :=
  ∃ P : ((openModuleRestrictionFunctor X U).obj F).Presentation, P.IsFinite

/-- The pointwise local form of finite presentation. -/
def LocallyFinitePresentation {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) : Prop :=
  ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧ HasFinitePresentationOn F U

/-- The exact sequence attached to a finite free cokernel presentation. -/
def HasExactFinitePresentationOn {X : RingedSpace.{v}}
    (F : Mod X.structureSheaf) (U : Opens X.carrier) : Prop :=
  ∃ (m n : ℕ)
    (φ : (SheafOfModules.free (ULift.{v} (Fin m)) :
      Mod (ringedOpenSubspace X U).structureSheaf) ⟶
      (SheafOfModules.free (ULift.{v} (Fin n)) :
        Mod (ringedOpenSubspace X U).structureSheaf))
    (e : ((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ),
    (ShortComplex.mk φ (cokernel.π φ ≫ e.inv) (by simp)).Exact

private noncomputable def freeEquivIso {Y : RingedSpace.{v}}
    {α β : Type v} (e : α ≃ β) :
    (SheafOfModules.free (R := Y.structureSheaf) α : Mod Y.structureSheaf) ≅
      SheafOfModules.free (R := Y.structureSheaf) β where
  hom := SheafOfModules.freeMap e
  inv := SheafOfModules.freeMap e.symm
  hom_inv_id := by
    apply (SheafOfModules.freeHomEquiv _).injective
    ext i
    simp only [SheafOfModules.freeHomEquiv_comp_apply,
      SheafOfModules.freeHomEquiv_freeMap, Function.comp_apply,
      SheafOfModules.sectionMap_freeMap_freeSection, Equiv.symm_apply_apply]
  inv_hom_id := by
    apply (SheafOfModules.freeHomEquiv _).injective
    ext i
    simp only [SheafOfModules.freeHomEquiv_comp_apply,
      SheafOfModules.freeHomEquiv_freeMap, Function.comp_apply,
      SheafOfModules.sectionMap_freeMap_freeSection, Equiv.apply_symm_apply]

private theorem finitePresentation_of_hasFinitePresentationOn
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) (U : Opens X.carrier)
    (h : HasFinitePresentationOn F U) :
    ∃ P : ((openModuleRestrictionFunctor X U).obj F).Presentation, P.IsFinite := by
  rcases h with ⟨m, n, φ, ⟨e⟩⟩
  let g := cokernel.π φ ≫ e.inv
  have hg : φ ≫ g = 0 := by simp [g]
  have hcolim : IsColimit (CokernelCofork.ofπ g hg) := by
    exact IsColimit.ofIsoColimit (cokernelIsCokernel φ) (Cofork.ext e.symm)
  let P := SheafOfModules.presentationOfIsCokernelFree φ g hg hcolim
  refine ⟨P, ?_⟩
  constructor
  · constructor
    change Finite (ULift (Fin n))
    infer_instance
  · constructor
    change Finite (ULift (Fin m))
    infer_instance

private theorem hasFinitePresentationOn_of_finitePresentation
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) (U : Opens X.carrier)
    (h : ∃ P : ((openModuleRestrictionFunctor X U).obj F).Presentation, P.IsFinite) :
    HasFinitePresentationOn F U := by
  rcases h with ⟨P, hP⟩
  let hr : Finite P.relations.I := hP.isFiniteType_relations.finite
  let hg' : Finite P.generators.I := hP.isFiniteType_generators.finite
  let fr : Fintype P.relations.I := @Fintype.ofFinite _ hr
  let fg : Fintype P.generators.I := @Fintype.ofFinite _ hg'
  let er : P.relations.I ≃ ULift (Fin (@Fintype.card _ fr)) :=
    (@Fintype.equivFin _ fr).trans Equiv.ulift.symm
  let eg : P.generators.I ≃ ULift (Fin (@Fintype.card _ fg)) :=
    (@Fintype.equivFin _ fg).trans Equiv.ulift.symm
  let ir := freeEquivIso (Y := ringedOpenSubspace X U) er
  let ig := freeEquivIso (Y := ringedOpenSubspace X U) eg
  let f := (SheafOfModules.freeHomEquiv _).symm P.relations.s ≫
    kernel.ι P.generators.π
  let φ := ir.inv ≫ f ≫ ig.hom
  let g := ig.inv ≫ P.generators.π
  have hg : φ ≫ g = 0 := by
    simp [φ, g, f]
  have hcolim : IsColimit (CokernelCofork.ofπ g hg) := by
    apply Cofork.isColimitOfIsos
      (CokernelCofork.ofπ P.generators.π (by simp)) P.isColimit
      (CokernelCofork.ofπ g hg) ir ig (Iso.refl _)
  have he : Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ) := by
    let e : ((openModuleRestrictionFunctor X U).obj F) ≅ cokernel φ :=
      hcolim.coconePointUniqueUpToIso (colimit.isColimit _)
    exact ⟨e⟩
  exact ⟨@Fintype.card _ fr, @Fintype.card _ fg, φ, he⟩

/-- Finite presentation is equivalent to the source's local finite-cokernel
formulation. -/
theorem isFinitePresentation_iff_locallyFinitePresentation
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) :
    IsFinitePresentation F ↔ LocallyFinitePresentation F := by
  sorry
  /- Original proof attempt:
  constructor
  · intro hF x
    rcases hF with ⟨⟨q, hq⟩⟩
    have hcover : IsOpenCover q.X :=
      (Opens.coversTop_iff X.carrier q.X).mp q.coversTop
    obtain ⟨i, hxi⟩ := hcover.exists_mem x
    refine ⟨q.X i, hxi, ?_⟩
    exact hasFinitePresentationOn_of_finitePresentation F (q.X i)
      ⟨q.presentation i, hq.isFinite_presentation i⟩
  · intro hF
    choose U hxU hP using hF
    choose P hPfin using fun x ↦
      finitePresentation_of_hasFinitePresentationOn F (U x) (hP x)
    let q : SheafOfModules.QuasicoherentData.{v, v} F :=
      { I := X.carrier
        X := U
        coversTop := (Opens.coversTop_iff X.carrier U).mpr (by
          apply TopologicalSpace.IsOpenCover.mk
          ext x
          constructor
          · intro
            trivial
          · intro _
            exact (le_iSup U x) (hxU x))
        presentation := P }
    refine { exists_quasicoherentData := ?_ }
    refine ⟨q.shrink, ?_⟩
    constructor
    intro i
    exact hPfin i.2.choose

/-- The finite-cokernel and finite-generators-and-relations descriptions on
an open are equivalent. -/
  -/
theorem hasFinitePresentationOn_iff_hasFiniteGeneratorsAndRelationsOn
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) (U : Opens X.carrier) :
    HasFinitePresentationOn F U ↔ HasFiniteGeneratorsAndRelationsOn F U := by
  constructor
  · exact finitePresentation_of_hasFinitePresentationOn F U
  · rintro ⟨P, hP⟩
    exact hasFinitePresentationOn_of_finitePresentation F U ⟨P, hP⟩

/-- The displayed finite-cokernel sequence is exact, and conversely an exact
sequence of this form supplies the displayed cokernel presentation. -/
theorem hasFinitePresentationOn_iff_hasExactFinitePresentationOn
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) (U : Opens X.carrier) :
    HasFinitePresentationOn F U ↔ HasExactFinitePresentationOn F U := by
  constructor
  · rintro ⟨m, n, φ, ⟨e⟩⟩
    refine ⟨m, n, φ, e, ?_⟩
    apply ShortComplex.exact_of_g_is_cokernel
    exact IsColimit.ofIsoColimit (cokernelIsCokernel φ) (Cofork.ext e.symm)
  · rintro ⟨m, n, φ, e, _⟩
    exact ⟨m, n, φ, ⟨e⟩⟩

/-! The two clauses in the source's explanation are represented by the finite
generators and finite relations in `SheafOfModules.Presentation.IsFinite`;
the local finite-cokernel interface above packages both clauses together. -/

/-- Source-facing form of the two clauses following the definition: locally,
the sheaf has finitely many generators and the kernel of their presentation
map has finitely many generators as well. -/
theorem finitePresentation_hasLocalFiniteGeneratorsAndRelations
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : IsFinitePresentation F) :
    ∀ x : X, ∃ U : Opens X.carrier, x ∈ U ∧
      HasFiniteGeneratorsAndRelationsOn F U := by
  intro x
  obtain ⟨U, hx, hU⟩ :=
    (isFinitePresentation_iff_locallyFinitePresentation F).mp hF x
  exact ⟨U, hx,
    (hasFinitePresentationOn_iff_hasFiniteGeneratorsAndRelationsOn F U).mp hU⟩

/-! ## Lemma `lemma-finite-presentation-quasi-coherent` -/

/-- Every module of finite presentation is quasi-coherent. -/
theorem finitePresentation_isQuasiCoherent
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : IsFinitePresentation F) :
    IsQuasiCoherent F := by
  sorry

/-! ## Lemma `lemma-cokernel-finite-finite-presentation` -/

/-- The cokernel of a map from a finite-type module to a finitely presented
module is finitely presented. -/
theorem cokernel_finiteType_finitePresentation
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (φ : G ⟶ F) (hF : IsFinitePresentation F) (hG : finiteType G) :
    IsFinitePresentation (cokernel φ) := by
  sorry

/-! ## Lemma `lemma-kernel-surjection-finite-free-onto-finite-presentation` -/

/-- The kernel of a surjection from a finite free module onto a finitely
presented module is of finite type. -/
theorem kernel_surjection_finiteFree_finiteType
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf} (r : ℕ)
    (ψ : (SheafOfModules.free (ULift.{v} (Fin r)) : Mod X.structureSheaf) ⟶ F)
    (hψ : Epi ψ) (hF : IsFinitePresentation F) :
    finiteType (kernel ψ) := by
  sorry

/-- The kernel of a surjection from a finite-type module onto a finitely
presented module is of finite type. -/
theorem kernel_surjection_finiteType_finiteType
    {X : RingedSpace.{v}} {F G : Mod X.structureSheaf}
    (θ : G ⟶ F) (hθ : Epi θ) (hG : finiteType G)
    (hF : IsFinitePresentation F) :
    finiteType (kernel θ) := by
  sorry

/- The displayed map in the source proof,
`(β ∘ χ, 1 - β ∘ α)`, is the local biproduct map which factors through the
kernel of the given finite-free surjection.  It is an intermediate witness
for the preceding finite-type conclusion rather than an additional global
interface. -/

/-! ## Lemma `lemma-pullback-finite-presentation` -/

/-- Pullback along a morphism of ringed spaces preserves finite presentation. -/
theorem pullback_finitePresentation
    {X Y : RingedSpace.{v}} (f : RingedSpaceHom X Y)
    (G : Mod Y.structureSheaf) (hG : IsFinitePresentation G)
    [((SheafOfModules.pushforward (F := Opens.map f.continuous)
      f.sharp).IsRightAdjoint)] :
    IsFinitePresentation ((sheafModuleRingedSpacePullback f).obj G) := by
  sorry

/-! ## Lemma `lemma-quasi-coherent-limit-finite-presentation` -/

/-- A directed colimit of finite-presentation sheaves representing `F`. -/
structure DirectedFinitePresentationColimit
    {X : RingedSpace.{v}} (F : Mod X.structureSheaf) where
  I : Type v
  [preorder : Preorder I]
  [nonempty : Nonempty I]
  [directed : IsDirectedOrder I]
  diagram : I ⥤ Mod X.structureSheaf
  finitePresentation : ∀ i, IsFinitePresentation (diagram.obj i)
  iso : Nonempty (colimit diagram ≅ F)

/-- The associated sheaf of any global-sections module is a directed colimit
of finitely presented sheaves. -/
theorem associatedSheaf_is_directedColimit_finitePresentation
    {X : RingedSpace.{v}}
    (M : ModuleCat (globalSectionsRing X)) :
    Nonempty (DirectedFinitePresentationColimit
      (associatedSheafOfGlobalSections M)) := by
  sorry

/-! ## Lemma `lemma-finite-presentation-stalk-free` -/

/-- The finite free module over the stalk of the structure sheaf. -/
noncomputable abbrev stalkFreeModule {X : RingedSpace.{v}} (x : X) (r : ℕ) :
    ModuleCat (TopCat.Presheaf.stalk (C := RingCat) X.structureSheaf.obj x) :=
  (ModuleCat.free
    (TopCat.Presheaf.stalk (C := RingCat) X.structureSheaf.obj x)).obj
      (ULift.{v} (Fin r))

/-- A finite-presentation module which is free at a stalk is free on a
neighbourhood of that point. -/
theorem finitePresentation_stalk_free
    {X : RingedSpace.{v}} {F : Mod X.structureSheaf}
    (hF : IsFinitePresentation F) (x : X) (r : ℕ)
    (hx : Nonempty ((sheafModuleStalkFunctor X.structureSheaf x).obj F ≅
      stalkFreeModule x r)) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      Nonempty (((openModuleRestrictionFunctor X U).obj F) ≅
        (SheafOfModules.free (ULift.{v} (Fin r)) :
          Mod (ringedOpenSubspace X U).structureSheaf)) := by
  sorry

end

end Formalization.Books.Modules.Unit11
