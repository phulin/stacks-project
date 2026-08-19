import Formalization.Books.Schemes.Unit03.OpenImmersions
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Topology.Constructions

/-!
# Schemes, Chapter 4: Closed immersions of locally ringed spaces

This file formalizes the source section `Closed immersions of locally ringed
spaces`.  The underlying locally ringed spaces and their morphisms are
Mathlib's canonical `AlgebraicGeometry.LocallyRingedSpace` objects.  Ideal
sheaves use the canonical category of sheaves of modules over the structure
sheaf, and the closed-immersion and closed-subspace constructions below keep
the source's universal properties explicit.
-/

namespace Formalization.Books.Schemes.Unit04

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open TopologicalSpace
open Topology
open Formalization.Books.Schemes.Unit03

universe u

noncomputable section

/-! ## Closed immersions and ideal sheaves -/

/-- The structure sheaf, viewed as a sheaf of (not necessarily commutative)
rings for the module-sheaf API. -/
noncomputable def structureSheafOfRings (X : LocallyRingedSpace.{u}) :
    Sheaf (Opens.grothendieckTopology X.toTopCat) RingCat :=
  ⟨X.𝒪.obj ⋙ forget₂ CommRingCat RingCat,
    Presheaf.isSheaf_comp_of_isSheaf
      (J := Opens.grothendieckTopology X.toTopCat)
      (P := X.𝒪.obj) (forget₂ CommRingCat RingCat) X.𝒪.property⟩

/-- A sheaf of ideals is represented canonically as a sheaf of modules together
with its monomorphism into the structure sheaf module. -/
structure IdealSheaf (X : LocallyRingedSpace.{u}) where
  module : SheafOfModules (structureSheafOfRings X)
  inclusion : module ⟶ SheafOfModules.unit (structureSheafOfRings X)
  inclusion_mono : Mono inclusion

/-- Local generation by sections for an ideal sheaf. -/
def LocallyGenerated {X : LocallyRingedSpace.{u}} (I : IdealSheaf X) : Prop :=
  ∀ x : X, ∃ U : Opens X.toTopCat, x ∈ U ∧
    ∃ (J : Type u) (s : J → I.module.val.obj (op U)),
      ∀ t : I.module.val.obj (op U),
        ∃ (F : Finset J) (a : J → (structureSheafOfRings X).obj.obj (op U)),
          I.inclusion.val.app (op U) t =
            Finset.sum F (fun j => a j • I.inclusion.val.app (op U) (s j))

/-- The pointwise universal property of the kernel ideal of a morphism. -/
def IsKernelIdeal {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (I : IdealSheaf Y) : Prop :=
  ∀ (U : Opens Y.toTopCat) (s : Y.presheaf.obj (op U)),
    f.toHom.c.app (op U) s = 0 ↔
      ∃ i : I.module.val.obj (op U), I.inclusion.val.app (op U) i = s

/-- The kernel of the structure-sheaf map is represented by an ideal sheaf.

The existence statement packages the standard kernel-sheaf construction; its
proof is deferred with the other proposition proofs in this statements stage.
-/
theorem exists_closedImmersionIdeal {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    ∃ I : IdealSheaf Y, IsKernelIdeal f I := by
  let b : X.toTopCat ⟶ Y.toTopCat := f.toHom.base
  let φ : structureSheafOfRings Y ⟶
      ((Opens.map b).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology Y.toTopCat)
        (Opens.grothendieckTopology X.toTopCat)).obj
        (structureSheafOfRings X) := by
    apply (TopCat.Sheaf.forget RingCat Y.toTopCat).preimage
    exact Functor.whiskerRight f.toHom.c (forget₂ CommRingCat RingCat)
  let p : SheafOfModules.unit (structureSheafOfRings Y) ⟶
      (SheafOfModules.pushforward φ).obj
        (SheafOfModules.unit (structureSheafOfRings X)) :=
    SheafOfModules.unitToPushforwardObjUnit φ
  let I : IdealSheaf Y :=
    { module := kernel p
      inclusion := kernel.ι p
      inclusion_mono := inferInstance }
  let g : (TopCat.Sheaf.forget RingCat Y.toTopCat).obj (structureSheafOfRings Y) ⟶
      (TopCat.Sheaf.forget RingCat Y.toTopCat).obj
        (((Opens.map b).sheafPushforwardContinuous RingCat
          (Opens.grothendieckTopology Y.toTopCat)
          (Opens.grothendieckTopology X.toTopCat)).obj
          (structureSheafOfRings X)) := by
    exact Functor.whiskerRight f.toHom.c (forget₂ CommRingCat RingCat)
  have hφ : (TopCat.Sheaf.forget RingCat Y.toTopCat).map φ =
      g := by
    change (TopCat.Sheaf.forget RingCat Y.toTopCat).map
      ((TopCat.Sheaf.forget RingCat Y.toTopCat).preimage g) = g
    exact (TopCat.Sheaf.forget RingCat Y.toTopCat).map_preimage g
  refine ⟨I, ?_⟩
  intro U s
  constructor
  · intro hs
    let E := SheafOfModules.evaluation (structureSheafOfRings Y) (op U)
    let toComm : E.obj (SheafOfModules.unit (structureSheafOfRings Y)) →
        Y.presheaf.obj (op U) := fun r => r
    let fromComm : Y.presheaf.obj (op U) →
        (structureSheafOfRings Y).obj.obj (op U) := fun r => r
    let fromRing : E.obj (SheafOfModules.unit (structureSheafOfRings Y)) →
        (structureSheafOfRings Y).obj.obj (op U) := fun r => r
    let sR : (structureSheafOfRings Y).obj.obj (op U) := s
    let sM : E.obj (SheafOfModules.unit (structureSheafOfRings Y)) := s
    let k : E.obj (SheafOfModules.unit (structureSheafOfRings Y)) ⟶
        E.obj (SheafOfModules.unit (structureSheafOfRings Y)) :=
      ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf
          ((structureSheafOfRings Y).obj.obj (op U)) ℤ
          (E.obj (SheafOfModules.unit (structureSheafOfRings Y)))).symm sM)
    let hk : k ≫ E.map p = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      have hkval : k r = fromRing r * sR := by
        change ((LinearMap.ringLmapEquivSelf
          ((structureSheafOfRings Y).obj.obj (op U)) ℤ
          (E.obj (SheafOfModules.unit (structureSheafOfRings Y)))).symm sM) r =
          fromRing r * sR
        rw [LinearMap.ringLmapEquivSelf_symm_apply,
          ]
        change (LinearMap.smulRight (1 :
          (structureSheafOfRings Y).obj.obj (op U) →ₗ[
            (structureSheafOfRings Y).obj.obj (op U)]
            (structureSheafOfRings Y).obj.obj (op U)) sM) (fromRing r) =
          fromRing r * sR
        rw [LinearMap.smulRight_apply]
        change (fromRing r) • (sR : E.obj
          (SheafOfModules.unit (structureSheafOfRings Y))) =
          fromRing r * sR
        rw [smul_eq_mul]
      have hφU := congrArg (fun t => t.app (op U)) hφ
      have hmap : (φ.hom.app (op U)).hom (fromRing r * sR) =
          (g.app (op U)).hom (fromRing r * sR) := by
        have h := congrArg (fun t => t.hom (fromRing r * sR)) hφU
        convert h using 1; rfl
      have hprod : (g.app (op U)).hom (fromRing r * sR) = 0 := by
        change f.toHom.c.app (op U) (toComm r * s) = 0
        rw [map_mul, hs]
        simp
      change (φ.hom.app (op U)).hom (k r) = 0
      rw [hkval, hmap]
      exact hprod
    let hzero : E.map (0 : SheafOfModules.unit (structureSheafOfRings Y) ⟶
        (SheafOfModules.pushforward φ).obj
          (SheafOfModules.unit (structureSheafOfRings X))) = 0 := by rfl
    let l : Cone (parallelPair p 0 ⋙ E) := Cone.ofFork (Fork.ofι k (by
      change k ≫ E.map p = k ≫ E.map 0
      rw [hzero]
      exact hk))
    let q : E.obj (SheafOfModules.unit (structureSheafOfRings Y)) ⟶
        E.obj (kernel p) :=
      (isLimitOfPreserves E (kernelIsKernel p)).lift l ≫ eqToHom (by rfl)
    exact ⟨q (1 : (structureSheafOfRings Y).obj.obj (op U)), by
      change (E.map (kernel.ι p))
        (q (1 : (structureSheafOfRings Y).obj.obj (op U))) = s
      dsimp [q]
      change (E.map (kernel.ι p))
        ((isLimitOfPreserves E (kernelIsKernel p)).lift l
          (1 : (structureSheafOfRings Y).obj.obj (op U))) = s
      have hq := (isLimitOfPreserves E (kernelIsKernel p)).fac
        l WalkingParallelPair.zero
      have hq' := congrArg (fun t => t
        (1 : (structureSheafOfRings Y).obj.obj (op U))) hq
      change (E.map (kernel.ι p))
          ((isLimitOfPreserves E (kernelIsKernel p)).lift l
            (1 : (structureSheafOfRings Y).obj.obj (op U))) =
        (l.π.app WalkingParallelPair.zero)
          (1 : (structureSheafOfRings Y).obj.obj (op U)) at hq'
      have hl : (l.π.app WalkingParallelPair.zero)
          (1 : (structureSheafOfRings Y).obj.obj (op U)) = s := by
        change k (1 : (structureSheafOfRings Y).obj.obj (op U)) = s
        change ((LinearMap.ringLmapEquivSelf
          ((structureSheafOfRings Y).obj.obj (op U)) ℤ
          (E.obj (SheafOfModules.unit (structureSheafOfRings Y)))).symm sM) 1 = s
        rw [LinearMap.ringLmapEquivSelf_symm_apply]
        change (LinearMap.smulRight (1 :
          (structureSheafOfRings Y).obj.obj (op U) →ₗ[
            (structureSheafOfRings Y).obj.obj (op U)]
            (structureSheafOfRings Y).obj.obj (op U)) sM) 1 = s
        rw [LinearMap.smulRight_apply]
        change (1 : (structureSheafOfRings Y).obj.obj (op U)) • sM = s
        rw [one_smul]
      exact hq'.trans hl
      ⟩
  · rintro ⟨i, hi⟩
    rw [← hi]
    have hp : p.val.app (op U) ((kernel.ι p).val.app (op U) i) = 0 := by
      have hc := congrArg (fun t => t.val.app (op U) i) (kernel.condition p)
      exact hc
    dsimp [I]
    have hφU := congrArg (fun t => t.app (op U)) hφ
    have hφUi := congrArg (fun t => t.hom
      ((kernel.ι p).val.app (op U) i)) hφU
    let jR : (structureSheafOfRings Y).obj.obj (op U) :=
      (kernel.ι p).val.app (op U) i
    let jC : Y.presheaf.obj (op U) :=
      (kernel.ι p).val.app (op U) i
    let out :
        ((SheafOfModules.pushforward φ).obj
          (SheafOfModules.unit (structureSheafOfRings X))).val.obj (op U) →
        (((Opens.map b).sheafPushforwardContinuous RingCat
          (Opens.grothendieckTopology Y.toTopCat)
          (Opens.grothendieckTopology X.toTopCat)).obj
          (structureSheafOfRings X)).obj.obj (op U) := fun x => x
    have hpR := congrArg out hp
    have hpP : p.val.app (op U) jR = 0 := by
      change out (p.val.app (op U) jR) = 0
      exact hpR
    have hunit : p.val.app (op U) jR = (φ.hom.app (op U)).hom jR := by
      dsimp [p]
      exact SheafOfModules.unitToPushforwardObjUnit_val_app_apply φ jR
    have hp' : (φ.hom.app (op U)).hom jR = 0 := by
      rw [← hunit]
      exact hpP
    have hmapR : (φ.hom.app (op U)).hom jR =
        (g.app (op U)).hom jR := by
      have h := congrArg (fun t => t.hom jR) hφU
      convert h using 1; rfl
    have hzeroG : (g.app (op U)).hom jR = 0 := by
      rw [← hmapR]
      exact hp'
    let outX :
        (((Opens.map b).sheafPushforwardContinuous RingCat
          (Opens.grothendieckTopology Y.toTopCat)
          (Opens.grothendieckTopology X.toTopCat)).obj
          (structureSheafOfRings X)).obj.obj (op U) →
        X.presheaf.obj (op ((Opens.map f.base).obj U)) := fun x => x
    have hzeroGX := congrArg outX hzeroG
    change f.toHom.c.app (op U) jC = 0 at hzeroGX
    exact hzeroGX

/-- The ideal sheaf cut out by a morphism of locally ringed spaces. -/
noncomputable def closedImmersionIdeal {X Y : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) : IdealSheaf Y :=
  Classical.choose (exists_closedImmersionIdeal f)

/-- The selected ideal sheaf satisfies the pointwise kernel property. -/
theorem closedImmersionIdeal_isKernel {X Y : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) : IsKernelIdeal f (closedImmersionIdeal f) :=
  Classical.choose_spec (exists_closedImmersionIdeal f)

/-- The canonical inclusion of the ideal sheaf of a morphism. -/
noncomputable def closedImmersionIdealInclusion {X Y : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) :
    (closedImmersionIdeal f).module ⟶
      SheafOfModules.unit (structureSheafOfRings Y) :=
  (closedImmersionIdeal f).inclusion

/-- A morphism of locally ringed spaces is a closed immersion when its
underlying map is a closed embedding, its structure-sheaf map is an epimorphism,
and its ideal sheaf is locally generated by sections. -/
structure IsClosedImmersion {X Y : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) : Prop where
  isClosedEmbedding : IsClosedEmbedding f.toHom.base
  structureSheaf_epi : Epi f.toHom.c
  ideal_locallyGenerated : LocallyGenerated (closedImmersionIdeal f)

/-! ## Locality on the target -/

/-- A closed-immersion datum over an open subset of the target.  The map is
the restriction to the inverse image of that open, and `commutes` records the
displayed square with the ambient inclusion maps. -/
structure TargetClosedImmersionData {X Y : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) (V : Opens Y.toTopCat) where
  map : openSubspace X (Opens.comap f.toHom.base.hom V) ⟶ openSubspace Y V
  isClosedImmersion : IsClosedImmersion map
  commutes : map ≫ openSubspaceInclusion Y V =
    openSubspaceInclusion X (Opens.comap f.toHom.base.hom V) ≫ f

/-- An indexed family of opens covers the target. -/
def IsOpenCover {ι : Type u} {Y : LocallyRingedSpace.{u}}
    (V : ι → Opens Y.toTopCat) : Prop :=
  ∀ y : Y, ∃ i, y ∈ V i

/-- Closed immersion is local on the target. -/
theorem isClosedImmersion_of_openCover {ι : Type u}
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (V : ι → Opens Y.toTopCat) (hV : IsOpenCover V)
    (hlocal : ∀ i, Nonempty (TargetClosedImmersionData f (V i))) :
    IsClosedImmersion f := by
  sorry

/-! ## Closed subspaces associated to ideals -/

/-- Data for the closed subspace associated to a locally generated ideal. -/
structure ClosedSubspaceData (X : LocallyRingedSpace.{u}) (I : IdealSheaf X)
    (hI : LocallyGenerated I) where
  carrier : LocallyRingedSpace.{u}
  inclusion : carrier ⟶ X
  isClosedImmersion : IsClosedImmersion inclusion
  idealIso : Nonempty (I.module ≅ (closedImmersionIdeal inclusion).module)
  stalk_nontrivial : ∀ z : carrier, Nontrivial (carrier.presheaf.stalk z)

/-- The ideal-defined closed subspace exists. -/
theorem exists_closedSubspaceData (X : LocallyRingedSpace.{u})
    (I : IdealSheaf X) (hI : LocallyGenerated I) :
    Nonempty (ClosedSubspaceData X I hI) := by
  sorry

/-- The locally ringed space associated to a locally generated ideal sheaf. -/
noncomputable def closedSubspace (X : LocallyRingedSpace.{u})
    (I : IdealSheaf X) (hI : LocallyGenerated I) : LocallyRingedSpace.{u} :=
  (Classical.choice (exists_closedSubspaceData X I hI)).carrier

/-- The canonical inclusion of the ideal-defined closed subspace. -/
noncomputable def closedSubspaceInclusion (X : LocallyRingedSpace.{u})
    (I : IdealSheaf X) (hI : LocallyGenerated I) :
    closedSubspace X I hI ⟶ X :=
  (Classical.choice (exists_closedSubspaceData X I hI)).inclusion

/-- The associated closed subspace is a closed immersion. -/
theorem closedSubspaceInclusion_isClosedImmersion
    (X : LocallyRingedSpace.{u}) (I : IdealSheaf X)
    (hI : LocallyGenerated I) :
    IsClosedImmersion (closedSubspaceInclusion X I hI) := by
  exact (Classical.choice (exists_closedSubspaceData X I hI)).isClosedImmersion

/-- The associated closed subspace has the prescribed ideal sheaf, up to the
canonical isomorphism supplied by its construction. -/
theorem closedSubspace_idealIso (X : LocallyRingedSpace.{u})
    (I : IdealSheaf X) (hI : LocallyGenerated I) :
    Nonempty (I.module ≅
      (closedImmersionIdeal (closedSubspaceInclusion X I hI)).module) := by
  exact (Classical.choice (exists_closedSubspaceData X I hI)).idealIso

/-- Stalks of the support construction are nonzero. -/
theorem closedSubspace_stalk_nontrivial (X : LocallyRingedSpace.{u})
    (I : IdealSheaf X) (hI : LocallyGenerated I)
    (z : closedSubspace X I hI) :
    Nontrivial ((closedSubspace X I hI).presheaf.stalk z) := by
  exact (Classical.choice (exists_closedSubspaceData X I hI)).stalk_nontrivial z

/-- The associated structure sheaf has the prescribed ideal as the kernel of
an epimorphism, which is the sheaf-theoretic quotient description. -/
theorem closedSubspace_quotient_characterization (X : LocallyRingedSpace.{u})
    (I : IdealSheaf X) (hI : LocallyGenerated I) :
    Epi (closedSubspaceInclusion X I hI).toHom.c ∧
      IsKernelIdeal (closedSubspaceInclusion X I hI)
        (closedImmersionIdeal (closedSubspaceInclusion X I hI)) ∧
      Nonempty (I.module ≅
        (closedImmersionIdeal (closedSubspaceInclusion X I hI)).module) := by
  refine ⟨(closedSubspaceInclusion_isClosedImmersion X I hI).structureSheaf_epi, ?_, ?_⟩
  · exact closedImmersionIdeal_isKernel (closedSubspaceInclusion X I hI)
  · exact closedSubspace_idealIso X I hI

/-- The associated stalks are local rings, as required for the locally ringed
space structure in the support construction. -/
theorem closedSubspace_stalk_isLocalRing (X : LocallyRingedSpace.{u})
    (I : IdealSheaf X) (hI : LocallyGenerated I)
    (z : closedSubspace X I hI) :
    IsLocalRing ((closedSubspace X I hI).presheaf.stalk z) := by
  infer_instance

/-! ## Characterizations of the associated closed subspace -/

/-- The closed subspace associated to the kernel of a closed immersion. -/
noncomputable def associatedClosedSubspaceOfClosedImmersion
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (hf : IsClosedImmersion f) : LocallyRingedSpace.{u} :=
  closedSubspace Y (closedImmersionIdeal f) hf.ideal_locallyGenerated

/-- A closed immersion is identified with the closed subspace defined by its
kernel ideal. -/
theorem exists_closedImmersion_associatedIso
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (hf : IsClosedImmersion f) :
    ∃ e : X ≅ associatedClosedSubspaceOfClosedImmersion f hf,
      e.hom ≫ closedSubspaceInclusion Y (closedImmersionIdeal f)
        hf.ideal_locallyGenerated = f := by
  sorry

/-- The isomorphism in the preceding characterization is unique. -/
theorem closedImmersion_associatedIso_unique
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (hf : IsClosedImmersion f)
    (e e' : X ≅ associatedClosedSubspaceOfClosedImmersion f hf)
    (he : e.hom ≫ closedSubspaceInclusion Y (closedImmersionIdeal f)
      hf.ideal_locallyGenerated = f)
    (he' : e'.hom ≫ closedSubspaceInclusion Y (closedImmersionIdeal f)
      hf.ideal_locallyGenerated = f) :
    e = e' := by
  sorry

/-! ## Factorization through a closed subspace -/

/-- Data for the inverse-image ideal module and its map to the structure
sheaf.  Mathlib does not yet expose this inverse-image construction for
locally ringed spaces, so the chapter records its canonical module and map as
an explicit interface. -/
structure IdealPullbackData {X Y : LocallyRingedSpace.{u}}
    (f : Y ⟶ X) (I : IdealSheaf X) where
  module : SheafOfModules (structureSheafOfRings Y)
  map : module ⟶ SheafOfModules.unit (structureSheafOfRings Y)

/-- The standard inverse-image ideal module exists. -/
theorem exists_idealPullbackData {X Y : LocallyRingedSpace.{u}}
    (f : Y ⟶ X) (I : IdealSheaf X) :
    Nonempty (IdealPullbackData f I) := by
  sorry

/-- The inverse-image ideal module and its map to the target structure sheaf. -/
noncomputable def idealPullbackData {X Y : LocallyRingedSpace.{u}}
    (f : Y ⟶ X) (I : IdealSheaf X) : IdealPullbackData f I :=
  Classical.choice (exists_idealPullbackData f I)

/-- The map `f^* I → O_Y` is zero, expressed sectionwise through the chosen
inverse-image ideal datum. -/
def pullbackIdealMapZero {X Y : LocallyRingedSpace.{u}}
    (f : Y ⟶ X) (I : IdealSheaf X) : Prop :=
  ∀ (U : Opens Y.toTopCat) (s : (idealPullbackData f I).module.val.obj (op U)),
    (idealPullbackData f I).map.val.app (op U) s = 0

/-- A morphism factors through the closed subspace cut out by `I` exactly when
the pullback of `I` maps to zero. -/
theorem factors_through_closedSubspace_iff
    {X Y : LocallyRingedSpace.{u}} (f : Y ⟶ X)
    (I : IdealSheaf X) (hI : LocallyGenerated I) :
    (∃ g : Y ⟶ closedSubspace X I hI,
      g ≫ closedSubspaceInclusion X I hI = f) ↔
      pullbackIdealMapZero f I := by
  sorry

/-- The factorization through a closed subspace is unique. -/
theorem factor_through_closedSubspace_unique
    {X Y : LocallyRingedSpace.{u}} (f : Y ⟶ X)
    (I : IdealSheaf X) (hI : LocallyGenerated I)
    (g h : Y ⟶ closedSubspace X I hI)
    (hg : g ≫ closedSubspaceInclusion X I hI = f)
    (hh : h ≫ closedSubspaceInclusion X I hI = f) :
    g = h := by
  sorry

/-! ## Restriction of a morphism to a closed subspace -/

/-- The image ideal data for a morphism and an ideal on its target. -/
structure ImageIdealData {X Y : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) (I : IdealSheaf Y)
    (P : IdealPullbackData f I) where
  image : IdealSheaf X
  image_locallyGenerated : LocallyGenerated image
  image_eq_range : ∀ (U : Opens X.toTopCat),
    (∀ t : image.module.val.obj (op U),
      ∃ s : P.module.val.obj (op U),
        image.inclusion.val.app (op U) t = P.map.val.app (op U) s) ∧
    (∀ s : P.module.val.obj (op U),
      ∃ t : image.module.val.obj (op U),
        image.inclusion.val.app (op U) t = P.map.val.app (op U) s)

/-- The image of the pullback of an ideal is an ideal sheaf. -/
theorem exists_imageIdealData {X Y : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) (I : IdealSheaf Y)
    (P : IdealPullbackData f I) :
    Nonempty (ImageIdealData f I P) := by
  sorry

/-- The chosen image ideal datum, based on the chosen inverse-image datum. -/
noncomputable def imageIdealData {X Y : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) (I : IdealSheaf Y) :
    ImageIdealData f I (idealPullbackData f I) :=
  Classical.choice (exists_imageIdealData f I (idealPullbackData f I))

/-- The ideal sheaf which is the image of `f^* I → O_X`. -/
noncomputable def imageIdeal {X Y : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) (I : IdealSheaf Y) : IdealSheaf X :=
  (imageIdealData f I).image

/-- The image ideal is locally generated. -/
theorem imageIdeal_locallyGenerated {X Y : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) (I : IdealSheaf Y) :
    LocallyGenerated (imageIdeal f I) := by
  exact (imageIdealData f I).image_locallyGenerated

/-- The image ideal is exactly the pointwise image of the chosen pullback map. -/
theorem imageIdeal_eq_range {X Y : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) (I : IdealSheaf Y) (U : Opens X.toTopCat) :
    (∀ t : (imageIdeal f I).module.val.obj (op U),
      ∃ s : (idealPullbackData f I).module.val.obj (op U),
        (imageIdeal f I).inclusion.val.app (op U) t =
          (idealPullbackData f I).map.val.app (op U) s) ∧
    (∀ s : (idealPullbackData f I).module.val.obj (op U),
      ∃ t : (imageIdeal f I).module.val.obj (op U),
        (imageIdeal f I).inclusion.val.app (op U) t =
          (idealPullbackData f I).map.val.app (op U) s) := by
  exact (imageIdealData f I).image_eq_range U

/-- The closed subspace of `X` associated to the image ideal of `I`. -/
noncomputable def restrictedClosedSubspace
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (I : IdealSheaf Y)
    (hI : LocallyGenerated I) : LocallyRingedSpace.{u} :=
  closedSubspace X (imageIdeal f I) (imageIdeal_locallyGenerated f I)

/-- The inclusion of the restricted closed subspace into `X`. -/
noncomputable def restrictedClosedSubspaceInclusion
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (I : IdealSheaf Y)
    (hI : LocallyGenerated I) :
    restrictedClosedSubspace f I hI ⟶ X :=
  closedSubspaceInclusion X (imageIdeal f I) (imageIdeal_locallyGenerated f I)

/-- The restricted morphism between the two associated closed subspaces
exists. -/
theorem exists_restrictedClosedSubspaceMap
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (I : IdealSheaf Y)
    (hI : LocallyGenerated I) :
    ∃ f' : restrictedClosedSubspace f I hI ⟶ closedSubspace Y I hI,
      f' ≫ closedSubspaceInclusion Y I hI =
        restrictedClosedSubspaceInclusion f I hI ≫ f := by
  sorry

/-- The morphism induced between the associated closed subspaces. -/
noncomputable def restrictedClosedSubspaceMap
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (I : IdealSheaf Y)
    (hI : LocallyGenerated I) :
    restrictedClosedSubspace f I hI ⟶ closedSubspace Y I hI :=
  Classical.choose (exists_restrictedClosedSubspaceMap f I hI)

/-- The restricted morphism makes the defining square commute. -/
theorem restrictedClosedSubspaceMap_fac
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (I : IdealSheaf Y)
    (hI : LocallyGenerated I) :
    restrictedClosedSubspaceMap f I hI ≫ closedSubspaceInclusion Y I hI =
      restrictedClosedSubspaceInclusion f I hI ≫ f :=
  Classical.choose_spec (exists_restrictedClosedSubspaceMap f I hI)

/-- The restricted morphism is the unique morphism making the square commute. -/
theorem restrictedClosedSubspaceMap_unique
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (I : IdealSheaf Y)
    (hI : LocallyGenerated I)
    (g h : restrictedClosedSubspace f I hI ⟶ closedSubspace Y I hI)
    (hg : g ≫ closedSubspaceInclusion Y I hI =
      restrictedClosedSubspaceInclusion f I hI ≫ f)
    (hh : h ≫ closedSubspaceInclusion Y I hI =
      restrictedClosedSubspaceInclusion f I hI ≫ f) :
    g = h := by
  sorry

/-- The square defining the restriction is a fibre square in locally ringed
spaces. -/
theorem restrictedClosedSubspace_isPullback
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (I : IdealSheaf Y)
    (hI : LocallyGenerated I) :
    IsPullback (restrictedClosedSubspaceInclusion f I hI)
      (restrictedClosedSubspaceMap f I hI) f
      (closedSubspaceInclusion Y I hI) := by
  sorry

end

end Formalization.Books.Schemes.Unit04
