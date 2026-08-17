import Formalization.Books.Sheaves.Unit06.PresheavesOfModules
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Sheaves on Spaces, Chapter 14: Stalks of presheaves of modules

The source section `books/sheaves.tex:1137--1176` has two statements.  The
first is implemented by Mathlib's canonical module structure on the stalk of
a presheaf of modules, together with its germ compatibility lemma.  The
second uses the change-of-rings presheaf from Chapter 6.  Its tensor notation
is represented by extension of scalars at the stalk and by a canonical module
isomorphism.  The commutative-ring presheaf aliases below make the book's
global convention on rings explicit while reusing the earlier `RingCat`-based
presheaf-of-modules API.
-/

namespace Formalization.Books.Sheaves.Unit14

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit06
open scoped ChangeOfRings

universe u

noncomputable section

/-! ## Source-facing commutative ring aliases -/

/-- A presheaf of rings, with the book's convention that rings are commutative. -/
abbrev CommRingPresheaf (X : TopCat.{u}) :=
  TopCat.Presheaf (CommRingCat.{u}) X

/-- A presheaf of modules over a commutative-ring presheaf. -/
abbrev CommRingPresheafModule {X : TopCat.{u}} (O : CommRingPresheaf X) :=
  PMod (O ⋙ (forget₂ CommRingCat RingCat))

/-- The underlying `RingCat` morphism of a commutative-ring-presheaf morphism. -/
abbrev commRingPresheafMorphismToRingPresheaf
    {X : TopCat.{u}} {O O' : CommRingPresheaf X} (α : O ⟶ O') :
    (O ⋙ (forget₂ CommRingCat RingCat)) ⟶
      (O' ⋙ (forget₂ CommRingCat RingCat)) :=
  Functor.whiskerRight α (forget₂ CommRingCat RingCat)

/-! ## The module structure on a stalk -/

/--
The canonical `O_x`-module structure on the underlying abelian group of the
stalk of an `O`-module presheaf.  This is the filtered-colimit structure from
Mathlib, not a parallel transported structure.
-/
noncomputable abbrev stalkModule
    {X : TopCat.{u}} (O : CommRingPresheaf X)
    (F : CommRingPresheafModule O) (x : X) :
    Module (O.stalk x)
      (↑(TopCat.Presheaf.stalk F.presheaf x)) :=
  inferInstance

/-- The germ maps respect the canonical scalar action on the stalk. -/
theorem germ_smul
    {X : TopCat.{u}} {O : CommRingPresheaf X}
    {F : CommRingPresheafModule O}
    (x : X) (U : Opens X) (hx : x ∈ U)
    (r : (O ⋙ (forget₂ CommRingCat RingCat)).obj (op U))
    (m : F.obj (op U)) :
    TopCat.Presheaf.germ F.presheaf U x hx (r • m) =
      TopCat.Presheaf.germ O U x hx r •
        TopCat.Presheaf.germ F.presheaf U x hx m := by
  exact PresheafOfModules.germ_smul F x U hx r m

example {X : TopCat.{u}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (F : CommRingPresheafModule O) (x : X) : True := by
  let cO := colimit.cocone ((OpenNhds.inclusion x).op ⋙ O)
  let hcO := colimit.isColimit ((OpenNhds.inclusion x).op ⋙ O)
  let cO_R := (forget₂ CommRingCat RingCat).mapCocone cO
  have hcO_R : IsColimit cO_R := by
    exact isColimitOfPreserves (forget₂ CommRingCat RingCat) hcO
  trivial

example {X : TopCat.{u}} (O : CommRingPresheaf X) (U : (Opens X)ᵒᵖ) :
    ModuleCat.{u, u} ((O ⋙ (forget₂ CommRingCat RingCat)).obj U) =
      ModuleCat.{u, u} (O.obj U) := by
  rfl

example {X : TopCat.{u}} {O O' : CommRingPresheaf X} (α : O ⟶ O')
    (U : (Opens X)ᵒᵖ) (M : ModuleCat.{u, u} (O.obj U)) :
    (ModuleCat.restrictScalars.{u, u, u}
        (RingCat.Hom.hom ((commRingPresheafMorphismToRingPresheaf α).app U))).obj
      ((ModuleCat.extendScalars.{u, u, u} (α.app U).hom).obj M) =
      (ModuleCat.restrictScalars.{u, u, u} (α.app U).hom).obj
        ((ModuleCat.extendScalars.{u, u, u} (α.app U).hom).obj M) := by
  rfl

/-! ## Stalks and change of rings -/

/--
The stalk-level extension of scalars corresponding to the source's
`F_x ⊗_{O_x} O'_x`.  Mathlib's canonical extension-of-scalars object is
`O'_x ⊗_{O_x} F_x`; over commutative stalk rings this is the same canonical
base-change module as the source's ordering.
-/
noncomputable abbrev stalkTensorProduct
    {X : TopCat.{u}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (F : CommRingPresheafModule O) (x : X) :
    ModuleCat (O'.stalk x) :=
  (ModuleCat.extendScalars
      ((TopCat.Presheaf.stalkFunctor (CommRingCat.{u}) x).map α).hom).obj
    (ModuleCat.of (O.stalk x)
        (↑(TopCat.Presheaf.stalk F.presheaf x)))

/--
The stalk of the presheaf change of rings is canonically the stalk-level
extension of scalars.  This is the source's equality of modules in its
usable isomorphism form.
-/
theorem stalk_tensorProductPresheaf_iso
    {X : TopCat.{u}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (F : CommRingPresheafModule O) (x : X) :
    Nonempty (stalkTensorProduct α F x ≅
      ModuleCat.of (O'.stalk x)
        (↑(TopCat.Presheaf.stalk
          (tensorProductPresheaf (commRingPresheafMorphismToRingPresheaf α) F).presheaf x))) := by
  let R := O ⋙ (forget₂ CommRingCat RingCat)
  let R' := O' ⋙ (forget₂ CommRingCat RingCat)
  let α_R := commRingPresheafMorphismToRingPresheaf α
  let baseMapAux {M : CommRingPresheafModule O} {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
      M.obj U ⟶
        (ModuleCat.restrictScalars (α.app U).hom).obj
          ((ModuleCat.restrictScalars (O'.map f).hom).obj
            ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V))) := by
    have hα :
        (α.app V).hom.comp ((O.map f).hom) =
          ((O'.map f).hom).comp (α.app U).hom := by
      have h := α.naturality f
      exact congrArg CommRingCat.Hom.hom h
    let e₁ :=
      ModuleCat.restrictScalarsComp' ((O.map f).hom) (α.app V).hom
        ((α.app V).hom.comp (O.map f).hom) rfl
    let e₂ :=
      ModuleCat.restrictScalarsComp' (α.app U).hom (O'.map f).hom
        ((O'.map f).hom.comp (α.app U).hom) rfl
    let ec := ModuleCat.restrictScalarsCongr hα
    let u := (ModuleCat.extendRestrictScalarsAdj (α.app V).hom).unit.app (M.obj V)
    exact
      M.map f ≫
        (ModuleCat.restrictScalars (O.map f).hom).map u ≫
        e₁.inv.app ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)) ≫
        ec.hom.app ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)) ≫
        e₂.hom.app ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V))

  let baseMap {M : CommRingPresheafModule O} {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
      (ModuleCat.extendScalars (α.app U).hom).obj (M.obj U) ⟶
        (ModuleCat.restrictScalars (O'.map f).hom).obj
          ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)) :=
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (α.app U).hom (baseMapAux f)

  have h_base {M : CommRingPresheafModule O} {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (m : M.obj U) :
      baseMap f ((1 : O'.obj U) ⊗ₜ[O.obj U,(α.app U).hom] m) =
        baseMapAux f m := by
    change
      ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (α.app U).hom)
        (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (α.app U).hom (baseMapAux f))) m = baseMapAux f m
    exact congrArg (fun k => k m)
      ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (α.app U).hom).apply_symm_apply
        (baseMapAux f))

  have h_aux_apply {M : CommRingPresheafModule O} {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
      (m : M.obj U) :
      (show (ModuleCat.extendScalars (α.app V).hom).obj (M.obj V) from baseMapAux f m) =
        (1 : O'.obj V) ⊗ₜ[O.obj V,(α.app V).hom]
          (show M.obj V from M.map f m) := by
    have h_unit :
        (ModuleCat.extendRestrictScalarsAdj (α.app V).hom).unit.app (M.obj V)
            (show M.obj V from M.map f m) =
          (1 : O'.obj V) ⊗ₜ[O.obj V,(α.app V).hom] (show M.obj V from M.map f m) := by
      exact ModuleCat.extendRestrictScalarsAdj_unit_app_apply
        (α.app V).hom (M.obj V) (show M.obj V from M.map f m)
    dsimp [baseMapAux]
    rw [h_unit]
    simp only [Category.assoc, ModuleCat.restrictScalars.map_apply,
      ModuleCat.restrictScalarsComp'App_inv_apply,
      ModuleCat.restrictScalarsCongr_hom_app]
    rfl

  have h_aux_apply' {M : CommRingPresheafModule O} {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
      (m : M.obj U) :
      (show (ModuleCat.restrictScalars (O'.map f).hom).obj
          ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)) from baseMapAux f m) =
        (show (ModuleCat.restrictScalars (O'.map f).hom).obj
          ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)) from
          (1 : O'.obj V) ⊗ₜ[O.obj V,(α.app V).hom]
            (show M.obj V from M.map f m)) := by
    exact h_aux_apply f m

  have h_ext_test {R S : Type u} [CommRing R] [CommRing S]
      (f : R →+* S) {M : ModuleCat R} {N : ModuleCat S}
      {p q : (ModuleCat.extendScalars f).obj M ⟶ N}
      (h : ∀ m : M,
        p ((1 : S) ⊗ₜ[R,f] m) = q ((1 : S) ⊗ₜ[R,f] m)) : p = q := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    let one : (ModuleCat.restrictScalars f).obj (ModuleCat.of S S) := by
      change S
      exact 1
    change p (one ⊗ₜ[R] m) = q (one ⊗ₜ[R] m)
    exact h m

  have h_id (M : CommRingPresheafModule O) (U : (Opens X)ᵒᵖ) :
      baseMap (M := M) (𝟙 U) =
        (ModuleCat.restrictScalarsId' (O'.map (𝟙 U)).hom
          (congrArg CommRingCat.Hom.hom (O'.map_id U))).inv.app
          ((ModuleCat.extendScalars (α.app U).hom).obj (M.obj U)) := by
    apply h_ext_test
    intro m
    rw [h_base]
    simp only [baseMapAux, M.map_id, O.map_id, O'.map_id,
      ModuleCat.restrictScalarsId'App_inv_apply]
    rfl

  have h_comp {M : CommRingPresheafModule O}
      {U V W : (Opens X)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
      baseMap (M := M) (f ≫ g) =
        baseMap f ≫
          (ModuleCat.restrictScalars (O'.map f).hom).map (baseMap g) ≫
          (ModuleCat.restrictScalarsComp' (O'.map f).hom (O'.map g).hom
            (O'.map (f ≫ g)).hom
            (congrArg CommRingCat.Hom.hom (O'.map_comp f g))).inv.app
            ((ModuleCat.extendScalars (α.app W).hom).obj (M.obj W)) := by
    apply h_ext_test
    intro m
    change
      baseMap (M := M) (f ≫ g)
          ((1 : O'.obj U) ⊗ₜ[O.obj U,(α.app U).hom] m) =
        (ModuleCat.restrictScalarsComp' (O'.map f).hom (O'.map g).hom
            (O'.map (f ≫ g)).hom
            (congrArg CommRingCat.Hom.hom (O'.map_comp f g))).inv.app
          ((ModuleCat.extendScalars (α.app W).hom).obj (M.obj W))
          ((ModuleCat.restrictScalars (O'.map f).hom).map (baseMap g)
            ((show (ModuleCat.extendScalars (α.app V).hom).obj (M.obj V) from
              baseMap (M := M) f
                ((1 : O'.obj U) ⊗ₜ[O.obj U,(α.app U).hom] m))))
    rw [h_base (f := f ≫ g)]
    rw [h_base (f := f)]
    change
      (show (ModuleCat.extendScalars (α.app W).hom).obj (M.obj W) from
        baseMapAux (f ≫ g) m) =
        (show (ModuleCat.extendScalars (α.app W).hom).obj (M.obj W) from
          (ModuleCat.restrictScalarsComp' (O'.map f).hom (O'.map g).hom
            (O'.map (f ≫ g)).hom
            (congrArg CommRingCat.Hom.hom (O'.map_comp f g))).inv.app
            ((ModuleCat.extendScalars (α.app W).hom).obj (M.obj W))
            ((ModuleCat.restrictScalars (O'.map f).hom).map
              (baseMap g)
              (show (ModuleCat.restrictScalars (O'.map f).hom).obj
                  ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)) from
                baseMapAux f m)))
    rw [h_aux_apply' (f := f ≫ g) (m := m)]
    rw [h_aux_apply' (f := f)]
    change
      _ =
        (ModuleCat.restrictScalarsComp' (O'.map f).hom (O'.map g).hom
            (O'.map (f ≫ g)).hom
            (congrArg CommRingCat.Hom.hom (O'.map_comp f g))).inv.app
          ((ModuleCat.extendScalars (α.app W).hom).obj (M.obj W))
          (show ((ModuleCat.restrictScalars (O'.map g).hom) ⋙
              (ModuleCat.restrictScalars (O'.map f).hom)).obj
               ((ModuleCat.extendScalars (α.app W).hom).obj (M.obj W)) from
            (show (ModuleCat.restrictScalars (O'.map g).hom).obj
                ((ModuleCat.extendScalars (α.app W).hom).obj (M.obj W)) from
              baseMap g
                ((1 : O'.obj V) ⊗ₜ[O.obj V,(α.app V).hom]
                  (show M.obj V from M.map f m))))
    rw [h_base (f := g) (m := show M.obj V from M.map f m)]
    rw [h_aux_apply' (f := g) (m := show M.obj V from M.map f m)]
    simp only [ModuleCat.restrictScalarsComp'App_inv_apply]
    rw [M.map_comp_apply]
    rfl

  let pointwiseChange : CommRingPresheafModule O ⥤ CommRingPresheafModule O' := {
    obj M :=
      { obj := fun U =>
          (ModuleCat.extendScalars (α.app U).hom).obj (M.obj U)
        map := fun f => baseMap f
        map_id := h_id M
        map_comp := fun f g => h_comp f g }
    map := fun {M N} φ =>
      { app := fun U => (ModuleCat.extendScalars (α.app U).hom).map (φ.app U)
        naturality := by
          intro U V f
          apply h_ext_test
          intro m
          change
            (show ((ModuleCat.restrictScalars (O'.map f).hom).obj
                ((ModuleCat.extendScalars (α.app V).hom).obj (N.obj V))) from
              ((ModuleCat.restrictScalars (O'.map f).hom).map
                ((ModuleCat.extendScalars (α.app V).hom).map (φ.app V)))
                (baseMap (M := M) f
                  ((1 : O'.obj U) ⊗ₜ[O.obj U,(α.app U).hom] m))) =
            (show ((ModuleCat.restrictScalars (O'.map f).hom).obj
                ((ModuleCat.extendScalars (α.app V).hom).obj (N.obj V))) from
              baseMap (M := N) f
                ((ModuleCat.extendScalars (α.app U).hom).map (φ.app U)
                  ((1 : O'.obj U) ⊗ₜ[O.obj U,(α.app U).hom] m)))
          rw [h_base (M := M) (f := f) (m := m)]
          have hleft := congrArg
            (fun z => (ModuleCat.restrictScalars (O'.map f).hom).map
              ((ModuleCat.extendScalars (α.app V).hom).map (φ.app V)) z)
            (h_aux_apply' (M := M) (f := f) (m := m))
          rw [hleft]
          simp only [ModuleCat.ExtendScalars.map_tmul,
            ModuleCat.restrictScalars.map_apply]
          change
            _ =
              (show ((ModuleCat.restrictScalars (O'.map f).hom).obj
                  ((ModuleCat.extendScalars (α.app V).hom).obj (N.obj V))) from
                baseMap (M := N) f
                  ((1 : O'.obj U) ⊗ₜ[O.obj U,(α.app U).hom] (φ.app U m)))
          rw [h_base (M := N) (f := f) (m := (φ.app U) m)]
          rw [h_aux_apply (M := N) (f := f) (m := (φ.app U) m)]
          change
            (show ((ModuleCat.restrictScalars (O'.map f).hom).obj
                ((ModuleCat.extendScalars (α.app V).hom).obj (N.obj V))) from
              ((ModuleCat.restrictScalars (O'.map f).hom).map
                ((ModuleCat.extendScalars (α.app V).hom).map (φ.app V)))
                ((1 : O'.obj V) ⊗ₜ[O.obj V,(α.app V).hom]
                  (show M.obj V from M.map f m))) =
            (1 : O'.obj V) ⊗ₜ[O.obj V,(α.app V).hom]
              (show N.obj V from N.map f (φ.app U m))
          change
            (show ((ModuleCat.restrictScalars (O'.map f).hom).obj
                ((ModuleCat.extendScalars (α.app V).hom).obj (N.obj V))) from
              ((ModuleCat.extendScalars (α.app V).hom).map (φ.app V))
                ((1 : O'.obj V) ⊗ₜ[O.obj V,(α.app V).hom]
                  (show M.obj V from M.map f m))) =
              (1 : O'.obj V) ⊗ₜ[O.obj V,(α.app V).hom]
                (show N.obj V from N.map f (φ.app U m))
          rw [ModuleCat.ExtendScalars.map_tmul]
          rw [PresheafOfModules.naturality_apply φ f m] }
    map_id := by
      intro M
      apply PresheafOfModules.hom_ext
      intro U
      ext m
      simp
    map_comp := by
      intro M N P φ ψ
      apply PresheafOfModules.hom_ext
      intro U
      ext m
      simp }

  let restriction := restrictionOfScalars α_R

  let unit : 𝟭 (CommRingPresheafModule O) ⟶
      pointwiseChange ⋙ restriction := {
    app := fun M =>
      { app := fun U => by
          dsimp [restriction, pointwiseChange, restrictionOfScalars,
            PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
            PresheafOfModules.pushforward₀Obj,
            PresheafOfModules.restrictScalars,
            PresheafOfModules.restrictScalarsObj]
          let hαU : (α.app U).hom =
              ((asIdentityRingPresheafMorphism α_R).app U).hom := by
            ext r
            simp [asIdentityRingPresheafMorphism, α_R,
              commRingPresheafMorphismToRingPresheaf]
          convert
            ((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).unit.app (M.obj U) ≫
              (ModuleCat.restrictScalarsCongr hαU).hom.app
                ((ModuleCat.extendScalars (α.app U).hom).obj (M.obj U))) using 1 <;>
            simp [Functor.id_obj, commRingPresheafMorphismToRingPresheaf,
              asIdentityRingPresheafMorphism]
        naturality := by
          intro U V f
          apply ModuleCat.hom_ext
          ext m
          change
            (ModuleCat.extendRestrictScalarsAdj (α.app V).hom).unit.app (M.obj V)
                (show M.obj V from M.map f m) =
              baseMap f
                ((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).unit.app
                  (M.obj U) m)
          rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply,
            ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
          rw [h_base]
          rw [h_aux_apply] }
    naturality := by
      intro M N φ
      apply PresheafOfModules.hom_ext
      intro U
      ext m
      change
        (ModuleCat.extendRestrictScalarsAdj (α.app U).hom).unit.app (N.obj U)
            (φ.app U m) =
          (ModuleCat.extendScalars (α.app U).hom).map (φ.app U)
            ((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).unit.app
              (M.obj U) m)
      rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply,
        ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
      rw [ModuleCat.ExtendScalars.map_tmul] }

  let counit : restriction ⋙ pointwiseChange ⟶
      𝟭 (CommRingPresheafModule O') := {
    app := fun G =>
      { app := fun U => by
          dsimp [restriction, pointwiseChange, restrictionOfScalars,
            PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
            PresheafOfModules.pushforward₀Obj,
            PresheafOfModules.restrictScalars,
            PresheafOfModules.restrictScalarsObj]
          let hαU : ((asIdentityRingPresheafMorphism α_R).app U).hom =
              (α_R.app U).hom := by
            ext r
            simp [asIdentityRingPresheafMorphism, α_R,
              commRingPresheafMorphismToRingPresheaf]
          convert
            ((ModuleCat.extendScalars (α_R.app U).hom).map
                ((ModuleCat.restrictScalarsCongr hαU).hom.app (G.obj U)) ≫
              (ModuleCat.extendRestrictScalarsAdj (α_R.app U).hom).counit.app (G.obj U)) using 1 <;>
            simp [Functor.id_obj, commRingPresheafMorphismToRingPresheaf,
              asIdentityRingPresheafMorphism]
        naturality := by
          intro U V f
          apply h_ext_test
          intro m
          change
            (ModuleCat.restrictScalars (O'.map f).hom).map
                ((ModuleCat.extendRestrictScalarsAdj (α.app V).hom).counit.app
                  (G.obj V))
                (baseMap (M := restriction.obj G) f
                ((1 : O'.obj U) ⊗ₜ[O.obj U,(α.app U).hom] m)) =
            G.map f
              ((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).counit.app
                (G.obj U)
                ((1 : O'.obj U) ⊗ₜ[O.obj U,(α.app U).hom] m))
          rw [h_base (M := restriction.obj G) (f := f)]
          rw [h_aux_apply (M := restriction.obj G) (f := f)]
          simp only [ModuleCat.restrictScalars.map_apply,
            ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul] }
    naturality := by
      intro G H φ
      apply PresheafOfModules.hom_ext
      intro U
      exact (ModuleCat.extendRestrictScalarsAdj (α.app U).hom).counit.naturality
        (φ.app U) }

  let pointwiseAdj : pointwiseChange ⊣ restriction :=
    Adjunction.mkOfUnitCounit {
      unit := unit
      counit := counit
      left_triangle := by
        ext M U m
        simp [unit, counit, pointwiseChange,
          ModuleCat.extendRestrictScalarsAdj_unit_app_apply,
          ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul]
      right_triangle := by
        ext G U m
        simp [unit, counit,
          ModuleCat.extendRestrictScalarsAdj_unit_app_apply,
          ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul] }

  sorry

end

example {X : TopCat.{u}} {O : CommRingPresheaf X}
    (F : CommRingPresheafModule O) (x : X) : True := by
  let R := O ⋙ (forget₂ CommRingCat RingCat)
  let R_x := (OpenNhds.inclusion x).op ⋙ R
  let F_x : PresheafOfModules R_x := {
    obj := fun U => F.obj ((OpenNhds.inclusion x).op.obj U)
    map := fun f => F.map ((OpenNhds.inclusion x).op.map f)
    map_id := by
      intro U
      dsimp [R_x]
      rw [(OpenNhds.inclusion x).map_id, CategoryTheory.op_id, F.map_id]
    map_comp := by
      intro U V W f g
      dsimp [R_x]
      rw [(OpenNhds.inclusion x).map_comp, CategoryTheory.op_comp, F.map_comp]
      }
  let cR := colimit.cocone R_x
  let hcR := colimit.isColimit R_x
  let cF := colimit.cocone F_x.presheaf
  let hcF := colimit.isColimit F_x.presheaf
  let β : F_x.presheaf ⟶
      (Functor.const (OpenNhds x)ᵒᵖ).obj (AddCommGrpCat.of (↑cF.pt)) := 0
  let g := (PresheafOfModules.ModuleColimit.homEquiv' hcR hcF).symm β
  have : (PresheafOfModules.ModuleColimit hcR hcF →+ (↑cF.pt)) := g
  trivial

example {X : TopCat.{u}} {O O' : CommRingPresheaf X} (α : O ⟶ O') :
    restrictionOfScalars (commRingPresheafMorphismToRingPresheaf α) =
      PresheafOfModules.restrictScalars (commRingPresheafMorphismToRingPresheaf α) := by
  rfl

end Formalization.Books.Sheaves.Unit14
