import Formalization.Books.Sheaves.Unit05.PresheavesOfAlgebraicStructures
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Sheaves on Spaces, Chapter 6: Presheaves of modules

The source section is formalized with Mathlib's canonical
`PresheafOfModules` construction.  Its objects carry a module over the ring
assigned to every open and semilinear restriction maps; its morphisms are the
componentwise linear maps satisfying the naturality condition.  Thus the
canonical structure subsumes the source's equivalent presentation by an
abelian presheaf with an action of the presheaf of rings.

For a morphism of presheaves of rings, Mathlib's presheaf change-of-rings
API supplies restriction of scalars and the canonical left-adjoint
`pullback`.  The latter is the usable categorical realization of the
pointwise tensor-product presheaf in the source.
-/

namespace Formalization.Books.Sheaves.Unit06

open CategoryTheory Opposite TopologicalSpace
open scoped ChangeOfRings

universe w v

/-! ## Presheaves of rings and modules -/

/-- A presheaf of rings on `X`, represented by Mathlib's canonical functor. -/
abbrev RingPresheaf (X : TopCat.{v}) := TopCat.Presheaf (RingCat.{w}) X

/-- A morphism of presheaves of rings. -/
abbrev RingPresheafMorphism {X : TopCat.{v}} {O₁ O₂ : RingPresheaf.{w, v} X} :=
  O₁ ⟶ O₂

/-- A presheaf of modules over a presheaf of rings. -/
abbrev PresheafOfOModules {X : TopCat.{v}} (O : RingPresheaf.{w, v} X) :=
  _root_.PresheafOfModules.{w} O

/-- The category `PMod(O)` of presheaves of `O`-modules. -/
abbrev PMod {X : TopCat.{v}} (O : RingPresheaf.{w, v} X) :=
  PresheafOfOModules O

/-- A morphism of presheaves of `O`-modules. -/
abbrev PresheafOfOModulesMorphism {X : TopCat.{v}}
    {O : RingPresheaf.{w, v} X} {F G : PMod O} := F ⟶ G

/-- The source's `Hom_O(F, G)`, represented by the canonical hom type. -/
abbrev OModuleHom {X : TopCat.{v}} {O : RingPresheaf.{w, v} X}
    (F G : PMod O) := F ⟶ G

/-- The abelian-group-valued presheaf underlying a presheaf of modules. -/
noncomputable abbrev underlyingAbelianPresheaf {X : TopCat.{v}}
    {O : RingPresheaf.{w, v} X} (F : PMod O) := F.presheaf

/-- The module of sections over an open set. -/
abbrev moduleOn {X : TopCat.{v}} {O : RingPresheaf.{w, v} X}
    (F : PMod O) (U : Opens X) := F.obj (op U)

/-- The restriction morphism of a presheaf of modules along an open inclusion. -/
abbrev moduleRestriction {X : TopCat.{v}} {O : RingPresheaf.{w, v} X}
    (F : PMod O) {U V : Opens X} (h : V ≤ U) :
    F.obj (op U) ⟶
      (ModuleCat.restrictScalars (O.map (homOfLE h).op).hom).obj (F.obj (op V)) :=
  F.map (homOfLE h).op

/-!
The following theorem exposes the source's commuting restriction square in
the canonical `PresheafOfModules.Hom` interface.  The module action and the
linearity of every component are fields of the canonical bundled modules.
-/

/-- A morphism of presheaves of modules commutes with restriction maps. -/
theorem presheafOfOModulesMorphism_naturality {X : TopCat.{v}}
    {O : RingPresheaf.{w, v} X} {F G : PMod O}
    (φ : PresheafOfOModulesMorphism (F := F) (G := G))
    {U V : Opens X} (h : V ≤ U) :
    moduleRestriction F h ≫
        (ModuleCat.restrictScalars (O.map (homOfLE h).op).hom).map
          (φ.app (op V)) =
      φ.app (op U) ≫ moduleRestriction G h := by
  exact φ.naturality (homOfLE h).op

/-- Every component of an `O`-module morphism is linear over the sections. -/
theorem presheafOfOModulesMorphism_smul {X : TopCat.{v}}
    {O : RingPresheaf.{w, v} X} {F G : PMod O}
    (φ : PresheafOfOModulesMorphism (F := F) (G := G)) (U : Opens X)
    (r : O.obj (op U)) (m : F.obj (op U)) :
    φ.app (op U) (r • m) = r • φ.app (op U) m := by
  exact (φ.app (op U)).hom.map_smul r m

/-!
`PresheafOfModules.pullback` is parameterized by a functor between the
indexing categories.  For the present section that functor is the identity
on `Opens X`; this helper only changes the type of the ring morphism and
introduces no additional mathematical data.
-/

/-- View a ring-presheaf morphism as one over the identity on the opens. -/
noncomputable def asIdentityRingPresheafMorphism {X : TopCat.{v}}
    {O₁ O₂ : RingPresheaf.{w, v} X} (α : O₁ ⟶ O₂) :
    O₁ ⟶ (𝟭 (Opens X)).op ⋙ O₂ := by
  exact α ≫
    (Functor.isoWhiskerRight (Functor.opId (Opens X)) O₂ ≪≫
      Functor.leftUnitor O₂).inv

/-! ## Restriction of scalars -/

/-- Restriction of scalars for a morphism of presheaves of rings. -/
noncomputable abbrev restrictionOfScalars {X : TopCat.{v}}
    {O₁ O₂ : RingPresheaf.{w, v} X} (α : O₁ ⟶ O₂) :
    PMod O₂ ⥤ PMod O₁ :=
  _root_.PresheafOfModules.pushforward
    (F := 𝟭 (Opens X)) (asIdentityRingPresheafMorphism α)

/-- The restriction of an individual presheaf of modules to the smaller ring. -/
noncomputable abbrev restrictedModule {X : TopCat.{v}}
    {O₁ O₂ : RingPresheaf.{w, v} X} (α : O₁ ⟶ O₂) (F : PMod O₂) : PMod O₁ :=
  (restrictionOfScalars α).obj F

/-! ## Tensor product and change of rings -/

/-!
The Mathlib pullback existence theorem is stated for a small indexing
category and a presheaf of rings in the same universe.  The change-of-rings
interface below follows that established universe convention for `Opens X`;
the imported canonical instance supplies the right adjoint for the
restriction-of-scalars functor.
-/

/-!
This private spelling keeps the source order: the tensor-product object is
introduced before the public change-of-rings functor, while both reuse the
same canonical pullback functor.
-/

noncomputable abbrev changeOfRingsCore {X : TopCat.{w}}
    {O₁ O₂ : RingPresheaf.{w, w} X} (α : O₁ ⟶ O₂) :
    PMod O₁ ⥤ PMod O₂ :=
  _root_.PresheafOfModules.pullback
    (F := 𝟭 (Opens X)) (asIdentityRingPresheafMorphism α)

/-- The tensor product presheaf described in the source. -/
noncomputable abbrev tensorProductPresheaf {X : TopCat.{w}}
    {O₁ O₂ : RingPresheaf.{w, w} X} (α : O₁ ⟶ O₂) (G : PMod O₁) : PMod O₂ :=
  (changeOfRingsCore α).obj G

/-!
The textbook uses commutative rings for the displayed sectionwise tensor
product.  The canonical `PresheafOfModules` API above is formulated for
`RingCat`, so the sectionwise bridge below starts with a commutative-ring
presheaf and then forgets to `RingCat`.  This keeps the existing pullback
construction unchanged while making the pointwise extension-of-scalars
object explicit.
-/

/-- A presheaf of commutative rings, viewed before forgetting to `RingCat`. -/
abbrev CommRingPresheaf (X : TopCat.{w}) :=
  TopCat.Presheaf (CommRingCat.{w}) X

/-!
This specialization is used by later stalk and sheaf constructions while
retaining the canonical `RingCat`-valued presheaf-of-modules API.
-/

/-- A presheaf of modules over a commutative-ring presheaf. -/
abbrev CommRingPresheafModule {X : TopCat.{w}} (O : CommRingPresheaf X) :=
  PMod (O ⋙ (forget₂ CommRingCat RingCat))

/-- The underlying `RingCat` morphism of a commutative-ring-presheaf map. -/
abbrev commRingPresheafMorphismToRingPresheaf
    {X : TopCat.{w}} {O₁ O₂ : CommRingPresheaf X} (α : O₁ ⟶ O₂) :
    (O₁ ⋙ (forget₂ CommRingCat RingCat)) ⟶
      (O₂ ⋙ (forget₂ CommRingCat RingCat)) :=
  Functor.whiskerRight α (forget₂ CommRingCat RingCat)

/-- The extension-of-scalars module on the sections over an open.

Its underlying module is the canonical `O₂(U) ⊗[O₁(U)] G(U)` extension
of scalars supplied by `ModuleCat.extendScalars`. -/
noncomputable abbrev sectionwiseExtensionOfScalars
    {X : TopCat.{w}} {O₁ O₂ : CommRingPresheaf X}
    (α : O₁ ⟶ O₂)
    (G : PMod (O₁ ⋙ (forget₂ CommRingCat RingCat))) (U : Opens X) :
    ModuleCat (O₂.obj (op U)) :=
  (ModuleCat.extendScalars (α.app (op U)).hom).obj
    (ModuleCat.of (O₁.obj (op U)) (G.obj (op U)))

/-- The pointwise tensor formula for the tensor-product presheaf. -/
theorem tensorProductPresheaf_section_iso
    {X : TopCat.{w}} {O₁ O₂ : CommRingPresheaf X}
    (α : O₁ ⟶ O₂)
    (G : PMod (O₁ ⋙ (forget₂ CommRingCat RingCat))) (U : Opens X) :
    Nonempty
      ((tensorProductPresheaf (commRingPresheafMorphismToRingPresheaf α) G).obj
          (op U) ≅
        sectionwiseExtensionOfScalars α G U) := by
  let R := O₁ ⋙ (forget₂ CommRingCat RingCat)
  let R' := O₂ ⋙ (forget₂ CommRingCat RingCat)
  let α_R := commRingPresheafMorphismToRingPresheaf α
  let baseMapAux {M : PMod R} {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
      M.obj U ⟶
        (ModuleCat.restrictScalars (α.app U).hom).obj
          ((ModuleCat.restrictScalars (O₂.map f).hom).obj
            ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V))) := by
    have hα :
        (α.app V).hom.comp ((O₁.map f).hom) =
          ((O₂.map f).hom).comp (α.app U).hom := by
      have h := α.naturality f
      exact congrArg CommRingCat.Hom.hom h
    let e₁ :=
      ModuleCat.restrictScalarsComp' ((O₁.map f).hom) (α.app V).hom
        ((α.app V).hom.comp (O₁.map f).hom) rfl
    let e₂ :=
      ModuleCat.restrictScalarsComp' (α.app U).hom (O₂.map f).hom
        ((O₂.map f).hom.comp (α.app U).hom) rfl
    let ec := ModuleCat.restrictScalarsCongr hα
    let u := (ModuleCat.extendRestrictScalarsAdj (α.app V).hom).unit.app (M.obj V)
    exact
      M.map f ≫
        (ModuleCat.restrictScalars (O₁.map f).hom).map u ≫
        e₁.inv.app ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)) ≫
        ec.hom.app ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)) ≫
        e₂.hom.app ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V))

  let baseMap {M : PMod R} {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
      (ModuleCat.extendScalars (α.app U).hom).obj (M.obj U) ⟶
        (ModuleCat.restrictScalars (O₂.map f).hom).obj
          ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)) :=
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (α.app U).hom (baseMapAux f)

  have h_base {M : PMod R} {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (m : M.obj U) :
      baseMap f ((1 : O₂.obj U) ⊗ₜ[O₁.obj U,(α.app U).hom] m) =
        baseMapAux f m := by
    change
      ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (α.app U).hom)
        (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (α.app U).hom (baseMapAux f))) m = baseMapAux f m
    exact congrArg (fun k => k m)
      ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (α.app U).hom).apply_symm_apply
        (baseMapAux f))

  have h_aux_apply {M : PMod R} {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
      (m : M.obj U) :
      (show (ModuleCat.extendScalars (α.app V).hom).obj (M.obj V) from baseMapAux f m) =
        (1 : O₂.obj V) ⊗ₜ[O₁.obj V,(α.app V).hom]
          (show M.obj V from M.map f m) := by
    have h_unit :
        (ModuleCat.extendRestrictScalarsAdj (α.app V).hom).unit.app (M.obj V)
            (show M.obj V from M.map f m) =
          (1 : O₂.obj V) ⊗ₜ[O₁.obj V,(α.app V).hom] (show M.obj V from M.map f m) := by
      exact ModuleCat.extendRestrictScalarsAdj_unit_app_apply
        (α.app V).hom (M.obj V) (show M.obj V from M.map f m)
    dsimp [baseMapAux]
    rw [h_unit]
    rfl

  have h_aux_apply' {M : PMod R} {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
      (m : M.obj U) :
      (show (ModuleCat.restrictScalars (O₂.map f).hom).obj
          ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)) from baseMapAux f m) =
        (show (ModuleCat.restrictScalars (O₂.map f).hom).obj
          ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)) from
          (1 : O₂.obj V) ⊗ₜ[O₁.obj V,(α.app V).hom]
            (show M.obj V from M.map f m)) := by
    exact h_aux_apply f m

  have h_ext_test {R S : Type w} [CommRing R] [CommRing S]
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

  have h_id (M : PMod R) (U : (Opens X)ᵒᵖ) :
      baseMap (M := M) (𝟙 U) =
        (ModuleCat.restrictScalarsId' (O₂.map (𝟙 U)).hom
          (congrArg CommRingCat.Hom.hom (O₂.map_id U))).inv.app
          ((ModuleCat.extendScalars (α.app U).hom).obj (M.obj U)) := by
    apply h_ext_test
    intro m
    rw [h_base]
    simp only [baseMapAux, M.map_id]
    rfl

  have h_comp {M : PMod R}
      {U V W : (Opens X)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
      baseMap (M := M) (f ≫ g) =
        baseMap f ≫
          (ModuleCat.restrictScalars (O₂.map f).hom).map (baseMap g) ≫
          (ModuleCat.restrictScalarsComp' (O₂.map f).hom (O₂.map g).hom
            (O₂.map (f ≫ g)).hom
            (congrArg CommRingCat.Hom.hom (O₂.map_comp f g))).inv.app
            ((ModuleCat.extendScalars (α.app W).hom).obj (M.obj W)) := by
    apply h_ext_test
    intro m
    change
      baseMap (M := M) (f ≫ g)
          ((1 : O₂.obj U) ⊗ₜ[O₁.obj U,(α.app U).hom] m) =
        (ModuleCat.restrictScalarsComp' (O₂.map f).hom (O₂.map g).hom
            (O₂.map (f ≫ g)).hom
            (congrArg CommRingCat.Hom.hom (O₂.map_comp f g))).inv.app
          ((ModuleCat.extendScalars (α.app W).hom).obj (M.obj W))
          ((ModuleCat.restrictScalars (O₂.map f).hom).map (baseMap g)
            ((show (ModuleCat.extendScalars (α.app V).hom).obj (M.obj V) from
              baseMap (M := M) f
                ((1 : O₂.obj U) ⊗ₜ[O₁.obj U,(α.app U).hom] m))))
    rw [h_base (f := f ≫ g)]
    rw [h_base (f := f)]
    change
      (show (ModuleCat.extendScalars (α.app W).hom).obj (M.obj W) from
        baseMapAux (f ≫ g) m) =
        (show (ModuleCat.extendScalars (α.app W).hom).obj (M.obj W) from
          (ModuleCat.restrictScalarsComp' (O₂.map f).hom (O₂.map g).hom
            (O₂.map (f ≫ g)).hom
            (congrArg CommRingCat.Hom.hom (O₂.map_comp f g))).inv.app
            ((ModuleCat.extendScalars (α.app W).hom).obj (M.obj W))
            ((ModuleCat.restrictScalars (O₂.map f).hom).map
              (baseMap g)
              (show (ModuleCat.restrictScalars (O₂.map f).hom).obj
                  ((ModuleCat.extendScalars (α.app V).hom).obj (M.obj V)) from
                baseMapAux f m)))
    rw [h_aux_apply' (f := f ≫ g) (m := m)]
    rw [h_aux_apply' (f := f)]
    change
      _ =
        (ModuleCat.restrictScalarsComp' (O₂.map f).hom (O₂.map g).hom
            (O₂.map (f ≫ g)).hom
            (congrArg CommRingCat.Hom.hom (O₂.map_comp f g))).inv.app
          ((ModuleCat.extendScalars (α.app W).hom).obj (M.obj W))
          (show ((ModuleCat.restrictScalars (O₂.map g).hom) ⋙
              (ModuleCat.restrictScalars (O₂.map f).hom)).obj
               ((ModuleCat.extendScalars (α.app W).hom).obj (M.obj W)) from
            (show (ModuleCat.restrictScalars (O₂.map g).hom).obj
                ((ModuleCat.extendScalars (α.app W).hom).obj (M.obj W)) from
              baseMap g
                ((1 : O₂.obj V) ⊗ₜ[O₁.obj V,(α.app V).hom]
                  (show M.obj V from M.map f m))))
    rw [h_base (f := g) (m := show M.obj V from M.map f m)]
    rw [h_aux_apply' (f := g) (m := show M.obj V from M.map f m)]
    rw [M.map_comp_apply]
    rfl

  let pointwiseChange : PMod R ⥤ PMod R' := {
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
            (show ((ModuleCat.restrictScalars (O₂.map f).hom).obj
                ((ModuleCat.extendScalars (α.app V).hom).obj (N.obj V))) from
              ((ModuleCat.restrictScalars (O₂.map f).hom).map
                ((ModuleCat.extendScalars (α.app V).hom).map (φ.app V)))
                (baseMap (M := M) f
                  ((1 : O₂.obj U) ⊗ₜ[O₁.obj U,(α.app U).hom] m))) =
            (show ((ModuleCat.restrictScalars (O₂.map f).hom).obj
                ((ModuleCat.extendScalars (α.app V).hom).obj (N.obj V))) from
              baseMap (M := N) f
                ((ModuleCat.extendScalars (α.app U).hom).map (φ.app U)
                  ((1 : O₂.obj U) ⊗ₜ[O₁.obj U,(α.app U).hom] m)))
          rw [h_base (M := M) (f := f) (m := m)]
          have hleft := congrArg
            (fun z => (ModuleCat.restrictScalars (O₂.map f).hom).map
              ((ModuleCat.extendScalars (α.app V).hom).map (φ.app V)) z)
            (h_aux_apply' (M := M) (f := f) (m := m))
          rw [hleft]
          simp only [ModuleCat.ExtendScalars.map_tmul]
          change
            _ =
              (show ((ModuleCat.restrictScalars (O₂.map f).hom).obj
                  ((ModuleCat.extendScalars (α.app V).hom).obj (N.obj V))) from
                baseMap (M := N) f
                  ((1 : O₂.obj U) ⊗ₜ[O₁.obj U,(α.app U).hom] (φ.app U m)))
          rw [h_base (M := N) (f := f) (m := (φ.app U) m)]
          rw [h_aux_apply (M := N) (f := f) (m := (φ.app U) m)]
          change
            (show ((ModuleCat.restrictScalars (O₂.map f).hom).obj
                ((ModuleCat.extendScalars (α.app V).hom).obj (N.obj V))) from
              ((ModuleCat.restrictScalars (O₂.map f).hom).map
                ((ModuleCat.extendScalars (α.app V).hom).map (φ.app V)))
                ((1 : O₂.obj V) ⊗ₜ[O₁.obj V,(α.app V).hom]
                  (show M.obj V from M.map f m))) =
            (1 : O₂.obj V) ⊗ₜ[O₁.obj V,(α.app V).hom]
              (show N.obj V from N.map f (φ.app U m))
          change
            (show ((ModuleCat.restrictScalars (O₂.map f).hom).obj
                ((ModuleCat.extendScalars (α.app V).hom).obj (N.obj V))) from
              ((ModuleCat.extendScalars (α.app V).hom).map (φ.app V))
                ((1 : O₂.obj V) ⊗ₜ[O₁.obj V,(α.app V).hom]
                  (show M.obj V from M.map f m))) =
              (1 : O₂.obj V) ⊗ₜ[O₁.obj V,(α.app V).hom]
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

  let unit : 𝟭 (PMod R) ⟶
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
                ((ModuleCat.extendScalars (α.app U).hom).obj (M.obj U))) using 1
          all_goals
            simp [R]
        naturality := by
          intro U V f
          dsimp [pointwiseChange, restriction, restrictionOfScalars,
            PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
            PresheafOfModules.pushforward₀Obj,
            PresheafOfModules.restrictScalars,
            PresheafOfModules.restrictScalarsObj]
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
          change
            (show (ModuleCat.extendScalars (α.app V).hom).obj (M.obj V) from
              (1 : O₂.obj V) ⊗ₜ[O₁.obj V,(α.app V).hom]
                (show M.obj V from M.map f m)) =
              (show (ModuleCat.extendScalars (α.app V).hom).obj (M.obj V) from
                baseMap f
                  ((1 : O₂.obj U) ⊗ₜ[O₁.obj U,(α.app U).hom]
                    (show M.obj U from m)))
          rw [h_base (M := M) (f := f) (m := m)]
          rw [h_aux_apply (M := M) (f := f) (m := m)]
          rfl }
    naturality := by
      intro M N φ
      dsimp [pointwiseChange, restriction, restrictionOfScalars,
        PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
        PresheafOfModules.pushforward₀Obj,
        PresheafOfModules.restrictScalars,
        PresheafOfModules.restrictScalarsObj]
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
      change
        (show (ModuleCat.extendScalars (α.app U).hom).obj (N.obj U) from
          (1 : O₂.obj U) ⊗ₜ[O₁.obj U,(α.app U).hom] (φ.app U m)) =
        (ModuleCat.extendScalars (α.app U).hom).map (φ.app U)
          ((1 : O₂.obj U) ⊗ₜ[O₁.obj U,(α.app U).hom] m)
      symm
      exact ModuleCat.ExtendScalars.map_tmul (α.app U).hom (φ.app U) 1 m }

  let counit : restriction ⋙ pointwiseChange ⟶
      𝟭 (PMod R') := {
    app := fun G' =>
      { app := fun U => by
          dsimp [restriction, pointwiseChange, restrictionOfScalars,
            PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
            PresheafOfModules.pushforward₀Obj,
            PresheafOfModules.restrictScalars,
            PresheafOfModules.restrictScalarsObj]
          let hαU : ((asIdentityRingPresheafMorphism α_R).app U).hom =
              (α.app U).hom := by
            ext r
            simp [asIdentityRingPresheafMorphism, α_R,
              commRingPresheafMorphismToRingPresheaf]
          convert
            ((ModuleCat.extendScalars (α.app U).hom).map
                ((ModuleCat.restrictScalarsCongr hαU).hom.app (G'.obj U)) ≫
              (ModuleCat.extendRestrictScalarsAdj (α.app U).hom).counit.app (G'.obj U)) using 1
          all_goals
            simp [R']
        naturality := by
          sorry }
    naturality := by sorry }

  let pointwiseAdj : pointwiseChange ⊣ restriction :=
    Adjunction.mkOfUnitCounit {
      unit := unit
      counit := counit
      left_triangle := by sorry
      right_triangle := by sorry }

  let pullbackAdj : changeOfRingsCore α_R ⊣ restriction :=
    _root_.PresheafOfModules.pullbackPushforwardAdjunction
      (F := 𝟭 (Opens X)) (asIdentityRingPresheafMorphism α_R)
  let e := Adjunction.leftAdjointUniq pullbackAdj pointwiseAdj
  exact ⟨(PresheafOfModules.evaluation R' (op U)).mapIso (e.app G)⟩

/-- A chosen sectionwise comparison isomorphism for the tensor-product
presheaf. -/
noncomputable def tensorProductPresheaf_sectionIso
    {X : TopCat.{w}} {O₁ O₂ : CommRingPresheaf X}
    (α : O₁ ⟶ O₂)
    (G : PMod (O₁ ⋙ (forget₂ CommRingCat RingCat))) (U : Opens X) :
    (tensorProductPresheaf (commRingPresheafMorphismToRingPresheaf α) G).obj
          (op U) ≅
      sectionwiseExtensionOfScalars α G U :=
  Classical.choice (tensorProductPresheaf_section_iso α G U)

/-- The restriction map transported across the sectionwise tensor
comparisons. -/
noncomputable def tensorProductPresheaf_sectionRestriction
    {X : TopCat.{w}} {O₁ O₂ : CommRingPresheaf X}
    (α : O₁ ⟶ O₂)
    (G : PMod (O₁ ⋙ (forget₂ CommRingCat RingCat)))
    {U V : Opens X} (h : V ≤ U) :
    sectionwiseExtensionOfScalars α G U ⟶
      (ModuleCat.restrictScalars
        (O₂.map (homOfLE h).op).hom).obj
        (sectionwiseExtensionOfScalars α G V) := by
  exact (tensorProductPresheaf_sectionIso α G U).inv ≫
    (tensorProductPresheaf (commRingPresheafMorphismToRingPresheaf α) G).map
      (homOfLE h).op ≫
    (ModuleCat.restrictScalars (O₂.map (homOfLE h).op).hom).map
      (tensorProductPresheaf_sectionIso α G V).hom

/-- The sectionwise comparisons commute with restriction maps. -/
theorem tensorProductPresheaf_sectionIso_naturality
    {X : TopCat.{w}} {O₁ O₂ : CommRingPresheaf X}
    (α : O₁ ⟶ O₂)
    (G : PMod (O₁ ⋙ (forget₂ CommRingCat RingCat)))
    {U V : Opens X} (h : V ≤ U) :
    (tensorProductPresheaf (commRingPresheafMorphismToRingPresheaf α) G).map
          (homOfLE h).op ≫
        (ModuleCat.restrictScalars (O₂.map (homOfLE h).op).hom).map
          (tensorProductPresheaf_sectionIso α G V).hom =
      (tensorProductPresheaf_sectionIso α G U).hom ≫
        tensorProductPresheaf_sectionRestriction α G h := by
  simp [tensorProductPresheaf_sectionRestriction]

/-- The change-of-rings functor `PMod(O₁) ⥤ PMod(O₂)`. -/
noncomputable abbrev changeOfRings {X : TopCat.{w}}
    {O₁ O₂ : RingPresheaf.{w, w} X} (α : O₁ ⟶ O₂) :
    PMod O₁ ⥤ PMod O₂ :=
  changeOfRingsCore α

/-! ## Adjointness -/

/-- Change of rings is left adjoint to restriction of scalars. -/
noncomputable def changeOfRingsAdjunction {X : TopCat.{w}}
    {O₁ O₂ : RingPresheaf.{w, w} X} (α : O₁ ⟶ O₂) :
    changeOfRings α ⊣ restrictionOfScalars α :=
  _root_.PresheafOfModules.pullbackPushforwardAdjunction
    (F := 𝟭 (Opens X)) (asIdentityRingPresheafMorphism α)

/-- The source-facing Hom bijection for change of rings and restriction. -/
noncomputable def changeOfRingsHomEquiv {X : TopCat.{w}}
    {O₁ O₂ : RingPresheaf.{w, w} X} (α : O₁ ⟶ O₂)
    (G : PMod O₁) (F : PMod O₂) :
    (G ⟶ restrictedModule α F) ≃
      (tensorProductPresheaf α G ⟶ F) := by
  exact (changeOfRingsAdjunction α).homEquiv G F |>.symm

end Formalization.Books.Sheaves.Unit06
