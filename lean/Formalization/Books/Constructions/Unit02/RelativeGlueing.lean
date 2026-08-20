import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Constructions of Schemes, §2 “Relative glueing”

This file records the two relative glueing lemmas in the source section.  Schemes,
open subschemes, inverse images, and sheaves of modules are Mathlib's canonical
objects; the proposition proofs are deferred to the proof stage.
-/

noncomputable section

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry

namespace Formalization.Books.Constructions.Unit02

universe u

/-! ## Relative glueing data -/

/-- The canonical morphism between inverse-image open subschemes induced by an inclusion. -/
def preimageOpenHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : Y.Opens} (hVU : V ≤ U) :
    (f ⁻¹ᵁ V).toScheme ⟶ (f ⁻¹ᵁ U).toScheme :=
  X.homOfLE (by
    intro x hx
    exact hVU hx)

/-- Data used to glue schemes over a basis of open subsets of a scheme. -/
structure RelativeGlueingData (S : Scheme.{u}) (B : Set S.Opens) where
  /-- The chosen basis of opens. -/
  basis : Opens.IsBasis B
  /-- The scheme over each basis open. -/
  X : ∀ (U : S.Opens), U ∈ B → Scheme.{u}
  /-- The structure morphism of each local scheme. -/
  f : ∀ (U : S.Opens) (hU : U ∈ B), X U hU ⟶ U.toScheme
  /-- The transition morphism for an inclusion of basis opens. -/
  rho : ∀ (U V : S.Opens) (hU : U ∈ B) (hV : V ∈ B) (_hVU : V ≤ U),
    X V hV ⟶ X U hU
  /-- Each transition morphism is over the ambient scheme. -/
  rho_over : ∀ (U V : S.Opens) (hU : U ∈ B) (hV : V ∈ B) (hVU : V ≤ U),
    rho U V hU hV hVU ≫ f U hU ≫ U.ι = f V hV ≫ V.ι
  /-- The transition morphism identifies the smaller scheme with the inverse image open. -/
  rho_isPreimage : ∀ (U V : S.Opens) (hU : U ∈ B) (hV : V ∈ B) (hVU : V ≤ U),
    ∃ e : X V hV ≅
      (f U hU ⁻¹ᵁ (U.ι ⁻¹ᵁ V)).toScheme,
      e.hom ≫ (f U hU ⁻¹ᵁ (U.ι ⁻¹ᵁ V)).ι = rho U V hU hV hVU
  /-- Transition morphisms satisfy the cocycle condition. -/
  rho_comp : ∀ (U V W : S.Opens) (hU : U ∈ B) (hV : V ∈ B) (hW : W ∈ B)
    (hVU : V ≤ U) (hWV : W ≤ V),
    rho U W hU hW (hWV.trans hVU) =
      rho V W hV hW hWV ≫ rho U V hU hV hVU

/-- A scheme over `S` realizing a relative glueing datum. -/
structure RelativeGlueingRealization {S : Scheme.{u}} {B : Set S.Opens}
    (D : RelativeGlueingData S B) where
  /-- The glued scheme. -/
  X : Scheme.{u}
  /-- Its structure morphism to the base. -/
  f : X ⟶ S
  /-- The identifications of its inverse images with the local schemes. -/
  i : ∀ (U : S.Opens) (hU : U ∈ B),
    (f ⁻¹ᵁ U).toScheme ≅ D.X U hU
  /-- The local identifications are over the corresponding basis opens. -/
  i_over : ∀ (U : S.Opens) (hU : U ∈ B),
    (i U hU).hom ≫ D.f U hU ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f
  /-- The local identifications recover the transition morphisms. -/
  i_rho : ∀ (U V : S.Opens) (hU : U ∈ B) (hV : V ∈ B) (hVU : V ≤ U),
    (i V hV).inv ≫ preimageOpenHom f hVU ≫ (i U hU).hom =
      D.rho U V hU hV hVU

/-- A chart-compatible isomorphism between two realizations of the same datum. -/
def RelativeGlueingRealizationIsoCondition {S : Scheme.{u}} {B : Set S.Opens}
    {D : RelativeGlueingData S B}
    (R₁ R₂ : RelativeGlueingRealization D) (e : R₁.X ≅ R₂.X) : Prop :=
  e.hom ≫ R₂.f = R₁.f ∧
    ∀ (U : S.Opens) (hU : U ∈ B),
      ∃ α : (R₁.f ⁻¹ᵁ U).toScheme ≅ (R₂.f ⁻¹ᵁ U).toScheme,
        α.hom ≫ (R₂.f ⁻¹ᵁ U).ι = (R₁.f ⁻¹ᵁ U).ι ≫ e.hom ∧
        α.hom ≫ (R₂.i U hU).hom = (R₁.i U hU).hom

/-- Relative glueing of schemes over a basis. -/
theorem relative_glueing (D : RelativeGlueingData S B) :
    Nonempty (RelativeGlueingRealization D) := by
  sorry

/-- The uniqueness clause for relative glueing, stated for realizing data. -/
theorem relative_glueing_unique (D : RelativeGlueingData S B)
    (R₁ R₂ : RelativeGlueingRealization D) :
    ∃! e : R₁.X ≅ R₂.X, RelativeGlueingRealizationIsoCondition R₁ R₂ e := by
  sorry

/-! ## Relative glueing of quasi-coherent sheaves -/

/-- Quasi-coherent sheaf glueing data over a relative scheme glueing datum. -/
structure RelativeGlueingSheafData {S : Scheme.{u}} {B : Set S.Opens}
    (D : RelativeGlueingData S B) where
  /-- The local sheaf of modules. -/
  F : ∀ (U : S.Opens) (hU : U ∈ B), (D.X U hU).Modules
  /-- Each local sheaf is quasi-coherent. -/
  F_quasi : ∀ (U : S.Opens) (hU : U ∈ B), (F U hU).IsQuasicoherent
  /-- The transition isomorphism on sheaves of modules. -/
  theta : ∀ (U V : S.Opens) (hU : U ∈ B) (hV : V ∈ B) (hVU : V ≤ U),
    (Scheme.Modules.pullback (D.rho U V hU hV hVU)).obj (F U hU) ⟶ F V hV
  /-- Every transition map is an isomorphism. -/
  theta_isIso : ∀ (U V : S.Opens) (hU : U ∈ B) (hV : V ∈ B) (hVU : V ≤ U),
    IsIso (theta U V hU hV hVU)
  /-- The transition isomorphisms satisfy the pullback cocycle condition. -/
  theta_comp : ∀ (U V W : S.Opens) (hU : U ∈ B) (hV : V ∈ B) (hW : W ∈ B)
    (hVU : V ≤ U) (hWV : W ≤ V),
    theta U W hU hW (hWV.trans hVU) =
      (Scheme.Modules.pullbackCongr
          (D.rho_comp U V W hU hV hW hVU hWV)).hom.app (F U hU) ≫
        (Scheme.Modules.pullbackComp (D.rho V W hV hW hWV)
          (D.rho U V hU hV hVU)).inv.app (F U hU) ≫
        (Scheme.Modules.pullback (D.rho V W hV hW hWV)).map
          (theta U V hU hV hVU) ≫
        theta V W hV hW hWV

/-- The inverse-image open inclusion is compatible with `preimageOpenHom`. -/
theorem preimageOpenHom_comp_ι {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : Y.Opens} (hVU : V ≤ U) :
    preimageOpenHom f hVU ≫ (f ⁻¹ᵁ U).ι = (f ⁻¹ᵁ V).ι := by
  sorry

/-- The chart description of a transition map, rewritten in the direction used for
pulling back sheaves. -/
theorem RelativeGlueingRealization.i_hom_rho
    {S : Scheme.{u}} {B : Set S.Opens} {D : RelativeGlueingData S B}
    (R : RelativeGlueingRealization D)
    (U V : S.Opens) (hU : U ∈ B) (hV : V ∈ B) (hVU : V ≤ U) :
    (R.i V hV).hom ≫ D.rho U V hU hV hVU =
      preimageOpenHom R.f hVU ≫ (R.i U hU).hom := by
  sorry

/-- The displayed sheaf equation in the relative glueing lemma, expressed as an
equality of module morphisms on the smaller inverse-image open. -/
def relativeGlueingSheafEquation
    {S : Scheme.{u}} {B : Set S.Opens} {D : RelativeGlueingData S B}
    (E : RelativeGlueingSheafData D)
    (R : RelativeGlueingRealization D) (F : R.X.Modules)
    (theta : ∀ (U : S.Opens) (hU : U ∈ B),
      (Scheme.Modules.pullback (R.i U hU).hom).obj (E.F U hU) ⟶
        (Scheme.Modules.pullback ((R.f ⁻¹ᵁ U).ι)).obj F)
    (theta_isIso : ∀ (U : S.Opens) (hU : U ∈ B), IsIso (theta U hU))
    (U V : S.Opens) (hU : U ∈ B) (hV : V ∈ B) (hVU : V ≤ U) : Prop :=
  let iU := (R.i U hU).hom
  let iV := (R.i V hV).hom
  let b := preimageOpenHom R.f hVU
  let rho := D.rho U V hU hV hVU
  let hsource : iV ≫ rho = b ≫ iU :=
    RelativeGlueingRealization.i_hom_rho R U V hU hV hVU
  let sourceIso :
      (Scheme.Modules.pullback b).obj
          ((Scheme.Modules.pullback iU).obj (E.F U hU)) ≅
      (Scheme.Modules.pullback iV).obj
          ((Scheme.Modules.pullback rho).obj (E.F U hU)) :=
    (Scheme.Modules.pullbackComp b iU).app (E.F U hU) ≪≫
      (Scheme.Modules.pullbackCongr hsource.symm).app (E.F U hU) ≪≫
      ((Scheme.Modules.pullbackComp iV rho).app (E.F U hU)).symm
  let hglobal : b ≫ (R.f ⁻¹ᵁ U).ι = (R.f ⁻¹ᵁ V).ι :=
    preimageOpenHom_comp_ι R.f hVU
  let globalIso :
      (Scheme.Modules.pullback b).obj
          ((Scheme.Modules.pullback ((R.f ⁻¹ᵁ U).ι)).obj F) ≅
        (Scheme.Modules.pullback ((R.f ⁻¹ᵁ V).ι)).obj F :=
    (Scheme.Modules.pullbackComp b (R.f ⁻¹ᵁ U).ι).app F ≪≫
      (Scheme.Modules.pullbackCongr hglobal).app F
  letI : IsIso (theta V hV) := theta_isIso V hV
  sourceIso.hom ≫
      (Scheme.Modules.pullback iV).map (E.theta U V hU hV hVU) =
    (Scheme.Modules.pullback b).map (theta U hU) ≫
      globalIso.hom ≫ inv (theta V hV)

/-- A glued quasi-coherent sheaf together with its local identifications. -/
structure RelativeGlueingSheafRealization {S : Scheme.{u}} {B : Set S.Opens}
    {D : RelativeGlueingData S B} (E : RelativeGlueingSheafData D) where
  /-- The underlying glued scheme and its local charts. -/
  scheme : RelativeGlueingRealization D
  /-- The glued quasi-coherent sheaf of modules. -/
  F : scheme.X.Modules
  /-- The glued sheaf is quasi-coherent. -/
  F_quasi : F.IsQuasicoherent
  /-- The local comparison maps from the local sheaves to the restriction of the glued sheaf. -/
  theta : ∀ (U : S.Opens) (hU : U ∈ B),
    (Scheme.Modules.pullback (scheme.i U hU).hom).obj (E.F U hU) ⟶
      (Scheme.Modules.pullback ((scheme.f ⁻¹ᵁ U).ι)).obj F
  /-- The local comparison maps are isomorphisms. -/
  theta_isIso : ∀ (U : S.Opens) (hU : U ∈ B), IsIso (theta U hU)
  /-- The local comparison maps induce the prescribed transition maps, namely the
  displayed sheaf equation in the source.  The equality is retained as a named
  proposition because it compares pullbacks along several canonical isomorphisms. -/
  theta_restricts_equation : ∀ (U V : S.Opens) (hU : U ∈ B) (hV : V ∈ B)
    (hVU : V ≤ U),
    relativeGlueingSheafEquation E scheme F theta theta_isIso U V hU hV hVU

/-- Relative glueing of quasi-coherent sheaves. -/
theorem relative_glueing_sheaves (E : RelativeGlueingSheafData D) :
    Nonempty (RelativeGlueingSheafRealization E) := by
  sorry

/-- Uniqueness of the glued scheme and quasi-coherent sheaf. -/
theorem relative_glueing_sheaves_unique (E : RelativeGlueingSheafData D)
    (R₁ R₂ : RelativeGlueingSheafRealization E) :
    ∃! e : R₁.scheme.X ≅ R₂.scheme.X,
      RelativeGlueingRealizationIsoCondition R₁.scheme R₂.scheme e ∧
        Nonempty (R₁.F ≅
          (Scheme.Modules.pullback e.hom).obj R₂.F) := by
  sorry

/-! ## Functoriality -/

/-- Morphisms of relative scheme glueing data. -/
structure RelativeGlueingDataHom {S : Scheme.{u}} {B : Set S.Opens}
    {D₁ D₂ : RelativeGlueingData S B} where
  /-- The local morphisms. -/
  h : ∀ (U : S.Opens) (hU : U ∈ B), D₁.X U hU ⟶ D₂.X U hU
  /-- They are over the basis opens. -/
  over : ∀ (U : S.Opens) (hU : U ∈ B),
    h U hU ≫ D₂.f U hU = D₁.f U hU
  /-- They commute with all transition morphisms. -/
  commutes : ∀ (U V : S.Opens) (hU : U ∈ B) (hV : V ∈ B) (hVU : V ≤ U),
    D₁.rho U V hU hV hVU ≫ h U hU = h V hV ≫ D₂.rho U V hU hV hVU

/-- The local-chart compatibility required of the map produced by functoriality. -/
def RelativeGlueingMapCondition {S : Scheme.{u}} {B : Set S.Opens}
    {D₁ D₂ : RelativeGlueingData S B}
    (R₁ : RelativeGlueingRealization D₁) (R₂ : RelativeGlueingRealization D₂)
    (h : RelativeGlueingDataHom (D₁ := D₁) (D₂ := D₂)) (g : R₁.X ⟶ R₂.X) : Prop :=
  g ≫ R₂.f = R₁.f ∧
    ∀ (U : S.Opens) (hU : U ∈ B),
      ∃ α : (R₁.f ⁻¹ᵁ U).toScheme ≅ (R₂.f ⁻¹ᵁ U).toScheme,
        α.hom ≫ (R₂.f ⁻¹ᵁ U).ι = (R₁.f ⁻¹ᵁ U).ι ≫ g ∧
        α.hom ≫ (R₂.i U hU).hom = (R₁.i U hU).hom ≫ h.h U hU

/-- Functoriality of relative scheme glueing. -/
theorem relative_glueing_map (D₁ D₂ : RelativeGlueingData S B)
    (R₁ : RelativeGlueingRealization D₁) (R₂ : RelativeGlueingRealization D₂)
    (h : RelativeGlueingDataHom (D₁ := D₁) (D₂ := D₂)) :
    ∃ g : R₁.X ⟶ R₂.X, RelativeGlueingMapCondition R₁ R₂ h g := by
  sorry

/-- Morphisms between quasi-coherent sheaf glueing data. -/
structure RelativeGlueingSheafDataHom {S : Scheme.{u}} {B : Set S.Opens}
    {D₁ D₂ : RelativeGlueingData S B}
    (E₁ : RelativeGlueingSheafData D₁) (E₂ : RelativeGlueingSheafData D₂) where
  /-- The underlying morphism of relative scheme glueing data. -/
  base : RelativeGlueingDataHom (D₁ := D₁) (D₂ := D₂)
  /-- The local morphisms of sheaves. -/
  tau : ∀ (U : S.Opens) (hU : U ∈ B),
    (Scheme.Modules.pullback (base.h U hU)).obj (E₂.F U hU) ⟶ E₁.F U hU
  /-- The local sheaf morphisms commute with the transition isomorphisms. -/
  tau_compatibility : ∀ (U V : S.Opens) (hU : U ∈ B) (hV : V ∈ B)
    (hVU : V ≤ U),
    (Scheme.Modules.pullback (D₁.rho U V hU hV hVU)).map (tau U hU) ≫
        E₁.theta U V hU hV hVU =
      (Scheme.Modules.pullbackComp (D₁.rho U V hU hV hVU)
          (base.h U hU)).hom.app (E₂.F U hU) ≫
        (Scheme.Modules.pullbackCongr
            (base.commutes U V hU hV hVU)).hom.app (E₂.F U hU) ≫
        (Scheme.Modules.pullbackComp (base.h V hV)
            (D₂.rho U V hU hV hVU)).inv.app (E₂.F U hU) ≫
        (Scheme.Modules.pullback (base.h V hV)).map
          (E₂.theta U V hU hV hVU) ≫
        tau V hV

/-- A global morphism induced by a morphism of quasi-coherent sheaf glueing data. -/
structure RelativeGlueingSheafMap {S : Scheme.{u}} {B : Set S.Opens}
    {D₁ D₂ : RelativeGlueingData S B}
    {E₁ : RelativeGlueingSheafData D₁} {E₂ : RelativeGlueingSheafData D₂}
    (R₁ : RelativeGlueingSheafRealization E₁)
    (R₂ : RelativeGlueingSheafRealization E₂)
    (H : RelativeGlueingSheafDataHom E₁ E₂) where
  /-- The global morphism of glued schemes. -/
  g : R₁.scheme.X ⟶ R₂.scheme.X
  /-- The global sheaf morphism. -/
  tau : (Scheme.Modules.pullback g).obj R₂.F ⟶ R₁.F
  /-- The global scheme morphism restricts to the local morphisms. -/
  scheme_condition : RelativeGlueingMapCondition R₁.scheme R₂.scheme H.base g
  /-- The global sheaf morphism restricts to the local morphisms. -/
  sheaf_condition : Prop

/-- Functoriality for relative glueing of schemes and quasi-coherent sheaves. -/
theorem relative_glueing_sheaves_map
    (E₁ : RelativeGlueingSheafData D₁) (E₂ : RelativeGlueingSheafData D₂)
    (R₁ : RelativeGlueingSheafRealization E₁)
    (R₂ : RelativeGlueingSheafRealization E₂)
    (H : RelativeGlueingSheafDataHom E₁ E₂) :
    Nonempty (RelativeGlueingSheafMap R₁ R₂ H) := by
  sorry

end Formalization.Books.Constructions.Unit02
