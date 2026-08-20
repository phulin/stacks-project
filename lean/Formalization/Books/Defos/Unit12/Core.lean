import Formalization.Books.Defos.Unit09.Core
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Torsor.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Deformation Theory, Chapter 12: Flat modules on flat thickenings of ringed topoi

This file formalizes `books/defos.tex:3692--3865`.  Chapter 9 supplies the
ringed-topos, thickening, kernel, and strictness interfaces.  The source's
tensor products and Ext groups for sheaves of modules on a ringed topos are
exposed through small interfaces here: the generic `RingCat` sheaf model in
Chapter 9 does not provide a canonical commutative tensor construction or the
set-theoretic hypotheses needed by the derived Ext API.
-/

namespace Formalization.Books.Defos.Unit12

open CategoryTheory CategoryTheory.Limits
open Formalization.Books.Defos.Unit09
open Formalization.Books.Defos.Unit09.MorphismOfThickenings

universe u

noncomputable section

/-! ## Modules, tensor products, flatness, and Ext -/

/-- Modules on a ringed topos. -/
abbrev ToposModule {C : Type u} [Category.{u} C]
    (X : RingedTopos C) := SheafOfModules.{u} X.structureSheaf

/-- A source-facing relative tensor product for modules on a ringed topos.

The first factor is a module on the base of `f`, and the second is a module
on the source.  The functorial map and the tensor functor are included so
that the coefficient maps and the categorical definition of flatness are
available without introducing a second sheaf tensor implementation. -/
class RelativeModuleTensorProduct
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {B : RingedTopos D}
    (f : RingedToposHom X B) where
  tensorFunctor : ToposModule X → (ToposModule B ⥤ ToposModule X)

/-- The module denoted by `f^* J ⊗ F` in the source. -/
abbrev relativeTensor
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {B : RingedTopos D}
    (f : RingedToposHom X B) [RelativeModuleTensorProduct f]
    (J : ToposModule B) (F : ToposModule X) : ToposModule X :=
  (RelativeModuleTensorProduct.tensorFunctor f F).obj J

/-- The map induced on relative tensors by maps in both factors. -/
abbrev relativeTensorMap
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {B : RingedTopos D}
    (f : RingedToposHom X B) [RelativeModuleTensorProduct f]
    (F : ToposModule X) {J J' : ToposModule B}
    (g : J ⟶ J') :
    relativeTensor f J F ⟶ relativeTensor f J' F :=
  (RelativeModuleTensorProduct.tensorFunctor f F).map g

/-- Flatness of a module over the base ringed topos, expressed by exactness
of the relative tensor functor. -/
def FlatModuleOver
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {B : RingedTopos D}
    (f : RingedToposHom X B) [RelativeModuleTensorProduct f]
    (F : ToposModule X) : Prop :=
  PreservesFiniteLimits (RelativeModuleTensorProduct.tensorFunctor f F)

/-- Flatness of a morphism of ringed topoi on module categories. -/
def FlatRingedToposHom
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {B : RingedTopos D}
    (f : RingedToposHom X B) : Prop :=
  PreservesFiniteLimits f.modulePullback

/-- The Ext groups used by the source's module statements. -/
class ToposExtTheory {C : Type u} [Category.{u} C]
    (X : RingedTopos C) where
  ext : ToposModule X → ToposModule X → ℕ → Type (u + 1)
  group : ∀ (F K : ToposModule X) (n : ℕ), AddCommGroup (ext F K n)
  map : ∀ {F K L : ToposModule X} (n : ℕ),
    (K ⟶ L) → ext F K n → ext F L n
  map_id : ∀ {F K : ToposModule X} (n : ℕ) (x : ext F K n),
    map n (𝟙 K) x = x
  map_comp : ∀ {F K L M : ToposModule X} (n : ℕ)
    (g : K ⟶ L) (h : L ⟶ M) (x : ext F K n),
    map n (g ≫ h) x = map n h (map n g x)
  boundary : ∀ {F K₃ K₂ K₁ : ToposModule X}
    (k₃₂ : K₃ ⟶ K₂) (k₂₁ : K₂ ⟶ K₁)
    (zero : k₃₂ ≫ k₂₁ = 0)
    (_ : (ShortComplex.mk k₃₂ k₂₁ zero).ShortExact),
    ext F K₁ 1 → ext F K₃ 2

/-- The source notation `Ext^n_X(F, K)`. -/
abbrev ExtGroup {C : Type u} [Category.{u} C]
    {X : RingedTopos C} [ToposExtTheory X]
    (F K : ToposModule X) (n : ℕ) : Type (u + 1) :=
  ToposExtTheory.ext F K n

instance extGroup_addCommGroup {C : Type u} [Category.{u} C]
    {X : RingedTopos C} [h : ToposExtTheory X]
    (F K : ToposModule X) (n : ℕ) : AddCommGroup (ExtGroup F K n) :=
  h.group F K n

/-! ## The flat-thickening setup -/

/-- A commutative square of ringed-topos morphisms, with the inverse/direct
image and module coherences used by pullback and flatness arguments. -/
structure RingedToposHomSquare
    {C₁ C₂ D₁ D₂ : Type u}
    [Category.{u} C₁] [Category.{u} C₂]
    [Category.{u} D₁] [Category.{u} D₂]
    {X₁ : RingedTopos C₁} {X₂ : RingedTopos C₂}
    {B₁ : RingedTopos D₁} {B₂ : RingedTopos D₂}
    (h : RingedToposHom X₁ X₂) (k : RingedToposHom B₁ B₂)
    (f₁ : RingedToposHom X₁ B₁) (f₂ : RingedToposHom X₂ B₂) where
  inverseImage_iso :
    k.inverseImage ⋙ f₁.inverseImage ≅ f₂.inverseImage ⋙ h.inverseImage
  ring_inverse_iso :
    k.inverseImageRing ⋙ f₁.inverseImageRing ≅
      f₂.inverseImageRing ⋙ h.inverseImageRing
  direct_ring_iso :
    h.directImageRing ⋙ f₂.directImageRing ≅
      f₁.directImageRing ⋙ k.directImageRing
  module_direct_iso :
    h.moduleDirectImage ⋙ f₂.moduleDirectImage ≅
      f₁.moduleDirectImage ⋙ k.moduleDirectImage
  module_unit_compatibility :
    f₂.moduleDirectImage_unit_map ≫
        f₂.moduleDirectImage.map h.moduleDirectImage_unit_map ≫
          module_direct_iso.hom.app _ =
      k.moduleDirectImage_unit_map ≫
        k.moduleDirectImage.map f₁.moduleDirectImage_unit_map
  module_pullback_iso :
    k.modulePullback ⋙ f₁.modulePullback ≅
      f₂.modulePullback ⋙ h.modulePullback
  sharp_compatibility :
    f₂.sharp ≫ f₂.directImageRing.map h.sharp ≫
        direct_ring_iso.hom.app _ =
      k.sharp ≫ k.directImageRing.map f₁.sharp

/-- A first-order thickening together with the flatness and strictness
hypotheses in the opening paragraph of Chapter 12. -/
structure FlatThickeningSituation
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    (X : RingedTopos C) (B : RingedTopos E)
    (f : RingedToposHom X B) where
  Y : RingedTopos D
  B' : RingedTopos F
  i : Thickening X Y
  t : Thickening B B'
  square : MorphismOfThickenings i t
  square_f : square.f = f
  source_first_order : FirstOrderThickening i
  base_first_order : FirstOrderThickening t
  strict : square.IsStrict
  f'_flat : FlatRingedToposHom square.f'

namespace FlatThickeningSituation

variable {C D E F : Type u} [Category.{u} C] [Category.{u} D]
  [Category.{u} E] [Category.{u} F]
  {X : RingedTopos C} {B : RingedTopos E}
  {f : RingedToposHom X B}

/-- The source and base kernel ideals in the opening diagram. -/
abbrev sourceIdeal
    (S : FlatThickeningSituation (D := D) (F := F) X B f) :=
  S.i.hom.kernel

abbrev baseIdeal
    (S : FlatThickeningSituation (D := D) (F := F) X B f) :=
  S.t.hom.kernel

/-- The canonical chosen module on the reduced topos representing a
first-order thickening kernel. -/
noncomputable def kernelModule {Y : RingedTopos D} (i : Thickening X Y)
    (hi : FirstOrderThickening i) : ToposModule X :=
  Classical.choose (kernel_is_module_over i hi)

/-- The pushforward identification of the chosen kernel module. -/
noncomputable def kernelModuleIso {Y : RingedTopos D} (i : Thickening X Y)
    (hi : FirstOrderThickening i) :
    i.hom.moduleDirectImage.obj (kernelModule i hi) ≅ i.hom.kernel.carrier :=
  Classical.choice (Classical.choose_spec (kernel_is_module_over i hi))

/-- A source-facing morphism between first-order thickenings, including the
induced map on the chosen kernel modules. -/
structure FirstOrderThickeningHom
    {D₁ D₂ : Type u} [Category.{u} D₁] [Category.{u} D₂]
    {Y₁ : RingedTopos D₁} {Y₂ : RingedTopos D₂}
    (i₁ : Thickening X Y₁) (i₂ : Thickening X Y₂)
    (hi₁ : FirstOrderThickening i₁) (hi₂ : FirstOrderThickening i₂) where
  h : RingedToposHom Y₁ Y₂
  inverseImage_iso : h.inverseImage ⋙ i₁.hom.inverseImage ≅ i₂.hom.inverseImage
  ring_inverse_iso :
    h.inverseImageRing ⋙ i₁.hom.inverseImageRing ≅ i₂.hom.inverseImageRing
  direct_ring_iso :
    i₁.hom.directImageRing ⋙ h.directImageRing ≅ i₂.hom.directImageRing
  module_direct_iso :
    i₁.hom.moduleDirectImage ⋙ h.moduleDirectImage ≅ i₂.hom.moduleDirectImage
  module_unit_compatibility :
    h.moduleDirectImage_unit_map ≫
        h.moduleDirectImage.map i₁.hom.moduleDirectImage_unit_map ≫
          module_direct_iso.hom.app _ = i₂.hom.moduleDirectImage_unit_map
  module_pullback_iso :
    h.modulePullback ⋙ i₁.hom.modulePullback ≅ i₂.hom.modulePullback
  sharp_compatibility :
    h.sharp ≫ h.directImageRing.map i₁.hom.sharp ≫
        direct_ring_iso.hom.app _ = i₂.hom.sharp
  kernelMap : kernelModule i₂ hi₂ ⟶ kernelModule i₁ hi₁

end FlatThickeningSituation

/-! ## Flat lifts and the obstruction/classification lemma -/

/-- A flat module on a thickening together with its identified reduction. -/
structure FlatModuleLift
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S : FlatThickeningSituation (D := D) (F := F) X B f)
    (F₀ : ToposModule X) [RelativeModuleTensorProduct f]
    [RelativeModuleTensorProduct S.square.f'] where
  module : ToposModule S.Y
  flat : FlatModuleOver S.square.f' module
  restrictionIso : S.i.hom.modulePullback.obj module ≅ F₀

/-- Isomorphisms of flat lifts which induce the identity on the fixed
reduction. -/
structure FlatModuleLiftIso
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    {S : FlatThickeningSituation (D := D) (F := F) X B f}
    {F₀ : ToposModule X} [RelativeModuleTensorProduct f]
    [RelativeModuleTensorProduct S.square.f']
    (A A' : FlatModuleLift S F₀) where
  hom : A.module ≅ A'.module
  restriction_commutes :
    S.i.hom.modulePullback.map hom.hom ≫ A'.restrictionIso.hom =
      A.restrictionIso.hom

namespace FlatModuleLiftIso

variable {C D E F : Type u} [Category.{u} C] [Category.{u} D]
  [Category.{u} E] [Category.{u} F]
  {X : RingedTopos C} {B : RingedTopos E}
  {f : RingedToposHom X B}
  {S : FlatThickeningSituation (D := D) (F := F) X B f}
  {F₀ : ToposModule X} [RelativeModuleTensorProduct f]
  [RelativeModuleTensorProduct S.square.f']

/-- The identity isomorphism of a flat lift. -/
def refl (A : FlatModuleLift S F₀) : FlatModuleLiftIso A A where
  hom := Iso.refl _
  restriction_commutes := by simp

/-- The inverse of an isomorphism of flat lifts. -/
def symm {A A' : FlatModuleLift S F₀} (e : FlatModuleLiftIso A A') :
    FlatModuleLiftIso A' A where
  hom := e.hom.symm
  restriction_commutes := by
    rw [← e.restriction_commutes]
    simp

/-- Composition of isomorphisms of flat lifts. -/
def trans {A A' A'' : FlatModuleLift S F₀}
    (e₁ : FlatModuleLiftIso A A') (e₂ : FlatModuleLiftIso A' A'') :
    FlatModuleLiftIso A A'' where
  hom := e₁.hom ≪≫ e₂.hom
  restriction_commutes := by
    change S.i.hom.modulePullback.map (e₁.hom.hom ≫ e₂.hom.hom) ≫
      A''.restrictionIso.hom = A.restrictionIso.hom
    rw [Functor.map_comp, Category.assoc, e₂.restriction_commutes,
      e₁.restriction_commutes]

end FlatModuleLiftIso

/-- The equivalence relation of isomorphism of flat lifts. -/
def flatModuleLiftSetoid
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S : FlatThickeningSituation (D := D) (F := F) X B f)
    (F₀ : ToposModule X) [RelativeModuleTensorProduct f]
    [RelativeModuleTensorProduct S.square.f'] :
    Setoid (FlatModuleLift S F₀) where
  r A A' := Nonempty (FlatModuleLiftIso A A')
  iseqv := by
    refine ⟨fun A => ⟨FlatModuleLiftIso.refl A⟩, ?_, ?_⟩
    · intro A A' h
      rcases h with ⟨h⟩
      exact ⟨FlatModuleLiftIso.symm h⟩
    · intro A A' A'' h₁ h₂
      rcases h₁ with ⟨h₁⟩
      rcases h₂ with ⟨h₂⟩
      exact ⟨FlatModuleLiftIso.trans h₁ h₂⟩

/-- Isomorphism classes of flat lifts. -/
abbrev FlatModuleLiftClasses
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S : FlatThickeningSituation (D := D) (F := F) X B f)
    (F₀ : ToposModule X) [RelativeModuleTensorProduct f]
    [RelativeModuleTensorProduct S.square.f'] :=
  Quotient (flatModuleLiftSetoid S F₀)

/-- The strictness hypothesis identifies the source kernel with the pullback
of the base kernel; in the Chapter 9 API this is the canonical epimorphism
of kernel modules. -/
theorem kernelComparison_is_epi
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S : FlatThickeningSituation (D := D) (F := F) X B f) :
    Epi S.square.pullbackKernelMap :=
  S.strict

/-- The flat-lift obstruction group `Ext^2(F, f^*J ⊗ F)`. -/
abbrev FlatLiftObstruction
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S : FlatThickeningSituation (D := D) (F := F) X B f)
    (F₀ : ToposModule X) [RelativeModuleTensorProduct f]
    [ToposExtTheory X] :=
  ExtGroup F₀
    (relativeTensor f (FlatThickeningSituation.kernelModule S.t S.base_first_order) F₀) 2

/-- Once a flat lift exists, its isomorphism classes form the source's
principal homogeneous space under Ext one. -/
theorem flatModuleLiftClasses_is_principalHomogeneousSpace
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S : FlatThickeningSituation (D := D) (F := F) X B f)
    (F₀ : ToposModule X) [RelativeModuleTensorProduct f]
    [RelativeModuleTensorProduct S.square.f']
    [ToposExtTheory X]
    (hF : FlatModuleOver f F₀)
    (h : Nonempty (FlatModuleLift S F₀)) :
    Nonempty (AddTorsor
      (ExtGroup F₀
        (relativeTensor f
          (FlatThickeningSituation.kernelModule S.t S.base_first_order) F₀) 1)
      (FlatModuleLiftClasses S F₀)) := by
  sorry

/-- Automorphisms of a lift which induce the identity on its reduction. -/
def FlatModuleLiftAutomorphism
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    {S : FlatThickeningSituation (D := D) (F := F) X B f}
    {F₀ : ToposModule X} [RelativeModuleTensorProduct f]
    [RelativeModuleTensorProduct S.square.f']
    (A : FlatModuleLift S F₀) :=
  { e : A.module ≅ A.module //
      S.i.hom.modulePullback.map e.hom ≫ A.restrictionIso.hom =
        A.restrictionIso.hom }

/-- The source's canonical identification of lift automorphisms with Ext zero. -/
theorem flatModuleLiftAutomorphisms_equiv_ext_zero
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S : FlatThickeningSituation (D := D) (F := F) X B f)
    (F₀ : ToposModule X) [RelativeModuleTensorProduct f]
    [RelativeModuleTensorProduct S.square.f']
    [ToposExtTheory X]
    (hF : FlatModuleOver f F₀)
    (A : FlatModuleLift S F₀) :
    Nonempty (FlatModuleLiftAutomorphism A ≃
      ExtGroup F₀
        (relativeTensor f
          (FlatThickeningSituation.kernelModule S.t S.base_first_order) F₀) 0) := by
  sorry

/-- Existence of the obstruction class for a flat lift. -/
theorem exists_flatLiftObstructionClass
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S : FlatThickeningSituation (D := D) (F := F) X B f)
    (F₀ : ToposModule X) [RelativeModuleTensorProduct f]
    [RelativeModuleTensorProduct S.square.f']
    [ToposExtTheory X]
    (hF : FlatModuleOver f F₀) :
    ∃ o : FlatLiftObstruction S F₀,
      (o = 0 ↔ Nonempty (FlatModuleLift S F₀)) := by
  sorry

/-- A chosen flat-lift obstruction class. -/
noncomputable def flatLiftObstructionClass
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S : FlatThickeningSituation (D := D) (F := F) X B f)
    (F₀ : ToposModule X) [RelativeModuleTensorProduct f]
    [RelativeModuleTensorProduct S.square.f']
    [ToposExtTheory X]
    (hF : FlatModuleOver f F₀) : FlatLiftObstruction S F₀ :=
  Classical.choose (exists_flatLiftObstructionClass S F₀ hF)

/-- Vanishing of the chosen class is equivalent to existence of a flat lift. -/
theorem flatLiftObstructionClass_vanishes_iff
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S : FlatThickeningSituation (D := D) (F := F) X B f)
    (F₀ : ToposModule X) [RelativeModuleTensorProduct f]
    [RelativeModuleTensorProduct S.square.f']
    [ToposExtTheory X]
    (hF : FlatModuleOver f F₀) :
    flatLiftObstructionClass S F₀ hF = 0 ↔
      Nonempty (FlatModuleLift S F₀) :=
  Classical.choose_spec (exists_flatLiftObstructionClass S F₀ hF)

/-! ## Functoriality in the thickening -/

/-- A square of ringed-topos morphisms is part of a morphism of the two
thickening diagrams. -/
structure FirstOrderThickeningDiagramMap
    {C D₁ D₂ E F₁ F₂ : Type u}
    [Category.{u} C] [Category.{u} D₁] [Category.{u} D₂]
    [Category.{u} E] [Category.{u} F₁] [Category.{u} F₂]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S₁ : FlatThickeningSituation (D := D₁) (F := F₁) X B f)
    (S₂ : FlatThickeningSituation (D := D₂) (F := F₂) X B f) where
  upper : FlatThickeningSituation.FirstOrderThickeningHom
    S₁.i S₂.i S₁.source_first_order S₂.source_first_order
  lower : FlatThickeningSituation.FirstOrderThickeningHom
    S₁.t S₂.t S₁.base_first_order S₂.base_first_order
  vertical_square : RingedToposHomSquare upper.h lower.h S₁.square.f' S₂.square.f'

namespace FirstOrderThickeningDiagramMap

variable {C D₁ D₂ E F₁ F₂ : Type u}
  [Category.{u} C] [Category.{u} D₁] [Category.{u} D₂]
  [Category.{u} E] [Category.{u} F₁] [Category.{u} F₂]
  {X : RingedTopos C} {B : RingedTopos E}
  {f : RingedToposHom X B}
  {S₁ : FlatThickeningSituation (D := D₁) (F := F₁) X B f}
  {S₂ : FlatThickeningSituation (D := D₂) (F := F₂) X B f}

/-- The canonical coefficient map from the second thickening to the first. -/
abbrev coefficientMap
    (D : FirstOrderThickeningDiagramMap S₁ S₂)
    (F₀ : ToposModule X) [RelativeModuleTensorProduct f] :
    relativeTensor f
        (FlatThickeningSituation.kernelModule S₂.t S₂.base_first_order) F₀ ⟶
      relativeTensor f
        (FlatThickeningSituation.kernelModule S₁.t S₁.base_first_order) F₀ :=
  relativeTensorMap f F₀ D.lower.kernelMap

/-- The induced map on Ext obstruction groups. -/
abbrev obstructionMap
    (D : FirstOrderThickeningDiagramMap S₁ S₂)
    (F₀ : ToposModule X) [RelativeModuleTensorProduct f]
    [ToposExtTheory X] :
    FlatLiftObstruction S₂ F₀ → FlatLiftObstruction S₁ F₀ :=
  ToposExtTheory.map 2 (coefficientMap D F₀)

end FirstOrderThickeningDiagramMap

/-- Functoriality of the obstruction class under a morphism of flat
thickenings. -/
theorem flatLiftObstructionClass_map
    {C D₁ D₂ E F₁ F₂ : Type u}
    [Category.{u} C] [Category.{u} D₁] [Category.{u} D₂]
    [Category.{u} E] [Category.{u} F₁] [Category.{u} F₂]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S₁ : FlatThickeningSituation (D := D₁) (F := F₁) X B f)
    (S₂ : FlatThickeningSituation (D := D₂) (F := F₂) X B f)
    (D : FirstOrderThickeningDiagramMap S₁ S₂)
    (F₀ : ToposModule X) [RelativeModuleTensorProduct f]
    [RelativeModuleTensorProduct S₁.square.f']
    [RelativeModuleTensorProduct S₂.square.f']
    [ToposExtTheory X]
    (hF : FlatModuleOver f F₀) :
    FirstOrderThickeningDiagramMap.obstructionMap D F₀
        (flatLiftObstructionClass S₂ F₀ hF) =
      flatLiftObstructionClass S₁ F₀ hF := by
  sorry

/-! ## Short exact sequences of thickenings -/

/-- A first-order thickening sequence records the maps of thickenings and the
short exact sequence of their chosen kernel modules. -/
structure FirstOrderThickeningSequence
    {C D₁ D₂ D₃ E F₁ F₂ F₃ : Type u}
    [Category.{u} C] [Category.{u} D₁] [Category.{u} D₂]
    [Category.{u} D₃] [Category.{u} E] [Category.{u} F₁]
    [Category.{u} F₂] [Category.{u} F₃]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S₁ : FlatThickeningSituation (D := D₁) (F := F₁) X B f)
    (S₂ : FlatThickeningSituation (D := D₂) (F := F₂) X B f)
    (S₃ : FlatThickeningSituation (D := D₃) (F := F₃) X B f) where
  upper₁₂ : FirstOrderThickeningDiagramMap S₁ S₂
  upper₂₃ : FirstOrderThickeningDiagramMap S₂ S₃
  top_zero : upper₂₃.upper.kernelMap ≫ upper₁₂.upper.kernelMap = 0
  top_short_exact :
    (ShortComplex.mk upper₂₃.upper.kernelMap upper₁₂.upper.kernelMap
      top_zero).ShortExact
  base_zero : upper₂₃.lower.kernelMap ≫ upper₁₂.lower.kernelMap = 0
  base_short_exact :
    (ShortComplex.mk upper₂₃.lower.kernelMap upper₁₂.lower.kernelMap
      base_zero).ShortExact

/-- A splitting of a first-order thickening, recorded at the module level. -/
structure ThickeningSplitting
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) where
  projection : RingedToposHom Y X
  retraction :
    projection.modulePullback ⋙ i.hom.modulePullback ≅ 𝟭 (ToposModule X)

/-- The reduction of the middle flat module in the short-exact situation. -/
abbrev reducedMiddleModule
    {C D₂ E F₂ : Type u}
    [Category.{u} C] [Category.{u} D₂]
    [Category.{u} E] [Category.{u} F₂]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S₂ : FlatThickeningSituation (D := D₂) (F := F₂) X B f)
    (G₂ : ToposModule S₂.Y) : ToposModule X :=
  S₂.i.hom.modulePullback.obj G₂

/-- Flatness descends from the middle thickening in the short-exact
configuration to its reduction. -/
theorem reducedMiddleModule_flat
    {C D₂ E F₂ : Type u}
    [Category.{u} C] [Category.{u} D₂]
    [Category.{u} E] [Category.{u} F₂]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S₂ : FlatThickeningSituation (D := D₂) (F := F₂) X B f)
    (G₂ : ToposModule S₂.Y) [RelativeModuleTensorProduct f]
    [RelativeModuleTensorProduct S₂.square.f']
    (hG₂ : FlatModuleOver S₂.square.f' G₂) :
    FlatModuleOver f (reducedMiddleModule S₂ G₂) := by
  sorry

/-- The data of Situation `situation-ses-flat-thickenings-ringed-topoi`. -/
structure ShortExactFlatThickeningSituation
    {C D₁ D₂ D₃ E F₁ F₂ F₃ : Type u}
    [Category.{u} C] [Category.{u} D₁] [Category.{u} D₂]
    [Category.{u} D₃] [Category.{u} E] [Category.{u} F₁]
    [Category.{u} F₂] [Category.{u} F₃]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S₁ : FlatThickeningSituation (D := D₁) (F := F₁) X B f)
    (S₂ : FlatThickeningSituation (D := D₂) (F := F₂) X B f)
    (S₃ : FlatThickeningSituation (D := D₃) (F := F₃) X B f)
    (P : FirstOrderThickeningSequence S₁ S₂ S₃)
    [RelativeModuleTensorProduct S₂.square.f'] where
  middleModule : ToposModule S₂.Y
  middleModule_flat : FlatModuleOver S₂.square.f' middleModule
  canonicalSplitting : ThickeningSplitting S₁.i

/-- The coefficient sequence obtained by tensoring the base kernel sequence
with a flat module. -/
structure CoefficientShortExactSequence
    {C D₁ D₂ D₃ E F₁ F₂ F₃ : Type u}
    [Category.{u} C] [Category.{u} D₁] [Category.{u} D₂]
    [Category.{u} D₃] [Category.{u} E] [Category.{u} F₁]
    [Category.{u} F₂] [Category.{u} F₃]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S₁ : FlatThickeningSituation (D := D₁) (F := F₁) X B f)
    (S₂ : FlatThickeningSituation (D := D₂) (F := F₂) X B f)
    (S₃ : FlatThickeningSituation (D := D₃) (F := F₃) X B f)
    (P : FirstOrderThickeningSequence S₁ S₂ S₃)
    (F₀ : ToposModule X) [RelativeModuleTensorProduct f] where
  k₃₂ : relativeTensor f
      (FlatThickeningSituation.kernelModule S₃.t S₃.base_first_order) F₀ ⟶
    relativeTensor f
      (FlatThickeningSituation.kernelModule S₂.t S₂.base_first_order) F₀
  k₂₁ : relativeTensor f
      (FlatThickeningSituation.kernelModule S₂.t S₂.base_first_order) F₀ ⟶
    relativeTensor f
      (FlatThickeningSituation.kernelModule S₁.t S₁.base_first_order) F₀
  k₃₂_canonical :
    k₃₂ = FirstOrderThickeningDiagramMap.coefficientMap P.upper₂₃ F₀
  k₂₁_canonical :
    k₂₁ = FirstOrderThickeningDiagramMap.coefficientMap P.upper₁₂ F₀
  zero : k₃₂ ≫ k₂₁ = 0
  short_exact : (ShortComplex.mk k₃₂ k₂₁ zero).ShortExact

/-- Flatness makes the displayed coefficient sequence short exact. -/
theorem coefficientShortExactSequence_exists
    {C D₁ D₂ D₃ E F₁ F₂ F₃ : Type u}
    [Category.{u} C] [Category.{u} D₁] [Category.{u} D₂]
    [Category.{u} D₃] [Category.{u} E] [Category.{u} F₁]
    [Category.{u} F₂] [Category.{u} F₃]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S₁ : FlatThickeningSituation (D := D₁) (F := F₁) X B f)
    (S₂ : FlatThickeningSituation (D := D₂) (F := F₂) X B f)
    (S₃ : FlatThickeningSituation (D := D₃) (F := F₃) X B f)
    (P : FirstOrderThickeningSequence S₁ S₂ S₃)
    (F₀ : ToposModule X) [RelativeModuleTensorProduct f]
    (hF : FlatModuleOver f F₀) :
    Nonempty (CoefficientShortExactSequence S₁ S₂ S₃ P F₀) := by
  sorry

/-- The connecting map for a coefficient short exact sequence. -/
def coefficientExtBoundary
    {C D₁ D₂ D₃ E F₁ F₂ F₃ : Type u}
    [Category.{u} C] [Category.{u} D₁] [Category.{u} D₂]
    [Category.{u} D₃] [Category.{u} E] [Category.{u} F₁]
    [Category.{u} F₂] [Category.{u} F₃]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S₁ : FlatThickeningSituation (D := D₁) (F := F₁) X B f)
    (S₂ : FlatThickeningSituation (D := D₂) (F := F₂) X B f)
    (S₃ : FlatThickeningSituation (D := D₃) (F := F₃) X B f)
    (P : FirstOrderThickeningSequence S₁ S₂ S₃)
    (F₀ : ToposModule X) [RelativeModuleTensorProduct f]
    [ToposExtTheory X]
    (Q : CoefficientShortExactSequence S₁ S₂ S₃ P F₀) :
    ExtGroup F₀
        (relativeTensor f
          (FlatThickeningSituation.kernelModule S₁.t S₁.base_first_order) F₀) 1 →
      ExtGroup F₀
        (relativeTensor f
          (FlatThickeningSituation.kernelModule S₃.t S₃.base_first_order) F₀) 2 :=
  ToposExtTheory.boundary Q.k₃₂ Q.k₂₁ Q.zero Q.short_exact

/-- The comparison and boundary statement of Lemma
`lemma-verify-iv-ringed-topoi`: the two displayed modules are flat lifts on
the first thickening, and their difference has boundary equal to the third
obstruction class. -/
theorem verify_iv_ringed_topoi
    {C D₁ D₂ D₃ E F₁ F₂ F₃ : Type u}
    [Category.{u} C] [Category.{u} D₁] [Category.{u} D₂]
    [Category.{u} D₃] [Category.{u} E] [Category.{u} F₁]
    [Category.{u} F₂] [Category.{u} F₃]
    {X : RingedTopos C} {B : RingedTopos E}
    {f : RingedToposHom X B}
    (S₁ : FlatThickeningSituation (D := D₁) (F := F₁) X B f)
    (S₂ : FlatThickeningSituation (D := D₂) (F := F₂) X B f)
    (S₃ : FlatThickeningSituation (D := D₃) (F := F₃) X B f)
    (P : FirstOrderThickeningSequence S₁ S₂ S₃)
    (G₂ : ToposModule S₂.Y)
    [RelativeModuleTensorProduct f]
    [RelativeModuleTensorProduct S₁.square.f']
    [RelativeModuleTensorProduct S₂.square.f']
    [RelativeModuleTensorProduct S₃.square.f']
    [ToposExtTheory X]
    (hG₂ : FlatModuleOver S₂.square.f' G₂)
    (π : ThickeningSplitting S₁.i)
    (Q : CoefficientShortExactSequence S₁ S₂ S₃ P
      (reducedMiddleModule S₂ G₂)) :
    ∃ A B₁ : FlatModuleLift S₁ (reducedMiddleModule S₂ G₂),
      A.module = π.projection.modulePullback.obj (reducedMiddleModule S₂ G₂) ∧
      B₁.module = P.upper₁₂.upper.h.modulePullback.obj G₂ ∧
      ∃ θ : ExtGroup (reducedMiddleModule S₂ G₂)
          (relativeTensor f
            (FlatThickeningSituation.kernelModule S₁.t S₁.base_first_order)
            (reducedMiddleModule S₂ G₂)) 1,
        coefficientExtBoundary S₁ S₂ S₃ P
            (reducedMiddleModule S₂ G₂) Q θ =
          flatLiftObstructionClass S₃ (reducedMiddleModule S₂ G₂)
            (reducedMiddleModule_flat S₂ G₂ hG₂) := by
  sorry

end

end Formalization.Books.Defos.Unit12
