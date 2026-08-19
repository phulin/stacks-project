import Formalization.Books.Descent.Unit03
import Formalization.Books.Categories.Unit10.Equalizers
import Formalization.Books.Categories.Unit11.Coequalizers
import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Formalization.Books.Algebra.Unit82.UniversallyInjective
import Formalization.Books.Algebra.Unit148.FormallyUnramifiedMaps
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent

/-!
# Descent, Chapter 4: Descent for universally injective morphisms

This file records the category-theoretic, module-theoretic, and algebraic
interfaces in the chapter.  The concrete tensor presentations and the
standard descent datum are inherited from Chapter 3; the chapter-facing
names below retain the source's organization and hypotheses.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct

namespace Formalization.Books.Descent.Unit04

open Formalization.Books.Descent.Unit03

universe u v w

/-! ## 4.1 Category-theoretic preliminaries -/

section CategoryPreliminaries

variable {C : Type u} [Category.{v} C]

/-- The split equalizer data displayed in the source.

The equations are written in Lean's left-to-right composition convention.
The first field records that the displayed pair is parallelized; the other
three fields are the auxiliary maps and their three splitting identities. -/
structure SplitEqualizer {A B D : C} (f : A ⟶ B) (g₁ g₂ : B ⟶ D) where
  condition : f ≫ g₁ = f ≫ g₂
  h : B ⟶ A
  i : D ⟶ B
  h_f : f ≫ h = 𝟙 A
  f_h : h ≫ f = g₁ ≫ i
  i_g₂ : g₂ ≫ i = 𝟙 B

/-- The dual split coequalizer data. -/
structure SplitCoequalizer {A B D : C} (f₁ f₂ : A ⟶ B) (q : B ⟶ D) where
  condition : f₁ ≫ q = f₂ ≫ q
  h : D ⟶ B
  i : B ⟶ A
  q_h : h ≫ q = 𝟙 D
  h_q : q ≫ h = i ≫ f₁
  i_f₂ : i ≫ f₂ = 𝟙 B := by cat_disch

/-- The source's universal-property formulation of a split equalizer. -/
noncomputable def SplitEqualizer.isLimit {A B D : C} {f : A ⟶ B} {g₁ g₂ : B ⟶ D}
    (s : SplitEqualizer f g₁ g₂) : IsLimit (Fork.ofι f s.condition) := by
  sorry

/-- The dual universal-property formulation. -/
noncomputable def SplitCoequalizer.isColimit {A B D : C} {f₁ f₂ : A ⟶ B} {q : B ⟶ D}
    (s : SplitCoequalizer f₁ f₂ q) : IsColimit (Cofork.ofπ q s.condition) := by
  sorry

theorem SplitEqualizer.isEqualizer {A B D : C} {f : A ⟶ B} {g₁ g₂ : B ⟶ D}
    (s : SplitEqualizer f g₁ g₂) :
    Formalization.Books.Categories.Unit10.IsEqualizer f g₁ g₂ := by
  exact ⟨s.condition, ⟨s.isLimit⟩⟩

theorem SplitCoequalizer.isCoequalizer {A B D : C} {f₁ f₂ : A ⟶ B} {q : B ⟶ D}
    (s : SplitCoequalizer f₁ f₂ q) :
    Formalization.Books.Categories.Unit11.IsCoequalizer q f₁ f₂ := by
  exact ⟨s.condition, ⟨s.isColimit⟩⟩

/-- Covariant functors carry split equalizers to split equalizers. -/
noncomputable def Functor.map_splitEqualizer {A B D : C} {f : A ⟶ B} {g₁ g₂ : B ⟶ D}
    {E : Type w} [Category.{v} E] (F : C ⥤ E) (s : SplitEqualizer f g₁ g₂) :
    SplitEqualizer (F.map f) (F.map g₁) (F.map g₂) := by
  sorry

/-- Contravariant functors carry split equalizers to split coequalizers. -/
noncomputable def Functor.map_op_splitEqualizer {A B D : C} {f : A ⟶ B} {g₁ g₂ : B ⟶ D}
    {E : Type w} [Category.{v} E] (F : Cᵒᵖ ⥤ E) (s : SplitEqualizer f g₁ g₂) :
    SplitCoequalizer (F.map g₁.op) (F.map g₂.op) (F.map f.op) := by
  sorry

end CategoryPreliminaries

/-! ## 4.2 Universally injective morphisms -/

section UniversallyInjective

variable {R S M N P : Type u}
  [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- An exact functor between abelian categories which sends nonzero objects to
nonzero objects reflects monomorphisms and epimorphisms. -/
theorem exact_nonzero_functor_reflects_mono_epi
    {A B : Type u} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (hF : ∀ X : A, ¬ IsZero X → ¬ IsZero (F.obj X))
    {X Y : A} (f : X ⟶ Y) :
    (Mono (F.map f) → Mono f) ∧ (Epi (F.map f) → Epi f) := by
  sorry

/-- The universal-injectivity predicate for the module map underlying a ring
map.  This reuses Algebra chapter 82's canonical tensor formulation. -/
def universallyInjectiveRingMap (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Formalization.Books.Algebra.Unit82.universallyInjective (Algebra.linearMap R S)

/-- A split module map is universally injective. -/
theorem universallyInjective_of_split_module_map
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) (h : g.comp f = LinearMap.id) :
    Formalization.Books.Algebra.Unit82.universallyInjective f :=
  Formalization.Books.Algebra.Unit82.universallyInjective_of_left_inverse f g h

/-- In particular, a split algebra map is universally injective. -/
theorem universallyInjective_of_split_algebra_map
    [Algebra R S] (g : S →ₐ[R] R)
    (h : g.toRingHom.comp (algebraMap R S) = RingHom.id R) :
    universallyInjectiveRingMap (algebraMap R S) := by
  sorry

/-- The finite standard-open cover map from the source, written as a product
of localizations (for a finite index type, product and direct sum agree). -/
def standardLocalizationProductMap {ι : Type u} [Fintype ι]
    (a : ι → R) : R →+* (∀ i, Localization.Away (a i)) where
  toFun r i := algebraMap R (Localization.Away (a i)) r
  map_one' := by ext i; simp
  map_mul' r s := by ext i; simp
  map_zero' := by ext i; simp
  map_add' r s := by ext i; simp

theorem standardLocalizationProductMap_universallyInjective
    {ι : Type u} [Fintype ι] (a : ι → R)
    (ha : Ideal.span (Set.range a) = ⊤) :
    universallyInjectiveRingMap (standardLocalizationProductMap a) := by
  sorry

/-- Faithfully flat ring maps are universally injective. -/
theorem faithfullyFlat_universallyInjective
    (f : R →+* S) (hf : RingHom.FaithfullyFlat f) :
    universallyInjectiveRingMap f := by
  sorry

/-- The character module `C(M) = Hom_Ab(M, Q/Z)` is Mathlib's
`CharacterModule M`. -/
abbrev C (M : Type u) [AddCommGroup M] := CharacterModule M

/-- The contravariant character-module map. -/
abbrev CMap (f : M →ₗ[R] N) : C N →ₗ[R] C M := CharacterModule.dual f

/-- The tensor--Hom adjunction used in the chapter. -/
noncomputable def characterTensorHomEquiv
    (M₁ M₂ : Type u) [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] :
    C (M₁ ⊗[R] M₂) ≃ₗ[R] (M₁ →ₗ[R] C M₂) :=
  CharacterModule.homEquiv.symm

/-- The character-module construction as a contravariant functor. -/
noncomputable def characterModuleFunctor : (ModuleCat R)ᵒᵖ ⥤ ModuleCat R where
  obj M := ModuleCat.of R (C (M.unop : Type u))
  map f := ModuleCat.ofHom (CMap f.unop.hom)
  map_id := by
    intro M
    ext x y
    rfl
  map_comp := by
    intro X Y Z f g
    ext x y
    rfl

/-- The character module is exact and reflects injections and surjections. -/
theorem characterModuleFunctor_exact_reflects :
    PreservesFiniteLimits (characterModuleFunctor (R := R)) ∧
      PreservesFiniteColimits (characterModuleFunctor (R := R)) := by
  sorry

theorem characterModule_reflects_injective_surjective (f : M →ₗ[R] N) :
    (Function.Injective (CMap f) → Function.Surjective f) ∧
      (Function.Surjective (CMap f) → Function.Injective f) := by
  sorry

/-- A linear map is split surjective when it has a linear section. -/
def SplitSurjective (f : M →ₗ[R] N) : Prop :=
  ∃ g : N →ₗ[R] M, f.comp g = LinearMap.id

/-- Universal injectivity is equivalent to split surjectivity after applying
the character module. -/
theorem universallyInjective_iff_CMap_splitSurjective (f : M →ₗ[R] N) :
    Formalization.Books.Algebra.Unit82.universallyInjective f ↔
      SplitSurjective (CMap f) := by
  sorry

/-- A chosen character-module splitting is functorial after tensoring. -/
theorem CMap_rTensor_splitSurjective
    (f : M →ₗ[R] N) (g : C M →ₗ[R] C N)
    (hg : (CMap f).comp g = LinearMap.id) (Q : Type u)
    [AddCommGroup Q] [Module R Q] :
    SplitSurjective (CMap (f.rTensor Q)) := by
  sorry

noncomputable def characterTensor_preserves_splitCoequalizer
    {X Y Z : Type u} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    {f : X →ₗ[R] Y} {g₁ g₂ : Y →ₗ[R] Z}
    (s : SplitEqualizer (ModuleCat.ofHom f)
      (ModuleCat.ofHom g₁) (ModuleCat.ofHom g₂))
    (Q : Type u) [AddCommGroup Q] [Module R Q] :
    SplitCoequalizer
      (ModuleCat.ofHom (CMap (g₁.rTensor Q)))
      (ModuleCat.ofHom (CMap (g₂.rTensor Q)))
      (ModuleCat.ofHom (CMap (f.rTensor Q))) := by
  sorry

end UniversallyInjective

/-! ## 4.3 Descent for modules and their morphisms -/

section ModuleDescent

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-! ### The low-degree Amitsur rings and their maps -/

abbrev S1 (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :=
  relativeTensorProduct R S 0
abbrev S2 (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :=
  relativeTensorProduct R S 1
abbrev S3 (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :=
  relativeTensorProduct R S 2

def deltaOneZero : S1 R S →+* S2 R S := relativeTensorFace R S 0 0
def deltaOneOne : S1 R S →+* S2 R S := relativeTensorFace R S 0 1
def deltaTwoZero : S2 R S →+* S3 R S := relativeTensorFace R S 1 0
def deltaTwoOne : S2 R S →+* S3 R S := relativeTensorFace R S 1 1
def deltaTwoTwo : S2 R S →+* S3 R S := relativeTensorFace R S 1 2

def deltaOneZeroOne : S1 R S →+* S3 R S :=
  relativeTensorMap R S (descentVertexSimplexMap 2 ⟨2, by decide⟩)
def deltaOneZeroTwo : S1 R S →+* S3 R S :=
  relativeTensorMap R S (descentVertexSimplexMap 2 ⟨1, by decide⟩)
def deltaOneTwo : S1 R S →+* S3 R S :=
  relativeTensorMap R S (descentVertexSimplexMap 2 ⟨0, by decide⟩)

theorem deltaOneZero_pure (s : S) : deltaOneZero (PiTensorProduct.tprod R (fun _ : Fin 1 => s)) =
    PiTensorProduct.tprod R (fun j : Fin 2 => if j = 0 then 1 else s) := by
  sorry

theorem deltaOneOne_pure (s : S) : deltaOneOne (PiTensorProduct.tprod R (fun _ : Fin 1 => s)) =
    PiTensorProduct.tprod R (fun j : Fin 2 => if j = 0 then s else 1) := by
  sorry

theorem deltaTwoZero_pure (s₀ s₁ : S) :
    deltaTwoZero (PiTensorProduct.tprod R (fun | 0 => s₀ | 1 => s₁)) =
      PiTensorProduct.tprod R (fun j : Fin 3 => if j = 0 then 1 else if j = 1 then s₀ else s₁) := by
  sorry

theorem deltaTwoOne_pure (s₀ s₁ : S) :
    deltaTwoOne (PiTensorProduct.tprod R (fun | 0 => s₀ | 1 => s₁)) =
      PiTensorProduct.tprod R (fun j : Fin 3 => if j = 0 then s₀ else if j = 1 then 1 else s₁) := by
  sorry

theorem deltaTwoTwo_pure (s₀ s₁ : S) :
    deltaTwoTwo (PiTensorProduct.tprod R (fun | 0 => s₀ | 1 => s₁)) =
      PiTensorProduct.tprod R (fun j : Fin 3 => if j = 0 then s₀ else if j = 1 then s₁ else 1) := by
  sorry

theorem deltaOneZeroOne_pure (s : S) :
    deltaOneZeroOne (PiTensorProduct.tprod R (fun _ : Fin 1 => s)) =
      PiTensorProduct.tprod R (fun j : Fin 3 => if j = 0 then 1 else if j = 1 then 1 else s) := by
  sorry

theorem deltaOneZeroTwo_pure (s : S) :
    deltaOneZeroTwo (PiTensorProduct.tprod R (fun _ : Fin 1 => s)) =
      PiTensorProduct.tprod R (fun j : Fin 3 => if j = 0 then 1 else if j = 1 then s else 1) := by
  sorry

theorem deltaOneTwo_pure (s : S) :
    deltaOneTwo (PiTensorProduct.tprod R (fun _ : Fin 1 => s)) =
      PiTensorProduct.tprod R (fun j : Fin 3 => if j = 0 then s else if j = 1 then 1 else 1) := by
  sorry

/-! ### Descent data and the base-extension functor -/

/-- An `S`-module equipped with the descent datum of Chapter 3.  The
comparison is the canonical tensor presentation of the source's `θ`; its
cocycle and scalar-compatibility fields are retained by `DescentDatum`. -/
structure ModuleDescentData (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [moduleR : Module R carrier]
  [moduleS : Module S carrier]
  [tower : IsScalarTower R S carrier]
  datum : DescentDatum (R := R) (A := S) (N := carrier)

instance (D : ModuleDescentData R S) : AddCommGroup D.carrier := D.addCommGroup
instance (D : ModuleDescentData R S) : Module R D.carrier := D.moduleR
instance (D : ModuleDescentData R S) : Module S D.carrier := D.moduleS
instance (D : ModuleDescentData R S) : IsScalarTower R S D.carrier := D.tower

/-- Morphisms of module descent data. -/
structure ModuleDescentDataHom (D E : ModuleDescentData R S) where
  hom : D.carrier →ₗ[S] E.carrier
  commutes : descentMorphismCompatibility D.datum E.datum hom

theorem ModuleDescentDataHom.ext {D E : ModuleDescentData R S}
    (f g : ModuleDescentDataHom D E) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (ModuleDescentData R S) where
  Hom D E := ModuleDescentDataHom D E
  id D :=
    { hom := LinearMap.id
      commutes := by sorry }
  comp f g :=
    { hom := g.hom.comp f.hom
      commutes := by sorry }
  id_comp := by intro D E f; cases f; rfl
  comp_id := by intro D E f; cases f; rfl
  assoc := by intro A B C D f g h; cases f; cases g; cases h; rfl

/-- The canonical datum attached to an `R`-module after extension of scalars. -/
noncomputable def baseExtensionObject (M : ModuleCat R) : ModuleDescentData R S :=
  { carrier := S ⊗[R] (M : Type u)
    datum := canonicalDescentDatum (R := R) (A := S) (M := (M : Type u)) }

noncomputable def baseExtension : ModuleCat R ⥤ ModuleDescentData R S where
  obj M := baseExtensionObject (R := R) (S := S) M
  map f :=
    { hom := TensorProduct.AlgebraTensorModule.lTensor S S f.hom
      commutes := by sorry }
  map_id := by
    sorry
  map_comp := by
    sorry

def descentMorphismForModules : Prop :=
  Nonempty (baseExtension (R := R) (S := S)).FullyFaithful

def effectiveDescentMorphismForModules : Prop :=
  (baseExtension (R := R) (S := S)).IsEquivalence

/-! ### Equalizer interfaces and the inverse functor -/

def descentEqualizerLeft (D : ModuleDescentData R S) :
    D.carrier →ₗ[R] TensorProduct R S D.carrier :=
  TensorProduct.mk R S D.carrier 1

def descentEqualizerRight (D : ModuleDescentData R S) :
    D.carrier →ₗ[R] TensorProduct R S D.carrier :=
  D.datum.comparison.toLinearMap.comp ((TensorProduct.mk R D.carrier S).flip 1)

def descentEqualizerInclusion (D : ModuleDescentData R S) :
    descentH0 D.datum →ₗ[R] D.carrier :=
  (descentH0 D.datum).subtype

theorem descentEqualizerInclusion_condition (D : ModuleDescentData R S) :
    (descentEqualizerLeft D).comp (descentEqualizerInclusion D) =
      (descentEqualizerRight D).comp (descentEqualizerInclusion D) := by
  sorry

noncomputable def descentEqualizer_is_split
    (D : ModuleDescentData R S) :
    SplitEqualizer (ModuleCat.ofHom (descentEqualizerInclusion D))
      (ModuleCat.ofHom (descentEqualizerLeft D))
      (ModuleCat.ofHom (descentEqualizerRight D)) := by
  sorry

theorem descentPushforwardObject_isEqualizer (D : ModuleDescentData R S) :
    Formalization.Books.Categories.Unit10.IsEqualizer
      (ModuleCat.ofHom (descentEqualizerInclusion D))
      (ModuleCat.ofHom (descentEqualizerLeft D))
      (ModuleCat.ofHom (descentEqualizerRight D)) :=
  (descentEqualizer_is_split D).isEqualizer

noncomputable def descentEqualizer_character_is_split_coequalizer
    (D : ModuleDescentData R S) :
    SplitCoequalizer
      (ModuleCat.ofHom (CMap (descentEqualizerLeft D)))
      (ModuleCat.ofHom (CMap (descentEqualizerRight D)))
      (ModuleCat.ofHom (CMap (descentEqualizerInclusion D))) := by
  sorry

noncomputable def tensor_ring_equalizer_is_split :
    SplitEqualizer (CommRingCat.ofHom (deltaOneOne (R := R) (S := S)))
      (CommRingCat.ofHom (deltaTwoTwo (R := R) (S := S)))
      (CommRingCat.ofHom (deltaTwoOne (R := R) (S := S))) := by
  sorry

/- The source's `f_*` is the degree-zero equalizer. -/
def descentPushforwardObject (D : ModuleDescentData R S) : ModuleCat R :=
  ModuleCat.of R (descentH0 D.datum)

noncomputable def descentPushforward : ModuleDescentData R S ⥤ ModuleCat R where
  obj D := descentPushforwardObject D
  map := by
    intro D E f
    apply ModuleCat.ofHom
    let h : descentH0 D.datum →ₗ[R] descentH0 E.datum :=
      { toFun := fun x => ⟨f.hom x, by sorry⟩
        map_add' := by sorry
        map_smul' := by sorry }
    exact h
  map_id := by
    intro D
    ext x
    rfl
  map_comp := by
    intro D E F f g
    ext x
    rfl

theorem baseExtension_adjunction_descentPushforward :
    Nonempty (baseExtension (R := R) (S := S) ⊣ descentPushforward (R := R) (S := S)) := by
  sorry

/-! ### The descent theorem -/

noncomputable def descent_lemma
    (D : ModuleDescentData R S)
    (hUI : Formalization.Books.Algebra.Unit82.universallyInjective
      (Algebra.linearMap R S)) :
    IsLimit (Fork.ofι
      (ModuleCat.ofHom (descentEqualizerInclusion D))
      (f := ModuleCat.ofHom (descentEqualizerLeft D))
      (g := ModuleCat.ofHom (descentEqualizerRight D))
      (by
        apply ModuleCat.hom_ext
        exact descentEqualizerInclusion_condition D)) := by
  sorry

theorem descent_for_modules_iff :
    (descentMorphismForModules (R := R) (S := S) ↔
      effectiveDescentMorphismForModules (R := R) (S := S)) ∧
      (effectiveDescentMorphismForModules (R := R) (S := S) ↔
        Formalization.Books.Algebra.Unit82.universallyInjective
          (Algebra.linearMap R S)) := by
  sorry

end ModuleDescent

/-! ## 4.4 Descent for properties of modules -/

section DescentProperties

variable {R S M A : Type u}
  [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]
  [CommRing A] [Algebra R A]

theorem flat_characterModule_injective
    [Module.Flat R M] : Module.Injective R (CharacterModule M) := by
  exact (Module.Flat.iff_characterModule_injective (R := R) (M := M)).mp inferInstance

/-- The five module properties listed in the source, in canonical Mathlib
forms.  The last clause uses the earlier chapter's canonical finite-projective
predicate rather than introducing a duplicate definition. -/
theorem descend_module_properties
    (hUI : Formalization.Books.Algebra.Unit82.universallyInjective
      (Algebra.linearMap R S)) :
    (Module.Finite S (S ⊗[R] M) ↔ Module.Finite R M) ∧
      (Module.FinitePresentation S (S ⊗[R] M) ↔ Module.FinitePresentation R M) ∧
      (Module.Flat S (S ⊗[R] M) ↔ Module.Flat R M) ∧
      (Module.FaithfullyFlat S (S ⊗[R] M) ↔ Module.FaithfullyFlat R M) ∧
      (Formalization.Books.Algebra.Unit78.FiniteProjective S (S ⊗[R] M) ↔
        Formalization.Books.Algebra.Unit78.FiniteProjective R M) := by
  sorry

/-- The five algebra properties listed in the source. -/
theorem descend_algebra_properties
    (hUI : Formalization.Books.Algebra.Unit82.universallyInjective
      (Algebra.linearMap R S)) :
    letI : Algebra S (S ⊗[R] A) := Algebra.TensorProduct.leftAlgebra
    (Algebra.FiniteType S (S ⊗[R] A) ↔ Algebra.FiniteType R A) ∧
      (Algebra.FinitePresentation S (S ⊗[R] A) ↔ Algebra.FinitePresentation R A) ∧
      (Algebra.FormallyUnramified S (S ⊗[R] A) ↔ Algebra.FormallyUnramified R A) ∧
      (Algebra.Unramified S (S ⊗[R] A) ↔ Algebra.Unramified R A) ∧
      (Algebra.Etale S (S ⊗[R] A) ↔ Algebra.Etale R A) := by
  sorry

/-! The final warning in the source is recorded with Mathlib's injective-module
predicate: over `ℤ`, no faithfully flat algebra is injective as a module. -/
theorem no_faithfullyFlat_injective_integer_algebra :
    ¬ ∃ (T : Type u) (_ : CommRing T) (_ : Algebra ℤ T),
      Module.FaithfullyFlat ℤ T ∧ Module.Injective ℤ T := by
  sorry

end DescentProperties

end Formalization.Books.Descent.Unit04
