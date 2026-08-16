import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.KrullDimension

/-!
# The structure sheaf on the fibre product

This file records the constructions and statements in Chapter 5 of
books/examples.tex. The difficult comparison theorems are deliberately
interfaces at this stage; their proofs belong to the proof stage.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped TensorProduct

namespace Formalization.«Books.Examples».Unit05

universe u

/-! ## The fibre-product diagram -/

structure FiberProductContext (X Y S : Scheme.{u}) where
  /-- The two maps entering the fibre product. -/
  a : X ⟶ S
  b : Y ⟶ S

namespace FiberProductContext

variable {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)

/-- The scheme-theoretic fibre product attached to C. -/
abbrev product (C : FiberProductContext X Y S) : Scheme := pullback C.a C.b

/-- The first projection from the fibre product. -/
abbrev p (C : FiberProductContext X Y S) : product C ⟶ X := pullback.fst C.a C.b

/-- The second projection from the fibre product. -/
abbrev q (C : FiberProductContext X Y S) : product C ⟶ Y := pullback.snd C.a C.b

/-- The structure map of the fibre product to the base. -/
def f (C : FiberProductContext X Y S) : product C ⟶ S := p C ≫ C.a

/-- The two routes from the fibre product to the base agree. -/
theorem projection_base_compatibility (C : FiberProductContext X Y S) :
    p C ≫ C.a = q C ≫ C.b := by
  exact pullback.condition

end FiberProductContext

/-! ## Tensor products and the canonical comparison maps -/

/-- The canonical algebra map out of a tensor product when the two maps commute.

For commutative target rings the commutation condition is automatic. This is
the algebraic model for the stalk map in the chapter.
-/
def canonicalTensorAlgHom
    {R A B C : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (left : A →ₐ[R] C) (right : B →ₐ[R] C) :
    A ⊗[R] B →ₐ[R] C :=
  Algebra.TensorProduct.lift left right (fun _ _ => Commute.all _ _)

@[simp]
theorem canonicalTensorAlgHom_tmul
    {R A B C : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (left : A →ₐ[R] C) (right : B →ₐ[R] C) (a : A) (b : B) :
    canonicalTensorAlgHom left right (a ⊗ₜ[R] b) = left a * right b := by
  exact Algebra.TensorProduct.lift_tmul left right (fun _ _ => Commute.all _ _) a b

/-!
Mathlib does not expose a pushout instance for sheaves of commutative rings.
The following span is therefore the minimal interface for the source's sheaf
tensor product and its canonical map; its tensor object and comparison map
are supplied by the geometric comparison theorem below.
-/

structure RingSheafSpan (Z : Scheme.{u}) where
  base : TopCat.Sheaf CommRingCat.{u} Z
  left : TopCat.Sheaf CommRingCat.{u} Z
  right : TopCat.Sheaf CommRingCat.{u} Z
  target : TopCat.Sheaf CommRingCat.{u} Z
  baseToLeft : base ⟶ left
  baseToRight : base ⟶ right
  leftToTarget : left ⟶ target
  rightToTarget : right ⟶ target
  compatibility : baseToLeft ≫ leftToTarget = baseToRight ≫ rightToTarget
  tensor : TopCat.Sheaf CommRingCat.{u} Z
  tensorInl : left ⟶ tensor
  tensorInr : right ⟶ tensor
  tensorCondition : baseToLeft ≫ tensorInl = baseToRight ≫ tensorInr
  tensorIsColimit :
    IsColimit (PushoutCocone.mk tensorInl tensorInr tensorCondition)

/-- The sheaf tensor product object recorded by a comparison span. -/
noncomputable def sheafTensor (D : RingSheafSpan Z) : TopCat.Sheaf CommRingCat.{u} Z :=
  D.tensor

/-- The canonical map from the sheaf tensor product to the target sheaf. -/
noncomputable def sheafTensorToTarget (D : RingSheafSpan Z) :
    sheafTensor D ⟶ D.target :=
  PushoutCocone.IsColimit.desc D.tensorIsColimit D.leftToTarget D.rightToTarget
    D.compatibility

/-- The inverse-image structure sheaf along a scheme morphism. -/
def inverseImageStructureSheaf {X Y : Scheme.{u}} (g : X ⟶ Y) :
    TopCat.Sheaf CommRingCat X :=
  (TopCat.Sheaf.pullback CommRingCat g.base).obj Y.sheaf

theorem fiberProduct_structureSheaf_comparison_interface
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S) :
    ∃ D : RingSheafSpan (FiberProductContext.product C),
      D.base = inverseImageStructureSheaf (FiberProductContext.f C) ∧
        D.left = inverseImageStructureSheaf (FiberProductContext.p C) ∧
        D.right = inverseImageStructureSheaf (FiberProductContext.q C) ∧
        D.target = (FiberProductContext.product C).sheaf := by
  sorry

theorem fiberProduct_structureSheaf_comparison_not_generally_isomorphic :
    ∃ (X Y S : Scheme.{u}) (C : FiberProductContext X Y S)
      (D : RingSheafSpan (FiberProductContext.product C)),
      D.base = inverseImageStructureSheaf (FiberProductContext.f C) ∧
        D.left = inverseImageStructureSheaf (FiberProductContext.p C) ∧
        D.right = inverseImageStructureSheaf (FiberProductContext.q C) ∧
        D.target = (FiberProductContext.product C).sheaf ∧
        ¬ IsIso (sheafTensorToTarget D) := by
  sorry

/-! ## The affine complex example -/

abbrev RealComplexBase : Scheme := Spec (.of ℝ)
abbrev RealComplexPoint : Scheme := Spec (.of ℂ)

def realComplexPointToBase : RealComplexPoint ⟶ RealComplexBase :=
  Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))

abbrev realComplexFiberProduct : Scheme :=
  pullback realComplexPointToBase realComplexPointToBase

abbrev realComplexTwoPointScheme : Scheme := RealComplexPoint ⨿ RealComplexPoint

/-- The pullback of two copies of Spec ℂ over Spec ℝ is two points. -/
theorem realComplex_fiberProduct_is_two_points :
    Nonempty (realComplexFiberProduct ≅ realComplexTwoPointScheme) := by
  sorry

/-- The source and target rings of the global-sections comparison in the
two-point example, written as real vector spaces. -/
abbrev realComplexSourceGlobalSections : Type :=
  (ℂ ⊗[ℝ] ℂ) × (ℂ ⊗[ℝ] ℂ)

abbrev realComplexTargetGlobalSections : Type := ℂ × ℂ

theorem realComplex_source_global_sections_finrank :
    Module.finrank ℝ realComplexSourceGlobalSections = 8 := by
  sorry

theorem realComplex_target_global_sections_finrank :
    Module.finrank ℝ realComplexTargetGlobalSections = 4 := by
  sorry

/-- Consequently the canonical global-sections comparison cannot be an
isomorphism of real vector spaces. -/
theorem realComplex_global_sections_not_linearly_equivalent :
    ¬ Nonempty (realComplexSourceGlobalSections ≃ₗ[ℝ] realComplexTargetGlobalSections) := by
  sorry

/-- The tensor product in the example is not local, matching the stalk-level
warning that a tensor product of local rings need not be local. -/
theorem realComplex_tensorProduct_not_local :
    ¬ IsLocalRing (ℂ ⊗[ℝ] ℂ) := by
  sorry

/-! ## Stalks -/

/-- The four stalk rings occurring at a point of a scheme fibre product. -/
abbrev fiberProductBaseStalk
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)
    (z : FiberProductContext.product C) : CommRingCat :=
  S.presheaf.stalk (C.a ((FiberProductContext.p C) z))

abbrev fiberProductLeftStalk
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)
    (z : FiberProductContext.product C) : CommRingCat :=
  X.presheaf.stalk ((FiberProductContext.p C) z)

abbrev fiberProductRightStalk
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)
    (z : FiberProductContext.product C) : CommRingCat :=
  Y.presheaf.stalk ((FiberProductContext.q C) z)

abbrev fiberProductTargetStalk
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)
    (z : FiberProductContext.product C) : CommRingCat :=
  (FiberProductContext.product C).presheaf.stalk z

theorem fiberProduct_basePointEq
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)
    (z : FiberProductContext.product C) :
    C.a ((FiberProductContext.p C) z) = C.b ((FiberProductContext.q C) z) := by
  sorry

/-- The stalk maps around the fibre-product square. -/
def fiberProductBaseToLeftStalk
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)
    (z : FiberProductContext.product C) :
    fiberProductBaseStalk C z ⟶ fiberProductLeftStalk C z :=
  C.a.stalkMap ((FiberProductContext.p C) z)

def fiberProductBaseToRightStalk
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)
    (z : FiberProductContext.product C) :
  fiberProductBaseStalk C z ⟶ fiberProductRightStalk C z :=
  (S.presheaf.stalkCongr (.of_eq (fiberProduct_basePointEq C z))).hom ≫
    C.b.stalkMap ((FiberProductContext.q C) z)

def fiberProductLeftToTargetStalk
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)
    (z : FiberProductContext.product C) :
    fiberProductLeftStalk C z ⟶ fiberProductTargetStalk C z :=
  (FiberProductContext.p C).stalkMap z

def fiberProductRightToTargetStalk
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)
    (z : FiberProductContext.product C) :
    fiberProductRightStalk C z ⟶ fiberProductTargetStalk C z :=
  (FiberProductContext.q C).stalkMap z

theorem fiberProduct_stalk_square
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)
    (z : FiberProductContext.product C) :
    fiberProductBaseToLeftStalk C z ≫ fiberProductLeftToTargetStalk C z =
      fiberProductBaseToRightStalk C z ≫ fiberProductRightToTargetStalk C z := by
  sorry

/-- A usable algebraic presentation of a stalk comparison map.

The scheme-specific existence theorem below supplies such presentations for
the stalks of a fibre product. The algebra map itself is the canonical
tensor-product map defined above.
-/
structure StalkTensorPresentation
    (R A B T : Type u)
    [CommRing R] [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T] where
  left : A →ₐ[R] T
  right : B →ₐ[R] T

def StalkTensorPresentation.map
    {R A B T : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T]
    (P : StalkTensorPresentation R A B T) : A ⊗[R] B →ₐ[R] T :=
  canonicalTensorAlgHom P.left P.right

def IsLocalizationAlong
    {A T : Type u} [CommRing A] [CommRing T]
    (φ : A →+* T) (M : Submonoid A) : Prop :=
  letI : Algebra A T := φ.toAlgebra
  IsLocalization M T

theorem fiberProduct_stalk_comparison_is_flat_of_localization
    {R A B T : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T]
    (P : StalkTensorPresentation R A B T) (M : Submonoid (A ⊗[R] B))
    (hM : IsLocalizationAlong (StalkTensorPresentation.map P).toRingHom M) :
    RingHom.Flat (StalkTensorPresentation.map P).toRingHom := by
  sorry

/-!
For a scheme fibre product, the four rings in the source statement are the
stalks at s, x, y, and z; the actual identification with a localization
is the geometric input to the preceding flatness interface.
-/
theorem fiberProduct_stalk_canonical_presentation
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)
    (z : FiberProductContext.product C)
    [Algebra (fiberProductBaseStalk C z) (fiberProductLeftStalk C z)]
    [Algebra (fiberProductBaseStalk C z) (fiberProductRightStalk C z)]
    [Algebra (fiberProductBaseStalk C z) (fiberProductTargetStalk C z)] :
    Nonempty (StalkTensorPresentation
      (fiberProductBaseStalk C z) (fiberProductLeftStalk C z)
      (fiberProductRightStalk C z) (fiberProductTargetStalk C z)) := by
  sorry

theorem fiberProduct_stalk_comparison_interface
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)
    (z : FiberProductContext.product C)
    [Algebra (fiberProductBaseStalk C z) (fiberProductLeftStalk C z)]
    [Algebra (fiberProductBaseStalk C z) (fiberProductRightStalk C z)]
    [Algebra (fiberProductBaseStalk C z) (fiberProductTargetStalk C z)] :
    ∃ (P : StalkTensorPresentation
        (fiberProductBaseStalk C z) (fiberProductLeftStalk C z)
        (fiberProductRightStalk C z) (fiberProductTargetStalk C z))
      (M : Submonoid
        (fiberProductLeftStalk C z ⊗[fiberProductBaseStalk C z]
          fiberProductRightStalk C z)),
      IsLocalizationAlong (StalkTensorPresentation.map P).toRingHom M ∧
        RingHom.Flat (StalkTensorPresentation.map P).toRingHom := by
  sorry

/-! ## The affine-plane example -/

abbrev AffineLine (k : Type u) [CommRing k] : Scheme :=
  Spec (.of (Polynomial k))

def affineLineToPoint (k : Type u) [CommRing k] :
    AffineLine k ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))

abbrev affinePlaneContext (k : Type u) [CommRing k] :
    FiberProductContext (AffineLine k) (AffineLine k) (Spec (.of k)) where
  a := affineLineToPoint k
  b := affineLineToPoint k

abbrev AffinePlane (k : Type u) [CommRing k] : Scheme :=
  FiberProductContext.product (affinePlaneContext k)

abbrev AffineTwoSpace (k : Type u) [CommRing k] : Scheme :=
  Spec (.of (MvPolynomial (Fin 2) k))

theorem affinePlane_is_affineTwoSpace
    (k : Type u) [Field k] :
    Nonempty (AffinePlane k ≅ AffineTwoSpace k) := by
  sorry

abbrev affinePlaneProjection₁ (k : Type u) [CommRing k] :
    AffinePlane k ⟶ AffineLine k :=
  FiberProductContext.p (affinePlaneContext k)

abbrev affinePlaneProjection₂ (k : Type u) [CommRing k] :
    AffinePlane k ⟶ AffineLine k :=
  FiberProductContext.q (affinePlaneContext k)

def IsNonconstantOn {α β : Type*} (g : α → β) (C : Set α) : Prop :=
  ∃ x ∈ C, ∃ y ∈ C, g x ≠ g y

structure AffinePlaneCurve (k : Type u) [CommRing k] where
  carrier : Set (AffinePlane k)
  nonempty : carrier.Nonempty
  isClosed : IsClosed carrier
  isIrreducible : IsIrreducible carrier
  dimension_one : topologicalKrullDim carrier = 1
  firstProjection_nonconstant :
    IsNonconstantOn
      ((affinePlaneProjection₁ k : AffinePlane k ⟶ AffineLine k) :
        AffinePlane k → AffineLine k) carrier
  secondProjection_nonconstant :
    IsNonconstantOn
      ((affinePlaneProjection₂ k : AffinePlane k ⟶ AffineLine k) :
        AffinePlane k → AffineLine k) carrier

def curveComplement {k : Type u} [CommRing k] (C : AffinePlaneCurve k) :
    (AffinePlane k).Opens :=
  ⟨C.carrierᶜ, C.isClosed.isOpen_compl⟩

theorem affinePlane_projection_images_are_open
    {k : Type u} [Field k] [IsAlgClosed k]
    (U : (AffinePlane k).Opens) (hU : (U : Set (AffinePlane k)).Nonempty) :
    IsOpen ((affinePlaneProjection₁ k) '' (U : Set (AffinePlane k))) ∧
      IsOpen ((affinePlaneProjection₂ k) '' (U : Set (AffinePlane k))) := by
  sorry

/-!
For the open complement of a curve, the source of the comparison is modeled
by the tensor product of the section rings over the two projection images.
The section formula below is a definitional normalization of that model; the
geometric assertion that it is not the full structure-sheaf section is the
theorem interface following it.
-/
abbrev schemeSections (X : Scheme.{u}) (U : X.Opens) : Type u :=
  (X.presheaf.obj (.op U)).1

noncomputable def affinePlaneProjectionImage₁
    {k : Type u} [Field k] [IsAlgClosed k]
    (U : (AffinePlane k).Opens) (hU : (U : Set (AffinePlane k)).Nonempty) :
    (AffineLine k).Opens :=
  ⟨(affinePlaneProjection₁ k) '' (U : Set (AffinePlane k)),
    (affinePlane_projection_images_are_open U hU).1⟩

noncomputable def affinePlaneProjectionImage₂
    {k : Type u} [Field k] [IsAlgClosed k]
    (U : (AffinePlane k).Opens) (hU : (U : Set (AffinePlane k)).Nonempty) :
    (AffineLine k).Opens :=
  ⟨(affinePlaneProjection₂ k) '' (U : Set (AffinePlane k)),
    (affinePlane_projection_images_are_open U hU).2⟩

def affinePlaneSourceSectionModel
    (k : Type u) [Field k] (pU qU : (AffineLine k).Opens)
    [Algebra k (schemeSections (AffineLine k) pU)]
    [Algebra k (schemeSections (AffineLine k) qU)] : Type u :=
  schemeSections (AffineLine k) pU ⊗[k] schemeSections (AffineLine k) qU

def affinePlaneSourceSectionModelOn
    {k : Type u} [Field k] [IsAlgClosed k]
    (U : (AffinePlane k).Opens) (hU : (U : Set (AffinePlane k)).Nonempty)
    [Algebra k
      (schemeSections (AffineLine k) (affinePlaneProjectionImage₁ U hU))]
    [Algebra k
      (schemeSections (AffineLine k) (affinePlaneProjectionImage₂ U hU))] : Type u :=
  affinePlaneSourceSectionModel k (affinePlaneProjectionImage₁ U hU)
    (affinePlaneProjectionImage₂ U hU)

theorem affinePlane_source_sections_formula_on
    {k : Type u} [Field k] [IsAlgClosed k]
    (U : (AffinePlane k).Opens) (hU : (U : Set (AffinePlane k)).Nonempty)
    [Algebra k
      (schemeSections (AffineLine k) (affinePlaneProjectionImage₁ U hU))]
    [Algebra k
      (schemeSections (AffineLine k) (affinePlaneProjectionImage₂ U hU))] :
    affinePlaneSourceSectionModelOn U hU =
      schemeSections (AffineLine k) (affinePlaneProjectionImage₁ U hU) ⊗[k]
        schemeSections (AffineLine k) (affinePlaneProjectionImage₂ U hU) := by
  rfl

theorem affinePlane_source_sections_formula
    {k : Type u} [Field k]
    (pU qU : (AffineLine k).Opens)
    [Algebra k (schemeSections (AffineLine k) pU)]
    [Algebra k (schemeSections (AffineLine k) qU)] :
    affinePlaneSourceSectionModel k pU qU =
      schemeSections (AffineLine k) pU ⊗[k] schemeSections (AffineLine k) qU := by
  rfl

theorem affinePlane_curve_complement_comparison_not_isomorphic
    {k : Type u} [Field k] [IsAlgClosed k] (C : AffinePlaneCurve k) :
    ∃ D : RingSheafSpan (AffinePlane k),
      D.base =
          inverseImageStructureSheaf
            (FiberProductContext.f (affinePlaneContext k)) ∧
        D.left =
          inverseImageStructureSheaf
            (FiberProductContext.p (affinePlaneContext k)) ∧
        D.right =
          inverseImageStructureSheaf
            (FiberProductContext.q (affinePlaneContext k)) ∧
        D.target = (AffinePlane k).sheaf ∧
        ¬ IsIso ((sheafTensorToTarget D).1.app (.op (curveComplement C))) := by
  sorry

/-! ## Pullback of modules -/

noncomputable def presheafModuleTensor
    {X : Scheme.{u}} (F G : X.Modules) :
    PresheafOfModules (X.ringCatSheaf.obj) :=
  PresheafOfModules.Monoidal.tensorObj F.val G.val

noncomputable def moduleTensor
    {X : Scheme.{u}} (F G : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (R₀ := X.ringCatSheaf.obj)
    (𝟙 X.ringCatSheaf.obj)).obj (presheafModuleTensor F G)

abbrev pullbackModule {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules) : X.Modules :=
  (Scheme.Modules.pullback g).obj M

abbrev fiberProductPullbackModules
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)
    (F : X.Modules) (G : Y.Modules) :
    (FiberProductContext.product C).Modules × (FiberProductContext.product C).Modules :=
  (pullbackModule (FiberProductContext.p C) F, pullbackModule (FiberProductContext.q C) G)

abbrev fiberProductModuleTarget
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)
    (F : X.Modules) (G : Y.Modules) : (FiberProductContext.product C).Modules :=
  moduleTensor (pullbackModule (FiberProductContext.p C) F)
    (pullbackModule (FiberProductContext.q C) G)

/-!
The source displays the canonical comparison through the inverse-image
modules, the structure sheaf of the fibre product, and finally the two module
pullbacks. The module category already supplies the objects at the two ends;
the comparison morphism is kept as a theorem interface because Mathlib does
not define a tensor product of arbitrary sheaves of modules in this API.
-/
structure ModuleComparison
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)
    (F : X.Modules) (G : Y.Modules) where
  source : (FiberProductContext.product C).Modules
  comparison : source ⟶ fiberProductModuleTarget C F G

theorem fiberProduct_module_comparison_interface
    {X Y S : Scheme.{u}} (C : FiberProductContext X Y S)
    (F : X.Modules) (G : Y.Modules) :
    Nonempty (ModuleComparison C F G) := by
  sorry

theorem fiberProduct_module_comparison_not_generally_isomorphic :
    ∃ (X Y S : Scheme.{u}) (C : FiberProductContext X Y S)
      (F : X.Modules) (G : Y.Modules) (P : ModuleComparison C F G),
      ¬ IsIso P.comparison := by
  sorry

end Formalization.«Books.Examples».Unit05
