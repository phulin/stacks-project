import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Deformation Theory, Chapter 9: Thickenings of ringed topoi

This file records the definitions from `books/defos.tex:2451-2540`.  A
ringed topos is represented by a site together with its category-valued sheaf
of rings.  The inverse and direct image functors of a morphism are retained
explicitly, as is the map on structure sheaves.  Ideals are represented by
additive sheaves embedded in the underlying additive sheaf of the structure
sheaf, with their local multiplicative closure made explicit.
-/

namespace Formalization.Books.Defos.Unit09

open CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

/-! ## Ringed topoi -/

/-- A ringed topos presented by a site and a sheaf of rings on that site. -/
structure RingedTopos (C : Type u) [Category.{u} C] where
  topology : GrothendieckTopology C
  structureSheaf : Sheaf topology RingCat.{u}

/-- The category of sheaves of sets on the site underlying a ringed topos. -/
abbrev Sheaves {C : Type u} [Category.{u} C] (X : RingedTopos C) :=
  Sheaf X.topology (Type u)

/-- The category of sheaves of rings on the site underlying a ringed topos. -/
abbrev RingSheaves {C : Type u} [Category.{u} C] (X : RingedTopos C) :=
  Sheaf X.topology RingCat.{u}

/-- The underlying additive sheaf of a sheaf of rings. -/
noncomputable abbrev underlyingAdditiveSheaf
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{u}) : Sheaf J AddCommGrpCat.{u} :=
  (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj O

/-! ## Sheaves of ideals and nilpotence -/

/-- A sheaf of ideals in a sheaf of rings.

The carrier is an additive sheaf, and `sectionValue` identifies its local
sections with sections of the ambient ring sheaf.  The closure field is the
usual condition that multiplication by a local ambient section stays in the
ideal. -/
structure SheafIdeal {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} (O : Sheaf J RingCat.{u}) where
  carrier : SheafOfModules.{u} O
  inclusion : (SheafOfModules.toSheaf O).obj carrier ⟶ underlyingAdditiveSheaf O
  inclusion_mono : Mono inclusion
  sectionValue : ∀ (U : C), carrier.val.obj (op U) → O.obj.obj (op U)
  sectionValue_inclusion : ∀ (U : C) (s : carrier.val.obj (op U)),
    sectionValue U s = inclusion.hom.app (op U) s
  isIdeal : ∀ (U : C) (r : O.obj.obj (op U)) (s : carrier.val.obj (op U)),
    ∃ t : carrier.val.obj (op U),
      sectionValue U t = r * sectionValue U s

namespace SheafIdeal

/-- The ideal acts trivially on a sheaf of modules when every local section of
the ideal acts by zero. -/
def Annihilates {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {O : Sheaf J RingCat.{u}}
    (I : SheafIdeal O) (F : SheafOfModules.{u} O) : Prop :=
  ∀ (U : C) (s : I.carrier.val.obj (op U)) (x : F.val.obj (op U)),
    I.sectionValue U s • x = 0

/-- A sheaf ideal can be regarded as a module over another sheaf of rings on
the same topos. -/
def IsModuleOver {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {O R : Sheaf J RingCat.{u}}
    (I : SheafIdeal O) : Prop :=
  ∃ F : SheafOfModules.{u} R,
    Nonempty ((SheafOfModules.toSheaf O).obj I.carrier ≅
      (SheafOfModules.toSheaf R).obj F)

/-- The full subcategory of `O`-modules annihilated by an ideal `I`. -/
abbrev AnnihilatedModuleCategory {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {O : Sheaf J RingCat.{u}}
    (I : SheafIdeal O) :=
  ObjectProperty.FullSubcategory (Annihilates I)

/-- Every local section of the ideal becomes nilpotent after restriction to a
covering sieve. -/
def IsLocallyNilpotent {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {O : Sheaf J RingCat.{u}}
    (I : SheafIdeal O) : Prop :=
  ∀ (U : C) (s : I.carrier.val.obj (op U)),
    ∃ (S : Sieve U), S ∈ J U ∧
      ∀ {V : C} (f : V ⟶ U), S f →
        ∃ n : ℕ,
          I.sectionValue V (I.carrier.val.map f.op s) ^ n = 0

end SheafIdeal

/-! ## Ringed-topos morphisms -/

/-- A morphism of ringed topoi, with its inverse/direct image adjunction and
map on structure sheaves. -/
structure RingedToposHom {C D : Type u} [Category.{u} C] [Category.{u} D]
    (X : RingedTopos C) (Y : RingedTopos D) where
  inverseImage : Sheaves Y ⥤ Sheaves X
  inverseImage_preservesFiniteLimits : PreservesFiniteLimits inverseImage
  directImage : Sheaves X ⥤ Sheaves Y
  inverse_direct_adjunction : inverseImage ⊣ directImage
  inverseImageRing : RingSheaves Y ⥤ RingSheaves X
  directImageRing : RingSheaves X ⥤ RingSheaves Y
  inverse_direct_ring_adjunction : inverseImageRing ⊣ directImageRing
  /-- The structure-sheaf map in the source-facing direction
  `O_Y ⟶ i_* O_X`. -/
  sharp : Y.structureSheaf ⟶ directImageRing.obj X.structureSheaf
  /-- The equivalent inverse-image form of `sharp`, used for pullbacks. -/
  inverseImageSharp : (inverseImageRing.obj Y.structureSheaf) ⟶ X.structureSheaf
  inverseImageSharp_is_adjunct :
    inverse_direct_ring_adjunction.homEquiv Y.structureSheaf X.structureSheaf
      inverseImageSharp = sharp
  /-- The sheaf of ideals which is the kernel of `sharp`, retained as the
  source-facing ideal object. -/
  kernel : SheafIdeal Y.structureSheaf
  kernel_is_kernel : ∀ (U : D)
      (s : Y.structureSheaf.obj.obj (op U)),
    sharp.hom.app (op U) s = 0 ↔
      ∃ t : kernel.carrier.val.obj (op U), kernel.sectionValue U t = s

/-! ## Thickenings -/

/-- A thickening of ringed topoi. -/
structure Thickening {C D : Type u} [Category.{u} C] [Category.{u} D]
    (X : RingedTopos C) (Y : RingedTopos D) where
  hom : RingedToposHom X Y
  directImage_isEquivalence : hom.directImage.IsEquivalence
  sharp_is_locally_surjective : Sheaf.IsLocallySurjective hom.sharp
  kernel_is_locally_nilpotent : hom.kernel.IsLocallyNilpotent

/-- The additive-sheaf map induced by the map on structure sheaves. -/
noncomputable abbrev underlyingSharp
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) :
    underlyingAdditiveSheaf Y.structureSheaf ⟶
      underlyingAdditiveSheaf (i.hom.directImageRing.obj X.structureSheaf) :=
  (sheafCompose Y.topology (forget₂ RingCat AddCommGrpCat)).map i.hom.sharp

/- The zero composite is part of the canonical sequence rather than an
   existential side condition.  Its proof uses the kernel interface and is
   intentionally left open at this statement-review stage. -/
noncomputable def thickeningKernelShortComplex
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) :
    ShortComplex (Sheaf Y.topology AddCommGrpCat.{u}) :=
  ShortComplex.mk i.hom.kernel.inclusion (underlyingSharp i) (by
    sorry)

/-- The displayed sequence `0 → I → O' → O → 0`, expressed as a short exact
sequence in the category of additive sheaves. -/
abbrev HasShortExactSequence
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) : Prop :=
  (thickeningKernelShortComplex i).ShortExact

theorem shortExactSequence
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) :
    (thickeningKernelShortComplex i).ShortExact := by
  sorry

/-- A thickening is first order when the square of its kernel ideal is zero. -/
def FirstOrderThickening {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) : Prop :=
  ∀ (U : D) (s t : i.hom.kernel.carrier.val.obj (op U)),
    i.hom.kernel.sectionValue U s * i.hom.kernel.sectionValue U t = 0

/-- The module-category equivalence for a thickening, as used in the source's
preliminary discussion. -/
theorem module_category_equivalence
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) :
    Nonempty
      (SheafOfModules.{u} X.structureSheaf ≌
        SheafIdeal.AnnihilatedModuleCategory i.hom.kernel) := by
  sorry

/-- For a first order thickening the kernel ideal is a module over the
structure sheaf of the smaller ringed topos. -/
theorem kernel_is_module_over
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) (hi : FirstOrderThickening i) :
    SheafIdeal.IsModuleOver
      (R := i.hom.directImageRing.obj X.structureSheaf) i.hom.kernel := by
  sorry

/-! ## Morphisms of thickenings -/

/-- A morphism of ideals along a morphism of ambient sheaves of rings. -/
structure SheafIdealMap {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {O P : Sheaf J RingCat.{u}}
    (α : O ⟶ P) (I : SheafIdeal O) (K : SheafIdeal P) where
  map : (SheafOfModules.toSheaf O).obj I.carrier ⟶
    (SheafOfModules.toSheaf P).obj K.carrier
  map_sectionValue : ∀ (U : C) (s : I.carrier.val.obj (op U)),
    K.sectionValue U (map.hom.app (op U) s) =
      α.hom.app (op U) (I.sectionValue U s)

/-- The data in the commutative diagram defining a morphism of thickenings.

The first kernel object models `f'^{-1} J`; its map to `I` is required to
lie over the induced map on ambient ring sheaves.  The two module objects
model `(f')^* J` and `f^* J` after the source's identification of the
underlying topoi. -/
structure MorphismOfThickenings
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    (i : Thickening X Y) (t : Thickening B B') where
  f : RingedToposHom X B
  f' : RingedToposHom Y B'
  underlying_commutes :
    f'.inverseImage ⋙ i.hom.inverseImage =
      t.hom.inverseImage ⋙ f.inverseImage
  ring_inverse_iso :
    f'.inverseImageRing ⋙ i.hom.inverseImageRing ≅
      t.hom.inverseImageRing ⋙ f.inverseImageRing
  direct_ring_iso :
    i.hom.directImageRing ⋙ f'.directImageRing ≅
      f.directImageRing ⋙ t.hom.directImageRing
  sharp_compatibility :
    f'.sharp ≫ f'.directImageRing.map i.hom.sharp ≫
        direct_ring_iso.hom.app X.structureSheaf =
      t.hom.sharp ≫ t.hom.directImageRing.map f.sharp
  inverseImageKernel : SheafIdeal (f'.inverseImageRing.obj B'.structureSheaf)
  inverseImageKernelMap :
    SheafIdealMap f'.inverseImageSharp
      inverseImageKernel i.hom.kernel
  pullbackKernel :
    SheafOfModules.{u} Y.structureSheaf
  basePullbackKernel :
    SheafOfModules.{u} Y.structureSheaf
  pullbackKernelMap :
    pullbackKernel ⟶ i.hom.kernel.carrier

/-- The strictness condition for a morphism of thickenings. -/
def MorphismOfThickenings.IsStrict
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t) : Prop :=
  Sheaf.IsLocallySurjective
    ((SheafOfModules.toSheaf Y.structureSheaf).map m.pullbackKernelMap)

/-- The kernel ideals of the horizontal thickenings in the displayed square. -/
abbrev MorphismOfThickenings.sourceKernel
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (_m : MorphismOfThickenings i t) :
    SheafIdeal Y.structureSheaf :=
  i.hom.kernel

abbrev MorphismOfThickenings.baseKernel
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (_m : MorphismOfThickenings i t) :
    SheafIdeal B'.structureSheaf :=
  t.hom.kernel

/-- For first order horizontal thickenings the two pullback descriptions of
the base kernel agree.  The canonical equality of module sheaves is exposed
as an isomorphism, which is the usable categorical form of the source's
notation `((f')^* J) = (f^* J)`. -/
theorem pullbackKernel_iso_basePullbackKernel_of_firstOrder
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t)
    (_hi : FirstOrderThickening i) (_ht : FirstOrderThickening t) :
    Nonempty
      ((SheafOfModules.toSheaf Y.structureSheaf).obj m.pullbackKernel ≅
        (SheafOfModules.toSheaf Y.structureSheaf).obj
          m.basePullbackKernel) := by
  sorry

/-! The inverse-image and tensor-pullback maps appearing in the source are
the two fields below; strictness is the local-surjectivity condition on the
second one. -/

theorem inverseImageKernel_map_exists
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t) :
    Nonempty
      (SheafIdealMap m.f'.inverseImageSharp
        m.inverseImageKernel i.hom.kernel) :=
  ⟨m.inverseImageKernelMap⟩

theorem pullbackKernel_map_exists
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t) :
    Nonempty
      (m.pullbackKernel ⟶ i.hom.kernel.carrier) :=
  ⟨m.pullbackKernelMap⟩

end

end Formalization.Books.Defos.Unit09
