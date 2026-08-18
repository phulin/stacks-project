import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
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
  carrier : Sheaf J AddCommGrpCat.{u}
  inclusion : carrier ⟶ underlyingAdditiveSheaf O
  inclusion_mono : Mono inclusion
  sectionValue : ∀ (U : C), carrier.obj.obj (op U) → O.obj.obj (op U)
  sectionValue_inclusion : ∀ (U : C) (s : carrier.obj.obj (op U)),
    sectionValue U s = inclusion.hom.app (op U) s
  isIdeal : ∀ (U : C) (r : O.obj.obj (op U)) (s : carrier.obj.obj (op U)),
    ∃ t : carrier.obj.obj (op U), sectionValue U t = r * sectionValue U s

namespace SheafIdeal

/-- The ideal acts trivially on a sheaf of modules when every local section of
the ideal acts by zero. -/
def Annihilates {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {O : Sheaf J RingCat.{u}}
    (I : SheafIdeal O) (F : SheafOfModules.{u} O) : Prop :=
  ∀ (U : C) (s : I.carrier.obj.obj (op U)) (x : F.val.obj (op U)),
    I.sectionValue U s • x = 0

/-- A sheaf ideal can be regarded as a module over another sheaf of rings on
the same topos. -/
def IsModuleOver {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {O R : Sheaf J RingCat.{u}}
    (I : SheafIdeal O) : Prop :=
  ∃ F : SheafOfModules.{u} R,
    Nonempty (I.carrier ≅ (SheafOfModules.toSheaf R).obj F)

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
  ∀ (U : C) (s : I.carrier.obj.obj (op U)),
    ∃ (S : Sieve U), S ∈ J U ∧
      ∀ {V : C} (f : V ⟶ U), S f →
        ∃ n : ℕ,
          I.sectionValue V (I.carrier.obj.map f.op s) ^ n = 0

end SheafIdeal

/-! ## Ringed-topos morphisms -/

/-- A morphism of ringed topoi, with its inverse/direct image adjunction and
map on structure sheaves. -/
structure RingedToposHom {C D : Type u} [Category.{u} C] [Category.{u} D]
    (X : RingedTopos C) (Y : RingedTopos D) where
  inverseImage : Sheaves Y ⥤ Sheaves X
  directImage : Sheaves X ⥤ Sheaves Y
  inverse_direct_adjunction : inverseImage ⊣ directImage
  inverseImageRing : RingSheaves Y ⥤ RingSheaves X
  sharp : (inverseImageRing.obj Y.structureSheaf) ⟶ X.structureSheaf
  /-- The sheaf of ideals which is the kernel of `sharp`, retained as the
  source-facing ideal object. -/
  kernel : SheafIdeal (inverseImageRing.obj Y.structureSheaf)
  kernel_is_kernel : ∀ (U : C)
      (s : (inverseImageRing.obj Y.structureSheaf).obj.obj (op U)),
    sharp.hom.app (op U) s = 0 ↔
      ∃ t : kernel.carrier.obj.obj (op U), kernel.sectionValue U t = s

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
    underlyingAdditiveSheaf (i.hom.inverseImageRing.obj Y.structureSheaf) ⟶
      underlyingAdditiveSheaf X.structureSheaf :=
  (sheafCompose X.topology (forget₂ RingCat AddCommGrpCat)).map i.hom.sharp

/-- The displayed sequence `0 → I → O' → O → 0`, expressed as a short exact
sequence in the category of additive sheaves. -/
def HasShortExactSequence
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) : Prop :=
  ∃ hzero : i.hom.kernel.inclusion ≫ underlyingSharp i = 0,
    (ShortComplex.mk i.hom.kernel.inclusion (underlyingSharp i) hzero).ShortExact

theorem shortExactSequence
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) : HasShortExactSequence i := by
  sorry

/-- A thickening is first order when the square of its kernel ideal is zero. -/
def FirstOrderThickening {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) : Prop :=
  ∀ (U : C) (s t : i.hom.kernel.carrier.obj.obj (op U)),
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
    SheafIdeal.IsModuleOver (R := X.structureSheaf) i.hom.kernel := by
  sorry

/-! ## Morphisms of thickenings -/

/-- A morphism between two sheaf ideals over the same ambient sheaf of rings. -/
structure SheafIdealMap {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {O : Sheaf J RingCat.{u}}
    (I K : SheafIdeal O) where
  map : I.carrier ⟶ K.carrier
  map_sectionValue : ∀ (U : C) (s : I.carrier.obj.obj (op U)),
    K.sectionValue U (map.hom.app (op U) s) = I.sectionValue U s

/-- The data in the commutative diagram defining a morphism of thickenings.

The two pullback-kernel objects model `f^{-1} J` and `(f')^* J` after the
underlying topoi have been identified.  The square is recorded by the
underlying inverse-image equality, a natural isomorphism on ring sheaves,
and the corresponding compatibility of the two sharp maps. -/
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
  sharp_compatibility :
    i.hom.inverseImageRing.map f'.sharp ≫ i.hom.sharp =
      ring_inverse_iso.hom.app B'.structureSheaf ≫
        (f.inverseImageRing.map t.hom.sharp ≫ f.sharp)
  inverseImageKernel : SheafIdeal (i.hom.inverseImageRing.obj Y.structureSheaf)
  pullbackKernel : SheafIdeal (i.hom.inverseImageRing.obj Y.structureSheaf)
  inverseImageKernelMap :
    SheafIdealMap inverseImageKernel i.hom.kernel
  pullbackKernelMap :
    SheafIdealMap pullbackKernel i.hom.kernel

/-- The strictness condition for a morphism of thickenings. -/
def MorphismOfThickenings.IsStrict
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t) : Prop :=
  Sheaf.IsLocallySurjective m.pullbackKernelMap.map

/-- The kernel ideals of the horizontal thickenings in the displayed square. -/
abbrev MorphismOfThickenings.sourceKernel
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (_m : MorphismOfThickenings i t) :
    SheafIdeal (i.hom.inverseImageRing.obj Y.structureSheaf) :=
  i.hom.kernel

abbrev MorphismOfThickenings.baseKernel
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (_m : MorphismOfThickenings i t) :
    SheafIdeal (t.hom.inverseImageRing.obj B'.structureSheaf) :=
  t.hom.kernel

/-- For first order horizontal thickenings the two pullback descriptions of
the base kernel agree.  The canonical equality of module sheaves is exposed
as an isomorphism, which is the usable categorical form of the source's
notation `((f')^* J) = (f^* J)`. -/
theorem pullbackKernel_iso_inverseImageKernel_of_firstOrder
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t)
    (_hi : FirstOrderThickening i) (_ht : FirstOrderThickening t) :
    Nonempty (m.pullbackKernel.carrier ≅ m.inverseImageKernel.carrier) := by
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
    Nonempty (SheafIdealMap m.inverseImageKernel i.hom.kernel) :=
  ⟨m.inverseImageKernelMap⟩

theorem pullbackKernel_map_exists
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t) :
    Nonempty (SheafIdealMap m.pullbackKernel i.hom.kernel) :=
  ⟨m.pullbackKernelMap⟩

end

end Formalization.Books.Defos.Unit09
