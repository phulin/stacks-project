import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Deformation Theory, Chapter 9: Thickenings of ringed topoi

This file records the definitions from `books/defos.tex:2451-2540`.  A
ringed topos is represented by a site together with its category-valued sheaf
of rings.  The inverse and direct image functors of a morphism are retained
explicitly, as is the map on structure sheaves.  Ideals are represented by
sheaves of modules embedded in the unit module of the structure sheaf, with
their local sections exposed as sections of the ambient ring sheaf.
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

/-- The underlying sheaf-of-types functor on sheaves of rings. -/
noncomputable def underlyingRingSheafFunctor
    {C : Type u} [Category.{u} C] (X : RingedTopos C) :
    RingSheaves X ⥤ Sheaves X :=
  sheafCompose X.topology
    (forget₂ RingCat AddCommGrpCat ⋙ (forget AddCommGrpCat))

/-! ## Sheaves of ideals and nilpotence -/

/-- A sheaf of ideals in a sheaf of rings.

The carrier is an `O`-module and the inclusion is a morphism of sheaves of
`O`-modules into the unit module.  `sectionValue` exposes its local sections
as sections of the ambient ring sheaf. -/
structure SheafIdeal {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} (O : Sheaf J RingCat.{u}) where
  carrier : SheafOfModules.{u} O
  inclusion : (SheafOfModules.toSheaf O).obj carrier ⟶ underlyingAdditiveSheaf O
  inclusion_mono : Mono inclusion
  moduleInclusion : carrier ⟶ SheafOfModules.unit O
  moduleInclusion_mono : Mono moduleInclusion
  moduleInclusion_underlying :
    (SheafOfModules.toSheaf O).map moduleInclusion = inclusion
  sectionValue : ∀ (U : C), carrier.val.obj (op U) → O.obj.obj (op U)
  sectionValue_inclusion : ∀ (U : C) (s : carrier.val.obj (op U)),
    sectionValue U s = inclusion.hom.app (op U) s

namespace SheafIdeal

/-- The ideal acts trivially on a sheaf of modules when every local section of
the ideal acts by zero. -/
def Annihilates {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {O : Sheaf J RingCat.{u}}
    (I : SheafIdeal O) (F : SheafOfModules.{u} O) : Prop :=
  ∀ (U : C) (s : I.carrier.val.obj (op U)) (x : F.val.obj (op U)),
    I.sectionValue U s • x = 0

/-- An ideal admits a module realization through a specified pushforward
functor.

The source identifies the kernel ideal with the pushforward of a module on
the smaller ringed topos.  An additive-sheaf isomorphism alone would lose the
module structure and would not express that identification, so the
realization functor is part of this interface. -/
def IsModuleOver {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {O : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (I : SheafIdeal O)
    (realization : SheafOfModules.{u} R ⥤ SheafOfModules.{u} O) : Prop :=
  ∃ F : SheafOfModules.{u} R,
    Nonempty (realization.obj F ≅ I.carrier)

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
  inverseImageRing_underlying :
    inverseImageRing ⋙ underlyingRingSheafFunctor X ≅
      underlyingRingSheafFunctor Y ⋙ inverseImage
  directImageRing_underlying :
    directImageRing ⋙ underlyingRingSheafFunctor Y ≅
      underlyingRingSheafFunctor X ⋙ directImage
  /-- Pullback of modules along this morphism of ringed topoi.  This is
  explicit because the generic site API does not construct it from the
  inverse-image functor on sheaves of rings. -/
  modulePullback :
    SheafOfModules.{u} Y.structureSheaf ⥤ SheafOfModules.{u} X.structureSheaf
  /-- Direct image of modules along this morphism of ringed topoi. -/
  moduleDirectImage :
    SheafOfModules.{u} X.structureSheaf ⥤ SheafOfModules.{u} Y.structureSheaf
  modulePullback_moduleDirectImage : modulePullback ⊣ moduleDirectImage
  /-- Inverse image of ideals.  This is the ideal-level interface needed for
  the map `f'^{-1} J → I`; it is not supplied by the generic sheaf API. -/
  inverseImageIdeal :
    SheafIdeal Y.structureSheaf →
      SheafIdeal (inverseImageRing.obj Y.structureSheaf)
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
  /-- The structure-sheaf map viewed as a morphism of `Y.structureSheaf`-
  modules.  The target is the direct-image structure sheaf with scalars
  restricted along `sharp`. -/
  moduleSharp :
    SheafOfModules.unit Y.structureSheaf ⟶
      (SheafOfModules.restrictScalars sharp).obj
        (SheafOfModules.unit (directImageRing.obj X.structureSheaf))
  moduleSharp_underlying :
    (SheafOfModules.toSheaf Y.structureSheaf).map moduleSharp =
      (sheafCompose Y.topology (forget₂ RingCat AddCommGrpCat)).map sharp
  /-- The direct image of the unit module is the unit module with scalars
  restricted along the structure-sheaf map. -/
  moduleDirectImage_unit_iso :
    moduleDirectImage.obj (SheafOfModules.unit X.structureSheaf) ≅
      (SheafOfModules.restrictScalars sharp).obj
        (SheafOfModules.unit (directImageRing.obj X.structureSheaf))
  /-- The inclusion of the kernel ideal has zero composite with `sharp`. -/
  kernel_condition :
    kernel.inclusion ≫
        (sheafCompose Y.topology (forget₂ RingCat AddCommGrpCat)).map sharp = 0
  /-- The same zero-composite condition in the category of modules. -/
  module_kernel_condition :
    kernel.moduleInclusion ≫ moduleSharp = 0
  /-- The kernel ideal satisfies the categorical kernel universal property. -/
  kernel_is_kernel :
    IsLimit (KernelFork.ofι kernel.inclusion kernel_condition)
  /-- The kernel ideal also satisfies the kernel universal property before
  forgetting the `Y.structureSheaf`-module structure. -/
  module_kernel_is_kernel :
    IsLimit (KernelFork.ofι kernel.moduleInclusion module_kernel_condition)

noncomputable def RingedToposHom.moduleDirectImage_unit_map
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D} (f : RingedToposHom X Y) :
    SheafOfModules.unit Y.structureSheaf ⟶
      f.moduleDirectImage.obj (SheafOfModules.unit X.structureSheaf) :=
  f.moduleSharp ≫ f.moduleDirectImage_unit_iso.inv

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
   existential side condition; it is supplied by the kernel interface. -/
noncomputable def thickeningKernelModuleShortComplex
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) :
  ShortComplex (SheafOfModules.{u} Y.structureSheaf) :=
  ShortComplex.mk i.hom.kernel.moduleInclusion i.hom.moduleSharp
    i.hom.module_kernel_condition

/-- The sequence in the source is a short exact sequence of modules over the
structure sheaf of the thickened topos. -/
abbrev HasShortExactSequence
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) : Prop :=
  (thickeningKernelModuleShortComplex i).ShortExact

/- The underlying additive sequence is retained because it is useful for
   transferring local surjectivity from sheaves of rings. -/
noncomputable def thickeningKernelShortComplex
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) :
  ShortComplex (Sheaf Y.topology AddCommGrpCat.{u}) :=
  ShortComplex.mk i.hom.kernel.inclusion (underlyingSharp i)
    i.hom.kernel_condition

/-- The displayed sequence `0 → I → O' → O → 0`, expressed as the exact
sequence of underlying additive sheaves.  The ideal inclusion is retained as
a sheaf-module morphism in the kernel interface. -/
abbrev HasUnderlyingShortExactSequence
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) : Prop :=
  (thickeningKernelShortComplex i).ShortExact

theorem underlyingShortExactSequence
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) [HasSheafify Y.topology AddCommGrpCat.{u}] :
    (thickeningKernelShortComplex i).ShortExact := by
  let hLocal : Sheaf.IsLocallySurjective (underlyingSharp i) := by
    change Presheaf.IsLocallySurjective Y.topology (underlyingSharp i).hom
    rw [Presheaf.isLocallySurjective_iff_whisker_forget]
    refine ⟨?_⟩
    intro U s
    have h := i.sharp_is_locally_surjective.imageSieve_mem (U := U) s
    change Presheaf.imageSieve (underlyingSharp i).hom s ∈ Y.topology U
    convert h using 1
    ext V f
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, ht⟩
  apply ShortComplex.ShortExact.mk'
  · apply ShortComplex.exact_of_f_is_kernel
    exact i.hom.kernel_is_kernel
  · exact i.hom.kernel.inclusion_mono
  · exact @Sheaf.epi_of_isLocallySurjective _ _ _ _ _ _ _ _ _ _ _
      (underlyingSharp i) _ hLocal

theorem shortExactSequence
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) [HasSheafify Y.topology AddCommGrpCat.{u}] :
    (thickeningKernelModuleShortComplex i).ShortExact := by
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

/-- For a first order thickening the kernel ideal is the pushforward of a
module on the smaller ringed topos. -/
theorem kernel_is_module_over
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (i : Thickening X Y) (hi : FirstOrderThickening i) :
    SheafIdeal.IsModuleOver (O := Y.structureSheaf) (R := X.structureSheaf)
      i.hom.kernel i.hom.moduleDirectImage := by
  sorry

/-! ## Morphisms of thickenings -/

/-- A morphism of ideals along a morphism of ambient sheaves of rings. -/
structure SheafIdealMap {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {O P : Sheaf J RingCat.{u}}
    (α : O ⟶ P) (I : SheafIdeal O) (K : SheafIdeal P) where
  map : (SheafOfModules.toSheaf O).obj I.carrier ⟶
    (SheafOfModules.toSheaf P).obj K.carrier
  map_smul : ∀ (U : C) (r : O.obj.obj (op U))
    (s : I.carrier.val.obj (op U)),
    map.hom.app (op U) (r • s) =
      α.hom.app (op U) r •
        (show K.carrier.val.obj (op U) from map.hom.app (op U) s)
  map_sectionValue : ∀ (U : C) (s : I.carrier.val.obj (op U)),
    K.sectionValue U (map.hom.app (op U) s) =
      α.hom.app (op U) (I.sectionValue U s)

/-- The data in the commutative diagram defining a morphism of thickenings.

  The first ideal and its map model `f'^{-1} J → I`; the module object and
  its map model `(f')^* J → I`.  The second module object is the corresponding
  realization of `f^* J` after the source's identification of the underlying
  topoi. -/
structure MorphismOfThickenings
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    (i : Thickening X Y) (t : Thickening B B') where
  f : RingedToposHom X B
  f' : RingedToposHom Y B'
  underlying_commutes :
    f'.inverseImage ⋙ i.hom.inverseImage ≅
      t.hom.inverseImage ⋙ f.inverseImage
  ring_inverse_iso :
    f'.inverseImageRing ⋙ i.hom.inverseImageRing ≅
      t.hom.inverseImageRing ⋙ f.inverseImageRing
  direct_ring_iso :
    i.hom.directImageRing ⋙ f'.directImageRing ≅
      f.directImageRing ⋙ t.hom.directImageRing
  /-- Coherence of direct image on modules for the commutative square. -/
  module_direct_iso :
    i.hom.moduleDirectImage ⋙ f'.moduleDirectImage ≅
      f.moduleDirectImage ⋙ t.hom.moduleDirectImage
  /-- Compatibility of the module structure-sheaf maps with the direct-image
  coherence above. -/
  module_unit_compatibility :
    f'.moduleDirectImage_unit_map ≫
        f'.moduleDirectImage.map i.hom.moduleDirectImage_unit_map ≫
          module_direct_iso.hom.app (SheafOfModules.unit X.structureSheaf) =
      t.hom.moduleDirectImage_unit_map ≫
        t.hom.moduleDirectImage.map f.moduleDirectImage_unit_map
  /-- Coherence of pullback on modules for the commutative square. -/
  module_pullback_iso :
    f'.modulePullback ⋙ i.hom.modulePullback ≅
      t.hom.modulePullback ⋙ f.modulePullback
  sharp_compatibility :
    f'.sharp ≫ f'.directImageRing.map i.hom.sharp ≫
        direct_ring_iso.hom.app X.structureSheaf =
      t.hom.sharp ≫ t.hom.directImageRing.map f.sharp

/-! The inverse-image ideal and the two module sheaves in the source's
notation are now determined by the corresponding interfaces on the vertical
maps. -/

abbrev MorphismOfThickenings.inverseImageKernel
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t) :
    SheafIdeal (m.f'.inverseImageRing.obj B'.structureSheaf) :=
  m.f'.inverseImageIdeal t.hom.kernel

abbrev MorphismOfThickenings.pullbackKernel
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t) : SheafOfModules.{u} Y.structureSheaf :=
  m.f'.modulePullback.obj t.hom.kernel.carrier

abbrev MorphismOfThickenings.basePullbackKernel
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t)
    (J : SheafOfModules.{u} B.structureSheaf) :
    SheafOfModules.{u} Y.structureSheaf :=
  i.hom.moduleDirectImage.obj (m.f.modulePullback.obj J)

/-- The inverse-image kernel map supplied by the commutative square. -/
theorem inverseImageKernel_map_exists
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t) :
    Nonempty
      (SheafIdealMap m.f'.inverseImageSharp
        m.inverseImageKernel i.hom.kernel) := by
  sorry

/-- A chosen representative of the inverse-image kernel map. -/
noncomputable def MorphismOfThickenings.inverseImageKernelMap
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t) :
    SheafIdealMap m.f'.inverseImageSharp
      m.inverseImageKernel i.hom.kernel :=
  Classical.choice (inverseImageKernel_map_exists m)

/- The module map before transposing along the pullback/direct-image
   adjunction.  The factorization equation records that this is the map
   induced by the commutative square, rather than an arbitrary morphism
   (in particular, not merely the zero morphism). -/
theorem pullbackKernel_factorization_exists
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t) :
    ∃ φ : t.hom.kernel.carrier ⟶
        m.f'.moduleDirectImage.obj i.hom.kernel.carrier,
      φ ≫ m.f'.moduleDirectImage.map i.hom.kernel.moduleInclusion =
        t.hom.kernel.moduleInclusion ≫
          m.f'.moduleDirectImage_unit_map := by
  sorry

noncomputable def MorphismOfThickenings.pullbackKernelFactorization
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t) :
    t.hom.kernel.carrier ⟶
      m.f'.moduleDirectImage.obj i.hom.kernel.carrier :=
  Classical.choose (pullbackKernel_factorization_exists m)

theorem MorphismOfThickenings.pullbackKernelFactorization_fac
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t) :
    m.pullbackKernelFactorization ≫
        m.f'.moduleDirectImage.map i.hom.kernel.moduleInclusion =
      t.hom.kernel.moduleInclusion ≫
        m.f'.moduleDirectImage_unit_map :=
  Classical.choose_spec (pullbackKernel_factorization_exists m)

/- The pullback kernel map is the transpose of the factorization above. -/
noncomputable def MorphismOfThickenings.pullbackKernelMap
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t) :
    m.pullbackKernel ⟶ i.hom.kernel.carrier :=
  (m.f'.modulePullback_moduleDirectImage.homEquiv
      t.hom.kernel.carrier i.hom.kernel.carrier).symm
    m.pullbackKernelFactorization

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

/-- In the first-order case the source's equality of the two pullback
descriptions is used through the induced equivalence on maps into the source
kernel.  A literal object isomorphism would be too strong: the two displayed
module objects need not be isomorphic before applying the first-order
identification. -/
theorem pullbackKernel_homEquiv_basePullbackKernel_of_firstOrder
    {C D E F : Type u} [Category.{u} C] [Category.{u} D]
    [Category.{u} E] [Category.{u} F]
    {X : RingedTopos C} {Y : RingedTopos D}
    {B : RingedTopos E} {B' : RingedTopos F}
    {i : Thickening X Y} {t : Thickening B B'}
    (m : MorphismOfThickenings i t)
    (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
    (J : SheafOfModules.{u} B.structureSheaf)
    (hJ : Nonempty
      (t.hom.moduleDirectImage.obj J ≅ t.hom.kernel.carrier)) :
    Nonempty
      ((m.pullbackKernel ⟶ i.hom.kernel.carrier) ≃
        (m.basePullbackKernel J ⟶ i.hom.kernel.carrier)) := by
  sorry

end

end Formalization.Books.Defos.Unit09
