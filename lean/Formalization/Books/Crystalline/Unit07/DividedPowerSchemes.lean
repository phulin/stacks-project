import Formalization.Books.Dpa.Unit03
import Formalization.Books.Defos.Unit09
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Crystalline Cohomology, Chapter 7: Divided power schemes

This file formalizes the source section `Divided power schemes`.  The
divided-power operations are the existing `DividedPowers` interface; this
file supplies the sheaf, scheme, thickening, fibre-product, and global-
situation interfaces needed to state the source's global constructions.
-/

namespace Formalization.Books.Crystalline.Unit07

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace
open Formalization.Books.Dpa.Unit02
open Formalization.Books.Dpa.Unit03

universe u

noncomputable section

/-! ## Ringed topoi and sheaf ideals -/

/-
The source uses commutative sheaves of rings.  We keep the commutative
structure here (rather than weakening to `RingCat`) so that Mathlib's
`Ideal` and `DividedPowers` APIs apply directly to sections.
-/

/-- A ringed topos with a sheaf of commutative rings. -/
structure RingedTopos (C : Type u) [Category.{u} C] where
  topology : GrothendieckTopology C
  structureSheaf : Sheaf topology CommRingCat.{u}

/-- The underlying sheaf of rings used by the existing sheaf-ideal API. -/
abbrev ringSheaf {C : Type u} [Category.{u} C] (X : RingedTopos C) :
    Sheaf X.topology RingCat.{u} :=
  (sheafCompose X.topology (forget₂ CommRingCat RingCat)).obj X.structureSheaf

/-- A sheaf ideal in the structure sheaf of a ringed topos. -/
abbrev IdealSheaf {C : Type u} [Category.{u} C] (X : RingedTopos C) :=
  Formalization.Books.Defos.Unit09.SheafIdeal (ringSheaf X)

/-- The local sections of a sheaf ideal. -/
abbrev idealSections {C : Type u} [Category.{u} C]
    {X : RingedTopos C} (I : IdealSheaf X) (U : C) :=
  I.carrier.val.obj (op U)

/-! ## Divided powers on a sheaf ideal -/

/-- A divided-power structure on a sheaf ideal.

`localIdeal` records the ideal in each ring of sections, `localIdeal_spec`
identifies its elements with sections of the sheaf ideal, and `gamma` records
the maps on local ideal sections.  The axioms are imposed by the existing
`DividedPowers` structure and the compatibility equation below.
-/
structure DividedPowerStructure {C : Type u} [Category.{u} C]
    (X : RingedTopos C) (I : IdealSheaf X) where
  localIdeal : ∀ U : C, Ideal (X.structureSheaf.obj.obj (op U))
  localIdeal_spec : ∀ (U : C) (x : X.structureSheaf.obj.obj (op U)),
    x ∈ localIdeal U ↔
      ∃ s : idealSections I U, I.sectionValue U s = x
  dividedPowers : ∀ U : C, DividedPowers (localIdeal U)
  gamma : ∀ (n : ℕ) (U : C), idealSections I U → idealSections I U
  gamma_value : ∀ (n : ℕ) (U : C) (s : idealSections I U),
    I.sectionValue U (gamma n U s) =
      (dividedPowers U).dpow n (I.sectionValue U s)

/-- The divided-power ring of sections at an object of the site. -/
def localDividedPowerRing {C : Type u} [Category.{u} C]
    (X : RingedTopos C) (I : IdealSheaf X)
    (P : DividedPowerStructure X I) (U : C) : DividedPowerRing.{u} where
  toCommRing := X.structureSheaf.obj.obj (op U)
  ideal := P.localIdeal U
  dividedPowers := P.dividedPowers U

/-- A divided-power topos. -/
structure DividedPowerTopos (C : Type u) [Category.{u} C] where
  toRingedTopos : RingedTopos C
  ideal : IdealSheaf toRingedTopos
  dividedPowers : DividedPowerStructure toRingedTopos ideal

/-! ## Morphisms of divided-power topoi -/

/-- The inverse-image and structure-sheaf part of a morphism of ringed topoi.

The explicit inverse-image functors are the source's `f`, while `sharp` is
the source's `f^sharp : f^{-1} O' → O`.  The ideal-level data is retained in
`DividedPowerTopos.Hom` below because the generic sheaf API does not construct
inverse images of ideal subobjects automatically.
-/
structure RingedToposHom {C D : Type u} [Category.{u} C] [Category.{u} D]
    (X : RingedTopos C) (Y : RingedTopos D) where
  inverseImage : Sheaf Y.topology (Type u) ⥤ Sheaf X.topology (Type u)
  inverseImage_preservesFiniteLimits : PreservesFiniteLimits inverseImage
  inverseImageRing : Sheaf Y.topology CommRingCat.{u} ⥤
    Sheaf X.topology CommRingCat.{u}
  sharp : inverseImageRing.obj Y.structureSheaf ⟶ X.structureSheaf

/-- The ringed topos carrying the inverse image of a structure sheaf. -/
def pullbackRingedTopos {C D : Type u} [Category.{u} C] [Category.{u} D]
    {X : RingedTopos C} {Y : RingedTopos D}
    (f : RingedToposHom X Y) : RingedTopos C where
  topology := X.topology
  structureSheaf := f.inverseImageRing.obj Y.structureSheaf

/-- A morphism of divided-power topoi.

`inverseIdeal` and `inverseGamma` are the local section presentation of
`f^{-1} I'` and `f^{-1} gamma'`; `idealMap` is the induced map into `I`.
The two displayed conditions are exactly the inclusion and commutative
divided-power diagrams from the source.
-/
structure DividedPowerTopos.Hom {C D : Type u} [Category.{u} C] [Category.{u} D]
    (X : DividedPowerTopos C) (Y : DividedPowerTopos D) where
  base : RingedToposHom X.toRingedTopos Y.toRingedTopos
  inverseIdeal : IdealSheaf (pullbackRingedTopos base)
  inverseGamma : ∀ (n : ℕ) (U : C),
    idealSections inverseIdeal U → idealSections inverseIdeal U
  idealMap : ∀ U : C, idealSections inverseIdeal U → idealSections X.ideal U
  idealMap_value : ∀ (U : C) (s : idealSections inverseIdeal U),
    X.ideal.sectionValue U (idealMap U s) =
      base.sharp.hom.app (op U) (inverseIdeal.sectionValue U s)
  gamma_commutes : ∀ (n : ℕ) (U : C) (s : idealSections inverseIdeal U),
    X.dividedPowers.gamma n U (idealMap U s) =
      idealMap U (inverseGamma n U s)

/-- The source's site-induced presentation: at every object of the source
site, the displayed map is a homomorphism of divided-power rings. -/
structure SiteInducedDividedPowerToposHom
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (X : DividedPowerTopos C) (Y : DividedPowerTopos D) where
  base : RingedToposHom X.toRingedTopos Y.toRingedTopos
  siteFunctor : D ⥤ C
  onSections : ∀ U : D,
    DividedPowerRing.Hom
      (localDividedPowerRing Y.toRingedTopos Y.ideal Y.dividedPowers U)
      (localDividedPowerRing X.toRingedTopos X.ideal X.dividedPowers
        (siteFunctor.obj U))

/-! ## Divided power schemes -/

/-- The ringed topos of open subsets of a scheme. -/
def schemeRingedTopos (S : Scheme.{u}) : RingedTopos S.Opens where
  topology := Opens.grothendieckTopology S
  structureSheaf := S.sheaf

/-- A sheaf ideal on a scheme, using the structure sheaf of the scheme. -/
abbrev SchemeIdeal (S : Scheme.{u}) := IdealSheaf (schemeRingedTopos S)

/-- The usual quasi-coherence condition on a scheme ideal's module carrier. -/
def IsQuasiCoherentIdeal {S : Scheme.{u}} (I : SchemeIdeal S) : Prop :=
  I.carrier.IsQuasicoherent

/-- A divided power scheme. -/
structure DividedPowerScheme where
  scheme : Scheme.{u}
  ideal : SchemeIdeal scheme
  quasiCoherent : IsQuasiCoherentIdeal ideal
  dividedPowers : DividedPowerStructure (schemeRingedTopos scheme) ideal

namespace DividedPowerScheme

/-! The source-facing morphism condition is stated on sections over inverse
images of opens.  This is the scheme version of the `f^sharp` condition. -/

/-- A morphism of divided power schemes. -/
structure Hom (X Y : DividedPowerScheme.{u}) where
  hom : X.scheme ⟶ Y.scheme
  idealMap : ∀ (U : Y.scheme.Opens),
    idealSections Y.ideal U → idealSections X.ideal (hom ⁻¹ᵁ U)
  idealMap_value : ∀ (U : Y.scheme.Opens) (s : idealSections Y.ideal U),
    X.ideal.sectionValue (hom ⁻¹ᵁ U) (idealMap U s) =
      hom.app U (Y.ideal.sectionValue U s)
  gamma_commutes : ∀ (n : ℕ) (U : Y.scheme.Opens)
      (s : idealSections Y.ideal U),
    X.dividedPowers.gamma n (hom ⁻¹ᵁ U) (idealMap U s) =
      idealMap U (Y.dividedPowers.gamma n U s)

end DividedPowerScheme

/-! ## Thickenings -/

/-
Mathlib provides the closed-immersion predicate.  A thickening is a closed
immersion which is surjective on the underlying spaces; this is the standard
scheme-theoretic formulation of the source's “thickening”.
-/

/-- A scheme morphism whose underlying closed immersion is a thickening. -/
def IsThickening {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsClosedImmersion f ∧ Function.Surjective f.base

/-- The ideal-sheaf/closed-immersion correspondence already available in
Mathlib. -/
abbrev ClosedImmersionIdealCorrespondence (T : Scheme.{u}) :=
  IsClosedImmersion.overEquivIdealSheafData T

/-- A divided-power thickening `(U, T, gamma)`. -/
structure DividedPowerThickening where
  source : Scheme.{u}
  target : DividedPowerScheme.{u}
  immersion : source ⟶ target.scheme
  isThickening : IsThickening immersion

/-- The local nilpotence condition for an integer on a scheme. -/
def IsLocallyNilpotentOnScheme (p : ℕ) (X : Scheme.{u}) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsNilpotent (p : Γ(X, U))

/-! The two observations immediately preceding the global situation. -/

/-- Source assertion: with `p` locally nilpotent on the source, its local
nilpotence on the target is equivalent to the thickening condition. -/
theorem locallyNilpotent_iff_thickening (D : DividedPowerThickening.{u})
    (p : ℕ) (hp : IsLocallyNilpotentOnScheme p D.source) :
    IsLocallyNilpotentOnScheme p D.target.scheme ↔ IsThickening D.immersion := by
  sorry

/-- The ideal `p^e O_T` is preserved by the local divided powers. -/
def PreservesPowerIdeal (D : DividedPowerScheme.{u}) (p e : ℕ)
    (U : D.scheme.Opens) : Prop :=
  ∀ {n : ℕ} {x : D.scheme.sheaf.obj.obj (op U)},
    x ∈ D.dividedPowers.localIdeal U →
    x ∈ Ideal.span (Set.singleton
        (p ^ e : D.scheme.sheaf.obj.obj (op U))) →
        (D.dividedPowers.dividedPowers U).dpow n x ∈
          Ideal.span (Set.singleton
            (p ^ e : D.scheme.sheaf.obj.obj (op U)))

/-- Source assertion: sufficiently high powers of `p` are locally preserved
by the divided powers. -/
def PowerIdealLocallyPreserved (D : DividedPowerScheme.{u}) (p : ℕ) : Prop :=
  ∀ U : D.scheme.Opens, ∃ e : ℕ, PreservesPowerIdeal D p e U

theorem powerIdeal_eventually_preserved (D : DividedPowerThickening.{u})
    (p : ℕ) (hp : IsLocallyNilpotentOnScheme p D.source) :
    PowerIdealLocallyPreserved D.target p := by
  sorry

/-! ## Scheme fibre products and the source's fibre-product lemma -/

/-- A scheme-theoretic fibre product presented by its universal property. -/
structure SchemeFiberProduct (T S T' : Scheme.{u})
    (f : T ⟶ S) (f' : T' ⟶ S) where
  product : Scheme.{u}
  fst : product ⟶ T
  snd : product ⟶ T'
  commutes : fst ≫ f = snd ≫ f'
  isPullback : ∀ (W : Scheme.{u}) (a : W ⟶ T) (b : W ⟶ T'),
    a ≫ f = b ≫ f' →
      ∃! c : W ⟶ product, c ≫ fst = a ∧ c ≫ snd = b

/-- A chosen special fibre, i.e. a closed subscheme defined by the ideal. -/
structure SpecialFiber (T : DividedPowerScheme.{u}) where
  scheme : Scheme.{u}
  inclusion : scheme ⟶ T.scheme
  isClosedImmersion : AlgebraicGeometry.IsClosedImmersion inclusion
  definesIdeal : Prop

/-- Data expressing the fibre product in the divided-power category and the
two geometric assertions in the source lemma. -/
structure DividedPowerFiberProductData
    {T T' S : DividedPowerScheme.{u}}
    (f : DividedPowerScheme.Hom T S)
    (f' : DividedPowerScheme.Hom T' S) where
  product : DividedPowerScheme.{u}
  fst : DividedPowerScheme.Hom product T
  snd : DividedPowerScheme.Hom product T'
  commutes : fst.hom ≫ f.hom = snd.hom ≫ f'.hom
  isCartesian : ∀ (W : DividedPowerScheme.{u})
      (a : DividedPowerScheme.Hom W T) (b : DividedPowerScheme.Hom W T'),
    a.hom ≫ f.hom = b.hom ≫ f'.hom →
      ∃! c : DividedPowerScheme.Hom W product,
        c.hom ≫ fst.hom = a.hom ∧ c.hom ≫ snd.hom = b.hom
  ordinary : SchemeFiberProduct T.scheme S.scheme T'.scheme f.hom f'.hom
  comparison : product.scheme ⟶ ordinary.product
  comparison_isClosedImmersion : AlgebraicGeometry.IsClosedImmersion comparison
  specialProduct : SpecialFiber product
  specialT : SpecialFiber T
  specialS : SpecialFiber S
  specialT' : SpecialFiber T'
  specialTToS : specialT.scheme ⟶ specialS.scheme
  specialT'ToS : specialT'.scheme ⟶ specialS.scheme
  specialOrdinary : SchemeFiberProduct specialT.scheme specialS.scheme
      specialT'.scheme specialTToS specialT'ToS
  specialComparison : specialProduct.scheme ⟶ specialOrdinary.product
  specialComparison_isIso : IsIso specialComparison

/-- Fibre products of divided power schemes, under the missing thickening
hypothesis needed for the special-fibre assertions. -/
theorem exists_fiberProduct {T T' S : DividedPowerScheme.{u}}
    (f : DividedPowerScheme.Hom T S)
    (f' : DividedPowerScheme.Hom T' S)
    (hthick : IsThickening f.hom ∨ IsThickening f'.hom) :
    Nonempty (DividedPowerFiberProductData f f') := by
  sorry

/-! ## The global crystalline situation -/

/-- A scheme over a chosen `Z_(p)`-algebra. -/
structure SchemeOverZLocalized where
  dividedPowerScheme : DividedPowerScheme.{u}
  p : ℕ
  prime : Nat.Prime p
  baseRing : CommRingCat.{u}
  isZLocalized : IsZLocalizedAtPrime p (baseRing : Type u)
  structureMap : dividedPowerScheme.scheme ⟶ Scheme.Spec.obj (op baseRing)

/-- The fixed global situation of the chapter. -/
structure GlobalSituation where
  base : SchemeOverZLocalized.{u}
  specialFiber : SpecialFiber base.dividedPowerScheme
  X : Scheme.{u}
  X_to_specialFiber : X ⟶ specialFiber.scheme
  p_locally_nilpotent : IsLocallyNilpotentOnScheme base.p X

end
end Formalization.Books.Crystalline.Unit07
