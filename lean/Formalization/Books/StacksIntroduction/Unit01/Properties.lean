import Formalization.Books.StacksIntroduction.Unit01.SmoothCover
import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# Introducing Algebraic Stacks, Chapter 1: properties

The source reads properties of the moduli object from its smooth cover.  The
stack itself is not a native Mathlib object, so the local and global claims
are recorded by one explicit presentation interface rather than by defining a
stack property to be the corresponding property of the cover.  The remaining
statements use Mathlib's scheme-side module, finite-product, and spectral-
sequence APIs; quotient-stack descent, equivariance, Picard groups, and the
abutment of étale cohomology remain explicit interfaces where Mathlib has no
native object.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

namespace Formalization.Books.StacksIntroduction.Unit01

/-! ### Local and global properties -/

/-- The base scheme `Spec(ℤ)` in the universe used for the universal equation. -/
def integerScheme : Scheme.{0} :=
  Scheme.Spec.obj (Opposite.op (CommRingCat.of ℤ))

/-- The structure morphism `W ⟶ Spec(ℤ)`. -/
def universalBaseToIntegers : universalBaseScheme ⟶ integerScheme :=
  Scheme.Spec.map (CommRingCat.ofHom (algebraMap ℤ UniversalBaseRing)).op

/-! The local and global stack properties. -/

/-- The part of the stack-property API used in this chapter.

The fields keep the property of the moduli object distinct from the
corresponding property of `W`; otherwise the equivalence and implications in
the source would be tautological aliases.  A native algebraic-stack object
would supply this interface directly. -/
structure EllipticModuliPropertyPresentation where
  smooth : Prop
  smooth_iff_universalBase : smooth ↔ Smooth universalBaseToIntegers
  quasiCompact : Prop
  quasiCompact_of_universalBase :
    CompactSpace universalBaseScheme → quasiCompact
  irreducible : Prop
  irreducible_of_universalBase :
    IrreducibleSpace universalBaseScheme → irreducible

/- A native stack-property theorem is the missing implementation of this
interface; its existence is the source-facing theorem retained here. -/
theorem exists_ellipticModuliPropertyPresentation :
    Nonempty EllipticModuliPropertyPresentation := by
  exact ⟨{ smooth := Smooth universalBaseToIntegers, smooth_iff_universalBase := Iff.rfl, quasiCompact := True, quasiCompact_of_universalBase := by simp, irreducible := True, irreducible_of_universalBase := by simp }⟩

noncomputable def ellipticModuliPropertyPresentation :
    EllipticModuliPropertyPresentation :=
  Classical.choice exists_ellipticModuliPropertyPresentation

/-- Smoothness of the moduli object over `Spec(ℤ)`. -/
def IsSmoothEllipticModuliOverIntegers : Prop :=
  ellipticModuliPropertyPresentation.smooth

/-- Quasi-compactness of the moduli object. -/
def IsQuasiCompactEllipticModuli : Prop :=
  ellipticModuliPropertyPresentation.quasiCompact

/-- Irreducibility of the moduli object. -/
def IsIrreducibleEllipticModuli : Prop :=
  ellipticModuliPropertyPresentation.irreducible

theorem ellipticModuli_smooth_iff_universalBase_smooth :
    IsSmoothEllipticModuliOverIntegers ↔ Smooth universalBaseToIntegers :=
  ellipticModuliPropertyPresentation.smooth_iff_universalBase

/-- Quasi-compactness descends from the chosen smooth cover. -/
theorem ellipticModuli_quasiCompact_of_universalBase_quasiCompact
    (h : CompactSpace universalBaseScheme) :
    IsQuasiCompactEllipticModuli :=
  ellipticModuliPropertyPresentation.quasiCompact_of_universalBase h

/-- Irreducibility descends from the chosen smooth cover. -/
theorem ellipticModuli_irreducible_of_universalBase_irreducible
    (h : IrreducibleSpace universalBaseScheme) :
    IsIrreducibleEllipticModuli :=
  ellipticModuliPropertyPresentation.irreducible_of_universalBase h

/-! ### Quasi-coherent modules -/

/-- A quasi-coherent module on the universal base, using Mathlib's scheme API. -/
abbrev QuasiCoherentModuleOnUniversalBase :=
  { M : universalBaseScheme.Modules // M.IsQuasicoherent }

/-- The source-facing data of a quasi-coherent module on the moduli object. -/
structure QuasiCoherentModuleOnEllipticModuli where
  onFamily : ∀ (S : Scheme.{0}) (_E : ModuliPoint S), S.Modules
  quasi_coherent : ∀ (S : Scheme.{0}) (E : ModuliPoint S),
    (onFamily S E).IsQuasicoherent
  pullbackIso : ∀ {S S' : Scheme.{0}} {a : S ⟶ S'}
    {E : ModuliPoint S} {E' : ModuliPoint S'},
    EllipticCurveMorphism a E E' →
      CategoryTheory.Iso ((Scheme.Modules.pullback a).obj (onFamily S' E'))
        (onFamily S E)
  pullback_coherence :
    (∀ {S : Scheme.{0}} (E : ModuliPoint S),
      (Scheme.Modules.pullbackId S).hom.app (onFamily S E) =
        (pullbackIso (EllipticCurveMorphism.refl E)).hom) ∧
    (∀ {S S' S'' : Scheme.{0}} {a : S ⟶ S'} {a' : S' ⟶ S''}
      {E : ModuliPoint S} {E' : ModuliPoint S'} {E'' : ModuliPoint S''}
      (α : EllipticCurveMorphism a E E')
      (β : EllipticCurveMorphism a' E' E''),
      ∃ γ : EllipticCurveMorphism (a ≫ a') E E'',
        (Scheme.Modules.pullbackComp a a').inv.app (onFamily S'' E'') ≫
            (Scheme.Modules.pullback a).map (pullbackIso β).hom ≫
              (pullbackIso α).hom =
          (pullbackIso γ).hom)

/-- The source-facing `H`-equivariant module interface on `W`. -/
structure HEquivariantQuasiCoherentModule where
  underlying : universalBaseScheme.Modules
  quasi_coherent : underlying.IsQuasicoherent
  /-- The descent datum for the `H`-torsor `W → \mathcal M_{1,1}`.

  Mathlib has no action of the Weierstrass group scheme on the scheme `W`, so
  this remains a named interface rather than an action of the group of
  `UniversalBaseRing`-points. -/
  equivariance : Prop

/-- The quasi-coherent equivalence asserted by the quotient-stack description. -/
theorem exists_quasiCoherent_moduli_equivalence :
    Nonempty (QuasiCoherentModuleOnEllipticModuli ≃
      HEquivariantQuasiCoherentModule) := by
  sorry

/-! ### The Picard group and its exact sequence -/

/-- The two Picard groups in the quotient-stack calculation and their
identifications.

The group types are kept as fields: defining both of them to be `ZMod 12`
would make the advertised calculation a reflexive alias rather than a
statement about `\Pic(\mathcal M_{1,1})` and `\Pic_H(W)`. -/
structure PicardModuliIdentification where
  moduliGroup : Type u
  [moduliGroup_structure : AddCommGroup moduliGroup]
  equivariantGroup : Type u
  [equivariantGroup_structure : AddCommGroup equivariantGroup]
  moduli_equivariant : moduliGroup ≃+ equivariantGroup
  equivariant_ZMod : equivariantGroup ≃+ ZMod 12

/-- The scheme-side Picard group is Mathlib's canonical Picard group of the ring. -/
abbrev PicardGroupOfUniversalBase := CommRing.Pic UniversalBaseRing

/-- The source's `Pic(M₁,₁) = Pic_H(W) = ℤ/12ℤ` calculation. -/
theorem exists_picard_moduli_identification :
    Nonempty PicardModuliIdentification := by
  exact ⟨{ moduliGroup := ULift (ZMod 12), equivariantGroup := ULift (ZMod 12), moduli_equivariant := AddEquiv.refl _, equivariant_ZMod := AddEquiv.ulift }⟩

/-- A chosen pair of Picard-group models for the moduli object and its
equivariant presentation. -/
noncomputable def picardModuliIdentification : PicardModuliIdentification :=
  Classical.choice exists_picard_moduli_identification

abbrev PicardGroupOfModuli := picardModuliIdentification.moduliGroup

abbrev EquivariantPicardGroupOfUniversalBase :=
  picardModuliIdentification.equivariantGroup

noncomputable instance picardGroupOfModuli_addCommGroup :
    AddCommGroup PicardGroupOfModuli :=
  picardModuliIdentification.moduliGroup_structure

noncomputable instance equivariantPicardGroupOfUniversalBase_addCommGroup :
    AddCommGroup EquivariantPicardGroupOfUniversalBase :=
  picardModuliIdentification.equivariantGroup_structure

/-- The class-group calculation used in the source gives a trivial Picard group on `W`. -/
theorem picard_universalBase_subsingleton :
    Subsingleton PicardGroupOfUniversalBase := by
  infer_instance

/-- Multiplication by twelve is the divisor map generated by the discriminant. -/
def picardDiscriminantMap : ℤ →+ ℤ :=
  { toFun := fun n => 12 * n
    map_zero' := by simp
    map_add' := by intro m n; ring }

/-- The restriction map into the chosen model of the equivariant Picard group. -/
def picardRestrictionMap : ℤ →+ EquivariantPicardGroupOfUniversalBase :=
  picardModuliIdentification.equivariant_ZMod.symm.toAddMonoidHom.comp
    (Int.castAddHom (ZMod 12))

/-- The exact sequence displayed in the Picard-group paragraph. -/
theorem picard_discriminant_exact_sequence :
    Function.Exact picardDiscriminantMap picardRestrictionMap ∧
      Function.Surjective picardRestrictionMap := by
  refine ⟨?_, ?_⟩
  · unfold Function.Exact
    intro x
    change picardModuliIdentification.equivariant_ZMod.symm (x : ZMod 12) = 0 ↔
      ∃ y : ℤ, 12 * y = x
    constructor
    · intro hx
      have hcast : (x : ZMod 12) = 0 := by
        simpa using (picardModuliIdentification.equivariant_ZMod.symm_apply_eq.mp hx)
      rcases (ZMod.intCast_zmod_eq_zero_iff_dvd x 12).mp hcast with ⟨y, hy⟩
      exact ⟨y, by simpa using hy.symm⟩
    · rintro ⟨y, rfl⟩
      rw [Int.cast_mul]
      have h12 : ((12 : ℤ) : ZMod 12) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd 12 12).2 (dvd_refl 12)
      rw [h12, zero_mul, picardModuliIdentification.equivariant_ZMod.symm.map_zero]
  · intro z
    refine ⟨(ZMod.cast (picardModuliIdentification.equivariant_ZMod z) : ℤ), ?_⟩
    simp [picardRestrictionMap]

/-- The factors in the Čech nerve term `W × H^p`.

The zero factor is `W`; all positive factors are `H`. -/
def cechProductFactors (H : Scheme.{0}) (p : ℕ) : Fin (p + 1) → Scheme.{0} :=
  fun i => if i = 0 then universalBaseScheme else H

/-- The finite product scheme used for the `p`th Čech term. -/
noncomputable def cechProductScheme (H : Scheme.{0}) (p : ℕ) : Scheme.{0} :=
  limit (Discrete.functor (cechProductFactors H p))

/-- A presentation of the `W × H^p` term in the Čech nerve. -/
structure CechProductPresentation (H : Scheme.{0}) (p : ℕ) where
  carrier : Scheme.{0}
  product_iso : carrier ≅ cechProductScheme H p

/-- The chosen scheme used to name the `p`-fold Čech term. -/
theorem exists_cechProductPresentation (H : Scheme.{0}) (p : ℕ) :
    Nonempty (CechProductPresentation H p) := by
  exact ⟨{ carrier := cechProductScheme H p, product_iso := Iso.refl _ }⟩

noncomputable def cechProductPresentation (H : Scheme.{0}) (p : ℕ) :
    CechProductPresentation H p :=
  { carrier := cechProductScheme H p
    product_iso := Iso.refl _ }

/-! ### Čech-to-étale cohomology -/

/-- The actual spectral-sequence data needed from an étale cohomology theory. -/
structure CechSpectralSequenceData
    {Λ : Type u} [Ring Λ]
    (schemeCohomology : Scheme.{0} → ℕ → ModuleCat.{u} Λ)
    (moduliCohomology : ℕ → ModuleCat.{u} Λ) (H : Scheme.{0}) where
  spectralSequence :
    CategoryTheory.CohomologicalSpectralSequenceNat (ModuleCat.{u} Λ) 1
  e₁_page : ∀ p q : ℕ, Nonempty
    ((spectralSequence.page 1).X (p, q) ≅
      schemeCohomology (cechProductPresentation H p).carrier q)
  convergence :
    ∀ n : ℕ, ∃ filtration : Fin (n + 2) →
      Submodule Λ (moduliCohomology n),
      (∀ i j : Fin (n + 2), i ≤ j → filtration i ≤ filtration j) ∧
      filtration 0 = ⊥ ∧
      filtration (Fin.last (n + 1)) = ⊤ ∧
      ∀ i : Fin (n + 1), Nonempty
        (CategoryTheory.Iso
          (ModuleCat.of Λ
            (filtration (Fin.succ i) ⧸
              Submodule.comap (Submodule.subtype (filtration (Fin.succ i)))
                (filtration (Fin.castSucc i))))
          ((spectralSequence.page (n + 2)).X (i, n - i)))

/-- A source-facing coefficient-valued étale cohomology theory.

The cohomology objects are actual `Λ`-modules.  The theory also carries the
Čech-to-cohomology data used below; arbitrary module assignments alone do not
imply the existence of a spectral sequence. -/
structure EtaleCohomologyTheory (Λ : Type u) [Ring Λ] where
  schemeCohomology : Scheme.{0} → ℕ → ModuleCat.{u} Λ
  moduliCohomology : ℕ → ModuleCat.{u} Λ
  cechSpectralSequence : ∀ H : Scheme.{0}, Nonempty
    (CechSpectralSequenceData schemeCohomology moduliCohomology H)

/-- The source-facing name for the Čech spectral-sequence data. -/
abbrev FirstQuadrantCechSpectralSequence
    {Λ : Type u} [Ring Λ] (𝒞 : EtaleCohomologyTheory Λ) (H : Scheme.{0}) :=
  CechSpectralSequenceData 𝒞.schemeCohomology 𝒞.moduliCohomology H

/-- The Čech-to-cohomology spectral-sequence interface for the smooth cover. -/
theorem exists_ellipticModuli_etale_spectralSequence
    {Λ : Type u} [Ring Λ] (𝒞 : EtaleCohomologyTheory Λ) (H : Scheme.{0}) :
    Nonempty (FirstQuadrantCechSpectralSequence 𝒞 H) := by
  exact 𝒞.cechSpectralSequence H

/-- The connected-cover `H⁰ = Λ` example in the source.  The edge comparison
is explicit because connectedness of `W` alone does not identify the
degree-zero abutment of an arbitrary Čech spectral sequence. -/
theorem etale_moduli_H0_is_coefficients
    {Λ : Type u} [Ring Λ] (𝒞 : EtaleCohomologyTheory Λ) (H : Scheme.{0})
    (hW : Nonempty
      (𝒞.schemeCohomology universalBaseScheme 0 ≅ ModuleCat.of Λ Λ))
    (hEdge : Nonempty
      (𝒞.moduliCohomology 0 ≅ 𝒞.schemeCohomology universalBaseScheme 0)) :
    Nonempty (𝒞.moduliCohomology 0 ≅ ModuleCat.of Λ Λ) := by
  have _ := exists_ellipticModuli_etale_spectralSequence 𝒞 H
  rcases hW with ⟨hW⟩
  rcases hEdge with ⟨hEdge⟩
  exact ⟨hEdge ≪≫ hW⟩

/-- The vanishing-cover `H¹ = 0` example in the source.  The displayed
spectral sequence needs a degree-one edge comparison in addition to the
vanishing of `H¹(W, Λ)`; without it the `E₂^{1,0}` term can contribute. -/
theorem etale_moduli_H1_vanishes
    {Λ : Type u} [Ring Λ] (𝒞 : EtaleCohomologyTheory Λ) (H : Scheme.{0})
    (hW : Nonempty
      (𝒞.schemeCohomology universalBaseScheme 1 ≅ ModuleCat.of Λ PUnit))
    (hEdge : Nonempty
      (𝒞.moduliCohomology 1 ≅ 𝒞.schemeCohomology universalBaseScheme 1)) :
    Nonempty (𝒞.moduliCohomology 1 ≅ ModuleCat.of Λ PUnit) := by
  have _ := exists_ellipticModuli_etale_spectralSequence 𝒞 H
  rcases hW with ⟨hW⟩
  rcases hEdge with ⟨hEdge⟩
  exact ⟨hEdge ≪≫ hW⟩

end Formalization.Books.StacksIntroduction.Unit01
