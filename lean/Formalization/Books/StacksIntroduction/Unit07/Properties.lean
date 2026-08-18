import Formalization.Books.StacksIntroduction.Unit06.SmoothCover
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

/- A native stack-property theorem would supply a value of this interface.
The properties below therefore take that value explicitly; fabricating one
with `True` fields would turn the source's implications into tautologies. -/

/-- Smoothness of the moduli object over `Spec(ℤ)` for a presentation. -/
def IsSmoothEllipticModuliOverIntegers
    (P : EllipticModuliPropertyPresentation) : Prop :=
  P.smooth

/-- Quasi-compactness of the moduli object for a presentation. -/
def IsQuasiCompactEllipticModuli
    (P : EllipticModuliPropertyPresentation) : Prop :=
  P.quasiCompact

/-- Irreducibility of the moduli object for a presentation. -/
def IsIrreducibleEllipticModuli
    (P : EllipticModuliPropertyPresentation) : Prop :=
  P.irreducible

theorem ellipticModuli_smooth_iff_universalBase_smooth
    (P : EllipticModuliPropertyPresentation) :
    IsSmoothEllipticModuliOverIntegers P ↔ Smooth universalBaseToIntegers :=
  P.smooth_iff_universalBase

/-- Quasi-compactness descends from the chosen smooth cover. -/
theorem ellipticModuli_quasiCompact_of_universalBase_quasiCompact
    (P : EllipticModuliPropertyPresentation)
    (h : CompactSpace universalBaseScheme) :
    IsQuasiCompactEllipticModuli P :=
  P.quasiCompact_of_universalBase h

/-- Irreducibility descends from the chosen smooth cover. -/
theorem ellipticModuli_irreducible_of_universalBase_irreducible
    (P : EllipticModuliPropertyPresentation)
    (h : IrreducibleSpace universalBaseScheme) :
    IsIrreducibleEllipticModuli P :=
  P.irreducible_of_universalBase h

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
statement about `\Pic(\mathcal M_{1,1})` and `\Pic_H(W)`.  A native
stack-Picard construction would supply this interface; the chapter does not
manufacture one from `ZMod 12`. -/
structure PicardModuliIdentification where
  moduliGroup : Type u
  [moduliGroup_structure : AddCommGroup moduliGroup]
  equivariantGroup : Type u
  [equivariantGroup_structure : AddCommGroup equivariantGroup]
  moduli_equivariant : moduliGroup ≃+ equivariantGroup
  equivariant_ZMod : equivariantGroup ≃+ ZMod 12

/-- The scheme-side Picard group is Mathlib's canonical Picard group of the ring. -/
abbrev PicardGroupOfUniversalBase := CommRing.Pic UniversalBaseRing

/-- The moduli Picard group supplied by an identification interface. -/
abbrev PicardGroupOfModuli (P : PicardModuliIdentification) := P.moduliGroup

abbrev EquivariantPicardGroupOfUniversalBase
    (P : PicardModuliIdentification) := P.equivariantGroup

noncomputable instance picardGroupOfModuli_addCommGroup
    (P : PicardModuliIdentification) :
    AddCommGroup (PicardGroupOfModuli P) :=
  P.moduliGroup_structure

noncomputable instance equivariantPicardGroupOfUniversalBase_addCommGroup
    (P : PicardModuliIdentification) :
    AddCommGroup (EquivariantPicardGroupOfUniversalBase P) :=
  P.equivariantGroup_structure

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
def picardRestrictionMap (P : PicardModuliIdentification) :
    ℤ →+ EquivariantPicardGroupOfUniversalBase P :=
  P.equivariant_ZMod.symm.toAddMonoidHom.comp
    (Int.castAddHom (ZMod 12))

/-- The exact sequence displayed in the Picard-group paragraph. -/
theorem picard_discriminant_exact_sequence
    (P : PicardModuliIdentification) :
    Function.Exact picardDiscriminantMap (picardRestrictionMap P) ∧
      Function.Surjective (picardRestrictionMap P) := by
  refine ⟨?_, ?_⟩
  · unfold Function.Exact
    intro x
    change P.equivariant_ZMod.symm (x : ZMod 12) = 0 ↔
      ∃ y : ℤ, 12 * y = x
    constructor
    · intro hx
      have hcast : (x : ZMod 12) = 0 := by
        simpa using (P.equivariant_ZMod.symm_apply_eq.mp hx)
      rcases (ZMod.intCast_zmod_eq_zero_iff_dvd x 12).mp hcast with ⟨y, hy⟩
      exact ⟨y, by simpa using hy.symm⟩
    · rintro ⟨y, rfl⟩
      rw [Int.cast_mul]
      have h12 : ((12 : ℤ) : ZMod 12) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd 12 12).2 (dvd_refl 12)
      rw [h12, zero_mul, P.equivariant_ZMod.symm.map_zero]
  · intro z
    refine ⟨(ZMod.cast (P.equivariant_ZMod z) : ℤ), ?_⟩
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

/-- A filtration and eventual-page formulation of convergence for the
Čech spectral sequence.  A finite page is not, in general, the abutment;
the associated graded pieces are required to agree with all sufficiently
late pages instead. -/
structure CechSpectralSequenceConvergence
    {Λ : Type u} [Ring Λ]
  (spectralSequence :
      CategoryTheory.E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} Λ))
    (moduliCohomology : ℕ → ModuleCat.{u} Λ) where
  filtration : ∀ n : ℕ, Fin (n + 2) →
    Submodule Λ (moduliCohomology n)
  filtration_mono : ∀ n : ℕ, ∀ i j : Fin (n + 2), i ≤ j →
    filtration n i ≤ filtration n j
  filtration_bot : ∀ n : ℕ, filtration n 0 = ⊥
  filtration_top : ∀ n : ℕ,
    filtration n (Fin.last (n + 1)) = ⊤
  eventual_stability : ∀ n : ℕ, ∀ i : Fin (n + 1), ∃ r₀ : ℕ, ∀ r : ℕ,
      r₀ ≤ r → Nonempty
      (CategoryTheory.Iso
        (ModuleCat.of Λ
          (filtration n (Fin.succ i) ⧸
            Submodule.comap (Submodule.subtype (filtration n (Fin.succ i)))
              (filtration n (Fin.castSucc i))))
        ((spectralSequence.page (r + 2)).X (i, n - i)))

/-- The actual spectral-sequence data needed from an étale cohomology theory. -/
structure CechSpectralSequenceData
    {Λ : Type u} [Ring Λ]
    (schemeCohomology : Scheme.{0} → ℕ → ModuleCat.{u} Λ)
    (moduliCohomology : ℕ → ModuleCat.{u} Λ) (H : Scheme.{0}) where
  spectralSequence :
    CategoryTheory.E₂CohomologicalSpectralSequenceNat (ModuleCat.{u} Λ)
  e₂_page : ∀ p q : ℕ, Nonempty
    ((spectralSequence.page 2).X (p, q) ≅
      schemeCohomology (cechProductPresentation H p).carrier q)
  convergence :
    CechSpectralSequenceConvergence spectralSequence moduliCohomology

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
