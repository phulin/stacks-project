import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit68.RegularSequences
import Formalization.Books.Algebra.Unit69.QuasiRegularSequences
import Formalization.Books.Algebra.Unit75.TorGroups
import Formalization.Books.Algebra.Unit76.FunctorialitiesForTor
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Commutative Algebra, Chapter 99: Criteria for flatness

This file records the theorem interfaces in the source section.  Flatness,
faithful flatness, Tor, regular sequences, quotient modules, and localization
use the canonical Mathlib and earlier-chapter APIs.
-/

namespace Formalization.Books.Algebra.Unit99

open CategoryTheory
open CategoryTheory.Limits
open Function
open Formalization.Books.Algebra.Unit75
open Formalization.Books.Algebra.Unit76
open scoped TensorProduct

noncomputable section

universe u v w z

/- A small source-facing abbreviation for the canonical Tor construction. -/
abbrev tor {R : Type u} [CommRing R]
    (M N : Type u) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (i : ℕ) : ModuleCat.{u} R :=
  Formalization.Books.Algebra.Unit75.Tor
    (ModuleCat.of R M) (ModuleCat.of R N) i

/-! ## The Noetherian local lemmas -/

/- The induced map on residue modules is Mathlib's `Submodule.mapQ`; the
   displayed maximal ideal action is written as `m • ⊤`. -/
theorem mod_injective
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] [Module R N] [IsScalarTower R S N]
    (hM : Module.Flat R M) (hN : Module.Finite S N)
    (u : N →ₗ[R] M)
    (hu : Function.Injective
      ((IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)).mapQ
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) u
        (Submodule.smul_top_le_comap_smul_top
          (IsLocalRing.maximalIdeal R) u))) :
    Function.Injective u ∧
      Module.Flat R (M ⧸ LinearMap.range u) := by
  sorry

theorem grothendieck
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (hflat : Module.Flat R S) (f : S)
    (hf : IsSMulRegular
      (S ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) : Submodule S S)) f) :
    Module.Flat R
        (S ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) : Submodule S S)) ∧
      IsSMulRegular S f := by
  sorry

theorem grothendieck_regular_sequence
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (hflat : Module.Flat R S) (xs : List S)
    (hxs : RingTheory.Sequence.IsRegular
      (S ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) : Submodule S S))
      (xs.map (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal R).map (algebraMap R S))))) :
    RingTheory.Sequence.IsRegular S xs ∧
      (∀ i : Fin xs.length,
        Module.Flat R
          (S ⧸ (Ideal.ofList (xs.take (i.1 + 1)) : Submodule S S))) := by
  sorry

theorem free_fibre_flat_free
    {R S M : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing R]
    [IsNoetherianRing S] [AddCommGroup M] [Module S M]
    [Module R M] [IsScalarTower R S M]
    (hM : Nontrivial M) (hfinite : Module.Finite S M)
    (hfibre : Module.Free
      (S ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S)))
      (M ⧸ (((IsLocalRing.maximalIdeal R).map (algebraMap R S)) •
        (⊤ : Submodule S M))))
    (hflat : Module.Flat R M) :
    Module.Free S M ∧ Module.Flat R S := by
  sorry

/-! ## Finite complexes over a local homomorphism -/

/-- A finite complex indexed so that `differential i` maps the `(i+1)`st
term to the `i`th term.  The last term is the leading zero in the source's
displayed complex. -/
structure FiniteModuleComplex (S : Type u) [CommRing S] (e : ℕ) where
  term : Fin (e + 2) → ModuleCat.{u} S
  differential : ∀ i : Fin (e + 1),
    term i.succ ⟶ term i.castSucc
  isComplex : ∀ i : Fin e,
    differential i.succ ≫ differential i.castSucc = 0
  last_is_zero : IsZero (term ⟨e + 1, Nat.lt_succ_self (e + 1)⟩)

/-- Exactness of `0 → F_e → ⋯ → F_0`, expressed at the terms where the
source asserts exactness.  The cokernel at `F_0` is intentionally not
required to vanish. -/
def FiniteModuleComplex.IsExact
    {S : Type u} [CommRing S] {e : ℕ}
    (C : FiniteModuleComplex S e) : Prop :=
  Function.Injective (C.differential ⟨e, Nat.lt_succ_self e⟩) ∧
    ∀ i : Fin e,
      Function.Exact (C.differential i.succ) (C.differential i.castSucc)

/-- A finite complex whose terms are finite and flat over a ring below `S`. -/
structure FiniteFlatModuleComplex
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (e : ℕ)
    extends FiniteModuleComplex S e where
  rModule : ∀ i, Module R (term i)
  scalarTower : ∀ i,
    letI := rModule i
    IsScalarTower R S (term i)
  finite : ∀ i, Module.Finite S (term i)
  flat : ∀ i,
    letI := rModule i
    letI := scalarTower i
    Module.Flat R (term i)

/-- The quotient term and induced differential modulo an ideal of `S`. -/
abbrev FiniteModuleComplex.quotientTerm
    {S : Type u} [CommRing S] {e : ℕ}
    (C : FiniteModuleComplex S e) (J : Ideal S) (i : Fin (e + 2)) :=
  (C.term i) ⧸ (J • (⊤ : Submodule S (C.term i)))

def FiniteModuleComplex.quotientDifferential
    {S : Type u} [CommRing S] {e : ℕ}
    (C : FiniteModuleComplex S e) (J : Ideal S) (i : Fin (e + 1)) :
    C.quotientTerm J i.succ →ₗ[S] C.quotientTerm J i.castSucc :=
  (J • (⊤ : Submodule S (C.term i.succ))).mapQ
    (J • (⊤ : Submodule S (C.term i.castSucc)))
    (C.differential i).hom
    (Submodule.smul_top_le_comap_smul_top J (C.differential i).hom)

/-- Exactness of the quotient complex modulo `J`. -/
def FiniteModuleComplex.quotientIsExact
    {S : Type u} [CommRing S] {e : ℕ}
    (C : FiniteModuleComplex S e) (J : Ideal S) : Prop :=
  Function.Injective (C.quotientDifferential J ⟨e, Nat.lt_succ_self e⟩) ∧
    ∀ i : Fin e,
      Function.Exact (C.quotientDifferential J i.succ)
        (C.quotientDifferential J i.castSucc)

theorem complex_exact_mod
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing R]
    [IsNoetherianRing S] (e : ℕ)
    (C : FiniteFlatModuleComplex R S e)
    (hfibre : C.toFiniteModuleComplex.quotientIsExact
      ((IsLocalRing.maximalIdeal R).map (algebraMap R S))) :
    C.toFiniteModuleComplex.IsExact ∧
      (letI := C.rModule 0
       letI := C.scalarTower 0
       letI := C.rModule ((0 : Fin (e + 1)).castSucc)
       letI := C.scalarTower ((0 : Fin (e + 1)).castSucc)
       letI := C.rModule ((0 : Fin (e + 1)).succ)
       letI := C.scalarTower ((0 : Fin (e + 1)).succ)
       Module.Flat R
         (C.term 0 ⧸ LinearMap.range ((C.differential 0).hom.restrictScalars R))) := by
  sorry

/-! ## Tor vanishing and the local criterion -/

theorem prepare_local_criterion_flatness
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [IsLocalRing R]
    (hTor : IsZero
      (tor (R := R) (R ⧸ IsLocalRing.maximalIdeal R) M 1))
    {N : Type u} [AddCommGroup N] [Module R N]
    (hN : IsFiniteLength R N) :
    IsZero (tor (R := R) N M 1) := by
    induction hN with
    | of_subsingleton =>
      rename_i N' _ _ hsub
      have hflat : Module.Flat R N' := by infer_instance
      have hcrit : Module.Flat R N' ↔
          TorFunctorZero (ModuleCat.of R N') 1 :=
        (flat_iff_tor_criteria (ModuleCat.of R N')).out 0 2
      exact hcrit.mp hflat (ModuleCat.of R M)
    | of_simple_quotient =>
      rename_i M' hAdd hMod N' hsimple hfin ih
      obtain ⟨I, hI, eI⟩ :=
        (isSimpleModule_iff_quot_maximal (R := R) (M := M' ⧸ N')).mp hsimple
      have hIe : I = IsLocalRing.maximalIdeal R :=
        IsLocalRing.eq_maximalIdeal hI
      subst I
      have hTorI : IsZero (tor (R := R) (R ⧸ IsLocalRing.maximalIdeal R) M 1) := hTor
      have hTorI' : IsZero (tor (R := R) M
          (R ⧸ IsLocalRing.maximalIdeal R) 1) :=
        IsZero.of_iso hTorI
          (torLeftRightIso (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R))
            (ModuleCat.of R M) 1).symm
      let eQ : ModuleCat.of R (M' ⧸ N') ≅
          ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) :=
        (Classical.choice eI).toModuleIso
      let qMap := torMapSecond (ModuleCat.of R M)
        (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R (M' ⧸ N')) eQ.inv 1
      let qMapInv := torMapSecond (ModuleCat.of R M)
        (ModuleCat.of R (M' ⧸ N')) (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) eQ.hom 1
      have hq1 : qMap ≫ qMapInv = 𝟙 _ := by
        dsimp [qMap, qMapInv]
        rw [← torMapSecond_comp, eQ.inv_hom_id, torMapSecond_id]
      have hq2 : qMapInv ≫ qMap = 𝟙 _ := by
        dsimp [qMap, qMapInv]
        rw [← torMapSecond_comp, eQ.hom_inv_id, torMapSecond_id]
      haveI : IsIso qMap := ⟨⟨qMapInv, hq1, hq2⟩⟩
      have hquotSym : IsZero (tor (R := R) M (M' ⧸ N') 1) :=
        IsZero.of_iso hTorI' (asIso qMap).symm
      have hiSym : IsZero (tor (R := R) M (N' : Type u) 1) :=
        IsZero.of_iso ih
          (torLeftRightIso (ModuleCat.of R (N' : Type u)) (ModuleCat.of R M) 1).symm
      let S : ShortComplex (ModuleCat.{u} R) :=
        ShortComplex.mk (ModuleCat.ofHom N'.subtype)
          (ModuleCat.ofHom (Submodule.mkQ N')) (by
            apply ModuleCat.hom_ext
            ext x
            simp [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, x.property])
      have hS : S.ShortExact := by
        apply ModuleCat.shortComplex_shortExact
        · simpa [S] using (LinearMap.exact_subtype_mkQ N')
        · exact Subtype.val_injective
        · exact Submodule.mkQ_surjective N'
      let hseq := Classical.choice (exists_tor_long_exact_sequence
        (ModuleCat.of R M) S hS)
      have hzero1 : IsZero (Tor (ModuleCat.of R M) S.X₁ 1) := by
        simpa [S] using hiSym
      have hzero3 : IsZero (Tor (ModuleCat.of R M) S.X₃ 1) := by
        simpa [S] using hquotSym
      haveI : Subsingleton (Tor (ModuleCat.of R M) S.X₁ 1) :=
        (ModuleCat.isZero_iff_subsingleton).mp hzero1
      haveI : Subsingleton (Tor (ModuleCat.of R M) S.X₃ 1) :=
        (ModuleCat.isZero_iff_subsingleton).mp hzero3
      haveI : Subsingleton (Tor (ModuleCat.of R M) S.X₂ 1) := by
        constructor
        intro x y
        have hxker : hseq.map₂ x = 0 := Subsingleton.elim _ _
        obtain ⟨z, hz⟩ := (hseq.exact₁ x).mp hxker
        have hz0 : z = 0 := Subsingleton.elim _ _
        have hx0 : x = 0 := by
          rw [← hz, hz0]
          simp
        have hyker : hseq.map₂ y = 0 := Subsingleton.elim _ _
        obtain ⟨w, hw⟩ := (hseq.exact₁ y).mp hyker
        have hw0 : w = 0 := Subsingleton.elim _ _
        have hy0 : y = 0 := by
          rw [← hw, hw0]
          simp
        exact hx0.trans hy0.symm
      have hzero2 : IsZero (Tor (ModuleCat.of R M) S.X₂ 1) :=
        ModuleCat.isZero_of_subsingleton _
      have hzero2' : IsZero (tor (R := R) M M' 1) := by
        simpa [S] using hzero2
      exact IsZero.of_iso hzero2'
        (torLeftRightIso (ModuleCat.of R M') (ModuleCat.of R M) 1)

theorem local_criterion_flatness
    {R S M : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing R]
    [IsNoetherianRing S]
    [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] (hfinite : Module.Finite S M)
    (hTor : IsZero
      (tor (R := R) (R ⧸ IsLocalRing.maximalIdeal R) M 1)) :
    Module.Flat R M := by
  sorry

/-! ## Powers of an ideal and the local criterion -/

/-- An `R`-module is annihilated by the indicated power of an ideal. -/
def IsAnnihilatedByIdealPower
    {R N : Type u} [CommRing R] [AddCommGroup N] [Module R N]
    (I : Ideal R) (m : ℕ) : Prop :=
  I ^ m • (⊤ : Submodule R N) = ⊥

theorem what_does_it_mean
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (hflat : Module.Flat (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))))
    (hTor : IsZero (tor (R := R) (R ⧸ I) M 1)) :
    (∀ n : ℕ, 0 < n →
      Module.Flat (R ⧸ I ^ n)
        (M ⧸ (I ^ n • (⊤ : Submodule R M)))) ∧
      (∀ {N : Type u} [AddCommGroup N] [Module R N] (m : ℕ),
        IsAnnihilatedByIdealPower (N := N) I m →
          IsZero (tor (R := R) N M 1)) ∧
      ((∃ m : ℕ, I ^ m = ⊥) → Module.Flat R M) := by
  sorry

/-- Data for the canonical multiplication map on associated graded pieces.
The `on_pure` field fixes the map on representatives, so this is not an
arbitrary auxiliary linear map. -/
structure IdealPowerPieceMap
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (n : ℕ) where
  map : M ⊗[R] Unit69.quasiRegularPiece R R I n →ₗ[R]
    Unit69.quasiRegularPiece R M I n
  on_pure : ∀ (m : M) (a : ↥(I ^ n • (⊤ : Submodule R R))),
    map (TensorProduct.tmul R m (Submodule.Quotient.mk a)) =
      Submodule.Quotient.mk
        (⟨a.1 • m,
          Submodule.smul_mem_smul (by simpa using a.2)
            (Submodule.mem_top : m ∈ (⊤ : Submodule R M))⟩ :
          ↥(I ^ n • (⊤ : Submodule R M)))

theorem what_does_it_mean_again
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (hflat : Module.Flat (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))))
    (hmap : ∀ n : ℕ, IdealPowerPieceMap (M := M) I n)
    (hInjective : Function.Injective (hmap 1).map) :
    Module.Flat (R ⧸ I ^ 2)
        (M ⧸ (I ^ 2 • (⊤ : Submodule R M))) ∧
      (∀ k : ℕ,
        (∀ n : ℕ, 1 ≤ n → n ≤ k →
          Function.Injective (hmap n).map) →
        Module.Flat (R ⧸ I ^ (k + 1))
          (M ⧸ (I ^ (k + 1) • (⊤ : Submodule R M)))) := by
  sorry

theorem variant_local_criterion_flatness
    {R S M : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing R]
    [IsNoetherianRing S] [AddCommGroup M] [Module S M]
    [Module R M] [IsScalarTower R S M]
    (I : Ideal R) (hI : I ≠ ⊤) (hfinite : Module.Finite S M)
    (hTor : IsZero (tor (R := R) M (R ⧸ I) 1))
    (hflat : Module.Flat (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Flat R M := by
  sorry

theorem principal_ideal_tor_one_iff
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (x : R) (hx : IsSMulRegular R x) :
    IsZero (tor (R := R) M (R ⧸ Ideal.span {x}) 1) ↔
      IsSMulRegular M x := by
  sorry

/-- Flatness over the base ring of a module localized at a prime of an
algebra.  The base action is the canonical restriction of the action of the
localized algebra. -/
noncomputable def flatAtPrimeOverBase
    {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (q : PrimeSpectrum S) : Prop :=
  letI : Module R (LocalizedModule q.asIdeal.primeCompl M) :=
    Module.compHom _ (algebraMap R (Localization.AtPrime q.asIdeal))
  Module.Flat R (LocalizedModule q.asIdeal.primeCompl M)

theorem flat_module_powers
    {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S M]
    (I : Ideal R)
    (hflat : ∀ n : ℕ, 0 < n →
      Module.Flat (R ⧸ I ^ n)
        (M ⧸ (I ^ n • (⊤ : Submodule R M)))) :
    (∀ q : PrimeSpectrum S, I.map (algebraMap R S) ≤ q.asIdeal →
      flatAtPrimeOverBase (R := R) (M := M) q) ∧
      ((∀ [hSlocal : IsLocalRing S],
          I.map (algebraMap R S) ≤ IsLocalRing.maximalIdeal S →
            Module.Flat R M)) := by
  sorry

/-! ## Change-of-rings maps on Tor -/

/-- The `R`-linear map of regular modules induced by two composable ring
maps. -/
def ringHomAsBaseLinearMap
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) :
    restrictedModule f (ModuleCat.of A A) ⟶
      restrictedModule (g.comp f) (ModuleCat.of B B) := by
  letI : Module R A := Module.compHom A f
  letI : Module R B := Module.compHom B (g.comp f)
  exact ModuleCat.ofHom
    { toFun := g
      map_add' := g.map_add
      map_smul' := by
        intro r x
        change g (f r * x) = g (f r) * g x
        rw [map_mul] }

/-- The Tor map induced by the second-variable map between the two regular
modules in the preceding definition. -/
noncomputable def torSecondBaseChangeMap
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    (f : R →+* R') (g : R' →+* R'') (M : ModuleCat.{u} R) :
    restrictedTor f M (ModuleCat.of R' R') 1 ⟶
      restrictedTor (g.comp f) M (ModuleCat.of R'' R'') 1 :=
  torMapSecond M
    (restrictedModule f (ModuleCat.of R' R'))
    (restrictedModule (g.comp f) (ModuleCat.of R'' R''))
    (ringHomAsBaseLinearMap f g) 1

/-- The source's natural base-change map on first Tor, with the target scalar
actions made explicit through the canonical `TargetTorModule` interface from
Chapter 76. -/
structure TorOneBaseChangeData
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    (f : R →+* R') (g : R' →+* R'') (M : ModuleCat.{u} R) where
  source : TargetTorModule f M (ModuleCat.of R' R') 1
  target : TargetTorModule (g.comp f) M (ModuleCat.of R'' R'') 1
  map :
    letI := source.module
    letI := target.module
    (ModuleCat.extendScalars g).obj
        (ModuleCat.of R'
          (restrictedTor f M (ModuleCat.of R' R') 1)) ⟶
      ModuleCat.of R''
        (restrictedTor (g.comp f) M (ModuleCat.of R'' R'') 1)
  natural :
    letI : Algebra R' R'' := g.toAlgebra
    letI := source.module
    letI := target.module
    ∀ (s : R'')
      (x : restrictedTor f M (ModuleCat.of R' R') 1),
      map.hom (TensorProduct.tmul R' s x) =
        s • torSecondBaseChangeMap f g M x

theorem exists_tor_one_base_change_data
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    (f : R →+* R') (g : R' →+* R'') (M : ModuleCat.{u} R) :
    Nonempty (TorOneBaseChangeData f g M) := by
  sorry

noncomputable def canonicalTorOneBaseChangeData
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    (f : R →+* R') (g : R' →+* R'') (M : ModuleCat.{u} R) :
    TorOneBaseChangeData f g M :=
  Classical.choice (exists_tor_one_base_change_data f g M)

theorem surjective_on_tor_one
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    (f : R →+* R') (g : R' →+* R'') (M : ModuleCat.{u} R)
    (hflat : Module.Flat R' ((ModuleCat.extendScalars f).obj M)) :
    Function.Surjective
      (let D := canonicalTorOneBaseChangeData f g M
       letI := D.source.module
       letI := D.target.module
       D.map.hom) := by
  sorry

/- The natural map in the trivial base-change situation.  It is the
change-of-rings map from Chapter 76 followed by the Tor map induced by the
extension/restriction counit on `R'/I'`. -/
noncomputable def canonicalTorOneTrivialChangeMap
    {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (I : Ideal R) (M : ModuleCat.{u} R) :
    Tor (restrictedModule f (ModuleCat.of R' (R' ⧸ I.map f))) M 1 ⟶
      (ModuleCat.restrictScalars f).obj
        (Tor (ModuleCat.of R' (R' ⧸ I.map f))
          ((ModuleCat.extendScalars f).obj M) 1) := by
  exact canonicalTorChangeOfRingsMap f
      (restrictedModule f (ModuleCat.of R' (R' ⧸ I.map f))) M 1 ≫
    (ModuleCat.restrictScalars f).map
      (torMapFirst (N := (ModuleCat.extendScalars f).obj M)
        ((ModuleCat.extendRestrictScalarsAdj f).counit.app
          (ModuleCat.of R' (R' ⧸ I.map f))) 1)

theorem surjective_on_tor_one_trivial
    {R R' : Type u} [CommRing R] [CommRing R']
    (f : R →+* R') (I : Ideal R) (M : ModuleCat.{u} R) :
    Function.Surjective
      (canonicalTorOneTrivialChangeMap f I M).hom := by
  sorry

/-! ## A localization of a tensor product -/

/-- The ring map from a tensor product to the target of a commutative square. -/
def tensorProductToSquareTarget
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    (compat : h.comp f = k.comp g) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    letI : Algebra R S' := (h.comp f).toAlgebra
    letI : Algebra R' S' := k.toAlgebra
    S ⊗[R] R' →+* S' := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  letI : Algebra R S' := (h.comp f).toAlgebra
  letI : Algebra R' S' := k.toAlgebra
  let hs : S →ₐ[R] S' :=
    { toRingHom := h
      commutes' := fun r => rfl }
  let hk : R' →ₐ[R] S' :=
    { toRingHom := k
      commutes' := fun r => by
        change k (g r) = h (f r)
        simpa [RingHom.comp_apply] using
          congrArg (fun q : R →+* S' => q r) compat.symm }
  exact (Algebra.TensorProduct.lift hs hk (fun _ _ => Commute.all _ _)).toRingHom

/-- `S'` is a localization of `S ⊗[R] R'` for the map supplied by the
commutative square. -/
def IsTensorProductLocalization
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    (compat : h.comp f = k.comp g) : Prop :=
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  letI : Algebra R S' := (h.comp f).toAlgebra
  letI : Algebra R' S' := k.toAlgebra
  ∃ P : Submonoid (S ⊗[R] R'),
    letI : Algebra (S ⊗[R] R') S' :=
      (tensorProductToSquareTarget f g h k compat).toAlgebra
    IsLocalization P S'

/-- The base-changed module `M ⊗_S S'`, viewed as an `R'`-module. -/
abbrev squareBaseChangedModule
    {R' S S' : Type u} [CommRing R'] [CommRing S] [CommRing S']
    (h : S →+* S') (k : R' →+* S') (M : ModuleCat.{u} S) : ModuleCat.{u} R' :=
  (ModuleCat.restrictScalars k).obj ((ModuleCat.extendScalars h).obj M)

/-- The natural Tor map for the second local-criterion variant, represented
as an `R`-linear map by restricting the target scalars along `R → R'`. -/
structure TorOneSquareMapData
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    (I : Ideal R) (M : ModuleCat.{u} S) where
  map :
    Tor ((ModuleCat.restrictScalars f).obj M)
        (ModuleCat.of R (R ⧸ I)) 1 ⟶
      (ModuleCat.restrictScalars g).obj
        (Tor (squareBaseChangedModule h k M)
          (ModuleCat.of R' (R' ⧸ I.map g)) 1)

theorem exists_tor_one_square_map_data
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    (I : Ideal R) (M : ModuleCat.{u} S) :
    Nonempty (TorOneSquareMapData f g h k I M) := by
  sorry

noncomputable def canonicalTorOneSquareMapData
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    (I : Ideal R) (M : ModuleCat.{u} S) :
    TorOneSquareMapData f g h k I M :=
  Classical.choice (exists_tor_one_square_map_data f g h k I M)

theorem another_variant_local_criterion_flatness
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing R'] [IsLocalRing S']
    [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing R']
    [IsNoetherianRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    [IsLocalHom f] [IsLocalHom g] [IsLocalHom h] [IsLocalHom k]
    (compat : h.comp f = k.comp g) (I : Ideal R) (hI : I ≠ ⊤)
    (M : ModuleCat.{u} S) (hfinite : Module.Finite S M)
    (hlocal : IsTensorProductLocalization f g h k compat)
    (hflat : Module.Flat (R ⧸ I)
      ((ModuleCat.restrictScalars f).obj M ⧸
        (I • (⊤ : Submodule R ((ModuleCat.restrictScalars f).obj M)))))
    (hzero : (canonicalTorOneSquareMapData f g h k I M).map = 0) :
    Module.Flat R' (squareBaseChangedModule h k M) := by
  sorry

/-! ## Fibre criterion and the scallop lemmas -/

theorem criterion_flatness_fibre_Noetherian
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing S']
    (f : R →+* S) (g : S →+* S') [IsLocalHom f] [IsLocalHom g]
    {M : ModuleCat.{u} S'} (hfinite : Module.Finite S' M)
    (hM : Nontrivial M)
    (hfibre : Module.Flat (S ⧸
        (IsLocalRing.maximalIdeal R).map f)
      ((ModuleCat.restrictScalars g).obj M ⧸
        ((IsLocalRing.maximalIdeal R).map f •
          (⊤ : Submodule S ((ModuleCat.restrictScalars g).obj M)))))
    (hflat : Module.Flat R
      ((ModuleCat.restrictScalars (g.comp f)).obj M)) :
    Module.Flat R ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) ∧
      Module.Flat S ((ModuleCat.restrictScalars g).obj M) := by
  sorry

theorem flatness_scallop
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (f : A) (hfA : IsSMulRegular A f) (hfM : IsSMulRegular M f)
    (hflat_local : Module.Flat (Localization (Submonoid.powers f))
      (LocalizedModule (Submonoid.powers f) M))
    (hflat_quotient : Module.Flat (A ⧸ Ideal.span {f})
      (M ⧸ (Ideal.span {f} • (⊤ : Submodule A M)))) :
    Module.Flat A M := by
  sorry

theorem faithfullyFlat_scallop
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (f : A) (hfA : IsSMulRegular A f) (hfM : IsSMulRegular M f)
    (hfaithful_local :
      Module.FaithfullyFlat (Localization (Submonoid.powers f))
        (LocalizedModule (Submonoid.powers f) M))
    (hfaithful_quotient : Module.FaithfullyFlat (A ⧸ Ideal.span {f})
      (M ⧸ (Ideal.span {f} • (⊤ : Submodule A M)))) :
    Module.FaithfullyFlat A M := by
  sorry

theorem flatness_scallop_pre
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (r : ℕ) (hr : 0 < r) (f : Fin r → A)
    (hflat_local : ∀ i : Fin r,
      Module.Flat (Localization (Submonoid.powers (f i)))
        (LocalizedModule (Submonoid.powers (f i)) M))
    (hflat_quotient :
      Module.Flat (A ⧸ Ideal.span (Set.range f))
        (M ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule A M))))
    (hTor : ∀ i : ℕ, 1 ≤ i → i ≤ r + 1 →
      IsZero (tor (R := A) M
        (A ⧸ Ideal.span (Set.range f)) i)) :
    Module.Flat A M := by
  sorry

theorem faithfullyFlat_scallop_pre
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (r : ℕ) (hr : 0 < r) (f : Fin r → A)
    (hfaithful_local : ∀ i : Fin r,
      Module.FaithfullyFlat (Localization (Submonoid.powers (f i)))
        (LocalizedModule (Submonoid.powers (f i)) M))
    (hfaithful_quotient :
      Module.FaithfullyFlat (A ⧸ Ideal.span (Set.range f))
        (M ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule A M))))
    (hTor : ∀ i : ℕ, 1 ≤ i → i ≤ r + 1 →
      IsZero (tor (R := A) M
        (A ⧸ Ideal.span (Set.range f)) i)) :
    Module.FaithfullyFlat A M := by
  sorry

end

end Formalization.Books.Algebra.Unit99
