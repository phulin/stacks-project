import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Commutative Algebra, Chapter 131: Differentials

The source's derivations and modules of Kähler differentials are Mathlib's
`Derivation` and `KaehlerDifferential`.  The declarations below keep the
source order while exposing the source-facing statements that are not already
single canonical Mathlib declarations.
-/

namespace Formalization.Books.Algebra.Unit131

open scoped TensorProduct

attribute [local instance] SMulCommClass.of_commMonoid

/-! ## Derivations and the universal differential -/

/- The source's `Der_R(S, M)` is Mathlib's `Derivation R S M`.  Its additive
   and scalar-module structures, the equivalent R-linearity observation
   `D (r * a) = r • D a`, and postcomposition by a module map are already
   supplied by `Mathlib.RingTheory.Derivation.Basic`. -/

/- The source's presentation by free modules and relations is represented by
   Mathlib's canonical Kähler differential quotient.  This abbreviation is
   only a source-facing name for that construction. -/
abbrev ModuleOfDifferentials (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] : Type _ :=
  KaehlerDifferential R S

/- The universal derivation is the canonical Mathlib construction, not a
   second quotient presentation. -/
noncomputable def universalDifferential
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Derivation R S (ModuleOfDifferentials R S) :=
  KaehlerDifferential.D R S

/- Composition with a linear map is the source's functoriality in the module. -/
def postcomposeDerivation
    {R S M N : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module S N] [Module R M] [Module R N]
    [IsScalarTower R S M] [IsScalarTower R S N]
    (D : Derivation R S M) (f : M →ₗ[S] N) : Derivation R S N :=
  f.compDer D

/- The universal-property isomorphism `Hom_S(Ω_{S/R}, M) ≅ Der_R(S, M)`. -/
noncomputable def derivationsEquivLinearMaps
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] :
    (ModuleOfDifferentials R S →ₗ[S] M) ≃ₗ[S] Derivation R S M :=
  KaehlerDifferential.linearMapEquivDerivation R S

theorem moduleOfDifferentials_subsingleton_of_surjective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (h : Function.Surjective (algebraMap R S)) :
    Subsingleton (ModuleOfDifferentials R S) :=
  KaehlerDifferential.subsingleton_of_surjective R S h

/-! ## Functoriality -/

/- A square of algebra maps is written in Mathlib's orientation
   `A → B` over `R → T`. -/
noncomputable def mapOfDifferentials
    {R T A B : Type*} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R T] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra T B]
    [IsScalarTower R A B] [IsScalarTower R T B] [SMulCommClass T A B] :
    ModuleOfDifferentials R A →ₗ[A] ModuleOfDifferentials T B :=
  KaehlerDifferential.map R T A B

theorem mapOfDifferentials_apply_universalDifferential
    {R T A B : Type*} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R T] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra T B]
    [IsScalarTower R A B] [IsScalarTower R T B] [SMulCommClass T A B]
    (a : A) :
    mapOfDifferentials (R := R) (T := T) (A := A) (B := B)
        (universalDifferential R A a) =
      universalDifferential T B (algebraMap A B a) :=
  KaehlerDifferential.map_D R T A B a

theorem mapOfDifferentials_smul_universalDifferential
    {R T A B : Type*} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R T] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra T B]
    [IsScalarTower R A B] [IsScalarTower R T B] [SMulCommClass T A B]
    (a b : A) :
    mapOfDifferentials (R := R) (T := T) (A := A) (B := B)
        (a • universalDifferential R A b) =
      algebraMap A B a • universalDifferential T B (algebraMap A B b) := by
  rw [LinearMap.map_smul, mapOfDifferentials_apply_universalDifferential,
    IsScalarTower.algebraMap_smul]

/-! ## Colimits and surjective maps -/

/- The source writes the colimit assertion in shorthand.  Since it does not
   specify the filtered category, its ring-map cocones, or the scalar action
   on the resulting module colimit, there is no source-faithful Lean type for
   that line without adding categorical data not present in the text.  The
   canonical maps above are the precise functorial content used by the later
   statements. -/

theorem mapOfDifferentials_surjective
    {R T A B : Type*} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R T] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra T B]
    [IsScalarTower R A B] [IsScalarTower R T B] [SMulCommClass T A B]
    (h : Function.Surjective (algebraMap A B)) :
    Function.Surjective (mapOfDifferentials (R := R) (T := T) (A := A) (B := B)) :=
  KaehlerDifferential.map_surjective_of_surjective R T A B h

theorem mapOfDifferentials_ker_span
    {R T A B : Type*} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R T] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra T B]
    [IsScalarTower R A B] [IsScalarTower R T B] [SMulCommClass T A B]
    (h : Function.Surjective (algebraMap A B)) :
    LinearMap.ker (mapOfDifferentials (R := R) (T := T) (A := A) (B := B)) =
      Submodule.span A
        ((universalDifferential R A) ''
          {a : A | ∃ t : T, algebraMap A B a = algebraMap T B t}) := by
  classical
  let LA : (A →₀ A) →ₗ[A] ModuleOfDifferentials R A :=
    Finsupp.linearCombination A (KaehlerDifferential.D R A)
  let F : (A →₀ A) →ₗ[A] (B →₀ B) :=
    (Finsupp.mapRange.linearMap (Algebra.linearMap A B)).comp
      (Finsupp.lmapDomain A A (algebraMap A B))
  let K : Submodule A (ModuleOfDifferentials R A) :=
    Submodule.span A
      ((KaehlerDifferential.D R A) ''
        {a : A | ∃ t : T, algebraMap A B a = algebraMap T B t})
  have hkerRR : LinearMap.ker (KaehlerDifferential.map R R A B) ≤ K := by
    intro z hz
    rw [KaehlerDifferential.ker_map_of_surjective R A B h] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    rw [← Finset.sum_fiberwise_of_maps_to
      (fun _ ↦ Finset.mem_image_of_mem (algebraMap A B))]
    apply Submodule.sum_mem
    intro c hc
    have hsum : ∑ i ∈ x.support with algebraMap A B i = c, x i ∈
        RingHom.ker (algebraMap A B) := by
      simpa [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply,
        RingHom.mem_ker, Finsupp.single_apply, ← Finset.sum_filter] using
        DFunLike.congr_fun hx c
    obtain ⟨a, ha⟩ := h c
    have hDadd : ∀ i : A,
        (KaehlerDifferential.D R A) i =
          (KaehlerDifferential.D R A) (i - a) +
            (KaehlerDifferential.D R A) a := by
      intro i
      conv_lhs => rw [← sub_add_cancel i a]
      rw [map_add]
    have hdecomp :
        (∑ i ∈ x.support with algebraMap A B i = c,
            x i • (KaehlerDifferential.D R A) i) =
          (∑ i ∈ x.support with algebraMap A B i = c,
            x i • (KaehlerDifferential.D R A) (i - a)) +
            (∑ i ∈ x.support with algebraMap A B i = c, x i) •
              (KaehlerDifferential.D R A) a := by
      calc
        _ = ∑ i ∈ x.support with algebraMap A B i = c,
            x i • ((KaehlerDifferential.D R A) (i - a) +
              (KaehlerDifferential.D R A) a) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hDadd i, smul_add]
        _ = _ := by
          simp_rw [smul_add]
          rw [Finset.sum_add_distrib, ← Finset.sum_smul]
    have hfirst :
        (∑ i ∈ x.support with algebraMap A B i = c,
            x i • (KaehlerDifferential.D R A) (i - a)) ∈ K := by
      apply Submodule.sum_mem
      intro i hi
      apply K.smul_mem
      apply Submodule.subset_span
      refine ⟨i - a, ?_, rfl⟩
      refine ⟨0, ?_⟩
      have hic : algebraMap A B i = c := (Finset.mem_filter.mp hi).2
      simp [hic, ha]
    have hsecond : ∀ (q a : A), q ∈ RingHom.ker (algebraMap A B) →
        q • (KaehlerDifferential.D R A) a ∈ K := by
      intro q a hq
      have hgen : ∀ v : A, v ∈ RingHom.ker (algebraMap A B) →
          (KaehlerDifferential.D R A) v ∈ K := by
        intro v hv
        exact Submodule.subset_span
          ⟨v, ⟨0, by simp [RingHom.mem_ker.mp hv]⟩, rfl⟩
      have hprod : (KaehlerDifferential.D R A) (q * a) ∈ K :=
        hgen (q * a) (RingHom.mem_ker.mpr (by
          simp [RingHom.mem_ker.mp hq]))
      have hq' : a • (KaehlerDifferential.D R A) q ∈ K :=
        K.smul_mem a (hgen q hq)
      have hsub : (KaehlerDifferential.D R A) (q * a) -
          a • (KaehlerDifferential.D R A) q ∈ K :=
        K.sub_mem hprod hq'
      simpa [Derivation.leibniz] using hsub
    rw [hdecomp]
    exact K.add_mem hfirst (hsecond _ _ hsum)
  change LinearMap.ker (KaehlerDifferential.map R T A B) = K
  rw [KaehlerDifferential.ker_map R T A B]
  change Submodule.map LA
    (Submodule.comap F (Submodule.restrictScalars A
      (KaehlerDifferential.kerTotal T B))) = K
  have lift_span :
      ∀ w : B →₀ B, w ∈ Submodule.span B (Set.range fun t : T =>
        Finsupp.single (algebraMap T B t) (1 : B)) →
        ∃ r : A →₀ A, LA r ∈ K ∧ F r = w := by
    intro w hw
    refine Submodule.span_induction
      (p := fun w _ => ∃ r : A →₀ A, LA r ∈ K ∧ F r = w) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨t, rfl⟩
      obtain ⟨a, ha⟩ := h (algebraMap T B t)
      refine ⟨Finsupp.single a 1, ?_, ?_⟩
      · apply Submodule.subset_span
        exact ⟨a, ⟨t, ha⟩, by simp [LA]⟩
      · simp [F, ha]
    · exact ⟨0, by simp [LA, K], map_zero F⟩
    · intro x y hx hy ⟨rx, hrx, hFx⟩ ⟨ry, hry, hFy⟩
      refine ⟨rx + ry, ?_, ?_⟩
      · simpa only [map_add] using K.add_mem hrx hry
      · simp [map_add, hFx, hFy]
    · intro c x hx ⟨rx, hrx, hFx⟩
      obtain ⟨a, ha⟩ := h c
      refine ⟨a • rx, ?_, ?_⟩
      · simpa only [map_smul] using K.smul_mem a hrx
      · rw [map_smul, hFx]
        rw [← IsScalarTower.algebraMap_smul B a x, ha]
  apply le_antisymm
  · rintro z ⟨u, hu, rfl⟩
    change F u ∈ Submodule.restrictScalars A
      (KaehlerDifferential.kerTotal T B) at hu
    rw [← KaehlerDifferential.kerTotal_map R T A B h] at hu
    rcases Submodule.mem_sup.mp hu with ⟨v, hv, w, hw, huv⟩
    rcases hv with ⟨q, hq, hvq⟩
    have hw' : w ∈ Submodule.span B (Set.range fun t : T =>
        Finsupp.single (algebraMap T B t) (1 : B)) := by
      refine Submodule.span_induction (R := A) (M := B →₀ B)
        (s := Set.range fun t : T =>
          (Finsupp.single (algebraMap T B t) (1 : B) : B →₀ B))
        (p := fun (w : B →₀ B) _ => w ∈
          Submodule.span B (Set.range fun t : T =>
            (Finsupp.single (algebraMap T B t) (1 : B) : B →₀ B))) ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨t, rfl⟩
        exact Submodule.subset_span ⟨t, rfl⟩
      · exact Submodule.zero_mem _
      · intro x y hx hy ihx ihy
        exact Submodule.add_mem _ ihx ihy
      · intro a x hx ihx
        rw [← IsScalarTower.algebraMap_smul B a x]
        exact Submodule.smul_mem _ _ ihx
    obtain ⟨r, hrK, hrF⟩ := lift_span w hw'
    let k := u - q - r
    have hkF : F k = 0 := by
      simp only [k, map_sub]
      rw [← huv, hvq, hrF]
      abel
    have hk : LA k ∈ LinearMap.ker (KaehlerDifferential.map R R A B) := by
      rw [KaehlerDifferential.ker_map_of_surjective R A B h]
      refine ⟨k, ?_, rfl⟩
      exact hkF
    have hqK : LA q = 0 := by
      change q ∈ LinearMap.ker
        (Finsupp.linearCombination A (KaehlerDifferential.D R A))
      rw [KaehlerDifferential.kerTotal_eq R A]
      exact hq
    have hku : LA u = LA k + LA q + LA r := by
      calc
        LA u = LA (k + q + r) := by
          congr 1
          simp only [k]
          abel
        _ = LA k + LA q + LA r := by
          rw [map_add, map_add]
    rw [hku]
    have hqmem : LA q ∈ K := hqK ▸ K.zero_mem
    exact K.add_mem (K.add_mem (hkerRR hk) hqmem) hrK
  · change Submodule.span A
      ((KaehlerDifferential.D R A) ''
        {a : A | ∃ t : T, algebraMap A B a = algebraMap T B t}) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨a, ⟨t, ht⟩, rfl⟩
    apply Submodule.mem_map.mpr
    refine ⟨Finsupp.single a 1, ?_, ?_⟩
    · change F (Finsupp.single a 1) ∈
        Submodule.restrictScalars A (KaehlerDifferential.kerTotal T B)
      rw [← KaehlerDifferential.kerTotal_eq T B]
      simp [F, ht]
    · simp [LA]

/- If `i` lies in the kernel of `A →+* B`, the witness `t = 0` in the
   displayed generator set accounts for the source's parenthetical special
   case. -/

/-! ## Exact sequences, localization, and quotients -/

theorem exact_sequence_of_differentials
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] :
    Function.Exact (KaehlerDifferential.mapBaseChange A B C)
      (KaehlerDifferential.map A B C C) :=
  KaehlerDifferential.exact_mapBaseChange_map A B C

theorem exact_sequence_of_differentials_surjective
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] :
    Function.Surjective (KaehlerDifferential.map A B C C) :=
  KaehlerDifferential.map_surjective A B C

/- The first localization assertion is an ordinary bijectivity statement.  The
   second is expressed by the standard `IsLocalizedModule` predicate, which
   records the source's localized-module isomorphism without falsely claiming
   that the unlocalized map itself is bijective. -/
theorem localize_differentials_base
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid A)
    [Algebra (Localization S) B] [IsScalarTower A (Localization S) B]
    (hS : ∀ s, s ∈ S → IsUnit (algebraMap A B s)) :
    Function.Bijective (KaehlerDifferential.map A (Localization S) B B) := by
  have hDlocalized : ∀
      (D : Derivation A B (ModuleOfDifferentials A B)) (t : Localization S),
      D (algebraMap (Localization S) B t) = 0 := by
    intro D t
    let f : A →ₐ[A] B := Algebra.ofId A B
    let hu : ∀ s : S, IsUnit (f s) := by
      intro s
      exact hS s.1 s.2
    let g : Localization S →ₐ[A] B := IsLocalization.liftAlgHom hu
    have hmap : (algebraMap (Localization S) B) = g.toRingHom := by
      apply IsLocalization.ringHom_ext S
      ext a
      simp [g, IsScalarTower.algebraMap_apply A (Localization S) B]
    rw [hmap]
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S t
    have hDs : D (algebraMap A B s) = 0 := by
      simp
    let u : Bˣ := IsUnit.liftRight (f.toMonoidHom.domRestrict S) hu s
    have huval : (u : B) = algebraMap A B s := by
      change (IsUnit.liftRight (f.toMonoidHom.domRestrict S) hu s : B) = f s
      exact IsUnit.coe_liftRight _ _ _
    have hDu : D (u : B) = 0 := by
      rw [huval]
      exact hDs
    have hDinv : D ((u⁻¹ : Bˣ) : B) = 0 := by
      apply (hS s.1 s.2).smul_left_cancel.mp
      calc
        algebraMap A B s • D ((u⁻¹ : Bˣ) : B) =
            D (algebraMap A B s * ((u⁻¹ : Bˣ) : B)) -
              ((u⁻¹ : Bˣ) : B) • D (algebraMap A B s) := by
          rw [D.leibniz]
          abel
        _ = algebraMap A B s • 0 := by
          have huu : (u : B) * ((u⁻¹ : Bˣ) : B) = 1 := u.val_inv
          rw [← huval, huu]
          simp [hDu]
    simp only [g]
    change D (IsLocalization.lift hu (IsLocalization.mk' (Localization S) a s)) = 0
    rw [IsLocalization.lift_mk']
    change D (f a * ((u⁻¹ : Bˣ) : B)) = 0
    rw [D.leibniz]
    simp [f, hDinv]
  constructor
  · apply (injective_iff_map_eq_zero _).2
    intro x hx
    change x ∈ LinearMap.ker (mapOfDifferentials
      (R := A) (T := Localization S) (A := B) (B := B)) at hx
    rw [mapOfDifferentials_ker_span (R := A) (T := Localization S)
      (A := B) (B := B) Function.surjective_id] at hx
    refine Submodule.span_induction (p := fun x _ => x = 0) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨b, ⟨t, ht⟩, rfl⟩
      have hb : b = algebraMap (Localization S) B t := by
        simpa using ht
      rw [hb]
      exact hDlocalized (KaehlerDifferential.D A B) t
    · rfl
    · intro x y _ _ hx hy
      rw [hx, hy, add_zero]
    · intro c x _ hx
      rw [hx, smul_zero]
  · exact mapOfDifferentials_surjective (R := A) (T := Localization S)
      (A := B) (B := B) Function.surjective_id

noncomputable def localizationDifferentialMap
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid B) :
    letI : Algebra B (Localization S) := inferInstance
    letI : Algebra A (Localization S) :=
      Algebra.compHom (Localization S) (algebraMap A B)
    letI : SMul B (Localization S) :=
      (inferInstance : Algebra B (Localization S)).toSMul
    letI : SMul A (Localization S) :=
      (inferInstance : Algebra A (Localization S)).toSMul
    letI : IsScalarTower A B (Localization S) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower A A (Localization S) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : SMulCommClass A B (Localization S) :=
      SMulCommClass.of_commMonoid A B (Localization S)
    ModuleOfDifferentials A B →ₗ[B] ModuleOfDifferentials A (Localization S) := by
  letI : Algebra B (Localization S) := inferInstance
  letI : Algebra A (Localization S) :=
    Algebra.compHom (Localization S) (algebraMap A B)
  letI : SMul B (Localization S) :=
    (inferInstance : Algebra B (Localization S)).toSMul
  letI : SMul A (Localization S) :=
    (inferInstance : Algebra A (Localization S)).toSMul
  letI : IsScalarTower A B (Localization S) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A A (Localization S) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : SMulCommClass A B (Localization S) :=
    SMulCommClass.of_commMonoid A B (Localization S)
  exact KaehlerDifferential.map A A B (Localization S)

theorem localize_differentials_top
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid B) :
    letI : Algebra B (Localization S) := inferInstance
    letI : Algebra A (Localization S) :=
      Algebra.compHom (Localization S) (algebraMap A B)
    letI : SMul B (Localization S) :=
      (inferInstance : Algebra B (Localization S)).toSMul
    letI : SMul A (Localization S) :=
      (inferInstance : Algebra A (Localization S)).toSMul
    letI : IsScalarTower A B (Localization S) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower A A (Localization S) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : SMulCommClass A B (Localization S) :=
      SMulCommClass.of_commMonoid A B (Localization S)
    IsLocalizedModule S (localizationDifferentialMap (A := A) (B := B) S) := by
  dsimp [localizationDifferentialMap]
  infer_instance

theorem conormal_differential_exact
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (h : Function.Surjective (algebraMap A B)) :
    Function.Exact (KaehlerDifferential.kerCotangentToTensor R A B)
      (KaehlerDifferential.mapBaseChange R A B) :=
  KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h

theorem conormal_differential_surjective
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (h : Function.Surjective (algebraMap A B)) :
    Function.Surjective (KaehlerDifferential.mapBaseChange R A B) :=
  KaehlerDifferential.mapBaseChange_surjective R A B h

theorem conormal_differential_on_generator
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (x : RingHom.ker (algebraMap A B)) :
    KaehlerDifferential.kerCotangentToTensor R A B (Ideal.toCotangent _ x) =
      1 ⊗ₜ[A] universalDifferential R A x.1 :=
  KaehlerDifferential.kerCotangentToTensor_toCotangent R A B x

theorem conormal_differential_split
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (sectionMap : B →ₐ[R] A)
    (sectionMap_right_inverse :
      ∀ b, algebraMap A B (sectionMap b) = b) :
    ∃ e : ModuleOfDifferentials R B →ₗ[B]
        B ⊗[A] ModuleOfDifferentials R A,
      (KaehlerDifferential.mapBaseChange R A B).comp e = LinearMap.id := by
  let : Algebra B A := sectionMap.toAlgebra
  let : IsScalarTower R B A :=
    IsScalarTower.of_algebraMap_eq' (by
      ext r
      exact (sectionMap.commutes r).symm)
  let f : ModuleOfDifferentials R B →ₗ[B] ModuleOfDifferentials R A :=
    KaehlerDifferential.map R R B A
  let e₀ : ModuleOfDifferentials R A →ₗ[A]
      B ⊗[A] ModuleOfDifferentials R A :=
    (TensorProduct.AlgebraTensorModule.mk A B B (ModuleOfDifferentials R A)) 1
  let e : ModuleOfDifferentials R B →ₗ[B]
      B ⊗[A] ModuleOfDifferentials R A :=
    { toFun := fun x => e₀ (f x)
      map_add' := by
        intro x y
        rw [f.map_add, e₀.map_add]
      map_smul' := by
        intro b x
        change e₀ (f (b • x)) = b • e₀ (f x)
        rw [f.map_smul]
        change e₀ (sectionMap b • f x) = b • e₀ (f x)
        rw [e₀.map_smul]
        rw [← IsScalarTower.algebraMap_smul B (sectionMap b)]
        rw [sectionMap_right_inverse] }
  refine ⟨e, ?_⟩
  ext x
  simp [e, e₀, f]
  rw [show algebraMap B A x = sectionMap x from rfl]
  rw [sectionMap_right_inverse]

noncomputable def differentialModPowerMap
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal S) {n : ℕ} :
    let S' := S ⧸ I ^ (n + 1)
    let T := S ⧸ I ^ n
    letI : Algebra S' T :=
      (Ideal.Quotient.factorPow I (Nat.le_succ n)).toAlgebra
    (T ⊗[S] ModuleOfDifferentials R S) →ₗ[T]
      (T ⊗[S'] ModuleOfDifferentials R S') := by
  let S' := S ⧸ I ^ (n + 1)
  let T := S ⧸ I ^ n
  letI : Algebra S' T :=
    (Ideal.Quotient.factorPow I (Nat.le_succ n)).toAlgebra
  letI : Algebra S T := Algebra.compHom T (algebraMap S S')
  letI : IsScalarTower S S' T := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower S T T := by
    constructor
    intro r t x
    change (algebraMap S T r * t) * x = algebraMap S T r * (t * x)
    rw [mul_assoc]
  let g : ModuleOfDifferentials R S →ₗ[S] ModuleOfDifferentials R S' :=
    KaehlerDifferential.map R R S S'
  let m₁ :=
    @TensorProduct.AlgebraTensorModule.map
      S T T (ModuleOfDifferentials R S) T (ModuleOfDifferentials R S')
      _ _ _ _ _ _ (inferInstance : IsScalarTower S T T) _ _ _ _ _
      (inferInstance : IsScalarTower S T T) _ _
      (LinearMap.id) g
  letI : IsScalarTower S' T T := by
    constructor
    intro r t x
    change (algebraMap S' T r * t) * x = algebraMap S' T r * (t * x)
    rw [mul_assoc]
  let e₀ :=
    @TensorProduct.AlgebraTensorModule.cancelBaseChange
      S S' T T (ModuleOfDifferentials R S')
      _ _ _ _ _ _ _ _ _ _ (inferInstance : IsScalarTower S T T) _ _ _ _
      (inferInstance : IsScalarTower S' T T)
  letI : TensorProduct.CompatibleSMul S S' S' (ModuleOfDifferentials R S') :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective
      (M := S') (N := ModuleOfDifferentials R S')
      (show Function.Surjective (algebraMap S S') from Ideal.Quotient.mk_surjective)
  let m₂ :=
    TensorProduct.AlgebraTensorModule.map
      (R := S') (A := T) (M := T)
      (N := S' ⊗[S] ModuleOfDifferentials R S') (P := T)
      (Q := ModuleOfDifferentials R S')
      (LinearMap.id) (TensorProduct.lidOfCompatibleSMul S S'
        (ModuleOfDifferentials R S')).toLinearMap
  exact m₂.comp (e₀.symm.toLinearMap.comp m₁)

private lemma differential_mem_power_smul
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal S) :
    ∀ m (x : S), x ∈ I ^ (m + 1) →
      universalDifferential R S x ∈ I ^ m • (⊤ : Submodule S (ModuleOfDifferentials R S)) := by
  intro m
  induction m with
  | zero =>
      intro x hx
      simpa only [pow_zero, Ideal.one_eq_top, Submodule.top_smul] using
        (show universalDifferential R S x ∈
            (⊤ : Submodule S (ModuleOfDifferentials R S)) from Submodule.mem_top)
  | succ m ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_
        (fun x y hx hy => by simpa only [map_add] using add_mem hx hy)
      intro a ha b hb
      rw [Derivation.leibniz]
      apply add_mem
      · rw [pow_succ] at ha
        exact Submodule.smul_mem_smul ha Submodule.mem_top
      · rw [pow_succ, mul_comm]
        rw [← Ideal.smul_eq_mul, Submodule.smul_assoc]
        exact Submodule.smul_mem_smul hb (ih a ha)

private lemma differential_map_kernel_le_power_smul
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal S) {n : ℕ} :
    LinearMap.ker (KaehlerDifferential.map R R S (S ⧸ I ^ (n + 1))) ≤
      I ^ n • (⊤ : Submodule S (ModuleOfDifferentials R S)) := by
  classical
  rw [KaehlerDifferential.ker_map_of_surjective R S (S ⧸ I ^ (n + 1))
    Ideal.Quotient.mk_surjective]
  rintro y ⟨x, hx, rfl⟩
  rw [← Finsupp.sum_single x, Finsupp.sum,
    ← Finset.sum_fiberwise_of_maps_to
      (fun _ ↦ Finset.mem_image_of_mem (algebraMap S (S ⧸ I ^ (n + 1))))]
  simp only [map_sum (s := x.support.image (algebraMap S (S ⧸ I ^ (n + 1))))]
  apply sum_mem
  intro c _
  obtain ⟨a, ha⟩ :=
    (Ideal.Quotient.mk_surjective :
      Function.Surjective (algebraMap S (S ⧸ I ^ (n + 1)))) c
  change algebraMap S (S ⧸ I ^ (n + 1)) a = c at ha
  have hsumKer :
      ∑ i ∈ x.support with algebraMap S (S ⧸ I ^ (n + 1)) i = c, x i ∈
        RingHom.ker (algebraMap S (S ⧸ I ^ (n + 1))) := by
    rw [RingHom.mem_ker, map_sum]
    simpa [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply,
      Finsupp.single_apply, ← Finset.sum_filter] using DFunLike.congr_fun hx c
  have hsum :
      ∑ i ∈ x.support with algebraMap S (S ⧸ I ^ (n + 1)) i = c, x i ∈ I ^ (n + 1) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact RingHom.mem_ker.mp hsumKer
  have hdiff (i : S) (hi : i ∈ x.support)
      (hic : algebraMap S (S ⧸ I ^ (n + 1)) i = c) :
      i - a ∈ I ^ (n + 1) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change algebraMap S (S ⧸ I ^ (n + 1)) (i - a) = 0
    rw [map_sub, ha, hic, sub_self]
  simp only [map_sum, Finsupp.linearCombination_single]
  rw [show
      (∑ i ∈ x.support with algebraMap S (S ⧸ I ^ (n + 1)) i = c,
          x i • KaehlerDifferential.D R S i) =
        (∑ i ∈ x.support with algebraMap S (S ⧸ I ^ (n + 1)) i = c,
          x i • KaehlerDifferential.D R S (i - a)) +
        (∑ i ∈ x.support with algebraMap S (S ⧸ I ^ (n + 1)) i = c,
          x i) • KaehlerDifferential.D R S a by
    calc
      (∑ i ∈ x.support with algebraMap S (S ⧸ I ^ (n + 1)) i = c,
          x i • KaehlerDifferential.D R S i) =
          ∑ i ∈ x.support with algebraMap S (S ⧸ I ^ (n + 1)) i = c,
            (x i • KaehlerDifferential.D R S (i - a) +
              x i • KaehlerDifferential.D R S a) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [map_sub, smul_sub, sub_add_cancel]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_smul]]
  apply add_mem
  · apply (I ^ n • (⊤ : Submodule S (ModuleOfDifferentials R S))).sum_mem
    intro i hi
    have hi' : i ∈ x.support ∧ algebraMap S (S ⧸ I ^ (n + 1)) i = c := by
      simpa [Finset.mem_filter] using hi
    exact (I ^ n • (⊤ : Submodule S (ModuleOfDifferentials R S))).smul_mem
      (x i) (differential_mem_power_smul I n (i - a)
        (hdiff i hi'.1 hi'.2))
  · apply (show I ^ (n + 1) • (⊤ : Submodule S (ModuleOfDifferentials R S)) ≤
      I ^ n • (⊤ : Submodule S (ModuleOfDifferentials R S)) from
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)))
    exact Submodule.smul_mem_smul hsum Submodule.mem_top

theorem differential_mod_power_ideal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal S) {n : ℕ} (hn : 1 ≤ n) :
    let S' := S ⧸ I ^ (n + 1)
    let T := S ⧸ I ^ n
    letI : Algebra S' T :=
      (Ideal.Quotient.factorPow I (Nat.le_succ n)).toAlgebra
    Function.Bijective
      (differentialModPowerMap (R := R) (S := S) I (n := n)) := by
  sorry

/-! ## Base change and the diagonal -/

noncomputable def baseChangeDifferentialsEquiv
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S]
    [Algebra R R'] [Algebra R S] :
    letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra.IsPushout R R' S (R' ⊗[R] S) := inferInstance
    letI : Module (R' ⊗[R] S) (R' ⊗[R] ModuleOfDifferentials R S) :=
      KaehlerDifferential.moduleBaseChange' R R' S (R' ⊗[R] S)
    -- Mathlib's tensor-product convention puts the base-change factor first.
    R' ⊗[R] ModuleOfDifferentials R S ≃ₗ[R' ⊗[R] S]
      ModuleOfDifferentials R' (R' ⊗[R] S) := by
  letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra.IsPushout R R' S (R' ⊗[R] S) := inferInstance
  letI : Module (R' ⊗[R] S) (R' ⊗[R] ModuleOfDifferentials R S) :=
    KaehlerDifferential.moduleBaseChange' R R' S (R' ⊗[R] S)
  let e := KaehlerDifferential.tensorKaehlerEquivBase R R' S (R' ⊗[R] S)
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := ?_ }
  intro b x
  exact KaehlerDifferential.map_liftBaseChange_smul R R' S (R' ⊗[R] S) b x

noncomputable def diagonalDifferentialsEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    ModuleOfDifferentials R S ≃ₗ[S]
      (KaehlerDifferential.ideal R S).Cotangent :=
  by
    change (KaehlerDifferential.ideal R S).Cotangent ≃ₗ[S]
      (KaehlerDifferential.ideal R S).Cotangent
    exact LinearEquiv.refl S (KaehlerDifferential.ideal R S).Cotangent

theorem diagonalDifferentialsEquiv_formula
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (a b : S) :
    diagonalDifferentialsEquiv (R := R) (S := S)
        (a • universalDifferential R S b) =
      a • (KaehlerDifferential.ideal R S).toCotangent
        ⟨1 ⊗ₜ[R] b - b ⊗ₜ[R] 1,
          KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R b⟩ := by
  rfl

/-! ## Polynomial rings and finiteness -/

noncomputable def polynomialDifferentialBasis
    (R : Type*) [CommRing R] (n : ℕ) :
    Module.Basis (Fin n) (MvPolynomial (Fin n) R)
      (ModuleOfDifferentials R (MvPolynomial (Fin n) R)) :=
  KaehlerDifferential.mvPolynomialBasis R (Fin n)

theorem polynomialDifferentialBasis_apply
    (R : Type*) [CommRing R] (n : ℕ) (i : Fin n) :
    polynomialDifferentialBasis R n i =
      universalDifferential R (MvPolynomial (Fin n) R) (MvPolynomial.X i) :=
  KaehlerDifferential.mvPolynomialBasis_apply R (Fin n) i

theorem polynomial_differentials_free
    (R : Type*) [CommRing R] (n : ℕ) :
    Module.Free (MvPolynomial (Fin n) R)
      (ModuleOfDifferentials R (MvPolynomial (Fin n) R)) := by
  infer_instance

theorem polynomial_differentials_finite
    (R : Type*) [CommRing R] (n : ℕ) :
    Module.Finite (MvPolynomial (Fin n) R)
      (ModuleOfDifferentials R (MvPolynomial (Fin n) R)) := by
  infer_instance

theorem differentials_finitely_presented
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] :
    Module.FinitePresentation S (ModuleOfDifferentials R S) := by
  infer_instance

theorem differentials_finitely_generated
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] :
    Module.Finite S (ModuleOfDifferentials R S) := by
  infer_instance

end Formalization.Books.Algebra.Unit131
