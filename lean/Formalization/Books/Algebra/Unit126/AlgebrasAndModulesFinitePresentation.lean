import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.Tensor
import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit32.LocallyNilpotent
import Formalization.Books.Algebra.Unit108.PureIdeals

/-!
# Commutative Algebra, Chapter 126: Algebras and modules of finite presentation

This file records the definitions and theorem interfaces in the chapter.  The
localization of a quotient is represented by Mathlib's `Localization` and
`LocalizedModule` constructions, and module witnesses are bundled as
`ModuleCat` objects so that their additive and scalar structures remain part of
the declaration.
-/

open scoped TensorProduct

namespace Formalization.Books.Algebra.Unit126

universe u v w

noncomputable section

/-! ### Quotients and localizations -/

/-- The ring `S⁻¹(R/I)` occurring in the module-construction lemmas. -/
abbrev localizedQuotientRing {R : Type u} [CommRing R]
    (I : Ideal R) (S : Submonoid R) : Type u :=
  Localization (S.map (Ideal.Quotient.mk I))

/-- The localization of `M/IM` at the image of `S`, over `S⁻¹(R/I)`. -/
abbrev localizedQuotientModule {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) (S : Submonoid R) : Type (max u v) :=
  LocalizedModule (S.map (Ideal.Quotient.mk I)) (M ⧸ I • (⊤ : Submodule R M))

/-- The ring map induced by localizing a ring map at a submonoid and its image. -/
noncomputable def localizedRingHom {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (M : Submonoid A) :
    Localization M →+* Localization (M.map f) :=
  IsLocalization.map (Localization (M.map f)) f M.le_comap_map

/-- A surjective ring map induces an equivalence on the local rings at a
prime when its kernel is killed after localizing at the corresponding prime.
The kernel hypothesis is the reusable quotient-cancellation step; it is
deliberately stated independently of finite-presentation or flatness data. -/
theorem localization_atPrime_equiv_of_surjective_of_kernel_torsion
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (q : Ideal B) [hq : q.IsPrime]
    (hf : Function.Surjective f)
    (hkill : ∀ x : A, f x = 0 →
      ∃ s : (q.comap f).primeCompl, (s : A) * x = 0) :
    Nonempty
      (Localization.AtPrime (q.comap f) ≃+*
        Localization.AtPrime q) := by
  have hsub : Submonoid.map f (q.comap f).primeCompl = q.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective f hf q
  let : IsLocalization (Submonoid.map f (q.comap f).primeCompl)
      (Localization.AtPrime q) := by
    rw [hsub]
    infer_instance
  let locMap : Localization.AtPrime (q.comap f) →+*
      Localization.AtPrime q :=
    IsLocalization.map (Localization.AtPrime q) f
      (Submonoid.le_comap_map (q.comap f).primeCompl)
  have hsurj : Function.Surjective locMap := by
    simpa [locMap] using
      (IsLocalization.map_surjective_of_surjective
        (q.comap f).primeCompl (Localization.AtPrime (q.comap f))
        (Localization.AtPrime q) hf)
  have hkerloc : RingHom.ker locMap =
      (RingHom.ker f).map
        (algebraMap A (Localization.AtPrime (q.comap f))) := by
    convert IsLocalization.ker_map (Localization.AtPrime q) f hsub using 1
    congr 1
  have hkerzero : RingHom.ker locMap = ⊥ := by
    rw [hkerloc]
    apply le_antisymm
    · apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      change algebraMap A (Localization.AtPrime (q.comap f)) x ∈
        (⊥ : Ideal (Localization.AtPrime (q.comap f)))
      rw [Ideal.mem_bot]
      apply (IsLocalization.map_eq_zero_iff
        (q.comap f).primeCompl (Localization.AtPrime (q.comap f)) x).2
      change f x = 0 at hx
      exact hkill x hx
    · exact bot_le
  exact ⟨RingEquiv.ofBijective locMap
    ⟨(RingHom.injective_iff_ker_eq_bot locMap).2 hkerzero, hsurj⟩⟩

/-! ### Descent of finite type and finite presentation -/

/-- Finite type descends and ascends along a faithfully flat base change. -/
theorem finite_type_descends {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hff : RingHom.FaithfullyFlat g) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    RingHom.FiniteType f ↔
      RingHom.FiniteType (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  let : Algebra R S := f.toAlgebra
  let : Algebra R R' := g.toAlgebra
  let : Algebra R' (S ⊗[R] R') :=
    Algebra.TensorProduct.rightAlgebra
  constructor
  · intro hf
    exact Formalization.Books.Algebra.Unit14.baseChange_finite_type f g hf
  · intro h
    change RingHom.FiniteType (algebraMap R' (S ⊗[R] R')) at h
    rw [RingHom.finiteType_algebraMap] at h
    let : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
    have hff' : Module.FaithfullyFlat R R' := by
      rw [← RingHom.faithfullyFlat_algebraMap_iff]
      exact hff
    let := hff'
    have h' : Algebra.FiniteType R' (R' ⊗[R] S) :=
      Algebra.FiniteType.equiv h (Algebra.TensorProduct.commRight R R' S).symm
    let := h'
    exact Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat R'

/-- Finite presentation descends and ascends along a faithfully flat base change. -/
theorem finite_presentation_descends {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hff : RingHom.FaithfullyFlat g) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    RingHom.FinitePresentation f ↔
      RingHom.FinitePresentation (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  let : Algebra R S := f.toAlgebra
  let : Algebra R R' := g.toAlgebra
  let : Algebra R' (S ⊗[R] R') :=
    Algebra.TensorProduct.rightAlgebra
  constructor
  · intro hf
    exact Formalization.Books.Algebra.Unit14.baseChange_finite_presentation f g hf
  · intro h
    change RingHom.FinitePresentation (algebraMap R' (S ⊗[R] R')) at h
    rw [RingHom.finitePresentation_algebraMap] at h
    let : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
    have hff' : Module.FaithfullyFlat R R' := by
      rw [← RingHom.faithfullyFlat_algebraMap_iff]
      exact hff
    let := hff'
    let : Algebra.FinitePresentation R' (S ⊗[R] R') := h
    have h' : Algebra.FinitePresentation R' (R' ⊗[R] S) :=
      Algebra.FinitePresentation.equiv (Algebra.TensorProduct.commRight R R' S).symm
    let := h'
    exact Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat R'

/-! ### Finite modules over localized quotients -/

private lemma finite_localized_submodule {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} [AddCommGroup M] [Module R M]
    (hM : Module.Finite (Localization S) (LocalizedModule S M)) :
    ∃ P : Submodule R M, Module.Finite R (P : Type v) ∧
      Function.Bijective (LocalizedModule.map S P.subtype) := by
  classical
  obtain ⟨s, hs⟩ := hM
  have hrep (y : s) : ∃ x : M, ∃ t : S,
      IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) x t = y.1 := by
    obtain ⟨⟨x, t⟩, hx⟩ :=
      IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M) y.1
    exact ⟨x, t, hx⟩
  choose m t hm using hrep
  let sm : Finset M := s.attach.image m
  let P : Submodule R M := Submodule.span R (sm : Set M)
  have hmP (y : s) : m y ∈ P := by
    apply Submodule.subset_span
    change m y ∈ s.attach.image m
    exact Finset.mem_image_of_mem m (Finset.mem_attach s y)
  have hsurj : Function.Surjective (LocalizedModule.map S P.subtype) := by
    apply LinearMap.range_eq_top.mp
    apply le_antisymm
    · exact le_top
    · rw [← hs]
      refine (Submodule.span_le (R := Localization S)).2 ?_
      intro y hy
      let y' : s := ⟨y, hy⟩
      refine ⟨LocalizedModule.mk ⟨m y', hmP y'⟩ (t y'), ?_⟩
      rw [LocalizedModule.map_mk]
      rw [IsLocalizedModule.mk_eq_mk']
      simpa [Submodule.subtype] using hm y'
  exact ⟨P, Module.Finite.span_finset (R := R) sm,
    ⟨LocalizedModule.map_injective S P.subtype P.subtype_injective, hsurj⟩⟩

private lemma finite_presentation_localized_module {R : Type u} [CommRing R]
    (S : Submonoid R) {N : Type (max u v)} [AddCommGroup N]
    [Module (Localization S) N]
    (hN : Module.FinitePresentation (Localization S) N) :
    ∃ P : ModuleCat.{u} R,
      Module.FinitePresentation R (P : Type u) ∧
        Nonempty (LocalizedModule S (P : Type u) ≃ₗ[Localization S] N) := by
  classical
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin (Localization S) N
  obtain ⟨t, ht⟩ := hK
  let bR := Finsupp.linearEquivFunOnFinite R R (Fin n)
  let bT := Finsupp.linearEquivFunOnFinite (Localization S) (Localization S) (Fin n)
  let j0 : (Fin n →₀ R) →ₗ[R] (Fin n →₀ Localization S) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization S))
  let j : (Fin n → R) →ₗ[R] (Fin n → Localization S) :=
    { toFun := fun x i => algebraMap R (Localization S) (x i)
      map_add' := by intro x y; ext i; simp
      map_smul' := by
        intro r x
        ext i
        conv_rhs => rw [Algebra.smul_def]
        simp [Pi.smul_apply, map_mul] }
  let : IsLocalizedModule S j := by
    have h' := IsLocalizedModule.of_linearEquiv_right S j0 bR.symm
    let : IsLocalizedModule S (j0.comp bR.symm.toLinearMap) := h'
    have h := IsLocalizedModule.of_linearEquiv S
      (j0.comp bR.symm.toLinearMap) (bT.restrictScalars R)
    convert h using 1
    apply LinearMap.ext
    intro x
    funext i
    simp [j, j0, bR, bT]
  have hrep (x : t) : ∃ y : Fin n → R, ∃ s : S,
      IsLocalizedModule.mk' j y s = x.1 := by
    obtain ⟨⟨y, s⟩, hy⟩ := IsLocalizedModule.mk'_surjective S j x.1
    exact ⟨y, s, hy⟩
  choose r d hr using hrep
  let L : Submodule R (Fin n → R) := Submodule.span R (Set.range r)
  have hrel : L.localized' (Localization S) S j = K := by
    change (Submodule.span R (Set.range r)).localized' (Localization S) S j = K
    rw [Submodule.localized'_span, ← ht]
    apply le_antisymm
    · refine (Submodule.span_le (R := Localization S)).2 ?_
      rintro y ⟨z, ⟨x, rfl⟩, rfl⟩
      have hzx := IsLocalizedModule.mk'_eq_iff.mp (hr x)
      rw [Submonoid.smul_def, ← algebraMap_smul (Localization S)] at hzx
      rw [hzx]
      exact Submodule.smul_mem _ (algebraMap R (Localization S) (d x))
        (Submodule.subset_span x.2)
    · refine (Submodule.span_le (R := Localization S)).2 ?_
      intro y hy
      let x : t := ⟨y, hy⟩
      have hxy := IsLocalizedModule.mk'_eq_iff.mp (hr x)
      rw [Submonoid.smul_def, ← algebraMap_smul (Localization S)] at hxy
      let u := IsLocalization.map_units (Localization S) (d x)
      have hu : u.unit⁻¹.val • j (r x) = (x : Fin n → Localization S) := by
        rw [hxy]
        have hval : u.unit.val = algebraMap R (Localization S) (d x) := u.unit_spec
        have hs : algebraMap R (Localization S) (d x) •
            (x : Fin n → Localization S) = u.unit.val • (x : Fin n → Localization S) :=
          congrArg (fun z : Localization S => z • (x : Fin n → Localization S)) hval.symm
        rw [hs]
        ext i
        simp only [Pi.smul_apply, smul_eq_mul]
        calc
          u.unit⁻¹.val * (u.unit.val * (x : Fin n → Localization S) i) =
              (u.unit⁻¹.val * u.unit.val) * (x : Fin n → Localization S) i := by
                exact (mul_assoc _ _ _).symm
          _ = (x : Fin n → Localization S) i := by
            simpa only [mul_assoc] using
              (Units.inv_mul_cancel_left u.unit ((x : Fin n → Localization S) i))
      have hgen : j (r x) ∈ Submodule.span (Localization S)
          (j '' Set.range r) := by
        apply Submodule.subset_span
        exact ⟨r x, ⟨x, rfl⟩, rfl⟩
      have hmem := Submodule.smul_mem _ u.unit⁻¹.val hgen
      simpa [x, hu] using hmem
  let q : (Fin n → R) →ₗ[R] ((Fin n → R) ⧸ L) := L.mkQ
  have hq : Function.Surjective q := L.mkQ_surjective
  have hL : L.FG := by
    exact Submodule.fg_span (Set.finite_range r)
  let : Module.FinitePresentation R ((Fin n → R) ⧸ L) :=
    Module.finitePresentation_of_free_of_surjective q hq (by simpa [q] using hL)
  let eQ0 : LocalizedModule S ((Fin n → R) ⧸ L) ≃ₗ[R]
      ((Fin n → Localization S) ⧸ L.localized' (Localization S) S j) :=
    IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S ((Fin n → R) ⧸ L))
      (L.toLocalizedQuotient' (Localization S) S j)
  let eQ : LocalizedModule S ((Fin n → R) ⧸ L) ≃ₗ[Localization S]
      ((Fin n → Localization S) ⧸ L.localized' (Localization S) S j) :=
    eQ0.extendScalarsOfIsLocalization S (Localization S)
  let eK : ((Fin n → Localization S) ⧸ L.localized' (Localization S) S j) ≃ₗ[Localization S]
      ((Fin n → Localization S) ⧸ K) := by
    exact Submodule.quotEquivOfEq _ _ hrel
  refine ⟨ModuleCat.of R ((Fin n → R) ⧸ L), inferInstance, ?_⟩
  exact ⟨eQ.trans (eK.trans e.symm)⟩

private lemma mem_span_of_eq {A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M]
    (t : Finset M) {K : Submodule A M}
    (ht : Submodule.span A (t : Set M) = K) {x : M} (hx : x ∈ K) :
    x ∈ Submodule.span A (t : Set M) := by
  rw [ht]
  exact hx

private lemma quotient_span_sup_ker {R : Type u} [CommRing R]
    (I : Ideal R) {n : ℕ}
    (K : Submodule (R ⧸ I) (Fin n → (R ⧸ I)))
    (t : Finset (Fin n → (R ⧸ I)))
    (ht : Submodule.span (R ⧸ I) (t : Set (Fin n → (R ⧸ I))) = K)
    (q : (Fin n → R) →ₗ[R] (Fin n → (R ⧸ I)))
    {hqker : LinearMap.ker q = I • (⊤ : Submodule R (Fin n → R))}
    (r : t → (Fin n → R)) (hr : ∀ x : t, q (r x) = x.1) :
    Submodule.span R (Set.range r) ⊔ I • (⊤ : Submodule R (Fin n → R)) =
      LinearMap.ker ((K.mkQ.restrictScalars R).comp q) := by
  let L : Submodule R (Fin n → R) := Submodule.span R (Set.range r)
  let T : Submodule R (Fin n → R) := I • (⊤ : Submodule R (Fin n → R))
  let g : (Fin n → (R ⧸ I)) →ₗ[R] ((Fin n → (R ⧸ I)) ⧸ K) :=
    K.mkQ.restrictScalars R
  let f₀ : (Fin n → R) →ₗ[R] ((Fin n → (R ⧸ I)) ⧸ K) := g.comp q
  have hLle : L ≤ (K.restrictScalars R).comap q := by
    change Submodule.span R (Set.range r) ≤ (K.restrictScalars R).comap q
    rw [Submodule.span_le]
    rintro x ⟨y, rfl⟩
    change q (r y) ∈ K.restrictScalars R
    rw [hr y, ← ht]
    exact Submodule.subset_span y.property
  have hker : LinearMap.ker f₀ = (K.restrictScalars R).comap q := by
    ext x
    simp [f₀, g]
  have hsup : L ⊔ T = LinearMap.ker f₀ := by
    apply le_antisymm
    · have hLle' : L ≤ LinearMap.ker f₀ := by
        rw [hker]
        exact hLle
      refine sup_le hLle' ?_
      refine Submodule.smul_le.2 ?_
      intro a ha x hx
      change f₀ (a • x) = 0
      change g (q (a • x)) = 0
      rw [q.map_smul]
      change g ((Ideal.Quotient.mk I a) • q x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_smul, map_zero]
    · rw [hker]
      intro x hx
      have hxK : q x ∈ K := hx
      have hxK' : q x ∈ Submodule.span (R ⧸ I)
          (t : Set (Fin n → (R ⧸ I))) :=
        mem_span_of_eq (A := R ⧸ I) (M := Fin n → (R ⧸ I)) t ht hxK
      have hxK'' : q x ∈ Submodule.span (R ⧸ I)
          (Set.range (fun y : t => y.1)) := by
        simpa [Subtype.range_val_subtype] using hxK'
      obtain ⟨c, hc⟩ :=
        (Submodule.mem_span_range_iff_exists_fun (R ⧸ I) (α := t)
          (M := Fin n → (R ⧸ I)) (v := fun y : t => y.1) (x := q x)).mp hxK''
      let d : t → R := fun y => Quotient.out (c y)
      have hd (y : t) : Ideal.Quotient.mk I (d y) = c y := by
        simp [d]
      let z : Fin n → R := ∑ y, d y • r y
      have hz : q z = q x := by
        calc
          q z = ∑ y, d y • q (r y) := by
            simp only [z, map_sum, LinearMap.map_smul]
          _ = ∑ y, c y • y.1 := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [hr y, ← hd y]
            rfl
          _ = q x := hc
      have hxz : x - z ∈ T := by
        have hxz' : q (x - z) = 0 := by rw [map_sub, hz, sub_self]
        change x - z ∈ I • (⊤ : Submodule R (Fin n → R))
        rw [← hqker]
        exact LinearMap.mem_ker.mpr hxz'
      have hzL : z ∈ L := by
        change z ∈ Submodule.span R (Set.range r)
        apply Submodule.sum_mem
        intro y hy
        exact Submodule.smul_mem _ (d y) (Submodule.subset_span ⟨y, rfl⟩)
      rw [← sub_add_cancel x z]
      simpa [add_comm] using (Submodule.add_mem_sup hzL hxz)
  simpa [L, T, f₀, g] using hsup

private lemma finite_presentation_quotient_lift {R : Type u} [CommRing R]
    (I : Ideal R) {P : Type u} [AddCommGroup P] [Module (R ⧸ I) P]
    (hP : Module.FinitePresentation (R ⧸ I) P) :
    ∃ Q : ModuleCat.{u} R,
      Module.FinitePresentation R (Q : Type u) ∧
        Nonempty
          (((Q : Type u) ⧸ I • (⊤ : Submodule R (Q : Type u))) ≃ₗ[R ⧸ I] P) := by
  classical
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin (R ⧸ I) P
  obtain ⟨t, ht⟩ := hK
  let q : (Fin n → R) →ₗ[R] (Fin n → (R ⧸ I)) :=
    { toFun := fun x i => Ideal.Quotient.mk I (x i)
      map_add' := by intro x y; ext i; simp
      map_smul' := by intro r x; ext i; simp [Algebra.smul_def] }
  have hq : Function.Surjective q := by
    intro x
    choose y hy using fun i => Ideal.Quotient.mk_surjective (x i)
    refine ⟨fun i => y i, ?_⟩
    ext i
    exact hy i
  let r : t → (Fin n → R) := fun x i => Quotient.out (x.1 i)
  have hr (x : t) : q (r x) = x.1 := by
    ext i
    simp [q, r]
  let L : Submodule R (Fin n → R) := Submodule.span R (Set.range r)
  have hL : L.FG := by
    exact Submodule.fg_span (Set.finite_range r)
  let V := (Fin n → R)
  let T : Submodule R V := I • (⊤ : Submodule R V)
  let g : (Fin n → (R ⧸ I)) →ₗ[R] ((Fin n → (R ⧸ I)) ⧸ K) :=
    K.mkQ.restrictScalars R
  let f₀ : V →ₗ[R] ((Fin n → (R ⧸ I)) ⧸ K) := g.comp q
  have hf₀ : Function.Surjective f₀ := by
    intro y
    obtain ⟨z, hz⟩ := K.mkQ_surjective y
    obtain ⟨x, hx⟩ := hq z
    refine ⟨x, ?_⟩
    simp [f₀, g, hx, hz]
  have hsup : L ⊔ T = LinearMap.ker f₀ := by
    simpa [L, T, f₀, g] using
      quotient_span_sup_ker I K t ht q (hqker := by
        apply le_antisymm
        · intro x hx
          have hxq : q x = 0 := LinearMap.mem_ker.mp hx
          have hi : ∀ i, x i ∈ I := by
            intro i
            apply Ideal.Quotient.eq_zero_iff_mem.mp
            simpa [q] using congrFun hxq i
          have heq : x = ∑ i, x i • (Pi.single i 1) := by
            ext i
            rw [Finset.sum_apply, Finset.sum_eq_single i] <;> simp_all
          rw [heq]
          apply Submodule.sum_mem
          intro i hi'
          exact Submodule.smul_mem_smul (hi i) Submodule.mem_top
        · refine Submodule.smul_le.2 ?_
          intro a ha x hx
          apply LinearMap.mem_ker.mpr
          ext i
          simp [q, Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem.mpr ha]) r hr
  let Q : ModuleCat.{u} R := ModuleCat.of R (V ⧸ L)
  let : Module.FinitePresentation R (Q : Type u) := by
    exact Module.finitePresentation_of_free_of_surjective L.mkQ L.mkQ_surjective
      (by
        rw [Submodule.ker_mkQ]
        exact hL)
  have hT : T.map L.mkQ = I • (⊤ : Submodule R (Q : Type u)) := by
    change (I • (⊤ : Submodule R V)).map L.mkQ = I • (⊤ : Submodule R (Q : Type u))
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr L.mkQ_surjective]
  let e₁ : ((Q : Type u) ⧸ I • (⊤ : Submodule R (Q : Type u))) ≃ₗ[R]
      V ⧸ (L ⊔ T) :=
    (Submodule.quotEquivOfEq _ _ hT).symm.trans
      (Submodule.quotientQuotientEquivQuotientSup L T)
  let e₂ : (V ⧸ (L ⊔ T)) ≃ₗ[R] (V ⧸ LinearMap.ker f₀) :=
    Submodule.quotEquivOfEq _ _ hsup
  let e₃ : (V ⧸ LinearMap.ker f₀) ≃ₗ[R] ((Fin n → (R ⧸ I)) ⧸ K) :=
    f₀.quotKerEquivOfSurjective hf₀
  let eR : ((Q : Type u) ⧸ I • (⊤ : Submodule R (Q : Type u))) ≃ₗ[R]
      ((Fin n → (R ⧸ I)) ⧸ K) := e₁.trans (e₂.trans e₃)
  let eA : ((Q : Type u) ⧸ I • (⊤ : Submodule R (Q : Type u))) ≃ₗ[R ⧸ I]
      ((Fin n → (R ⧸ I)) ⧸ K) :=
    eR.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  refine ⟨Q, inferInstance, ?_⟩
  exact ⟨eA.trans e.symm⟩

/-- Finite and finitely presented modules over `S⁻¹(R/I)` descend to `R`. -/
theorem construct_fp_module {R : Type u} [CommRing R] (I : Ideal R) (S : Submonoid R) :
    (∀ M' : ModuleCat.{max u v} (localizedQuotientRing I S),
      Module.Finite (localizedQuotientRing I S) (M' : Type (max u v)) →
        ∃ M : ModuleCat.{max u v} R,
          Module.Finite R (M : Type (max u v)) ∧
            Nonempty
              (localizedQuotientModule I S (M := (M : Type (max u v))) ≃ₗ[
                localizedQuotientRing I S] (M' : Type (max u v)))) ∧
    (∀ M' : ModuleCat.{max u v} (localizedQuotientRing I S),
      Module.FinitePresentation (localizedQuotientRing I S) (M' : Type (max u v)) →
        ∃ M : ModuleCat.{max u v} R,
          Module.FinitePresentation R (M : Type (max u v)) ∧
            Nonempty
              (localizedQuotientModule I S (M := (M : Type (max u v))) ≃ₗ[
                localizedQuotientRing I S] (M' : Type (max u v)))) := by
  constructor
  · intro M' hM'
    let A := R ⧸ I
    let p := S.map (Ideal.Quotient.mk I)
    let T := localizedQuotientRing I S
    let : Module A (M' : Type (max u v)) :=
      Module.compHom (M' : Type (max u v)) (algebraMap A T)
    let : IsScalarTower A T (M' : Type (max u v)) :=
      IsScalarTower.of_compHom A T (M' : Type (max u v))
    let : SMulCommClass T A (M' : Type (max u v)) := by
      constructor
      intro t a x
      change t • ((algebraMap A T a) • x) = a • (t • x)
      rw [← mul_smul, mul_comm, mul_smul]
      rfl
    obtain ⟨s, hs⟩ := hM'
    let P : Submodule A (M' : Type (max u v)) := Submodule.span A (s : Set (M' : Type (max u v)))
    let : Module.Finite A (P : Type (max u v)) := Module.Finite.span_finset (R := A) s
    let : Module R (P : Type (max u v)) := Module.compHom (P : Type (max u v)) (algebraMap R A)
    let : IsScalarTower R A (P : Type (max u v)) :=
      IsScalarTower.of_compHom R A (P : Type (max u v))
    let : Module.Finite R (P : Type (max u v)) := Module.Finite.trans A (P : Type (max u v))
    let f : (P : Type (max u v)) →ₗ[A] (M' : Type (max u v)) := P.subtype
    let : IsLocalizedModule p f := by
      constructor
      · intro x
        have hu := (IsLocalization.map_units T x).map
          ((Module.toModuleEnd A (S := T) (M' : Type (max u v))) :
            T →+* Module.End A (M' : Type (max u v)))
        have hmap :
            (Module.toModuleEnd A (S := T) (M' : Type (max u v)))
                (algebraMap A T (x : A)) =
              algebraMap A (Module.End A (M' : Type (max u v))) (x : A) := by
          ext z
          rfl
        rw [hmap] at hu
        exact hu
      · intro y
        have hy : y ∈ Submodule.span T (s : Set (M' : Type (max u v))) := by
          rw [hs]
          trivial
        obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span p T
          (s : Set (M' : Type (max u v))) y hy
        change c.1 • y ∈ P at hc
        refine ⟨⟨⟨(c.1 : A) • y, hc⟩, c⟩, ?_⟩
        simp [f, Submonoid.smul_def]
      · intro x y hxy
        refine ⟨1, ?_⟩
        apply Subtype.ext
        simpa [f] using hxy
    refine ⟨ModuleCat.of R (P : Type (max u v)), inferInstance, ?_⟩
    have hI : I • (⊤ : Submodule R (P : Type (max u v))) = ⊥ := by
      apply le_antisymm
      · refine Submodule.smul_le.2 ?_
        intro r hr x hx
        have hr0 : algebraMap R A r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
        change (algebraMap R A r) • (x : P) = 0
        rw [hr0, zero_smul]
      · exact bot_le
    let qR :
        (P ⧸ I • (⊤ : Submodule R (P : Type (max u v)))) ≃ₗ[R]
          (P : Type (max u v)) :=
      Submodule.quotEquivOfEqBot _ hI
    let qA :
        (P ⧸ I • (⊤ : Submodule R (P : Type (max u v)))) ≃ₗ[A]
          (P : Type (max u v)) :=
      qR.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    let eQ :
        LocalizedModule p (P ⧸ I • (⊤ : Submodule R (P : Type (max u v)))) ≃ₗ[T]
          LocalizedModule p (P : Type (max u v)) :=
      IsLocalizedModule.mapEquiv p
        (LocalizedModule.mkLinearMap p (P ⧸ I • (⊤ : Submodule R (P : Type (max u v)))))
        (LocalizedModule.mkLinearMap p (P : Type (max u v))) T qA
    let eA : LocalizedModule p (P : Type (max u v)) ≃ₗ[A] (M' : Type (max u v)) :=
      IsLocalizedModule.linearEquiv p (LocalizedModule.mkLinearMap p (P : Type (max u v))) f
    let eT : LocalizedModule p (P : Type (max u v)) ≃ₗ[T] (M' : Type (max u v)) :=
      eA.extendScalarsOfIsLocalization p T
    exact ⟨eQ.trans eT⟩
  · intro M' hM'
    let A := R ⧸ I
    let p := S.map (Ideal.Quotient.mk I)
    let T := localizedQuotientRing I S
    obtain ⟨P, hP, eP⟩ := finite_presentation_localized_module p
      (N := (M' : Type (max u v))) (by simpa [A, p, T] using hM')
    obtain ⟨Q, hQ, eQ⟩ := finite_presentation_quotient_lift I
      (P := (P : Type u)) hP
    obtain ⟨eP⟩ := eP
    obtain ⟨eQ⟩ := eQ
    let Q' : ModuleCat.{max u v} R :=
      ModuleCat.of R (ULift.{v} (Q : Type u))
    let eUL : (ULift.{v} (Q : Type u)) ≃ₗ[R] (Q : Type u) := ULift.moduleEquiv
    have hUL :
        (I • (⊤ : Submodule R (ULift.{v} (Q : Type u)))).map eUL.toLinearMap =
          I • (⊤ : Submodule R (Q : Type u)) := by
      rw [Submodule.map_smul'', Submodule.map_top]
      simp [eUL]
    let eQUL :
        ((Q' : Type (max u v)) ⧸ I • (⊤ : Submodule R (Q' : Type (max u v)))) ≃ₗ[R]
          ((Q : Type u) ⧸ I • (⊤ : Submodule R (Q : Type u))) :=
      Submodule.Quotient.equiv _ _ eUL hUL
    let eQULA :
        ((Q' : Type (max u v)) ⧸ I • (⊤ : Submodule R (Q' : Type (max u v)))) ≃ₗ[R ⧸ I]
          ((Q : Type u) ⧸ I • (⊤ : Submodule R (Q : Type u))) :=
      eQUL.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    let : Module.FinitePresentation R (Q : Type u) := hQ
    let : Module.FinitePresentation R (Q' : Type (max u v)) :=
      Module.FinitePresentation.of_equiv eUL.symm
    let eQA :
        ((Q' : Type (max u v)) ⧸ I • (⊤ : Submodule R (Q' : Type (max u v)))) ≃ₗ[R ⧸ I]
          (P : Type u) := eQULA.trans eQ
    let eQ' : LocalizedModule p
        (Q' ⧸ I • (⊤ : Submodule R (Q' : Type (max u v)))) ≃ₗ[T]
        LocalizedModule p (P : Type u) :=
      IsLocalizedModule.mapEquiv p
        (LocalizedModule.mkLinearMap p
          (Q' ⧸ I • (⊤ : Submodule R (Q' : Type (max u v)))))
        (LocalizedModule.mkLinearMap p (P : Type u)) T eQA
    refine ⟨Q', inferInstance, ?_⟩
    exact ⟨eQ'.trans eP⟩

/-! ### Finite modules after localization -/

/-- Finite and finitely presented localized modules can be lifted to `R`. -/
theorem construct_fp_module_from_localization {R : Type u} [CommRing R]
    (S : Submonoid R) (M : ModuleCat.{v} R) :
    (Module.Finite (Localization S) (LocalizedModule S (M : Type v)) →
      ∃ M' : ModuleCat.{max u v} R,
        Module.Finite R (M' : Type (max u v)) ∧
          ∃ f : (M' : Type (max u v)) →ₗ[R] (M : Type v),
            Function.Bijective (LocalizedModule.map S f)) ∧
    (Module.FinitePresentation (Localization S) (LocalizedModule S (M : Type v)) →
      ∃ M' : ModuleCat.{max u v} R,
        Module.FinitePresentation R (M' : Type (max u v)) ∧
          ∃ f : (M' : Type (max u v)) →ₗ[R] (M : Type v),
            Function.Bijective (LocalizedModule.map S f)) := by
  constructor
  · intro hM
    obtain ⟨P, hP, hbij⟩ := finite_localized_submodule S hM
    let eUL : (ULift.{u} (P : Type v)) ≃ₗ[R] (P : Type v) := ULift.moduleEquiv
    let f : (ULift.{u} (P : Type v)) →ₗ[R] (M : Type v) :=
      P.subtype.comp eUL.toLinearMap
    have hbijP : Function.Bijective
        (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (P : Type v))
          (LocalizedModule.mkLinearMap S (M : Type v)) P.subtype) := by
      rw [IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective]
      exact hbij
    have hbijUL : Function.Bijective
        (IsLocalizedModule.map S
          (LocalizedModule.mkLinearMap S (ULift.{u} (P : Type v)))
          (LocalizedModule.mkLinearMap S (P : Type v)) eUL.toLinearMap) := by
      rw [IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective]
      exact ⟨LocalizedModule.map_injective S eUL.toLinearMap eUL.injective,
        LocalizedModule.map_surjective S eUL.toLinearMap eUL.surjective⟩
    have hcomp :
        IsLocalizedModule.map S
            (LocalizedModule.mkLinearMap S (ULift.{u} (P : Type v)))
            (LocalizedModule.mkLinearMap S (M : Type v)) f =
          IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (P : Type v))
            (LocalizedModule.mkLinearMap S (M : Type v)) P.subtype ∘ₗ
            IsLocalizedModule.map S
              (LocalizedModule.mkLinearMap S (ULift.{u} (P : Type v)))
              (LocalizedModule.mkLinearMap S (P : Type v)) eUL.toLinearMap := by
      exact IsLocalizedModule.map_comp' (S := S)
        (f₀ := LocalizedModule.mkLinearMap S (ULift.{u} (P : Type v)))
        (f₁ := LocalizedModule.mkLinearMap S (P : Type v))
        (f₂ := LocalizedModule.mkLinearMap S (M : Type v)) eUL.toLinearMap P.subtype
    have hbij' : Function.Bijective (LocalizedModule.map S f) := by
      apply (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
        (g₁ := LocalizedModule.mkLinearMap S (ULift.{u} (P : Type v)))
        (g₂ := LocalizedModule.mkLinearMap S (M : Type v)) (l := f)).mp
      rw [hcomp]
      exact hbijP.comp hbijUL
    let : Module.Finite R (ULift.{u} (P : Type v)) :=
      Module.Finite.equiv eUL.symm
    exact ⟨ModuleCat.of R (ULift.{u} (P : Type v)), inferInstance, f, hbij'⟩
  · intro hM
    let : Module.FinitePresentation (Localization S) (LocalizedModule S (M : Type v)) := hM
    obtain ⟨s, hs⟩ := hM
    have hrep (y : s) : ∃ x : (M : Type v), ∃ t : S,
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S (M : Type v)) x t = y.1 := by
      obtain ⟨⟨x, t⟩, hx⟩ := IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S (M : Type v)) y.1
      exact ⟨x, t, hx⟩
    choose r d hr using hrep
    let g : (s →₀ R) →ₗ[R] (M : Type v) := Finsupp.linearCombination R (fun y : s => r y)
    let gL := LocalizedModule.map S g
    have hgen (y : s) : y.1 ∈ LinearMap.range gL := by
      refine ⟨(LocalizedModule.mk (M := s →₀ R) (S := S)
          (Finsupp.single y (1 : R)) (d y) : LocalizedModule S (s →₀ R)), ?_⟩
      rw [LocalizedModule.map_mk]
      rw [IsLocalizedModule.mk_eq_mk']
      rw [Finsupp.linearCombination_single, one_smul]
      exact hr y
    have hrange : LinearMap.range gL =
        (⊤ : Submodule (Localization S) (LocalizedModule S (M : Type v))) := by
      apply top_unique
      rw [← hs.1]
      refine (Submodule.span_le (R := Localization S)).2 ?_
      intro y hy
      exact hgen ⟨y, hy⟩
    have hsurj : Function.Surjective gL := LinearMap.range_eq_top.mp hrange
    let K : Submodule R (s →₀ R) := LinearMap.ker g
    let eK : LocalizedModule S (K : Type _) ≃ₗ[Localization S]
        LinearMap.ker gL := by
      let e₁ := (Submodule.localizedEquiv S K).symm
      let e₂ : K.localized S ≃ₗ[Localization S] LinearMap.ker gL :=
        LinearEquiv.ofEq _ _
          (LinearMap.localized'_ker_eq_ker_localizedMap
            (S := Localization S) (p := S)
            (f := LocalizedModule.mkLinearMap S (s →₀ R))
            (f' := LocalizedModule.mkLinearMap S (M : Type v)) g)
      exact e₁.trans e₂
    have hKfg : (LinearMap.ker gL).FG :=
      Module.FinitePresentation.fg_ker
        (M := LocalizedModule S (s →₀ R))
        (N := LocalizedModule S (M : Type v)) gL hsurj
    let : Module.Finite (Localization S) (LinearMap.ker gL) :=
      Module.Finite.of_fg hKfg
    let : Module.Finite (Localization S) (LocalizedModule S (K : Type _)) :=
      Module.Finite.equiv eK.symm
    obtain ⟨P, hP, hPbij⟩ := finite_localized_submodule S
        (M := (K : Type _)) (inferInstance : Module.Finite (Localization S)
          (LocalizedModule S (K : Type _)))
    let K' : Submodule R (s →₀ R) := P.map K.subtype
    have hPfg : P.FG := (Module.Finite.iff_fg).mp hP
    have hK'fg : K'.FG := by
      change (P.map K.subtype).FG
      exact hPfg.map K.subtype
    have hKle : K' ≤ K := by
      change P.map K.subtype ≤ K
      rintro x ⟨p, hp, rfl⟩
      exact p.property
    have hKleG : K' ≤ LinearMap.ker g := by
      simpa [K] using hKle
    let q : (s →₀ R) →ₗ[R] ((s →₀ R) ⧸ K') := K'.mkQ
    have hq : Function.Surjective q := K'.mkQ_surjective
    let f : ((s →₀ R) ⧸ K') →ₗ[R] (M : Type v) :=
      K'.liftQ g hKleG
    have hfq : f ∘ₗ q = g := by
      ext x
      simp [f, q]
    let : Module.FinitePresentation R ((s →₀ R) ⧸ K') :=
      Module.finitePresentation_of_free_of_surjective q hq (by simpa [q] using hK'fg)
    let qL := LocalizedModule.map S q
    let fL := LocalizedModule.map S f
    have hcomp : fL ∘ₗ qL = gL := by
      ext x
      induction x using LocalizedModule.induction_on with
      | _ x t =>
        change LocalizedModule.map S f (LocalizedModule.map S q (LocalizedModule.mk x t)) =
          LocalizedModule.map S g (LocalizedModule.mk x t)
        rw [LocalizedModule.map_mk, LocalizedModule.map_mk]
        have h := congrArg (fun h : (s →₀ R) →ₗ[R] (M : Type v) => h x) hfq
        simpa [LinearMap.comp_apply] using
          congrArg (fun z : (M : Type v) => LocalizedModule.mk z t) h
    have hqLsurj : Function.Surjective qL := LocalizedModule.map_surjective S q hq
    have hkcomm : (LinearMap.ker gL).subtype ∘ₗ eK =
          LocalizedModule.map S K.subtype := by
      have hkcommR :
          ((LinearMap.ker gL).subtype ∘ₗ eK).restrictScalars R =
            (LocalizedModule.map S K.subtype).restrictScalars R := by
        exact IsLocalizedModule.linearMap_ext (S := S)
          (f := LocalizedModule.mkLinearMap S (K : Type _))
          (f' := LocalizedModule.mkLinearMap S (s →₀ R))
          (g := ((LinearMap.ker gL).subtype ∘ₗ eK).restrictScalars R)
          (g' := (LocalizedModule.map S K.subtype).restrictScalars R)
          (by
            ext x
            simp only [LinearMap.comp_apply]
            simp [eK, Submodule.localizedEquiv]
            change ((Submodule.localizedEquiv S K).symm (LocalizedModule.mk x 1)).1 =
              LocalizedModule.mk (K.subtype x) 1
            have he : (Submodule.localizedEquiv S K).symm (LocalizedModule.mk x 1) =
                K.toLocalized (p := S) x := by
              apply (Submodule.localizedEquiv S K).injective
              simp [Submodule.localizedEquiv]
            rw [he]
            rfl)
      ext x
      exact congrArg (fun h => h x) hkcommR
    have hqP (p : P) : q (K.subtype p) = 0 := by
      change Submodule.Quotient.mk (K.subtype p) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨p, p.property, rfl⟩
    have hqP' : qL ∘ₗ LocalizedModule.map S K.subtype ∘ₗ
            LocalizedModule.map S P.subtype = 0 := by
      ext x
      induction x using LocalizedModule.induction_on with
      | _ x t =>
        simp only [LinearMap.comp_apply]
        rw [LocalizedModule.map_mk, LocalizedModule.map_mk, LocalizedModule.map_mk]
        have hxq : q (K.subtype (P.subtype x)) = 0 := hqP x
        rw [hxq]
        simp
    have hfLsurj : Function.Surjective fL := by
      intro y
      obtain ⟨x, hx⟩ := hsurj y
      refine ⟨qL x, ?_⟩
      calc
        fL (qL x) = (fL ∘ₗ qL) x := rfl
        _ = gL x := congrArg (fun h => h x) hcomp
        _ = y := hx
    have hfLinj : Function.Injective fL := by
      intro z z' hzz
      obtain ⟨x, hx⟩ := hqLsurj z
      obtain ⟨x', hx'⟩ := hqLsurj z'
      have hgx : gL x = fL (qL x) := by
        simpa [LinearMap.comp_apply] using congrArg (fun h => h x) hcomp.symm
      have hgx' : gL x' = fL (qL x') := by
        simpa [LinearMap.comp_apply] using congrArg (fun h => h x') hcomp.symm
      have hxg : gL (x - x') = 0 := by
        calc
          gL (x - x') = gL x - gL x' := by rw [map_sub]
          _ = fL (qL x) - fL (qL x') := by rw [hgx, hgx']
          _ = fL z - fL z' := by rw [hx, hx']
          _ = 0 := sub_eq_zero.mpr hzz
      let y : LinearMap.ker gL := Subtype.mk (x - x') hxg
      obtain ⟨p, hp⟩ := hPbij.2 (eK.symm y)
      have hpx : LocalizedModule.map S K.subtype
          (LocalizedModule.map S P.subtype p) = x - x' := by
        rw [← hkcomm, LinearMap.comp_apply, hp]
        simp [y]
      have hz0 : qL (x - x') = 0 := by
        rw [← hpx]
        simpa [LinearMap.comp_apply] using congrArg (fun z => z p) hqP'
      have hqeq : qL x = qL x' :=
        sub_eq_zero.mp (by simpa using hz0)
      calc
        z = qL x := hx.symm
        _ = qL x' := hqeq
        _ = z' := hx'
    exact ⟨ModuleCat.of R ((s →₀ R) ⧸ K'), inferInstance, f, hfLinj, hfLsurj⟩

/-! ### The stalk case -/

/-- The preceding localization lifting result specialized to a prime stalk. -/
theorem construct_fp_module_from_stalk {R : Type u} [CommRing R]
    (p : Ideal R) [hp : p.IsPrime] (M : ModuleCat.{v} R) :
    (Module.Finite (Localization.AtPrime p)
        (LocalizedModule p.primeCompl (M : Type v)) →
      ∃ M' : ModuleCat.{max u v} R,
        Module.Finite R (M' : Type (max u v)) ∧
          ∃ f : (M' : Type (max u v)) →ₗ[R] (M : Type v),
            Function.Bijective (LocalizedModule.map p.primeCompl f)) ∧
    (Module.FinitePresentation (Localization.AtPrime p)
        (LocalizedModule p.primeCompl (M : Type v)) →
      ∃ M' : ModuleCat.{max u v} R,
        Module.FinitePresentation R (M' : Type (max u v)) ∧
          ∃ f : (M' : Type (max u v)) →ₗ[R] (M : Type v),
            Function.Bijective (LocalizedModule.map p.primeCompl f)) := by
  constructor
  · intro hM
    exact (construct_fp_module_from_localization p.primeCompl M).1 hM
  · intro hM
    exact (construct_fp_module_from_localization p.primeCompl M).2 hM

/-! ### Local isomorphisms and spreading out -/

private noncomputable def awayToAtPrime {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] (a : R) (ha : a ∉ p) :
    Localization.Away a →ₐ[R] Localization.AtPrime p :=
  IsLocalization.Away.liftAlgHom a (f := Algebra.ofId R (Localization.AtPrime p))
    (IsLocalization.map_units (Localization.AtPrime p) (⟨a, ha⟩ : p.primeCompl))

private lemma exists_away_lift_algHom {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FinitePresentation R A]
    (p : Ideal R) [p.IsPrime] (f : A →ₐ[R] Localization.AtPrime p) :
    ∃ (a : R) (ha : a ∉ p) (g : A →ₐ[R] Localization.Away a),
      (awayToAtPrime p a ha).comp g = f := by
  classical
  obtain ⟨n, π, hπ, hker⟩ :=
    (inferInstance : Algebra.FinitePresentation R A).out
  obtain ⟨s, hs⟩ := hker
  have hrep (i : Fin n) : ∃ b : R, ∃ d : p.primeCompl,
      IsLocalization.mk' (Localization.AtPrime p) b d = f (π (MvPolynomial.X i)) := by
    obtain ⟨⟨b, d⟩, h⟩ :=
      IsLocalization.mk'_surjective p.primeCompl (f (π (MvPolynomial.X i)))
    exact ⟨b, d, h⟩
  choose b d hd using hrep
  let a₀ : R := ∏ i : Fin n, (d i : R)
  have ha₀ : a₀ ∉ p := by
    exact p.primeCompl.prod_mem fun i _ ↦ (d i).property
  let c (i : Fin n) : R := ∏ j ∈ Finset.univ.erase i, (d j : R)
  have ha₀_eq (i : Fin n) : a₀ = (d i : R) * c i := by
    change (∏ j : Fin n, (d j : R)) =
      (d i : R) * ∏ j ∈ Finset.univ.erase i, (d j : R)
    exact (Finset.mul_prod_erase Finset.univ (fun j : Fin n ↦ (d j : R))
      (Finset.mem_univ i)).symm
  let z (i : Fin n) : Localization.Away a₀ :=
    IsLocalization.mk' (Localization.Away a₀) (b i * c i)
      (⟨a₀, Submonoid.mem_powers a₀⟩ : Submonoid.powers a₀)
  let g₀ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away a₀ :=
    MvPolynomial.aeval z
  have hcomp₀ : (awayToAtPrime p a₀ ha₀).comp g₀ = f.comp π := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, g₀, MvPolynomial.aeval_X, z]
    rw [← (IsLocalization.map_units (Localization.AtPrime p)
      (⟨a₀, ha₀⟩ : p.primeCompl)).mul_right_inj]
    have hzspec := congrArg (awayToAtPrime p a₀ ha₀)
      (IsLocalization.mk'_spec' (Localization.Away a₀) (b i * c i)
        (⟨a₀, Submonoid.mem_powers a₀⟩ : Submonoid.powers a₀))
    simp only [map_mul, AlgHom.commutes] at hzspec
    rw [hzspec]
    change algebraMap R (Localization.AtPrime p) (b i) *
        algebraMap R (Localization.AtPrime p) (c i) =
      algebraMap R (Localization.AtPrime p) a₀ * f (π (MvPolynomial.X i))
    rw [ha₀_eq i, map_mul, ← hd i]
    have hspec := IsLocalization.mk'_spec' (Localization.AtPrime p) (b i) (d i)
    rw [← hspec]
    ring
  have hzero (x : s) : awayToAtPrime p a₀ ha₀ (g₀ x.1) = 0 := by
    have hx : π x.1 = 0 := by
      exact (RingHom.mem_ker.mp (hs.le (Ideal.subset_span x.2)))
    have h := congrArg (fun h : MvPolynomial (Fin n) R →ₐ[R]
      Localization.AtPrime p ↦ h x.1) hcomp₀
    simpa only [AlgHom.comp_apply, hx, map_zero] using h
  have hfrac (x : s) : ∃ y : R, ∃ k : ℕ,
      IsLocalization.mk' (Localization.Away a₀) y
        (⟨a₀ ^ k, (Submonoid.powers a₀).pow_mem (Submonoid.mem_powers a₀) k⟩ :
          Submonoid.powers a₀) = g₀ x.1 := by
    obtain ⟨y, t, ht⟩ := IsLocalization.exists_mk'_eq
      (Submonoid.powers a₀) (g₀ x.1)
    obtain ⟨k, hk⟩ := t.property
    refine ⟨y, k, ?_⟩
    have ht' : t = (⟨a₀ ^ k,
        (Submonoid.powers a₀).pow_mem (Submonoid.mem_powers a₀) k⟩ :
          Submonoid.powers a₀) :=
      Subtype.ext hk.symm
    rw [← ht']
    exact ht
  choose y k hy using hfrac
  have hnumzero (x : s) : algebraMap R (Localization.AtPrime p) (y x) = 0 := by
    have h := hzero x
    rw [← hy x] at h
    have hspec := congrArg (awayToAtPrime p a₀ ha₀)
      (IsLocalization.mk'_spec' (Localization.Away a₀) (y x)
        (⟨a₀ ^ k x, (Submonoid.powers a₀).pow_mem (Submonoid.mem_powers a₀) (k x)⟩ :
          Submonoid.powers a₀))
    simp only [map_mul, h, mul_zero] at hspec
    simpa [awayToAtPrime] using hspec.symm
  have hkill (x : s) : ∃ t : p.primeCompl, (t : R) * y x = 0 :=
    (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) (y x)).mp
      (hnumzero x)
  choose t ht using hkill
  let t₀ : R := ∏ x : s, (t x : R)
  have ht₀ : t₀ ∉ p := p.primeCompl.prod_mem fun x _ ↦ (t x).property
  let a : R := t₀ * a₀
  have ha : a ∉ p := (inferInstance : p.IsPrime).mul_notMem ht₀ ha₀
  have ha₀_dvd : a₀ ∣ a := ⟨t₀, by simp [a, mul_comm]⟩
  let j : Localization.Away a₀ →ₐ[R] Localization.Away a :=
    IsLocalization.Away.liftAlgHom a₀ (f := Algebra.ofId R (Localization.Away a))
      (IsLocalization.Away.isUnit_of_dvd a ha₀_dvd)
  let gP : MvPolynomial (Fin n) R →ₐ[R] Localization.Away a := j.comp g₀
  have hrels : RingHom.ker π.toRingHom ≤ RingHom.ker gP.toRingHom := by
    rw [← hs, Ideal.span_le]
    intro x hx
    change j (g₀ x) = 0
    let x' : s := ⟨x, hx⟩
    rw [← hy x']
    have hdiv : (t x' : R) ∣ t₀ := by
      exact Finset.dvd_prod_of_mem (fun z : s ↦ (t z : R)) (Finset.mem_univ x')
    obtain ⟨q, hq⟩ := hdiv
    have hya : a * y x' = 0 := by
      calc
        a * y x' = (t₀ * a₀) * y x' := rfl
        _ = ((t x' : R) * q * a₀) * y x' := by rw [hq]
        _ = q * a₀ * ((t x' : R) * y x') := by ring
        _ = 0 := by rw [ht x']; simp
    have hyA : algebraMap R (Localization.Away a) (y x') = 0 := by
      apply (IsLocalization.map_eq_zero_iff (Submonoid.powers a)
        (Localization.Away a) (y x')).2
      exact ⟨(⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a), hya⟩
    have hu : IsUnit (j (algebraMap R (Localization.Away a₀) (a₀ ^ k x'))) :=
      (IsLocalization.map_units (Localization.Away a₀)
        (⟨a₀ ^ k x', (Submonoid.powers a₀).pow_mem
          (Submonoid.mem_powers a₀) (k x')⟩ : Submonoid.powers a₀)).map j
    rw [← hu.mul_right_inj]
    rw [mul_zero]
    have hspec := congrArg j
      (IsLocalization.mk'_spec' (Localization.Away a₀) (y x')
        (⟨a₀ ^ k x', (Submonoid.powers a₀).pow_mem
          (Submonoid.mem_powers a₀) (k x')⟩ : Submonoid.powers a₀))
    simpa only [map_mul, AlgHom.commutes, hyA] using hspec
  let g : A →ₐ[R] Localization.Away a :=
    AlgHom.liftOfSurjective π hπ gP hrels
  refine ⟨a, ha, g, ?_⟩
  rw [← AlgHom.cancel_right hπ]
  rw [AlgHom.comp_assoc, AlgHom.liftOfSurjective_comp]
  rw [← hcomp₀]
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, gP, g₀, MvPolynomial.aeval_X]
  have hj : (awayToAtPrime p a ha).comp j = awayToAtPrime p a₀ ha₀ := by
    apply Localization.algHom_ext (Submonoid.powers a₀)
    ext
  exact DFunLike.congr_fun hj (z i)

private noncomputable def awayToAtPrimeOver
    {R : Type u} {B : Type w} [CommRing R] [CommRing B] [Algebra R B]
    (p : Ideal B) [p.IsPrime] (b : B) (hb : b ∉ p) :
    Localization.Away b →ₐ[R] Localization.AtPrime p :=
  (awayToAtPrime p b hb).restrictScalars R

private lemma exists_away_lift_algHom_over
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.FinitePresentation R A]
    (p : Ideal B) [p.IsPrime] (f : A →ₐ[R] Localization.AtPrime p) :
    ∃ (b : B) (hb : b ∉ p) (g : A →ₐ[R] Localization.Away b),
      (awayToAtPrimeOver p b hb).comp g = f := by
  let BA := B ⊗[R] A
  let : Algebra B BA := Algebra.TensorProduct.leftAlgebra
  let : Algebra.FinitePresentation B BA := by infer_instance
  let h : BA →ₐ[B] Localization.AtPrime p :=
    (AlgHom.liftEquiv R B A (Localization.AtPrime p)) f
  obtain ⟨b, hb, G, hG⟩ := exists_away_lift_algHom p h
  let g : A →ₐ[R] Localization.Away b :=
    (G.restrictScalars R).comp Algebra.TensorProduct.includeRight
  refine ⟨b, hb, g, ?_⟩
  apply AlgHom.ext
  intro x
  have hGx := DFunLike.congr_fun hG
    (Algebra.TensorProduct.includeRight x)
  change awayToAtPrime p b hb (G (Algebra.TensorProduct.includeRight x)) = f x
  calc
    awayToAtPrime p b hb (G (Algebra.TensorProduct.includeRight x)) =
        h (Algebra.TensorProduct.includeRight x) := hGx
    _ = f x := by
      rw [Algebra.TensorProduct.includeRight_apply]
      change ((AlgHom.liftEquiv R B A (Localization.AtPrime p)) f)
        (1 ⊗ₜ[R] x) = f x
      rw [AlgHom.liftEquiv_tmul, one_smul]

private theorem local_isomorphism_with_selector
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Ideal R) (q : Ideal S) [hp : p.IsPrime] [hq : q.IsPrime]
    (hpq : p = q.comap f) :
    letI : Algebra R S := f.toAlgebra
    RingHom.FinitePresentation f →
      Function.Bijective (Localization.localRingHom p q f hpq) →
        ∃ a : R, a ∉ p ∧
          ∃ C : CommAlgCat (Localization.Away a),
            ∃ E :
                Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) ≃ₐ[
                  Localization.Away a] (Localization.Away a × (C : Type u)),
              ∃ e : Localization
                  (Algebra.algebraMapSubmonoid S (Submonoid.powers a)),
                e ∉ q.map (algebraMap S
                  (Localization
                    (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))) ∧
                  E e = (1, 0) := by
  let : Algebra R S := f.toAlgebra
  intro hfp hbij
  let : Algebra.FinitePresentation R S := hfp
  let F : Localization.AtPrime p →ₐ[R] Localization.AtPrime q :=
    Localization.localAlgHom p q (Algebra.ofId R S) hpq
  have hFbij : Function.Bijective F := hbij
  let E : Localization.AtPrime p ≃ₐ[R] Localization.AtPrime q :=
    AlgEquiv.ofBijective F hFbij
  let locS : S →ₐ[R] Localization.AtPrime q :=
    IsScalarTower.toAlgHom R S (Localization.AtPrime q)
  obtain ⟨a, ha, g, hg⟩ :=
    exists_away_lift_algHom p (E.symm.toAlgHom.comp locS)
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let U := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let eU : Rp ⊗[R] S ≃ₐ[Rp] U :=
    Localization.tensorRightAlgEquiv p.primeCompl S
  let h : S →ₐ[R] Rp := E.symm.toAlgHom.comp locS
  let rP : U →ₐ[Rp] Rp := (h.liftEquiv R Rp S Rp).comp eU.symm.toAlgHom
  have hrPsurj : Function.Surjective rP := by
    intro x
    refine ⟨algebraMap Rp U x, ?_⟩
    exact rP.commutes x
  let M : Submonoid S := Algebra.algebraMapSubmonoid S p.primeCompl
  have hMq : M ≤ q.primeCompl := by
    rintro _ ⟨x, hx, rfl⟩ hmem
    change f x ∈ q at hmem
    exact hx (by rw [hpq]; exact hmem)
  let : Algebra U Sq :=
    IsLocalization.localizationAlgebraOfSubmonoidLe U Sq M q.primeCompl hMq
  let : IsScalarTower S U Sq :=
    IsLocalization.localization_isScalarTower_of_submonoid_le U Sq M q.primeCompl hMq
  let : IsLocalization (q.primeCompl.map (algebraMap S U)) Sq :=
    IsLocalization.isLocalization_of_submonoid_le U Sq M q.primeCompl hMq
  have hUrP : E.toRingEquiv.toRingHom.comp rP.toRingHom = algebraMap U Sq := by
    apply IsLocalization.ringHom_ext M
    ext x
    have heinv : eU.symm (algebraMap S U x) = (1 : Rp) ⊗ₜ[R] x := by
      apply eU.injective
      rw [eU.apply_symm_apply]
      change (algebraMap S
        (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))) x =
          Localization.tensorRightAlgEquiv p.primeCompl S ((1 : Rp) ⊗ₜ[R] x)
      exact (Localization.tensorRightAlgEquiv_apply_one_tmul p.primeCompl x).symm
    change E (rP (algebraMap S U x)) = algebraMap U Sq (algebraMap S U x)
    rw [show rP (algebraMap S U x) = h x by simp [rP, heinv]]
    rw [← IsScalarTower.algebraMap_apply S U Sq]
    have hloc : locS x = algebraMap S Sq x := rfl
    simp only [h, AlgHom.comp_apply, hloc]
    exact E.apply_symm_apply _
  have hrPcomp : rP.toRingHom.comp (algebraMap Rp U) = RingHom.id Rp := by
    ext x
    exact rP.commutes x
  have hrPfp : RingHom.FinitePresentation rP.toRingHom := by
    apply RingHom.FinitePresentation.of_comp_finiteType (algebraMap Rp U)
    · rw [hrPcomp]
      exact RingHom.FinitePresentation.of_bijective Function.bijective_id
    · apply RingHom.FiniteType.of_finitePresentation
      let V := Rp ⊗[R] S
      have hV : RingHom.FinitePresentation (algebraMap Rp V) :=
        RingHom.finitePresentation_algebraMap.mpr
          (inferInstance : Algebra.FinitePresentation Rp V)
      have he : RingHom.FinitePresentation eU.toRingEquiv.toRingHom :=
        RingHom.FinitePresentation.of_bijective eU.bijective
      have hc := he.comp hV
      convert hc using 1
      ext x
      symm
      change eU (algebraMap Rp (Rp ⊗[R] S) x) = algebraMap Rp U x
      exact eU.commutes x
  let : Algebra U Rp := rP.toRingHom.toAlgebra
  let : Algebra.FinitePresentation U Rp := hrPfp
  let I : Ideal U := RingHom.ker (algebraMap U Rp)
  have hIfg : I.FG := by
    simpa [I] using
      Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId U Rp) hrPsurj
  let eUr : Rp ≃ₐ[U] Sq :=
    { E.toRingEquiv with
      commutes' := fun x ↦ DFunLike.congr_fun hUrP x }
  let qE : (U ⧸ I) ≃ₐ[U] Rp :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId U Rp) hrPsurj
  have hIpure : Ideal.Pure I := by
    have hflat : Module.Flat U Sq := IsLocalization.flat Sq
      (q.primeCompl.map (algebraMap S U))
    let : Module.Flat U Sq := hflat
    exact Module.Flat.of_linearEquiv ((qE.trans eUr).toLinearEquiv)
  obtain ⟨e, he, hIe⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg I hIfg).mp
      (Ideal.isIdempotentElem_of_pure I)
  let A := Localization.Away a
  let T := Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a))
  let eT : A ⊗[R] S ≃ₐ[A] T :=
    Localization.tensorRightAlgEquiv (Submonoid.powers a) S
  let r : T →ₐ[A] A := (g.liftEquiv R A S A).comp eT.symm.toAlgHom
  have har : Submonoid.powers a ≤ p.primeCompl := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact fun hpow ↦ ha (hp.mem_of_pow_mem n hpow)
  have hTM : Algebra.algebraMapSubmonoid S (Submonoid.powers a) ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, har hx, rfl⟩
  let : Algebra T U := IsLocalization.localizationAlgebraOfSubmonoidLe T U
    (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) M hTM
  let : IsScalarTower S T U :=
    IsLocalization.localization_isScalarTower_of_submonoid_le T U
      (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) M hTM
  let : IsLocalization (M.map (algebraMap S T)) U :=
    IsLocalization.isLocalization_of_submonoid_le T U
      (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) M hTM
  let : Algebra A Rp := IsLocalization.localizationAlgebraOfSubmonoidLe A Rp
    (Submonoid.powers a) p.primeCompl har
  let : IsScalarTower R A Rp :=
    IsLocalization.localization_isScalarTower_of_submonoid_le A Rp
      (Submonoid.powers a) p.primeCompl har
  let : IsLocalization (p.primeCompl.map (algebraMap R A)) Rp :=
    IsLocalization.isLocalization_of_submonoid_le A Rp
      (Submonoid.powers a) p.primeCompl har
  have hrbase (d : R) : r (algebraMap S T (algebraMap R S d)) =
      algebraMap R A d := by
    rw [← IsScalarTower.algebraMap_apply R S T]
    rw [IsScalarTower.algebraMap_apply R A T]
    exact r.commutes (algebraMap R A d)
  have hmap : Submonoid.map r.toRingHom (M.map (algebraMap S T)) =
      p.primeCompl.map (algebraMap R A) := by
    ext x
    constructor
    · rintro ⟨y, ⟨s, ⟨d, hd, hds⟩, hsy⟩, hyx⟩
      refine ⟨d, hd, ?_⟩
      subst y
      subst s
      subst x
      exact (hrbase d).symm
    · rintro ⟨d, hd, rfl⟩
      refine ⟨algebraMap S T (algebraMap R S d), ?_, ?_⟩
      · exact ⟨algebraMap R S d, ⟨d, hd, rfl⟩, rfl⟩
      · exact hrbase d
  let lr : U →+* Rp := IsLocalization.map Rp r.toRingHom
    (hmap.symm ▸ (M.map (algebraMap S T)).le_comap_map)
  have hlr : lr = rP.toRingHom := by
    apply IsLocalization.ringHom_ext M
    ext x
    have haway : IsScalarTower.toAlgHom R A Rp = awayToAtPrime p a ha := by
      apply Localization.algHom_ext (Submonoid.powers a)
      ext
    have her : (algebraMap A Rp).comp g.toRingHom = h.toRingHom := by
      ext y
      change algebraMap A Rp (g y) = h y
      have hy := DFunLike.congr_fun haway (g y)
      change algebraMap A Rp (g y) = awayToAtPrime p a ha (g y) at hy
      rw [hy]
      simpa [h] using DFunLike.congr_fun hg y
    have hrS : r (algebraMap S T x) = g x := by
      have heinv : eT.symm (algebraMap S T x) = (1 : A) ⊗ₜ[R] x := by
        apply eT.injective
        rw [eT.apply_symm_apply]
        change (algebraMap S
          (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)))) x =
            Localization.tensorRightAlgEquiv (Submonoid.powers a) S
              ((1 : A) ⊗ₜ[R] x)
        exact (Localization.tensorRightAlgEquiv_apply_one_tmul
          (Submonoid.powers a) x).symm
      simp [r, heinv]
    have hrPS : rP (algebraMap S U x) = h x := by
      have heinv : eU.symm (algebraMap S U x) = (1 : Rp) ⊗ₜ[R] x := by
        apply eU.injective
        rw [eU.apply_symm_apply]
        change (algebraMap S
          (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))) x =
            Localization.tensorRightAlgEquiv p.primeCompl S ((1 : Rp) ⊗ₜ[R] x)
        exact (Localization.tensorRightAlgEquiv_apply_one_tmul p.primeCompl x).symm
      simp [rP, heinv]
    have hxTU : algebraMap S U x = algebraMap T U (algebraMap S T x) :=
      IsScalarTower.algebraMap_apply S T U x
    change lr (algebraMap S U x) = rP (algebraMap S U x)
    calc
      lr (algebraMap S U x) = lr (algebraMap T U (algebraMap S T x)) :=
        congrArg lr hxTU
      _ = algebraMap A Rp (r (algebraMap S T x)) := IsLocalization.map_eq _ _
      _ = algebraMap A Rp (g x) := congrArg (algebraMap A Rp) hrS
      _ = h x := DFunLike.congr_fun her x
      _ = rP (algebraMap S U x) := hrPS.symm
  let J : Ideal T := RingHom.ker r.toRingHom
  have hJU : J.map (algebraMap T U) = I := by
    rw [← IsLocalization.ker_map Rp r.toRingHom hmap]
    change RingHom.ker lr = I
    rw [hlr]
    rfl
  have hrsurj : Function.Surjective r := by
    intro y
    refine ⟨algebraMap A T y, ?_⟩
    exact r.commutes y
  have hrcomp : r.toRingHom.comp (algebraMap A T) = RingHom.id A := by
    ext y
    exact r.commutes y
  have hrfp : RingHom.FinitePresentation r.toRingHom := by
    apply RingHom.FinitePresentation.of_comp_finiteType (algebraMap A T)
    · rw [hrcomp]
      exact RingHom.FinitePresentation.of_bijective Function.bijective_id
    · apply RingHom.FiniteType.of_finitePresentation
      let V := A ⊗[R] S
      have hV : RingHom.FinitePresentation (algebraMap A V) :=
        RingHom.finitePresentation_algebraMap.mpr
          (inferInstance : Algebra.FinitePresentation A V)
      have hefp : RingHom.FinitePresentation eT.toRingEquiv.toRingHom :=
        RingHom.FinitePresentation.of_bijective eT.bijective
      have hc := hefp.comp hV
      convert hc using 1
      ext y
      symm
      change eT (algebraMap A (A ⊗[R] S) y) = algebraMap A T y
      exact eT.commutes y
  let : Algebra T A := r.toRingHom.toAlgebra
  let : Algebra.FinitePresentation T A := hrfp
  have hJfg : J.FG := by
    have hfg :=
      Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId T A) hrsurj
    have halg : (Algebra.ofId T A).toRingHom = r.toRingHom := rfl
    rw [halg] at hfg
    simpa [J] using hfg
  let N : Submonoid T := M.map (algebraMap S T)
  obtain ⟨x, t, ht⟩ := IsLocalization.exists_mk'_eq N e
  let K : Ideal T := Ideal.span ({x} : Set T)
  have hspan : Ideal.span ({e} : Set U) = K.map (algebraMap T U) := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    apply le_antisymm
    · rw [Ideal.span_singleton_le_span_singleton]
      have hut : IsUnit (algebraMap T U (t : T)) := IsLocalization.map_units U t
      have hspec : e * algebraMap T U (t : T) = algebraMap T U x := by
        rw [← ht]
        simp
      refine ⟨↑hut.unit⁻¹, ?_⟩
      apply hut.mul_right_cancel
      rw [hspec]
      simp [mul_assoc]
    · rw [Ideal.span_singleton_le_span_singleton]
      refine ⟨algebraMap T U (t : T), ?_⟩
      have hspec : e * algebraMap T U (t : T) = algebraMap T U x := by
        rw [← ht]
        simp
      exact hspec.symm
  have hJKU : J.map (algebraMap T U) = K.map (algebraMap T U) := by
    rw [hJU, hIe]
    change Ideal.span ({e} : Set U) = K.map (algebraMap T U)
    exact hspan
  have N_base (m : T) (hm : m ∈ N) :
      ∃ d : R, d ∉ p ∧ m = algebraMap R T d := by
    rcases hm with ⟨s, hs, rfl⟩
    rcases hs with ⟨d, hd, rfl⟩
    refine ⟨d, hd, ?_⟩
    exact (IsScalarTower.algebraMap_apply R S T d).symm
  obtain ⟨s, hsJ⟩ := hJfg
  have hclearJ (y : s) : ∃ d : R, d ∉ p ∧
      algebraMap R T d * y.1 ∈ K := by
    have hyJ : y.1 ∈ J := by
      rw [← hsJ]
      exact Ideal.subset_span y.2
    have hyU : algebraMap T U y.1 ∈ K.map (algebraMap T U) := by
      rw [← hJKU]
      exact Ideal.mem_map_of_mem (algebraMap T U) hyJ
    obtain ⟨m, hmN, hmy⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff N U K y.1).mp hyU
    obtain ⟨d, hd, hmd⟩ := N_base m hmN
    refine ⟨d, hd, ?_⟩
    simpa [hmd] using hmy
  choose dJ hdJ hdyJ using hclearJ
  let cJ : R := ∏ y : s, dJ y
  have hcJ : cJ ∉ p := p.primeCompl.prod_mem fun y _ ↦ hdJ y
  have hcyJ (y : s) : algebraMap R T cJ * y.1 ∈ K := by
    have hdiv : dJ y ∣ cJ :=
      Finset.dvd_prod_of_mem (fun z : s ↦ dJ z) (Finset.mem_univ y)
    obtain ⟨v, hv⟩ := hdiv
    rw [hv, map_mul]
    rw [mul_assoc]
    have hh := K.mul_mem_left (algebraMap R T v) (hdyJ y)
    convert hh using 1; ring
  have hxU : algebraMap T U x ∈ J.map (algebraMap T U) := by
    rw [hJKU]
    exact Ideal.mem_map_of_mem (algebraMap T U) (Ideal.subset_span (Set.mem_singleton x))
  obtain ⟨mK, hmKN, hmKx⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff N U J x).mp hxU
  obtain ⟨dK, hdK, hmK⟩ := N_base mK hmKN
  have hdKx : algebraMap R T dK * x ∈ J := by simpa [hmK] using hmKx
  obtain ⟨d₀, hd₀, htbase⟩ := N_base (t : T) t.property
  have hspecU : algebraMap T U x = algebraMap T U (algebraMap R T d₀) * e := by
    have hspec := IsLocalization.mk'_spec' U x t
    rw [ht, htbase] at hspec
    exact hspec.symm
  let w : T := x * x - algebraMap R T d₀ * x
  have hwU : algebraMap T U w = 0 := by
    simp only [w, map_sub, map_mul]
    rw [hspecU]
    calc
      algebraMap T U (algebraMap R T d₀) * e *
            (algebraMap T U (algebraMap R T d₀) * e) -
          algebraMap T U (algebraMap R T d₀) *
            (algebraMap T U (algebraMap R T d₀) * e) =
          (algebraMap T U (algebraMap R T d₀)) ^ 2 * (e * e - e) := by ring
      _ = 0 := by rw [he.eq]; simp
  obtain ⟨mI, hmIw⟩ :=
    (IsLocalization.map_eq_zero_iff N U w).mp hwU
  obtain ⟨dI, hdI, hmI⟩ := N_base (mI : T) mI.property
  have hdIw : algebraMap R T dI * w = 0 := by simpa [hmI] using hmIw
  let c : R := d₀ * dI * cJ * dK
  have hc : c ∉ p := by
    exact hp.mul_notMem (hp.mul_notMem (hp.mul_notMem hd₀ hdI) hcJ) hdK
  let B := Localization.Away (algebraMap R T c)
  let D := Localization.Away (algebraMap R A c)
  have hd₀c : d₀ ∣ c := ⟨dI * cJ * dK, by simp [c, mul_assoc]⟩
  have hdIc : dI ∣ c := ⟨d₀ * cJ * dK, by simp [c]; ring⟩
  have hcJc : cJ ∣ c := ⟨d₀ * dI * dK, by simp [c]; ring⟩
  have hdKc : dK ∣ c := ⟨d₀ * dI * cJ, by simp [c]; ring⟩
  have hu₀ : IsUnit (algebraMap T B (algebraMap R T d₀)) :=
    IsLocalization.Away.isUnit_of_dvd (algebraMap R T c)
      (map_dvd (algebraMap R T) hd₀c)
  have huI : IsUnit (algebraMap T B (algebraMap R T dI)) :=
    IsLocalization.Away.isUnit_of_dvd (algebraMap R T c)
      (map_dvd (algebraMap R T) hdIc)
  have huJ : IsUnit (algebraMap T B (algebraMap R T cJ)) :=
    IsLocalization.Away.isUnit_of_dvd (algebraMap R T c)
      (map_dvd (algebraMap R T) hcJc)
  have huK : IsUnit (algebraMap T B (algebraMap R T dK)) :=
    IsLocalization.Away.isUnit_of_dvd (algebraMap R T c)
      (map_dvd (algebraMap R T) hdKc)
  have hwB : algebraMap T B w = 0 := by
    apply (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R T c)) B w).2
    refine ⟨(⟨algebraMap R T c, Submonoid.mem_powers _⟩ :
      Submonoid.powers (algebraMap R T c)), ?_⟩
    obtain ⟨v, hv⟩ := hdIc
    change algebraMap R T c * w = 0
    rw [hv, map_mul]
    calc
      (algebraMap R T dI * algebraMap R T v) * w =
          algebraMap R T v * (algebraMap R T dI * w) := by ring
      _ = 0 := by rw [hdIw]; simp
  let z : B := algebraMap T B x * ↑hu₀.unit⁻¹
  have hzidem : IsIdempotentElem z := by
    have hrel : algebraMap T B x * algebraMap T B x =
        algebraMap T B (algebraMap R T d₀) * algebraMap T B x := by
      exact sub_eq_zero.mp (by simpa [w] using hwB)
    change z * z = z
    simp only [z]
    calc
      (algebraMap T B x * ↑hu₀.unit⁻¹) *
          (algebraMap T B x * ↑hu₀.unit⁻¹) =
          (algebraMap T B x * algebraMap T B x) *
            (↑hu₀.unit⁻¹ * ↑hu₀.unit⁻¹) := by ring
      _ = (algebraMap T B (algebraMap R T d₀) * algebraMap T B x) *
            (↑hu₀.unit⁻¹ * ↑hu₀.unit⁻¹) := by rw [hrel]
      _ = algebraMap T B x * ↑hu₀.unit⁻¹ := by
        have hu : algebraMap T B (algebraMap R T d₀) * ↑hu₀.unit⁻¹ = 1 := by
          change (hu₀.unit : B) * ↑hu₀.unit⁻¹ = 1
          simp
        rw [show (algebraMap T B (algebraMap R T d₀) * algebraMap T B x) *
              (↑hu₀.unit⁻¹ * ↑hu₀.unit⁻¹) =
            (algebraMap T B (algebraMap R T d₀) * ↑hu₀.unit⁻¹) *
              (algebraMap T B x * ↑hu₀.unit⁻¹) by ring]
        rw [hu, one_mul]
  have hJBK : J.map (algebraMap T B) = K.map (algebraMap T B) := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap, ← hsJ, Ideal.span_le]
      intro y hy
      let ys : s := ⟨y, hy⟩
      have hh : algebraMap T B (algebraMap R T cJ) * algebraMap T B y ∈
          K.map (algebraMap T B) := by
        rw [← map_mul]
        exact Ideal.mem_map_of_mem (algebraMap T B) (hcyJ ys)
      exact (Ideal.unit_mul_mem_iff_mem _ huJ).mp hh
    · rw [Ideal.map_le_iff_le_comap]
      change Ideal.span ({x} : Set T) ≤ _
      rw [Ideal.span_le]
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      have hh : algebraMap T B (algebraMap R T dK) * algebraMap T B x ∈
          J.map (algebraMap T B) := by
        rw [← map_mul]
        exact Ideal.mem_map_of_mem (algebraMap T B) hdKx
      exact (Ideal.unit_mul_mem_iff_mem _ huK).mp hh
  have hKz : K.map (algebraMap T B) = Ideal.span ({z} : Set B) := by
    change (Ideal.span ({x} : Set T)).map (algebraMap T B) = _
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    apply le_antisymm
    · rw [Ideal.span_singleton_le_span_singleton]
      refine ⟨algebraMap T B (algebraMap R T d₀), ?_⟩
      simp only [z]
      have hu : (↑hu₀.unit⁻¹ : B) * algebraMap T B (algebraMap R T d₀) = 1 := by
        change (↑hu₀.unit⁻¹ : B) * (hu₀.unit : B) = 1
        simp
      rw [mul_assoc, hu, mul_one]
    · rw [Ideal.span_singleton_le_span_singleton]
      exact ⟨↑hu₀.unit⁻¹, rfl⟩
  have hJBz : J.map (algebraMap T B) = Ideal.span ({z} : Set B) := hJBK.trans hKz
  have hrbase' (d : R) : r (algebraMap R T d) = algebraMap R A d := by
    rw [IsScalarTower.algebraMap_apply R S T]
    exact hrbase d
  have hpowmap : Submonoid.map r.toRingHom
      (Submonoid.powers (algebraMap R T c)) =
        Submonoid.powers (algebraMap R A c) := by
    rw [Submonoid.map_powers]
    apply congrArg Submonoid.powers
    change r (algebraMap R T c) = algebraMap R A c
    exact hrbase' c
  let : IsLocalization
      ((Submonoid.powers (algebraMap R T c)).map r.toRingHom) D :=
    hpowmap.symm ▸ (inferInstance :
      IsLocalization (Submonoid.powers (algebraMap R A c)) D)
  let rB : B →+* D := IsLocalization.map D r.toRingHom
    ((Submonoid.powers (algebraMap R T c)).le_comap_of_map_le
      (le_of_eq hpowmap))
  have hrBsurj : Function.Surjective rB := by
    simpa [rB] using
      (IsLocalization.map_surjective_of_surjective
        (Submonoid.powers (algebraMap R T c)) B D hrsurj)
  have hkerB : RingHom.ker rB = Ideal.span ({z} : Set B) := by
    change RingHom.ker (IsLocalization.map D r.toRingHom
      ((Submonoid.powers (algebraMap R T c)).le_comap_of_map_le
        (le_of_eq hpowmap))) = _
    rw [IsLocalization.ker_map D r.toRingHom hpowmap]
    exact hJBz
  let : Algebra B D := rB.toAlgebra
  let qB : (B ⧸ RingHom.ker rB) ≃ₐ[B] D :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId B D) hrBsurj
  let qZ : (B ⧸ Ideal.span ({z} : Set B)) ≃ₐ[B] D :=
    (Ideal.quotientEquivAlgOfEq B hkerB.symm).trans qB
  let Cbig := B ⧸ Ideal.span ({1 - z} : Set B)
  let prodQ : B ≃ₐ[B] (B ⧸ Ideal.span ({z} : Set B)) × Cbig :=
    AlgEquiv.prodQuotientOfIsIdempotentElem B hzidem hzidem.one_sub
      (by ring) (by rw [mul_sub, mul_one, hzidem.eq, sub_self])
  let prodE : B ≃+* D × Cbig := prodQ.toRingEquiv.trans
    (RingEquiv.prodCongr qZ.toRingEquiv (RingEquiv.refl Cbig))
  have hAB (y : A) : algebraMap A B y = algebraMap T B (algebraMap A T y) :=
    IsScalarTower.algebraMap_apply A T B y
  have hunitAc : IsUnit (algebraMap A B (algebraMap R A c)) := by
    rw [hAB, ← IsScalarTower.algebraMap_apply R A T]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap R T c)
  let sB : D →ₐ[A] B := IsLocalization.Away.liftAlgHom (algebraMap R A c)
    (f := Algebra.ofId A B) hunitAc
  have hrBs : rB.comp sB.toRingHom = RingHom.id D := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R A c))
    ext y
    change rB (sB (algebraMap A D y)) = algebraMap A D y
    rw [sB.commutes]
    change rB (algebraMap T B (algebraMap A T y)) = algebraMap A D y
    change IsLocalization.map D r.toRingHom _
      (algebraMap T B (algebraMap A T y)) = algebraMap A D y
    rw [IsLocalization.map_eq]
    have hry : r.toRingHom (algebraMap A T y) = y := r.commutes y
    rw [hry]
  let : Algebra D B := sB.toRingHom.toAlgebra
  let prodED : B ≃ₐ[D] D × Cbig :=
    { prodE with
      commutes' := by
        intro y
        ext
        · change (prodE (sB y)).1 = y
          simp only [prodE, RingEquiv.trans_apply, RingEquiv.prodCongr_apply,
            prodQ, qZ]
          change qB (Ideal.quotientEquivAlgOfEq B hkerB.symm
            (Ideal.Quotient.mk (Ideal.span ({z} : Set B)) (sB y))) = y
          change rB (sB y) = y
          exact DFunLike.congr_fun hrBs y
        · rfl }
  let b : R := a * c
  have hb : b ∉ p := hp.mul_notMem ha hc
  let L := Localization.Away b
  let LB := Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers b))
  let : IsLocalization.Away b D := by
    exact IsLocalization.Away.mul' A D a c
  have hTc : algebraMap R T c = algebraMap S T (algebraMap R S c) :=
    IsScalarTower.algebraMap_apply R S T c
  let : IsLocalization.Away (algebraMap S T (algebraMap R S c)) B := by
    rw [← hTc]
    infer_instance
  let : IsLocalization.Away (algebraMap R S a) T := by
    simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
    infer_instance
  let : IsLocalization.Away
      (algebraMap R S a * algebraMap R S c) B :=
    IsLocalization.Away.mul' T B (algebraMap R S a) (algebraMap R S c)
  let : IsLocalization.Away (algebraMap R S b) B := by
    change IsLocalization.Away (algebraMap R S (a * c)) B
    rw [map_mul]
    infer_instance
  let eD : L ≃ₐ[R] D :=
    IsLocalization.algEquiv (Submonoid.powers b) L D
  let eB : LB ≃ₐ[S] B :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid S (Submonoid.powers b)) LB B
  let V := A ⊗[R] S
  let : Small.{u} V := Algebra.FiniteType.small (R := A) (S := V)
  let : Small.{u} T := small_of_surjective eT.surjective
  let : Small.{u} B := small_of_surjective Localization.mkHom_surjective
  let : Small.{u} Cbig := small_of_surjective Ideal.Quotient.mk_surjective
  let : Algebra L Cbig :=
    ((algebraMap D Cbig).comp eD.toRingEquiv.toRingHom).toAlgebra
  let dC : D →+* Cbig := algebraMap D Cbig
  let lC : L →+* Cbig := algebraMap L Cbig
  let eC : Shrink Cbig ≃ₐ[L] Cbig := Shrink.algEquiv L Cbig
  let finalRing : @RingEquiv LB (L × Shrink Cbig)
      OreLocalization.instSemiring.toNonAssocSemiring.toDistrib.toMul
      Prod.instSemiring.toNonAssocSemiring.toDistrib.toMul
      OreLocalization.instSemiring.toNonAssocSemiring.toDistrib.toAdd
      Prod.instSemiring.toNonAssocSemiring.toDistrib.toAdd :=
    { eB.toEquiv.trans <| prodED.toEquiv.trans <|
        Equiv.prodCongr eD.symm.toEquiv eC.symm.toEquiv with
      map_mul' := by
        intro x y
        ext <;> simp
      map_add' := by
        intro x y
        ext <;> simp }
  have hfinalBase : finalRing.toRingHom.comp (algebraMap L LB) =
      algebraMap L (L × Shrink Cbig) := by
    apply IsLocalization.ringHom_ext (R := R) (S := L) (Submonoid.powers b)
    apply RingHom.ext
    intro y
    have hLBR : algebraMap L LB (algebraMap R L y) =
        algebraMap S LB (algebraMap R S y) := by
      rw [← IsScalarTower.algebraMap_apply R L LB]
      rw [← IsScalarTower.algebraMap_apply R S LB]
    have hDB : algebraMap S B (algebraMap R S y) =
        algebraMap D B (algebraMap R D y) := by
      change algebraMap S B (algebraMap R S y) = sB (algebraMap R D y)
      rw [show algebraMap R D y = algebraMap A D (algebraMap R A y) by
        rw [← IsScalarTower.algebraMap_apply R A D]]
      rw [sB.commutes]
      rw [← IsScalarTower.algebraMap_apply R A B]
      rw [← IsScalarTower.algebraMap_apply R S B]
    have hDC : dC (algebraMap R D y) = lC (algebraMap R L y) := by
      change dC (algebraMap R D y) = dC (eD (algebraMap R L y))
      rw [eD.commutes]
    change finalRing (algebraMap L LB (algebraMap R L y)) = _
    rw [hLBR]
    change (eD.symm (prodED (eB (algebraMap S LB (algebraMap R S y)))).1,
      eC.symm (prodED (eB (algebraMap S LB (algebraMap R S y)))).2) = _
    rw [eB.commutes, hDB, prodED.commutes]
    apply Prod.ext
    · exact eD.symm.commutes y
    · change eC.symm (dC (algebraMap R D y)) = _
      rw [hDC]
      exact eC.symm.commutes (algebraMap R L y)
  let C : CommAlgCat L := CommAlgCat.of L (Shrink Cbig)
  let finalE : LB ≃ₐ[L] L × Shrink Cbig :=
    { finalRing with
      commutes' := fun y ↦ DFunLike.congr_fun hfinalBase y }
  have heI : e ∈ I := by
    rw [hIe]
    exact Ideal.mem_span_singleton_self e
  have hrPe : rP e = 0 := by
    exact heI
  have hSqe : algebraMap U Sq e = 0 := by
    have heq := DFunLike.congr_fun hUrP e
    change E (rP e) = algebraMap U Sq e at heq
    rw [hrPe, map_zero] at heq
    exact heq.symm
  let tToSq : T →+* Sq := (algebraMap U Sq).comp (algebraMap T U)
  have htx : tToSq x = 0 := by
    change algebraMap U Sq (algebraMap T U x) = 0
    rw [hspecU, map_mul, hSqe, mul_zero]
  have hfc : f c ∉ q := by
    intro h
    apply hc
    rw [hpq]
    exact h
  have htcsq : tToSq (algebraMap R T c) = algebraMap S Sq (f c) := by
    change algebraMap U Sq (algebraMap T U (algebraMap R T c)) =
      algebraMap S Sq (f c)
    rw [show algebraMap R T c = algebraMap S T (f c) by
      exact IsScalarTower.algebraMap_apply R S T c]
    rw [← IsScalarTower.algebraMap_apply S T U]
    rw [← IsScalarTower.algebraMap_apply S U Sq]
  have hcunit : IsUnit (tToSq (algebraMap R T c)) := by
    rw [htcsq]
    exact IsLocalization.map_units Sq (⟨f c, hfc⟩ : q.primeCompl)
  let bToSq : B →+* Sq := IsLocalization.Away.lift (algebraMap R T c) hcunit
  have hbz : bToSq z = 0 := by
    change bToSq (algebraMap T B x * ↑hu₀.unit⁻¹) = 0
    rw [map_mul, IsLocalization.Away.lift_eq, htx, zero_mul]
  have hbsel : bToSq (1 - z) = 1 := by
    rw [map_sub, map_one, hbz, sub_zero]
  have hrBz : rB z = 0 := by
    rw [← RingHom.mem_ker, hkerB]
    exact Ideal.mem_span_singleton_self z
  have hprodSel : prodED (1 - z) = (1, 0) := by
    apply Prod.ext
    · change rB (1 - z) = 1
      rw [map_sub, map_one, hrBz, sub_zero]
    · change Ideal.Quotient.mk (Ideal.span ({1 - z} : Set B)) (1 - z) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton_self (1 - z))
  let sel : LB := eB.symm (1 - z)
  have hfinalSel : finalE sel = (1, 0) := by
    change finalRing (eB.symm (1 - z)) = (1, 0)
    change (eD.symm (prodED (eB (eB.symm (1 - z)))).1,
      eC.symm (prodED (eB (eB.symm (1 - z)))).2) = (1, 0)
    rw [eB.apply_symm_apply, hprodSel]
    simp
  let lbToSq : LB →+* Sq := bToSq.comp eB.toRingEquiv.toRingHom
  have hlbbase (y : S) : lbToSq (algebraMap S LB y) = algebraMap S Sq y := by
    change bToSq (eB (algebraMap S LB y)) = algebraMap S Sq y
    rw [eB.commutes]
    change bToSq (algebraMap T B (algebraMap S T y)) = algebraMap S Sq y
    rw [IsLocalization.Away.lift_eq]
    change algebraMap U Sq (algebraMap T U (algebraMap S T y)) =
      algebraMap S Sq y
    rw [← IsScalarTower.algebraMap_apply S T U]
    rw [← IsScalarTower.algebraMap_apply S U Sq]
  have hqle : q.map (algebraMap S LB) ≤
      (IsLocalRing.maximalIdeal Sq).comap lbToSq := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    change lbToSq (algebraMap S LB y) ∈ IsLocalRing.maximalIdeal Sq
    rw [hlbbase]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Sq q y).2 hy
  have hsel : sel ∉ q.map (algebraMap S LB) := by
    intro h
    have hm := hqle h
    change lbToSq sel ∈ IsLocalRing.maximalIdeal Sq at hm
    have hlbsel : lbToSq sel = 1 := by
      change bToSq (eB (eB.symm (1 - z))) = 1
      rw [eB.apply_symm_apply]
      exact hbsel
    rw [hlbsel] at hm
    exact (IsLocalRing.maximalIdeal.isMaximal Sq).ne_top
      ((IsLocalRing.maximalIdeal Sq).eq_top_iff_one.mpr hm)
  exact ⟨b, hb, C, finalE, sel, hsel, hfinalSel⟩

/-- A finitely presented map which is an isomorphism at a prime spreads out
to a product decomposition after inverting an element away from that prime. -/
theorem local_isomorphism {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Ideal R) (q : Ideal S) [hp : p.IsPrime] [hq : q.IsPrime]
    (hpq : p = q.comap f) :
    letI : Algebra R S := f.toAlgebra
    RingHom.FinitePresentation f →
      Function.Bijective (Localization.localRingHom p q f hpq) →
        ∃ a : R, a ∉ p ∧
          ∃ C : CommAlgCat (Localization.Away a),
            Nonempty
              (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers a)) ≃ₐ[
                Localization.Away a]
                (Localization.Away a × (C : Type u))) := by
  let : Algebra R S := f.toAlgebra
  intro hfp hbij
  obtain ⟨a, ha, C, E, _e, _he, _hE⟩ :=
    local_isomorphism_with_selector f p q hpq hfp hbij
  exact ⟨a, ha, C, ⟨E⟩⟩

/-- An isomorphism between finite-presentation local rings spreads out to an
isomorphism after inverting elements outside the corresponding primes. -/
theorem isomorphic_local_rings {R : Type u} {S : Type v} {S' : Type w}
    [CommRing R] [CommRing S] [CommRing S']
    (f : R →+* S) (f' : R →+* S') (q : Ideal S) (q' : Ideal S')
    [hq : q.IsPrime] [hq' : q'.IsPrime] :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R S' := f'.toAlgebra
    RingHom.FinitePresentation f →
      RingHom.FinitePresentation f' →
        Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime q') →
          ∃ g : S, g ∉ q ∧
            ∃ g' : S', g' ∉ q' ∧
              Nonempty (Localization.Away g ≃ₐ[R] Localization.Away g') := by
  let : Algebra R S := f.toAlgebra
  let : Algebra R S' := f'.toAlgebra
  intro hf hf' hE
  let : Algebra.FinitePresentation R S := hf
  let : Algebra.FinitePresentation R S' := hf'
  let Sq := Localization.AtPrime q
  let Sq' := Localization.AtPrime q'
  let E : Sq ≃ₐ[R] Sq' := hE.some
  let locS : S →ₐ[R] Sq := IsScalarTower.toAlgHom R S Sq
  obtain ⟨d, hd, φ, hφ⟩ :=
    exists_away_lift_algHom_over q' (E.toAlgHom.comp locS)
  let T := Localization.Away d
  have hpow : Submonoid.powers d ≤ q'.primeCompl := by
    exact Submonoid.powers_le.mpr hd
  let : Algebra T Sq' :=
    IsLocalization.localizationAlgebraOfSubmonoidLe T Sq'
      (Submonoid.powers d) q'.primeCompl hpow
  let : IsScalarTower S' T Sq' :=
    IsLocalization.localization_isScalarTower_of_submonoid_le T Sq'
      (Submonoid.powers d) q'.primeCompl hpow
  let : IsScalarTower R T Sq' := by
    apply IsScalarTower.of_algebraMap_eq'
    rw [IsScalarTower.algebraMap_eq R S' Sq']
    rw [IsScalarTower.algebraMap_eq R S' T]
    rw [← RingHom.comp_assoc]
    rw [← IsScalarTower.algebraMap_eq S' T Sq']
  let : IsLocalization
      (Submonoid.map (algebraMap S' T) q'.primeCompl) Sq' :=
    IsLocalization.isLocalization_of_submonoid_le T Sq'
      (Submonoid.powers d) q'.primeCompl hpow
  let tToSq' : T →ₐ[R] Sq' := IsScalarTower.toAlgHom R T Sq'
  have haway : awayToAtPrimeOver (R := R) (B := S') q' d hd = tToSq' := by
    apply Localization.algHom_ext (Submonoid.powers d)
    ext x
    rfl
  have hdisj : Disjoint (Submonoid.powers d : Set S') (q' : Set S') := by
    exact Set.disjoint_left.mpr fun x hx hq'x ↦
      (show x ∈ q'.primeCompl from hpow hx) hq'x
  let Q : Ideal T := q'.map (algebraMap S' T)
  have hQprime : Q.IsPrime := by
    exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers d) T q' hq' hdisj
  let _ : Q.IsPrime := hQprime
  have hQunder : Q.under S' = q' := by
    exact IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers d) T hq' hdisj
  let _ : IsLocalRing Sq := IsLocalization.AtPrime.isLocalRing Sq q
  let _ : IsLocalRing Sq' := IsLocalization.AtPrime.isLocalRing Sq' q'
  have hmaxUnder : (IsLocalRing.maximalIdeal Sq').under T = Q := by
    apply (IsLocalization.orderEmbedding (Submonoid.powers d) T).injective
    change ((IsLocalRing.maximalIdeal Sq').under T).under S' = Q.under S'
    rw [hQunder]
    apply Ideal.ext
    intro x
    change algebraMap T Sq' (algebraMap S' T x) ∈
        IsLocalRing.maximalIdeal Sq' ↔ x ∈ q'
    rw [← IsScalarTower.algebraMap_apply S' T Sq']
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff Sq' q' x
  let N : Submonoid T := Submonoid.map (algebraMap S' T) q'.primeCompl
  have hNQ : N ≤ Q.primeCompl := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submonoid.mem_map.mp hx
    intro hxy
    exact hy (by
      rw [← hQunder]
      exact hxy)
  have hQunit (x : T) (hx : x ∈ Q.primeCompl) :
      IsUnit (algebraMap T Sq' x) := by
    have hn : algebraMap T Sq' x ∉ IsLocalRing.maximalIdeal Sq' := by
      intro h
      exact hx (by
        rw [← hmaxUnder]
        exact h)
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Classical.not_not] using hn
  let : IsLocalization.AtPrime Sq' Q :=
    IsLocalization.of_le N Q.primeCompl hNQ hQunit
  have hEmax : (IsLocalRing.maximalIdeal Sq').comap E.toRingEquiv.toRingHom =
      IsLocalRing.maximalIdeal Sq := by
    apply Ideal.ext
    intro x
    change E x ∈ IsLocalRing.maximalIdeal Sq' ↔
      x ∈ IsLocalRing.maximalIdeal Sq
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    apply not_congr
    constructor
    · intro hx
      have h := hx.map E.symm.toRingEquiv.toRingHom
      simpa using h
    · intro hx
      exact hx.map E.toRingEquiv.toRingHom
  have hqφ : q = Q.comap φ.toRingHom := by
    apply Ideal.ext
    intro x
    change x ∈ q ↔ φ x ∈ Q
    rw [← hmaxUnder]
    change x ∈ q ↔ algebraMap T Sq' (φ x) ∈ IsLocalRing.maximalIdeal Sq'
    change x ∈ q ↔ tToSq' (φ x) ∈ IsLocalRing.maximalIdeal Sq'
    rw [← DFunLike.congr_fun haway (φ x)]
    have hφx : awayToAtPrimeOver (R := R) (B := S') q' d hd (φ x) = E (locS x) :=
      DFunLike.congr_fun hφ x
    rw [hφx]
    change x ∈ q ↔ algebraMap S Sq x ∈
      (IsLocalRing.maximalIdeal Sq').comap E.toRingEquiv.toRingHom
    rw [hEmax]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Sq q x).symm
  have hφfp : RingHom.FinitePresentation φ.toRingHom := by
    apply RingHom.FinitePresentation.of_comp_finiteType (algebraMap R S)
    · have hRT : RingHom.FinitePresentation (algebraMap R T) :=
        RingHom.finitePresentation_algebraMap.mpr
          (inferInstance : Algebra.FinitePresentation R T)
      convert hRT using 1
      ext x
      exact φ.commutes x
    · exact RingHom.FiniteType.of_finitePresentation hf
  let AtQ := Localization.AtPrime Q
  let H : AtQ ≃ₐ[T] Sq' :=
    IsLocalization.algEquiv Q.primeCompl AtQ Sq'
  let loc : Sq →+* AtQ := Localization.localRingHom q Q φ.toRingHom hqφ
  have hcomp : H.toRingEquiv.toRingHom.comp loc = E.toRingEquiv.toRingHom := by
    apply IsLocalization.ringHom_ext q.primeCompl
    apply RingHom.ext
    intro x
    change H (loc (algebraMap S Sq x)) = E (algebraMap S Sq x)
    rw [Localization.localRingHom_to_map, H.commutes]
    change tToSq' (φ x) = E (algebraMap S Sq x)
    rw [← DFunLike.congr_fun haway (φ x)]
    have hφx := DFunLike.congr_fun hφ x
    exact hφx
  have hlocbij : Function.Bijective loc := by
    have hcomp_apply (x : Sq) : H (loc x) = E x := by
      have hx := DFunLike.congr_fun hcomp x
      exact hx
    constructor
    · intro x y hxy
      apply E.injective
      rw [← hcomp_apply x, ← hcomp_apply y, hxy]
    · intro y
      obtain ⟨x, hx⟩ := E.surjective (H y)
      refine ⟨x, H.injective ?_⟩
      rw [hcomp_apply x, hx]
  let : Algebra S T := φ.toRingHom.toAlgebra
  obtain ⟨g, hg, C, P, sel, hsel, hPsel⟩ :=
    local_isomorphism_with_selector φ.toRingHom q Q hqφ hφfp hlocbij
  let A := Localization.Away g
  let TT := Localization (Algebra.algebraMapSubmonoid T (Submonoid.powers g))
  let : IsLocalization.Away (algebraMap S T g) TT := by
    simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
    infer_instance
  let s'ToTT : S' →+* TT := (algebraMap T TT).comp (algebraMap S' T)
  let : Algebra S' TT := s'ToTT.toAlgebra
  let : SMul S' T := (inferInstance : Algebra S' T).toSMul
  let : SMul T TT := (inferInstance : Algebra T TT).toSMul
  let : SMul S' TT := (inferInstance : Algebra S' TT).toSMul
  let : IsScalarTower S' T TT := IsScalarTower.of_algebraMap_eq' rfl
  let h : S' := (IsLocalization.Away.sec d (algebraMap S T g)).1
  have hassoc : Associated (algebraMap S' T h) (algebraMap S T g) :=
    IsLocalization.Away.associated_sec_fst d (algebraMap S T g)
  let G : S' := d * h
  let : IsLocalization.Away G TT :=
    IsLocalization.Away.mul_of_associated d h (algebraMap S T g) hassoc
  have hφg : algebraMap S T g ∉ Q := by
    intro hmem
    exact hg (by
      rw [hqφ]
      exact hmem)
  have hh : h ∉ q' := by
    intro hhq
    apply hφg
    rw [← Ideal.mem_iff_of_associated hassoc]
    exact Ideal.mem_map_of_mem (algebraMap S' T) hhq
  have hG : G ∉ q' := hq'.mul_notMem hd hh
  let proj : TT →+* A :=
    (RingHom.fst A C).comp P.toRingEquiv.toRingHom
  let : Algebra TT A := proj.toAlgebra
  let : Algebra (A × C) A := (RingHom.fst A C).toAlgebra
  let : IsLocalization.Away sel A := by
    change IsLocalization (Submonoid.powers sel) A
    apply IsLocalization.of_ringEquiv_left
      (K := A) (M₁ := Submonoid.powers ((1 : A), (0 : C)))
      (M₂ := Submonoid.powers sel) P.toRingEquiv
    · rw [Submonoid.map_powers]
      exact congr_arg Submonoid.powers hPsel
    · intro x
      rfl
  let k : S' := (IsLocalization.Away.sec G sel).1
  have hassocSel : Associated (algebraMap S' TT k) sel :=
    IsLocalization.Away.associated_sec_fst G sel
  have hk : k ∉ q' := by
    intro hkq
    apply hsel
    rw [Ideal.mem_iff_of_associated hassocSel.symm]
    rw [IsScalarTower.algebraMap_apply S' T TT]
    exact Ideal.mem_map_of_mem (algebraMap T TT)
      (Ideal.mem_map_of_mem (algebraMap S' T) hkq)
  let g' : S' := G * k
  have hg' : g' ∉ q' := hq'.mul_notMem hG hk
  let s'ToA : S' →+* A := proj.comp (algebraMap S' TT)
  let : Algebra S' A := s'ToA.toAlgebra
  let : IsScalarTower S' TT A := IsScalarTower.of_algebraMap_eq' rfl
  let : IsLocalization.Away g' A :=
    IsLocalization.Away.mul_of_associated G k sel hassocSel
  have hbase (r : R) :
      algebraMap S' TT (f' r) = algebraMap A TT (algebraMap R A r) := by
    calc
      algebraMap S' TT (f' r) =
          algebraMap T TT (algebraMap S' T (f' r)) :=
        IsScalarTower.algebraMap_apply S' T TT (f' r)
      _ = algebraMap T TT (algebraMap R T r) := by
        apply congr_arg (algebraMap T TT)
        change algebraMap S' T (algebraMap R S' r) = algebraMap R T r
        exact (IsScalarTower.algebraMap_apply R S' T r).symm
      _ = algebraMap T TT (φ (f r)) := by
        apply congr_arg (algebraMap T TT)
        change algebraMap R T r = φ (algebraMap R S r)
        exact (φ.commutes r).symm
      _ = algebraMap S TT (f r) :=
        (IsScalarTower.algebraMap_apply S T TT (f r)).symm
      _ = algebraMap A TT (algebraMap S A (f r)) :=
        IsScalarTower.algebraMap_apply S A TT (f r)
      _ = algebraMap A TT (algebraMap R A r) := by
        apply congr_arg (algebraMap A TT)
        change algebraMap S A (algebraMap R S r) = algebraMap R A r
        exact (IsScalarTower.algebraMap_apply R S A r).symm
  have hproj (a : A) : proj (algebraMap A TT a) = a := by
    change (P (algebraMap A TT a)).1 = a
    rw [P.commutes]
    rfl
  let : IsScalarTower R S' A := IsScalarTower.of_algebraMap_eq' <| by
    apply RingHom.ext
    intro r
    change algebraMap R A r = proj (algebraMap S' TT (f' r))
    rw [hbase]
    exact (hproj (algebraMap R A r)).symm
  let e' : Localization.Away g' ≃ₐ[S'] A :=
    IsLocalization.algEquiv (Submonoid.powers g') _ _
  exact ⟨g, hg, g', hg', ⟨e'.symm.restrictScalars R⟩⟩

/-! ### Nilpotent thickenings -/

/-- Finite type lifts across a nilpotent ideal. -/
theorem finite_type_mod_nilpotent {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hI : IsNilpotent I) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    RingHom.FiniteType (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))) →
      RingHom.FiniteType f := by
  let : Algebra R S := f.toAlgebra
  let J : Ideal S := I.map (algebraMap R S)
  let π : S →ₐ[R] (S ⧸ J) := Ideal.Quotient.mkₐ R J
  intro h
  change Algebra.FiniteType R S
  let q : R →+* (S ⧸ J) := (Ideal.Quotient.mk J).comp f
  have hq : RingHom.FiniteType q := by
    have hmk : RingHom.FiniteType (Ideal.Quotient.mk I) :=
      RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective
    have hcomp : RingHom.FiniteType
        ((algebraMap (R ⧸ I) (S ⧸ J)).comp (Ideal.Quotient.mk I)) :=
      (show RingHom.FiniteType (algebraMap (R ⧸ I) (S ⧸ J)) from h).comp hmk
    convert hcomp using 1
    ext r
    rfl
  let : Algebra R (S ⧸ J) := q.toAlgebra
  have hq' : Algebra.FiniteType R (S ⧸ J) := hq
  obtain ⟨s, hs⟩ := hq'.out
  classical
  let lift : (S ⧸ J) → S := fun x => (Ideal.Quotient.mk_surjective x).choose
  have hlift (x : S ⧸ J) : Ideal.Quotient.mk J (lift x) = x :=
    (Ideal.Quotient.mk_surjective x).choose_spec
  let T : Set S := lift '' (s : Set (S ⧸ J))
  let A : Subalgebra R S := Algebra.adjoin R T
  have hT : T.Finite := s.finite_toSet.image lift
  have hπ : Function.Surjective (π.comp A.val) := by
    apply (AlgHom.range_eq_top _).mp
    apply Algebra.eq_top_iff.mpr
    intro x
    have hle : Algebra.adjoin R (s : Set (S ⧸ J)) ≤ (π.comp A.val).range := by
      apply Algebra.adjoin_le
      intro y hy
      exact ⟨⟨lift y, Algebra.subset_adjoin ⟨y, hy, rfl⟩⟩, by
        simpa [π] using hlift y⟩
    exact hle (by rw [hs]; trivial)
  have hbase : ∀ x : S, ∃ a : A, x - a.1 ∈ J := by
    intro x
    obtain ⟨a, ha⟩ := hπ (π x)
    refine ⟨a, ?_⟩
    have hz : π (x - a.1) = 0 := by
      simpa [map_sub, Function.comp_apply] using sub_eq_zero.mpr ha.symm
    simpa [π] using Ideal.Quotient.eq_zero_iff_mem.mp hz
  obtain ⟨N, hIN⟩ := hI
  have hN : J ^ N = ⊥ := by
    change (Ideal.map (algebraMap R S) I) ^ N = ⊥
    rw [← Ideal.map_pow, hIN]
    simp
  have hdecomp (n : ℕ) (x : S) (hx : x ∈ J ^ n) :
      ∃ a : A, a.1 ∈ J ^ n ∧ x - a.1 ∈ J ^ (n + 1) := by
    have hx' : x ∈ Ideal.map (algebraMap R S) (I ^ n) := by
      simpa [J, Ideal.map_pow] using hx
    rw [Ideal.map] at hx'
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx'
    · rintro y ⟨r, hr, rfl⟩
      let a : A := ⟨algebraMap R S r, A.algebraMap_mem r⟩
      refine ⟨a, ?_, ?_⟩
      · rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hr
      · simp [a]
    · exact ⟨0, Ideal.zero_mem _, by simp⟩
    · rintro x y _ _ ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩
      refine ⟨a + b, add_mem ha hb, ?_⟩
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using add_mem hxa hyb
    · rintro c x _ ⟨a, ha, hxa⟩
      obtain ⟨b, hb⟩ := hbase c
      refine ⟨b * a, ?_, ?_⟩
      · exact Ideal.mul_mem_left _ _ ha
      · have h₁ : c * (x - a.1) ∈ J ^ (n + 1) :=
          Ideal.mul_mem_left _ _ hxa
        have h₂ : (c - b.1) * a.1 ∈ J ^ (n + 1) := by
          have := Ideal.mul_mem_mul hb ha
          simpa [pow_succ', mul_comm] using this
        have hres := add_mem h₁ h₂
        change c * x - b.1 * a.1 ∈ J ^ (n + 1)
        convert hres using 1
        ring
  have hgen : ∀ n : ℕ, ∀ x : S, ∃ a : A, x - a.1 ∈ J ^ n := by
    intro n
    induction n with
    | zero => intro x; exact ⟨0, by simp⟩
    | succ n ih =>
      intro x
      obtain ⟨a, ha⟩ := ih x
      obtain ⟨b, hb, hxb⟩ := hdecomp n (x - a.1) ha
      refine ⟨a + b, ?_⟩
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxb
  have hAtop : A = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨a, ha⟩ := hgen N x
    have hzero : x - a.1 = 0 := by simpa [hN] using ha
    have hxa : x = a.1 := sub_eq_zero.mp hzero
    rw [hxa]
    exact a.property
  have hAfinite : Algebra.FiniteType R A := Algebra.FiniteType.adjoin_of_finite hT
  apply hAfinite.of_surjective A.val
  intro x
  have hx : x ∈ A := by rw [hAtop]; trivial
  exact ⟨⟨x, hx⟩, rfl⟩

/-- Surjectivity lifts across a locally nilpotent thickening. -/
theorem surjective_mod_locally_nilpotent {R S S' : Type*} [CommRing R] [CommRing S]
    [CommRing S'] [Algebra R S] [Algebra R S'] (f : S →ₐ[R] S') (I : Ideal R)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I)
    (hquot : Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap R S'))).comp f.toRingHom))
    (hfinite : RingHom.FiniteType (algebraMap R S')) :
    Function.Surjective f := by
  classical
  let J : Ideal S' := I.map (algebraMap R S')
  let B : Subalgebra R S' := f.range
  have hfinite' : Algebra.FiniteType R S' :=
    (RingHom.finiteType_algebraMap).mp hfinite
  let _ : Algebra.FiniteType R S' := hfinite'
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R S').out
  choose y hy using fun x : s => hquot (Ideal.Quotient.mk J x.1)
  let d : s → S' := fun x => x.1 - f (y x)
  have hd (x : s) : d x ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk J (x.1 - f (y x)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (hy x).symm
  let t : Finset S' := s.attach.image d
  have ht : (t : Set S') ⊆ Ideal.span ((algebraMap R S') '' (I : Set R)) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    simpa [J, Ideal.map] using hd x
  obtain ⟨u, hu, htu⟩ :=
    Submodule.subset_span_finite_of_subset_span (t := t) ht
  choose r hrI hr using fun z : u => hu z.property
  let K : Ideal R := Ideal.span (Set.range r)
  have hKle : K ≤ I := by
    apply Ideal.span_le.2
    rintro x ⟨z, rfl⟩
    exact hrI z
  have hKfg : K.FG := Submodule.fg_span (Set.toFinite (Set.range r))
  have hKnil : IsNilpotent K := by
    apply hKfg.isNilpotent_iff_le_nilradical.mpr
    intro x hx
    rw [mem_nilradical]
    exact hI x (hKle hx)
  have huK : (u : Set S') ⊆ K.map (algebraMap R S') := by
    intro z hz
    have hz' : algebraMap R S' (r ⟨z, hz⟩) ∈ K.map (algebraMap R S') :=
      Ideal.mem_map_of_mem (algebraMap R S')
        (Ideal.subset_span (s := Set.range r) (Set.mem_range_self _))
    rw [hr] at hz'
    exact hz'
  have hspan : Ideal.span (u : Set S') ≤ K.map (algebraMap R S') :=
    Ideal.span_le.2 huK
  have hdK (x : s) : d x ∈ K.map (algebraMap R S') :=
    hspan (htu (Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, rfl⟩))
  have hgen (x : S') : ∃ b : B, x - b.1 ∈ K.map (algebraMap R S') := by
    have hx : x ∈ Algebra.adjoin R (s : Set S') := by simp [hs]
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
        exact ⟨⟨f (y ⟨x, hx⟩), ⟨y ⟨x, hx⟩, rfl⟩⟩, hdK ⟨x, hx⟩⟩
    | algebraMap r =>
        exact ⟨⟨algebraMap R S' r, ⟨algebraMap R S r, by simp⟩⟩, by simp⟩
    | add x y hx hy ihx ihy =>
        obtain ⟨bx, hbx⟩ := ihx
        obtain ⟨b_y, hby⟩ := ihy
        refine ⟨bx + b_y, ?_⟩
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using add_mem hbx hby
    | mul x y hx hy ihx ihy =>
        obtain ⟨bx, hbx⟩ := ihx
        obtain ⟨b_y, hby⟩ := ihy
        refine ⟨bx * b_y, ?_⟩
        have h₁ : bx.1 * (y - b_y.1) ∈ K.map (algebraMap R S') :=
          Ideal.mul_mem_left _ _ hby
        have h₂ : b_y.1 * (x - bx.1) ∈ K.map (algebraMap R S') :=
          Ideal.mul_mem_left _ _ hbx
        have h₃ : (x - bx.1) * (y - b_y.1) ∈ K.map (algebraMap R S') :=
          Ideal.mul_mem_left _ _ hby
        have hsum := add_mem (add_mem h₁ h₂) h₃
        change x * y - bx.1 * b_y.1 ∈ K.map (algebraMap R S')
        convert hsum using 1 ; ring
  let Kmap : Ideal S' := K.map (algebraMap R S')
  have hstep (L : Ideal R) (x : S') (hx : x ∈ L.map (algebraMap R S')) :
      ∃ b : B, b.1 ∈ L.map (algebraMap R S') ∧
        x - b.1 ∈ (L.map (algebraMap R S')) * Kmap := by
    rw [Ideal.map] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro z ⟨r, hrL, rfl⟩
      refine ⟨⟨algebraMap R S' r, ⟨algebraMap R S r, by simp⟩⟩, ?_, ?_⟩
      · exact Ideal.mem_map_of_mem _ hrL
      · simp
    · exact ⟨0, by simp, by simp⟩
    · rintro x y _ _ ⟨bx, hbx, hxr⟩ ⟨b_y, hby, hyr⟩
      refine ⟨bx + b_y, add_mem hbx hby, ?_⟩
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using add_mem hxr hyr
    · rintro c x _ ⟨bx, hbx, hxr⟩
      obtain ⟨bc, hbc⟩ := hgen c
      refine ⟨bc * bx, Ideal.mul_mem_left _ _ hbx, ?_⟩
      change c - bc.1 ∈ Kmap at hbc
      have h₁ : c * (x - bx.1) ∈ (L.map (algebraMap R S')) * Kmap :=
        Ideal.mul_mem_left _ _ hxr
      have h₂ : (c - bc.1) * bx.1 ∈ (L.map (algebraMap R S')) * Kmap := by
        have h₂' : (c - bc.1) * bx.1 ∈ Kmap * (L.map (algebraMap R S')) :=
          Ideal.mul_mem_mul hbc hbx
        rw [Ideal.mul_comm] at h₂'
        exact h₂'
      have hsum := add_mem h₁ h₂
      convert hsum using 1 ; simp ; ring
  have hpow (n : ℕ) : Kmap ^ n = (K ^ n).map (algebraMap R S') := by
    rw [← Ideal.map_pow]
  obtain ⟨n, hn⟩ := hKnil
  have happ : ∀ n : ℕ, ∀ x : S', ∃ b : B, x - b.1 ∈ Kmap ^ n := by
    intro n
    induction n with
    | zero =>
        intro x
        exact ⟨0, by simp⟩
    | succ n ih =>
        intro x
        obtain ⟨b, hb⟩ := ih x
        obtain ⟨c, hc, hxc⟩ := hstep (K ^ n) (x - b.1) (by simpa [hpow n] using hb)
        refine ⟨b + c, ?_⟩
        have : (x - b.1) - c.1 ∈ Kmap ^ n * Kmap := by
          simpa [hpow n] using hxc
        simpa [pow_succ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  intro x
  obtain ⟨b, hb⟩ := happ n x
  have hzero : x - b.1 = 0 := by simpa [hn, hpow n] using hb
  obtain ⟨y, hy⟩ := b.property
  exact ⟨y, hy.trans (sub_eq_zero.mp hzero).symm⟩

/-! ### Isomorphisms modulo an ideal -/

/-- The localized quotient isomorphism in the next theorem is recorded by an
equivalence whose values on quotient representatives are the canonical local
map.  This avoids introducing a duplicate quotient-map definition. -/
def localQuotientIsomorphism {R : Type u} {S : Type v} {S' : Type w}
    [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S'] (f : S →ₐ[R] S') (I : Ideal R) (q : Ideal S)
    [q.IsPrime]
    (e : (Localization q.primeCompl ⧸
        (I.map (algebraMap R (Localization q.primeCompl)))) ≃+*
      (Localization (q.primeCompl.map f.toRingHom) ⧸
        (I.map (algebraMap R (Localization (q.primeCompl.map f.toRingHom)))))) : Prop :=
  ∀ x : Localization q.primeCompl,
    e (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (localizedRingHom f.toRingHom q.primeCompl x)

/-- A surjective map satisfying the local quotient and flatness hypotheses is
an isomorphism after inverting an element outside the chosen prime. -/
theorem isomorphism_modulo_ideal {R : Type u} {S : Type v} {S' : Type w}
    [CommRing R] [CommRing S]
    [CommRing S'] [Algebra R S] [Algebra R S'] (f : S →ₐ[R] S') (I : Ideal R)
    (q : Ideal S) [hq : q.IsPrime]
    (hIq : I.map (algebraMap R S) ≤ q)
    (hsurj : Function.Surjective f)
    (hlocal : ∃ e :
      (Localization q.primeCompl ⧸
          (I.map (algebraMap R (Localization q.primeCompl)))) ≃+*
        (Localization (q.primeCompl.map f.toRingHom) ⧸
          (I.map (algebraMap R (Localization (q.primeCompl.map f.toRingHom))))),
      localQuotientIsomorphism f I q e)
    (hfinite : RingHom.FiniteType (algebraMap R S))
    (hfp : RingHom.FinitePresentation (algebraMap R S'))
    (hflat : Module.Flat R (Localization (q.primeCompl.map f.toRingHom))) :
    ∃ g : S, g ∉ q ∧ Function.Bijective (localizedRingHom f.toRingHom (Submonoid.powers g)) := by
  classical
  let A := Localization q.primeCompl
  let B := Localization (q.primeCompl.map f.toRingHom)
  let F : A →+* B := localizedRingHom f.toRingHom q.primeCompl
  let IA : Ideal A := I.map (algebraMap R A)
  let IB : Ideal B := I.map (algebraMap R B)
  let K : Ideal A := RingHom.ker F
  have hcomp : RingHom.FinitePresentation
      (f.toRingHom.comp (algebraMap R S)) := by
    have hcomp' : f.toRingHom.comp (algebraMap R S) = algebraMap R S' := by
      ext r
      exact f.commutes r
    rw [hcomp']
    exact hfp
  have hfpp : RingHom.FinitePresentation f.toRingHom :=
    RingHom.FinitePresentation.of_comp_finiteType (algebraMap R S)
      (g := f.toRingHom) hcomp hfinite
  let _ : Algebra S S' := f.toRingHom.toAlgebra
  let _ : Algebra.FinitePresentation S S' := hfpp
  have hker : (RingHom.ker f.toRingHom).FG := by
    have hker' :=
      Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId S S') hsurj
    convert hker' using 1
    ext x
    rfl
  have hK : K.FG := by
    change (RingHom.ker (IsLocalization.map B f.toRingHom
      q.primeCompl.le_comap_map)).FG
    rw [IsLocalization.ker_map B f.toRingHom rfl]
    exact hker.map (algebraMap S A)
  have hFsurj : Function.Surjective F := by
    exact IsLocalization.map_surjective_of_surjective _ _ _ hsurj
  have hFA (r : R) : F (algebraMap R A r) = algebraMap R B r := by
    change IsLocalization.map B f.toRingHom _ (algebraMap R A r) = _
    rw [IsScalarTower.algebraMap_apply R S A]
    rw [IsLocalization.map_eq]
    simp [IsScalarTower.algebraMap_apply R S' B, f.commutes]
  let Flin : A →ₗ[R] B :=
    { toFun := F
      map_add' := fun x y => F.map_add x y
      map_smul' := by
        intro r x
        simp [Algebra.smul_def, hFA] }
  have hIAIB : IA ≤ IB.comap F := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change F (algebraMap R A r) ∈ IB
    rw [hFA]
    simpa [IB] using
      (Ideal.mem_map_of_mem (algebraMap R B) hr)
  obtain ⟨e, he⟩ := hlocal
  have hKIA : K ≤ IA := by
    intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.injective
    rw [he x]
    change F x = 0 at hx
    rw [hx]
    change (0 : _) = e 0
    exact (map_zero e).symm
  let lA : I ⊗[R] A →ₗ[R] A :=
    TensorProduct.lift ((LinearMap.lsmul R A).comp I.subtype)
  let lB : I ⊗[R] B →ₗ[R] B :=
    TensorProduct.lift ((LinearMap.lsmul R B).comp I.subtype)
  have hmem (x : A) (hx : x ∈ IA) : ∃ y : I ⊗[R] A, lA y = x := by
    change x ∈ Ideal.map (algebraMap R A) I at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨r, hr, rfl⟩ := hx
        refine ⟨(⟨r, hr⟩ : I) ⊗ₜ[R] (1 : A), ?_⟩
        simp [lA, Algebra.smul_def]
    | zero => exact ⟨0, by simp [lA]⟩
    | add x y _ _ ihx ihy =>
        exact ⟨ihx.choose + ihy.choose, by simp [lA, ihx.choose_spec, ihy.choose_spec]⟩
    | smul c x _ ihx =>
        let hmul (y : I ⊗[R] A) :
            lA (TensorProduct.map (LinearMap.id : I →ₗ[R] I)
              (LinearMap.mulLeft R c) y) = c * lA y := by
          induction y using TensorProduct.induction_on with
          | zero => simp [lA]
          | add y z ihy ihz => simp [lA, ihy, ihz, mul_add]
          | tmul y z => simp [lA, Algebra.smul_def, mul_assoc, mul_comm]
        refine ⟨TensorProduct.map (LinearMap.id : I →ₗ[R] I)
            (LinearMap.mulLeft R c) ihx.choose, ?_⟩
        rw [hmul, ihx.choose_spec]
        rfl
  change Module.Flat R B at hflat
  have hlB : Function.Injective lB := by
    intro x y hxy
    have hlt : Function.Injective (I.subtype.rTensor B) :=
      Module.Flat.iff_rTensor_injective'.mp hflat I
    have hxy' : ((TensorProduct.lid R B).toLinearMap.comp
          (I.subtype.rTensor B)) x =
        ((TensorProduct.lid R B).toLinearMap.comp
          (I.subtype.rTensor B)) y := by
      simpa only [lB,
        ← LinearMap.lid_comp_rTensor (R := R) (M := B) I.subtype] using hxy
    exact hlt ((TensorProduct.lid R B).injective hxy')
  let Klin : Submodule R A := LinearMap.ker Flin
  have hker_smul : K ≤ IA * K := by
    intro x hx
    obtain ⟨y, hy⟩ := hmem x (hKIA hx)
    have hyzero : (Flin.lTensor I) y = 0 := by
      apply hlB
      have hcomm (z : I ⊗[R] A) : lB ((Flin.lTensor I) z) = F (lA z) := by
        induction z using TensorProduct.induction_on with
        | zero => simp [lA, lB]
        | add y z ihy ihz => simp [lA, lB, ihy, ihz]
        | tmul y z =>
            simp only [lA, lB, LinearMap.lTensor_tmul, TensorProduct.lift.tmul,
              LinearMap.comp_apply, LinearMap.lsmul_apply, Flin]
            simp [Algebra.smul_def, map_mul, hFA, mul_comm]
            rfl
      rw [hcomm]
      change F x = 0 at hx
      rw [hy, hx]
      simp
    let z : I ⊗[R] Klin :=
      (LinearMap.kerLTensorEquivOfSurjective Flin hFsurj I)
        ⟨y, hyzero⟩
    have hz : Klin.subtype.lTensor I z = y := by
      have hz' := congrArg Subtype.val
        ((LinearMap.kerLTensorEquivOfSurjective Flin hFsurj I).symm_apply_apply
          ⟨y, hyzero⟩)
      change ((LinearMap.kerLTensorEquivOfSurjective Flin hFsurj I).symm z).1 = y
      exact hz'
    have hzl : lA (Klin.subtype.lTensor I z) ∈ IA * K := by
      induction z using TensorProduct.induction_on with
      | zero => simp [lA]
      | add y z ihy ihz =>
          simpa [lA] using add_mem ihy ihz
      | tmul y z =>
          have hzK : z.1 ∈ K := by
            change F z.1 = 0
            exact z.2
          simpa [lA, Algebra.smul_def] using
            (Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R A) y.2) hzK)
    rw [hz, hy] at hzl
    exact hzl
  have hIAq : IA ≤ q.map (algebraMap S A) := by
    simpa [IA, Ideal.map_map, ← IsScalarTower.algebraMap_eq R S A] using
      (Ideal.map_mono hIq : (I.map (algebraMap R S)).map (algebraMap S A) ≤
        q.map (algebraMap S A))
  have hIAjac : IA ≤ Ideal.jacobson (⊥ : Ideal A) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) (by exact bot_ne_top),
      ← Localization.AtPrime.map_eq_maximalIdeal]
    exact hIAq
  have hKzero : K = ⊥ := by
    have hKsmul : (K : Submodule A A) ≤ IA • (K : Submodule A A) := by
      simpa [smul_eq_mul] using hker_smul
    have hIAjac' : IA ≤ Ring.jacobson A := by
      simpa only [Ideal.jacobson_bot] using hIAjac
    exact Submodule.FG.eq_bot_of_le_jacobson_smul hK
      (hKsmul.trans (Submodule.smul_mono hIAjac' le_rfl))
  have hKmap : K = (RingHom.ker f.toRingHom).map (algebraMap S A) := by
    change RingHom.ker (IsLocalization.map B f.toRingHom
      q.primeCompl.le_comap_map) = _
    rw [IsLocalization.ker_map B f.toRingHom rfl]
  obtain ⟨t, htfin, htspan⟩ := Submodule.fg_def.mp hker
  let _ : Fintype t := htfin.fintype
  choose s hs using fun x : t => by
    have hxK : algebraMap S A (x : S) ∈ K := by
      rw [hKmap]
      exact Ideal.mem_map_of_mem (algebraMap S A)
        (show (x : S) ∈ RingHom.ker f.toRingHom by
          rw [← htspan]
          exact Submodule.subset_span x.2)
    have hxzero : algebraMap S A (x : S) = 0 := by
      rw [hKzero] at hxK
      exact hxK
    exact (IsLocalization.map_eq_zero_iff q.primeCompl A (x : S)).mp hxzero
  let g : S := ∏ x : t, (s x : S)
  have hg : g ∉ q := by
    intro hgq
    obtain ⟨x, -, hxq⟩ :=
      (hq.prod_mem_iff (s := (Finset.univ : Finset t))
        (x := fun x : t => (s x : S))).mp (by simpa [g] using hgq)
    exact (s x).property hxq
  have hgj : ∀ x ∈ RingHom.ker f.toRingHom, g * x = 0 := by
    intro x hx
    rw [← htspan] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨y, hy⟩ := Finset.dvd_prod_of_mem (fun z : t => (s z : S))
          (Finset.mem_univ (⟨x, hx⟩ : t))
        change (∏ z : t, (s z : S)) * x = 0
        rw [hy]
        calc
          (s ⟨x, hx⟩ : S) * y * x =
              y * ((s ⟨x, hx⟩ : S) * x) := by ring
          _ = 0 := by rw [hs ⟨x, hx⟩, mul_zero]
    | zero => simp
    | add x y _ _ ihx ihy => simp [mul_add, ihx, ihy]
    | smul c x _ ihx =>
        simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
          congrArg (fun z => c * z) ihx
  have haway_inj :
      Function.Injective (localizedRingHom f.toRingHom (Submonoid.powers g)) := by
    let L := Localization (Submonoid.powers g)
    let _ : Algebra S L := by
      dsimp [L]
      infer_instance
    let L' := Localization ((Submonoid.powers g).map f.toRingHom)
    let G : Localization (Submonoid.powers g) →+*
        Localization ((Submonoid.powers g).map f.toRingHom) :=
      localizedRingHom f.toRingHom (Submonoid.powers g)
    have hGker : RingHom.ker G =
        (RingHom.ker f.toRingHom).map (algebraMap S L) := by
      change RingHom.ker (IsLocalization.map L' f.toRingHom
        (Submonoid.powers g).le_comap_map) = _
      rw [IsLocalization.ker_map L' f.toRingHom rfl]
    have hGzero : RingHom.ker G = ⊥ := by
      rw [hGker]
      apply le_antisymm
      · apply Ideal.map_le_iff_le_comap.mpr
        intro x hx
        change algebraMap S L x ∈ (⊥ : Ideal L)
        rw [Ideal.mem_bot]
        apply (IsLocalization.map_eq_zero_iff (Submonoid.powers g) L x).2
        refine ⟨⟨g, 1, by simp⟩, ?_⟩
        exact hgj x hx
      · exact bot_le
    exact (RingHom.injective_iff_ker_eq_bot G).2 hGzero
  have haway_surj :
      Function.Surjective (localizedRingHom f.toRingHom (Submonoid.powers g)) := by
    exact IsLocalization.map_surjective_of_surjective _ _ _ hsurj
  exact ⟨g, hg, haway_inj, haway_surj⟩

/-! ### Isomorphisms modulo a locally nilpotent ideal -/

/-- The quotient isomorphism in the final theorem is recorded by its action on
canonical quotient representatives. -/
def quotientIsomorphism {R : Type u} {S : Type v} {S' : Type w}
    [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S'] (f : S →ₐ[R] S') (I : Ideal R)
    (e : (S ⧸ I.map (algebraMap R S)) ≃+* (S' ⧸ I.map (algebraMap R S'))) : Prop :=
  ∀ x : S,
    e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (f x)

/-- Under the finite type, finite presentation, flatness, and local nilpotence
hypotheses, an isomorphism modulo the ideal is an isomorphism. -/
theorem isomorphism_modulo_locally_nilpotent {R : Type u} {S : Type v} {S' : Type w}
    [CommRing R] [CommRing S]
    [CommRing S'] [Algebra R S] [Algebra R S'] (f : S →ₐ[R] S') (I : Ideal R)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I)
    (hquot : ∃ e : (S ⧸ I.map (algebraMap R S)) ≃+* (S' ⧸ I.map (algebraMap R S')),
      quotientIsomorphism f I e)
    (hfinite : RingHom.FiniteType (algebraMap R S))
    (hfp : RingHom.FinitePresentation (algebraMap R S'))
    (hflat : Module.Flat R S') :
    Function.Bijective f := by
  classical
  obtain ⟨e, he⟩ := hquot
  have hquotSurj : Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap R S'))).comp f.toRingHom) := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
      (e.symm (Ideal.Quotient.mk (I.map (algebraMap R S')) x))
    refine ⟨y, ?_⟩
    change Ideal.Quotient.mk _ (f y) = Ideal.Quotient.mk _ x
    calc
      Ideal.Quotient.mk (I.map (algebraMap R S')) (f y) =
          e (Ideal.Quotient.mk (I.map (algebraMap R S)) y) := (he y).symm
      _ = e (e.symm (Ideal.Quotient.mk (I.map (algebraMap R S')) x)) := congrArg e hy
      _ = Ideal.Quotient.mk (I.map (algebraMap R S')) x := e.apply_symm_apply _
  have hfinite' : RingHom.FiniteType (algebraMap R S') :=
    RingHom.FiniteType.of_finitePresentation hfp
  have hsurj : Function.Surjective f :=
    surjective_mod_locally_nilpotent f I hI hquotSurj hfinite'
  have hcomp : RingHom.FinitePresentation
      (f.toRingHom.comp (algebraMap R S)) := by
    have hcomp' : f.toRingHom.comp (algebraMap R S) = algebraMap R S' := by
      ext r
      exact f.commutes r
    rw [hcomp']
    exact hfp
  have hfpp : RingHom.FinitePresentation f.toRingHom :=
    RingHom.FinitePresentation.of_comp_finiteType (algebraMap R S)
      (g := f.toRingHom) hcomp hfinite
  let _ : Algebra S S' := f.toRingHom.toAlgebra
  let _ : Algebra.FinitePresentation S S' := hfpp
  have hker : (RingHom.ker f.toRingHom).FG := by
    have hker' :=
      Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId S S') hsurj
    convert hker' using 1
    ext x
    rfl
  let JA : Ideal S := I.map (algebraMap R S)
  let JB : Ideal S' := I.map (algebraMap R S')
  let K : Ideal S := RingHom.ker f.toRingHom
  have hKIA : K ≤ JA := by
    intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.injective
    rw [he x]
    change f x = 0 at hx
    rw [hx]
    change (0 : _) = e 0
    exact (map_zero e).symm
  let lA : I ⊗[R] S →ₗ[R] S :=
    TensorProduct.lift ((LinearMap.lsmul R S).comp I.subtype)
  let lB : I ⊗[R] S' →ₗ[R] S' :=
    TensorProduct.lift ((LinearMap.lsmul R S').comp I.subtype)
  have hmem (x : S) (hx : x ∈ JA) : ∃ y : I ⊗[R] S, lA y = x := by
    change x ∈ Ideal.map (algebraMap R S) I at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨r, hr, rfl⟩ := hx
        refine ⟨(⟨r, hr⟩ : I) ⊗ₜ[R] (1 : S), ?_⟩
        simp [lA, Algebra.smul_def]
    | zero => exact ⟨0, by simp [lA]⟩
    | add x y _ _ ihx ihy =>
        exact ⟨ihx.choose + ihy.choose, by simp [lA, ihx.choose_spec, ihy.choose_spec]⟩
    | smul c x _ ihx =>
        let hmul (y : I ⊗[R] S) :
            lA (TensorProduct.map (LinearMap.id : I →ₗ[R] I)
              (LinearMap.mulLeft R c) y) = c * lA y := by
          induction y using TensorProduct.induction_on with
          | zero => simp [lA]
          | add y z ihy ihz => simp [lA, ihy, ihz, mul_add]
          | tmul y z => simp [lA, Algebra.smul_def, mul_assoc, mul_comm]
        refine ⟨TensorProduct.map (LinearMap.id : I →ₗ[R] I)
            (LinearMap.mulLeft R c) ihx.choose, ?_⟩
        rw [hmul, ihx.choose_spec]
        rfl
  have hlB : Function.Injective lB := by
    intro x y hxy
    have hlt : Function.Injective (I.subtype.rTensor S') :=
      Module.Flat.iff_rTensor_injective'.mp hflat I
    have hxy' : ((TensorProduct.lid R S').toLinearMap.comp
          (I.subtype.rTensor S')) x =
        ((TensorProduct.lid R S').toLinearMap.comp
          (I.subtype.rTensor S')) y := by
      simpa only [lB,
        ← LinearMap.lid_comp_rTensor (R := R) (M := S') I.subtype] using hxy
    exact hlt ((TensorProduct.lid R S').injective hxy')
  let Flin : S →ₗ[R] S' :=
    { toFun := f
      map_add' := fun x y => f.map_add x y
      map_smul' := by
        intro r x
        simp [Algebra.smul_def] }
  have hker_smul : K ≤ JA * K := by
    intro x hx
    obtain ⟨y, hy⟩ := hmem x (hKIA hx)
    have hyzero : (Flin.lTensor I) y = 0 := by
      apply hlB
      have hcomm (z : I ⊗[R] S) : lB ((Flin.lTensor I) z) = f (lA z) := by
        induction z using TensorProduct.induction_on with
        | zero => simp [lA, lB]
        | add y z ihy ihz => simp [lA, lB, ihy, ihz]
        | tmul y z =>
            simp only [lA, lB, LinearMap.lTensor_tmul, TensorProduct.lift.tmul,
              LinearMap.comp_apply, LinearMap.lsmul_apply, Flin]
            simp [Algebra.smul_def, map_mul, f.commutes, mul_comm]
      rw [hcomm]
      change f x = 0 at hx
      rw [hy, hx]
      simp
    let Klin : Submodule R S := LinearMap.ker Flin
    let z : I ⊗[R] Klin :=
      (LinearMap.kerLTensorEquivOfSurjective Flin hsurj I)
        ⟨y, hyzero⟩
    have hz : Klin.subtype.lTensor I z = y := by
      have hz' := congrArg Subtype.val
        ((LinearMap.kerLTensorEquivOfSurjective Flin hsurj I).symm_apply_apply
          ⟨y, hyzero⟩)
      change ((LinearMap.kerLTensorEquivOfSurjective Flin hsurj I).symm z).1 = y
      exact hz'
    have hzl : lA (Klin.subtype.lTensor I z) ∈ JA * K := by
      induction z using TensorProduct.induction_on with
      | zero => simp [lA]
      | add y z ihy ihz => simpa [lA] using add_mem ihy ihz
      | tmul y z =>
          have hzK : z.1 ∈ K := by
            change f z.1 = 0
            exact z.2
          simpa [lA, Algebra.smul_def] using
            (Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R S) y.2) hzK)
    rw [hz, hy] at hzl
    exact hzl
  have hJA_rad : JA ≤ nilradical S := by
    intro x hx
    exact (mem_nilradical).2
      (Formalization.Books.Algebra.Unit32.locallyNilpotentIdeal_map
        (algebraMap R S) I hI x hx)
  have hJA_jac : JA ≤ Ring.jacobson S :=
    hJA_rad.trans (nilradical_le_jacobson S)
  have hKzero : K = ⊥ := by
    have hKsmul : (K : Submodule S S) ≤ JA • (K : Submodule S S) := by
      simpa [smul_eq_mul] using hker_smul
    have hKsmul' : (K : Submodule S S) ≤ (Ring.jacobson S) • (K : Submodule S S) :=
      hKsmul.trans (Submodule.smul_mono hJA_jac le_rfl)
    exact Submodule.FG.eq_bot_of_le_jacobson_smul hker hKsmul'
  have hinj : Function.Injective f := by
    intro x y hxy
    have hmem : x - y ∈ K := by
      change f (x - y) = 0
      rw [map_sub, hxy, sub_self]
    have hzero : x - y = 0 := by
      have hmem' : x - y ∈ (⊥ : Ideal S) := by
        rw [← hKzero]
        exact hmem
      exact Ideal.mem_bot.mp hmem'
    exact sub_eq_zero.mp hzero
  exact ⟨hinj, hsurj⟩

end

end Formalization.Books.Algebra.Unit126
