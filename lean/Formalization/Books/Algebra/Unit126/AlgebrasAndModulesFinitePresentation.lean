import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit14.BaseChange

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
      ∃ M' : ModuleCat.{v} R,
        Module.Finite R (M' : Type v) ∧
          ∃ f : (M' : Type v) →ₗ[R] (M : Type v),
            Function.Bijective (LocalizedModule.map S f)) ∧
    (Module.FinitePresentation (Localization S) (LocalizedModule S (M : Type v)) →
      ∃ M' : ModuleCat.{v} R,
        Module.FinitePresentation R (M' : Type v) ∧
          ∃ f : (M' : Type v) →ₗ[R] (M : Type v),
            Function.Bijective (LocalizedModule.map S f)) := by
  constructor
  · intro hM
    obtain ⟨P, hP, hbij⟩ := finite_localized_submodule S hM
    exact ⟨ModuleCat.of R (P : Type v), hP, P.subtype, hbij⟩
  · sorry

/-! ### The stalk case -/

/-- The preceding localization lifting result specialized to a prime stalk. -/
theorem construct_fp_module_from_stalk {R : Type u} [CommRing R]
    (p : Ideal R) [hp : p.IsPrime] (M : ModuleCat.{v} R) :
    (Module.Finite (Localization.AtPrime p)
        (LocalizedModule p.primeCompl (M : Type v)) →
      ∃ M' : ModuleCat.{v} R,
        Module.Finite R (M' : Type v) ∧
          ∃ f : (M' : Type v) →ₗ[R] (M : Type v),
            Function.Bijective (LocalizedModule.map p.primeCompl f)) ∧
    (Module.FinitePresentation (Localization.AtPrime p)
        (LocalizedModule p.primeCompl (M : Type v)) →
      ∃ M' : ModuleCat.{v} R,
        Module.FinitePresentation R (M' : Type v) ∧
          ∃ f : (M' : Type v) →ₗ[R] (M : Type v),
            Function.Bijective (LocalizedModule.map p.primeCompl f)) := by
  constructor
  · intro hM
    exact (construct_fp_module_from_localization p.primeCompl M).1 hM
  · intro hM
    exact (construct_fp_module_from_localization p.primeCompl M).2 hM

/-! ### Local isomorphisms and spreading out -/

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
  sorry

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
  sorry

/-! ### Nilpotent thickenings -/

/-- Finite type lifts across a nilpotent ideal. -/
theorem finite_type_mod_nilpotent {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hI : IsNilpotent I) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    RingHom.FiniteType (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))) →
      RingHom.FiniteType f := by
  sorry

/-- Surjectivity lifts across a locally nilpotent thickening. -/
theorem surjective_mod_locally_nilpotent {R S S' : Type*} [CommRing R] [CommRing S]
    [CommRing S'] [Algebra R S] [Algebra R S'] (f : S →ₐ[R] S') (I : Ideal R)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I)
    (hquot : Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap R S'))).comp f.toRingHom))
    (hfinite : RingHom.FiniteType (algebraMap R S')) :
    Function.Surjective f := by
  sorry

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
  sorry

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
  sorry

end

end Formalization.Books.Algebra.Unit126
