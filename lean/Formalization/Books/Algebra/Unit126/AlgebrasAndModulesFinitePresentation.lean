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
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.Tensor
import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit32.LocallyNilpotent

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
