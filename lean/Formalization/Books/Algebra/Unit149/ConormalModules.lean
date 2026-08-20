import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Extension.Cotangent.BaseChange
import Mathlib.RingTheory.Extension.ExtendScalars
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Unramified.Basic

/-!
# Commutative Algebra, Chapter 149: Conormal modules and universal thickenings

The source constructs a universal square-zero extension for a formally
unramified algebra.  Mathlib's `Algebra.Extension` is the canonical interface
for a surjection of algebras, and its `Cotangent` is the canonical
presentation-independent `I/I²` module.  The declarations below add the
universal property and record the quotient, localization, and differential
statements from the source section.  The universal-property predicate itself
is stated independently of the hypothesis used by the existence lemma, which
lets the quotient construction be recorded directly before relating it to a
chosen universal thickening.
-/

namespace Formalization.Books.Algebra.Unit149

open scoped TensorProduct

noncomputable section

universe u

/-! ## Universal first-order thickenings -/

/--
An extension is a universal first-order thickening when its kernel is
square-zero and it has the lifting property against every square-zero ideal.

The quotient map in the lifting property is Mathlib's canonical algebra map,
so the displayed equality is precisely the commutative diagram in the source.
-/
def IsUniversalFirstOrderThickening
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension.{u} R S) : Prop :=
  P.ker ^ 2 = ⊥ ∧
    ∀ {A : Type u} [CommRing A] [Algebra R A]
      (I : Ideal A) (_hI : I ^ 2 = ⊥) (a : S →ₐ[R] A ⧸ I),
      ∃! a' : P.Ring →ₐ[R] A,
        (Ideal.Quotient.mkₐ R I).comp a' =
          a.comp (IsScalarTower.toAlgHom R P.Ring S)

/-- A universal first-order thickening exists for every formally unramified map. -/
theorem exists_universal_first_order_thickening
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) :
    ∃ P : Algebra.Extension.{u} R S, IsUniversalFirstOrderThickening P := by
  sorry

/-- A chosen universal first-order thickening. -/
noncomputable def universalFirstOrderThickening
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) : Algebra.Extension.{u} R S :=
  Classical.choose (exists_universal_first_order_thickening h)

theorem universalFirstOrderThickening_isUniversal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) :
    IsUniversalFirstOrderThickening (universalFirstOrderThickening h) :=
  Classical.choose_spec (exists_universal_first_order_thickening h)

/-- The square-zero kernel of a universal first-order thickening. -/
abbrev universalFirstOrderThickeningKernel
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) :
    Ideal (universalFirstOrderThickening h).Ring :=
  (universalFirstOrderThickening h).ker

theorem universalFirstOrderThickening_kernel_square_zero
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) :
    universalFirstOrderThickeningKernel h ^ 2 = ⊥ :=
  (universalFirstOrderThickening_isUniversal h).1

/-- The algebra map underlying the chosen universal first-order thickening. -/
noncomputable def universalFirstOrderThickeningMap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) :
    (universalFirstOrderThickening h).Ring →ₐ[R] S :=
  IsScalarTower.toAlgHom R (universalFirstOrderThickening h).Ring S

theorem universalFirstOrderThickeningMap_surjective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) :
    Function.Surjective (universalFirstOrderThickeningMap h) :=
  (universalFirstOrderThickening h).algebraMap_surjective

/-- The conormal module, represented by Mathlib's canonical `I/I²` module. -/
abbrev conormalModule
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.FormallyUnramified R S) : Type u :=
  (universalFirstOrderThickening h).Cotangent

theorem universal_first_order_thickening_unique
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P Q : Algebra.Extension.{u} R S)
    (hP : IsUniversalFirstOrderThickening P)
    (hQ : IsUniversalFirstOrderThickening Q) :
    ∃! e : P.Ring ≃ₐ[R] Q.Ring,
      (IsScalarTower.toAlgHom R Q.Ring S).comp e.toAlgHom =
        IsScalarTower.toAlgHom R P.Ring S := by
  let pKer : Ideal P.Ring := RingHom.ker (Algebra.ofId P.Ring S)
  let qKer : Ideal Q.Ring := RingHom.ker (Algebra.ofId Q.Ring S)
  have hpKer : pKer = P.ker := by rfl
  have hqKer : qKer = Q.ker := by rfl
  let pEq₀ := Ideal.quotientKerAlgEquivOfRightInverse
    (f := Algebra.ofId P.Ring S) (g := P.σ) (by
      intro x
      exact P.algebraMap_σ x)
  let qEq₀ := Ideal.quotientKerAlgEquivOfRightInverse
    (f := Algebra.ofId Q.Ring S) (g := Q.σ) (by
      intro x
      exact Q.algebraMap_σ x)
  let pEq := pEq₀.restrictScalars R
  let qEq := qEq₀.restrictScalars R
  let pMap : P.Ring →ₐ[R] S := IsScalarTower.toAlgHom R P.Ring S
  let qMap : Q.Ring →ₐ[R] S := IsScalarTower.toAlgHom R Q.Ring S
  let pLift := pEq.symm.toAlgHom
  let qLift := qEq.symm.toAlgHom
  have hpSq : pKer ^ 2 = ⊥ := hpKer.symm ▸ hP.1
  have hqSq : qKer ^ 2 = ⊥ := hqKer.symm ▸ hQ.1
  obtain ⟨f, hf, hfu⟩ := hP.2 qKer hqSq qLift
  obtain ⟨g, hg, hgu⟩ := hQ.2 pKer hpSq pLift
  obtain ⟨uP, huP, huPu⟩ := hP.2 pKer hpSq pLift
  obtain ⟨uQ, huQ, huQu⟩ := hQ.2 qKer hqSq qLift
  have hpMap : pEq.toAlgHom.comp (Ideal.Quotient.mkₐ R pKer) = pMap := by
    apply AlgHom.ext
    intro x
    rfl
  have hqMap : qEq.toAlgHom.comp (Ideal.Quotient.mkₐ R qKer) = qMap := by
    apply AlgHom.ext
    intro x
    rfl
  have hpInv : pEq.toAlgHom.comp pLift = AlgHom.id R S := by
    apply AlgHom.ext
    intro x
    exact pEq.apply_symm_apply x
  have hqInv : qEq.toAlgHom.comp qLift = AlgHom.id R S := by
    apply AlgHom.ext
    intro x
    exact qEq.apply_symm_apply x
  have hpInv' : pLift.comp pEq.toAlgHom = AlgHom.id _ _ := by
    apply AlgHom.ext
    intro x
    exact pEq.symm_apply_apply x
  have hqInv' : qLift.comp qEq.toAlgHom = AlgHom.id _ _ := by
    apply AlgHom.ext
    intro x
    exact qEq.symm_apply_apply x
  have hpCancel (v : Q.Ring →ₐ[R] S) :
      pEq.toAlgHom.comp (pLift.comp v) = v := by
    rw [← AlgHom.comp_assoc, hpInv, AlgHom.id_comp]
  have hqCancel (v : P.Ring →ₐ[R] S) :
      qEq.toAlgHom.comp (qLift.comp v) = v := by
    rw [← AlgHom.comp_assoc, hqInv, AlgHom.id_comp]
  have hpAfterMk :
      pLift.comp (pEq.toAlgHom.comp (Ideal.Quotient.mkₐ R pKer)) =
        Ideal.Quotient.mkₐ R pKer := by
    rw [← AlgHom.comp_assoc, hpInv', AlgHom.id_comp]
  have hqAfterMk :
      qLift.comp (qEq.toAlgHom.comp (Ideal.Quotient.mkₐ R qKer)) =
        Ideal.Quotient.mkₐ R qKer := by
    rw [← AlgHom.comp_assoc, hqInv', AlgHom.id_comp]
  have hcompP :
      (Ideal.Quotient.mkₐ R pKer).comp (g.comp f) = pLift.comp pMap := by
    calc
      (Ideal.Quotient.mkₐ R pKer).comp (g.comp f) =
          ((Ideal.Quotient.mkₐ R pKer).comp g).comp f := by
            rw [AlgHom.comp_assoc]
      _ = (pLift.comp qMap).comp f := by rw [hg]
      _ = pLift.comp (qMap.comp f) := by rw [← AlgHom.comp_assoc]
      _ = pLift.comp (qEq.toAlgHom.comp
          ((Ideal.Quotient.mkₐ R qKer).comp f)) := by
            rw [← hqMap, AlgHom.comp_assoc]
      _ = pLift.comp (qEq.toAlgHom.comp (qLift.comp pMap)) := by rw [hf]
      _ = pLift.comp pMap := by rw [hqCancel]
  have hcompQ :
      (Ideal.Quotient.mkₐ R qKer).comp (f.comp g) = qLift.comp qMap := by
    calc
      (Ideal.Quotient.mkₐ R qKer).comp (f.comp g) =
          ((Ideal.Quotient.mkₐ R qKer).comp f).comp g := by
            rw [AlgHom.comp_assoc]
      _ = (qLift.comp pMap).comp g := by rw [hf]
      _ = qLift.comp (pMap.comp g) := by rw [← AlgHom.comp_assoc]
      _ = qLift.comp (pEq.toAlgHom.comp
          ((Ideal.Quotient.mkₐ R pKer).comp g)) := by
            rw [← hpMap, AlgHom.comp_assoc]
      _ = qLift.comp (pEq.toAlgHom.comp (pLift.comp qMap)) := by rw [hg]
      _ = qLift.comp qMap := by rw [hpCancel]
  have hIdP :
      (Ideal.Quotient.mkₐ R pKer).comp (AlgHom.id R P.Ring) = pLift.comp pMap := by
    calc
      (Ideal.Quotient.mkₐ R pKer).comp (AlgHom.id R P.Ring) =
          Ideal.Quotient.mkₐ R pKer := by rw [AlgHom.comp_id]
      _ = pLift.comp (pEq.toAlgHom.comp (Ideal.Quotient.mkₐ R pKer)) := by
        exact hpAfterMk.symm
      _ = pLift.comp pMap := by rw [hpMap]
  have hIdQ :
      (Ideal.Quotient.mkₐ R qKer).comp (AlgHom.id R Q.Ring) = qLift.comp qMap := by
    calc
      (Ideal.Quotient.mkₐ R qKer).comp (AlgHom.id R Q.Ring) =
          Ideal.Quotient.mkₐ R qKer := by rw [AlgHom.comp_id]
      _ = qLift.comp (qEq.toAlgHom.comp (Ideal.Quotient.mkₐ R qKer)) := by
        exact hqAfterMk.symm
      _ = qLift.comp qMap := by rw [hqMap]
  have hfg : g.comp f = AlgHom.id R P.Ring :=
    (huPu (g.comp f) hcompP).trans (huPu (AlgHom.id R P.Ring) hIdP).symm
  have hgf : f.comp g = AlgHom.id R Q.Ring :=
    (huQu (f.comp g) hcompQ).trans (huQu (AlgHom.id R Q.Ring) hIdQ).symm
  let e : P.Ring ≃ₐ[R] Q.Ring :=
    { f with
      invFun := g
      left_inv := by intro x; exact DFunLike.congr_fun hfg x
      right_inv := by intro x; exact DFunLike.congr_fun hgf x }
  have he : qMap.comp f = pMap := by
    calc
      qMap.comp f = qEq.toAlgHom.comp ((Ideal.Quotient.mkₐ R qKer).comp f) := by
        rw [← AlgHom.comp_assoc, hqMap]
      _ = qEq.toAlgHom.comp (qLift.comp pMap) := by rw [hf]
      _ = pMap := by rw [hqCancel]
  refine ⟨e, he, ?_⟩
  intro e' he'
  have he'f : e'.toAlgHom = f := hfu e'.toAlgHom (by
    calc
      (Ideal.Quotient.mkₐ R qKer).comp e'.toAlgHom =
          qLift.comp (qMap.comp e'.toAlgHom) := by
            apply AlgHom.ext
            intro x
            apply qEq.injective
            calc
              qEq ((Ideal.Quotient.mkₐ R qKer) (e' x)) = qMap (e' x) := by
                exact DFunLike.congr_fun hqMap (e' x)
              _ = qEq (qLift (qMap (e' x))) := by
                simpa only [AlgEquiv.coe_toAlgHom, AlgHom.comp_apply, AlgHom.id_apply] using
                  (DFunLike.congr_fun (hqCancel (qMap.comp e'.toAlgHom)) x).symm
      _ = qLift.comp pMap := by rw [he'])
  exact AlgEquiv.ext (by
    intro x
    exact DFunLike.congr_fun he'f x)

/-! ## Quotients -/

/-- The canonical extension `R/I² → R/I`. -/
noncomputable def quotientFirstOrderThickening
    {R : Type u} [CommRing R] (I : Ideal R) :
    Algebra.Extension.{u} R (R ⧸ I) := by
  let hI : I ^ 2 ≤ I := Ideal.pow_le_self two_ne_zero
  let f : (R ⧸ I ^ 2) →ₐ[R] (R ⧸ I) := Ideal.Quotient.factorₐ R hI
  exact Algebra.Extension.ofSurjective f (Ideal.Quotient.factor_surjective hI)

/-- The quotient map underlying `quotientFirstOrderThickening`. -/
noncomputable def quotientFirstOrderThickeningMap
    {R : Type u} [CommRing R] (I : Ideal R) :
    (quotientFirstOrderThickening I).Ring →ₐ[R] R ⧸ I :=
  IsScalarTower.toAlgHom R (quotientFirstOrderThickening I).Ring (R ⧸ I)

theorem quotientFirstOrderThickeningMap_surjective
    {R : Type u} [CommRing R] (I : Ideal R) :
    Function.Surjective (quotientFirstOrderThickeningMap I) :=
  (quotientFirstOrderThickening I).algebraMap_surjective

/-- The quotient `R/I² → R/I` is the universal first-order thickening. -/
theorem universal_first_order_thickening_quotient
    {R : Type u} [CommRing R] (I : Ideal R) :
    IsUniversalFirstOrderThickening (quotientFirstOrderThickening I) := by
  let hI : I ^ 2 ≤ I := Ideal.pow_le_self two_ne_zero
  change IsUniversalFirstOrderThickening
    (Algebra.Extension.ofSurjective (Ideal.Quotient.factorₐ R hI)
      (by
        intro x
        obtain ⟨y, hy⟩ := Ideal.Quotient.factor_surjective hI x
        exact ⟨y, by simpa only [Ideal.Quotient.factorₐ_apply] using hy⟩))
  unfold IsUniversalFirstOrderThickening
  constructor
  · change (RingHom.ker (Ideal.Quotient.factorₐ R hI).toRingHom) ^ 2 = ⊥
    have hker : RingHom.ker (Ideal.Quotient.factorₐ R hI).toRingHom =
        I.cotangentIdeal := by
      ext x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (I ^ 2) x
      change (Ideal.Quotient.factorₐ R hI) (Ideal.Quotient.mk (I ^ 2) x) = 0 ↔
        Ideal.Quotient.mk (I ^ 2) x ∈ I.cotangentIdeal
      rw [Ideal.Quotient.factorₐ_apply_mk]
      simp only [Ideal.Quotient.eq_zero_iff_mem, Ideal.mk_mem_cotangentIdeal]
    rw [hker]
    exact Ideal.cotangentIdeal_square I
  · intro A _ _ K hK a
    have hIle : I ≤ Ideal.comap (algebraMap R A) K := by
      intro x hx
      change algebraMap R A x ∈ K
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change algebraMap R (A ⧸ K) x = 0
      calc
        algebraMap R (A ⧸ K) x = a (algebraMap R (R ⧸ I) x) :=
          (AlgHom.commutes a x).symm
        _ = 0 := by
          change a (Ideal.Quotient.mk I x) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
    have hI2 : I ^ 2 ≤ RingHom.ker (algebraMap R A) := by
      rw [pow_two]
      refine Ideal.mul_le.mpr fun r hr s hs => ?_
      change algebraMap R A (r * s) = 0
      rw [map_mul]
      have hmul : algebraMap R A r * algebraMap R A s ∈ K * K :=
        Ideal.mul_mem_mul (hIle hr) (hIle hs)
      have hmul' : algebraMap R A r * algebraMap R A s ∈ K ^ 2 := by
        simpa only [pow_two] using hmul
      rw [hK] at hmul'
      simpa only [Submodule.mem_bot] using hmul'
    let b : (R ⧸ I ^ 2) →ₐ[R] A :=
      Ideal.Quotient.liftₐ (I ^ 2) (Algebra.ofId R A)
        (fun x hx => hI2 hx)
    refine ⟨b, ?_, ?_⟩
    · apply AlgHom.ext
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (I ^ 2) x
      change algebraMap R (A ⧸ K) x = a (algebraMap R (R ⧸ I) x)
      exact (AlgHom.commutes a x).symm
    · intro c hc
      apply Ideal.Quotient.algHom_ext (R₁ := R) (I := I ^ 2)
      have hc' : c.comp (Ideal.Quotient.mkₐ R (I ^ 2)) = Algebra.ofId R A := by
        apply AlgHom.ext
        intro x
        change c (algebraMap R (R ⧸ I ^ 2) x) = algebraMap R A x
        exact AlgHom.commutes c x
      have hb' : b.comp (Ideal.Quotient.mkₐ R (I ^ 2)) = Algebra.ofId R A := by
        apply AlgHom.ext
        intro x
        change b (algebraMap R (R ⧸ I ^ 2) x) = algebraMap R A x
        exact AlgHom.commutes b x
      exact hc'.trans hb'.symm

/-- The quotient description of the conormal module is `I/I²`. -/
abbrev quotientConormalModule
    {R : Type u} [CommRing R] (I : Ideal R) : Type u := I.Cotangent

theorem quotient_first_order_thickening_conormal
    {R : Type u} [CommRing R] (I : Ideal R) :
    Nonempty
      ((quotientFirstOrderThickening I).Cotangent ≃ₗ[R ⧸ I]
        quotientConormalModule I) := by
  let hI : I ^ 2 ≤ I := Ideal.pow_le_self two_ne_zero
  let P : Algebra.Extension R (R ⧸ I) :=
    Algebra.Extension.ofSurjective (Ideal.Quotient.factorₐ R hI)
      (by
        intro x
        obtain ⟨y, hy⟩ := Ideal.Quotient.factor_surjective hI x
        exact ⟨y, by simpa only [Ideal.Quotient.factorₐ_apply] using hy⟩)
  have hker : P.ker = I.cotangentIdeal := by
    change RingHom.ker (Ideal.Quotient.factorₐ R hI).toRingHom = _
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (I ^ 2) x
    change (Ideal.Quotient.factorₐ R hI) (Ideal.Quotient.mk (I ^ 2) x) = 0 ↔
      Ideal.Quotient.mk (I ^ 2) x ∈ I.cotangentIdeal
    rw [Ideal.Quotient.factorₐ_apply_mk]
    simp only [Ideal.Quotient.eq_zero_iff_mem, Ideal.mk_mem_cotangentIdeal]
  have heq : P.ker.comap (algebraMap R (R ⧸ I ^ 2)) =
      RingHom.ker (algebraMap R (R ⧸ I ^ 2)) ⊔ I := by
    rw [hker]
    change I.cotangentIdeal.comap (Ideal.Quotient.mk (I ^ 2)) =
      RingHom.ker (Ideal.Quotient.mk (I ^ 2)) ⊔ I
    rw [Ideal.comap_cotangentIdeal, Ideal.mk_ker]
    exact (sup_eq_right.mpr (show I ^ 2 ≤ I from Ideal.pow_le_self two_ne_zero)).symm
  let m : I.Cotangent →ₗ[R] P.ker.Cotangent :=
    Ideal.mapCotangent I P.ker (Algebra.ofId R (R ⧸ I ^ 2))
      (le_of_le_of_eq le_sup_right heq.symm)
  have hm_surj : Function.Surjective m := by
    exact Ideal.mapCotangent_surjective_of_comap_eq
      Ideal.Quotient.mk_surjective heq
  have hm_inj : Function.Injective m := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    obtain ⟨y, rfl⟩ := I.toCotangent_surjective y
    have hdiff : m (I.toCotangent (x - y)) = 0 := by
      rw [map_sub I.toCotangent, m.map_sub, sub_eq_zero.mpr hxy]
    have hdiff' : P.ker.toCotangent
        ⟨algebraMap R (R ⧸ I ^ 2) (x - y),
          (le_of_le_of_eq le_sup_right heq.symm) (sub_mem x.2 y.2)⟩ = 0 := by
      let z : I := x - y
      calc
        P.ker.toCotangent ⟨algebraMap R (R ⧸ I ^ 2) (x - y), _⟩ =
            m (I.toCotangent z) :=
          (Ideal.mapCotangent_toCotangent I P.ker
            (Algebra.ofId R (R ⧸ I ^ 2))
            (le_of_le_of_eq le_sup_right heq.symm) z).symm
        _ = 0 := by simpa only [z] using hdiff
    have hsq : P.ker ^ 2 = ⊥ := by
      rw [hker]
      exact Ideal.cotangentIdeal_square I
    have hdiffK : algebraMap R (R ⧸ I ^ 2) (x - y) ∈ P.ker ^ 2 :=
      (P.ker.toCotangent_eq_zero _).mp hdiff'
    rw [hsq] at hdiffK
    have hdiff0 : algebraMap R (R ⧸ I ^ 2) (x - y) = 0 := by
      exact Ideal.mem_bot.mp hdiffK
    apply I.toCotangent_eq.mpr
    exact Ideal.Quotient.eq_zero_iff_mem.mp hdiff0
  let m' : I.Cotangent →ₗ[R ⧸ I] P.Cotangent :=
    { toFun := fun x => Algebra.Extension.Cotangent.of (m x)
      map_add' := m.map_add
      map_smul' := by
        intro r x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
        apply Algebra.Extension.Cotangent.ext
        change m (r • I.toCotangent x) = P.σ (Ideal.Quotient.mk I r) • m (I.toCotangent x)
        rw [m.map_smul]
        have hσ : P.σ (Ideal.Quotient.mk I r) -
            algebraMap R P.Ring r ∈ P.ker := by
          apply RingHom.mem_ker.mp
          change algebraMap P.Ring (R ⧸ I) (P.σ (Ideal.Quotient.mk I r) -
            algebraMap R P.Ring r) = 0
          rw [map_sub, P.algebraMap_σ]
          rw [← IsScalarTower.algebraMap_apply R P.Ring (R ⧸ I),
            Ideal.Quotient.algebraMap_eq]
          exact sub_self _
        have hz := Algebra.Extension.Cotangent.smul_eq_zero_of_mem
          (P.σ (Ideal.Quotient.mk I r) - algebraMap R P.Ring r) hσ
          (m (I.toCotangent x))
        rw [sub_smul] at hz
        rw [← algebraMap_smul P.Ring]
        exact (sub_eq_zero.mp hz).symm }
  have hm'_inj : Function.Injective m' := by
    intro x y hxy
    change Algebra.Extension.Cotangent.of (m x) =
      Algebra.Extension.Cotangent.of (m y) at hxy
    apply hm_inj
    exact congrArg Algebra.Extension.Cotangent.val hxy
  have hm'_surj : Function.Surjective m' := by
    intro x
    obtain ⟨y, hy⟩ := hm_surj x.val
    refine ⟨y, ?_⟩
    change Algebra.Extension.Cotangent.of (m y) = x
    apply Algebra.Extension.Cotangent.ext
    simpa only [Algebra.Extension.Cotangent.val_of] using hy
  have hm'_bij : Function.Bijective m' := ⟨hm'_inj, hm'_surj⟩
  change Nonempty (P.Cotangent ≃ₗ[R ⧸ I] I.Cotangent)
  exact ⟨(LinearEquiv.ofBijective m' hm'_bij).symm⟩

theorem conormalModule_quotient
    {R : Type u} [CommRing R] (I : Ideal R)
    (h : Algebra.FormallyUnramified R (R ⧸ I)) :
    Nonempty
      (conormalModule h ≃ₗ[R ⧸ I] quotientConormalModule I) := by
  let P := universalFirstOrderThickening h
  let Q := quotientFirstOrderThickening I
  have hP : IsUniversalFirstOrderThickening P :=
    universalFirstOrderThickening_isUniversal h
  have hQ : IsUniversalFirstOrderThickening Q :=
    universal_first_order_thickening_quotient I
  obtain ⟨e, he, _⟩ := universal_first_order_thickening_unique P Q hP hQ
  have he' :
      (IsScalarTower.toAlgHom R Q.Ring (R ⧸ I)).comp e.toAlgHom =
        IsScalarTower.toAlgHom R P.Ring (R ⧸ I) := he
  let f : P.Hom Q := Algebra.Extension.Hom.ofAlgHom e.toAlgHom he'
  let g : Q.Hom P :=
    Algebra.Extension.Hom.ofAlgHom e.symm.toAlgHom (by
      apply AlgHom.ext
      intro x
      have hx := congrArg (fun k => k (e.symm x)) he'
      change (IsScalarTower.toAlgHom R P.Ring (R ⧸ I)) (e.symm x) =
        (IsScalarTower.toAlgHom R Q.Ring (R ⧸ I)) x
      have hx' :
          (IsScalarTower.toAlgHom R P.Ring (R ⧸ I)) (e.symm x) =
            (IsScalarTower.toAlgHom R Q.Ring (R ⧸ I))
              (e.toAlgHom (e.symm x)) := by
        simpa only [AlgHom.comp_apply] using hx.symm
      exact hx'.trans (congrArg (IsScalarTower.toAlgHom R Q.Ring (R ⧸ I))
        (e.apply_symm_apply x)))
  have hgf : g.comp f = Algebra.Extension.Hom.id P := by
    ext x
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  have hfg : f.comp g = Algebra.Extension.Hom.id Q := by
    ext x
    change e (e.symm x) = x
    exact e.apply_symm_apply x
  let mf : P.Cotangent →ₗ[R ⧸ I] Q.Cotangent :=
    Algebra.Extension.Cotangent.map f
  let mg : Q.Cotangent →ₗ[R ⧸ I] P.Cotangent :=
    Algebra.Extension.Cotangent.map g
  have hmgf :
      mg.restrictScalars (R ⧸ I) ∘ₗ mf = LinearMap.id := by
    rw [← Algebra.Extension.Cotangent.map_comp, hgf,
      Algebra.Extension.Cotangent.map_id]
  have hmfg :
      mf.restrictScalars (R ⧸ I) ∘ₗ mg = LinearMap.id := by
    rw [← Algebra.Extension.Cotangent.map_comp, hfg,
      Algebra.Extension.Cotangent.map_id]
  have hmf_inj : Function.Injective mf := by
    intro x y hxy
    have hx := LinearMap.congr_fun hmgf x
    have hy := LinearMap.congr_fun hmgf y
    calc
      x = mg (mf x) := by simpa using hx.symm
      _ = mg (mf y) := by rw [hxy]
      _ = y := by simpa using hy
  have hmf_surj : Function.Surjective mf := by
    intro y
    refine ⟨mg y, ?_⟩
    simpa using LinearMap.congr_fun hmfg y
  let E : P.Cotangent ≃ₗ[R ⧸ I] Q.Cotangent :=
    LinearEquiv.ofBijective mf ⟨hmf_inj, hmf_surj⟩
  obtain ⟨q⟩ := quotient_first_order_thickening_conormal I
  exact ⟨by
    simpa [P, Q, conormalModule, quotientConormalModule] using E.trans q⟩

/-! ## Localization -/

/-- The multiplicative subset in an extension ring lying over a target subset. -/
def localizationPreimage
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension.{u} R S) (M : Submonoid S) : Submonoid P.Ring :=
  M.comap (algebraMap P.Ring S)

/- The source's base-localization statement uses the localization of the
   extension ring at the image of the base multiplicative set.  This is the
   canonical ring map from that localization to the localized target. -/
noncomputable def baseLocalizationMap
    {A B Bₘ : Type u} [CommRing A] [CommRing B] [CommRing Bₘ]
    [Algebra A B] [Algebra B Bₘ] [Algebra A Bₘ] [IsScalarTower A B Bₘ]
    (P : Algebra.Extension.{u} A B) (M : Submonoid A)
    [IsLocalization (M.map (algebraMap A B)) Bₘ] :
    Localization (M.map (algebraMap A P.Ring)) →+* Bₘ := by
  let h : ∀ y : M.map (algebraMap A P.Ring),
      IsUnit ((algebraMap B Bₘ)
        ((algebraMap P.Ring B) (y : P.Ring))) := by
    rintro ⟨_, ⟨a, ha, rfl⟩⟩
    change IsUnit ((algebraMap B Bₘ)
      ((algebraMap P.Ring B) ((algebraMap A P.Ring) a)))
    rw [← IsScalarTower.algebraMap_apply A P.Ring B]
    exact IsLocalization.map_units Bₘ
      ⟨algebraMap A B a, Submonoid.mem_map_of_mem (algebraMap A B) ha⟩
  exact IsLocalization.lift (M := M.map (algebraMap A P.Ring))
    (g := (algebraMap B Bₘ).comp (IsScalarTower.toAlgHom A P.Ring B).toRingHom) h

/-- Localization of the target preserves the universal first-order property.

`P.localization M` has underlying ring
`(M.comap (algebraMap P.Ring S))⁻¹P.Ring`, which is the source's `S'⁻¹B'`.
-/
theorem universal_first_order_thickening_localize_target
    {A B B' : Type u} [CommRing A] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra B B'] [Algebra A B']
    [IsScalarTower A B B']
    (hAB : Algebra.FormallyUnramified A B)
    (P : Algebra.Extension.{u} A B)
    (hP : IsUniversalFirstOrderThickening P)
    (M : Submonoid B) [IsLocalization M B'] :
    IsUniversalFirstOrderThickening (P.localization (S' := B') M) ∧
      Nonempty
        (B' ⊗[B] P.Cotangent ≃ₗ[B'] (P.localization (S' := B') M).Cotangent) := by
  sorry

/-- Localization of the base preserves the universal first-order property.

The base and target localization rings may be arbitrary chosen models; the
extension ring in the conclusion is the canonical localization of `P.Ring`.
-/
theorem universal_first_order_thickening_localize_base
    {A B Aₘ Bₘ : Type u} [CommRing A] [CommRing B] [CommRing Aₘ] [CommRing Bₘ]
    [Algebra A B] [Algebra A Aₘ] [Algebra B Bₘ] [Algebra A Bₘ]
    [Algebra Aₘ Bₘ] [IsScalarTower A Aₘ Bₘ] [IsScalarTower A B Bₘ]
    (hAB : Algebra.FormallyUnramified A B)
    (M : Submonoid A) [IsLocalization M Aₘ]
    [IsLocalization (M.map (algebraMap A B)) Bₘ]
    (P : Algebra.Extension.{u} A B)
    (hP : IsUniversalFirstOrderThickening P)
    :
    letI : IsLocalization (Algebra.algebraMapSubmonoid P.Ring M)
        (Localization (M.map (algebraMap A P.Ring))) := by
      simpa only [Algebra.algebraMapSubmonoid] using
        (inferInstance : IsLocalization (M.map (algebraMap A P.Ring))
          (Localization (M.map (algebraMap A P.Ring))))
    letI : Algebra Aₘ (Localization (M.map (algebraMap A P.Ring))) :=
      localizationAlgebra M P.Ring
    ∃ Q : Algebra.Extension.{u} Aₘ Bₘ,
      IsUniversalFirstOrderThickening Q ∧
        Nonempty (Bₘ ⊗[B] P.Cotangent ≃ₗ[Bₘ] Q.Cotangent) ∧
        ∃ e : Q.Ring ≃ₐ[Aₘ] Localization (M.map (algebraMap A P.Ring)),
          ((IsScalarTower.toAlgHom Aₘ Q.Ring Bₘ : Q.Ring →ₐ[Aₘ] Bₘ).toRingHom) =
            (baseLocalizationMap (Bₘ := Bₘ) P M).comp
              e.toRingEquiv.toRingHom := by
  sorry

/-! ## Differentials -/

/-- The canonical differential map in the final lemma of the source section.

It is the base change to `B` of the Kähler differential map induced by
`A → P.Ring`, with codomain
`B ⊗[P.Ring] Ω[P.Ring⁄R]`.  This is deliberately not `P.CotangentSpace`,
which uses differentials relative to `A`.
-/
noncomputable def differentialComparisonMap
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (P : Algebra.Extension.{u} A B) :
    B ⊗[A] KaehlerDifferential R A →ₗ[B]
      B ⊗[P.Ring] KaehlerDifferential R P.Ring :=
  let q : KaehlerDifferential R P.Ring →ₗ[A]
      B ⊗[P.Ring] KaehlerDifferential R P.Ring :=
    by
      exact (TensorProduct.mk P.Ring B (KaehlerDifferential R P.Ring) 1).restrictScalars A
  LinearMap.liftBaseChange B (q ∘ₗ KaehlerDifferential.map R R A P.Ring)

/-- The canonical differential map is an isomorphism for the universal
first-order thickening. -/
theorem differentialComparisonMap_bijective
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (hAB : Algebra.FormallyUnramified A B)
    (P : Algebra.Extension.{u} A B)
    (hP : IsUniversalFirstOrderThickening P) :
    Function.Bijective (differentialComparisonMap (R := R) (A := A) (B := B) P) := by
  sorry

/--
The canonical linear equivalence induced by the differential comparison map.

This packages the source's assertion that the comparison map is an isomorphism
in a reusable form, while `differentialComparisonMap` remains available when
the actual canonical map is needed.
-/
noncomputable def differentialComparisonEquiv
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (hAB : Algebra.FormallyUnramified A B)
    (P : Algebra.Extension.{u} A B)
    (hP : IsUniversalFirstOrderThickening P) :
    B ⊗[A] KaehlerDifferential R A ≃ₗ[B]
      B ⊗[P.Ring] KaehlerDifferential R P.Ring :=
  LinearEquiv.ofBijective (differentialComparisonMap (R := R) (A := A) (B := B) P)
    (differentialComparisonMap_bijective (R := R) (A := A) (B := B) hAB P hP)

/-- If `A → B` is formally unramified, its universal thickening remains
formally unramified over `A`. -/
theorem universal_first_order_thickening_formallyUnramified
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hAB : Algebra.FormallyUnramified A B)
    (P : Algebra.Extension.{u} A B)
    (hP : IsUniversalFirstOrderThickening P) :
    Algebra.FormallyUnramified A P.Ring := by
  sorry

/-- Differential comparison for a universal first-order thickening.

The displayed equivalence is the source's canonical map
`Ω[A/R] ⊗[A] B → Ω[P.Ring/R] ⊗[P.Ring] B`, with the target written as
the explicit base-changed differential module.
-/
theorem differentials_universal_first_order_thickening
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (hAB : Algebra.FormallyUnramified A B)
    (P : Algebra.Extension.{u} A B)
    (hP : IsUniversalFirstOrderThickening P) :
    Algebra.FormallyUnramified A P.Ring ∧
      Nonempty
        (B ⊗[A] KaehlerDifferential R A ≃ₗ[B]
          B ⊗[P.Ring] KaehlerDifferential R P.Ring) := by
  exact ⟨universal_first_order_thickening_formallyUnramified hAB P hP,
    ⟨differentialComparisonEquiv hAB P hP⟩⟩

end

end Formalization.Books.Algebra.Unit149
