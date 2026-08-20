import Formalization.Books.Algebra.Unit113.DimensionFormula
import Formalization.Books.Algebra.Unit122.QuasiFinite
import Formalization.Books.Algebra.Unit144.LocalStructureEtaleRingMaps
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.Etale

/-!
# Commutative Algebra, Chapter 145: Étale local structure of quasi-finite ring maps

The four lemmas in the source section are stated below.  The product
presentations keep the algebra structures and the maps from the original
tensor product explicit, so that the assertions about primes are usable by
later chapters.
-/

namespace Formalization.Books.Algebra.Unit145

open Set
open scoped TensorProduct

noncomputable section

universe u

/-! ## 145.1 Étale local structure of quasi-finite ring maps -/

/- The introductory remarks recall the openness and base-change properties of
quasi-finite loci from the preceding quasi-finite chapter; they are not
duplicated here. -/

/-- A binary product presentation of an algebra over `R`, with its factor
maps retained for transporting primes from the original algebra. -/
structure BinaryAlgebraProduct
    (R X : Type u) [CommRing R] [CommRing X] [Algebra R X] where
  A : Type u
  [commRingA : CommRing A]
  [algebraA : Algebra R A]
  B : Type u
  [commRingB : CommRing B]
  [algebraB : Algebra R B]
  equiv : X ≃ₐ[R] A × B

def BinaryAlgebraProduct.leftMap
    {R X : Type u} [CommRing R] [CommRing X] [Algebra R X]
    (D : BinaryAlgebraProduct R X) :
    letI : CommRing D.A := D.commRingA
    letI : CommRing D.B := D.commRingB
    X →+* D.A := by
  letI : CommRing D.A := D.commRingA
  letI : CommRing D.B := D.commRingB
  exact
    { toFun := fun x => (D.equiv x).1
      map_one' := by simp
      map_mul' := by intro x y; simp
      map_zero' := by simp
      map_add' := by intro x y; simp }

def BinaryAlgebraProduct.rightMap
    {R X : Type u} [CommRing R] [CommRing X] [Algebra R X]
    (D : BinaryAlgebraProduct R X) :
    letI : CommRing D.A := D.commRingA
    letI : CommRing D.B := D.commRingB
    X →+* D.B := by
  letI : CommRing D.A := D.commRingA
  letI : CommRing D.B := D.commRingB
  exact
    { toFun := fun x => (D.equiv x).2
      map_one' := by simp
      map_mul' := by intro x y; simp
      map_zero' := by simp
      map_add' := by intro x y; simp }

/-- After localizing at an element, the finite map supplied by the first
source lemma.  The bijectivity assumption is stronger than the surjectivity
used by Mathlib's `Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ`,
and records the source's stated isomorphism exactly at the ring-map level. -/
theorem produce_finite
    {R S' S : Type u} [CommRing R] [CommRing S'] [CommRing S]
    (f : R →+* S') (g : S' →+* S) (p : PrimeSpectrum R) (s : S')
    (hintegral : f.IsIntegral)
    (hfiniteType : (g.comp f).FiniteType)
    (hloc : Function.Bijective (Localization.awayMap g s))
    (hinvertible :
      letI : Algebra R S' := f.toAlgebra
      IsUnit (algebraMap S' (S' ⊗[R] p.asIdeal.ResidueField) s)) :
    ∃ r : R, r ∉ p.asIdeal ∧
      RingHom.Finite (Localization.awayMap (g.comp f) r) := by
  letI : Algebra R S' := f.toAlgebra
  letI : Algebra S' S := g.toAlgebra
  letI : Algebra R S := (g.comp f).toAlgebra
  letI : IsScalarTower R S' S := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  let F : S' →ₐ[R] S :=
    { g with
      commutes' := by
        intro r
        rfl }
  letI : Algebra.FiniteType R S := hfiniteType
  let hintegral' : (algebraMap R S').IsIntegral := by
    simpa [RingHom.algebraMap_toAlgebra] using hintegral
  letI : Algebra.IsIntegral R S' := algebraMap_isIntegral_iff.mp hintegral'
  have hsurj : Function.Surjective (Localization.awayMapₐ F s) := by
    have hmap : (Localization.awayMapₐ F s).toRingHom = Localization.awayMap g s := by
      ext x
      rfl
    change Function.Surjective (Localization.awayMapₐ F s).toRingHom
    rw [hmap]
    simpa using hloc.2
  have hunit : IsUnit (1 ⊗ₜ[R] s : p.asIdeal.Fiber S') := by
    have h := hinvertible
    have h' := h.map (Algebra.TensorProduct.commRight R S' p.asIdeal.ResidueField).toRingHom
    simpa [Algebra.TensorProduct.commRight_tmul] using h'
  obtain ⟨r, hr, hfin⟩ :=
    Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ F s hsurj
      p.asIdeal hunit
  refine ⟨r, hr, ?_⟩
  have hF : F.toRingHom = g := by
    ext x
    rfl
  have hmap : (Localization.awayMapₐ (Algebra.ofId R S) r).toRingHom =
      Localization.awayMap (g.comp f) r := by
    ext x
    rfl
  exact hmap ▸ hfin

/-- Data for the étale neighborhood and product decomposition around one
quasi-finite prime.  Bijectivity of the canonical residue-field map records
the source's notation `κ(p) = κ(p')`. -/
structure EtaleFiniteAtPrimeData
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) where
  R' : Type u
  [commRingR' : CommRing R']
  [algebraRR' : Algebra R R']
  etale : RingHom.Etale (algebraMap R R')
  p' : PrimeSpectrum R'
  liesOver : PrimeSpectrum.comap (algebraMap R R') p' = p
  residueFieldMapBijective :
    Function.Bijective
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt
        (algebraMap R R') p p' liesOver)
  decomposition : BinaryAlgebraProduct R' (R' ⊗[R] S)
  finiteA : letI : CommRing decomposition.A := decomposition.commRingA
    letI : Algebra R' decomposition.A := decomposition.algebraA
    RingHom.Finite (algebraMap R' decomposition.A)
  uniquePrime : letI : CommRing decomposition.A := decomposition.commRingA
    letI : Algebra R' decomposition.A := decomposition.algebraA
    ∃! r : PrimeSpectrum decomposition.A,
      PrimeSpectrum.comap (algebraMap R' decomposition.A) r = p'
  primeOverQ : letI : CommRing decomposition.A := decomposition.commRingA
    letI : Algebra R' decomposition.A := decomposition.algebraA
    ∀ r : PrimeSpectrum decomposition.A,
      PrimeSpectrum.comap (algebraMap R' decomposition.A) r = p' →
        PrimeSpectrum.comap
            (decomposition.leftMap.comp
              Algebra.TensorProduct.includeRight.toRingHom) r = q
  noPrimeB : letI : CommRing decomposition.B := decomposition.commRingB
    letI : Algebra R' decomposition.B := decomposition.algebraB
    ∀ r : PrimeSpectrum decomposition.B,
      PrimeSpectrum.comap (algebraMap R' decomposition.B) r = p' →
        PrimeSpectrum.comap
            (decomposition.rightMap.comp
              Algebra.TensorProduct.includeRight.toRingHom) r ≠ q

/-- Étale local structure at one quasi-finite prime. -/
theorem etale_makes_quasiFinite_finite_one_prime
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    (hfiniteType : f.FiniteType)
    (hquasi : Formalization.Books.Algebra.Unit122.IsQuasiFiniteAt f q) :
    letI : Algebra R S := f.toAlgebra
    Nonempty (EtaleFiniteAtPrimeData f p q hq) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra.FiniteType R S := hfiniteType
  letI : Algebra.QuasiFiniteAt R q.asIdeal := hquasi.2
  have hq' : q.asIdeal.LiesOver p.asIdeal := by
    rw [Ideal.liesOver_iff, Ideal.under_def]
    simpa [PrimeSpectrum.comap_asIdeal, RingHom.algebraMap_toAlgebra] using
      (congrArg PrimeSpectrum.asIdeal hq).symm
  obtain ⟨R', _, _, hEtale, P, hPprime, hPover, e, he, P', hP'prime,
      hP'over, hPq, heP', hres, hfinite, hunique⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq
      (p := p.asIdeal) (q := q.asIdeal)
  let pprime : PrimeSpectrum R' := ⟨P, hPprime⟩
  have hpprime : PrimeSpectrum.comap (algebraMap R R') pprime = p := by
    apply PrimeSpectrum.ext
    change P.comap (algebraMap R R') = p.asIdeal
    exact hPover.over.symm
  have hresprime : Function.Bijective
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt
        (algebraMap R R') p pprime hpprime) := by
    simpa [Formalization.Books.Algebra.Unit113.residueFieldMapAt, pprime,
      Ideal.ResidueField.mapₐ, RingHom.algebraMap_toAlgebra] using hres
  let A := Localization.Away e
  let B := Localization.Away (1 - e)
  letI : IsLocalization.Away e
      ((R' ⊗[R] S) ⧸ Ideal.span ({1 - e} : Set (R' ⊗[R] S))) :=
    IsLocalization.Away.quotient_of_isIdempotentElem he
  letI : IsLocalization.Away (1 - e)
      ((R' ⊗[R] S) ⧸ Ideal.span ({e} : Set (R' ⊗[R] S))) := by
    have h := IsLocalization.Away.quotient_of_isIdempotentElem he.one_sub
    rw [sub_sub_cancel] at h
    exact h
  let awayE : A ≃ₐ[R']
      ((R' ⊗[R] S) ⧸ Ideal.span ({1 - e} : Set (R' ⊗[R] S))) :=
    (IsLocalization.algEquiv (Submonoid.powers e) A _).restrictScalars R'
  let awayOneSub : B ≃ₐ[R']
      ((R' ⊗[R] S) ⧸ Ideal.span ({e} : Set (R' ⊗[R] S))) :=
    (IsLocalization.algEquiv (Submonoid.powers (1 - e)) B _).restrictScalars R'
  let qprod : (R' ⊗[R] S) ≃ₐ[R']
      ((R' ⊗[R] S) ⧸ Ideal.span ({1 - e} : Set (R' ⊗[R] S))) ×
        ((R' ⊗[R] S) ⧸ Ideal.span ({e} : Set (R' ⊗[R] S))) :=
    (AlgEquiv.prodQuotientOfIsIdempotentElem (R := R' ⊗[R] S) he.one_sub he
      (by ring) (by simpa using he.one_sub_mul_self)).restrictScalars R'
  let decomposition : (R' ⊗[R] S) ≃ₐ[R'] A × B :=
    qprod.trans (AlgEquiv.prodCongr awayE.symm awayOneSub.symm)
  let binary : BinaryAlgebraProduct R' (R' ⊗[R] S) :=
    { A := A, B := B, equiv := decomposition }
  let etale' : RingHom.Etale (algebraMap R R') := RingHom.etale_algebraMap.mpr hEtale
  refine ⟨EtaleFiniteAtPrimeData.mk (R' := R') etale' pprime hpprime hresprime
    binary ?_ ?_ ?_ ?_⟩
  · simpa [binary] using hfinite
  · let r0Ideal : Ideal A := P'.map (algebraMap (R' ⊗[R] S) A)
    have hdisj : Disjoint (Submonoid.powers e : Set (R' ⊗[R] S)) (P' : Set (R' ⊗[R] S)) := by
      rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
      exact heP'
    have hr0prime : r0Ideal.IsPrime := by
      exact IsLocalization.isPrime_of_isPrime_disjoint
        (Submonoid.powers e) A P' hP'prime hdisj
    let r0 : PrimeSpectrum A := ⟨r0Ideal, hr0prime⟩
    have hr0under : r0Ideal.comap (algebraMap (R' ⊗[R] S) A) = P' := by
      exact IsLocalization.under_map_of_isPrime_disjoint
        (Submonoid.powers e) A hP'prime hdisj
    have hr0over : PrimeSpectrum.comap (algebraMap R' A) r0 = pprime := by
      apply PrimeSpectrum.ext
      change r0Ideal.comap (algebraMap R' A) = P
      rw [IsScalarTower.algebraMap_eq R' (R' ⊗[R] S) A]
      rw [← Ideal.comap_comap, hr0under]
      exact (hP'over.over).symm
    refine ⟨r0, hr0over, ?_⟩
    intro r hr
    let P'' : Ideal (R' ⊗[R] S) := r.asIdeal.comap (algebraMap (R' ⊗[R] S) A)
    have hP''prime : P''.IsPrime := Ideal.comap_isPrime _ _
    have hP''over : P''.LiesOver P := by
      rw [Ideal.liesOver_iff, Ideal.under_def]
      simpa [P'', ← IsScalarTower.algebraMap_eq R' (R' ⊗[R] S) A,
        Ideal.comap_comap, PrimeSpectrum.comap_asIdeal, binary] using
        (congrArg PrimeSpectrum.asIdeal hr).symm
    have heP'' : e ∉ P'' := by
      intro heP''
      change algebraMap (R' ⊗[R] S) A e ∈ r.asIdeal at heP''
      exact (Ideal.notMem_of_isUnit _
        (IsLocalization.Away.algebraMap_isUnit e)) heP''
    have hEq : P'' = P' := hunique P'' hP''prime hP''over heP''
    apply PrimeSpectrum.localization_comap_injective A (Submonoid.powers e)
    apply PrimeSpectrum.ext
    simpa [P'', r0, r0Ideal, hr0under] using hEq
  · intro r hr
    have hleft : BinaryAlgebraProduct.leftMap binary =
        algebraMap (R' ⊗[R] S) A := by
      ext x
      · change (IsLocalization.algEquiv (Submonoid.powers e)
          (R' ⊗[R] S ⧸ Ideal.span ({1 - e} : Set (R' ⊗[R] S))) A)
          ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set (R' ⊗[R] S))))
            (x ⊗ₜ[R] 1)) =
          (algebraMap (R' ⊗[R] S) A) (x ⊗ₜ[R] 1)
        have hmk :
            (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set (R' ⊗[R] S))))
                (x ⊗ₜ[R] 1) =
              IsLocalization.mk' (M := Submonoid.powers e)
                (R' ⊗[R] S ⧸ Ideal.span ({1 - e} : Set (R' ⊗[R] S)))
                (x ⊗ₜ[R] 1) (1 : Submonoid.powers e) := by
          rw [IsLocalization.mk'_one]
          rfl
        rw [hmk, IsLocalization.algEquiv_mk', IsLocalization.mk'_one]
      · change (IsLocalization.algEquiv (Submonoid.powers e)
          (R' ⊗[R] S ⧸ Ideal.span ({1 - e} : Set (R' ⊗[R] S))) A)
          ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set (R' ⊗[R] S))))
            (1 ⊗ₜ[R] x)) =
          (algebraMap (R' ⊗[R] S) A) (1 ⊗ₜ[R] x)
        have hmk :
            (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set (R' ⊗[R] S))))
                (1 ⊗ₜ[R] x) =
              IsLocalization.mk' (M := Submonoid.powers e)
                (R' ⊗[R] S ⧸ Ideal.span ({1 - e} : Set (R' ⊗[R] S)))
                (1 ⊗ₜ[R] x) (1 : Submonoid.powers e) := by
          rw [IsLocalization.mk'_one]
          rfl
        rw [hmk, IsLocalization.algEquiv_mk', IsLocalization.mk'_one]
    let P'' : Ideal (R' ⊗[R] S) := r.asIdeal.comap (algebraMap (R' ⊗[R] S) A)
    have hP''prime : P''.IsPrime := Ideal.comap_isPrime _ _
    have hP''over : P''.LiesOver P := by
      rw [Ideal.liesOver_iff, Ideal.under_def]
      simpa [P'', ← IsScalarTower.algebraMap_eq R' (R' ⊗[R] S) A,
        Ideal.comap_comap, PrimeSpectrum.comap_asIdeal, binary] using
        (congrArg PrimeSpectrum.asIdeal hr).symm
    have heP'' : e ∉ P'' := by
      intro heP''
      change algebraMap (R' ⊗[R] S) A e ∈ r.asIdeal at heP''
      exact (Ideal.notMem_of_isUnit _
        (IsLocalization.Away.algebraMap_isUnit e)) heP''
    have hEq : P'' = P' := hunique P'' hP''prime hP''over heP''
    apply PrimeSpectrum.ext
    rw [hleft]
    change P''.comap Algebra.TensorProduct.includeRight.toRingHom = q.asIdeal
    rw [hEq]
    exact hPq
  · intro r hr
    have hright : BinaryAlgebraProduct.rightMap binary =
        algebraMap (R' ⊗[R] S) B := by
      ext x
      · change (IsLocalization.algEquiv (Submonoid.powers (1 - e))
          (R' ⊗[R] S ⧸ Ideal.span ({e} : Set (R' ⊗[R] S))) B)
          ((Ideal.Quotient.mk (Ideal.span ({e} : Set (R' ⊗[R] S))))
            (x ⊗ₜ[R] 1)) =
          (algebraMap (R' ⊗[R] S) B) (x ⊗ₜ[R] 1)
        have hmk :
            (Ideal.Quotient.mk (Ideal.span ({e} : Set (R' ⊗[R] S))))
                (x ⊗ₜ[R] 1) =
              IsLocalization.mk' (M := Submonoid.powers (1 - e))
                (R' ⊗[R] S ⧸ Ideal.span ({e} : Set (R' ⊗[R] S)))
                (x ⊗ₜ[R] 1) (1 : Submonoid.powers (1 - e)) := by
          rw [IsLocalization.mk'_one]
          rfl
        rw [hmk, IsLocalization.algEquiv_mk', IsLocalization.mk'_one]
      · change (IsLocalization.algEquiv (Submonoid.powers (1 - e))
          (R' ⊗[R] S ⧸ Ideal.span ({e} : Set (R' ⊗[R] S))) B)
          ((Ideal.Quotient.mk (Ideal.span ({e} : Set (R' ⊗[R] S))))
            (1 ⊗ₜ[R] x)) =
          (algebraMap (R' ⊗[R] S) B) (1 ⊗ₜ[R] x)
        have hmk :
            (Ideal.Quotient.mk (Ideal.span ({e} : Set (R' ⊗[R] S))))
                (1 ⊗ₜ[R] x) =
              IsLocalization.mk' (M := Submonoid.powers (1 - e))
                (R' ⊗[R] S ⧸ Ideal.span ({e} : Set (R' ⊗[R] S)))
                (1 ⊗ₜ[R] x) (1 : Submonoid.powers (1 - e)) := by
          rw [IsLocalization.mk'_one]
          rfl
        rw [hmk, IsLocalization.algEquiv_mk', IsLocalization.mk'_one]
    let P'' : Ideal (R' ⊗[R] S) := r.asIdeal.comap (algebraMap (R' ⊗[R] S) B)
    have hP''prime : P''.IsPrime := Ideal.comap_isPrime _ _
    have hP''over : P''.LiesOver P := by
      rw [Ideal.liesOver_iff, Ideal.under_def]
      simpa [P'', ← IsScalarTower.algebraMap_eq R' (R' ⊗[R] S) B,
        Ideal.comap_comap, PrimeSpectrum.comap_asIdeal] using
        (congrArg PrimeSpectrum.asIdeal hr).symm
    have hzero : algebraMap (R' ⊗[R] S) B e = 0 := by
      rw [IsLocalization.map_eq_zero_iff (M := Submonoid.powers (1 - e))]
      refine ⟨⟨1 - e, Submonoid.mem_powers _⟩, ?_⟩
      simpa [mul_comm] using he.one_sub_mul_self
    have heP'' : e ∈ P'' := by
      change algebraMap (R' ⊗[R] S) B e ∈ r.asIdeal
      rw [hzero]
      exact r.asIdeal.zero_mem
    intro hqeq
    have hP''q : P''.comap Algebra.TensorProduct.includeRight.toRingHom =
        P'.comap Algebra.TensorProduct.includeRight.toRingHom := by
      rw [hPq]
      simpa [P'', hright, PrimeSpectrum.comap_asIdeal, Ideal.comap_comap] using
        (congrArg PrimeSpectrum.asIdeal hqeq)
    letI : P''.IsPrime := hP''prime
    letI : P''.LiesOver P := hP''over
    letI : P'.IsPrime := hP'prime
    letI : P'.LiesOver P := hP'over
    have hEq : P'' = P' :=
      Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hres P'' P' hP''q
    exact heP' (hEq ▸ heP'')

/-! The finite-product version is indexed by the finite set of isolated
closed points in the fibre. -/

/-- A finite product presentation of an algebra over `R`. -/
structure FiniteAlgebraProduct
    (R X : Type u) [CommRing R] [CommRing X] [Algebra R X] where
  n : ℕ
  A : Fin n → Type u
  [commRingA : ∀ i, CommRing (A i)]
  [algebraA : ∀ i, Algebra R (A i)]
  B : Type u
  [commRingB : CommRing B]
  [algebraB : Algebra R B]
  equiv : X ≃ₐ[R] (∀ i, A i) × B

/-- The étale neighborhood and finite product around all quasi-finite primes
over a fixed prime. -/
structure EtaleFiniteOverPrimeData
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (f : R →+* S) (p : PrimeSpectrum R) where
  R' : Type u
  [commRingR' : CommRing R']
  [algebraRR' : Algebra R R']
  etale : RingHom.Etale (algebraMap R R')
  p' : PrimeSpectrum R'
  liesOver : PrimeSpectrum.comap (algebraMap R R') p' = p
  residueFieldMapBijective :
    Function.Bijective
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt
        (algebraMap R R') p p' liesOver)
  decomposition : FiniteAlgebraProduct R' (R' ⊗[R] S)
  finiteFactors : ∀ i, letI : CommRing (decomposition.A i) := decomposition.commRingA i
    letI : Algebra R' (decomposition.A i) := decomposition.algebraA i
    RingHom.Finite (algebraMap R' (decomposition.A i))
  uniquePrime : ∀ i, letI : CommRing (decomposition.A i) := decomposition.commRingA i
    letI : Algebra R' (decomposition.A i) := decomposition.algebraA i
    ∃! r : PrimeSpectrum (decomposition.A i),
      PrimeSpectrum.comap (algebraMap R' (decomposition.A i)) r = p'
  noQuasiFiniteB : letI : CommRing decomposition.B := decomposition.commRingB
    letI : Algebra R' decomposition.B := decomposition.algebraB
    ∀ r : PrimeSpectrum decomposition.B,
      PrimeSpectrum.comap (algebraMap R' decomposition.B) r = p' →
        ¬ Formalization.Books.Algebra.Unit122.IsQuasiFiniteAt
          (algebraMap R' decomposition.B) r

/-- Étale local structure after collecting all quasi-finite points over a
prime into finitely many finite factors. -/
theorem etale_makes_quasiFinite_finite
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (hfiniteType : f.FiniteType) :
    letI : Algebra R S := f.toAlgebra
    Nonempty (EtaleFiniteOverPrimeData f p) := by
  sorry

/-- The variant in which the residue-field extensions of the finite factors
are purely inseparable. -/
structure EtaleFinitePurelyInseparableData
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (f : R →+* S) (p : PrimeSpectrum R) where
  R' : Type u
  [commRingR' : CommRing R']
  [algebraRR' : Algebra R R']
  etale : RingHom.Etale (algebraMap R R')
  p' : PrimeSpectrum R'
  liesOver : PrimeSpectrum.comap (algebraMap R R') p' = p
  decomposition : FiniteAlgebraProduct R' (R' ⊗[R] S)
  finiteFactors : ∀ i, letI : CommRing (decomposition.A i) := decomposition.commRingA i
    letI : Algebra R' (decomposition.A i) := decomposition.algebraA i
    RingHom.Finite (algebraMap R' (decomposition.A i))
  uniquePrime : ∀ i, letI : CommRing (decomposition.A i) := decomposition.commRingA i
    letI : Algebra R' (decomposition.A i) := decomposition.algebraA i
    ∃! r : PrimeSpectrum (decomposition.A i),
      PrimeSpectrum.comap (algebraMap R' (decomposition.A i)) r = p'
  residuePurelyInseparable : ∀ i,
    letI : CommRing (decomposition.A i) := decomposition.commRingA i
    letI : Algebra R' (decomposition.A i) := decomposition.algebraA i
    ∀ r : PrimeSpectrum (decomposition.A i),
    ∀ hr : PrimeSpectrum.comap (algebraMap R' (decomposition.A i)) r = p',
      letI : Algebra p'.asIdeal.ResidueField r.asIdeal.ResidueField :=
        (Formalization.Books.Algebra.Unit113.residueFieldMapAt
          (algebraMap R' (decomposition.A i)) p' r hr).toAlgebra
      Module.Finite p'.asIdeal.ResidueField r.asIdeal.ResidueField ∧
        IsPurelyInseparable p'.asIdeal.ResidueField r.asIdeal.ResidueField
  noQuasiFiniteB : letI : CommRing decomposition.B := decomposition.commRingB
    letI : Algebra R' decomposition.B := decomposition.algebraB
    ∀ r : PrimeSpectrum decomposition.B,
      PrimeSpectrum.comap (algebraMap R' decomposition.B) r = p' →
        ¬ Formalization.Books.Algebra.Unit122.IsQuasiFiniteAt
          (algebraMap R' decomposition.B) r

theorem etale_makes_quasiFinite_finite_variant
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (hfiniteType : f.FiniteType) :
    letI : Algebra R S := f.toAlgebra
    Nonempty (EtaleFinitePurelyInseparableData f p) := by
  sorry

end

end Formalization.Books.Algebra.Unit145
