import Formalization.Books.Algebra.Unit20.Nakayama
import Formalization.Books.Algebra.Unit39.FlatModules
import Formalization.Books.Algebra.Unit75.TorGroups
import Formalization.Books.Algebra.Unit99.CriteriaForFlatness
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.Ideal.Finsupp

/-!
# Commutative Algebra, Chapter 101: Flatness criteria over Artinian rings

The statements in this section use Mathlib's canonical flat, free, projective,
basis, quotient-module, residue-field, localization, and ring-hom flatness
interfaces.  Tor is the canonical construction recorded in Chapter 75.

The short exact sequences and tensor-product maps displayed inside the source
proofs are proof scaffolding for the theorem interfaces below, so they are not
duplicated as unreferenced declarations.
-/

namespace Formalization.Books.Algebra.Unit101

open CategoryTheory
open CategoryTheory.Limits
open Function
open scoped TensorProduct

noncomputable section

universe u

/-! ## Nilpotent local criteria -/

/-- An Artinian local ring has a nilpotent maximal ideal. -/
theorem artinian_local_maximalIdeal_isNilpotent
    {R : Type u} [CommRing R] [IsArtinianRing R] [IsLocalRing R] :
    IsNilpotent (IsLocalRing.maximalIdeal R) :=
  (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp inferInstance

/- The ideal used in the preparation lemma is the contraction of the extension
   of `I ^ 2` along the given ring map. -/
def prepareIdeal {R R' : Type u} [CommRing R] [CommRing R']
    (φ : R →+* R') (I : Ideal R) : Ideal R :=
  Ideal.comap φ (Ideal.map φ (I ^ 2))

/- Mathlib packages a basis as a structure and does not take its vector
   family as a type parameter.  This predicate records the source's phrase
   that a specified family forms a basis. -/
def IsBasisFamily {R M A : Type u} [Semiring R] [AddCommMonoid M]
    [Module R M] (x : A → M) : Prop :=
  ∃ b : Module.Basis A R M, (b : A → M) = x

private theorem basis_family_lift_of_flat_of_isNilpotent
    {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : IsNilpotent I) (hflat : Module.Flat R M)
    (x : A → M)
    (hbasis : IsBasisFamily
      (R := R ⧸ I) (M := M ⧸ (I • (⊤ : Submodule R M)))
      (fun a => (I • (⊤ : Submodule R M)).mkQ (x a))) :
    IsBasisFamily (R := R) (M := M) x := by
  classical
  let IM : Submodule R M := I • (⊤ : Submodule R M)
  let ψ : (A →₀ R) →ₗ[R] M := Finsupp.linearCombination R x
  rcases hbasis with ⟨b, hb⟩
  have hspan : Submodule.span R
      (Set.range (fun a => IM.mkQ (x a))) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ I)
      Ideal.Quotient.mk_surjective, ← hb]
    simp
  have hspanx : Submodule.span R (Set.range x) = ⊤ := by
    exact Formalization.Books.Algebra.Unit20.nakayama_part_twelve I x hspan hI
  have hsurj : Function.Surjective ψ := by
    rw [span_range_eq_top_iff_surjective_finsuppLinearCombination R] at hspanx
    exact hspanx
  letI : Module.Flat R M := hflat
  have hkerI : ∀ z : A →₀ R, ψ z = 0 →
      z ∈ I • (⊤ : Submodule R (A →₀ R)) := by
    intro z hz
    let zbar : A →₀ (R ⧸ I) :=
      Finsupp.mapRange (Ideal.Quotient.mk I) (by simp) z
    have hzbar : Finsupp.linearCombination (R ⧸ I)
        (fun a => IM.mkQ (x a)) zbar = 0 := by
      have hz' : IM.mkQ (ψ z) = 0 := by simp [hz]
      calc
        Finsupp.linearCombination (R ⧸ I)
            (fun a => IM.mkQ (x a)) zbar = IM.mkQ (ψ z) := by
          dsimp [zbar, ψ]
          refine Finsupp.induction_linear z (by simp)
            (fun f g hf hg => ?_) (fun a c => ?_)
          · rw [Finsupp.mapRange_add']
            rw [map_add, hf, hg]
            simpa [ψ]
          · simp [Finsupp.linearCombination_apply,
              Finsupp.sum_mapRange_index]
        _ = 0 := hz'
    have hzbar' : Finsupp.linearCombination (R ⧸ I)
        (b : A → M ⧸ IM) zbar = 0 := by
      simpa [hb] using hzbar
    have hzbar0 : zbar = 0 :=
      b.linearIndependent.finsuppLinearCombination_injective hzbar'
    have hcoeff : ∀ a, z a ∈ I := by
      intro a
      have ha := congrArg (fun w : A →₀ (R ⧸ I) => w a) hzbar0
      have ha' : Ideal.Quotient.mk I (z a) = 0 := by
        simpa [zbar] using ha
      exact Ideal.Quotient.eq_zero_iff_mem.mp ha'
    rw [← Finsupp.sum_single z]
    apply Submodule.sum_mem
    intro a ha
    simpa [Finsupp.smul_single] using
      (Submodule.smul_mem_smul (hcoeff a)
        (show (Finsupp.single a (1 : R) : A →₀ R) ∈
          (⊤ : Submodule R (A →₀ R)) from Submodule.mem_top))
  have hker_pow : ∀ n : ℕ,
      LinearMap.ker ψ ≤ I ^ n • (⊤ : Submodule R (A →₀ R)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        intro z hz
        have hzI := hkerI z hz
        have hz' : z ∈ LinearMap.ker ψ ⊓
            (I • (⊤ : Submodule R (A →₀ R))) := ⟨hz, hzI⟩
        rw [LinearMap.ker_inf_smul_top_eq_smul_of_flat I ψ hsurj] at hz'
        have hle : I • LinearMap.ker ψ ≤
            I ^ (n + 1) • (⊤ : Submodule R (A →₀ R)) := by
          apply Submodule.smul_le.2
          intro r hr y hy
          have hy' := ih hy
          have hsmul : r • y ∈ I •
              (I ^ n • (⊤ : Submodule R (A →₀ R))) :=
            Submodule.smul_mem_smul hr hy'
          simpa [pow_succ, mul_comm, mul_smul] using hsmul
        exact hle hz'
  obtain ⟨n, hn⟩ := hI
  have hker : LinearMap.ker ψ = ⊥ := by
    apply le_antisymm
    · intro z hz
      have hz' := hker_pow n hz
      rw [hn] at hz'
      simpa using hz'
    · exact bot_le
  have hli : LinearIndependent R x := by
    rw [linearIndependent_iff_injective_finsuppLinearCombination]
    exact LinearMap.ker_eq_bot.mp hker
  exact ⟨Module.Basis.mk hli hspanx.ge, Module.Basis.coe_mk hli hspanx.ge⟩

private theorem basis_family_descend_of_basis
    {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (x : A → M)
    (hbasis : IsBasisFamily (R := R) (M := M) x) :
    IsBasisFamily
      (R := R ⧸ I) (M := M ⧸ (I • (⊤ : Submodule R M)))
      (fun a => (I • (⊤ : Submodule R M)).mkQ (x a)) := by
  classical
  let IM : Submodule R M := I • (⊤ : Submodule R M)
  let ψ : (A →₀ R) →ₗ[R] M := Finsupp.linearCombination R x
  rcases hbasis with ⟨b, hb⟩
  have hψbij : Function.Bijective ψ := by
    rw [show ψ = b.repr.symm by
      ext z
      simp [ψ, ← hb]]
    exact b.repr.symm.bijective
  let e : (A →₀ R) ≃ₗ[R] M := LinearEquiv.ofBijective ψ hψbij
  have hinv : IM.map e.symm.toLinearMap ≤
      I • (⊤ : Submodule R (A →₀ R)) := by
    apply Submodule.map_le_iff_le_comap.mpr
    intro m hm
    refine Submodule.smul_induction_on hm
      (fun r hr y _ => ?_) (fun y z hy hz => ?_)
    · change e.symm (r • y) ∈ I • (⊤ : Submodule R (A →₀ R))
      rw [map_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · change e.symm (y + z) ∈ I • (⊤ : Submodule R (A →₀ R))
      rw [map_add]
      exact (I • (⊤ : Submodule R (A →₀ R))).add_mem hy hz
  have hformula (z : A →₀ R) :
      Finsupp.linearCombination (R ⧸ I)
        (fun a => IM.mkQ (x a))
        (Finsupp.mapRange (Ideal.Quotient.mk I) (by simp) z) =
        IM.mkQ (ψ z) := by
    dsimp [ψ]
    refine Finsupp.induction_linear z (by simp)
      (fun f g hf hg => ?_) (fun a c => ?_)
    · rw [Finsupp.mapRange_add']
      rw [map_add, hf, hg]
      simpa [ψ]
    · simp [Finsupp.linearCombination_apply,
        Finsupp.sum_mapRange_index]
  have hli : LinearIndependent (R ⧸ I)
      (fun a => IM.mkQ (x a)) := by
    rw [linearIndependent_iff_injective_finsuppLinearCombination]
    intro zbar₁ zbar₂ h
    let zd := zbar₁ - zbar₂
    obtain ⟨z, hz⟩ := Finsupp.mapRange_surjective
      (Ideal.Quotient.mk I) (by simp) Ideal.Quotient.mk_surjective zd
    have hz0 : Finsupp.linearCombination (R ⧸ I)
        (fun a => IM.mkQ (x a)) zd = 0 := by
      rw [map_sub]
      apply sub_eq_zero.mpr
      simpa [IM] using h
    have hmk : IM.mkQ (ψ z) = 0 := by
      calc
        IM.mkQ (ψ z) = Finsupp.linearCombination (R ⧸ I)
            (fun a => IM.mkQ (x a))
            (Finsupp.mapRange (Ideal.Quotient.mk I) (by simp) z) :=
          (hformula z).symm
        _ = Finsupp.linearCombination (R ⧸ I)
            (fun a => IM.mkQ (x a)) zd := by rw [hz]
        _ = 0 := hz0
    have hmem : ψ z ∈ IM :=
      (Submodule.Quotient.mk_eq_zero IM).mp hmk
    have hzmem : z ∈ I • (⊤ : Submodule R (A →₀ R)) := by
      have hzmap : z ∈ IM.map e.symm.toLinearMap := by
        refine ⟨ψ z, hmem, ?_⟩
        simp [e]
      simpa [e] using hinv hzmap
    have hIF_eq : I • (⊤ : Submodule R (A →₀ R)) =
        Finsupp.submodule (fun _ : A => (I : Submodule R R)) := by
      have hItop : I • (⊤ : Submodule R R) = I := by
        apply le_antisymm
        · apply Submodule.smul_le.2
          intro r hr s hs
          change r * s ∈ I
          simpa [mul_comm] using I.mul_mem_left s hr
        · intro r hr
          simpa using Submodule.smul_mem_smul hr
            (show (1 : R) ∈ (⊤ : Submodule R R) from Submodule.mem_top)
      calc
        I • (⊤ : Submodule R (A →₀ R)) =
            I • Finsupp.submodule (fun _ : A => (⊤ : Submodule R R)) := by
              rw [Finsupp.submodule_top]
        _ = Finsupp.submodule
            (fun _ : A => I • (⊤ : Submodule R R)) :=
          (Finsupp.submodule_smul R A
            (fun _ : A => (⊤ : Submodule R R)) I).symm
        _ = Finsupp.submodule (fun _ : A => (I : Submodule R R)) := by
          rw [hItop]
    have hzcoeff : ∀ a, z a ∈ I := by
      rw [hIF_eq] at hzmem
      exact hzmem
    have hzzero : Finsupp.mapRange (Ideal.Quotient.mk I)
        (by simp) z = 0 := by
      ext a
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hzcoeff a)
    have hzd : zd = 0 := by simpa [hz] using hzzero
    exact sub_eq_zero.mp hzd
  have hspan : Submodule.span (R ⧸ I)
      (Set.range (fun a => IM.mkQ (x a))) = ⊤ := by
    have hmap : (Submodule.span R (Set.range x)).map IM.mkQ = ⊤ := by
      rw [← hb, b.span_eq, Submodule.map_top, Submodule.range_mkQ]
    rw [Submodule.map_span] at hmap
    have himage : IM.mkQ '' Set.range x =
        Set.range (fun a => IM.mkQ (x a)) := by
      ext y
      constructor
      · rintro ⟨z, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨x a, ⟨a, rfl⟩, rfl⟩
    have hspanR : Submodule.span R
        (Set.range (fun a => IM.mkQ (x a))) = ⊤ := by
      simpa [himage] using hmap
    rw [← Submodule.restrictScalars_eq_top_iff R,
      Submodule.restrictScalars_span R (R ⧸ I)
        Ideal.Quotient.mk_surjective, hspanR]
  exact ⟨Module.Basis.mk hli hspan.ge, Module.Basis.coe_mk hli hspan.ge⟩

private theorem basis_family_iff_of_flat_of_isNilpotent
    {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : IsNilpotent I) (hflat : Module.Flat R M)
    (x : A → M) :
    IsBasisFamily
      (R := R ⧸ I) (M := M ⧸ (I • (⊤ : Submodule R M)))
      (fun a => (I • (⊤ : Submodule R M)).mkQ (x a)) ↔
      IsBasisFamily (R := R) (M := M) x := by
  constructor
  · exact basis_family_lift_of_flat_of_isNilpotent I hI hflat x
  · exact basis_family_descend_of_basis I x

/- The source's residue vectors are the images under the canonical quotient
   map of the maximal-ideal multiple of the module. -/
theorem local_artinian_basis_when_flat
    {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [IsLocalRing R] (hmax : IsNilpotent (IsLocalRing.maximalIdeal R))
    (hflat : Module.Flat R M) (x : A → M) :
    IsBasisFamily
        (R := R ⧸ IsLocalRing.maximalIdeal R)
        (M := M ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)))
        (fun a =>
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).mkQ (x a)) ↔
      IsBasisFamily (R := R) (M := M) x := by
  exact basis_family_iff_of_flat_of_isNilpotent
    (IsLocalRing.maximalIdeal R) hmax hflat x

theorem local_artinian_characterize_flat
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [IsLocalRing R]
    (hmax : IsNilpotent (IsLocalRing.maximalIdeal R)) :
    List.TFAE [Module.Flat R M, Module.Free R M, Module.Projective R M] := by
  tfae_have 1 → 2 := by
    intro hflat
    let k := R ⧸ IsLocalRing.maximalIdeal R
    let Q := M ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))
    letI : Field k := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
    let A' := Module.Basis.ofVectorSpaceIndex k Q
    let b : Module.Basis A' k Q := Module.Basis.ofVectorSpace k Q
    let y : A' → M := fun a =>
      Classical.choose (Submodule.mkQ_surjective
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) (b a))
    have hy (a : A') :
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).mkQ (y a) = b a := by
      exact Classical.choose_spec (Submodule.mkQ_surjective
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) (b a))
    have hbq : IsBasisFamily
        (R := R ⧸ IsLocalRing.maximalIdeal R)
        (M := M ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)))
        (fun a =>
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).mkQ (y a)) := by
      refine ⟨b, ?_⟩
      funext a
      exact (hy a).symm
    rcases (local_artinian_basis_when_flat hmax hflat y).mp hbq with ⟨bM, hbM⟩
    exact Module.Free.of_basis bM
  tfae_have 2 → 3 := by
    intro hfree
    letI : Module.Free R M := hfree
    exact Module.Projective.of_free
  tfae_have 3 → 1 := by
    intro hprojective
    letI : Module.Projective R M := hprojective
    exact Module.Flat.of_projective
  tfae_finish

theorem lift_basis
    {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : IsNilpotent I) (x : A → M)
    (hbasis :
      IsBasisFamily
        (R := R ⧸ I) (M := M ⧸ (I • (⊤ : Submodule R M)))
        (fun a => (I • (⊤ : Submodule R M)).mkQ (x a)))
    (hTor : IsZero
      (Formalization.Books.Algebra.Unit75.Tor
        (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R M) 1)) :
    IsBasisFamily (R := R) (M := M) x := by
  rcases hbasis with ⟨b, hb⟩
  have hflatbar : Module.Flat (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))) := by
    letI : Module.Free (R ⧸ I)
        (M ⧸ (I • (⊤ : Submodule R M))) := Module.Free.of_basis b
    exact Module.Flat.of_free
  obtain ⟨n, hn⟩ := hI
  have hflat : Module.Flat R M :=
    (Formalization.Books.Algebra.Unit99.what_does_it_mean
      I hflatbar hTor).2.2 ⟨n, by simpa using hn⟩
  exact basis_family_lift_of_flat_of_isNilpotent I ⟨n, hn⟩ hflat x
    ⟨b, hb⟩

theorem prepare_lift_flatness
    {R R' M : Type u} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R M] (φ : R →+* R') (I : Ideal R)
    (hflat : Module.Flat (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))))
    (hbase :
      letI : Algebra R R' := φ.toAlgebra
      Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat (R ⧸ prepareIdeal φ I)
      (M ⧸ (prepareIdeal φ I • (⊤ : Submodule R M))) := by
  sorry

theorem lift_flatness
    {R R' M : Type u} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R M] (φ : R →+* R') (I : Ideal R)
    (hI : IsNilpotent I) (hφ : Injective φ)
    (hflat : Module.Flat (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M))))
    (hbase :
      letI : Algebra R R' := φ.toAlgebra
      Module.Flat R' (R' ⊗[R] M)) :
    Module.Flat R M := by
  sorry

theorem artinian_variant_local_criterion_flatness
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [IsArtinianRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    Module.Flat R M ↔
      Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) ∧
        IsZero
          (Formalization.Books.Algebra.Unit75.Tor
            (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R M) 1) := by
  sorry

theorem descent_flatness_injective_map_artinian_rings
    {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M]
    [Module R M] [IsArtinianRing R] (φ : R →+* S) (hφ : Injective φ)
    (hflat :
      letI : Algebra R S := φ.toAlgebra
      Module.Flat S (S ⊗[R] M)) :
    Module.Flat R M := by
  sorry

/- The condition in the fibre criterion is the source's assertion that the
   fibre of `M` at `q` is nonzero, with the `S`-action restricted from `S'`. -/
def nontrivialFibreAt
    {S S' M : Type u} [CommRing S] [CommRing S'] [AddCommGroup M]
    [Module S' M] (g : S →+* S') (q : PrimeSpectrum S) : Prop :=
  letI : Module S M := Module.compHom M g
  Nontrivial (M ⊗[S] q.asIdeal.ResidueField)

/- This is the nilpotent fibre criterion.  The comparison warning in the
   source points to the Noetherian, finitely presented, and locally nilpotent
   fibre criteria formalized in the preceding chapter. -/
theorem criterion_flatness_fibre_nilpotent
    {R S S' M : Type u} [CommRing R] [CommRing S] [CommRing S']
    [AddCommGroup M] [Module S' M]
    (f : R →+* S) (g : S →+* S') (h : R →+* S')
    (comm : g.comp f = h) (I : Ideal R) (hI : IsNilpotent I)
    (hflat_fibre :
      letI : Module S M := Module.compHom M g
      Module.Flat (S ⧸ (I.map f))
        (M ⧸ ((I.map f) • (⊤ : Submodule S M))))
    (hflat_base :
      letI : Module R M := Module.compHom M h
      Module.Flat R M) :
    (letI : Module S M := Module.compHom M g
     Module.Flat S M) ∧
      ∀ q : PrimeSpectrum S,
        nontrivialFibreAt (M := M) g q →
          RingHom.Flat
            ((algebraMap S (Localization.AtPrime q.asIdeal)).comp f) := by
  sorry

end

end Formalization.Books.Algebra.Unit101
