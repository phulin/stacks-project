import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets
import Formalization.Books.Algebra.Unit98.TakingLimits
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Data.PNat.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Algebraization of Formal Spaces, Chapter 2: Two categories

This file formalizes the two categories used in the chapter.  The category
`AdicSystemCategory` is modeled as a full subcategory of structured arrows
from the canonical system of quotients `A / I^n`; this records both the
`A_n`-algebra structures and the compatibility of all transition maps.  The
category `CompleteAlgebraCategory` is the full subcategory of `CommAlgCat A`
cut out by adic completeness and finite type of the residue algebra.

The source section is statement-heavy.  The construction-level definitions
below use Mathlib's canonical quotient, tensor-product, and completion APIs;
the longer algebraic and categorical proofs are left as theorem interfaces
for the proof stage.
-/

namespace Formalization.Books.Restricted.Unit02

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21
open scoped TensorProduct

universe u v

noncomputable section

/-! ## The canonical quotient systems -/

/-- The `n`th quotient in the `J`-adic inverse system, indexed by `ℕ+`. -/
abbrev powerQuotient (R : Type u) [CommRing R] (J : Ideal R) (n : ℕ+) : Type u :=
  R ⧸ J ^ (n : ℕ)

/-- The transition map `R / J^m → R / J^n` for `n ≤ m`. -/
def powerQuotientTransition {R : Type u} [CommRing R] (J : Ideal R)
    {m n : ℕ+} (h : n ≤ m) :
    powerQuotient R J m →+* powerQuotient R J n :=
  Ideal.Quotient.factorPow J ((PNat.coe_le_coe n m).mpr h)

/- The identities and composition law for the quotient transitions are the
   ordinary quotient-factor identities in Mathlib. -/
theorem powerQuotientTransition_id {R : Type u} [CommRing R] (J : Ideal R)
    (n : ℕ+) :
    powerQuotientTransition J (m := n) (n := n) le_rfl = RingHom.id _ := by
  ext x
  simp [powerQuotientTransition]

theorem powerQuotientTransition_comp {R : Type u} [CommRing R] (J : Ideal R)
    {m n k : ℕ+} (hnm : n ≤ m) (hkn : k ≤ n) :
    (powerQuotientTransition J hkn).comp (powerQuotientTransition J hnm) =
      powerQuotientTransition J (hkn.trans hnm) := by
  simp only [powerQuotientTransition]
  exact Ideal.Quotient.factor_comp _ _

/-- The canonical inverse system of powers of an ideal. -/
def powerQuotientSystem {R : Type u} [CommRing R] (J : Ideal R) :
    InverseSystem ℕ+ CommRingCat.{u} where
  obj i := CommRingCat.of (powerQuotient R J i.unop)
  map f :=
    CommRingCat.ofHom
      (powerQuotientTransition J (CategoryTheory.leOfHom f.unop))
  map_id := by
    intro i
    apply CommRingCat.hom_ext
    exact powerQuotientTransition_id J i.unop
  map_comp := by
    intro i j k f g
    apply CommRingCat.hom_ext
    simpa using
      (powerQuotientTransition_comp J
        (CategoryTheory.leOfHom f.unop) (CategoryTheory.leOfHom g.unop)).symm

/-! ## The category `𝓒` of compatible finite-type systems -/

/-- The book's notation `A_n = A / I^n`. -/
abbrev adicQuotient (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ+) : Type u :=
  powerQuotient A I n

/-- The canonical inverse system `(A_n)`. -/
abbrev adicQuotientSystem (A : Type u) [CommRing A] (I : Ideal A) :
    InverseSystem ℕ+ CommRingCat.{u} :=
  powerQuotientSystem I

/-- Mathlib's canonical `I`-adic completion of `A`. -/
abbrev adicCompletionRing (A : Type u) [CommRing A] (I : Ideal A) : Type u :=
  AdicCompletion I A

/-- The source's display `A^ = lim A_n`, with the positive-index quotient system. -/
theorem adicCompletion_is_powerQuotientLimit {A : Type u} [CommRing A]
    (I : Ideal A) :
    Nonempty
      (adicCompletionRing A I ≃+*
        ((limit (adicQuotientSystem A I) : CommRingCat.{u}) : Type u)) := by
  let F := adicQuotientSystem A I
  have heval : ∀ {m n : ℕ} (hmn : m ≤ n)
      (x : AdicCompletion I A),
      Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
        AdicCompletion.evalₐ I m x := by
    intro m n hmn x
    let hn : (I ^ n • ⊤ : Submodule A A) ≤ I ^ n :=
      le_of_eq (Ideal.mul_top _)
    let hm : (I ^ m • ⊤ : Submodule A A) ≤ I ^ m :=
      le_of_eq (Ideal.mul_top _)
    have hfac : ∀ (y : A ⧸ (I ^ n • ⊤ : Submodule A A)),
        Ideal.Quotient.factorPow I hmn (Submodule.factor hn y) =
          Submodule.factor hm (AdicCompletion.transitionMap I A hmn y) := by
      intro y
      induction y using Quotient.inductionOn' with
      | _ a => rfl
    rw [← AdicCompletion.factor_eval_eq_evalₐ I x hn]
    rw [← AdicCompletion.factor_eval_eq_evalₐ I x hm]
    rw [hfac]
    exact congrArg (fun z => Submodule.factor hm z)
      (AdicCompletion.transitionMap_comp_eval_apply I A hmn x)
  let c : Cone F :=
    { pt := CommRingCat.of (AdicCompletion I A)
      π :=
        { app := fun i =>
            CommRingCat.ofHom
              (AdicCompletion.evalₐ I (i.unop : ℕ)).toRingHom
          naturality := by
            intro i j f
            apply CommRingCat.hom_ext
            apply RingHom.ext
            intro x
            have hmn : (j.unop : ℕ) ≤ (i.unop : ℕ) := by
              exact (PNat.coe_le_coe _ _).mpr (CategoryTheory.le_of_op_hom f)
            change AdicCompletion.evalₐ I (j.unop : ℕ) x =
              powerQuotientTransition I (CategoryTheory.le_of_op_hom f)
                (AdicCompletion.evalₐ I (i.unop : ℕ) x)
            simpa [powerQuotientTransition] using (heval hmn x).symm }
      }
  let φ : AdicCompletion I A →+*
      ((limit F : CommRingCat) : Type u) :=
    (limit.lift F c).hom
  let pos : ℕ → ℕ+ := fun n => ⟨n + 1, Nat.succ_pos n⟩
  let g : ∀ n : ℕ,
      ((limit F : CommRingCat) : Type u) →+* A ⧸ I ^ n := fun n =>
    (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp
      (limit.π F (Opposite.op (pos n))).hom
  have hg : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow I hmn).comp (g n) = g m := by
    intro m n hmn
    apply RingHom.ext
    intro x
    have hpos : pos m ≤ pos n := by
      change m + 1 ≤ n + 1
      exact Nat.succ_le_succ hmn
    have hlim := limit.w F (CategoryTheory.homOfLE hpos).op
    have hlim' := congrArg (fun q => q.hom x) hlim
    change
      Ideal.Quotient.factorPow I hmn
          (Ideal.Quotient.factorPow I (Nat.le_succ n)
            ((limit.π F (Opposite.op (pos n))).hom x)) =
        Ideal.Quotient.factorPow I (Nat.le_succ m)
          ((limit.π F (Opposite.op (pos m))).hom x)
    change powerQuotientTransition I hpos
        ((limit.π F (Opposite.op (pos n))).hom x) =
      (limit.π F (Opposite.op (pos m))).hom x at hlim'
    rw [← hlim']
    obtain ⟨a, ha⟩ :=
      Ideal.Quotient.mk_surjective
        ((limit.π F (Opposite.op (pos n))).hom x)
    rw [← ha]
    rfl
  let ψ : ((limit F : CommRingCat) : Type u) →+* AdicCompletion I A :=
    AdicCompletion.liftRingHom I g hg
  have hφ : ∀ (n : ℕ) (x : AdicCompletion I A),
      (limit.π F (Opposite.op (pos n))).hom (φ x) =
        AdicCompletion.evalₐ I (n + 1) x := by
    intro n x
    have hπ := limit.lift_π c (Opposite.op (pos n))
    have hπ' := congrArg (fun q => q.hom x) hπ
    change (limit.π F (Opposite.op (pos n))).hom (φ x) =
      AdicCompletion.evalₐ I (n + 1) x
    exact hπ'
  have hψφ : ψ.comp φ = RingHom.id _ := by
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ I n (ψ (φ x)) =
      AdicCompletion.evalₐ I n x
    rw [AdicCompletion.evalₐ_liftRingHom]
    change Ideal.Quotient.factorPow I (Nat.le_succ n)
        ((limit.π F (Opposite.op (pos n))).hom (φ x)) =
      AdicCompletion.evalₐ I n x
    rw [hφ n x]
    exact heval (Nat.le_succ n) x
  have hφψ : φ.comp ψ = RingHom.id _ := by
    have hD : IsLimit ((forget CommRingCat).mapCone (limit.cone F)) :=
      isLimitOfPreserves (forget CommRingCat) (limit.isLimit F)
    apply RingHom.ext
    intro x
    apply (Types.isLimitEquivSections hD).injective
    ext i
    cases i with
    | op i =>
      have hstep : i ≤ pos (i : ℕ) := by
        change (i : ℕ) ≤ (i : ℕ) + 1
        exact Nat.le_succ _
      have hπ := congrArg (fun q => q.hom (ψ x))
        (limit.lift_π c (Opposite.op i))
      have hlim := limit.w F (CategoryTheory.homOfLE hstep).op
      have hlim' := congrArg (fun q => q.hom x) hlim
      change
        (limit.π F (Opposite.op i)).hom (φ (ψ x)) =
          AdicCompletion.evalₐ I (i : ℕ) (ψ x) at hπ
      change
        (limit.π F (Opposite.op i)).hom (φ (ψ x)) =
          (limit.π F (Opposite.op i)).hom x
      rw [hπ]
      rw [AdicCompletion.evalₐ_liftRingHom]
      change
        Ideal.Quotient.factorPow I (Nat.le_succ (i : ℕ))
            ((limit.π F (Opposite.op (pos (i : ℕ)))).hom x) =
          (limit.π F (Opposite.op i)).hom x
      change
        powerQuotientTransition I hstep
            ((limit.π F (Opposite.op (pos (i : ℕ)))).hom x) =
          (limit.π F (Opposite.op i)).hom x
      exact hlim'
  refine ⟨RingEquiv.ofBijective φ ?_⟩
  refine ⟨?_, ?_⟩
  · intro x y hxy
    calc
      x = (ψ.comp φ) x := by rw [hψφ]; rfl
      _ = (ψ.comp φ) y := congrArg ψ hxy
      _ = y := by rw [hψφ]; rfl
  · intro y
    exact ⟨ψ y, by
      simpa only [RingHom.comp_apply, RingHom.id_apply] using
        congrArg (fun q => q y) hφψ⟩

/-- The image of `I^n` in `A_{n+1}`. -/
def adicStagePowerIdeal {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ+) :
    Ideal (adicQuotient A I (n + 1)) :=
  Ideal.map
    (Ideal.Quotient.mk (I ^ ((n + 1 : ℕ+) : ℕ)))
    (I ^ (n : ℕ))

/-- A system equipped with its compatible maps from the quotient system `(A_n)`. -/
abbrev AdicSystemArrow (A : Type u) [CommRing A] (I : Ideal A) :=
  StructuredArrow (adicQuotientSystem A I)
    (𝟭 (InverseSystem ℕ+ CommRingCat.{u}))

/-- The `I^n`-part of the `(n+1)`st stage of a structured system. -/
def adicSystemPowerIdeal {A : Type u} [CommRing A] (I : Ideal A)
    (X : AdicSystemArrow A I) (n : ℕ+) :
    Ideal (X.right.obj (Opposite.op (n + 1))) :=
  Ideal.map
    (X.hom.app (Opposite.op (n + 1))).hom
    (adicStagePowerIdeal I n)

/-- The transition map of a structured inverse system. -/
def adicSystemTransition {A : Type u} [CommRing A] (I : Ideal A)
    (X : AdicSystemArrow A I) {m n : ℕ+} (h : n ≤ m) :
    X.right.obj (Opposite.op m) →+* X.right.obj (Opposite.op n) :=
  (X.right.map (CategoryTheory.homOfLE h).op).hom

/-- The quotient presentation of one successive transition in `𝓒`. -/
structure AdicSystemStep {A : Type u} [CommRing A] (I : Ideal A)
    (X : AdicSystemArrow A I) (n : ℕ+) where
  equivalence :
    (X.right.obj (Opposite.op (n + 1)) ⧸ adicSystemPowerIdeal I X n) ≃+*
      X.right.obj (Opposite.op n)
  transition_eq :
    equivalence.toRingHom.comp
        (Ideal.Quotient.mk (adicSystemPowerIdeal I X n)) =
      adicSystemTransition I X (PNat.lt_add_right n 1).le

/-- The object property defining the chapter's category `𝓒`. -/
def AdicSystemProperty {A : Type u} [CommRing A] (I : Ideal A) :
    ObjectProperty (AdicSystemArrow A I) :=
  fun X =>
    (∀ n : ℕ+, RingHom.FiniteType
      (X.hom.app (Opposite.op n)).hom) ∧
      (∀ n : ℕ+, Nonempty (AdicSystemStep I X n))

/-- The category `𝓒` of compatible finite-type inverse systems. -/
abbrev AdicSystemCategory (A : Type u) [CommRing A] (I : Ideal A) :=
  (AdicSystemProperty I).FullSubcategory

/-- The stagewise `A_n`-algebra structure carried by a structured system. -/
abbrev adicSystemStageAlgebra {A : Type u} [CommRing A] (I : Ideal A)
    (X : AdicSystemArrow A I) (n : ℕ+) :
    Algebra (adicQuotient A I n) (X.right.obj (Opposite.op n)) :=
  (X.hom.app (Opposite.op n)).hom.toAlgebra

/-- The scalar map from `A_{n+1}` to the lower stage, through `A_n`. -/
def adicSystemLowerStageScalarMap {A : Type u} [CommRing A] (I : Ideal A)
    (X : AdicSystemArrow A I) (n : ℕ+) :
    adicQuotient A I (n + 1) →+*
      X.right.obj (Opposite.op n) :=
  (X.hom.app (Opposite.op n)).hom.comp
    (powerQuotientTransition I
      (m := n + 1) (n := n) (PNat.lt_add_right n 1).le)

/-- The transition in `𝓒` is an `A_{n+1}`-algebra map. -/
theorem adicSystemTransition_is_algebraMap {A : Type u} [CommRing A]
    (I : Ideal A) (X : AdicSystemArrow A I) (n : ℕ+) :
    (adicSystemTransition I X (PNat.lt_add_right n 1).le).comp
        (X.hom.app (Opposite.op (n + 1))).hom =
      adicSystemLowerStageScalarMap I X n := by
  apply RingHom.ext
  intro x
  have h := congrArg
    (fun q : ((adicQuotientSystem A I).obj (Opposite.op (n + 1)) ⟶
      X.right.obj (Opposite.op n)) => q.hom x)
    (X.hom.naturality (CategoryTheory.homOfLE (PNat.lt_add_right n 1).le).op)
  change
    (X.hom.app (Opposite.op n)).hom
        (powerQuotientTransition I
          (m := n + 1) (n := n) (PNat.lt_add_right n 1).le x) =
      (X.right.map (CategoryTheory.homOfLE (PNat.lt_add_right n 1).le).op).hom
        ((X.hom.app (Opposite.op (n + 1))).hom x) at h
  change
    (X.right.map (CategoryTheory.homOfLE (PNat.lt_add_right n 1).le).op).hom
        ((X.hom.app (Opposite.op (n + 1))).hom x) =
      (X.hom.app (Opposite.op n)).hom
        (powerQuotientTransition I
          (m := n + 1) (n := n) (PNat.lt_add_right n 1).le x)
  exact h.symm

/-! ## The category `𝓒'` of complete algebras -/

/-- The extension `IB` of `I` to an `A`-algebra `B`. -/
def cprimeIdeal {A : Type u} [CommRing A] (I : Ideal A) (B : CommAlgCat A) :
    Ideal B :=
  Ideal.map (algebraMap A B) I

/-- The residue algebra `B / IB` over `A / I`. -/
def cprimeResidueAlgebra {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) : CommAlgCat (A ⧸ I) := by
  letI : Algebra (A ⧸ I) (B ⧸ cprimeIdeal I B) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (R := A) (A := B) (p := I) (P := cprimeIdeal I B)
      Ideal.le_comap_map
  exact CommAlgCat.of (A ⧸ I) (B ⧸ cprimeIdeal I B)

/-- The object property defining `𝓒'`. -/
def CompleteAlgebraProperty {A : Type u} [CommRing A] (I : Ideal A) :
    ObjectProperty (CommAlgCat.{u} A) :=
  fun B =>
    IsAdicComplete (cprimeIdeal I B) B ∧
      Algebra.FiniteType (A ⧸ I) (cprimeResidueAlgebra I B)

/-- The category `𝓒'` of `I`-adically complete algebras with finite residue algebra. -/
abbrev CompleteAlgebraCategory (A : Type u) [CommRing A] (I : Ideal A) :=
  (CompleteAlgebraProperty I).FullSubcategory

/-- Put the canonical `A`-algebra structure on a quotient of an `A`-algebra. -/
def quotientCommAlg {A : Type u} [CommRing A] (B : CommAlgCat A) (J : Ideal B) :
    CommAlgCat A := by
  letI : Algebra A (B ⧸ J) :=
    ((Ideal.Quotient.mk J).comp (algebraMap A B)).toAlgebra
  exact CommAlgCat.of A (B ⧸ J)

/-! ## The quotient functor `𝓒' → 𝓒` -/

/-- The `n`th stage of the quotient system attached to an algebra. -/
abbrev cprimeQuotientStage {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) (n : ℕ+) : Type u :=
  B ⧸ (cprimeIdeal I B) ^ (n : ℕ)

/-- The transition map in the quotient system attached to `B`. -/
abbrev cprimeQuotientTransition {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) {m n : ℕ+} (h : n ≤ m) :
    cprimeQuotientStage I B m →+* cprimeQuotientStage I B n :=
  powerQuotientTransition (cprimeIdeal I B) h

/-- The quotient inverse system attached to an `A`-algebra. -/
abbrev cprimeQuotientSystem {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) : InverseSystem ℕ+ CommRingCat.{u} :=
  powerQuotientSystem (cprimeIdeal I B)

/-- The ideal inclusion needed for the map `A/I^n → B/(IB)^n`. -/
theorem cprimeBaseIdeal_le {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) (n : ℕ+) :
    I ^ (n : ℕ) ≤
      ((cprimeIdeal I B) ^ (n : ℕ)).comap (algebraMap A B) := by
  rw [cprimeIdeal, ← Ideal.map_pow]
  exact Ideal.le_comap_map

/-- The stagewise quotient map from `A_n` to `B/(IB)^n`. -/
def cprimeBaseComponent {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) (n : ℕ+) :
    adicQuotient A I n →+* cprimeQuotientStage I B n :=
  Ideal.quotientMap
    ((cprimeIdeal I B) ^ (n : ℕ)) (algebraMap A B)
    (cprimeBaseIdeal_le I B n)

private theorem finiteType_of_finiteType_quotient
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (K : Ideal R) (hK : IsNilpotent K) :
    RingHom.FiniteType
        (Ideal.quotientMap (K.map f) f Ideal.le_comap_map) →
      RingHom.FiniteType f := by
  let : Algebra R S := f.toAlgebra
  let J : Ideal S := K.map f
  let π : S →ₐ[R] (S ⧸ J) := Ideal.Quotient.mkₐ R J
  let : Algebra (R ⧸ K) (S ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  intro h
  have h' : RingHom.FiniteType
      (algebraMap (R ⧸ K) (S ⧸ J)) := by
    have he : algebraMap (R ⧸ K) (S ⧸ J) =
        Ideal.quotientMap J f Ideal.le_comap_map := by
      apply RingHom.ext
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    exact he ▸ h
  change Algebra.FiniteType R S
  let q : R →+* (S ⧸ J) := (Ideal.Quotient.mk J).comp f
  have hq : RingHom.FiniteType q := by
    have hmk : RingHom.FiniteType (Ideal.Quotient.mk K) :=
      RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective
    have hcomp : RingHom.FiniteType
        ((algebraMap (R ⧸ K) (S ⧸ J)).comp (Ideal.Quotient.mk K)) :=
      h'.comp hmk
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
  let C : Subalgebra R S := Algebra.adjoin R T
  have hT : T.Finite := s.finite_toSet.image lift
  have hπ : Function.Surjective (π.comp C.val) := by
    apply (AlgHom.range_eq_top _).mp
    apply Algebra.eq_top_iff.mpr
    intro x
    have hle : Algebra.adjoin R (s : Set (S ⧸ J)) ≤ (π.comp C.val).range := by
      apply Algebra.adjoin_le
      intro y hy
      exact ⟨⟨lift y, Algebra.subset_adjoin ⟨y, hy, rfl⟩⟩, by
        simpa [π] using hlift y⟩
    exact hle (by rw [hs]; trivial)
  have hbase : ∀ x : S, ∃ a : C, x - a.1 ∈ J := by
    intro x
    obtain ⟨a, ha⟩ := hπ (π x)
    refine ⟨a, ?_⟩
    have hz : π (x - a.1) = 0 := by
      simpa [map_sub, Function.comp_apply] using sub_eq_zero.mpr ha.symm
    simpa [π] using Ideal.Quotient.eq_zero_iff_mem.mp hz
  obtain ⟨N, hKN⟩ := hK
  have hN : J ^ N = ⊥ := by
    change (Ideal.map f K) ^ N = ⊥
    rw [← Ideal.map_pow, hKN]
    simp
  have hdecomp (n : ℕ) (x : S) (hx : x ∈ J ^ n) :
      ∃ a : C, a.1 ∈ J ^ n ∧ x - a.1 ∈ J ^ (n + 1) := by
    have hx' : x ∈ Ideal.map f (K ^ n) := by
      simpa [J, Ideal.map_pow] using hx
    rw [Ideal.map] at hx'
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx'
    · rintro y ⟨r, hr, rfl⟩
      let a : C := ⟨f r, C.algebraMap_mem r⟩
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
          have hmul := Ideal.mul_mem_mul hb ha
          simpa [pow_succ', mul_comm] using hmul
        have hres := add_mem h₁ h₂
        change c * x - b.1 * a.1 ∈ J ^ (n + 1)
        convert hres using 1
        ring
  have hgen : ∀ n : ℕ, ∀ x : S, ∃ a : C, x - a.1 ∈ J ^ n := by
    intro n
    induction n with
    | zero => intro x; exact ⟨0, by simp⟩
    | succ n ih =>
      intro x
      obtain ⟨a, ha⟩ := ih x
      obtain ⟨b, hb, hxb⟩ := hdecomp n (x - a.1) ha
      refine ⟨a + b, ?_⟩
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxb
  have hCtop : C = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨a, ha⟩ := hgen N x
    have hzero : x - a.1 = 0 := by simpa [hN] using ha
    have hxa : x = a.1 := sub_eq_zero.mp hzero
    rw [hxa]
    exact a.property
  have hCfinite : Algebra.FiniteType R C := Algebra.FiniteType.adjoin_of_finite hT
  apply hCfinite.of_surjective C.val
  intro x
  have hx : x ∈ C := by rw [hCtop]; trivial
  exact ⟨⟨x, hx⟩, rfl⟩

private theorem finiteType_cprime_stage_quotient {A : Type u} [CommRing A]
    (I : Ideal A) (B : CommAlgCat A) (n : ℕ+)
    (hres : RingHom.FiniteType
      (Ideal.quotientMap (cprimeIdeal I B) (algebraMap A B)
        Ideal.le_comap_map)) :
    RingHom.FiniteType
      (Ideal.quotientMap
        ((Ideal.map (Ideal.Quotient.mk (I ^ (n : ℕ))) I).map
          (cprimeBaseComponent I B n))
        (cprimeBaseComponent I B n) Ideal.le_comap_map) := by
  let p : Ideal A := I ^ (n : ℕ)
  let J : Ideal B := (cprimeIdeal I B) ^ (n : ℕ)
  let K : Ideal (A ⧸ p) := Ideal.map (Ideal.Quotient.mk p) I
  let f := cprimeBaseComponent I B n
  let : Algebra (A ⧸ p) (B ⧸ J) := f.toAlgebra
  let L : Ideal (B ⧸ J) := (cprimeIdeal I B).map (Ideal.Quotient.mk J)
  have hL : K.map (algebraMap (A ⧸ p) (B ⧸ J)) = L := by
    dsimp [L, K]
    rw [Ideal.map_map]
    change Ideal.map ((Ideal.Quotient.mk J).comp (algebraMap A B)) I = _
    rw [cprimeIdeal, ← Ideal.map_map]
  let : Algebra (A ⧸ I) (B ⧸ cprimeIdeal I B) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have hres' : RingHom.FiniteType
      (algebraMap (A ⧸ I) (B ⧸ cprimeIdeal I B)) := by
    have he : algebraMap (A ⧸ I) (B ⧸ cprimeIdeal I B) =
        Ideal.quotientMap (cprimeIdeal I B) (algebraMap A B)
          Ideal.le_comap_map := by
      apply RingHom.ext
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    exact he ▸ hres
  let : Algebra A (B ⧸ J) :=
    ((Ideal.Quotient.mk J).comp (algebraMap A B)).toAlgebra
  let q : (A ⧸ p) →+* ((B ⧸ J) ⧸ L) :=
    (Ideal.Quotient.mk L).comp f
  let : Algebra (A ⧸ p) ((B ⧸ J) ⧸ L) :=
    q.toAlgebra
  have hIL : I ≤ L.comap (algebraMap A (B ⧸ J)) := by
    intro x hx
    change algebraMap A (B ⧸ J) x ∈ L
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx)
  let : Algebra (A ⧸ I) ((B ⧸ J) ⧸ L) :=
    Ideal.Quotient.algebraQuotientOfLEComap hIL
  have hKq : ∀ x : A ⧸ p, x ∈ K → q x = 0 := by
    intro x hx
    change (Ideal.Quotient.mk L) (f x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    rw [← hL]
    exact Ideal.mem_map_of_mem _ hx
  let q' : ((A ⧸ p) ⧸ K) →+* ((B ⧸ J) ⧸ L) :=
    Ideal.Quotient.lift K q hKq
  let : Algebra ((A ⧸ p) ⧸ K) ((B ⧸ J) ⧸ L) := q'.toAlgebra
  have hJ : J ≤ cprimeIdeal I B := by
    dsimp [J]
    exact Ideal.pow_le_self (by exact_mod_cast n.ne_zero)
  let e : ((B ⧸ J) ⧸ L) ≃+* (B ⧸ cprimeIdeal I B) :=
    DoubleQuot.quotQuotEquivQuotOfLE hJ
  have hAIT' : RingHom.FiniteType
      (e.symm.toRingHom.comp
        (algebraMap (A ⧸ I) (B ⧸ cprimeIdeal I B))) :=
    hres'.comp_surjective e.symm.surjective
  have hAIT : RingHom.FiniteType
      (algebraMap (A ⧸ I) ((B ⧸ J) ⧸ L)) := by
    convert hAIT' using 1
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  let hq : A ⧸ I →+* (A ⧸ p) ⧸ K :=
    Ideal.quotientMap K (Ideal.Quotient.mk p) Ideal.le_comap_map
  have hcomp : RingHom.FiniteType
      (algebraMap (A ⧸ I) ((B ⧸ J) ⧸ L)) := hAIT
  have heq :
      (algebraMap ((A ⧸ p) ⧸ K) ((B ⧸ J) ⧸ L)).comp hq =
        algebraMap (A ⧸ I) ((B ⧸ J) ⧸ L) := by
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change q' (Ideal.Quotient.mk K (Ideal.Quotient.mk p x)) =
      Ideal.Quotient.mk L (algebraMap A (B ⧸ J) x)
    rw [Ideal.Quotient.lift_mk]
    change q (Ideal.Quotient.mk p x) =
      Ideal.Quotient.mk L (algebraMap A (B ⧸ J) x)
    dsimp [q, f, cprimeBaseComponent]
    rw [Ideal.quotientMap_mk]
    change Ideal.Quotient.mk L
        (Ideal.Quotient.mk J (algebraMap A B x)) =
      Ideal.Quotient.mk L (Ideal.Quotient.mk J (algebraMap A B x))
    rfl
  have hq' : RingHom.FiniteType
      (algebraMap ((A ⧸ p) ⧸ K) ((B ⧸ J) ⧸ L)) :=
    RingHom.FiniteType.of_comp_finiteType (heq ▸ hcomp)
  have hLf : K.map f = L := by
    change K.map (algebraMap (A ⧸ p) (B ⧸ J)) = L
    exact hL
  let eLf : ((B ⧸ J) ⧸ L) ≃+*
      ((B ⧸ J) ⧸ K.map f) := Ideal.quotEquivOfEq hLf.symm
  have hq'' : RingHom.FiniteType
      (eLf.toRingHom.comp
        (algebraMap ((A ⧸ p) ⧸ K) ((B ⧸ J) ⧸ L))) :=
    hq'.comp_surjective eLf.surjective
  have heq' :
      eLf.toRingHom.comp
          (algebraMap ((A ⧸ p) ⧸ K) ((B ⧸ J) ⧸ L)) =
        Ideal.quotientMap (K.map f) f Ideal.le_comap_map := by
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change eLf (q' (Ideal.Quotient.mk K x)) =
      Ideal.Quotient.mk (K.map f) (f x)
    rw [Ideal.Quotient.lift_mk]
    change eLf (q x) = Ideal.Quotient.mk (K.map f) (f x)
    dsimp [eLf, q]
  exact heq' ▸ hq''

/-- The finite-type assertion used to show that the quotient functor lands in `𝓒`. -/
theorem cprimeBaseComponent_finiteType {A : Type u} [CommRing A]
    (I : Ideal A) (B : CompleteAlgebraCategory A I) (n : ℕ+) :
    RingHom.FiniteType (cprimeBaseComponent I B.obj n) := by
  let p : Ideal A := I ^ (n : ℕ)
  let K : Ideal (A ⧸ p) := Ideal.map (Ideal.Quotient.mk p) I
  let f := cprimeBaseComponent I B.obj n
  have hK : IsNilpotent K := by
    refine ⟨n, ?_⟩
    dsimp [K]
    rw [← Ideal.map_pow]
    simp [p]
  change RingHom.FiniteType f
  apply finiteType_of_finiteType_quotient f K hK
  let : Algebra (A ⧸ I) (B.obj ⧸ cprimeIdeal I B.obj) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have hres : RingHom.FiniteType
      (Ideal.quotientMap (cprimeIdeal I B.obj) (algebraMap A B.obj)
        Ideal.le_comap_map) := by
    change RingHom.FiniteType (algebraMap (A ⧸ I)
      (B.obj ⧸ cprimeIdeal I B.obj))
    rw [RingHom.finiteType_algebraMap]
    exact B.property.2
  simpa [p, K, f] using finiteType_cprime_stage_quotient I B.obj n hres

theorem cprimeBaseMap_naturality {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) {i j : ℕ+ᵒᵖ} (f : i ⟶ j) :
    (adicQuotientSystem A I).map f ≫
        CommRingCat.ofHom (cprimeBaseComponent I B j.unop) =
      CommRingCat.ofHom (cprimeBaseComponent I B i.unop) ≫
        (cprimeQuotientSystem I B).map f := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The natural transformation from `(A_n)` to the quotient system of `B`. -/
def cprimeBaseMap {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) :
    adicQuotientSystem A I ⟶ cprimeQuotientSystem I B where
  app n := CommRingCat.ofHom (cprimeBaseComponent I B n.unop)
  naturality := by
    intro i j f
    exact cprimeBaseMap_naturality I B f

/-- The structured arrow underlying the quotient system of `B`. -/
def cprimeQuotientArrow {A : Type u} [CommRing A] (I : Ideal A)
    (B : CommAlgCat A) : AdicSystemArrow A I :=
  StructuredArrow.mk (cprimeBaseMap I B)

/-- The quotient system of a complete algebra satisfies the defining system conditions. -/
theorem cprimeQuotientArrow_property {A : Type u} [CommRing A] (I : Ideal A)
    (B : CompleteAlgebraCategory A I) :
    AdicSystemProperty I (cprimeQuotientArrow I B.obj) := by
  change
    (∀ n : ℕ+, RingHom.FiniteType (cprimeBaseComponent I B.obj n)) ∧
      (∀ n : ℕ+, Nonempty (AdicSystemStep I (cprimeQuotientArrow I B.obj) n))
  constructor
  · intro n
    exact cprimeBaseComponent_finiteType I B n
  · intro n
    refine ⟨{ equivalence := ?_, transition_eq := ?_ }⟩
    · change
        (B.obj ⧸ (cprimeIdeal I B.obj) ^ ((n + 1 : ℕ+) : ℕ)) ⧸
            Ideal.map (cprimeBaseComponent I B.obj (n + 1))
              (adicStagePowerIdeal I n) ≃+*
          B.obj ⧸ (cprimeIdeal I B.obj) ^ (n : ℕ)
      let p : Ideal A := I ^ ((n + 1 : ℕ+) : ℕ)
      let J : Ideal B.obj :=
        (cprimeIdeal I B.obj) ^ ((n + 1 : ℕ+) : ℕ)
      let K : Ideal (A ⧸ p) :=
        Ideal.map (Ideal.Quotient.mk p) (I ^ (n : ℕ))
      let f := cprimeBaseComponent I B.obj (n + 1)
      let L : Ideal (B.obj ⧸ J) :=
        ((cprimeIdeal I B.obj) ^ (n : ℕ)).map (Ideal.Quotient.mk J)
      have hL : K.map f = L := by
        dsimp [K, L]
        rw [Ideal.map_map]
        change Ideal.map ((Ideal.Quotient.mk J).comp (algebraMap A B.obj))
          (I ^ (n : ℕ)) = _
        rw [cprimeIdeal, ← Ideal.map_pow, ← Ideal.map_map]
      have hJ : J ≤ (cprimeIdeal I B.obj) ^ (n : ℕ) := by
        dsimp [J]
        exact Ideal.pow_le_pow_right (I := cprimeIdeal I B.obj) (Nat.le_succ (n : ℕ))
      let e0 : ((B.obj ⧸ J) ⧸ L) ≃+*
          (B.obj ⧸ (cprimeIdeal I B.obj) ^ (n : ℕ)) :=
        DoubleQuot.quotQuotEquivQuotOfLE hJ
      have e : (cprimeQuotientStage I B.obj (n + 1) ⧸ L) ≃+*
          (B.obj ⧸ (cprimeIdeal I B.obj) ^ (n : ℕ)) := by
        simpa [cprimeQuotientStage, J] using e0
      let q : (cprimeQuotientStage I B.obj (n + 1) ⧸ K.map f) ≃+*
          (cprimeQuotientStage I B.obj (n + 1) ⧸ L) :=
        Ideal.quotEquivOfEq hL
      change (B.obj ⧸ J) ⧸ K.map f ≃+*
        B.obj ⧸ (cprimeIdeal I B.obj) ^ (n : ℕ)
      exact q.trans e
    · apply RingHom.ext
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl

/-- The object part of the canonical functor `𝓒' → 𝓒`. -/
def completeAlgebraSystemObject {A : Type u} [CommRing A] (I : Ideal A)
    (B : CompleteAlgebraCategory A I) : AdicSystemCategory A I :=
  ⟨cprimeQuotientArrow I B.obj, cprimeQuotientArrow_property I B⟩

/-- The ideal inclusion needed for the quotient map induced by an algebra map. -/
theorem cprimeQuotientMapIdeal_le {A : Type u} [CommRing A] (I : Ideal A)
    {B C : CommAlgCat A} (f : B ⟶ C) (n : ℕ+) :
    (cprimeIdeal I B) ^ (n : ℕ) ≤
      ((cprimeIdeal I C) ^ (n : ℕ)).comap f.hom.toRingHom := by
  have hf : f.hom.toRingHom.comp (algebraMap A B) = algebraMap A C := by
    ext x
    exact f.hom.commutes x
  have hmap :
      Ideal.map f.hom.toRingHom ((cprimeIdeal I B) ^ (n : ℕ)) =
        (cprimeIdeal I C) ^ (n : ℕ) := by
    simp only [cprimeIdeal]
    rw [← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map, hf]
  rw [← hmap]
  exact Ideal.le_comap_map

/-- The map on quotient stages induced by an `A`-algebra map. -/
def cprimeQuotientMapComponent {A : Type u} [CommRing A] (I : Ideal A)
    {B C : CommAlgCat A} (f : B ⟶ C) (n : ℕ+) :
    cprimeQuotientStage I B n →+* cprimeQuotientStage I C n :=
  Ideal.quotientMap
    ((cprimeIdeal I C) ^ (n : ℕ)) f.hom.toRingHom
    (cprimeQuotientMapIdeal_le I f n)

theorem cprimeQuotientMap_naturality {A : Type u} [CommRing A] (I : Ideal A)
    {B C : CommAlgCat A} (f : B ⟶ C) {i j : ℕ+ᵒᵖ} (g : i ⟶ j) :
    (cprimeQuotientSystem I B).map g ≫
        CommRingCat.ofHom (cprimeQuotientMapComponent I f j.unop) =
      CommRingCat.ofHom (cprimeQuotientMapComponent I f i.unop) ≫
        (cprimeQuotientSystem I C).map g := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The natural transformation induced on quotient systems by an algebra map. -/
def cprimeQuotientMap {A : Type u} [CommRing A] (I : Ideal A)
    {B C : CommAlgCat A} (f : B ⟶ C) :
    cprimeQuotientSystem I B ⟶ cprimeQuotientSystem I C where
  app n := CommRingCat.ofHom (cprimeQuotientMapComponent I f n.unop)
  naturality := by
    intro i j g
    exact cprimeQuotientMap_naturality I f g

theorem cprimeBaseMap_map_compatibility {A : Type u} [CommRing A]
    (I : Ideal A) {B C : CommAlgCat A} (f : B ⟶ C) :
    cprimeBaseMap I B ≫ cprimeQuotientMap I f = cprimeBaseMap I C := by
  apply CategoryTheory.NatTrans.ext
  funext n
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change cprimeQuotientMapComponent I f n.unop
      (cprimeBaseComponent I B n.unop x) =
    cprimeBaseComponent I C n.unop x
  dsimp [cprimeQuotientMapComponent, cprimeBaseComponent]
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.quotientMap_mk]
  exact congrArg (Ideal.Quotient.mk _) (f.hom.commutes x)

/-- The morphism part of the canonical functor `𝓒' → 𝓒`. -/
def completeAlgebraSystemMap {A : Type u} [CommRing A] (I : Ideal A)
    {B C : CompleteAlgebraCategory A I} (f : B ⟶ C) :
    completeAlgebraSystemObject I B ⟶ completeAlgebraSystemObject I C :=
  ObjectProperty.homMk <|
    StructuredArrow.homMk (cprimeQuotientMap I f.hom)
      (cprimeBaseMap_map_compatibility I f.hom)

theorem completeAlgebraSystemMap_id {A : Type u} [CommRing A]
    (I : Ideal A) (B : CompleteAlgebraCategory A I) :
    completeAlgebraSystemMap I (𝟙 B) = 𝟙 (completeAlgebraSystemObject I B) := by
  apply ObjectProperty.hom_ext
  apply StructuredArrow.hom_ext
  apply CategoryTheory.NatTrans.ext
  funext n
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change cprimeQuotientMapComponent I (𝟙 B.obj) n.unop x = x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem completeAlgebraSystemMap_comp {A : Type u} [CommRing A]
    (I : Ideal A) {B C D : CompleteAlgebraCategory A I}
    (f : B ⟶ C) (g : C ⟶ D) :
    completeAlgebraSystemMap I (f ≫ g) =
      completeAlgebraSystemMap I f ≫ completeAlgebraSystemMap I g := by
  have hfg : (f ≫ g).hom.hom =
      g.hom.hom.comp f.hom.hom := rfl
  apply ObjectProperty.hom_ext
  apply StructuredArrow.hom_ext
  change cprimeQuotientMap I (f ≫ g).hom =
    cprimeQuotientMap I f.hom ≫ cprimeQuotientMap I g.hom
  apply CategoryTheory.NatTrans.ext
  funext n
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change cprimeQuotientMapComponent I (f ≫ g).hom n.unop x =
      cprimeQuotientMapComponent I g.hom n.unop
      (cprimeQuotientMapComponent I f.hom n.unop x)
  dsimp [cprimeQuotientMapComponent]
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The canonical functor `𝓒' → 𝓒`, sending `B` to `(B/I^nB)_n`. -/
def completeAlgebraSystemFunctor {A : Type u} [CommRing A] (I : Ideal A) :
    CompleteAlgebraCategory A I ⥤ AdicSystemCategory A I where
  obj := completeAlgebraSystemObject I
  map f := completeAlgebraSystemMap I f
  map_id := completeAlgebraSystemMap_id I
  map_comp := completeAlgebraSystemMap_comp I

/-! ## The inverse limit and the quasi-inverse statement -/

/-- The underlying inverse-limit ring of an object of `𝓒`. -/
abbrev adicSystemLimitRing {A : Type u} [CommRing A] (I : Ideal A)
    (X : AdicSystemCategory A I) : CommRingCat.{u} :=
  limit X.obj.right

/-- The complete algebra supplied by the inverse limit construction. -/
structure AdicSystemLimitData {A : Type u} [CommRing A] (I : Ideal A)
    (X : AdicSystemCategory A I) where
  algebra : CommAlgCat A
  comparison : (algebra : Type u) ≃+* adicSystemLimitRing I X
  complete : IsAdicComplete (cprimeIdeal I algebra) algebra
  residue_finite : Algebra.FiniteType (A ⧸ I) (cprimeResidueAlgebra I algebra)

/-- The completeness lemma supplies an `A`-algebra structure on the limit. -/
theorem adicSystemLimitData_exists {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) (X : AdicSystemCategory A I) :
    Nonempty (AdicSystemLimitData I X) := by
  sorry

noncomputable def adicSystemLimitData {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) (X : AdicSystemCategory A I) : AdicSystemLimitData I X :=
  Classical.choice (adicSystemLimitData_exists I hI X)

def adicSystemLimitObject {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) (X : AdicSystemCategory A I) : CompleteAlgebraCategory A I :=
  let d := adicSystemLimitData I hI X
  ⟨d.algebra, ⟨d.complete, d.residue_finite⟩⟩

/-- The limit algebra has the prescribed quotient at every positive stage. -/
theorem adicSystemLimit_quotient_presentation {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I.FG) (X : AdicSystemCategory A I) (n : ℕ+) :
    Nonempty
      (((adicSystemLimitObject I hI X).obj : Type u) ⧸
          (cprimeIdeal I (adicSystemLimitObject I hI X).obj) ^ (n : ℕ) ≃+*
        X.obj.right.obj (Opposite.op n)) := by
  sorry

/-- A map of systems induces a map between the chosen complete limit algebras. -/
theorem adicSystemLimitMap_exists {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) {X Y : AdicSystemCategory A I} (f : X ⟶ Y) :
    Nonempty (adicSystemLimitObject I hI X ⟶ adicSystemLimitObject I hI Y) := by
  sorry

/-- The functor from `𝓒` to `𝓒'` defined by inverse limit. -/
theorem systemLimitFunctor_exists {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) :
    Nonempty (AdicSystemCategory A I ⥤ CompleteAlgebraCategory A I) := by
  sorry

noncomputable def systemLimitFunctor {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) : AdicSystemCategory A I ⥤ CompleteAlgebraCategory A I :=
  Classical.choice (systemLimitFunctor_exists I hI)

/-- The two constructions are quasi-inverse equivalences of categories. -/
theorem quotient_limit_quasiInverse {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I.FG) :
    Nonempty
        (completeAlgebraSystemFunctor I ⋙ systemLimitFunctor I hI ≅
          𝟭 (CompleteAlgebraCategory A I)) ∧
      Nonempty
        (systemLimitFunctor I hI ⋙ completeAlgebraSystemFunctor I ≅
          𝟭 (AdicSystemCategory A I)) := by
  sorry

/-- Conversely, completeness identifies an algebra with the limit of its quotients. -/
theorem completeAlgebra_limit_presentation {A : Type u} [CommRing A]
    (I : Ideal A) (B : CompleteAlgebraCategory A I) :
    Nonempty
      (B.obj ≃+*
        ((limit (cprimeQuotientSystem I B.obj) : CommRingCat.{u}) : Type u)) := by
  sorry

/-! ## Presentations by completed polynomial algebras -/

/-- The completion of a finite-type `A`-algebra for the extended ideal. -/
def adicCompletionAlgebra {A : Type u} [CommRing A] (I : Ideal A)
    (C : CommAlgCat A) : CommAlgCat A :=
  CommAlgCat.of A (AdicCompletion (cprimeIdeal I C) C)

/-- Every finite-type `A`-algebra has a complete finite-type completion. -/
theorem adicCompletionAlgebra_property {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (C : CommAlgCat A)
    (hC : Algebra.FiniteType A C) :
    CompleteAlgebraProperty I (adicCompletionAlgebra I C) := by
  sorry

/-- A polynomial algebra in `r` variables over `A`. -/
def polynomialAlgebra {A : Type u} [CommRing A] (r : ℕ) : CommAlgCat A :=
  CommAlgCat.of A (MvPolynomial (Fin r) A)

/-- The completed polynomial algebra `A⟦x₁, ..., xᵣ⟧`. -/
def polynomialCompletion {A : Type u} [CommRing A] (I : Ideal A) (r : ℕ) :
    CommAlgCat A :=
  adicCompletionAlgebra I (polynomialAlgebra r)

theorem polynomialCompletion_property {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (r : ℕ) :
    CompleteAlgebraProperty I (polynomialCompletion I r) := by
  sorry

/-- Every complete algebra in `𝓒'` is a quotient of a completed polynomial algebra. -/
theorem exists_polynomialCompletion_quotient {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (B : CompleteAlgebraCategory A I) :
    ∃ (r : ℕ) (J : Ideal (polynomialCompletion I r)),
        Nonempty
        (B.obj ≃ₐ[A]
          (polynomialCompletion I r : Type u) ⧸ J) := by
  sorry

/-! ## The four Noetherian assertions -/

/-- A complete algebra in `𝓒'` is Noetherian when `A` is Noetherian. -/
theorem completeAlgebra_isNoetherian {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (B : CompleteAlgebraCategory A I) :
    IsNoetherianRing B.obj := by
  sorry

/-- A quotient of an object of `𝓒'` is again an object of `𝓒'` over a Noetherian base. -/
theorem quotient_completeAlgebra_property {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (B : CompleteAlgebraCategory A I)
    (J : Ideal B.obj) :
    CompleteAlgebraProperty I (quotientCommAlg B.obj J) := by
  sorry

/-- The quotient construction used in the second Noetherian assertion. -/
def quotientCompleteAlgebra {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (B : CompleteAlgebraCategory A I)
    (J : Ideal B.obj) : CompleteAlgebraCategory A I :=
  ⟨quotientCommAlg B.obj J, quotient_completeAlgebra_property I B J⟩

/-- The completion of a finite-type algebra is in `𝓒'`. -/
theorem finiteType_completion_completeAlgebra_property {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (C : CommAlgCat A)
    (hC : Algebra.FiniteType A C) :
    CompleteAlgebraProperty I (adicCompletionAlgebra I C) := by
  exact adicCompletionAlgebra_property I C hC

/-! ## The warning without Noetherian hypotheses -/

/-- Data witnessing that quotient closure for `𝓒'` is not a general-ring fact. -/
structure CPrimeQuotientFailure where
  base : Type u
  [commRing : CommRing base]
  ideal : Ideal base
  algebra : CommAlgCat base
  quotientIdeal : Ideal algebra
  base_complete : CompleteAlgebraProperty ideal algebra
  quotient_not_complete :
    ¬ CompleteAlgebraProperty ideal (quotientCommAlg algebra quotientIdeal)

/-- The non-Noetherian quotient warning from the source. -/
theorem exists_cprime_quotient_failure : Nonempty CPrimeQuotientFailure := by
  sorry

/-! ## Base change -/

/-- Data for a base change `A₁ → A₂` carrying `I₁^c` into `I₂`. -/
structure AdicBaseChangeData (A₁ A₂ : Type u) [CommRing A₁] [CommRing A₂] where
  map : A₁ →+* A₂
  I₁ : Ideal A₁
  I₂ : Ideal A₂
  exponent : ℕ+
  ideal_le : Ideal.map map (I₁ ^ (exponent : ℕ)) ≤ I₂

theorem baseChange_power_le {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    (D : AdicBaseChangeData A₁ A₂) (n : ℕ+) :
    D.I₁ ^ ((D.exponent * n : ℕ+) : ℕ) ≤
      (D.I₂ ^ (n : ℕ)).comap D.map := by
  sorry

/-- The induced map `A₁/I₁^(cn) → A₂/I₂^n`. -/
def baseChangeQuotientComponent {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    (D : AdicBaseChangeData A₁ A₂) (n : ℕ+) :
    adicQuotient A₁ D.I₁ (D.exponent * n) →+*
      adicQuotient A₂ D.I₂ n :=
  Ideal.quotientMap (D.I₂ ^ (n : ℕ)) D.map
    (baseChange_power_le D n)

/-- The stagewise tensor product appearing in base change of systems. -/
def systemBaseChangeStage {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    (D : AdicBaseChangeData A₁ A₂) (X : AdicSystemCategory A₁ D.I₁)
    (n : ℕ+) : CommRingCat.{u} := by
  let R := adicQuotient A₁ D.I₁ (D.exponent * n)
  letI : Algebra R (X.obj.right.obj (Opposite.op (D.exponent * n))) :=
    (X.obj.hom.app (Opposite.op (D.exponent * n))).hom.toAlgebra
  letI : Algebra R (adicQuotient A₂ D.I₂ n) :=
    (baseChangeQuotientComponent D n).toAlgebra
  exact CommRingCat.of
    (X.obj.right.obj (Opposite.op (D.exponent * n)) ⊗[R]
      adicQuotient A₂ D.I₂ n)

/-- The system base-change functor supplied by the stagewise tensor products. -/
theorem systemBaseChangeFunctor_exists {A₁ A₂ : Type u}
    [CommRing A₁] [CommRing A₂] (D : AdicBaseChangeData A₁ A₂) :
    Nonempty
      (AdicSystemCategory A₁ D.I₁ ⥤ AdicSystemCategory A₂ D.I₂) := by
  sorry

noncomputable def systemBaseChangeFunctor {A₁ A₂ : Type u}
    [CommRing A₁] [CommRing A₂] (D : AdicBaseChangeData A₁ A₂) :
    AdicSystemCategory A₁ D.I₁ ⥤ AdicSystemCategory A₂ D.I₂ :=
  Classical.choice (systemBaseChangeFunctor_exists D)

/-- The system base-change functor has the source's tensor-product stages. -/
theorem systemBaseChangeFunctor_stage_spec {A₁ A₂ : Type u}
    [CommRing A₁] [CommRing A₂] (D : AdicBaseChangeData A₁ A₂)
    (X : AdicSystemCategory A₁ D.I₁) (n : ℕ+) :
    Nonempty
      (((systemBaseChangeFunctor D).obj X).obj.right.obj (Opposite.op n) ≃+*
        (systemBaseChangeStage D X n : Type u)) := by
  sorry

/-- The completed tensor product appearing in base change of complete algebras. -/
def completeBaseChangeAlgebra {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    (D : AdicBaseChangeData A₁ A₂) (B : CompleteAlgebraCategory A₁ D.I₁) :
    CommAlgCat A₂ := by
  letI : Algebra A₁ A₂ := D.map.toAlgebra
  let T := B.obj ⊗[A₁] A₂
  letI : Algebra A₂ T := Algebra.TensorProduct.rightAlgebra
  exact CommAlgCat.of A₂
    (AdicCompletion (Ideal.map (algebraMap A₂ T) D.I₂) T)

theorem completeBaseChangeAlgebra_property {A₁ A₂ : Type u}
    [CommRing A₁] [CommRing A₂] (D : AdicBaseChangeData A₁ A₂)
    (hI₂ : D.I₂.FG) (B : CompleteAlgebraCategory A₁ D.I₁) :
    CompleteAlgebraProperty D.I₂ (completeBaseChangeAlgebra D B) := by
  sorry

/-- The object part of completed tensor-product base change. -/
def completeBaseChangeObject {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    (D : AdicBaseChangeData A₁ A₂) (hI₂ : D.I₂.FG)
    (B : CompleteAlgebraCategory A₁ D.I₁) :
    CompleteAlgebraCategory A₂ D.I₂ :=
  ⟨completeBaseChangeAlgebra D B, completeBaseChangeAlgebra_property D hI₂ B⟩

/-- Base change on `𝓒'`, after completing the tensor product. -/
theorem completeBaseChangeFunctor_exists {A₁ A₂ : Type u}
    [CommRing A₁] [CommRing A₂] (D : AdicBaseChangeData A₁ A₂)
    (hI₂ : D.I₂.FG) :
    Nonempty
      (CompleteAlgebraCategory A₁ D.I₁ ⥤ CompleteAlgebraCategory A₂ D.I₂) := by
  sorry

noncomputable def completeBaseChangeFunctor {A₁ A₂ : Type u}
    [CommRing A₁] [CommRing A₂] (D : AdicBaseChangeData A₁ A₂)
    (hI₂ : D.I₂.FG) :
    CompleteAlgebraCategory A₁ D.I₁ ⥤ CompleteAlgebraCategory A₂ D.I₂ :=
  Classical.choice (completeBaseChangeFunctor_exists D hI₂)

/-- The completed base-change functor has the displayed completed tensor product as its object. -/
theorem completeBaseChangeFunctor_obj_spec {A₁ A₂ : Type u}
    [CommRing A₁] [CommRing A₂] (D : AdicBaseChangeData A₁ A₂)
    (hI₂ : D.I₂.FG) (B : CompleteAlgebraCategory A₁ D.I₁) :
    Nonempty
      ((completeBaseChangeFunctor D hI₂).obj B ≅ completeBaseChangeObject D hI₂ B) := by
  sorry

/-- The two base-change constructions agree through the equivalences `𝓒 ≃ 𝓒'`. -/
theorem baseChange_functors_agree {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    (D : AdicBaseChangeData A₁ A₂) (hI₁ : D.I₁.FG) (hI₂ : D.I₂.FG) :
    Nonempty
      (completeBaseChangeFunctor D hI₂ ≅
        completeAlgebraSystemFunctor D.I₁ ⋙
          systemBaseChangeFunctor D ⋙
          systemLimitFunctor D.I₂ hI₂) := by
  sorry

/-! ## Closed immersions and the final base-change identity -/

/-- The data for the closed-immersion base change in the source. -/
structure ClosedImmersionData (A : Type u) [CommRing A] where
  I : Ideal A
  a : Ideal A
  Ibar : Ideal (A ⧸ a)
  c : ℕ+
  d : ℕ+
  I_power_le :
    Ideal.map (Ideal.Quotient.mk a) (I ^ (c : ℕ)) ≤ Ibar
  Ibar_power_le :
    Ibar ^ (d : ℕ) ≤ Ideal.map (Ideal.Quotient.mk a) I

theorem closedImmersion_Ibar_fg {A : Type u} [CommRing A]
    [IsNoetherianRing A] (D : ClosedImmersionData A) : D.Ibar.FG := by
  sorry

/-- The quotient `B/aB`, as an algebra over `A/a`. -/
def closedImmersionQuotient {A : Type u} [CommRing A]
    (D : ClosedImmersionData A) (B : CompleteAlgebraCategory A D.I) :
    CommAlgCat (A ⧸ D.a) := by
  let J : Ideal B.obj := Ideal.map (algebraMap A B.obj) D.a
  letI : Algebra (A ⧸ D.a) (B.obj ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (R := A) (A := B.obj) (p := D.a) (P := J) Ideal.le_comap_map
  exact CommAlgCat.of (A ⧸ D.a) (B.obj ⧸ J)

/-- The tensor product with `A/a` is canonically the quotient `B/aB`. -/
def closedImmersionTensorAlgebra {A : Type u} [CommRing A]
    (D : ClosedImmersionData A) (B : CompleteAlgebraCategory A D.I) :
    CommAlgCat (A ⧸ D.a) := by
  letI : Algebra A (A ⧸ D.a) :=
    (Ideal.Quotient.mk D.a).toAlgebra
  let T := (A ⧸ D.a) ⊗[A] B.obj
  letI : Semiring T := Algebra.TensorProduct.instSemiring
  letI : CommRing T := Algebra.TensorProduct.instCommRing
  letI : Algebra (A ⧸ D.a) T := Algebra.TensorProduct.leftAlgebra
  exact CommAlgCat.of (A ⧸ D.a) T

theorem closedImmersion_tensor_quotient_equiv {A : Type u} [CommRing A]
    (D : ClosedImmersionData A) (B : CompleteAlgebraCategory A D.I) :
    Nonempty
      ((closedImmersionTensorAlgebra D B : Type u) ≃ₐ[A ⧸ D.a]
        (closedImmersionQuotient D B : Type u)) := by
  sorry

/-- The closed-immersion completion is the completed tensor product from base change. -/
def closedImmersionBaseChangeData {A : Type u} [CommRing A]
    (D : ClosedImmersionData A) :
    AdicBaseChangeData A (A ⧸ D.a) where
  map := Ideal.Quotient.mk D.a
  I₁ := D.I
  I₂ := D.Ibar
  exponent := D.c
  ideal_le := D.I_power_le

def closedImmersionBaseChangeAlgebra {A : Type u} [CommRing A]
    (D : ClosedImmersionData A) (B : CompleteAlgebraCategory A D.I) :
    CommAlgCat (A ⧸ D.a) :=
  completeBaseChangeAlgebra (closedImmersionBaseChangeData D) B

/-- The quotient `B/aB` is complete for the induced `Ibar`-adic topology. -/
theorem closedImmersion_quotient_complete {A : Type u} [CommRing A]
    [IsNoetherianRing A] (D : ClosedImmersionData A)
    (B : CompleteAlgebraCategory A D.I) :
    CompleteAlgebraProperty D.Ibar (closedImmersionQuotient D B) := by
  sorry

/-- The closed-immersion quotient as an object of the target complete-algebra category. -/
def closedImmersionQuotientObject {A : Type u} [CommRing A]
    [IsNoetherianRing A] (D : ClosedImmersionData A)
    (B : CompleteAlgebraCategory A D.I) :
    CompleteAlgebraCategory (A ⧸ D.a) D.Ibar :=
  ⟨closedImmersionQuotient D B, closedImmersion_quotient_complete D B⟩

/-- The source's identity `(B ⊗ Abar)^ = (B/aB)^ = B/aB`, expressed canonically. -/
theorem closedImmersion_completion_identity {A : Type u} [CommRing A]
    [IsNoetherianRing A] (D : ClosedImmersionData A)
    (B : CompleteAlgebraCategory A D.I) :
    Nonempty
      (closedImmersionBaseChangeAlgebra D B ≅ closedImmersionQuotient D B) := by
  sorry

/-- The target base-change functor is the quotient functor `B ↦ B/aB`. -/
theorem closedImmersion_baseChangeFunctor_obj {A : Type u} [CommRing A]
    [IsNoetherianRing A] (D : ClosedImmersionData A)
    (B : CompleteAlgebraCategory A D.I) :
    Nonempty
      ((completeBaseChangeFunctor (closedImmersionBaseChangeData D)
          (closedImmersion_Ibar_fg D)).obj B ≅
        closedImmersionQuotientObject D B) := by
  sorry

end

end Formalization.Books.Restricted.Unit02
