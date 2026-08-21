import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.SetTheory.Cardinal.ENat

/-!
# Varieties, Chapter 5: Change of fields and local rings

This file formalizes the three lemmas in the source section. Scheme base
change and stalks use Mathlib's canonical `Scheme`, pullback, and residue-field
interfaces. The source's tensor-product residue map is exposed through its
two canonical restrictions, since the direct affine calculation is deferred
to the proof stage.
-/

namespace Formalization.Books.Varieties.Unit05

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped TensorProduct

universe u

noncomputable section

/-! ## Base change over a field -/

/-- The base change of a scheme over `k` along the field extension `K/k`. -/
def baseChange {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : Scheme.{u} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- The projection from a field base change to the original scheme. -/
abbrev baseChangeProjection {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (K : Type u) [Field K]
    [Algebra k K] :
    baseChange (K := K) f ⟶ X :=
  pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- The projection from a field base change to the spectrum of the new field. -/
abbrev baseChangeFieldProjection {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (K : Type u) [Field K]
    [Algebra k K] :
    baseChange (K := K) f ⟶ Spec (.of K) :=
  pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-! ## Canonical scalar maps at points -/

/-- The scalar map from the ground ring to the stalk at a point of a scheme
over that ground ring. -/
def schemeStalkAlgebraMap {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    k →+* X.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x trivial).hom

/-- The scalar map from the ground ring to the residue field at a point of a
scheme over that ground ring. -/
def schemeResidueFieldAlgebraMap {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    k →+* X.residueField x :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom

/-! ### The tensor map defining the fibre prime -/

/-- The canonical residue-field tensor map at a point of a field base change
exists with the prescribed maps on the two tensor factors. -/
theorem exists_baseChangeResidueFieldTensorMap
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (K : Type u) [Field K] [Algebra k K]
    (y : baseChange (K := K) f) :
    letI : Algebra k (X.residueField (baseChangeProjection f K y)) :=
      (schemeResidueFieldAlgebraMap f (baseChangeProjection f K y)).toAlgebra
    ∃ φ : (X.residueField (baseChangeProjection f K y) ⊗[k] K) →+*
        (baseChange (K := K) f).residueField y,
      φ.comp Algebra.TensorProduct.includeLeftRingHom =
          ((baseChangeProjection f K).residueFieldMap y).hom ∧
        φ.comp Algebra.TensorProduct.includeRight.toRingHom =
          schemeResidueFieldAlgebraMap (baseChangeFieldProjection f K) y := by
  sorry

/-- The residue-field tensor map at a point of a field base change.

Its restrictions are the residue-field map of the first projection and the
scalar map of the second projection. This is the book's map
`κ(x) ⊗_k K → κ(y)`.
-/
noncomputable def baseChangeResidueFieldTensorMap
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (K : Type u) [Field K] [Algebra k K]
    (y : baseChange (K := K) f) :
    letI : Algebra k (X.residueField (baseChangeProjection f K y)) :=
      (schemeResidueFieldAlgebraMap f (baseChangeProjection f K y)).toAlgebra
    (X.residueField (baseChangeProjection f K y) ⊗[k] K) →+*
      (baseChange (K := K) f).residueField y :=
  Classical.choose (exists_baseChangeResidueFieldTensorMap f K y)

/-- The prime of the residue-field tensor product determined by `y`. -/
noncomputable def baseChangePointPrime
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (K : Type u) [Field K] [Algebra k K]
    (y : baseChange (K := K) f) :
    letI : Algebra k (X.residueField (baseChangeProjection f K y)) :=
      (schemeResidueFieldAlgebraMap f (baseChangeProjection f K y)).toAlgebra
    PrimeSpectrum (X.residueField (baseChangeProjection f K y) ⊗[k] K) :=
  ⟨RingHom.ker (baseChangeResidueFieldTensorMap f K y),
    RingHom.ker_isPrime _⟩

/-- The ideal `p₀` in the source's notation. -/
abbrev baseChangePointPrimeIdeal
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (K : Type u) [Field K] [Algebra k K]
    (y : baseChange (K := K) f) :
    letI : Algebra k (X.residueField (baseChangeProjection f K y)) :=
      (schemeResidueFieldAlgebraMap f (baseChangeProjection f K y)).toAlgebra
    Ideal (X.residueField (baseChangeProjection f K y) ⊗[k] K) :=
  (baseChangePointPrime f K y).asIdeal

/-! ### The localization prime in the tensor product of local rings -/

/-- The local-ring tensor map induced by the residue map of `x` exists with
the expected restrictions. -/
theorem exists_baseChangeLocalTensorMap
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (K : Type u) [Field K] [Algebra k K]
    (y : baseChange (K := K) f) :
    let x := baseChangeProjection f K y
    letI : Algebra k (X.presheaf.stalk x) :=
      (schemeStalkAlgebraMap f x).toAlgebra
    letI : Algebra k (X.residueField x) :=
      (schemeResidueFieldAlgebraMap f x).toAlgebra
    ∃ φ : (X.presheaf.stalk x ⊗[k] K) →+*
        (X.residueField x ⊗[k] K),
      φ.comp Algebra.TensorProduct.includeLeftRingHom =
          Algebra.TensorProduct.includeLeftRingHom.comp (X.residue x).hom ∧
        φ.comp Algebra.TensorProduct.includeRight.toRingHom =
          Algebra.TensorProduct.includeRight.toRingHom := by
  sorry

/-- The local-ring tensor map induced by the residue map of `x`. -/
noncomputable def baseChangeLocalTensorMap
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (K : Type u) [Field K] [Algebra k K]
    (y : baseChange (K := K) f) :
    let x := baseChangeProjection f K y
    letI : Algebra k (X.presheaf.stalk x) :=
      (schemeStalkAlgebraMap f x).toAlgebra
    letI : Algebra k (X.residueField x) :=
      (schemeResidueFieldAlgebraMap f x).toAlgebra
    (X.presheaf.stalk x ⊗[k] K) →+*
      (X.residueField x ⊗[k] K) :=
  Classical.choose (exists_baseChangeLocalTensorMap f K y)

/-- The inverse image `p` of `p₀` in the tensor product of local rings. -/
noncomputable def baseChangeLocalPrimeIdeal
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (K : Type u) [Field K] [Algebra k K]
    (y : baseChange (K := K) f) :
    let x := baseChangeProjection f K y
    letI : Algebra k (X.presheaf.stalk x) :=
      (schemeStalkAlgebraMap f x).toAlgebra
    letI : Algebra k (X.residueField x) :=
      (schemeResidueFieldAlgebraMap f x).toAlgebra
    Ideal (X.presheaf.stalk x ⊗[k] K) :=
  Ideal.comap (baseChangeLocalTensorMap f K y) (baseChangePointPrimeIdeal f K y)

theorem baseChangeLocalPrimeIdeal_isPrime
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (K : Type u) [Field K] [Algebra k K]
    (y : baseChange (K := K) f) :
    let x := baseChangeProjection f K y
    letI : Algebra k (X.presheaf.stalk x) :=
      (schemeStalkAlgebraMap f x).toAlgebra
    letI : Algebra k (X.residueField x) :=
      (schemeResidueFieldAlgebraMap f x).toAlgebra
    (baseChangeLocalPrimeIdeal f K y).IsPrime := by
  let x := baseChangeProjection f K y
  letI : Algebra k (X.presheaf.stalk x) :=
    (schemeStalkAlgebraMap f x).toAlgebra
  letI : Algebra k (X.residueField x) :=
    (schemeResidueFieldAlgebraMap f x).toAlgebra
  letI : (baseChangePointPrimeIdeal f K y).IsPrime :=
    (baseChangePointPrime f K y).isPrime
  exact Ideal.comap_isPrime _ _

/-! ## Change of fields and local rings -/

/-- Lemma 5.1(1): the local map on stalks after extending the ground field is
faithfully flat and local. -/
theorem changeOfFields_localRingMap
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (y : baseChange (K := K) f) :
    RingHom.FaithfullyFlat ((baseChangeProjection f K).stalkMap y).hom ∧
      IsLocalHom ((baseChangeProjection f K).stalkMap y).hom := by
  sorry

/-- Lemma 5.1(2): the residue field at `y` is the residue field of the fibre
prime `p₀`. -/
theorem changeOfFields_residueField
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (y : baseChange (K := K) f) :
    letI : Algebra k (X.residueField (baseChangeProjection f K y)) :=
      (schemeResidueFieldAlgebraMap f (baseChangeProjection f K y)).toAlgebra
    Nonempty ((baseChange (K := K) f).residueField y ≃+*
      (baseChangePointPrime f K y).asIdeal.ResidueField) := by
  sorry

/-- Lemma 5.1(3): the local ring at `y` is the localization of the tensor
product of the local ring at `x` at the inverse image `p` of `p₀`. -/
theorem changeOfFields_localRing_localization
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (y : baseChange (K := K) f) :
    let x := baseChangeProjection f K y
    letI : Algebra k (X.presheaf.stalk x) :=
      (schemeStalkAlgebraMap f x).toAlgebra
    letI : Algebra k (X.residueField x) :=
      (schemeResidueFieldAlgebraMap f x).toAlgebra
    letI : (baseChangePointPrimeIdeal f K y).IsPrime :=
      (baseChangePointPrime f K y).isPrime
    letI : (baseChangeLocalPrimeIdeal f K y).IsPrime :=
      baseChangeLocalPrimeIdeal_isPrime f K y
    Nonempty ((baseChange (K := K) f).presheaf.stalk y ≃+*
      Localization.AtPrime (baseChangeLocalPrimeIdeal f K y)) := by
  sorry

/-- Lemma 5.1(4): quotienting the new local ring by the extended old maximal
ideal gives the localization of the residue-field tensor product. -/
theorem changeOfFields_residueQuotient
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (y : baseChange (K := K) f) :
    let x := baseChangeProjection f K y
    letI : Algebra k (X.presheaf.stalk x) :=
      (schemeStalkAlgebraMap f x).toAlgebra
    letI : Algebra k (X.residueField x) :=
      (schemeResidueFieldAlgebraMap f x).toAlgebra
    letI : (baseChangePointPrimeIdeal f K y).IsPrime :=
      (baseChangePointPrime f K y).isPrime
    letI : (baseChangeLocalPrimeIdeal f K y).IsPrime :=
      baseChangeLocalPrimeIdeal_isPrime f K y
    Nonempty ((baseChange (K := K) f).presheaf.stalk y ⧸
        Ideal.map ((baseChangeProjection f K).stalkMap y).hom
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ≃+*
      Localization.AtPrime (baseChangePointPrimeIdeal f K y)) := by
  sorry

/-! ## Dimension and the residue-field tensor product -/

/-- If either field extension is separable, the residue-field tensor product
in Lemma 5.3 is reduced. -/
theorem changeOfFields_residueTensor_isReduced_of_separable
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (y : baseChange (K := K) f)
    (hsep :
      letI : Algebra k (X.residueField (baseChangeProjection f K y)) :=
        (schemeResidueFieldAlgebraMap f (baseChangeProjection f K y)).toAlgebra
      Algebra.IsSeparable k (X.residueField (baseChangeProjection f K y)) ∨
        Algebra.IsSeparable k K) :
    letI : Algebra k (X.residueField (baseChangeProjection f K y)) :=
      (schemeResidueFieldAlgebraMap f (baseChangeProjection f K y)).toAlgebra
    IsReduced (X.residueField (baseChangeProjection f K y) ⊗[k] K) := by
  sorry

/-- Lemma 5.2: the dimension of the fibre local ring is the drop in
transcendence degree and in local Krull dimension. -/
theorem changeOfFields_dimension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [AlgebraicGeometry.LocallyOfFiniteType f]
    (y : baseChange (K := K) f) :
    let x := baseChangeProjection f K y
    letI : Algebra k (X.presheaf.stalk x) :=
      (schemeStalkAlgebraMap f x).toAlgebra
    letI : Algebra k (X.residueField x) :=
      (schemeResidueFieldAlgebraMap f x).toAlgebra
    letI : Algebra K ((baseChange (K := K) f).residueField y) :=
      (schemeResidueFieldAlgebraMap (baseChangeFieldProjection f K) y).toAlgebra
    WithBot.unbotD 0 (ringKrullDim ((baseChange (K := K) f).presheaf.stalk y ⧸
        Ideal.map ((baseChangeProjection f K).stalkMap y).hom
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))) =
      Cardinal.toENat (Algebra.trdeg k (X.residueField x)) -
        Cardinal.toENat (Algebra.trdeg K ((baseChange (K := K) f).residueField y)) ∧
    WithBot.unbotD 0 (ringKrullDim ((baseChange (K := K) f).presheaf.stalk y ⧸
        Ideal.map ((baseChangeProjection f K).stalkMap y).hom
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))) =
      WithBot.unbotD 0 (ringKrullDim ((baseChange (K := K) f).presheaf.stalk y)) -
        WithBot.unbotD 0 (ringKrullDim (X.presheaf.stalk x)) := by
  sorry

/-! ## Unramifiedness at equal-dimensional points -/

/-- Lemma 5.3: under equal local dimensions and reduced residue-field tensor,
the extended maximal ideal is the maximal ideal upstairs. -/
theorem changeOfFields_unramified
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [AlgebraicGeometry.LocallyOfFiniteType f]
    (y : baseChange (K := K) f)
    (hdim : ringKrullDim (X.presheaf.stalk (baseChangeProjection f K y)) =
      ringKrullDim ((baseChange (K := K) f).presheaf.stalk y))
    (hreduced :
      letI : Algebra k (X.residueField (baseChangeProjection f K y)) :=
        (schemeResidueFieldAlgebraMap f (baseChangeProjection f K y)).toAlgebra
      IsReduced (X.residueField (baseChangeProjection f K y) ⊗[k] K)) :
    Ideal.map ((baseChangeProjection f K).stalkMap y).hom
        (IsLocalRing.maximalIdeal
          (X.presheaf.stalk (baseChangeProjection f K y))) =
      IsLocalRing.maximalIdeal ((baseChange (K := K) f).presheaf.stalk y) := by
  sorry

end

end Formalization.Books.Varieties.Unit05
