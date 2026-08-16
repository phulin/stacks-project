/-
# More on Morphisms, Chapter 19: Normalization revisited

This file records the affine integral-closure form of the first lemma in the
source section.  The canonical comparison map is provided by Mathlib.
-/

import Mathlib.AlgebraicGeometry.Normalization

namespace MoreMorphisms.Unit19

open scoped TensorProduct

universe u

/-!
The source sheaf statement is affine-locally the following comparison: after
a smooth base change `R → S`, the tensor product of the old integral closure
with `S` is the new integral closure.
-/

noncomputable def integralClosureSmoothBaseChangeEquiv
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra.Smooth R S] :
    S ⊗[R] integralClosure R B ≃ₐ[S] integralClosure S (S ⊗[R] B) :=
  AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R S B)
    (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S) (B := B))

theorem integralClosureSmoothBaseChange_bijective
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra.Smooth R S] :
    Function.Bijective (TensorProduct.toIntegralClosure R S B) :=
  TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S) (B := B)

end MoreMorphisms.Unit19
