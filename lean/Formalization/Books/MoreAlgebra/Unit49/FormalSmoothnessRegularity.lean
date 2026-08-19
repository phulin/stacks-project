import Formalization.Books.MoreAlgebra.Unit40.GeometricRegularityFormalSmoothness
import Formalization.Books.MoreAlgebra.Unit41.RegularRingMaps
import Formalization.Books.MoreAlgebra.Unit48.RegularityAndDerivations
import Formalization.Books.Algebra.Unit97.CompletionForNoetherianRings

/-!
# More Algebra, Chapter 49: Formal smoothness and regularity

This file records the derivation-lifting lemma and the two regularity/formal-
smoothness equivalences from the source section.  Formal smoothness is the
canonical target-ideal predicate from Chapter 37, regular maps use the
Chapter 41 `IsRegularRingMap` predicate, and the special fibre uses Chapter
40's canonical tensor-product order.
-/

namespace Formalization.Books.MoreAlgebra.Unit49

open Formalization.Books.MoreAlgebra.Unit40
open Formalization.Books.MoreAlgebra.Unit37
open Formalization.Books.MoreAlgebra.Unit41
open Formalization.Books.Algebra.Unit97
open Formalization.Books.Algebra.Unit96

noncomputable section

universe u

/-! ## Formal smoothness and derivations -/

/-- A derivation on a Noetherian local source extends across a complete,
formally smooth local target. -/
theorem exists_derivation_extension_of_formallySmooth
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (f : A →+* B) [IsLocalHom f]
    (D : Derivation ℤ A A)
    (hfs : Formalization.Books.MoreAlgebra.Unit37.FormallySmoothForIdeal
      f (IsLocalRing.maximalIdeal B)) :
    ∃ D' : Derivation ℤ B B, ∀ a : A, D' (f a) = f (D a) := by
  sorry

/-! ## The complete-local equivalence -/

/-- For a local map of Noetherian complete local rings, regularity is
equivalent to flatness with geometrically regular special fibre, to the
corresponding special-fibre formal smoothness condition, and to formal
smoothness in the target maximal-ideal-adic topology.

The special fibre is written using Chapter 40's canonical `SpecialFiber`
normalization `k ⊗[A] B`, which is canonically equivalent to the source's
`B ⊗[A] k` presentation. -/
theorem proposition_fs_regular
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (f : A →+* B) [IsLocalHom f] :
    letI : Algebra A B := f.toAlgebra
    letI : IsLocalHom (algebraMap A B) := by
      change IsLocalHom f
      infer_instance
    let k := IsLocalRing.ResidueField A
    let F := SpecialFiber A B
    letI : Algebra k F := Algebra.TensorProduct.leftAlgebra
    List.TFAE
      [ IsRegularRingMap f,
        RingHom.Flat f ∧ IsGeometricallyRegular k F,
        RingHom.Flat f ∧ FormallySmoothLocalMap (A := k) (B := F),
        FormallySmoothLocalMap (A := A) (B := B) ] := by
  sorry

/-! ## André's theorem -/

/-- André's characterization: for a local homomorphism of Noetherian local
rings whose source-to-completion map is regular, the four regularity,
flat/geometrically-regular-fibre, special-fibre formal-smoothness, and target
formal-smoothness conditions are equivalent. -/
theorem theorem_fs_regular
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hcompletion :
      IsRegularRingMap
        (algebraMap A (ringCompletion (IsLocalRing.maximalIdeal A)))) :
    letI : Algebra A B := f.toAlgebra
    letI : IsLocalHom (algebraMap A B) := by
      change IsLocalHom f
      infer_instance
    let k := IsLocalRing.ResidueField A
    let F := SpecialFiber A B
    letI : Algebra k F := Algebra.TensorProduct.leftAlgebra
    List.TFAE
      [ IsRegularRingMap f,
        RingHom.Flat f ∧ IsGeometricallyRegular k F,
        RingHom.Flat f ∧ FormallySmoothLocalMap (A := k) (B := F),
        FormallySmoothLocalMap (A := A) (B := B) ] := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit49
