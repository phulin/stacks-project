import Formalization.Books.Sheaves.Unit06.PresheavesOfModules
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Sheaves on Spaces, Chapter 14: Stalks of presheaves of modules

The source section `books/sheaves.tex:1137--1176` has two statements.  The
first is implemented by Mathlib's canonical module structure on the stalk of
a presheaf of modules, together with its germ compatibility lemma.  The
second uses the change-of-rings presheaf from Chapter 6.  Its tensor notation
is represented by extension of scalars at the stalk and by a canonical module
isomorphism.  The commutative-ring presheaf aliases from Chapter 6 make the
book's global convention on rings explicit while reusing the earlier
`RingCat`-based presheaf-of-modules API.
-/

namespace Formalization.Books.Sheaves.Unit14

open CategoryTheory Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit06

universe u

noncomputable section

/-! ## The module structure on a stalk -/

/--
The canonical `O_x`-module structure on the underlying abelian group of the
stalk of an `O`-module presheaf.  This is the filtered-colimit structure from
Mathlib, not a parallel transported structure.
-/
noncomputable abbrev stalkModule
    {X : TopCat.{u}} (O : CommRingPresheaf X)
    (F : CommRingPresheafModule O) (x : X) :
    Module (O.stalk x)
      (↑(TopCat.Presheaf.stalk F.presheaf x)) :=
  inferInstance

/-! The germ maps respect the canonical scalar action on the stalk. -/
theorem germ_smul
    {X : TopCat.{u}} {O : CommRingPresheaf X}
    {F : CommRingPresheafModule O}
    (x : X) (U : Opens X) (hx : x ∈ U)
    (r : (O ⋙ (forget₂ CommRingCat RingCat)).obj (op U))
    (m : F.obj (op U)) :
    TopCat.Presheaf.germ F.presheaf U x hx (r • m) =
      TopCat.Presheaf.germ O U x hx r •
        TopCat.Presheaf.germ F.presheaf U x hx m := by
  exact PresheafOfModules.germ_smul F x U hx r m

/-! ## Stalks and change of rings -/

/--
The stalk-level extension of scalars corresponding to the source's
`F_x ⊗_{O_x} O'_x`.  Mathlib's canonical extension-of-scalars object is
`O'_x ⊗_{O_x} F_x`; over commutative stalk rings this is the same canonical
base-change module as the source's ordering.
-/
noncomputable abbrev stalkTensorProduct
    {X : TopCat.{u}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (F : CommRingPresheafModule O) (x : X) :
    ModuleCat (O'.stalk x) :=
  (ModuleCat.extendScalars
      ((TopCat.Presheaf.stalkFunctor (CommRingCat.{u}) x).map α).hom).obj
    (ModuleCat.of (O.stalk x)
        (↑(TopCat.Presheaf.stalk F.presheaf x)))

/--
The stalk of the presheaf change of rings is canonically the stalk-level
extension of scalars.  This is the source's equality of modules in its
usable isomorphism form.
-/
theorem stalk_tensorProductPresheaf_iso
    {X : TopCat.{u}} {O O' : CommRingPresheaf X}
    (α : O ⟶ O') (F : CommRingPresheafModule O) (x : X) :
    Nonempty (stalkTensorProduct α F x ≅
      ModuleCat.of (O'.stalk x)
        (↑(TopCat.Presheaf.stalk
          (tensorProductPresheaf (commRingPresheafMorphismToRingPresheaf α) F).presheaf x))) := by
  sorry

end

end Formalization.Books.Sheaves.Unit14
