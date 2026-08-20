import Formalization.Books.Modules.Unit17.FlatModules
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Properties of Schemes, Chapter 20: Flat modules

The source section is `books/properties.tex:2590--2610`.  Its only precise
assertion identifies flatness of a quasi-coherent module on an affine scheme
with flatness of the corresponding ring module.
-/

namespace Formalization.Books.Properties.Unit20

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

/-! ## Lemma `lemma-flat-module` -/

/-- On an affine scheme, the tilde module is flat exactly when the original
module is flat.  The left-hand side uses the earlier ringed-space definition
of sheaf flatness, while `AlgebraicGeometry.tilde` is Mathlib's canonical
quasi-coherent module construction. -/
theorem lemma_flat_module (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    Formalization.Books.Modules.Unit17.IsFlat
        (AlgebraicGeometry.Scheme.sheaf (AlgebraicGeometry.Spec R))
        (AlgebraicGeometry.tilde M) ↔
      Module.Flat (R : Type u) (M : Type u) := by
  sorry

end

end Formalization.Books.Properties.Unit20
