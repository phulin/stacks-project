import Formalization.Books.Algebra.Unit93.AscendingProperties

/-!
# Commutative Algebra, Chapter 94: Ascending properties of modules

The source's four ascent assertions are already packaged by the earlier
source-faithful interface in Chapter 93.  This chapter-facing declaration
reuses that interface with the canonical `S ⊗[R] M` base-change orientation.
-/

namespace Formalization.Books.Algebra.Unit94

open Formalization.Books.Algebra.Unit84
open Formalization.Books.Algebra.Unit88
open scoped TensorProduct

universe u v

noncomputable section

/- The source lemma has four numbered conclusions; they are the four
   conjuncts of the reused declaration below. -/
theorem ascend_properties_modules
    {R S : Type u} {M : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] :
    (Module.Flat R M → Module.Flat S (S ⊗[R] M)) ∧
      (IsMittagLefflerModule (ModuleCat.of R M) →
        IsMittagLefflerModule (ModuleCat.of S (S ⊗[R] M))) ∧
        (IsDirectSumOfCountablyGeneratedModules (ModuleCat.of R M) →
          IsDirectSumOfCountablyGeneratedModules
            (ModuleCat.of S (S ⊗[R] M))) ∧
          (Module.Projective R M → Module.Projective S (S ⊗[R] M)) :=
  Formalization.Books.Algebra.Unit93.ascend_properties_modules

end

end Formalization.Books.Algebra.Unit94
