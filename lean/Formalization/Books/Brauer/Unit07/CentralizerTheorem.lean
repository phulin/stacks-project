import Formalization.Books.Brauer.Unit07.Foundation

/-!
# Brauer groups, Chapter 7: The centralizer theorem

The source-facing centralizer interfaces were already established with
Mathlib's `Subalgebra.centralizer` in the earlier Brauer formalization.  This
file re-exports those declarations under the chapter-specific namespace.
-/

namespace Formalization.Books.Brauer.Unit07

open Formalization.Books.Brauer
open scoped TensorProduct

/-! ## The centralizer theorem -/

alias IsMaximalCommutativeSubalgebra :=
  Formalization.Books.Brauer.IsMaximalCommutativeSubalgebra

alias centralizer_theorem :=
  Formalization.Books.Brauer.centralizer_theorem

alias lemma_when_tensor_is_equal :=
  Formalization.Books.Brauer.central_simple_tensor_decomposition

theorem lemma_self_centralizing_subfield (k A K : Type*) [Field k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] [Algebra.IsCentral k A]
    [IsSimpleRing A] [Field K] [Algebra k K]
    (f : K →ₐ[k] A) (hf : Function.Injective f) :
    List.TFAE
      [Module.finrank k A = Module.finrank k K ^ 2,
        Subalgebra.centralizer k (Set.range f) = AlgHom.range f,
        IsMaximalCommutativeSubalgebra k A (AlgHom.range f)] := by
  have hfin : FiniteDimensional k K :=
    FiniteDimensional.of_injective f.toLinearMap hf
  exact @Formalization.Books.Brauer.self_centralizing_subfield_tfae
    k A K _ _ _ _ _ _ _ _ hfin f hf

theorem lemma_maximal_subfield (k A K : Type*) [Field k]
    [DivisionRing A] [Algebra k A] [FiniteDimensional k A]
    [Algebra.IsCentral k A] [Field K] [Algebra k K]
    (f : K →ₐ[k] A) (hf : Function.Injective f)
    (hmax : IsMaximalCommutativeSubalgebra k A (AlgHom.range f)) :
    Module.finrank k A = Module.finrank k K ^ 2 := by
  have hfin : FiniteDimensional k K :=
    FiniteDimensional.of_injective f.toLinearMap hf
  exact @Formalization.Books.Brauer.maximal_subfield_dimension_square
    k A K _ _ _ _ _ _ _ hfin f hf hmax

end Formalization.Books.Brauer.Unit07
