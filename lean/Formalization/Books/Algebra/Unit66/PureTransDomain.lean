import Formalization.Books.Algebra.Unit66.PureTransGlobal

namespace Formalization.Books.Algebra.Unit66
open scoped TensorProduct

set_option linter.style.haveILetI false

/-- A purely transcendental coefficient field has domain-valued tensor
product with every domain over the base field. -/
theorem isDomain_tensorProduct_adjoin_of_algebraicIndependent_of_domain
    {k D K ι : Type*} [Field k] [CommRing D] [IsDomain D]
    [Field K] [Algebra k D] [Algebra k K] {x : ι → K}
    (hx : AlgebraicIndependent k x) :
    IsDomain (D ⊗[k] IntermediateField.adjoin k (Set.range x)) := by
  let E := FractionRing D
  let f : D →ₗ[k] E := (IsScalarTower.toAlgHom k D E).toLinearMap
  let g : (D ⊗[k] IntermediateField.adjoin k (Set.range x)) →+*
      (E ⊗[k] IntermediateField.adjoin k (Set.range x)) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k D E)
      (AlgHom.id k _)).toRingHom
  have hg : Function.Injective g := by
    have hf : Function.Injective f :=
      FaithfulSMul.algebraMap_injective D E
    have ht : Function.Injective
        (f.rTensor (IntermediateField.adjoin k (Set.range x))) :=
      Module.Flat.rTensor_preserves_injective_linearMap f hf
    exact ht
  letI : IsDomain (E ⊗[k] IntermediateField.adjoin k (Set.range x)) :=
    isDomain_tensorProduct_adjoin_of_algebraicIndependent hx
  exact Function.Injective.isDomain g hg

end Formalization.Books.Algebra.Unit66
