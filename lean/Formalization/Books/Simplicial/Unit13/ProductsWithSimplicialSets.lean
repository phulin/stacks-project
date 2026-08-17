import Formalization.Books.Simplicial.Unit12.TruncatedSimplicialObjects
import Formalization.Books.Categories.Unit05.CoproductsOfPairs
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

namespace Formalization.Books.Simplicial.Unit13

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial

universe v u

#check HasBinaryCoproducts
#check HasCoproduct
#check HasCoproducts
#check HasFiniteCoproducts
#check hasFiniteCoproducts_of_hasCoproducts
#check getColimitCocone
#check colimit
#check Sigma
#check Sigma.ι
#check Sigma.desc
#check Sigma.map
#check colimit.isColimit
#check Discrete.functor
#check FunctorCategory.HasColimit
#check hasFiniteCoproducts_of_
#check hasColimit_of_
#check hasCoproduct_of_

end Formalization.Books.Simplicial.Unit13
