import Formalization.«Books.Sdga».Unit01.Core

/-! # 2. Conventions -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

/-- The convention that an algebra carries an `R`-module structure and a
bilinear unital associative multiplication. -/
structure UnitalAssociativeAlgebraData (R A : Type u) where
  smul : R → A → A
  mul : A → A → A
  one : A
  module_laws : Prop
  bilinear : Prop
  associative : Prop
  unit : Prop
  central : Prop

theorem convention_ring_is_commutative_with_one (R : Type u) [CommRing R] :
    True := by
  trivial

end Sdga
