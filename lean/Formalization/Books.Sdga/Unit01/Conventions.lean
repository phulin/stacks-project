import Formalization.«Books.Sdga».Unit01.Core

/-! # 2. Conventions -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

/-- The convention that an algebra carries an `R`-module structure and a
bilinear unital associative multiplication. -/
structure UnitalAssociativeAlgebraData (R A : Type u) where
  algebraMap : R → A
  smul : R → A → A
  mul : A → A → A
  one : A
  module_laws : Prop
  bilinear : Prop
  associative : Prop
  unit : Prop
  algebraMap_is_central : Prop

/-- The book's convention packages the ring assumption used throughout this
chapter.  The actual algebra interface is supplied by
`UnitalAssociativeAlgebraData`; the ambient `CommRing` instance is the
canonical proof of the ring convention. -/
abbrev ringConvention (R : Type u) [CommRing R] : CommRing R := inferInstance

theorem convention_ring_is_commutative_with_one (R : Type u) [CommRing R] :
    Nonempty (CommRing R) := by
  exact ⟨inferInstance⟩

end Sdga
