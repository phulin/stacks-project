import Formalization.Books.Dpa.Unit03
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# Crystalline Cohomology, Chapter 3: Some explicit divided power thickenings

This file formalizes the two explicit thickenings used later for the
connection on a crystal.  The divided-power operations are kept as explicit
functions, while the divided-power axioms are packaged by Mathlib's
`DividedPowers` structure.
-/

namespace Formalization.Books.Crystalline.Unit03

open Formalization.Books.Dpa.Unit03
open Formalization.Books.Dpa.Unit03.DividedPowerRing

universe u

noncomputable section

/-! ## The first-order thickening -/

/-- The carrier `A ⊕ M` of the first-order thickening. -/
structure FirstOrderThickening (A M : Type u) where
  base : A
  infinitesimal : M

@[ext]
theorem FirstOrderThickening.ext {A M : Type u}
    (x y : FirstOrderThickening A M) (hbase : x.base = y.base)
    (hinfinitesimal : x.infinitesimal = y.infinitesimal) : x = y := by
  cases x
  cases y
  cases hbase
  cases hinfinitesimal
  rfl

namespace FirstOrderThickening

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]

instance instAdd : Add (FirstOrderThickening A M) :=
  ⟨fun x y => ⟨x.base + y.base, x.infinitesimal + y.infinitesimal⟩⟩

instance instZero : Zero (FirstOrderThickening A M) := ⟨⟨0, 0⟩⟩

instance instNeg : Neg (FirstOrderThickening A M) :=
  ⟨fun x => ⟨-x.base, -x.infinitesimal⟩⟩

instance instMul : Mul (FirstOrderThickening A M) :=
  ⟨fun x y =>
    ⟨x.base * y.base,
      x.base • y.infinitesimal + y.base • x.infinitesimal⟩⟩

instance instOne : One (FirstOrderThickening A M) := ⟨⟨1, 0⟩⟩

instance : CommRing (FirstOrderThickening A M) :=
  CommRing.ofMinimalAxioms
    (by
      intro x y z
      apply FirstOrderThickening.ext
      · change (x.base + y.base) + z.base = x.base + (y.base + z.base)
        exact add_assoc _ _ _
      · change (x.infinitesimal + y.infinitesimal) + z.infinitesimal =
          x.infinitesimal + (y.infinitesimal + z.infinitesimal)
        exact add_assoc _ _ _)
    (by
      intro x
      apply FirstOrderThickening.ext
      · change 0 + x.base = x.base
        exact zero_add _
      · change 0 + x.infinitesimal = x.infinitesimal
        exact zero_add _)
    (by
      intro x
      apply FirstOrderThickening.ext
      · change -x.base + x.base = 0
        exact neg_add_cancel _
      · change -x.infinitesimal + x.infinitesimal = 0
        exact neg_add_cancel _)
    (by
      intro x y z
      apply FirstOrderThickening.ext
      · change (x.base * y.base) * z.base = x.base * (y.base * z.base)
        exact mul_assoc _ _ _
      · change
          ((x.base * y.base) • z.infinitesimal +
            z.base • (x.base • y.infinitesimal + y.base • x.infinitesimal)) =
            x.base • (y.base • z.infinitesimal + z.base • y.infinitesimal) +
              (y.base * z.base) • x.infinitesimal
        simp [smul_add, add_smul, smul_smul, mul_assoc, mul_comm, mul_left_comm,
          add_assoc, add_comm, add_left_comm])
    (by
      intro x y
      apply FirstOrderThickening.ext
      · change x.base * y.base = y.base * x.base
        exact mul_comm _ _
      · change x.base • y.infinitesimal + y.base • x.infinitesimal =
          y.base • x.infinitesimal + x.base • y.infinitesimal
        exact add_comm _ _)
    (by
      intro x
      apply FirstOrderThickening.ext
      · change 1 * x.base = x.base
        exact one_mul _
      · change 1 • x.infinitesimal + x.base • (0 : M) = x.infinitesimal
        simp)
    (by
      intro x y z
      apply FirstOrderThickening.ext
      · change x.base * (y.base + z.base) = x.base * y.base + x.base * z.base
        exact mul_add _ _ _
      · change x.base • (y.infinitesimal + z.infinitesimal) +
          (y.base + z.base) • x.infinitesimal =
          (x.base • y.infinitesimal + y.base • x.infinitesimal) +
            (x.base • z.infinitesimal + z.base • x.infinitesimal)
        simp [smul_add, add_smul, add_assoc, add_comm, add_left_comm])

/-- The canonical inclusion of `A` into its first-order thickening. -/
def baseHom : A →+* FirstOrderThickening A M where
  toFun a := ⟨a, 0⟩
  map_one' := rfl
  map_mul' x y := by
    change (⟨x * y, (0 : M)⟩ : FirstOrderThickening A M) =
      ⟨x * y, x • (0 : M) + y • (0 : M)⟩
    simp
  map_zero' := rfl
  map_add' x y := by
    change (⟨x + y, (0 : M)⟩ : FirstOrderThickening A M) =
      ⟨x + y, (0 : M) + 0⟩
    simp

/-- The canonical `A`-algebra structure on the first-order thickening. -/
instance algebra : Algebra A (FirstOrderThickening A M) := baseHom.toAlgebra

end FirstOrderThickening

open FirstOrderThickening

/-- The ideal `I ⊕ M` in the first-order thickening. -/
def firstOrderIdeal {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) : Ideal (FirstOrderThickening A M) where
  carrier := {x | x.base ∈ I}
  zero_mem' := by
    change (0 : A) ∈ I
    exact I.zero_mem
  add_mem' := by
    intro x y hx hy
    exact I.add_mem hx hy
  smul_mem' := by
    intro r x hx
    exact I.mul_mem_left r.base hx

/-- The copy of the square-zero ideal `M` inside `A ⊕ M`. -/
def firstOrderInfinitesimal {A M : Type u} [CommRing A] [AddCommGroup M]
    [Module A M] (m : M) : FirstOrderThickening A M :=
  ⟨0, m⟩

@[simp]
theorem firstOrderInfinitesimal_mem_ideal
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (m : M) :
    firstOrderInfinitesimal m ∈ firstOrderIdeal I := by
  exact I.zero_mem

/-- The infinitesimal summand in the first-order thickening has square zero. -/
theorem firstOrderInfinitesimal_mul
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (m m' : M) :
    firstOrderInfinitesimal m * firstOrderInfinitesimal m' =
      (0 : FirstOrderThickening A M) := by
  apply FirstOrderThickening.ext
  · dsimp [firstOrderInfinitesimal]
    change (0 : A) * 0 = 0
    simp
  · dsimp [firstOrderInfinitesimal]
    change (0 : A) • m' + 0 • m = (0 : M)
    simp

/-- The source's formula for the divided powers on the first-order thickening.
The zero case makes the convention `γ_{-1} = 0` explicit. -/
def firstOrderDpow {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (γ : ℕ → A → A) (n : ℕ) (x : FirstOrderThickening A M) :
    FirstOrderThickening A M :=
  match n with
  | 0 => ⟨1, 0⟩
  | n + 1 => ⟨γ (n + 1) x.base, γ n x.base • x.infinitesimal⟩

/-- The first-order thickening as a divided-power ring, once its displayed
divided-power operations have been shown to satisfy the axioms. -/
def firstOrderDividedPowerRing {A M : Type u} [CommRing A] [AddCommGroup M]
    [Module A M] (I : Ideal A)
    (δ : DividedPowers (firstOrderIdeal (A := A) (M := M) I)) :
    DividedPowerRing.{u} :=
  { toCommRing := CommRingCat.of (FirstOrderThickening A M)
    ideal := firstOrderIdeal (A := A) (M := M) I
    dividedPowers := δ }

/-- Existence of the divided powers in the first-order thickening, together
with the fact that the canonical inclusion is a divided-power-ring map. -/
theorem exists_firstOrderDividedPowers
    (A : DividedPowerRing.{u}) (M : Type u) [AddCommGroup M]
    [Module (A : Type u) M] :
    ∃ δ : DividedPowers (firstOrderIdeal (A := (A : Type u)) (M := M) A.ideal),
      (∀ {n : ℕ} {x : FirstOrderThickening (A : Type u) M},
        x ∈ firstOrderIdeal (A := (A : Type u)) (M := M) A.ideal →
          δ.dpow n x =
            firstOrderDpow A.dividedPowers.dpow n x) ∧
      ∃ h : DividedPowerRing.Hom A
          (firstOrderDividedPowerRing (A := (A : Type u)) (M := M) A.ideal δ),
        h.hom = FirstOrderThickening.baseHom := by
  sorry

/-- A chosen divided-power structure on the first-order thickening. -/
noncomputable def firstOrderDividedPowers
    (A : DividedPowerRing.{u}) (M : Type u) [AddCommGroup M]
    [Module (A : Type u) M] :
    DividedPowers (firstOrderIdeal (A := (A : Type u)) (M := M) A.ideal) :=
  Classical.choose (exists_firstOrderDividedPowers A M)

theorem firstOrderDividedPowers_dpow
    (A : DividedPowerRing.{u}) (M : Type u) [AddCommGroup M]
    [Module (A : Type u) M] {n : ℕ}
    {x : FirstOrderThickening (A : Type u) M}
    (hx : x ∈ firstOrderIdeal (A := (A : Type u)) (M := M) A.ideal) :
    (firstOrderDividedPowers A M).dpow n x = firstOrderDpow A.dividedPowers.dpow n x :=
  (Classical.choose_spec (exists_firstOrderDividedPowers A M)).1 hx

/-- The canonical divided-power-ring map from `A` to the chosen first-order
thickening. -/
noncomputable def firstOrderDividedPowerHom
    (A : DividedPowerRing.{u}) (M : Type u) [AddCommGroup M]
    [Module (A : Type u) M] :
    DividedPowerRing.Hom A
      (firstOrderDividedPowerRing (A := (A : Type u)) (M := M) A.ideal
        (firstOrderDividedPowers A M)) :=
  Classical.choose ((Classical.choose_spec (exists_firstOrderDividedPowers A M)).2)

theorem firstOrderDividedPowerHom_eq_baseHom
    (A : DividedPowerRing.{u}) (M : Type u) [AddCommGroup M]
    [Module (A : Type u) M] :
    (firstOrderDividedPowerHom A M).hom = FirstOrderThickening.baseHom :=
  Classical.choose_spec ((Classical.choose_spec (exists_firstOrderDividedPowers A M)).2)

/-! ## The second-order thickening -/

/-- The carrier `A ⊕ M ⊕ N` of the second-order thickening. -/
structure SecondOrderThickening (A M N : Type u) [CommRing A]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) where
  base : A
  first : M
  second : N

@[ext]
theorem SecondOrderThickening.ext {A M N : Type u}
    [CommRing A] [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    (x y : SecondOrderThickening A M N q) (hbase : x.base = y.base)
    (hfirst : x.first = y.first) (hsecond : x.second = y.second) : x = y := by
  cases x
  cases y
  cases hbase
  cases hfirst
  cases hsecond
  rfl

namespace SecondOrderThickening

variable {A M N : Type u} [CommRing A] [AddCommGroup M] [AddCommGroup N]
  [Module A M] [Module A N] (q : M →ₗ[A] M →ₗ[A] N)

instance instAdd : Add (SecondOrderThickening A M N q) :=
  ⟨fun x y => ⟨x.base + y.base, x.first + y.first, x.second + y.second⟩⟩

instance instZero : Zero (SecondOrderThickening A M N q) := ⟨⟨0, 0, 0⟩⟩

instance instNeg : Neg (SecondOrderThickening A M N q) :=
  ⟨fun x => ⟨-x.base, -x.first, -x.second⟩⟩

instance instMul : Mul (SecondOrderThickening A M N q) :=
  ⟨fun x y =>
    ⟨x.base * y.base,
      x.base • y.first + y.base • x.first,
      x.base • y.second + y.base • x.second + q x.first y.first +
        q y.first x.first⟩⟩

instance instOne : One (SecondOrderThickening A M N q) := ⟨⟨1, 0, 0⟩⟩

/-- Associativity of the displayed second-order multiplication. -/
theorem secondOrder_mul_assoc
    (x y z : SecondOrderThickening A M N q) : x * y * z = x * (y * z) := by
  sorry

/-- Left distributivity of the displayed second-order multiplication. -/
theorem secondOrder_left_distrib
    (x y z : SecondOrderThickening A M N q) : x * (y + z) = x * y + x * z := by
  sorry

instance : CommRing (SecondOrderThickening A M N q) :=
  CommRing.ofMinimalAxioms
    (by
      intro x y z
      apply SecondOrderThickening.ext q
      · change (x.base + y.base) + z.base = x.base + (y.base + z.base)
        exact add_assoc _ _ _
      · change (x.first + y.first) + z.first = x.first + (y.first + z.first)
        exact add_assoc _ _ _
      · change (x.second + y.second) + z.second =
          x.second + (y.second + z.second)
        exact add_assoc _ _ _)
    (by
      intro x
      apply SecondOrderThickening.ext q
      · change 0 + x.base = x.base
        exact zero_add _
      · change 0 + x.first = x.first
        exact zero_add _
      · change 0 + x.second = x.second
        exact zero_add _)
    (by
      intro x
      apply SecondOrderThickening.ext q
      · change -x.base + x.base = 0
        exact neg_add_cancel _
      · change -x.first + x.first = 0
        exact neg_add_cancel _
      · change -x.second + x.second = 0
        exact neg_add_cancel _)
    (by
      exact secondOrder_mul_assoc q)
    (by
      intro x y
      apply SecondOrderThickening.ext q
      · change x.base * y.base = y.base * x.base
        exact mul_comm _ _
      · change x.base • y.first + y.base • x.first =
          y.base • x.first + x.base • y.first
        exact add_comm _ _
      · change x.base • y.second + y.base • x.second + q x.first y.first +
          q y.first x.first =
          y.base • x.second + x.base • y.second + q y.first x.first +
            q x.first y.first
        simp [add_comm, add_left_comm, add_assoc])
    (by
      intro x
      apply SecondOrderThickening.ext q
      · change 1 * x.base = x.base
        exact one_mul _
      · change 1 • x.first + x.base • (0 : M) = x.first
        simp
      · change 1 • x.second + x.base • (0 : N) + q 0 x.first + q x.first 0 =
          x.second
        simp)
    (by
      exact secondOrder_left_distrib q)

/-- The canonical inclusion of `A` into its second-order thickening. -/
def baseHom : A →+* SecondOrderThickening A M N q where
  toFun a := ⟨a, 0, 0⟩
  map_one' := rfl
  map_mul' x y := by
    change (⟨x * y, (0 : M), (0 : N)⟩ : SecondOrderThickening A M N q) =
      ⟨x * y, x • (0 : M) + y • (0 : M),
        x • (0 : N) + y • (0 : N) + q 0 0 + q 0 0⟩
    simp
  map_zero' := rfl
  map_add' x y := by
    change (⟨x + y, (0 : M), (0 : N)⟩ : SecondOrderThickening A M N q) =
      ⟨x + y, (0 : M) + 0, (0 : N) + 0⟩
    simp

instance algebra : Algebra A (SecondOrderThickening A M N q) := baseHom q |>.toAlgebra

end SecondOrderThickening

open SecondOrderThickening

/-- The ideal `I ⊕ M ⊕ N` in the second-order thickening. -/
def secondOrderIdeal {A M N : Type u} [CommRing A] [AddCommGroup M]
    [AddCommGroup N] [Module A M] [Module A N]
    (I : Ideal A) (q : M →ₗ[A] M →ₗ[A] N) :
    Ideal (SecondOrderThickening A M N q) where
  carrier := {x | x.base ∈ I}
  zero_mem' := by
    change (0 : A) ∈ I
    exact I.zero_mem
  add_mem' := by
    intro x y hx hy
    exact I.add_mem hx hy
  smul_mem' := by
    intro r x hx
    exact I.mul_mem_left r.base hx

/-- The source's formula for the divided powers on the second-order
thickening, with the low-degree conventions made explicit. -/
def secondOrderDpow {A M N : Type u} [CommRing A] [AddCommGroup M]
    [AddCommGroup N] [Module A M] [Module A N]
    (γ : ℕ → A → A) (q : M →ₗ[A] M →ₗ[A] N) (n : ℕ)
    (x : SecondOrderThickening A M N q) : SecondOrderThickening A M N q :=
  match n with
  | 0 => ⟨1, 0, 0⟩
  | 1 => ⟨γ 1 x.base, γ 0 x.base • x.first, γ 0 x.base • x.second⟩
  | n + 2 =>
      ⟨γ (n + 2) x.base, γ (n + 1) x.base • x.first,
        γ (n + 1) x.base • x.second + γ n x.base • q x.first x.first⟩

/-- The second-order thickening as a divided-power ring, once its displayed
divided-power operations have been shown to satisfy the axioms. -/
def secondOrderDividedPowerRing {A M N : Type u} [CommRing A] [AddCommGroup M]
    [AddCommGroup N] [Module A M] [Module A N]
    (I : Ideal A) (q : M →ₗ[A] M →ₗ[A] N)
    (δ : DividedPowers (secondOrderIdeal I q)) : DividedPowerRing.{u} :=
  { toCommRing := CommRingCat.of (SecondOrderThickening A M N q)
    ideal := secondOrderIdeal I q
    dividedPowers := δ }

/-- Existence of the divided powers in the second-order thickening, together
with the fact that the canonical inclusion is a divided-power-ring map. -/
theorem exists_secondOrderDividedPowers
    (A : DividedPowerRing.{u}) (M N : Type u) [AddCommGroup M]
    [AddCommGroup N] [Module (A : Type u) M] [Module (A : Type u) N]
    (q : M →ₗ[(A : Type u)] M →ₗ[(A : Type u)] N) :
    ∃ δ : DividedPowers (secondOrderIdeal A.ideal q),
      (∀ {n : ℕ} {x : SecondOrderThickening (A : Type u) M N q},
        x ∈ secondOrderIdeal A.ideal q →
          δ.dpow n x = secondOrderDpow A.dividedPowers.dpow q n x) ∧
      ∃ h : DividedPowerRing.Hom A
          (secondOrderDividedPowerRing A.ideal q δ),
        h.hom = SecondOrderThickening.baseHom q := by
  sorry

/-- A chosen divided-power structure on the second-order thickening. -/
noncomputable def secondOrderDividedPowers
    (A : DividedPowerRing.{u}) (M N : Type u) [AddCommGroup M]
    [AddCommGroup N] [Module (A : Type u) M] [Module (A : Type u) N]
    (q : M →ₗ[(A : Type u)] M →ₗ[(A : Type u)] N) :
    DividedPowers (secondOrderIdeal A.ideal q) :=
  Classical.choose (exists_secondOrderDividedPowers A M N q)

theorem secondOrderDividedPowers_dpow
    (A : DividedPowerRing.{u}) (M N : Type u) [AddCommGroup M]
    [AddCommGroup N] [Module (A : Type u) M] [Module (A : Type u) N]
    (q : M →ₗ[(A : Type u)] M →ₗ[(A : Type u)] N) {n : ℕ}
    {x : SecondOrderThickening (A : Type u) M N q}
    (hx : x ∈ secondOrderIdeal A.ideal q) :
    (secondOrderDividedPowers A M N q).dpow n x =
      secondOrderDpow A.dividedPowers.dpow q n x :=
  (Classical.choose_spec (exists_secondOrderDividedPowers A M N q)).1 hx

/-- The canonical divided-power-ring map from `A` to the chosen second-order
thickening. -/
noncomputable def secondOrderDividedPowerHom
    (A : DividedPowerRing.{u}) (M N : Type u) [AddCommGroup M]
    [AddCommGroup N] [Module (A : Type u) M] [Module (A : Type u) N]
    (q : M →ₗ[(A : Type u)] M →ₗ[(A : Type u)] N) :
    DividedPowerRing.Hom A
      (secondOrderDividedPowerRing A.ideal q
        (secondOrderDividedPowers A M N q)) :=
  Classical.choose ((Classical.choose_spec (exists_secondOrderDividedPowers A M N q)).2)

theorem secondOrderDividedPowerHom_eq_baseHom
    (A : DividedPowerRing.{u}) (M N : Type u) [AddCommGroup M]
    [AddCommGroup N] [Module (A : Type u) M] [Module (A : Type u) N]
    (q : M →ₗ[(A : Type u)] M →ₗ[(A : Type u)] N) :
    (secondOrderDividedPowerHom A M N q).hom = SecondOrderThickening.baseHom q :=
  Classical.choose_spec
    ((Classical.choose_spec (exists_secondOrderDividedPowers A M N q)).2)

end
end Formalization.Books.Crystalline.Unit03
