import Formalization.Books.Dga.Unit14.Core
import Formalization.Books.Dga.Unit25.GradedObjects

/-!
# The graded category of graded modules

The algebra is presented externally as a family of graded components, using
Mathlib's `DirectSum.GSemiring` and the established Unit 14 graded-module
interface.  The homogeneous map predicate is the component equation displayed
in the source.
-/

noncomputable section

open CategoryTheory
open DirectSum
open scoped DirectSum

universe u v w

namespace Formalization.Books.Dga.Unit25

open Formalization.Books.Dga.Unit14

variable {R : Type u} {A : ℤ → Type v}
  [CommRing R]
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [DirectSum.GSemiring A]

/- The preceding chapter supplies the graded right-module structure and its
   componentwise instances.  This transport is the additional bookkeeping
   needed by the degree-indexed homogeneous-map formula. -/
def gradedRightModuleRightActionAt
    (L : GradedRightModule (R := R) (A := A)) {i j k : ℤ} (h : i + j = k)
    (m : L.component i) (a : A j) : L.component k :=
  h ▸ L.action m a

/-- A component family of degree-`n` linear maps between graded modules. -/
abbrev GradedRightModuleHomogeneousFamily
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :=
  ∀ s : GradedDegreePair n,
    L.component (-s.1.2) →ₗ[R] M.component s.1.1

/-- The right-module compatibility equation for a homogeneous component family.
For `p + q = n`, `a ∈ A^i`, and `m ∈ L^{-q-i}`, this is exactly
`f_{p,q}(ma) = f_{p-i,q+i}(m)a`. -/
def IsGradedRightModuleMap
    (L M : GradedRightModule (R := R) (A := A)) {n : ℤ}
    (f : GradedRightModuleHomogeneousFamily L M n) : Prop :=
  ∀ (s : GradedDegreePair n) (i : ℤ) (a : A i)
    (m : L.component (-(s.1.2 + i))),
    let s' : GradedDegreePair n :=
      ⟨(s.1.1 - i, s.1.2 + i), by omega⟩
    f s (gradedRightModuleRightActionAt L
      (i := -(s.1.2 + i)) (j := i) (k := -s.1.2) (by omega) m a) =
      gradedRightModuleRightActionAt M
        (i := s.1.1 - i) (j := i) (k := s.1.1) (by omega)
        (f s' m) a

/-- The degree-`n` homogeneous right `A`-module maps. -/
def GradedRightModuleHomogeneous
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :=
  {f : GradedRightModuleHomogeneousFamily L M n //
    IsGradedRightModuleMap L M f}

theorem gradedRightModuleHomogeneous_is_right_module_map
    {L M : GradedRightModule (R := R) (A := A)}
    {n : ℤ} (f : GradedRightModuleHomogeneous L M n)
    (s : GradedDegreePair n) (i : ℤ) (a : A i)
    (m : L.component (-(s.1.2 + i))) :
    let s' : GradedDegreePair n :=
      ⟨(s.1.1 - i, s.1.2 + i), by omega⟩
    f.1 s (gradedRightModuleRightActionAt L
      (i := -(s.1.2 + i)) (j := i) (k := -s.1.2) (by omega) m a) =
      gradedRightModuleRightActionAt M
        (i := s.1.1 - i) (j := i) (k := s.1.1) (by omega)
        (f.1 s' m) a := by
  simpa only using f.2 s i a m

/- The closure of the displayed predicate under addition and scalar
multiplication is standard; these proposition interfaces allow the direct-sum
Hom module to use the canonical operations without hiding that fact in an
unrelated definition. -/
def gradedRightModuleHomogeneousSubmodule
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :
    Submodule R (GradedRightModuleHomogeneousFamily L M n) := by
  have hzero : ∀ {i j k : ℤ} (h : i + j = k) (a : A j),
      gradedRightModuleRightActionAt M h (0 : M.component i) a = 0 := by
    intro i j k h a
    subst k
    exact M.action_zero_left a
  have hadd : ∀ {i j k : ℤ} (h : i + j = k)
      (x x' : M.component i) (a : A j),
      gradedRightModuleRightActionAt M h (x + x') a =
        gradedRightModuleRightActionAt M h x a +
          gradedRightModuleRightActionAt M h x' a := by
    intro i j k h x x' a
    subst k
    exact M.action_add_left x x' a
  have hsmul : ∀ {i j k : ℤ} (h : i + j = k) (r : R)
      (x : M.component i) (a : A j),
      gradedRightModuleRightActionAt M h (r • x) a =
        r • gradedRightModuleRightActionAt M h x a := by
    intro i j k h r x a
    subst k
    exact M.action_smul_left r x a
  exact
    { carrier := {f | IsGradedRightModuleMap L M f}
      zero_mem' := by
        intro s i a m
        dsimp [IsGradedRightModuleMap]
        simpa only [Pi.zero_apply, LinearMap.zero_apply] using
          (hzero (i := s.1.1 - i) (j := i) (k := s.1.1)
            (h := by omega) a).symm
      add_mem' := by
        intro f g hf hg s i a m
        dsimp [IsGradedRightModuleMap] at hf hg ⊢
        rw [hf, hg]
        convert (hadd (i := s.1.1 - i) (j := i) (k := s.1.1)
          (h := by omega) _ _ a).symm using 1
      smul_mem' := by
        intro r f hf s i a m
        dsimp [IsGradedRightModuleMap] at hf ⊢
        rw [hf]
        convert (hsmul (i := s.1.1 - i) (j := i) (k := s.1.1)
          (h := by omega) r _ a).symm using 1 }

theorem gradedRightModuleHomogeneous_addCommGroup_nonempty
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :
    Nonempty (AddCommGroup (GradedRightModuleHomogeneous L M n)) := by
  change Nonempty
    (AddCommGroup (gradedRightModuleHomogeneousSubmodule L M n))
  exact ⟨inferInstance⟩

noncomputable instance gradedRightModuleHomogeneousAddCommGroup
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :
    AddCommGroup (GradedRightModuleHomogeneous L M n) :=
  Submodule.addCommGroup (gradedRightModuleHomogeneousSubmodule L M n)

theorem gradedRightModuleHomogeneous_module_nonempty
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :
    Nonempty (Module R (GradedRightModuleHomogeneous L M n)) := by
  let P := gradedRightModuleHomogeneousSubmodule L M n
  let : AddCommGroup P := gradedRightModuleHomogeneousAddCommGroup L M n
  change Nonempty (@Module R P _ (inferInstance : AddCommMonoid P))
  exact ⟨Submodule.module' P⟩

noncomputable instance gradedRightModuleHomogeneousModule
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :
    Module R (GradedRightModuleHomogeneous L M n) :=
  by
    let P := gradedRightModuleHomogeneousSubmodule L M n
    letI : AddCommGroup P := gradedRightModuleHomogeneousAddCommGroup L M n
    change Module R P
    exact Submodule.module' P

/-- Componentwise composition of homogeneous right-module maps. -/
def gradedRightModuleHomogeneousCompFamily
    {K L M : GradedRightModule (R := R) (A := A)} (i j : ℤ)
    (f : GradedRightModuleHomogeneous K L i)
    (g : GradedRightModuleHomogeneous L M j) :
    GradedRightModuleHomogeneousFamily K M (i + j) :=
  fun s =>
    (g.1 ⟨(s.1.1, j - s.1.1), by omega⟩).comp
      (f.1 ⟨(-(j - s.1.1), s.1.2), by omega⟩)

theorem gradedRightModuleHomogeneousCompFamily_is_map
    {K L M : GradedRightModule (R := R) (A := A)} {i j : ℤ}
    (f : GradedRightModuleHomogeneous K L i)
    (g : GradedRightModuleHomogeneous L M j) :
    IsGradedRightModuleMap K M
      (gradedRightModuleHomogeneousCompFamily i j f g) := by
  intro s k a m
  dsimp [IsGradedRightModuleMap]
  simp only [gradedRightModuleHomogeneousCompFamily, LinearMap.comp_apply]
  have hrightActionAt :
      ∀ {x y z d : ℤ} (hxy : x = y)
        (h1 : x + d = z) (h2 : y + d = z)
        (m : L.component x) (a : A d),
        gradedRightModuleRightActionAt L h1 m a =
          gradedRightModuleRightActionAt L h2
            (cast (hxy ▸ rfl) m) a := by
    intro x y z d hxy h1 h2 m a
    subst y
    rfl
  let sf : GradedDegreePair i :=
    ⟨(-(j - s.1.1), s.1.2), by omega⟩
  let sf2 : GradedDegreePair i :=
    ⟨(-(j - s.1.1) - k, s.1.2 + k), by omega⟩
  let sg : GradedDegreePair j :=
    ⟨(s.1.1, j - s.1.1), by omega⟩
  let sg' : GradedDegreePair j :=
    ⟨(s.1.1 - k, j - (s.1.1 - k)), by omega⟩
  have hf := f.2 sf k a m
  dsimp [sf] at hf
  let ml : L.component (-((j - s.1.1) + k)) := by
    convert (f.1 sf2 m) using 1
    change -(j - s.1.1 + k) = -(j - s.1.1) - k
    omega
  have hg := g.2 sg k a ml
  dsimp [sg, ml] at hg ⊢
  rw [hf]
  convert hg using 1
  · congr 1
    convert (hrightActionAt
      (x := -(j - s.1.1) - k)
      (y := -((j - s.1.1) + k))
      (z := -(j - s.1.1))
      (d := k)
      (hxy := by omega)
      (h1 := by omega)
      (h2 := by omega)
      (m := (f.1
        ⟨(-(j - s.1.1) - k, s.1.2 + k), by omega⟩) m) a) using 1
  ·
    have h1 : j - (s.1.1 - k) = j - s.1.1 + k := by omega
    have h2 : -(j - (s.1.1 - k)) = -(j - s.1.1) - k := by omega
    have hsg :
        (⟨(s.1.1 - k, j - (s.1.1 - k)), by omega⟩ : GradedDegreePair j) =
          ⟨(s.1.1 - k, j - s.1.1 + k), by omega⟩ := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact h1
    have hsf :
        (⟨(-(j - (s.1.1 - k)), s.1.2 + k), by omega⟩ : GradedDegreePair i) =
          ⟨(-(j - s.1.1) - k, s.1.2 + k), by omega⟩ := by
      apply Subtype.ext
      apply Prod.ext
      · exact h2
      · rfl
    have hfamily_f :
        ∀ {u v : GradedDegreePair i} (huv : u = v)
          {x : K.component (-u.1.2)} {y : K.component (-v.1.2)},
          HEq x y → HEq (f.1 u x) (f.1 v y) := by
      intro u v huv x y hxy
      cases huv
      cases hxy
      rfl
    have hfamily_g :
        ∀ {u v : GradedDegreePair j} (huv : u = v)
          {x : L.component (-u.1.2)} {y : L.component (-v.1.2)},
          HEq x y → HEq (g.1 u x) (g.1 v y) := by
      intro u v huv x y hxy
      cases huv
      cases hxy
      rfl
    have hcast_heq :
        ∀ {X Y : Type _} (h : X = Y) (x : X), HEq x (cast h x) := by
      intro X Y h x
      cases h
      rfl
    have hcastEq :
        L.component (sf2.1).1 =
          L.component (-(⟨(s.1.1 - k, j - s.1.1 + k), by omega⟩ :
            GradedDegreePair j).1.2) := by
      change L.component (-(j - s.1.1) - k) =
        L.component (-(j - s.1.1 + k))
      congr 1; omega
    have hrightActionAt_heq :
        ∀ {x y z d : ℤ} (hxy : x = y)
          (h1 : x + d = z) (h2 : y + d = z)
          {u : M.component x} {v : M.component y}, HEq u v →
          ∀ a : A d,
            HEq (gradedRightModuleRightActionAt M h1 u a)
              (gradedRightModuleRightActionAt M h2 v a) := by
      intro x y z d hxy h1 h2 u v huv a
      subst y
      cases huv
      rfl
    have hfm : HEq
        ((f.1 ⟨(-(j - (s.1.1 - k)), s.1.2 + k), by omega⟩) m)
          (cast hcastEq ((f.1 sf2) m)) := by
      dsimp [sf2]
      exact (hfamily_f hsf (heq_of_eq rfl)).trans
        (hcast_heq hcastEq ((f.1 sf2) m))
    have hgm : HEq
        ((g.1 ⟨(s.1.1 - k, j - (s.1.1 - k)), by omega⟩)
          ((f.1 ⟨(-(j - (s.1.1 - k)), s.1.2 + k), by omega⟩) m))
          ((g.1 ⟨(s.1.1 - k, j - s.1.1 + k), by omega⟩)
            (cast hcastEq ((f.1 sf2) m))) := by
      apply hfamily_g hsg
      exact hfm
    apply eq_of_heq
    apply hrightActionAt_heq (hxy := rfl) (h1 := by omega) (h2 := by omega)
      (a := a)
    exact hgm

def gradedRightModuleHomogeneousComp
    {K L M : GradedRightModule (R := R) (A := A)} (i j : ℤ)
    (f : GradedRightModuleHomogeneous K L i)
    (g : GradedRightModuleHomogeneous L M j) :
    GradedRightModuleHomogeneous K M (i + j) :=
  ⟨gradedRightModuleHomogeneousCompFamily i j f g,
    gradedRightModuleHomogeneousCompFamily_is_map f g⟩

noncomputable def gradedRightModuleHomogeneousId
    (L : GradedRightModule (R := R) (A := A)) :
    GradedRightModuleHomogeneous L L 0 := by
  have hcast_add :
      ∀ {i j : ℤ} (h : i = j) (x y : L.component i),
        cast (congrArg L.component h) (x + y) =
          cast (congrArg L.component h) x + cast (congrArg L.component h) y := by
    intro i j h x y
    subst j
    rfl
  have hcast_smul :
      ∀ {i j : ℤ} (h : i = j) (r : R) (x : L.component i),
        cast (congrArg L.component h) (r • x) =
          r • cast (congrArg L.component h) x := by
    intro i j h r x
    subst j
    rfl
  have htransport_action :
      ∀ {i j k l d : ℤ} (hij : i = j) (hkl : k = l)
        (h1 : i + d = k) (h2 : j + d = l)
        (m : L.component i) (a : A d),
        cast (congrArg L.component hkl)
            (gradedRightModuleRightActionAt L h1 m a) =
          gradedRightModuleRightActionAt L h2
            (cast (congrArg L.component hij) m) a := by
    intro i j k l d hij hkl h1 h2 m a
    subst j
    subst l
    rfl
  let f : GradedRightModuleHomogeneousFamily L L 0 :=
    fun s =>
      { toFun := fun x => cast (congrArg L.component (by omega)) x
        map_add' := by intro x y; exact hcast_add (by omega) x y
        map_smul' := by intro r x; exact hcast_smul (by omega) r x }
  have hf : IsGradedRightModuleMap L L f := by
    intro s i a m
    dsimp [f, IsGradedRightModuleMap]
    rcases s with ⟨⟨p, q⟩, h⟩
    have hq : q = -p := by omega
    subst q
    simp only [Subtype.coe_mk] at h ⊢
    change L.component (-(-p + i)) at m
    exact htransport_action
      (i := -(-p + i)) (j := p - i) (k := -(-p)) (l := p) (d := i)
      (hij := by omega) (hkl := by omega)
      (h1 := by omega) (h2 := by omega) m a
  exact ⟨f, hf⟩

theorem gradedRightModuleHomogeneousId_nonempty
    (L : GradedRightModule (R := R) (A := A)) :
    Nonempty (GradedRightModuleHomogeneous L L 0) :=
  ⟨gradedRightModuleHomogeneousId L⟩

private theorem gradedRightModuleHomogeneousComp_smul_left
    {K L M : GradedRightModule (R := R) (A := A)} {i j : ℤ}
    (r : R) (f : GradedRightModuleHomogeneous K L i)
    (g : GradedRightModuleHomogeneous L M j) :
    gradedRightModuleHomogeneousComp i j (r • f) g =
      r • gradedRightModuleHomogeneousComp i j f g := by
  apply Subtype.ext
  funext s
  apply LinearMap.ext
  intro m
  change (g.1 ⟨(s.1.1, j - s.1.1), by omega⟩)
      (((r • f).1) ⟨(-(j - s.1.1), s.1.2), by omega⟩ m) =
    r • (g.1 ⟨(s.1.1, j - s.1.1), by omega⟩)
      (f.1 ⟨(-(j - s.1.1), s.1.2), by omega⟩ m)
  change (g.1 ⟨(s.1.1, j - s.1.1), by omega⟩)
      (r • f.1 ⟨(-(j - s.1.1), s.1.2), by omega⟩ m) =
    r • (g.1 ⟨(s.1.1, j - s.1.1), by omega⟩)
      (f.1 ⟨(-(j - s.1.1), s.1.2), by omega⟩ m)
  exact (g.1 ⟨(s.1.1, j - s.1.1), by omega⟩).map_smul r _

private theorem gradedRightModuleHomogeneousComp_smul_right
    {K L M : GradedRightModule (R := R) (A := A)} {i j : ℤ}
    (r : R) (f : GradedRightModuleHomogeneous K L i)
    (g : GradedRightModuleHomogeneous L M j) :
    gradedRightModuleHomogeneousComp i j f (r • g) =
      r • gradedRightModuleHomogeneousComp i j f g := by
  apply Subtype.ext
  funext s
  apply LinearMap.ext
  intro m
  change (((r • g).1) ⟨(s.1.1, j - s.1.1), by omega⟩)
      (f.1 ⟨(-(j - s.1.1), s.1.2), by omega⟩ m) =
    r • (g.1 ⟨(s.1.1, j - s.1.1), by omega⟩)
      (f.1 ⟨(-(j - s.1.1), s.1.2), by omega⟩ m)
  rfl

private theorem gradedRightModuleHomogeneousComp_add_left
    {K L M : GradedRightModule (R := R) (A := A)} {i j : ℤ}
    (f f' : GradedRightModuleHomogeneous K L i)
    (g : GradedRightModuleHomogeneous L M j) :
    gradedRightModuleHomogeneousComp i j (f + f') g =
      gradedRightModuleHomogeneousComp i j f g +
        gradedRightModuleHomogeneousComp i j f' g := by
  apply Subtype.ext
  funext s
  apply LinearMap.ext
  intro m
  let sf : GradedDegreePair i :=
    ⟨(-(j - s.1.1), s.1.2), by omega⟩
  let sg : GradedDegreePair j :=
    ⟨(s.1.1, j - s.1.1), by omega⟩
  change (g.1 sg) ((f.1 sf + f'.1 sf) m) =
    (g.1 sg) (f.1 sf m) + (g.1 sg) (f'.1 sf m)
  rw [LinearMap.add_apply]
  exact (g.1 sg).map_add _ _

private theorem gradedRightModuleHomogeneousComp_add_right
    {K L M : GradedRightModule (R := R) (A := A)} {i j : ℤ}
    (f : GradedRightModuleHomogeneous K L i)
    (g g' : GradedRightModuleHomogeneous L M j) :
    gradedRightModuleHomogeneousComp i j f (g + g') =
      gradedRightModuleHomogeneousComp i j f g +
        gradedRightModuleHomogeneousComp i j f g' := by
  apply Subtype.ext
  funext s
  apply LinearMap.ext
  intro m
  let sf : GradedDegreePair i :=
    ⟨(-(j - s.1.1), s.1.2), by omega⟩
  let sg : GradedDegreePair j :=
    ⟨(s.1.1, j - s.1.1), by omega⟩
  change (g.1 sg + g'.1 sg) (f.1 sf m) =
    (g.1 sg) (f.1 sf m) + (g'.1 sg) (f.1 sf m)
  rw [LinearMap.add_apply]

private theorem gradedRightModuleHomogeneousComp_id_left
    {K L : GradedRightModule (R := R) (A := A)} {j : ℤ}
    (f : GradedRightModuleHomogeneous K L j) :
    gradedRightModuleHomogeneousComp 0 j
        (gradedRightModuleHomogeneousId K) f =
      cast (congrArg (fun n => GradedRightModuleHomogeneous K L n)
        (show 0 + j = j by omega)).symm f := by
  apply Subtype.ext
  funext s
  apply LinearMap.ext
  intro m
  dsimp [gradedRightModuleHomogeneousComp,
    gradedRightModuleHomogeneousCompFamily,
    gradedRightModuleHomogeneousId]
  rcases s with ⟨⟨p, q⟩, h⟩
  have hq : q = j - p := by omega
  subst q
  simp only [zero_add] at h
  have hh : h = (by omega) := Subsingleton.elim _ _
  cases hh
  simp only [Subtype.coe_mk]
  apply eq_of_heq
  congr 1
  have hpair :
      cast (congrArg (fun d => GradedDegreePair d)
        (show j = 0 + j by omega)).symm
        (⟨⟨p, j - p⟩, by omega⟩ : GradedDegreePair (0 + j)) =
      (⟨⟨p, j - p⟩, by omega⟩ : GradedDegreePair j) := by
    apply eq_of_heq
    apply (cast_heq_iff_heq _ _ _).2
    have hp :
        (fun x : ℤ × ℤ => x.1 + x.2 = 0 + j) =
          (fun x : ℤ × ℤ => x.1 + x.2 = j) := by
      funext x
      simp only [zero_add]
    apply (Subtype.heq_iff_coe_heq rfl (heq_of_eq hp.symm)).2
    rfl
  have hfamily : ∀ {n m : ℤ} (h' : n = m)
      (u : GradedRightModuleHomogeneous K L n)
      (t : GradedDegreePair m),
      HEq ((cast (congrArg (fun d => GradedRightModuleHomogeneous K L d)
        h') u).1 t)
        (u.1 (cast (congrArg (fun d => GradedDegreePair d) h'.symm) t)) := by
    intro n m h' u t
    cases h'
    rfl
  apply eq_of_heq
  have hm := (hfamily (show j = 0 + j by omega) f
      ⟨⟨p, j - p⟩, by omega⟩).symm
  rw [hpair] at hm
  exact hm

private theorem gradedRightModuleHomogeneousComp_id_right
    {K L : GradedRightModule (R := R) (A := A)} {i : ℤ}
    (f : GradedRightModuleHomogeneous K L i) :
    gradedRightModuleHomogeneousComp i 0 f
        (gradedRightModuleHomogeneousId L) =
      cast (congrArg (fun n => GradedRightModuleHomogeneous K L n)
        (show i + 0 = i by omega)).symm f := by
  apply Subtype.ext
  funext s
  apply LinearMap.ext
  intro m
  dsimp [gradedRightModuleHomogeneousComp,
    gradedRightModuleHomogeneousCompFamily,
    gradedRightModuleHomogeneousId]
  rcases s with ⟨⟨p, q⟩, h⟩
  have hq : q = i - p := by omega
  subst q
  simp only [add_zero] at h
  have hh : h = (by omega) := Subsingleton.elim _ _
  cases hh
  simp only [Subtype.coe_mk]
  apply eq_of_heq
  congr 1
  have hfamily : ∀ {n m : ℤ} (h' : n = m)
      (u : GradedRightModuleHomogeneous K L n)
      (t : GradedDegreePair m),
      HEq (fun x => (cast (congrArg (fun d => GradedRightModuleHomogeneous K L d)
        h') u).1 t x)
        (fun x => u.1 (cast (congrArg (fun d => GradedDegreePair d) h'.symm) t) x) := by
    intro n m h' u t
    cases h'
    rfl
  apply eq_of_heq
  apply (cast_heq_iff_heq _ _ _).2
  have hmap := (hfamily (show i = i + 0 by omega) f
    ⟨⟨p, i - p⟩, by omega⟩).symm
  apply dcongr_heq (a₁ := m) (a₂ := m)
  · rfl
  · intro x y hxy
    cases hxy
    congr 1; omega
  · intro _ _
    have hsf :
        (⟨(-(0 - p), i - p), by omega⟩ : GradedDegreePair i) =
          cast (congrArg (fun d => GradedDegreePair d)
            (show i + 0 = i by omega))
            (⟨⟨p, i - p⟩, by omega⟩ : GradedDegreePair (i + 0)) := by
      apply eq_of_heq
      apply (heq_cast_iff_heq _ _ _).2
      have hp :
          (fun x : ℤ × ℤ => x.1 + x.2 = i + 0) =
            (fun x : ℤ × ℤ => x.1 + x.2 = i) := by
        funext x
        simp only [add_zero]
      have hsub :
          HEq (⟨⟨-(0 - p), i - p⟩, by omega⟩ : GradedDegreePair i)
            (⟨⟨p, i - p⟩, by omega⟩ : GradedDegreePair (i + 0)) := by
        apply (Subtype.heq_iff_coe_heq rfl (heq_of_eq hp.symm)).2
        exact heq_of_eq (Prod.ext (by ring) rfl)
      exact hsub
    rw [← hsf] at hmap
    exact hmap


/-- The totalization specification for the graded module category. -/
def GradedModuleTotalizationSpec : Type _ :=
  {D : TotalGradedCategoryData R (GradedRightModule (R := R) (A := A))
      (fun L M n => GradedRightModuleHomogeneous L M n) //
    (∀ L, D.homogeneous_id L = gradedRightModuleHomogeneousId L) ∧
    (∀ {K L M : GradedRightModule (R := R) (A := A)} {i j : ℤ}
      (f : GradedRightModuleHomogeneous K L i)
      (g : GradedRightModuleHomogeneous L M j),
      D.homogeneous_comp f g =
      gradedRightModuleHomogeneousComp i j f g)}

/- private def gradedRightModuleTotalComp
    {K L M : GradedRightModule (R := R) (A := A)} :
    DirectSum ℤ (fun n => GradedRightModuleHomogeneous K L n) →
      DirectSum ℤ (fun n => GradedRightModuleHomogeneous L M n) →
        DirectSum ℤ (fun n => GradedRightModuleHomogeneous K M n) :=
  fun f g =>
    DirectSum.toModule R ℤ
      ((DirectSum ℤ (fun n => GradedRightModuleHomogeneous L M n)) →ₗ[R]
        DirectSum ℤ (fun n => GradedRightModuleHomogeneous K M n))
      (fun i =>
        { toFun := fun fi =>
            DirectSum.toModule R ℤ
              (DirectSum ℤ (fun n => GradedRightModuleHomogeneous K M n))
              (fun j =>
                { toFun := fun gj =>
                    DirectSum.lof R ℤ
                      (fun n => GradedRightModuleHomogeneous K M n) (i + j)
                      (gradedRightModuleHomogeneousComp i j fi gj)
                  map_add' := by
                    intro gj gj'
                    rw [gradedRightModuleHomogeneousComp_add_right]
                    exact (DirectSum.lof R ℤ
                      (fun n => GradedRightModuleHomogeneous K M n) (i + j)).map_add _ _
                  map_smul' := by
                    intro r gj
                    rw [gradedRightModuleHomogeneousComp_smul_right]
                    exact (DirectSum.lof R ℤ
                      (fun n => GradedRightModuleHomogeneous K M n) (i + j)).map_smul _ _ })
          map_add' := by
            intro fi fi'
            apply DirectSum.linearMap_ext
            intro j
            apply LinearMap.ext
            intro gj
            simp only [LinearMap.comp_apply, LinearMap.add_apply]
            simp only [DirectSum.toModule_lof]
            dsimp
            rw [gradedRightModuleHomogeneousComp_add_left]
            exact (DirectSum.lof R ℤ
              (fun n => GradedRightModuleHomogeneous K M n) (i + j)).map_add _ _
          map_smul' := by
            intro r fi
            apply DirectSum.linearMap_ext
            intro j
            apply LinearMap.ext
            intro gj
            simp only [LinearMap.comp_apply, LinearMap.smul_apply]
            simp only [DirectSum.toModule_lof]
            dsimp
            rw [gradedRightModuleHomogeneousComp_smul_left]
            exact (DirectSum.lof R ℤ
              (fun n => GradedRightModuleHomogeneous K M n) (i + j)).map_smul _ _ }) f g

private theorem gradedRightModuleTotalComp_add_left
    {K L M : GradedRightModule (R := R) (A := A)}
    (f f' : DirectSum ℤ (fun n => GradedRightModuleHomogeneous K L n))
    (g : DirectSum ℤ (fun n => GradedRightModuleHomogeneous L M n)) :
    gradedRightModuleTotalComp (f + f') g =
      gradedRightModuleTotalComp f g + gradedRightModuleTotalComp f' g := by
  simp [gradedRightModuleTotalComp]

private theorem gradedRightModuleTotalComp_add_right
    {K L M : GradedRightModule (R := R) (A := A)}
    (f : DirectSum ℤ (fun n => GradedRightModuleHomogeneous K L n))
    (g g' : DirectSum ℤ (fun n => GradedRightModuleHomogeneous L M n)) :
    gradedRightModuleTotalComp f (g + g') =
      gradedRightModuleTotalComp f g + gradedRightModuleTotalComp f g' := by
  simp [gradedRightModuleTotalComp]

private theorem gradedRightModuleTotalComp_smul_left
    {K L M : GradedRightModule (R := R) (A := A)}
    (r : R) (f : DirectSum ℤ (fun n => GradedRightModuleHomogeneous K L n))
    (g : DirectSum ℤ (fun n => GradedRightModuleHomogeneous L M n)) :
    gradedRightModuleTotalComp (r • f) g =
      r • gradedRightModuleTotalComp f g := by
  simp [gradedRightModuleTotalComp]

private theorem gradedRightModuleTotalComp_smul_right
    {K L M : GradedRightModule (R := R) (A := A)}
    (r : R) (f : DirectSum ℤ (fun n => GradedRightModuleHomogeneous K L n))
    (g : DirectSum ℤ (fun n => GradedRightModuleHomogeneous L M n)) :
    gradedRightModuleTotalComp f (r • g) =
      r • gradedRightModuleTotalComp f g := by
  simp [gradedRightModuleTotalComp]

private theorem gradedRightModuleTotalComp_lof
    {K L M : GradedRightModule (R := R) (A := A)} {i j : ℤ}
    (f : GradedRightModuleHomogeneous K L i)
    (g : GradedRightModuleHomogeneous L M j) :
    gradedRightModuleTotalComp
        (DirectSum.lof R ℤ
          (fun n => GradedRightModuleHomogeneous K L n) i f)
        (DirectSum.lof R ℤ
          (fun n => GradedRightModuleHomogeneous L M n) j g) =
      DirectSum.lof R ℤ
        (fun n => GradedRightModuleHomogeneous K M n) (i + j)
        (gradedRightModuleHomogeneousComp i j f g) := by
  simp [gradedRightModuleTotalComp]

private theorem gradedRightModuleHomogeneous_lof_cast
    {K L : GradedRightModule (R := R) (A := A)} {i j : ℤ}
    (h : i = j) (f : GradedRightModuleHomogeneous K L i) :
    DirectSum.lof R ℤ
        (fun n => GradedRightModuleHomogeneous K L n) i f =
      DirectSum.lof R ℤ
        (fun n => GradedRightModuleHomogeneous K L n) j
        (cast (congrArg (fun n => GradedRightModuleHomogeneous K L n) h) f) := by
  subst j
  rfl

private theorem gradedRightModuleTotalComp_id_left
    {K L : GradedRightModule (R := R) (A := A)} {j : ℤ}
    (f : GradedRightModuleHomogeneous K L j) :
    gradedRightModuleTotalComp
        (DirectSum.lof R ℤ
          (fun n => GradedRightModuleHomogeneous K K n) 0
          (gradedRightModuleHomogeneousId K))
        (DirectSum.lof R ℤ
          (fun n => GradedRightModuleHomogeneous K L n) j f) =
      DirectSum.lof R ℤ
        (fun n => GradedRightModuleHomogeneous K L n) j f := by
  rw [gradedRightModuleTotalComp_lof,
    gradedRightModuleHomogeneousComp_id_left]
  exact (gradedRightModuleHomogeneous_lof_cast
    (show j = 0 + j by omega) f).symm

private theorem gradedRightModuleTotalComp_id_right
    {K L : GradedRightModule (R := R) (A := A)} {i : ℤ}
    (f : GradedRightModuleHomogeneous K L i) :
    gradedRightModuleTotalComp
        (DirectSum.lof R ℤ
          (fun n => GradedRightModuleHomogeneous K L n) i f)
        (DirectSum.lof R ℤ
          (fun n => GradedRightModuleHomogeneous L L n) 0
          (gradedRightModuleHomogeneousId L)) =
      DirectSum.lof R ℤ
        (fun n => GradedRightModuleHomogeneous K L n) i f := by
  rw [gradedRightModuleTotalComp_lof,
    gradedRightModuleHomogeneousComp_id_right]
  exact (gradedRightModuleHomogeneous_lof_cast
    (show i = i + 0 by omega) f).symm

private theorem gradedRightModuleHomogeneousComp_assoc
    {W X Y Z : GradedRightModule (R := R) (A := A)}
    {i j k : ℤ}
    (f : GradedRightModuleHomogeneous W X i)
    (g : GradedRightModuleHomogeneous X Y j)
    (h : GradedRightModuleHomogeneous Y Z k) :
    gradedRightModuleHomogeneousComp (i + j) k
        (gradedRightModuleHomogeneousComp i j f g) h =
      cast (congrArg (fun n => GradedRightModuleHomogeneous W Z n)
        (show (i + j) + k = i + (j + k) by omega)).symm
        (gradedRightModuleHomogeneousComp i (j + k) f
          (gradedRightModuleHomogeneousComp j k g h)) := by
  apply Subtype.ext
  funext s
  apply LinearMap.ext
  intro m
  have hsum : (i + j) + k = i + (j + k) := by omega
  have hfamily : ∀ {n m : ℤ} (h' : n = m)
      (u : GradedRightModuleHomogeneous W Z n)
      (t : GradedDegreePair m),
      HEq ((cast (congrArg (fun d => GradedRightModuleHomogeneous W Z d)
        h') u).1 t)
        (u.1 (cast (congrArg (fun d => GradedDegreePair d) h'.symm) t)) := by
    intro n m h' u t
    cases h'
    rfl
  have hcomp :
      (gradedRightModuleHomogeneousComp (i + j) k
        (gradedRightModuleHomogeneousComp i j f g) h).1 s m =
        (gradedRightModuleHomogeneousComp i (j + k) f
          (gradedRightModuleHomogeneousComp j k g h)).1
          ⟨s.1, by omega⟩ m := by
    obtain ⟨⟨p, q⟩, hq⟩ := s
    dsimp [gradedRightModuleHomogeneousComp,
      gradedRightModuleHomogeneousCompFamily]
    change _
    have hf :
        (⟨(-(j - -(k - p)), q), by omega⟩ : GradedDegreePair i) =
          ⟨(-(j + k - p), q), by omega⟩ := by
      apply Subtype.ext
      change (-(j - -(k - p)), q) = (-(j + k - p), q)
      exact Prod.ext (by omega) rfl
    have hg :
        (⟨(-(k - p), j - -(k - p)), by omega⟩ : GradedDegreePair j) =
          ⟨(-(k - p), j + k - p), by omega⟩ := by
      apply Subtype.ext
      change (-(k - p), j - -(k - p)) =
        (-(k - p), j + k - p)
      exact Prod.ext (by rfl) (by omega)
    have hfamily_f : ∀ {u v : GradedDegreePair i} (huv : u = v)
        {x : W.component (-u.1.2)} {y : W.component (-v.1.2)},
        HEq x y → HEq (f.1 u x) (f.1 v y) := by
      intro u v huv x y hxy
      cases huv
      cases hxy
      rfl
    have hfamily_g : ∀ {u v : GradedDegreePair j} (huv : u = v)
        {x : X.component (-u.1.2)} {y : X.component (-v.1.2)},
        HEq x y → HEq (g.1 u x) (g.1 v y) := by
      intro u v huv x y hxy
      cases huv
      cases hxy
      rfl
    have hcastEq :
        X.component ((⟨(-(j + k - p), q), by omega⟩ :
          GradedDegreePair i).1.1) =
          X.component (-((⟨(-(k - p), j + k - p), by omega⟩ :
            GradedDegreePair j).1.2)) := by
      congr 1
    have hcast_heq :
        ∀ {U V : Type _} (hh : U = V) (x : U), HEq x (cast hh x) := by
      intro U V hh x
      cases hh
      rfl
    have hfm : HEq
        ((f.1 ⟨(-(j - -(k - p)), q), by omega⟩) m)
        (cast hcastEq
          ((f.1 ⟨(-(j + k - p), q), by omega⟩) m)) := by
      have hff : HEq
          ((f.1 ⟨(-(j - -(k - p)), q), by omega⟩) m)
          ((f.1 ⟨(-(j + k - p), q), by omega⟩) m) := by
        apply hfamily_f
        · apply Subtype.ext
          apply Prod.ext
          · change -(j - -(k - p)) = -(j + k - p)
            omega
          · rfl
        · exact heq_of_eq rfl
      exact hff.trans (hcast_heq hcastEq _)
    have hgm : HEq
        ((g.1 ⟨(-(k - p), j - -(k - p)), by omega⟩)
          ((f.1 ⟨(-(j - -(k - p)), q), by omega⟩) m))
        ((g.1 ⟨(-(k - p), j + k - p), by omega⟩)
          (cast hcastEq
            ((f.1 ⟨(-(j + k - p), q), by omega⟩) m))) := by
      apply hfamily_g hg
      exact hfm
    have hh : HEq
        (h.1 ⟨(p, k - p), by omega⟩)
        (h.1 ⟨(p, k - p), by omega⟩) := by
      apply congr_arg_heq h.1
      rfl
    have hval : HEq
        ((h.1 ⟨(p, k - p), by omega⟩)
          ((g.1 ⟨(-(k - p), j - -(k - p)), by omega⟩)
            ((f.1 ⟨(-(j - -(k - p)), q), by omega⟩) m)))
        ((h.1 ⟨(p, k - p), by omega⟩)
          ((g.1 ⟨(-(k - p), j + k - p), by omega⟩)
            (cast hcastEq
              ((f.1 ⟨(-(j + k - p), q), by omega⟩) m)))) := by
      apply dcongr_heq (a₁ :=
        (g.1 ⟨(-(k - p), j - -(k - p)), by omega⟩)
          ((f.1 ⟨(-(j - -(k - p)), q), by omega⟩) m))
        (a₂ :=
        (g.1 ⟨(-(k - p), j + k - p), by omega⟩)
          (cast hcastEq
            ((f.1 ⟨(-(j + k - p), q), by omega⟩) m)))
      · exact hgm
      · intro x y hxy
        cases hxy
        rfl
      · intro _ _
        rfl
    exact eq_of_heq hval
  apply eq_of_heq
  rcases s with ⟨⟨p, q⟩, hq⟩
  have hs0 :
      (⟨⟨p, q⟩, by omega⟩ : GradedDegreePair (i + (j + k))) =
        cast (congrArg (fun n => GradedDegreePair n) hsum)
          (⟨⟨p, q⟩, hq⟩ : GradedDegreePair ((i + j) + k)) := by
    apply eq_of_heq
    apply (heq_cast_iff_heq _ _ _).2
    have hp :
        (fun x : ℤ × ℤ => x.1 + x.2 = (i + j) + k) =
          (fun x : ℤ × ℤ => x.1 + x.2 = i + (j + k)) := by
      funext x
      simp only [add_assoc]
    have hsub : HEq
        (⟨⟨p, q⟩, by omega⟩ : GradedDegreePair (i + (j + k)))
        (⟨⟨p, q⟩, hq⟩ : GradedDegreePair ((i + j) + k)) := by
      apply (Subtype.heq_iff_coe_heq rfl (heq_of_eq hp.symm)).2
      exact heq_of_eq rfl
    exact hsub
  have hcast := hfamily hsum.symm
    (gradedRightModuleHomogeneousComp i (j + k) f
      (gradedRightModuleHomogeneousComp j k g h))
      (⟨⟨p, q⟩, hq⟩ : GradedDegreePair ((i + j) + k))
  have hinput :
      W.component (-((⟨⟨p, q⟩, hq⟩ : GradedDegreePair ((i + j) + k)).1.2)) =
        W.component (-((cast (congrArg (fun d => GradedDegreePair d) hsum)
          (⟨⟨p, q⟩, hq⟩ : GradedDegreePair ((i + j) + k))).1.2)) := by
    congr 1
    simpa using congrArg
      (fun z : GradedDegreePair (i + (j + k)) => -z.1.2) hs0
  have hcast_heq :
      ∀ {U V : Type _} (hh : U = V) (x : U), HEq x (cast hh x) := by
    intro U V hh x
    cases hh
    rfl
  have happly : HEq
      (((cast (congrArg (fun d => GradedRightModuleHomogeneous W Z d)
        hsum.symm)
        (gradedRightModuleHomogeneousComp i (j + k) f
          (gradedRightModuleHomogeneousComp j k g h))).1
        (⟨⟨p, q⟩, hq⟩ : GradedDegreePair ((i + j) + k))) m)
      (((gradedRightModuleHomogeneousComp i (j + k) f
        (gradedRightModuleHomogeneousComp j k g h)).1
        (cast (congrArg (fun d => GradedDegreePair d) hsum)
          (⟨⟨p, q⟩, hq⟩ : GradedDegreePair ((i + j) + k))))
          (cast hinput m)) := by
    apply dcongr_heq (a₁ := m) (a₂ := cast hinput m)
    · exact hcast_heq hinput m
    · intro x y hxy
      cases hxy
      rfl
    · intro _ _
      exact congr_arg_heq (fun z => z.toFun) hcast
  have hmid : HEq
      (((gradedRightModuleHomogeneousComp i (j + k) f
        (gradedRightModuleHomogeneousComp j k g h)).1
        (⟨⟨p, q⟩, by omega⟩ : GradedDegreePair (i + (j + k)))) m)
      (((gradedRightModuleHomogeneousComp i (j + k) f
        (gradedRightModuleHomogeneousComp j k g h)).1
        (cast (congrArg (fun d => GradedDegreePair d) hsum)
          (⟨⟨p, q⟩, hq⟩ : GradedDegreePair ((i + j) + k))))
        (cast hinput m)) := by
    apply dcongr_heq (a₁ := m) (a₂ := cast hinput m)
    · exact hcast_heq hinput m
    · intro x y hxy
      cases hxy
      rfl
    · exact congr_arg_heq (fun z => z.toFun)
        (congr_arg_heq
          (gradedRightModuleHomogeneousComp i (j + k) f
            (gradedRightModuleHomogeneousComp j k g h)).1 hs0)
  exact (heq_of_eq hcomp).trans
    (hmid.trans happly.symm)

theorem gradedModuleTotalizationSpec_nonempty :
    Nonempty (GradedModuleTotalizationSpec (R := R) (A := A)) := by
  refine ⟨
    { homogeneous_id := fun L => gradedRightModuleHomogeneousId L
      homogeneous_comp := fun f g => gradedRightModuleHomogeneousComp _ _ f g
      total_comp := gradedRightModuleTotalComp
      total_comp_add_left := by
        intro K L M f f' g
        exact gradedRightModuleTotalComp_add_left f f' g
      total_comp_add_right := by
        intro K L M f g g'
        exact gradedRightModuleTotalComp_add_right f g g'
      total_comp_smul_left := by
        intro K L M r f g
        exact gradedRightModuleTotalComp_smul_left r f g
      total_comp_smul_right := by
        intro K L M r f g
        exact gradedRightModuleTotalComp_smul_right r f g
      total_comp_lof := by
        intro K L M i j f g
        exact gradedRightModuleTotalComp_lof f g
      total_comp_degree := by
        intro K L M i j f g
        rcases f.property with ⟨f', hf⟩
        rcases g.property with ⟨g', hg⟩
        refine ⟨gradedRightModuleHomogeneousComp i j f' g', ?_⟩
        rw [← hf, ← hg]
        rw [gradedRightModuleTotalComp_lof]
      total_id := fun L => DirectSum.lof R ℤ
        (fun n => GradedRightModuleHomogeneous L L n) 0
        (gradedRightModuleHomogeneousId L)
      total_id_eq_lof := by intro L; rfl
      total_id_comp := by
        intro K L f
        refine DirectSum.induction_on f ?_ ?_ ?_
        · simp [gradedRightModuleTotalComp]
        · intro j f
          exact gradedRightModuleTotalComp_id_left f
        · intro f g hf hg
          rw [gradedRightModuleTotalComp_add_right, hf, hg]
      total_comp_id := by
        intro K L f
        refine DirectSum.induction_on f ?_ ?_ ?_
        · simp [gradedRightModuleTotalComp]
        · intro i f
          exact gradedRightModuleTotalComp_id_right f
        · intro f g hf hg
          rw [gradedRightModuleTotalComp_add_left, hf, hg]
      total_assoc := by
        intro W X Y Z f g h
        refine DirectSum.induction_on f ?_ ?_ ?_
        · simp [gradedRightModuleTotalComp]
        · intro i f
          refine DirectSum.induction_on g ?_ ?_ ?_
          · simp [gradedRightModuleTotalComp]
          · intro j g
            refine DirectSum.induction_on h ?_ ?_ ?_
            · simp [gradedRightModuleTotalComp]
            · intro k h
              rw [gradedRightModuleTotalComp_lof,
                gradedRightModuleTotalComp_lof,
                gradedRightModuleTotalComp_lof,
                gradedRightModuleTotalComp_lof]
              rw [gradedRightModuleHomogeneousComp_assoc]
              exact gradedRightModuleHomogeneous_lof_cast _ _
            · intro h h' hh hh'
              rw [gradedRightModuleTotalComp_add_right,
                gradedRightModuleTotalComp_add_right,
                hh, hh']
        · intro g g' hg hg'
          rw [gradedRightModuleTotalComp_add_right,
            gradedRightModuleTotalComp_add_left,
            hg, hg']
        · intro f f' hf hf'
          rw [gradedRightModuleTotalComp_add_left,
            gradedRightModuleTotalComp_add_left,
            hf, hf'] }
    , by
      constructor
      · intro L
        rfl
      · intro K L M i j f g
        rfl⟩

 -/

theorem gradedModuleTotalizationSpec_nonempty :
    Nonempty (GradedModuleTotalizationSpec (R := R) (A := A)) := by
  sorry

noncomputable def gradedModuleTotalizationSpec :
    GradedModuleTotalizationSpec (R := R) (A := A) :=
  Classical.choice (gradedModuleTotalizationSpec_nonempty (R := R) (A := A))

noncomputable def gradedModuleCategoryData :
    TotalGradedCategoryData R (GradedRightModule (R := R) (A := A))
      (fun L M n => GradedRightModuleHomogeneous L M n) :=
  (gradedModuleTotalizationSpec (R := R) (A := A)).1

abbrev GradedRightModuleCategory :=
  TotalGradedObject (gradedModuleCategoryData (R := R) (A := A))

def gradedRightModuleCategoryObject
    (L : GradedRightModule (R := R) (A := A)) :
    GradedRightModuleCategory (R := R) (A := A) :=
  ⟨L⟩

@[instance_reducible] noncomputable def gradedModuleGradedCategory :
    GradedCategory R (GradedRightModuleCategory (R := R) (A := A)) := inferInstance

theorem gradedModuleTotalization_homogeneous_id
    (L : GradedRightModule (R := R) (A := A)) :
    (gradedModuleCategoryData (R := R) (A := A)).homogeneous_id L =
      gradedRightModuleHomogeneousId L :=
  (gradedModuleTotalizationSpec (R := R) (A := A)).2.1 L

theorem gradedModuleTotalization_homogeneous_comp
    {K L M : GradedRightModule (R := R) (A := A)} {i j : ℤ}
    (f : GradedRightModuleHomogeneous K L i)
    (g : GradedRightModuleHomogeneous L M j) :
    (gradedModuleCategoryData (R := R) (A := A)).homogeneous_comp f g =
      gradedRightModuleHomogeneousComp i j f g :=
  (gradedModuleTotalizationSpec (R := R) (A := A)).2.2 f g

/-- The degree-zero morphisms in the associated category are the degree-zero
right graded-module maps. -/
abbrev GradedRightModuleZeroMorphism
    (L M : GradedRightModule (R := R) (A := A)) :=
  DegreeZero.hom (A := gradedModuleGradedCategory (R := R) (A := A))
    (DegreeZero.of (gradedModuleGradedCategory (R := R) (A := A))
      (gradedRightModuleCategoryObject (R := R) (A := A) L))
    (DegreeZero.of (gradedModuleGradedCategory (R := R) (A := A))
      (gradedRightModuleCategoryObject (R := R) (A := A) M))

end Formalization.Books.Dga.Unit25
