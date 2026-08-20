import Formalization.Books.Dga.Unit07.AdmissibleShortExactSequences
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Differential Graded Algebra, Chapter 8: Distinguished triangles

This file records the triangle attached to an admissible short exact
sequence.  The connecting map is represented by the splitting-dependent
data from Chapter 7, while the independence theorem records that changing
those choices only changes the triangle up to isomorphism in the homotopy
category.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Dga.Unit03
open Formalization.Books.Dga.Unit04
open Formalization.Books.Dga.Unit05
open Formalization.Books.Dga.Unit07

universe u

namespace Formalization.Books.Dga.Unit08

/-! ## Triangles in the homotopy category

Mathlib's `Pretriangulated.Triangle` requires a `HasShift` instance on the
ambient category.  The preceding DGA chapters provide the shift functor on
differential graded modules, but not the induced coherent shift structure on
the quotient category, so this source-facing structure records the same data
without introducing a second shift infrastructure.
-/

/-- The quotient category `K(Mod_(A,d))` used by the source. -/
abbrev DgmHomotopyCategory {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :=
  DifferentialGradedModuleHomotopyCategory A

/-- The quotient functor from differential graded modules to the homotopy
category. -/
abbrev DgmHomotopyQuotient {R : Type u} [CommRing R]
    (A : DifferentialGradedAlgebra R) :
    DifferentialGradedModuleCategory A ⥤ DgmHomotopyCategory A :=
  differentialGradedModuleHomotopyQuotient A

/-- A triangle `K ⟶ L ⟶ M ⟶ K[1]` in the DGA homotopy category. -/
structure DgmTriangle {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R} where
  obj₁ : DifferentialGradedModule A
  obj₂ : DifferentialGradedModule A
  obj₃ : DifferentialGradedModule A
  mor₁ : (DgmHomotopyQuotient A).obj obj₁ ⟶
    (DgmHomotopyQuotient A).obj obj₂
  mor₂ : (DgmHomotopyQuotient A).obj obj₂ ⟶
    (DgmHomotopyQuotient A).obj obj₃
  mor₃ : (DgmHomotopyQuotient A).obj obj₃ ⟶
    (DgmHomotopyQuotient A).obj (dgmShift obj₁ (1 : ℤ))

/-- A triangle isomorphism, expressed using differential graded
  representatives of its three component homotopy equivalences in the
  homotopy category.  The commutativity equations live in the quotient
  category, as they do in the source. -/
structure DgmTriangleIsomorphism {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (T U : DgmTriangle (A := A)) where
  e₁ : DifferentialGradedModuleHom T.obj₁ U.obj₁
  e₂ : DifferentialGradedModuleHom T.obj₂ U.obj₂
  e₃ : DifferentialGradedModuleHom T.obj₃ U.obj₃
  e₁_iso : Formalization.Books.Dga.Unit07.DgmHomotopyEquivalence e₁
  e₂_iso : Formalization.Books.Dga.Unit07.DgmHomotopyEquivalence e₂
  e₃_iso : Formalization.Books.Dga.Unit07.DgmHomotopyEquivalence e₃
  comm₁ : T.mor₁ ≫ (DgmHomotopyQuotient A).map e₂ =
    (DgmHomotopyQuotient A).map e₁ ≫ U.mor₁
  comm₂ : T.mor₂ ≫ (DgmHomotopyQuotient A).map e₃ =
    (DgmHomotopyQuotient A).map e₂ ≫ U.mor₂
  comm₃ : T.mor₃ ≫
      (DgmHomotopyQuotient A).map (dgmShiftMap e₁ (1 : ℤ)) =
    (DgmHomotopyQuotient A).map e₃ ≫ U.mor₃

/-- Two source-facing triangles are isomorphic when their displayed
component maps give an isomorphism after passage to the homotopy category.
The quotient-level isomorphism is represented by differential graded module
maps, using the homotopy-equivalence interface from Chapter 7. -/
def DgmTriangleIsomorphic
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (T U : DgmTriangle (A := A)) : Prop :=
  Nonempty (DgmTriangleIsomorphism T U)

/-! ## The connecting map and associated triangle -/

/-- All data needed to choose the connecting morphism supplied by the
admissible-short-exact-sequence lemma.  The two graded maps are splittings;
the kernel-image equality is the exactness condition used by the Chapter 7
connecting-map interface. -/
structure DgmAdmissibleConnectingData {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S) where
  splitting : DgmGradedSplitting S
  kernel_eq_image : DgmGradedKernelEqImage
    splitting.sectionMap splitting.retraction
  connecting : DgmConnectingMapData hS
    splitting.sectionMap splitting.retraction

private theorem dgm_exact_degree
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : S.ShortExact) (n : ℤ) :
    ∀ x : S.X₂.complex.X n, S.g.underlying.f n x = 0 →
      ∃ y : S.X₁.complex.X n, S.f.underlying.f n y = x := by
  have hdegree :=
    (HomologicalComplex.exact_iff_degreewise_exact
      (dgmUnderlyingShortComplex S)).1
      (dgmUnderlyingShortExact S hS).exact n
  rw [ShortComplex.moduleCat_exact_iff] at hdegree
  exact hdegree

private def dgm_shiftedHomotopyHom
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M N : DifferentialGradedModule A}
    (h : DgmGradedHom M N) (n m : ℤ) :
    M.complex.X n ⟶ (dgmShift N (1 : ℤ)).complex.X m :=
  if hnm : n - 1 = m then
    ModuleCat.ofHom (h.component n) ≫ eqToHom (by
      rw [dgmShift_component]
      subst m
      rw [sub_add_cancel])
  else 0

private def dgm_shift_sub
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {M : DifferentialGradedModule A} (n : ℤ)
    (x y : M.complex.X (n + 1)) :
    (dgmShift M (1 : ℤ)).complex.X n :=
  (x : (dgmShift M (1 : ℤ)).complex.X n) -
    (y : (dgmShift M (1 : ℤ)).complex.X n)

@[simp] private theorem dgm_eqToHom_apply_heq
    {R : Type u} [CommRing R]
    {X Y : ModuleCat R} (hEq : X = Y) (x : X) :
    HEq (ModuleCat.Hom.hom (eqToHom hEq) x) x := by
  cases hEq
  rfl

private theorem dgm_neg_negOne_smul_hom_apply
    {R : Type u} [CommRing R]
    {X Y : ModuleCat R} (f : X ⟶ Y) (x : X) :
    -(ModuleCat.Hom.hom ((-1 : ℤ) • f) x) =
      ModuleCat.Hom.hom f x := by
  simp

private theorem dgm_g_surjective_degree
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : S.ShortExact) (n : ℤ) :
    Function.Surjective (S.g.underlying.f n) := by
  have hdegree :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact
      (dgmUnderlyingShortComplex S)).1
      (dgmUnderlyingShortExact S hS) n
  exact ShortComplex.ShortExact.moduleCat_surjective_g hdegree

private theorem dgm_g_section_rightInverse
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    {hS : DgmAdmissibleShortExactSequence S}
    (c : DgmAdmissibleConnectingData hS) (n : ℤ)
    (x : S.X₃.complex.X n) :
    S.g.underlying.f n (c.splitting.sectionMap.component n x) = x := by
  rcases dgm_g_surjective_degree hS.shortExact n x with ⟨y, hy⟩
  rw [← hy, c.splitting.section_rightInverse]

/-- The connecting-map data exists for every admissible short exact
sequence. -/
theorem dgmAdmissibleConnectingData_exists
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S) :
    Nonempty (DgmAdmissibleConnectingData hS) := by
  rcases hS.splitting with ⟨s₀⟩
  have hg_inj : ∀ n : ℤ, Function.Injective (S.g.underlying.f n) := by
    intro n x y hxy
    calc
      x = s₀.sectionMap.component n (S.g.underlying.f n x) :=
        (s₀.section_rightInverse n x).symm
      _ = s₀.sectionMap.component n (S.g.underlying.f n y) := by rw [hxy]
      _ = y := s₀.section_rightInverse n y
  have hf_zero : ∀ (n : ℤ) (x : S.X₁.complex.X n),
      S.f.underlying.f n x = 0 := by
    intro n x
    apply hg_inj n
    have hz : S.g.underlying.f n (S.f.underlying.f n x) = 0 := by
      change S.g.underlying.f n (S.f.underlying.f n x) =
        (0 : DifferentialGradedModuleHom S.X₁ S.X₃).underlying.f n x
      exact congrArg
        (fun q : DifferentialGradedModuleHom S.X₁ S.X₃ =>
          (q.underlying.f n).hom x) S.zero
    rw [hz, map_zero]
  have hK_zero : ∀ (n : ℤ) (x : S.X₁.complex.X n),
      s₀.retraction.component n (S.f.underlying.f n x) = x :=
    s₀.retraction_leftInverse
  have hK_subsingleton : ∀ (n : ℤ) (x : S.X₁.complex.X n), x = 0 := by
    intro n x
    calc
      x = s₀.retraction.component n (S.f.underlying.f n x) :=
        (hK_zero n x).symm
      _ = s₀.retraction.component n 0 := by rw [hf_zero n x]
      _ = 0 := (s₀.retraction.component n).map_zero
  let splitting : DgmGradedSplitting S := s₀
  let s : DgmGradedHom S.X₃ S.X₂ := splitting.sectionMap
  let π : DgmGradedHom S.X₂ S.X₁ := splitting.retraction
  have hs : DgmGradedRightInverse S.g s := splitting.section_rightInverse
  have hπ : DgmGradedLeftInverse S.f π := splitting.retraction_leftInverse
  have hker : DgmGradedKernelEqImage s π := by
    intro n
    ext x
    constructor
    · intro hx
      refine ⟨S.g.underlying.f n x, ?_⟩
      exact hs n x
    · rintro ⟨y, rfl⟩
      exact hK_subsingleton n _
  exact ⟨⟨splitting, hker,
    Classical.choice (dgmConnectingMapData_exists hS s π hs hπ hker)⟩⟩

/-- A chosen connecting-map datum for an admissible short exact sequence. -/
noncomputable def dgmAdmissibleConnectingData
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S) :
    DgmAdmissibleConnectingData hS :=
  Classical.choice (dgmAdmissibleConnectingData_exists hS)

/-- The triangle associated to a chosen splitting and its connecting map. -/
noncomputable def dgmAssociatedTriangleWithData
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S)
    (c : DgmAdmissibleConnectingData hS) : DgmTriangle (A := A) where
  obj₁ := S.X₁
  obj₂ := S.X₂
  obj₃ := S.X₃
  mor₁ := (DgmHomotopyQuotient A).map S.f
  mor₂ := (DgmHomotopyQuotient A).map S.g
  mor₃ := (DgmHomotopyQuotient A).map c.connecting.map

/-- The triangle associated to an admissible short exact sequence, using a
chosen connecting-map datum. -/
noncomputable def dgmAssociatedTriangle
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S) : DgmTriangle (A := A) :=
  dgmAssociatedTriangleWithData hS (dgmAdmissibleConnectingData hS)

private theorem dgm_connecting_retraction_zero
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    {hS : DgmAdmissibleShortExactSequence S}
    (c : DgmAdmissibleConnectingData hS) (n : ℤ)
    (x : S.X₃.complex.X n) :
    c.splitting.retraction.component n
        (c.splitting.sectionMap.component n x) = 0 := by
  have hx : c.splitting.sectionMap.component n x ∈
      Set.range (c.splitting.sectionMap.component n) := Set.mem_range_self x
  rw [← c.kernel_eq_image n] at hx
  exact hx

private theorem dgm_f_retraction_of_g_zero
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    {hS : DgmAdmissibleShortExactSequence S}
    (c : DgmAdmissibleConnectingData hS) (n : ℤ)
    (x : S.X₂.complex.X n) (hx : S.g.underlying.f n x = 0) :
    S.f.underlying.f n (c.splitting.retraction.component n x) = x := by
  rcases dgm_exact_degree hS.shortExact n x hx with ⟨y, hy⟩
  rw [← hy, c.splitting.retraction_leftInverse]

private theorem dgm_splitting_decomposition
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    {hS : DgmAdmissibleShortExactSequence S}
    (c : DgmAdmissibleConnectingData hS) (n : ℤ)
    (x : S.X₂.complex.X n) :
    S.f.underlying.f n (c.splitting.retraction.component n x) +
        c.splitting.sectionMap.component n (S.g.underlying.f n x) = x := by
  have hx₀ : S.g.underlying.f n
      (x - c.splitting.sectionMap.component n (S.g.underlying.f n x)) = 0 := by
    rw [map_sub, c.splitting.section_rightInverse, sub_self]
  have hfx := dgm_f_retraction_of_g_zero c n
    (x - c.splitting.sectionMap.component n (S.g.underlying.f n x)) hx₀
  rw [map_sub, dgm_connecting_retraction_zero c n (S.g.underlying.f n x),
    sub_zero] at hfx
  calc
    S.f.underlying.f n (c.splitting.retraction.component n x) +
          c.splitting.sectionMap.component n (S.g.underlying.f n x) =
        (x - c.splitting.sectionMap.component n (S.g.underlying.f n x)) +
          c.splitting.sectionMap.component n (S.g.underlying.f n x) := by
            rw [hfx]
    _ = x := sub_add_cancel _ _

private def dgm_splitting_difference
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    {hS : DgmAdmissibleShortExactSequence S}
    (c c' : DgmAdmissibleConnectingData hS) : DgmGradedHom S.X₃ S.X₁ where
  component n := c.splitting.retraction.component n |>.comp
    (c'.splitting.sectionMap.component n -
      c.splitting.sectionMap.component n)
  map_action := by
    intro n m x a
    simp only [LinearMap.comp_apply, LinearMap.sub_apply]
    have hs' := c'.splitting.sectionMap.map_action n m x a
    have hs := c.splitting.sectionMap.map_action n m x a
    have hr' := c.splitting.retraction.map_action n m
      (c'.splitting.sectionMap.component n x) a
    have hr := c.splitting.retraction.map_action n m
      (c.splitting.sectionMap.component n x) a
    rw [map_sub, hs', hs, hr', hr, map_sub]
    change
      (S.X₁.homogeneousAction n m).hom
          (c.splitting.retraction.component n
            (c'.splitting.sectionMap.component n x) ⊗ₜ[R] a) -
        (S.X₁.homogeneousAction n m).hom
          (c.splitting.retraction.component n
            (c.splitting.sectionMap.component n x) ⊗ₜ[R] a) =
      (S.X₁.homogeneousAction n m).hom
        ((c.splitting.retraction.component n
            (c'.splitting.sectionMap.component n x) -
          c.splitting.retraction.component n
            (c.splitting.sectionMap.component n x)) ⊗ₜ[R] a)
    rw [TensorProduct.sub_tmul, map_sub]

private theorem dgm_f_splitting_difference
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    {hS : DgmAdmissibleShortExactSequence S}
    (c c' : DgmAdmissibleConnectingData hS) (n : ℤ)
    (x : S.X₃.complex.X n) :
    S.f.underlying.f n ((dgm_splitting_difference c c').component n x) =
      c'.splitting.sectionMap.component n x -
        c.splitting.sectionMap.component n x := by
  have hx₀ : S.g.underlying.f n
      (c'.splitting.sectionMap.component n x -
        c.splitting.sectionMap.component n x) = 0 := by
    rw [map_sub, dgm_g_section_rightInverse c' n x,
      dgm_g_section_rightInverse c n x, sub_self]
  have hfx := dgm_f_retraction_of_g_zero c n
    (c'.splitting.sectionMap.component n x -
      c.splitting.sectionMap.component n x) hx₀
  simpa [dgm_splitting_difference, LinearMap.comp_apply] using hfx

private theorem dgm_splitting_difference_pi'_section
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    {hS : DgmAdmissibleShortExactSequence S}
    (c c' : DgmAdmissibleConnectingData hS) (n : ℤ)
  (x : S.X₃.complex.X n) :
    c'.splitting.retraction.component n
        (c.splitting.sectionMap.component n x) =
      - (dgm_splitting_difference c c').component n x := by
  have hsection := dgm_f_splitting_difference c c' n x
  have hr := c'.splitting.retraction_leftInverse n
    ((dgm_splitting_difference c c').component n x)
  calc
    c'.splitting.retraction.component n
        (c.splitting.sectionMap.component n x) =
      c'.splitting.retraction.component n
          (c'.splitting.sectionMap.component n x -
            S.f.underlying.f n ((dgm_splitting_difference c c').component n x)) := by
              rw [hsection]
              abel
    _ = c'.splitting.retraction.component n
          (c'.splitting.sectionMap.component n x) -
        (dgm_splitting_difference c c').component n x := by
            rw [map_sub, hr]
    _ = - (dgm_splitting_difference c c').component n x := by
      rw [dgm_connecting_retraction_zero c' n x]
      simp

private theorem dgm_splitting_difference_pi_sub
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    {hS : DgmAdmissibleShortExactSequence S}
    (c c' : DgmAdmissibleConnectingData hS) (n : ℤ)
    (x : S.X₂.complex.X n) :
    c'.splitting.retraction.component n x -
        c.splitting.retraction.component n x =
      - (dgm_splitting_difference c c').component n
          (S.g.underlying.f n x) := by
  have hdecomp := dgm_splitting_decomposition c n x
  calc
    c'.splitting.retraction.component n x -
          c.splitting.retraction.component n x =
        c'.splitting.retraction.component n
            (S.f.underlying.f n (c.splitting.retraction.component n x) +
              c.splitting.sectionMap.component n (S.g.underlying.f n x)) -
          c.splitting.retraction.component n
            (S.f.underlying.f n (c.splitting.retraction.component n x) +
              c.splitting.sectionMap.component n (S.g.underlying.f n x)) := by
            rw [hdecomp]
    _ = c'.splitting.retraction.component n
          (c.splitting.sectionMap.component n (S.g.underlying.f n x)) -
        c.splitting.retraction.component n
          (c.splitting.sectionMap.component n (S.g.underlying.f n x)) := by
            rw [map_add, map_add, c'.splitting.retraction_leftInverse,
              c.splitting.retraction_leftInverse]
            simp
    _ = - (dgm_splitting_difference c c').component n
          (S.g.underlying.f n x) := by
            rw [dgm_splitting_difference_pi'_section,
              dgm_connecting_retraction_zero]
            simp

private theorem dgm_connecting_difference_formula
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    {hS : DgmAdmissibleShortExactSequence S}
    (c c' : DgmAdmissibleConnectingData hS) (n : ℤ)
    (x : S.X₃.complex.X n) :
    dgm_shift_sub n
      (c'.connecting.map.underlying.f n x : S.X₁.complex.X (n + 1))
      (c.connecting.map.underlying.f n x : S.X₁.complex.X (n + 1)) =
    dgm_shift_sub n
      ((S.X₁.complex.d n (n + 1)).hom
        ((dgm_splitting_difference c c').component n x))
      ((dgm_splitting_difference c c').component (n + 1)
        ((S.X₃.complex.d n (n + 1)).hom x)) := by
  rw [c'.connecting.component_eq, c.connecting.component_eq]
  dsimp [dgm_shift_sub, dgmConnectingComponent]
  change dgm_shift_sub n
      (((c'.splitting.retraction.component (n + 1)).comp
        ((S.X₂.complex.d n (n + 1)).hom)).comp
          (c'.splitting.sectionMap.component n) x)
      (((c.splitting.retraction.component (n + 1)).comp
        ((S.X₂.complex.d n (n + 1)).hom)).comp
          (c.splitting.sectionMap.component n) x) =
    dgm_shift_sub n
      ((S.X₁.complex.d n (n + 1)).hom
        ((dgm_splitting_difference c c').component n x))
      ((dgm_splitting_difference c c').component (n + 1)
        ((S.X₃.complex.d n (n + 1)).hom x))
  have hπ := dgm_splitting_difference_pi_sub c c' (n + 1)
    ((S.X₂.complex.d n (n + 1)).hom
      (c'.splitting.sectionMap.component n x))
  have hg := congrArg
    (fun q => q (c'.splitting.sectionMap.component n x))
    (S.g.underlying.comm n (n + 1))
  have hf := congrArg
    (fun q => q ((dgm_splitting_difference c c').component n x))
    (S.f.underlying.comm n (n + 1))
  simp only [CategoryTheory.Category.assoc, ModuleCat.comp_apply] at hg hf
  rw [dgm_g_section_rightInverse c' n x] at hg
  let z : S.X₁.complex.X (n + 1) :=
    (dgm_splitting_difference c c').component (n + 1)
      ((S.g.underlying.f (n + 1))
        ((S.X₂.complex.d n (n + 1)).hom
          (c'.splitting.sectionMap.component n x)))
  have hc' :
      (((c'.splitting.retraction.component (n + 1)).comp
        ((S.X₂.complex.d n (n + 1)).hom)).comp
          (c'.splitting.sectionMap.component n)) x =
        c'.splitting.retraction.component (n + 1)
          ((S.X₂.complex.d n (n + 1)).hom
            (c'.splitting.sectionMap.component n x)) := rfl
  have hc :
      (((c.splitting.retraction.component (n + 1)).comp
        ((S.X₂.complex.d n (n + 1)).hom)).comp
          (c.splitting.sectionMap.component n)) x =
        c.splitting.retraction.component (n + 1)
          ((S.X₂.complex.d n (n + 1)).hom
            (c.splitting.sectionMap.component n x)) := rfl
  rw [hc', hc]
  have hπshift :
      dgm_shift_sub n
          (c'.splitting.retraction.component (n + 1)
            ((S.X₂.complex.d n (n + 1)).hom
              (c'.splitting.sectionMap.component n x)))
          (c.splitting.retraction.component (n + 1)
            ((S.X₂.complex.d n (n + 1)).hom
              (c'.splitting.sectionMap.component n x))) =
        - (z : (dgmShift S.X₁ 1).complex.X n) := by
    simpa [dgm_shift_sub] using hπ
  dsimp [dgm_shift_sub] at ⊢
  dsimp [z] at hπshift
  rw [hg]
  simp only [sub_eq_add_neg]
  have htarget :
      - ((dgm_splitting_difference c c').component (n + 1)
          ((S.g.underlying.f (n + 1))
            ((S.X₂.complex.d n (n + 1)).hom
              (c'.splitting.sectionMap.component n x)))) =
        - (z : (dgmShift S.X₁ 1).complex.X n) := by
    rfl
  rw [htarget, ← hπshift]
  have hdf :
      (S.X₁.complex.d n (n + 1)).hom
          ((dgm_splitting_difference c c').component n x) =
        c.splitting.retraction.component (n + 1)
          ((S.X₂.complex.d n (n + 1)).hom
            (S.f.underlying.f n
              ((dgm_splitting_difference c c').component n x))) := by
    calc
      (S.X₁.complex.d n (n + 1)).hom
          ((dgm_splitting_difference c c').component n x) =
        c.splitting.retraction.component (n + 1)
          (S.f.underlying.f (n + 1)
            ((S.X₁.complex.d n (n + 1)).hom
              ((dgm_splitting_difference c c').component n x))) :=
        (c.splitting.retraction_leftInverse (n + 1) _).symm
      _ = c.splitting.retraction.component (n + 1)
          ((S.X₂.complex.d n (n + 1)).hom
            (S.f.underlying.f n
              ((dgm_splitting_difference c c').component n x))) := by
        exact congrArg (c.splitting.retraction.component (n + 1)) hf.symm
  rw [hdf, dgm_f_splitting_difference c c' n x]
  dsimp [dgm_shift_sub] at ⊢
  simp only [map_sub]
  abel

/-- The connecting maps obtained from two choices in the admissible
short-exact-sequence construction are homotopic.  This is the map-level
assertion used to identify the two associated triangles in the homotopy
category. -/
theorem dgmConnectingMap_homotopic_of_choices
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S)
    (c c' : DgmAdmissibleConnectingData hS) :
    DifferentialGradedModuleHomotopic c.connecting.map c'.connecting.map := by
  let h := dgm_splitting_difference c' c
  let hneg : DgmGradedHom S.X₃ S.X₁ := {
    component n := -(h.component n)
    map_action := by
      intro n m x a
      simp only [LinearMap.neg_apply]
      rw [h.map_action]
      change
        -(S.X₁.homogeneousAction n m).hom
            (h.component n x ⊗ₜ[R] a) =
          (S.X₁.homogeneousAction n m).hom
            (-(h.component n x) ⊗ₜ[R] a)
      simp [TensorProduct.neg_tmul]
  }
  refine ⟨{
    homotopy := {
      hom := fun n m => dgm_shiftedHomotopyHom hneg n m
      zero := by
        intro n m hnm
        by_cases heq : n - 1 = m
        · exfalso
          apply hnm
          dsimp [ComplexShape.up, ComplexShape.up']
          omega
        · simp [dgm_shiftedHomotopyHom, heq]
          rfl
      comm := by
        intro n
        ext x
        rw [dNext_eq _ (by
          dsimp [ComplexShape.up, ComplexShape.up'])]
        rw [prevD_eq _ (j' := n - 1) (by
          dsimp [ComplexShape.up, ComplexShape.up']
          omega)]
        have hformula := dgm_connecting_difference_formula c' c n x
        have hmapx :
            (ModuleCat.Hom.hom
              (S.X₃.complex.d n (n + 1) ≫
                  dgm_shiftedHomotopyHom hneg (n + 1) n +
                dgm_shiftedHomotopyHom hneg n (n - 1) ≫
                    (dgmShift S.X₁ (1 : ℤ)).complex.d (n - 1) n +
                c'.connecting.map.underlying.f n)) x =
              dgm_shift_sub n
                ((S.X₁.complex.d n (n + 1)).hom
                  (h.component n x))
                (h.component (n + 1)
                  ((S.X₃.complex.d n (n + 1)).hom x)) +
              (c'.connecting.map.underlying.f n) x := by
          change
            dgm_shiftedHomotopyHom hneg (n + 1) n
                ((S.X₃.complex.d n (n + 1)).hom x) +
              (dgmShift S.X₁ (1 : ℤ)).complex.d (n - 1) n
                (dgm_shiftedHomotopyHom hneg n (n - 1) x) +
              (c'.connecting.map.underlying.f n) x =
            dgm_shift_sub n
              ((S.X₁.complex.d n (n + 1)).hom
                (h.component n x))
              (h.component (n + 1)
                ((S.X₃.complex.d n (n + 1)).hom x)) +
            (c'.connecting.map.underlying.f n) x
          let p₀ : S.X₁.complex.X n =
              (dgmShift S.X₁ 1).complex.X (n - 1) := by
            rw [dgmShift_component]
            rw [sub_add_cancel]
          have hq₀ : HEq
              (ModuleCat.Hom.hom (eqToHom p₀) (h.component n x))
              (h.component n x) :=
            dgm_eqToHom_apply_heq p₀ (h.component n x)
          have hpair : HEq
              (⟨n - 1 + 1,
                ModuleCat.Hom.hom (eqToHom p₀) (h.component n x)⟩ :
                Σ k : ℤ, S.X₁.complex.X k)
              (⟨n, h.component n x⟩ :
                Σ k : ℤ, S.X₁.complex.X k) := by
            apply heq_of_eq
            apply Sigma.ext (sub_add_cancel n 1)
            exact hq₀
          have hdiff := congr_arg_heq
            (fun z : Σ k : ℤ, S.X₁.complex.X k =>
              (S.X₁.complex.d z.1 (n + 1)).hom z.2)
            (eq_of_heq hpair)
          have hdiff' : HEq
              ((S.X₁.complex.d (n - 1 + 1) (n + 1)).hom
                (ModuleCat.Hom.hom (eqToHom p₀) (h.component n x)))
              ((S.X₁.complex.d n (n + 1)).hom
                (h.component n x)) := by
            exact hdiff
          have hB : HEq
              (((dgmShift S.X₁ (1 : ℤ)).complex.d (n - 1) n).hom
                ((dgm_shiftedHomotopyHom hneg n (n - 1)).hom x))
              ((S.X₁.complex.d n (n + 1)).hom
                (h.component n x)) := by
            convert hdiff' using 1 <;>
              simp [dgm_shiftedHomotopyHom, hneg, ModuleCat.comp_apply,
                LinearMap.comp_apply, map_neg] <;>
              try rfl
            all_goals
              change
                (ModuleCat.Hom.hom ((dgmShift S.X₁ 1).complex.d (n - 1) n))
                    (-(ModuleCat.Hom.hom (eqToHom p₀) (h.component n x))) = _
              rw [map_neg]
              have hD := congrArg (fun f =>
                  ModuleCat.Hom.hom f
                    (ModuleCat.Hom.hom (eqToHom p₀) (h.component n x)))
                (dgmShift_differential S.X₁ 1 (n - 1) n)
              have hDneg := congrArg (fun z => -z) hD
              have hscalar :
                  -(ModuleCat.Hom.hom
                    ((-1 : ℤ) • S.X₁.complex.d (n - 1 + 1) (n + 1)))
                      (ModuleCat.Hom.hom (eqToHom p₀) (h.component n x)) =
                    (ModuleCat.Hom.hom
                      (S.X₁.complex.d (n - 1 + 1) (n + 1)))
                      (ModuleCat.Hom.hom (eqToHom p₀) (h.component n x)) := by
                let z : Σ k : ℤ, S.X₁.complex.X k :=
                  ⟨n - 1 + 1, ModuleCat.Hom.hom (eqToHom p₀) (h.component n x)⟩
                have hz := dgm_neg_negOne_smul_hom_apply
                  (S.X₁.complex.d z.1 (n + 1)) z.2
                simpa [z] using hz
              rw [Int.negOnePow_one] at hDneg
              exact hDneg.trans hscalar
          have hB_eq := eq_of_heq hB
          rw [hB_eq]
          simp [dgm_shiftedHomotopyHom, hneg, dgm_shift_sub,
            dgmShift_differential, sub_add_eq_add_sub, neg_one_smul]
          simp only [sub_eq_add_neg]
          ac_rfl
        have hformula' := (sub_eq_iff_eq_add).mp hformula
        rw [hmapx]
        change (ConcreteCategory.hom (c.connecting.map.underlying.f n)) x = _
        simpa only [h] using hformula'
    }
    map_action := by
      intro n m x a
      simp [dgm_shiftedHomotopyHom, hneg, LinearMap.comp_apply]
      let p₁ : S.X₁.complex.X (n + m) =
          (dgmShift S.X₁ 1).complex.X ((n + m) - 1) := by
        rw [dgmShift_component]
        rw [sub_add_cancel]
      let p₀ : S.X₁.complex.X n =
          (dgmShift S.X₁ 1).complex.X (n - 1) := by
        rw [dgmShift_component]
        rw [sub_add_cancel]
      change HEq
        (-(ModuleCat.Hom.hom (eqToHom p₁)
          (h.component (n + m)
            (DifferentialGradedModule.actionOnHomogeneous S.X₃ n m x a))))
        ((dgmShift S.X₁ 1).actionOnHomogeneous (n - 1) m
          (-(ModuleCat.Hom.hom (eqToHom p₀) (h.component n x))) a)
      rw [h.map_action]
      rw [dgmShift_action_preserves_underlying_action]
      simp only [transportComponent, dgmShift_component]
      have hq₁ : HEq
          (-(ModuleCat.Hom.hom (eqToHom p₁)
            (S.X₁.actionOnHomogeneous n m (h.component n x) a)))
          (-(S.X₁.actionOnHomogeneous n m (h.component n x) a)) := by
        have hmap :
            -(ModuleCat.Hom.hom (eqToHom p₁)
                (S.X₁.actionOnHomogeneous n m (h.component n x) a)) =
              ModuleCat.Hom.hom (eqToHom p₁)
                (-(S.X₁.actionOnHomogeneous n m (h.component n x) a)) := by
          exact ((ModuleCat.Hom.hom (eqToHom p₁)).map_neg _).symm
        exact (heq_of_eq hmap).trans
          (dgm_eqToHom_apply_heq p₁
            (-(S.X₁.actionOnHomogeneous n m (h.component n x) a)))
      have hq₀ : HEq
          (-(ModuleCat.Hom.hom (eqToHom p₀) (h.component n x)))
          (-(h.component n x)) := by
        have hmap :
            -(ModuleCat.Hom.hom (eqToHom p₀) (h.component n x)) =
              ModuleCat.Hom.hom (eqToHom p₀) (-(h.component n x)) := by
          exact ((ModuleCat.Hom.hom (eqToHom p₀)).map_neg _).symm
        exact (heq_of_eq hmap).trans
          (dgm_eqToHom_apply_heq p₀ (-(h.component n x)))
      have hsign :
          -(S.X₁.actionOnHomogeneous n m (h.component n x) a) =
            S.X₁.actionOnHomogeneous n m (-(h.component n x)) a := by
        change
          -(S.X₁.homogeneousAction n m).hom
              (h.component n x ⊗ₜ[R] a) =
            (S.X₁.homogeneousAction n m).hom
              (-(h.component n x) ⊗ₜ[R] a)
        simp [TensorProduct.neg_tmul]
      have hpair : HEq
          (⟨n - 1 + 1, -(ModuleCat.Hom.hom (eqToHom p₀)
            (h.component n x))⟩ :
              Σ k : ℤ, S.X₁.complex.X k)
          (⟨n, -(h.component n x)⟩ :
              Σ k : ℤ, S.X₁.complex.X k) := by
        apply heq_of_eq
        apply Sigma.ext (sub_add_cancel n 1)
        exact hq₀
      have hact := congr_arg_heq
        (fun z : Σ k : ℤ, S.X₁.complex.X k =>
          S.X₁.actionOnHomogeneous z.1 m z.2 a) (eq_of_heq hpair)
      have hchain := hq₁.trans ((heq_of_eq hsign).trans hact.symm)
      simpa [transportComponent, dgmShift_component] using hchain
  }⟩

/-- Changing the splittings in the connecting-map construction changes the
associated triangle by the canonical isomorphism whose three component maps
are identities on `S.X₁`, `S.X₂`, and `S.X₃`. -/
theorem dgmAssociatedTriangle_independent_of_splittings
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    {S : ShortComplex (DifferentialGradedModuleCategory A)}
    (hS : DgmAdmissibleShortExactSequence S)
    (c c' : DgmAdmissibleConnectingData hS) :
    ∃ e : DgmTriangleIsomorphism
        (dgmAssociatedTriangleWithData hS c)
        (dgmAssociatedTriangleWithData hS c'),
      e.e₁ = (𝟙 S.X₁ : DifferentialGradedModuleHom S.X₁ S.X₁) ∧
      e.e₂ = (𝟙 S.X₂ : DifferentialGradedModuleHom S.X₂ S.X₂) ∧
      e.e₃ = (𝟙 S.X₃ : DifferentialGradedModuleHom S.X₃ S.X₃) := by
  have hconn := dgmConnectingMap_homotopic_of_choices hS c c'
  have hquot := CategoryTheory.Quotient.sound
    (differentialGradedModuleHomotopyRelation A) hconn
  have hshift : dgmShiftMap (𝟙 S.X₁) (1 : ℤ) =
      (𝟙 (dgmShift S.X₁ (1 : ℤ)) :
        DifferentialGradedModuleHom (dgmShift S.X₁ (1 : ℤ))
          (dgmShift S.X₁ (1 : ℤ))) := by
    ext n x
    rfl
  let e : DgmTriangleIsomorphism
      (dgmAssociatedTriangleWithData hS c)
      (dgmAssociatedTriangleWithData hS c') := {
    e₁ := 𝟙 S.X₁
    e₂ := 𝟙 S.X₂
    e₃ := 𝟙 S.X₃
    e₁_iso := by
      refine ⟨𝟙 S.X₁, ?_, ?_⟩
      · change DifferentialGradedModuleHomotopic
          (differentialGradedModuleHomComp (𝟙 S.X₁) (𝟙 S.X₁))
          (𝟙 S.X₁)
        simpa only [differentialGradedModuleHomComp,
          Category.comp_id, Category.id_comp] using
          (show DifferentialGradedModuleHomotopic
            (𝟙 S.X₁) (𝟙 S.X₁) from
            ⟨DifferentialGradedModuleHomotopy.refl (𝟙 S.X₁)⟩)
      · change DifferentialGradedModuleHomotopic
          (differentialGradedModuleHomComp (𝟙 S.X₁) (𝟙 S.X₁))
          (𝟙 S.X₁)
        simpa only [differentialGradedModuleHomComp,
          Category.comp_id, Category.id_comp] using
          (show DifferentialGradedModuleHomotopic
            (𝟙 S.X₁) (𝟙 S.X₁) from
            ⟨DifferentialGradedModuleHomotopy.refl (𝟙 S.X₁)⟩)
    e₂_iso := by
      refine ⟨𝟙 S.X₂, ?_, ?_⟩
      · change DifferentialGradedModuleHomotopic
          (differentialGradedModuleHomComp (𝟙 S.X₂) (𝟙 S.X₂))
          (𝟙 S.X₂)
        simpa only [differentialGradedModuleHomComp,
          Category.comp_id, Category.id_comp] using
          (show DifferentialGradedModuleHomotopic
            (𝟙 S.X₂) (𝟙 S.X₂) from
            ⟨DifferentialGradedModuleHomotopy.refl (𝟙 S.X₂)⟩)
      · change DifferentialGradedModuleHomotopic
          (differentialGradedModuleHomComp (𝟙 S.X₂) (𝟙 S.X₂))
          (𝟙 S.X₂)
        simpa only [differentialGradedModuleHomComp,
          Category.comp_id, Category.id_comp] using
          (show DifferentialGradedModuleHomotopic
            (𝟙 S.X₂) (𝟙 S.X₂) from
            ⟨DifferentialGradedModuleHomotopy.refl (𝟙 S.X₂)⟩)
    e₃_iso := by
      refine ⟨𝟙 S.X₃, ?_, ?_⟩
      · change DifferentialGradedModuleHomotopic
          (differentialGradedModuleHomComp (𝟙 S.X₃) (𝟙 S.X₃))
          (𝟙 S.X₃)
        simpa only [differentialGradedModuleHomComp,
          Category.comp_id, Category.id_comp] using
          (show DifferentialGradedModuleHomotopic
            (𝟙 S.X₃) (𝟙 S.X₃) from
            ⟨DifferentialGradedModuleHomotopy.refl (𝟙 S.X₃)⟩)
      · change DifferentialGradedModuleHomotopic
          (differentialGradedModuleHomComp (𝟙 S.X₃) (𝟙 S.X₃))
          (𝟙 S.X₃)
        simpa only [differentialGradedModuleHomComp,
          Category.comp_id, Category.id_comp] using
          (show DifferentialGradedModuleHomotopic
            (𝟙 S.X₃) (𝟙 S.X₃) from
            ⟨DifferentialGradedModuleHomotopy.refl (𝟙 S.X₃)⟩)
    comm₁ := by
      simp [dgmAssociatedTriangleWithData]
    comm₂ := by
      simp [dgmAssociatedTriangleWithData]
    comm₃ := by
      simp only [dgmAssociatedTriangleWithData, hshift]
      have hm₁ := (DgmHomotopyQuotient A).map_id
        (dgmShift S.X₁ 1)
      have hm₃ := (DgmHomotopyQuotient A).map_id S.X₃
      rw [hm₁, Category.comp_id, hm₃, Category.id_comp]
      exact hquot
  }
  refine ⟨e, ?_, ?_, ?_⟩
  · change (𝟙 S.X₁ : DifferentialGradedModuleHom S.X₁ S.X₁) = 𝟙 S.X₁
    rfl
  · change (𝟙 S.X₂ : DifferentialGradedModuleHom S.X₂ S.X₂) = 𝟙 S.X₂
    rfl
  · change (𝟙 S.X₃ : DifferentialGradedModuleHom S.X₃ S.X₃) = 𝟙 S.X₃
    rfl

/-! ## Distinguished triangles -/

/-- A triangle is distinguished when it is isomorphic in the homotopy
category to one associated to an admissible short exact sequence. -/
def DgmDistinguishedTriangle
    {R : Type u} [CommRing R]
    {A : DifferentialGradedAlgebra R}
    (T : DgmTriangle (A := A)) : Prop :=
  ∃ (S : ShortComplex (DifferentialGradedModuleCategory A))
    (hS : DgmAdmissibleShortExactSequence S),
    DgmTriangleIsomorphic (dgmAssociatedTriangle hS) T

end Formalization.Books.Dga.Unit08
