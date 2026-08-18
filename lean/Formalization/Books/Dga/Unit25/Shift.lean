import Formalization.Books.Dga.Unit25.GradedModules
import Mathlib.CategoryTheory.Equivalence

/-!
# Shift functors and graded totalization

The first structure below is the source's strict collection of shifts on an
`R`-linear category.  The totalized category uses `Hom(X,Y[n])` as its
degree-`n` homogeneous Hom type.  The construction theorem is left as a
proposition proof, while all interfaces and the resulting definitions are
explicit.
-/

noncomputable section

open CategoryTheory
open DirectSum
open scoped DirectSum

universe u v w

namespace Formalization.Books.Dga.Unit25

/-- A strict family of `R`-linear shift functors. -/
structure LinearShiftFamily (R : Type u) (C : Type v)
    [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C] where
  shift : ℤ → C ⥤ C
  additive : ∀ n, Functor.Additive (shift n)
  linear : ∀ n, Functor.Linear R (shift n)
  shift_comp : ∀ n m, shift m ⋙ shift n = shift (n + m)
  shift_zero : shift 0 = 𝟭 C

namespace LinearShiftFamily

variable {R : Type u} {C : Type v}
  [CommRing R] [Category.{w} C] [Preadditive C]
  [CategoryTheory.Linear R C]
  (S : LinearShiftFamily R C)

/-- The degree-`n` homogeneous Hom type in the shift totalization. -/
abbrev homogeneous (X Y : C) (n : ℤ) : Type w :=
  (X ⟶ (S.shift n).obj Y)

instance homogeneousAddCommGroup (X Y : C) (n : ℤ) :
    AddCommGroup (homogeneous S X Y n) := inferInstance

instance homogeneousModule (X Y : C) (n : ℤ) :
    Module R (homogeneous S X Y n) := inferInstance

/-- The componentwise composition in the shift totalization. -/
def homogeneousComp {X Y Z : C} (i j : ℤ)
    (f : homogeneous S X Y i) (g : homogeneous S Y Z j) :
    homogeneous S X Z (i + j) :=
  f ≫ (S.shift i).map g ≫
    eqToHom (congrArg (fun F : C ⥤ C => F.obj Z) (S.shift_comp i j))

/-- The degree-zero identity in the shift totalization. -/
def homogeneousId (X : C) : homogeneous S X X 0 :=
  eqToHom (congrArg (fun F : C ⥤ C => F.obj X) S.shift_zero).symm

theorem homogeneousComp_component {X Y Z : C} {i j : ℤ}
    (f : homogeneous S X Y i) (g : homogeneous S Y Z j) :
    homogeneousComp S i j f g =
      f ≫ (S.shift i).map g ≫
        eqToHom (congrArg (fun F : C ⥤ C => F.obj Z) (S.shift_comp i j)) :=
  rfl

/-- The totalization specification for a shift family. -/
def TotalizationSpec : Type _ :=
  {D : TotalGradedCategoryData R C (homogeneous S) //
    (∀ X, D.homogeneous_id X = homogeneousId S X) ∧
    (∀ {X Y Z : C} {i j : ℤ}
      (f : homogeneous S X Y i) (g : homogeneous S Y Z j),
      D.homogeneous_comp f g = homogeneousComp S i j f g)}

theorem totalizationSpec_nonempty : Nonempty (TotalizationSpec S) := by
  have hid_comp :
      ∀ {X Y : C} {j : ℤ} (f : homogeneous S X Y j),
        cast (congrArg (homogeneous S X Y) (show (0 : ℤ) + j = j by omega))
            (homogeneousComp S (0 : ℤ) j (homogeneousId S X) f) = f := by
    intro X Y j f
    dsimp [homogeneousComp, homogeneousId]
    rw [Functor.congr_hom S.shift_zero f]
    apply eq_of_heq
    simp only [Functor.id_map, Category.id_comp, Category.comp_id,
      Category.assoc, eqToHom_trans, eqToHom_refl, cast_heq_iff_heq,
      eqToHom_comp_heq_iff, heq_comp_eqToHom_iff]
    exact comp_eqToHom_heq f _
  have hcomp_id :
      ∀ {X Y : C} {i : ℤ} (f : homogeneous S X Y i),
        cast (congrArg (homogeneous S X Y) (show i + (0 : ℤ) = i by omega))
            (homogeneousComp S i (0 : ℤ) f (homogeneousId S Y)) = f := by
    intro X Y i f
    dsimp [homogeneousComp, homogeneousId]
    apply eq_of_heq
    simp only [eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id, Category.id_comp, cast_heq_iff_heq,
      eqToHom_comp_heq_iff, heq_comp_eqToHom_iff]
    exact comp_eqToHom_heq f _
  let total_comp :
      ∀ {X Y Z : C},
        DirectSum ℤ (fun n => homogeneous S X Y n) →
          DirectSum ℤ (fun n => homogeneous S Y Z n) →
            DirectSum ℤ (fun n => homogeneous S X Z n) :=
    fun {X Y Z} f g =>
      DirectSum.toModule R ℤ
        ((DirectSum ℤ (fun n => homogeneous S Y Z n)) →ₗ[R]
          DirectSum ℤ (fun n => homogeneous S X Z n))
        (fun i =>
          { toFun := fun fi =>
              DirectSum.toModule R ℤ
                (DirectSum ℤ (fun n => homogeneous S X Z n))
                (fun j =>
                  { toFun := fun gj =>
                      DirectSum.lof R ℤ
                        (fun n => homogeneous S X Z n) (i + j)
                        (homogeneousComp S i j fi gj)
                    map_add' := by
                      intro gj gj'
                      letI : Functor.Additive (S.shift i) := S.additive i
                      have hcomp := congrArg
                        (DirectSum.lof R ℤ
                          (fun n => homogeneous S X Z n) (i + j))
                        (show homogeneousComp S i j fi (gj + gj') =
                            homogeneousComp S i j fi gj +
                              homogeneousComp S i j fi gj' by
                          simp [homogeneousComp])
                      rw [hcomp]
                      exact (DirectSum.lof R ℤ
                        (fun n => homogeneous S X Z n) (i + j)).map_add _ _
                    map_smul' := by
                      intro r gj
                      letI : Functor.Additive (S.shift i) := S.additive i
                      letI : Functor.Linear R (S.shift i) := S.linear i
                      have hcomp := congrArg
                        (DirectSum.lof R ℤ
                          (fun n => homogeneous S X Z n) (i + j))
                        (show homogeneousComp S i j fi (r • gj) =
                            r • homogeneousComp S i j fi gj by
                          simp [homogeneousComp])
                      rw [hcomp]
                      exact (DirectSum.lof R ℤ
                        (fun n => homogeneous S X Z n) (i + j)).map_smul _ _ })
            map_add' := by
              intro fi fi'
              letI : Functor.Additive (S.shift i) := S.additive i
              apply DirectSum.linearMap_ext
              intro j
              apply LinearMap.ext
              intro gj'
              simp only [LinearMap.comp_apply, LinearMap.add_apply]
              simp only [DirectSum.toModule_lof]
              dsimp
              have hcomp := congrArg
                (DirectSum.lof R ℤ
                  (fun n => homogeneous S X Z n) (i + j))
                (show homogeneousComp S i j (fi + fi') gj' =
                    homogeneousComp S i j fi gj' +
                      homogeneousComp S i j fi' gj' by
                  simp [homogeneousComp])
              rw [hcomp]
              exact (DirectSum.lof R ℤ
                (fun n => homogeneous S X Z n) (i + j)).map_add _ _
            map_smul' := by
              intro r fi
              letI : Functor.Additive (S.shift i) := S.additive i
              letI : Functor.Linear R (S.shift i) := S.linear i
              apply DirectSum.linearMap_ext
              intro j
              apply LinearMap.ext
              intro gj'
              simp only [LinearMap.comp_apply, LinearMap.smul_apply]
              simp only [DirectSum.toModule_lof]
              dsimp
              have hcomp := congrArg
                (DirectSum.lof R ℤ
                  (fun n => homogeneous S X Z n) (i + j))
                (show homogeneousComp S i j (r • fi) gj' =
                    r • homogeneousComp S i j fi gj' by
                  simp [homogeneousComp])
              rw [hcomp]
              exact (DirectSum.lof R ℤ
                (fun n => homogeneous S X Z n) (i + j)).map_smul _ _ }) f g
  have hcomp_add_left :
      ∀ {X Y Z : C}
        (f f' : DirectSum ℤ (fun n => homogeneous S X Y n))
        (g : DirectSum ℤ (fun n => homogeneous S Y Z n)),
        total_comp (f + f') g = total_comp f g + total_comp f' g := by
    intro X Y Z f f' g
    simp [total_comp]
  have hcomp_add_right :
      ∀ {X Y Z : C}
        (f : DirectSum ℤ (fun n => homogeneous S X Y n))
        (g g' : DirectSum ℤ (fun n => homogeneous S Y Z n)),
        total_comp f (g + g') = total_comp f g + total_comp f g' := by
    intro X Y Z f g g'
    simp [total_comp]
  have hcomp_smul_left :
      ∀ {X Y Z : C} (r : R)
        (f : DirectSum ℤ (fun n => homogeneous S X Y n))
        (g : DirectSum ℤ (fun n => homogeneous S Y Z n)),
        total_comp (r • f) g = r • total_comp f g := by
    intro X Y Z r f g
    simp [total_comp]
  have hcomp_smul_right :
      ∀ {X Y Z : C} (r : R)
        (f : DirectSum ℤ (fun n => homogeneous S X Y n))
        (g : DirectSum ℤ (fun n => homogeneous S Y Z n)),
        total_comp f (r • g) = r • total_comp f g := by
    intro X Y Z r f g
    simp [total_comp]
  have hcomp_lof :
      ∀ {X Y Z : C} {i j : ℤ}
        (f : homogeneous S X Y i) (g : homogeneous S Y Z j),
        total_comp
            (DirectSum.lof R ℤ (fun n => homogeneous S X Y n) i f)
            (DirectSum.lof R ℤ (fun n => homogeneous S Y Z n) j g) =
          DirectSum.lof R ℤ (fun n => homogeneous S X Z n) (i + j)
            (homogeneousComp S i j f g) := by
    intro X Y Z i j f g
    simp [total_comp]
  have hid_lof :
      ∀ {X Y : C} {j : ℤ} (f : homogeneous S X Y j),
        total_comp
            (DirectSum.lof R ℤ (fun n => homogeneous S X X n) 0
              (homogeneousId S X))
            (DirectSum.lof R ℤ (fun n => homogeneous S X Y n) j f) =
          DirectSum.lof R ℤ (fun n => homogeneous S X Y n) j f := by
    intro X Y j f
    rw [hcomp_lof]
    rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
    apply (DFinsupp.single_eq_single_iff _ _ _ _).2
    left
    constructor
    · omega
    · exact (cast_heq_iff_heq
        (congrArg (homogeneous S X Y) (show (0 : ℤ) + j = j by omega)) _ _).mp
        (heq_of_eq (hid_comp f))
  have hcomp_id_lof :
      ∀ {X Y : C} {i : ℤ} (f : homogeneous S X Y i),
        total_comp
            (DirectSum.lof R ℤ (fun n => homogeneous S X Y n) i f)
            (DirectSum.lof R ℤ (fun n => homogeneous S Y Y n) 0
              (homogeneousId S Y)) =
          DirectSum.lof R ℤ (fun n => homogeneous S X Y n) i f := by
    intro X Y i f
    rw [hcomp_lof]
    rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
    apply (DFinsupp.single_eq_single_iff _ _ _ _).2
    left
    constructor
    · omega
    · exact (cast_heq_iff_heq
        (congrArg (homogeneous S X Y) (show i + (0 : ℤ) = i by omega)) _ _).mp
        (heq_of_eq (hcomp_id f))
  have hcomp_assoc :
      ∀ {W X Y Z : C} {i j k : ℤ}
        (f : homogeneous S W X i) (g : homogeneous S X Y j)
        (h : homogeneous S Y Z k),
        cast (congrArg (homogeneous S W Z)
          (show (i + j) + k = i + (j + k) by omega))
            (homogeneousComp S (i + j) k
              (homogeneousComp S i j f g) h) =
          homogeneousComp S i (j + k) f
            (homogeneousComp S j k g h) := by
    intro W X Y Z i j k f g h
    dsimp [homogeneousComp]
    simp only [Functor.map_comp]
    rw [← Functor.comp_map]
    rw [Functor.congr_hom (S.shift_comp i j) h]
    apply eq_of_heq
    simp only [cast_heq_iff_heq, Category.assoc, eqToHom_trans,
      eqToHom_refl, Category.comp_id, Category.id_comp,
      eqToHom_comp_heq_iff, heq_comp_eqToHom_iff,
      comp_eqToHom_heq_iff, eqToHom_map, eqToHom_trans_assoc,
      Functor.comp_obj, Functor.comp_map]
    congr 1
    · exact congrArg (fun n : ℤ => (S.shift n).obj Z) (by omega)
    · congr 1
      · exact congrArg (fun n : ℤ => (S.shift n).obj Z) (by omega)
      · congr 1
        · exact congrArg (fun n : ℤ => (S.shift n).obj Z) (by omega)
        · exact (comp_eqToHom_heq _ _).trans
            (comp_eqToHom_heq _ _).symm
  refine ⟨
    { homogeneous_id := fun X => homogeneousId S X
      homogeneous_comp := fun f g => homogeneousComp S _ _ f g
      total_comp := total_comp
      total_comp_add_left := by
        intro X Y Z f f' g
        exact hcomp_add_left f f' g
      total_comp_add_right := by
        intro X Y Z f g g'
        exact hcomp_add_right f g g'
      total_comp_smul_left := by
        intro X Y Z r f g
        exact hcomp_smul_left r f g
      total_comp_smul_right := by
        intro X Y Z r f g
        exact hcomp_smul_right r f g
      total_comp_lof := by
        intro X Y Z i j f g
        exact hcomp_lof f g
      total_comp_degree := by
        intro X Y Z i j f g
        rcases f.property with ⟨f', hf⟩
        rcases g.property with ⟨g', hg⟩
        refine ⟨homogeneousComp S i j f' g', ?_⟩
        rw [← hf, ← hg]
        simp [total_comp]
      total_id := fun X => DirectSum.lof R ℤ
        (fun n => homogeneous S X X n) 0 (homogeneousId S X)
      total_id_eq_lof := by intro X; rfl
      total_id_comp := by
        intro X Y f
        refine DirectSum.induction_on f ?_ ?_ ?_
        · simp [total_comp]
        · intro j g
          exact hid_lof g
        · intro f g hf hg
          rw [hcomp_add_right, hf, hg]
      total_comp_id := by
        intro X Y f
        refine DirectSum.induction_on f ?_ ?_ ?_
        · simp [total_comp]
        · intro i f
          exact hcomp_id_lof f
        · intro f g hf hg
          rw [hcomp_add_left, hf, hg]
      total_assoc := by
        intro W X Y Z f g h
        refine DirectSum.induction_on f ?_ ?_ ?_
        · simp [total_comp]
        · intro i f
          refine DirectSum.induction_on g ?_ ?_ ?_
          · simp [total_comp]
          · intro j g
            refine DirectSum.induction_on h ?_ ?_ ?_
            · simp [total_comp]
            · intro k h
              change total_comp
                  (total_comp
                    (DirectSum.lof R ℤ
                      (fun n => homogeneous S W X n) i f)
                    (DirectSum.lof R ℤ
                      (fun n => homogeneous S X Y n) j g))
                  (DirectSum.lof R ℤ
                    (fun n => homogeneous S Y Z n) k h) =
                total_comp
                  (DirectSum.lof R ℤ
                    (fun n => homogeneous S W X n) i f)
                  (total_comp
                    (DirectSum.lof R ℤ
                      (fun n => homogeneous S X Y n) j g)
                    (DirectSum.lof R ℤ
                      (fun n => homogeneous S Y Z n) k h))
              rw [hcomp_lof, hcomp_lof, hcomp_lof, hcomp_lof]
              rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
              apply (DFinsupp.single_eq_single_iff _ _ _ _).2
              left
              constructor
              · omega
              · exact (cast_heq_iff_heq
                  (congrArg (homogeneous S W Z)
                    (show (i + j) + k = i + (j + k) by omega)) _ _).mp
                  (heq_of_eq (hcomp_assoc f g h))
            · intro h h' hh hh'
              change total_comp
                  (total_comp
                    (DirectSum.lof R ℤ
                      (fun n => homogeneous S W X n) i f)
                    (DirectSum.lof R ℤ
                      (fun n => homogeneous S X Y n) j g))
                  (h + h') =
                total_comp
                  (DirectSum.lof R ℤ
                    (fun n => homogeneous S W X n) i f)
                  (total_comp
                    (DirectSum.lof R ℤ
                      (fun n => homogeneous S X Y n) j g)
                    (h + h'))
              have hh0 :
                  total_comp
                      (total_comp
                        (DirectSum.lof R ℤ
                          (fun n => homogeneous S W X n) i f)
                        (DirectSum.lof R ℤ
                          (fun n => homogeneous S X Y n) j g)) h =
                    total_comp
                      (DirectSum.lof R ℤ
                        (fun n => homogeneous S W X n) i f)
                      (total_comp
                        (DirectSum.lof R ℤ
                          (fun n => homogeneous S X Y n) j g) h) := by
                simpa only [DirectSum.lof_eq_of] using hh
              have hh0' :
                  total_comp
                      (total_comp
                        (DirectSum.lof R ℤ
                          (fun n => homogeneous S W X n) i f)
                        (DirectSum.lof R ℤ
                          (fun n => homogeneous S X Y n) j g)) h' =
                    total_comp
                      (DirectSum.lof R ℤ
                        (fun n => homogeneous S W X n) i f)
                      (total_comp
                        (DirectSum.lof R ℤ
                          (fun n => homogeneous S X Y n) j g) h') := by
                simpa only [DirectSum.lof_eq_of] using hh'
              calc
                total_comp
                    (total_comp
                      (DirectSum.lof R ℤ
                          (fun n => homogeneous S W X n) i f)
                      (DirectSum.lof R ℤ
                          (fun n => homogeneous S X Y n) j g))
                    (h + h') =
                    total_comp
                        (total_comp
                          (DirectSum.lof R ℤ
                              (fun n => homogeneous S W X n) i f)
                          (DirectSum.lof R ℤ
                              (fun n => homogeneous S X Y n) j g)) h +
                      total_comp
                        (total_comp
                          (DirectSum.lof R ℤ
                              (fun n => homogeneous S W X n) i f)
                          (DirectSum.lof R ℤ
                              (fun n => homogeneous S X Y n) j g)) h' :=
                  hcomp_add_right _ _ _
                _ =
                    total_comp
                      (DirectSum.lof R ℤ
                        (fun n => homogeneous S W X n) i f)
                        (total_comp
                          (DirectSum.lof R ℤ
                            (fun n => homogeneous S X Y n) j g) h) +
                      total_comp
                      (DirectSum.lof R ℤ
                        (fun n => homogeneous S W X n) i f)
                        (total_comp
                          (DirectSum.lof R ℤ
                            (fun n => homogeneous S X Y n) j g) h') := by
                  rw [hh0, hh0']
                _ = total_comp
                      (DirectSum.lof R ℤ
                        (fun n => homogeneous S W X n) i f)
                    (total_comp
                      (DirectSum.lof R ℤ
                          (fun n => homogeneous S X Y n) j g) h +
                      total_comp
                        (DirectSum.lof R ℤ
                            (fun n => homogeneous S X Y n) j g) h') := by
                  symm
                  apply hcomp_add_right
                _ = total_comp
                      (DirectSum.lof R ℤ
                        (fun n => homogeneous S W X n) i f)
                    (total_comp
                      (DirectSum.lof R ℤ
                        (fun n => homogeneous S X Y n) j g)
                      (h + h')) := by
                  exact congrArg
                    (fun x => total_comp
                        (DirectSum.lof R ℤ
                          (fun n => homogeneous S W X n) i f) x)
                    (hcomp_add_right
                      (DirectSum.lof R ℤ
                        (fun n => homogeneous S X Y n) j g) h h').symm
          · intro g g' hg hg'
            change total_comp
                (total_comp
                  (DirectSum.lof R ℤ
                    (fun n => homogeneous S W X n) i f) (g + g')) h =
              total_comp
                (DirectSum.lof R ℤ
                  (fun n => homogeneous S W X n) i f)
                (total_comp (g + g') h)
            have hg0 :
                total_comp
                    (total_comp
                      (DirectSum.lof R ℤ
                        (fun n => homogeneous S W X n) i f) g) h =
                  total_comp
                    (DirectSum.lof R ℤ
                      (fun n => homogeneous S W X n) i f)
                    (total_comp g h) := by
              simpa only [DirectSum.lof_eq_of] using hg
            have hg0' :
                total_comp
                    (total_comp
                      (DirectSum.lof R ℤ
                        (fun n => homogeneous S W X n) i f) g') h =
                  total_comp
                    (DirectSum.lof R ℤ
                      (fun n => homogeneous S W X n) i f)
                    (total_comp g' h) := by
              simpa only [DirectSum.lof_eq_of] using hg'
            calc
              total_comp
                  (total_comp
                    (DirectSum.lof R ℤ
                      (fun n => homogeneous S W X n) i f) (g + g')) h =
                  total_comp
                      (total_comp
                        (DirectSum.lof R ℤ
                          (fun n => homogeneous S W X n) i f) g +
                        total_comp
                        (DirectSum.lof R ℤ
                            (fun n => homogeneous S W X n) i f) g') h := by
                    rw [hcomp_add_right, hcomp_add_left]
              _ = total_comp
                    (total_comp
                      (DirectSum.lof R ℤ
                        (fun n => homogeneous S W X n) i f) g) h +
                    total_comp
                      (total_comp
                        (DirectSum.lof R ℤ
                          (fun n => homogeneous S W X n) i f) g') h := by
                    apply hcomp_add_left
              _ = total_comp
                    (DirectSum.lof R ℤ
                      (fun n => homogeneous S W X n) i f)
                    (total_comp g h) +
                    total_comp
                      (DirectSum.lof R ℤ
                        (fun n => homogeneous S W X n) i f)
                      (total_comp g' h) := by
                    rw [hg0, hg0']
              _ = total_comp
                    (DirectSum.lof R ℤ
                      (fun n => homogeneous S W X n) i f)
                    (total_comp g h + total_comp g' h) := by
                    symm
                    apply hcomp_add_right
              _ = total_comp
                    (DirectSum.lof R ℤ
                      (fun n => homogeneous S W X n) i f)
                    (total_comp (g + g') h) := by
                    rw [hcomp_add_left]
        · intro f f' hf hf'
          calc
            total_comp (total_comp (f + f') g) h =
                total_comp (total_comp f g + total_comp f' g) h := by
              rw [hcomp_add_left]
            _ = total_comp (total_comp f g) h +
                total_comp (total_comp f' g) h := by
              apply hcomp_add_left
            _ = total_comp f (total_comp g h) +
                total_comp f' (total_comp g h) := by
              rw [hf, hf']
            _ = total_comp (f + f') (total_comp g h) := by
              symm
              apply hcomp_add_left }
    , by
      constructor
      · intro X
        rfl
      · intro X Y Z i j f g
        rfl⟩

noncomputable def totalizationSpec : TotalizationSpec S :=
  Classical.choice (totalizationSpec_nonempty S)

noncomputable def categoryData : TotalGradedCategoryData R C (homogeneous S) :=
  (totalizationSpec S).1

abbrev GradedCategory := TotalGradedObject (categoryData S)

def categoryObject (X : C) : GradedCategory S := ⟨X⟩

@[instance_reducible] noncomputable def gradedCategory :
    Formalization.Books.Dga.Unit25.GradedCategory R (GradedCategory S) :=
  inferInstance

theorem categoryData_homogeneous_id (X : C) :
    (categoryData S).homogeneous_id X = homogeneousId S X :=
  (totalizationSpec S).2.1 X

theorem categoryData_homogeneous_comp {X Y Z : C} {i j : ℤ}
    (f : homogeneous S X Y i) (g : homogeneous S Y Z j) :
    (categoryData S).homogeneous_comp f g = homogeneousComp S i j f g :=
  (totalizationSpec S).2.2 f g

theorem degree_zero_recovers :
    Nonempty (DegreeZero (gradedCategory S) ≌ C) := by
  let homTo {A Y : C}
      (f : directSumComponent R
        (fun n => homogeneous S A Y n) 0) :
      homogeneous S A Y 0 :=
    Classical.choose f.2
  let homFrom {A Y : C}
      (f : homogeneous S A Y 0) :
      directSumComponent R
        (fun n => homogeneous S A Y n) 0 :=
      ⟨DirectSum.lof R ℤ
        (fun n => homogeneous S A Y n) 0 f,
      ⟨f, rfl⟩⟩
  let totalComp0 {A Y E : C}
      (f : directSumComponent R
        (fun n => homogeneous S A Y n) 0)
      (g : directSumComponent R
        (fun n => homogeneous S Y E n) 0) :
      directSumComponent R
        (fun n => homogeneous S A E n) 0 :=
    ⟨(categoryData S).total_comp
        (f : DirectSum ℤ (fun n => homogeneous S A Y n))
        (g : DirectSum ℤ (fun n => homogeneous S Y E n)),
      (categoryData S).total_comp_degree f g⟩
  have homFrom_homTo {A Y : C}
      (f : directSumComponent R
        (fun n => homogeneous S A Y n) 0) :
      homFrom (homTo f) = f := by
    apply Subtype.ext
    exact Classical.choose_spec f.2
  have homTo_homFrom {A Y : C}
      (f : homogeneous S A Y 0) :
      homTo (homFrom f) = f := by
    apply DirectSum.of_injective 0
    simpa [DirectSum.lof_eq_of, homTo, homFrom] using
      (Classical.choose_spec (homFrom f).2)
  have homFrom_injective {A Y : C} :
      Function.Injective (homFrom (A := A) (Y := Y)) := by
    intro f g h
    exact (homTo_homFrom f).symm.trans
      ((congrArg (homTo (A := A) (Y := Y)) h).trans
        (homTo_homFrom g))
  let familyToMap {A Y : C}
      (f : homogeneous S A Y 0) : A ⟶ Y :=
    f ≫ eqToHom
      (congrArg (fun F : C ⥤ C => F.obj Y) S.shift_zero)
  let mapToFamily {A Y : C}
      (f : A ⟶ Y) : homogeneous S A Y 0 :=
    f ≫ eqToHom
      (congrArg (fun F : C ⥤ C => F.obj Y) S.shift_zero).symm
  have mapToFamily_familyToMap
      {A Y : C} (f : homogeneous S A Y 0) :
      mapToFamily (familyToMap f) = f := by
    dsimp [mapToFamily, familyToMap]
    simp
  have familyToMap_mapToFamily
      {A Y : C} (f : A ⟶ Y) :
      familyToMap (mapToFamily f) = f := by
    dsimp [mapToFamily, familyToMap]
    simp
  have hzero_id (A : C) :
      mapToFamily (𝟙 A) = homogeneousId S A := by
    dsimp [mapToFamily, homogeneousId]
    simp
  have hzero_comp {A Y E : C}
      (f : homogeneous S A Y 0)
      (g : homogeneous S Y E 0) :
      homogeneousComp S 0 0 f g =
        mapToFamily (familyToMap f ≫ familyToMap g) := by
    dsimp [homogeneousComp, mapToFamily, familyToMap]
    rw [Functor.congr_hom S.shift_zero g]
    simp only [Functor.id_map, Category.assoc, Category.comp_id,
      Category.id_comp, eqToHom_trans, eqToHom_refl]
  have hsource_id (A : C) :
      homFrom (mapToFamily (𝟙 A)) =
        𝟙 (DegreeZero.of (gradedCategory S) (categoryObject S A)) := by
    apply Subtype.ext
    change DirectSum.lof R ℤ
        (fun n => homogeneous S A A n) 0
        (mapToFamily (𝟙 A)) =
      (categoryData S).total_id A
    rw [hzero_id, (categoryData S).total_id_eq_lof,
      categoryData_homogeneous_id]
  have hhom_comp {A Y E : C}
      (f : directSumComponent R
        (fun n => homogeneous S A Y n) 0)
      (g : directSumComponent R
        (fun n => homogeneous S Y E n) 0) :
      homTo (totalComp0 f g) =
        homogeneousComp S 0 0 (homTo f) (homTo g) := by
    apply homFrom_injective
    rw [homFrom_homTo]
    rw [← homFrom_homTo f, ← homFrom_homTo g]
    simp only [homTo_homFrom]
    dsimp [totalComp0, homFrom]
    apply Subtype.ext
    change (categoryData S).total_comp
        (DirectSum.lof R ℤ
          (fun n => homogeneous S A Y n) 0 (homTo f))
        (DirectSum.lof R ℤ
          (fun n => homogeneous S Y E n) 0 (homTo g)) =
      DirectSum.lof R ℤ
        (fun n => homogeneous S A E n) 0
        (homogeneousComp S 0 0 (homTo f) (homTo g))
    rw [(categoryData S).total_comp_lof]
    congr 1
    exact categoryData_homogeneous_comp S _ _
  have hsource_comp {A Y E : C}
      (f : A ⟶ Y) (g : Y ⟶ E) :
      homFrom (mapToFamily (f ≫ g)) =
        totalComp0 (homFrom (mapToFamily f))
          (homFrom (mapToFamily g)) := by
    apply Subtype.ext
    change DirectSum.lof R ℤ
        (fun n => homogeneous S A E n) 0
        (mapToFamily (f ≫ g)) =
      (categoryData S).total_comp _ _
    rw [(categoryData S).total_comp_lof]
    congr 1
    rw [categoryData_homogeneous_comp S]
    rw [hzero_comp, familyToMap_mapToFamily,
      familyToMap_mapToFamily]
  let F :
      DegreeZero (gradedCategory S) ⥤ C :=
    { obj := fun X =>
          (DegreeZero.obj (gradedCategory S) X).underlying
      map := fun {X Y} f =>
        familyToMap
          (A := (DegreeZero.obj (gradedCategory S) X).underlying)
          (Y := (DegreeZero.obj (gradedCategory S) Y).underlying)
          (homTo f)
      map_id := by
        intro X
        cases X with
        | up X =>
          cases X with
          | mk A =>
            change familyToMap (homTo
                (𝟙 (DegreeZero.of (gradedCategory S)
                  (categoryObject S A)))) = 𝟙 A
            rw [← hsource_id A]
            change familyToMap
              (homTo (homFrom (mapToFamily (𝟙 A)))) = 𝟙 A
            calc
              familyToMap
                  (homTo (homFrom (mapToFamily (𝟙 A)))) =
                familyToMap (mapToFamily (𝟙 A)) := by
                  congr 1
                  exact homTo_homFrom (mapToFamily (𝟙 A))
              _ = 𝟙 A := familyToMap_mapToFamily (𝟙 A)
      map_comp := by
        intro X Y Z f g
        cases X with
        | up X =>
          cases X with
          | mk A =>
            cases Y with
            | up Y =>
              cases Y with
              | mk Y =>
                cases Z with
                | up Z =>
                  cases Z with
                  | mk E =>
                    change directSumComponent R
                      (fun n => homogeneous S A Y n) 0 at f
                    change directSumComponent R
                      (fun n => homogeneous S Y E n) 0 at g
                    change familyToMap (homTo (totalComp0 f g)) =
                      familyToMap (homTo f) ≫ familyToMap (homTo g)
                    rw [hhom_comp, hzero_comp,
                      familyToMap_mapToFamily] }
  let G :
      C ⥤ DegreeZero (gradedCategory S) :=
    { obj := fun A => DegreeZero.of (gradedCategory S)
          (categoryObject S A)
      map := fun f => homFrom (mapToFamily f)
      map_id := by
        intro A
        exact hsource_id A
      map_comp := by
        intro A Y E f g
        change homFrom (mapToFamily (f ≫ g)) =
            totalComp0 (homFrom (mapToFamily f))
              (homFrom (mapToFamily g))
        exact hsource_comp f g }
  let unitIso (X : DegreeZero (gradedCategory S)) :
      X ≅ (F ⋙ G).obj X := by
    cases X with
    | up X =>
      cases X with
      | mk A =>
        exact Iso.refl _
  let counitIso (A : C) :
      (G ⋙ F).obj A ≅ A := by
    exact Iso.refl _
  let unitNatIso :
      𝟭 (DegreeZero (gradedCategory S)) ≅ F ⋙ G := by
    refine NatIso.ofComponents
        (fun X => unitIso X)
        (fun {X Y} f => ?_)
    cases X with
    | up X =>
      cases X with
      | mk A =>
        cases Y with
        | up Y =>
          cases Y with
          | mk Y =>
            change directSumComponent R
              (fun n => homogeneous S A Y n) 0 at f
            dsimp [unitIso, F, G]
            apply Subtype.ext
            change (categoryData S).total_comp f.1
                ((categoryData S).total_id Y) =
              (categoryData S).total_comp
                ((categoryData S).total_id A)
                ((homFrom (mapToFamily (familyToMap (homTo f))) :
                  directSumComponent R
                    (fun n => homogeneous S A Y n) 0) :
                  DirectSum ℤ (fun n => homogeneous S A Y n))
            rw [(categoryData S).total_comp_id,
              (categoryData S).total_id_comp]
            calc
              (f : DirectSum ℤ (fun n => homogeneous S A Y n)) =
                  (homFrom (homTo f) : DirectSum ℤ
                    (fun n => homogeneous S A Y n)) :=
                congrArg Subtype.val (homFrom_homTo f).symm
              _ = (homFrom (mapToFamily (familyToMap (homTo f))) :
                  DirectSum ℤ (fun n => homogeneous S A Y n)) := by
                rw [mapToFamily_familyToMap]
  let counitNatIso :
      G ⋙ F ≅ 𝟭 C := by
    refine NatIso.ofComponents (fun A => counitIso A) (fun {X Y} f => ?_)
    simp [counitIso]
    dsimp [F, G]
    change familyToMap (homTo (homFrom (mapToFamily f))) ≫ 𝟙 Y =
      𝟙 X ≫ f
    rw [Category.comp_id, Category.id_comp, homTo_homFrom,
      familyToMap_mapToFamily]
  refine ⟨⟨F, G, unitNatIso, counitNatIso, ?_⟩⟩
  · intro X
    cases X with
    | up X =>
      cases X with
      | mk A =>
        change F.map (unitIso (DegreeZero.of
          (gradedCategory S) (categoryObject S A))).hom ≫
          (counitIso A).hom = 𝟙 A
        have hunit :
            (unitIso (DegreeZero.of (gradedCategory S)
              (categoryObject S A))).hom =
              𝟙 (DegreeZero.of (gradedCategory S)
                (categoryObject S A)) := by
          dsimp [unitIso]
          rfl
        have hmap :
            F.map (unitIso (DegreeZero.of (gradedCategory S)
              (categoryObject S A))).hom = 𝟙 A := by
          rw [hunit]
          exact F.map_id _
        have hcount : (counitIso A).hom = 𝟙 A := by
          rfl
        rw [hmap, hcount]
        dsimp [F]
        exact Category.id_comp (𝟙 A)

noncomputable def degree_zero_equivalence : DegreeZero (gradedCategory S) ≌ C :=
  Classical.choice (degree_zero_recovers S)

end LinearShiftFamily

/-! ## Graded-module shift isomorphisms -/

/-- A degree shift isomorphism between two internal graded modules.  The
`total` equivalence is compatible with the component equivalences, so this
records an isomorphism of graded modules rather than only a family of
set-theoretic bijections. -/
structure GradedModuleShiftIso (R : Type u)
    {M N : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (G : GradedModuleData R M ℤ) (H : GradedModuleData R N ℤ)
    (n : ℤ) where
  total : M ≃ₗ[R] N
  component : ∀ i, G.component i ≃ₗ[R] H.component (i + n)
  component_coe : ∀ i (x : G.component i),
    total (x : M) = (component i x : N)

/-- A graded category equipped with strict shifts and the Hom-shift
isomorphisms required in the source remark. -/
structure GradedShiftFamily (R : Type u) (C : Type v)
    [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C] [GradedCategory R C] where
  shift : ℤ → C ⥤ C
  graded : ∀ n, GradedFunctor R (shift n)
  shift_comp : ∀ n m, shift m ⋙ shift n = shift (n + m)
  shift_zero : shift 0 = 𝟭 C
  hom_shift : ∀ (X Y : C) (n : ℤ),
    GradedModuleShiftIso R
      (GradedCategory.hom X ((shift n).obj Y))
      (GradedCategory.hom X Y) n
  hom_shift_comp_pre : ∀ {X Y Z : C} (n : ℤ)
    (f : X ⟶ Y) (g : Y ⟶ (shift n).obj Z),
    (hom_shift X Z n).total (f ≫ g) =
      f ≫ (hom_shift Y Z n).total g
  hom_shift_comp_post : ∀ {X Y Z : C} (n : ℤ)
    (f : X ⟶ (shift n).obj Y) (g : Y ⟶ Z),
    (hom_shift X Z n).total (f ≫ (shift n).map g) =
      (hom_shift X Y n).total f ≫ g

namespace GradedFunctor

variable {R : Type u} {C D : Type v}
  [CommRing R] [Category.{w} C] [Category.{w} D]
  [Preadditive C] [Preadditive D]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  [GradedCategory R C] [GradedCategory R D]
  {F : C ⥤ D} (G : GradedFunctor R F)

/-- Restrict a graded functor to the degree-zero categories. -/
def degreeZero : DegreeZero (inferInstance : GradedCategory R C) ⥤
    DegreeZero (inferInstance : GradedCategory R D) where
  obj X := DegreeZero.of (inferInstance : GradedCategory R D)
    (F.obj (DegreeZero.obj (inferInstance : GradedCategory R C) X))
  map f :=
    ⟨F.map f.1, G.map_component f⟩
  map_id := by
    intro X
    apply Subtype.ext
    change F.map (𝟙 X.down) = 𝟙 (F.obj X.down)
    exact F.map_id _
  map_comp := by
    intro X Y Z f g
    apply Subtype.ext
    change F.map (f.1 ≫ g.1) = F.map f.1 ≫ F.map g.1
    exact F.map_comp _ _

theorem degreeZero_additive : Functor.Additive (G.degreeZero) := by
  constructor
  intro X Y f g
  apply Subtype.ext
  change F.map (f.1 + g.1) = F.map f.1 + F.map g.1
  exact G.additive.map_add

theorem degreeZero_linear : Functor.Linear R (G.degreeZero) := by
  constructor
  intro X Y f r
  apply Subtype.ext
  change F.map (r • f.1) = r • F.map f.1
  exact G.linear.map_smul f.1 r

end GradedFunctor

namespace GradedShiftFamily

variable {R : Type u} {C : Type v}
  [CommRing R] [Category.{w} C] [Preadditive C]
  [CategoryTheory.Linear R C] [GradedCategory R C]
  (S : GradedShiftFamily R C)

def IsDegreeZeroShiftRestriction
    (S : GradedShiftFamily R C)
    (T : LinearShiftFamily R (DegreeZero (inferInstance : GradedCategory R C))) : Prop :=
  ∀ (n : ℤ) (X : DegreeZero (inferInstance : GradedCategory R C)),
    (T.shift n).obj X =
      DegreeZero.of (inferInstance : GradedCategory R C)
        ((S.shift n).obj X.down)

theorem degree_zero_shift_family_nonempty :
    Nonempty
      {T : LinearShiftFamily R (DegreeZero (inferInstance : GradedCategory R C)) //
        IsDegreeZeroShiftRestriction S T} := by
  sorry

noncomputable def degree_zero_shift_family :
    LinearShiftFamily R (DegreeZero (inferInstance : GradedCategory R C)) :=
  (Classical.choice (degree_zero_shift_family_nonempty S)).1

theorem degree_zero_shift_family_restricts :
    IsDegreeZeroShiftRestriction S (degree_zero_shift_family S) :=
  (Classical.choice (degree_zero_shift_family_nonempty S)).2

theorem reconstructs_from_degree_zero :
    Nonempty
      (C ≌ LinearShiftFamily.GradedCategory (degree_zero_shift_family S)) := by
  sorry

end GradedShiftFamily

/-- The inherited shift family on a totalization, including its action on
objects. -/
structure InheritedGradedShiftFamily
    {R : Type u} {C : Type v}
    [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C]
    (S : LinearShiftFamily R C) where
  family : GradedShiftFamily R (LinearShiftFamily.GradedCategory S)
  object_shift : ∀ (n : ℤ) (X : LinearShiftFamily.GradedCategory S),
    (family.shift n).obj X =
      LinearShiftFamily.categoryObject S ((S.shift n).obj X.underlying)

theorem shift_totalization_inherits_graded_shifts
    {R : Type u} {C : Type v}
    [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C]
    (S : LinearShiftFamily R C) :
    Nonempty (InheritedGradedShiftFamily S) := by
  sorry

noncomputable def shift_totalization_graded_shifts
    {R : Type u} {C : Type v}
    [CommRing R] [Category.{w} C] [Preadditive C]
    [CategoryTheory.Linear R C]
    (S : LinearShiftFamily R C) :
    InheritedGradedShiftFamily S :=
  Classical.choice (shift_totalization_inherits_graded_shifts S)

end Formalization.Books.Dga.Unit25
