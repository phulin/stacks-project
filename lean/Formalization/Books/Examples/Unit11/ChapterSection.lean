import Formalization.Books.Examples.Unit11.Definitions

/-!
# The category of derived complete modules

This is the formalization of the numbered section in Examples, Chapter 11.
The declarations retain the source order: first the direct-sum counterexample,
then the filtered-colimit system, and finally the structural lemma about the
category of derived complete modules.
-/

namespace Formalization.Books.Examples.Unit11

open CategoryTheory CategoryTheory.Limits

universe u

variable {A : Type u} [CommRing A]

/-! ### The direct-sum counterexample -/

/- The finitely generated hypothesis needed to identify derived completeness
with the ordinary adic completion criterion in the counterexample. -/
theorem padicIdeal_finitelyGenerated (p : ℕ) [Fact p.Prime] :
    (padicIdeal p).FG := by
  exact Submodule.fg_span_singleton _

/- Each `ℤ_p` summand in the counterexample is derived complete. -/
theorem padicIntegerModule_isDerivedComplete (p : ℕ) [Fact p.Prime] :
    IsDerivedComplete (padicIdeal p) (ModuleCat.of ℤ_[p] ℤ_[p]) := by
  sorry

/- A derived-complete module has a surjective map to its adic completion when
the ideal is finitely generated. -/
theorem derivedComplete_adicCompletionUnit_surjective (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A) (hM : IsDerivedComplete I M) :
    Function.Surjective (adicCompletionUnit I M) := by
  sorry

/- The completion map from `⊕ₙ ℤ_[p]` to its `p`-adic completion is not
surjective. -/
theorem padicDirectSum_adicCompletionUnit_not_surjective (p : ℕ) [Fact p.Prime] :
    ¬ Function.Surjective
      (adicCompletionUnit (padicIdeal p) (countableDirectSum ℤ_[p])) := by
  sorry

/- Hence the countable direct sum of derived-complete `ℤ_[p]`-modules need not
be derived complete. -/
theorem padicDirectSum_not_derivedComplete (p : ℕ) [Fact p.Prime] :
    ¬ IsDerivedComplete (padicIdeal p) (countableDirectSum ℤ_[p]) := by
  intro hM
  apply padicDirectSum_adicCompletionUnit_not_surjective p
  exact derivedComplete_adicCompletionUnit_surjective (padicIdeal p)
    (padicIdeal_finitelyGenerated p) _ hM

/- The multiplication maps between the power quotients compose as expected. -/
theorem padicPowerQuotientMap_comp (p m n k : ℕ) [Fact p.Prime]
    (hmn : m ≤ n) (hnk : n ≤ k) :
    padicPowerQuotientMap p m n hmn ≫ padicPowerQuotientMap p n k hnk =
      padicPowerQuotientMap p m k (hmn.trans hnk) := by
  sorry

/- The map from a power quotient to itself is the identity. -/
theorem padicPowerQuotientMap_id (p m : ℕ) [Fact p.Prime] (h : m ≤ m) :
    padicPowerQuotientMap p m m h = 𝟙 (padicQuotient p m) := by
  sorry

/- The maps used for `f_n` are inclusions, not merely homomorphisms. -/
theorem padicQuotientInclusionMap_injective (p n : ℕ) [Fact p.Prime] :
    Function.Injective
      (padicPowerQuotientMap p 1 (n + 1) (Nat.succ_pos n)).hom := by
  sorry

/- The concrete countable filtered system of power quotients. -/
noncomputable def padicQuotientDiagram (p : ℕ) [Fact p.Prime] :
    ℕ ⥤ ModuleCat ℤ_[p] where
  obj n := padicQuotient p (n + 1)
  map {m n} h :=
    padicPowerQuotientMap p (m + 1) (n + 1) (Nat.succ_le_succ (leOfHom h))
  map_id := by
    intro n
    exact padicPowerQuotientMap_id p (n + 1) (Nat.le_refl _)
  map_comp := by
    intro m n k hmn hnk
    exact (padicPowerQuotientMap_comp p (m + 1) (n + 1) (k + 1)
      (Nat.succ_le_succ (leOfHom hmn)) (Nat.succ_le_succ (leOfHom hnk))).symm

/- The constant system with value `ℤ_[p] / pℤ_[p]`. -/
noncomputable def padicConstantQuotientDiagram (p : ℕ) [Fact p.Prime] :
    ℕ ⥤ ModuleCat ℤ_[p] where
  obj _ := padicQuotient p 1
  map _ := 𝟙 _
  map_id := by intros; rfl
  map_comp := by intros; simp

/- The compatible family of maps `f_n` from the source text. -/
noncomputable def padicQuotientInclusion (p : ℕ) [Fact p.Prime] :
    padicConstantQuotientDiagram p ⟶ padicQuotientDiagram p where
  app n := padicPowerQuotientMap p 1 (n + 1) (Nat.succ_pos n)
  naturality := by
    intro m n h
    change padicPowerQuotientMap p 1 (n + 1) (Nat.succ_pos n) =
      padicPowerQuotientMap p 1 (m + 1) (Nat.succ_pos m) ≫
        padicPowerQuotientMap p (m + 1) (n + 1)
          (Nat.succ_le_succ (leOfHom h))
    exact (padicPowerQuotientMap_comp p 1 (m + 1) (n + 1)
      (Nat.succ_pos m) (Nat.succ_le_succ (leOfHom h))).symm

/- The commutative square from the source, with the right-hand map given by
multiplication by `p`. -/
theorem padicQuotientSquare_commutes (p n : ℕ) [Fact p.Prime] (hn : 0 < n) :
    (𝟙 (padicQuotient p 1) ≫ padicPowerQuotientMap p 1 (n + 1)
      (Nat.succ_pos n)) =
      padicPowerQuotientMap p 1 n hn ≫ padicPowerQuotientMap p n (n + 1)
        (Nat.le_succ n) := by
  simpa using (padicPowerQuotientMap_comp p 1 n (n + 1) hn (Nat.le_succ n)).symm

/- Each term in the displayed power-quotient system is derived complete. -/
theorem padicQuotient_isDerivedComplete (p n : ℕ) [Fact p.Prime] :
    IsDerivedComplete (padicIdeal p) (padicQuotient p n) := by
  sorry

/- The same quotients are complete for the ordinary p-adic topology. -/
theorem padicQuotient_isAdicComplete (p n : ℕ) [Fact p.Prime] :
    IsAdicComplete (padicIdeal p) (padicQuotient p n : Type) := by
  sorry

/- The displayed filtered system, now regarded as a diagram in the category
of derived-complete modules. -/
noncomputable def padicCompleteQuotientObject (p n : ℕ) [Fact p.Prime] :
    DerivedCompleteModuleCategory (padicIdeal p) :=
  ⟨padicQuotient p n, padicQuotient_isDerivedComplete p n⟩

noncomputable def padicDerivedQuotientDiagram (p : ℕ) [Fact p.Prime] :
    ℕ ⥤ DerivedCompleteModuleCategory (padicIdeal p) where
  obj n := padicCompleteQuotientObject p (n + 1)
  map {m n} h :=
    ObjectProperty.homMk
      (padicPowerQuotientMap p (m + 1) (n + 1)
        (Nat.succ_le_succ (leOfHom h)))
  map_id := by
    intro n
    apply ObjectProperty.hom_ext
    exact padicPowerQuotientMap_id p (n + 1) (Nat.le_refl _)
  map_comp := by
    intro m n k hmn hnk
    apply ObjectProperty.hom_ext
    exact (padicPowerQuotientMap_comp p (m + 1) (n + 1) (k + 1)
      (Nat.succ_le_succ (leOfHom hmn)) (Nat.succ_le_succ (leOfHom hnk))).symm

noncomputable def padicDerivedConstantQuotientDiagram (p : ℕ) [Fact p.Prime] :
    ℕ ⥤ DerivedCompleteModuleCategory (padicIdeal p) where
  obj _ := padicCompleteQuotientObject p 1
  map _ := 𝟙 _
  map_id := by intros; rfl
  map_comp := by intros; simp

/- The displayed maps as a natural transformation of derived-complete
diagrams. -/
noncomputable def padicDerivedQuotientInclusion (p : ℕ) [Fact p.Prime] :
    padicDerivedConstantQuotientDiagram p ⟶ padicDerivedQuotientDiagram p where
  app n :=
    ObjectProperty.homMk (padicPowerQuotientMap p 1 (n + 1) (Nat.succ_pos n))
  naturality := by
    intro m n h
    apply ObjectProperty.hom_ext
    change padicPowerQuotientMap p 1 (n + 1) (Nat.succ_pos n) =
      padicPowerQuotientMap p 1 (m + 1) (Nat.succ_pos m) ≫
        padicPowerQuotientMap p (m + 1) (n + 1)
          (Nat.succ_le_succ (leOfHom h))
    exact (padicPowerQuotientMap_comp p 1 (m + 1) (n + 1)
      (Nat.succ_pos m) (Nat.succ_le_succ (leOfHom h))).symm

/-! ### The colimit computation -/

/- Existence of the derived-completion/H⁰ interface for a finitely generated
ideal, corresponding to the earlier derived-completion construction. -/
theorem derivedCompletionData_exists (I : Ideal A) (hI : I.FG) :
    Nonempty (DerivedCompletionData I) := by
  sorry

/- The copy of `ℤ_[p]` inside `ℚ_[p]`, viewed as an `ℤ_[p]`-submodule. -/
noncomputable def padicIntegerSubmodule (p : ℕ) [Fact p.Prime] :
    Submodule ℤ_[p] ℚ_[p] :=
  LinearMap.range (Algebra.linearMap ℤ_[p] ℚ_[p])

/- The module `ℚ_p / ℤ_p` appearing as the colimit in `Mod_{ℤ_p}`. -/
noncomputable def padicTorsionQuotient (p : ℕ) [Fact p.Prime] : ModuleCat ℤ_[p] :=
  ModuleCat.of ℤ_[p] (ℚ_[p] ⧸ padicIntegerSubmodule p)

/- The colimit of the right-hand system is `ℚ_p / ℤ_p`. -/
theorem padicModuleColimit_iso_padicTorsionQuotient (p : ℕ) [Fact p.Prime] :
    Nonempty (colimit (padicQuotientDiagram p) ≅ padicTorsionQuotient p) := by
  sorry

/- The module-level `H⁰` of the derived-completed `ℚ_p / ℤ_p` is zero. -/
theorem padicTorsionQuotient_derivedCompletionH0_iso_zero (p : ℕ) [Fact p.Prime]
    (D : DerivedCompletionData (padicIdeal p)) :
    Nonempty (derivedCompletionH0 D (padicTorsionQuotient p) ≅
      (ModuleCat.of ℤ_[p] PUnit)) := by
  sorry

/- The completed colimit used for the colimit in the derived-complete
category is zero in the `p`-adic example. -/
theorem padicDerivedCompleteColimit_iso_zero (p : ℕ) [Fact p.Prime]
    (D : DerivedCompletionData (padicIdeal p)) :
    Nonempty
      (derivedCompletionH0 D (colimit (padicQuotientDiagram p)) ≅
        (ModuleCat.of ℤ_[p] PUnit)) := by
  sorry

/- The map from the first quotient to the completed colimit in the derived-
complete category is zero, as in the source's displayed colimit map. -/
noncomputable def padicDerivedCompleteColimitMap (p : ℕ) [Fact p.Prime]
    (D : DerivedCompletionData (padicIdeal p)) :
    (padicDerivedQuotientDiagram p).obj 0 ⟶
      derivedCompleteColimit D (padicDerivedQuotientDiagram p) :=
  derivedCompleteColimitMap D (padicDerivedQuotientDiagram p) 0

theorem padicDerivedCompleteColimitMap_eq_zero (p : ℕ) [Fact p.Prime]
    (D : DerivedCompletionData (padicIdeal p)) :
    padicDerivedCompleteColimitMap p D = 0 := by
  sorry

/-! ### Structural properties of the category `C` -/

/- The full subcategory of derived complete modules is abelian. -/
instance derivedCompleteModuleCategory_abelian (I : Ideal A) :
    Abelian (DerivedCompleteModuleCategory I) := by
  sorry

/- The full inclusion preserves zero morphisms, as every full functor does. -/
instance derivedCompleteModuleInclusion_preservesZeroMorphisms (I : Ideal A) :
    (derivedCompleteModuleInclusion I).PreservesZeroMorphisms := by
  change (DerivedCompleteModuleProperty I).ι.PreservesZeroMorphisms
  exact Functor.preservesZeroMorphisms_of_full _

/- The category `C` has arbitrary limits. -/
theorem derivedCompleteModuleCategory_has_limits (I : Ideal A) :
    HasLimits (DerivedCompleteModuleCategory I) := by
  sorry

/- The inclusion `C ↪ Mod_A` preserves arbitrary limits. -/
theorem derivedCompleteModuleInclusion_preserves_limits (I : Ideal A) :
    PreservesLimits (derivedCompleteModuleInclusion I) := by
  sorry

/- If `I` is finitely generated, `C` has arbitrary colimits. -/
theorem derivedCompleteModuleCategory_has_colimits (I : Ideal A) (hI : I.FG) :
    HasColimits (DerivedCompleteModuleCategory I) := by
  sorry

/- If `I` is finitely generated, `C` has arbitrary coproducts/direct sums. -/
theorem derivedCompleteModuleCategory_has_coproducts (I : Ideal A) (hI : I.FG) :
    HasCoproducts (DerivedCompleteModuleCategory I) := by
  sorry

/- The inclusion does not preserve countable direct sums in the `p`-adic
counterexample. -/
theorem padicDerivedCompleteInclusion_not_preserves_directSums (p : ℕ)
    [Fact p.Prime] :
    ¬ PreservesColimitsOfShape (Discrete ℕ)
      (derivedCompleteModuleInclusion (padicIdeal p)) := by
  sorry

/- The inclusion does not preserve filtered colimits in the `p`-adic
counterexample. -/
theorem padicDerivedCompleteInclusion_not_preserves_filteredColimits (p : ℕ)
    [Fact p.Prime] :
    ¬ PreservesFilteredColimits
      (derivedCompleteModuleInclusion (padicIdeal p)) := by
  sorry

/- The inclusion preserves exact short complexes. -/
theorem derivedCompleteModuleInclusion_preserves_exact (I : Ideal A) :
    ∀ ⦃S : ShortComplex (DerivedCompleteModuleCategory I)⦄,
      S.Exact →
        (S.map (derivedCompleteModuleInclusion I)).Exact := by
  sorry

/- Filtered colimits in the `p`-adic derived-complete category are not exact. -/
theorem padicDerivedCompleteModuleCategory_filteredColimits_not_exact
    (p : ℕ) [Fact p.Prime] :
    ¬ FilteredColimitsExact
      (DerivedCompleteModuleCategory (padicIdeal p)) := by
  sorry

/- Consequently, this `p`-adic category is not Grothendieck abelian. -/
theorem padicDerivedCompleteModuleCategory_not_grothendieck
    (p : ℕ) [Fact p.Prime] :
    ¬ IsGrothendieckAbelian
      (DerivedCompleteModuleCategory (padicIdeal p)) := by
  sorry

end Formalization.Books.Examples.Unit11
