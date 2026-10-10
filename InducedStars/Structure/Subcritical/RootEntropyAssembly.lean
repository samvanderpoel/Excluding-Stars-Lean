import InducedStars.Structure.Subcritical.ExternalRows

/-!
# Finite retained-root entropy assembly

The own row, inside rows, and external rows are kept separate until the
last scalar inequality. Every displayed error is in natural units.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}

/-- The fixed threshold in the elementary relocation proof. -/
def subcriticalSmallOwnConstant (k : ℕ) : ℝ := 8 * k

def subcriticalSmallOwnErrorNat (k : ℕ) (alpha xi : ℝ) : ℝ :=
  Real.binEntropy (subcriticalSmallOwnConstant k * alpha / (1 - xi)) +
    subcriticalLogOddsNat k * subcriticalSmallOwnConstant k * alpha

theorem subcriticalProfileOwnCount_le_trimmed
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots) :
    (p.ownCount v).val ≤
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots).card :=
  p.ownCount_capacity v hv

theorem subcriticalOwnEntropy_le
    (hk : 3 ≤ k) (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (hv : v ∈ p.retainedRoots) :
    subcriticalProfileOwnMissingEntropyNat p v ≤ subcriticalLocalU_Nat k *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card := by
  rw [subcriticalProfileOwnMissingEntropyNat, dif_pos hv]
  exact subcriticalLocalEntropy_own_le_untrimmed hk (Nat.cast_nonneg _)
    (by exact_mod_cast subcriticalProfileOwnCount_le_trimmed p v hv)
    (by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset :
      D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots ⊆ _))

theorem subcriticalOwnEntropy_high_le
    (hk : 3 ≤ k) (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (hv : v ∈ p.retainedRoots) {alpha : ℝ}
    (ha : 0 ≤ alpha) (ha4 : alpha ≤ 1 / 4)
    (hI : (1 - 2 * alpha) *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots).card ≤
        ((p.ownCount v).val : ℝ)) :
    subcriticalProfileOwnMissingEntropyNat p v ≤
      (subcriticalLogOddsNat k + Real.binEntropy (2 * alpha)) *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card := by
  rw [subcriticalProfileOwnMissingEntropyNat, dif_pos hv]
  exact (subcriticalLocalEntropy_high_own_le hk ha ha4 (Nat.cast_nonneg _)
    (by exact_mod_cast subcriticalProfileOwnCount_le_trimmed p v hv) hI).trans
    (mul_le_mul_of_nonneg_left
      (by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset :
        D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots ⊆ _))
      (add_nonneg (subcriticalLogOddsNat_pos hk).le
        (Real.binEntropy_nonneg (by linarith) (by linarith))))

theorem subcriticalOwnEntropy_small_le
    (hk : 3 ≤ k) (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (hv : v ∈ p.retainedRoots) {alpha xi : ℝ}
    (ha : 0 ≤ alpha) (hxi : xi < 1)
    (hband : subcriticalSmallOwnConstant k * alpha / (1 - xi) ≤ 1 / 2)
    (htrim : (1 - xi) * (D.part (D.retainedVertexPart eta R₀ v
        (p.retainedRoots_subset hv))).card ≤
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots).card)
    (hI : ((p.ownCount v).val : ℝ) ≤ subcriticalSmallOwnConstant k * alpha *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card) :
    subcriticalProfileOwnMissingEntropyNat p v ≤ subcriticalSmallOwnErrorNat k alpha xi *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card := by
  rw [subcriticalProfileOwnMissingEntropyNat, dif_pos hv]
  have h := subcriticalLocalEntropy_small_own_le hk
    (show 0 ≤ subcriticalSmallOwnConstant k by unfold subcriticalSmallOwnConstant; positivity)
    ha hxi hband (Nat.cast_nonneg _)
    (by exact_mod_cast subcriticalProfileOwnCount_le_trimmed p v hv)
    (by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset :
      D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots ⊆ _))
    htrim hI
  simpa only [subcriticalSmallOwnErrorNat, mul_comm] using h

/-- The complete inside-row entropy with one improvement for every high
row, retaining the actual count of rows and actual full own-part scale. -/
theorem subcriticalInsideRowsEntropy
    (hk : 3 ≤ k) (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (hv : v ∈ p.retainedRoots) {alpha zeta : ℝ}
    (ha : 0 ≤ alpha) (ha4 : alpha ≤ 1 / 4) (hz : 0 ≤ zeta)
    (hscale : ∀ a ∈ subcriticalProfileInsideRows p v hv,
      |((D.part a \ p.roots).card : ℝ) -
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card| ≤ zeta *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card) :
    (∑ a ∈ subcriticalProfileInsideRows p v hv, subcriticalProfilePresentRowEntropyNat p v a) ≤
      (subcriticalLocalA_Nat k * (subcriticalProfileInsideRows p v hv).card -
        subcriticalLocalU_Nat k * (subcriticalProfileHighInsideRows p alpha v hv).card +
        subcriticalRowErrorNat k alpha zeta * (subcriticalProfileInsideRows p v hv).card) *
          (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card := by
  apply subcriticalEntropySum_le_high_improvement hk _ _ (Finset.filter_subset _ _)
  · intro a haS
    rw [subcriticalProfilePresentRowEntropyNat_eq_rowCount]
    exact subcriticalLocalEntropy_row_le_with_error hk ha ha4 (Nat.cast_nonneg _) hz
      (Nat.cast_nonneg _) (by exact_mod_cast subcriticalProfile_rowCount_le_trimmed p v a)
      (hscale a haS)
  · intro a haH
    obtain ⟨haS, hah⟩ := (mem_subcriticalProfileHighInsideRows p alpha v hv a).mp haH
    rw [subcriticalProfilePresentRowEntropyNat_eq_rowCount]
    exact subcriticalLocalEntropy_high_row_le_with_error hk ha ha4 (Nat.cast_nonneg _) hz
      (Nat.cast_nonneg _) (by exact_mod_cast subcriticalProfile_rowCount_le_trimmed p v a)
      hah (hscale a haS)

theorem subcriticalRootEntropy_decomposition
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots) :
    subcriticalProfileRootEntropyNat p v = subcriticalProfileOwnMissingEntropyNat p v +
      (∑ a ∈ subcriticalProfileInsideRows p v hv, subcriticalProfilePresentRowEntropyNat p v a) +
      (∑ a ∈ subcriticalProfileOutsideRows p v hv, subcriticalProfilePresentRowEntropyNat p v a) := by
  rw [subcriticalProfileRootEntropyNat, subcriticalProfilePresentRowEntropyNat_sum_eq_rows,
    ← subcriticalProfileRows_partition p v hv,
    Finset.sum_union (subcriticalProfileInsideOutsideRows_disjoint p v hv)]
  ring

end InducedStars
