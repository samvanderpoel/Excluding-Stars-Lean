import InducedStars.Graphon.ProfileBlocks
import Mathlib.Tactic

/-!
# Quantitative tails of admissible block sequences

This file supplies the uniform rank, square-tail, and normalized-mass-tail
estimates used in the finite-block compactness argument.  Tails are indexed
as `N + j`, so rank `N` is included.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace InducedStars

namespace AdmissibleBlockSequence

variable {k : ℕ} (L : AdmissibleBlockSequence k)

/-- The `i`-th length in a nonincreasing admissible sequence is at most
`1 / (i+1)`. -/
theorem alpha_le_inv_succ (i : ℕ) :
    L.alpha i ≤ 1 / ((i + 1 : ℕ) : ℝ) := by
  have hsum : ((i + 1 : ℕ) : ℝ) * L.alpha i ≤ 1 := by
    calc
      ((i + 1 : ℕ) : ℝ) * L.alpha i =
          ∑ j ∈ Finset.range (i + 1), L.alpha i := by simp
      _ ≤ ∑ j ∈ Finset.range (i + 1), L.alpha j := by
        apply Finset.sum_le_sum
        intro j hj
        exact L.alpha_antitone (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      _ ≤ ∑' j, L.alpha j :=
        L.summable_alpha.sum_le_tsum (Finset.range (i + 1))
          (fun j _ ↦ L.alpha_nonneg j)
      _ ≤ 1 := L.tsum_alpha_le_one
  have hi : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
  apply (le_div_iff₀ hi).2
  simpa [mul_comm] using hsum

/-- The square tail beginning at rank `N`. -/
def alphaSquareTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, L.alpha (N + j) ^ 2

/-- The normalized quadratic-mass tail beginning at rank `N`. -/
def massTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, L.massTerm (N + j)

theorem summable_alpha_shift (N : ℕ) :
    Summable (fun j : ℕ ↦ L.alpha (N + j)) := by
  exact L.summable_alpha.comp_injective (fun _ _ h ↦ Nat.add_left_cancel h)

theorem summable_alpha_sq_shift (N : ℕ) :
    Summable (fun j : ℕ ↦ L.alpha (N + j) ^ 2) := by
  exact L.summable_alpha_sq.comp_injective
    (fun _ _ h ↦ Nat.add_left_cancel h)

theorem summable_massTerm_shift (N : ℕ) :
    Summable (fun j : ℕ ↦ L.massTerm (N + j)) := by
  exact L.summable_massTerm.comp_injective
    (fun _ _ h ↦ Nat.add_left_cancel h)

theorem alphaSquareTail_nonneg (N : ℕ) : 0 ≤ L.alphaSquareTail N := by
  exact tsum_nonneg fun _ ↦ sq_nonneg _

theorem massTail_nonneg (N : ℕ) : 0 ≤ L.massTail N := by
  exact tsum_nonneg fun _ ↦ L.massTerm_nonneg _

/-- The whole square tail is controlled by its first length. -/
theorem alphaSquareTail_le_alpha (N : ℕ) :
    L.alphaSquareTail N ≤ L.alpha N := by
  have hpoint (j : ℕ) :
      L.alpha (N + j) ^ 2 ≤ L.alpha N * L.alpha (N + j) := by
    have hmono : L.alpha (N + j) ≤ L.alpha N :=
      L.alpha_antitone (Nat.le_add_right N j)
    nlinarith [L.alpha_nonneg (N + j)]
  calc
    L.alphaSquareTail N ≤
        ∑' j : ℕ, L.alpha N * L.alpha (N + j) := by
      exact Summable.tsum_le_tsum (fun j ↦ hpoint j)
        (L.summable_alpha_sq_shift N)
        ((L.summable_alpha_shift N).mul_left (L.alpha N))
    _ = L.alpha N * ∑' j : ℕ, L.alpha (N + j) := by
      rw [(L.summable_alpha_shift N).tsum_mul_left]
    _ ≤ L.alpha N * 1 := by
      apply mul_le_mul_of_nonneg_left _ (L.alpha_nonneg N)
      calc
        ∑' j : ℕ, L.alpha (N + j) ≤ ∑' i : ℕ, L.alpha i := by
          exact (L.summable_alpha_shift N).tsum_le_tsum_of_inj
            (fun j ↦ N + j) (fun _ _ h ↦ Nat.add_left_cancel h)
            (fun c _ ↦ L.alpha_nonneg c) (fun _ ↦ le_rfl)
            L.summable_alpha
        _ ≤ 1 := L.tsum_alpha_le_one
    _ = L.alpha N := mul_one _

/-- Uniform square-tail estimate, including rank `N`. -/
theorem alphaSquareTail_le_inv_succ (N : ℕ) :
    L.alphaSquareTail N ≤ 1 / ((N + 1 : ℕ) : ℝ) :=
  (L.alphaSquareTail_le_alpha N).trans (L.alpha_le_inv_succ N)

/-- Every normalized mass tail is at most `1/(k-1)` times the corresponding
square tail. -/
theorem massTail_le_inv_k_sub_one_mul_alphaSquareTail
    (hk : 3 ≤ k) (N : ℕ) :
    L.massTail N ≤
      (1 / ((k - 1 : ℕ) : ℝ)) * L.alphaSquareTail N := by
  have hkpos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hpoint (j : ℕ) :
      L.massTerm (N + j) ≤
        (1 / ((k - 1 : ℕ) : ℝ)) * L.alpha (N + j) ^ 2 := by
    have horderNat := RegularBlockCore.k_sub_one_le_order hk (L.core (N + j))
    have horder : ((k - 1 : ℕ) : ℝ) ≤ (L.core (N + j)).order := by
      exact_mod_cast horderNat
    unfold massTerm
    have horderPos : (0 : ℝ) < ((L.core (N + j)).order : ℝ) := by
      exact_mod_cast (L.core (N + j)).order_pos
    have hinv : (1 : ℝ) / (L.core (N + j)).order ≤
        1 / ((k - 1 : ℕ) : ℝ) := by
      exact one_div_le_one_div_of_le hkpos horder
    rw [div_eq_mul_inv, one_div]
    calc
      L.alpha (N + j) ^ 2 * ((L.core (N + j)).order : ℝ)⁻¹ ≤
          L.alpha (N + j) ^ 2 * ((k - 1 : ℕ) : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left (by simpa [one_div] using hinv) (sq_nonneg _)
      _ = ((k - 1 : ℕ) : ℝ)⁻¹ * L.alpha (N + j) ^ 2 := by ring
  calc
    L.massTail N ≤
        ∑' j : ℕ,
          (1 / ((k - 1 : ℕ) : ℝ)) * L.alpha (N + j) ^ 2 := by
      exact Summable.tsum_le_tsum (fun j ↦ hpoint j)
        (L.summable_massTerm_shift N)
        ((L.summable_alpha_sq_shift N).mul_left _)
    _ = (1 / ((k - 1 : ℕ) : ℝ)) * L.alphaSquareTail N := by
      rw [(L.summable_alpha_sq_shift N).tsum_mul_left]
      rfl

/-- Fully explicit normalized mass-tail estimate. -/
theorem massTail_le_inv_k_sub_one_mul_inv_succ
    (hk : 3 ≤ k) (N : ℕ) :
    L.massTail N ≤
      (1 / ((k - 1 : ℕ) : ℝ)) *
        (1 / ((N + 1 : ℕ) : ℝ)) := by
  exact (L.massTail_le_inv_k_sub_one_mul_alphaSquareTail hk N).trans
    (mul_le_mul_of_nonneg_left (L.alphaSquareTail_le_inv_succ N) (by positivity))

/-- The square tails tend uniformly to zero. -/
theorem alphaSquareTail_tendsto_zero :
    Tendsto L.alphaSquareTail atTop (𝓝 0) := by
  apply squeeze_zero
  · exact L.alphaSquareTail_nonneg
  · exact L.alphaSquareTail_le_inv_succ
  · simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end AdmissibleBlockSequence

end InducedStars
