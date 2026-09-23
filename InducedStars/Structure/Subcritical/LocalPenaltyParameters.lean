import InducedStars.Structure.Subcritical.LocalPenaltyErrors
import InducedStars.Structure.Subcritical.SparseRowBudget

/-!
# Common finite scalar reserves for local compensation

These are numerical hypotheses only. No field assumes a root penalty,
an entropy estimate, a tail estimate, or a relocation conclusion.
-/

noncomputable section
open Filter
open scoped Topology
namespace InducedStars

/-- All finite reserves used by unified local compensation, with the genuine
profile root fraction and the finite alignment rounding error substituted. -/
structure SubcriticalLocalPenaltyParameters (k R₀ : ℕ)
    (eta theta alpha delta epsilon : ℝ) (n : ℕ) : Prop where
  star_order : 3 ≤ k
  retained_order : 1 ≤ R₀
  eta_pos : 0 < eta
  theta_pos : 0 < theta
  alpha_pos : 0 < alpha
  alpha_small : 5 * alpha ≤ 1 / 2
  relocation_alpha : (4 * (k : ℝ) + 8) * alpha ≤ 1
  delta_nonneg : 0 ≤ delta
  epsilon_nonneg : 0 ≤ epsilon
  retained_visible : theta ≤ eta / (2 * (R₀ : ℝ))
  relocation_theta : 20 * (k : ℝ) * theta ≤ eta / (2 * (R₀ : ℝ))
  row_counting : delta ≤ subcriticalRowCountingTolerance k
  density_lower : 6 * delta ≤ pK k
  density_upper : 6 * delta ≤ 1 - pK k
  root_fraction : subcriticalProfileRootFraction alpha theta epsilon ≤ alpha * theta / 4
  entropy_band : subcriticalSmallOwnConstant k * alpha /
    (1 - subcriticalTrimErrorNat (subcriticalProfileRootFraction alpha theta epsilon) theta) ≤ 1 / 2
  row_scale : 8 ≤ alpha * theta * n
  sparse_scale : 32 * (k : ℝ) ^ 3 ≤ theta * n
  source_scale : 4 * (R₀ : ℝ) ≤ eta * n
  zero_probability_reserve : ((k - 2 : ℕ) : ℝ) * subcriticalLocalU_Nat k ≤ ((n : ℝ) + 1) ^ 2
  total_error : subcriticalTotalErrorNat k R₀ eta alpha delta
    (subcriticalTrimErrorNat (subcriticalProfileRootFraction alpha theta epsilon) theta)
    (subcriticalInsideScaleErrorNat alpha delta theta n) ≤ subcriticalLocalA_Nat k / 4

namespace SubcriticalLocalPenaltyParameters
variable {k R₀ n : ℕ} {eta theta alpha delta epsilon : ℝ}
  (P : SubcriticalLocalPenaltyParameters k R₀ eta theta alpha delta epsilon n)

include P

theorem alpha_quarter : alpha ≤ 1 / 4 := by have := P.alpha_small; linarith
theorem alpha_fifth : alpha ≤ 1 / 5 := by have := P.alpha_small; linarith

theorem order_pos : 0 < n := by
  by_contra h
  have hn : n = 0 := by omega
  have h := P.row_scale
  norm_num [hn] at h

theorem root_fraction_nonneg : 0 ≤ subcriticalProfileRootFraction alpha theta epsilon := by
  unfold subcriticalProfileRootFraction
  exact div_nonneg (mul_nonneg (by norm_num) P.epsilon_nonneg)
    (mul_nonneg P.alpha_pos.le P.theta_pos.le)

theorem trim_nonneg : 0 ≤
    subcriticalTrimErrorNat (subcriticalProfileRootFraction alpha theta epsilon) theta :=
  div_nonneg (mul_nonneg (by norm_num) P.root_fraction_nonneg) P.theta_pos.le

theorem trim_le_half_alpha :
    subcriticalTrimErrorNat (subcriticalProfileRootFraction alpha theta epsilon) theta ≤ alpha / 2 := by
  unfold subcriticalTrimErrorNat
  apply (div_le_iff₀ P.theta_pos).mpr
  linarith [P.root_fraction]

theorem trim_lt_one :
    subcriticalTrimErrorNat (subcriticalProfileRootFraction alpha theta epsilon) theta < 1 := by
  have := P.trim_le_half_alpha
  have := P.alpha_small
  linarith

theorem tail_band : 2 * alpha /
    (1 - subcriticalTrimErrorNat (subcriticalProfileRootFraction alpha theta epsilon) theta) ≤ 1 / 2 := by
  apply le_trans _ P.entropy_band
  apply div_le_div_of_nonneg_right _ (by linarith [P.trim_lt_one])
  have hk : (3 : ℝ) ≤ k := by exact_mod_cast P.star_order
  unfold subcriticalSmallOwnConstant
  nlinarith [P.alpha_pos]

theorem inside_error_nonneg : 0 ≤ subcriticalInsideScaleErrorNat alpha delta theta n := by
  unfold subcriticalInsideScaleErrorNat
  have ha := P.alpha_pos
  have hd := P.delta_nonneg
  have ht := P.theta_pos
  positivity

/-- Flexible Goal-9f parameters: the current arbitrarily small alpha is
retained, not replaced by the example witness from that goal. -/
def sparseRowParameters : SubcriticalSparseRowParameters k R₀ eta where
  alpha := alpha
  theta := theta
  alpha_pos := P.alpha_pos
  alpha_quarter := P.alpha_quarter
  alpha_budget := by
    have h := P.relocation_alpha
    have ha := P.alpha_pos
    have hk1 : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
    nlinarith
  theta_pos := P.theta_pos
  retained_visible := P.retained_visible
  relocation_reserve := P.relocation_theta

/-- Every visible target has enough room to absorb both root deletion and
the own-part loop. The order reserve is uniform over targets and profiles. -/
theorem roots_add_one_le_part
    {G : SimpleGraph (Fin n)} {D : SubcriticalDivision k (Fin n)}
    {L : AdmissibleBlockSequence k} {omega : ℝ} {hk : 3 ≤ k}
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (homega : omega ≤ 1) {p : SubcriticalProfile D eta R₀ theta}
    (hB : (p.roots.card : ℝ) ≤ subcriticalProfileRootFraction alpha theta epsilon * n)
    (a : D.PartIndex) (ha : a ∈ D.visiblePartIndices theta) :
    (p.roots.card : ℝ) + 1 ≤ alpha * (D.part a).card := by
  have hsize := R.visible_part_card_ge_half homega a ha
  have hmul := mul_le_mul_of_nonneg_left hsize P.alpha_pos.le
  have hroot := mul_le_mul_of_nonneg_right P.root_fraction (Nat.cast_nonneg n)
  have hs := P.row_scale
  nlinarith

theorem half_trim
    {G : SimpleGraph (Fin n)} {D : SubcriticalDivision k (Fin n)}
    {L : AdmissibleBlockSequence k} {omega : ℝ} {hk : 3 ≤ k}
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (homega : omega ≤ 1) {p : SubcriticalProfile D eta R₀ theta}
    (hB : (p.roots.card : ℝ) ≤ subcriticalProfileRootFraction alpha theta epsilon * n)
    (a : D.PartIndex) (ha : a ∈ D.visiblePartIndices theta) :
    2 * (p.roots.card : ℝ) ≤ (D.part a).card := by
  have h := P.roots_add_one_le_part R homega hB a ha
  have hsmall := P.alpha_quarter
  have hsize : (0 : ℝ) ≤ (D.part a).card := Nat.cast_nonneg _
  nlinarith

end SubcriticalLocalPenaltyParameters
end InducedStars
