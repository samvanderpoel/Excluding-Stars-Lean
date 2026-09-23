import InducedStars.Structure.Subcritical.LocalPenaltyParameters
import InducedStars.Structure.Subcritical.ResidualMatchingParameters
import InducedStars.Structure.Subcritical.ProfileHeadroom

/-!
# One scalar package for finite subcritical aggregation

The two exponential rates are fixed before any of the four small parameters.
The package contains only numerical reserves, never graph-count or probability
conclusions. Binary entropy and `log2` retain the original profile-error units.
-/

noncomputable section
namespace InducedStars

def subcriticalAggregationRootRate (k : ℕ) (eta : ℝ) (R₀ : ℕ) : ℝ :=
  subcriticalLocalPenaltyUnit k * eta / R₀

def subcriticalAggregationMatchingRate (k : ℕ) (eta : ℝ) (R₀ : ℕ) : ℝ :=
  subcriticalResidualMatchingConstant k eta R₀ /
    (2 * (subcriticalResidualMatchingKappa eta R₀ : ℝ))

/-- The factor 64 leaves room for both polynomial absorption and summation;
polynomial absorption consumes only a fixed portion of each profile penalty. -/
def subcriticalAggregationConstant (k : ℕ) (eta : ℝ) (R₀ : ℕ) : ℝ :=
  min (subcriticalAggregationRootRate k eta R₀)
    (subcriticalAggregationMatchingRate k eta R₀) / 64

theorem subcriticalAggregationRootRate_pos {k R₀ : ℕ} {eta : ℝ}
    (hk : 3 ≤ k) (heta : 0 < eta) (hR : 1 ≤ R₀) :
    0 < subcriticalAggregationRootRate k eta R₀ := by
  have hRpos : (0 : ℝ) < R₀ := by exact_mod_cast (show 0 < R₀ by omega)
  exact div_pos (mul_pos (subcriticalLocalPenaltyUnit_pos hk) heta) hRpos

theorem subcriticalAggregationMatchingRate_pos {k R₀ : ℕ} {eta : ℝ}
    (hk : 3 ≤ k) (heta : 0 < eta) (hR : 1 ≤ R₀) :
    0 < subcriticalAggregationMatchingRate k eta R₀ := by
  have hkap : (0 : ℝ) < subcriticalResidualMatchingKappa eta R₀ := by
    have hh := subcriticalResidualMatchingKappa_pos heta hR
    exact_mod_cast (show 0 < subcriticalResidualMatchingKappa eta R₀ by omega)
  exact div_pos (subcriticalResidualMatchingConstant_pos hk heta hR) (by positivity)

theorem subcriticalAggregationConstant_pos {k R₀ : ℕ} {eta : ℝ}
    (hk : 3 ≤ k) (heta : 0 < eta) (hR : 1 ≤ R₀) :
    0 < subcriticalAggregationConstant k eta R₀ := by
  have ha := subcriticalAggregationRootRate_pos hk heta hR
  have hb := subcriticalAggregationMatchingRate_pos hk heta hR
  unfold subcriticalAggregationConstant
  positivity

theorem subcriticalAggregationConstant_le_root (k : ℕ) (eta : ℝ) (R₀ : ℕ) :
    64 * subcriticalAggregationConstant k eta R₀ ≤
      subcriticalAggregationRootRate k eta R₀ := by
  unfold subcriticalAggregationConstant
  linarith only [min_le_left (subcriticalAggregationRootRate k eta R₀)
    (subcriticalAggregationMatchingRate k eta R₀)]

theorem subcriticalAggregationConstant_le_matching (k : ℕ) (eta : ℝ) (R₀ : ℕ) :
    64 * subcriticalAggregationConstant k eta R₀ ≤
      subcriticalAggregationMatchingRate k eta R₀ := by
  unfold subcriticalAggregationConstant
  linarith only [min_le_right (subcriticalAggregationRootRate k eta R₀)
    (subcriticalAggregationMatchingRate k eta R₀)]

/-- The whole finite scalar hierarchy, with a single shared tuple. -/
structure SubcriticalAggregationParameters
    (k : ℕ) (gamma eta : ℝ) (R₀ : ℕ)
    (theta alpha delta epsilon : ℝ) (n : ℕ) : Prop where
  localConditions : SubcriticalLocalPenaltyParameters k R₀ eta theta alpha delta epsilon n
  residual : SubcriticalResidualMatchingConditions k eta R₀ theta alpha delta epsilon n
  gamma_pos : 0 < gamma
  retained_inverse : 1 / (R₀ : ℝ) ≤ eta
  alpha_theta : alpha ≤ theta / (100 * (k : ℝ))
  matching_entropy : binaryEntropy (5 * alpha) + theta ≤
    subcriticalResidualMatchingConstant k eta R₀ /
      (8 * (subcriticalResidualMatchingKappa eta R₀ : ℝ) ^ 2)
  epsilon_cap : epsilon ≤ min eta (theta ^ 2)
  density_headroom : subcriticalSparseSideConstant k * eta + epsilon ≤ gamma / 16
  shift_headroom : epsilon ≤ delta * gamma / 192
  profile_error_base : subcriticalProfileErrorConstant k R₀ *
    (binaryEntropy (5 * alpha) + theta + delta +
      subcriticalProfileRootFraction alpha theta epsilon) ≤
        subcriticalAggregationRootRate k eta R₀ / 8
  profile_error_log : subcriticalProfileErrorConstant k R₀ * log2 (n + 1) ≤
    subcriticalAggregationRootRate k eta R₀ / 8 * n
  profile_order : 2 ≤ n
  active_rounding : subcriticalActiveRoundingThreshold delta theta ≤ n

end InducedStars
