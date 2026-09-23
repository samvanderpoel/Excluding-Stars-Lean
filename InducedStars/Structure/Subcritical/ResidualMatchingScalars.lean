import InducedStars.Structure.Subcritical.ResidualCandidateProbability
import InducedStars.Structure.Subcritical.ResidualCandidateCounting

/-!
# Fixed residual matching constants

The expectation, overlap, and final matching rates are fixed by `k,eta,R₀`
before choosing `theta,alpha,delta,epsilon`. All exponential units are natural. These deliberately uniform constants work in all four placements.
-/

noncomputable section
namespace InducedStars

def subcriticalResidualDependencyCoefficient (k : ℕ) : ℝ := 2 * (k + 1 : ℝ)^4

theorem subcriticalResidualDependencyCoefficient_pos (k : ℕ) :
    0 < subcriticalResidualDependencyCoefficient k := by
  unfold subcriticalResidualDependencyCoefficient
  positivity

def subcriticalResidualMuCoefficient (k : ℕ) (eta : ℝ) (R₀ : ℕ) : ℝ :=
  subcriticalResidualCandidateRate k (subcriticalResidualMatchingLambda eta R₀) *
    subcriticalResidualCandidateAtomFloor k

theorem subcriticalResidualMuCoefficient_pos {k R₀ : ℕ} {eta : ℝ}
    (hk : 3 ≤ k) (heta : 0 < eta) (hR : 1 ≤ R₀) :
    0 < subcriticalResidualMuCoefficient k eta R₀ :=
  mul_pos (subcriticalResidualCandidateRate_pos k
    (subcriticalResidualMatchingLambda_pos heta hR))
      (subcriticalResidualCandidateAtomFloor_pos hk)

def subcriticalResidualMatchingConstant (k : ℕ) (eta : ℝ) (R₀ : ℕ) : ℝ :=
  subcriticalResidualJansonLinearConstant (subcriticalResidualMuCoefficient k eta R₀)
    (subcriticalResidualDependencyCoefficient k) *
      subcriticalResidualMatchingLambda eta R₀ / 8

theorem subcriticalResidualMatchingConstant_pos {k R₀ : ℕ} {eta : ℝ}
    (hk : 3 ≤ k) (heta : 0 < eta) (hR : 1 ≤ R₀) :
    0 < subcriticalResidualMatchingConstant k eta R₀ := by
  have hJ := subcriticalResidualJansonLinearConstant_pos
    (subcriticalResidualMuCoefficient_pos hk heta hR)
    (subcriticalResidualDependencyCoefficient_pos k)
  have hl := subcriticalResidualMatchingLambda_pos heta hR
  unfold subcriticalResidualMatchingConstant
  positivity

/-- One fixed cap controls both endpoint cleaning and free-pair deletion. -/
def subcriticalResidualDegreeCap (k : ℕ) (eta : ℝ) (R₀ : ℕ) : ℝ :=
  min (subcriticalResidualMatchingLambda eta R₀ / 8)
    (subcriticalResidualCandidateRate k (subcriticalResidualMatchingLambda eta R₀) /
      (k + 1 : ℝ)^2)

theorem subcriticalResidualDegreeCap_pos (k : ℕ) {R₀ : ℕ} {eta : ℝ}
    (heta : 0 < eta) (hR : 1 ≤ R₀) :
    0 < subcriticalResidualDegreeCap k eta R₀ := by
  have hl := subcriticalResidualMatchingLambda_pos heta hR
  have hc := subcriticalResidualCandidateRate_pos k hl
  unfold subcriticalResidualDegreeCap
  positivity

theorem subcriticalResidualDegreeCap_endpoint (k : ℕ) {R₀ : ℕ} {eta d : ℝ}
    (heta : 0 < eta) (hR : 1 ≤ R₀)
    (hd : d ≤ subcriticalResidualDegreeCap k eta R₀) :
    2*d ≤ subcriticalResidualMatchingLambda eta R₀ / 2 := by
  have hl := subcriticalResidualMatchingLambda_pos heta hR
  have hh := hd.trans (min_le_left _ _)
  change d ≤ subcriticalResidualMatchingLambda eta R₀ / 8 at hh
  linarith

theorem subcriticalResidualDegreeCap_free (k : ℕ) {R₀ : ℕ} {eta d : ℝ}
    (hd0 : 0 ≤ d) (hd : d ≤ subcriticalResidualDegreeCap k eta R₀) :
    ((k-1 : ℕ) : ℝ)^2*d ≤
      (subcriticalResidualMatchingLambda eta R₀ / 2)^(k-1)/2 := by
  have hh := hd.trans (min_le_right _ _)
  change d ≤ subcriticalResidualCandidateRate k (subcriticalResidualMatchingLambda eta R₀) /
    (k + 1 : ℝ)^2 at hh
  have hp : 0 < (k + 1 : ℝ)^2 := by positivity
  have hb := (le_div_iff₀ hp).mp hh
  have hk : ((k-1 : ℕ) : ℝ) ≤ k + 1 := by exact_mod_cast (show k-1 ≤ k+1 by omega)
  calc
    _ ≤ (k+1 : ℝ)^2*d := by gcongr
    _ = d*(k+1 : ℝ)^2 := by ring
    _ ≤ _ := hb

end InducedStars
