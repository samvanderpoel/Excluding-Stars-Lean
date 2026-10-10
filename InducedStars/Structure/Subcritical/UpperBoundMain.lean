import InducedStars.Structure.Subcritical.CandidateUpperBound

/-!
# Finite density reserve for retained-key counting

A positive asymptotic edge density gives the finite lower bound used by
`lemma:profile-bound-K1k` for all sufficiently large graph orders.
-/

noncomputable section
open Filter Finset Set
open scoped BigOperators Classical Topology
namespace InducedStars

/-- Every positive asymptotic edge density supplies the finite lower-density
condition. No feasibility or rounding assumption on early terms is needed. -/
theorem HasAsymptoticEdgeDensity.eventually_subcritical_lower_density
    {m : ℕ → ℕ} {gamma : ℝ} (hm : HasAsymptoticEdgeDensity m gamma)
    (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in atTop, gamma / 8 * (n : ℝ)^2 ≤ m n := by
  have hd := (tendsto_order.1 hm).1 (gamma / 2) (by linarith)
  filter_upwards [hd, eventually_ge_atTop 2] with n hn hn2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hepos : (0 : ℝ) < completeEdgeCount n := by
    rw [completeEdgeCount, Nat.cast_choose_two]
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    exact div_pos (mul_pos hnpos (by linarith)) (by norm_num)
  have h := (lt_div_iff₀ hepos).mp hn
  rw [completeEdgeCount, Nat.cast_choose_two] at h
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  nlinarith [mul_nonneg hgamma.le
    (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hnR))]

end InducedStars
