import InducedStars.Structure.Critical.FineBalanceConditional
import InducedStars.Structure.Critical.FineBalanceUniformReference
import Mathlib.Tactic

/-!
# The critical fine-balance theorem

This file packages the fixed-sparse, fixed-remainder Gaussian calculation
into the paper-facing canonical clean-family statement.  The close radius
and sparse radius are chosen only after an arbitrary positive cap on the
close radius is supplied; no assertion is made here that these radii agree
with parameters selected by the later critical cleanup aggregation.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The explicit `k`-only error sequence in the final fixed-sparse
fine-balance comparison. -/
noncomputable def criticalFineBalanceError (k n : ℕ) : ℝ :=
  (2 * (k - 1).factorial : ℝ) * criticalFineBalanceRawError k n

theorem criticalFineBalanceError_nonneg (k n : ℕ) :
    0 ≤ criticalFineBalanceError k n := by
  unfold criticalFineBalanceError
  exact mul_nonneg (by positivity) (criticalFineBalanceRawError_nonneg k n)

/-- For fixed `k ≥ 3`, the explicit critical fine-balance error tends to
zero. -/
theorem criticalFineBalanceError_tendsto_zero
    {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (criticalFineBalanceError k) atTop (nhds 0) := by
  unfold criticalFineBalanceError
  simpa only [Pi.mul_apply, mul_zero] using
    (tendsto_const_nhds.mul (criticalFineBalanceRawError_tendsto_zero hk))

/-- Paper-facing fixed-sparse fine-balance theorem.  Below any prescribed
positive cap on the close radius, there are positive close and sparse radii
and a nonnegative `k`-only error tending to zero such that, uniformly over
every sufficiently large `n` and every sparse set in that radius, the
canonical clean graphs whose ordered main parts violate the literal
`sqrt (log₂ n)` pairwise balance condition form at most that error fraction
of the full canonical clean fixed-sparse family. -/
theorem criticalFixedSparseFineBalanceK1k
    (k : ℕ) (hk : 3 ≤ k) {tauCap : ℝ} (hCap : 0 < tauCap) :
    ∃ tau delta : ℝ,
      0 < tau ∧ tau ≤ tauCap ∧ 0 < delta ∧
        ∃ e : ℕ → ℝ,
          Tendsto e atTop (nhds 0) ∧
          (∀ n, 0 ≤ e n) ∧
          ∀ᶠ n : ℕ in atTop,
            ∀ (hn : k - 1 ≤ n) (S : Finset (Fin n)),
              (S.card : ℝ) ≤ delta * (n : ℝ) →
              ((criticalFixedSparseUnbalancedCleanGraphFinset
                  k hk n tau hn S).card : ℝ) ≤
                e n *
                  ((criticalCanonicalCleanFixedSparseGraphFinset
                    k hk n tau hn S).card : ℝ) := by
  obtain ⟨tau, deltaReference, htau, htauCap, hdeltaReference,
      hreference⟩ :=
    eventually_criticalFixedSparseBalancedCrossSliceMass_le_canonical
      k hk hCap
  let delta := min deltaReference (criticalFineBalanceSparseFraction k)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hdeltaReference (criticalFineBalanceSparseFraction_pos hk)
  have hdeltaReferenceLe : delta ≤ deltaReference := min_le_left _ _
  have hdeltaRawLe : delta ≤ criticalFineBalanceSparseFraction k :=
    min_le_right _ _
  refine ⟨tau, delta, htau, htauCap, hdelta,
    criticalFineBalanceError k,
    criticalFineBalanceError_tendsto_zero hk,
    criticalFineBalanceError_nonneg k, ?_⟩
  filter_upwards [hreference, eventually_ge_atTop 2] with
      n hnReference hnTwo
  intro hn S hsSmall
  have hsReference : (S.card : ℝ) ≤
      deltaReference * (n : ℝ) :=
    hsSmall.trans
      (mul_le_mul_of_nonneg_right hdeltaReferenceLe (by positivity))
  have hsRaw : (S.card : ℝ) ≤
      criticalFineBalanceSparseFraction k * (n : ℝ) :=
    hsSmall.trans
      (mul_le_mul_of_nonneg_right hdeltaRawLe (by positivity))
  have href := hnReference hn S hsReference
  have hbound :=
    criticalFixedSparseUnbalancedCleanGraphFinset_card_le_of_remainders
      hk tau hn hnTwo S hsRaw (2 * (k - 1).factorial : ℝ)
      (fun R hR ↦ by
        have h := href R hR
        simpa only [SimpleGraph.edgeFinset_card,
          ← Nat.card_eq_fintype_card] using h)
  simpa only [criticalFineBalanceError] using hbound

/-- Conditional-probability consequence of
`criticalFixedSparseFineBalanceK1k`.  The only extra hypothesis is eventual
nonemptiness of the exact canonical clean conditioning family along the
chosen sequence of sparse sets. -/
theorem criticalFixedSparseFineBalanceFailureProbability_tendsto_zero
    (k : ℕ) (hk : 3 ≤ k) {tauCap : ℝ} (hCap : 0 < tauCap) :
    ∃ tau delta : ℝ,
      0 < tau ∧ tau ≤ tauCap ∧ 0 < delta ∧
        ∀ S : ∀ n : ℕ, Finset (Fin n),
          (∀ᶠ n : ℕ in atTop,
            ((S n).card : ℝ) ≤ delta * (n : ℝ)) →
          (∀ᶠ n : ℕ in atTop, ∀ hn : k - 1 ≤ n,
            (criticalCanonicalCleanFixedSparseGraphFinset
              k hk n tau hn (S n)).Nonempty) →
          Tendsto
            (fun n ↦ criticalFixedSparseFineBalanceFailureProbability
              k hk tau n (S n)) atTop (nhds 0) := by
  obtain ⟨tau, delta, htau, htauCap, hdelta, e, he,
      heNonneg, hcard⟩ := criticalFixedSparseFineBalanceK1k k hk hCap
  refine ⟨tau, delta, htau, htauCap, hdelta, ?_⟩
  intro S hsSmall hne
  have hlarge : ∀ᶠ n : ℕ in atTop, k - 1 ≤ n :=
    eventually_ge_atTop (k - 1)
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ criticalFixedSparseFineBalanceFailureProbability
        k hk tau n (S n) := by
    filter_upwards [hlarge, hne] with n hn hnNonempty
    rw [criticalFixedSparseFineBalanceFailureProbability, dif_pos hn]
    apply uniformSubfamilyProbability_nonneg (hnNonempty hn)
    intro G hG
    exact (mem_criticalFixedSparseUnbalancedCleanGraphFinset.mp hG).1
  have hupper : ∀ᶠ n : ℕ in atTop,
      criticalFixedSparseFineBalanceFailureProbability
          k hk tau n (S n) ≤ e n := by
    filter_upwards [hlarge, hsSmall, hne, hcard] with
      n hn hnSmall hnNonempty hnCard
    exact criticalFixedSparseFineBalanceFailureProbability_le_of_card_le
      k hk tau n hn (S n) (hnNonempty hn) (hnCard hn (S n) hnSmall)
  exact squeeze_zero' hnonneg hupper he

end InducedStars
