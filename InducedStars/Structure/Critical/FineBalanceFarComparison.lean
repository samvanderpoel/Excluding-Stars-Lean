import DenseGraph.Combinatorics.ExponentialSums
import InducedStars.Structure.Critical.FiniteGeometry
import InducedStars.Main.AsymptoticConsequences

/-!
# Far-graph errors in the fixed-sparse critical comparison

The fine-balance calculation counts displayed clique covers, whereas the
paper's clean families also impose a cut-distance restriction.  The estimates
here express the existing far-family bound in the same natural-logarithm,
ordered-square normalization as the binomial reference count.  This lets the
close-family restriction be retained when a balanced reference fiber is used.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- Natural-logarithm entropy per ordered vertex square at critical density. -/
noncomputable def criticalNaturalEntropyExponent (k : ℕ) : ℝ :=
  entropyDensity k (gammaK k) * Real.log 2 / 2

/-- The completed exact-edge entropy theorem in the normalization used for
the critical binomial estimates. -/
theorem criticalTotal_log_div_sq_tendsto
    (k : ℕ) (hk : 3 ≤ k) :
    Tendsto
      (fun n : ℕ ↦ Real.log (criticalInducedStarFreeGraphCount k n : ℝ) /
        (n : ℝ) ^ 2)
      atTop (𝓝 (criticalNaturalEntropyExponent k)) := by
  have htotal := inducedStarFixedDensityEntropyAsymptotic k hk
    (gammaK k) ⟨gammaK_pos hk, gammaK_lt_one hk⟩
    (criticalEdgeCount k) (criticalEdgeCount_hasAsymptoticEdgeDensity hk)
  have hlimit := (htotal.mul
    completeEdgeCount_orderedSquareFactor_tendsto_one).mul_const
      (Real.log 2 / 2)
  have hlimit' : Tendsto
      (fun n : ℕ ↦ normalizedLogGraphCount n
          (inducedStarFreeGraphCountWithEdges k n (criticalEdgeCount k n)) *
        (2 * (completeEdgeCount n : ℝ) / (n : ℝ) ^ 2) *
          (Real.log 2 / 2))
      atTop (𝓝 (criticalNaturalEntropyExponent k)) := by
    simpa [criticalNaturalEntropyExponent, mul_div_assoc] using hlimit
  apply hlimit'.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hN : (completeEdgeCount n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hlog : Real.log 2 ≠ 0 := realLogTwo_pos.ne'
  change (Real.log (criticalInducedStarFreeGraphCount k n : ℝ) /
      Real.log 2 / (completeEdgeCount n : ℝ)) *
        (2 * (completeEdgeCount n : ℝ) / (n : ℝ) ^ 2) *
          (Real.log 2 / 2) = _
  field_simp

/-- Every positive entropy tolerance gives an eventual upper bound for the
entire critical conditioning family. -/
theorem eventually_criticalTotal_le_exp_entropy
    (k : ℕ) (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (criticalInducedStarFreeGraphCount k n : ℝ) ≤
        Real.exp ((criticalNaturalEntropyExponent k + ε) * (n : ℝ) ^ 2) := by
  have hupper := (tendsto_order.mp
    (criticalTotal_log_div_sq_tendsto k hk)).2
      (criticalNaturalEntropyExponent k + ε) (lt_add_of_pos_right _ hε)
  filter_upwards [hupper, eventually_ge_atTop 1] with n hn hnPos
  by_cases hzero : criticalInducedStarFreeGraphCount k n = 0
  · rw [hzero, Nat.cast_zero]
    exact (Real.exp_pos _).le
  have hcount : (0 : ℝ) < criticalInducedStarFreeGraphCount k n := by
    exact_mod_cast Nat.pos_of_ne_zero hzero
  apply (Real.log_le_iff_le_exp hcount).mp
  exact ((div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).mp hn).le

/-- The critical far family has a strict loss in its absolute entropy
exponent.  Both the gap and the threshold are independent of the sparse set
and of its induced graph. -/
theorem eventually_criticalFar_le_exp_entropy_gap
    (k : ℕ) (hk : 3 ≤ k) (τ : ℝ) (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ((criticalFarGraphFinset k hk n τ).card : ℝ) ≤
        Real.exp ((criticalNaturalEntropyExponent k - c) * (n : ℝ) ^ 2) := by
  obtain ⟨cFar, hcFar, hfar⟩ := eventually_criticalFarTotal_le k hk τ hτ
  refine ⟨cFar / 2, half_pos hcFar, ?_⟩
  filter_upwards [hfar,
    eventually_criticalTotal_le_exp_entropy k hk (half_pos hcFar)] with
      n hnFar hnTotal
  calc
    ((criticalFarGraphFinset k hk n τ).card : ℝ) ≤
        (criticalInducedStarFreeGraphCount k n : ℝ) *
          Real.exp (-cFar * (n : ℝ) ^ 2) := hnFar
    _ ≤ Real.exp ((criticalNaturalEntropyExponent k + cFar / 2) *
          (n : ℝ) ^ 2) * Real.exp (-cFar * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hnTotal (Real.exp_pos _).le
    _ = Real.exp ((criticalNaturalEntropyExponent k - cFar / 2) *
          (n : ℝ) ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Once a reference family retains half of the absolute entropy gap, even
counting each excluded far graph once for every division is negligible.
The statement is uniform over all reference counts satisfying the displayed
lower bound; it imposes no choice of a sparse set or a sparse graph. -/
theorem eventually_criticalFarPairs_le_reference_of_entropy
    (k : ℕ) (hk : 3 ≤ k) (τ : ℝ) (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ B : ℝ,
        Real.exp ((criticalNaturalEntropyExponent k - 2 * c) * (n : ℝ) ^ 2) ≤ B →
        ((k ^ n : ℕ) : ℝ) * ((criticalFarGraphFinset k hk n τ).card : ℝ) ≤
          B * Real.exp (-(c * (n : ℝ) ^ 2)) := by
  obtain ⟨d, hd, hfar⟩ := eventually_criticalFar_le_exp_entropy_gap k hk τ hτ
  refine ⟨d / 4, by positivity, ?_⟩
  filter_upwards [hfar,
    DenseGraph.eventually_pow_mul_exp_neg_sq_le k (half_pos hd)] with
      n hnFar hnPow B hB
  have hB' : Real.exp ((criticalNaturalEntropyExponent k - d / 2) *
      (n : ℝ) ^ 2) ≤ B := by convert hB using 1 <;> congr 2 <;> ring
  calc
    ((k ^ n : ℕ) : ℝ) * ((criticalFarGraphFinset k hk n τ).card : ℝ) ≤
        ((k ^ n : ℕ) : ℝ) *
          Real.exp ((criticalNaturalEntropyExponent k - d) * (n : ℝ) ^ 2) := by
      gcongr
    _ = Real.exp ((criticalNaturalEntropyExponent k - d / 2) * (n : ℝ) ^ 2) *
        (((k ^ n : ℕ) : ℝ) * Real.exp (-((d / 2) * (n : ℝ) ^ 2))) := by
      rw [← mul_assoc, mul_comm (Real.exp _) _, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ B * Real.exp (-((d / 4) * (n : ℝ) ^ 2)) := by
      apply mul_le_mul hB'
      · convert hnPow using 1 <;> congr 2 <;> ring
      · positivity
      · exact (Real.exp_pos _).le.trans hB'

end InducedStars
