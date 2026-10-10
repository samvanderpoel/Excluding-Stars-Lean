import InducedStars.C4.TypeGrouping
import DenseGraph.Analysis.EntropyFeasibilityEnvelope

/-!
# The entropy gap for far lifted C4 templates

Paper: `eqn:entropy-gap` and `lemma:c4-rough-struc`. The complete-template
benchmark is compared with the feasible entropy envelope, including the
infeasible ideal-target case. The positive benchmark lower bound makes the latter harmless;
it is not asserted that a partial template's ideal target must be feasible.
-/

noncomputable section
open Filter Set InducedStars.Regularity InducedStars.Regularity.RegularityColoredGraph
open scoped Classical
namespace InducedStars

/-- Uniform ideal-target entropy gap for every far nearly complete partial
template. The infeasible reference envelope is zero by definition. -/
theorem exists_c4FarTemplate_entropy_gap {gamma epsilon : ℝ}
    (hgamma : gamma ∈ Ioo 0 1) (hepsilon : 0 < epsilon) :
    ∃ delta eta : ℝ, 0 < delta ∧ 0 < eta ∧ ∀ᶠ n : ℕ in atTop,
      ∀ J : RegularityColoredGraph (Fin n),
        ¬ColoredHomExists inducedC4 J →
        ((finiteGraphEdges J.graphᶜ).card : ℝ) ≤ eta*(n : ℝ)^2 →
        (∀ D : C4Division (Fin n),
          epsilon*(n : ℝ)^2 ≤ DenseGraph.coloredEditDistance J (c4SplitColoring D)) →
        DenseGraph.feasibleEntropyEnvelope (c4ColorEdgeCount J .red)
            (c4ColorEdgeCount J .blue) (gamma*completeEdgeCount n) ≤
          c4CompleteEntropyBenchmark n gamma - delta*(n : ℝ)^2 := by
  obtain ⟨d, eta, hd, heta, n0, hstable⟩ :=
    c4ColoredStability hgamma (epsilon/2) (half_pos hepsilon)
  let delta := min d (gamma*(1-gamma)/8)
  have hgap : 0 < delta := lt_min hd (by
    have := mul_pos hgamma.1 (sub_pos.mpr hgamma.2)
    positivity)
  refine ⟨delta, eta, hgap, heta, ?_⟩
  filter_upwards [eventually_ge_atTop n0, eventually_ge_atTop 1,
    eventually_c4CompleteEntropyBenchmark_lower hgamma] with n hn hnpos hbenchmark
  intro J hfree hmissing hfar
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsquare := sq_pos_of_pos hnR
  by_cases hf : gamma*(completeEdgeCount n : ℝ) ∈
      Icc (c4ColorEdgeCount J .blue : ℝ)
        ((c4ColorEdgeCount J .blue : ℝ)+(c4ColorEdgeCount J .red : ℝ))
  · have hfeasible : C4ColoredEntropyFeasible J gamma := ⟨by positivity, hf.1, hf.2⟩
    have hlt : c4ColoredEntropy J gamma hfeasible <
        c4CompleteEntropyBenchmark n gamma - d*(n : ℝ)^2 := by
      by_contra h
      obtain ⟨D, hD⟩ := hstable n hn J hfree hmissing hfeasible (not_lt.mp h)
      have hF := hfar D
      have hp := mul_pos hepsilon hsquare
      nlinarith
    rw [DenseGraph.feasibleEntropyEnvelope_eq_of_mem hf,
      ← c4ColoredEntropy_eq J gamma hfeasible]
    exact hlt.le.trans (by
      have hh := mul_le_mul_of_nonneg_right (min_le_left d (gamma*(1-gamma)/8))
        hsquare.le
      dsimp only [delta]
      linarith)
  · rw [DenseGraph.feasibleEntropyEnvelope_eq_zero_of_not_mem hf]
    have hh := mul_le_mul_of_nonneg_right (min_le_right d (gamma*(1-gamma)/8))
      hsquare.le
    have hp := mul_pos hgamma.1 (sub_pos.mpr hgamma.2)
    dsimp only [delta]
    nlinarith [mul_nonneg hp.le hsquare.le]

end InducedStars
