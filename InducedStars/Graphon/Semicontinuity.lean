import InducedStars.Graphon.Counting
import InducedStars.Graphon.RelativeEntropy
import InducedStars.PriorInstances

/-!
# Semicontinuity and cut-closed graphon constraints

This file wraps the published sequential entropy semicontinuity input and
derives the corresponding lower semicontinuity of graphon relative entropy.
It also records the two cut-sequential closure lemmas needed by the rough
structure argument.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- Entropy is upper semicontinuous along cut-convergent graphon sequences
when supplied with the exact theorem-valued semicontinuity input. -/
theorem graphonEntropy_eventually_le_of_cutDist_tendsto_zero_withInput
    (input : DenseGraph.EntropySemicontinuityInput)
    (Wseq : ℕ → Graphon) (W : Graphon)
    (hcut : Tendsto (fun n ↦ cutDist (Wseq n) W) atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      graphonEntropy (Wseq n) ≤ graphonEntropy W + ε :=
  input.eventually_le Wseq W hcut ε hε

/-- Entropy is upper semicontinuous along cut-convergent graphon sequences,
in the epsilon-eventual form used by compactness arguments. -/
theorem graphonEntropy_eventually_le_of_cutDist_tendsto_zero
    (Wseq : ℕ → Graphon) (W : Graphon)
    (hcut : Tendsto (fun n ↦ cutDist (Wseq n) W) atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      graphonEntropy (Wseq n) ≤ graphonEntropy W + ε :=
  graphonEntropy_eventually_le_of_cutDist_tendsto_zero_withInput
    PriorInstances.entropySemicontinuityInput Wseq W hcut hε

/-- For an interior reference density, graphon relative entropy is lower
semicontinuous along cut-convergent sequences when supplied with the exact
entropy-semicontinuity input.  This is derived locally from entropy
semicontinuity and cut-continuity of edge density. -/
theorem graphonRelativeEntropy_eventually_ge_of_cutDist_tendsto_zero_withInput
    (input : DenseGraph.EntropySemicontinuityInput)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (Wseq : ℕ → Graphon) (W : Graphon)
    (hcut : Tendsto (fun n ↦ cutDist (Wseq n) W) atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      graphonRelativeEntropy p W - ε ≤
        graphonRelativeEntropy p (Wseq n) := by
  let c : ℝ := log2 ((1 - p) / p)
  have hedge : Tendsto
      (fun n ↦ graphonEdgeDensity (Wseq n) * c) atTop
      (nhds (graphonEdgeDensity W * c)) :=
    (graphonEdgeDensity_tendsto_of_cutDist_tendsto_zero Wseq W hcut).mul_const c
  have hedgeLower : ∀ᶠ n in atTop,
      graphonEdgeDensity W * c - ε / 2 <
        graphonEdgeDensity (Wseq n) * c :=
    (tendsto_order.mp hedge).1 _ (sub_lt_self _ (half_pos hε))
  have hentropy :=
    graphonEntropy_eventually_le_of_cutDist_tendsto_zero_withInput
      input Wseq W hcut (half_pos hε)
  filter_upwards [hentropy, hedgeLower] with n hnEntropy hnEdge
  rw [graphonRelativeEntropy_eq_negEntropy_add_edge hp W,
    graphonRelativeEntropy_eq_negEntropy_add_edge hp (Wseq n)]
  dsimp only [c] at hnEdge
  linarith

/-- For an interior reference density, graphon relative entropy is lower
semicontinuous along cut-convergent sequences.  This is derived locally from
the published entropy-semicontinuity input and cut-continuity of edge density. -/
theorem graphonRelativeEntropy_eventually_ge_of_cutDist_tendsto_zero
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (Wseq : ℕ → Graphon) (W : Graphon)
    (hcut : Tendsto (fun n ↦ cutDist (Wseq n) W) atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      graphonRelativeEntropy p W - ε ≤
        graphonRelativeEntropy p (Wseq n) :=
  graphonRelativeEntropy_eventually_ge_of_cutDist_tendsto_zero_withInput
    PriorInstances.entropySemicontinuityInput hp Wseq W hcut hε

/-- The fixed-density induced-star-free feasible set is sequentially closed
for cut convergence. -/
theorem mem_fixedDensityFeasible_of_cutDist_tendsto_zero
    {k : ℕ} {γ : ℝ} (Wseq : ℕ → Graphon) (W : Graphon)
    (hWseq : ∀ n, Wseq n ∈ fixedDensityFeasible k γ)
    (hcut : Tendsto (fun n ↦ cutDist (Wseq n) W) atTop (nhds 0)) :
    W ∈ fixedDensityFeasible k γ := by
  constructor
  · have hlimit := graphonInducedDensity_tendsto_of_cutDist_tendsto_zero
      (inducedStar k) Wseq W hcut
    have hzero : Tendsto
        (fun n ↦ graphonInducedDensity (inducedStar k) (Wseq n))
        atTop (nhds 0) := by
      apply tendsto_const_nhds.congr'
      exact Eventually.of_forall fun n ↦ (hWseq n).1.symm
    exact tendsto_nhds_unique hlimit hzero
  · have hlimit :=
      graphonEdgeDensity_tendsto_of_cutDist_tendsto_zero Wseq W hcut
    have hdensity : Tendsto
        (fun n ↦ graphonEdgeDensity (Wseq n)) atTop (nhds γ) := by
      apply tendsto_const_nhds.congr'
      exact Eventually.of_forall fun n ↦ (hWseq n).2.symm
    exact tendsto_nhds_unique hlimit hdensity

/-- The induced-star-free graphon set is sequentially closed for cut
convergence. -/
theorem mem_inducedStarFreeGraphons_of_cutDist_tendsto_zero
    {k : ℕ} (Wseq : ℕ → Graphon) (W : Graphon)
    (hWseq : ∀ n, Wseq n ∈ inducedStarFreeGraphons k)
    (hcut : Tendsto (fun n ↦ cutDist (Wseq n) W) atTop (nhds 0)) :
    W ∈ inducedStarFreeGraphons k := by
  have hlimit := graphonInducedDensity_tendsto_of_cutDist_tendsto_zero
    (inducedStar k) Wseq W hcut
  have hzero : Tendsto
      (fun n ↦ graphonInducedDensity (inducedStar k) (Wseq n))
      atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun n ↦ (hWseq n).symm
  exact tendsto_nhds_unique hlimit hzero

end InducedStars
