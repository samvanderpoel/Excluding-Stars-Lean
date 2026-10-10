import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Sequential uniformity near a limiting density

A limit along every feasible density-convergent sequence gives a uniform
estimate in some fixed density window, after some fixed order threshold.
The reference sequence fills the orders omitted by a counterexample
subsequence.  No finiteness, compactness, or quantitative convergence rate
of the feasible fibers is needed.
-/

open Filter
open scoped Topology

namespace DenseGraph

/-- Fill the missing orders of a strictly increasing subsequence using a
feasible reference sequence.  Convergence of the density is preserved. -/
theorem exists_feasible_density_sequence_extension
    {α : Type*} (feasible : ℕ → α → Prop) (density : ℕ → α → ℝ)
    {γ : ℝ} (reference : ℕ → α)
    (hreference : ∀ n, feasible n (reference n))
    (hreference_lim : Tendsto (fun n ↦ density n (reference n)) atTop (𝓝 γ))
    (orders : ℕ → ℕ) (horders : StrictMono orders) (values : ℕ → α)
    (hvalues : ∀ j, feasible (orders j) (values j))
    (hvalues_lim : Tendsto (fun j ↦ density (orders j) (values j)) atTop (𝓝 γ)) :
    ∃ sequence : ℕ → α,
      (∀ n, feasible n (sequence n)) ∧
      (∀ j, sequence (orders j) = values j) ∧
      Tendsto (fun n ↦ density n (sequence n)) atTop (𝓝 γ) := by
  classical
  let sequence : ℕ → α := fun n ↦
    if h : ∃ j, orders j = n then values h.choose else reference n
  have hselected (j : ℕ) : sequence (orders j) = values j := by
    have hex : ∃ i, orders i = orders j := ⟨j, rfl⟩
    simp only [sequence, dite_eq_left hex]
    congr 1
    exact horders.injective hex.choose_spec
  refine ⟨sequence, ?_, hselected, ?_⟩
  · intro n
    by_cases hn : ∃ j, orders j = n
    · rw [← hn.choose_spec, hselected]
      exact hvalues _
    · simpa only [sequence, dite_eq_right hn] using hreference n
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hreference_lim ε hε
    obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hvalues_lim ε hε
    refine ⟨max N (orders J), fun n hn ↦ ?_⟩
    by_cases hselected_n : ∃ j, orders j = n
    · obtain ⟨j, rfl⟩ := hselected_n
      rw [hselected]
      exact hJ j (horders.le_iff_le.mp ((le_max_right _ _).trans hn))
    · simpa only [sequence, dite_eq_right hselected_n] using
        hN n ((le_max_left _ _).trans hn)

/-- If an error tends to zero along every feasible sequence whose density
tends to `γ`, then it is uniformly small in some density neighborhood of
`γ` at all sufficiently large orders.  The window and threshold may depend
on the error tolerance, but not on the point in the feasible fiber. -/
theorem exists_densityWindow_of_tendsto_along_feasible_sequences
    {α : Type*} (feasible : ℕ → α → Prop)
    (density error : ℕ → α → ℝ) {γ : ℝ}
    (reference : ℕ → α)
    (hreference : ∀ n, feasible n (reference n))
    (hreference_lim : Tendsto (fun n ↦ density n (reference n)) atTop (𝓝 γ))
    (hsequential : ∀ sequence : ℕ → α,
      (∀ n, feasible n (sequence n)) →
      Tendsto (fun n ↦ density n (sequence n)) atTop (𝓝 γ) →
      Tendsto (fun n ↦ error n (sequence n)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ a,
      feasible n a → |density n a - γ| < δ → error n a < ε := by
  classical
  by_contra h
  push Not at h
  have hbad : ∀ j : ℕ, ∃ᶠ n in atTop, ∃ a,
      feasible n a ∧ |density n a - γ| < 1 / ((j : ℝ) + 1) ∧ ε ≤ error n a := by
    intro j
    rw [frequently_atTop]
    intro N
    obtain ⟨n, hn, a, ha, hd, he⟩ := h (1 / ((j : ℝ) + 1)) (by positivity) N
    exact ⟨n, hn, a, ha, hd, he⟩
  obtain ⟨orders, horders, hbad_orders⟩ := extraction_forall_of_frequently hbad
  choose values hvalues hdensity herror using hbad_orders
  have hvalues_lim : Tendsto (fun j ↦ density (orders j) (values j)) atTop (𝓝 γ) := by
    apply Metric.tendsto_atTop.mpr
    intro η hη
    obtain ⟨J, hJ⟩ := eventually_atTop.mp
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hη))
    exact ⟨J, fun j hj ↦ by simpa only [Real.dist_eq] using (hdensity j).trans (hJ j hj)⟩
  obtain ⟨sequence, hfeasible, hselected, hlim⟩ :=
    exists_feasible_density_sequence_extension feasible density reference hreference
      hreference_lim orders horders values hvalues hvalues_lim
  have hsmall := ((hsequential sequence hfeasible hlim).comp
    horders.tendsto_atTop).eventually (gt_mem_nhds hε)
  obtain ⟨j, hj⟩ := hsmall.exists
  have : error (orders j) (values j) < ε := by simpa only [Function.comp_apply, hselected] using hj
  exact (not_lt_of_ge (herror j)) this

end DenseGraph
