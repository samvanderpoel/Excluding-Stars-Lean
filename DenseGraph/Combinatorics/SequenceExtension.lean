import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Extending natural-valued convergent subsequences

A natural-valued sequence prescribed on a strictly increasing subsequence
can be filled at the remaining indices while preserving its normalized
limit.  This allows sequential finite-model estimates to be upgraded to
uniform estimates on compact parameter ranges.
-/

noncomputable section

open Filter Set Topology

namespace DenseGraph

/-- Flooring a nonnegative multiple of a diverging scale preserves the
normalized limit, including a zero multiplier. -/
theorem natFloor_mul_div_tendsto
    {D : ℕ → ℝ} (hD : Tendsto D atTop atTop) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n ↦ (⌊x * D n⌋₊ : ℝ) / D n) atTop (𝓝 x) := by
  have hp := hD.eventually (eventually_gt_atTop (0 : ℝ))
  have he : Tendsto (fun n ↦ x - (⌊x * D n⌋₊ : ℝ) / D n) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ (tendsto_const_nhds.div_atTop hD :
      Tendsto (fun n ↦ (1 : ℝ) / D n) atTop (𝓝 0))
    · filter_upwards [hp] with n hn
      have h := Nat.floor_le (mul_nonneg hx hn.le)
      exact sub_nonneg.mpr ((div_le_iff₀ hn).mpr h)
    · filter_upwards [hp] with n hn
      have h := Nat.lt_floor_add_one (x * D n)
      apply (le_div_iff₀ hn).mpr
      have heq : (x - (⌊x * D n⌋₊ : ℝ) / D n) * D n =
          x * D n - (⌊x * D n⌋₊ : ℝ) := by field_simp
      rw [heq]
      linarith
  simpa only [sub_zero, sub_sub_cancel] using (tendsto_const_nhds (x := x)).sub he

/-- Extension of a normalized natural-valued subsequence.  The prescribed
values are retained exactly, and no monotonicity of the normalization is
required. -/
theorem exists_natSequence_extension_of_div_tendsto
    {D : ℕ → ℝ} (hD : Tendsto D atTop atTop)
    {u g : ℕ → ℕ} (hg : StrictMono g) {x : ℝ} (hx : 0 ≤ x)
    (hu : Tendsto (fun j ↦ (u j : ℝ) / D (g j)) atTop (𝓝 x)) :
    ∃ v : ℕ → ℕ, (∀ j, v (g j) = u j) ∧
      Tendsto (fun n ↦ (v n : ℝ) / D n) atTop (𝓝 x) := by
  classical
  let v : ℕ → ℕ := fun n ↦
    if n ∈ Set.range g then u (Function.invFun g n) else ⌊x * D n⌋₊
  have hmatch : ∀ j, v (g j) = u j := by
    intro j
    simp only [v, Set.mem_range_self, ↓reduceIte, Function.leftInverse_invFun hg.injective j]
  refine ⟨v, hmatch, Metric.tendsto_nhds.mpr ?_⟩
  intro epsilon hepsilon
  rcases eventually_atTop.1 (Metric.tendsto_nhds.mp hu epsilon hepsilon) with ⟨J, hJ⟩
  rcases eventually_atTop.1
    (Metric.tendsto_nhds.mp (natFloor_mul_div_tendsto hD hx) epsilon hepsilon) with ⟨N, hN⟩
  refine eventually_atTop.mpr ⟨max (g J) N, ?_⟩
  intro n hn
  by_cases hm : n ∈ Set.range g
  · rcases hm with ⟨j, rfl⟩
    rw [hmatch]
    apply hJ j
    exact hg.le_iff_le.mp ((le_max_left _ _).trans hn)
  · simp only [v, hm, ↓reduceIte]
    exact hN n ((le_max_right _ _).trans hn)

/-- Replacing a natural sequence by its maximum with one does not alter a
normalized limit on a diverging scale. -/
theorem max_one_div_tendsto
    {D : ℕ → ℝ} (hD : Tendsto D atTop atTop) {v : ℕ → ℕ} {x : ℝ}
    (hv : Tendsto (fun n ↦ (v n : ℝ) / D n) atTop (𝓝 x)) :
    Tendsto (fun n ↦ (max 1 (v n) : ℕ) / D n) atTop (𝓝 x) := by
  have hp := hD.eventually (eventually_gt_atTop (0 : ℝ))
  have he : Tendsto (fun n ↦ ((max 1 (v n) : ℕ) - (v n : ℝ)) / D n)
      atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ (tendsto_const_nhds.div_atTop hD :
      Tendsto (fun n ↦ (1 : ℝ) / D n) atTop (𝓝 0))
    · filter_upwards [hp] with n hn
      apply div_nonneg ?_ hn.le
      have hh : (v n : ℝ) ≤ (max 1 (v n) : ℕ) := by exact_mod_cast (le_max_right 1 (v n))
      linarith
    · filter_upwards [hp] with n hn
      apply div_le_div_of_nonneg_right ?_ hn.le
      have hh : (max 1 (v n) : ℕ) ≤ v n + 1 := by omega
      have hh' : (max 1 (v n) : ℕ) ≤ (v n : ℝ) + 1 := by exact_mod_cast hh
      linarith
  have h := hv.add he
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards with n
  ring

/-- A positive prescribed subsequence has an everywhere positive extension
with the same normalized limit. -/
theorem exists_positive_natSequence_extension_of_div_tendsto
    {D : ℕ → ℝ} (hD : Tendsto D atTop atTop)
    {u g : ℕ → ℕ} (hg : StrictMono g) {x : ℝ} (hx : 0 ≤ x)
    (hupos : ∀ j, 1 ≤ u j)
    (hu : Tendsto (fun j ↦ (u j : ℝ) / D (g j)) atTop (𝓝 x)) :
    ∃ v : ℕ → ℕ, (∀ j, v (g j) = u j) ∧ (∀ n, 1 ≤ v n) ∧
      Tendsto (fun n ↦ (v n : ℝ) / D n) atTop (𝓝 x) := by
  rcases exists_natSequence_extension_of_div_tendsto hD hg hx hu with ⟨v, hv, hvlim⟩
  refine ⟨fun n ↦ max 1 (v n), ?_, fun _ ↦ le_max_left _ _, max_one_div_tendsto hD hvlim⟩
  intro j
  change max 1 (v (g j)) = u j
  rw [hv j, max_eq_right (hupos j)]

end DenseGraph
