import InducedStars.C4.SplitColorings
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast

/-!
# A quadratic lower bound for the complete C4 entropy benchmark

Paper: `eqn:Phi0-LB`. The construction uses a complete split template with
`floor (gamma*n)` blue vertices. Feasibility is proved
before this template is admitted to the benchmark.
-/

noncomputable section
open Filter Set Topology
namespace InducedStars

theorem c4_choose_normalized_tendsto {b : ℕ → ℕ} {x : ℝ}
    (hb : Tendsto (fun n ↦ (b n : ℝ) / n) atTop (𝓝 x)) :
    Tendsto (fun n ↦ (Nat.choose (b n) 2 : ℝ) / (n : ℝ)^2)
      atTop (𝓝 (x^2/2)) := by
  have hi : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := (hb.mul (hb.sub hi)).div_const 2
  simp only [sub_zero, ← sq] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Nat.cast_choose_two]
  field_simp

theorem c4_cross_normalized_tendsto {b : ℕ → ℕ} {x : ℝ}
    (hbn : ∀ᶠ n in atTop, b n ≤ n)
    (hb : Tendsto (fun n ↦ (b n : ℝ) / n) atTop (𝓝 x)) :
    Tendsto (fun n ↦ ((n - b n) * b n : ℕ) / (n : ℝ)^2)
      atTop (𝓝 (x*(1-x))) := by
  have h := hb.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hb)
  apply h.congr'
  filter_upwards [hbn, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Nat.cast_mul, Nat.cast_sub hn]
  field_simp

theorem c4_complete_normalized_tendsto :
    Tendsto (fun n ↦ (completeEdgeCount n : ℝ) / (n : ℝ)^2)
      atTop (𝓝 (1/2)) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℝ) / n) atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (div_self (by exact_mod_cast (show n ≠ 0 by omega))).symm
  simpa [completeEdgeCount] using c4_choose_normalized_tendsto h

theorem c4_floor_clique_le {gamma : ℝ} (hgamma : gamma ∈ Icc 0 1) (n : ℕ) :
    ⌊gamma * n⌋₊ ≤ n := by
  apply Nat.floor_le_of_le
  exact mul_le_of_le_one_left (Nat.cast_nonneg n) hgamma.2

theorem c4_floor_split_capacity_tendsto {gamma : ℝ} (hgamma : gamma ∈ Ioo 0 1) :
    Tendsto (fun n : ℕ ↦ ((n - ⌊gamma * n⌋₊) * ⌊gamma * n⌋₊ : ℕ) / (n : ℝ)^2)
      atTop (𝓝 (gamma * (1-gamma))) := by
  apply c4_cross_normalized_tendsto
  · exact Eventually.of_forall (c4_floor_clique_le ⟨hgamma.1.le, hgamma.2.le⟩)
  · exact (tendsto_nat_floor_mul_div_atTop hgamma.1.le).comp tendsto_natCast_atTop_atTop

/-- The blue count and the density target give asymptotic red density one
half for the floor-gamma split construction. -/
theorem c4_floor_split_density_tendsto {gamma : ℝ} (hgamma : gamma ∈ Ioo 0 1) :
    Tendsto (fun n : ℕ ↦
      (gamma * completeEdgeCount n - Nat.choose ⌊gamma * n⌋₊ 2) /
        (((n - ⌊gamma * n⌋₊) * ⌊gamma * n⌋₊ : ℕ) : ℝ)) atTop (𝓝 (1/2)) := by
  have hb := (tendsto_nat_floor_mul_div_atTop hgamma.1.le).comp
    tendsto_natCast_atTop_atTop
  have hB := c4_choose_normalized_tendsto hb
  have hR := c4_floor_split_capacity_tendsto hgamma
  have hp : 0 < gamma*(1-gamma) := mul_pos hgamma.1 (sub_pos.mpr hgamma.2)
  have h := ((c4_complete_normalized_tendsto.const_mul gamma).sub hB).div hR hp.ne'
  have hv : (gamma * (1/2) - gamma^2/2) / (gamma*(1-gamma)) = 1/2 := by
    apply (div_eq_iff hp.ne').mpr
    ring
  rw [hv] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [Pi.div_apply, ← mul_div_assoc, ← sub_div]
  rw [div_div_div_cancel_right₀ (pow_ne_zero 2 hn0)]

theorem c4_floor_split_eventually_feasible {gamma : ℝ}
    (hgamma : gamma ∈ Ioo 0 1) :
    ∀ᶠ n in atTop, C4ColoredEntropyFeasible
      (c4SplitColoring (c4DivisionOfCliqueSize n ⌊gamma*n⌋₊)) gamma := by
  have hp : 0 < gamma*(1-gamma) := mul_pos hgamma.1 (sub_pos.mpr hgamma.2)
  have hR := (c4_floor_split_capacity_tendsto hgamma).eventually (lt_mem_nhds hp)
  have hq := (c4_floor_split_density_tendsto hgamma).eventually
    (Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1))
  filter_upwards [hR, hq] with n hR hq
  have hcap : 0 < (((n - ⌊gamma*n⌋₊)*⌊gamma*n⌋₊ : ℕ) : ℝ) :=
    (div_pos_iff.mp hR).resolve_right (by rintro ⟨_, h⟩; nlinarith [sq_nonneg (n : ℝ)]) |>.1
  have hb := c4_floor_clique_le ⟨hgamma.1.le, hgamma.2.le⟩ n
  unfold C4ColoredEntropyFeasible
  simp only [c4SplitColoring_red_count, c4SplitColoring_blue_count,
    c4DivisionOfCliqueSize_clique_card hb, c4DivisionOfCliqueSize_independent_card hb]
  refine ⟨hcap.le, ?_, ?_⟩
  · have := (div_pos_iff_of_pos_right hcap).mp hq.1
    linarith
  · have := (div_lt_one hcap).mp hq.2
    linarith

theorem c4_floor_split_entropy_tendsto {gamma : ℝ} (hgamma : gamma ∈ Ioo 0 1) :
    Tendsto (fun n : ℕ ↦
      ((((n - ⌊gamma*n⌋₊)*⌊gamma*n⌋₊ : ℕ) : ℝ) *
        binaryEntropy ((gamma*completeEdgeCount n - Nat.choose ⌊gamma*n⌋₊ 2) /
          (((n - ⌊gamma*n⌋₊)*⌊gamma*n⌋₊ : ℕ) : ℝ))) / (n : ℝ)^2)
      atTop (𝓝 (gamma*(1-gamma))) := by
  have h := (c4_floor_split_capacity_tendsto hgamma).mul
    (binaryEntropy_continuous.continuousAt.tendsto.comp (c4_floor_split_density_tendsto hgamma))
  have hhalf : binaryEntropy (1/2) = 1 := by
    rw [binaryEntropy, one_div, Real.binEntropy_two_inv, div_self realLogTwo_ne_zero]
  rw [hhalf, mul_one] at h
  convert! h using 1
  funext n
  simp only [Function.comp_apply, div_mul_eq_mul_div]

/-- Paper: `eqn:Phi0-LB`, with the complete-template benchmark. -/
theorem eventually_c4CompleteEntropyBenchmark_lower {gamma : ℝ}
    (hgamma : gamma ∈ Ioo 0 1) :
    ∀ᶠ n : ℕ in atTop, gamma*(1-gamma)/4*(n : ℝ)^2 ≤
      c4CompleteEntropyBenchmark n gamma := by
  have hp : 0 < gamma*(1-gamma) := mul_pos hgamma.1 (sub_pos.mpr hgamma.2)
  have hE := (c4_floor_split_entropy_tendsto hgamma).eventually
    (lt_mem_nhds (show gamma*(1-gamma)/4 < gamma*(1-gamma) by linarith))
  filter_upwards [c4_floor_split_eventually_feasible hgamma, hE,
    eventually_ge_atTop 1] with n hf hE hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := c4SplitColoring_entropy_le_benchmark
    (c4DivisionOfCliqueSize n ⌊gamma*n⌋₊) gamma hf
  have hb := c4_floor_clique_le ⟨hgamma.1.le, hgamma.2.le⟩ n
  simp only [c4DivisionOfCliqueSize_clique_card hb,
    c4DivisionOfCliqueSize_independent_card hb, Nat.cast_mul] at h hE
  exact le_trans ((lt_div_iff₀ (sq_pos_of_pos hn0)).mp hE).le h

end InducedStars
