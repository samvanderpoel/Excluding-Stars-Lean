import InducedStars.C4.NondegenerateFamilies

/-!
# Uniform entropy loss for degenerate split fibers

The finite fiber is evaluated at its actual perturbed feasible
density, including the clique diagonal and the signed edge-count shift.
Continuity of the optimizer and of the optimal entropy then preserves a
fixed quadratic gap. No uniform endpoint derivative estimate is used.
-/

noncomputable section
namespace InducedStars
open Filter Set
open scoped Topology

/-- A uniform neighborhood of the density preserves a strict
entropy loss outside any fixed neighborhood of the original optimizer. -/
theorem exists_c4Split_degenerate_entropy_window {gamma zeta : ℝ}
    (hgamma : gamma ∈ Ioo 0 1) (hzeta : 0 < zeta) :
    ∃ delta gap : ℝ, 0 < delta ∧ 0 < gap ∧
      ∀ d : ℝ, |d-gamma| < delta → d ∈ Ioo 0 1 ∧
        ∀ x ∈ Icc (1-Real.sqrt (1-d)) (Real.sqrt d),
          zeta ≤ |x-c4Lambda gamma| →
            c4SplitEntropyNat d x ≤ c4SplitEntropyNat gamma (c4Lambda gamma)-gap := by
  let gap := Real.log 2*zeta^2/8
  have hgap : 0 < gap := by dsimp [gap]; positivity
  have hmem : ∀ᶠ d in 𝓝 gamma, d ∈ Ioo 0 1 := isOpen_Ioo.mem_nhds hgamma
  have hL : ∀ᶠ d in 𝓝 gamma, |c4Lambda d-c4Lambda gamma| < zeta/2 := by
    simpa only [Real.dist_eq] using (analyticAt_c4Lambda hgamma).continuousAt.eventually
      (Metric.ball_mem_nhds _ (by positivity))
  have hE : ∀ᶠ d in 𝓝 gamma,
      c4SplitEntropyNat d (c4Lambda d) < c4SplitEntropyNat gamma (c4Lambda gamma)+gap :=
    (analyticAt_c4SplitEntropyNat_optimizer hgamma).continuousAt.eventually
      (gt_mem_nhds (by linarith))
  obtain ⟨delta, hdelta, hw⟩ := Metric.eventually_nhds_iff.mp (hmem.and (hL.and hE))
  refine ⟨delta, gap, hdelta, hgap, ?_⟩
  intro d hd
  obtain ⟨hd, hL, hE⟩ := hw (by simpa only [Real.dist_eq] using hd)
  refine ⟨hd, ?_⟩
  intro x hx hfar
  have htriangle := abs_sub_le x (c4Lambda d) (c4Lambda gamma)
  have hsep : zeta/2 ≤ |x-c4Lambda d| := by linarith
  have hsquare : zeta^2/4 ≤ (x-c4Lambda d)^2 := by
    nlinarith [sq_abs (x-c4Lambda d)]
  have hquad := c4SplitEntropyNat_quadratic_gap hd hx
  have hmul := mul_le_mul_of_nonneg_left hsquare (Real.log_pos (by norm_num : (1 : ℝ)<2)).le
  dsimp [gap] at hE ⊢
  nlinarith

/-- Uniform finite shifted-density fiber estimate. The constants
are chosen before the edge-count sequence; both signs of its finite shift
are covered by the same absolute-value hypothesis. -/
theorem eventually_c4DegenerateShiftedSplitFiber_le {gamma zeta delta gap epsilon : ℝ}
    (hdelta : 0 < delta) (hepsilon : 0 ≤ epsilon) (hepsdelta : epsilon ≤ delta/8)
    (hwindow : ∀ d : ℝ, |d-gamma| < delta → d ∈ Ioo 0 1 ∧
      ∀ x ∈ Icc (1-Real.sqrt (1-d)) (Real.sqrt d), zeta ≤ |x-c4Lambda gamma| →
        c4SplitEntropyNat d x ≤ c4SplitEntropyNat gamma (c4Lambda gamma)-gap)
    {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n in atTop, ∀ D ∈ c4DegenerateDivisions n gamma zeta,
      ∀ j ∈ c4SplitRepairEdgeWindow n (m n) ⌊epsilon*(n : ℝ)^2⌋₊,
        ((c4SplitFiber D j).card : ℝ) ≤
          Real.exp ((c4SplitEntropyNat gamma (c4Lambda gamma)-gap)*(n : ℝ)^2) := by
  have hmclose : ∀ᶠ n in atTop, |2*(m n : ℝ)/(n : ℝ)^2-gamma| < delta/4 := by
    simpa only [Real.dist_eq] using (hasAsymptoticEdgeDensity_orderedSquare hm).eventually
      (Metric.ball_mem_nhds gamma (by positivity))
  have hinv : ∀ᶠ n : ℕ in atTop, (1 : ℝ)/n < delta/4 :=
    tendsto_one_div_atTop_nhds_zero_nat.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hmclose, hinv, eventually_ge_atTop 1] with n hmclose hinv hn D hD j hj
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnSq := sq_pos_of_pos hnR
  have hshift : |(j : ℝ)-(m n : ℝ)| ≤ epsilon*(n : ℝ)^2 := by
    have h := (Finset.mem_filter.mp hj).2
    exact h.trans (Nat.floor_le (by positivity))
  let b := D.cliquePart.card
  have hparts : D.independentPart.card+b=n := by simpa [b] using D.card_add
  have hb : b ≤ n := by omega
  have hA : D.independentPart.card=n-b := by omega
  have hbR : (b : ℝ) ≤ n := by exact_mod_cast hb
  have hbsmall : 0 ≤ (b : ℝ)/(n : ℝ)^2 ∧ (b : ℝ)/(n : ℝ)^2 ≤ 1/n := by
    refine ⟨by positivity, ?_⟩
    apply (div_le_iff₀ hnSq).mpr
    field_simp
    nlinarith
  have hshiftNorm : |2*((j : ℝ)-(m n : ℝ))/(n : ℝ)^2| ≤ 2*epsilon := by
    rw [abs_div, abs_mul, abs_of_pos hnSq, abs_of_pos (by norm_num : (0 : ℝ)<2)]
    apply (div_le_iff₀ hnSq).mpr
    nlinarith
  have hdnear : |(2*(j : ℝ)+b)/(n : ℝ)^2-gamma| < delta := by
    have htri := abs_add_le (2*(m n : ℝ)/(n : ℝ)^2-gamma)
      (2*((j : ℝ)-(m n : ℝ))/(n : ℝ)^2)
    have htri' := abs_add_le
      ((2*(m n : ℝ)/(n : ℝ)^2-gamma)+(2*((j : ℝ)-(m n : ℝ))/(n : ℝ)^2))
      ((b : ℝ)/(n : ℝ)^2)
    rw [abs_of_nonneg hbsmall.1] at htri'
    have heq : (2*(j : ℝ)+b)/(n : ℝ)^2-gamma =
        ((2*(m n : ℝ)/(n : ℝ)^2-gamma)+(2*((j : ℝ)-(m n : ℝ))/(n : ℝ)^2))+
        (b : ℝ)/(n : ℝ)^2 := by ring
    rw [heq]
    linarith
  obtain ⟨hdensity, hgap⟩ := hwindow _ hdnear
  have hfar : zeta ≤ |(b : ℝ)/n-c4Lambda gamma| := by
    have hdeg := (Finset.mem_filter.mp hD).2
    have hnorm : |(b : ℝ)/n-c4Lambda gamma| =
        |(b : ℝ)-c4Lambda gamma*n|/n := by
      calc
        _ = |((b : ℝ)-c4Lambda gamma*n)/n| := by congr 1; field_simp
        _ = _ := by rw [abs_div, abs_of_pos hnR]
    rw [hnorm]
    exact ((le_div_iff₀ hnR).mpr hdeg.le)
  rw [card_c4SplitFiber, hA]
  change ((if b.choose 2 ≤ j then Nat.choose ((n-b)*b) (j-b.choose 2) else 0 : ℕ) : ℝ) ≤ _
  split_ifs with hbm
  · by_cases hcap : j-b.choose 2 ≤ (n-b)*b
    · apply (DenseGraph.choose_le_exp_binomialEntropyPerspective hcap).trans
      apply Real.exp_le_exp.mpr
      have hx := c4_finite_cliqueFraction_feasible hnpos hb hbm hcap hdensity
      have hscalar := hgap _ hx hfar
      rw [← c4_split_binomialEntropy_normalized hnpos hb hbm] at hscalar
      exact (div_le_iff₀ hnSq).mp hscalar
    · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hcap), Nat.cast_zero]
      exact (Real.exp_pos _).le
  · simp only [Nat.cast_zero]
    exact (Real.exp_pos _).le

end InducedStars
