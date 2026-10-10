import InducedStars.C4.BenchmarkLower
import InducedStars.C4.BenchmarkParameters
import InducedStars.C4.ColoredCounting
import InducedStars.C4.ColoredDistance

/-!
# Colored induced-C4 stability

Paper: Lemma `lemma:c4-stability`. The entropy benchmark uses complete
templates; the inputs may be nearly complete partial templates.
The third case uses an absolute clique-capacity comparison.
The split competitor is proved feasible before using benchmark maximality.
-/

noncomputable section
open Set Filter Topology InducedStars.Regularity
open InducedStars.Regularity.RegularityColoredGraph
open scoped Classical

namespace InducedStars

/-- The neighborhood clique estimate, inverted and summed on the actual green
vertices. No missing template edge is assigned a color. -/
theorem c4_redCount_le_green_mul_blueSize {n : ℕ}
    (J : RegularityColoredGraph (Fin n)) (hfree : ¬ColoredHomExists inducedC4 J)
    {bs : ℕ} {eta : ℝ} (heta : 0 ≤ eta)
    (hthreshold : 1 ≤ Real.sqrt eta * n)
    (hblue : c4ColorEdgeCount J .blue < (bs + 1).choose 2)
    (hmissing : (c4MissingEdgeCount J : ℝ) ≤ eta * (n : ℝ) ^ 2) :
    (c4ColorEdgeCount J .red : ℝ) ≤
      (c4GreenVertices J).card * ((bs : ℝ) + 2 * Real.sqrt eta * n) := by
  rw [c4Free_redCount_eq_sum_green_degrees J hfree, Nat.cast_sum]
  calc
    (∑ v ∈ c4GreenVertices J, (c4RedDegree J v : ℝ)) ≤
        ∑ _v ∈ c4GreenVertices J, ((bs : ℝ) + 2 * Real.sqrt eta * n) := by
      apply Finset.sum_le_sum
      intro v hv
      apply c4_red_degree_le_of_choose_bound heta hthreshold
        (blue := c4ColorEdgeCount J .blue) (missing := c4MissingEdgeCount J)
      · exact_mod_cast c4Free_redDegree_choose_le_blue_add_missing J hfree hv
      · exact_mod_cast hblue
      · exact hmissing
    _ = _ := by simp [mul_add]

/-- Entropy boosting produces a genuinely feasible complete split competitor.
Thus a red-capacity gain cannot occur within half the boost gap of the
complete-template benchmark. -/
theorem c4_no_red_gain_near_benchmark
    {alpha d gamma : ℝ} (ha : 0 < alpha) (hd : 0 < d)
    {n : ℕ} (hn : 1 ≤ n)
    (hboost : ∀ R B Dr Db target : ℝ,
      alpha ≤ (target - B) / R → (target - B) / R ≤ 1 - alpha →
      alpha * (n : ℝ) ^ 2 ≤ R → alpha * (n : ℝ) ^ 2 ≤ Dr →
      |Db| ≤ (n : ℝ) →
      0 < R ∧ 0 < R + Dr ∧ 0 < (target - (B + Db)) / (R + Dr) ∧
      (target - (B + Db)) / (R + Dr) < 1 ∧
      R * binaryEntropy ((target - B) / R) + d * (n : ℝ) ^ 2 ≤
        (R + Dr) * binaryEntropy ((target - (B + Db)) / (R + Dr)))
    (J : RegularityColoredGraph (Fin n)) (h : C4ColoredEntropyFeasible J gamma)
    {bs : ℕ} (hbs : bs ≤ n)
    (hband : (gamma * completeEdgeCount n - c4ColorEdgeCount J .blue) /
      c4ColorEdgeCount J .red ∈ Icc alpha (1 - alpha))
    (hred : alpha * (n : ℝ) ^ 2 ≤ c4ColorEdgeCount J .red)
    (hgain : alpha * (n : ℝ) ^ 2 ≤
      (n - bs : ℕ) * (bs : ℝ) - c4ColorEdgeCount J .red)
    (hblue : |(bs.choose 2 : ℝ) - c4ColorEdgeCount J .blue| ≤ n)
    (hnear : c4CompleteEntropyBenchmark n gamma - d / 2 * (n : ℝ) ^ 2 ≤
      c4ColoredEntropy J gamma h) : False := by
  let D : C4Division (Fin n) := c4DivisionOfCliqueSize n bs
  obtain ⟨_, hRstar, hq0, hq1, hE⟩ := hboost
    (c4ColorEdgeCount J .red) (c4ColorEdgeCount J .blue)
    ((n - bs : ℕ) * (bs : ℝ) - c4ColorEdgeCount J .red)
    ((bs.choose 2 : ℝ) - c4ColorEdgeCount J .blue)
    (gamma * completeEdgeCount n) hband.1 hband.2 hred hgain hblue
  have hRcancel : (c4ColorEdgeCount J .red : ℝ) +
      ((n - bs : ℕ) * (bs : ℝ) - c4ColorEdgeCount J .red) =
      (n - bs : ℕ) * (bs : ℝ) := by ring
  have hBcancel : (c4ColorEdgeCount J .blue : ℝ) +
      ((bs.choose 2 : ℝ) - c4ColorEdgeCount J .blue) = bs.choose 2 := by ring
  rw [hRcancel] at hRstar
  rw [hRcancel, hBcancel] at hq0 hq1 hE
  have hfeasible : C4ColoredEntropyFeasible (c4SplitColoring D) gamma := by
    unfold C4ColoredEntropyFeasible
    simp only [c4SplitColoring_red_count, c4SplitColoring_blue_count, D,
      c4DivisionOfCliqueSize_clique_card hbs, c4DivisionOfCliqueSize_independent_card hbs,
      Nat.cast_mul]
    refine ⟨hRstar.le, ?_, ?_⟩
    · have hh := (div_pos_iff_of_pos_right hRstar).1 hq0
      linarith only [hh]
    · have hh := (div_lt_one hRstar).1 hq1
      linarith
  have hmax := c4SplitColoring_entropy_le_benchmark D gamma hfeasible
  simp only [D, c4DivisionOfCliqueSize_clique_card hbs,
    c4DivisionOfCliqueSize_independent_card hbs, Nat.cast_mul] at hmax
  rw [c4ColoredEntropy_eq] at hnear
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  nlinarith [mul_pos hd (sq_pos_of_pos hn0)]

/-- Paper: Lemma `lemma:c4-stability`.
The entropy benchmark uses complete templates. Nearly complete partial
templates are permitted as inputs, and Case 3 uses an absolute comparison. -/
theorem c4ColoredStability {gamma : ℝ} (hgamma : gamma ∈ Ioo 0 1) :
    C4ColoredStable gamma := by
  intro epsilon hepsilon
  let e : ℝ := min epsilon 1
  have he : 0 < e := lt_min hepsilon zero_lt_one
  have he1 : e ≤ 1 := min_le_right _ _
  have heeps : e ≤ epsilon := min_le_left _ _
  let kappa : ℝ := gamma * (1 - gamma)
  have hk : 0 < kappa := mul_pos hgamma.1 (sub_pos.mpr hgamma.2)
  have hk1 : kappa ≤ 1 := by dsimp [kappa]; nlinarith [sq_nonneg gamma]
  obtain ⟨a, ha, ha1, hband⟩ := c4_entropy_level_compact_band hk
  let alpha : ℝ := min (e * kappa / 320) a
  have halpha : 0 < alpha := lt_min (by positivity) ha
  have halpha1 : alpha < 1 / 2 := (min_le_right _ _).trans_lt ha1
  have halphae : alpha ≤ e * kappa / 320 := min_le_left _ _
  have halphaa : alpha ≤ a := min_le_right _ _
  have halphak : alpha ≤ kappa / 8 := by
    have hh := mul_le_mul_of_nonneg_right he1 hk.le
    linarith
  obtain ⟨d, hd, nb, hboost⟩ := DenseGraph.entropy_quadratic_boost halpha halpha1
  let delta : ℝ := min (kappa / 8) (d / 2)
  let eta : ℝ := (e * kappa / 3000) ^ 2
  have hdelta : 0 < delta := lt_min (by positivity) (by positivity)
  have hdeltaK : delta ≤ kappa / 8 := min_le_left _ _
  have hdeltaD : delta ≤ d / 2 := min_le_right _ _
  have heta : 0 < eta := sq_pos_of_pos (by positivity)
  have hsqrt : Real.sqrt eta = e * kappa / 3000 := by
    dsimp [eta]
    rw [Real.sqrt_sq (by positivity)]
  have hetaSmall : eta ≤ e / 3 := by
    have hek : e * kappa ≤ e := by nlinarith [mul_nonneg he.le (sub_nonneg.mpr hk1)]
    have hfactor : 0 ≤ e * kappa / 3000 := by positivity
    have hfactor1 : e * kappa / 3000 ≤ 1 := by linarith
    have hh := mul_nonneg hfactor (sub_nonneg.mpr hfactor1)
    dsimp [eta]
    nlinarith
  let rho : ℝ := 2 * Real.sqrt eta
  have hrho : 0 ≤ rho := by dsimp [rho]; positivity
  have hrhosmall : rho ≤ e * kappa / 1500 := by dsimp [rho]; rw [hsqrt]; linarith
  have hrhok : rho ≤ kappa / 40 := by
    have hh := mul_le_mul_of_nonneg_right he1 hk.le
    linarith
  have hlarge : ∀ᶠ n : ℕ in atTop, 1 / Real.sqrt eta ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  refine ⟨delta, eta, hdelta, heta, ?_⟩
  have hall : ∀ᶠ n : ℕ in atTop, ∀ J : RegularityColoredGraph (Fin n),
      ¬ColoredHomExists inducedC4 J →
      ((finiteGraphEdges J.graphᶜ).card : ℝ) ≤ eta * (n : ℝ) ^ 2 →
      ∀ h : C4ColoredEntropyFeasible J gamma,
      c4CompleteEntropyBenchmark n gamma - delta * (n : ℝ) ^ 2 ≤
        c4ColoredEntropy J gamma h →
      ∃ D : C4Division (Fin n),
        (DenseGraph.coloredEditDistance J (c4SplitColoring D) : ℝ) ≤
          epsilon * (n : ℝ) ^ 2 := by
    filter_upwards [eventually_c4CompleteEntropyBenchmark_lower hgamma,
      eventually_ge_atTop nb, eventually_ge_atTop 1, hlarge]
      with n hbench hnb hn1 hneta
    intro J hfree hmissing h hnear
    let R : ℝ := c4ColorEdgeCount J .red
    let B : ℕ := c4ColorEdgeCount J .blue
    let green : ℝ := c4ColorEdgeCount J .green
    let missing : ℝ := c4MissingEdgeCount J
    let E : ℝ := c4ColoredEntropy J gamma h
    let q : ℝ := (gamma * completeEdgeCount n - B) / R
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hmiss : missing ≤ eta * (n : ℝ) ^ 2 := hmissing
    have hEeq : E = R * binaryEntropy q := c4ColoredEntropy_eq J gamma h
    have hE_le_R : E ≤ R := h.value_le_capacity
    have hElower : kappa / 8 * (n : ℝ) ^ 2 ≤ E := by
      have hh := mul_le_mul_of_nonneg_right hdeltaK (sq_nonneg (n : ℝ))
      change kappa / 4 * (n : ℝ) ^ 2 ≤ c4CompleteEntropyBenchmark n gamma at hbench
      change c4CompleteEntropyBenchmark n gamma - delta * (n : ℝ) ^ 2 ≤ E at hnear
      linarith only [hbench, hnear, hh]
    have hRlower : kappa / 8 * (n : ℝ) ^ 2 ≤ R := hElower.trans hE_le_R
    have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hRlower
    have hRalpha : alpha * (n : ℝ) ^ 2 ≤ R :=
      (mul_le_mul_of_nonneg_right halphak (sq_nonneg (n : ℝ))).trans hRlower
    have hRupper : R ≤ (n : ℝ) ^ 2 / 2 := by
      have hc : R ≤ (completeEdgeCount n : ℝ) := by
        dsimp [R]
        exact_mod_cast c4ColorEdgeCount_le_complete J .red
      have hc' : (completeEdgeCount n : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
        rw [completeEdgeCount, Nat.cast_choose_two]
        nlinarith only [Nat.cast_nonneg (α := ℝ) n]
      exact hc.trans hc'
    have hqIcc : q ∈ Icc (0 : ℝ) 1 := h.density_mem_Icc hRpos
    have hlevel : kappa / 4 ≤ binaryEntropy q := by
      have hh := mul_le_mul_of_nonneg_left hRupper (show 0 ≤ kappa / 4 by positivity)
      rw [hEeq] at hElower
      have hprod : R * (kappa / 4) ≤ R * binaryEntropy q := by
        nlinarith only [hh, hElower]
      exact (mul_le_mul_iff_right₀ hRpos).mp hprod
    have hqbandA := hband q hqIcc hlevel
    have hqband : q ∈ Icc alpha (1 - alpha) := by
      exact ⟨halphaa.trans hqbandA.1, hqbandA.2.trans (by linarith)⟩
    have hcountsNat : c4ColorEdgeCount J .red + c4ColorEdgeCount J .green +
        B + c4MissingEdgeCount J = n.choose 2 := by
      simpa only [Fintype.card_fin] using c4ColorEdgeCounts_add_missing J
    have hcounts : R + green + B + missing = (n.choose 2 : ℝ) := by
      dsimp [R, green, missing]
      exact_mod_cast hcountsNat
    have hBlt : B < n.choose 2 := by
      have hrNat : 0 < c4ColorEdgeCount J .red := by
        have hh := hRpos
        dsimp [R] at hh
        exact_mod_cast hh
      omega
    let bs : ℕ := c4BalancedBlueSize n B
    let gs : ℕ := n - bs
    have hbsn : bs ≤ n := c4BalancedBlueSize_le n B
    have hbslt : bs < n := c4BalancedBlueSize_lt_of_blue_lt hBlt
    have hgs : 1 ≤ gs := by dsimp [gs]; omega
    have hstar : gs + bs = n := Nat.sub_add_cancel hbsn
    have hblue : (bs.choose 2 : ℝ) ≤ B := by
      exact_mod_cast c4BalancedBlueSize_choose_le n B
    have hblueSucc : B < (bs + 1).choose 2 := c4BalancedBlueSize_succ_choose_gt hn1 hBlt.le
    have hblueRound : |(bs.choose 2 : ℝ) - B| ≤ n :=
      c4BalancedBlueSize_rounding_abs hn1 hBlt.le
    have hthreshold : 1 ≤ Real.sqrt eta * n := by
      have hh := (div_le_iff₀ (Real.sqrt_pos.2 heta)).1 hneta
      nlinarith only [hh]
    let g : ℕ := (c4GreenVertices J).card
    let b : ℕ := (c4BlueVertices J).card
    have hpart : g + b = n := by
      simpa only [Fintype.card_fin] using c4GreenVertices_card_add_blue J
    have hgn : g ≤ n := by omega
    have hRdegree : R ≤ (g : ℝ) * ((bs : ℝ) + rho * n) := by
      simpa only [rho, mul_assoc] using
        c4_redCount_le_green_mul_blueSize J hfree heta.le hthreshold hblueSucc hmiss
    obtain ⟨hgsize, hbsize⟩ := c4_part_sizes_lower_of_red_count hnpos
      (Nat.cast_nonneg g) (show (g : ℝ) ≤ n by exact_mod_cast hgn)
      (Nat.cast_nonneg bs) (show (bs : ℝ) ≤ n by exact_mod_cast hbsn)
      hk.le hk1 hrho hrhok hRlower hRdegree
    have hgreenNat := c4Free_greenCount_add_missing_ge J hfree
    have hgreenR : (g.choose 2 : ℝ) + (c4GreenInsideBlueEdges J).card ≤ green + missing := by
      dsimp [g, green, missing]
      exact_mod_cast hgreenNat
    have hgreenBase : (g.choose 2 : ℝ) - missing ≤ green := by
      linarith only [hgreenR, Nat.cast_nonneg (α := ℝ) (c4GreenInsideBlueEdges J).card]
    have hnoGain : ¬ alpha * (n : ℝ) ^ 2 ≤ (gs : ℝ) * bs - R := by
      intro hgain
      apply c4_no_red_gain_near_benchmark halpha hd hn1 (hboost n hnb) J h hbsn
        hqband hRalpha hgain hblueRound
      have hh := mul_le_mul_of_nonneg_right hdeltaD (sq_nonneg (n : ℝ))
      change c4CompleteEntropyBenchmark n gamma - delta * (n : ℝ) ^ 2 ≤ E at hnear
      change c4CompleteEntropyBenchmark n gamma - d / 2 * (n : ℝ) ^ 2 ≤ E
      linarith only [hnear, hh]
    have hbadBound : (c4GreenInsideBlueEdges J).card ≤ e / 3 * (n : ℝ) ^ 2 ∧
        (c4NonredCrossEdges J).card ≤ e / 3 * (n : ℝ) ^ 2 := by
      by_contra hbad
      push_neg at hbad
      have hfailure : (g.choose 2 : ℝ) + e / 3 * (n : ℝ) ^ 2 - missing ≤ green ∨
          R ≤ (g : ℝ) * b - e / 3 * (n : ℝ) ^ 2 := by
        by_cases hgBad : (c4GreenInsideBlueEdges J).card ≤ e / 3 * (n : ℝ) ^ 2
        · right
          have hbBad := hbad hgBad
          have hcross : R + (c4NonredCrossEdges J).card ≤ (g : ℝ) * b := by
            dsimp [R, g, b]
            exact_mod_cast c4Free_redCount_add_nonredCross_le J hfree
          linarith only [hcross, hbBad]
        · left
          push_neg at hgBad
          linarith only [hgreenR, hgBad]
      have hgain := c4_red_capacity_gain_of_edit_failure he.le hk.le hk1
        hpart hstar hgs hgsize hbsize hrho hrhosmall hRdegree hcounts hblue hgreenBase hfailure
      exact hnoGain ((mul_le_mul_of_nonneg_right halphae (sq_nonneg (n : ℝ))).trans hgain)
    refine ⟨c4VertexColorDivision J, ?_⟩
    have hedit : (DenseGraph.coloredEditDistance J (c4SplitColoring (c4VertexColorDivision J)) : ℝ) ≤
        missing + (c4GreenInsideBlueEdges J).card + (c4NonredCrossEdges J).card := by
      dsimp [missing]
      exact_mod_cast c4Free_coloredEdit_le_badCounts J hfree
    have hetaBound := mul_le_mul_of_nonneg_right hetaSmall (sq_nonneg (n : ℝ))
    have heBound := mul_le_mul_of_nonneg_right heeps (sq_nonneg (n : ℝ))
    linarith only [hedit, hmiss, hetaBound, heBound, hbadBound.1, hbadBound.2]
  exact eventually_atTop.1 hall

end InducedStars
