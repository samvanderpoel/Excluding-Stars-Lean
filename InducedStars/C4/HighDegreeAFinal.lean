import InducedStars.C4.HighDegreeAAggregation

/-!
# The uniform high independent-side degree penalty

Paper: Lemma `lemma:FPi1`. Constants are chosen before the edge-count
sequence. Both defect tolerance and nondegeneracy radius may subsequently
be decreased without changing the eventual threshold.
-/

noncomputable section
open Finset Filter
open scoped Classical Topology
namespace InducedStars

theorem c4HighIndependentGraphFinset_mono {n m : ℕ} {gamma alpha e1 e2 z1 z2 : ℝ}
    (D : C4Division (Fin n)) (he : e1 ≤ e2) (hz : z1 ≤ z2) :
    c4HighIndependentGraphFinset n m gamma e1 z1 alpha D ⊆
      c4HighIndependentGraphFinset n m gamma e2 z2 alpha D := by
  intro G hG
  obtain ⟨hclose, hdegree⟩ := mem_c4HighIndependentGraphFinset.mp hG
  obtain ⟨hfree, hcanon, hcost, hnear⟩ := mem_c4CloseDivisionGraphFinset.mp hclose
  apply mem_c4HighIndependentGraphFinset.mpr
  refine ⟨mem_c4CloseDivisionGraphFinset.mpr ⟨hfree, hcanon, ?_, ?_⟩, hdegree⟩
  · exact hcost.trans (mul_le_mul_of_nonneg_right he (sq_nonneg _))
  · exact hnear.trans (mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg n))

/-- Paper: Lemma `lemma:FPi1`.

This is the actual canonical-family bound against the guarded split-fiber
cardinality. The positive rate and radius depend only on `gamma`, and the
defect ceiling is chosen after `alpha`, before the edge-count sequence.
The eventual bound is simultaneous for every smaller tolerance and radius. -/
theorem inducedC4HighIndependentPenalty_uniform {gamma : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1) :
    ∃ zetaMax c : ℝ, 0 < zetaMax ∧ 0 < c ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 →
        ∃ epsilonMax : ℝ, 0 < epsilonMax ∧
          ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
            ∀ᶠ n in atTop, ∀ D : C4Division (Fin n), ∀ epsilon zeta : ℝ,
              epsilon ≤ epsilonMax → zeta ≤ zetaMax →
                ((c4HighIndependentGraphFinset n (m n) gamma epsilon zeta alpha D).card : ℝ) ≤
                  ((c4SplitFiber D (m n)).card : ℝ) * Real.exp (-c * alpha ^ 2 * (n : ℝ) ^ 2) := by
  obtain ⟨zetaBand, hzetaBand, epsBand, hepsBand, beta, hbeta, hbetaHalf, hsampling⟩ :=
    exists_c4NondegenerateSamplingBand hgamma
  obtain ⟨zetaMat, hzetaMat, epsMat, hepsMat, cMat, hcMat, hmatching⟩ :=
    inducedC4MatchingPenalty hgamma
  let zetaMax := min zetaBand zetaMat
  let rate := min (cMat * beta / 8) (beta ^ 6 / 64)
  have hzetaMax : 0 < zetaMax := lt_min hzetaBand hzetaMat
  have hrate : 0 < rate := lt_min (by positivity) (by positivity)
  let C := DenseGraph.binomialCompactBandShiftConstant beta
  have hC : 0 < C := DenseGraph.binomialCompactBandShiftConstant_pos hbeta hbetaHalf
  refine ⟨zetaMax, rate / 4, hzetaMax, by positivity, ?_⟩
  intro alpha halpha halpha1
  let q : ℝ := rate * alpha ^ 2
  have hq : 0 < q := mul_pos hrate (sq_pos_of_pos halpha)
  obtain ⟨e0, he0, hecontrol⟩ :=
    exists_epsilon0_supercriticalDefectPatternRate_lt (show 0 < q / 4 by positivity)
  let epsilonMax := min epsBand (min epsMat (min (q / (4 * (C + 1))) (e0 / 2)))
  have hepsilonMax : 0 < epsilonMax := by dsimp [epsilonMax]; positivity
  have hepsBand' : epsilonMax ≤ epsBand := min_le_left _ _
  have hepsMat' : epsilonMax ≤ epsMat := (min_le_right _ _).trans (min_le_left _ _)
  have hepsCost : epsilonMax ≤ q / (4 * (C + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepsE0 : epsilonMax < e0 := ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (by linarith)
  obtain ⟨hepsHalf, hepsRate⟩ := hecontrol hepsilonMax hepsE0
  have hCe : C * epsilonMax ≤ q / 4 := by
    have hh := (le_div_iff₀ (show 0 < 4 * (C + 1) by positivity)).mp hepsCost
    nlinarith only [hh, hepsilonMax, hC]
  refine ⟨epsilonMax, hepsilonMax, ?_⟩
  intro m hm
  have hlarge : ∀ᶠ n : ℕ in atTop, 8 / (alpha * beta) ≤ (n : ℝ) ∧
      (Real.log 2 + 3) / (q / 4) ≤ (n : ℝ) := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (8 / (alpha * beta)),
      tendsto_natCast_atTop_atTop.eventually_ge_atTop ((Real.log 2 + 3) / (q / 4))] with n h1 h2
    exact ⟨h1, h2⟩
  have hmain : ∀ᶠ n in atTop, ∀ D : C4Division (Fin n),
      ((c4HighIndependentGraphFinset n (m n) gamma epsilonMax zetaMax alpha D).card : ℝ) ≤
        ((c4SplitFiber D (m n)).card : ℝ) * Real.exp (-(rate / 4) * alpha ^ 2 * (n : ℝ) ^ 2) := by
    filter_upwards [hsampling m hm, hmatching m hm,
      eventually_hammingBallVolume_floor_square_le_exp hepsilonMax hepsHalf, hlarge]
      with n hn hmat hball hlarge
    intro D
    by_cases hnonempty : (c4HighIndependentGraphFinset n (m n) gamma epsilonMax zetaMax alpha D).Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty, Finset.card_empty, Nat.cast_zero]
      positivity
    obtain ⟨G, hG⟩ := hnonempty
    have hclose := (mem_c4HighIndependentGraphFinset.mp hG).1
    have hnear := (mem_c4CloseDivisionGraphFinset.mp hclose).2.2.2
    have hnear' := (c4_nondegenerate_ratio_iff hn.1 D gamma zetaMax).mpr hnear
    have hbn : D.cliquePart.card ≤ n := by simpa using Finset.card_le_univ D.cliquePart
    have hsample : ∀ t : ℤ, |(t : ℝ)| ≤ epsilonMax * (n : ℝ) ^ 2 + n →
        ∀ z : ℕ, z ≤ n → C4NondegenerateSamplingBounds n (m n) D.cliquePart.card z t beta := by
      intro t ht z hz
      apply hn.2 D.cliquePart.card hbn (hnear'.trans (min_le_left _ _)) t _ z hz
      exact ht.trans (by nlinarith only [mul_le_mul_of_nonneg_right hepsBand' (sq_nonneg (n : ℝ))])
    have hbase := hsample 0 (by simp; positivity) 0 (Nat.zero_le n)
    have hdegree : 8 ≤ alpha * beta * n := by
      simpa only [mul_comm] using (div_le_iff₀ (mul_pos halpha hbeta)).mp hlarge.1
    have hA : beta * n ≤ (D.independentPart.card : ℝ) := by
      have hparts := D.card_add
      simp only [Fintype.card_fin] at hparts
      have heq : n - D.cliquePart.card = D.independentPart.card := by omega
      simpa only [heq] using hbase.independent_size.le
    have hfinite := c4HighIndependent_card_le_explicit (gamma := gamma) (zeta := zetaMax)
      D hepsilonMax.le halpha halpha1
      hbeta hbetaHalf hcMat hrate (min_le_left _ _) (min_le_right _ _) hdegree hA hsample
      (fun T hT q' hq' hside ↦ hmat D (hnear'.trans (min_le_right _ _)) T
        ((c4SmallDefectGraphFinset_edgeCount_le hepsilonMax.le hT).trans
          (mul_le_mul_of_nonneg_right hepsMat' (sq_nonneg (n : ℝ)))) q' hq' (Or.inl hside))
    have hlinear : (Real.log 2 + 3) * n ≤ q / 4 * (n : ℝ) ^ 2 := by
      have hh := (div_le_iff₀ (show 0 < q / 4 by positivity)).mp hlarge.2
      have hh' := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) n)
      nlinarith only [hh']
    have hfinalExp : supercriticalDefectPatternRate epsilonMax * (n : ℝ) ^ 2 +
        (Real.log 2 + 3) * n + (C * epsilonMax - rate * alpha ^ 2) * (n : ℝ) ^ 2 ≤
          -(rate / 4) * alpha ^ 2 * (n : ℝ) ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_right hepsRate.le (sq_nonneg (n : ℝ))
      have h2 := mul_le_mul_of_nonneg_right hCe (sq_nonneg (n : ℝ))
      dsimp [q] at *
      nlinarith only [h1, h2, hlinear]
    calc
      _ ≤ _ := hfinite
      _ = ((c4SplitFiber D (m n)).card : ℝ) *
          (hammingBallVolume (completeEdgeCount n) ⌊epsilonMax * (n : ℝ) ^ 2⌋₊ : ℝ) *
          (((n : ℝ) * (2 : ℝ) ^ n) * ((n : ℝ) ^ 2 + 1)) *
          Real.exp ((C * epsilonMax - rate * alpha ^ 2) * (n : ℝ) ^ 2) := by ring
      _ ≤ ((c4SplitFiber D (m n)).card : ℝ) *
          Real.exp (supercriticalDefectPatternRate epsilonMax * (n : ℝ) ^ 2) *
          Real.exp ((Real.log 2 + 3) * n) *
          Real.exp ((C * epsilonMax - rate * alpha ^ 2) * (n : ℝ) ^ 2) := by
        gcongr
        simpa using c4DefectEnumeration_linearOverhead_le n 0
      _ = ((c4SplitFiber D (m n)).card : ℝ) *
          Real.exp (supercriticalDefectPatternRate epsilonMax * (n : ℝ) ^ 2 +
            (Real.log 2 + 3) * n + (C * epsilonMax - rate * alpha ^ 2) * (n : ℝ) ^ 2) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hfinalExp) (by positivity)
  filter_upwards [hmain] with n hn
  intro D epsilon zeta hepsilon hzeta
  exact (Nat.cast_le.mpr (Finset.card_le_card
    (c4HighIndependentGraphFinset_mono D hepsilon hzeta))).trans (hn D)

end InducedStars
