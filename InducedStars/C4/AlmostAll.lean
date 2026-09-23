import InducedStars.C4.HighDegreeAFinal
import InducedStars.C4.HighDegreeBAggregation
import InducedStars.C4.CanonicalLowDegree
import InducedStars.C4.GlobalBounds
import InducedStars.C4.CountComparison
import InducedStars.C4.RoughStructure
import InducedStars.C4.NondegenerateCounting
import InducedStars.C4.SplitSizeEnumeration

/-!
# Almost all fixed-density induced-C4-free graphs are split

Paper: Theorem `thm:c4-main` and `eqn:c4-entropy-main`.
All five exceptional-family estimates are discharged here. The constants
are chosen before the edge-count sequence: first the degree and
nondegeneracy tolerances, then the defect tolerance, then the rough
structure rate. The rough structure theorem uses the complete benchmark
and feasible quota envelope. The polynomial split-cover bound is the
estimate in `eqn:c4-sPi-sum`.
-/

noncomputable section
open Filter
open scoped Topology
namespace InducedStars

theorem c4CloseDegenerateGraphFinset_mono {n m : ℕ}
    {gamma epsilon epsilon' zeta : ℝ} (he : epsilon ≤ epsilon') :
    c4CloseDegenerateGraphFinset n m gamma epsilon zeta ⊆
      c4CloseDegenerateGraphFinset n m gamma epsilon' zeta := by
  classical
  intro G hG
  obtain ⟨hfree, hcost, hdeg⟩ := mem_c4CloseDegenerateGraphFinset.mp hG
  exact mem_c4CloseDegenerateGraphFinset.mpr ⟨hfree,
    hcost.trans (mul_le_mul_of_nonneg_right he (sq_nonneg (n : ℝ))), hdeg⟩

/-- The final finite-count estimate, with both rates depending only on the
limiting density. No penalty estimate remains as an assumption. -/
theorem inducedC4FinalCountBound {gamma : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
        ∀ᶠ n in atTop,
          (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) ≤
            (1 + Real.exp (-c*n))*(splitGraphCountWithEdges n (m n) : ℝ) +
              Real.exp (-d*(n : ℝ)^2)*(inducedC4FreeGraphCountWithEdges n (m n) : ℝ) := by
  classical
  obtain ⟨zl, hzl, el, hel, al, hal, _, l, hl, hlow⟩ :=
    inducedC4CanonicalLowDegreeSplitRate hgamma
  obtain ⟨za, ca, hza, hca, hhighA⟩ := inducedC4HighIndependentPenalty_uniform hgamma
  obtain ⟨zb, cb, hzb, hcb, hhighB⟩ := inducedC4HighCliquePenalty_uniform hgamma
  let alpha : ℝ := min al (1/4)
  have ha : 0 < alpha := lt_min hal (by norm_num)
  have ha1 : alpha ≤ 1 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨ea, hea, hhighA⟩ := hhighA alpha ha ha1
  obtain ⟨eb, heb, hhighB⟩ := hhighB alpha ha
  let zeta : ℝ := min zl (min za zb)
  have hz : 0 < zeta := lt_min hzl (lt_min hza hzb)
  obtain ⟨eg, g, heg, hg, hdeg⟩ := inducedC4AlmostAllNondegenerate hgamma zeta hz
  let epsilon : ℝ := min el (min ea (min eb eg))
  have he : 0 < epsilon := lt_min hel (lt_min hea (lt_min heb heg))
  have hel' : epsilon ≤ el := min_le_left _ _
  have hea' : epsilon ≤ ea := (min_le_right _ _).trans (min_le_left _ _)
  have heb' : epsilon ≤ eb :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have heg' : epsilon ≤ eg :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨f, hf, hfar⟩ := inducedC4RoughSplitStructure hgamma he
  obtain ⟨c, hc, hlocal⟩ := eventually_c4_local_penalties_absorb_cover
    (show 0 < ca*alpha^2 by positivity) (show 0 < cb*alpha^3 by positivity) hl
  obtain ⟨d, hd, hglobal⟩ := eventually_c4_quadratic_penalties_combine hf hg
  refine ⟨c, d, hc, hd, ?_⟩
  intro m hm
  filter_upwards [hhighA m hm, hhighB m hm, hlow m hm, hdeg m hm,
    hfar m hm, hlocal, hglobal] with n hA hB hL hG hF hlocal hglobal
  simp only [neg_mul] at hlocal
  have hA' (D : C4Division (Fin n)) :=
    hA D epsilon zeta hea' ((min_le_right _ _).trans (min_le_left _ _))
  have hB' (D : C4Division (Fin n)) :=
    hB D epsilon zeta heb' ((min_le_right _ _).trans (min_le_right _ _))
  have hL' (D : C4Division (Fin n)) :=
    hL D zeta (min_le_left _ _) epsilon hel' alpha ⟨ha.le, min_le_left _ _⟩
  have hG' : ((c4CloseDegenerateGraphFinset n (m n) gamma epsilon zeta).card : ℝ) ≤
      Real.exp (-g*(n : ℝ)^2)*(inducedC4FreeGraphCountWithEdges n (m n) : ℝ) := by
    apply le_trans _ hG
    exact_mod_cast Finset.card_le_card (c4CloseDegenerateGraphFinset_mono heg')
  have hraw := c4Nonsplit_card_le_weighted_reference n (m n) gamma epsilon zeta alpha ha.le
    (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le hA' hB' hL'
  have hsum := congrArg (fun t : ℕ ↦ (t : ℝ)) (splitGraphCount_add_c4NonsplitCount n (m n))
  push_cast at hsum
  have hlocal' := mul_le_mul_of_nonneg_right hlocal
    (Nat.cast_nonneg (α := ℝ) (splitGraphCountWithEdges n (m n)))
  have hglobal' := mul_le_mul_of_nonneg_right hglobal
    (Nat.cast_nonneg (α := ℝ) (inducedC4FreeGraphCountWithEdges n (m n)))
  simp only [neg_mul] at hraw hF hG' hlocal' hglobal' ⊢
  nlinarith only [hraw, hsum, hF, hG', hlocal', hglobal']

/-- Paper: Theorem `thm:c4-main`, with its exponential relative-count rate.
The rate is chosen before the arbitrary asymptotic edge-count sequence. -/
theorem inducedC4CountComparison {gamma : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1) :
    ∃ c > 0, ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
      ∀ᶠ n in atTop,
        |(inducedC4FreeGraphCountWithEdges n (m n) : ℝ) /
          (splitGraphCountWithEdges n (m n) : ℝ) - 1| ≤ Real.exp (-c*n) := by
  obtain ⟨a, b, ha, hb, hcount⟩ := inducedC4FinalCountBound hgamma
  exact ⟨a/2, half_pos ha, fun m hm ↦
    eventually_c4CountRatio_abs_sub_one_le_exp_of_count_bound hgamma ha hb hm (hcount m hm)⟩

theorem inducedC4FreeCount_div_splitCount_tendsto_one {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo 0 1) {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m gamma) :
    Tendsto (fun n ↦ (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) /
      (splitGraphCountWithEdges n (m n) : ℝ)) atTop (𝓝 1) := by
  obtain ⟨a, b, ha, hb, hcount⟩ := inducedC4FinalCountBound hgamma
  exact c4CountRatio_tendsto_one_of_count_bound hgamma ha hb hm (hcount m hm)

/-- Paper: Theorem `thm:c4-main`: the actual conditional proportion of split
graphs in the labeled, exact-edge, induced-C4-free family tends to one. -/
theorem inducedC4AlmostAllSplit {gamma : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1)
    {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m gamma) :
    Tendsto (fun n ↦ c4SplitProbability n (m n)) atTop (𝓝 1) :=
  c4SplitProbability_tendsto_one_of_countRatio
    (inducedC4FreeCount_div_splitCount_tendsto_one hgamma hm)

theorem inducedC4NonsplitProbability_tendsto_zero {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo 0 1) {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m gamma) :
    Tendsto (fun n ↦ c4NonsplitProbability n (m n)) atTop (𝓝 0) :=
  c4NonsplitProbability_tendsto_zero_of_splitProbability hgamma hm
    (inducedC4AlmostAllSplit hgamma hm)

/-- Paper: Equation `eqn:c4-entropy-main`, normalized by `choose n 2`.
The factor two is included in `c4SplitOptimalEntropy`. -/
theorem inducedC4Entropy {gamma : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1)
    {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m gamma) :
    Tendsto (fun n ↦ log2 (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) /
      (completeEdgeCount n : ℝ)) atTop (𝓝 (c4SplitOptimalEntropy gamma)) :=
  c4Count_normalizedLog_tendsto_of_countRatio hgamma hm
    (inducedC4FreeCount_div_splitCount_tendsto_one hgamma hm)

/-- The literal feasible-interval maximum formula. The supremum is attained,
as proved separately by `c4SplitOptimalEntropy_isGreatest`. -/
theorem inducedC4Entropy_eq_scalarMax {gamma : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1)
    {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m gamma) :
    Tendsto (fun n ↦ log2 (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) /
      (completeEdgeCount n : ℝ)) atTop
      (𝓝 (sSup ((fun x : ℝ ↦ 2*x*(1-x)*binaryEntropy (c4SplitCrossDensity gamma x)) ''
        Set.Icc (1-Real.sqrt (1-gamma)) (Real.sqrt gamma)))) := by
  rw [← c4SplitOptimalEntropy_eq_scalarSup hgamma]
  exact inducedC4Entropy hgamma hm

end InducedStars
