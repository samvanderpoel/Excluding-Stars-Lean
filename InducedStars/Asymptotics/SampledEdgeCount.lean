import InducedStars.Asymptotics.FlexiblePairAbundance
import InducedStars.FiniteModels.EntropyAsymptotics
import InducedStars.Graphon.Counting
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-!
# Concentration near an asymptotically prescribed edge count

This file converts the exact ordered-square normalization supplied by
`wRandomGraphNormalizedEdgeCount_convergenceInProbability` into the
unordered-edge edit radius used by exact-edge repair.  No rounding error is
lost: failure of the floored-radius bound gives a strict real discrepancy.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The natural-number distance becomes the usual absolute difference after
casting to the reals. -/
theorem natCast_natDist_eq_abs_sub (a b : ℕ) :
    (Nat.dist a b : ℝ) = |(a : ℝ) - (b : ℝ)| := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, Nat.cast_sub hab]
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    rw [abs_of_nonpos (sub_nonpos.mpr hab'), neg_sub]
  · rw [Nat.dist_eq_sub_of_le_right hba, Nat.cast_sub hba]
    have hba' : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
    rw [abs_of_nonneg (sub_nonneg.mpr hba')]

/-- An edge-count sequence with density `γ` in the unordered-pair
normalization also has density `γ` in the ordered-square normalization.
-/
theorem hasAsymptoticEdgeDensity_orderedSquare
    {m : ℕ → ℕ} {γ : ℝ} (hm : HasAsymptoticEdgeDensity m γ) :
    Tendsto (fun n ↦ 2 * (m n : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds γ) := by
  have hprod := hm.mul completeEdgeCount_orderedSquareFactor_tendsto_one
  apply (show Tendsto
      (fun n ↦ ((m n : ℝ) / (completeEdgeCount n : ℝ)) *
        (2 * (completeEdgeCount n : ℝ) / (n : ℝ) ^ 2))
      atTop (nhds γ) by simpa using hprod).congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hN : (completeEdgeCount n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  field_simp

/-- The probability that a `W`-random graph misses the floored edit window
around an asymptotically prescribed edge count tends to zero. -/
theorem wRandomGraphEdgeCount_outsideFractionalRadius_probability_tendsto_zero
    (W : Graphon) (m : ℕ → ℕ) (γ η : ℝ)
    (hm : HasAsymptoticEdgeDensity m γ)
    (hDensity : graphonEdgeDensity W = γ) (hη : 0 < η) :
    Tendsto
      (fun n ↦ wRandomGraphEventProbability W
        {G : SimpleGraph (Fin n) |
          fractionalEditRadius η (completeEdgeCount n) <
            Nat.dist (finiteGraphEdges G).card (m n)})
      atTop (nhds 0) := by
  have hsample :=
    wRandomGraphNormalizedEdgeCount_convergenceInProbability
      W γ (η / 4) hDensity (by positivity)
  have htarget := hasAsymptoticEdgeDensity_orderedSquare hm
  have htargetClose : ∀ᶠ n in atTop,
      |2 * (m n : ℝ) / (n : ℝ) ^ 2 - γ| < η / 4 :=
    by
      have hdist : ∀ᶠ n in atTop,
          dist (2 * (m n : ℝ) / (n : ℝ) ^ 2) γ < η / 4 :=
        htarget.eventually (Metric.ball_mem_nhds γ (by positivity))
      simpa only [Real.dist_eq] using hdist
  have hfactorClose : ∀ᶠ n in atTop,
      (1 : ℝ) / 2 <
        2 * (completeEdgeCount n : ℝ) / (n : ℝ) ^ 2 :=
    (tendsto_order.1 completeEdgeCount_orderedSquareFactor_tendsto_one).1
      (1 / 2) (by norm_num)
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      wRandomGraphEventProbability_nonneg W _
  · filter_upwards [eventually_ge_atTop 2, htargetClose, hfactorClose]
      with n hn htargetN hfactorN
    apply wRandomGraphEventProbability_mono W
    intro G hbad
    change fractionalEditRadius η (completeEdgeCount n) <
      Nat.dist (finiteGraphEdges G).card (m n) at hbad
    change η / 4 ≤
      |2 * ((finiteGraphEdges G).card : ℝ) / (n : ℝ) ^ 2 - γ|
    have hNnonneg : 0 ≤ η * (completeEdgeCount n : ℝ) :=
      mul_nonneg hη.le (Nat.cast_nonneg _)
    have hdist : η * (completeEdgeCount n : ℝ) <
        (Nat.dist (finiteGraphEdges G).card (m n) : ℝ) := by
      exact (Nat.floor_lt hNnonneg).mp hbad
    have hscale : 0 < (2 : ℝ) / (n : ℝ) ^ 2 := by positivity
    have hscaled := mul_lt_mul_of_pos_left hdist hscale
    have hetaFactor : η / 2 <
        η * (2 * (completeEdgeCount n : ℝ) / (n : ℝ) ^ 2) := by
      have := mul_lt_mul_of_pos_left hfactorN hη
      nlinarith
    have hpair : η / 2 <
        |2 * ((finiteGraphEdges G).card : ℝ) / (n : ℝ) ^ 2 -
          2 * (m n : ℝ) / (n : ℝ) ^ 2| := by
      have hrewrite :
          (2 / (n : ℝ) ^ 2) *
              (η * (completeEdgeCount n : ℝ)) =
            η * (2 * (completeEdgeCount n : ℝ) / (n : ℝ) ^ 2) := by
        ring
      rw [hrewrite] at hscaled
      have hpairEq :
          |2 * ((finiteGraphEdges G).card : ℝ) / (n : ℝ) ^ 2 -
              2 * (m n : ℝ) / (n : ℝ) ^ 2| =
            (2 / (n : ℝ) ^ 2) *
              (Nat.dist (finiteGraphEdges G).card (m n) : ℝ) := by
        rw [natCast_natDist_eq_abs_sub]
        rw [← abs_of_pos hscale, ← abs_mul]
        congr 1
        ring
      -- The absolute-value rewrite above reduces the claim to the scaled
      -- natural distance; the two inequalities give the strict bound.
      rw [hpairEq]
      calc
        η / 2 < η *
            (2 * (completeEdgeCount n : ℝ) / (n : ℝ) ^ 2) := hetaFactor
        _ < (2 / (n : ℝ) ^ 2) *
            (Nat.dist (finiteGraphEdges G).card (m n) : ℝ) := hscaled
    have htriangle := abs_sub_le
      (2 * ((finiteGraphEdges G).card : ℝ) / (n : ℝ) ^ 2) γ
      (2 * (m n : ℝ) / (n : ℝ) ^ 2)
    have htargetN' :
        |γ - 2 * (m n : ℝ) / (n : ℝ) ^ 2| < η / 4 := by
      simpa only [abs_sub_comm] using htargetN
    by_contra hsampleSmall
    have hsampleSmall' :
        |2 * ((finiteGraphEdges G).card : ℝ) / (n : ℝ) ^ 2 - γ| <
          η / 4 := lt_of_not_ge hsampleSmall
    have himpossible : η / 2 < η / 2 := calc
      η / 2 <
          |2 * ((finiteGraphEdges G).card : ℝ) / (n : ℝ) ^ 2 -
            2 * (m n : ℝ) / (n : ℝ) ^ 2| := hpair
      _ ≤ |2 * ((finiteGraphEdges G).card : ℝ) / (n : ℝ) ^ 2 - γ| +
          |γ - 2 * (m n : ℝ) / (n : ℝ) ^ 2| := htriangle
      _ < η / 4 + η / 4 := add_lt_add hsampleSmall' htargetN'
      _ = η / 2 := by ring
    exact (lt_irrefl _) himpossible
  · exact hsample

/-- Equivalently, a `W`-random graph lies within the floored edit window
around an asymptotically prescribed edge count with probability tending to
one. -/
theorem wRandomGraphEdgeCount_withinFractionalRadius_probability_tendsto_one
    (W : Graphon) (m : ℕ → ℕ) (γ η : ℝ)
    (hm : HasAsymptoticEdgeDensity m γ)
    (hDensity : graphonEdgeDensity W = γ) (hη : 0 < η) :
    Tendsto
      (fun n ↦ wRandomGraphEventProbability W
        {G : SimpleGraph (Fin n) |
          Nat.dist (finiteGraphEdges G).card (m n) ≤
            fractionalEditRadius η (completeEdgeCount n)})
      atTop (nhds 1) := by
  have hbad :=
    wRandomGraphEdgeCount_outsideFractionalRadius_probability_tendsto_zero
      W m γ η hm hDensity hη
  have hsub : Tendsto
      (fun n ↦ 1 - wRandomGraphEventProbability W
        {G : SimpleGraph (Fin n) |
          fractionalEditRadius η (completeEdgeCount n) <
            Nat.dist (finiteGraphEdges G).card (m n)})
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hbad
  apply hsub.congr'
  filter_upwards [] with n
  classical
  rw [← sum_wRandomGraphMass (n := n) W]
  unfold wRandomGraphEventProbability
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro G _hG
  by_cases hgood : Nat.dist (finiteGraphEdges G).card (m n) ≤
      fractionalEditRadius η (completeEdgeCount n)
  · have hnotbad : ¬ fractionalEditRadius η (completeEdgeCount n) <
        Nat.dist (finiteGraphEdges G).card (m n) := Nat.not_lt.mpr hgood
    simp [hgood, hnotbad]
  · have hbad' : fractionalEditRadius η (completeEdgeCount n) <
        Nat.dist (finiteGraphEdges G).card (m n) := Nat.lt_of_not_ge hgood
    simp [hgood, hbad']

end InducedStars
