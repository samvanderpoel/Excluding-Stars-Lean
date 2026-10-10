import InducedStars.Structure.Supercritical.AlmostAll
import InducedStars.Structure.Supercritical.AlmostAllLimits
import InducedStars.Structure.Supercritical.CleanGlobalAggregation
import InducedStars.Structure.Supercritical.FixedDefectGlobalAggregation
import InducedStars.Structure.Supercritical.MediumGlobalAggregation
import InducedStars.Structure.Supercritical.GlobalBoundAlgebra

/-!
# Final strictly supercritical aggregation

This module chooses the common scalar package, combines the clean,
fixed-defect, medium-degree, and graphon-far estimates, and exposes the
probability and count-ratio forms of the strictly supercritical theorem.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The four finite exceptional contributions admit one uniform positive
linear rate relative to the co-multipartite family and one uniform positive
quadratic rate relative to the whole induced-star-free family.  Both rates
are chosen before the edge-count sequence. -/
theorem eventually_supercriticalGlobalExceptional_le
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    ∃ cLinear cQuadratic : ℝ,
      0 < cLinear ∧ 0 < cQuadratic ∧
        ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
          SupercriticalExceptionalBound k m cLinear cQuadratic := by
  obtain ⟨P⟩ := exists_supercriticalAggregationParameters k hk gamma hgamma
  obtain ⟨cFar, hcFar, hfar⟩ :=
    eventually_supercriticalFarTotal_le
      k hk gamma ⟨hgamma.1.le, hgamma.2⟩ P.tau P.tau_pos
  let cClean : ℝ := P.cAbs / 8
  let cFixed : ℝ := P.linearRate / 2
  let cMedium : ℝ := P.mediumRate
  let cLinear : ℝ := min cClean cFixed / 2
  let cQuadratic : ℝ := min cMedium cFar / 2
  have hcClean : 0 < cClean := by
    dsimp [cClean]
    exact div_pos P.cAbs_pos (by norm_num)
  have hcFixed : 0 < cFixed := by
    dsimp [cFixed]
    exact half_pos P.linearRate_pos
  have hcMedium : 0 < cMedium := by
    simpa [cMedium] using P.mediumRate_pos
  have hcLinear : 0 < cLinear := by
    simpa [cLinear] using
      supercriticalGlobalLinearRate_pos hcClean hcFixed
  have hcQuadratic : 0 < cQuadratic := by
    simpa [cQuadratic] using
      supercriticalGlobalQuadraticRate_pos hcMedium hcFar
  refine ⟨cLinear, cQuadratic, hcLinear, hcQuadratic, ?_⟩
  intro m hm
  have hfarTotal : ∀ m' : ℕ → ℕ,
      HasAsymptoticEdgeDensity m' gamma →
        ∀ᶠ n in atTop,
          (supercriticalFarTotal k hk gamma
            ⟨hgamma.1.le, hgamma.2⟩ (m' n) n P.tau : ℝ) ≤
            (inducedStarFreeGraphCountWithEdges k n (m' n) : ℝ) *
              Real.exp (-cFar * (n : ℝ) ^ 2) := by
    intro m' hm'
    simpa [supercriticalFarTotal] using hfar m' hm'
  have hfour :=
    eventually_supercriticalGlobalExceptional_four_term_of_total_bounds
      k hk gamma hgamma P cClean cFixed cMedium cFar
      (by
        intro m' hm'
        simpa [cClean] using
          eventually_supercriticalCleanTotal_le
            k hk gamma hgamma P m' hm')
      (by
        intro m' hm'
        simpa [cFixed] using
          eventually_supercriticalFixedDefectTotal_le
            k hk gamma hgamma P m' hm')
      (by
        intro m' hm'
        simpa [cMedium] using
          eventually_supercriticalMediumTotal_le
            k hk gamma hgamma P m' hm')
      hfarTotal m hm
  simpa [SupercriticalExceptionalBound, cLinear, cQuadratic] using
    eventually_supercriticalGlobalExceptional_two_term_of_four_term
      k hk m cClean cFixed cMedium cFar
        hcClean hcFixed hcMedium hcFar hfour

/-- Among induced-`K₁,ₖ`-free graphs with asymptotic edge density in the
strictly supercritical interval, the proportion which is not
`(k - 1)`-co-multipartite tends to zero. -/
theorem supercriticalNonCoMultipartiteProbability_tendsto_zero
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    Tendsto
      (fun n ↦ supercriticalNonCoMultipartiteProbability k n (m n))
      atTop (nhds 0) := by
  obtain ⟨cLinear, cQuadratic, hcLinear, hcQuadratic, hbound⟩ :=
    eventually_supercriticalGlobalExceptional_le k hk gamma hgamma
  exact supercriticalNonCoMultipartiteProbability_tendsto_zero_of_bound
    k hk gamma hgamma m hm hcLinear hcQuadratic (hbound m hm)

/-- Equivalently, the `(k - 1)`-co-multipartite proportion tends to one. -/
theorem supercriticalCoMultipartiteProbability_tendsto_one
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    Tendsto
      (fun n ↦ supercriticalCoMultipartiteProbability k n (m n))
      atTop (nhds 1) := by
  exact supercriticalCoMultipartiteProbability_tendsto_one_of_bad
    k hk gamma hgamma m hm
      (supercriticalNonCoMultipartiteProbability_tendsto_zero
        k hk gamma hgamma m hm)

/-- Count-ratio form of the strictly supercritical almost-all theorem. -/
theorem inducedStarFreeCount_div_coMultipartiteCount_tendsto_one
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    Tendsto
      (fun n ↦
        (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) /
          (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ))
      atTop (nhds 1) := by
  exact inducedStarFreeCount_div_coMultipartiteCount_tendsto_one_of_good
    k hk gamma hgamma m hm
      (supercriticalCoMultipartiteProbability_tendsto_one
        k hk gamma hgamma m hm)

/-- Paper: Theorem `thm:main-almostall`,
item `item:thm:main-almostall-super`.

For every exact edge-count sequence with limiting density strictly above the
transition, asymptotically almost every induced-`K₁,ₖ`-free graph is
`(k - 1)`-co-multipartite. -/
theorem inducedStarSupercriticalAlmostAllCoMultipartite
    (k : ℕ) (hk : 3 ≤ k)
    (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (m : ℕ → ℕ)
    (hm : HasAsymptoticEdgeDensity m gamma) :
    Tendsto
      (fun n ↦
        supercriticalCoMultipartiteProbability k n (m n))
      atTop
      (nhds 1) :=
  supercriticalCoMultipartiteProbability_tendsto_one
    k hk gamma hgamma m hm

end InducedStars
