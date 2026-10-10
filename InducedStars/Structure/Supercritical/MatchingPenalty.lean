import InducedStars.Structure.Supercritical.Closeness
import InducedStars.Structure.Supercritical.MatchingFiberPenalty
import Mathlib.Tactic

/-!
# The supercritical matching-defect penalty

This file supplies the uniform parameter hierarchy and the paper-facing
wrapper for the concrete fixed-profile matching/Janson estimate.  The finite
core is separated from the BCLSV alignment step so its project-specific trust
boundary is exactly the Riordan--Warnke principal Janson input.
-/

noncomputable section

open Filter Finset Set

namespace InducedStars

/-! ## A common small-density radius -/

/-- One radius simultaneously supplies the close-structure hypotheses, the
candidate balance estimate, and the two globally oriented probability
floors. -/
def supercriticalMatchingDeltaBound
    (k : ℕ) (gamma alpha : ℝ) : ℝ :=
  min (alpha / 100)
    (min (supercriticalMatchingSuccessFloor k gamma / 2)
      (1 / (6 * ((k - 1 : ℕ) : ℝ))))

theorem supercriticalMatchingDeltaBound_pos
    {k : ℕ} (hk : 3 ≤ k) {gamma alpha : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (halpha : 0 < alpha) :
    0 < supercriticalMatchingDeltaBound k gamma alpha := by
  unfold supercriticalMatchingDeltaBound
  apply lt_min
  · positivity
  · apply lt_min
    · exact half_pos (supercriticalMatchingSuccessFloor_pos hk hgamma)
    · have hk1Nat : 0 < k - 1 := by omega
      have hk1 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
        exact_mod_cast hk1Nat
      positivity

/-- All scalar consequences consumed by close structure, candidate counting,
and the oriented Bernoulli comparison. -/
theorem supercriticalMatchingDeltaBound_spec
    {k : ℕ} (hk : 3 ≤ k) {gamma alpha delta : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (hdelta : delta < supercriticalMatchingDeltaBound k gamma alpha) :
    delta < alpha / 100 ∧
      delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)) ∧
      supercriticalMatchingSuccessFloor k gamma ≤
        supercriticalOffDiagonal k gamma - delta ∧
      supercriticalOffDiagonal k gamma + delta ≤
        1 - supercriticalMatchingSuccessFloor k gamma ∧
      3 * delta < supercriticalOffDiagonal k gamma ∧
      supercriticalOffDiagonal k gamma + 3 * delta < 1 := by
  let rho := supercriticalOffDiagonal k gamma
  let qFloor := supercriticalMatchingSuccessFloor k gamma
  have halpha := hdelta.trans_le
    (min_le_left (alpha / 100)
      (min (qFloor / 2) (1 / (6 * ((k - 1 : ℕ) : ℝ)))))
  have hright := hdelta.trans_le
    (min_le_right (alpha / 100)
      (min (qFloor / 2) (1 / (6 * ((k - 1 : ℕ) : ℝ)))))
  have hfloor : delta < qFloor / 2 := hright.trans_le
    (min_le_left (qFloor / 2) (1 / (6 * ((k - 1 : ℕ) : ℝ))))
  have hcandidate : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)) :=
    (hright.trans_le
      (min_le_right (qFloor / 2)
        (1 / (6 * ((k - 1 : ℕ) : ℝ))))).le
  have hqFloorRho : qFloor ≤ rho / 2 := by
    dsimp [qFloor, rho, supercriticalMatchingSuccessFloor,
      mediumSuccessProbabilityFloor]
    gcongr
    exact min_le_left _ _
  have hqFloorComp : qFloor ≤ (1 - rho) / 2 := by
    dsimp [qFloor, rho, supercriticalMatchingSuccessFloor,
      mediumSuccessProbabilityFloor]
    gcongr
    exact min_le_right _ _
  have hrho : 0 < rho := by
    exact supercriticalOffDiagonal_pos hk hgamma.1
  have hrhoOne : rho < 1 := by
    exact supercriticalOffDiagonal_lt_one hk hgamma.2
  have hlower : qFloor ≤ rho - delta := by linarith
  have hupper : rho + delta ≤ 1 - qFloor := by linarith
  have hthreeLower : 3 * delta < rho := by linarith
  have hthreeUpper : rho + 3 * delta < 1 := by linarith
  simpa only [rho, qFloor] using
    ⟨halpha, hcandidate, hlower, hupper, hthreeLower, hthreeUpper⟩

/-- The same parameter choice places the exact profile-density band inside
the quarter-width interval used by the matching success-floor lemma. -/
theorem supercriticalMatchingDeltaBound_four_mul_le
    {k : ℕ} {gamma alpha delta : ℝ}
    (hdelta : delta < supercriticalMatchingDeltaBound k gamma alpha) :
    4 * delta ≤
      min (supercriticalOffDiagonal k gamma)
        (1 - supercriticalOffDiagonal k gamma) := by
  let rho := supercriticalOffDiagonal k gamma
  let qFloor := supercriticalMatchingSuccessFloor k gamma
  have hright := hdelta.trans_le
    (min_le_right (alpha / 100)
      (min (qFloor / 2) (1 / (6 * ((k - 1 : ℕ) : ℝ)))))
  have hfloor : delta < qFloor / 2 := hright.trans_le
    (min_le_left (qFloor / 2) (1 / (6 * ((k - 1 : ℕ) : ℝ))))
  dsimp [qFloor, supercriticalMatchingSuccessFloor,
    mediumSuccessProbabilityFloor, rho] at hfloor ⊢
  linarith

/-! ## Paper-facing parameter hierarchy -/

/-- Paper: Lemma `lemma:super-FPiT`, using one matching-wide orientation.

For every admissible supercritical density, a constant depending only on
`k` and `gamma` gives the required linear-in-`h(T)n` penalty in every exact
combined-defect/profile fiber.  The small parameters are quantified in the
paper's order; BCLSV alignment enters only when a nonempty fiber is converted
to the explicit hypotheses of `supercriticalMatchingPenalty_of_closeStructure`.
-/
theorem superFPiT
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1) :
    ∃ cMat : ℝ, 0 < cMat ∧
      ∀ alpha : ℝ,
        alpha ∈ Set.Ioo (0 : ℝ) (1 / (100 * (k : ℝ))) →
        ∃ delta0 : ℝ, 0 < delta0 ∧
          ∀ delta : ℝ, 0 < delta → delta < delta0 →
            ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
              ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilon0 →
                ∃ tau : ℝ, 0 < tau ∧
                  ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
                    ∀ (m : ℕ) (hn : k - 1 ≤ n)
                      (D : SupercriticalDivision k (Fin n))
                      (T : SimpleGraph (Fin n))
                      (profile : SupercriticalEdgeProfile D),
                      T ∈ supercriticalCombinedDefectPatternFinset
                          k hk gamma hgamma m n tau hn D →
                      SupercriticalProfileAtShift D m
                          (supercriticalOffDiagonal k gamma) delta
                          (supercriticalDefectShift T D) profile →
                      ((supercriticalFixedDefectProfileGraphFinset
                          k hk gamma hgamma alpha m n tau hn D T profile).card :
                            ℝ) ≤
                        (supercriticalProfileMultiplicity profile : ℝ) *
                          Real.exp (-(cMat *
                            (supercriticalMatchingNumber D T : ℝ) *
                            (n : ℝ))) := by
  classical
  let cMat := supercriticalMatchingPenaltyConstant k gamma
  have hcMat : 0 < cMat :=
    supercriticalMatchingPenaltyConstant_pos hk hgamma
  refine ⟨cMat, hcMat, ?_⟩
  intro alpha halpha
  let delta0 := supercriticalMatchingDeltaBound k gamma alpha
  have hdelta0 : 0 < delta0 :=
    supercriticalMatchingDeltaBound_pos hk hgamma halpha.1
  refine ⟨delta0, hdelta0, ?_⟩
  intro delta hdelta hdeltaLt
  obtain ⟨hdeltaAlpha, hdeltaCount, _hlower, _hupper,
      hrhoLower, hrhoUpper⟩ :=
    supercriticalMatchingDeltaBound_spec hk hgamma hdeltaLt
  have hdeltaFloor : 4 * delta ≤
      min (supercriticalOffDiagonal k gamma)
        (1 - supercriticalOffDiagonal k gamma) :=
    supercriticalMatchingDeltaBound_four_mul_le hdeltaLt
  refine ⟨(1 : ℝ), by norm_num, ?_⟩
  intro epsilon hepsilon _hepsilonLt
  let tau := supercriticalCloseStructureCutRadius k hk gamma hgamma alpha
    halpha delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon
  have htau : 0 < tau := by
    dsimp [tau]
    exact supercriticalCloseStructureCutRadius_pos k hk gamma hgamma alpha
      halpha delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon
  refine ⟨tau, htau, ?_⟩
  obtain ⟨nCore, hnCore⟩ := eventually_atTop.1
    (supercriticalMatchingPenalty_of_closeStructure k hk gamma hgamma)
  let nClose := supercriticalCloseStructureVertexThreshold k hk gamma hgamma
    alpha halpha delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon
  refine ⟨max nCore nClose, ?_⟩
  intro n hnLarge m hn D T profile hT hprofile
  have hnCore' : nCore ≤ n := (Nat.le_max_left _ _).trans hnLarge
  have hnClose : nClose ≤ n := (Nat.le_max_right _ _).trans hnLarge
  let F := supercriticalFixedDefectProfileGraphFinset
    k hk gamma hgamma alpha m n tau hn D T profile
  by_cases hF : F = ∅
  · change ((F.card : ℕ) : ℝ) ≤ _
    rw [hF]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hF
    obtain ⟨G, hG⟩ := hFne
    have hGprofile : G ∈ supercriticalFixedDefectProfileGraphFinset
        k hk gamma hgamma alpha m n tau hn D T profile := by
      simpa [F] using hG
    have hGfixed :=
      (mem_supercriticalFixedDefectProfileGraphFinset.mp hGprofile).1
    have hGdivision :=
      (mem_supercriticalFixedDefectGraphFinset.mp hGfixed).1
    have hcloseMem :=
      (mem_supercriticalDivisionDefectGraphFinset.mp hGdivision).1
    have hfamily : G ∈
        inducedFreeGraphFinsetWithEdges (inducedStar k) n m \
          supercriticalFarGraphFinset k hk gamma hgamma m n tau := by
      rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
      exact hcloseMem
    obtain ⟨R⟩ := superCloseStructureK1k k hk gamma hgamma alpha
      halpha delta hdelta hdeltaAlpha hrhoLower hrhoUpper epsilon hepsilon
      m hnClose G (by simpa [tau] using hfamily)
    have hdivision :=
      (mem_supercriticalDivisionDefectGraphFinset.mp hGdivision).2.1
    have hcastSub : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have hbalanced : ∀ i : Fin (k - 1),
        |((D.parts i).card : ℝ) -
            (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n := by
      intro i
      simpa only [hdivision, hcastSub] using R.part_card_close i
    have hlow : ∀ v : Fin n, ∀ i : Fin (k - 1),
        HasLowDegreeInPart T alpha D v i :=
      low_degree_everywhere_of_mem_fixedDefectProfile hGprofile R
    change ((F.card : ℕ) : ℝ) ≤ _
    simpa [F, cMat] using
      hnCore n hnCore' alpha m tau hn D T profile hT delta halpha
        hdelta.le hdeltaCount hdeltaFloor hbalanced hlow hprofile

end InducedStars
