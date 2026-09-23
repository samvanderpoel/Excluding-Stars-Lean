import InducedStars.Structure.Supercritical.MediumCandidateAbundance
import InducedStars.Structure.Supercritical.MediumFiberPenalty
import InducedStars.Structure.Supercritical.MediumParameters
import Mathlib.Tactic

/-!
# The supercritical medium-degree penalty

This file performs the final uniform aggregation.  The core theorem takes the
five deterministic conclusions of close structure as explicit finite data;
the paper-facing wrapper is the only step which invokes the published BCLSV
alignment input through `superCloseStructureK1k`.
-/

noncomputable section

open Filter Finset Set

namespace InducedStars

/-! ## Uniform finite core -/

/-- The complete medium-degree penalty once close-structure records are
supplied for the defective canonical-division family.  Among project-specific
inputs this theorem uses only the Riordan--Warnke principal Janson instance;
in particular it does not invoke finite graphon alignment. -/
theorem supercriticalMediumDegreePenalty_of_closeStructure
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    {alpha delta epsilon : ℝ} (halpha : 0 < alpha)
    (hdelta : 0 < delta)
    (hdeltaCandidate :
      delta < supercriticalMediumCandidateDeltaBound k)
    (hJansonRange : 2 * delta <
      min (supercriticalOffDiagonal k gamma)
        (1 - supercriticalOffDiagonal k gamma) / 2)
    (hprofileLower :
      0 < supercriticalOffDiagonal k gamma - 2 * delta)
    (hprofileUpper :
      supercriticalOffDiagonal k gamma + 2 * delta < 1)
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : 3 * epsilon < 1 / 2)
    (hepsilonCandidate :
      epsilon < supercriticalMediumCandidateRate k alpha / 2)
    (hdefectRate : supercriticalDefectPatternRate epsilon <
      supercriticalMediumBernoulliPenalty k gamma
        (supercriticalMediumCandidateRate k alpha) / 16)
    (hprofileRate :
      supercriticalMediumProfileComparisonRate k
          (supercriticalOffDiagonal k gamma) delta <
        supercriticalMediumBernoulliPenalty k gamma
          (supercriticalMediumCandidateRate k alpha) / 16) :
    ∀ᶠ n : ℕ in atTop, ∀ (m : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
      (D : SupercriticalDivision k (Fin n))
      (base : SupercriticalEdgeProfile D),
      SupercriticalProfileWindow D m
          (supercriticalOffDiagonal k gamma) delta
          ⌊epsilon * (n : ℝ) ^ 2⌋₊ base →
      (∀ G ∈ supercriticalDivisionDefectGraphFinset
          k hk gamma hgamma m n tau hn D,
        Nonempty (SupercriticalCloseStructureResult
          k hk gamma alpha delta epsilon hgamma G hn)) →
      ((supercriticalMediumDegreeGraphFinset
        k hk gamma hgamma alpha m n tau hn D).card : ℝ) ≤
        (supercriticalProfileMultiplicity base : ℝ) *
          Real.exp (-(supercriticalMediumPenalty k gamma alpha *
            (n : ℝ) ^ 2)) := by
  let candidateRate := supercriticalMediumCandidateRate k alpha
  let bernoulliPenalty :=
    supercriticalMediumBernoulliPenalty k gamma candidateRate
  let conditioningRate := bernoulliPenalty / 2
  let auxiliaryRate := bernoulliPenalty / 16
  have hcandidateRate : 0 < candidateRate := by
    exact supercriticalMediumCandidateRate_pos hk halpha
  have hbernoulliPenalty : 0 < bernoulliPenalty := by
    exact supercriticalMediumBernoulliPenalty_pos hk hgamma hcandidateRate
  have hconditioningRate : 0 < conditioningRate := by
    dsimp [conditioningRate]
    positivity
  have hauxiliaryRate : 0 < auxiliaryRate := by
    dsimp [auxiliaryRate]
    positivity
  have hfiberPenalty : bernoulliPenalty - conditioningRate =
      bernoulliPenalty / 2 := by
    dsimp [conditioningRate]
    ring
  have hnet : 0 < supercriticalMediumAggregatedPenalty k epsilon
      auxiliaryRate (supercriticalOffDiagonal k gamma) delta
        (bernoulliPenalty / 2) := by
    dsimp [supercriticalMediumAggregatedPenalty, auxiliaryRate,
      bernoulliPenalty, candidateRate] at hdefectRate hprofileRate ⊢
    linarith
  have hfinal : supercriticalMediumPenalty k gamma alpha ≤
      supercriticalMediumAggregatedPenalty k epsilon auxiliaryRate
        (supercriticalOffDiagonal k gamma) delta
          (bernoulliPenalty / 2) := by
    dsimp [supercriticalMediumPenalty,
      supercriticalMediumAggregatedPenalty, auxiliaryRate,
      bernoulliPenalty, candidateRate] at hdefectRate hprofileRate ⊢
    linarith
  have haggregate :=
    eventually_card_supercriticalMediumDegreeGraphFinset_le_profileMultiplicity_mul_exp_neg_aggregatedPenalty
      k hk hgamma hepsilon hepsilonSmall hauxiliaryRate
        (half_pos hbernoulliPenalty) hdelta.le hprofileLower hprofileUpper hnet
  have hconditioning := eventually_nsq_add_one_pow_le_exp
    (Fintype.card (SupercriticalPartPair k)) hconditioningRate
  have hnBase : ∀ᶠ n : ℕ in atTop,
      4 * ((k - 1 : ℕ) : ℝ) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (4 * ((k - 1 : ℕ) : ℝ)))
  have hnAlpha : ∀ᶠ n : ℕ in atTop,
      4 * ((k - 1 : ℕ) : ℝ) ≤ alpha * (n : ℝ) := by
    have htend : Tendsto (fun n : ℕ ↦ alpha * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop halpha
    exact htend.eventually
      (eventually_ge_atTop (4 * ((k - 1 : ℕ) : ℝ)))
  have hnDelta : ∀ᶠ n : ℕ in atTop,
      4 * ((k - 1 : ℕ) : ℝ) ≤ delta * (n : ℝ) := by
    have htend : Tendsto (fun n : ℕ ↦ delta * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hdelta
    exact htend.eventually
      (eventually_ge_atTop (4 * ((k - 1 : ℕ) : ℝ)))
  filter_upwards [haggregate, hconditioning, hnBase, hnAlpha, hnDelta,
      eventually_ge_atTop 1] with n haggregateN hconditioningN
        hnBaseN hnAlphaN hnDeltaN hnOne
  intro m tau hn D base hbase hresult
  have hmediumResult : ∀ G ∈ supercriticalMediumDegreeGraphFinset
      k hk gamma hgamma alpha m n tau hn D,
      Nonempty (SupercriticalCloseStructureResult
        k hk gamma alpha delta epsilon hgamma G hn) := by
    intro G hG
    exact hresult G (mem_supercriticalMediumDegreeGraphFinset.mp hG).1
  have hprofile : ∀ key ∈ supercriticalMediumRefinementKeyFinset
      k hk gamma hgamma alpha halpha m n tau hn D,
      SupercriticalProfileWindow D m
        (supercriticalOffDiagonal k gamma) delta
        ⌊epsilon * (n : ℝ) ^ 2⌋₊ key.profile := by
    intro key hkey
    exact supercriticalMediumRefinementKey_profile_mem_window_of_closeStructureResult
      halpha hmediumResult hkey
  have hcost : ∀ G ∈ supercriticalDivisionDefectGraphFinset
      k hk gamma hgamma m n tau hn D,
      supercriticalDefectCost G D ≤ ⌊epsilon * (n : ℝ) ^ 2⌋₊ := by
    intro G hG
    obtain ⟨R⟩ := hresult G hG
    have hdivision :=
      (mem_supercriticalDivisionDefectGraphFinset.mp hG).2.1
    have hcostReal : (supercriticalDefectCost G D : ℝ) ≤
        epsilon * (n : ℝ) ^ 2 := by
      simpa [canonicalSupercriticalDefectCost, hdivision] using
        R.canonicalDefectCost_le
    by_cases hz : supercriticalDefectCost G D = 0
    · simp [hz]
    · exact (Nat.le_floor_iff' hz).2 hcostReal
  have hfiber : ∀ key ∈ supercriticalMediumRefinementKeyFinset
      k hk gamma hgamma alpha halpha m n tau hn D,
      ((supercriticalMediumRefinedGraphFinset
        k hk gamma hgamma alpha halpha m n tau hn key).card : ℝ) ≤
        (supercriticalProfileMultiplicity key.profile : ℝ) *
          Real.exp (-(bernoulliPenalty / 2) * (n : ℝ) ^ 2) := by
    intro key hkey
    obtain ⟨K, hK⟩ := mem_supercriticalMediumRefinementKeyFinset.mp hkey
    subst key
    let w := supercriticalMediumWitnessOfMem halpha K.2
    have hdefect := (mem_supercriticalMediumDegreeGraphFinset.mp K.2).1
    have hdivision :=
      (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).2.1
    obtain ⟨R⟩ := hresult K.1 hdefect
    have hcastSub : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have hclose : ∀ i : Fin (k - 1),
        |((D.parts i).card : ℝ) -
            (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n := by
      intro i
      simpa only [hdivision, hcastSub] using R.part_card_close i
    have hbalanced : ∀ i : Fin (k - 1),
        (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
          ((D.parts i).card : ℝ) := by
      intro i
      exact supercriticalPart_card_lower_of_abs_close hk hdelta.le
        hdeltaCandidate.le hclose i
    have hcostReal : (supercriticalDefectCost K.1 D : ℝ) ≤
        epsilon * (n : ℝ) ^ 2 := by
      simpa [canonicalSupercriticalDefectCost, hdivision] using
        R.canonicalDefectCost_le
    have hcandidate : candidateRate * (n : ℝ) ^ k ≤
        ((mediumStarCandidateFinset hk w).card : ℝ) := by
      exact mediumStarCandidate_card_lower_rate_of_canonical hk halpha
        hdelta.le hdeltaCandidate.le hepsilon.le hepsilonCandidate.le
          hn hnBaseN hnAlphaN hdivision w hclose hcostReal
    have hblock : ∀ e : SupercriticalPartPair k,
        ((supercriticalMediumFixedModel w).block e).card ≤ n ^ 2 := by
      intro e
      change (supercriticalMediumCrossBlock w e).card ≤ n ^ 2
      rw [card_supercriticalMediumCrossBlock]
      have hleft :
          (supercriticalMediumSampledPart w e.left).card ≤ n := by
        have hpart : (D.parts e.left).card ≤ n := by
          simpa using Finset.card_le_univ (D.parts e.left)
        exact (Finset.card_le_card
          (supercriticalMediumSampledPart_subset w e.left)).trans hpart
      have hright :
          (supercriticalMediumSampledPart w e.right).card ≤ n := by
        have hpart : (D.parts e.right).card ≤ n := by
          simpa using Finset.card_le_univ (D.parts e.right)
        exact (Finset.card_le_card
          (supercriticalMediumSampledPart_subset w e.right)).trans hpart
      calc
        (supercriticalMediumSampledPart w e.left).card *
            (supercriticalMediumSampledPart w e.right).card ≤ n * n :=
          Nat.mul_le_mul hleft hright
        _ = n ^ 2 := by ring
    have hconditioningFactor :
        (supercriticalMediumFixedModel w).conditioningFactor ≤
          Real.exp (conditioningRate * (n : ℝ) ^ 2) := by
      exact ((supercriticalMediumFixedModel w).conditioningFactor_le_nsq_pow
        n hblock).trans (by simpa using hconditioningN)
    have hfiberK :=
      card_supercriticalMediumRefinedGraphFinset_le_profileMultiplicity_mul_exp
        halpha K hcandidateRate hdelta hbalanced hnDeltaN hnOne
          (by
            intro e
            have hc := R.cross_density_close e.left e.right
              e.left_ne_right
            simpa only [hdivision] using hc)
          hJansonRange hcandidate hconditioningFactor
    change ((supercriticalMediumRefinedGraphFinset
        k hk gamma hgamma alpha halpha m n tau hn
          (supercriticalMediumRefinementKeyOf halpha K)).card : ℝ) ≤
      (supercriticalProfileMultiplicity (crossEdgeProfile K.1 D) : ℝ) *
        Real.exp (-(bernoulliPenalty / 2) * (n : ℝ) ^ 2)
    simpa [w, candidateRate, bernoulliPenalty, conditioningRate,
      hfiberPenalty] using hfiberK
  have haggregated := haggregateN alpha halpha m tau hn D m
    ⌊epsilon * (n : ℝ) ^ 2⌋₊ base hbase hprofile hcost hfiber
  calc
    ((supercriticalMediumDegreeGraphFinset
      k hk gamma hgamma alpha m n tau hn D).card : ℝ) ≤
        (supercriticalProfileMultiplicity base : ℝ) *
          Real.exp (-supercriticalMediumAggregatedPenalty k epsilon
            auxiliaryRate (supercriticalOffDiagonal k gamma) delta
              (bernoulliPenalty / 2) * (n : ℝ) ^ 2) := haggregated
    _ ≤ (supercriticalProfileMultiplicity base : ℝ) *
        Real.exp (-(supercriticalMediumPenalty k gamma alpha *
          (n : ℝ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hnSq : 0 ≤ (n : ℝ) ^ 2 := by positivity
      nlinarith

/-! ## Paper-facing parameter hierarchy -/

/-- Explicit parameter hierarchy for the supercritical medium-degree
penalty.  The rate depends only on `k`, `gamma`, and `alpha`; `delta` is then
chosen, followed by `epsilon`, the close-structure cut radius, and the finite
vertex threshold. -/
theorem exists_supercriticalMediumDegreePenalty
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ)
      (1 / (100 * (k : ℝ)))) :
    ∃ cMed : ℝ, 0 < cMed ∧
      ∃ delta0 : ℝ, 0 < delta0 ∧
        ∀ delta : ℝ, 0 < delta → delta < delta0 →
          ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
            ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilon0 →
              ∃ tau : ℝ, 0 < tau ∧
                ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
                  ∀ (m : ℕ) (hn : k - 1 ≤ n)
                    (D : SupercriticalDivision k (Fin n))
                    (base : SupercriticalEdgeProfile D),
                    SupercriticalProfileWindow D m
                        (supercriticalOffDiagonal k gamma) delta
                        ⌊epsilon * (n : ℝ) ^ 2⌋₊ base →
                    ((supercriticalMediumDegreeGraphFinset
                      k hk gamma hgamma alpha m n tau hn D).card : ℝ) ≤
                      (supercriticalProfileMultiplicity base : ℝ) *
                        Real.exp (-(cMed * (n : ℝ) ^ 2)) := by
  classical
  let candidateRate := supercriticalMediumCandidateRate k alpha
  let bernoulliPenalty :=
    supercriticalMediumBernoulliPenalty k gamma candidateRate
  let cMed := supercriticalMediumPenalty k gamma alpha
  have hcandidateRate : 0 < candidateRate :=
    supercriticalMediumCandidateRate_pos hk halpha.1
  have hbernoulliPenalty : 0 < bernoulliPenalty :=
    supercriticalMediumBernoulliPenalty_pos hk hgamma hcandidateRate
  have hcMed : 0 < cMed :=
    supercriticalMediumPenalty_pos hk hgamma halpha.1
  refine ⟨cMed, hcMed, ?_⟩
  obtain ⟨delta0, hdelta0, hdeltaSpec⟩ :=
    exists_supercriticalMediumDelta0 hk hgamma halpha.1 hbernoulliPenalty
  refine ⟨delta0, hdelta0, ?_⟩
  intro delta hdelta hdelta0'
  obtain ⟨hdeltaAlpha, hJansonRange, hrhoThree, hrhoUpperThree,
    hprofileLower, hprofileUpper, hdeltaCandidate, hprofileRate⟩ :=
      hdeltaSpec hdelta hdelta0'
  obtain ⟨epsilonDefect, hepsilonDefect,
      hepsilonDefectSpec⟩ :=
    exists_epsilon0_supercriticalDefectPatternRate_lt
      (show 0 < bernoulliPenalty / 16 by positivity)
  let epsilon0 := min epsilonDefect (candidateRate / 2)
  have hepsilon0 : 0 < epsilon0 := by
    exact lt_min hepsilonDefect (half_pos hcandidateRate)
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro epsilon hepsilon hepsilon0'
  have hepsilonDefect' : epsilon < epsilonDefect :=
    lt_of_lt_of_le hepsilon0' (min_le_left _ _)
  have hepsilonCandidate : epsilon < candidateRate / 2 :=
    lt_of_lt_of_le hepsilon0' (min_le_right _ _)
  obtain ⟨hepsilonSmall, hdefectRate⟩ :=
    hepsilonDefectSpec hepsilon hepsilonDefect'
  let tau := supercriticalCloseStructureCutRadius k hk gamma hgamma alpha
    halpha delta hdelta hdeltaAlpha hrhoThree hrhoUpperThree
      epsilon hepsilon
  have htau : 0 < tau := by
    dsimp [tau]
    exact supercriticalCloseStructureCutRadius_pos k hk gamma hgamma alpha
      halpha delta hdelta hdeltaAlpha hrhoThree hrhoUpperThree
        epsilon hepsilon
  refine ⟨tau, htau, ?_⟩
  have hcore := supercriticalMediumDegreePenalty_of_closeStructure
    k hk hgamma halpha.1 hdelta hdeltaCandidate hJansonRange
      hprofileLower hprofileUpper hepsilon hepsilonSmall
        hepsilonCandidate hdefectRate (by
          simpa [bernoulliPenalty, candidateRate] using hprofileRate)
  obtain ⟨nCore, hnCore⟩ := eventually_atTop.1 hcore
  let nClose := supercriticalCloseStructureVertexThreshold k hk gamma hgamma
    alpha halpha delta hdelta hdeltaAlpha hrhoThree hrhoUpperThree
      epsilon hepsilon
  refine ⟨max nCore nClose, ?_⟩
  intro n hn m hnPart D base hbase
  have hnCore' : nCore ≤ n := (Nat.le_max_left _ _).trans hn
  have hnClose : nClose ≤ n := (Nat.le_max_right _ _).trans hn
  apply hnCore n hnCore' m tau hnPart D base hbase
  intro G hG
  have hclose := (mem_supercriticalDivisionDefectGraphFinset.mp hG).1
  have hfamily : G ∈ inducedFreeGraphFinsetWithEdges (inducedStar k) n m \
      supercriticalFarGraphFinset k hk gamma hgamma m n tau := by
    rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
    exact hclose
  have hR := superCloseStructureK1k k hk gamma hgamma alpha halpha delta
    hdelta hdeltaAlpha hrhoThree hrhoUpperThree epsilon hepsilon m hnClose G
      (by simpa [tau] using hfamily)
  simpa [nClose] using hR

/-- Paper: Lemma `lemma:super-FPiprime`.

The medium-degree defective family has a uniform quadratic exponential
penalty relative to every base profile in the admissible profile window. -/
theorem superFPiPrime
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ)
      (1 / (100 * (k : ℝ)))) :
    ∃ cMed : ℝ, 0 < cMed ∧
      ∃ delta0 : ℝ, 0 < delta0 ∧
        ∀ delta : ℝ, 0 < delta → delta < delta0 →
          ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
            ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilon0 →
              ∃ tau : ℝ, 0 < tau ∧
                ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
                  ∀ (m : ℕ) (hn : k - 1 ≤ n)
                    (D : SupercriticalDivision k (Fin n))
                    (base : SupercriticalEdgeProfile D),
                    SupercriticalProfileWindow D m
                        (supercriticalOffDiagonal k gamma) delta
                        ⌊epsilon * (n : ℝ) ^ 2⌋₊ base →
                    ((supercriticalMediumDegreeGraphFinset
                      k hk gamma hgamma alpha m n tau hn D).card : ℝ) ≤
                      (supercriticalProfileMultiplicity base : ℝ) *
                        Real.exp (-(cMed * (n : ℝ) ^ 2)) :=
  exists_supercriticalMediumDegreePenalty k hk gamma hgamma alpha halpha

end InducedStars
