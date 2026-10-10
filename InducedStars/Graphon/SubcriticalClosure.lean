import InducedStars.Graphon.BlockSequenceCompactness
import InducedStars.Graphon.CutLimit
import InducedStars.Graphon.FiniteBlockApproximation

/-!
# Local closure of the subcritical candidate family

This file proves the fixed-interior-density closure statement used in the
proof of `prop:graphon-char-fixed-gamma`. The limiting block construction
controls omitted components by their quadratic mass.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace InducedStars

/-- A sequence of admissible block graphons whose masses converge to the
positive mass prescribed at a fixed subcritical interior density has an exact
candidate limit in the same cut-distance-zero class.

Paper: the fixed-interior-density closure step in
`prop:graphon-char-fixed-gamma`. -/
theorem subcriticalCandidate_limit
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k))
    (L : ℕ → AdmissibleBlockSequence k)
    (W : Graphon)
    (hmass :
      Tendsto (fun m ↦ (L m).mass) atTop
        (nhds (γ / (1 + ((k - 2 : ℕ) : ℝ) * pK k))))
    (hcut :
      Tendsto (fun m ↦ cutDist (WLambda hk (L m)) W)
        atTop (nhds 0)) :
    ∃ Llim : AdmissibleBlockSequence k,
      IsSubcriticalCandidate k γ Llim ∧
      cutDist W (WLambda hk Llim) = 0 := by
  let hp : pK k ∈ Ioo (0 : ℝ) 1 :=
    ⟨pK_pos (by omega : 2 ≤ k), pK_lt_one (by omega : 2 ≤ k)⟩
  have hden : 0 < 1 + ((k - 2 : ℕ) : ℝ) * pK k := by
    have := hp.1
    positivity
  have hM : 0 < γ / (1 + ((k - 2 : ℕ) : ℝ) * pK k) :=
    div_pos hγ.1 hden
  obtain ⟨σ, hσ, Llim, hLmass, hprofile⟩ :=
    exists_positiveMass_profileBlock_limit k hk (pK k) hp L
      (γ / (1 + ((k - 2 : ℕ) : ℝ) * pK k)) hM hmass
  have hstage :
      Tendsto
        (fun m ↦ cutDist (WLambda hk (L (σ m))) (WLambda hk Llim))
        atTop (nhds 0) := by
    simpa only [profileWLambda_pK hk] using hprofile
  have htarget :
      Tendsto (fun m ↦ cutDist (WLambda hk (L (σ m))) W)
        atTop (nhds 0) := by
    simpa only [Function.comp_def] using hcut.comp hσ.tendsto_atTop
  refine ⟨Llim, ?_, cutDist_eq_zero_of_common_approximation htarget hstage⟩
  simpa only [IsSubcriticalCandidate, blockSequenceMass_eq_mass] using hLmass

namespace OptimizerFiniteBlockApproximationResult

variable {k : ℕ} {γ : ℝ} {W : Graphon}

/-- Constructive subcritical limit: the canonical finite block approximation
produces an actual limiting admissible sequence with the exact prescribed
mass and the optimizer target in its cut-distance-zero class. -/
theorem exists_subcritical_limit_sequence
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hsub : γ < gammaK k) :
    ∃ Llim : AdmissibleBlockSequence k,
      IsSubcriticalCandidate k γ Llim ∧
      cutDist A.extremalApproximation.target (WLambda A.three_le_k Llim) = 0 := by
  apply subcriticalCandidate_limit k A.three_le_k γ ⟨hγ.1, hsub⟩
    A.blockSequence A.extremalApproximation.target
  · change Tendsto A.blockMass atTop
      (nhds (γ / (1 + ((k - 2 : ℕ) : ℝ) * pK k)))
    exact A.subcriticalBlockMass_tendsto hsub
  · apply A.cut_tendsto.congr'
    filter_upwards [] with m
    rw [A.blockGraphon_eq_WLambda_of_lt_gammaK hγ hsub m]

/-- Every subcritical optimizer target is cut-equivalent to an exact member
of the candidate family at the original fixed density. -/
theorem exists_subcritical_candidate_equivalent
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hsub : γ < gammaK k) :
    ∃ V : Graphon,
      V ∈ candidateOptimizerFamily k γ ∧
      cutDist A.extremalApproximation.target V = 0 := by
  obtain ⟨Llim, hLlim, hcut⟩ := A.exists_subcritical_limit_sequence hγ hsub
  refine ⟨WLambda A.three_le_k Llim, ?_, hcut⟩
  rw [candidateOptimizerFamily_of_lt A.three_le_k hγ hsub]
  exact ⟨Llim, hLlim, rfl⟩

end OptimizerFiniteBlockApproximationResult

end InducedStars
