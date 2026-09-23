import InducedStars.Graphon.CutLimit
import InducedStars.Graphon.EntropyUpperBound
import InducedStars.Graphon.Equivalence
import InducedStars.Graphon.SubcriticalClosure
import InducedStars.Graphon.SupercriticalClassification

/-!
# Fixed-density graphon optimizer classification

This file contains the set-theoretic and paper-facing endpoint of the
fixed-density optimizer classification.  The subcritical compactness and
supercritical concentration branches are imported below once established;
the definitions in this first section are independent of those branches.
-/

noncomputable section

open MeasureTheory Set

namespace InducedStars

/-- Saturation of a graphon set under cut-distance-zero equivalence. -/
def cutSaturation (S : Set Graphon) : Set Graphon :=
  {W | ∃ V ∈ S, cutDist W V = 0}

@[simp] theorem mem_cutSaturation {S : Set Graphon} {W : Graphon} :
    W ∈ cutSaturation S ↔ ∃ V ∈ S, cutDist W V = 0 :=
  Iff.rfl

/-- The paper's explicit graphon equivalence relation: two graphons have
measure-preserving pullbacks to the unit interval that agree almost
everywhere. -/
def GraphonEquivalent (U W : Graphon) : Prop :=
  ∃ φ ψ : UnitInterval → UnitInterval,
    MeasurePreserving φ volume volume ∧
    MeasurePreserving ψ volume volume ∧
    ∀ᵐ z ∂unitSquareMeasure,
      U.value (φ z.1, φ z.2) = W.value (ψ z.1, ψ z.2)

/-- Cut distance zero implies the exact measure-preserving-pullback
equivalence used in the paper. -/
theorem graphonEquivalent_of_cutDist_eq_zero
    (U W : Graphon) (hcut : cutDist U W = 0) :
    GraphonEquivalent U W :=
  commonPullback_of_cutDist_eq_zero U W hcut

/-! ## Reverse classification and cut saturation -/

/-- Every fixed-density optimizer is cut-equivalent to an exact member of
the piecewise candidate family. -/
theorem exists_candidate_cutEquivalent_of_optimizer
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (W : Graphon) (hW : W ∈ fixedDensityOptimizers k γ) :
    ∃ V : Graphon,
      V ∈ candidateOptimizerFamily k γ ∧
      cutDist W V = 0 := by
  obtain ⟨A⟩ := existsOptimizerFiniteBlockApproximation k hk γ hγ W hW
  have hcandidate :
      ∃ V : Graphon,
        V ∈ candidateOptimizerFamily k γ ∧
        cutDist A.extremalApproximation.target V = 0 := by
    by_cases hsub : γ < gammaK k
    · exact A.exists_subcritical_candidate_equivalent hγ hsub
    · exact A.exists_supercritical_candidate_equivalent hγ (le_of_not_gt hsub)
  obtain ⟨V, hV, htargetV⟩ := hcandidate
  refine ⟨V, hV, le_antisymm ?_ (cutDist_nonneg W V)⟩
  calc
    cutDist W V ≤
        cutDist W A.extremalApproximation.target +
          cutDist A.extremalApproximation.target V :=
      cutDist_triangle W A.extremalApproximation.target V
    _ = 0 := by
      rw [cutDist_comm W A.extremalApproximation.target,
        A.extremalApproximation.target_cut_eq_zero, htargetV,
        zero_add]

/-- Elementwise form of the complete fixed-density classification: the
optimizer set is exactly the cut-distance-zero saturation of the candidate
family. -/
theorem mem_fixedDensityOptimizers_iff_exists_candidate_cutDist_zero
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (W : Graphon) :
    W ∈ fixedDensityOptimizers k γ ↔
      ∃ V ∈ candidateOptimizerFamily k γ,
        cutDist W V = 0 := by
  constructor
  · exact exists_candidate_cutEquivalent_of_optimizer k hk γ hγ W
  · rintro ⟨V, hV, hcut⟩
    exact fixedDensityOptimizer_of_cutDist_eq_zero
      (candidate_mem_fixedDensityOptimizers k hk γ hγ hV) hcut

/-- Set equality expressing fixed-density optimizer classification under
cut-distance-zero saturation. -/
theorem fixedDensityOptimizers_eq_cutSaturation_candidateOptimizerFamily
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    fixedDensityOptimizers k γ = cutSaturation (candidateOptimizerFamily k γ) := by
  ext W
  exact mem_fixedDensityOptimizers_iff_exists_candidate_cutDist_zero
    k hk γ hγ W

/-! ## Paper-facing formulations -/

/-- Paper: Proposition `prop:graphon-char-fixed-gamma`.

At every fixed interior edge density, a graphon is an entropy optimizer
exactly when it lies at cut distance zero from one of the explicit candidate
graphons. -/
theorem graphonCharacterizationFixedDensity
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∀ W : Graphon,
      W ∈ fixedDensityOptimizers k γ ↔
        ∃ V ∈ candidateOptimizerFamily k γ,
          cutDist W V = 0 :=
  mem_fixedDensityOptimizers_iff_exists_candidate_cutDist_zero k hk γ hγ

/-- Literal formulation of the paper's phrase "up to equivalence": every
candidate is an optimizer, and every optimizer admits common
measure-preserving pullbacks with an exact candidate. -/
theorem graphonCharacterizationFixedDensity_upToEquivalence
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    (∀ V : Graphon,
        V ∈ candidateOptimizerFamily k γ →
          V ∈ fixedDensityOptimizers k γ) ∧
      ∀ W : Graphon,
        W ∈ fixedDensityOptimizers k γ →
          ∃ V ∈ candidateOptimizerFamily k γ,
            GraphonEquivalent W V := by
  constructor
  · intro V hV
    exact candidate_mem_fixedDensityOptimizers k hk γ hγ hV
  · intro W hW
    obtain ⟨V, hV, hcut⟩ :=
      exists_candidate_cutEquivalent_of_optimizer k hk γ hγ W hW
    exact ⟨V, hV, graphonEquivalent_of_cutDist_eq_zero W V hcut⟩

end InducedStars
