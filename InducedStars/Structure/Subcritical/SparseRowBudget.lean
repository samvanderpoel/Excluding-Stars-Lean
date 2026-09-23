import InducedStars.Structure.Subcritical.SparseRetainedRows
import InducedStars.Structure.Subcritical.SingletonTargetGain

/-!
# The singleton-safe sparse retained-row budget

Paper: Lemma `lemma:sparse-retained-row-budget-K1k`. The source comparison remains admissible by using a donor swap or a bounded-cost regular-core replacement.
-/

noncomputable section
open scoped Classical
namespace InducedStars

variable {k n R₀ : ℕ} {G : SimpleGraph (Fin n)}
  {D : SubcriticalDivision k (Fin n)} {eta : ℝ}

/-- Every high-target source is removable. The proof treats donor
components and all-singleton components separately; it never deletes an
empty part while retaining its core vertex. -/
theorem subcriticalHighTarget_source_card_ge_two
    (hk : 3 ≤ k) {L : AdmissibleBlockSequence k} {omega delta epsilon : ℝ}
    (P : SubcriticalSparseRowParameters k R₀ eta)
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta P.theta P.alpha delta epsilon)
    (hminimal : ∀ E : SubcriticalDivision k (Fin n),
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (hR₀ : 1 ≤ R₀) (heta : 0 ≤ eta) (homega : omega ≤ 1)
    (hscale : 32 * (k : ℝ) ^ 3 ≤ P.theta * n)
    {v : Fin n} (hv : v ∈ D.nonretainedVertices eta R₀)
    (a : D.PartIndex) (hva : v ∈ D.part a)
    (b : D.PartIndex) (hb : b ∈ D.retainedPartIndices eta R₀)
    (hrow : (1 - P.alpha) * (D.part b).card ≤ (degreeInFinset G v (D.part b) : ℝ)) :
    2 ≤ (D.part a).card := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hcube : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hscale8 : 8 ≤ P.theta * n := by linarith
  by_cases hdonor : ∃ j : Fin (D.core a.1).order, 2 ≤ (D.parts a.1 j).card
  · exact subcriticalHighTarget_source_card_ge_two_of_donor hk R hminimal hR₀ heta
      homega P.alpha_quarter P.relocation_reserve hscale8 hv a hva hdonor b hb hrow
  have hsingle : ∀ j : Fin (D.core a.1).order, (D.parts a.1 j).card = 1 := by
    intro j
    have hp := (D.parts_nonempty a.1 j).card_pos
    have hn : ¬ 2 ≤ (D.parts a.1 j).card := fun hj ↦ hdonor ⟨j, hj⟩
    omega
  have htarget : b.1 ≠ a.1 := by
    intro hba
    have ha : a ∈ D.retainedPartIndices eta R₀ := by
      simpa only [D.mem_retainedPartIndices, hba] using hb
    exact (D.mem_nonretainedVertices eta R₀ v).mp hv
      (D.part_subset_retainedVertices ha hva)
  have hgain := subcriticalMinimal_singleton_component_target_gain_le hk G D hminimal
    a.1 hsingle v (D.mem_componentSupport.mpr ⟨a.2, hva⟩) b htarget
  have hgainR : 2 * (degreeInFinset G v (D.part b) : ℝ) ≤
      (D.part b).card + 4 * (k : ℝ) ^ 3 := by exact_mod_cast hgain
  have hlower := R.visible_part_card_ge_half homega b
    (D.retainedPartIndices_subset_visiblePartIndices hR₀ P.theta_pos.le P.retained_visible hb)
  have hcard : (0 : ℝ) ≤ (D.part b).card := by positivity
  have halpha := P.alpha_quarter
  exfalso
  nlinarith

/-- Pure finite sparse-row core. Its inputs are actual finite minimality,
proved row constraints, and geometric bounds; no counting or probability
certificate is assumed. The comparison divisions remain valid in each source case. -/
theorem subcriticalSparseRetainedRowBudget_of_closeStructure
    (hk : 3 ≤ k) {L : AdmissibleBlockSequence k} {omega delta epsilon : ℝ}
    (P : SubcriticalSparseRowParameters k R₀ eta)
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta P.theta P.alpha delta epsilon)
    (C : SubcriticalRowConstraints G D P.alpha P.theta)
    (hminimal : ∀ E : SubcriticalDivision k (Fin n),
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (hR₀ : 1 ≤ R₀) (heta : 0 ≤ eta) (homega : omega ≤ 1)
    (hscale : 32 * (k : ℝ) ^ 3 ≤ P.theta * n) :
    SubcriticalSparseRetainedRowBudget G D eta P.theta P.alpha R₀ := by
  intro v hv hhigh
  obtain ⟨t, ht, hrow⟩ := hhigh
  obtain ⟨b, hbret, _, hrowb⟩ := subcriticalRetainedHighRow_has_high_target C P.alpha_pos.le
    (D.retainedPartIndices_subset_visiblePartIndices hR₀ P.theta_pos.le P.retained_visible)
    hv ht hrow
  have hnotSparse := subcritical_not_sparse_of_high_target hminimal
    (by have h := P.alpha_quarter; linarith : P.alpha < 1 / 2) v b hrowb
  have hvSupport : v ∈ D.support := by simpa only [D.mem_sparse, not_not] using hnotSparse
  obtain ⟨a, hva⟩ := D.mem_support.mp hvSupport
  have hsource := subcriticalHighTarget_source_card_ge_two hk P R hminimal hR₀ heta
    homega hscale hv a hva b hbret hrowb
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hcube : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hscale8 : 8 ≤ P.theta * n := by linarith
  obtain ⟨_, hown, hcard⟩ := subcriticalSparseRetainedRowBudget_of_removable_source hk R C
    hminimal hR₀ heta P.theta_pos homega P.alpha_pos.le P.alpha_quarter P.alpha_budget
    P.retained_visible P.relocation_reserve hscale8 hv a hva hsource ⟨t, ht, hrow⟩
  refine ⟨hnotSparse, ?_, hcard⟩
  intro c hvc
  have hac := D.mem_part_unique hva hvc
  subst c
  exact hown

/-- Paper: Lemma `lemma:sparse-retained-row-budget-K1k`.
The radius is chosen before the candidate representation. Only the finite
threshold depends on that representation; there is no hidden source-size
assumption. The proof includes singleton-safe source comparisons. -/
theorem subcriticalSparseRetainedRowBudget
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (_hgamma : gamma ∈ Set.Ioo (0 : ℝ) (gammaK k))
    (R₀ : ℕ) (hR₀ : 1 ≤ R₀) (eta : ℝ) (heta : 0 < eta)
    (P : SubcriticalSparseRowParameters k R₀ eta)
    (omega delta epsilon : ℝ) (homega : 0 < omega) (homegaOne : omega ≤ 1)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      WLambda hk L ∈ candidateOptimizerFamily k gamma →
        ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
          ∀ (m : ℕ) (G : SimpleGraph (Fin n)),
            G ∈ subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau →
              SubcriticalSparseRetainedRowBudget G
                (canonicalSubcriticalDivision G R₀ hk (by simpa using hn0.trans hn))
                eta P.theta P.alpha R₀ := by
  let deltaRow := min delta (subcriticalRowCountingTolerance k) / 2
  have hdeltaRow : 0 < deltaRow :=
    div_pos (lt_min hdelta (subcriticalRowCountingTolerance_pos hk)) (by norm_num)
  have hdeltaRow_le : deltaRow ≤ subcriticalRowCountingTolerance k := by
    have hmin := min_le_right delta (subcriticalRowCountingTolerance k)
    have htol := (subcriticalRowCountingTolerance_pos hk).le
    dsimp [deltaRow]
    linarith
  obtain ⟨tau, htau, hbridge⟩ := subcriticalCloseStructure k hk R₀ hR₀
    omega eta P.theta P.alpha deltaRow epsilon homega heta P.theta_pos P.alpha_pos
    hdeltaRow hepsilon
  refine ⟨tau, htau, ?_⟩
  intro L _hL
  obtain ⟨nBridge, hnBridge, hbridge⟩ := hbridge L
  let n0 := max nBridge (max (Nat.ceil (8 / (P.alpha * P.theta)))
    (Nat.ceil (32 * (k : ℝ) ^ 3 / P.theta)))
  have hn0 : k - 1 ≤ n0 := hnBridge.trans (le_max_left _ _)
  refine ⟨n0, hn0, ?_⟩
  intro n hn m G hG
  have hnBridge' : nBridge ≤ n := (le_max_left _ _).trans hn
  have hrowceil : Nat.ceil (8 / (P.alpha * P.theta)) ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hcoreceil : Nat.ceil (32 * (k : ℝ) ^ 3 / P.theta) ≤ n :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hrowdiv : 8 / (P.alpha * P.theta) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hrowceil)
  have hcorediv : 32 * (k : ℝ) ^ 3 / P.theta ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hcoreceil)
  have hrowscale : 8 ≤ P.alpha * P.theta * n := by
    have h := (div_le_iff₀ (mul_pos P.alpha_pos P.theta_pos)).mp hrowdiv
    simpa only [mul_comm] using h
  have hcorescale : 32 * (k : ℝ) ^ 3 ≤ P.theta * n := by
    have h := (div_le_iff₀ P.theta_pos).mp hcorediv
    simpa only [mul_comm] using h
  have hmem := mem_subcriticalCandidateCutBallGraphFinset.mp hG
  have hfree := (mem_inducedStarFreeGraphFinsetWithEdges.mp hmem.1).1
  obtain ⟨R⟩ := hbridge hnBridge' G hmem.2
  have C := subcriticalRowConstraints_of_closeStructure hk R hfree homegaOne
    P.alpha_pos P.theta_pos hdeltaRow_le hrowscale
  exact subcriticalSparseRetainedRowBudget_of_closeStructure hk P R C
    (canonicalSubcriticalDivision_minimal G R₀ hk (by simpa using hn0.trans hn))
    hR₀ heta.le homegaOne hcorescale

end InducedStars
