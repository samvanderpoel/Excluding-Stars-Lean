import InducedStars.Structure.Subcritical.Nonlow
import InducedStars.Structure.Subcritical.DeterministicRows
import InducedStars.Structure.Subcritical.Closeness

/-!
# The three deterministic row constraints in a subcritical candidate cut ball

Paper and auxiliary row constraints: `lemma:deterministic-nonlow-bound-K1k`,
`lemma:deterministic-medium-companion-K1k`, and
`lemma:deterministic-opposite-row-K1k`. The first two are current paper results; the opposite-row exclusion is an auxiliary compatibility result. Their proofs count the free vertices of a restricted induced pattern. The cut radius is chosen before
the candidate representation, and only the finite threshold may depend on
that representation.
-/

noncomputable section

open DenseGraph
open scoped Classical

namespace InducedStars

/-- The three literal deterministic row conclusions. This proposition
contains no assumed counting or alignment certificate. -/
structure SubcriticalRowConstraints {k n : ℕ} (G : SimpleGraph (Fin n))
    (D : SubcriticalDivision k (Fin n)) (alpha theta : ℝ) : Prop where
  nonlow : ∀ v : Fin n,
    (subcriticalNonlowVisibleParts G D alpha theta v).card ≤ k - 1
  medium_companion : ∀ (i : Fin D.componentCount),
    i ∈ D.visibleComponentIndices theta →
    ∀ (j : Fin (D.core i).order) (v : Fin n),
      v ∉ subcriticalCoreNeighborUnion D i j →
      alpha * (D.parts i j).card ≤ (degreeInFinset G v (D.parts i j) : ℝ) →
      (degreeInFinset G v (D.parts i j) : ℝ) ≤ (1 - alpha) * (D.parts i j).card →
      ∃ j', (D.core i).graph.Adj j j' ∧
        (1 - alpha) * (D.parts i j').card ≤ (degreeInFinset G v (D.parts i j') : ℝ)
  opposite_row : ∀ (i : Fin D.componentCount),
    i ∈ D.visibleComponentIndices theta →
    ∀ (j s : Fin (D.core i).order), (D.core i).graph.Adj j s →
      ∀ (v : Fin n), v ∈ D.parts i j →
        alpha * (D.parts i j).card ≤ (complementDegreeInFinset G v (D.parts i j) : ℝ) →
        alpha * (D.parts i s).card ≤ (degreeInFinset G v (D.parts i s) : ℝ) →
        (degreeInFinset G v (D.parts i s) : ℝ) ≤ (1 - alpha) * (D.parts i s).card →
        (∀ t, (D.core i).graph.Adj s t → t ≠ j →
          alpha * (D.parts i t).card ≤ (complementDegreeInFinset G v (D.parts i t) : ℝ)) →
        False

/-- Finite, capability-free assembly of the row constraints from explicit
bridge data and the actual local counting proofs. -/
theorem subcriticalRowConstraints_of_closeStructure
    {k n R₀ : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)}
    {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
    {omega eta theta alpha delta epsilon : ℝ}
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n) :
    SubcriticalRowConstraints G D alpha theta where
  nonlow := subcriticalNonlowVisibleParts_card_le hk R hfree homega halpha htheta hdelta hscale
  medium_companion := subcriticalMediumDegree_companion R hfree homega halpha htheta hdelta hscale
  opposite_row := subcriticalOppositeRow_impossible R hfree homega halpha htheta hdelta hscale

/-- Common project-facing wrapper for the three deterministic row lemmas.
The radius is uniform in the candidate representation; the exact edge count
and graph are quantified only after its finite threshold. The only published
input is the existing finite weighted alignment theorem inside the completed
cut-to-division bridge. The row conclusions follow from restricted induced-pattern counting. -/
theorem subcriticalRowConstraints_of_mem_candidateCutBall
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (_hgamma : gamma ∈ Set.Ioo (0 : ℝ) (gammaK k))
    (R₀ : ℕ) (hR₀ : 1 ≤ R₀)
    (omega eta theta alpha delta epsilon : ℝ)
    (homega : 0 < omega) (homegaOne : omega ≤ 1)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (_halphaHalf : alpha < 1 / 2)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      WLambda hk L ∈ candidateOptimizerFamily k gamma →
        ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
          ∀ (m : ℕ) (G : SimpleGraph (Fin n)),
            G ∈ subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau →
              SubcriticalRowConstraints G
                (canonicalSubcriticalDivision G R₀ hk (by simpa using hn0.trans hn))
                alpha theta := by
  let deltaRow := min delta (subcriticalRowCountingTolerance k) / 2
  have hdeltaRow : 0 < deltaRow :=
    div_pos (lt_min hdelta (subcriticalRowCountingTolerance_pos hk)) (by norm_num)
  have hdeltaRow_le : deltaRow ≤ subcriticalRowCountingTolerance k := by
    have hmin := min_le_right delta (subcriticalRowCountingTolerance k)
    have htol := (subcriticalRowCountingTolerance_pos hk).le
    dsimp [deltaRow]
    linarith
  obtain ⟨tau, htau, hbridge⟩ := subcriticalCloseStructure k hk R₀ hR₀
    omega eta theta alpha deltaRow epsilon homega heta htheta halpha hdeltaRow hepsilon
  refine ⟨tau, htau, ?_⟩
  intro L _hL
  obtain ⟨nBridge, hnBridge, hbridge⟩ := hbridge L
  let n0 := max nBridge (Nat.ceil (8 / (alpha * theta)))
  have hn0 : k - 1 ≤ n0 := hnBridge.trans (le_max_left _ _)
  refine ⟨n0, hn0, ?_⟩
  intro n hn m G hG
  have hnBridge' : nBridge ≤ n := (le_max_left _ _).trans hn
  have hceil : Nat.ceil (8 / (alpha * theta)) ≤ n := (le_max_right _ _).trans hn
  have hdiv : 8 / (alpha * theta) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hscale : 8 ≤ alpha * theta * n := by
    have h := (div_le_iff₀ (mul_pos halpha htheta)).mp hdiv
    simpa only [mul_comm] using h
  have hmem := mem_subcriticalCandidateCutBallGraphFinset.mp hG
  have hfree := (mem_inducedStarFreeGraphFinsetWithEdges.mp hmem.1).1
  obtain ⟨R⟩ := hbridge hnBridge' G hmem.2
  exact subcriticalRowConstraints_of_closeStructure hk R hfree homegaOne
    halpha htheta hdeltaRow_le hscale

end InducedStars
