import InducedStars.Structure.Subcritical.Closeness
import InducedStars.Structure.Subcritical.Retained
import InducedStars.Structure.Subcritical.SparseSide
import InducedStars.Structure.Subcritical.RetainedCounts
import InducedStars.Structure.Subcritical.RetainedShift

/-!
# Retained counting for an actual graph in a candidate cut ball

The finite candidate/division family uses the original graph's canonical
division. Structural tolerances and the cut radius are chosen before the
candidate representation, and only the order threshold may depend on it.
The edge-count vector here is the paper's `𝒎`, not a root/row/tail profile.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

/-- Explicit availability of the sparse-side parameter hierarchy. First
fix `eta`, then take any sufficiently large core cutoff, then arbitrarily
small positive `theta`, and finally arbitrarily small positive `epsilon`.
No residual-matching constant enters these choices. -/
theorem exists_subcriticalSparseSideHierarchy (eta : ℝ) (heta : 0 < eta) :
    ∃ Rmin : ℕ, 1 ≤ Rmin ∧ ∀ R₀ : ℕ, Rmin ≤ R₀ →
      1 / (R₀ : ℝ) ≤ eta ∧
        ∃ thetaMax : ℝ, 0 < thetaMax ∧
          ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax →
            theta ≤ eta / (2 * (R₀ : ℝ)) ∧
              ∃ epsilonMax : ℝ, 0 < epsilonMax ∧
                ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilonMax →
                  epsilon ≤ min eta (theta ^ 2) := by
  let Rmin := Nat.ceil (1 / eta) + 1
  refine ⟨Rmin, by dsimp [Rmin]; omega, ?_⟩
  intro R₀ hR₀
  have hRpos : (0 : ℝ) < R₀ := by
    have : 0 < R₀ := by dsimp [Rmin] at hR₀; omega
    exact_mod_cast this
  have hceil : Nat.ceil (1 / eta) ≤ R₀ := by
    dsimp [Rmin] at hR₀
    omega
  have hdiv : 1 / eta ≤ (R₀ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hproduct : 1 ≤ (R₀ : ℝ) * eta := (div_le_iff₀ heta).mp hdiv
  refine ⟨(div_le_iff₀ hRpos).mpr (by nlinarith),
    eta / (2 * (R₀ : ℝ)), by positivity, ?_⟩
  intro theta htheta hthetaMax
  refine ⟨hthetaMax, min eta (theta ^ 2),
    lt_min heta (sq_pos_of_pos htheta), ?_⟩
  intro epsilon _hepsilon hepsilonMax
  exact hepsilonMax

/-- The literal finite family `𝓕_{W,Π}`: an induced-star-free exact-edge
candidate cut ball filtered by equality with the canonical division.
The ambient-order proof is only the input needed by that existing selector.
This is not a later profile class. -/
def subcriticalCandidateDivisionGraphFinset
    (k n m : ℕ) (W : Graphon) (tau : ℝ) (R₀ : ℕ)
    (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (D : SubcriticalDivision k (Fin n)) : Finset (SimpleGraph (Fin n)) :=
  (subcriticalCandidateCutBallGraphFinset k n m W tau).filter fun G ↦
    canonicalSubcriticalDivision G R₀ hk (by simpa using hn) = D

@[simp] theorem mem_subcriticalCandidateDivisionGraphFinset
    {k n m : ℕ} {W : Graphon} {tau : ℝ} {R₀ : ℕ}
    {hk : 3 ≤ k} {hn : k - 1 ≤ n}
    {D : SubcriticalDivision k (Fin n)} {G : SimpleGraph (Fin n)} :
    G ∈ subcriticalCandidateDivisionGraphFinset k n m W tau R₀ hk hn D ↔
      G ∈ subcriticalCandidateCutBallGraphFinset k n m W tau ∧
        canonicalSubcriticalDivision G R₀ hk (by simpa using hn) = D := by
  simp [subcriticalCandidateDivisionGraphFinset]

namespace SubcriticalCloseStructureResult

variable {k n R₀ : ℕ} {hk : 3 ≤ k}
  {G : SimpleGraph (Fin n)} {D : SubcriticalDivision k (Fin n)}
  {L : AdmissibleBlockSequence k} {omega eta theta alpha delta epsilon : ℝ}

/-- Every retained part is itself at least `theta*n`, not just a member
of a component containing some large part. -/
theorem retainedPart_card_ge_theta
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hR : 1 ≤ R₀) (heta : 0 ≤ eta)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ)))
    {a : D.PartIndex} (ha : a ∈ D.retainedPartIndices eta R₀) :
    theta * n ≤ ((D.part a).card : ℝ) := by
  have hmul := mul_le_mul_of_nonneg_right hcutoff (Nat.cast_nonneg n)
  have hstep : theta * n ≤ eta * n / (2 * (R₀ : ℝ)) := by
    simpa only [div_mul_eq_mul_div] using hmul
  exact hstep.trans (R.retainedPart_card_lower_bound hR heta ha)

/-- Apply the bridge to whole retained active parts. This is the actual
graph density, and the conclusion uses the narrow tolerance `delta`.
The bound `alpha ≤ 4` suffices for the bridge's whole-part size test. -/
theorem retainedActivePart_density_close
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hR : 1 ≤ R₀) (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ))) (halpha : alpha ≤ 4)
    {a b : D.PartIndex} (ha : a ∈ D.retainedPartIndices eta R₀)
    (hb : b ∈ D.retainedPartIndices eta R₀) (hactive : D.ActivePart a b) :
    |Regularity.graphDensity G (D.part a) (D.part b) - pK k| ≤ delta := by
  have hne : a ≠ b := by
    intro hab
    obtain ⟨i, u, v, ha', hb', huv⟩ := hactive
    have huv' : u = v := by simpa using ha'.symm.trans (hab.trans hb')
    exact huv.ne huv'
  have hvis := D.retainedPartIndices_subset_visiblePartIndices hR htheta hcutoff
  have hsize {c : D.PartIndex} (hc : c ∈ D.retainedPartIndices eta R₀) :
      alpha * theta * n / 4 ≤ ((D.part c).card : ℝ) := by
    have hprod := mul_le_mul_of_nonneg_right halpha
      (mul_nonneg htheta (Nat.cast_nonneg n))
    have hpart := R.retainedPart_card_ge_theta hR heta hcutoff hc
    nlinarith
  have h := R.visible_subset_density ⟨a, hvis ha⟩ ⟨b, hvis hb⟩
    (D.part a) (D.part b) (D.part_disjoint hne) (fun _ h ↦ h) (fun _ h ↦ h)
    (hsize ha) (hsize hb)
  simpa only [subcriticalDivisionPartWeight, hne, hactive, ↓reduceIte] using h

end SubcriticalCloseStructureResult

/-- One common bridge threshold supplies the explicit sparse-side scale.
The radius is fixed before the candidate representation. -/
private theorem subcriticalCloseStructure_at_sparseSideScale
    (k : ℕ) (hk : 3 ≤ k) (R₀ : ℕ) (hR₀ : 1 ≤ R₀)
    (omega eta theta alpha delta epsilon : ℝ)
    (homega : 0 < omega) (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
        ∀ G : SimpleGraph (Fin n),
          cutDist (graphGraphon G) (WLambda hk L) < tau →
            1 ≤ theta * n ∧
              Nonempty (SubcriticalCloseStructureResult hk G
                (canonicalSubcriticalDivision G R₀ hk (by simpa using hn0.trans hn))
                L R₀ omega eta theta alpha delta epsilon) := by
  obtain ⟨tau, htau, hbridge⟩ := subcriticalCloseStructure k hk R₀ hR₀
    omega eta theta alpha delta epsilon homega heta htheta halpha hdelta hepsilon
  refine ⟨tau, htau, ?_⟩
  intro L
  obtain ⟨nBridge, hnBridge, hbridge⟩ := hbridge L
  let n0 := max nBridge (Nat.ceil (1 / theta))
  have hn0 : k - 1 ≤ n0 := hnBridge.trans (le_max_left _ _)
  refine ⟨n0, hn0, ?_⟩
  intro n hn G hG
  have hnBridge' : nBridge ≤ n := (le_max_left _ _).trans hn
  have hceil : Nat.ceil (1 / theta) ≤ n := (le_max_right _ _).trans hn
  have hdiv : 1 / theta ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hscale : 1 ≤ theta * n := by
    have h := (div_le_iff₀ htheta).mp hdiv
    simpa only [mul_comm] using h
  exact ⟨hscale, hbridge hnBridge' G hG⟩

private theorem subcriticalSparseSide_theta_le_eta
    {R₀ : ℕ} {eta theta : ℝ} (hR₀ : 1 ≤ R₀) (heta : 0 ≤ eta)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ))) : theta ≤ eta := by
  have hR : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR₀
  exact hcutoff.trans (div_le_self heta (by linarith))

/-- Paper: Lemma `lemma:SubCompareSparseSideEdgesK1k`, all three items.
The single constant `subcriticalSparseSideConstant k = 100*k^2` is fixed
before the density and every structural tolerance. The cut radius is
uniform in the candidate representation; the exact edge count is arbitrary
after the order threshold. Only the existing finite weighted alignment
input is inherited through the completed bridge. -/
theorem subcriticalSparseSideControls_of_mem_candidateCutBall
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (_hgamma : gamma ∈ Set.Ioo (0 : ℝ) (gammaK k))
    (R₀ : ℕ) (hR₀ : 1 ≤ R₀)
    (omega eta theta alpha delta epsilon : ℝ)
    (homega : 0 < omega) (homegaOne : omega ≤ 1)
    (heta : 0 < eta) (htheta : 0 < theta) (halpha : 0 < alpha)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hinv : 1 / (R₀ : ℝ) ≤ eta)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ)))
    (hepsilonCap : epsilon ≤ min eta (theta ^ 2)) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      WLambda hk L ∈ candidateOptimizerFamily k gamma →
        ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
          ∀ (m : ℕ) (G : SimpleGraph (Fin n)),
            G ∈ subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau →
              let D := canonicalSubcriticalDivision G R₀ hk (by simpa using hn0.trans hn)
              (inducedEdgeCount G (D.nonretainedVertices eta R₀) : ℝ) ≤
                  subcriticalSparseSideConstant k * eta * (n : ℝ)^2 ∧
                (∀ A ⊆ D.nonretainedSmallVertices eta R₀ theta,
                  (inducedEdgeCount G A : ℝ) ≤
                    subcriticalSparseSideConstant k * theta * n * A.card +
                      epsilon * (n : ℝ)^2) ∧
                (∀ x : Fin n,
                  (degreeInFinset G x (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
                    subcriticalSparseSideConstant k * theta * n) := by
  obtain ⟨tau, htau, hbridge⟩ := subcriticalCloseStructure_at_sparseSideScale
    k hk R₀ hR₀ omega eta theta alpha delta epsilon
      homega heta htheta halpha hdelta hepsilon
  refine ⟨tau, htau, ?_⟩
  intro L _hL
  obtain ⟨n0, hn0, hbridge⟩ := hbridge L
  refine ⟨n0, hn0, ?_⟩
  intro n hn m G hG
  obtain ⟨hball, hcut⟩ := mem_subcriticalCandidateCutBallGraphFinset.mp hG
  have hfree := (mem_inducedStarFreeGraphFinsetWithEdges.mp hball).1
  obtain ⟨hscale, ⟨R⟩⟩ := hbridge hn G hcut
  exact R.sparseSideControls heta.le hR₀ hinv homegaOne
    (subcriticalSparseSide_theta_le_eta hR₀ heta.le hcutoff)
    (hepsilonCap.trans (min_le_left _ _)) (hepsilonCap.trans (min_le_right _ _))
    hscale hfree

/-- The stronger actual-graph shift window uses one copy of the defect
error. Both bounds follow from the signed decomposition; there is no
nonnegative-shift hypothesis. -/
theorem retainedEdgeShift_mem_strongWindow_of_bounds
    {k n R₀ : ℕ} (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n))
    {eta C epsilon : ℝ}
    (hsparse : (inducedEdgeCount G (D.nonretainedVertices eta R₀) : ℝ) ≤
      C * eta * (n : ℝ) ^ 2)
    (hdefect : (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ) ^ 2) :
    -epsilon * (n : ℝ) ^ 2 ≤ (retainedEdgeShift G D eta R₀ : ℝ) ∧
      (retainedEdgeShift G D eta R₀ : ℝ) ≤
        C * eta * (n : ℝ) ^ 2 + epsilon * (n : ℝ) ^ 2 := by
  have habs : |(retainedEdgeShift G D eta R₀ : ℝ) -
      (inducedEdgeCount G (D.nonretainedVertices eta R₀) : ℝ)| ≤
        (subcriticalDefectCost G D : ℝ) := by
    exact_mod_cast abs_retainedEdgeShift_sub_nonretainedEdgeCount_le G D eta R₀
  obtain ⟨hlo, hhi⟩ := abs_le.mp habs
  have hnonneg := Nat.cast_nonneg (α := ℝ)
    (inducedEdgeCount G (D.nonretainedVertices eta R₀))
  constructor <;> linarith

namespace SubcriticalCloseStructureResult

variable {k n R₀ : ℕ} {hk : 3 ≤ k}
  {G : SimpleGraph (Fin n)} {D : SubcriticalDivision k (Fin n)}
  {L : AdmissibleBlockSequence k} {omega eta theta alpha delta epsilon : ℝ}

/-- Whole retained active parts put the actual edge-count vector in the
narrow level at its exact signed shift. This assertion needs neither
star-freeness nor a sparse-side estimate. -/
theorem actualRetainedEdgeCountVector_mem_narrowLevel
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hR : 1 ≤ R₀) (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ))) (halpha : alpha ≤ 4)
    {m : ℕ} (hedges : (finiteGraphEdges G).card = m) :
    actualRetainedEdgeCountVector G D eta R₀ ∈
      retainedNarrowEdgeCountLevel D eta R₀ m delta (retainedEdgeShift G D eta R₀) := by
  refine mem_retainedNarrowEdgeCountLevel.mpr ⟨?_, ?_⟩
  · simpa only [hedges] using retainedEdgeCountTotal_add_shift G D eta R₀
  · intro e
    rw [retainedEdgeCountDensity_actual_eq_graphDensity]
    have h := R.retainedActivePart_density_close hR heta htheta hcutoff halpha
      e.leftPart_mem_retained e.rightPart_mem_retained e.activePart
    obtain ⟨hl, hu⟩ := abs_le.mp h
    constructor <;> linarith

/-- The actual vector belongs to the paper's full narrow shift window.
The proof first obtains the stronger one-error shift bound. All inputs
here are explicit finite geometric facts packaged by the existing bridge. -/
theorem actualRetainedEdgeCountVector_mem_narrowWindow
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hR : 1 ≤ R₀) (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hinv : 1 / (R₀ : ℝ) ≤ eta) (homega : omega ≤ 1)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ))) (halpha : alpha ≤ 4)
    (hepsilonCap : epsilon ≤ min eta (theta ^ 2)) (hscale : 1 ≤ theta * n)
    (hfree : ¬Regularity.InducedEmbeds (inducedStar k) G)
    {m : ℕ} (hedges : (finiteGraphEdges G).card = m) :
    actualRetainedEdgeCountVector G D eta R₀ ∈
      retainedNarrowEdgeCountWindow D eta R₀ m
        (subcriticalSparseSideConstant k) delta epsilon := by
  have hsparse := (R.sparseSideControls heta hR hinv homega
    (subcriticalSparseSide_theta_le_eta hR heta hcutoff)
    (hepsilonCap.trans (min_le_left _ _)) (hepsilonCap.trans (min_le_right _ _))
    hscale hfree).1
  obtain ⟨hlo, hhi⟩ := retainedEdgeShift_mem_strongWindow_of_bounds G D
    hsparse R.defect_cost_le
  have herror : 0 ≤ epsilon * (n : ℝ) ^ 2 :=
    (Nat.cast_nonneg (subcriticalDefectCost G D)).trans R.defect_cost_le
  apply mem_retainedNarrowEdgeCountWindow_of_mem_level
    (R.actualRetainedEdgeCountVector_mem_narrowLevel hR heta htheta hcutoff halpha hedges)
  · simp only [Fintype.card_fin]
    linarith
  · simp only [Fintype.card_fin]
    linarith

end SubcriticalCloseStructureResult

/-- Paper: the actual-vector membership assertion preceding
`eqn:clean-partition-function-K1k`. For the literal family `𝓕_{W,Π}`,
the actual retained active-edge vector lies in `𝓜^nar_Π`. The cut radius
precedes the candidate representation, and only the order threshold may
depend on it. The family uses the original graph's canonical division.
This is not a root/row/tail profile or a random graph model. -/
theorem actualRetainedEdgeCountVector_mem_narrowWindow_of_mem_candidateDivision
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (_hgamma : gamma ∈ Set.Ioo (0 : ℝ) (gammaK k))
    (R₀ : ℕ) (hR₀ : 1 ≤ R₀)
    (omega eta theta alpha delta epsilon : ℝ)
    (homega : 0 < omega) (homegaOne : omega ≤ 1)
    (heta : 0 < eta) (htheta : 0 < theta) (halpha : 0 < alpha)
    (halphaFour : alpha ≤ 4) (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hinv : 1 / (R₀ : ℝ) ≤ eta)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ)))
    (hepsilonCap : epsilon ≤ min eta (theta ^ 2)) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      WLambda hk L ∈ candidateOptimizerFamily k gamma →
        ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
          ∀ (m : ℕ) (D : SubcriticalDivision k (Fin n)) (G : SimpleGraph (Fin n)),
            G ∈ subcriticalCandidateDivisionGraphFinset k n m (WLambda hk L) tau R₀
              hk (hn0.trans hn) D →
                actualRetainedEdgeCountVector G D eta R₀ ∈
                  retainedNarrowEdgeCountWindow D eta R₀ m
                    (subcriticalSparseSideConstant k) delta epsilon := by
  obtain ⟨tau, htau, hbridge⟩ := subcriticalCloseStructure_at_sparseSideScale
    k hk R₀ hR₀ omega eta theta alpha delta epsilon
      homega heta htheta halpha hdelta hepsilon
  refine ⟨tau, htau, ?_⟩
  intro L _hL
  obtain ⟨n0, hn0, hbridge⟩ := hbridge L
  refine ⟨n0, hn0, ?_⟩
  intro n hn m D G hG
  obtain ⟨hball, hcanonical⟩ := mem_subcriticalCandidateDivisionGraphFinset.mp hG
  obtain ⟨hfamily, hcut⟩ := mem_subcriticalCandidateCutBallGraphFinset.mp hball
  obtain ⟨hfree, hedges⟩ := mem_inducedStarFreeGraphFinsetWithEdges.mp hfamily
  obtain ⟨hscale, ⟨R⟩⟩ := hbridge hn G hcut
  have RD : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon := by
    simpa only [hcanonical] using R
  apply RD.actualRetainedEdgeCountVector_mem_narrowWindow hR₀ heta.le htheta.le
    hinv homegaOne hcutoff halphaFour hepsilonCap hscale hfree
  simpa only [finiteGraphEdges_card_eq_edgeFinset_card] using hedges

end InducedStars
