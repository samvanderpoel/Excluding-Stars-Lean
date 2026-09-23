import InducedStars.Structure.Subcritical.ProfileLeftoverCounting
import InducedStars.Structure.Subcritical.ProfileLeftoverAlgebra
import InducedStars.Structure.Subcritical.ProfileLeftoverEdgeBound

/-!
# Fixed-remainder profile leftovers

The full nonretained graph `H` is fixed before counting leftover
patterns. The unrestricted family remains separately defined; the theorem
below does not assert a bound on the union over different remainder graphs.
-/

noncomputable section
open scoped Classical BigOperators
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta alpha delta epsilon : ℝ} {R₀ : ℕ}
  {p : SubcriticalProfile D eta R₀ theta}

/-- Transfer the uniform small-side degree estimate from a generating graph
to the fixed remainder. This is a finite equality, not an extra assumption
on independently varying remainder graphs. -/
theorem subcriticalRemainderGraph_small_degree_eq
    {G : SimpleGraph V} {H : SubcriticalRemainderGraph D eta R₀}
    (hH : subcriticalRemainderGraph G D eta R₀ = H) {v : V}
    (hv : v ∈ D.nonretainedSmallVertices eta R₀ theta) :
    degreeInFinset (subcriticalRemainderGraphSpanningCoe H) v
        (D.nonretainedSmallVertices eta R₀ theta) =
      degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) := by
  unfold degreeInFinset
  congr 1
  ext y
  simp only [Finset.mem_filter]
  by_cases hy : y ∈ D.nonretainedSmallVertices eta R₀ theta
  · simp only [hy, true_and]
    exact subcriticalRemainderGraph_small_adj hH hv hy
  · simp [hy]

/-- The fixed-`H` cardinality part of the paper lemma.
All inputs are finite profile geometry and the established small-side
degree estimate; no candidate graphon or probability hypothesis is used. -/
theorem subcriticalProfileLeftover_card_le_exp_errorBudget
    (F : Finset (SimpleGraph V)) (H : SubcriticalRemainderGraph D eta R₀)
    (TB R : SimpleGraph V) (hk : 3 ≤ k) (hn : 2 ≤ Fintype.card V)
    (halpha : 0 ≤ alpha) (halpha_half : 5 * alpha ≤ 1 / 2)
    (htheta : 0 ≤ theta) (hdelta : 0 ≤ delta) (hepsilon : 0 ≤ epsilon)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hpart : ∀ a ∈ D.visiblePartIndices theta,
      theta * Fintype.card V / 2 ≤ ((D.part a).card : ℝ))
    (hroot : (p.roots.card : ℝ) ≤
      subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V)
    (hrho : subcriticalProfileRootFraction alpha theta epsilon ≤ alpha * theta / 2)
    (hfree : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hsmall : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p, ∀ v,
      (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
        subcriticalSparseSideConstant k * theta * Fintype.card V) :
    ((subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R).card : ℝ) ≤
      Real.exp (subcriticalProfileErrorBudget alpha delta epsilon p) := by
  classical
  by_cases hEmpty : (subcriticalLeftoverDefectPatternFinsetWithRemainder
      F alpha p H TB R).Nonempty
  · obtain ⟨L₀, hL₀⟩ := hEmpty
    obtain ⟨G₀, hG₀, hH, _, _, _⟩ :=
      (mem_subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R L₀).mp hL₀
    let d := ⌊subcriticalSparseSideConstant k * theta * Fintype.card V⌋₊
    have hdeg : ∀ v ∈ D.nonretainedSmallVertices eta R₀ theta,
        degreeInFinset (subcriticalRemainderGraphSpanningCoe H) v
          (D.nonretainedSmallVertices eta R₀ theta) ≤ d := by
      intro v hv
      rw [subcriticalRemainderGraph_small_degree_eq hH hv]
      exact Nat.le_floor (hsmall G₀ hG₀ v)
    have hB : ∀ a ∈ D.visiblePartIndices theta,
        (p.roots.card : ℝ) ≤ alpha * (D.part a).card := by
      intro a ha
      exact subcriticalProfile_roots_card_le_alpha_target halpha hroot hrho (hpart a ha)
    have hc := subcriticalProfileLeftover_card_le_rowProduct F H TB R d
      halpha (by linarith) hret hB hfree hdeg
    have hEnt := subcritical_smallSubsetCard_le_exp_entropy
      (Finset.univ : Finset V) (by positivity : 0 ≤ 5 * alpha) halpha_half
    simp only [Finset.card_univ, mul_assoc] at hEnt
    have hScalar := subcriticalLeftoverRawCount_le_exp_errorBudget p hk hn
      halpha halpha_half htheta hdelta hepsilon hroot
      ((finsetSubsetsAtMost (Finset.univ : Finset V) ⌊5 * alpha * Fintype.card V⌋₊).card : ℝ)
      (Nat.cast_nonneg _) (by simpa only [mul_assoc] using hEnt)
    apply le_trans (by exact_mod_cast hc)
      (show ((_ : ℝ) * ((_ : ℝ) ^ (k - 1) * (2 : ℝ) ^ ((k - 1) * (d + 1))) *
        (2 : ℝ) ^ p.roots.card) ^ p.roots.card ≤ _ from hScalar)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hEmpty]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact (Real.exp_pos _).le

/-- Paper: Lemma `lemma:profile-root-leftover-bound-K1k`, with the
fixed-remainder decomposition. The full nonretained graph
`H` is held fixed in the counted family. The edge and signed-size bounds
follow separately for each generating graph and require no fixed-remainder
argument. -/
theorem subcriticalProfileRootLeftoverBound
    (F : Finset (SimpleGraph V)) (H : SubcriticalRemainderGraph D eta R₀)
    (TB R : SimpleGraph V) (hk : 3 ≤ k) (hn : 2 ≤ Fintype.card V)
    (halpha : 0 ≤ alpha) (halpha_half : 5 * alpha ≤ 1 / 2)
    (htheta : 0 ≤ theta) (hdelta : 0 ≤ delta) (hepsilon : 0 ≤ epsilon)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hpart : ∀ a ∈ D.visiblePartIndices theta,
      theta * Fintype.card V / 2 ≤ ((D.part a).card : ℝ))
    (hroot : (p.roots.card : ℝ) ≤
      subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V)
    (hrho : subcriticalProfileRootFraction alpha theta epsilon ≤ alpha * theta / 2)
    (hfree : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hsmall : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p, ∀ v,
      (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
        subcriticalSparseSideConstant k * theta * Fintype.card V) :
    ((subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R).card : ℝ) ≤
        Real.exp (subcriticalProfileErrorBudget alpha delta epsilon p) ∧
      ∀ L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R,
        ((finiteGraphEdges L).card : ℝ) ≤ subcriticalProfileErrorBudget alpha delta epsilon p ∧
          |(subcriticalSignedDefectSize D eta R₀ L : ℝ)| ≤
            subcriticalProfileErrorBudget alpha delta epsilon p := by
  refine ⟨subcriticalProfileLeftover_card_le_exp_errorBudget F H TB R hk hn
    halpha halpha_half htheta hdelta hepsilon hret hpart hroot hrho hfree hsmall, ?_⟩
  intro L hL
  obtain ⟨G, hG, _, _, _, hGL⟩ :=
    (mem_subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R L).mp hL
  have hprofile := (mem_subcriticalProfileClassGraphFinset.mp hG).2
  have hB : ∀ a ∈ D.visiblePartIndices theta,
      (p.roots.card : ℝ) ≤ alpha * (D.part a).card := by
    intro a ha
    exact subcriticalProfile_roots_card_le_alpha_target halpha hroot hrho (hpart a ha)
  have hedge := subcriticalActualLeftover_edgeCount_signedSize_le_errorBudget
    hprofile hret halpha halpha_half htheta hdelta hepsilon hB hroot (hsmall G hG)
  simpa only [hGL] using hedge

end InducedStars
