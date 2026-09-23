import InducedStars.Structure.Subcritical.ProfileBound

/-!
# Profile counting with the actual remainder fixed

The ambient family and its probability maxima are unchanged, while
the exact induced graph on the nonretained vertices is fixed before counting.
This removes the outer remainder multiplicity, not a summand after bounding it.
Natural units and fixed-remainder compatibility are retained.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

variable {k n : ℕ} {D : SubcriticalDivision k (Fin n)}
  {eta theta : ℝ} {R₀ : ℕ}

/-- The exact reconstruction sum when every member has the same remainder. No enlargement of the family in a probability maximum occurs. -/
theorem subcriticalProfileCountingDecomposition_fixedRemainder
    (F : Finset (SimpleGraph (Fin n))) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (alpha delta : ℝ) (E : SimpleGraph (Fin n) → Set (SimpleGraph (Fin n)))
    (H : SubcriticalRemainderGraph D eta R₀)
    (hH : H ∈ subcriticalProfileRemainderFinset p)
    (hfixed : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      subcriticalRemainderGraph G D eta R₀ = H)
    (hfree : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hnarrow : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      actualRetainedEdgeCountVector G D eta R₀ ∈
        retainedNarrowEdgeCountLevel D eta R₀ m delta (retainedEdgeShift G D eta R₀))
    (hevent : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      G ∈ E (subcriticalResidualDefectGraph G D eta R₀ theta alpha)) :
    ((subcriticalProfileClassGraphFinset F alpha p).card : ℝ) ≤
      ∑ TB ∈ subcriticalRootedDefectPatternFinset F alpha p,
        ∑ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
          ∑ L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R,
            ∑ mvec ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta
              (p.b + subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L)),
              (retainedEdgeCountMultiplicity mvec : ℝ) *
                subcriticalActiveFixedProbability H (TB ⊔ R ⊔ L) mvec (E R) := by
  apply (subcriticalProfileCountingDecomposition F p m alpha delta E
    hfree hnarrow hevent).trans_eq
  apply Finset.sum_eq_single H
  · intro H' _ hne
    apply Finset.sum_eq_zero
    intro TB _
    apply Finset.sum_eq_zero
    intro R _
    have hempty :
        subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H' TB R = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro L hL
      obtain ⟨G, hG, hrem, _⟩ :=
        (mem_subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H' TB R L).mp hL
      exact hne (hrem.symm.trans (hfixed G hG))
    rw [hempty, Finset.sum_empty]
  · exact fun hh ↦ (hh hH).elim

set_option maxHeartbeats 800000 in
/-- Fixed-remainder master profile bound. The outer remainder sum is
absent, and the same actual family supplies every probability maximum. -/
theorem subcriticalProfileBound_fixedRemainder_of_geometry
    (F : Finset (SimpleGraph (Fin n))) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (alpha delta epsilon : ℝ)
    (H : SubcriticalRemainderGraph D eta R₀)
    (hk : 3 ≤ k) (hn : 2 ≤ n)
    (halpha : 0 ≤ alpha) (halpha_half : 5 * alpha ≤ 1 / 2)
    (htheta : 0 ≤ theta) (hdelta : 0 ≤ delta) (hepsilon : 0 ≤ epsilon)
    (hdp : 6 * delta ≤ pK k) (hdq : 6 * delta ≤ 1 - pK k)
    (hreserve : ∀ e, 2 ≤ delta * retainedActiveCapacity D eta R₀ e)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hpart : ∀ a ∈ D.visiblePartIndices theta,
      theta * (n : ℝ) / 2 ≤ ((D.part a).card : ℝ))
    (hroot : (p.roots.card : ℝ) ≤
      subcriticalProfileRootFraction alpha theta epsilon * (n : ℝ))
    (hrho : subcriticalProfileRootFraction alpha theta epsilon ≤ alpha * theta / 2)
    (hfree : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hsmall : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p, ∀ v,
      (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
        subcriticalSparseSideConstant k * theta * (n : ℝ))
    (hedges : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      (finiteGraphEdges G).card = m)
    (hwindow : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      actualRetainedEdgeCountVector G D eta R₀ ∈
        retainedNarrowEdgeCountWindow D eta R₀ m (subcriticalSparseSideConstant k) delta epsilon)
    (hdefect : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ) ^ 2)
    (hheadroom : epsilon * (n : ℝ) ^ 2 ≤ delta * retainedActiveTotalCapacity D eta R₀ / 4)
    (hfixed : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      subcriticalRemainderGraph G D eta R₀ = H) :
    ((subcriticalProfileClassGraphFinset F alpha p).card : ℝ) ≤
      (n : ℝ) ^ (6 * Fintype.card (RetainedActivePair D eta R₀)) *
        (retainedPartitionFunction D eta R₀ m delta
          ((finiteGraphEdges H).card : ℤ) : ℝ) *
        Real.exp ((∑ v ∈ p.roots,
          subcriticalProfileLocalExponent p m (subcriticalSparseSideConstant k)
            alpha delta epsilon v) +
          subcriticalProfileMatchingExponent F p m (subcriticalSparseSideConstant k)
            alpha delta epsilon + subcriticalProfileErrorBudget alpha delta epsilon p) := by
  by_cases hne : (subcriticalProfileClassGraphFinset F alpha p).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨G₀, hG₀⟩ := hne
  have hHmem := subcriticalRemainder_mem_profileFinset
    (mem_subcriticalProfileClassGraphFinset.mp hG₀).2 (hfree G₀ hG₀)
  rw [hfixed G₀ hG₀] at hHmem
  have hbEq := (mem_subcriticalProfileRemainderFinset p H).mp hHmem |>.2
  rw [hbEq]
  let C := subcriticalSparseSideConstant k
  have htrim : ∀ v a t, p.tails v a = some t →
      (p.roots.card : ℝ) ≤ alpha * (D.part a).card := by
    exact subcriticalProfile_tailTrim_of_geometry p halpha hret
      (by simpa using hpart) (by simpa using hroot) hrho
  have hnarrow : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      actualRetainedEdgeCountVector G D eta R₀ ∈
        retainedNarrowEdgeCountLevel D eta R₀ m delta (retainedEdgeShift G D eta R₀) := by
    intro G hG
    have h := (mem_retainedNarrowEdgeCountWindow.mp (hwindow G hG)).1
    rwa [subcriticalActualLevelShift_eq_of_edge_count G D eta R₀ m (hedges G hG)] at h
  have hcount := subcriticalProfileCountingDecomposition_fixedRemainder F p m alpha delta
    (subcriticalProfileProbabilityEvent p alpha) H hHmem hfixed hfree hnarrow
    (fun G hG ↦ (mem_subcriticalProfileClassGraphFinset.mp hG).2.mem_probabilityEvent
      halpha htrim (hfree G hG) _)
  exact hcount.trans
    (subcriticalProfileFixedRemainderSum_le_of_geometry F p m alpha delta epsilon
      hk hn halpha halpha_half htheta hdelta hepsilon hdp hdq hreserve hret hpart
      hroot hrho hfree hsmall hedges hwindow hdefect hheadroom H hHmem)

end InducedStars
