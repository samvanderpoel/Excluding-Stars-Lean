import InducedStars.Structure.Subcritical.ProfileExponents
import InducedStars.Structure.Subcritical.ActiveModelsRecovery

/-!
# Exact finite enumeration underlying the profile bound

The remainder is a full graph, not just its edge count. It remains the
outermost index throughout the fixed-remainder decomposition.
-/

noncomputable section
open Finset Set
open scoped Classical BigOperators
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}

/-- All induced-free remainders with the exact edge count stored by the profile. -/
def subcriticalProfileRemainderFinset (p : SubcriticalProfile D eta R₀ theta) :
    Finset (SubcriticalRemainderGraph D eta R₀) :=
  Finset.univ.filter fun H ↦ ¬ Regularity.InducedEmbeds (inducedStar k) H ∧
    (finiteGraphEdges H).card = p.b

@[simp] theorem mem_subcriticalProfileRemainderFinset
    (p : SubcriticalProfile D eta R₀ theta) (H : SubcriticalRemainderGraph D eta R₀) :
    H ∈ subcriticalProfileRemainderFinset p ↔
      ¬ Regularity.InducedEmbeds (inducedStar k) H ∧ (finiteGraphEdges H).card = p.b := by
  simp [subcriticalProfileRemainderFinset]

/-- Relabel the actual nonretained subtype bijectively onto `Fin s`.
No factor for the choice of labels is introduced. -/
theorem card_subcriticalProfileRemainderFinset
    (p : SubcriticalProfile D eta R₀ theta) :
    (subcriticalProfileRemainderFinset p).card =
      inducedStarFreeGraphCountWithEdges k (D.nonretainedVertices eta R₀).card p.b := by
  let e : ↥(D.nonretainedVertices eta R₀) ≃
      Fin (D.nonretainedVertices eta R₀).card :=
    Fintype.equivFinOfCardEq (Fintype.card_coe _)
  apply Finset.card_equiv e.simpleGraph
  intro H
  have iso : e.simpleGraph H ≃g H := SimpleGraph.Iso.comap e.symm H
  have hfree : Regularity.InducedEmbeds (inducedStar k) H ↔
      Regularity.InducedEmbeds (inducedStar k) (e.simpleGraph H) :=
    ⟨fun h ↦ h.trans iso.isIndContained', fun h ↦ h.trans iso.isIndContained⟩
  have hedge : (finiteGraphEdges H).card = (finiteGraphEdges (e.simpleGraph H)).card := by
    calc
      _ = H.edgeFinset.card := by congr 1; ext z; simp
      _ = (e.simpleGraph H).edgeFinset.card := iso.card_edgeFinset_eq.symm
      _ = _ := by congr 1; ext z; simp
  rw [mem_subcriticalProfileRemainderFinset,
    mem_inducedFreeGraphFinsetWithEdges_iff_finiteGraphEdges, hfree, hedge]

theorem subcriticalRemainder_mem_profileFinset
    {G : SimpleGraph V} {alpha : ℝ} {p : SubcriticalProfile D eta R₀ theta}
    (hp : RealizesSubcriticalProfile G alpha p)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G) :
    subcriticalRemainderGraph G D eta R₀ ∈ subcriticalProfileRemainderFinset p := by
  apply (mem_subcriticalProfileRemainderFinset p _).mpr
  refine ⟨?_, ?_⟩
  swap
  · calc
      _ = inducedEdgeCount G (D.nonretainedVertices eta R₀) := by
        congr 1
        ext z
        simp only [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
        rfl
      _ = _ := hp.edge_count
  intro h
  exact hfree (h.trans
    (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G).isIndContained)

/-- Graphs obtained from the exact fixed-count samples in a specified event.
Some outcomes may fail the profile conditions; this is an upper cover only. -/
def subcriticalFixedOutcomeGraphFinset (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph V) (mvec : RetainedEdgeCountVector D eta R₀)
    (E : Set (SimpleGraph V)) : Finset (SimpleGraph V) :=
  (Finset.univ.filter fun S : (subcriticalActiveFixedBlockModel mvec).Sample ↦
    subcriticalActiveGraphFromOutcome H T S ∈ E).image
      (fun S ↦ subcriticalActiveGraphFromOutcome H T S)

/-- Fixed sample counts are multiplicity times probability, exactly.
This bound does not require injectivity, so also covers arbitrary patterns. -/
theorem card_subcriticalFixedOutcomeGraphFinset_le
    (H : SubcriticalRemainderGraph D eta R₀) (T : SimpleGraph V)
    (mvec : RetainedEdgeCountVector D eta R₀) (E : Set (SimpleGraph V)) :
    ((subcriticalFixedOutcomeGraphFinset H T mvec E).card : ℝ) ≤
      retainedEdgeCountMultiplicity mvec * subcriticalActiveFixedProbability H T mvec E := by
  let M := subcriticalActiveFixedBlockModel mvec
  let S := Finset.univ.filter fun S : M.Sample ↦ subcriticalActiveGraphFromOutcome H T S ∈ E
  have hcard : ((subcriticalFixedOutcomeGraphFinset H T mvec E).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_image_le
  rw [subcriticalActiveFixedProbability_eq_eventProbability, M.eventProbability_eq_card_div]
  have hM : M.sampleSpaceCard = retainedEdgeCountMultiplicity mvec := by
    rw [← M.card_sample]
    exact subcriticalActiveFixedBlockModel_card mvec
  rw [hM]
  have hpos : (0 : ℝ) < retainedEdgeCountMultiplicity mvec := by
    exact_mod_cast hM ▸ M.sampleSpaceCard_pos
  simpa only [← mul_div_assoc, mul_div_cancel_left₀ _ hpos.ne'] using hcard

/-- The exact clean partition-function cutoff contains the profile remainder
term. No positivity assumption on the level partition function is needed. -/
theorem subcriticalProfileRemainderTerm_le_cleanPartitionFunction
    (p : SubcriticalProfile D eta R₀ theta) (m : ℕ) (delta : ℝ)
    (hb : (p.b : ℝ) ≤
      subcriticalSparseSideConstant k * eta * (Fintype.card V : ℝ)^2) :
    inducedStarFreeGraphCountWithEdges k (D.nonretainedVertices eta R₀).card p.b *
        retainedPartitionFunction D eta R₀ m delta (p.b : ℤ) ≤
      cleanRetainedPartitionFunction D eta R₀ m delta := by
  unfold cleanRetainedPartitionFunction
  apply Finset.single_le_sum (f := fun b ↦
    inducedStarFreeGraphCountWithEdges k (D.nonretainedVertices eta R₀).card b *
      retainedPartitionFunction D eta R₀ m delta (b : ℤ)) (fun _ _ ↦ Nat.zero_le _)
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hb))

/-- The literal graph cover with the summation order `H,TB,R,L,mvec`.
The active level uses the signed size of the combined pattern. -/
def subcriticalProfileOutcomeCover (F : Finset (SimpleGraph V))
    (p : SubcriticalProfile D eta R₀ theta) (m : ℕ) (alpha delta : ℝ)
    (E : SimpleGraph V → Set (SimpleGraph V)) : Finset (SimpleGraph V) :=
  (subcriticalProfileRemainderFinset p).biUnion fun H ↦
    (subcriticalRootedDefectPatternFinset F alpha p).biUnion fun TB ↦
      (subcriticalResidualDefectPatternFinset F alpha p TB).biUnion fun R ↦
        (subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R).biUnion fun L ↦
          (retainedNarrowEdgeCountLevel D eta R₀ m delta
            (p.b + subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L))).biUnion fun mvec ↦
              subcriticalFixedOutcomeGraphFinset H (TB ⊔ R ⊔ L) mvec (E R)

theorem subcriticalProfileClass_subset_outcomeCover
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (alpha delta : ℝ) (E : SimpleGraph V → Set (SimpleGraph V))
    (hfree : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hnarrow : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      actualRetainedEdgeCountVector G D eta R₀ ∈
        retainedNarrowEdgeCountLevel D eta R₀ m delta (retainedEdgeShift G D eta R₀))
    (hevent : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      G ∈ E (subcriticalResidualDefectGraph G D eta R₀ theta alpha)) :
    subcriticalProfileClassGraphFinset F alpha p ⊆
      subcriticalProfileOutcomeCover F p m alpha delta E := by
  intro G hG
  have hp := (mem_subcriticalProfileClassGraphFinset.mp hG).2
  let H := subcriticalRemainderGraph G D eta R₀
  let TB := subcriticalRootedDefectGraph G D eta R₀ theta alpha
  let R := subcriticalResidualDefectGraph G D eta R₀ theta alpha
  let L := subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha
  have hH := subcriticalRemainder_mem_profileFinset hp (hfree G hG)
  have hTB : TB ∈ subcriticalRootedDefectPatternFinset F alpha p :=
    Finset.mem_image.mpr ⟨G, hG, rfl⟩
  have hR : R ∈ subcriticalResidualDefectPatternFinset F alpha p TB :=
    Finset.mem_image.mpr ⟨G, Finset.mem_filter.mpr ⟨hG, rfl⟩, rfl⟩
  have hL : L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R :=
    (mem_subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R L).mpr
      ⟨G, hG, rfl, rfl, rfl, rfl⟩
  have hT : TB ⊔ R ⊔ L = subcriticalRetainedIncidentDefectGraph G D eta R₀ :=
    subcriticalLeftoverDefectGraph_union _ _ _
      (subcriticalRootedDefectGraph_le G D eta R₀ theta alpha)
      (subcriticalResidualDefectGraph_le G D eta R₀ theta alpha)
  have hshift : retainedEdgeShift G D eta R₀ =
      p.b + subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L) := by
    rw [hT, subcriticalSignedDefectSize_actual,
      retainedEdgeShift_eq_nonretained_add_present_sub_missing, hp.edge_count]
    ring
  have hm := hnarrow G hG
  rw [hshift] at hm
  unfold subcriticalProfileOutcomeCover
  refine Finset.mem_biUnion.mpr ⟨H, hH, Finset.mem_biUnion.mpr ⟨TB, hTB,
    Finset.mem_biUnion.mpr ⟨R, hR, Finset.mem_biUnion.mpr ⟨L, hL,
      Finset.mem_biUnion.mpr ⟨actualRetainedEdgeCountVector G D eta R₀, hm, ?_⟩⟩⟩⟩⟩
  rw [hT]
  apply Finset.mem_image.mpr
  refine ⟨subcriticalActualActiveSample G D eta R₀,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      subcriticalActiveGraphFromOutcome_actual G D eta R₀⟩
  rw [subcriticalActiveGraphFromOutcome_actual]
  exact hevent G hG

private theorem real_card_biUnion_le {ι X : Type*} [DecidableEq X]
    (s : Finset ι) (t : ι → Finset X) :
    ((s.biUnion t).card : ℝ) ≤ ∑ i ∈ s, ((t i).card : ℝ) := by
  exact_mod_cast (Finset.card_biUnion_le : (s.biUnion t).card ≤ ∑ i ∈ s, (t i).card)

theorem subcriticalActualLevelShift_eq_of_edge_count (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m : ℕ)
    (hm : (finiteGraphEdges G).card = m) :
    retainedLevelShift m (actualRetainedEdgeCountVector G D eta R₀) =
      retainedEdgeShift G D eta R₀ := by
  unfold retainedLevelShift retainedEdgeShift
  rw [hm]

/-- A compatible fixed-remainder triple has one common level shift. Thus
every vector in that narrow level is in the complete narrow window whenever
the actual generating vectors are. The maximum in `J_v` loses no vectors. -/
theorem subcriticalCompatible_narrowLevel_subset_window
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C alpha delta epsilon : ℝ) (H : SubcriticalRemainderGraph D eta R₀)
    (TB R L : SimpleGraph V)
    (hL : L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R)
    (hedges : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p, (finiteGraphEdges G).card = m)
    (hwindow : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      actualRetainedEdgeCountVector G D eta R₀ ∈
        retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon) :
    retainedNarrowEdgeCountLevel D eta R₀ m delta
        (p.b + subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L)) ⊆
      retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon := by
  obtain ⟨G, hG, _, hTB, hR, hL⟩ :=
    (mem_subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R L).mp hL
  have hp := (mem_subcriticalProfileClassGraphFinset.mp hG).2
  have hT : TB ⊔ R ⊔ L = subcriticalRetainedIncidentDefectGraph G D eta R₀ := by
    rw [← hTB, ← hR, ← hL]
    exact subcriticalLeftoverDefectGraph_union _ _ _
      (subcriticalRootedDefectGraph_le G D eta R₀ theta alpha)
      (subcriticalResidualDefectGraph_le G D eta R₀ theta alpha)
  have hs : retainedLevelShift m (actualRetainedEdgeCountVector G D eta R₀) =
      p.b + subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L) := by
    rw [subcriticalActualLevelShift_eq_of_edge_count G D eta R₀ m (hedges G hG),
      hT, subcriticalSignedDefectSize_actual,
      retainedEdgeShift_eq_nonretained_add_present_sub_missing, hp.edge_count]
    ring
  have hw := (mem_retainedNarrowEdgeCountWindow.mp (hwindow G hG)).2
  rw [hs] at hw
  intro mvec hmvec
  exact mem_retainedNarrowEdgeCountWindow_of_mem_level hmvec hw.1 hw.2

/-- The exact finite profile counting inequality before exponent simplification.
The full remainder is fixed before the leftover fiber. Outcome probabilities
are multiplied by their exact fixed-count sample multiplicities. -/
theorem subcriticalProfileCountingDecomposition
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (alpha delta : ℝ) (E : SimpleGraph V → Set (SimpleGraph V))
    (hfree : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hnarrow : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      actualRetainedEdgeCountVector G D eta R₀ ∈
        retainedNarrowEdgeCountLevel D eta R₀ m delta (retainedEdgeShift G D eta R₀))
    (hevent : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      G ∈ E (subcriticalResidualDefectGraph G D eta R₀ theta alpha)) :
    ((subcriticalProfileClassGraphFinset F alpha p).card : ℝ) ≤
      ∑ H ∈ subcriticalProfileRemainderFinset p,
        ∑ TB ∈ subcriticalRootedDefectPatternFinset F alpha p,
          ∑ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
            ∑ L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R,
              ∑ mvec ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta
                (p.b + subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L)),
                (retainedEdgeCountMultiplicity mvec : ℝ) *
                  subcriticalActiveFixedProbability H (TB ⊔ R ⊔ L) mvec (E R) := by
  have hcover : ((subcriticalProfileClassGraphFinset F alpha p).card : ℝ) ≤
      (subcriticalProfileOutcomeCover F p m alpha delta E).card := by
    exact_mod_cast Finset.card_le_card
      (subcriticalProfileClass_subset_outcomeCover F p m alpha delta E hfree hnarrow hevent)
  apply hcover.trans
  unfold subcriticalProfileOutcomeCover
  apply (real_card_biUnion_le _ _).trans
  apply Finset.sum_le_sum
  intro H hH
  apply (real_card_biUnion_le _ _).trans
  apply Finset.sum_le_sum
  intro TB hTB
  apply (real_card_biUnion_le _ _).trans
  apply Finset.sum_le_sum
  intro R hR
  apply (real_card_biUnion_le _ _).trans
  apply Finset.sum_le_sum
  intro L hL
  apply (real_card_biUnion_le _ _).trans
  exact Finset.sum_le_sum fun mvec _ ↦ card_subcriticalFixedOutcomeGraphFinset_le _ _ mvec _

end InducedStars
