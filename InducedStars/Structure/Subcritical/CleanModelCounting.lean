import InducedStars.Structure.Subcritical.CleanModels

/-!
# The clean partition function counts actual labeled graphs

Paper: `eqn:clean-partition-function-K1k` and the clean-family comparison in
`lemma:NtaunmWUpperBdK1k`. The floor cutoff and wide levels are unchanged.
The actual graph recovers every stored datum, so the count is not merely
a cardinality of choice tuples. No division uniqueness is asserted.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta delta : ℝ} {R₀ m : ℕ}

/-- Induced-free exact-edge remainders on the actual nonretained subtype. -/
def subcriticalCleanRemainderGraphFinset (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ b : ℕ) : Finset (SubcriticalRemainderGraph D eta R₀) :=
  Finset.univ.filter fun H ↦ ¬Regularity.InducedEmbeds (inducedStar k) H ∧
    (finiteGraphEdges H).card = b

@[simp] theorem mem_subcriticalCleanRemainderGraphFinset
    (H : SubcriticalRemainderGraph D eta R₀) (b : ℕ) :
    H ∈ subcriticalCleanRemainderGraphFinset D eta R₀ b ↔
      ¬Regularity.InducedEmbeds (inducedStar k) H ∧ (finiteGraphEdges H).card = b := by
  simp [subcriticalCleanRemainderGraphFinset]

/-- Relabeling the fixed vertex subtype is a graph equivalence, not an
additional choice of labels; in particular there is no factorial factor. -/
theorem card_subcriticalCleanRemainderGraphFinset
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ b : ℕ) :
    (subcriticalCleanRemainderGraphFinset D eta R₀ b).card =
      inducedStarFreeGraphCountWithEdges k (D.nonretainedVertices eta R₀).card b := by
  let e : ↥(D.nonretainedVertices eta R₀) ≃ Fin (D.nonretainedVertices eta R₀).card :=
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
  rw [mem_subcriticalCleanRemainderGraphFinset,
    mem_inducedFreeGraphFinsetWithEdges_iff_finiteGraphEdges, hfree, hedge]

/-- Exact data counted by the existing clean partition function: the floor
edge-count level, an actual remainder graph, a wide vector, and its choices. -/
abbrev SubcriticalCleanModelData (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) :=
  Σ b : ↥(Finset.range (Nat.floor
    (subcriticalSparseSideConstant k * eta * (Fintype.card V : ℝ)^2) + 1)),
    ↥(subcriticalCleanRemainderGraphFinset D eta R₀ b.val) ×
      (Σ v : ↥(retainedEdgeCountLevel D eta R₀ m delta (b.val : ℤ)),
        RetainedEdgeChoices v.val)

def SubcriticalCleanModelData.graph
    (d : SubcriticalCleanModelData D eta R₀ m delta) : SimpleGraph V :=
  subcriticalCleanGraph d.2.1.val d.2.2.2

theorem SubcriticalCleanModelData.graph_injective :
    Function.Injective (SubcriticalCleanModelData.graph (D := D) (eta := eta)
      (R₀ := R₀) (m := m) (delta := delta)) := by
  rintro ⟨⟨b, hb⟩, ⟨H, hH⟩, ⟨v, hv⟩, S⟩ ⟨⟨c, hc⟩, ⟨K, hK⟩, ⟨w, hw⟩, U⟩ h
  change subcriticalCleanGraph H S = subcriticalCleanGraph K U at h
  have hHK := congrArg (fun G ↦ subcriticalRemainderGraph G D eta R₀) h
  simp only [subcriticalCleanGraph_remainder] at hHK
  subst K
  have hbc : b = c := (mem_subcriticalCleanRemainderGraphFinset H b).mp hH |>.2.symm.trans
    ((mem_subcriticalCleanRemainderGraphFinset H c).mp hK).2
  subst c
  have hvw := congrArg (fun G ↦ actualRetainedEdgeCountVector G D eta R₀) h
  simp only [subcriticalCleanGraph_active_vector] at hvw
  subst w
  have hSU := subcriticalActiveGraphFromOutcome_injective H ⊥
    (isSubcriticalRetainedDefectPattern_bot D eta R₀) v h
  subst U
  rfl

theorem card_subcriticalCleanModelData (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) :
    Fintype.card (SubcriticalCleanModelData D eta R₀ m delta) =
      cleanRetainedPartitionFunction D eta R₀ m delta := by
  simp only [SubcriticalCleanModelData, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_coe, card_subcriticalCleanRemainderGraphFinset,
    retainedEdgeChoices_card, cleanRetainedPartitionFunction,
    retainedPartitionFunction, Finset.sum_coe_sort]
  simpa only using (Finset.sum_coe_sort
    (Finset.range (Nat.floor
      (subcriticalSparseSideConstant k * eta * (Fintype.card V : ℝ)^2) + 1))
    (fun b : ℕ ↦ inducedStarFreeGraphCountWithEdges k
      (D.nonretainedVertices eta R₀).card b *
      ∑ v ∈ retainedEdgeCountLevel D eta R₀ m delta (b : ℤ),
        retainedEdgeCountMultiplicity v))

/-- The finite family of actual graphs represented by the clean partition
function. It does not filter on canonicality or cut distance. -/
def subcriticalCleanModelGraphFinset (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) : Finset (SimpleGraph V) :=
  Finset.univ.image (SubcriticalCleanModelData.graph (D := D) (eta := eta)
    (R₀ := R₀) (m := m) (delta := delta))

/-- Exact graph cardinality, including infeasible levels and the single
empty active choice when there are no retained active indices. -/
theorem card_subcriticalCleanModelGraphFinset (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) :
    (subcriticalCleanModelGraphFinset D eta R₀ m delta).card =
      cleanRetainedPartitionFunction D eta R₀ m delta := by
  rw [subcriticalCleanModelGraphFinset,
    Finset.card_image_of_injective _ SubcriticalCleanModelData.graph_injective,
    Finset.card_univ, card_subcriticalCleanModelData]

theorem SubcriticalCleanModelData.graph_card
    (d : SubcriticalCleanModelData D eta R₀ m delta) :
    (finiteGraphEdges d.graph).card = m := by
  apply subcriticalCleanGraph_card_of_mem_level
  rw [((mem_subcriticalCleanRemainderGraphFinset d.2.1.val d.1.val).mp d.2.1.property).2]
  exact d.2.2.1.property

/-- Any clean actual graph satisfying the exact cutoff and wide-level
condition is recovered by a member of the model family. -/
theorem mem_subcriticalCleanModelGraphFinset_of_clean
    (G : SimpleGraph V)
    (hclean : subcriticalRetainedIncidentDefectGraph G D eta R₀ = ⊥)
    (hfree : ¬Regularity.InducedEmbeds (inducedStar k) G)
    (hb : ((finiteGraphEdges (subcriticalRemainderGraph G D eta R₀)).card : ℝ) ≤
      subcriticalSparseSideConstant k * eta * (Fintype.card V : ℝ)^2)
    (hv : actualRetainedEdgeCountVector G D eta R₀ ∈
      retainedEdgeCountLevel D eta R₀ m delta
        (finiteGraphEdges (subcriticalRemainderGraph G D eta R₀)).card) :
    G ∈ subcriticalCleanModelGraphFinset D eta R₀ m delta := by
  have hH : subcriticalRemainderGraph G D eta R₀ ∈
      subcriticalCleanRemainderGraphFinset D eta R₀
        (finiteGraphEdges (subcriticalRemainderGraph G D eta R₀)).card := by
    refine (mem_subcriticalCleanRemainderGraphFinset _ _).mpr ⟨?_, rfl⟩
    intro h
    exact hfree (h.trans
      (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G).isIndContained)
  let d : SubcriticalCleanModelData D eta R₀ m delta :=
    ⟨⟨_, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hb))⟩,
      ⟨subcriticalRemainderGraph G D eta R₀, hH⟩,
      ⟨actualRetainedEdgeCountVector G D eta R₀, hv⟩,
      subcriticalActualActiveSample G D eta R₀⟩
  apply Finset.mem_image.mpr
  refine ⟨d, Finset.mem_univ _, ?_⟩
  change subcriticalActiveGraphFromOutcome (subcriticalRemainderGraph G D eta R₀) ⊥
    (subcriticalActualActiveSample G D eta R₀) = G
  rw [← hclean]
  exact subcriticalActiveGraphFromOutcome_actual G D eta R₀

end InducedStars
