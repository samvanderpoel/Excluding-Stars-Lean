import InducedStars.Structure.Subcritical.FixedRemainderAggregation
import InducedStars.Structure.Subcritical.FixedRemainderGeometry
import InducedStars.Structure.Subcritical.RetainedKeyCounts
import InducedStars.Structure.Subcritical.CandidateUpperBound

/-!
# Profile aggregation over retained keys and actual remainders

Each fixed-(key,remainder) fiber is counted with its own common
minimizing completion. The original canonical selector assigns the key,
and each induced remainder graph is summed exactly once.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

variable {k n R₀ m : ℕ} {gamma omega eta theta alpha delta epsilon tau : ℝ}
  {L : AdmissibleBlockSequence k}

/-- The geometric bridge for every globally minimizing division; no
counting, probability, or uniqueness conclusion is part of this input. -/
abbrev SubcriticalMinimizerBridge (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    (R₀ : ℕ) (omega eta theta alpha delta epsilon tau : ℝ) (n : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n)),
    (∀ E : SubcriticalDivision k (Fin n),
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E) →
    cutDist (graphGraphon G) (WLambda hk L) < tau →
      Nonempty (SubcriticalCloseStructureResult hk G D L R₀
        omega eta theta alpha delta epsilon)

/-- Noncleanliness is tested at the unchanged original selector. -/
def subcriticalCanonicalNoncleanGraphFinset
    (F : Finset (SimpleGraph (Fin n))) (eta : ℝ) (R₀ : ℕ)
    (hk : 3 ≤ k) (hn : k - 1 ≤ n) : Finset (SimpleGraph (Fin n)) :=
  F.filter fun G ↦ subcriticalRetainedIncidentDefectGraph G
    (canonicalSubcriticalDivision G R₀ hk (by simpa using hn)) eta R₀ ≠ ⊥

@[simp] theorem mem_subcriticalCanonicalNoncleanGraphFinset
    (F : Finset (SimpleGraph (Fin n))) (eta : ℝ) (R₀ : ℕ)
    (hk : 3 ≤ k) (hn : k - 1 ≤ n) (G : SimpleGraph (Fin n)) :
    G ∈ subcriticalCanonicalNoncleanGraphFinset F eta R₀ hk hn ↔
      G ∈ F ∧ subcriticalRetainedIncidentDefectGraph G
        (canonicalSubcriticalDivision G R₀ hk (by simpa using hn)) eta R₀ ≠ ⊥ := by
  simp [subcriticalCanonicalNoncleanGraphFinset]

/-- The canonical nonclean subfamily in a fixed fiber is exactly the
nonclean family for its minimizing completion. -/
theorem subcriticalFixedKeyNoncleanRemainder_eq
    (F : Finset (SimpleGraph (Fin n))) (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (K : SubcriticalRetainedKey k (Fin n))
    (H : SimpleGraph {v : Fin n // v ∈ K.remainder})
    (hK : (subcriticalRetainedKeyCompletions K eta R₀).Nonempty) :
    subcriticalFixedKeyRemainderGraphFinset
      (subcriticalCanonicalNoncleanGraphFinset F eta R₀ hk hn)
      K eta R₀ hk (by simpa using hn) H =
    subcriticalNoncleanDivisionGraphFinset
      (subcriticalFixedKeyRemainderGraphFinset F K eta R₀ hk (by simpa using hn) H)
      (subcriticalFixedRemainderCompletion K eta R₀ H hK) eta R₀ := by
  ext G
  simp only [mem_subcriticalFixedKeyRemainderGraphFinset,
    mem_subcriticalCanonicalNoncleanGraphFinset, mem_subcriticalNoncleanDivisionGraphFinset]
  have hD := (subcriticalFixedRemainderCompletion_mem K eta R₀ H hK).2
  constructor
  · rintro ⟨⟨hF, hnon⟩, hkey, hH⟩
    refine ⟨⟨hF, hkey, hH⟩, ?_⟩
    rwa [← subcriticalRetainedIncidentDefectGraph_eq_of_retainedKey_eq G
      (hkey.trans hD.symm)]
  · rintro ⟨⟨hF, hkey, hH⟩, hnon⟩
    refine ⟨⟨hF, ?_⟩, hkey, hH⟩
    rwa [subcriticalRetainedIncidentDefectGraph_eq_of_retainedKey_eq G
      (hkey.trans hD.symm)]

/-- Induced-free graphs of one exact edge count on the key's remainder. -/
def subcriticalRetainedKeyRemainderGraphFinset
    (K : SubcriticalRetainedKey k (Fin n)) (b : ℕ) :
    Finset (SimpleGraph {v : Fin n // v ∈ K.remainder}) :=
  Finset.univ.filter fun H ↦ ¬Regularity.InducedEmbeds (inducedStar k) H ∧
    (finiteGraphEdges H).card = b

@[simp] theorem mem_subcriticalRetainedKeyRemainderGraphFinset
    (K : SubcriticalRetainedKey k (Fin n)) (b : ℕ)
    (H : SimpleGraph {v : Fin n // v ∈ K.remainder}) :
    H ∈ subcriticalRetainedKeyRemainderGraphFinset K b ↔
      ¬Regularity.InducedEmbeds (inducedStar k) H ∧ (finiteGraphEdges H).card = b := by
  simp [subcriticalRetainedKeyRemainderGraphFinset]

theorem card_subcriticalRetainedKeyRemainderGraphFinset
    (K : SubcriticalRetainedKey k (Fin n)) (b : ℕ) :
    (subcriticalRetainedKeyRemainderGraphFinset K b).card =
      inducedStarFreeGraphCountWithEdges k K.remainder.card b := by
  let e : ↥K.remainder ≃ Fin K.remainder.card :=
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
  rw [mem_subcriticalRetainedKeyRemainderGraphFinset,
    mem_inducedFreeGraphFinsetWithEdges_iff_finiteGraphEdges, hfree, hedge]

/-- All feasible induced remainders, with no division decoration. -/
def subcriticalAdmissibleKeyRemainders
    (K : SubcriticalRetainedKey k (Fin n)) (eta : ℝ) :
    Finset (SimpleGraph {v : Fin n // v ∈ K.remainder}) :=
  (Finset.range (Nat.floor (subcriticalSparseSideConstant k * eta * (n : ℝ)^2) + 1)).biUnion
    (subcriticalRetainedKeyRemainderGraphFinset K)

@[simp] theorem mem_subcriticalAdmissibleKeyRemainders
    (K : SubcriticalRetainedKey k (Fin n)) (eta : ℝ)
    (H : SimpleGraph {v : Fin n // v ∈ K.remainder}) :
    H ∈ subcriticalAdmissibleKeyRemainders K eta ↔
      ¬Regularity.InducedEmbeds (inducedStar k) H ∧
        (finiteGraphEdges H).card ≤
          Nat.floor (subcriticalSparseSideConstant k * eta * (n : ℝ)^2) := by
  simp [subcriticalAdmissibleKeyRemainders, Finset.mem_range, Nat.lt_succ_iff,
    and_left_comm, and_assoc, and_comm]

/-- Exact grouping by edge count of the actual remainder graph. There is
one term per H, including zero and infeasible active levels. -/
theorem sum_retainedKeyPartitionFunction_remainders
    (K : SubcriticalRetainedKey k (Fin n)) (eta : ℝ) (m : ℕ) (delta : ℝ) :
    (∑ H ∈ subcriticalAdmissibleKeyRemainders K eta,
      retainedKeyPartitionFunction K m delta ((finiteGraphEdges H).card : ℤ)) =
        retainedKeyCleanPartitionFunction K eta m delta := by
  rw [subcriticalAdmissibleKeyRemainders, Finset.sum_biUnion]
  · unfold retainedKeyCleanPartitionFunction
    simp only [Fintype.card_fin]
    apply Finset.sum_congr rfl
    intro b hb
    calc
      _ = ∑ _H ∈ subcriticalRetainedKeyRemainderGraphFinset K b,
          retainedKeyPartitionFunction K m delta (b : ℤ) := by
        apply Finset.sum_congr rfl
        intro H hH
        rw [(mem_subcriticalRetainedKeyRemainderGraphFinset K b H).mp hH |>.2]
      _ = _ := by simp [card_subcriticalRetainedKeyRemainderGraphFinset]
  · intro b _ c _ hbc
    apply Finset.disjoint_left.mpr
    intro H hb hc
    exact hbc (((mem_subcriticalRetainedKeyRemainderGraphFinset K b H).mp hb).2.symm.trans
      ((mem_subcriticalRetainedKeyRemainderGraphFinset K c H).mp hc).2)

theorem subcriticalFixedKeyRemainder_card_bounds
    (hk : 3 ≤ k) (hn : k - 1 ≤ n) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (K : SubcriticalRetainedKey k (Fin n))
    (H : SimpleGraph {v : Fin n // v ∈ K.remainder})
    (hK : (subcriticalRetainedKeyCompletions K eta R₀).Nonempty)
    (P : SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n)
    (hetaOne : eta ≤ 1) (homega : omega ≤ 1)
    (hdensity : gamma / 8 * (n : ℝ)^2 ≤ m)
    (hpoly : subcriticalAggregationPolynomialReserve k n R₀ eta theta)
    (hbridge : SubcriticalMinimizerBridge hk L R₀ omega eta theta alpha delta epsilon tau n) :
    let F := subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau
    (((subcriticalFixedKeyRemainderGraphFinset
        (subcriticalCanonicalNoncleanGraphFinset F eta R₀ hk hn)
        K eta R₀ hk (by simpa using hn) H).card : ℝ) ≤
      Real.exp (-subcriticalAggregationConstant k eta R₀ * n) *
        retainedKeyPartitionFunction K m delta ((finiteGraphEdges H).card : ℤ)) ∧
    (((subcriticalFixedKeyRemainderGraphFinset F K eta R₀ hk (by simpa using hn) H).card : ℝ) ≤
      (1 + Real.exp (-subcriticalAggregationConstant k eta R₀ * n)) *
        retainedKeyPartitionFunction K m delta ((finiteGraphEdges H).card : ℤ)) := by
  let F := subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau
  let D := subcriticalFixedRemainderCompletion K eta R₀ H hK
  have hD : retainedKey D eta R₀ = K :=
    (subcriticalFixedRemainderCompletion_mem K eta R₀ H hK).2
  let H' := retainedKeyRemainderTransport K D eta R₀ hD H
  let FH := subcriticalFixedKeyRemainderGraphFinset F K eta R₀ hk (by simpa using hn) H
  have A := subcriticalFixedKeyRemainder_aggregationGeometry (m := m) hk hn K H hK hbridge
  have hfixed : ∀ G ∈ FH, subcriticalRemainderGraph G D eta R₀ = H' :=
    fun _ hG ↦ subcriticalFixedKeyRemainder_remainder_eq F hk hn K H hK hG
  have hz : retainedPartitionFunction D eta R₀ m delta ((finiteGraphEdges H').card : ℤ) =
      retainedKeyPartitionFunction K m delta ((finiteGraphEdges H).card : ℤ) := by
    rw [retainedKeyRemainderTransport_card, ← retainedKeyPartitionFunction_retainedKey, hD]
  have hnon := subcriticalNoncleanDivision_card_le_fixedRemainder
    hk J FH H' P hetaOne homega hdensity A hfixed hpoly
  have hall := subcriticalDivision_card_le_fixedRemainder
    hk J FH H' P hetaOne homega hdensity A hfixed hpoly
  rw [hz] at hnon hall
  constructor
  · rw [subcriticalFixedKeyNoncleanRemainder_eq F hk hn K H hK]
    exact hnon
  · exact hall

/-- Every nonempty fixed fiber supplies an induced-free remainder below
the genuine geometric sparse-edge cutoff. No condition is imposed on an
arbitrary graph H: impossible fibers are discarded because they are empty. -/
theorem subcriticalFixedKeyRemainder_mem_admissible
    (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (K : SubcriticalRetainedKey k (Fin n))
    (H : SimpleGraph {v : Fin n // v ∈ K.remainder})
    (hK : (subcriticalRetainedKeyCompletions K eta R₀).Nonempty)
    (P : SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n)
    (homega : omega ≤ 1)
    (hbridge : SubcriticalMinimizerBridge hk L R₀ omega eta theta alpha delta epsilon tau n)
    {G : SimpleGraph (Fin n)}
    (hG : G ∈ subcriticalFixedKeyRemainderGraphFinset
      (subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau)
      K eta R₀ hk (by simpa using hn) H) :
    H ∈ subcriticalAdmissibleKeyRemainders K eta := by
  let F := subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau
  let D := subcriticalFixedRemainderCompletion K eta R₀ H hK
  have A := subcriticalFixedKeyRemainder_aggregationGeometry (m := m) hk hn K H hK hbridge
  let R := (A.close G hG).some
  have hdata := (mem_subcriticalFixedKeyRemainderGraphFinset
    F K eta R₀ hk (by simpa using hn) H G).mp hG
  have hR := P.localConditions.retained_order
  have heta := P.localConditions.eta_pos
  have hthetaEta : theta ≤ eta := by
    have hRreal : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR
    exact P.localConditions.retained_visible.trans (div_le_self heta.le (by linarith))
  have hb := (R.sparseSideControls heta.le hR P.retained_inverse homega hthetaEta
    (P.epsilon_cap.trans (min_le_left _ _))
    (P.epsilon_cap.trans (min_le_right _ _)) P.residual.sparse_scale (A.free G hG)).1
  have hedge := subcriticalRemainderGraph_edgeCount G D eta R₀
  rw [subcriticalFixedKeyRemainder_remainder_eq F hk hn K H hK hG,
    retainedKeyRemainderTransport_card] at hedge
  apply (mem_subcriticalAdmissibleKeyRemainders K eta H).mpr
  constructor
  · rw [← hdata.2.2]
    intro h
    exact A.free G hG (h.trans
      (SimpleGraph.Embedding.comap (Function.Embedding.subtype _) G).isIndContained)
  · apply Nat.le_floor
    rw [hedge]
    exact hb

/-- Summing fixed H once gives both key-fiber bounds. This is a new bound
from the fixed-remainder reconstruction argument, not a removal of duplicate
terms from the old full-division bound. -/
theorem subcriticalCanonicalRetainedKey_card_bounds
    (hk : 3 ≤ k) (hn : k - 1 ≤ n) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (K : SubcriticalRetainedKey k (Fin n))
    (P : SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n)
    (hetaOne : eta ≤ 1) (homega : omega ≤ 1)
    (hdensity : gamma / 8 * (n : ℝ)^2 ≤ m)
    (hpoly : subcriticalAggregationPolynomialReserve k n R₀ eta theta)
    (hbridge : SubcriticalMinimizerBridge hk L R₀ omega eta theta alpha delta epsilon tau n) :
    let F := subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau
    (((subcriticalCanonicalRetainedKeyGraphFinset
        (subcriticalCanonicalNoncleanGraphFinset F eta R₀ hk hn)
        K eta R₀ hk (by simpa using hn)).card : ℝ) ≤
      Real.exp (-subcriticalAggregationConstant k eta R₀ * n) *
        retainedKeyCleanPartitionFunction K eta m delta) ∧
    (((subcriticalCanonicalRetainedKeyGraphFinset
        F K eta R₀ hk (by simpa using hn)).card : ℝ) ≤
      (1 + Real.exp (-subcriticalAggregationConstant k eta R₀ * n)) *
        retainedKeyCleanPartitionFunction K eta m delta) := by
  let F := subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau
  let FN := subcriticalCanonicalNoncleanGraphFinset F eta R₀ hk hn
  have hFN : FN ⊆ F := Finset.filter_subset _ _
  have hsub : subcriticalCanonicalRetainedKeyGraphFinset FN K eta R₀ hk (by simpa using hn) ⊆
      subcriticalCanonicalRetainedKeyGraphFinset F K eta R₀ hk (by simpa using hn) := by
    intro G hG
    obtain ⟨hG, hkey⟩ := (mem_subcriticalCanonicalRetainedKeyGraphFinset
      FN K eta R₀ hk (by simpa using hn) G).mp hG
    exact (mem_subcriticalCanonicalRetainedKeyGraphFinset
      F K eta R₀ hk (by simpa using hn) G).mpr ⟨hFN hG, hkey⟩
  by_cases hne : (subcriticalCanonicalRetainedKeyGraphFinset
      F K eta R₀ hk (by simpa using hn)).Nonempty
  swap
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hne
    have hzn := Finset.subset_empty.mp (hz ▸ hsub)
    change ((_ : ℝ) ≤ _) ∧ ((_ : ℝ) ≤ _)
    rw [hzn, hz, Finset.card_empty, Nat.cast_zero]
    constructor <;> positivity
  obtain ⟨G₀, hG₀⟩ := hne
  have hK := subcriticalRetainedKeyCompletions_nonempty_of_mem
    F K eta R₀ hk (by simpa using hn) hG₀
  have hempty (H : SimpleGraph {v : Fin n // v ∈ K.remainder})
      (hH : H ∉ subcriticalAdmissibleKeyRemainders K eta) :
      subcriticalFixedKeyRemainderGraphFinset F K eta R₀ hk (by simpa using hn) H = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro G hG
    exact hH (subcriticalFixedKeyRemainder_mem_admissible hk hn K H hK P homega hbridge hG)
  have hemptyN (H : SimpleGraph {v : Fin n // v ∈ K.remainder})
      (hH : H ∉ subcriticalAdmissibleKeyRemainders K eta) :
      subcriticalFixedKeyRemainderGraphFinset FN K eta R₀ hk (by simpa using hn) H = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro G hG
    obtain ⟨hGF, hkey, hrem⟩ := (mem_subcriticalFixedKeyRemainderGraphFinset
      FN K eta R₀ hk (by simpa using hn) H G).mp hG
    have hh := (mem_subcriticalFixedKeyRemainderGraphFinset
      F K eta R₀ hk (by simpa using hn) H G).mpr ⟨hFN hGF, hkey, hrem⟩
    rw [hempty H hH] at hh
    exact Finset.notMem_empty _ hh
  have hsumF : (subcriticalCanonicalRetainedKeyGraphFinset
      F K eta R₀ hk (by simpa using hn)).card =
      ∑ H ∈ subcriticalAdmissibleKeyRemainders K eta,
        (subcriticalFixedKeyRemainderGraphFinset F K eta R₀ hk (by simpa using hn) H).card := by
    rw [card_subcriticalCanonicalRetainedKeyGraphFinset_eq_sum_remainders]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro H _ hH
    rw [hempty H hH, Finset.card_empty]
  have hsumN : (subcriticalCanonicalRetainedKeyGraphFinset
      FN K eta R₀ hk (by simpa using hn)).card =
      ∑ H ∈ subcriticalAdmissibleKeyRemainders K eta,
        (subcriticalFixedKeyRemainderGraphFinset FN K eta R₀ hk (by simpa using hn) H).card := by
    rw [card_subcriticalCanonicalRetainedKeyGraphFinset_eq_sum_remainders]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro H _ hH
    rw [hemptyN H hH, Finset.card_empty]
  have hz : (∑ H ∈ subcriticalAdmissibleKeyRemainders K eta,
      (retainedKeyPartitionFunction K m delta ((finiteGraphEdges H).card : ℤ) : ℝ)) =
      (retainedKeyCleanPartitionFunction K eta m delta : ℝ) := by
    exact_mod_cast sum_retainedKeyPartitionFunction_remainders K eta m delta
  have hfixed H := subcriticalFixedKeyRemainder_card_bounds
    hk hn J K H hK P hetaOne homega hdensity hpoly hbridge
  constructor
  · change ((_ : ℕ) : ℝ) ≤ _
    rw [hsumN, Nat.cast_sum, ← hz, Finset.mul_sum]
    exact Finset.sum_le_sum fun H _ ↦ (hfixed H).1
  · change ((_ : ℕ) : ℝ) ≤ _
    rw [hsumF, Nat.cast_sum, ← hz, Finset.mul_sum]
    exact Finset.sum_le_sum fun H _ ↦ (hfixed H).2


end InducedStars
