import InducedStars.Graphon.TypeTowerFinal
import InducedStars.Graphon.TypeTowerRecursion
import InducedStars.PriorLiterature
import InducedStars.Regularity.TypeLemma
import Mathlib.Tactic

/-!
# The Type Graphon Sequence Lemma

This module performs the paper-facing assembly of the clean Type tower.  The
finite construction uses the enhanced Type Lemma, while the graphon limit is
obtained only after the tower's exact nested-density-matrix compatibility has
been proved.
-/

noncomputable section

open Filter
open scoped Topology

namespace InducedStars

open Regularity

/-- The first clean tower level, constructed over the one-part partition. -/
private theorem exists_initialCleanTypeLevel
    {f : ℕ} (hf : 0 < f)
    (G : (n : ℕ) → SimpleGraph (Fin (n + 1)))
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    {epsilonStar : ℝ} (hepsilonStar : 0 < epsilonStar)
    (hStar :
      ∀ L t : ℕ, 0 < L → 0 < t →
        ∀ eta : ℝ, 0 < eta → eta < epsilonStar →
          ∃ U n0 : ℕ,
            ∀ {V : Type} [Fintype V] [DecidableEq V]
              (H : SimpleGraph V) [DecidableRel H.Adj]
              {q : ℕ} (_hq : 0 < q) (_hqt : q ≤ t)
              (initial : EquitableInitialPartition V q),
                n0 ≤ Fintype.card V →
                  Nonempty (TypeLemmaResult H eta delta f initial L U)) :
    Nonempty (CleanTypeSequenceLevel (f := f) G
      (typeSequenceEta epsilonStar 0) delta) := by
  obtain ⟨R, ⟨C⟩⟩ := exists_compactCleanTypeRowResult_of_typeLemma
    hf G EquitablePartitionRow.trivial (by norm_num) delta hdelta hdeltaHalf
    hStar (typeSequenceEta_pos hepsilonStar 0)
    (typeSequenceEta_lt hepsilonStar 0)
    1 1 (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C.toCleanTypeSequenceLevel⟩

/-- Construct the next tower level, with at least twice as many clusters,
over the current clean row. -/
private theorem exists_successorCleanTypeLevel
    {f : ℕ} (hf : 0 < f)
    (G : (n : ℕ) → SimpleGraph (Fin (n + 1)))
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    {epsilonStar : ℝ} (hepsilonStar : 0 < epsilonStar)
    (hStar :
      ∀ L t : ℕ, 0 < L → 0 < t →
        ∀ eta : ℝ, 0 < eta → eta < epsilonStar →
          ∃ U n0 : ℕ,
            ∀ {V : Type} [Fintype V] [DecidableEq V]
              (H : SimpleGraph V) [DecidableRel H.Adj]
              {q : ℕ} (_hq : 0 < q) (_hqt : q ≤ t)
              (initial : EquitableInitialPartition V q),
                n0 ≤ Fintype.card V →
                  Nonempty (TypeLemmaResult H eta delta f initial L U))
    (m : ℕ)
    (parent : CleanTypeSequenceLevel (f := f) G
      (typeSequenceEta epsilonStar m) delta) :
    Nonempty (CleanTypeTowerSuccessor
      (typeSequenceEta epsilonStar (m + 1)) parent) := by
  obtain ⟨R, ⟨C⟩⟩ := exists_compactCleanTypeRowResult_of_typeLemma
    hf G parent.row parent.clusterCount_pos delta hdelta hdeltaHalf hStar
    (typeSequenceEta_pos hepsilonStar (m + 1))
    (typeSequenceEta_lt hepsilonStar (m + 1))
    (2 * parent.clusterCount) parent.clusterCount
    (Nat.mul_pos (by norm_num) parent.clusterCount_pos)
    parent.clusterCount_pos le_rfl
  refine ⟨{
    child := C.toCleanTypeSequenceLevel
    extension :=
      CompactCleanTypeRowResult.toCleanTypeSequenceExtension parent R C
    clusterCount_growth := ?_ }⟩
  letI : DecidableRel
      (G (parent.row.extraction (R.factor (C.selection 0)))).Adj :=
    Classical.decRel _
  calc
    2 * parent.clusterCount ≤
        (R.result (C.selection 0)).regularityType.partition.clusterCount :=
      (R.result (C.selection 0)).lower_clusterCount
    _ = parent.clusterCount * R.childCount :=
      R.clusterCount_eq (C.selection 0)
    _ = C.toCleanTypeSequenceLevel.clusterCount := rfl

/-- Finish the graphon-limit argument from an exact clean Type tower. -/
private theorem typeGraphonSequence_of_cleanTypeTower
    {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon) (delta : ℝ)
    {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
    (hGfree : ∀ n, ¬ InducedEmbeds F (G n))
    (hGcut : Tendsto (fun n ↦ cutDist (graphGraphon (G n)) W)
      atTop (nhds 0))
    {epsilonStar : ℝ} (hepsilonStar : 0 < epsilonStar)
    (S : CleanTypeTowerSystem (f := f) G
      (typeSequenceEta epsilonStar) delta) :
    Nonempty (TypeGraphonSequenceResult F W delta) := by
  obtain ⟨D⟩ := TypeTowerDiagonalSelection.nonempty
    (eta := typeSequenceEta epsilonStar) (delta := delta) (level := S.level)
  obtain ⟨W', hmatrix, _hblocks⟩ :=
    PriorLiterature.lovaszSzegedyNestedMatrixLimit_l1 S.nestedDensityMatrices
  have hmatrix' : Tendsto
      (fun m ↦ graphonL1Dist (S.matrixLimitGraphon m) W')
      atTop (nhds 0) := by
    apply hmatrix.congr'
    filter_upwards [] with m
    simp [PriorLiterature.nestedMatrixGraphon,
      CleanTypeTowerSystem.matrixLimitGraphon,
      CleanTypeTowerSystem.nestedDensityMatrices_matrix]
    congr
  exact ⟨(S.toTypeSequenceAssemblyData D
    (typeSequenceEta_pos hepsilonStar)
    (typeSequenceEta_tendsto_zero hepsilonStar)
    hGfree hGcut W' hmatrix').toTypeGraphonSequenceResult⟩

/-- Paper: Lemma `lemma:UFHatGraphonSeq`.

The density threshold satisfies `0 < delta < 1 / 2`. The finite
diagonal-block term vanishes because successive reduced graphs at least
double in order.

The result retains the actual induced-`F`-free hosts and their actual Types,
not merely the resulting graphons. -/
theorem typeGraphonSequence
    {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon) (delta : ℝ)
    (hdelta : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hfree : graphonInducedDensity F W = 0) :
    Nonempty (TypeGraphonSequenceResult F W delta) := by
  by_cases hf : 0 < f
  · obtain ⟨G, hGfree, _hGhom, hGcut⟩ :=
      PriorLiterature.existsInducedFreeApproximatingGraphSequence_cut F W hfree
    obtain ⟨epsilonStar, hepsilonStar, _hepsilonStarHalf, hStar⟩ :=
      Regularity.typeLemma delta f hdelta hdeltaHalf hf
    have hbase : Nonempty (CleanTypeSequenceLevel (f := f) G
        (typeSequenceEta epsilonStar 0) delta) :=
      exists_initialCleanTypeLevel hf G delta hdelta hdeltaHalf
        hepsilonStar hStar
    have hstep : ∀ (m : ℕ)
        (parent : CleanTypeSequenceLevel (f := f) G
          (typeSequenceEta epsilonStar m) delta),
        Nonempty (CleanTypeTowerSuccessor
          (typeSequenceEta epsilonStar (m + 1)) parent) := by
      intro m parent
      exact exists_successorCleanTypeLevel hf G delta hdelta hdeltaHalf
        hepsilonStar hStar m parent
    obtain ⟨S⟩ := exists_cleanTypeTowerSystem_of_base_step hbase hstep
    exact typeGraphonSequence_of_cleanTypeTower F W delta
      hGfree hGcut hepsilonStar S
  · have hfzero : f = 0 := Nat.eq_zero_of_not_pos hf
    subst f
    have hone := graphonInducedDensity_fin_zero F W
    rw [hfree] at hone
    norm_num at hone

end InducedStars
