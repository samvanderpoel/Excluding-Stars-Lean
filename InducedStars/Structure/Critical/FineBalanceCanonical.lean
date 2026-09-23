import InducedStars.Structure.Critical.FineBalance
import InducedStars.Structure.Critical.FixedSparseCoverMultiplicity
import Mathlib.Tactic

/-!
# Canonical fixed-sparse transfer for critical fine balance

This file connects the raw ordered-cover Gaussian calculation in
`Critical.FineBalance` to actual canonical clean graph families with a fixed
sparse induced graph.  The deterministic cover-multiplicity and denominator
comparisons remain separate: here we prove the exact finite injection and
multinomial summation bounds they consume.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance criticalFineBalanceCanonicalGraphDecidableEq
    (n : ℕ) : DecidableEq (SimpleGraph (Fin n)) :=
  Classical.decEq _

noncomputable local instance criticalFineBalanceCanonicalDivisionDecidableEq
    (k n : ℕ) : DecidableEq (SupercriticalDivision k (Fin n)) :=
  Classical.decEq _

noncomputable local instance criticalFineBalanceCanonicalRemainderDecidableEq
    (n : ℕ) (S : Finset (Fin n)) :
    DecidableEq (SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))) :=
  Classical.decEq _

noncomputable local instance criticalFineBalanceCanonicalEdgeSetFintype
    {V : Type*} [Fintype V] (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

noncomputable local instance criticalFineBalanceCanonicalAdjDecidable
    {V : Type*} (G : SimpleGraph V) : DecidableRel G.Adj :=
  Classical.decRel _

/-! ## Exact multinomial count of displayed divisions -/

/-- Divisions with a prescribed sparse set and prescribed ordered main-part
size vector. -/
noncomputable def criticalFixedSparseSizeVectorDivisions
    (k n : ℕ) (S : Finset (Fin n)) (a : Fin (k - 1) → ℕ) :
    Finset (SupercriticalDivision k (Fin n)) :=
  (criticalFixedSparseCoverDivisions k n S).filter fun D ↦
    criticalMainPartSizeVector D = a

@[simp] theorem mem_criticalFixedSparseSizeVectorDivisions
    {k n : ℕ} {S : Finset (Fin n)} {a : Fin (k - 1) → ℕ}
    {D : SupercriticalDivision k (Fin n)} :
    D ∈ criticalFixedSparseSizeVectorDivisions k n S a ↔
      D.sparse = S ∧ criticalMainPartSizeVector D = a := by
  simp [criticalFixedSparseSizeVectorDivisions]

private theorem assignmentFiberSize_fullAssignment
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) (hD : D.IsFull)
    (i : Fin (k - 1)) :
    DenseGraph.assignmentFiberSize (D.fullAssignment hD) i =
      (D.parts i).card := by
  apply congrArg Finset.card
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hv
    simpa [hv] using D.fullAssignment_mem_part hD v
  · intro hv
    exact D.mem_part_unique (D.fullAssignment_mem_part hD v) hv

/-- There are at most the expected multinomial number of ordered displayed
divisions with fixed sparse set and size vector.  Restricting to the
complement of `S` turns the division into an ordinary labeled assignment. -/
theorem card_criticalFixedSparseSizeVectorDivisions_le_multinomial
    {k n : ℕ} (S : Finset (Fin n)) (a : Fin (k - 1) → ℕ)
    (hsum : ∑ i, a i = n - S.card) :
    (criticalFixedSparseSizeVectorDivisions k n S a).card ≤
      Nat.multinomial Finset.univ a := by
  classical
  let family := criticalFixedSparseSizeVectorDivisions k n S a
  have hdata (D : ↑family) :
      D.1.sparse = S ∧ criticalMainPartSizeVector D.1 = a :=
    mem_criticalFixedSparseSizeVectorDivisions.mp D.2
  let core (D : ↑family) :
      SupercriticalDivision k (Fin (fixedSparseCoreCard S)) :=
    fixedSparseCoreFinDivision S D.1 (hdata D).1
  have hcoreFull (D : ↑family) : (core D).IsFull := by
    dsimp [core]
    exact fixedSparseCoreFinDivision_isFull (hdata D).1
  let encode (D : ↑family) :
      {f : Fin (fixedSparseCoreCard S) → Fin (k - 1) //
        f ∈ DenseGraph.assignmentsOfFiberSizes a} :=
    ⟨(core D).fullAssignment (hcoreFull D), by
      rw [DenseGraph.mem_assignmentsOfFiberSizes]
      intro i
      rw [assignmentFiberSize_fullAssignment]
      dsimp [core]
      rw [card_fixedSparseCoreFinDivision_part]
      exact congrFun (hdata D).2 i⟩
  have hencode : Function.Injective encode := by
    intro D E hDE
    have hfun : (core D).fullAssignment (hcoreFull D) =
        (core E).fullAssignment (hcoreFull E) :=
      congrArg Subtype.val hDE
    apply Subtype.ext
    apply fixedSparseCoreFinDivision_injective (hdata D).1 (hdata E).1
    apply SupercriticalDivision.assignment_injective
    funext v
    rw [(core D).assignment_eq_some_fullAssignment (hcoreFull D),
      (core E).assignment_eq_some_fullAssignment (hcoreFull E), hfun]
  have hcard := Fintype.card_le_of_injective encode hencode
  have hcard' : family.card ≤
      (DenseGraph.assignmentsOfFiberSizes
        (V := Fin (fixedSparseCoreCard S)) a).card := by
    simpa only [Fintype.card_coe] using hcard
  calc
    family.card ≤ (DenseGraph.assignmentsOfFiberSizes
        (V := Fin (fixedSparseCoreCard S)) a).card := hcard'
    _ = Nat.multinomial Finset.univ a := by
      apply DenseGraph.card_assignmentsOfFiberSizes_eq_multinomial
      rw [Fintype.card_fin]
      simpa only [fixedSparseCoreCard] using hsum

/-! ## Fixed-remainder canonical numerator -/

/-- The part of one canonical clean division fiber having one prescribed
graph induced on its sparse set. -/
noncomputable def criticalFixedRemainderCleanDivisionGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n))
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    (D : SupercriticalDivision k (Fin n)) :
    Finset (SimpleGraph (Fin n)) :=
  (criticalCleanDivisionGraphFinset k hk n tau hn D).filter fun G ↦
    fixedSparseRemainderGraph S G = R

@[simp] theorem mem_criticalFixedRemainderCleanDivisionGraphFinset
    {k : ℕ} {hk : 3 ≤ k} {n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {S : Finset (Fin n)}
    {R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))}
    {D : SupercriticalDivision k (Fin n)} {G : SimpleGraph (Fin n)} :
    G ∈ criticalFixedRemainderCleanDivisionGraphFinset
        k hk n tau hn S R D ↔
      G ∈ criticalCleanDivisionGraphFinset k hk n tau hn D ∧
        fixedSparseRemainderGraph S G = R := by
  simp [criticalFixedRemainderCleanDivisionGraphFinset]

/-- The full canonical clean family with both its canonical sparse set and
the graph induced on that sparse set prescribed.  This is the exact
fixed-remainder conditioning family used by the denominator comparison. -/
noncomputable def criticalFixedRemainderCanonicalCleanGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n))
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))) :
    Finset (SimpleGraph (Fin n)) :=
  (criticalCanonicalCleanFixedSparseGraphFinset k hk n tau hn S).filter fun G ↦
    fixedSparseRemainderGraph S G = R

@[simp] theorem mem_criticalFixedRemainderCanonicalCleanGraphFinset
    {k : ℕ} {hk : 3 ≤ k} {n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {S : Finset (Fin n)}
    {R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))}
    {G : SimpleGraph (Fin n)} :
    G ∈ criticalFixedRemainderCanonicalCleanGraphFinset
        k hk n tau hn S R ↔
      G ∈ criticalCanonicalCleanFixedSparseGraphFinset
          k hk n tau hn S ∧
        fixedSparseRemainderGraph S G = R := by
  simp [criticalFixedRemainderCanonicalCleanGraphFinset]

/-- Actual canonical clean graphs with fixed sparse induced graph and with
main-part range above the literal `sqrt (log₂ n)` cutoff.  The nested union
is indexed first by range, then size vector, then displayed division; this
is the form needed for exact multinomial summation. -/
noncomputable def
    criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n))
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))) :
    Finset (SimpleGraph (Fin n)) :=
  ((Finset.Icc 0 n).filter fun d : ℕ ↦
      Real.sqrt (Real.logb 2 (n : ℝ)) < (d : ℝ)).biUnion fun d ↦
    (criticalFixedSparseSizeVectorShell k n S.card d hk).biUnion fun a ↦
      (criticalFixedSparseSizeVectorDivisions k n S a).biUnion fun D ↦
        criticalFixedRemainderCleanDivisionGraphFinset
          k hk n tau hn S R D

/-- The nested counting presentation is extensionally the fixed-remainder
filter of the literal canonical, clean, fixed-sparse-set bad family. -/
theorem mem_criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset
    {k : ℕ} {hk : 3 ≤ k} {n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {S : Finset (Fin n)}
    {R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))}
    {G : SimpleGraph (Fin n)} :
    G ∈ criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset
        k hk n tau hn S R ↔
      G ∈ criticalFixedSparseUnbalancedCleanGraphFinset
          k hk n tau hn S ∧
        fixedSparseRemainderGraph S G = R := by
  classical
  constructor
  · intro hG
    rw [criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset,
      Finset.mem_biUnion] at hG
    obtain ⟨d, hd, hG⟩ := hG
    rw [Finset.mem_biUnion] at hG
    obtain ⟨a, ha, hG⟩ := hG
    rw [Finset.mem_biUnion] at hG
    obtain ⟨D, hD, hG⟩ := hG
    have hdData := Finset.mem_filter.mp hd
    have haData := mem_criticalFixedSparseSizeVectorShell.mp ha
    have hDData := mem_criticalFixedSparseSizeVectorDivisions.mp hD
    have hGData :=
      mem_criticalFixedRemainderCleanDivisionGraphFinset.mp hG
    constructor
    · rw [criticalFixedSparseUnbalancedCleanGraphFinset,
        Finset.mem_biUnion]
      refine ⟨D, ?_, hGData.1⟩
      rw [Finset.mem_filter]
      refine ⟨mem_criticalDivisionsWithSparseSet.mpr hDData.1, ?_⟩
      intro hbalanced
      have hrange :
          (DenseGraph.sizeVectorRange (by omega : 0 < k - 1) a : ℝ) ≤
            Real.sqrt (Real.logb 2 (n : ℝ)) := by
        simpa [IsCriticalFineBalanced, criticalMainPartSizeRange,
          criticalMainPartSizeVector, hDData.2] using hbalanced
      rw [haData.2.1] at hrange
      exact (not_lt_of_ge hrange) hdData.2
    · exact hGData.2
  · rintro ⟨hbad, hremainder⟩
    rw [criticalFixedSparseUnbalancedCleanGraphFinset,
      Finset.mem_biUnion] at hbad
    obtain ⟨D, hD, hGclean⟩ := hbad
    have hDData := Finset.mem_filter.mp hD
    have hsparse := mem_criticalDivisionsWithSparseSet.mp hDData.1
    let a := criticalMainPartSizeVector D
    let d := criticalMainPartSizeRange hk D
    have hsum : ∑ i, a i = n - S.card := by
      have hparts := D.card_parts_add_card_sparse
      simp only [Fintype.card_fin] at hparts
      dsimp [a, criticalMainPartSizeVector]
      rw [hsparse] at hparts
      omega
    have hrange : DenseGraph.sizeVectorRange
        (by omega : 0 < k - 1) a = d := by
      rfl
    have hdCutoff : Real.sqrt (Real.logb 2 (n : ℝ)) < (d : ℝ) := by
      have := hDData.2
      rw [IsCriticalFineBalanced, not_le] at this
      exact this
    have hdLe : d ≤ n := by
      obtain ⟨i, hi⟩ := DenseGraph.exists_eq_sizeVectorMax
        (by omega : 0 < k - 1) a
      calc
        d ≤ DenseGraph.sizeVectorMax (by omega : 0 < k - 1) a := by
          dsimp [d, criticalMainPartSizeRange]
          exact Nat.sub_le _ _
        _ = a i := hi.symm
        _ = (D.parts i).card := rfl
        _ ≤ n := by simpa using Finset.card_le_univ (D.parts i)
    rw [criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset,
      Finset.mem_biUnion]
    refine ⟨d, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hdLe⟩, hdCutoff⟩, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨a, mem_criticalFixedSparseSizeVectorShell.mpr
      ⟨hsum, hrange, ?_⟩, ?_⟩
    · intro i
      exact (D.parts_nonempty i).card_pos
    · rw [Finset.mem_biUnion]
      refine ⟨D, mem_criticalFixedSparseSizeVectorDivisions.mpr
        ⟨hsparse, rfl⟩, ?_⟩
      exact mem_criticalFixedRemainderCleanDivisionGraphFinset.mpr
        ⟨hGclean, hremainder⟩

/-! ## One-division injection into the missing cross-edge slice -/

/-- Once the sparse induced graph is fixed, restriction to the complementary
core injects a canonical clean division fiber into the corresponding full
co-multipartite fiber.  Taking complements among the cross coordinates gives
the division-independent missing-coordinate count used by the raw mass. -/
theorem card_criticalFixedRemainderCleanDivisionGraphFinset_le_choose_missing
    {k n : ℕ} (hk : 3 ≤ k) (tau : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n))
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    (D : SupercriticalDivision k (Fin n)) (hD : D.sparse = S) :
    (criticalFixedRemainderCleanDivisionGraphFinset
        k hk n tau hn S R D).card ≤
      Nat.choose
        (DenseGraph.multipartiteCrossCapacity
          (criticalMainPartSizeVector D))
        (criticalFixedSparseCrossMissingCount
          k n S.card R.edgeFinset.card) := by
  classical
  let family := criticalFixedRemainderCleanDivisionGraphFinset
    k hk n tau hn S R D
  let C := fixedSparseCoreFinDivision S D hD
  let t := R.edgeFinset.card
  let mCore := criticalEdgeCount k n - t
  let target := supercriticalCoPartiteFiber C mCore
  have hclean (G : ↑family) : supercriticalDefectGraph G.1 D = ⊥ := by
    have hG :=
      mem_criticalFixedRemainderCleanDivisionGraphFinset.mp G.2 |>.1
    obtain ⟨_hclose, hcanonical, hzero⟩ :=
      mem_supercriticalCleanDivisionGraphFinset.mp hG
    apply simpleGraph_eq_bot_of_finiteGraphEdges_card_eq_zero
    simpa [canonicalSupercriticalDefectGraph, hcanonical] using hzero
  have hremainder (G : ↑family) : fixedSparseRemainderGraph S G.1 = R :=
    (mem_criticalFixedRemainderCleanDivisionGraphFinset.mp G.2).2
  have htotal (G : ↑family) :
      (finiteGraphEdges G.1).card = criticalEdgeCount k n := by
    have hG :=
      mem_criticalFixedRemainderCleanDivisionGraphFinset.mp G.2 |>.1
    have hclose := (mem_supercriticalCleanDivisionGraphFinset.mp hG).1
    have hedge := (mem_supercriticalCloseGraphFinset.mp hclose).2.1
    simpa [finiteGraphEdges_card_eq_edgeFinset_card] using hedge
  have hcoreCard (G : ↑family) :
      (finiteGraphEdges (fixedSparseCoreGraph S G.1)).card = mCore := by
    have hdecomp := card_core_add_remainder_eq_of_fixedSparse_clean
      hD (hclean G)
    rw [hremainder G, htotal G] at hdecomp
    dsimp [mCore, t]
    omega
  let encode : ↑family → ↑target := fun G ↦
    ⟨fixedSparseCoreGraph S G.1,
      fixedSparseCoreGraph_mem_supercriticalCoPartiteFiber
        hD (hclean G) (by
          simpa only [card_finiteGraphEdges_fixedSparseCoreGraph] using
            hcoreCard G)⟩
  have hencode : Function.Injective encode := by
    intro G H hGH
    apply Subtype.ext
    apply fixedSparseGraph_eq_of_core_eq_of_remainder_eq
      hD hD (hclean G) (hclean H)
    · exact congrArg Subtype.val hGH
    · exact (hremainder G).trans (hremainder H).symm
  have hcardTarget : family.card ≤ target.card := by
    have hcard := Fintype.card_le_of_injective encode hencode
    simpa only [Fintype.card_coe] using hcard
  by_cases hfamily : family.Nonempty
  · obtain ⟨G, hG⟩ := hfamily
    let Gsub : ↑family := ⟨G, hG⟩
    have htarget : fixedSparseCoreGraph S G ∈ target := (encode Gsub).2
    have htargetData := mem_supercriticalCoPartiteFiber.mp htarget
    have hlower : divisionInternalCliqueCapacity C ≤ mCore :=
      htargetData.2.1
    obtain ⟨Achoice, hAchoice, hAcard, _hgraph⟩ := htargetData.2.2
    have hselected : mCore - divisionInternalCliqueCapacity C ≤
        supercriticalTotalCrossCapacity C := by
      have hcard := Finset.card_le_card hAchoice
      rw [hAcard, card_supercriticalTaggedCrossChoiceUniverse] at hcard
      exact hcard
    have hcross : supercriticalTotalCrossCapacity C =
        DenseGraph.multipartiteCrossCapacity
          (criticalMainPartSizeVector D) := by
      rw [supercriticalTotalCrossCapacity_eq_multipartiteCrossCapacity]
      apply congrArg DenseGraph.multipartiteCrossCapacity
      funext i
      simpa [C, criticalMainPartSizeVector] using
        (card_fixedSparseCoreFinDivision_part hD i)
    have hinternal : divisionInternalCliqueCapacity C =
        divisionInternalCliqueCapacity D := by
      unfold divisionInternalCliqueCapacity
      apply Finset.sum_congr rfl
      intro i _hi
      rw [card_fixedSparseCoreFinDivision_part hD]
    have hsupport : D.support.card = n - S.card := by
      have hpartition := D.card_support_add_card_sparse
      simp only [Fintype.card_fin] at hpartition
      rw [hD] at hpartition
      omega
    have hcapacity := supercriticalTotalCrossCapacity_add_internal D
    rw [hsupport,
      supercriticalTotalCrossCapacity_eq_multipartiteCrossCapacity] at hcapacity
    have htLe : t ≤ criticalEdgeCount k n := by
      have hdecomp := card_core_add_remainder_eq_of_fixedSparse_clean
        hD (hclean Gsub)
      rw [hremainder Gsub, htotal Gsub] at hdecomp
      dsimp [t] at hdecomp ⊢
      omega
    have hmCoreAdd : mCore + t = criticalEdgeCount k n := by
      dsimp [mCore]
      exact Nat.sub_add_cancel htLe
    have hcapacityC : supercriticalTotalCrossCapacity C +
        divisionInternalCliqueCapacity C = Nat.choose (n - S.card) 2 := by
      rw [hcross, hinternal]
      exact hcapacity
    have hselectedSplit :
        (mCore - divisionInternalCliqueCapacity C) +
            divisionInternalCliqueCapacity C = mCore :=
      Nat.sub_add_cancel hlower
    have hcrossSplit :
        (supercriticalTotalCrossCapacity C -
            (mCore - divisionInternalCliqueCapacity C)) +
          (mCore - divisionInternalCliqueCapacity C) =
        supercriticalTotalCrossCapacity C :=
      Nat.sub_add_cancel hselected
    have hmissing :
        DenseGraph.multipartiteCrossCapacity
              (criticalMainPartSizeVector D) -
            (mCore - divisionInternalCliqueCapacity C) =
          criticalFixedSparseCrossMissingCount
            k n S.card R.edgeFinset.card := by
      rw [← hcross]
      have hadd :
          (supercriticalTotalCrossCapacity C -
              (mCore - divisionInternalCliqueCapacity C)) +
              criticalEdgeCount k n =
            Nat.choose (n - S.card) 2 + t := by
        omega
      have hsub := Nat.eq_sub_of_add_eq hadd
      simpa only [criticalFixedSparseCrossMissingCount, t] using hsub
    have htargetCard := card_supercriticalCoPartiteFiber C
      (fixedSparseCoreFinDivision_isFull hD) (m := mCore)
    rw [if_pos hlower] at htargetCard
    calc
      family.card ≤ target.card := hcardTarget
      _ = Nat.choose (supercriticalTotalCrossCapacity C)
          (mCore - divisionInternalCliqueCapacity C) := htargetCard
      _ = Nat.choose (supercriticalTotalCrossCapacity C)
          (supercriticalTotalCrossCapacity C -
            (mCore - divisionInternalCliqueCapacity C)) :=
        (Nat.choose_symm hselected).symm
      _ = Nat.choose
          (DenseGraph.multipartiteCrossCapacity
            (criticalMainPartSizeVector D))
          (criticalFixedSparseCrossMissingCount
            k n S.card R.edgeFinset.card) := by
        rw [hcross, hmissing]
  · have hempty : family = ∅ := Finset.not_nonempty_iff_eq_empty.mp hfamily
    simp [family, hempty]

/-! ## Summation over displayed divisions -/

/-- After fixing the graph induced on the sparse set, the actual canonical
unbalanced numerator is bounded by the raw ordered-cover mass from
`Critical.FineBalance`.  The proof loses only by taking union bounds: the
number of displayed divisions with a given size vector is bounded by the
corresponding multinomial coefficient, and each fixed-division fiber injects
into its missing-cross-coordinate binomial slice. -/
theorem
    card_criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset_le_raw
    {k n : ℕ} (hk : 3 ≤ k) (tau : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n))
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))) :
    ((criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset
        k hk n tau hn S R).card : ℝ) ≤
      criticalFixedSparseUnbalancedCrossSliceMass
        k hk n S.card R.edgeFinset.card := by
  classical
  let ranges : Finset ℕ :=
    (Finset.Icc 0 n).filter fun d : ℕ ↦
      Real.sqrt (Real.logb 2 (n : ℝ)) < (d : ℝ)
  let vectors (d : ℕ) : Finset (Fin (k - 1) → ℕ) :=
    criticalFixedSparseSizeVectorShell k n S.card d hk
  let divisions (a : Fin (k - 1) → ℕ) :
      Finset (SupercriticalDivision k (Fin n)) :=
    criticalFixedSparseSizeVectorDivisions k n S a
  let graphs (D : SupercriticalDivision k (Fin n)) :
      Finset (SimpleGraph (Fin n)) :=
    criticalFixedRemainderCleanDivisionGraphFinset
      k hk n tau hn S R D
  let missing := criticalFixedSparseCrossMissingCount
    k n S.card R.edgeFinset.card
  have hgraph (a : Fin (k - 1) → ℕ) (D : SupercriticalDivision k (Fin n))
      (hD : D ∈ divisions a) :
      ((graphs D).card : ℝ) ≤
        (Nat.choose (DenseGraph.multipartiteCrossCapacity a) missing : ℝ) := by
    have hDData := mem_criticalFixedSparseSizeVectorDivisions.mp hD
    have hcard :=
      card_criticalFixedRemainderCleanDivisionGraphFinset_le_choose_missing
        hk tau hn S R D hDData.1
    have hcardReal : ((graphs D).card : ℝ) ≤
        (Nat.choose
          (DenseGraph.multipartiteCrossCapacity
            (criticalMainPartSizeVector D))
          missing : ℝ) := by
      dsimp [graphs, missing]
      exact_mod_cast hcard
    simpa [hDData.2] using hcardReal
  have hdivisions (a : Fin (k - 1) → ℕ)
      (haSum : ∑ i, a i = n - S.card) :
      ∑ D ∈ divisions a, ((graphs D).card : ℝ) ≤
        (Nat.multinomial Finset.univ a : ℝ) *
          (Nat.choose (DenseGraph.multipartiteCrossCapacity a) missing : ℝ) := by
    calc
      ∑ D ∈ divisions a, ((graphs D).card : ℝ) ≤
          ∑ _D ∈ divisions a,
            (Nat.choose (DenseGraph.multipartiteCrossCapacity a) missing : ℝ) :=
        Finset.sum_le_sum fun D hD ↦ hgraph a D hD
      _ = ((divisions a).card : ℝ) *
          (Nat.choose (DenseGraph.multipartiteCrossCapacity a) missing : ℝ) := by
        simp
      _ ≤ (Nat.multinomial Finset.univ a : ℝ) *
          (Nat.choose (DenseGraph.multipartiteCrossCapacity a) missing : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast
          card_criticalFixedSparseSizeVectorDivisions_le_multinomial S a haSum
  have hinner (d : ℕ) (a : Fin (k - 1) → ℕ) (ha : a ∈ vectors d) :
      (((divisions a).biUnion graphs).card : ℝ) ≤
        (Nat.multinomial Finset.univ a : ℝ) *
          (Nat.choose (DenseGraph.multipartiteCrossCapacity a) missing : ℝ) := by
    calc
      (((divisions a).biUnion graphs).card : ℝ) ≤
          ∑ D ∈ divisions a, ((graphs D).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le
          (s := divisions a) (t := graphs))
      _ ≤ (Nat.multinomial Finset.univ a : ℝ) *
          (Nat.choose (DenseGraph.multipartiteCrossCapacity a) missing : ℝ) := by
        exact hdivisions a (mem_criticalFixedSparseSizeVectorShell.mp ha).1
  have hmiddle (d : ℕ) :
      (((vectors d).biUnion fun a ↦ (divisions a).biUnion graphs).card : ℝ) ≤
        ∑ a ∈ vectors d,
          (Nat.multinomial Finset.univ a : ℝ) *
            (Nat.choose (DenseGraph.multipartiteCrossCapacity a) missing : ℝ) := by
    calc
      (((vectors d).biUnion fun a ↦ (divisions a).biUnion graphs).card : ℝ) ≤
          ∑ a ∈ vectors d,
            (((divisions a).biUnion graphs).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le
          (s := vectors d) (t := fun a ↦ (divisions a).biUnion graphs))
      _ ≤ ∑ a ∈ vectors d,
          (Nat.multinomial Finset.univ a : ℝ) *
            (Nat.choose (DenseGraph.multipartiteCrossCapacity a) missing : ℝ) :=
        Finset.sum_le_sum fun a ha ↦ hinner d a ha
  change
    (((ranges.biUnion fun d ↦
        (vectors d).biUnion fun a ↦
          (divisions a).biUnion graphs).card : ℕ) : ℝ) ≤
      ∑ d ∈ ranges, ∑ a ∈ vectors d,
        (Nat.multinomial Finset.univ a : ℝ) *
          (Nat.choose (DenseGraph.multipartiteCrossCapacity a) missing : ℝ)
  calc
    (((ranges.biUnion fun d ↦
        (vectors d).biUnion fun a ↦
          (divisions a).biUnion graphs).card : ℕ) : ℝ) ≤
        ∑ d ∈ ranges,
          ((((vectors d).biUnion fun a ↦
            (divisions a).biUnion graphs).card : ℕ) : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le
        (s := ranges)
        (t := fun d ↦ (vectors d).biUnion fun a ↦
          (divisions a).biUnion graphs))
    _ ≤ ∑ d ∈ ranges, ∑ a ∈ vectors d,
        (Nat.multinomial Finset.univ a : ℝ) *
          (Nat.choose (DenseGraph.multipartiteCrossCapacity a) missing : ℝ) :=
      Finset.sum_le_sum fun d _hd ↦ hmiddle d

/-- Actual canonical clean fixed-remainder graphs above the literal
`sqrt (log₂ n)` cutoff are bounded by the balanced ordered-cover reference
mass times the universal Gaussian tail.  This is the fixed-remainder
numerator estimate used by the later cover-multiplicity transfer. -/
theorem
    card_criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset_le_reference_mul_error
    {k n : ℕ} (hk : 3 ≤ k) (tau : ℝ) (hn : k - 1 ≤ n)
    (hnTwo : 2 ≤ n) (S : Finset (Fin n))
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    (hsSmall : (S.card : ℝ) ≤
      criticalFineBalanceSparseFraction k * (n : ℝ)) :
    ((criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset
        k hk n tau hn S R).card : ℝ) ≤
      criticalFixedSparseBalancedCrossSliceMass
          k n S.card R.edgeFinset.card *
        criticalFineBalanceRawError k n := by
  calc
    ((criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset
        k hk n tau hn S R).card : ℝ) ≤
        criticalFixedSparseUnbalancedCrossSliceMass
          k hk n S.card R.edgeFinset.card :=
      card_criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset_le_raw
        hk tau hn S R
    _ ≤ criticalFixedSparseBalancedCrossSliceMass
          k n S.card R.edgeFinset.card *
        DenseGraph.gaussianRangeShellTail (k - 1)
          (criticalFineBalanceCrossGaussianRate k) n :=
      criticalFixedSparseUnbalancedCrossSliceMass_le hk hnTwo
        (by simpa using Finset.card_le_univ S) hsSmall
    _ = criticalFixedSparseBalancedCrossSliceMass
          k n S.card R.edgeFinset.card *
        criticalFineBalanceRawError k n := rfl

end InducedStars
