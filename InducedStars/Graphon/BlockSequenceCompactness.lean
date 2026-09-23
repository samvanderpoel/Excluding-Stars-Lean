import InducedStars.Graphon.FiniteBlockLayouts
import InducedStars.Graphon.LimitInputs
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic

/-!
# Compactness of ordered profile block sequences

This file supplies the local sequential compactness argument needed for the
subcritical optimizer classification.  It extracts all block lengths in one
countable compact product and then uses a nested subsequence tower for the
finite core labels.  At each fixed rank a core either becomes literally
constant or its order tends to infinity.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace InducedStars

namespace RegularBlockCore

/-- Two bundled cores are equal once their dependent graph fields are
heterogeneously equal and their orders agree. -/
theorem eq_of_order_eq_of_graph_heq {k : ℕ} (A B : RegularBlockCore k)
    (horder : A.order = B.order) (hgraph : A.graph ≍ B.graph) : A = B := by
  cases A
  cases B
  rw [RegularBlockCore.mk.injEq]
  exact ⟨horder, hgraph⟩

end RegularBlockCore

namespace Graphon

/-! ## A local core dichotomy -/

/-- The two possible limits of the core label at one fixed block rank. -/
inductive CoreRankLimit (k : ℕ) where
  | persistent (core : RegularBlockCore k)
  | diffuse

/-- A subsequence witnessing the persistent/diffuse dichotomy for one
sequence of literal regular cores. -/
structure CoreSubsequenceLimit {k : ℕ} (C : ℕ → RegularBlockCore k) where
  extraction : ℕ → ℕ
  extraction_strictMono : StrictMono extraction
  limit : CoreRankLimit k
  persistent_eq : ∀ (core : RegularBlockCore k),
    limit = CoreRankLimit.persistent core →
      ∀ n, C (extraction n) = core
  diffuse_order_tendsto :
    limit = CoreRankLimit.diffuse →
      Tendsto (fun n ↦ (C (extraction n)).order) atTop atTop

/-- An unbounded natural-number sequence admits a strictly monotone index
subsequence along which its values tend to infinity. -/
theorem exists_subsequence_tendsto_atTop_of_not_bddAbove
    (u : ℕ → ℕ) (hu : ¬ BddAbove (Set.range u)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop atTop := by
  have hrange : (Set.range u).Infinite := by
    intro hfinite
    exact hu hfinite.bddAbove
  let values : ℕ → ℕ := Nat.nth (fun r ↦ r ∈ Set.range u)
  have hvalues_mem (n : ℕ) : values n ∈ Set.range u :=
    Nat.nth_mem_of_infinite hrange n
  let index : ℕ → ℕ := fun n ↦ Classical.choose (hvalues_mem n)
  have hindex (n : ℕ) : u (index n) = values n :=
    Classical.choose_spec (hvalues_mem n)
  have hvalues_strict : StrictMono values := Nat.nth_strictMono hrange
  have hindex_injective : Function.Injective index := by
    intro a b hab
    apply hvalues_strict.injective
    rw [← hindex a, ← hindex b, hab]
  obtain ⟨ψ, hψ, hindexψ⟩ :=
    strictMono_subseq_of_tendsto_atTop hindex_injective.nat_tendsto_atTop
  refine ⟨index ∘ ψ, hindexψ, ?_⟩
  have hvalues_top : Tendsto values atTop atTop :=
    hvalues_strict.tendsto_atTop
  have hcomp := hvalues_top.comp hψ.tendsto_atTop
  apply hcomp.congr'
  filter_upwards [] with n
  simp only [Function.comp_apply]
  exact (hindex (ψ n)).symm

/-- A sequence of regular finite cores has either a literally constant
subsequence or a subsequence whose orders tend to infinity. -/
theorem exists_coreSubsequenceLimit {k : ℕ}
    (C : ℕ → RegularBlockCore k) :
    Nonempty (CoreSubsequenceLimit C) := by
  classical
  by_cases hbounded : BddAbove (Set.range fun n ↦ (C n).order)
  · obtain ⟨U, hU⟩ := hbounded
    have horder_le (n : ℕ) : (C n).order ≤ U := hU ⟨n, rfl⟩
    obtain ⟨r, hrpos, hrU, φ, hφ, horder⟩ :=
      boundedNat_constant_subsequence U (fun n ↦ (C n).order)
        (fun n ↦ (C n).order_pos) horder_le
    let graphAt : ℕ → SimpleGraph (Fin r) := fun n ↦
      cast (congrArg (fun q ↦ SimpleGraph (Fin q)) (horder n))
        (C (φ n)).graph
    obtain ⟨G, ψ, hψ, hgraph⟩ := finite_constant_subsequence graphAt
    let coreLim : RegularBlockCore k := C (φ (ψ 0))
    have hcore (n : ℕ) : C (φ (ψ n)) = coreLim := by
      apply RegularBlockCore.eq_of_order_eq_of_graph_heq
      · exact (horder (ψ n)).trans (horder (ψ 0)).symm
      · let hn := congrArg (fun q ↦ SimpleGraph (Fin q)) (horder (ψ n))
        let hzero := congrArg (fun q ↦ SimpleGraph (Fin q)) (horder (ψ 0))
        have hcastn :
            cast hn (C (φ (ψ n))).graph = G := hgraph n
        have hcastzero :
            cast hzero (C (φ (ψ 0))).graph = G := hgraph 0
        exact (cast_heq hn (C (φ (ψ n))).graph).symm.trans
          ((heq_of_eq (hcastn.trans hcastzero.symm)).trans
            (cast_heq hzero (C (φ (ψ 0))).graph))
    exact ⟨{
      extraction := φ ∘ ψ
      extraction_strictMono := hφ.comp hψ
      limit := CoreRankLimit.persistent coreLim
      persistent_eq := by
        intro core hlimit n
        injection hlimit with h
        simpa [h] using hcore n
      diffuse_order_tendsto := by simp
    }⟩
  · obtain ⟨φ, hφ, htop⟩ :=
      exists_subsequence_tendsto_atTop_of_not_bddAbove
        (fun n ↦ (C n).order) hbounded
    exact ⟨{
      extraction := φ
      extraction_strictMono := hφ
      limit := CoreRankLimit.diffuse
      persistent_eq := by simp
      diffuse_order_tendsto := by
        intro _
        exact htop
    }⟩

/-- A fixed classical choice of the core dichotomy, used to build the
rankwise nested subsequence tower. -/
noncomputable def coreSubsequenceLimit {k : ℕ}
    (C : ℕ → RegularBlockCore k) : CoreSubsequenceLimit C :=
  Classical.choice (exists_coreSubsequenceLimit C)

/-! ## One diagonal extraction for all ranks -/

/-- The recursively refined rows.  Row zero is the supplied base extraction;
the successor row additionally settles the core label at the preceding rank. -/
noncomputable def orderedCoreTowerRow {k : ℕ}
    (L : ℕ → AdmissibleBlockSequence k) (base : ℕ → ℕ) :
    ℕ → ℕ → ℕ
  | 0 => base
  | i + 1 =>
      let row := orderedCoreTowerRow L base i
      row ∘ (coreSubsequenceLimit (fun n ↦ (L (row n)).core i)).extraction

theorem orderedCoreTowerRow_strictMono {k : ℕ}
    (L : ℕ → AdmissibleBlockSequence k) {base : ℕ → ℕ}
    (hbase : StrictMono base) (i : ℕ) :
    StrictMono (orderedCoreTowerRow L base i) := by
  induction i with
  | zero => simpa [orderedCoreTowerRow] using hbase
  | succ i ih =>
      simpa only [orderedCoreTowerRow] using ih.comp
        (coreSubsequenceLimit
          (fun n ↦ (L (orderedCoreTowerRow L base i n)).core i)).extraction_strictMono

/-- The nested tower of core-label refinements. -/
noncomputable def orderedCoreTower {k : ℕ}
    (L : ℕ → AdmissibleBlockSequence k) (base : ℕ → ℕ)
    (hbase : StrictMono base) : SubsequenceTower where
  extraction := orderedCoreTowerRow L base
  strictMono := orderedCoreTowerRow_strictMono L hbase
  next_refines := by
    intro i
    refine ⟨(coreSubsequenceLimit
      (fun n ↦ (L (orderedCoreTowerRow L base i n)).core i)).extraction,
      (coreSubsequenceLimit
        (fun n ↦ (L (orderedCoreTowerRow L base i n)).core i)).extraction_strictMono,
      ?_⟩
    rfl

/-- The selected persistent/diffuse alternative at rank `i`. -/
noncomputable def orderedCoreRankLimit {k : ℕ}
    (L : ℕ → AdmissibleBlockSequence k) (base : ℕ → ℕ)
    (i : ℕ) : CoreRankLimit k :=
  (coreSubsequenceLimit
    (fun n ↦ (L (orderedCoreTowerRow L base i n)).core i)).limit

/-- Simultaneous rankwise limit data for an ordered block sequence. -/
structure OrderedBlockLimitData {k : ℕ}
    (L : ℕ → AdmissibleBlockSequence k) where
  extraction : ℕ → ℕ
  extraction_strictMono : StrictMono extraction
  alphaLimit : ℕ → ℝ
  alpha_tendsto : ∀ i,
    Tendsto (fun m ↦ (L (extraction m)).alpha i) atTop (nhds (alphaLimit i))
  coreLimit : ℕ → CoreRankLimit k
  persistent_eventually : ∀ i (core : RegularBlockCore k),
    coreLimit i = CoreRankLimit.persistent core →
      ∀ᶠ m in atTop, (L (extraction m)).core i = core
  diffuse_order_tendsto : ∀ i,
    coreLimit i = CoreRankLimit.diffuse →
      Tendsto (fun m ↦ ((L (extraction m)).core i).order) atTop atTop

/-- One cofinal subsequence simultaneously settles every block length and
every core rank. -/
theorem exists_orderedBlockLimitData {k : ℕ}
    (L : ℕ → AdmissibleBlockSequence k) :
    Nonempty (OrderedBlockLimitData L) := by
  let alphaUI : ℕ → ℕ → unitInterval := fun m i ↦
    ⟨(L m).alpha i, (L m).alpha_nonneg i, (L m).alpha_le_one i⟩
  obtain ⟨alphaLim, base, hbase, halpha⟩ := CompactSpace.tendsto_subseq alphaUI
  let T := orderedCoreTower L base hbase
  have hdiag : StrictMono T.diagonal := T.diagonal_strictMono
  refine ⟨{
    extraction := T.diagonal
    extraction_strictMono := hdiag
    alphaLimit := fun i ↦ (alphaLim i : ℝ)
    alpha_tendsto := ?_
    coreLimit := orderedCoreRankLimit L base
    persistent_eventually := ?_
    diffuse_order_tendsto := ?_
  }⟩
  · intro i
    have hrowUI :
        Tendsto (fun n ↦ alphaUI (base n) i) atTop (nhds (alphaLim i)) :=
      tendsto_pi_nhds.mp halpha i
    have hrow :
        Tendsto (fun n ↦ (L (base n)).alpha i) atTop
          (nhds (alphaLim i : ℝ)) :=
      (continuous_subtype_val.tendsto (alphaLim i)).comp hrowUI
    rw [tendsto_def] at hrow ⊢
    intro s hs
    apply T.eventually_diagonal_of_eventually_row
      (m := 0) (P := fun n ↦ (L n).alpha i ∈ s)
    simpa [T, orderedCoreTower, orderedCoreTowerRow] using hrow s hs
  · intro i core hlimit
    let S := coreSubsequenceLimit
      (fun n ↦ (L (orderedCoreTowerRow L base i n)).core i)
    have hrow : ∀ n,
        (L (orderedCoreTowerRow L base (i + 1) n)).core i = core := by
      intro n
      exact S.persistent_eq core hlimit n
    apply T.eventually_diagonal_of_row
      (m := i + 1) (P := fun n ↦ (L n).core i = core)
    simpa [T, orderedCoreTower] using hrow
  · intro i hlimit
    let S := coreSubsequenceLimit
      (fun n ↦ (L (orderedCoreTowerRow L base i n)).core i)
    have hrow : Tendsto
        (fun n ↦ (L (orderedCoreTowerRow L base (i + 1) n)).core i |>.order)
        atTop atTop := S.diffuse_order_tendsto hlimit
    rw [tendsto_atTop_atTop] at hrow ⊢
    intro b
    have hrow' : ∀ᶠ n in atTop,
        b ≤ ((L (T.extraction (i + 1) n)).core i).order := by
      simpa [T, orderedCoreTower, eventually_atTop] using hrow b
    have hdiag' := T.eventually_diagonal_of_eventually_row
      (m := i + 1) (P := fun n ↦ b ≤ ((L n).core i).order) hrow'
    simpa only [eventually_atTop] using hdiag'

namespace OrderedBlockLimitData

variable {k : ℕ} {L : ℕ → AdmissibleBlockSequence k}
  (D : OrderedBlockLimitData L)

theorem alphaLimit_nonneg (i : ℕ) : 0 ≤ D.alphaLimit i := by
  exact ge_of_tendsto (D.alpha_tendsto i)
    (Eventually.of_forall fun m ↦ (L (D.extraction m)).alpha_nonneg i)

theorem alphaLimit_le_one (i : ℕ) : D.alphaLimit i ≤ 1 := by
  exact le_of_tendsto (D.alpha_tendsto i)
    (Eventually.of_forall fun m ↦ (L (D.extraction m)).alpha_le_one i)

theorem alphaLimit_antitone : Antitone D.alphaLimit := by
  intro i j hij
  exact le_of_tendsto_of_tendsto (D.alpha_tendsto j) (D.alpha_tendsto i)
    (Eventually.of_forall fun m ↦
      (L (D.extraction m)).alpha_antitone hij)

/-- Every finite partial sum of limiting block lengths is at most one. -/
theorem sum_range_alphaLimit_le_one (N : ℕ) :
    ∑ i ∈ Finset.range N, D.alphaLimit i ≤ 1 := by
  have hsum : Tendsto
      (fun m ↦ ∑ i ∈ Finset.range N, (L (D.extraction m)).alpha i)
      atTop (nhds (∑ i ∈ Finset.range N, D.alphaLimit i)) := by
    exact tendsto_finset_sum (Finset.range N) fun i _ ↦ D.alpha_tendsto i
  apply le_of_tendsto hsum
  filter_upwards [] with m
  exact ((L (D.extraction m)).summable_alpha.sum_le_tsum
    (Finset.range N) (fun i _ ↦ (L (D.extraction m)).alpha_nonneg i)).trans
      (L (D.extraction m)).tsum_alpha_le_one

/-- The limiting nonnegative length sequence is summable. -/
theorem summable_alphaLimit : Summable D.alphaLimit := by
  apply summable_of_sum_le D.alphaLimit_nonneg
  intro s
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range s
  calc
    ∑ i ∈ s, D.alphaLimit i ≤
        ∑ i ∈ Finset.range N, D.alphaLimit i :=
      Finset.sum_le_sum_of_subset_of_nonneg hN
        (fun i _ _ ↦ D.alphaLimit_nonneg i)
    _ ≤ 1 := D.sum_range_alphaLimit_le_one N

theorem tsum_alphaLimit_le_one : ∑' i, D.alphaLimit i ≤ 1 := by
  exact D.summable_alphaLimit.tsum_le_of_sum_le fun s ↦ by
    obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range s
    exact (Finset.sum_le_sum_of_subset_of_nonneg hN
      (fun i _ _ ↦ D.alphaLimit_nonneg i)).trans
        (D.sum_range_alphaLimit_le_one N)

/-! ## Persistent positive ranks and their increasing enumeration -/

/-- A rank survives in the limiting candidate precisely when it has positive
limiting length and its literal core persists. -/
def PersistentPositive (i : ℕ) : Prop :=
  0 < D.alphaLimit i ∧
    ∃ core : RegularBlockCore k,
      D.coreLimit i = CoreRankLimit.persistent core

instance persistentPositiveDecidable (i : ℕ) : Decidable (D.PersistentPositive i) :=
  Classical.propDecidable _

/-- `some s` for `s` persistent-positive ranks and `none` when there are
infinitely many. -/
noncomputable def persistentCount : Option ℕ := by
  classical
  exact if h : (Set.ofPred D.PersistentPositive).Finite then
    some h.toFinset.card
  else none

/-- Persistent-positive ranks enumerated in increasing original-rank order. -/
noncomputable def persistentRank (j : ℕ) : ℕ :=
  Nat.nth D.PersistentPositive j

theorem active_persistentCount_iff (j : ℕ) :
    blockIndexActive D.persistentCount j ↔
      ∀ h : (Set.ofPred D.PersistentPositive).Finite,
        j < h.toFinset.card := by
  classical
  by_cases hfinite : (Set.ofPred D.PersistentPositive).Finite
  · simp [persistentCount, hfinite, blockIndexActive]
  · simp [persistentCount, hfinite, blockIndexActive]

theorem persistentRank_mem_of_active {j : ℕ}
    (hj : blockIndexActive D.persistentCount j) :
    D.PersistentPositive (D.persistentRank j) := by
  classical
  rw [active_persistentCount_iff] at hj
  unfold persistentRank
  by_cases hfinite : (Set.ofPred D.PersistentPositive).Finite
  · exact Nat.nth_mem_of_lt_card hfinite (hj hfinite)
  · exact Nat.nth_mem_of_infinite hfinite j

theorem persistentRank_strictMono_of_lt_of_active {i j : ℕ}
    (hij : i < j) (hj : blockIndexActive D.persistentCount j) :
    D.persistentRank i < D.persistentRank j := by
  classical
  rw [active_persistentCount_iff] at hj
  unfold persistentRank
  by_cases hfinite : (Set.ofPred D.PersistentPositive).Finite
  · exact Nat.nth_lt_nth_of_lt_card hfinite hij (hj hfinite)
  · exact (Nat.nth_strictMono hfinite) hij

theorem persistentRank_mono_of_le_of_active {i j : ℕ}
    (hij : i ≤ j) (hj : blockIndexActive D.persistentCount j) :
    D.persistentRank i ≤ D.persistentRank j := by
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  · exact (D.persistentRank_strictMono_of_lt_of_active hij hj).le

theorem self_le_persistentRank_of_active {j : ℕ}
    (hj : blockIndexActive D.persistentCount j) :
    j ≤ D.persistentRank j := by
  classical
  rw [active_persistentCount_iff] at hj
  exact Nat.le_nth (fun hfinite ↦ hj hfinite)

/-- Every persistent-positive original rank occurs at a unique active place
in the increasing enumeration. -/
theorem exists_active_persistentRank_eq {i : ℕ} (hi : D.PersistentPositive i) :
    ∃ j, blockIndexActive D.persistentCount j ∧ D.persistentRank j = i := by
  classical
  by_cases hfinite : (Set.ofPred D.PersistentPositive).Finite
  · obtain ⟨j, hjcard, hji⟩ :=
      Nat.exists_lt_card_finite_nth_eq hfinite hi
    refine ⟨j, ?_, hji⟩
    simp [persistentCount, hfinite, blockIndexActive, hjcard]
  · have hinfinite : (Set.ofPred D.PersistentPositive).Infinite := hfinite
    have hi' : i ∈ Set.ofPred D.PersistentPositive := hi
    rw [← Nat.range_nth_of_infinite hinfinite] at hi'
    obtain ⟨j, hji⟩ := hi'
    refine ⟨j, ?_, hji⟩
    simp [persistentCount, hfinite, blockIndexActive]

/-- Number of active final blocks among the first `S` possible final
indices.  It is `S` in the infinite case and `min S s` for `s` final
blocks. -/
def persistentPrefixCount (S : ℕ) : ℕ :=
  match D.persistentCount with
  | none => S
  | some s => min S s

theorem lt_persistentPrefixCount_iff {S j : ℕ} :
    j < D.persistentPrefixCount S ↔
      j < S ∧ blockIndexActive D.persistentCount j := by
  cases hcount : D.persistentCount with
  | none => simp [persistentPrefixCount, hcount, blockIndexActive]
  | some s =>
      simp [persistentPrefixCount, hcount, blockIndexActive]

theorem persistentPrefixCount_le (S : ℕ) :
    D.persistentPrefixCount S ≤ S := by
  cases hcount : D.persistentCount with
  | none => simp [persistentPrefixCount, hcount]
  | some s => simp [persistentPrefixCount, hcount]

theorem persistentRank_mem_of_lt_prefixCount {S j : ℕ}
    (hj : j < D.persistentPrefixCount S) :
    D.PersistentPositive (D.persistentRank j) :=
  D.persistentRank_mem_of_active (D.lt_persistentPrefixCount_iff.mp hj).2

theorem persistentRank_strictMonoOn_prefixCount (S : ℕ) :
    StrictMonoOn D.persistentRank (Iio (D.persistentPrefixCount S)) := by
  intro i hi j hj hij
  exact D.persistentRank_strictMono_of_lt_of_active hij
    (D.lt_persistentPrefixCount_iff.mp hj).2

theorem persistentCount_pos (hnonempty :
    (Set.ofPred D.PersistentPositive).Nonempty) (n : ℕ)
    (hcount : D.persistentCount = some n) : 0 < n := by
  classical
  by_cases hfinite : (Set.ofPred D.PersistentPositive).Finite
  · have hn : n = hfinite.toFinset.card := by
      symm
      simpa [persistentCount, hfinite] using hcount
    rw [hn, Finset.card_pos]
    obtain ⟨i, hi⟩ := hnonempty
    exact ⟨i, (Set.Finite.mem_toFinset hfinite).2 hi⟩
  · simp [persistentCount, hfinite] at hcount

/-- A pair of large final/original rank cutoffs for which the compressed
persistent prefix enumerates exactly the persistent-positive original ranks
inside the original-rank window. -/
structure PersistentWindow (S₀ R₀ : ℕ) where
  finalCutoff : ℕ
  originalCutoff : ℕ
  finalCutoff_large : S₀ ≤ finalCutoff
  originalCutoff_large : R₀ ≤ originalCutoff
  final_le_original : finalCutoff ≤ originalCutoff
  infinite_or_exhausted : D.persistentCount = none ∨
    ∃ n, D.persistentCount = some n ∧ n ≤ finalCutoff
  selected_lt : ∀ {j : ℕ},
    j < D.persistentPrefixCount finalCutoff →
      D.persistentRank j < originalCutoff
  complete : ∀ {i : ℕ}, i < originalCutoff →
    D.PersistentPositive i →
      ∃ j < D.persistentPrefixCount finalCutoff,
        D.persistentRank j = i

/-- Persistent windows exist with both cutoffs arbitrarily large.  In the
infinite case the next persistent rank is the original cutoff; in the finite
case the cutoff is enlarged past the last persistent rank. -/
theorem exists_persistentWindow
    (hnonempty : (Set.ofPred D.PersistentPositive).Nonempty)
    (S₀ R₀ : ℕ) : Nonempty (D.PersistentWindow S₀ R₀) := by
  cases hcount : D.persistentCount with
  | none =>
      let S := max S₀ R₀
      let R := D.persistentRank S
      have hactive (j : ℕ) : blockIndexActive D.persistentCount j := by
        simp [hcount, blockIndexActive]
      have hSleR : S ≤ R := D.self_le_persistentRank_of_active (hactive S)
      exact ⟨{
        finalCutoff := S
        originalCutoff := R
        finalCutoff_large := le_max_left _ _
        originalCutoff_large := (le_max_right _ _).trans hSleR
        final_le_original := hSleR
        infinite_or_exhausted := Or.inl hcount
        selected_lt := by
          intro j hj
          have hjS : j < S :=
            (D.lt_persistentPrefixCount_iff.mp hj).1
          exact D.persistentRank_strictMono_of_lt_of_active hjS (hactive S)
        complete := by
          intro i hiR hi
          obtain ⟨j, hjactive, hjrank⟩ := D.exists_active_persistentRank_eq hi
          refine ⟨j, ?_, hjrank⟩
          rw [D.lt_persistentPrefixCount_iff]
          refine ⟨?_, hjactive⟩
          by_contra hjS
          have hSleJ : S ≤ j := Nat.le_of_not_gt hjS
          have hrankLe : R ≤ D.persistentRank j :=
            D.persistentRank_mono_of_le_of_active hSleJ hjactive
          rw [hjrank] at hrankLe
          exact (not_le_of_gt hiR) hrankLe
      }⟩
  | some n =>
      have hn : 0 < n := D.persistentCount_pos hnonempty n hcount
      let S := max S₀ n
      let last : ℕ := n - 1
      let R := max (max R₀ S) (D.persistentRank last + 1)
      have hlastActive : blockIndexActive D.persistentCount last := by
        simp [hcount, blockIndexActive, last, hn]
      exact ⟨{
        finalCutoff := S
        originalCutoff := R
        finalCutoff_large := le_max_left _ _
        originalCutoff_large :=
          (le_max_left R₀ S).trans (le_max_left _ _)
        final_le_original :=
          (le_max_right R₀ S).trans (le_max_left _ _)
        infinite_or_exhausted :=
          Or.inr ⟨n, hcount, le_max_right S₀ n⟩
        selected_lt := by
          intro j hj
          have hjactive := (D.lt_persistentPrefixCount_iff.mp hj).2
          have hjn : j < n := by
            simpa [hcount, blockIndexActive] using hjactive
          have hjlast : j ≤ last := by
            dsimp [last]
            omega
          have hrankLe : D.persistentRank j ≤ D.persistentRank last :=
            D.persistentRank_mono_of_le_of_active hjlast hlastActive
          exact hrankLe.trans_lt
            (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _))
        complete := by
          intro i _hiR hi
          obtain ⟨j, hjactive, hjrank⟩ := D.exists_active_persistentRank_eq hi
          have hjn : j < n := by
            simpa [hcount, blockIndexActive] using hjactive
          refine ⟨j, ?_, hjrank⟩
          rw [D.lt_persistentPrefixCount_iff]
          exact ⟨hjn.trans_le (le_max_right S₀ n), hjactive⟩
      }⟩

theorem persistentPrefixCount_le_originalCutoff
    {S₀ R₀ : ℕ} (Q : D.PersistentWindow S₀ R₀) :
    D.persistentPrefixCount Q.finalCutoff ≤ Q.originalCutoff :=
  (D.persistentPrefixCount_le Q.finalCutoff).trans Q.final_le_original

/-- A finite permutation that places the selected persistent ranks at the
front of their original-rank window, preserving their increasing order. -/
noncomputable def windowPermutation {S₀ R₀ : ℕ}
    (Q : D.PersistentWindow S₀ R₀) :
    Equiv.Perm (Fin Q.originalCutoff) := by
  let front : Fin (D.persistentPrefixCount Q.finalCutoff) →
      Fin Q.originalCutoff :=
    fun j ↦ Fin.castLE (D.persistentPrefixCount_le_originalCutoff Q) j
  let selected : Fin (D.persistentPrefixCount Q.finalCutoff) →
      Fin Q.originalCutoff :=
    fun j ↦ ⟨D.persistentRank j, Q.selected_lt j.isLt⟩
  have hselected : Function.Injective selected := by
    intro i j hij
    apply Fin.ext
    exact (D.persistentRank_strictMonoOn_prefixCount Q.finalCutoff).injOn
      i.isLt j.isLt (congrArg Fin.val hij)
  exact Classical.choose (Equiv.Perm.exists_extending_pair front selected
    (Fin.castLE_injective _) hselected)

theorem windowPermutation_front {S₀ R₀ : ℕ}
    (Q : D.PersistentWindow S₀ R₀)
    (j : Fin (D.persistentPrefixCount Q.finalCutoff)) :
    D.windowPermutation Q
        (Fin.castLE (D.persistentPrefixCount_le_originalCutoff Q) j) =
      ⟨D.persistentRank j, Q.selected_lt j.isLt⟩ := by
  unfold windowPermutation
  exact Classical.choose_spec
    (Equiv.Perm.exists_extending_pair
      (fun j : Fin (D.persistentPrefixCount Q.finalCutoff) ↦
        Fin.castLE (D.persistentPrefixCount_le_originalCutoff Q) j)
      (fun j ↦ ⟨D.persistentRank j, Q.selected_lt j.isLt⟩)
      (Fin.castLE_injective _)
      (by
        intro i j hij
        apply Fin.ext
        exact (D.persistentRank_strictMonoOn_prefixCount Q.finalCutoff).injOn
          i.isLt j.isLt (congrArg Fin.val hij))) j

theorem windowPermutation_not_persistentPositive_of_suffix
    {S₀ R₀ : ℕ} (Q : D.PersistentWindow S₀ R₀)
    (i : Fin Q.originalCutoff)
    (hi : D.persistentPrefixCount Q.finalCutoff ≤ (i : ℕ)) :
    ¬ D.PersistentPositive (D.windowPermutation Q i) := by
  intro hpersistent
  obtain ⟨j, hj, hjrank⟩ :=
    Q.complete (D.windowPermutation Q i).isLt hpersistent
  let jf : Fin (D.persistentPrefixCount Q.finalCutoff) := ⟨j, hj⟩
  have hfront := D.windowPermutation_front Q jf
  have hpermEq : D.windowPermutation Q
      (Fin.castLE (D.persistentPrefixCount_le_originalCutoff Q) jf) =
      D.windowPermutation Q i := by
    rw [hfront]
    apply Fin.ext
    exact hjrank
  have heq := (D.windowPermutation Q).injective hpermEq
  have hval := congrArg Fin.val heq
  dsimp [jf] at hval
  omega

/-- The literal persistent core selected at an active final index. -/
noncomputable def persistentCore (hk : 3 ≤ k) (j : ℕ) : RegularBlockCore k :=
  if hj : blockIndexActive D.persistentCount j then
    Classical.choose (D.persistentRank_mem_of_active hj).2
  else RegularBlockCore.complete k hk

theorem coreLimit_persistentCore_of_active (hk : 3 ≤ k) {j : ℕ}
    (hj : blockIndexActive D.persistentCount j) :
    D.coreLimit (D.persistentRank j) =
      CoreRankLimit.persistent (D.persistentCore hk j) := by
  rw [persistentCore, dif_pos hj]
  exact Classical.choose_spec (D.persistentRank_mem_of_active hj).2

/-! ## Finite layouts selected by the persistent enumeration -/

/-- At stage `m`, retain the persistent ranks belonging to the first `S`
final indices, packed in increasing original-rank order. -/
noncomputable def selectedStageLayout (S m : ℕ) :
    FiniteProfileBlockLayout k where
  count := D.persistentPrefixCount S
  alpha := fun j ↦
    (L (D.extraction m)).alpha (D.persistentRank j)
  core := fun j ↦
    (L (D.extraction m)).core (D.persistentRank j)
  alpha_nonneg := fun j ↦
    (L (D.extraction m)).alpha_nonneg (D.persistentRank j)
  sum_alpha_le_one := by
    let A := L (D.extraction m)
    let f : Fin (D.persistentPrefixCount S) → ℕ :=
      fun j ↦ D.persistentRank j
    have hf_inj : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      exact (D.persistentRank_strictMonoOn_prefixCount S).injOn
        i.isLt j.isLt hij
    have hs : Summable (fun j : Fin (D.persistentPrefixCount S) ↦
        A.alpha (f j)) := Summable.of_finite
    calc
      ∑ j : Fin (D.persistentPrefixCount S), A.alpha (f j) =
          ∑' j : Fin (D.persistentPrefixCount S), A.alpha (f j) := by
        rw [tsum_fintype]
      _ ≤ ∑' i : ℕ, A.alpha i :=
        hs.tsum_le_tsum_of_inj f hf_inj
          (fun i _ ↦ A.alpha_nonneg i) (fun _ ↦ le_rfl)
          A.summable_alpha
      _ ≤ 1 := A.tsum_alpha_le_one

@[simp] theorem selectedStageLayout_count (S m : ℕ) :
    (D.selectedStageLayout S m).count = D.persistentPrefixCount S := rfl

@[simp] theorem selectedStageLayout_alpha (S m : ℕ)
    (j : Fin (D.persistentPrefixCount S)) :
    (D.selectedStageLayout S m).alpha j =
      (L (D.extraction m)).alpha (D.persistentRank j) := rfl

@[simp] theorem selectedStageLayout_core (S m : ℕ)
    (j : Fin (D.persistentPrefixCount S)) :
    (D.selectedStageLayout S m).core j =
      (L (D.extraction m)).core (D.persistentRank j) := rfl

/-- The same stage lengths with the already selected literal limiting cores.
For fixed `S` this agrees eventually with `selectedStageLayout`. -/
noncomputable def selectedFixedStageLayout (hk : 3 ≤ k) (S m : ℕ) :
    FiniteProfileBlockLayout k where
  count := D.persistentPrefixCount S
  alpha := fun j ↦
    (L (D.extraction m)).alpha (D.persistentRank j)
  core := fun j ↦ D.persistentCore hk j
  alpha_nonneg := fun j ↦
    (L (D.extraction m)).alpha_nonneg (D.persistentRank j)
  sum_alpha_le_one := (D.selectedStageLayout S m).sum_alpha_le_one

@[simp] theorem selectedFixedStageLayout_alpha (hk : 3 ≤ k) (S m : ℕ)
    (j : Fin (D.persistentPrefixCount S)) :
    (D.selectedFixedStageLayout hk S m).alpha j =
      (L (D.extraction m)).alpha (D.persistentRank j) := rfl

@[simp] theorem selectedFixedStageLayout_core (hk : 3 ≤ k) (S m : ℕ)
    (j : Fin (D.persistentPrefixCount S)) :
    (D.selectedFixedStageLayout hk S m).core j = D.persistentCore hk j := rfl

theorem selectedStageLayout_eventually_eq_fixed (hk : 3 ≤ k) (S : ℕ) :
    ∀ᶠ m in atTop,
      D.selectedStageLayout S m = D.selectedFixedStageLayout hk S m := by
  have hcores : ∀ j : Fin (D.persistentPrefixCount S),
      ∀ᶠ m in atTop,
        (L (D.extraction m)).core (D.persistentRank j) =
          D.persistentCore hk j := by
    intro j
    have hjactive := (D.lt_persistentPrefixCount_iff.mp j.isLt).2
    exact D.persistent_eventually (D.persistentRank j)
      (D.persistentCore hk j)
      (D.coreLimit_persistentCore_of_active hk hjactive)
  have hall : ∀ᶠ m in atTop,
      ∀ j : Fin (D.persistentPrefixCount S),
        (L (D.extraction m)).core (D.persistentRank j) =
          D.persistentCore hk j := by
    simpa using (eventually_all_finset (Finset.univ :
      Finset (Fin (D.persistentPrefixCount S)))).2
        (fun j _ ↦ hcores j)
  filter_upwards [hall] with m hm
  unfold selectedStageLayout selectedFixedStageLayout
  congr 1
  funext j
  exact hm j

/-- The corresponding fixed-core layout made from the limiting persistent
lengths. -/
noncomputable def selectedLimitLayout (hk : 3 ≤ k) (S : ℕ) :
    FiniteProfileBlockLayout k where
  count := D.persistentPrefixCount S
  alpha := fun j ↦ D.alphaLimit (D.persistentRank j)
  core := fun j ↦ D.persistentCore hk j
  alpha_nonneg := fun j ↦ D.alphaLimit_nonneg _
  sum_alpha_le_one := by
    let f : Fin (D.persistentPrefixCount S) → ℕ :=
      fun j ↦ D.persistentRank j
    have hf_inj : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      exact (D.persistentRank_strictMonoOn_prefixCount S).injOn
        i.isLt j.isLt hij
    have hs : Summable (fun j : Fin (D.persistentPrefixCount S) ↦
        D.alphaLimit (f j)) := Summable.of_finite
    calc
      ∑ j : Fin (D.persistentPrefixCount S), D.alphaLimit (f j) =
          ∑' j : Fin (D.persistentPrefixCount S),
            D.alphaLimit (f j) := by
        rw [tsum_fintype]
      _ ≤ ∑' i : ℕ, D.alphaLimit i :=
        hs.tsum_le_tsum_of_inj f hf_inj
          (fun i _ ↦ D.alphaLimit_nonneg i) (fun _ ↦ le_rfl)
          D.summable_alphaLimit
      _ ≤ 1 := D.tsum_alphaLimit_le_one

@[simp] theorem selectedLimitLayout_count (hk : 3 ≤ k) (S : ℕ) :
    (D.selectedLimitLayout hk S).count = D.persistentPrefixCount S := rfl

@[simp] theorem selectedLimitLayout_alpha (hk : 3 ≤ k) (S : ℕ)
    (j : Fin (D.persistentPrefixCount S)) :
    (D.selectedLimitLayout hk S).alpha j =
      D.alphaLimit (D.persistentRank j) := rfl

@[simp] theorem selectedLimitLayout_core (hk : 3 ≤ k) (S : ℕ)
    (j : Fin (D.persistentPrefixCount S)) :
    (D.selectedLimitLayout hk S).core j = D.persistentCore hk j := rfl

/-- The limiting admissible sequence obtained by discarding zero-length and
diffuse ranks and retaining persistent-positive ranks in their original
order. -/
noncomputable def limitBlockSequence (hk : 3 ≤ k)
    (hnonempty : (Set.ofPred D.PersistentPositive).Nonempty) :
    AdmissibleBlockSequence k where
  count := D.persistentCount
  count_pos := D.persistentCount_pos hnonempty
  alpha := fun j ↦ if blockIndexActive D.persistentCount j then
    D.alphaLimit (D.persistentRank j) else 0
  core := D.persistentCore hk
  alpha_pos_of_active := by
    intro j hj
    rw [if_pos hj]
    exact (D.persistentRank_mem_of_active hj).1
  alpha_eq_zero_of_inactive := by
    intro j hj
    rw [if_neg hj]
  alpha_antitone := by
    intro i j hij
    change
      (if blockIndexActive D.persistentCount j then
        D.alphaLimit (D.persistentRank j) else 0) ≤
      (if blockIndexActive D.persistentCount i then
        D.alphaLimit (D.persistentRank i) else 0)
    by_cases hj : blockIndexActive D.persistentCount j
    · have hi : blockIndexActive D.persistentCount i := by
        cases hcount : D.persistentCount with
        | none => simp [blockIndexActive, hcount]
        | some n =>
            simp only [blockIndexActive, hcount] at hj ⊢
            omega
      rw [if_pos hi, if_pos hj]
      exact D.alphaLimit_antitone
        (D.persistentRank_mono_of_le_of_active hij hj)
    · rw [if_neg hj]
      split_ifs
      · exact D.alphaLimit_nonneg _
      · exact le_rfl
  summable_alpha := by
    apply Summable.of_nonneg_of_le
      (fun j ↦ by
        split_ifs with hj
        · exact D.alphaLimit_nonneg _
        · exact le_rfl)
      (fun j ↦ by
        split_ifs with hj
        · exact D.alphaLimit_antitone (D.self_le_persistentRank_of_active hj)
        · exact D.alphaLimit_nonneg j)
      D.summable_alphaLimit
  tsum_alpha_le_one := by
    refine (Summable.tsum_le_tsum (fun j ↦ ?_)
      (by
        apply Summable.of_nonneg_of_le
          (fun j ↦ by
            split_ifs with hj
            · exact D.alphaLimit_nonneg _
            · exact le_rfl)
          (fun j ↦ by
            split_ifs with hj
            · exact D.alphaLimit_antitone
                (D.self_le_persistentRank_of_active hj)
            · exact D.alphaLimit_nonneg j)
          D.summable_alphaLimit)
      D.summable_alphaLimit).trans D.tsum_alphaLimit_le_one
    split_ifs with hj
    · exact D.alphaLimit_antitone (D.self_le_persistentRank_of_active hj)
    · exact D.alphaLimit_nonneg j

@[simp] theorem limitBlockSequence_alpha_of_active (hk : 3 ≤ k)
    (hnonempty : (Set.ofPred D.PersistentPositive).Nonempty) {j : ℕ}
    (hj : blockIndexActive D.persistentCount j) :
    (D.limitBlockSequence hk hnonempty).alpha j =
      D.alphaLimit (D.persistentRank j) := by
  simp [limitBlockSequence, hj]

@[simp] theorem limitBlockSequence_core_of_active (hk : 3 ≤ k)
    (hnonempty : (Set.ofPred D.PersistentPositive).Nonempty) {j : ℕ}
    (hj : blockIndexActive D.persistentCount j) :
    (D.limitBlockSequence hk hnonempty).core j = D.persistentCore hk j :=
  rfl

theorem limitBlockSequence_alphaSquareTail_eq_zero_of_count
    (hk : 3 ≤ k)
    (hnonempty : (Set.ofPred D.PersistentPositive).Nonempty)
    {n S : ℕ} (hcount : D.persistentCount = some n) (hnS : n ≤ S) :
    (D.limitBlockSequence hk hnonempty).alphaSquareTail
        (D.persistentPrefixCount S) = 0 := by
  have hprefix : D.persistentPrefixCount S = n := by
    simp [persistentPrefixCount, hcount, Nat.min_eq_right hnS]
  rw [hprefix]
  unfold AdmissibleBlockSequence.alphaSquareTail
  calc
    ∑' j : ℕ, (D.limitBlockSequence hk hnonempty).alpha (n + j) ^ 2 =
        ∑' _j : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro j
      rw [(D.limitBlockSequence hk hnonempty).alpha_eq_zero_of_count_eq_some
        hcount (Nat.le_add_right n j)]
      simp
    _ = 0 := tsum_zero

theorem limitBlockSequence_alphaSquareTail_le_window
    (hk : 3 ≤ k)
    (hnonempty : (Set.ofPred D.PersistentPositive).Nonempty)
    {S₀ R₀ : ℕ} (Q : D.PersistentWindow S₀ R₀) :
    (D.limitBlockSequence hk hnonempty).alphaSquareTail
        (D.persistentPrefixCount Q.finalCutoff) ≤
      1 / ((Q.finalCutoff + 1 : ℕ) : ℝ) := by
  rcases Q.infinite_or_exhausted with hinfinite | ⟨n, hcount, hnS⟩
  · have hprefix : D.persistentPrefixCount Q.finalCutoff = Q.finalCutoff := by
      simp [persistentPrefixCount, hinfinite]
    rw [hprefix]
    exact (D.limitBlockSequence hk hnonempty).alphaSquareTail_le_inv_succ _
  · rw [D.limitBlockSequence_alphaSquareTail_eq_zero_of_count
      hk hnonempty hcount hnS]
    positivity

/-- The persistent-prefix finite layout of the limiting block sequence is
literally the layout assembled from the corresponding rankwise limits. -/
theorem ofPrefix_limitBlockSequence_eq_selectedLimitLayout
    (hk : 3 ≤ k)
    (hnonempty : (Set.ofPred D.PersistentPositive).Nonempty) (S : ℕ) :
    FiniteProfileBlockLayout.ofPrefix
        (D.limitBlockSequence hk hnonempty)
        (D.persistentPrefixCount S) =
      D.selectedLimitLayout hk S := by
  rw [FiniteProfileBlockLayout.mk.injEq]
  refine ⟨rfl, ?_, ?_⟩
  · apply heq_of_eq
    funext j
    change (if blockIndexActive D.persistentCount j then
      D.alphaLimit (D.persistentRank j) else 0) =
        D.alphaLimit (D.persistentRank j)
    rw [if_pos ((D.lt_persistentPrefixCount_iff.mp j.isLt).2)]
  · apply heq_of_eq
    funext j
    rfl

/-! ## Rankwise and total mass limits -/

/-- Limiting normalized mass attached to an original rank.  Diffuse cores
contribute zero; a persistent core contributes the evident quadratic term. -/
def rankMassLimit (i : ℕ) : ℝ :=
  match D.coreLimit i with
  | CoreRankLimit.persistent core => D.alphaLimit i ^ 2 / core.order
  | CoreRankLimit.diffuse => 0

theorem rankMassLimit_nonneg (i : ℕ) : 0 ≤ D.rankMassLimit i := by
  unfold rankMassLimit
  cases D.coreLimit i with
  | persistent core => exact div_nonneg (sq_nonneg _) (by positivity)
  | diffuse => exact le_rfl

theorem rankMassLimit_le (hk : 3 ≤ k) (i : ℕ) :
    D.rankMassLimit i ≤
      (1 / ((k - 1 : ℕ) : ℝ)) * D.alphaLimit i ^ 2 := by
  unfold rankMassLimit
  cases hcore : D.coreLimit i with
  | diffuse => positivity
  | persistent core =>
      simp only [rankMassLimit, hcore]
      have hkpos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < k - 1 by omega)
      have horder : ((k - 1 : ℕ) : ℝ) ≤ core.order := by
        exact_mod_cast RegularBlockCore.k_sub_one_le_order hk core
      have hinv : (1 : ℝ) / core.order ≤
          1 / ((k - 1 : ℕ) : ℝ) :=
        one_div_le_one_div_of_le hkpos horder
      calc
        D.alphaLimit i ^ 2 / (core.order : ℝ) =
            D.alphaLimit i ^ 2 * ((core.order : ℝ))⁻¹ := by
          rw [div_eq_mul_inv]
        _ ≤ D.alphaLimit i ^ 2 * (((k - 1 : ℕ) : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left (by simpa [one_div] using hinv) (sq_nonneg _)
        _ = (1 / ((k - 1 : ℕ) : ℝ)) * D.alphaLimit i ^ 2 := by
          ring

theorem summable_rankMassLimit (hk : 3 ≤ k) :
    Summable D.rankMassLimit := by
  have hsquare : Summable (fun i ↦ D.alphaLimit i ^ 2) := by
    apply Summable.of_nonneg_of_le (fun i ↦ sq_nonneg _)
      (fun i ↦ by
        nlinarith [D.alphaLimit_nonneg i, D.alphaLimit_le_one i])
      D.summable_alphaLimit
  exact Summable.of_nonneg_of_le D.rankMassLimit_nonneg
    (D.rankMassLimit_le hk) (hsquare.mul_left _)

/-- At every fixed original rank, normalized block mass converges to the
persistent-core contribution, while diffuse core orders force the term to
zero. -/
theorem massTerm_tendsto_rankMassLimit (hk : 3 ≤ k) (i : ℕ) :
    Tendsto (fun m ↦ (L (D.extraction m)).massTerm i) atTop
      (nhds (D.rankMassLimit i)) := by
  cases hcore : D.coreLimit i with
  | persistent core =>
      have hconst := D.persistent_eventually i core hcore
      have halpha : Tendsto
          (fun m ↦ (L (D.extraction m)).alpha i ^ 2) atTop
          (nhds (D.alphaLimit i ^ 2)) := (D.alpha_tendsto i).pow 2
      have hquot := halpha.div_const (core.order : ℝ)
      have ht : Tendsto (fun m ↦ (L (D.extraction m)).massTerm i) atTop
          (nhds (D.alphaLimit i ^ 2 / (core.order : ℝ))) := by
        apply hquot.congr'
        filter_upwards [hconst] with m hm
        simp only [AdmissibleBlockSequence.massTerm]
        rw [hm]
      simpa [rankMassLimit, hcore] using ht
  | diffuse =>
      have horderNat := D.diffuse_order_tendsto i hcore
      have horderReal : Tendsto
          (fun m ↦ (((L (D.extraction m)).core i).order : ℝ))
          atTop atTop := tendsto_natCast_atTop_atTop.comp horderNat
      have hinv : Tendsto
          (fun m ↦ (((L (D.extraction m)).core i).order : ℝ)⁻¹)
          atTop (nhds 0) := horderReal.inv_tendsto_atTop
      have hsqueeze : Tendsto
          (fun m ↦ (L (D.extraction m)).massTerm i) atTop (nhds 0) := by
        refine squeeze_zero ?_ ?_ hinv
        · intro m
          exact (L (D.extraction m)).massTerm_nonneg i
        · intro m
          unfold AdmissibleBlockSequence.massTerm
          have ha : (L (D.extraction m)).alpha i ^ 2 ≤ 1 := by
            nlinarith [(L (D.extraction m)).alpha_nonneg i,
              (L (D.extraction m)).alpha_le_one i]
          rw [div_eq_mul_inv]
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right ha (by positivity :
              0 ≤ (((L (D.extraction m)).core i).order : ℝ)⁻¹))
      simpa [rankMassLimit, hcore] using hsqueeze

/-! The analogous one-block estimate for arbitrary profile-valued graphons. -/

/-- `L¹` mass of the profile-valued block at original rank `i` and
subsequence stage `m`. -/
def stageProfileBlockMass (p : ℝ) (m i : ℕ) : ℝ :=
  (L (D.extraction m)).alpha i ^ 2 *
      (1 + ((k - 2 : ℕ) : ℝ) * p) /
    ((L (D.extraction m)).core i).order

theorem stageProfileBlockMass_nonneg {p : ℝ}
    (hp : 0 ≤ p) (m i : ℕ) :
    0 ≤ D.stageProfileBlockMass p m i := by
  unfold stageProfileBlockMass
  positivity

theorem stageProfileBlockMass_le_alpha_sq (hk : 3 ≤ k)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (m i : ℕ) :
    D.stageProfileBlockMass p m i ≤
      (L (D.extraction m)).alpha i ^ 2 := by
  let C := (L (D.extraction m)).core i
  have hnum : 1 + ((k - 2 : ℕ) : ℝ) * p ≤
      ((k - 1 : ℕ) : ℝ) := by
    have hd : 0 ≤ ((k - 2 : ℕ) : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hp.2 hd
    calc
      1 + ((k - 2 : ℕ) : ℝ) * p ≤
          1 + ((k - 2 : ℕ) : ℝ) * 1 := by linarith
      _ = ((k - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (show 2 ≤ k by omega),
          Nat.cast_sub (show 1 ≤ k by omega)]
        ring
  have horder : ((k - 1 : ℕ) : ℝ) ≤ (C.order : ℝ) := by
    exact_mod_cast RegularBlockCore.k_sub_one_le_order hk C
  have hratio : (1 + ((k - 2 : ℕ) : ℝ) * p) / C.order ≤ 1 := by
    exact (div_le_one (by exact_mod_cast C.order_pos)).2 (hnum.trans horder)
  unfold stageProfileBlockMass
  calc
    (L (D.extraction m)).alpha i ^ 2 *
          (1 + ((k - 2 : ℕ) : ℝ) * p) /
        ((L (D.extraction m)).core i).order =
        (L (D.extraction m)).alpha i ^ 2 *
          ((1 + ((k - 2 : ℕ) : ℝ) * p) / C.order) := by
      dsimp [C]
      ring
    _ ≤ (L (D.extraction m)).alpha i ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hratio
        (sq_nonneg ((L (D.extraction m)).alpha i))
    _ = (L (D.extraction m)).alpha i ^ 2 := mul_one _

theorem stageProfileBlockMass_le_order_inv (hk : 3 ≤ k)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (m i : ℕ) :
    D.stageProfileBlockMass p m i ≤
      ((k - 1 : ℕ) : ℝ) /
        ((L (D.extraction m)).core i).order := by
  let C := (L (D.extraction m)).core i
  have ha : (L (D.extraction m)).alpha i ^ 2 ≤ 1 := by
    nlinarith [(L (D.extraction m)).alpha_nonneg i,
      (L (D.extraction m)).alpha_le_one i]
  have hnum : 1 + ((k - 2 : ℕ) : ℝ) * p ≤
      ((k - 1 : ℕ) : ℝ) := by
    have hd : 0 ≤ ((k - 2 : ℕ) : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hp.2 hd
    calc
      1 + ((k - 2 : ℕ) : ℝ) * p ≤
          1 + ((k - 2 : ℕ) : ℝ) * 1 := by linarith
      _ = ((k - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (show 2 ≤ k by omega),
          Nat.cast_sub (show 1 ≤ k by omega)]
        ring
  have hnum0 : 0 ≤ 1 + ((k - 2 : ℕ) : ℝ) * p :=
    add_nonneg zero_le_one (mul_nonneg (by positivity) hp.1)
  unfold stageProfileBlockMass
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    (L (D.extraction m)).alpha i ^ 2 *
        (1 + ((k - 2 : ℕ) : ℝ) * p) ≤
        1 * (1 + ((k - 2 : ℕ) : ℝ) * p) :=
      mul_le_mul_of_nonneg_right ha hnum0
    _ ≤ ((k - 1 : ℕ) : ℝ) := by simpa using hnum

/-- A rank discarded by the persistent-positive compression has vanishing
profile-graphon block mass.  This covers both zero limiting length and
diffuse core order. -/
theorem stageProfileBlockMass_tendsto_zero_of_not_persistentPositive
    (hk : 3 ≤ k) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) {i : ℕ}
    (hi : ¬ D.PersistentPositive i) :
    Tendsto (fun m ↦ D.stageProfileBlockMass p m i) atTop (nhds 0) := by
  by_cases halpha : 0 < D.alphaLimit i
  · have hcore : D.coreLimit i = CoreRankLimit.diffuse := by
      cases hlim : D.coreLimit i with
      | diffuse => rfl
      | persistent core =>
          exact False.elim (hi ⟨halpha, core, hlim⟩)
    have horderNat := D.diffuse_order_tendsto i hcore
    have horderReal : Tendsto
        (fun m ↦ (((L (D.extraction m)).core i).order : ℝ))
        atTop atTop := tendsto_natCast_atTop_atTop.comp horderNat
    have hinv : Tendsto
        (fun m ↦ (((L (D.extraction m)).core i).order : ℝ)⁻¹)
        atTop (nhds 0) := horderReal.inv_tendsto_atTop
    have hbound : Tendsto
        (fun m ↦ ((k - 1 : ℕ) : ℝ) /
          ((L (D.extraction m)).core i).order)
        atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds.mul hinv : Tendsto
          (fun m ↦ ((k - 1 : ℕ) : ℝ) *
            (((L (D.extraction m)).core i).order : ℝ)⁻¹)
          atTop (nhds (((k - 1 : ℕ) : ℝ) * 0)))
    exact squeeze_zero
      (fun m ↦ D.stageProfileBlockMass_nonneg hp.1 m i)
      (fun m ↦ D.stageProfileBlockMass_le_order_inv hk hp m i) hbound
  · have halpha0 : D.alphaLimit i = 0 :=
      le_antisymm (not_lt.mp halpha) (D.alphaLimit_nonneg i)
    have hsquare : Tendsto
        (fun m ↦ (L (D.extraction m)).alpha i ^ 2) atTop (nhds 0) := by
      simpa [halpha0] using (D.alpha_tendsto i).pow 2
    exact squeeze_zero
      (fun m ↦ D.stageProfileBlockMass_nonneg hp.1 m i)
      (fun m ↦ D.stageProfileBlockMass_le_alpha_sq hk hp m i) hsquare

theorem sum_stageProfileBlockMass_tendsto_zero
    (hk : 3 ≤ k) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (s : Finset ℕ) (hs : ∀ i ∈ s, ¬ D.PersistentPositive i) :
    Tendsto (fun m ↦ ∑ i ∈ s, D.stageProfileBlockMass p m i)
      atTop (nhds 0) := by
  simpa using tendsto_finsetSum s fun i hi ↦
    D.stageProfileBlockMass_tendsto_zero_of_not_persistentPositive
      hk hp (hs i hi)

/-- After the window permutation, deleting the suffix of the finite
original-rank window has vanishing `L¹` cost. -/
theorem windowSuffix_l1_tendsto_zero
    (hk : 3 ≤ k) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    {S₀ R₀ : ℕ} (Q : D.PersistentWindow S₀ R₀) :
    Tendsto
      (fun m ↦ graphonL1Dist
        ((((FiniteProfileBlockLayout.ofPrefix
          (L (D.extraction m)) Q.originalCutoff).permute
            (D.windowPermutation Q)).graphon p hp))
        (((FiniteProfileBlockLayout.ofPrefix
          (L (D.extraction m)) Q.originalCutoff).permute
            (D.windowPermutation Q)).prefixGraphon p hp
              (D.persistentPrefixCount Q.finalCutoff)))
      atTop (nhds 0) := by
  let t := D.persistentPrefixCount Q.finalCutoff
  have hterm (i : Fin Q.originalCutoff) : Tendsto
      (fun m ↦ if t ≤ (i : ℕ) then
        D.stageProfileBlockMass p m (D.windowPermutation Q i) else 0)
      atTop (nhds 0) := by
    by_cases hi : t ≤ (i : ℕ)
    · have hvanish :=
        D.stageProfileBlockMass_tendsto_zero_of_not_persistentPositive
          hk hp (D.windowPermutation_not_persistentPositive_of_suffix Q i hi)
      apply hvanish.congr'
      filter_upwards [] with m
      simp [hi]
    · simp [hi]
  have hsum : Tendsto
      (fun m ↦ ∑ i : Fin Q.originalCutoff, if t ≤ (i : ℕ) then
        D.stageProfileBlockMass p m (D.windowPermutation Q i) else 0)
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum
      (Finset.univ : Finset (Fin Q.originalCutoff))
      (fun i _ ↦ hterm i)
  apply hsum.congr'
  filter_upwards [] with m
  let A := (FiniteProfileBlockLayout.ofPrefix
    (L (D.extraction m)) Q.originalCutoff).permute (D.windowPermutation Q)
  change (∑ i : Fin Q.originalCutoff, if t ≤ (i : ℕ) then
      D.stageProfileBlockMass p m (D.windowPermutation Q i) else 0) =
    graphonL1Dist (A.graphon p hp) (A.prefixGraphon p hp t)
  rw [A.graphonL1Dist_prefixGraphon_eq_sum_omittedBlockMass p hp t]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : t ≤ (i : ℕ)
  · simp only [hi, if_true]
    rfl
  · simp [hi]

/-- Taking the selected front of the permuted original-rank window gives
exactly the finite persistent-rank layout. -/
theorem windowTake_eq_selectedStageLayout
    {S₀ R₀ : ℕ} (Q : D.PersistentWindow S₀ R₀) (m : ℕ) :
    ((((FiniteProfileBlockLayout.ofPrefix
        (L (D.extraction m)) Q.originalCutoff).permute
          (D.windowPermutation Q)).take
        (D.persistentPrefixCount Q.finalCutoff)
        (D.persistentPrefixCount_le_originalCutoff Q))) =
      D.selectedStageLayout Q.finalCutoff m := by
  rw [FiniteProfileBlockLayout.mk.injEq]
  refine ⟨rfl, ?_, ?_⟩
  · apply heq_of_eq
    funext j
    change (L (D.extraction m)).alpha
      (D.windowPermutation Q
        (Fin.castLE (D.persistentPrefixCount_le_originalCutoff Q) j)) =
      (L (D.extraction m)).alpha (D.persistentRank j)
    rw [D.windowPermutation_front Q j]
  · apply heq_of_eq
    funext j
    change (L (D.extraction m)).core
      (D.windowPermutation Q
        (Fin.castLE (D.persistentPrefixCount_le_originalCutoff Q) j)) =
      (L (D.extraction m)).core (D.persistentRank j)
    rw [D.windowPermutation_front Q j]

/-- The selected persistent-rank layout represents the raw prefix of the
permuted finite original-rank window. -/
theorem windowPrefixGraphon_eq_selectedStageLayout_graphon
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    {S₀ R₀ : ℕ} (Q : D.PersistentWindow S₀ R₀) (m : ℕ) :
    (((FiniteProfileBlockLayout.ofPrefix
        (L (D.extraction m)) Q.originalCutoff).permute
          (D.windowPermutation Q)).prefixGraphon p hp
        (D.persistentPrefixCount Q.finalCutoff)) =
      (D.selectedStageLayout Q.finalCutoff m).graphon p hp := by
  let A := (FiniteProfileBlockLayout.ofPrefix
    (L (D.extraction m)) Q.originalCutoff).permute (D.windowPermutation Q)
  rw [A.prefixGraphon_eq_graphon_take p hp
      (D.persistentPrefixCount Q.finalCutoff)
      (D.persistentPrefixCount_le_originalCutoff Q),
    D.windowTake_eq_selectedStageLayout Q m]

/-- For a fixed persistent prefix, the finite fixed-core stage layouts
converge in `L¹` to the corresponding rankwise limiting layout. -/
theorem selectedFixedStageLayout_l1_tendsto_selectedLimitLayout
    (hk : 3 ≤ k) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (S : ℕ) :
    Tendsto
      (fun m ↦ graphonL1Dist
        ((D.selectedFixedStageLayout hk S m).graphon p hp)
        ((D.selectedLimitLayout hk S).graphon p hp))
      atTop (nhds 0) := by
  let a : ℕ → FiniteProfileBlockLengths (D.persistentPrefixCount S) :=
    fun m ↦ {
      alpha := fun j ↦ (L (D.extraction m)).alpha (D.persistentRank j)
      alpha_nonneg := fun j ↦
        (L (D.extraction m)).alpha_nonneg (D.persistentRank j)
      sum_alpha_le_one := (D.selectedStageLayout S m).sum_alpha_le_one
    }
  let b : FiniteProfileBlockLengths (D.persistentPrefixCount S) := {
    alpha := fun j ↦ D.alphaLimit (D.persistentRank j)
    alpha_nonneg := fun j ↦ D.alphaLimit_nonneg _
    sum_alpha_le_one := (D.selectedLimitLayout hk S).sum_alpha_le_one
  }
  let C : Fin (D.persistentPrefixCount S) → RegularBlockCore k :=
    fun j ↦ D.persistentCore hk j
  have hα (j : Fin (D.persistentPrefixCount S)) :
      Tendsto (fun m ↦ (a m).alpha j) atTop (nhds (b.alpha j)) := by
    simpa [a, b] using D.alpha_tendsto (D.persistentRank j)
  simpa [a, b, C, FiniteProfileBlockLengths.layout,
      selectedFixedStageLayout, selectedLimitLayout] using
    (FiniteProfileBlockLayout.graphonL1Dist_fixedCoreLayouts_tendsto_zero
      p hp a b C hα)

/-- The actual selected stage layouts have the same `L¹` limit, since
their persistent core labels are eventually literally constant. -/
theorem selectedStageLayout_l1_tendsto_selectedLimitLayout
    (hk : 3 ≤ k) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (S : ℕ) :
    Tendsto
      (fun m ↦ graphonL1Dist
        ((D.selectedStageLayout S m).graphon p hp)
        ((D.selectedLimitLayout hk S).graphon p hp))
      atTop (nhds 0) := by
  apply (D.selectedFixedStageLayout_l1_tendsto_selectedLimitLayout
    hk hp S).congr'
  filter_upwards [D.selectedStageLayout_eventually_eq_fixed hk S] with m hm
  rw [hm]

/-- A stage profile graphon is close to the selected persistent window: the
only costs are the original-rank square tail and deletion of the permuted
diffuse suffix. -/
theorem cutDist_profileWLambda_selectedStageLayout_le
    (hk : 3 ≤ k) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    {S₀ R₀ : ℕ} (Q : D.PersistentWindow S₀ R₀) (m : ℕ) :
    cutDist
        (profileWLambda p (L (D.extraction m)) hp)
        ((D.selectedStageLayout Q.finalCutoff m).graphon p hp) ≤
      (L (D.extraction m)).alphaSquareTail Q.originalCutoff +
        graphonL1Dist
          (((FiniteProfileBlockLayout.ofPrefix
            (L (D.extraction m)) Q.originalCutoff).permute
              (D.windowPermutation Q)).graphon p hp)
          (((FiniteProfileBlockLayout.ofPrefix
            (L (D.extraction m)) Q.originalCutoff).permute
              (D.windowPermutation Q)).prefixGraphon p hp
                (D.persistentPrefixCount Q.finalCutoff)) := by
  rw [← D.windowPrefixGraphon_eq_selectedStageLayout_graphon hp Q m]
  let Lm := L (D.extraction m)
  let A := FiniteProfileBlockLayout.ofPrefix Lm Q.originalCutoff
  let B := A.permute (D.windowPermutation Q)
  have hpermBA : cutDist (B.graphon p hp) (A.graphon p hp) = 0 := by
    change cutDist
      ((A.permute (D.windowPermutation Q)).graphon p hp)
      (A.graphon p hp) = 0
    exact A.cutDist_graphon_permute_eq_zero p hp (D.windowPermutation Q)
  have hperm : cutDist (A.graphon p hp) (B.graphon p hp) = 0 := by
    rw [cutDist_comm]
    exact hpermBA
  calc
    cutDist (profileWLambda p Lm hp)
        (B.prefixGraphon p hp (D.persistentPrefixCount Q.finalCutoff)) ≤
        cutDist (profileWLambda p Lm hp) (A.graphon p hp) +
          cutDist (A.graphon p hp)
            (B.prefixGraphon p hp
              (D.persistentPrefixCount Q.finalCutoff)) :=
      cutDist_triangle _ _ _
    _ ≤ cutDist (profileWLambda p Lm hp) (A.graphon p hp) +
          (cutDist (A.graphon p hp) (B.graphon p hp) +
            cutDist (B.graphon p hp)
              (B.prefixGraphon p hp
                (D.persistentPrefixCount Q.finalCutoff))) := by
      gcongr
      exact cutDist_triangle _ _ _
    _ = cutDist (profileWLambda p Lm hp) (A.graphon p hp) +
          cutDist (B.graphon p hp)
            (B.prefixGraphon p hp
              (D.persistentPrefixCount Q.finalCutoff)) := by
      rw [hperm]
      ring
    _ ≤ Lm.alphaSquareTail Q.originalCutoff +
          graphonL1Dist (B.graphon p hp)
            (B.prefixGraphon p hp
              (D.persistentPrefixCount Q.finalCutoff)) := by
      gcongr
      · exact
          FiniteProfileBlockLayout.cutDist_profileWLambda_graphon_ofPrefix_le_alphaSquareTail
            hk p hp Lm Q.originalCutoff
      · exact cutDist_le_graphonL1Dist _ _

/-- The selected finite prefix of the limit differs from the full limiting
profile graphon by at most its square tail. -/
theorem cutDist_selectedLimitLayout_profileWLambda_le
    (hk : 3 ≤ k) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hnonempty : (Set.ofPred D.PersistentPositive).Nonempty) (S : ℕ) :
    cutDist
        ((D.selectedLimitLayout hk S).graphon p hp)
        (profileWLambda p (D.limitBlockSequence hk hnonempty) hp) ≤
      (D.limitBlockSequence hk hnonempty).alphaSquareTail
        (D.persistentPrefixCount S) := by
  rw [← D.ofPrefix_limitBlockSequence_eq_selectedLimitLayout hk hnonempty S,
    cutDist_comm]
  exact
    FiniteProfileBlockLayout.cutDist_profileWLambda_graphon_ofPrefix_le_alphaSquareTail
      hk p hp (D.limitBlockSequence hk hnonempty)
        (D.persistentPrefixCount S)

/-- Four-term cut-distance bound through a persistent window: the stage
tail, discarded diffuse suffix, moving finite persistent prefix, and final
tail. -/
theorem cutDist_profileWLambda_limitBlockSequence_le_window
    (hk : 3 ≤ k) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hnonempty : (Set.ofPred D.PersistentPositive).Nonempty)
    {S₀ R₀ : ℕ} (Q : D.PersistentWindow S₀ R₀) (m : ℕ) :
    cutDist
        (profileWLambda p (L (D.extraction m)) hp)
        (profileWLambda p (D.limitBlockSequence hk hnonempty) hp) ≤
      (L (D.extraction m)).alphaSquareTail Q.originalCutoff +
        graphonL1Dist
          (((FiniteProfileBlockLayout.ofPrefix
            (L (D.extraction m)) Q.originalCutoff).permute
              (D.windowPermutation Q)).graphon p hp)
          (((FiniteProfileBlockLayout.ofPrefix
            (L (D.extraction m)) Q.originalCutoff).permute
              (D.windowPermutation Q)).prefixGraphon p hp
                (D.persistentPrefixCount Q.finalCutoff)) +
        graphonL1Dist
          ((D.selectedStageLayout Q.finalCutoff m).graphon p hp)
          ((D.selectedLimitLayout hk Q.finalCutoff).graphon p hp) +
        (D.limitBlockSequence hk hnonempty).alphaSquareTail
          (D.persistentPrefixCount Q.finalCutoff) := by
  let W := profileWLambda p (L (D.extraction m)) hp
  let C := (D.selectedStageLayout Q.finalCutoff m).graphon p hp
  let F := (D.selectedLimitLayout hk Q.finalCutoff).graphon p hp
  let V := profileWLambda p (D.limitBlockSequence hk hnonempty) hp
  have hWC := D.cutDist_profileWLambda_selectedStageLayout_le hk hp Q m
  have hCF : cutDist C F ≤ graphonL1Dist C F :=
    cutDist_le_graphonL1Dist C F
  have hFV := D.cutDist_selectedLimitLayout_profileWLambda_le
    hk hp hnonempty Q.finalCutoff
  have hWV := cutDist_triangle W C V
  have hCV := cutDist_triangle C F V
  dsimp only [W, C, F, V] at hWC hCF hFV hWV hCV ⊢
  linarith

/-- Along the diagonal extraction, the profile graphons converge in cut
distance to the profile graphon of the persistent limiting sequence. -/
theorem profileWLambda_tendsto_limitBlockSequence
    (hk : 3 ≤ k) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hnonempty : (Set.ofPred D.PersistentPositive).Nonempty) :
    Tendsto
      (fun m ↦ cutDist
        (profileWLambda p (L (D.extraction m)) hp)
        (profileWLambda p (D.limitBlockSequence hk hnonempty) hp))
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hinv : Tendsto (fun N : ℕ ↦ 1 / ((N + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hfour : Tendsto
      (fun N : ℕ ↦ 4 * (1 / ((N + 1 : ℕ) : ℝ)))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hinv : Tendsto
      (fun N : ℕ ↦ (4 : ℝ) * (1 / ((N + 1 : ℕ) : ℝ)))
      atTop (nhds ((4 : ℝ) * 0)))
  rw [Metric.tendsto_atTop] at hfour
  obtain ⟨N, hN⟩ := hfour ε hε
  have hNsmall : 4 * (1 / ((N + 1 : ℕ) : ℝ)) < ε := by
    have h := hN N le_rfl
    have hnonneg : 0 ≤ 4 * (1 / ((N + 1 : ℕ) : ℝ)) := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at h
    exact h
  let Q := Classical.choice (D.exists_persistentWindow hnonempty N N)
  have hQfinal : N ≤ Q.finalCutoff := Q.finalCutoff_large
  have hQoriginal : N ≤ Q.originalCutoff := Q.originalCutoff_large
  have hfinalInv :
      1 / ((Q.finalCutoff + 1 : ℕ) : ℝ) ≤
        1 / ((N + 1 : ℕ) : ℝ) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hQfinal 1
  have horiginalInv :
      1 / ((Q.originalCutoff + 1 : ℕ) : ℝ) ≤
        1 / ((N + 1 : ℕ) : ℝ) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hQoriginal 1
  have hvariable : Tendsto
      (fun m ↦
        graphonL1Dist
          (((FiniteProfileBlockLayout.ofPrefix
            (L (D.extraction m)) Q.originalCutoff).permute
              (D.windowPermutation Q)).graphon p hp)
          (((FiniteProfileBlockLayout.ofPrefix
            (L (D.extraction m)) Q.originalCutoff).permute
              (D.windowPermutation Q)).prefixGraphon p hp
                (D.persistentPrefixCount Q.finalCutoff)) +
        graphonL1Dist
          ((D.selectedStageLayout Q.finalCutoff m).graphon p hp)
          ((D.selectedLimitLayout hk Q.finalCutoff).graphon p hp))
      atTop (nhds 0) := by
    simpa using (D.windowSuffix_l1_tendsto_zero hk hp Q).add
      (D.selectedStageLayout_l1_tendsto_selectedLimitLayout
        hk hp Q.finalCutoff)
  rw [Metric.tendsto_atTop] at hvariable
  obtain ⟨m₀, hm₀⟩ := hvariable (ε / 2) (half_pos hε)
  refine ⟨m₀, fun m hm ↦ ?_⟩
  have hvar := hm₀ m hm
  have hvarNonneg : 0 ≤
      graphonL1Dist
          (((FiniteProfileBlockLayout.ofPrefix
            (L (D.extraction m)) Q.originalCutoff).permute
              (D.windowPermutation Q)).graphon p hp)
          (((FiniteProfileBlockLayout.ofPrefix
            (L (D.extraction m)) Q.originalCutoff).permute
              (D.windowPermutation Q)).prefixGraphon p hp
                (D.persistentPrefixCount Q.finalCutoff)) +
        graphonL1Dist
          ((D.selectedStageLayout Q.finalCutoff m).graphon p hp)
          ((D.selectedLimitLayout hk Q.finalCutoff).graphon p hp) :=
    add_nonneg (graphonL1Dist_nonneg _ _) (graphonL1Dist_nonneg _ _)
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg hvarNonneg] at hvar
  have hstageTail :=
    (L (D.extraction m)).alphaSquareTail_le_inv_succ Q.originalCutoff
  have hfinalTail :=
    D.limitBlockSequence_alphaSquareTail_le_window hk hnonempty Q
  have htotal :=
    D.cutDist_profileWLambda_limitBlockSequence_le_window
      hk hp hnonempty Q m
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (cutDist_nonneg _ _)]
  linarith

/-- Finite heads of the stage mass series converge termwise. -/
theorem massHead_tendsto (hk : 3 ≤ k) (N : ℕ) :
    Tendsto
      (fun m ↦ ∑ i ∈ Finset.range N, (L (D.extraction m)).massTerm i)
      atTop (nhds (∑ i ∈ Finset.range N, D.rankMassLimit i)) := by
  exact tendsto_finsetSum (Finset.range N) fun i _ ↦
    D.massTerm_tendsto_rankMassLimit hk i

theorem alphaLimit_le_inv_succ (i : ℕ) :
    D.alphaLimit i ≤ 1 / ((i + 1 : ℕ) : ℝ) := by
  have hsum : ((i + 1 : ℕ) : ℝ) * D.alphaLimit i ≤ 1 := by
    calc
      ((i + 1 : ℕ) : ℝ) * D.alphaLimit i =
          ∑ j ∈ Finset.range (i + 1), D.alphaLimit i := by simp
      _ ≤ ∑ j ∈ Finset.range (i + 1), D.alphaLimit j := by
        apply Finset.sum_le_sum
        intro j hj
        exact D.alphaLimit_antitone
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      _ ≤ 1 := D.sum_range_alphaLimit_le_one (i + 1)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((i + 1 : ℕ) : ℝ))).2
  simpa [mul_comm] using hsum

/-- Square tail of the rankwise limiting length data. -/
def alphaLimitSquareTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, D.alphaLimit (N + j) ^ 2

/-- Tail of the rankwise limiting mass data. -/
def rankMassTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, D.rankMassLimit (N + j)

theorem summable_alphaLimit_sq_shift (N : ℕ) :
    Summable (fun j : ℕ ↦ D.alphaLimit (N + j) ^ 2) := by
  have hsquare : Summable (fun i ↦ D.alphaLimit i ^ 2) := by
    apply Summable.of_nonneg_of_le (fun i ↦ sq_nonneg _)
      (fun i ↦ by nlinarith [D.alphaLimit_nonneg i, D.alphaLimit_le_one i])
      D.summable_alphaLimit
  exact hsquare.comp_injective (fun _ _ h ↦ Nat.add_left_cancel h)

theorem alphaLimitSquareTail_le_inv_succ (N : ℕ) :
    D.alphaLimitSquareTail N ≤ 1 / ((N + 1 : ℕ) : ℝ) := by
  have hshift : Summable (fun j : ℕ ↦ D.alphaLimit (N + j)) :=
    D.summable_alphaLimit.comp_injective
      (fun _ _ h ↦ Nat.add_left_cancel h)
  have hpoint (j : ℕ) :
      D.alphaLimit (N + j) ^ 2 ≤
        D.alphaLimit N * D.alphaLimit (N + j) := by
    have hmono := D.alphaLimit_antitone (Nat.le_add_right N j)
    nlinarith [D.alphaLimit_nonneg (N + j)]
  calc
    D.alphaLimitSquareTail N ≤
        ∑' j : ℕ, D.alphaLimit N * D.alphaLimit (N + j) := by
      exact Summable.tsum_le_tsum hpoint (D.summable_alphaLimit_sq_shift N)
        (hshift.mul_left _)
    _ = D.alphaLimit N * ∑' j : ℕ, D.alphaLimit (N + j) := by
      rw [hshift.tsum_mul_left]
    _ ≤ D.alphaLimit N * 1 := by
      apply mul_le_mul_of_nonneg_left _ (D.alphaLimit_nonneg N)
      exact (hshift.tsum_le_tsum_of_inj (fun j ↦ N + j)
        (fun _ _ h ↦ Nat.add_left_cancel h)
        (fun i _ ↦ D.alphaLimit_nonneg i) (fun _ ↦ le_rfl)
        D.summable_alphaLimit).trans D.tsum_alphaLimit_le_one
    _ = D.alphaLimit N := mul_one _
    _ ≤ _ := D.alphaLimit_le_inv_succ N

theorem rankMassTail_nonneg (N : ℕ) : 0 ≤ D.rankMassTail N :=
  tsum_nonneg fun _ ↦ D.rankMassLimit_nonneg _

theorem rankMassTail_le_inv (hk : 3 ≤ k) (N : ℕ) :
    D.rankMassTail N ≤
      (1 / ((k - 1 : ℕ) : ℝ)) *
        (1 / ((N + 1 : ℕ) : ℝ)) := by
  have hmassShift : Summable (fun j : ℕ ↦ D.rankMassLimit (N + j)) :=
    (D.summable_rankMassLimit hk).comp_injective
      (fun _ _ h ↦ Nat.add_left_cancel h)
  calc
    D.rankMassTail N ≤
        ∑' j : ℕ, (1 / ((k - 1 : ℕ) : ℝ)) *
          D.alphaLimit (N + j) ^ 2 := by
      exact Summable.tsum_le_tsum (fun j ↦ D.rankMassLimit_le hk (N + j))
        hmassShift ((D.summable_alphaLimit_sq_shift N).mul_left _)
    _ = (1 / ((k - 1 : ℕ) : ℝ)) * D.alphaLimitSquareTail N := by
      rw [(D.summable_alphaLimit_sq_shift N).tsum_mul_left]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (D.alphaLimitSquareTail_le_inv_succ N) (by positivity)

theorem mass_eq_head_add_tail (A : AdmissibleBlockSequence k) (N : ℕ) :
    A.mass =
      (∑ i ∈ Finset.range N, A.massTerm i) + A.massTail N := by
  rw [AdmissibleBlockSequence.mass, AdmissibleBlockSequence.massTail]
  simpa [Nat.add_comm] using
    (A.summable_massTerm.sum_add_tsum_nat_add N).symm

theorem rankMass_eq_head_add_tail (hk : 3 ≤ k) (N : ℕ) :
    ∑' i, D.rankMassLimit i =
      (∑ i ∈ Finset.range N, D.rankMassLimit i) + D.rankMassTail N := by
  rw [rankMassTail]
  simpa [Nat.add_comm] using
    ((D.summable_rankMassLimit hk).sum_add_tsum_nat_add N).symm

theorem abs_mass_sub_rankMass_le (hk : 3 ≤ k) (N m : ℕ) :
    |(L (D.extraction m)).mass - ∑' i, D.rankMassLimit i| ≤
      (L (D.extraction m)).massTail N +
        |∑ i ∈ Finset.range N, (L (D.extraction m)).massTerm i -
          ∑ i ∈ Finset.range N, D.rankMassLimit i| +
        D.rankMassTail N := by
  let headStage := ∑ i ∈ Finset.range N,
    (L (D.extraction m)).massTerm i
  let headLimit := ∑ i ∈ Finset.range N, D.rankMassLimit i
  let tailStage := (L (D.extraction m)).massTail N
  let tailLimit := D.rankMassTail N
  have hstage : (L (D.extraction m)).mass = headStage + tailStage :=
    mass_eq_head_add_tail (L (D.extraction m)) N
  have hlimit : ∑' i, D.rankMassLimit i = headLimit + tailLimit :=
    D.rankMass_eq_head_add_tail hk N
  have htail : |tailStage - tailLimit| ≤ tailStage + tailLimit := by
    rw [abs_le]
    constructor <;> linarith [
      (L (D.extraction m)).massTail_nonneg N,
      D.rankMassTail_nonneg N]
  rw [hstage, hlimit]
  calc
    |headStage + tailStage - (headLimit + tailLimit)| =
        |(headStage - headLimit) + (tailStage - tailLimit)| := by ring_nf
    _ ≤ |headStage - headLimit| + |tailStage - tailLimit| := abs_add_le _ _
    _ ≤ tailStage + |headStage - headLimit| + tailLimit := by linarith

/-- The entire normalized mass series converges to the sum of the rankwise
limits; the proof uses the explicit uniform `1/(N+1)` tail bound. -/
theorem mass_tendsto_rankMass (hk : 3 ≤ k) :
    Tendsto (fun m ↦ (L (D.extraction m)).mass) atTop
      (nhds (∑' i, D.rankMassLimit i)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let tailBound : ℕ → ℝ := fun N ↦
    (1 / ((k - 1 : ℕ) : ℝ)) * (1 / ((N + 1 : ℕ) : ℝ))
  have hinv : Tendsto (fun N : ℕ ↦ 1 / ((N + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have htailBound : Tendsto (fun N ↦ 2 * tailBound N) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦
        2 * (1 / ((k - 1 : ℕ) : ℝ))) atTop
        (nhds (2 * (1 / ((k - 1 : ℕ) : ℝ)))) := tendsto_const_nhds
    simpa [tailBound, mul_assoc] using hconst.mul hinv
  rw [Metric.tendsto_atTop] at htailBound
  obtain ⟨N, hN⟩ := htailBound (ε / 2) (half_pos hε)
  have hNsmall : 2 * tailBound N < ε / 2 := by
    have := hN N le_rfl
    have htb : 0 ≤ tailBound N := by
      dsimp [tailBound]
      positivity
    simpa [Real.dist_eq, abs_of_nonneg htb,
      abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) htb)] using this
  have hhead : Tendsto
      (fun m ↦
        |∑ i ∈ Finset.range N, (L (D.extraction m)).massTerm i -
          ∑ i ∈ Finset.range N, D.rankMassLimit i|)
      atTop (nhds 0) := by
    have hconst : Tendsto
        (fun _ : ℕ ↦ ∑ i ∈ Finset.range N, D.rankMassLimit i) atTop
        (nhds (∑ i ∈ Finset.range N, D.rankMassLimit i)) :=
      tendsto_const_nhds
    have hsub := (D.massHead_tendsto hk N).sub hconst
    simpa only [Real.norm_eq_abs, sub_self, abs_zero] using hsub.norm
  rw [Metric.tendsto_atTop] at hhead
  obtain ⟨m₀, hm₀⟩ := hhead (ε / 2) (half_pos hε)
  refine ⟨m₀, fun m hm ↦ ?_⟩
  have hheadSmall := hm₀ m hm
  simp only [Real.dist_eq, sub_zero, abs_abs] at hheadSmall
  have hstageTail :=
    (L (D.extraction m)).massTail_le_inv_k_sub_one_mul_inv_succ hk N
  have hlimitTail := D.rankMassTail_le_inv hk N
  have htotal := D.abs_mass_sub_rankMass_le hk N m
  rw [Real.dist_eq]
  have htwo :
      (L (D.extraction m)).massTail N + D.rankMassTail N ≤
        2 * tailBound N := by
    dsimp [tailBound]
    linarith
  linarith

theorem rankMassLimit_eq_zero_of_not_persistentPositive {i : ℕ}
    (hi : ¬ D.PersistentPositive i) : D.rankMassLimit i = 0 := by
  cases hcore : D.coreLimit i with
  | diffuse => simp [rankMassLimit, hcore]
  | persistent core =>
      have hnotpos : ¬ 0 < D.alphaLimit i := by
        intro hpos
        exact hi ⟨hpos, core, hcore⟩
      have halpha : D.alphaLimit i = 0 :=
        le_antisymm (not_lt.mp hnotpos) (D.alphaLimit_nonneg i)
      simp [rankMassLimit, hcore, halpha]

theorem persistentRank_injectiveOn_active :
    Set.InjOn D.persistentRank
      (Set.ofPred fun j ↦ blockIndexActive D.persistentCount j) := by
  intro i hi j hj hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (D.persistentRank_strictMono_of_lt_of_active hlt hj).ne hij
  · exact (D.persistentRank_strictMono_of_lt_of_active hgt hi).ne hij.symm

/-- Order-preserving enumeration as an equivalence between active final
indices and persistent-positive original ranks. -/
noncomputable def persistentRankEquiv :
    (Set.ofPred fun j ↦ blockIndexActive D.persistentCount j) ≃
      Set.ofPred D.PersistentPositive where
  toFun j := ⟨D.persistentRank j, D.persistentRank_mem_of_active j.property⟩
  invFun i := ⟨Classical.choose (D.exists_active_persistentRank_eq i.property),
    (Classical.choose_spec (D.exists_active_persistentRank_eq i.property)).1⟩
  left_inv j := by
    apply Subtype.ext
    apply D.persistentRank_injectiveOn_active
    · exact (Classical.choose_spec
        (D.exists_active_persistentRank_eq
          (D.persistentRank_mem_of_active j.property))).1
    · exact j.property
    · exact (Classical.choose_spec
        (D.exists_active_persistentRank_eq
          (D.persistentRank_mem_of_active j.property))).2
  right_inv i := by
    apply Subtype.ext
    exact (Classical.choose_spec
      (D.exists_active_persistentRank_eq i.property)).2

/-- Exact identification of the compressed limit sequence's mass with the
sum of the original-rank persistent contributions. -/
theorem limitBlockSequence_mass_eq_rankMass (hk : 3 ≤ k)
    (hnonempty : (Set.ofPred D.PersistentPositive).Nonempty) :
    (D.limitBlockSequence hk hnonempty).mass =
      ∑' i, D.rankMassLimit i := by
  let active : Set ℕ :=
    Set.ofPred fun j ↦ blockIndexActive D.persistentCount j
  let persistent : Set ℕ := Set.ofPred D.PersistentPositive
  let Linf := D.limitBlockSequence hk hnonempty
  have hinactive (j : ℕ) (hj : j ∉ active) : Linf.massTerm j = 0 := by
    have hj' : ¬ blockIndexActive D.persistentCount j := hj
    unfold AdmissibleBlockSequence.massTerm Linf
    change
      (if blockIndexActive D.persistentCount j then
        D.alphaLimit (D.persistentRank j) else 0) ^ 2 /
          (D.persistentCore hk j).order = 0
    simp [hj']
  have horiginal (i : ℕ) (hi : i ∉ persistent) :
      D.rankMassLimit i = 0 :=
    D.rankMassLimit_eq_zero_of_not_persistentPositive hi
  calc
    Linf.mass = ∑' j, Linf.massTerm j := rfl
    _ = ∑' j : active, Linf.massTerm j := by
      rw [tsum_subtype]
      apply tsum_congr
      intro j
      by_cases hj : j ∈ active
      · simp [Set.indicator_of_mem hj]
      · simp [Set.indicator_of_notMem hj, hinactive j hj]
    _ = ∑' i : persistent, D.rankMassLimit i := by
      rw [← (D.persistentRankEquiv).tsum_eq
        (fun i : persistent ↦ D.rankMassLimit i)]
      apply tsum_congr
      intro j
      have hj : blockIndexActive D.persistentCount j := j.property
      have hcore := D.coreLimit_persistentCore_of_active hk hj
      change Linf.massTerm j = D.rankMassLimit (D.persistentRank j)
      rw [show Linf.massTerm j =
          D.alphaLimit (D.persistentRank j) ^ 2 /
            (D.persistentCore hk j).order by
        change (D.limitBlockSequence hk hnonempty).massTerm j = _
        unfold AdmissibleBlockSequence.massTerm
        rw [D.limitBlockSequence_alpha_of_active hk hnonempty hj,
          D.limitBlockSequence_core_of_active hk hnonempty hj]]
      simp [rankMassLimit, hcore]
    _ = ∑' i, D.rankMassLimit i := by
      rw [tsum_subtype]
      apply tsum_congr
      intro i
      by_cases hi : i ∈ persistent
      · simp [Set.indicator_of_mem hi]
      · simp [Set.indicator_of_notMem hi, horiginal i hi]

/-- If the original block masses converge, their limit is the sum of the
rankwise persistent contributions selected by the diagonal extraction. -/
theorem rankMass_eq_of_mass_tendsto (hk : 3 ≤ k) {M : ℝ}
    (hmass : Tendsto (fun m ↦ (L m).mass) atTop (nhds M)) :
    ∑' i, D.rankMassLimit i = M := by
  exact tendsto_nhds_unique (D.mass_tendsto_rankMass hk)
    (hmass.comp D.extraction_strictMono.tendsto_atTop)

/-- A positive limiting mass forces at least one rank to have both positive
limiting length and a persistent finite core. -/
theorem persistentPositive_nonempty_of_mass_tendsto (hk : 3 ≤ k)
    {M : ℝ} (hM : 0 < M)
    (hmass : Tendsto (fun m ↦ (L m).mass) atTop (nhds M)) :
    (Set.ofPred D.PersistentPositive).Nonempty := by
  by_contra hnone
  have hzero (i : ℕ) : D.rankMassLimit i = 0 := by
    apply D.rankMassLimit_eq_zero_of_not_persistentPositive
    intro hi
    exact hnone ⟨i, hi⟩
  have htsum : ∑' i, D.rankMassLimit i = 0 := by
    calc
      ∑' i, D.rankMassLimit i = ∑' _i : ℕ, (0 : ℝ) :=
        tsum_congr hzero
      _ = 0 := tsum_zero
  have heq := D.rankMass_eq_of_mass_tendsto hk hmass
  rw [htsum] at heq
  linarith

/-- Exact mass of the admissible limit sequence produced by the diagonal
compactness construction. -/
theorem limitBlockSequence_mass_eq_of_tendsto (hk : 3 ≤ k)
    {M : ℝ} (hM : 0 < M)
    (hmass : Tendsto (fun m ↦ (L m).mass) atTop (nhds M)) :
    (D.limitBlockSequence hk
      (D.persistentPositive_nonempty_of_mass_tendsto hk hM hmass)).mass = M := by
  rw [D.limitBlockSequence_mass_eq_rankMass hk,
    D.rankMass_eq_of_mass_tendsto hk hmass]

end OrderedBlockLimitData

end Graphon

/-- A positive-mass sequence of admissible profile-block graphons has a
subsequence converging in cut distance to another admissible profile-block
graphon, with the limiting block sequence carrying exactly the limiting
normalized mass. -/
theorem exists_positiveMass_profileBlock_limit
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (L : ℕ → AdmissibleBlockSequence k)
    (M : ℝ) (hM : 0 < M)
    (hmass : Tendsto (fun m ↦ (L m).mass) atTop (nhds M)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ Llim : AdmissibleBlockSequence k,
        Llim.mass = M ∧
        Tendsto
          (fun m ↦ cutDist
            (profileWLambda p (L (σ m)) ⟨hp.1.le, hp.2.le⟩)
            (profileWLambda p Llim ⟨hp.1.le, hp.2.le⟩))
          atTop (nhds 0) := by
  let D : Graphon.OrderedBlockLimitData L :=
    Classical.choice (Graphon.exists_orderedBlockLimitData L)
  let hnonempty : (Set.ofPred D.PersistentPositive).Nonempty :=
    D.persistentPositive_nonempty_of_mass_tendsto hk hM hmass
  refine ⟨D.extraction, D.extraction_strictMono, ?_⟩
  refine ⟨D.limitBlockSequence hk hnonempty, ?_, ?_⟩
  · exact D.limitBlockSequence_mass_eq_of_tendsto hk hM hmass
  · exact D.profileWLambda_tendsto_limitBlockSequence
      hk ⟨hp.1.le, hp.2.le⟩ hnonempty

end InducedStars
