import InducedStars.Regularity.WeightedCut

/-!
# Finite cut bookkeeping for regular partitions

This file isolates the finite rectangle estimate used when a regular
partition is aligned with an equal-cell graphon partition.
-/

open Finset
open scoped BigOperators SimpleGraph

namespace InducedStars.Regularity

noncomputable section

/-- The vertex slice of a set of `(vertex, copy)` pairs at a fixed copy. -/
def copySlice {n k : ℕ} (S : Finset (Fin n × Fin k)) (b : Fin k) : Finset (Fin n) :=
  Finset.univ.filter fun v ↦ (v, b) ∈ S

@[simp] theorem mem_copySlice {n k : ℕ} (S : Finset (Fin n × Fin k))
    (b : Fin k) (v : Fin n) :
    v ∈ copySlice S b ↔ (v, b) ∈ S := by
  simp [copySlice]

/-- Regroup a sum over two arbitrary copy-sets by their copy coordinates. -/
theorem sum_copyPairs_eq_sum_slices {n k : ℕ}
    (S T : Finset (Fin n × Fin k)) (f : Fin n → Fin n → ℝ) :
    ∑ p ∈ S, ∑ q ∈ T, f p.1 q.1 =
      ∑ b : Fin k, ∑ c : Fin k,
        ∑ v ∈ copySlice S b, ∑ w ∈ copySlice T c, f v w := by
  have hS (g : Fin n → ℝ) :
      ∑ p ∈ S, g p.1 = ∑ b : Fin k, ∑ v ∈ copySlice S b, g v := by
    simpa using
      (Finset.sum_finset_product_right S (Finset.univ : Finset (Fin k))
        (copySlice S) (by intro p; simp) (f := fun p ↦ g p.1))
  have hT (v : Fin n) :
      ∑ q ∈ T, f v q.1 =
        ∑ c : Fin k, ∑ w ∈ copySlice T c, f v w := by
    simpa using
      (Finset.sum_finset_product_right T (Finset.univ : Finset (Fin k))
        (copySlice T) (by intro p; simp) (f := fun p ↦ f v p.1))
  calc
    (∑ p ∈ S, ∑ q ∈ T, f p.1 q.1) =
        ∑ b : Fin k, ∑ v ∈ copySlice S b, ∑ q ∈ T, f v q.1 :=
      hS (fun v ↦ ∑ q ∈ T, f v q.1)
    _ = ∑ b : Fin k, ∑ v ∈ copySlice S b,
        ∑ c : Fin k, ∑ w ∈ copySlice T c, f v w := by
      simp_rw [hT]
    _ = ∑ b : Fin k, ∑ c : Fin k,
        ∑ v ∈ copySlice S b, ∑ w ∈ copySlice T c, f v w := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm

/-- A rectangle estimate on every copy-coordinate slice loses only the
expected factor `k²`. -/
theorem abs_sum_copyPairs_le {n k : ℕ}
    (S T : Finset (Fin n × Fin k)) (f : Fin n → Fin n → ℝ)
    {E : ℝ} (hE : 0 ≤ E)
    (hslice : ∀ b c,
      |∑ v ∈ copySlice S b, ∑ w ∈ copySlice T c, f v w| ≤ E) :
    |∑ p ∈ S, ∑ q ∈ T, f p.1 q.1| ≤ (k : ℝ) ^ 2 * E := by
  rw [sum_copyPairs_eq_sum_slices]
  calc
    |∑ b : Fin k, ∑ c : Fin k,
        ∑ v ∈ copySlice S b, ∑ w ∈ copySlice T c, f v w| ≤
        ∑ b : Fin k, |∑ c : Fin k,
          ∑ v ∈ copySlice S b, ∑ w ∈ copySlice T c, f v w| := by
      exact Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ b : Fin k, ∑ c : Fin k,
        |∑ v ∈ copySlice S b, ∑ w ∈ copySlice T c, f v w| := by
      apply Finset.sum_le_sum
      intro b hb
      exact Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ _b : Fin k, ∑ _c : Fin k, E := by
      gcongr with b c
      exact hslice b c
    _ = (k : ℝ) ^ 2 * E := by
      simp
      ring

/-- Copy-coordinate slicing when the summand itself depends on both copy
coordinates. -/
theorem sum_copyPairs_dep_eq_sum_slices {n k : ℕ}
    (S T : Finset (Fin n × Fin k))
    (F : (Fin n × Fin k) → (Fin n × Fin k) → ℝ) :
    ∑ p ∈ S, ∑ q ∈ T, F p q =
      ∑ b : Fin k, ∑ c : Fin k,
        ∑ v ∈ copySlice S b, ∑ w ∈ copySlice T c, F (v, b) (w, c) := by
  have hS (g : Fin n × Fin k → ℝ) :
      ∑ p ∈ S, g p = ∑ b : Fin k, ∑ v ∈ copySlice S b, g (v, b) := by
    simpa using
      (Finset.sum_finset_product_right S (Finset.univ : Finset (Fin k))
        (copySlice S) (by intro p; simp) (f := g))
  have hT (p : Fin n × Fin k) :
      ∑ q ∈ T, F p q =
        ∑ c : Fin k, ∑ w ∈ copySlice T c, F p (w, c) := by
    simpa using
      (Finset.sum_finset_product_right T (Finset.univ : Finset (Fin k))
        (copySlice T) (by intro q; simp) (f := fun q ↦ F p q))
  calc
    (∑ p ∈ S, ∑ q ∈ T, F p q) =
        ∑ b : Fin k, ∑ v ∈ copySlice S b, ∑ q ∈ T, F (v, b) q :=
      hS (fun p ↦ ∑ q ∈ T, F p q)
    _ = ∑ b : Fin k, ∑ v ∈ copySlice S b,
        ∑ c : Fin k, ∑ w ∈ copySlice T c, F (v, b) (w, c) := by
      simp_rw [hT]
    _ = ∑ b : Fin k, ∑ c : Fin k,
        ∑ v ∈ copySlice S b, ∑ w ∈ copySlice T c, F (v, b) (w, c) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm

/-- A uniform bound on all copy-coordinate slices gives the expected `k²`
bound for a copy-dependent summand. -/
theorem abs_sum_copyPairs_dep_le {n k : ℕ}
    (S T : Finset (Fin n × Fin k))
    (F : (Fin n × Fin k) → (Fin n × Fin k) → ℝ)
    {E : ℝ}
    (hslice : ∀ b c,
      |∑ v ∈ copySlice S b, ∑ w ∈ copySlice T c, F (v, b) (w, c)| ≤ E) :
    |∑ p ∈ S, ∑ q ∈ T, F p q| ≤ (k : ℝ) ^ 2 * E := by
  rw [sum_copyPairs_dep_eq_sum_slices]
  calc
    |∑ b : Fin k, ∑ c : Fin k,
        ∑ v ∈ copySlice S b, ∑ w ∈ copySlice T c, F (v, b) (w, c)| ≤
        ∑ b : Fin k, |∑ c : Fin k,
          ∑ v ∈ copySlice S b, ∑ w ∈ copySlice T c, F (v, b) (w, c)| := by
      exact Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ b : Fin k, ∑ c : Fin k,
        |∑ v ∈ copySlice S b, ∑ w ∈ copySlice T c, F (v, b) (w, c)| := by
      apply Finset.sum_le_sum
      intro b hb
      exact Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ _b : Fin k, ∑ _c : Fin k, E := by
      gcongr with b c
      exact hslice b c
    _ = (k : ℝ) ^ 2 * E := by
      simp
      ring

/-- The regular-pair rectangle estimate after taking `k` copies of each
vertex, with an arbitrary subset of those copies on either side. -/
theorem IsRegularPair.abs_sum_centered_adjIndicator_copies_le
    {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {epsilon : ℝ} {A B : Finset (Fin n)}
    (hreg : IsRegularPair G epsilon A B) (hε : 0 ≤ epsilon)
    (S T : Finset (Fin n × Fin k))
    (hS : ∀ p ∈ S, p.1 ∈ A) (hT : ∀ p ∈ T, p.1 ∈ B) :
    |∑ p ∈ S, ∑ q ∈ T,
        ((if G.Adj p.1 q.1 then (1 : ℝ) else 0) - graphDensity G A B)| ≤
      (k : ℝ) ^ 2 * (epsilon * (A.card : ℝ) * (B.card : ℝ)) := by
  apply abs_sum_copyPairs_le S T
    (fun v w ↦ (if G.Adj v w then (1 : ℝ) else 0) - graphDensity G A B)
  · positivity
  · intro b c
    apply hreg.abs_sum_centered_adjIndicator_le G hε
    · intro v hv
      exact hS (v, b) ((mem_copySlice S b v).mp hv)
    · intro v hv
      exact hT (v, c) ((mem_copySlice T c v).mp hv)

/-! ## Partition bookkeeping -/

/-- The exceptional part of a vertex set. -/
def exceptionalPart {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {epsilon : ℝ}
    (P : RegularPartition G epsilon) (s : Finset (Fin n)) : Finset (Fin n) :=
  s.filter fun v ↦ v ∈ P.exceptional

/-- The nonexceptional part of a vertex set. -/
def nonexceptionalPart {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {epsilon : ℝ}
    (P : RegularPartition G epsilon) (s : Finset (Fin n)) : Finset (Fin n) :=
  s.filter fun v ↦ v ∉ P.exceptional

theorem sum_eq_exceptionalPart_add_nonexceptionalPart
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {epsilon : ℝ}
    (P : RegularPartition G epsilon) (s : Finset (Fin n)) (f : Fin n → ℝ) :
    ∑ v ∈ s, f v =
      ∑ v ∈ exceptionalPart P s, f v + ∑ v ∈ nonexceptionalPart P s, f v := by
  simpa [exceptionalPart, nonexceptionalPart] using
    (Finset.sum_filter_add_sum_filter_not s (fun v ↦ v ∈ P.exceptional) f).symm

/-- The part of `s` lying in a specified nonexceptional cluster. -/
def clusterPart {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {epsilon : ℝ}
    (P : RegularPartition G epsilon) (s : Finset (Fin n))
    (i : Fin P.clusterCount) : Finset (Fin n) :=
  s ∩ P.clusters i

theorem sum_nonexceptionalPart_eq_sum_clusterPart
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {epsilon : ℝ}
    (P : RegularPartition G epsilon) (s : Finset (Fin n)) (f : Fin n → ℝ) :
    ∑ v ∈ nonexceptionalPart P s, f v =
      ∑ i : Fin P.clusterCount, ∑ v ∈ clusterPart P s i, f v := by
  classical
  let U := Finset.univ.biUnion P.clusters
  have hdisj : (↑(Finset.univ : Finset (Fin P.clusterCount)) :
      Set (Fin P.clusterCount)).PairwiseDisjoint (fun i ↦ clusterPart P s i) := by
    intro i hi j hj hij
    exact (P.clusters_disjoint hij).mono inter_subset_right inter_subset_right
  have hUnion : Finset.univ.biUnion (fun i ↦ clusterPart P s i) =
      nonexceptionalPart P s := by
    ext v
    have hcover : v ∈ P.exceptional ∪ U := by
      rw [show P.exceptional ∪ U = Finset.univ by exact P.cover]
      simp
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, clusterPart,
      Finset.mem_inter, nonexceptionalPart, Finset.mem_filter]
    constructor
    · rintro ⟨i, hvs, hvi⟩
      refine ⟨hvs, ?_⟩
      intro hvE
      exact (Finset.disjoint_left.mp (P.exceptional_disjoint i)) hvE hvi
    · rintro ⟨hvs, hvE⟩
      have hvU : v ∈ U := (Finset.mem_union.mp hcover).resolve_left hvE
      obtain ⟨i, -, hvi⟩ := Finset.mem_biUnion.mp hvU
      exact ⟨i, hvs, hvi⟩
  rw [← hUnion, Finset.sum_biUnion hdisj]

/-- Any centered adjacency rectangle has the trivial unit-per-entry bound. -/
theorem abs_centered_sum_le_card
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s t : Finset (Fin n)) (d : Fin n → Fin n → ℝ)
    (hd₀ : ∀ v w, 0 ≤ d v w) (hd₁ : ∀ v w, d v w ≤ 1) :
    |∑ v ∈ s, ∑ w ∈ t,
        ((if G.Adj v w then (1 : ℝ) else 0) - d v w)| ≤
      (s.card : ℝ) * (t.card : ℝ) := by
  calc
    |∑ v ∈ s, ∑ w ∈ t,
        ((if G.Adj v w then (1 : ℝ) else 0) - d v w)| ≤
        ∑ v ∈ s, |∑ w ∈ t,
          ((if G.Adj v w then (1 : ℝ) else 0) - d v w)| :=
      Finset.abs_sum_le_sum_abs _ s
    _ ≤ ∑ _v ∈ s, ∑ _w ∈ t, (1 : ℝ) := by
      gcongr with v hv
      calc
        |∑ w ∈ t, ((if G.Adj v w then (1 : ℝ) else 0) - d v w)| ≤
            ∑ w ∈ t, |((if G.Adj v w then (1 : ℝ) else 0) - d v w)| :=
          Finset.abs_sum_le_sum_abs _ t
        _ ≤ ∑ _w ∈ t, (1 : ℝ) := by
          gcongr with w hw
          by_cases h : G.Adj v w
          · simp only [if_pos h]
            rw [abs_of_nonneg (sub_nonneg.mpr (hd₁ v w))]
            linarith [hd₀ v w]
          · simp only [if_neg h, zero_sub, abs_neg, abs_of_nonneg (hd₀ v w)]
            exact hd₁ v w
    _ = (s.card : ℝ) * (t.card : ℝ) := by simp

/-- Ordered off-diagonal cluster pairs which are not regular. -/
def orderedIrregularPairs {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (epsilon : ℝ) (P : RegularPartition G epsilon) :
    Finset (Fin P.clusterCount × Fin P.clusterCount) := by
  classical
  exact Finset.univ.offDiag.filter fun ij ↦
    ¬ IsRegularPair G epsilon (P.clusters ij.1) (P.clusters ij.2)

theorem card_orderedIrregularPairs_le {n : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {epsilon : ℝ}
    (P : RegularPartition G epsilon) :
    (orderedIrregularPairs epsilon P).card ≤
      2 * (irregularPairs G epsilon P.clusters).card := by
  classical
  let swap : (Fin P.clusterCount × Fin P.clusterCount) ↪
      (Fin P.clusterCount × Fin P.clusterCount) :=
    (Equiv.prodComm _ _).toEmbedding
  have heq : orderedIrregularPairs epsilon P =
      irregularPairs G epsilon P.clusters ∪
        (irregularPairs G epsilon P.clusters).map swap := by
    ext ij
    rcases ij with ⟨i, j⟩
    simp only [orderedIrregularPairs, irregularPairs, Finset.mem_filter,
      Finset.mem_offDiag, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_map, swap, Equiv.coe_toEmbedding, Equiv.prodComm_apply,
      Prod.mk.injEq]
    by_cases hij : i = j
    · subst j
      simp
    · rcases lt_or_gt_of_ne hij with hlt | hgt
      · simp [hij, hlt, not_lt_of_ge hlt.le, isRegularPair_comm]
      · have hji : j ≠ i := fun h ↦ hij h.symm
        simp [hij, hji, hgt, not_lt_of_ge hgt.le, isRegularPair_comm]
  rw [heq]
  calc
    (irregularPairs G epsilon P.clusters ∪
        (irregularPairs G epsilon P.clusters).map swap).card ≤
        (irregularPairs G epsilon P.clusters).card +
          ((irregularPairs G epsilon P.clusters).map swap).card :=
      Finset.card_union_le _ _
    _ = 2 * (irregularPairs G epsilon P.clusters).card := by
      rw [Finset.card_map]
      omega

/-- Ordered cluster pairs on which the regular-pair estimate is unavailable:
the diagonal together with the irregular off-diagonal pairs. -/
def badClusterPairs {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (epsilon : ℝ) (P : RegularPartition G epsilon) :
    Finset (Fin P.clusterCount × Fin P.clusterCount) := by
  classical
  exact Finset.univ.filter fun ij ↦
    ij.1 = ij.2 ∨
      ¬ IsRegularPair G epsilon (P.clusters ij.1) (P.clusters ij.2)

theorem card_badClusterPairs_le {n : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {epsilon : ℝ}
    (P : RegularPartition G epsilon) :
    (badClusterPairs epsilon P).card ≤ P.clusterCount +
      2 * (irregularPairs G epsilon P.clusters).card := by
  classical
  have hsub : badClusterPairs epsilon P ⊆
      (Finset.univ : Finset (Fin P.clusterCount)).diag ∪
        orderedIrregularPairs epsilon P := by
    intro ij hij
    rcases ij with ⟨i, j⟩
    simp only [badClusterPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hij
    rcases hij with hij | hirr
    · simp [hij]
    · by_cases hij : i = j
      · simp [hij]
      · simp [orderedIrregularPairs, hij, hirr]
  calc
    (badClusterPairs epsilon P).card ≤
        ((Finset.univ : Finset (Fin P.clusterCount)).diag ∪
          orderedIrregularPairs epsilon P).card := Finset.card_le_card hsub
    _ ≤ ((Finset.univ : Finset (Fin P.clusterCount)).diag).card +
          (orderedIrregularPairs epsilon P).card := Finset.card_union_le _ _
    _ ≤ P.clusterCount +
          2 * (irregularPairs G epsilon P.clusters).card := by
      simpa using add_le_add_left (card_orderedIrregularPairs_le P) P.clusterCount

/-- The centered contribution of one ordered pair of partition clusters. -/
def clusterRectangleError {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {epsilon : ℝ} (P : RegularPartition G epsilon)
    (s t : Finset (Fin n)) (i j : Fin P.clusterCount) : ℝ :=
  ∑ v ∈ clusterPart P s i, ∑ w ∈ clusterPart P t j,
    ((if G.Adj v w then (1 : ℝ) else 0) -
      graphDensity G (P.clusters i) (P.clusters j))

theorem abs_clusterRectangleError_le {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {epsilon : ℝ} (P : RegularPartition G epsilon)
    (hε : 0 ≤ epsilon) (s t : Finset (Fin n))
    (i j : Fin P.clusterCount) :
    |clusterRectangleError G P s t i j| ≤
      epsilon * (P.clusterSize : ℝ) ^ 2 +
        if (i, j) ∈ badClusterPairs epsilon P then (P.clusterSize : ℝ) ^ 2 else 0 := by
  classical
  by_cases hbad : (i, j) ∈ badClusterPairs epsilon P
  · have htriv := abs_centered_sum_le_card G
      (clusterPart P s i) (clusterPart P t j)
      (fun _ _ ↦ graphDensity G (P.clusters i) (P.clusters j))
      (fun _ _ ↦ graphDensity_nonneg G _ _)
      (fun _ _ ↦ graphDensity_le_one G _ _)
    have hsi : (clusterPart P s i).card ≤ P.clusterSize := by
      rw [← P.cluster_card_eq i]
      exact Finset.card_le_card inter_subset_right
    have htj : (clusterPart P t j).card ≤ P.clusterSize := by
      rw [← P.cluster_card_eq j]
      exact Finset.card_le_card inter_subset_right
    rw [if_pos hbad]
    calc
      |clusterRectangleError G P s t i j| ≤
          ((clusterPart P s i).card : ℝ) *
            ((clusterPart P t j).card : ℝ) := htriv
      _ ≤ (P.clusterSize : ℝ) ^ 2 := by
        norm_num [pow_two]
        gcongr <;> exact_mod_cast ‹_›
      _ ≤ epsilon * (P.clusterSize : ℝ) ^ 2 +
          (P.clusterSize : ℝ) ^ 2 := by
        nlinarith [mul_nonneg hε (sq_nonneg (P.clusterSize : ℝ))]
  · have hreg : IsRegularPair G epsilon (P.clusters i) (P.clusters j) := by
      have hp : i ≠ j ∧
          IsRegularPair G epsilon (P.clusters i) (P.clusters j) := by
        simpa [badClusterPairs] using hbad
      exact hp.2
    rw [if_neg hbad]
    calc
      |clusterRectangleError G P s t i j| ≤
          epsilon * ((P.clusters i).card : ℝ) *
            ((P.clusters j).card : ℝ) :=
        hreg.abs_sum_centered_adjIndicator_le G hε
          (inter_subset_right : clusterPart P s i ⊆ P.clusters i)
          (inter_subset_right : clusterPart P t j ⊆ P.clusters j)
      _ = epsilon * (P.clusterSize : ℝ) ^ 2 := by
        rw [P.cluster_card_eq i, P.cluster_card_eq j]
        ring
      _ = epsilon * (P.clusterSize : ℝ) ^ 2 + 0 := by ring

/-- On nonexceptional vertices, a label which is constant on every cluster
turns the centered sum into the sum of the cluster-pair errors. -/
theorem sum_nonexceptional_centered_eq_clusterErrors {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {epsilon : ℝ} (P : RegularPartition G epsilon)
    (label : Fin n × Fin P.clusterCount → Fin P.clusterCount)
    (hcl : ∀ i v, v ∈ P.clusters i → ∀ b, label (v, b) = i)
    (s t : Finset (Fin n)) (b c : Fin P.clusterCount) :
    ∑ v ∈ nonexceptionalPart P s, ∑ w ∈ nonexceptionalPart P t,
        ((if G.Adj v w then (1 : ℝ) else 0) -
          graphDensity G (P.clusters (label (v, b)))
            (P.clusters (label (w, c)))) =
      ∑ i : Fin P.clusterCount, ∑ j : Fin P.clusterCount,
        clusterRectangleError G P s t i j := by
  classical
  rw [sum_nonexceptionalPart_eq_sum_clusterPart P s]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [sum_nonexceptionalPart_eq_sum_clusterPart P t]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [clusterRectangleError]
  apply Finset.sum_congr rfl
  intro v hv
  have hvi : v ∈ P.clusters i := (Finset.mem_inter.mp hv).2
  rw [hcl i v hvi b]
  apply Finset.sum_congr rfl
  intro w hw
  have hwj : w ∈ P.clusters j := (Finset.mem_inter.mp hw).2
  rw [hcl j w hwj c]

/-- The total nonexceptional contribution of a regular partition, before
using the numerical irregular-pair bound. -/
theorem abs_sum_clusterRectangleError_le {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {epsilon : ℝ} (P : RegularPartition G epsilon) (hε : 0 ≤ epsilon)
    (s t : Finset (Fin n)) :
    |∑ i : Fin P.clusterCount, ∑ j : Fin P.clusterCount,
        clusterRectangleError G P s t i j| ≤
      epsilon * (P.clusterCount : ℝ) ^ 2 * (P.clusterSize : ℝ) ^ 2 +
        ((badClusterPairs epsilon P).card : ℝ) * (P.clusterSize : ℝ) ^ 2 := by
  classical
  let M : ℝ := (P.clusterSize : ℝ) ^ 2
  have hbadSum :
      (∑ i : Fin P.clusterCount, ∑ j : Fin P.clusterCount,
        if (i, j) ∈ badClusterPairs epsilon P then M else 0) =
        ((badClusterPairs epsilon P).card : ℝ) * M := by
    rw [← Finset.sum_product', Finset.univ_product_univ]
    calc
      (∑ ij : Fin P.clusterCount × Fin P.clusterCount,
          if ij ∈ badClusterPairs epsilon P then M else 0) =
          ∑ ij : Fin P.clusterCount × Fin P.clusterCount,
            (if ij ∈ badClusterPairs epsilon P then (1 : ℝ) else 0) * M := by
        apply Finset.sum_congr rfl
        intro ij hij
        split <;> simp_all
      _ = (∑ ij : Fin P.clusterCount × Fin P.clusterCount,
          if ij ∈ badClusterPairs epsilon P then (1 : ℝ) else 0) * M := by
        rw [Finset.sum_mul]
      _ = ((badClusterPairs epsilon P).card : ℝ) * M := by simp
  calc
    |∑ i : Fin P.clusterCount, ∑ j : Fin P.clusterCount,
        clusterRectangleError G P s t i j| ≤
        ∑ i : Fin P.clusterCount,
          |∑ j : Fin P.clusterCount, clusterRectangleError G P s t i j| := by
      exact Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ i : Fin P.clusterCount, ∑ j : Fin P.clusterCount,
        |clusterRectangleError G P s t i j| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ i : Fin P.clusterCount, ∑ j : Fin P.clusterCount,
        (epsilon * M +
          if (i, j) ∈ badClusterPairs epsilon P then M else 0) := by
      gcongr with i j
      simpa [M] using abs_clusterRectangleError_le G P hε s t i j
    _ = epsilon * (P.clusterCount : ℝ) ^ 2 * M +
        ((badClusterPairs epsilon P).card : ℝ) * M := by
      simp_rw [Finset.sum_add_distrib]
      rw [hbadSum]
      simp
      ring
    _ = epsilon * (P.clusterCount : ℝ) ^ 2 *
          (P.clusterSize : ℝ) ^ 2 +
        ((badClusterPairs epsilon P).card : ℝ) *
          (P.clusterSize : ℝ) ^ 2 := rfl

private theorem partitionCardIdentity {n : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {epsilon : ℝ}
    (P : RegularPartition G epsilon) :
    P.exceptional.card + P.clusterCount * P.clusterSize = n := by
  classical
  let U : Finset (Fin n) := Finset.univ.biUnion P.clusters
  have hdisj : Disjoint P.exceptional U := by
    rw [Finset.disjoint_left]
    intro v hvE hvU
    obtain ⟨i, _, hvi⟩ := Finset.mem_biUnion.mp hvU
    exact (Finset.disjoint_left.mp (P.exceptional_disjoint i)) hvE hvi
  have hUcard : U.card = P.clusterCount * P.clusterSize := by
    dsimp only [U]
    rw [Finset.card_biUnion (by simpa using P.clusters_pairwiseDisjoint)]
    simp [P.cluster_card_eq]
  have hcover : P.exceptional ∪ U = (Finset.univ : Finset (Fin n)) := P.cover
  calc
    P.exceptional.card + P.clusterCount * P.clusterSize =
        P.exceptional.card + U.card := by rw [hUcard]
    _ = (P.exceptional ∪ U).card :=
      (Finset.card_union_of_disjoint hdisj).symm
    _ = (Finset.univ : Finset (Fin n)).card := congrArg Finset.card hcover
    _ = n := by simp

/-- Coarse numerical form of the core estimate.  The factor `3ε` consists
of one regular-pair contribution and two orientations of each irregular
unordered pair. -/
theorem abs_sum_clusterRectangleError_le_coarse {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {epsilon : ℝ} (P : RegularPartition G epsilon) (hε : 0 ≤ epsilon)
    (s t : Finset (Fin n)) :
    |∑ i : Fin P.clusterCount, ∑ j : Fin P.clusterCount,
        clusterRectangleError G P s t i j| ≤
      (3 * epsilon * (P.clusterCount : ℝ) ^ 2 + P.clusterCount) *
        (P.clusterSize : ℝ) ^ 2 := by
  have hchoose : ((Nat.choose P.clusterCount 2 : ℕ) : ℝ) ≤
      (P.clusterCount : ℝ) ^ 2 := by
    exact_mod_cast Nat.choose_le_pow P.clusterCount 2
  have hirr : ((irregularPairs G epsilon P.clusters).card : ℝ) ≤
      epsilon * (P.clusterCount : ℝ) ^ 2 :=
    P.irregular_pair_card_le.trans (mul_le_mul_of_nonneg_left hchoose hε)
  have hbad : ((badClusterPairs epsilon P).card : ℝ) ≤
      (P.clusterCount : ℝ) +
        2 * (epsilon * (P.clusterCount : ℝ) ^ 2) := by
    calc
      ((badClusterPairs epsilon P).card : ℝ) ≤
          (P.clusterCount : ℝ) +
            2 * ((irregularPairs G epsilon P.clusters).card : ℝ) := by
        exact_mod_cast card_badClusterPairs_le P
      _ ≤ (P.clusterCount : ℝ) +
            2 * (epsilon * (P.clusterCount : ℝ) ^ 2) := by gcongr
  calc
    |∑ i : Fin P.clusterCount, ∑ j : Fin P.clusterCount,
        clusterRectangleError G P s t i j| ≤
        epsilon * (P.clusterCount : ℝ) ^ 2 * (P.clusterSize : ℝ) ^ 2 +
          ((badClusterPairs epsilon P).card : ℝ) *
            (P.clusterSize : ℝ) ^ 2 :=
      abs_sum_clusterRectangleError_le G P hε s t
    _ ≤ epsilon * (P.clusterCount : ℝ) ^ 2 * (P.clusterSize : ℝ) ^ 2 +
          ((P.clusterCount : ℝ) +
            2 * (epsilon * (P.clusterCount : ℝ) ^ 2)) *
              (P.clusterSize : ℝ) ^ 2 := by gcongr
    _ = (3 * epsilon * (P.clusterCount : ℝ) ^ 2 + P.clusterCount) *
          (P.clusterSize : ℝ) ^ 2 := by ring

/-- The core contribution, normalized using that the clusters occupy at most
all `n` vertices. -/
theorem abs_sum_clusterRectangleError_le_normalized {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {epsilon : ℝ} (P : RegularPartition G epsilon)
    (hk : 0 < P.clusterCount) (hε : 0 ≤ epsilon)
    (s t : Finset (Fin n)) :
    |∑ i : Fin P.clusterCount, ∑ j : Fin P.clusterCount,
        clusterRectangleError G P s t i j| ≤
      (3 * epsilon + 1 / (P.clusterCount : ℝ)) * (n : ℝ) ^ 2 := by
  have hkR : (0 : ℝ) < P.clusterCount := by exact_mod_cast hk
  have hkmNat : P.clusterCount * P.clusterSize ≤ n := by
    have hcard := partitionCardIdentity P
    omega
  have hkm : (P.clusterCount : ℝ) * (P.clusterSize : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hkmNat
  have hcoef : 0 ≤ 3 * epsilon + 1 / (P.clusterCount : ℝ) := by positivity
  calc
    |∑ i : Fin P.clusterCount, ∑ j : Fin P.clusterCount,
        clusterRectangleError G P s t i j| ≤
        (3 * epsilon * (P.clusterCount : ℝ) ^ 2 + P.clusterCount) *
          (P.clusterSize : ℝ) ^ 2 :=
      abs_sum_clusterRectangleError_le_coarse G P hε s t
    _ = (3 * epsilon + 1 / (P.clusterCount : ℝ)) *
          ((P.clusterCount : ℝ) * (P.clusterSize : ℝ)) ^ 2 := by
      field_simp
    _ ≤ (3 * epsilon + 1 / (P.clusterCount : ℝ)) * (n : ℝ) ^ 2 := by
      gcongr

/-- Split a rectangle into an exceptional-row part, an exceptional-column
part among the remaining rows, and the nonexceptional core. -/
theorem sum_rectangle_eq_exceptional_add_core {n : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {epsilon : ℝ} (P : RegularPartition G epsilon)
    (s t : Finset (Fin n)) (f : Fin n → Fin n → ℝ) :
    ∑ v ∈ s, ∑ w ∈ t, f v w =
      (∑ v ∈ exceptionalPart P s, ∑ w ∈ t, f v w) +
      (∑ v ∈ nonexceptionalPart P s,
        ∑ w ∈ exceptionalPart P t, f v w) +
      ∑ v ∈ nonexceptionalPart P s,
        ∑ w ∈ nonexceptionalPart P t, f v w := by
  rw [sum_eq_exceptionalPart_add_nonexceptionalPart P s]
  have hinner (v : Fin n) :
      ∑ w ∈ t, f v w =
        (∑ w ∈ exceptionalPart P t, f v w) +
          ∑ w ∈ nonexceptionalPart P t, f v w :=
    sum_eq_exceptionalPart_add_nonexceptionalPart P t (f v)
  simp_rw [hinner, Finset.sum_add_distrib]
  ring

/-- The centered rectangle estimate on one fixed pair of copy coordinates.
Exceptional rows and columns cost `2ε n²`; the regular-partition core costs
`(3ε + 1/k)n²`. -/
theorem RegularPartition.abs_centered_slice_sum_le {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {epsilon : ℝ} (P : RegularPartition G epsilon)
    (hk : 0 < P.clusterCount) (hε : 0 ≤ epsilon)
    (label : Fin n × Fin P.clusterCount → Fin P.clusterCount)
    (_hex : ∀ v, v ∈ P.exceptional → ∀ b, label (v, b) = b)
    (hcl : ∀ i v, v ∈ P.clusters i → ∀ b, label (v, b) = i)
    (s t : Finset (Fin n)) (b c : Fin P.clusterCount) :
    |∑ v ∈ s, ∑ w ∈ t,
        ((if G.Adj v w then (1 : ℝ) else 0) -
          graphDensity G (P.clusters (label (v, b)))
            (P.clusters (label (w, c))))| ≤
      (5 * epsilon + 1 / (P.clusterCount : ℝ)) * (n : ℝ) ^ 2 := by
  let f : Fin n → Fin n → ℝ := fun v w ↦
    (if G.Adj v w then (1 : ℝ) else 0) -
      graphDensity G (P.clusters (label (v, b)))
        (P.clusters (label (w, c)))
  let left : ℝ :=
    ∑ v ∈ exceptionalPart P s, ∑ w ∈ t, f v w
  let right : ℝ :=
    ∑ v ∈ nonexceptionalPart P s, ∑ w ∈ exceptionalPart P t, f v w
  let core : ℝ :=
    ∑ v ∈ nonexceptionalPart P s,
      ∑ w ∈ nonexceptionalPart P t, f v w
  have hsplit : (∑ v ∈ s, ∑ w ∈ t, f v w) = left + right + core := by
    exact sum_rectangle_eq_exceptional_add_core P s t f
  have hleft : |left| ≤
      ((exceptionalPart P s).card : ℝ) * (t.card : ℝ) := by
    exact abs_centered_sum_le_card G (exceptionalPart P s) t
      (fun v w ↦ graphDensity G (P.clusters (label (v, b)))
        (P.clusters (label (w, c))))
      (fun v w ↦ graphDensity_nonneg G _ _)
      (fun v w ↦ graphDensity_le_one G _ _)
  have hright : |right| ≤
      ((nonexceptionalPart P s).card : ℝ) *
        ((exceptionalPart P t).card : ℝ) := by
    exact abs_centered_sum_le_card G (nonexceptionalPart P s)
      (exceptionalPart P t)
      (fun v w ↦ graphDensity G (P.clusters (label (v, b)))
        (P.clusters (label (w, c))))
      (fun v w ↦ graphDensity_nonneg G _ _)
      (fun v w ↦ graphDensity_le_one G _ _)
  have hsE : (exceptionalPart P s).card ≤ P.exceptional.card :=
    Finset.card_le_card (by intro v hv; exact (Finset.mem_filter.mp hv).2)
  have htE : (exceptionalPart P t).card ≤ P.exceptional.card :=
    Finset.card_le_card (by intro v hv; exact (Finset.mem_filter.mp hv).2)
  have hsN : (nonexceptionalPart P s).card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ (nonexceptionalPart P s))
  have ht : t.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ t)
  have hleft' : |left| ≤ (P.exceptional.card : ℝ) * (n : ℝ) := by
    calc
      |left| ≤ ((exceptionalPart P s).card : ℝ) * (t.card : ℝ) := hleft
      _ ≤ (P.exceptional.card : ℝ) * (n : ℝ) := by
        gcongr <;> exact_mod_cast ‹_›
  have hright' : |right| ≤ (n : ℝ) * (P.exceptional.card : ℝ) := by
    calc
      |right| ≤ ((nonexceptionalPart P s).card : ℝ) *
          ((exceptionalPart P t).card : ℝ) := hright
      _ ≤ (n : ℝ) * (P.exceptional.card : ℝ) := by
        gcongr <;> exact_mod_cast ‹_›
  have hE : (P.exceptional.card : ℝ) ≤ epsilon * (n : ℝ) := by
    simpa using P.exceptional_card_le
  have hcoreEq : core =
      ∑ i : Fin P.clusterCount, ∑ j : Fin P.clusterCount,
        clusterRectangleError G P s t i j := by
    exact sum_nonexceptional_centered_eq_clusterErrors G P label hcl s t b c
  have hcore : |core| ≤
      (3 * epsilon + 1 / (P.clusterCount : ℝ)) * (n : ℝ) ^ 2 := by
    rw [hcoreEq]
    exact abs_sum_clusterRectangleError_le_normalized G P hk hε s t
  have hnonnegN : (0 : ℝ) ≤ n := by positivity
  change |∑ v ∈ s, ∑ w ∈ t, f v w| ≤ _
  rw [hsplit]
  calc
    |left + right + core| ≤ |left| + |right| + |core| := by
      calc
        |left + right + core| ≤ |left + right| + |core| := abs_add_le _ _
        _ ≤ (|left| + |right|) + |core| := by gcongr; exact abs_add_le _ _
    _ ≤ (P.exceptional.card : ℝ) * (n : ℝ) +
          (n : ℝ) * (P.exceptional.card : ℝ) +
          (3 * epsilon + 1 / (P.clusterCount : ℝ)) * (n : ℝ) ^ 2 := by
      gcongr
    _ ≤ (epsilon * (n : ℝ)) * (n : ℝ) +
          (n : ℝ) * (epsilon * (n : ℝ)) +
          (3 * epsilon + 1 / (P.clusterCount : ℝ)) * (n : ℝ) ^ 2 := by
      gcongr
    _ = (5 * epsilon + 1 / (P.clusterCount : ℝ)) * (n : ℝ) ^ 2 := by ring

/-- Finite regular-partition cut bookkeeping after taking `k` copies of every
vertex.  This is the host-rectangle estimate used by graphon approximation.
The label may be arbitrary on exceptional vertices; it only has to agree with
the cluster index on each nonexceptional cluster.

The finite estimate retains the diagonal-block contribution. -/
theorem RegularPartition.abs_centered_copy_sum_le {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {epsilon : ℝ} (P : RegularPartition G epsilon)
    (hk : 0 < P.clusterCount) (hε : 0 ≤ epsilon)
    (label : Fin n × Fin P.clusterCount → Fin P.clusterCount)
    (hex : ∀ v, v ∈ P.exceptional → ∀ b, label (v, b) = b)
    (hcl : ∀ i v, v ∈ P.clusters i → ∀ b, label (v, b) = i)
    (S T : Finset (Fin n × Fin P.clusterCount)) :
    |∑ p ∈ S, ∑ q ∈ T,
        ((if G.Adj p.1 q.1 then (1 : ℝ) else 0) -
          graphDensity G (P.clusters (label p)) (P.clusters (label q)))| ≤
      (5 * epsilon + 1 / (P.clusterCount : ℝ)) *
        (((P.clusterCount * n : ℕ) : ℝ) ^ 2) := by
  let F : (Fin n × Fin P.clusterCount) →
      (Fin n × Fin P.clusterCount) → ℝ := fun p q ↦
    (if G.Adj p.1 q.1 then (1 : ℝ) else 0) -
      graphDensity G (P.clusters (label p)) (P.clusters (label q))
  have hcopy : |∑ p ∈ S, ∑ q ∈ T, F p q| ≤
      (P.clusterCount : ℝ) ^ 2 *
        ((5 * epsilon + 1 / (P.clusterCount : ℝ)) * (n : ℝ) ^ 2) := by
    apply abs_sum_copyPairs_dep_le S T F
    intro b c
    exact P.abs_centered_slice_sum_le G hk hε label hex hcl
      (copySlice S b) (copySlice T c) b c
  change |∑ p ∈ S, ∑ q ∈ T, F p q| ≤ _
  calc
    |∑ p ∈ S, ∑ q ∈ T, F p q| ≤
        (P.clusterCount : ℝ) ^ 2 *
          ((5 * epsilon + 1 / (P.clusterCount : ℝ)) * (n : ℝ) ^ 2) := hcopy
    _ = (5 * epsilon + 1 / (P.clusterCount : ℝ)) *
        (((P.clusterCount * n : ℕ) : ℝ) ^ 2) := by
      push_cast
      ring

end

end InducedStars.Regularity
