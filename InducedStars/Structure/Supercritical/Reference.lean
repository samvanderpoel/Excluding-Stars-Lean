import DenseGraph.FiniteModels.BalancedPartition
import DenseGraph.FiniteModels.WeightedGraph
import InducedStars.Graphon.Candidates
import InducedStars.Graphon.SupercriticalClassification
import Mathlib.Tactic

/-!
# Finite supercritical reference models

The reference matrix uses the canonical balanced consecutive partition of
`Fin n`.  Its value is one on each diagonal block (including matrix loops)
and `phaseLower k γ` between distinct blocks.
-/

noncomputable section

open Finset Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff

namespace InducedStars

/-- The paper's supercritical off-diagonal scalar is strictly positive on
the closed supercritical density interval. -/
theorem supercriticalOffDiagonal_pos {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : gammaK k ≤ γ) : 0 < supercriticalOffDiagonal k γ :=
  (pK_pos (by omega : 2 ≤ k)).trans_le
    (pK_le_supercriticalOffDiagonal hk hγ)

/-- The `i`th consecutive reference block. -/
def supercriticalReferencePart (k n : ℕ) (i : Fin (k - 1)) :
    Finset (Fin n) :=
  DenseGraph.balancedFinPartition (k - 1) n i

theorem supercriticalReferenceParts_pairwiseDisjoint (k n : ℕ) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin (k - 1)))
      (supercriticalReferencePart k n) := by
  change Set.PairwiseDisjoint (Set.univ : Set (Fin (k - 1)))
    (DenseGraph.balancedFinPartition (k - 1) n)
  exact DenseGraph.balancedFinPartition_pairwiseDisjoint (k - 1) n

@[simp] theorem biUnion_supercriticalReferencePart
    {k n : ℕ} (hk : 3 ≤ k) :
    Finset.univ.biUnion (supercriticalReferencePart k n) =
      (Finset.univ : Finset (Fin n)) := by
  change Finset.univ.biUnion
      (DenseGraph.balancedFinPartition (k - 1) n) = Finset.univ
  exact DenseGraph.biUnion_balancedFinPartition
    (n := n) (by omega : 0 < k - 1)

@[simp] theorem card_supercriticalReferencePart
    {k n : ℕ} (hk : 3 ≤ k) (i : Fin (k - 1)) :
    (supercriticalReferencePart k n i).card =
      n / (k - 1) + if i.1 < n % (k - 1) then 1 else 0 := by
  simpa [supercriticalReferencePart] using
    DenseGraph.card_balancedFinPartition (n := n)
      (by omega : 0 < k - 1) i

theorem supercriticalReferencePart_nonempty
    {k n : ℕ} (hk : 3 ≤ k) (hkn : k - 1 ≤ n)
    (i : Fin (k - 1)) :
    (supercriticalReferencePart k n i).Nonempty := by
  exact DenseGraph.balancedFinPartition_nonempty
    (by omega : 0 < k - 1) hkn i

/-- Two finite vertices lie in the same reference block. -/
def SupercriticalReferenceSamePart (k n : ℕ) (x y : Fin n) : Prop :=
  ∃ i : Fin (k - 1),
    x ∈ supercriticalReferencePart k n i ∧
      y ∈ supercriticalReferencePart k n i

instance instDecidableSupercriticalReferenceSamePart
    (k n : ℕ) (x y : Fin n) :
    Decidable (SupercriticalReferenceSamePart k n x y) :=
  Classical.propDecidable _

theorem supercriticalReferenceSamePart_comm
    {k n : ℕ} {x y : Fin n} :
    SupercriticalReferenceSamePart k n x y ↔
      SupercriticalReferenceSamePart k n y x := by
  constructor <;> rintro ⟨i, hx, hy⟩ <;> exact ⟨i, hy, hx⟩

theorem supercriticalReferenceSamePart_self
    {k n : ℕ} (hk : 3 ≤ k) (x : Fin n) :
    SupercriticalReferenceSamePart k n x x := by
  have hx : x ∈ Finset.univ.biUnion (supercriticalReferencePart k n) := by
    rw [biUnion_supercriticalReferencePart hk]
    exact Finset.mem_univ x
  obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
  exact ⟨i, hxi, hxi⟩

/-- The balanced finite weighted discretization of `Wstar`. -/
def supercriticalReferenceWeightedGraph
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (n : ℕ) :
    DenseGraph.FiniteWeightedGraph (Fin n) where
  weight x y :=
    if SupercriticalReferenceSamePart k n x y then 1
    else supercriticalOffDiagonal k γ
  symmetric x y := by
    by_cases hxy : SupercriticalReferenceSamePart k n x y
    · have hyx := supercriticalReferenceSamePart_comm.mp hxy
      simp [hxy, hyx]
    · have hyx : ¬ SupercriticalReferenceSamePart k n y x := by
        exact fun h ↦ hxy (supercriticalReferenceSamePart_comm.mpr h)
      simp [hxy, hyx]
  nonneg x y := by
    split
    · norm_num
    · exact (supercriticalOffDiagonal_pos hk hγ.1).le
  le_one x y := by
    split
    · exact le_rfl
    · exact (supercriticalOffDiagonal_lt_one hk hγ.2).le

theorem supercriticalReferenceWeightedGraph_weight_of_samePart
    {k n : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) {x y : Fin n}
    (hxy : SupercriticalReferenceSamePart k n x y) :
    (supercriticalReferenceWeightedGraph k hk γ hγ n).weight x y = 1 := by
  simp [supercriticalReferenceWeightedGraph, hxy]

theorem supercriticalReferenceWeightedGraph_weight_of_mem_samePart
    {k n : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (i : Fin (k - 1))
    {x y : Fin n} (hx : x ∈ supercriticalReferencePart k n i)
    (hy : y ∈ supercriticalReferencePart k n i) :
    (supercriticalReferenceWeightedGraph k hk γ hγ n).weight x y = 1 :=
  supercriticalReferenceWeightedGraph_weight_of_samePart hk hγ ⟨i, hx, hy⟩

theorem not_supercriticalReferenceSamePart_of_mem_distinct
    {k n : ℕ} {i j : Fin (k - 1)} (hij : i ≠ j)
    {x y : Fin n} (hx : x ∈ supercriticalReferencePart k n i)
    (hy : y ∈ supercriticalReferencePart k n j) :
    ¬ SupercriticalReferenceSamePart k n x y := by
  rintro ⟨a, hxa, hya⟩
  have hai : a = i := by
    by_contra hne
    exact (Finset.disjoint_left.mp
      (supercriticalReferenceParts_pairwiseDisjoint k n
        (Set.mem_univ a) (Set.mem_univ i) hne)) hxa hx
  have haj : a = j := by
    by_contra hne
    exact (Finset.disjoint_left.mp
      (supercriticalReferenceParts_pairwiseDisjoint k n
        (Set.mem_univ a) (Set.mem_univ j) hne)) hya hy
  exact hij (hai.symm.trans haj)

theorem supercriticalReferenceWeightedGraph_weight_of_mem_distinct
    {k n : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) {i j : Fin (k - 1)}
    (hij : i ≠ j) {x y : Fin n}
    (hx : x ∈ supercriticalReferencePart k n i)
    (hy : y ∈ supercriticalReferencePart k n j) :
    (supercriticalReferenceWeightedGraph k hk γ hγ n).weight x y =
      supercriticalOffDiagonal k γ := by
  simp [supercriticalReferenceWeightedGraph,
    not_supercriticalReferenceSamePart_of_mem_distinct hij hx hy]

@[simp] theorem supercriticalReferenceWeightedGraph_weight_diag
    {k n : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (x : Fin n) :
    (supercriticalReferenceWeightedGraph k hk γ hγ n).weight x x = 1 :=
  supercriticalReferenceWeightedGraph_weight_of_samePart hk hγ
    (supercriticalReferenceSamePart_self hk x)

theorem supercriticalOffDiagonal_le_referenceWeight
    {k n : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (x y : Fin n) :
    supercriticalOffDiagonal k γ ≤
      (supercriticalReferenceWeightedGraph k hk γ hγ n).weight x y := by
  change supercriticalOffDiagonal k γ ≤
    if SupercriticalReferenceSamePart k n x y then 1
    else supercriticalOffDiagonal k γ
  split
  · exact (supercriticalOffDiagonal_lt_one hk hγ.2).le
  · exact le_rfl

theorem supercriticalReferenceWeightedGraph_weight_le_one
    {k n : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (x y : Fin n) :
    (supercriticalReferenceWeightedGraph k hk γ hγ n).weight x y ≤ 1 :=
  (supercriticalReferenceWeightedGraph k hk γ hγ n).le_one x y

/-- Equal-cell graphon of the explicit finite reference matrix. -/
def supercriticalReferenceGraphon
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (n : ℕ) : Graphon :=
  (supercriticalReferenceWeightedGraph k hk γ hγ n).toGraphon

/-! ## Quantitative convergence to `Wstar` -/

/-- Left endpoint of the interval occupied by one finite reference block. -/
def supercriticalReferenceBlockLeft
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n) (i : Fin (k - 1)) :
    UnitInterval :=
  ⟨(DenseGraph.balancedFinPartitionStart (k - 1) n i : ℝ) / n,
    by positivity, by
      apply (div_le_one (by exact_mod_cast hn)).2
      exact_mod_cast DenseGraph.balancedFinPartitionStart_le_card
        (by omega : 0 < k - 1) i.2.le⟩

/-- Right endpoint of the interval occupied by one finite reference block. -/
def supercriticalReferenceBlockRight
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n) (i : Fin (k - 1)) :
    UnitInterval :=
  ⟨(DenseGraph.balancedFinPartitionStart (k - 1) n (i.1 + 1) : ℝ) / n,
    by positivity, by
      apply (div_le_one (by exact_mod_cast hn)).2
      exact_mod_cast DenseGraph.balancedFinPartitionStart_le_card
        (by omega : 0 < k - 1) (Nat.succ_le_iff.mpr i.2)⟩

/-- The consecutive interval occupied by one finite reference block. -/
def supercriticalReferenceBlock
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n) (i : Fin (k - 1)) :
    Set UnitInterval :=
  Set.Ico (supercriticalReferenceBlockLeft hk hn i)
    (supercriticalReferenceBlockRight hk hn i)

theorem measurableSet_supercriticalReferenceBlock
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n) (i : Fin (k - 1)) :
    MeasurableSet (supercriticalReferenceBlock hk hn i) :=
  measurableSet_Ico

/-- Membership in a finite reference part is exactly membership of a point
of its fine cell in the corresponding consecutive interval. -/
theorem mem_supercriticalReferencePart_iff_mem_block
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n)
    (i : Fin (k - 1)) (v : Fin n) {x : UnitInterval}
    (hx : x ∈ equalCell v) :
    v ∈ supercriticalReferencePart k n i ↔
      x ∈ supercriticalReferenceBlock hk hn i := by
  have hnℝ : 0 < (n : ℝ) := by exact_mod_cast hn
  change v ∈ DenseGraph.balancedFinPartition (k - 1) n i ↔ _
  rw [DenseGraph.mem_balancedFinPartition]
  change (_ ≤ v.1 ∧ v.1 < _) ↔
    ((_ : ℝ) / n ≤ (x : ℝ) ∧ (x : ℝ) < (_ : ℝ) / n)
  change (v : ℝ) / n ≤ (x : ℝ) ∧
    (x : ℝ) < ((v : ℕ) + 1 : ℝ) / n at hx
  constructor
  · rintro ⟨hleft, hright⟩
    constructor
    · exact (div_le_div_of_nonneg_right (by exact_mod_cast hleft) hnℝ.le).trans hx.1
    · have hs : (v : ℕ) + 1 ≤
          DenseGraph.balancedFinPartitionStart (k - 1) n (i.1 + 1) :=
        Nat.succ_le_iff.mpr hright
      exact hx.2.trans_le
        (div_le_div_of_nonneg_right (by exact_mod_cast hs) hnℝ.le)
  · rintro ⟨hleft, hright⟩
    constructor
    · by_contra hnot
      have hs : (v : ℕ) + 1 ≤
          DenseGraph.balancedFinPartitionStart (k - 1) n i := by omega
      have hsℝ : ((v : ℝ) + 1) / n ≤
          (DenseGraph.balancedFinPartitionStart (k - 1) n i : ℝ) / n :=
        div_le_div_of_nonneg_right (by exact_mod_cast hs) hnℝ.le
      exact (not_lt_of_ge hleft) (hx.2.trans_le hsℝ)
    · by_contra hnot
      have hs : DenseGraph.balancedFinPartitionStart
          (k - 1) n (i.1 + 1) ≤ v.1 := Nat.le_of_not_gt hnot
      have hsℝ :
          (DenseGraph.balancedFinPartitionStart (k - 1) n (i.1 + 1) : ℝ) / n ≤
            (v : ℝ) / n :=
        div_le_div_of_nonneg_right (by exact_mod_cast hs) hnℝ.le
      exact (not_le_of_gt hright) (hsℝ.trans hx.1)

/-- A balanced prefix endpoint differs from its limiting equal-block
endpoint by at most `(r : ℝ) / n`. -/
theorem abs_balancedFinPartitionStart_div_sub
    {r n i : ℕ} (hr : 0 < r) (hn : 0 < n) (hi : i ≤ r) :
    |(DenseGraph.balancedFinPartitionStart r n i : ℝ) / n -
        (i : ℝ) / r| ≤ (r : ℝ) / n := by
  let s := n % r
  let t := min i s
  have hslt : s < r := Nat.mod_lt n hr
  have htS : t ≤ s := min_le_right _ _
  have htI : t ≤ i := min_le_left _ _
  have hrℝ : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnℝ : 0 < (n : ℝ) := by exact_mod_cast hn
  have hiℝ : (i : ℝ) ≤ r := by exact_mod_cast hi
  have hsℝ : (s : ℝ) ≤ r := by exact_mod_cast hslt.le
  have htSℝ : (t : ℝ) ≤ s := by exact_mod_cast htS
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hi0 : (0 : ℝ) ≤ i := by positivity
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hnum : |(r : ℝ) * t - (i : ℝ) * s| ≤ (r : ℝ) ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hdecomp : (n : ℝ) = (s : ℝ) + (r : ℝ) * (n / r : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n r).symm
  have hformula :
      (DenseGraph.balancedFinPartitionStart r n i : ℝ) / n -
          (i : ℝ) / r =
        ((r : ℝ) * t - (i : ℝ) * s) / ((n : ℝ) * r) := by
    unfold DenseGraph.balancedFinPartitionStart
    simp only [Nat.cast_add, Nat.cast_mul]
    change (((i : ℝ) * (n / r : ℕ) + (t : ℝ)) / n -
      (i : ℝ) / r) = _
    field_simp [hnℝ.ne', hrℝ.ne']
    nlinarith [hdecomp]
  rw [hformula, abs_div, abs_of_pos (mul_pos hnℝ hrℝ)]
  calc
    |(r : ℝ) * t - (i : ℝ) * s| / ((n : ℝ) * r) ≤
        (r : ℝ) ^ 2 / ((n : ℝ) * r) := by
      gcongr
    _ = (r : ℝ) / n := by
      field_simp [hnℝ.ne', hrℝ.ne']

theorem abs_supercriticalReferenceBlockLeft_sub_equalCellLeft
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n) (i : Fin (k - 1)) :
    |((supercriticalReferenceBlockLeft hk hn i : UnitInterval) : ℝ) -
        ((equalCellLeft i : UnitInterval) : ℝ)| ≤
      ((k - 1 : ℕ) : ℝ) / n := by
  simpa [supercriticalReferenceBlockLeft, equalCellLeft] using
    (abs_balancedFinPartitionStart_div_sub
      (by omega : 0 < k - 1) hn i.2.le)

theorem abs_supercriticalReferenceBlockRight_sub_equalCellRight
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n) (i : Fin (k - 1)) :
    |((supercriticalReferenceBlockRight hk hn i : UnitInterval) : ℝ) -
        ((equalCellRight i : UnitInterval) : ℝ)| ≤
      ((k - 1 : ℕ) : ℝ) / n := by
  simpa [supercriticalReferenceBlockRight, equalCellRight] using
    (abs_balancedFinPartitionStart_div_sub
      (by omega : 0 < k - 1) hn (Nat.succ_le_iff.mpr i.2))

/-- One-dimensional set on which the finite balanced block labels may differ
from the limiting equal-block labels. -/
def supercriticalReferenceBoundaryError
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n) : Set UnitInterval :=
  ⋃ i : Fin (k - 1),
    supercriticalReferenceBlock hk hn i ∆ equalCell i

theorem measurableSet_supercriticalReferenceBoundaryError
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n) :
    MeasurableSet (supercriticalReferenceBoundaryError hk hn) := by
  unfold supercriticalReferenceBoundaryError
  exact MeasurableSet.iUnion fun i ↦
    (measurableSet_supercriticalReferenceBlock hk hn i).symmDiff
      (measurableSet_equalCell i)

/-- Explicit one-dimensional boundary-error estimate. -/
theorem volumeReal_supercriticalReferenceBoundaryError_le
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n) :
    (volume : Measure UnitInterval).real
        (supercriticalReferenceBoundaryError hk hn) ≤
      2 * ((k - 1 : ℕ) : ℝ) ^ 2 / n := by
  calc
    (volume : Measure UnitInterval).real
        (supercriticalReferenceBoundaryError hk hn) ≤
        ∑ i : Fin (k - 1),
          (volume : Measure UnitInterval).real
            (supercriticalReferenceBlock hk hn i ∆ equalCell i) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin (k - 1),
        2 * ((k - 1 : ℕ) : ℝ) / n := by
      apply Finset.sum_le_sum
      intro i _
      calc
        (volume : Measure UnitInterval).real
            (supercriticalReferenceBlock hk hn i ∆ equalCell i) ≤
            |((supercriticalReferenceBlockLeft hk hn i : UnitInterval) : ℝ) -
                ((equalCellLeft i : UnitInterval) : ℝ)| +
              |((supercriticalReferenceBlockRight hk hn i : UnitInterval) : ℝ) -
                ((equalCellRight i : UnitInterval) : ℝ)| :=
          FiniteProfileBlockLayout.measureReal_Ico_symmDiff_le _ _ _ _
        _ ≤ 2 * ((k - 1 : ℕ) : ℝ) / n := by
          have hleft :=
            abs_supercriticalReferenceBlockLeft_sub_equalCellLeft hk hn i
          have hright :=
            abs_supercriticalReferenceBlockRight_sub_equalCellRight hk hn i
          calc
            _ ≤ ((k - 1 : ℕ) : ℝ) / n +
                ((k - 1 : ℕ) : ℝ) / n := add_le_add hleft hright
            _ = 2 * ((k - 1 : ℕ) : ℝ) / n := by ring
    _ = 2 * ((k - 1 : ℕ) : ℝ) ^ 2 / n := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

/-- Two-dimensional set generated by all moved reference-block boundaries. -/
def supercriticalReferenceGraphonError
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n) : Set UnitSquare :=
  let B := supercriticalReferenceBoundaryError hk hn
  (B ×ˢ (Set.univ : Set UnitInterval)) ∪
    ((Set.univ : Set UnitInterval) ×ˢ B)

theorem measurableSet_supercriticalReferenceGraphonError
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n) :
    MeasurableSet (supercriticalReferenceGraphonError hk hn) := by
  unfold supercriticalReferenceGraphonError
  exact ((measurableSet_supercriticalReferenceBoundaryError hk hn).prod
    MeasurableSet.univ).union
      (MeasurableSet.univ.prod
        (measurableSet_supercriticalReferenceBoundaryError hk hn))

theorem unitSquareMeasureReal_supercriticalReferenceGraphonError_le
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n) :
    unitSquareMeasure.real (supercriticalReferenceGraphonError hk hn) ≤
      4 * ((k - 1 : ℕ) : ℝ) ^ 2 / n := by
  let B := supercriticalReferenceBoundaryError hk hn
  have hleft : unitSquareMeasure.real
      (B ×ˢ (Set.univ : Set UnitInterval)) =
        (volume : Measure UnitInterval).real B := by
    simp [Measure.real, unitSquareMeasure]
  have hright : unitSquareMeasure.real
      ((Set.univ : Set UnitInterval) ×ˢ B) =
        (volume : Measure UnitInterval).real B := by
    simp [Measure.real, unitSquareMeasure]
  calc
    unitSquareMeasure.real (supercriticalReferenceGraphonError hk hn) ≤
        unitSquareMeasure.real
            (B ×ˢ (Set.univ : Set UnitInterval)) +
          unitSquareMeasure.real
            ((Set.univ : Set UnitInterval) ×ˢ B) :=
      measureReal_union_le _ _
    _ = 2 * (volume : Measure UnitInterval).real B := by
      rw [hleft, hright]
      ring
    _ ≤ 4 * ((k - 1 : ℕ) : ℝ) ^ 2 / n := by
      have hB := volumeReal_supercriticalReferenceBoundaryError_le hk hn
      change 2 * (volume : Measure UnitInterval).real
          (supercriticalReferenceBoundaryError hk hn) ≤ _
      calc
        2 * (volume : Measure UnitInterval).real
            (supercriticalReferenceBoundaryError hk hn) ≤
            2 * (2 * ((k - 1 : ℕ) : ℝ) ^ 2 / n) :=
          mul_le_mul_of_nonneg_left hB (by norm_num)
        _ = 4 * ((k - 1 : ℕ) : ℝ) ^ 2 / n := by ring

private theorem mem_referenceBlock_of_not_mem_boundaryError
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n)
    {x : UnitInterval} (hx : x ∉ supercriticalReferenceBoundaryError hk hn)
    (i : Fin (k - 1)) (hxi : x ∈ equalCell i) :
    x ∈ supercriticalReferenceBlock hk hn i := by
  by_contra hnot
  apply hx
  apply Set.mem_iUnion.2
  refine ⟨i, ?_⟩
  rw [Set.mem_symmDiff]
  exact Or.inr ⟨hxi, hnot⟩

/-- Quantitative `L¹` convergence estimate for the explicit finite
discretization of `Wstar`. -/
theorem graphonL1Dist_supercriticalReferenceGraphon_Wstar_le
    {k n : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (hn : 0 < n) :
    graphonL1Dist (supercriticalReferenceGraphon k hk γ hγ n)
        (Wstar k hk γ hγ) ≤
      4 * ((k - 1 : ℕ) : ℝ) ^ 2 / n := by
  let R := supercriticalReferenceWeightedGraph k hk γ hγ n
  let S := supercriticalReferenceGraphonError hk hn
  have heq : ∀ᵐ z ∂unitSquareMeasure, z ∉ S →
      supercriticalReferenceGraphon k hk γ hγ n z =
        Wstar k hk γ hγ z := by
    filter_upwards [matrixGraphon_ae_eq_kernel R.weight R.weight_isSymm
        R.nonneg R.le_one,
      matrixGraphon_ae_eq_kernel (WstarMatrix k γ)
        (WstarMatrix_isSymm k γ)
        (WstarMatrix_nonneg hk hγ.1) (WstarMatrix_le_one hk hγ.2),
      ae_mem_iUnion_equalCell_prod hn,
      ae_mem_iUnion_equalCell_prod (show 0 < k - 1 by omega)]
      with z hzR hzW hzFine hzCoarse
    intro hzS
    obtain ⟨vw, hvw⟩ := Set.mem_iUnion.1 hzFine
    obtain ⟨⟨i, j⟩, hij⟩ := Set.mem_iUnion.1 hzCoarse
    have hxB : z.1 ∉ supercriticalReferenceBoundaryError hk hn := by
      intro hx
      apply hzS
      exact Or.inl ⟨hx, Set.mem_univ _⟩
    have hyB : z.2 ∉ supercriticalReferenceBoundaryError hk hn := by
      intro hy
      apply hzS
      exact Or.inr ⟨Set.mem_univ _, hy⟩
    have hxi : z.1 ∈ supercriticalReferenceBlock hk hn i :=
      mem_referenceBlock_of_not_mem_boundaryError hk hn hxB i hij.1
    have hyj : z.2 ∈ supercriticalReferenceBlock hk hn j :=
      mem_referenceBlock_of_not_mem_boundaryError hk hn hyB j hij.2
    have hvi : vw.1 ∈ supercriticalReferencePart k n i :=
      (mem_supercriticalReferencePart_iff_mem_block hk hn i vw.1 hvw.1).2 hxi
    have hwj : vw.2 ∈ supercriticalReferencePart k n j :=
      (mem_supercriticalReferencePart_iff_mem_block hk hn j vw.2 hvw.2).2 hyj
    change matrixGraphon R.weight R.weight_isSymm R.nonneg R.le_one z =
      matrixGraphon (WstarMatrix k γ) (WstarMatrix_isSymm k γ)
        (WstarMatrix_nonneg hk hγ.1) (WstarMatrix_le_one hk hγ.2) z
    rw [hzR, hzW,
      matrixKernel_of_mem R.weight vw.1 vw.2 z hvw.1 hvw.2,
      matrixKernel_of_mem (WstarMatrix k γ) i j z hij.1 hij.2]
    by_cases heqij : i = j
    · subst j
      exact supercriticalReferenceWeightedGraph_weight_of_mem_samePart
        hk hγ i hvi hwj |>.trans (WstarMatrix_apply_self k γ i).symm
    · exact supercriticalReferenceWeightedGraph_weight_of_mem_distinct
        hk hγ heqij hvi hwj |>.trans
          (WstarMatrix_apply_of_ne k γ heqij).symm
  calc
    graphonL1Dist (supercriticalReferenceGraphon k hk γ hγ n)
        (Wstar k hk γ hγ) ≤ unitSquareMeasure.real S :=
      graphonL1Dist_le_measureReal_of_ae_eq_off _ _ S
        (measurableSet_supercriticalReferenceGraphonError hk hn) heq
    _ ≤ 4 * ((k - 1 : ℕ) : ℝ) ^ 2 / n :=
      unitSquareMeasureReal_supercriticalReferenceGraphonError_le hk hn

theorem cutDist_supercriticalReferenceGraphon_Wstar_le
    {k n : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (hn : 0 < n) :
    cutDist (supercriticalReferenceGraphon k hk γ hγ n)
        (Wstar k hk γ hγ) ≤
      4 * ((k - 1 : ℕ) : ℝ) ^ 2 / n :=
  (cutDist_le_graphonL1Dist _ _).trans
    (graphonL1Dist_supercriticalReferenceGraphon_Wstar_le hk hγ hn)

/-- The explicit balanced finite discretization converges to `Wstar`. -/
theorem supercriticalReferenceGraphon_tendsto_Wstar
    {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) :
    Tendsto
      (fun n ↦ cutDist (supercriticalReferenceGraphon k hk γ hγ n)
        (Wstar k hk γ hγ)) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ cutDist_nonneg _ _
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact cutDist_supercriticalReferenceGraphon_Wstar_le hk hγ hn
  · exact tendsto_const_div_atTop_nhds_zero_nat
      (4 * ((k - 1 : ℕ) : ℝ) ^ 2)

end InducedStars
