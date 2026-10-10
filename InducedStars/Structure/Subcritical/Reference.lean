import DenseGraph.FiniteModels.WeightedGraph
import InducedStars.Graphon.FiniteBlockLayouts
import InducedStars.Graphon.BlockEqualization
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Explicit finite references for subcritical candidate graphons

For an admissible block sequence `L`, the finite reference on `Fin n`
samples the *explicit* profile block kernel at the midpoint of each equal
cell.  It does not evaluate an arbitrary representative of the graphon.
Consequently every matrix entry is exactly `0`, `pK k`, or `1`.

The cell finsets below retain the literal component and core-vertex labels
of `L`.  They are the finite coordinates used by the subcritical edit
construction.  The convergence proof compares the full sampled reference
with a fixed finite prefix and then lets the prefix grow; this works for both
finite and infinite admissible sequences.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal unitInterval

namespace InducedStars

/-! ## The sampled full reference -/

/-- Midpoint of the equal interval belonging to `v : Fin n`.  The type of
`v` supplies `0 < n`, so this is always a point of the unit interval. -/
def subcriticalReferenceSamplePoint {n : ℕ} (v : Fin n) : UnitInterval :=
  ⟨(((v : ℕ) : ℝ) + (1 / 2 : ℝ)) / n, by positivity, by
    have hv : (v : ℕ) + 1 ≤ n := Nat.succ_le_iff.mpr v.isLt
    have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt v.isLt)
    apply (div_le_one hn).2
    exact (by exact_mod_cast hv : ((v : ℕ) : ℝ) + 1 ≤ n) |>.trans'
      (by norm_num : (((v : ℕ) : ℝ) + (1 / 2 : ℝ)) ≤
        ((v : ℕ) : ℝ) + 1)⟩

theorem subcriticalReferenceSamplePoint_mem_equalCell {n : ℕ} (v : Fin n) :
    subcriticalReferenceSamplePoint v ∈ equalCell v := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt v.isLt)
  unfold equalCell equalCellLeft equalCellRight
  simp only [Set.mem_Ico]
  constructor
  · change ((v : ℝ) / n ≤
      (((v : ℕ) : ℝ) + (1 / 2 : ℝ)) / n)
    exact (div_le_div_iff_of_pos_right hn).2 (by norm_num)
  · change ((((v : ℕ) : ℝ) + (1 / 2 : ℝ)) / n <
      ((v : ℝ) + 1) / n)
    exact (div_lt_div_iff_of_pos_right hn).2 (by norm_num)

theorem subcriticalReferenceSamplePoint_lt_one {n : ℕ} (v : Fin n) :
    (subcriticalReferenceSamplePoint v : ℝ) < 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt v.isLt)
  have hv : ((v : ℕ) : ℝ) + 1 ≤ n := by
    exact_mod_cast (Nat.succ_le_iff.mpr v.isLt)
  change ((((v : ℕ) : ℝ) + (1 / 2 : ℝ)) / n) < 1
  rw [div_lt_one hn]
  linarith

/-- Full finite weighted reference obtained by sampling the explicit block
kernel.  No tail of the candidate is discarded in this definition. -/
def subcriticalReferenceWeightedGraph
    {k : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k) (n : ℕ) :
    DenseGraph.FiniteWeightedGraph (Fin n) where
  weight x y :=
    L.profileKernel (pK k)
      (subcriticalReferenceSamplePoint x, subcriticalReferenceSamplePoint y)
  symmetric x y := (L.profileKernel_symm (pK k)
    (subcriticalReferenceSamplePoint x, subcriticalReferenceSamplePoint y)).symm
  nonneg x y := (L.profileKernel_mem_Icc (pK_mem_Icc k) _).1
  le_one x y := (L.profileKernel_mem_Icc (pK_mem_Icc k) _).2

/-- Equal-cell graphon of the full sampled reference. -/
def subcriticalReferenceGraphon
    {k : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k) (n : ℕ) :
    Graphon :=
  (subcriticalReferenceWeightedGraph hk L n).toGraphon

theorem subcriticalReferenceWeightedGraph_weight_eq_zero_or_pK_or_one
    {k n : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    (x y : Fin n) :
    (subcriticalReferenceWeightedGraph hk L n).weight x y = 0 ∨
      (subcriticalReferenceWeightedGraph hk L n).weight x y = pK k ∨
      (subcriticalReferenceWeightedGraph hk L n).weight x y = 1 := by
  change L.profileKernel (pK k) _ = 0 ∨
    L.profileKernel (pK k) _ = pK k ∨ L.profileKernel (pK k) _ = 1
  rw [AdmissibleBlockSequence.profileKernel,
    L.profileRecolor_pK_kernel hk]
  exact L.kernel_eq_zero_or_pK_or_one _

/-! ## Literal finite block cells -/

/-- Vertices whose sampling points lie in block `i`. -/
def subcriticalReferenceBlockVertices
    {k : ℕ} (L : AdmissibleBlockSequence k) (n i : ℕ) : Finset (Fin n) :=
  by
    classical
    exact Finset.univ.filter fun x ↦
      subcriticalReferenceSamplePoint x ∈ L.blockInterval i

/-- Vertices whose sampling points lie in the core cell `(i,v)`. -/
def subcriticalReferenceCellVertices
    {k : ℕ} (L : AdmissibleBlockSequence k) (n i : ℕ)
    (v : Fin (L.core i).order) : Finset (Fin n) :=
  by
    classical
    exact Finset.univ.filter fun x ↦
      subcriticalReferenceSamplePoint x ∈ L.blockCell i v

@[simp] theorem mem_subcriticalReferenceBlockVertices
    {k n i : ℕ} {L : AdmissibleBlockSequence k} {x : Fin n} :
    x ∈ subcriticalReferenceBlockVertices L n i ↔
      subcriticalReferenceSamplePoint x ∈ L.blockInterval i := by
  simp [subcriticalReferenceBlockVertices]

@[simp] theorem mem_subcriticalReferenceCellVertices
    {k n i : ℕ} {L : AdmissibleBlockSequence k}
    {v : Fin (L.core i).order} {x : Fin n} :
    x ∈ subcriticalReferenceCellVertices L n i v ↔
      subcriticalReferenceSamplePoint x ∈ L.blockCell i v := by
  simp [subcriticalReferenceCellVertices]

theorem subcriticalReferenceCellVertices_subset_blockVertices
    {k n i : ℕ} (L : AdmissibleBlockSequence k)
    (v : Fin (L.core i).order) :
    subcriticalReferenceCellVertices L n i v ⊆
      subcriticalReferenceBlockVertices L n i := by
  intro x hx
  exact mem_subcriticalReferenceBlockVertices.mpr
    (L.blockCell_subset_interval i v
      (mem_subcriticalReferenceCellVertices.mp hx))

theorem subcriticalReferenceBlockVertices_disjoint
    {k n : ℕ} (L : AdmissibleBlockSequence k) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (subcriticalReferenceBlockVertices L n i)
      (subcriticalReferenceBlockVertices L n j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  exact Set.disjoint_left.mp (L.pairwise_disjoint_blockInterval hij)
    (mem_subcriticalReferenceBlockVertices.mp hxi)
    (mem_subcriticalReferenceBlockVertices.mp hxj)

theorem subcriticalReferenceCellVertices_disjoint_of_ne
    {k n i : ℕ} (L : AdmissibleBlockSequence k)
    {v w : Fin (L.core i).order} (hvw : v ≠ w) :
    Disjoint (subcriticalReferenceCellVertices L n i v)
      (subcriticalReferenceCellVertices L n i w) := by
  rw [Finset.disjoint_left]
  intro x hxv hxw
  exact hvw (L.blockCell_vertex_eq_of_mem
    (mem_subcriticalReferenceCellVertices.mp hxv)
    (mem_subcriticalReferenceCellVertices.mp hxw))

theorem subcriticalReferenceWeightedGraph_weight_of_mem_cells
    {k n i : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    (v w : Fin (L.core i).order) {x y : Fin n}
    (hx : x ∈ subcriticalReferenceCellVertices L n i v)
    (hy : y ∈ subcriticalReferenceCellVertices L n i w) :
    (subcriticalReferenceWeightedGraph hk L n).weight x y =
      profileXiMatrix (pK k) (L.core i) v w := by
  exact L.profileKernel_of_mem hk (pK k) i v w _
    (mem_subcriticalReferenceCellVertices.mp hx)
    (mem_subcriticalReferenceCellVertices.mp hy)

theorem subcriticalReferenceWeightedGraph_weight_of_mem_distinct_blocks
    {k n i j : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    (hij : i ≠ j) {x y : Fin n}
    (hx : x ∈ subcriticalReferenceBlockVertices L n i)
    (hy : y ∈ subcriticalReferenceBlockVertices L n j) :
    (subcriticalReferenceWeightedGraph hk L n).weight x y = 0 := by
  exact L.profileKernel_eq_zero_of_mem_distinct_blocks (pK k) hij _
    (mem_subcriticalReferenceBlockVertices.mp hx)
    (mem_subcriticalReferenceBlockVertices.mp hy)

/-! ## Midpoint-grid interval estimates -/

/-- Midpoint samples which lie in a prescribed half-open interval. -/
def midpointGridIco (n : ℕ) (a b : UnitInterval) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun x ↦ subcriticalReferenceSamplePoint x ∈ Ico a b

@[simp] theorem mem_midpointGridIco {n : ℕ} {a b : UnitInterval} {x : Fin n} :
    x ∈ midpointGridIco n a b ↔ subcriticalReferenceSamplePoint x ∈ Ico a b := by
  simp [midpointGridIco]

/-- A half-open interval of length `b-a` contains at most
`n (b-a) + 1` midpoint samples from the `n`-grid. -/
theorem card_midpointGridIco_le {n : ℕ} (hn : 0 < n)
    (a b : UnitInterval) (hab : a ≤ b) :
    ((midpointGridIco n a b).card : ℝ) ≤
      (n : ℝ) * ((b : ℝ) - (a : ℝ)) + 1 := by
  classical
  let S := midpointGridIco n a b
  by_cases hS : S.Nonempty
  · let lo : Fin n := S.min' hS
    let hi : Fin n := S.max' hS
    have hloMem : lo ∈ S := S.min'_mem hS
    have hhiMem : hi ∈ S := S.max'_mem hS
    have hlohi : lo ≤ hi := S.min'_le_max' hS
    have hsubset : S ⊆ Finset.Icc lo hi := by
      intro x hx
      exact Finset.mem_Icc.mpr ⟨S.min'_le x hx, S.le_max' x hx⟩
    have hcard : S.card ≤ hi.val - lo.val + 1 := by
      calc
        S.card ≤ (Finset.Icc lo hi).card := Finset.card_le_card hsubset
        _ = hi.val + 1 - lo.val := by simp
        _ = hi.val - lo.val + 1 := by omega
    have hlo := (mem_midpointGridIco.mp hloMem).1
    have hhi := (mem_midpointGridIco.mp hhiMem).2
    have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
    change (a : ℝ) ≤
      ((((lo : ℕ) : ℝ) + (1 / 2 : ℝ)) / n) at hlo
    change ((((hi : ℕ) : ℝ) + (1 / 2 : ℝ)) / n) <
      (b : ℝ) at hhi
    have hwidth : (((hi : ℕ) : ℝ) - ((lo : ℕ) : ℝ)) <
        (n : ℝ) * ((b : ℝ) - (a : ℝ)) := by
      have hlo' := (le_div_iff₀ hnℝ).mp hlo
      have hhi' := (div_lt_iff₀ hnℝ).mp hhi
      nlinarith
    have hcast : ((hi.val - lo.val : ℕ) : ℝ) =
        (hi : ℝ) - (lo : ℝ) := by
      rw [Nat.cast_sub (show lo.val ≤ hi.val from hlohi)]
    have hcardR : (S.card : ℝ) ≤ ((hi.val - lo.val : ℕ) : ℝ) + 1 := by
      exact_mod_cast hcard
    rw [hcast] at hcardR
    change (S.card : ℝ) ≤ _
    exact hcardR.trans (by linarith)
  · have hzero : S.card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hS)
    change (S.card : ℝ) ≤ _
    rw [hzero]
    norm_num
    have habR : (a : ℝ) ≤ (b : ℝ) := hab
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity)
      (sub_nonneg.mpr habR)]

/-- The matching lower estimate.  The loss of two grid points accounts for
the two endpoints and is deliberately stated with a safe constant. -/
theorem card_midpointGridIco_ge {n : ℕ} (hn : 0 < n)
    (a b : UnitInterval) (hab : a ≤ b) :
    (n : ℝ) * ((b : ℝ) - (a : ℝ)) - 2 ≤
      ((midpointGridIco n a b).card : ℝ) := by
  classical
  let A := midpointGridIco n (0 : UnitInterval) a
  let C := midpointGridIco n a b
  let B := midpointGridIco n b (1 : UnitInterval)
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro x hxA hxC
    have hxA' := (mem_midpointGridIco.mp hxA).2
    have hxC' := (mem_midpointGridIco.mp hxC).1
    exact (not_le_of_gt hxA') hxC'
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hxA' := (mem_midpointGridIco.mp hxA).2
    have hxB' := (mem_midpointGridIco.mp hxB).1
    have habR : (a : ℝ) ≤ (b : ℝ) := hab
    exact (not_le_of_gt hxA') (habR.trans hxB')
  have hCB : Disjoint C B := by
    rw [Finset.disjoint_left]
    intro x hxC hxB
    have hxC' := (mem_midpointGridIco.mp hxC).2
    have hxB' := (mem_midpointGridIco.mp hxB).1
    exact (not_le_of_gt hxC') hxB'
  have hUnion : A ∪ C ∪ B = (Finset.univ : Finset (Fin n)) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    let z : ℝ := subcriticalReferenceSamplePoint x
    have hz0 : 0 ≤ z := (subcriticalReferenceSamplePoint x).property.1
    have hz1 : z < 1 := subcriticalReferenceSamplePoint_lt_one x
    by_cases hza : z < (a : ℝ)
    · exact Or.inl (Or.inl (mem_midpointGridIco.mpr
        ⟨(show (0 : UnitInterval) ≤ subcriticalReferenceSamplePoint x from hz0),
          (show subcriticalReferenceSamplePoint x < a from hza)⟩))
    · have haz : (a : ℝ) ≤ z := le_of_not_gt hza
      by_cases hzb : z < (b : ℝ)
      · exact Or.inl (Or.inr (mem_midpointGridIco.mpr
          ⟨(show a ≤ subcriticalReferenceSamplePoint x from haz),
            (show subcriticalReferenceSamplePoint x < b from hzb)⟩))
      · exact Or.inr (mem_midpointGridIco.mpr
          ⟨(show b ≤ subcriticalReferenceSamplePoint x from le_of_not_gt hzb),
            (show subcriticalReferenceSamplePoint x < (1 : UnitInterval) from hz1)⟩)
  have hAub := card_midpointGridIco_le hn (0 : UnitInterval) a
    (show (0 : UnitInterval) ≤ a from a.property.1)
  have hBub := card_midpointGridIco_le hn b (1 : UnitInterval)
    (show b ≤ (1 : UnitInterval) from b.property.2)
  have hcard : A.card + C.card + B.card = n := by
    have hACB : Disjoint (A ∪ C) B :=
      Finset.disjoint_union_left.mpr ⟨hAB, hCB⟩
    rw [← Finset.card_union_of_disjoint hAC,
      ← Finset.card_union_of_disjoint hACB, hUnion]
    simp
  change (n : ℝ) * ((b : ℝ) - (a : ℝ)) - 2 ≤ (C.card : ℝ)
  change (A.card : ℝ) ≤ _ at hAub
  change (B.card : ℝ) ≤ _ at hBub
  have hcardR : (A.card : ℝ) + C.card + B.card = n := by
    exact_mod_cast hcard
  norm_num at hAub hBub
  nlinarith

theorem abs_card_midpointGridIco_div_sub_le {n : ℕ} (hn : 0 < n)
    (a b : UnitInterval) (hab : a ≤ b) :
    |((midpointGridIco n a b).card : ℝ) / n -
        ((b : ℝ) - (a : ℝ))| ≤ 2 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hup := card_midpointGridIco_le hn a b hab
  have hlo := card_midpointGridIco_ge hn a b hab
  let c : ℝ := ((midpointGridIco n a b).card : ℝ)
  let d : ℝ := (b : ℝ) - (a : ℝ)
  have hlo' : d - 2 / (n : ℝ) ≤ c / n := by
    apply (le_div_iff₀ hnR).2
    calc
      (d - 2 / (n : ℝ)) * n = (n : ℝ) * d - 2 := by
        field_simp
        <;> ring
      _ ≤ c := by simpa [c, d] using hlo
  have hup' : c / n ≤ d + 1 / (n : ℝ) := by
    apply (div_le_iff₀ hnR).2
    calc
      c ≤ (n : ℝ) * d + 1 := by simpa [c, d] using hup
      _ = (d + 1 / (n : ℝ)) * n := by
        field_simp
        <;> ring
  have honeTwo : 1 / (n : ℝ) ≤ 2 / (n : ℝ) := by
    exact div_le_div_of_nonneg_right (by norm_num) hnR.le
  rw [abs_le]
  constructor
  · change -(2 / (n : ℝ)) ≤ c / n - d
    linarith
  · change c / n - d ≤ 2 / (n : ℝ)
    linarith

theorem card_subcriticalReferenceBlockVertices_le
    {k n i : ℕ} (hn : 0 < n) (L : AdmissibleBlockSequence k) :
    ((subcriticalReferenceBlockVertices L n i).card : ℝ) ≤
      (n : ℝ) * L.alpha i + 1 := by
  simpa [subcriticalReferenceBlockVertices, midpointGridIco,
    AdmissibleBlockSequence.blockInterval,
    AdmissibleBlockSequence.blockEndUI, AdmissibleBlockSequence.blockStartUI,
    AdmissibleBlockSequence.blockEnd] using
    card_midpointGridIco_le hn (L.blockStartUI i) (L.blockEndUI i)
      (show L.blockStartUI i ≤ L.blockEndUI i by
        change L.blockStart i ≤ L.blockEnd i
        simp [AdmissibleBlockSequence.blockEnd, L.alpha_nonneg i])

theorem abs_card_subcriticalReferenceCellVertices_div_sub_le
    {k n i : ℕ} (hn : 0 < n) (L : AdmissibleBlockSequence k)
    (v : Fin (L.core i).order) :
    |((subcriticalReferenceCellVertices L n i v).card : ℝ) / n -
        L.alpha i / (L.core i).order| ≤ 2 / (n : ℝ) := by
  have hle : L.cellLeftUI i v ≤ L.cellRightUI i v := by
    change L.cellLeft i v ≤ L.cellRight i v
    unfold AdmissibleBlockSequence.cellLeft AdmissibleBlockSequence.cellRight
    have hden : (0 : ℝ) < (L.core i).order := by
      exact_mod_cast (L.core i).order_pos
    have hv : (v : ℝ) ≤ (((v : ℕ) + 1 : ℕ) : ℝ) := by norm_num
    have hmul := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hv hden.le) (L.alpha_nonneg i)
    norm_num [Nat.cast_add, Nat.cast_one] at hmul
    simpa [add_comm] using add_le_add_left hmul (L.blockStart i)
  have hbase := abs_card_midpointGridIco_div_sub_le hn
    (L.cellLeftUI i v) (L.cellRightUI i v) hle
  have hwidth :
      L.alpha i * ((((v : ℕ) + 1 : ℕ) : ℝ) / (L.core i).order) -
        L.alpha i * ((v : ℝ) / (L.core i).order) =
          L.alpha i / (L.core i).order := by
    have horder : ((L.core i).order : ℝ) ≠ 0 := by
      exact_mod_cast (L.core i).order_pos.ne'
    field_simp [horder]
    push_cast
    ring
  have hwidthUI :
      ((L.cellRightUI i v : UnitInterval) : ℝ) -
          ((L.cellLeftUI i v : UnitInterval) : ℝ) =
        L.alpha i / (L.core i).order := by
    change L.cellRight i v - L.cellLeft i v = _
    unfold AdmissibleBlockSequence.cellRight AdmissibleBlockSequence.cellLeft
    have horder : ((L.core i).order : ℝ) ≠ 0 := by
      exact_mod_cast (L.core i).order_pos.ne'
    field_simp [horder]
    ring
  rw [hwidthUI] at hbase
  simpa [subcriticalReferenceCellVertices, midpointGridIco,
    AdmissibleBlockSequence.blockCell,
    AdmissibleBlockSequence.cellLeftUI, AdmissibleBlockSequence.cellRightUI,
    AdmissibleBlockSequence.cellLeft, AdmissibleBlockSequence.cellRight] using hbase

/-! ## Retained finite support -/

/-- Block indices retained after imposing a lower mass cutoff and an upper
core-order cutoff.  This finite index set is shared by the reference and the
finite structural division. -/
def subcriticalRetainedBlockIndices
    {k : ℕ} (L : AdmissibleBlockSequence k) (η : ℝ) (R : ℕ) : Finset ℕ :=
  (Finset.range (Nat.ceil (1 / η))).filter fun i ↦
    η ≤ L.alpha i ∧ (L.core i).order ≤ R

@[simp] theorem mem_subcriticalRetainedBlockIndices
    {k i R : ℕ} {L : AdmissibleBlockSequence k} {η : ℝ} :
    i ∈ subcriticalRetainedBlockIndices L η R ↔
      i < Nat.ceil (1 / η) ∧ η ≤ L.alpha i ∧ (L.core i).order ≤ R := by
  simp [subcriticalRetainedBlockIndices]

/-- Union of all literal finite cells whose block index is retained. -/
def subcriticalRetainedVertexSet
    {k n : ℕ} (L : AdmissibleBlockSequence k) (retained : Finset ℕ) : Finset (Fin n) :=
  retained.biUnion fun i ↦
    Finset.univ.biUnion fun v : Fin (L.core i).order ↦
      subcriticalReferenceCellVertices L n i v

@[simp] theorem mem_subcriticalRetainedVertexSet
    {k n : ℕ} {L : AdmissibleBlockSequence k} {retained : Finset ℕ} {x : Fin n} :
    x ∈ subcriticalRetainedVertexSet L retained ↔
      ∃ i ∈ retained, ∃ v : Fin (L.core i).order,
        x ∈ subcriticalReferenceCellVertices L n i v := by
  simp [subcriticalRetainedVertexSet]

/-- Vertices not lying in any retained literal cell. -/
def subcriticalReferenceResidualVertices
    {k n : ℕ} (L : AdmissibleBlockSequence k) (retained : Finset ℕ) : Finset (Fin n) :=
  Finset.univ \ subcriticalRetainedVertexSet L retained

@[simp] theorem mem_subcriticalReferenceResidualVertices
    {k n : ℕ} {L : AdmissibleBlockSequence k} {retained : Finset ℕ} {x : Fin n} :
    x ∈ subcriticalReferenceResidualVertices L retained ↔
      x ∉ subcriticalRetainedVertexSet L retained := by
  simp [subcriticalReferenceResidualVertices]

/-! ## Cell-size convergence -/

/-- Each literal finite core cell has the expected asymptotic proportion. -/
theorem tendsto_card_subcriticalReferenceCellVertices_div
    {k i : ℕ} (L : AdmissibleBlockSequence k)
    (v : Fin (L.core i).order) :
    Tendsto
      (fun n ↦
        ((subcriticalReferenceCellVertices L n i v).card : ℝ) / n)
      atTop (nhds (L.alpha i / (L.core i).order)) := by
  have htwo : Tendsto (fun n : ℕ ↦ (2 : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 2
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero'
    (f := fun n ↦ dist
      (((subcriticalReferenceCellVertices L n i v).card : ℝ) / n)
      (L.alpha i / (L.core i).order))
    (g := fun n : ℕ ↦ (2 : ℝ) / n)
  · exact Eventually.of_forall fun _ ↦ dist_nonneg
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [Real.dist_eq]
    exact abs_card_subcriticalReferenceCellVertices_div_sub_le hn L v
  · exact htwo

/-- Eventually every positive-mass literal core cell contains a midpoint
sample. -/
theorem eventually_subcriticalReferenceCellVertices_nonempty
    {k i : ℕ} (L : AdmissibleBlockSequence k)
    (hi : 0 < L.alpha i) (v : Fin (L.core i).order) :
    ∀ᶠ n in atTop, (subcriticalReferenceCellVertices L n i v).Nonempty := by
  have htarget : 0 < L.alpha i / (L.core i).order := by
    exact div_pos hi (by exact_mod_cast (L.core i).order_pos)
  have hconv := tendsto_card_subcriticalReferenceCellVertices_div L v
  have hev : ∀ᶠ n in atTop,
      L.alpha i / (L.core i).order / 2 <
        ((subcriticalReferenceCellVertices L n i v).card : ℝ) / n := by
    have hopen : Set.Ioi (L.alpha i / (L.core i).order / 2) ∈
        nhds (L.alpha i / (L.core i).order) := by
      exact Ioi_mem_nhds (by linarith)
    exact hconv.eventually hopen
  filter_upwards [hev, eventually_gt_atTop (0 : ℕ)] with n hnpos hn
  apply Finset.card_pos.mp
  have hhalf : 0 < L.alpha i / (L.core i).order / 2 := by positivity
  have hquot : 0 <
      ((subcriticalReferenceCellVertices L n i v).card : ℝ) / n :=
    hhalf.trans hnpos
  have hcardR : 0 <
      ((subcriticalReferenceCellVertices L n i v).card : ℝ) := by
    rcases div_pos_iff.mp hquot with h | h
    · exact h.1
    · exact (not_lt_of_ge (by positivity : (0 : ℝ) ≤ n) h.2).elim
  exact_mod_cast hcardR

/-! ## Sampled tail-block pairs -/

/-- Ordered midpoint pairs which land in one of the block squares with index
at least `N`. -/
def subcriticalReferenceTailPairFinset
    {k : ℕ} (L : AdmissibleBlockSequence k) (n N : ℕ) :
    Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun z ↦
    (subcriticalReferenceSamplePoint z.1,
      subcriticalReferenceSamplePoint z.2) ∈
        FiniteProfileBlockLayout.tailBlockSquares L N

@[simp] theorem mem_subcriticalReferenceTailPairFinset
    {k n N : ℕ} {L : AdmissibleBlockSequence k} {z : Fin n × Fin n} :
    z ∈ subcriticalReferenceTailPairFinset L n N ↔
      (subcriticalReferenceSamplePoint z.1,
        subcriticalReferenceSamplePoint z.2) ∈
          FiniteProfileBlockLayout.tailBlockSquares L N := by
  simp [subcriticalReferenceTailPairFinset]

/-- Pointwise form of membership in the sampled tail: both endpoints lie in
one common block whose index is at least the cutoff. -/
theorem mem_subcriticalReferenceTailPairFinset_iff
    {k n N : ℕ} {L : AdmissibleBlockSequence k} {x y : Fin n} :
    (x, y) ∈ subcriticalReferenceTailPairFinset L n N ↔
      ∃ i : ℕ, N ≤ i ∧
        x ∈ subcriticalReferenceBlockVertices L n i ∧
        y ∈ subcriticalReferenceBlockVertices L n i := by
  rw [mem_subcriticalReferenceTailPairFinset]
  constructor
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨j, hj⟩
    refine ⟨N + j, Nat.le_add_right N j, ?_, ?_⟩
    · exact mem_subcriticalReferenceBlockVertices.mpr hj.1
    · exact mem_subcriticalReferenceBlockVertices.mpr hj.2
  · rintro ⟨i, hi, hxi, hyi⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    apply Set.mem_iUnion.mpr
    exact ⟨j, mem_subcriticalReferenceBlockVertices.mp hxi,
      mem_subcriticalReferenceBlockVertices.mp hyi⟩

/-- For a fixed first endpoint, all sampled tail partners lie in one common
tail block, if such a block exists. -/
theorem card_subcriticalReferenceTailPartners_le
    {k n N : ℕ} (hn : 0 < n) (L : AdmissibleBlockSequence k)
    (x : Fin n) :
    ((Finset.univ.filter fun y : Fin n ↦
        (x, y) ∈ subcriticalReferenceTailPairFinset L n N).card : ℝ) ≤
      (n : ℝ) * L.alpha N + 1 := by
  classical
  by_cases hx : ∃ i : ℕ, N ≤ i ∧
      x ∈ subcriticalReferenceBlockVertices L n i
  · obtain ⟨i, hNi, hxi⟩ := hx
    have hsubset :
        (Finset.univ.filter fun y : Fin n ↦
          (x, y) ∈ subcriticalReferenceTailPairFinset L n N) ⊆
          subcriticalReferenceBlockVertices L n i := by
      intro y hy
      have hpair := (mem_subcriticalReferenceTailPairFinset_iff.mp
        (Finset.mem_filter.mp hy).2)
      obtain ⟨j, _hNj, hxj, hyj⟩ := hpair
      have hij : i = j := by
        by_contra hne
        exact (Finset.disjoint_left.mp
          (subcriticalReferenceBlockVertices_disjoint L hne)) hxi hxj
      simpa [hij] using hyj
    have hcard :
        ((Finset.univ.filter fun y : Fin n ↦
          (x, y) ∈ subcriticalReferenceTailPairFinset L n N).card : ℝ) ≤
          (subcriticalReferenceBlockVertices L n i).card := by
      exact_mod_cast Finset.card_le_card hsubset
    have hblock := card_subcriticalReferenceBlockVertices_le hn L (i := i)
    have hmono := L.alpha_antitone hNi
    calc
      _ ≤ ((subcriticalReferenceBlockVertices L n i).card : ℝ) := hcard
      _ ≤ (n : ℝ) * L.alpha i + 1 := hblock
      _ ≤ (n : ℝ) * L.alpha N + 1 := by
        gcongr
  · have hempty :
        (Finset.univ.filter fun y : Fin n ↦
          (x, y) ∈ subcriticalReferenceTailPairFinset L n N) = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨y, hy⟩
      obtain ⟨i, hi, hxi, _⟩ := mem_subcriticalReferenceTailPairFinset_iff.mp
        (Finset.mem_filter.mp hy).2
      exact hx ⟨i, hi, hxi⟩
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    nlinarith [L.alpha_nonneg N]

/-- The normalized number of midpoint pairs in the discarded tail is at
most `alpha N + 1/n`.  Unlike summing independent rounding errors over all
tail blocks, this row-wise bound is uniform for countably many blocks. -/
theorem subcriticalReferenceTailPairProportion_le
    {k n N : ℕ} (hn : 0 < n) (L : AdmissibleBlockSequence k) :
    (1 / (n : ℝ)) ^ 2 *
        (subcriticalReferenceTailPairFinset L n N).card ≤
      L.alpha N + 1 / (n : ℝ) := by
  classical
  have hrows :
      ((subcriticalReferenceTailPairFinset L n N).card : ℝ) ≤
        (n : ℝ) * ((n : ℝ) * L.alpha N + 1) := by
    have hcardNat :
        (subcriticalReferenceTailPairFinset L n N).card =
          ∑ x : Fin n,
            (Finset.univ.filter fun y : Fin n ↦
              (x, y) ∈ subcriticalReferenceTailPairFinset L n N).card := by
      let tail := subcriticalReferenceTailPairFinset L n N
      have hmaps : (tail : Set (Fin n × Fin n)).MapsTo Prod.fst
          (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)) := by
        intro z hz
        simp
      have hfiber (x : Fin n) :
          (tail.filter fun z ↦ z.1 = x).card =
            (Finset.univ.filter fun y : Fin n ↦ (x, y) ∈ tail).card := by
        apply Finset.card_bij (fun z _ ↦ z.2)
        · intro z hz
          have hz' := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            have hzEq : (x, z.2) = z := by
              apply Prod.ext
              · exact hz'.2.symm
              · rfl
            simpa [hzEq] using hz'.1⟩
        · intro z₁ hz₁ z₂ hz₂ heq
          apply Prod.ext
          · exact (Finset.mem_filter.mp hz₁).2.trans
              (Finset.mem_filter.mp hz₂).2.symm
          · exact heq
        · intro y hy
          have hy' := Finset.mem_filter.mp hy
          refine ⟨(x, y), Finset.mem_filter.mpr ⟨hy'.2, rfl⟩, rfl⟩
      calc
        tail.card = ∑ x ∈ (Finset.univ : Finset (Fin n)),
            (tail.filter fun z ↦ z.1 = x).card :=
          Finset.card_eq_sum_card_fiberwise hmaps
        _ = ∑ x ∈ (Finset.univ : Finset (Fin n)),
            (Finset.univ.filter fun y : Fin n ↦ (x, y) ∈ tail).card := by
              apply Finset.sum_congr rfl
              intro x _
              exact hfiber x
        _ = ∑ x : Fin n,
            (Finset.univ.filter fun y : Fin n ↦ (x, y) ∈ tail).card := by simp
    rw [hcardNat, Nat.cast_sum]
    calc
      ∑ x : Fin n,
          ((Finset.univ.filter fun y : Fin n ↦
            (x, y) ∈ subcriticalReferenceTailPairFinset L n N).card : ℝ)
          ≤ ∑ _x : Fin n, ((n : ℝ) * L.alpha N + 1) := by
            exact Finset.sum_le_sum fun x _ ↦
              card_subcriticalReferenceTailPartners_le hn L x
      _ = (n : ℝ) * ((n : ℝ) * L.alpha N + 1) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (1 / (n : ℝ)) ^ 2 *
        (subcriticalReferenceTailPairFinset L n N).card
        ≤ (1 / (n : ℝ)) ^ 2 *
          ((n : ℝ) * ((n : ℝ) * L.alpha N + 1)) := by
            gcongr
    _ = L.alpha N + 1 / (n : ℝ) := by field_simp <;> ring

end InducedStars
