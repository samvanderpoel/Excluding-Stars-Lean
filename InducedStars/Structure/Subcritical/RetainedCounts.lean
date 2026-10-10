import InducedStars.Structure.Subcritical.RetainedEdges
import InducedStars.Structure.Subcritical.SparseSide
import DenseGraph.FiniteModels.FixedCardinalityBlocks
import InducedStars.FiniteModels.GraphFamilies

/-!
# Retained edge-count levels and partition functions

Paper: the counting introduction preceding
`lemma:SubCompareSparseSideEdgesK1k` and
`eqn:clean-partition-function-K1k`. The vector here is `𝒎`, not the later
root/row/tail profile `𝔭`. All constructions are finite counting objects;
no probability law or partition-function comparison is introduced.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- A coarse uniform bound on the active coordinate count, independent of
the graph order and candidate representation. Each coordinate injects into
an ordered pair of retained parts. -/
theorem card_retainedActivePair_le_sq_retainedParts
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    Fintype.card (RetainedActivePair D eta R₀) ≤ (D.retainedPartIndices eta R₀).card^2 := by
  let f : RetainedActivePair D eta R₀ →
      {a : D.PartIndex // a ∈ D.retainedPartIndices eta R₀} ×
        {a : D.PartIndex // a ∈ D.retainedPartIndices eta R₀} := fun e ↦
    (⟨e.leftPart, e.leftPart_mem_retained⟩, ⟨e.rightPart, e.rightPart_mem_retained⟩)
  have hf : Function.Injective f := by
    intro e g h
    exact RetainedActivePair.eq_of_parts
      (congrArg (fun z ↦ z.1.val) h) (congrArg (fun z ↦ z.2.val) h)
  simpa only [Fintype.card_prod, Fintype.card_coe, pow_two] using Fintype.card_le_of_injective f hf

theorem eta_sq_mul_card_retainedActivePair_le
    (D : SubcriticalDivision k V) {eta : ℝ} (R₀ : ℕ) (heta : 0 ≤ eta) :
    eta^2 * Fintype.card (RetainedActivePair D eta R₀) ≤ (R₀ : ℝ)^2 := by
  have hcard : (Fintype.card (RetainedActivePair D eta R₀) : ℝ) ≤
      ((D.retainedPartIndices eta R₀).card : ℝ)^2 := by
    exact_mod_cast card_retainedActivePair_le_sq_retainedParts D eta R₀
  have hm := mul_le_mul_of_nonneg_left hcard (sq_nonneg eta)
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ eta * (D.retainedPartIndices eta R₀).card)
    (D.eta_mul_card_retainedPartIndices_le R₀ heta) 2
  nlinarith

theorem card_retainedActivePair_le_uniform
    (D : SubcriticalDivision k V) {eta : ℝ} (R₀ : ℕ) (heta : 0 < eta) :
    (Fintype.card (RetainedActivePair D eta R₀) : ℝ) ≤ (R₀ : ℝ)^2 / eta^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos heta)).mpr
  simpa only [mul_comm] using eta_sq_mul_card_retainedActivePair_le D R₀ heta.le

/-- The finite independent choices of exactly the prescribed number of
unordered edges in each retained active block. Only the finite-choice
interface of the existing block model is used. -/
def retainedEdgeChoiceModel {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (v : RetainedEdgeCountVector D eta R₀) :
    DenseGraph.FixedCardinalityBlockModel (RetainedActivePair D eta R₀) (Sym2 V) where
  block := retainedActivePotentialEdges D eta R₀
  pairwiseDisjoint := fun e _ f _ hef ↦ retainedActivePotentialEdges_disjoint D eta R₀ hef
  quota := v.count
  quota_le e := by
    rw [retainedActivePotentialEdges_card]
    exact v.count_le_capacity e

abbrev RetainedEdgeChoices {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (v : RetainedEdgeCountVector D eta R₀) := (retainedEdgeChoiceModel v).Sample

/-- The exact multiplicity `∏ e, choose N_e m_e` counts the actual finite
block choices, including the single empty choice when there are no indices. -/
theorem retainedEdgeChoices_card {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (v : RetainedEdgeCountVector D eta R₀) :
    Fintype.card (RetainedEdgeChoices v) = retainedEdgeCountMultiplicity v := by
  calc
    Fintype.card (RetainedEdgeChoices v) =
        (retainedEdgeChoiceModel v).sampleSpaceCard :=
      (retainedEdgeChoiceModel v).card_sample
    _ = retainedEdgeCountMultiplicity v := by
      simp only [DenseGraph.FixedCardinalityBlockModel.sampleSpaceCard,
        retainedEdgeChoiceModel, retainedActivePotentialEdges_card,
        retainedEdgeCountMultiplicity]

/-- The zero vector always exists; this asserts no density-level feasibility. -/
def zeroRetainedEdgeCountVector (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    RetainedEdgeCountVector D eta R₀ where
  count _ := 0
  count_le_capacity _ := Nat.zero_le _

theorem retainedEdgeCountVector_eq_zero_of_isEmpty
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    [IsEmpty (RetainedActivePair D eta R₀)] (v : RetainedEdgeCountVector D eta R₀) :
    v = zeroRetainedEdgeCountVector D eta R₀ := by
  apply RetainedEdgeCountVector.ext
  funext e
  exact isEmptyElim e

theorem retainedEdgeCountVector_card_of_isEmpty
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    [IsEmpty (RetainedActivePair D eta R₀)] :
    Fintype.card (RetainedEdgeCountVector D eta R₀) = 1 := by
  letI : Unique (RetainedEdgeCountVector D eta R₀) :=
    ⟨⟨zeroRetainedEdgeCountVector D eta R₀⟩, retainedEdgeCountVector_eq_zero_of_isEmpty⟩
  exact Fintype.card_unique

@[simp] theorem retainedEdgeCountTotal_of_isEmpty
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    [IsEmpty (RetainedActivePair D eta R₀)] (v : RetainedEdgeCountVector D eta R₀) :
    retainedEdgeCountTotal v = 0 := by simp [retainedEdgeCountTotal]

@[simp] theorem retainedEdgeCountMultiplicity_of_isEmpty
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    [IsEmpty (RetainedActivePair D eta R₀)] (v : RetainedEdgeCountVector D eta R₀) :
    retainedEdgeCountMultiplicity v = 1 := by simp [retainedEdgeCountMultiplicity]

/-- The unique signed shift compatible with a total edge count and a vector. -/
def retainedLevelShift {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (m : ℕ) (v : RetainedEdgeCountVector D eta R₀) : ℤ :=
  (m : ℤ) - (retainedCliqueCapacity D eta R₀ : ℤ) - (retainedEdgeCountTotal v : ℤ)

theorem retainedLevelShift_identity {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (m : ℕ) (v : RetainedEdgeCountVector D eta R₀) :
    (retainedCliqueCapacity D eta R₀ : ℤ) + (retainedEdgeCountTotal v : ℤ) +
      retainedLevelShift m v = (m : ℤ) := by
  unfold retainedLevelShift
  omega

/-- The wide level `𝓜_{Π,u}`, with the exact integer edge equation. -/
def retainedEdgeCountLevel (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m : ℕ)
    (delta : ℝ) (u : ℤ) : Finset (RetainedEdgeCountVector D eta R₀) :=
  Finset.univ.filter fun v ↦
    (retainedCliqueCapacity D eta R₀ : ℤ) + (retainedEdgeCountTotal v : ℤ) + u = (m : ℤ) ∧
      ∀ e, pK k - 2 * delta ≤ retainedEdgeCountDensity v e ∧
        retainedEdgeCountDensity v e ≤ pK k + 2 * delta

/-- The narrow level `𝓜^nar_{Π,u}` uses `pK k ± delta`. -/
def retainedNarrowEdgeCountLevel (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m : ℕ)
    (delta : ℝ) (u : ℤ) : Finset (RetainedEdgeCountVector D eta R₀) :=
  Finset.univ.filter fun v ↦
    (retainedCliqueCapacity D eta R₀ : ℤ) + (retainedEdgeCountTotal v : ℤ) + u = (m : ℤ) ∧
      ∀ e, pK k - delta ≤ retainedEdgeCountDensity v e ∧
        retainedEdgeCountDensity v e ≤ pK k + delta

@[simp] theorem mem_retainedEdgeCountLevel
    {D : SubcriticalDivision k V} {eta delta : ℝ} {R₀ m : ℕ} {u : ℤ}
    {v : RetainedEdgeCountVector D eta R₀} :
    v ∈ retainedEdgeCountLevel D eta R₀ m delta u ↔
      (retainedCliqueCapacity D eta R₀ : ℤ) + (retainedEdgeCountTotal v : ℤ) + u = (m : ℤ) ∧
        ∀ e, pK k - 2 * delta ≤ retainedEdgeCountDensity v e ∧
          retainedEdgeCountDensity v e ≤ pK k + 2 * delta := by
  simp [retainedEdgeCountLevel]

@[simp] theorem mem_retainedNarrowEdgeCountLevel
    {D : SubcriticalDivision k V} {eta delta : ℝ} {R₀ m : ℕ} {u : ℤ}
    {v : RetainedEdgeCountVector D eta R₀} :
    v ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta u ↔
      (retainedCliqueCapacity D eta R₀ : ℤ) + (retainedEdgeCountTotal v : ℤ) + u = (m : ℤ) ∧
        ∀ e, pK k - delta ≤ retainedEdgeCountDensity v e ∧
          retainedEdgeCountDensity v e ≤ pK k + delta := by
  simp [retainedNarrowEdgeCountLevel]

theorem retainedNarrowEdgeCountLevel_subset (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ m : ℕ) {delta : ℝ} (hdelta : 0 ≤ delta) (u : ℤ) :
    retainedNarrowEdgeCountLevel D eta R₀ m delta u ⊆
      retainedEdgeCountLevel D eta R₀ m delta u := by
  intro v hv
  obtain ⟨hid, hdensity⟩ := mem_retainedNarrowEdgeCountLevel.mp hv
  refine mem_retainedEdgeCountLevel.mpr ⟨hid, ?_⟩
  intro e
  obtain ⟨hl, hu⟩ := hdensity e
  constructor <;> linarith

theorem retainedLevelShift_eq_of_mem_narrowLevel
    {D : SubcriticalDivision k V} {eta delta : ℝ} {R₀ m : ℕ} {u : ℤ}
    {v : RetainedEdgeCountVector D eta R₀}
    (hv : v ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta u) :
    retainedLevelShift m v = u := by
  have h := (mem_retainedNarrowEdgeCountLevel.mp hv).1
  unfold retainedLevelShift
  omega

/-- The complete narrow window, implemented as a finite filter using the
unique shift. At the paper-facing applications `C` is exactly
`subcriticalSparseSideConstant k`. No nonemptiness or nonnegative-shift
assumption is made. -/
def retainedNarrowEdgeCountWindow (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m : ℕ)
    (C delta epsilon : ℝ) : Finset (RetainedEdgeCountVector D eta R₀) :=
  Finset.univ.filter fun v ↦
    v ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta (retainedLevelShift m v) ∧
      -2 * epsilon * (Fintype.card V : ℝ)^2 ≤ (retainedLevelShift m v : ℝ) ∧
        (retainedLevelShift m v : ℝ) ≤
          C * eta * (Fintype.card V : ℝ)^2 + 2 * epsilon * (Fintype.card V : ℝ)^2

@[simp] theorem mem_retainedNarrowEdgeCountWindow
    {D : SubcriticalDivision k V} {eta C delta epsilon : ℝ} {R₀ m : ℕ}
    {v : RetainedEdgeCountVector D eta R₀} :
    v ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon ↔
      v ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta (retainedLevelShift m v) ∧
        -2 * epsilon * (Fintype.card V : ℝ)^2 ≤ (retainedLevelShift m v : ℝ) ∧
          (retainedLevelShift m v : ℝ) ≤
            C * eta * (Fintype.card V : ℝ)^2 + 2 * epsilon * (Fintype.card V : ℝ)^2 := by
  simp only [retainedNarrowEdgeCountWindow, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_retainedNarrowEdgeCountWindow_of_mem_level
    {D : SubcriticalDivision k V} {eta C delta epsilon : ℝ} {R₀ m : ℕ} {u : ℤ}
    {v : RetainedEdgeCountVector D eta R₀}
    (hv : v ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta u)
    (hlo : -2 * epsilon * (Fintype.card V : ℝ)^2 ≤ (u : ℝ))
    (hhi : (u : ℝ) ≤
      C * eta * (Fintype.card V : ℝ)^2 + 2 * epsilon * (Fintype.card V : ℝ)^2) :
    v ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon := by
  apply mem_retainedNarrowEdgeCountWindow.mpr
  rw [retainedLevelShift_eq_of_mem_narrowLevel hv]
  exact ⟨hv, hlo, hhi⟩

/-- `Z_Π(u)`, a natural-valued finite sum over the wide level. -/
def retainedPartitionFunction (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m : ℕ)
    (delta : ℝ) (u : ℤ) : ℕ :=
  ∑ v ∈ retainedEdgeCountLevel D eta R₀ m delta u, retainedEdgeCountMultiplicity v

/-- `Z^nar_Π(u)`, with no feasibility assumption. -/
def retainedNarrowPartitionFunction (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m : ℕ)
    (delta : ℝ) (u : ℤ) : ℕ :=
  ∑ v ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta u, retainedEdgeCountMultiplicity v

theorem retainedNarrowPartitionFunction_le (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ m : ℕ) {delta : ℝ} (hdelta : 0 ≤ delta) (u : ℤ) :
    retainedNarrowPartitionFunction D eta R₀ m delta u ≤
      retainedPartitionFunction D eta R₀ m delta u := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (retainedNarrowEdgeCountLevel_subset D eta R₀ m hdelta u) (fun _ _ _ ↦ Nat.zero_le _)

theorem retainedPartitionFunction_eq_zero_of_empty
    {D : SubcriticalDivision k V} {eta delta : ℝ} {R₀ m : ℕ} {u : ℤ}
    (h : retainedEdgeCountLevel D eta R₀ m delta u = ∅) :
    retainedPartitionFunction D eta R₀ m delta u = 0 := by
  simp [retainedPartitionFunction, h]

theorem retainedNarrowPartitionFunction_eq_zero_of_empty
    {D : SubcriticalDivision k V} {eta delta : ℝ} {R₀ m : ℕ} {u : ℤ}
    (h : retainedNarrowEdgeCountLevel D eta R₀ m delta u = ∅) :
    retainedNarrowPartitionFunction D eta R₀ m delta u = 0 := by
  simp [retainedNarrowPartitionFunction, h]

theorem retainedEdgeCountMultiplicity_le_partitionFunction
    {D : SubcriticalDivision k V} {eta delta : ℝ} {R₀ m : ℕ} {u : ℤ}
    {v : RetainedEdgeCountVector D eta R₀}
    (hv : v ∈ retainedEdgeCountLevel D eta R₀ m delta u) :
    retainedEdgeCountMultiplicity v ≤ retainedPartitionFunction D eta R₀ m delta u :=
  Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hv

theorem retainedEdgeCountMultiplicity_le_narrowPartitionFunction
    {D : SubcriticalDivision k V} {eta delta : ℝ} {R₀ m : ℕ} {u : ℤ}
    {v : RetainedEdgeCountVector D eta R₀}
    (hv : v ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta u) :
    retainedEdgeCountMultiplicity v ≤ retainedNarrowPartitionFunction D eta R₀ m delta u :=
  Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hv

/-- Paper: equation `eqn:clean-partition-function-K1k`. The remainder count
is the labeled induced-star-free count on `Fin s`, not the count of all
graphs. The cutoff is the explicit natural floor of `C*eta*n^2`. -/
def cleanRetainedPartitionFunction (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m : ℕ)
    (delta : ℝ) : ℕ :=
  ∑ b ∈ Finset.range (Nat.floor
      (subcriticalSparseSideConstant k * eta * (Fintype.card V : ℝ)^2) + 1),
    inducedStarFreeGraphCountWithEdges k (D.nonretainedVertices eta R₀).card b *
      retainedPartitionFunction D eta R₀ m delta (b : ℤ)

theorem cleanRetainedPartitionFunction_eq_sum
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) :
    cleanRetainedPartitionFunction D eta R₀ m delta =
      ∑ b ∈ Finset.range (Nat.floor
          (subcriticalSparseSideConstant k * eta * (Fintype.card V : ℝ)^2) + 1),
        inducedStarFreeGraphCountWithEdges k (D.nonretainedVertices eta R₀).card b *
          retainedPartitionFunction D eta R₀ m delta (b : ℤ) := rfl

theorem mem_cleanRetainedPartitionFunction_cutoff
    (D : SubcriticalDivision k V) (eta : ℝ)
    (hcutoff : 0 ≤ subcriticalSparseSideConstant k * eta * (Fintype.card V : ℝ)^2)
    (b : ℕ) :
    b ∈ Finset.range (Nat.floor
        (subcriticalSparseSideConstant k * eta * (Fintype.card V : ℝ)^2) + 1) ↔
      (b : ℝ) ≤ subcriticalSparseSideConstant k * eta * (Fintype.card V : ℝ)^2 := by
  rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hcutoff]

end InducedStars
