import InducedStars.Structure.Subcritical.ClosenessResult
import Mathlib.Order.Interval.Finset.Fin

/-!
# Retained components and the nonretained side

Paper: the counting-argument introduction in `paper/subcritical.tex`.
Retained components are selected by their actual support size and core order,
not by their position in an arbitrary representation.  The division remainder
`D.sparse` is generally smaller than the full nonretained side.
-/

noncomputable section

open Finset Set
open scoped BigOperators Classical

namespace InducedStars
namespace SubcriticalDivision

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The components with support at least `eta * |V|` and core order at most `R₀`. -/
def retainedComponentIndices (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    Finset (Fin D.componentCount) :=
  Finset.univ.filter fun i ↦
    eta * Fintype.card V ≤ (D.componentSupport i).card ∧ (D.core i).order ≤ R₀

def retainedComponentCount (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) : ℕ :=
  (D.retainedComponentIndices eta R₀).card

/-- All parts of retained components; the family is allowed to be empty. -/
def retainedPartIndices (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    Finset D.PartIndex :=
  (D.retainedComponentIndices eta R₀).sigma fun i ↦ Finset.univ

def retainedVertices (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) : Finset V :=
  (D.retainedComponentIndices eta R₀).biUnion D.componentSupport

/-- The complement of all retained components, not merely `D.sparse`. -/
def nonretainedVertices (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) : Finset V :=
  Finset.univ \ D.retainedVertices eta R₀

def nonretainedVisibleVertices (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta : ℝ) : Finset V :=
  (D.visibleComponentIndices theta \ D.retainedComponentIndices eta R₀).biUnion
    D.componentSupport

def nonretainedSmallVertices (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta : ℝ) : Finset V :=
  D.nonretainedVertices eta R₀ \ D.nonretainedVisibleVertices eta R₀ theta

@[simp] theorem mem_retainedComponentIndices (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (i : Fin D.componentCount) :
    i ∈ D.retainedComponentIndices eta R₀ ↔
      eta * Fintype.card V ≤ (D.componentSupport i).card ∧ (D.core i).order ≤ R₀ := by
  simp [retainedComponentIndices]

@[simp] theorem mem_retainedPartIndices (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (a : D.PartIndex) :
    a ∈ D.retainedPartIndices eta R₀ ↔ a.1 ∈ D.retainedComponentIndices eta R₀ := by
  simp [retainedPartIndices]

@[simp] theorem mem_retainedVertices (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (v : V) :
    v ∈ D.retainedVertices eta R₀ ↔
      ∃ i ∈ D.retainedComponentIndices eta R₀, v ∈ D.componentSupport i := by
  simp [retainedVertices]

@[simp] theorem mem_nonretainedVertices (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (v : V) :
    v ∈ D.nonretainedVertices eta R₀ ↔ v ∉ D.retainedVertices eta R₀ := by
  simp [nonretainedVertices]

@[simp] theorem mem_nonretainedVisibleVertices (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta : ℝ) (v : V) :
    v ∈ D.nonretainedVisibleVertices eta R₀ theta ↔
      ∃ i, i ∈ D.visibleComponentIndices theta ∧
        i ∉ D.retainedComponentIndices eta R₀ ∧ v ∈ D.componentSupport i := by
  simp [nonretainedVisibleVertices, and_assoc]

@[simp] theorem mem_nonretainedSmallVertices (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta : ℝ) (v : V) :
    v ∈ D.nonretainedSmallVertices eta R₀ theta ↔
      v ∈ D.nonretainedVertices eta R₀ ∧
        v ∉ D.nonretainedVisibleVertices eta R₀ theta := by
  simp [nonretainedSmallVertices]

theorem mem_componentSupport_unique (D : SubcriticalDivision k V)
    {i j : Fin D.componentCount} {v : V}
    (hi : v ∈ D.componentSupport i) (hj : v ∈ D.componentSupport j) : i = j := by
  by_contra h
  exact Finset.disjoint_left.mp (D.componentSupport_disjoint h) hi hj

theorem mem_retainedVertices_iff_of_mem_componentSupport
    (D : SubcriticalDivision k V) {eta : ℝ} {R₀ : ℕ}
    {i : Fin D.componentCount} {v : V} (hv : v ∈ D.componentSupport i) :
    v ∈ D.retainedVertices eta R₀ ↔ i ∈ D.retainedComponentIndices eta R₀ := by
  constructor
  · rintro h
    obtain ⟨j, hj, hvj⟩ := (D.mem_retainedVertices eta R₀ v).mp h
    rwa [D.mem_componentSupport_unique hv hvj]
  · intro hi
    exact (D.mem_retainedVertices eta R₀ v).mpr ⟨i, hi, hv⟩

theorem retainedVertices_subset_support (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) : D.retainedVertices eta R₀ ⊆ D.support := by
  intro v hv
  obtain ⟨i, _, hi⟩ := (D.mem_retainedVertices eta R₀ v).mp hv
  exact D.componentSupport_subset_support i hi

theorem sparse_subset_nonretainedVertices (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) : D.sparse ⊆ D.nonretainedVertices eta R₀ := by
  intro v hv
  exact (D.mem_nonretainedVertices eta R₀ v).mpr fun h ↦
    (mem_sparse.mp hv) (D.retainedVertices_subset_support eta R₀ h)

theorem retainedVertices_eq_part_union (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) :
    D.retainedVertices eta R₀ = (D.retainedPartIndices eta R₀).biUnion D.part := by
  ext v
  simp only [mem_retainedVertices, mem_componentSupport, Finset.mem_biUnion,
    mem_retainedPartIndices]
  constructor
  · rintro ⟨i, hi, j, hj⟩
    exact ⟨⟨i, j⟩, hi, hj⟩
  · rintro ⟨⟨i, j⟩, hi, hj⟩
    exact ⟨i, hi, j, hj⟩

theorem part_subset_retainedVertices (D : SubcriticalDivision k V)
    {eta : ℝ} {R₀ : ℕ} {a : D.PartIndex}
    (ha : a ∈ D.retainedPartIndices eta R₀) :
    D.part a ⊆ D.retainedVertices eta R₀ := by
  intro v hv
  exact (D.mem_retainedVertices eta R₀ v).mpr
    ⟨a.1, (D.mem_retainedPartIndices eta R₀ a).mp ha,
      mem_componentSupport.mpr ⟨a.2, hv⟩⟩

@[simp] theorem retainedVertices_union_nonretainedVertices
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    D.retainedVertices eta R₀ ∪ D.nonretainedVertices eta R₀ = Finset.univ := by
  ext v
  by_cases h : v ∈ D.retainedVertices eta R₀ <;> simp [h]

theorem retainedVertices_disjoint_nonretainedVertices
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    Disjoint (D.retainedVertices eta R₀) (D.nonretainedVertices eta R₀) :=
  Finset.disjoint_left.mpr fun _ hv hs ↦
    ((D.mem_nonretainedVertices eta R₀ _).mp hs) hv

theorem card_retainedVertices (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    (D.retainedVertices eta R₀).card =
      ∑ i ∈ D.retainedComponentIndices eta R₀, (D.componentSupport i).card := by
  rw [retainedVertices, Finset.card_biUnion]
  intro i _ j _ hij
  exact D.componentSupport_disjoint hij

theorem card_retainedPartIndices (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    (D.retainedPartIndices eta R₀).card =
      ∑ i ∈ D.retainedComponentIndices eta R₀, (D.core i).order := by
  simp [retainedPartIndices, Finset.card_sigma]

theorem card_retainedVertices_eq_sum_parts (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) :
    (D.retainedVertices eta R₀).card =
      ∑ a ∈ D.retainedPartIndices eta R₀, (D.part a).card := by
  rw [D.retainedVertices_eq_part_union, Finset.card_biUnion]
  intro a _ b _ hab
  exact D.part_disjoint hab

theorem card_retained_add_nonretained (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) :
    (D.retainedVertices eta R₀).card + (D.nonretainedVertices eta R₀).card =
      Fintype.card V := by
  rw [← Finset.card_union_of_disjoint (D.retainedVertices_disjoint_nonretainedVertices eta R₀)]
  simp

theorem nonretainedVisibleVertices_subset_nonretainedVertices
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta : ℝ) :
    D.nonretainedVisibleVertices eta R₀ theta ⊆ D.nonretainedVertices eta R₀ := by
  intro v hv
  obtain ⟨i, _, hi, hv⟩ := (D.mem_nonretainedVisibleVertices eta R₀ theta v).mp hv
  exact (D.mem_nonretainedVertices eta R₀ v).mpr fun h ↦
    hi ((D.mem_retainedVertices_iff_of_mem_componentSupport hv).mp h)

theorem nonretainedVisible_union_small (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta : ℝ) :
    D.nonretainedVisibleVertices eta R₀ theta ∪
      D.nonretainedSmallVertices eta R₀ theta = D.nonretainedVertices eta R₀ := by
  exact Finset.union_sdiff_of_subset
    (D.nonretainedVisibleVertices_subset_nonretainedVertices eta R₀ theta)

theorem nonretainedVisible_disjoint_small (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta : ℝ) :
    Disjoint (D.nonretainedVisibleVertices eta R₀ theta)
      (D.nonretainedSmallVertices eta R₀ theta) := by
  exact Finset.disjoint_left.mpr fun _ hv hs ↦
    ((D.mem_nonretainedSmallVertices eta R₀ theta _).mp hs).2 hv

theorem card_nonretainedVisible_add_small (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta : ℝ) :
    (D.nonretainedVisibleVertices eta R₀ theta).card +
      (D.nonretainedSmallVertices eta R₀ theta).card =
        (D.nonretainedVertices eta R₀).card := by
  rw [← Finset.card_union_of_disjoint (D.nonretainedVisible_disjoint_small eta R₀ theta),
    D.nonretainedVisible_union_small]

/-- The alternative paper description is valid once retained components
have been proved visible. -/
theorem mem_nonretainedSmallVertices_iff
    (D : SubcriticalDivision k V) {eta theta : ℝ} {R₀ : ℕ}
    (hvis : D.retainedComponentIndices eta R₀ ⊆ D.visibleComponentIndices theta)
    (v : V) :
    v ∈ D.nonretainedSmallVertices eta R₀ theta ↔
      v ∈ D.sparse ∨ ∃ i, i ∉ D.visibleComponentIndices theta ∧
        v ∈ D.componentSupport i := by
  constructor
  · intro hv
    obtain ⟨hret, hlg⟩ := (D.mem_nonretainedSmallVertices eta R₀ theta v).mp hv
    by_cases hs : v ∈ D.support
    · obtain ⟨i, j, hj⟩ := mem_support_iff.mp hs
      have hi : v ∈ D.componentSupport i := mem_componentSupport.mpr ⟨j, hj⟩
      refine Or.inr ⟨i, ?_, hi⟩
      intro hvi
      have hnret : i ∉ D.retainedComponentIndices eta R₀ := fun h ↦
        ((D.mem_nonretainedVertices eta R₀ v).mp hret)
          ((D.mem_retainedVertices_iff_of_mem_componentSupport hi).mpr h)
      exact hlg ((D.mem_nonretainedVisibleVertices eta R₀ theta v).mpr
        ⟨i, hvi, hnret, hi⟩)
    · exact Or.inl (mem_sparse.mpr hs)
  · rintro (hs | ⟨i, hi, hvi⟩)
    · refine (D.mem_nonretainedSmallVertices eta R₀ theta v).mpr
        ⟨D.sparse_subset_nonretainedVertices eta R₀ hs, ?_⟩
      intro hlg
      obtain ⟨i, _, _, hvi⟩ := (D.mem_nonretainedVisibleVertices eta R₀ theta v).mp hlg
      exact (mem_sparse.mp hs) (D.componentSupport_subset_support i hvi)
    · refine (D.mem_nonretainedSmallVertices eta R₀ theta v).mpr ⟨?_, ?_⟩
      · exact (D.mem_nonretainedVertices eta R₀ v).mpr fun h ↦
          hi (hvis ((D.mem_retainedVertices_iff_of_mem_componentSupport hvi).mp h))
      · intro hlg
        obtain ⟨j, hj, _, hvj⟩ :=
          (D.mem_nonretainedVisibleVertices eta R₀ theta v).mp hlg
        exact hi ((D.mem_componentSupport_unique hvi hvj).symm ▸ hj)

theorem nonretainedSmallVertices_eq_sparse_union_nonvisible
    (D : SubcriticalDivision k V) {eta theta : ℝ} {R₀ : ℕ}
    (hvis : D.retainedComponentIndices eta R₀ ⊆ D.visibleComponentIndices theta) :
    D.nonretainedSmallVertices eta R₀ theta = D.sparse ∪
      (Finset.univ \ D.visibleComponentIndices theta).biUnion D.componentSupport := by
  ext v
  simp only [D.mem_nonretainedSmallVertices_iff hvis, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_univ, true_and]

theorem mem_nonretainedVertices_iff_of_mem_part
    (D : SubcriticalDivision k V) {eta : ℝ} {R₀ : ℕ}
    {a : D.PartIndex} {v : V} (hv : v ∈ D.part a) :
    v ∈ D.nonretainedVertices eta R₀ ↔ a.1 ∉ D.retainedComponentIndices eta R₀ := by
  rw [D.mem_nonretainedVertices,
    D.mem_retainedVertices_iff_of_mem_componentSupport
      (mem_componentSupport.mpr ⟨a.2, hv⟩)]

/-- This implication does not require that all retained components are visible. -/
theorem not_visible_of_mem_nonretainedSmallVertices_of_mem_part
    (D : SubcriticalDivision k V) {eta theta : ℝ} {R₀ : ℕ}
    {a : D.PartIndex} {v : V} (hv : v ∈ D.part a)
    (hs : v ∈ D.nonretainedSmallVertices eta R₀ theta) :
    a.1 ∉ D.visibleComponentIndices theta := by
  obtain ⟨hnret, hlg⟩ := (D.mem_nonretainedSmallVertices eta R₀ theta v).mp hs
  intro hi
  exact hlg ((D.mem_nonretainedVisibleVertices eta R₀ theta v).mpr
    ⟨a.1, hi, (D.mem_nonretainedVertices_iff_of_mem_part hv).mp hnret,
      mem_componentSupport.mpr ⟨a.2, hv⟩⟩)

theorem retainedComponentIndices_subset_visibleComponentIndices
    (D : SubcriticalDivision k V) {eta theta : ℝ} {R₀ : ℕ}
    (hR : 1 ≤ R₀) (htheta : 0 ≤ theta)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ))) :
    D.retainedComponentIndices eta R₀ ⊆ D.visibleComponentIndices theta := by
  intro i hi
  obtain ⟨hsize, horder⟩ := (D.mem_retainedComponentIndices eta R₀ i).mp hi
  have hRpos : (0 : ℝ) < R₀ := by exact_mod_cast (by omega : 0 < R₀)
  have hqR : ((D.core i).order : ℝ) ≤ R₀ := by exact_mod_cast horder
  have hcoeff : (D.core i).order * theta ≤ eta := by
    have hcut := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * R₀)).mp hcutoff
    have hq := mul_le_mul_of_nonneg_right hqR htheta
    nlinarith [mul_nonneg hRpos.le htheta]
  apply (D.mem_visibleComponentIndices theta i).mpr
  by_contra h
  have hall (j : Fin (D.core i).order) :
      ((D.parts i j).card : ℝ) < theta * Fintype.card V := by
    exact lt_of_not_ge fun hj ↦ h ⟨j, hj⟩
  have hsum : (∑ j : Fin (D.core i).order, ((D.parts i j).card : ℝ)) <
      ∑ _j : Fin (D.core i).order, theta * Fintype.card V := by
    apply Finset.sum_lt_sum (fun j _ ↦ (hall j).le)
    exact ⟨⟨0, (D.core i).order_pos⟩, Finset.mem_univ _, hall _⟩
  have heq : (∑ j : Fin (D.core i).order, ((D.parts i j).card : ℝ)) =
      (D.componentSupport i).card := by simp [D.card_componentSupport]
  rw [heq] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hmul := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg (Fintype.card V))
  nlinarith

theorem retainedPartIndices_subset_visiblePartIndices
    (D : SubcriticalDivision k V) {eta theta : ℝ} {R₀ : ℕ}
    (hR : 1 ≤ R₀) (htheta : 0 ≤ theta)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ))) :
    D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta := by
  intro a ha
  exact (D.mem_visiblePartIndices theta a).mpr
    (D.retainedComponentIndices_subset_visibleComponentIndices hR htheta hcutoff
      ((D.mem_retainedPartIndices eta R₀ a).mp ha))

theorem eta_mul_retainedComponentCount_le_one
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    eta * D.retainedComponentCount eta R₀ ≤ 1 := by
  have hn : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast D.componentCount_pos.trans_le D.componentCount_le_card
  have hsum : (∑ _i ∈ D.retainedComponentIndices eta R₀,
      eta * Fintype.card V) ≤
      ∑ i ∈ D.retainedComponentIndices eta R₀, ((D.componentSupport i).card : ℝ) := by
    exact Finset.sum_le_sum fun i hi ↦ (D.mem_retainedComponentIndices eta R₀ i).mp hi |>.1
  have hcard : (∑ i ∈ D.retainedComponentIndices eta R₀,
      ((D.componentSupport i).card : ℝ)) ≤ Fintype.card V := by
    exact_mod_cast (D.card_retainedVertices eta R₀).symm ▸
      Finset.card_le_univ (D.retainedVertices eta R₀)
  have hmul : (eta * D.retainedComponentCount eta R₀) * Fintype.card V ≤
      1 * Fintype.card V := by
    simpa [retainedComponentCount, mul_assoc, mul_comm, mul_left_comm] using hsum.trans hcard
  exact (mul_le_mul_iff_left₀ hn).mp hmul

theorem card_retainedPartIndices_le
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    (D.retainedPartIndices eta R₀).card ≤ R₀ * D.retainedComponentCount eta R₀ := by
  rw [D.card_retainedPartIndices]
  calc
    _ ≤ ∑ _i ∈ D.retainedComponentIndices eta R₀, R₀ :=
      Finset.sum_le_sum fun i hi ↦ (D.mem_retainedComponentIndices eta R₀ i).mp hi |>.2
    _ = _ := by simp [retainedComponentCount, mul_comm]

theorem eta_mul_card_retainedPartIndices_le
    (D : SubcriticalDivision k V) {eta : ℝ} (R₀ : ℕ) (heta : 0 ≤ eta) :
    eta * (D.retainedPartIndices eta R₀).card ≤ R₀ := by
  have hcard : ((D.retainedPartIndices eta R₀).card : ℝ) ≤
      R₀ * D.retainedComponentCount eta R₀ := by
    exact_mod_cast D.card_retainedPartIndices_le eta R₀
  calc
    _ ≤ eta * (R₀ * D.retainedComponentCount eta R₀) :=
      mul_le_mul_of_nonneg_left hcard heta
    _ = R₀ * (eta * D.retainedComponentCount eta R₀) := by ring
    _ ≤ R₀ * 1 := mul_le_mul_of_nonneg_left
      (D.eta_mul_retainedComponentCount_le_one eta R₀) (Nat.cast_nonneg R₀)
    _ = _ := mul_one _

theorem retained_of_le_of_isOrdered (D : SubcriticalDivision k V)
    {eta : ℝ} {R₀ : ℕ} (hordered : D.IsOrderedByCutoff R₀)
    {i j : Fin D.componentCount} (hij : i ≤ j)
    (hj : j ∈ D.retainedComponentIndices eta R₀) :
    i ∈ D.retainedComponentIndices eta R₀ := by
  obtain ⟨hsize, horder⟩ := (D.mem_retainedComponentIndices eta R₀ j).mp hj
  have hiorder := (hordered i j hij).1 horder
  have hsize' := (hordered i j hij).2 (iff_of_true hiorder horder)
  exact (D.mem_retainedComponentIndices eta R₀ i).mpr
    ⟨hsize.trans (by exact_mod_cast hsize'), hiorder⟩

/-- Under the paper's ordering, the finite-set definition is precisely its
initial segment of length `ell_*`. -/
theorem mem_retainedComponentIndices_iff_lt_count_of_isOrdered
    (D : SubcriticalDivision k V) {eta : ℝ} {R₀ : ℕ}
    (hordered : D.IsOrderedByCutoff R₀) (i : Fin D.componentCount) :
    i ∈ D.retainedComponentIndices eta R₀ ↔
      i.val < D.retainedComponentCount eta R₀ := by
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ D.retainedComponentIndices eta R₀ := by
      intro j hj
      exact D.retained_of_le_of_isOrdered hordered (Finset.mem_Iic.mp hj) hi
    have hc := Finset.card_le_card hsub
    simpa [Fin.card_Iic, retainedComponentCount] using hc
  · intro hi
    by_contra hnot
    have hsub : D.retainedComponentIndices eta R₀ ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hji
      exact hnot (D.retained_of_le_of_isOrdered hordered (le_of_not_gt hji) hj)
    have hc := Finset.card_le_card hsub
    simp only [Fin.card_Iio] at hc
    exact (not_lt_of_ge hc) hi

/-- A finite lower-bound adapter: only the actual bounded-order balance
inequality for retained components is needed. -/
theorem retainedPart_card_lower_bound_of_balance
    (D : SubcriticalDivision k V) {eta : ℝ} {R₀ : ℕ}
    (hR : 0 < R₀)
    (hbalance : ∀ i ∈ D.retainedComponentIndices eta R₀,
      ∀ j : Fin (D.core i).order,
        (D.componentSupport i).card / (2 * (R₀ : ℝ)) ≤ ((D.parts i j).card : ℝ))
    {a : D.PartIndex} (ha : a ∈ D.retainedPartIndices eta R₀) :
    eta * Fintype.card V / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ) := by
  have hi := (D.mem_retainedPartIndices eta R₀ a).mp ha
  exact (div_le_div_of_nonneg_right
    ((D.mem_retainedComponentIndices eta R₀ a.1).mp hi).1
      (by positivity)).trans (hbalance a.1 hi a.2)

end SubcriticalDivision

namespace SubcriticalCloseStructureResult

/-- Every retained part crosses the quantitative whole-part threshold
supplied by the close-structure bridge. -/
theorem retainedPart_card_lower_bound
    {k n R₀ : ℕ} {hk : 3 ≤ k}
    {G : SimpleGraph (Fin n)} {D : SubcriticalDivision k (Fin n)}
    {L : AdmissibleBlockSequence k} {omega eta theta alpha delta epsilon : ℝ}
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hR : 1 ≤ R₀) (heta : 0 ≤ eta)
    {a : D.PartIndex} (ha : a ∈ D.retainedPartIndices eta R₀) :
    eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ) := by
  simpa only [Fintype.card_fin] using D.retainedPart_card_lower_bound_of_balance
    (by omega : 0 < R₀) (fun i hi j ↦ by
      obtain ⟨hsize, horder⟩ := (D.mem_retainedComponentIndices eta R₀ i).mp hi
      simp only [Fintype.card_fin] at hsize
      have hR1 : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR
      have hbound : eta * n / (4 * (R₀ : ℝ)) ≤ eta * n := by
        apply div_le_self (mul_nonneg heta (Nat.cast_nonneg n))
        linarith
      exact (R.bounded_order_balance i horder (hbound.trans hsize) j).2) ha

end SubcriticalCloseStructureResult
end InducedStars
