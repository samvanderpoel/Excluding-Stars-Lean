import InducedStars.EdgeColoring.Stability
import InducedStars.Graphon.GraphonMantel
import Mathlib.Tactic

/-!
# Profile graphons of finite colorings

This file realizes the paper's finite red--green--blue colorings as equal-cell
step graphons.  Red, green, and blue receive the values `p`, `0`, and `1`,
respectively, while the project's total color accessor makes every diagonal
cell blue.  It also records the exact finite normalizations and the edit
estimate used in the stability transfer in the proof of
`prop:graphon-char-fixed-gamma`.
-/

noncomputable section

open Filter Finset MeasureTheory Set
open scoped BigOperators ENNReal

namespace InducedStars

/-! ## The finite profile matrix and graphon -/

/-- The graphon value assigned to one finite edge color. -/
def profileColorValue (p : ℝ) : EdgeColor → ℝ
  | .red => p
  | .green => 0
  | .blue => 1

@[simp] theorem profileColorValue_red (p : ℝ) :
    profileColorValue p .red = p := rfl

@[simp] theorem profileColorValue_green (p : ℝ) :
    profileColorValue p .green = 0 := rfl

@[simp] theorem profileColorValue_blue (p : ℝ) :
    profileColorValue p .blue = 1 := rfl

theorem profileColorValue_mem_Icc {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (c : EdgeColor) : profileColorValue p c ∈ Icc (0 : ℝ) 1 := by
  cases c <;> simp [hp.1, hp.2]

/-- The symmetric matrix obtained by replacing the colors of `C` by
`p`, `0`, and `1`. -/
def profileColorMatrix {q : ℕ} (p : ℝ) (C : ColoredGraph (Fin q)) :
    Matrix (Fin q) (Fin q) ℝ :=
  fun i j => profileColorValue p (C.color i j)

@[simp] theorem profileColorMatrix_apply {q : ℕ} (p : ℝ)
    (C : ColoredGraph (Fin q)) (i j : Fin q) :
    profileColorMatrix p C i j = profileColorValue p (C.color i j) := rfl

theorem profileColorMatrix_isSymm {q : ℕ} (p : ℝ)
    (C : ColoredGraph (Fin q)) : (profileColorMatrix p C).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [profileColorMatrix]
  rw [C.color_comm]

theorem profileColorMatrix_nonneg {q : ℕ} {p : ℝ}
    (C : ColoredGraph (Fin q)) (hp : 0 ≤ p) (i j : Fin q) :
    0 ≤ profileColorMatrix p C i j := by
  cases hcolor : C.color i j <;> simp [profileColorMatrix, profileColorValue, hcolor, hp]

theorem profileColorMatrix_le_one {q : ℕ} {p : ℝ}
    (C : ColoredGraph (Fin q)) (hp : p ≤ 1) (i j : Fin q) :
    profileColorMatrix p C i j ≤ 1 := by
  cases hcolor : C.color i j <;> simp [profileColorMatrix, profileColorValue, hcolor, hp]

@[simp] theorem profileColorMatrix_diagonal {q : ℕ} (p : ℝ)
    (C : ColoredGraph (Fin q)) (i : Fin q) :
    profileColorMatrix p C i i = 1 := by
  simp [profileColorMatrix]

/-- The equal-cell graphon of a finite coloring with palette `{0,p,1}`.
The interval hypothesis supplies the range proof required by `matrixGraphon`. -/
noncomputable def profileColoringGraphon {q : ℕ} (p : ℝ)
    (C : ColoredGraph (Fin q)) (hp : p ∈ Icc (0 : ℝ) 1) : Graphon :=
  matrixGraphon (profileColorMatrix p C)
    (profileColorMatrix_isSymm p C)
    (profileColorMatrix_nonneg C hp.1)
    (profileColorMatrix_le_one C hp.2)

/-- Exact value of the profile graphon on a canonical matrix cell, almost
everywhere. -/
theorem profileColoringGraphon_ae_eq_on_cell {q : ℕ} (p : ℝ)
    (C : ColoredGraph (Fin q)) (hp : p ∈ Icc (0 : ℝ) 1) (i j : Fin q) :
    ∀ᵐ z ∂unitSquareMeasure, z ∈ equalCell i ×ˢ equalCell j →
      (profileColoringGraphon p C hp).value z = profileColorValue p (C.color i j) := by
  let W := profileColoringGraphon p C hp
  filter_upwards [W.value_ae_eq,
    matrixGraphon_ae_eq_on_cell (profileColorMatrix p C)
      (profileColorMatrix_isSymm p C)
      (profileColorMatrix_nonneg C hp.1)
      (profileColorMatrix_le_one C hp.2) i j]
    with z hzValue hzCell hzMem
  rw [hzValue]
  simpa only [W, profileColoringGraphon, profileColorMatrix_apply] using hzCell hzMem

theorem profileColoringGraphon_ae_eq_on_red_cell {q : ℕ} (p : ℝ)
    (C : ColoredGraph (Fin q)) (hp : p ∈ Icc (0 : ℝ) 1) {i j : Fin q}
    (hred : C.color i j = .red) :
    ∀ᵐ z ∂unitSquareMeasure, z ∈ equalCell i ×ˢ equalCell j →
      (profileColoringGraphon p C hp).value z = p := by
  filter_upwards [profileColoringGraphon_ae_eq_on_cell p C hp i j] with z hz hmem
  simpa [hred] using hz hmem

theorem profileColoringGraphon_ae_eq_on_green_cell {q : ℕ} (p : ℝ)
    (C : ColoredGraph (Fin q)) (hp : p ∈ Icc (0 : ℝ) 1) {i j : Fin q}
    (hgreen : C.color i j = .green) :
    ∀ᵐ z ∂unitSquareMeasure, z ∈ equalCell i ×ˢ equalCell j →
      (profileColoringGraphon p C hp).value z = 0 := by
  filter_upwards [profileColoringGraphon_ae_eq_on_cell p C hp i j] with z hz hmem
  simpa [hgreen] using hz hmem

theorem profileColoringGraphon_ae_eq_on_blue_cell {q : ℕ} (p : ℝ)
    (C : ColoredGraph (Fin q)) (hp : p ∈ Icc (0 : ℝ) 1) {i j : Fin q}
    (hblue : C.color i j = .blue) :
    ∀ᵐ z ∂unitSquareMeasure, z ∈ equalCell i ×ˢ equalCell j →
      (profileColoringGraphon p C hp).value z = 1 := by
  filter_upwards [profileColoringGraphon_ae_eq_on_cell p C hp i j] with z hz hmem
  simpa [hblue] using hz hmem

theorem profileColoringGraphon_ae_eq_one_on_diagonal_cell {q : ℕ} (p : ℝ)
    (C : ColoredGraph (Fin q)) (hp : p ∈ Icc (0 : ℝ) 1) (i : Fin q) :
    ∀ᵐ z ∂unitSquareMeasure, z ∈ equalCell i ×ˢ equalCell i →
      (profileColoringGraphon p C hp).value z = 1 := by
  exact profileColoringGraphon_ae_eq_on_blue_cell p C hp (C.color_self i)

/-- A finite profile graphon takes values in its three-element palette almost
everywhere. -/
theorem profileColoringGraphon_ae_threeValued {q : ℕ} (hq : 0 < q)
    (p : ℝ) (C : ColoredGraph (Fin q)) (hp : p ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂unitSquareMeasure,
      (profileColoringGraphon p C hp).value z = 0 ∨
        (profileColoringGraphon p C hp).value z = p ∨
          (profileColoringGraphon p C hp).value z = 1 := by
  let W := profileColoringGraphon p C hp
  filter_upwards [ae_mem_iUnion_equalCell_prod hq, W.value_ae_eq,
    matrixGraphon_ae_eq_kernel (profileColorMatrix p C)
      (profileColorMatrix_isSymm p C)
      (profileColorMatrix_nonneg C hp.1)
      (profileColorMatrix_le_one C hp.2)]
    with z hzCover hzValue hzKernel
  obtain ⟨ij, hzij⟩ := Set.mem_iUnion.mp hzCover
  have hW : W.value z = profileColorValue p (C.color ij.1 ij.2) := by
    rw [hzValue]
    have hKernel : (W : UnitSquare → ℝ) z = matrixKernel (profileColorMatrix p C) z := by
      simpa only [W, profileColoringGraphon] using hzKernel
    rw [hKernel,
      matrixKernel_of_mem (profileColorMatrix p C) ij.1 ij.2 z hzij.1 hzij.2]
    rfl
  change W.value z = 0 ∨ W.value z = p ∨ W.value z = 1
  rw [hW]
  cases hcolor : C.color ij.1 ij.2 <;> simp [profileColorValue, hcolor]

/-! ## Exact value-region measures -/

private theorem mem_equalCellPairRegion_iff_of_mem_cell {q : ℕ}
    (s : Finset (Fin q × Fin q)) {i j : Fin q} {z : UnitSquare}
    (hzi : z.1 ∈ equalCell i) (hzj : z.2 ∈ equalCell j) :
    z ∈ equalCellPairRegion s ↔ (i, j) ∈ s := by
  constructor
  · intro hz
    simp only [equalCellPairRegion, Set.mem_iUnion] at hz
    obtain ⟨a, ha, hza⟩ := hz
    have hai : a.1 = i := equalCell_eq_of_mem hza.1 hzi
    have haj : a.2 = j := equalCell_eq_of_mem hza.2 hzj
    have haeq : a = (i, j) := by
      apply Prod.ext
      · exact hai
      · exact haj
    simpa [haeq] using ha
  · intro hij
    simp only [equalCellPairRegion, Set.mem_iUnion]
    exact ⟨(i, j), hij, hzi, hzj⟩

private theorem graphonRandomRegion_profileColoringGraphon_ae_eq {q : ℕ}
    (hq : 0 < q) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (C : ColoredGraph (Fin q)) :
    graphonRandomRegion
        (profileColoringGraphon p C ⟨hp.1.le, hp.2.le⟩) =ᵐ[unitSquareMeasure]
      equalCellPairRegion (C.orderedColorPairs .red) := by
  let hpIcc : p ∈ Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  let W := profileColoringGraphon p C hpIcc
  filter_upwards [ae_mem_iUnion_equalCell_prod hq, W.value_ae_eq,
    matrixGraphon_ae_eq_kernel (profileColorMatrix p C)
      (profileColorMatrix_isSymm p C)
      (profileColorMatrix_nonneg C hpIcc.1)
      (profileColorMatrix_le_one C hpIcc.2)]
    with z hzCover hzValue hzKernel
  obtain ⟨ij, hzij⟩ := Set.mem_iUnion.mp hzCover
  have hW : W.value z = profileColorValue p (C.color ij.1 ij.2) := by
    rw [hzValue]
    have hKernel : (W : UnitSquare → ℝ) z = matrixKernel (profileColorMatrix p C) z := by
      simpa only [W, profileColoringGraphon] using hzKernel
    rw [hKernel,
      matrixKernel_of_mem (profileColorMatrix p C) ij.1 ij.2 z hzij.1 hzij.2]
    rfl
  change (z ∈ graphonRandomRegion W) =
    (z ∈ equalCellPairRegion (C.orderedColorPairs .red))
  apply propext
  rw [mem_equalCellPairRegion_iff_of_mem_cell
    (C.orderedColorPairs .red) hzij.1 hzij.2, C.mem_orderedColorPairs]
  change (0 < W.value z ∧ W.value z < 1) ↔ _
  rw [hW]
  cases hcolor : C.color ij.1 ij.2 <;>
    simp [profileColorValue, hcolor, hp.1, hp.2]

private theorem graphonOneRegion_profileColoringGraphon_ae_eq {q : ℕ}
    (hq : 0 < q) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (C : ColoredGraph (Fin q)) :
    graphonOneRegion
        (profileColoringGraphon p C ⟨hp.1.le, hp.2.le⟩) =ᵐ[unitSquareMeasure]
      equalCellPairRegion (C.orderedColorPairs .blue) := by
  let hpIcc : p ∈ Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  let W := profileColoringGraphon p C hpIcc
  filter_upwards [ae_mem_iUnion_equalCell_prod hq, W.value_ae_eq,
    matrixGraphon_ae_eq_kernel (profileColorMatrix p C)
      (profileColorMatrix_isSymm p C)
      (profileColorMatrix_nonneg C hpIcc.1)
      (profileColorMatrix_le_one C hpIcc.2)]
    with z hzCover hzValue hzKernel
  obtain ⟨ij, hzij⟩ := Set.mem_iUnion.mp hzCover
  have hW : W.value z = profileColorValue p (C.color ij.1 ij.2) := by
    rw [hzValue]
    have hKernel : (W : UnitSquare → ℝ) z = matrixKernel (profileColorMatrix p C) z := by
      simpa only [W, profileColoringGraphon] using hzKernel
    rw [hKernel,
      matrixKernel_of_mem (profileColorMatrix p C) ij.1 ij.2 z hzij.1 hzij.2]
    rfl
  change (z ∈ graphonOneRegion W) =
    (z ∈ equalCellPairRegion (C.orderedColorPairs .blue))
  apply propext
  rw [mem_equalCellPairRegion_iff_of_mem_cell
    (C.orderedColorPairs .blue) hzij.1 hzij.2, C.mem_orderedColorPairs]
  change W.value z = 1 ↔ _
  rw [hW]
  cases hcolor : C.color ij.1 ij.2 <;>
    simp [profileColorValue, hcolor, ne_of_lt hp.2]

/-- The random-valued region is exactly the union of the red ordered cells. -/
theorem graphonRandomMass_profileColoringGraphon {q : ℕ} (hq : 0 < q)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (C : ColoredGraph (Fin q)) :
    graphonRandomMass
        (profileColoringGraphon p C ⟨hp.1.le, hp.2.le⟩) =
      C.normalizedRedArea := by
  unfold graphonRandomMass
  rw [Measure.real, measure_congr
    (graphonRandomRegion_profileColoringGraphon_ae_eq hq hp C),
    ← Measure.real]
  exact measureReal_equalCellPairRegion_orderedRed_eq hq C

/-- The one-valued region is exactly the union of the blue ordered cells,
including all diagonal cells. -/
theorem graphonOneMass_profileColoringGraphon {q : ℕ} (hq : 0 < q)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (C : ColoredGraph (Fin q)) :
    graphonOneMass
        (profileColoringGraphon p C ⟨hp.1.le, hp.2.le⟩) =
      C.normalizedBlueDiagonalArea := by
  unfold graphonOneMass
  rw [Measure.real, measure_congr
    (graphonOneRegion_profileColoringGraphon_ae_eq hq hp C),
    ← Measure.real]
  exact measureReal_equalCellPairRegion_orderedBlue_eq hq C

/-! ## Exact edge-density and entropy formulas -/

private theorem profileColorValue_eq_indicators (p : ℝ) (c : EdgeColor) :
    profileColorValue p c =
      (if c = .red then p else 0) + (if c = .blue then 1 else 0) := by
  cases c <;> simp [profileColorValue]

private theorem sum_profileColorMatrix {q : ℕ} (p : ℝ)
    (C : ColoredGraph (Fin q)) :
    (∑ i : Fin q, ∑ j : Fin q, (profileColorMatrix p C) i j) =
      (#(C.orderedColorPairs .red) : ℝ) * p +
        (#(C.orderedColorPairs .blue) : ℝ) := by
  rw [← Fintype.sum_prod_type (f := fun ij : Fin q × Fin q =>
    (profileColorMatrix p C) ij.1 ij.2)]
  simp_rw [profileColorMatrix_apply, profileColorValue_eq_indicators]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  simp [ColoredGraph.orderedColorPairs]

private theorem sum_binaryEntropy_profileColorMatrix {q : ℕ} (p : ℝ)
    (C : ColoredGraph (Fin q)) :
    (∑ i : Fin q, ∑ j : Fin q,
        binaryEntropy ((profileColorMatrix p C) i j)) =
      (#(C.orderedColorPairs .red) : ℝ) * binaryEntropy p := by
  rw [← Fintype.sum_prod_type (f := fun ij : Fin q × Fin q =>
    binaryEntropy ((profileColorMatrix p C) ij.1 ij.2))]
  have hvalue (c : EdgeColor) :
      binaryEntropy (profileColorValue p c) =
        if c = .red then binaryEntropy p else 0 := by
    cases c <;> simp [profileColorValue]
  simp_rw [profileColorMatrix_apply, hvalue]
  rw [← Finset.sum_filter]
  simp [ColoredGraph.orderedColorPairs]

/-- Exact edge density of a finite profile graphon. -/
theorem graphonEdgeDensity_profileColoringGraphon {q : ℕ} (hq : 0 < q)
    (p : ℝ) (C : ColoredGraph (Fin q)) (hp : p ∈ Icc (0 : ℝ) 1) :
    graphonEdgeDensity (profileColoringGraphon p C hp) =
      p * C.normalizedRedArea + C.normalizedBlueDiagonalArea := by
  rw [profileColoringGraphon,
    graphonEdgeDensity_matrixGraphon hq,
    sum_profileColorMatrix,
    C.normalizedRedArea_eq_card_orderedRedPairs,
    C.normalizedBlueDiagonalArea_eq_card_orderedBluePairs hq]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  field_simp

/-- Exact entropy of a finite profile graphon. -/
theorem graphonEntropy_profileColoringGraphon {q : ℕ} (hq : 0 < q)
    (p : ℝ) (C : ColoredGraph (Fin q)) (hp : p ∈ Icc (0 : ℝ) 1) :
    graphonEntropy (profileColoringGraphon p C hp) =
      binaryEntropy p * C.normalizedRedArea := by
  rw [profileColoringGraphon,
    graphonEntropy_matrixGraphon hq,
    sum_binaryEntropy_profileColorMatrix,
    C.normalizedRedArea_eq_card_orderedRedPairs]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  field_simp

/-! ## Hamming edits and profile graphon distance -/

namespace ColoredGraph

/-- Ordered pairs whose colors differ in two colorings.  Diagonal pairs never
belong to this set. -/
def orderedColorDisagreementPairs {q : ℕ} (C D : ColoredGraph (Fin q)) :
    Finset (Fin q × Fin q) :=
  Finset.univ.filter fun ij => C.color ij.1 ij.2 ≠ D.color ij.1 ij.2

@[simp] theorem mem_orderedColorDisagreementPairs {q : ℕ}
    (C D : ColoredGraph (Fin q)) (i j : Fin q) :
    (i, j) ∈ C.orderedColorDisagreementPairs D ↔
      C.color i j ≠ D.color i j := by
  simp [orderedColorDisagreementPairs]

private def colorDifferenceGraph {q : ℕ} (C D : ColoredGraph (Fin q)) :
    SimpleGraph (Fin q) where
  Adj i j := C.color i j ≠ D.color i j
  symm := ⟨by
    intro i j hij
    simpa only [C.color_comm i j, D.color_comm i j] using hij⟩
  loopless := ⟨by
    intro i hij
    apply hij
    simp only [C.color_self, D.color_self]⟩

/-- Each changed unordered edge has exactly two ordered orientations. -/
theorem card_orderedColorDisagreementPairs {q : ℕ}
    (C D : ColoredGraph (Fin q)) :
    #(C.orderedColorDisagreementPairs D) =
      2 * C.coloringHammingDistance D := by
  classical
  let G := colorDifferenceGraph C D
  have hsupport : C.coloringHammingSupport D = G.edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ i j =>
        rw [pair_mem_coloringHammingSupport, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet]
        change (i ≠ j ∧ C.color i j ≠ D.color i j) ↔
          C.color i j ≠ D.color i j
        constructor
        · exact fun h => h.2
        · intro hdiff
          refine ⟨?_, hdiff⟩
          intro hij
          subst j
          exact hdiff (by simp)
  rw [orderedColorDisagreementPairs, coloringHammingDistance, hsupport]
  simpa only [G, colorDifferenceGraph] using G.two_mul_card_edgeFinset.symm

private theorem orderedColorPairs_card_diff_le_hamming {q : ℕ}
    (C D : ColoredGraph (Fin q)) (c : EdgeColor) :
    |(#(C.orderedColorPairs c) : ℝ) - (#(D.orderedColorPairs c) : ℝ)| ≤
      2 * (C.coloringHammingDistance D : ℝ) := by
  let A := C.orderedColorPairs c
  let B := D.orderedColorPairs c
  let E := C.orderedColorDisagreementPairs D
  have hAB : A ⊆ B ∪ E := by
    intro ij hij
    by_cases hB : ij ∈ B
    · exact Finset.mem_union_left E hB
    · apply Finset.mem_union_right B
      rw [mem_orderedColorDisagreementPairs]
      intro heq
      apply hB
      have hij' : (ij.1, ij.2) ∈ C.orderedColorPairs c := by
        simpa only [A] using hij
      apply (D.mem_orderedColorPairs c ij.1 ij.2).mpr
      rw [← heq]
      exact (C.mem_orderedColorPairs c ij.1 ij.2).mp hij'
  have hBA : B ⊆ A ∪ E := by
    intro ij hij
    by_cases hA : ij ∈ A
    · exact Finset.mem_union_left E hA
    · apply Finset.mem_union_right A
      rw [mem_orderedColorDisagreementPairs]
      intro heq
      apply hA
      have hij' : (ij.1, ij.2) ∈ D.orderedColorPairs c := by
        simpa only [B] using hij
      apply (C.mem_orderedColorPairs c ij.1 ij.2).mpr
      rw [heq]
      exact (D.mem_orderedColorPairs c ij.1 ij.2).mp hij'
  have hcardAB : A.card ≤ B.card + E.card :=
    (Finset.card_le_card hAB).trans (Finset.card_union_le B E)
  have hcardBA : B.card ≤ A.card + E.card :=
    (Finset.card_le_card hBA).trans (Finset.card_union_le A E)
  have hrealAB : (A.card : ℝ) - (B.card : ℝ) ≤ (E.card : ℝ) := by
    have hcast : (A.card : ℝ) ≤ (B.card : ℝ) + (E.card : ℝ) := by
      exact_mod_cast hcardAB
    linarith
  have hrealBA : (B.card : ℝ) - (A.card : ℝ) ≤ (E.card : ℝ) := by
    have hcast : (B.card : ℝ) ≤ (A.card : ℝ) + (E.card : ℝ) := by
      exact_mod_cast hcardBA
    linarith
  have hEreal : (E.card : ℝ) = 2 * (C.coloringHammingDistance D : ℝ) := by
    have hE : E.card = 2 * C.coloringHammingDistance D := by
      exact C.card_orderedColorDisagreementPairs D
    exact_mod_cast hE
  rw [abs_le]
  constructor <;> linarith

/-- Changing `d` unordered edges changes normalized red area by at most
`2d/q²`. -/
theorem abs_normalizedRedArea_sub_le_hamming {q : ℕ} (hq : 0 < q)
    (C D : ColoredGraph (Fin q)) :
    |C.normalizedRedArea - D.normalizedRedArea| ≤
      2 * (C.coloringHammingDistance D : ℝ) / (q : ℝ) ^ 2 := by
  rw [C.normalizedRedArea_eq_card_orderedRedPairs,
    D.normalizedRedArea_eq_card_orderedRedPairs]
  have hqSq : 0 < (q : ℝ) ^ 2 := by positivity
  rw [← sub_div, abs_div, abs_of_pos hqSq]
  exact div_le_div_of_nonneg_right
    (orderedColorPairs_card_diff_le_hamming C D .red) hqSq.le

/-- The same edit bound holds for normalized blue-plus-diagonal area; the
diagonal cells agree automatically. -/
theorem abs_normalizedBlueDiagonalArea_sub_le_hamming {q : ℕ} (hq : 0 < q)
    (C D : ColoredGraph (Fin q)) :
    |C.normalizedBlueDiagonalArea - D.normalizedBlueDiagonalArea| ≤
      2 * (C.coloringHammingDistance D : ℝ) / (q : ℝ) ^ 2 := by
  rw [C.normalizedBlueDiagonalArea_eq_card_orderedBluePairs hq,
    D.normalizedBlueDiagonalArea_eq_card_orderedBluePairs hq]
  have hqSq : 0 < (q : ℝ) ^ 2 := by positivity
  rw [← sub_div, abs_div, abs_of_pos hqSq]
  exact div_le_div_of_nonneg_right
    (orderedColorPairs_card_diff_le_hamming C D .blue) hqSq.le

end ColoredGraph

private theorem graphonL1Dist_profileColoringGraphon_eq_sum {q : ℕ}
    (hq : 0 < q) (p : ℝ) (C D : ColoredGraph (Fin q))
    (hp : p ∈ Icc (0 : ℝ) 1) :
    graphonL1Dist (profileColoringGraphon p C hp)
        (profileColoringGraphon p D hp) =
      (1 / (q : ℝ)) ^ 2 *
        ∑ i : Fin q, ∑ j : Fin q,
          |(profileColorMatrix p C) i j - (profileColorMatrix p D) i j| := by
  let WC := profileColoringGraphon p C hp
  let WD := profileColoringGraphon p D hp
  have hcell (i j : Fin q) :
      (∫ z in equalCell i ×ˢ equalCell j, |WC z - WD z| ∂unitSquareMeasure) =
        (1 / (q : ℝ)) ^ 2 *
          |(profileColorMatrix p C) i j - (profileColorMatrix p D) i j| := by
    calc
      _ = ∫ _z in equalCell i ×ˢ equalCell j,
          |(profileColorMatrix p C) i j - (profileColorMatrix p D) i j|
          ∂unitSquareMeasure := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem ((measurableSet_equalCell i).prod
            (measurableSet_equalCell j)),
          ae_restrict_of_ae (matrixGraphon_ae_eq_on_cell
            (profileColorMatrix p C) (profileColorMatrix_isSymm p C)
            (profileColorMatrix_nonneg C hp.1)
            (profileColorMatrix_le_one C hp.2) i j),
          ae_restrict_of_ae (matrixGraphon_ae_eq_on_cell
            (profileColorMatrix p D) (profileColorMatrix_isSymm p D)
            (profileColorMatrix_nonneg D hp.1)
            (profileColorMatrix_le_one D hp.2) i j)]
          with z hzMem hzC hzD
        have hC := hzC hzMem
        have hD := hzD hzMem
        simpa only [WC, WD, profileColoringGraphon] using
          congrArg₂ (fun x y : ℝ => |x - y|) hC hD
      _ = (unitSquareMeasure (equalCell i ×ˢ equalCell j)).toReal *
          |(profileColorMatrix p C) i j - (profileColorMatrix p D) i j| := by
        rw [integral_const]
        simp [smul_eq_mul, Measure.real_def]
      _ = _ := by
        rw [show unitSquareMeasure (equalCell i ×ˢ equalCell j) =
            ENNReal.ofReal (1 / (q : ℝ)) ^ 2 from volume_equalCell_prod i j,
          ENNReal.toReal_pow, ENNReal.toReal_ofReal]
        positivity
  rw [graphonL1Dist_eq_integral,
    integral_eq_setIntegral (ae_mem_iUnion_equalCell_prod hq),
    integral_iUnion_fintype]
  · calc
      (∑ ij : Fin q × Fin q,
          ∫ z in equalCell ij.1 ×ˢ equalCell ij.2, |WC z - WD z|
            ∂unitSquareMeasure) =
          ∑ ij : Fin q × Fin q, (1 / (q : ℝ)) ^ 2 *
            |(profileColorMatrix p C) ij.1 ij.2 -
              (profileColorMatrix p D) ij.1 ij.2| := by
        apply Finset.sum_congr rfl
        intro ij _hij
        exact hcell ij.1 ij.2
      _ = _ := by rw [← Finset.mul_sum, Fintype.sum_prod_type]
  · intro ij
    exact (measurableSet_equalCell ij.1).prod (measurableSet_equalCell ij.2)
  · exact pairwise_disjoint_equalCell_prod
  · intro ij
    exact ((profileColoringGraphon p C hp).integrable.sub
      (profileColoringGraphon p D hp).integrable).abs.integrableOn

private theorem sum_abs_profileColorMatrix_sub_le_hamming {q : ℕ}
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (C D : ColoredGraph (Fin q)) :
    (∑ i : Fin q, ∑ j : Fin q,
        |(profileColorMatrix p C) i j - (profileColorMatrix p D) i j|) ≤
      2 * (C.coloringHammingDistance D : ℝ) := by
  rw [← Fintype.sum_prod_type (f := fun ij : Fin q × Fin q =>
    |(profileColorMatrix p C) ij.1 ij.2 -
      (profileColorMatrix p D) ij.1 ij.2|)]
  let E := C.orderedColorDisagreementPairs D
  calc
    (∑ ij : Fin q × Fin q,
        |(profileColorMatrix p C) ij.1 ij.2 -
          (profileColorMatrix p D) ij.1 ij.2|) ≤
        ∑ ij : Fin q × Fin q,
          if C.color ij.1 ij.2 ≠ D.color ij.1 ij.2 then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro ij _hij
      have hC := profileColorValue_mem_Icc hp (C.color ij.1 ij.2)
      have hD := profileColorValue_mem_Icc hp (D.color ij.1 ij.2)
      change |profileColorValue p (C.color ij.1 ij.2) -
          profileColorValue p (D.color ij.1 ij.2)| ≤
        if C.color ij.1 ij.2 ≠ D.color ij.1 ij.2 then 1 else 0
      by_cases hdiff : C.color ij.1 ij.2 ≠ D.color ij.1 ij.2
      · rw [if_pos hdiff]
        rw [abs_le]
        constructor <;> linarith [hC.1, hC.2, hD.1, hD.2]
      · have heq : C.color ij.1 ij.2 = D.color ij.1 ij.2 := not_ne_iff.mp hdiff
        rw [heq]
        simp
    _ = (E.card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [E, ColoredGraph.orderedColorDisagreementPairs]
    _ = 2 * (C.coloringHammingDistance D : ℝ) := by
      have hE : E.card = 2 * C.coloringHammingDistance D := by
        exact C.card_orderedColorDisagreementPairs D
      exact_mod_cast hE

/-- Hamming distance of finite colorings controls the `L¹` distance of their
profile graphons.  The factor two records the two oriented cells belonging to
each changed unordered edge. -/
theorem graphonL1Dist_profileColoringGraphon_le {q : ℕ} (hq : 0 < q)
    (p : ℝ) (C D : ColoredGraph (Fin q)) (hp : p ∈ Icc (0 : ℝ) 1) :
    graphonL1Dist (profileColoringGraphon p C hp)
        (profileColoringGraphon p D hp) ≤
      2 * (C.coloringHammingDistance D : ℝ) / (q : ℝ) ^ 2 := by
  rw [graphonL1Dist_profileColoringGraphon_eq_sum hq p C D hp]
  have hfactor : (1 / (q : ℝ)) ^ 2 = 1 / (q : ℝ) ^ 2 := by ring
  rw [hfactor]
  rw [one_div, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right
    (sum_abs_profileColorMatrix_sub_le_hamming hp C D)
    (sq_nonneg (q : ℝ))

/-! ## The normalized finite objective -/

/-- The paper's finite objective divided by the ordered-cell scale `q²/2`. -/
noncomputable def normalizedObjective (k : ℕ) {q : ℕ}
    (C : ColoredGraph (Fin q)) : ℝ :=
  2 * (ColoredGraph.objective k C : ℝ) / (q : ℝ) ^ 2

/-- Exact relation between the finite integer objective and the two profile
areas.  The compensating term removes the diagonal cells included in the
blue profile region. -/
theorem normalizedObjective_eq (k : ℕ) {q : ℕ} (hq : 0 < q)
    (C : ColoredGraph (Fin q)) :
    normalizedObjective k C =
      C.normalizedRedArea -
        (delta k : ℝ) * C.normalizedBlueDiagonalArea +
          (delta k : ℝ) / (q : ℝ) := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  simp only [normalizedObjective, ColoredGraph.objective, Int.cast_sub,
    Int.cast_natCast, Int.cast_mul, Nat.cast_ofNat, Nat.cast_sub]
  unfold ColoredGraph.normalizedRedArea ColoredGraph.normalizedBlueDiagonalArea
  field_simp
  ring

end InducedStars
