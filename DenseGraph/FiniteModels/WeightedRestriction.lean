import DenseGraph.FiniteModels.WeightedGraph

/-!
# Restricting finite weighted graphs

Foundational same-label cut estimates for a weighted graph restricted to a
finite vertex subset.  The error term records the vertices on which a
reference graph and a model graph need not agree.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DenseGraph.FiniteWeightedGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Restrict a finite weighted graph to the subtype carried by a finset. -/
def restrictToFinset (A : FiniteWeightedGraph V) (U : Finset V) :
    FiniteWeightedGraph ↑U where
  weight x y := A.weight x.1 y.1
  symmetric x y := A.symmetric x.1 y.1
  nonneg x y := A.nonneg x.1 y.1
  le_one x y := A.le_one x.1 y.1

@[simp] theorem restrictToFinset_weight (A : FiniteWeightedGraph V)
    (U : Finset V) (x y : ↑U) :
    (A.restrictToFinset U).weight x y = A.weight x.1 y.1 := rfl

/-- The constant finite weighted graph with value `w`. -/
def constant (w : ℝ) (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
    FiniteWeightedGraph V where
  weight _ _ := w
  symmetric _ _ := rfl
  nonneg _ _ := hw₀
  le_one _ _ := hw₁

@[simp] theorem constant_weight (w : ℝ) (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1)
    (x y : V) : (constant w hw₀ hw₁ : FiniteWeightedGraph V).weight x y = w := rfl

/-- The inclusion of the subtype carried by `U`. -/
def restrictToFinsetEmbedding (U : Finset V) : ↑U ↪ V where
  toFun := Subtype.val
  inj' := Subtype.val_injective

@[simp] theorem map_restrictToFinsetEmbedding_mem (U : Finset V)
    (S : Finset ↑U) {x : V} :
    x ∈ S.map (restrictToFinsetEmbedding U) ↔
      ∃ y ∈ S, (y : V) = x := by
  simp [restrictToFinsetEmbedding]

theorem rectangleDiscrepancy_restrictToFinset
    (A B : FiniteWeightedGraph V) (U : Finset V) (S T : Finset ↑U) :
    rectangleDiscrepancy (A.restrictToFinset U) (B.restrictToFinset U) S T =
      rectangleDiscrepancy A B
        (S.map (restrictToFinsetEmbedding U))
        (T.map (restrictToFinsetEmbedding U)) := by
  classical
  simp [rectangleDiscrepancy, restrictToFinsetEmbedding]

/-- Restriction cannot increase the unnormalized labeled cut discrepancy. -/
theorem finiteLabeledCutRaw_restrictToFinset_le
    (A B : FiniteWeightedGraph V) (U : Finset V) :
    finiteLabeledCutRaw (A.restrictToFinset U) (B.restrictToFinset U) ≤
      finiteLabeledCutRaw A B := by
  obtain ⟨S, T, hST⟩ := exists_rectangleDiscrepancy_eq_raw
    (A.restrictToFinset U) (B.restrictToFinset U)
  rw [← hST, rectangleDiscrepancy_restrictToFinset]
  exact abs_rectangleDiscrepancy_le_raw A B _ _

/-- A global normalized cut estimate restricts with the expected ratio of
ambient and retained vertex counts.  This form avoids division and is also
valid when the retained set is empty. -/
theorem finiteLabeledCutDist_restrictToFinset_mul_card_sq_le
    (A B : FiniteWeightedGraph V) (U : Finset V) :
    finiteLabeledCutDist (A.restrictToFinset U) (B.restrictToFinset U) *
        (U.card : ℝ) ^ 2 ≤
      finiteLabeledCutDist A B * (Fintype.card V : ℝ) ^ 2 := by
  by_cases hU : U.card = 0
  · have hleft :
        finiteLabeledCutDist (A.restrictToFinset U) (B.restrictToFinset U) *
            (U.card : ℝ) ^ 2 = 0 := by simp [hU]
    rw [hleft]
    exact mul_nonneg (finiteLabeledCutDist_nonneg A B) (sq_nonneg _)
  · have hUℝ : (U.card : ℝ) ≠ 0 := by exact_mod_cast hU
    have hV : Fintype.card V ≠ 0 := by
      intro hV
      have : U.card ≤ Fintype.card V := Finset.card_le_univ U
      omega
    have hVℝ : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hV
    have hleft :
        finiteLabeledCutDist (A.restrictToFinset U) (B.restrictToFinset U) *
            (U.card : ℝ) ^ 2 =
          finiteLabeledCutRaw (A.restrictToFinset U) (B.restrictToFinset U) := by
      rw [finiteLabeledCutDist, Fintype.card_coe]
      field_simp
    have hright : finiteLabeledCutDist A B * (Fintype.card V : ℝ) ^ 2 =
        finiteLabeledCutRaw A B := by
      rw [finiteLabeledCutDist]
      field_simp
    rw [hleft, hright]
    exact finiteLabeledCutRaw_restrictToFinset_le A B U

private theorem abs_weight_sub_weight_le_one
    (A B : FiniteWeightedGraph V) (x y : V) :
    |A.weight x y - B.weight x y| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [A.nonneg x y, A.le_one x y,
    B.nonneg x y, B.le_one x y]

/-- Deleting rows and columns on which pointwise agreement is unavailable
costs at most the number of affected ordered pairs. -/
theorem abs_rectangleDiscrepancy_le_deleted_rows_cols
    (A B : FiniteWeightedGraph V) (X Y Xgood Ygood : Finset V)
    (hXgood : Xgood ⊆ X) (hYgood : Ygood ⊆ Y)
    (hagree : ∀ x ∈ Xgood, ∀ y ∈ Ygood, A.weight x y = B.weight x y) :
    |rectangleDiscrepancy A B X Y| ≤
      ((X \ Xgood).card : ℝ) * Y.card +
        (X.card : ℝ) * (Y \ Ygood).card := by
  let rowBad : V → ℝ := fun x ↦ if x ∈ Xgood then 0 else 1
  let colBad : V → ℝ := fun y ↦ if y ∈ Ygood then 0 else 1
  have hpoint : ∀ x ∈ X, ∀ y ∈ Y,
      |A.weight x y - B.weight x y| ≤ rowBad x + colBad y := by
    intro x hx y hy
    by_cases hxg : x ∈ Xgood
    · by_cases hyg : y ∈ Ygood
      · simp [rowBad, colBad, hxg, hyg, hagree x hxg y hyg]
      · simpa [rowBad, colBad, hxg, hyg] using
          abs_weight_sub_weight_le_one A B x y
    · have h := abs_weight_sub_weight_le_one A B x y
      by_cases hyg : y ∈ Ygood
      · simpa [rowBad, colBad, hxg, hyg] using h
      · have hone : (1 : ℝ) ≤ 1 + 1 := by norm_num
        simpa [rowBad, colBad, hxg, hyg] using h.trans hone
  have hsum : |rectangleDiscrepancy A B X Y| ≤
      ∑ x ∈ X, ∑ y ∈ Y, (rowBad x + colBad y) := by
    calc
      _ ≤ ∑ x ∈ X, |∑ y ∈ Y, (A.weight x y - B.weight x y)| := by
        unfold rectangleDiscrepancy
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ X, ∑ y ∈ Y, |A.weight x y - B.weight x y| := by
        exact Finset.sum_le_sum fun x _ ↦ Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun x hx ↦
        Finset.sum_le_sum fun y hy ↦ hpoint x hx y hy
  have hrow : (∑ x ∈ X, rowBad x) = ((X \ Xgood).card : ℝ) := by
    have hfilter : X.filter (fun x ↦ x ∉ Xgood) = X \ Xgood := by
      ext x
      simp
    calc
      _ = ((X.filter (fun x ↦ x ∉ Xgood)).card : ℝ) := by
        simpa [rowBad] using
          (Finset.sum_boole (R := ℝ) (fun x : V ↦ x ∉ Xgood) X)
      _ = _ := by rw [hfilter]
  have hcol : (∑ y ∈ Y, colBad y) = ((Y \ Ygood).card : ℝ) := by
    have hfilter : Y.filter (fun y ↦ y ∉ Ygood) = Y \ Ygood := by
      ext y
      simp
    calc
      _ = ((Y.filter (fun y ↦ y ∉ Ygood)).card : ℝ) := by
        simpa [colBad] using
          (Finset.sum_boole (R := ℝ) (fun y : V ↦ y ∉ Ygood) Y)
      _ = _ := by rw [hfilter]
  calc
    _ ≤ ∑ x ∈ X, ∑ y ∈ Y, (rowBad x + colBad y) := hsum
    _ = (Y.card : ℝ) * (∑ x ∈ X, rowBad x) +
        (X.card : ℝ) * (∑ y ∈ Y, colBad y) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum]
    _ = _ := by rw [hrow, hcol]; ring

private theorem card_filter_bad_le (U Good : Finset V) (S : Finset ↑U) :
    ((S.filter fun x : ↑U ↦ x.1 ∉ Good).card : ℝ) ≤
      ((U \ Good).card : ℝ) := by
  have hmap : (S.filter fun x : ↑U ↦ x.1 ∉ Good).map
      (restrictToFinsetEmbedding U) ⊆ U \ Good := by
    intro x hx
    simp only [Finset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨_, hyGood⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_sdiff.mpr ⟨y.property, hyGood⟩
  have hnat : (S.filter fun x : ↑U ↦ x.1 ∉ Good).card ≤
      (U \ Good).card := by
    simpa using Finset.card_le_card hmap
  exact_mod_cast hnat

private theorem abs_rectangleDiscrepancy_restrictToFinset_le_bad
    (A B : FiniteWeightedGraph V) (U Good : Finset V)
    (hGood : Good ⊆ U)
    (hagree : ∀ x ∈ Good, ∀ y ∈ Good, A.weight x y = B.weight x y)
    (S T : Finset ↑U) :
    |rectangleDiscrepancy (A.restrictToFinset U) (B.restrictToFinset U) S T| ≤
      2 * ((U \ Good).card : ℝ) * U.card := by
  let bad : ↑U → ℝ := fun x ↦ if (x : V) ∈ Good then 0 else 1
  have hpoint : ∀ x : ↑U, ∀ y : ↑U,
      |(A.restrictToFinset U).weight x y -
          (B.restrictToFinset U).weight x y| ≤ bad x + bad y := by
    intro x y
    by_cases hx : (x : V) ∈ Good
    · by_cases hy : (y : V) ∈ Good
      · simp [bad, hx, hy, hagree x hx y hy]
      · simpa [bad, hx, hy] using abs_weight_sub_weight_le_one A B x y
    · have h := abs_weight_sub_weight_le_one A B x y
      by_cases hy : (y : V) ∈ Good
      · simpa [bad, hx, hy] using h
      · have hone : (1 : ℝ) ≤ 1 + 1 := by norm_num
        simpa [bad, hx, hy] using h.trans hone
  have hsum :
      |rectangleDiscrepancy (A.restrictToFinset U) (B.restrictToFinset U) S T| ≤
        ∑ x ∈ S, ∑ y ∈ T, (bad x + bad y) := by
    calc
      _ ≤ ∑ x ∈ S, |∑ y ∈ T,
          ((A.restrictToFinset U).weight x y -
            (B.restrictToFinset U).weight x y)| := by
        unfold rectangleDiscrepancy
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ S, ∑ y ∈ T,
          |(A.restrictToFinset U).weight x y -
            (B.restrictToFinset U).weight x y| := by
        exact Finset.sum_le_sum fun x _ ↦ Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ S, ∑ y ∈ T, (bad x + bad y) := by
        exact Finset.sum_le_sum fun x _ ↦
          Finset.sum_le_sum fun y _ ↦ hpoint x y
  have hbadS : (∑ x ∈ S, bad x) ≤ ((U \ Good).card : ℝ) := by
    calc
      _ = ((S.filter fun x : ↑U ↦ x.1 ∉ Good).card : ℝ) := by
        simpa [bad] using
          (Finset.sum_boole (R := ℝ) (fun x : ↑U ↦ x.1 ∉ Good) S)
      _ ≤ _ := card_filter_bad_le U Good S
  have hbadT : (∑ y ∈ T, bad y) ≤ ((U \ Good).card : ℝ) := by
    calc
      _ = ((T.filter fun y : ↑U ↦ y.1 ∉ Good).card : ℝ) := by
        simpa [bad] using
          (Finset.sum_boole (R := ℝ) (fun y : ↑U ↦ y.1 ∉ Good) T)
      _ ≤ _ := card_filter_bad_le U Good T
  have hcardS : (S.card : ℝ) ≤ U.card := by
    simpa [Fintype.card_coe] using
      (show (S.card : ℝ) ≤ Fintype.card ↑U by exact_mod_cast Finset.card_le_univ S)
  have hcardT : (T.card : ℝ) ≤ U.card := by
    simpa [Fintype.card_coe] using
      (show (T.card : ℝ) ≤ Fintype.card ↑U by exact_mod_cast Finset.card_le_univ T)
  calc
    _ ≤ ∑ x ∈ S, ∑ y ∈ T, (bad x + bad y) := hsum
    _ = (T.card : ℝ) * (∑ x ∈ S, bad x) +
        (S.card : ℝ) * (∑ y ∈ T, bad y) := by
      simp only [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum]
    _ ≤ (U.card : ℝ) * (U \ Good).card +
        (U.card : ℝ) * (U \ Good).card := by gcongr
    _ = 2 * ((U \ Good).card : ℝ) * U.card := by ring

/-- If two weighted graphs agree on `Good × Good`, their discrepancy after
restriction to `U` is paid for only by vertices in `U \ Good`. -/
theorem finiteLabeledCutDist_restrictToFinset_le_bad
    (A B : FiniteWeightedGraph V) (U Good : Finset V)
    (hGood : Good ⊆ U)
    (hagree : ∀ x ∈ Good, ∀ y ∈ Good, A.weight x y = B.weight x y) :
    finiteLabeledCutDist (A.restrictToFinset U) (B.restrictToFinset U) ≤
      2 * ((U \ Good).card : ℝ) / U.card := by
  by_cases hU : U.card = 0
  · have hUempty : U = ∅ := Finset.card_eq_zero.mp hU
    have hAB : A.restrictToFinset U = B.restrictToFinset U := by
      ext x
      have hx : False := by simpa [hUempty] using x.property
      exact hx.elim
    simp [hAB, hUempty]
  · have hUℝ : (U.card : ℝ) ≠ 0 := by exact_mod_cast hU
    obtain ⟨S, T, hST⟩ := exists_rectangleDiscrepancy_eq_raw
      (A.restrictToFinset U) (B.restrictToFinset U)
    have hraw : finiteLabeledCutRaw (A.restrictToFinset U) (B.restrictToFinset U) ≤
        2 * ((U \ Good).card : ℝ) * U.card := by
      rw [← hST]
      exact abs_rectangleDiscrepancy_restrictToFinset_le_bad A B U Good
        hGood hagree S T
    rw [finiteLabeledCutDist, Fintype.card_coe]
    calc
      finiteLabeledCutRaw (A.restrictToFinset U) (B.restrictToFinset U) /
          (U.card : ℝ) ^ 2 ≤
        (2 * ((U \ Good).card : ℝ) * U.card) / (U.card : ℝ) ^ 2 := by
          gcongr
      _ = 2 * ((U \ Good).card : ℝ) / U.card := by field_simp

/-- Combined restriction estimate: compare the original graph to a reference
globally, then replace the reference by a model on the retained good set. -/
theorem finiteLabeledCutDist_restrictToFinset_le_cut_add_bad
    (G R P : FiniteWeightedGraph V) (U Good : Finset V) {beta : ℝ}
    (hGood : Good ⊆ U)
    (hagree : ∀ x ∈ Good, ∀ y ∈ Good, R.weight x y = P.weight x y)
    (hcut : finiteLabeledCutDist G R ≤ beta) :
    finiteLabeledCutDist (G.restrictToFinset U) (P.restrictToFinset U) ≤
      beta * (Fintype.card V : ℝ) ^ 2 / (U.card : ℝ) ^ 2 +
        2 * ((U \ Good).card : ℝ) / U.card := by
  by_cases hU : U.card = 0
  · have hUempty : U = ∅ := Finset.card_eq_zero.mp hU
    have hGP : G.restrictToFinset U = P.restrictToFinset U := by
      ext x
      have hx : False := by simpa [hUempty] using x.property
      exact hx.elim
    simp [hGP, hUempty]
  · have hUpos : 0 < (U.card : ℝ) := by positivity
    calc
      finiteLabeledCutDist (G.restrictToFinset U) (P.restrictToFinset U) ≤
          finiteLabeledCutDist (G.restrictToFinset U) (R.restrictToFinset U) +
            finiteLabeledCutDist (R.restrictToFinset U) (P.restrictToFinset U) :=
        finiteLabeledCutDist_triangle _ _ _
      _ ≤ beta * (Fintype.card V : ℝ) ^ 2 / (U.card : ℝ) ^ 2 +
          2 * ((U \ Good).card : ℝ) / U.card := by
        gcongr
        · apply (le_div_iff₀ (sq_pos_of_pos hUpos)).2
          calc
            finiteLabeledCutDist (G.restrictToFinset U) (R.restrictToFinset U) *
                (U.card : ℝ) ^ 2 ≤
              finiteLabeledCutDist G R * (Fintype.card V : ℝ) ^ 2 :=
                finiteLabeledCutDist_restrictToFinset_mul_card_sq_le G R U
            _ ≤ beta * (Fintype.card V : ℝ) ^ 2 := by gcongr
        · exact finiteLabeledCutDist_restrictToFinset_le_bad R P U Good
            hGood hagree

end DenseGraph.FiniteWeightedGraph
