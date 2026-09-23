import InducedStars.Graphon.BlockEqualization
import InducedStars.Graphon.OptimizerClassification

/-!
# Explicit multiplicity below the fixed-density transition

This file constructs a concrete two-block family in the subcritical candidate
class and separates its members by the measure of the positive-degree region.
That quantity is a genuine weak-isomorphism invariant: common
measure-preserving pullbacks preserve the whole distribution of graphon
degrees.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace InducedStars

/-! ## A graphon-equivalence invariant -/

/-- The degree of a point in the canonical representative of a graphon. -/
noncomputable def graphonDegree (W : Graphon) (x : UnitInterval) : ℝ :=
  ∫ y : UnitInterval, W.value (x, y)

theorem measurable_graphonDegree (W : Graphon) : Measurable (graphonDegree W) := by
  exact W.measurable_value.stronglyMeasurable.integral_prod_right'.measurable

/-- The distribution of graphon degrees. -/
noncomputable def graphonDegreeLaw (W : Graphon) : Measure ℝ :=
  Measure.map (graphonDegree W) volume

/-- The measure of points having positive graphon degree. -/
noncomputable def graphonPositiveDegreeMass (W : Graphon) : ℝ :=
  (graphonDegreeLaw W).real (Ioi (0 : ℝ))

private theorem integral_comp_measurePreserving
    {f : UnitInterval → UnitInterval}
    (hf : MeasurePreserving f volume volume)
    (g : UnitInterval → ℝ) (hg : Measurable g) :
    (∫ x, g (f x) ∂volume) = ∫ x, g x ∂volume := by
  calc
    (∫ x, g (f x) ∂volume) =
        ∫ x, g x ∂Measure.map f volume := by
      symm
      exact integral_map hf.measurable.aemeasurable hg.aestronglyMeasurable
    _ = ∫ x, g x ∂volume := by rw [hf.map_eq]

/-- Common measure-preserving pullbacks preserve the complete degree law. -/
theorem graphonDegreeLaw_eq_of_graphonEquivalent
    {U W : Graphon} (h : GraphonEquivalent U W) :
    graphonDegreeLaw U = graphonDegreeLaw W := by
  obtain ⟨φ, ψ, hφ, hψ, heq⟩ := h
  have heqRows : ∀ᵐ x ∂volume, ∀ᵐ y ∂volume,
      U.value (φ x, φ y) = W.value (ψ x, ψ y) :=
    Measure.ae_ae_of_ae_prod heq
  have hdegrees :
      (fun x ↦ graphonDegree U (φ x)) =ᵐ[volume]
        fun x ↦ graphonDegree W (ψ x) := by
    filter_upwards [heqRows] with x hx
    rw [graphonDegree, graphonDegree]
    calc
      (∫ y, U.value (φ x, y) ∂volume) =
          ∫ y, U.value (φ x, φ y) ∂volume := by
        symm
        exact integral_comp_measurePreserving hφ _
          (U.measurable_value.comp (measurable_const.prodMk measurable_id))
      _ = ∫ y, W.value (ψ x, ψ y) ∂volume := integral_congr_ae hx
      _ = ∫ y, W.value (ψ x, y) ∂volume :=
        integral_comp_measurePreserving hψ _
          (W.measurable_value.comp (measurable_const.prodMk measurable_id))
  have hU : HasLaw (graphonDegree U) (graphonDegreeLaw U) volume :=
    ⟨(measurable_graphonDegree U).aemeasurable, rfl⟩
  have hW : HasLaw (graphonDegree W) (graphonDegreeLaw W) volume :=
    ⟨(measurable_graphonDegree W).aemeasurable, rfl⟩
  have hUφ : HasLaw (graphonDegree U ∘ φ) (graphonDegreeLaw U) volume :=
    hU.comp hφ.hasLaw
  have hWψ : HasLaw (graphonDegree W ∘ ψ) (graphonDegreeLaw W) volume :=
    hW.comp hψ.hasLaw
  calc
    graphonDegreeLaw U =
        Measure.map (graphonDegree U ∘ φ) volume := hUφ.map_eq.symm
    _ = Measure.map (graphonDegree W ∘ ψ) volume := by
      apply Measure.map_congr
      filter_upwards [hdegrees] with x hx
      exact hx
    _ = graphonDegreeLaw W := hWψ.map_eq

/-- The positive-degree mass is invariant under the paper's graphon
equivalence relation. -/
theorem graphonPositiveDegreeMass_eq_of_graphonEquivalent
    {U W : Graphon} (h : GraphonEquivalent U W) :
    graphonPositiveDegreeMass U = graphonPositiveDegreeMass W := by
  rw [graphonPositiveDegreeMass, graphonPositiveDegreeMass,
    graphonDegreeLaw_eq_of_graphonEquivalent h]

/-! ## Positive-degree mass of a finite block sequence -/

/-- Degree computed directly from the raw block kernel. -/
noncomputable def AdmissibleBlockSequence.kernelDegree {k : ℕ}
    (L : AdmissibleBlockSequence k) (x : UnitInterval) : ℝ :=
  ∫ y : UnitInterval, L.kernel (x, y)

theorem AdmissibleBlockSequence.measurable_kernelDegree {k : ℕ}
    (L : AdmissibleBlockSequence k) : Measurable L.kernelDegree := by
  exact L.measurable_kernel.stronglyMeasurable.integral_prod_right'.measurable

theorem AdmissibleBlockSequence.integrable_kernel_row {k : ℕ}
    (L : AdmissibleBlockSequence k) (hk : 3 ≤ k) (x : UnitInterval) :
    Integrable (fun y : UnitInterval ↦ L.kernel (x, y)) := by
  apply Integrable.of_bound
    (L.measurable_kernel.comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
  filter_upwards [] with y
  change |L.kernel (x, y)| ≤ 1
  rw [abs_of_nonneg (L.kernel_mem_Icc hk (x, y)).1]
  exact (L.kernel_mem_Icc hk (x, y)).2

theorem AdmissibleBlockSequence.kernelDegree_nonneg {k : ℕ}
    (L : AdmissibleBlockSequence k) (hk : 3 ≤ k) (x : UnitInterval) :
    0 ≤ L.kernelDegree x := by
  exact integral_nonneg fun y ↦ (L.kernel_mem_Icc hk (x, y)).1

theorem AdmissibleBlockSequence.graphonDegree_ae_eq_kernelDegree {k : ℕ}
    (L : AdmissibleBlockSequence k) (hk : 3 ≤ k) :
    graphonDegree (L.graphon hk) =ᵐ[volume] L.kernelDegree := by
  have hsquare : (L.graphon hk).value =ᵐ[unitSquareMeasure] L.kernel := by
    calc
      (L.graphon hk).value =ᵐ[unitSquareMeasure] (L.graphon hk : UnitSquare → ℝ) :=
        (L.graphon hk).value_ae_eq
      _ =ᵐ[unitSquareMeasure] L.kernel := L.graphon_ae_eq_kernel hk
  filter_upwards [Measure.ae_ae_of_ae_prod hsquare] with x hx
  exact integral_congr_ae hx

private theorem alpha_pos_of_mem_blockCell {k : ℕ}
    (L : AdmissibleBlockSequence k) {i : ℕ}
    {v : Fin (L.core i).order} {x : UnitInterval}
    (hx : x ∈ L.blockCell i v) : 0 < L.alpha i := by
  have hne : L.alpha i ≠ 0 := by
    intro hzero
    have hempty := L.blockInterval_eq_empty_of_alpha_eq_zero i hzero
    have hxInterval := L.blockCell_subset_interval i v hx
    rw [hempty] at hxInterval
    exact hxInterval
  exact lt_of_le_of_ne (L.alpha_nonneg i) (Ne.symm hne)

theorem AdmissibleBlockSequence.kernelDegree_pos_of_mem_blockCell {k : ℕ}
    (L : AdmissibleBlockSequence k) (hk : 3 ≤ k)
    {i : ℕ} {v : Fin (L.core i).order} {x : UnitInterval}
    (hx : x ∈ L.blockCell i v) : 0 < L.kernelDegree x := by
  let S : Set UnitInterval := L.blockCell i v
  have hSmeas : MeasurableSet S := L.measurableSet_blockCell i v
  have hrow : Integrable (fun y : UnitInterval ↦ L.kernel (x, y)) :=
    L.integrable_kernel_row hk x
  have hminor : Integrable (S.indicator fun _ : UnitInterval ↦ (1 : ℝ)) :=
    (integrable_const (1 : ℝ)).indicator hSmeas
  have hle : ∀ y : UnitInterval,
      S.indicator (fun _ : UnitInterval ↦ (1 : ℝ)) y ≤ L.kernel (x, y) := by
    intro y
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy,
        L.kernel_eq_blockKernel_of_mem i (x, y)
          (L.blockCell_subset_interval i v hx),
        L.blockKernel_of_mem i v v (x, y) hx hy,
        xiMatrix_apply_eq]
    · rw [Set.indicator_of_notMem hy]
      exact (L.kernel_mem_Icc hk (x, y)).1
  have hlower : L.alpha i / (L.core i).order ≤ L.kernelDegree x := by
    calc
      L.alpha i / (L.core i).order =
          ∫ y : UnitInterval, S.indicator (fun _ ↦ (1 : ℝ)) y ∂volume := by
        rw [integral_indicator_const (1 : ℝ) hSmeas, smul_eq_mul,
          L.volumeReal_blockCell i v]
        ring
      _ ≤ ∫ y : UnitInterval, L.kernel (x, y) ∂volume :=
        integral_mono hminor hrow hle
      _ = L.kernelDegree x := rfl
  have horder : (0 : ℝ) < (L.core i).order := by
    exact_mod_cast (L.core i).order_pos
  exact lt_of_lt_of_le
    (div_pos (alpha_pos_of_mem_blockCell L hx) horder) hlower

theorem AdmissibleBlockSequence.kernelDegree_eq_zero_of_no_blockCell {k : ℕ}
    (L : AdmissibleBlockSequence k) (x : UnitInterval)
    (hx : ∀ i : ℕ, ∀ v : Fin (L.core i).order, x ∉ L.blockCell i v) :
    L.kernelDegree x = 0 := by
  unfold kernelDegree
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  exact L.kernel_eq_zero_of_no_leftCell (x, y) hx

theorem AdmissibleBlockSequence.kernelDegree_pos_iff_exists_mem_blockCell {k : ℕ}
    (L : AdmissibleBlockSequence k) (hk : 3 ≤ k) (x : UnitInterval) :
    0 < L.kernelDegree x ↔
      ∃ i : ℕ, ∃ v : Fin (L.core i).order, x ∈ L.blockCell i v := by
  constructor
  · intro hpos
    by_contra hnone
    push Not at hnone
    rw [L.kernelDegree_eq_zero_of_no_blockCell x hnone] at hpos
    exact lt_irrefl 0 hpos
  · rintro ⟨i, v, hx⟩
    exact L.kernelDegree_pos_of_mem_blockCell hk hx

/-- A two-block sequence has positive-degree mass equal to the sum of its two
block lengths. -/
theorem graphonPositiveDegreeMass_graphon_of_count_two {k : ℕ}
    (L : AdmissibleBlockSequence k) (hk : 3 ≤ k)
    (hcount : L.count = some 2) :
    graphonPositiveDegreeMass (L.graphon hk) = L.alpha 0 + L.alpha 1 := by
  have hmap : graphonDegreeLaw (L.graphon hk) =
      Measure.map L.kernelDegree volume := by
    unfold graphonDegreeLaw
    exact Measure.map_congr (L.graphonDegree_ae_eq_kernelDegree hk)
  have hregion : {x : UnitInterval | 0 < L.kernelDegree x} =
      L.blockCellUnion 0 ∪ L.blockCellUnion 1 := by
    ext x
    change (0 < L.kernelDegree x ↔
      x ∈ L.blockCellUnion 0 ∪ L.blockCellUnion 1)
    rw [L.kernelDegree_pos_iff_exists_mem_blockCell hk]
    constructor
    · rintro ⟨i, v, hx⟩
      have hi : i < 2 := by
        by_contra hi
        have halpha : L.alpha i = 0 :=
          L.alpha_eq_zero_of_count_eq_some hcount (Nat.le_of_not_gt hi)
        have hempty := L.blockInterval_eq_empty_of_alpha_eq_zero i halpha
        have hxInterval := L.blockCell_subset_interval i v hx
        rw [hempty] at hxInterval
        exact hxInterval
      have hi_cases : i = 0 ∨ i = 1 := by omega
      rcases hi_cases with rfl | rfl
      · exact Or.inl (Set.mem_iUnion.2 ⟨v, hx⟩)
      · exact Or.inr (Set.mem_iUnion.2 ⟨v, hx⟩)
    · rintro (hx | hx)
      · obtain ⟨v, hx⟩ := Set.mem_iUnion.1 hx
        exact ⟨0, v, hx⟩
      · obtain ⟨v, hx⟩ := Set.mem_iUnion.1 hx
        exact ⟨1, v, hx⟩
  have hdisj : Disjoint (L.blockCellUnion 0) (L.blockCellUnion 1) := by
    rw [Set.disjoint_left]
    intro x hx0 hx1
    exact Set.disjoint_left.1 (L.pairwise_disjoint_blockInterval (by omega))
      (L.blockCellUnion_subset_interval 0 hx0)
      (L.blockCellUnion_subset_interval 1 hx1)
  have hpre : L.kernelDegree ⁻¹' Ioi (0 : ℝ) =
      L.blockCellUnion 0 ∪ L.blockCellUnion 1 := by
    simpa only [Set.preimage, Set.mem_Ioi] using hregion
  rw [graphonPositiveDegreeMass, hmap, Measure.real,
    Measure.map_apply (L.measurable_kernelDegree)
      measurableSet_Ioi, hpre, ← Measure.real,
    measureReal_union hdisj (L.measurableSet_blockCellUnion 1),
    L.volumeReal_blockCellUnion 0, L.volumeReal_blockCellUnion 1]

/-! ## A reusable two-complete-block sequence -/

private def twoBlockAlpha (a b : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then a else if i = 1 then b else 0

private theorem hasSum_twoBlockAlpha (a b : ℝ) :
    HasSum (twoBlockAlpha a b) (a + b) := by
  have ha : HasSum (fun i : ℕ ↦ if i = 0 then a else 0) a := by
    simpa only [eq_comm] using hasSum_ite_eq (0 : ℕ) a
  have hb : HasSum (fun i : ℕ ↦ if i = 1 then b else 0) b := by
    simpa only [eq_comm] using hasSum_ite_eq (1 : ℕ) b
  convert ha.add hb using 1
  funext i
  simp only [twoBlockAlpha]
  by_cases hi0 : i = 0
  · subst i
    simp
  · by_cases hi1 : i = 1 <;> simp [hi0, hi1]

/-- The finite sequence with block lengths `a,b` and two copies of the
complete `(k-2)`-regular core. -/
def twoCompleteBlockSequence (k : ℕ) (hk : 3 ≤ k) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hsum : a + b ≤ 1) :
    AdmissibleBlockSequence k where
  count := some 2
  count_pos := by
    intro n hn
    have : n = 2 := by simpa using hn.symm
    omega
  alpha := twoBlockAlpha a b
  core := fun _ ↦ RegularBlockCore.complete k hk
  alpha_pos_of_active := by
    intro i hi
    have hi2 : i < 2 := by simpa [blockIndexActive] using hi
    have hi_cases : i = 0 ∨ i = 1 := by omega
    rcases hi_cases with rfl | rfl
    · simpa [twoBlockAlpha] using ha
    · simpa [twoBlockAlpha] using hb
  alpha_eq_zero_of_inactive := by
    intro i hi
    have hi2 : 2 ≤ i := by
      have hnot : ¬ i < 2 := by simpa [blockIndexActive] using hi
      omega
    have hi0 : i ≠ 0 := by omega
    have hi1 : i ≠ 1 := by omega
    simp [twoBlockAlpha, hi0, hi1]
  alpha_antitone := by
    intro i j hij
    by_cases hi0 : i = 0
    · subst i
      by_cases hj0 : j = 0
      · subst j
        rfl
      · by_cases hj1 : j = 1
        · subst j
          simpa [twoBlockAlpha] using hba
        · simpa [twoBlockAlpha, hj0, hj1] using ha.le
    · by_cases hi1 : i = 1
      · subst i
        have hj0 : j ≠ 0 := by omega
        by_cases hj1 : j = 1
        · subst j
          rfl
        · simpa [twoBlockAlpha, hj0, hj1] using hb.le
      · have hi2 : 2 ≤ i := by omega
        have hj2 : 2 ≤ j := hi2.trans hij
        have hj0 : j ≠ 0 := by omega
        have hj1 : j ≠ 1 := by omega
        simp [twoBlockAlpha, hi0, hi1, hj0, hj1]
  summable_alpha := (hasSum_twoBlockAlpha a b).summable
  tsum_alpha_le_one := by
    rw [(hasSum_twoBlockAlpha a b).tsum_eq]
    exact hsum

@[simp] theorem twoCompleteBlockSequence_count (k : ℕ) (hk : 3 ≤ k)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hsum : a + b ≤ 1) :
    (twoCompleteBlockSequence k hk a b ha hb hba hsum).count = some 2 :=
  rfl

@[simp] theorem twoCompleteBlockSequence_alpha_zero (k : ℕ) (hk : 3 ≤ k)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hsum : a + b ≤ 1) :
    (twoCompleteBlockSequence k hk a b ha hb hba hsum).alpha 0 = a := by
  simp [twoCompleteBlockSequence, twoBlockAlpha]

@[simp] theorem twoCompleteBlockSequence_alpha_one (k : ℕ) (hk : 3 ≤ k)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hsum : a + b ≤ 1) :
    (twoCompleteBlockSequence k hk a b ha hb hba hsum).alpha 1 = b := by
  simp [twoCompleteBlockSequence, twoBlockAlpha]

theorem blockSequenceMass_twoCompleteBlockSequence (k : ℕ) (hk : 3 ≤ k)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hsum : a + b ≤ 1) :
    blockSequenceMass (twoCompleteBlockSequence k hk a b ha hb hba hsum) =
      (a ^ 2 + b ^ 2) / (k - 1 : ℕ) := by
  rw [blockSequenceMass, tsum_eq_sum (s := Finset.range 2)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    simp [twoCompleteBlockSequence, twoBlockAlpha,
      RegularBlockCore.complete_order]
    ring
  · intro i hi
    have hi2 : 2 ≤ i := by
      have hnot : ¬ i < 2 := by simpa using hi
      omega
    have hi0 : i ≠ 0 := by omega
    have hi1 : i ≠ 1 := by omega
    simp [twoCompleteBlockSequence, twoBlockAlpha, hi0, hi1]

/-! ## Explicit subcritical parameters -/

/-- The fraction of the critical density used as total squared block mass. -/
noncomputable def subcriticalMultiplicityRatio (k : ℕ) (γ : ℝ) : ℝ :=
  γ / gammaK k

/-- Square root of the normalized subcritical density. -/
noncomputable def subcriticalMultiplicityRadius (k : ℕ) (γ : ℝ) : ℝ :=
  Real.sqrt (subcriticalMultiplicityRatio k γ)

/-- A uniform positive slack that keeps every two-block support inside the
unit interval and keeps the quadratic discriminant positive. -/
noncomputable def subcriticalMultiplicitySlack (k : ℕ) (γ : ℝ) : ℝ :=
  min ((1 - subcriticalMultiplicityRadius k γ) / 2)
    (subcriticalMultiplicityRadius k γ / 4)

/-- The strictly decreasing perturbation used at index `n`. -/
noncomputable def subcriticalMultiplicityShift (k : ℕ) (γ : ℝ)
    (n : ℕ) : ℝ :=
  subcriticalMultiplicitySlack k γ / (n + 1 : ℕ)

/-- Total support length of the `n`th two-block candidate. -/
noncomputable def subcriticalMultiplicitySupport (k : ℕ) (γ : ℝ)
    (n : ℕ) : ℝ :=
  subcriticalMultiplicityRadius k γ + subcriticalMultiplicityShift k γ n

/-- Difference between the two block lengths. -/
noncomputable def subcriticalMultiplicityDifference (k : ℕ) (γ : ℝ)
    (n : ℕ) : ℝ :=
  Real.sqrt (2 * subcriticalMultiplicityRatio k γ -
    subcriticalMultiplicitySupport k γ n ^ 2)

/-- Larger block length in the `n`th candidate. -/
noncomputable def subcriticalFirstBlockLength (k : ℕ) (γ : ℝ)
    (n : ℕ) : ℝ :=
  (subcriticalMultiplicitySupport k γ n +
    subcriticalMultiplicityDifference k γ n) / 2

/-- Smaller block length in the `n`th candidate. -/
noncomputable def subcriticalSecondBlockLength (k : ℕ) (γ : ℝ)
    (n : ℕ) : ℝ :=
  (subcriticalMultiplicitySupport k γ n -
    subcriticalMultiplicityDifference k γ n) / 2

theorem subcriticalMultiplicityRatio_pos {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) :
    0 < subcriticalMultiplicityRatio k γ := by
  exact div_pos hγ.1 (gammaK_pos hk)

theorem subcriticalMultiplicityRatio_lt_one {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) :
    subcriticalMultiplicityRatio k γ < 1 := by
  exact (div_lt_one (gammaK_pos hk)).2 hγ.2

theorem subcriticalMultiplicityRadius_pos {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) :
    0 < subcriticalMultiplicityRadius k γ := by
  rw [subcriticalMultiplicityRadius, Real.sqrt_pos]
  exact subcriticalMultiplicityRatio_pos hk hγ

theorem subcriticalMultiplicityRadius_sq {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) :
    subcriticalMultiplicityRadius k γ ^ 2 =
      subcriticalMultiplicityRatio k γ := by
  rw [subcriticalMultiplicityRadius, Real.sq_sqrt]
  exact (subcriticalMultiplicityRatio_pos hk hγ).le

theorem subcriticalMultiplicityRadius_lt_one {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) :
    subcriticalMultiplicityRadius k γ < 1 := by
  rw [subcriticalMultiplicityRadius, Real.sqrt_lt' zero_lt_one, one_pow]
  exact subcriticalMultiplicityRatio_lt_one hk hγ

theorem subcriticalMultiplicitySlack_pos {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) :
    0 < subcriticalMultiplicitySlack k γ := by
  rw [subcriticalMultiplicitySlack, lt_min_iff]
  exact ⟨
    div_pos (sub_pos.mpr (subcriticalMultiplicityRadius_lt_one hk hγ)) (by norm_num),
    div_pos (subcriticalMultiplicityRadius_pos hk hγ) (by norm_num)⟩

theorem subcriticalMultiplicityShift_pos {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    0 < subcriticalMultiplicityShift k γ n := by
  exact div_pos (subcriticalMultiplicitySlack_pos hk hγ) (by positivity)

theorem subcriticalMultiplicityShift_le_slack {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    subcriticalMultiplicityShift k γ n ≤ subcriticalMultiplicitySlack k γ := by
  unfold subcriticalMultiplicityShift
  apply div_le_self (subcriticalMultiplicitySlack_pos hk hγ).le
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

theorem subcriticalMultiplicityShift_le_one_sub_radius_div_two
    {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    subcriticalMultiplicityShift k γ n ≤
      (1 - subcriticalMultiplicityRadius k γ) / 2 := by
  exact (subcriticalMultiplicityShift_le_slack hk hγ n).trans
    (min_le_left _ _)

theorem subcriticalMultiplicityShift_le_radius_div_four
    {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    subcriticalMultiplicityShift k γ n ≤
      subcriticalMultiplicityRadius k γ / 4 := by
  exact (subcriticalMultiplicityShift_le_slack hk hγ n).trans
    (min_le_right _ _)

theorem subcriticalMultiplicitySupport_pos {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    0 < subcriticalMultiplicitySupport k γ n := by
  unfold subcriticalMultiplicitySupport
  exact add_pos (subcriticalMultiplicityRadius_pos hk hγ)
    (subcriticalMultiplicityShift_pos hk hγ n)

theorem subcriticalMultiplicityRadius_lt_support {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    subcriticalMultiplicityRadius k γ <
      subcriticalMultiplicitySupport k γ n := by
  unfold subcriticalMultiplicitySupport
  linarith [subcriticalMultiplicityShift_pos hk hγ n]

theorem subcriticalMultiplicitySupport_le_one {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    subcriticalMultiplicitySupport k γ n ≤ 1 := by
  unfold subcriticalMultiplicitySupport
  linarith [subcriticalMultiplicityShift_le_one_sub_radius_div_two hk hγ n,
    subcriticalMultiplicityRadius_lt_one hk hγ]

theorem subcriticalMultiplicityRatio_lt_support_sq {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    subcriticalMultiplicityRatio k γ <
      subcriticalMultiplicitySupport k γ n ^ 2 := by
  rw [← subcriticalMultiplicityRadius_sq hk hγ]
  exact (sq_lt_sq₀
    (subcriticalMultiplicityRadius_pos hk hγ).le
    (subcriticalMultiplicitySupport_pos hk hγ n).le).2
      (subcriticalMultiplicityRadius_lt_support hk hγ n)

theorem subcriticalMultiplicitySupport_sq_lt_two_ratio
    {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    subcriticalMultiplicitySupport k γ n ^ 2 <
      2 * subcriticalMultiplicityRatio k γ := by
  have hsbound : subcriticalMultiplicitySupport k γ n ≤
      5 * subcriticalMultiplicityRadius k γ / 4 := by
    unfold subcriticalMultiplicitySupport
    linarith [subcriticalMultiplicityShift_le_radius_div_four hk hγ n]
  have hsquare : subcriticalMultiplicitySupport k γ n ^ 2 ≤
      (5 * subcriticalMultiplicityRadius k γ / 4) ^ 2 :=
    (sq_le_sq₀ (subcriticalMultiplicitySupport_pos hk hγ n).le
      (div_nonneg
        (mul_nonneg (by norm_num) (subcriticalMultiplicityRadius_pos hk hγ).le)
        (by norm_num))).2 hsbound
  nlinarith [subcriticalMultiplicityRadius_sq hk hγ,
    subcriticalMultiplicityRatio_pos hk hγ]

theorem subcriticalMultiplicityDifference_pos {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    0 < subcriticalMultiplicityDifference k γ n := by
  rw [subcriticalMultiplicityDifference, Real.sqrt_pos]
  linarith [subcriticalMultiplicitySupport_sq_lt_two_ratio hk hγ n]

theorem subcriticalMultiplicityDifference_sq {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    subcriticalMultiplicityDifference k γ n ^ 2 =
      2 * subcriticalMultiplicityRatio k γ -
        subcriticalMultiplicitySupport k γ n ^ 2 := by
  rw [subcriticalMultiplicityDifference, Real.sq_sqrt]
  linarith [subcriticalMultiplicitySupport_sq_lt_two_ratio hk hγ n]

theorem subcriticalMultiplicityDifference_lt_support {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    subcriticalMultiplicityDifference k γ n <
      subcriticalMultiplicitySupport k γ n := by
  apply (sq_lt_sq₀ (subcriticalMultiplicityDifference_pos hk hγ n).le
    (subcriticalMultiplicitySupport_pos hk hγ n).le).1
  rw [subcriticalMultiplicityDifference_sq hk hγ n]
  linarith [subcriticalMultiplicityRatio_lt_support_sq hk hγ n]

theorem subcriticalFirstBlockLength_pos {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    0 < subcriticalFirstBlockLength k γ n := by
  unfold subcriticalFirstBlockLength
  exact div_pos
    (add_pos (subcriticalMultiplicitySupport_pos hk hγ n)
      (subcriticalMultiplicityDifference_pos hk hγ n)) (by norm_num)

theorem subcriticalSecondBlockLength_pos {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    0 < subcriticalSecondBlockLength k γ n := by
  unfold subcriticalSecondBlockLength
  linarith [subcriticalMultiplicityDifference_lt_support hk hγ n]

theorem subcriticalSecondBlockLength_le_first {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    subcriticalSecondBlockLength k γ n ≤
      subcriticalFirstBlockLength k γ n := by
  unfold subcriticalSecondBlockLength subcriticalFirstBlockLength
  linarith [subcriticalMultiplicityDifference_pos hk hγ n]

theorem subcriticalBlockLengths_sum {k : ℕ} (_hk : 3 ≤ k)
    {γ : ℝ} (_hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    subcriticalFirstBlockLength k γ n +
      subcriticalSecondBlockLength k γ n =
        subcriticalMultiplicitySupport k γ n := by
  unfold subcriticalFirstBlockLength subcriticalSecondBlockLength
  ring

theorem subcriticalBlockLengths_sq_sum {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    subcriticalFirstBlockLength k γ n ^ 2 +
      subcriticalSecondBlockLength k γ n ^ 2 =
        subcriticalMultiplicityRatio k γ := by
  have hd := subcriticalMultiplicityDifference_sq hk hγ n
  unfold subcriticalFirstBlockLength subcriticalSecondBlockLength
  nlinarith

theorem strictAnti_subcriticalMultiplicitySupport {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) :
    StrictAnti (subcriticalMultiplicitySupport k γ) := by
  intro m n hmn
  unfold subcriticalMultiplicitySupport subcriticalMultiplicityShift
  have hden : ((m + 1 : ℕ) : ℝ) < (n + 1 : ℕ) := by
    exact_mod_cast Nat.add_lt_add_right hmn 1
  have hdiv := div_lt_div_of_pos_left
    (subcriticalMultiplicitySlack_pos hk hγ)
    (by positivity : (0 : ℝ) < (m + 1 : ℕ)) hden
  linarith

/-! ## The optimizer sequence -/

/-- The explicit two-complete-core block sequence at index `n`. -/
noncomputable def subcriticalTwoBlockSequence
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    AdmissibleBlockSequence k :=
  twoCompleteBlockSequence k hk
    (subcriticalFirstBlockLength k γ n)
    (subcriticalSecondBlockLength k γ n)
    (subcriticalFirstBlockLength_pos hk hγ n)
    (subcriticalSecondBlockLength_pos hk hγ n)
    (subcriticalSecondBlockLength_le_first hk hγ n)
    (by
      rw [subcriticalBlockLengths_sum hk hγ n]
      exact subcriticalMultiplicitySupport_le_one hk hγ n)

@[simp] theorem subcriticalTwoBlockSequence_count
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    (subcriticalTwoBlockSequence k hk γ hγ n).count = some 2 :=
  rfl

@[simp] theorem subcriticalTwoBlockSequence_alpha_zero
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    (subcriticalTwoBlockSequence k hk γ hγ n).alpha 0 =
      subcriticalFirstBlockLength k γ n := by
  simp [subcriticalTwoBlockSequence]

@[simp] theorem subcriticalTwoBlockSequence_alpha_one
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    (subcriticalTwoBlockSequence k hk γ hγ n).alpha 1 =
      subcriticalSecondBlockLength k γ n := by
  simp [subcriticalTwoBlockSequence]

theorem subcriticalTwoBlockSequence_isCandidate
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    IsSubcriticalCandidate k γ
      (subcriticalTwoBlockSequence k hk γ hγ n) := by
  rw [IsSubcriticalCandidate]
  unfold subcriticalTwoBlockSequence
  rw [blockSequenceMass_twoCompleteBlockSequence,
    subcriticalBlockLengths_sq_sum hk hγ n]
  unfold subcriticalMultiplicityRatio
  rw [div_div, gammaK_mul_denominator k hk]

/-- The explicit sequence of subcritical graphons.  Every member consists of
exactly two copies of the complete `(k-2)`-regular core. -/
noncomputable def subcriticalOptimizerSequence
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) : ℕ → Graphon :=
  fun n ↦ WLambda hk (subcriticalTwoBlockSequence k hk γ hγ n)

theorem subcriticalOptimizerSequence_mem_candidate
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    subcriticalOptimizerSequence k hk γ hγ n ∈
      candidateOptimizerFamily k γ := by
  have hγfull : γ ∈ Ioo (0 : ℝ) 1 :=
    ⟨hγ.1, hγ.2.trans (gammaK_lt_one hk)⟩
  rw [candidateOptimizerFamily_of_lt hk hγfull hγ.2]
  exact ⟨subcriticalTwoBlockSequence k hk γ hγ n,
    subcriticalTwoBlockSequence_isCandidate k hk γ hγ n, rfl⟩

theorem subcriticalOptimizerSequence_mem_fixedDensityOptimizers
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    subcriticalOptimizerSequence k hk γ hγ n ∈
      fixedDensityOptimizers k γ := by
  have hγfull : γ ∈ Ioo (0 : ℝ) 1 :=
    ⟨hγ.1, hγ.2.trans (gammaK_lt_one hk)⟩
  exact candidate_mem_fixedDensityOptimizers k hk γ hγfull
    (subcriticalOptimizerSequence_mem_candidate k hk γ hγ n)

/-- The separating invariant of the `n`th optimizer is its explicitly chosen
support length. -/
theorem graphonPositiveDegreeMass_subcriticalOptimizerSequence
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    graphonPositiveDegreeMass
        (subcriticalOptimizerSequence k hk γ hγ n) =
      subcriticalMultiplicitySupport k γ n := by
  rw [subcriticalOptimizerSequence, WLambda]
  rw [graphonPositiveDegreeMass_graphon_of_count_two
    (subcriticalTwoBlockSequence k hk γ hγ n) hk rfl]
  rw [subcriticalTwoBlockSequence_alpha_zero,
    subcriticalTwoBlockSequence_alpha_one,
    subcriticalBlockLengths_sum hk hγ n]

theorem subcriticalOptimizerSequence_pairwise_not_graphonEquivalent
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k))
    {m n : ℕ} (hmn : m ≠ n) :
    ¬ GraphonEquivalent
      (subcriticalOptimizerSequence k hk γ hγ m)
      (subcriticalOptimizerSequence k hk γ hγ n) := by
  intro hequiv
  have hinvariant := graphonPositiveDegreeMass_eq_of_graphonEquivalent hequiv
  rw [graphonPositiveDegreeMass_subcriticalOptimizerSequence,
    graphonPositiveDegreeMass_subcriticalOptimizerSequence] at hinvariant
  exact hmn ((strictAnti_subcriticalMultiplicitySupport hk hγ).injective hinvariant)

/-- Below the transition, the fixed-density optimizer set contains an
explicit countable sequence of pairwise non-equivalent graphons. -/
theorem exists_pairwiseNonEquivalent_subcriticalOptimizers
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) (gammaK k)) :
    ∃ Wseq : ℕ → Graphon,
      (∀ n, Wseq n ∈ fixedDensityOptimizers k γ) ∧
      ∀ ⦃m n : ℕ⦄, m ≠ n → ¬ GraphonEquivalent (Wseq m) (Wseq n) := by
  refine ⟨subcriticalOptimizerSequence k hk γ hγ, ?_, ?_⟩
  · exact subcriticalOptimizerSequence_mem_fixedDensityOptimizers k hk γ hγ
  · intro m n hmn
    exact subcriticalOptimizerSequence_pairwise_not_graphonEquivalent
      k hk γ hγ hmn

end InducedStars
