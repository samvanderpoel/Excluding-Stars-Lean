import InducedStars.Analysis.Entropy
import InducedStars.Graphon.StepEstimates
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Entropy and edge-density functionals for graphons

This file defines the two scalar graphon functionals used in the fixed-density
variational problem.  Both use the canonical pointwise-bounded representative
`Graphon.value`, so their definitions are independent of choices of an `L¹`
representative.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace InducedStars

/-! ## Constant graphons -/

/-- The constant graphon with value `p ∈ [0,1]`. -/
noncomputable def constantGraphon (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) : Graphon :=
  Graphon.ofFun (fun _ : UnitSquare ↦ p) (integrable_const p)
    (ae_of_all _ fun _ ↦ hp.1) (ae_of_all _ fun _ ↦ hp.2) (fun _ ↦ rfl)

/-- The chosen `L¹` representative of a constant graphon is a.e. constant. -/
theorem constantGraphon_ae_eq (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂unitSquareMeasure, constantGraphon p hp z = p := by
  exact Graphon.coe_ofFun (fun _ : UnitSquare ↦ p) (integrable_const p)
    (ae_of_all _ fun _ ↦ hp.1) (ae_of_all _ fun _ ↦ hp.2) (fun _ ↦ rfl)

/-- The zero graphon. -/
noncomputable def zeroGraphon : Graphon :=
  constantGraphon 0 ⟨le_rfl, zero_le_one⟩

/-- The one graphon. -/
noncomputable def oneGraphon : Graphon :=
  constantGraphon 1 ⟨zero_le_one, le_rfl⟩

theorem zeroGraphon_ae_eq :
    ∀ᵐ z ∂unitSquareMeasure, zeroGraphon z = 0 := by
  simpa only [zeroGraphon] using
    constantGraphon_ae_eq 0 (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)

theorem oneGraphon_ae_eq :
    ∀ᵐ z ∂unitSquareMeasure, oneGraphon z = 1 := by
  simpa only [oneGraphon] using
    constantGraphon_ae_eq 1 (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)

/-! ## Scalar observables and graphon entropy -/

/-- Integral of a scalar observable of the canonical graphon value.

This is the shared low-level functional behind entropy and relative entropy.
It deliberately imposes no global measurability or integrability hypotheses:
individual APIs state the hypotheses needed for their own theorems, while
Mathlib's integral remains total for every function. -/
noncomputable def graphonValueFunctional (f : ℝ → ℝ) (W : Graphon) : ℝ :=
  ∫ z : UnitSquare, f (W.value z) ∂unitSquareMeasure

/-- The paper's graphon entropy, with scalar entropy measured in bits. -/
noncomputable def graphonEntropy (W : Graphon) : ℝ :=
  graphonValueFunctional binaryEntropy W

/-- Base-two binary entropy is at most one. -/
lemma binaryEntropy_le_one (p : ℝ) : binaryEntropy p ≤ 1 := by
  rw [binaryEntropy, div_le_one realLogTwo_pos]
  exact Real.binEntropy_le_log_two

/-- The entropy integrand of a graphon is integrable. -/
theorem integrable_binaryEntropy_value (W : Graphon) :
    Integrable (fun z : UnitSquare ↦ binaryEntropy (W.value z)) unitSquareMeasure := by
  refine Integrable.of_bound
    (binaryEntropy_continuous.measurable.comp W.measurable_value).aestronglyMeasurable 1 ?_
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (binaryEntropy_nonneg (W.value_nonneg z) (W.value_le_one z))]
  exact binaryEntropy_le_one _

/-- Graphon entropy is nonnegative. -/
theorem graphonEntropy_nonneg (W : Graphon) : 0 ≤ graphonEntropy W := by
  exact integral_nonneg fun z ↦
    binaryEntropy_nonneg (W.value_nonneg z) (W.value_le_one z)

/-- The zero graphon has zero entropy. -/
@[simp] theorem graphonEntropy_zero : graphonEntropy zeroGraphon = 0 := by
  unfold graphonEntropy graphonValueFunctional
  apply integral_eq_zero_of_ae
  filter_upwards [zeroGraphon.value_ae_eq, zeroGraphon_ae_eq] with z hzValue hzZero
  simp [hzValue, hzZero]

/-- The one graphon has zero entropy. -/
@[simp] theorem graphonEntropy_one : graphonEntropy oneGraphon = 0 := by
  unfold graphonEntropy graphonValueFunctional
  apply integral_eq_zero_of_ae
  filter_upwards [oneGraphon.value_ae_eq, oneGraphon_ae_eq] with z hzValue hzOne
  simp [hzValue, hzOne]

/-- Explicit equality invariance of graphon entropy. -/
theorem graphonEntropy_congr {W U : Graphon} (h : W = U) :
    graphonEntropy W = graphonEntropy U := by
  subst h
  rfl

/-- An a.e. equality of graphon representatives implies equality of entropy. -/
theorem graphonEntropy_eq_of_ae_eq {W U : Graphon}
    (h : ∀ᵐ z ∂unitSquareMeasure, W z = U z) :
    graphonEntropy W = graphonEntropy U :=
  graphonEntropy_congr (Graphon.ext h)

/-- Exact entropy contribution of one equal-cell rectangle. -/
private theorem setIntegral_entropy_matrixGraphon_equalCell {q : ℕ}
    (M : Matrix (Fin q) (Fin q) ℝ) (hM : M.IsSymm)
    (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (i j : Fin q) :
    ∫ z in equalCell i ×ˢ equalCell j,
        binaryEntropy ((matrixGraphon M hM hM₀ hM₁).value z) ∂unitSquareMeasure =
      (1 / (q : ℝ)) ^ 2 * binaryEntropy (M i j) := by
  let W := matrixGraphon M hM hM₀ hM₁
  let R : Set UnitSquare := equalCell i ×ˢ equalCell j
  calc
    (∫ z in R, binaryEntropy (W.value z) ∂unitSquareMeasure) =
        ∫ _z in R, binaryEntropy (M i j) ∂unitSquareMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem ((measurableSet_equalCell i).prod
          (measurableSet_equalCell j)),
        ae_restrict_of_ae W.value_ae_eq,
        ae_restrict_of_ae (matrixGraphon_ae_eq_on_cell M hM hM₀ hM₁ i j)]
        with z hzR hzValue hzCell
      rw [hzValue, hzCell hzR]
    _ = (unitSquareMeasure R).toReal * binaryEntropy (M i j) := by
      rw [integral_const]
      simp [smul_eq_mul, Measure.real_def]
    _ = (1 / (q : ℝ)) ^ 2 * binaryEntropy (M i j) := by
      rw [show unitSquareMeasure R = ENNReal.ofReal (1 / (q : ℝ)) ^ 2 by
        exact volume_equalCell_prod i j]
      rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal]
      positivity

/-- Entropy of an equal-cell matrix graphon is the ordered average of the
entry entropies. -/
theorem graphonEntropy_matrixGraphon {q : ℕ} (hq : 0 < q)
    (M : Matrix (Fin q) (Fin q) ℝ) (hM : M.IsSymm)
    (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1) :
    graphonEntropy (matrixGraphon M hM hM₀ hM₁) =
      (1 / (q : ℝ)) ^ 2 * ∑ i : Fin q, ∑ j : Fin q, binaryEntropy (M i j) := by
  unfold graphonEntropy graphonValueFunctional
  rw [integral_eq_setIntegral (ae_mem_iUnion_equalCell_prod hq)]
  rw [integral_iUnion_fintype]
  · simp_rw [setIntegral_entropy_matrixGraphon_equalCell]
    rw [← Finset.mul_sum, Fintype.sum_prod_type]
  · intro p
    exact (measurableSet_equalCell p.1).prod (measurableSet_equalCell p.2)
  · exact pairwise_disjoint_equalCell_prod
  · intro p
    exact (integrable_binaryEntropy_value (matrixGraphon M hM hM₀ hM₁)).integrableOn

/-! ## Edge density -/

/-- The canonical one-edge graph is the complete graph on `Fin 2`. -/
abbrev oneEdgeGraph : SimpleGraph (Fin 2) :=
  SimpleGraph.completeGraph (Fin 2)

/-- The canonical one-edge graph has exactly one unordered edge. -/
theorem finiteGraphEdges_oneEdgeGraph :
    finiteGraphEdges oneEdgeGraph = {s(0, 1)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ i j => fin_cases i <;> fin_cases j <;> simp [oneEdgeGraph]

/-- The edge-product integrand for `K₂` is just one graphon value. -/
theorem graphonHomIntegrand_oneEdgeGraph (W : Graphon) (x : Fin 2 → UnitInterval) :
    graphonHomIntegrand oneEdgeGraph W x = W.value (x 0, x 1) := by
  rw [graphonHomIntegrand, finiteGraphEdges_oneEdgeGraph]
  simp

/-- The paper's ordered-square edge density `t(K₂,W)`. -/
noncomputable def graphonEdgeDensity (W : Graphon) : ℝ :=
  graphonHomDensity oneEdgeGraph W

/-- Edge density is the integral of the canonical graphon representative. -/
theorem graphonEdgeDensity_eq_integral_value (W : Graphon) :
    graphonEdgeDensity W =
      ∫ z : UnitSquare, W.value z ∂unitSquareMeasure := by
  unfold graphonEdgeDensity graphonHomDensity
  simp_rw [graphonHomIntegrand_oneEdgeGraph]
  exact (volume_preserving_finTwoArrow UnitInterval).integral_comp' W.value

/-- Edge density is also the integral of the underlying `L¹` representative. -/
theorem graphonEdgeDensity_eq_integral (W : Graphon) :
    graphonEdgeDensity W = ∫ z : UnitSquare, W z ∂unitSquareMeasure := by
  rw [graphonEdgeDensity_eq_integral_value]
  exact integral_congr_ae W.value_ae_eq

/-- Edge density of an equal-cell matrix graphon is the ordered average of
its entries. -/
theorem graphonEdgeDensity_matrixGraphon {q : ℕ} (hq : 0 < q)
    (M : Matrix (Fin q) (Fin q) ℝ) (hM : M.IsSymm)
    (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1) :
    graphonEdgeDensity (matrixGraphon M hM hM₀ hM₁) =
      (1 / (q : ℝ)) ^ 2 * ∑ i : Fin q, ∑ j : Fin q, M i j := by
  rw [graphonEdgeDensity_eq_integral,
    integral_graphon_eq_sum_equalCell_prod hq]
  simp_rw [integral_matrixGraphon_equalCell]
  rw [← Finset.mul_sum, Fintype.sum_prod_type]

end InducedStars
