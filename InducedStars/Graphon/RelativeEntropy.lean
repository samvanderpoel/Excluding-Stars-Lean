import InducedStars.Analysis.RelativeEntropy
import InducedStars.Analysis.RateMinimization
import InducedStars.Graphon.EntropyUpperBound
import InducedStars.Graphon.Equivalence

/-!
# Relative entropy of graphons

This file formalizes the graphon-functional part of the paper's conditioned
`G(n,p)` variational problem.  It integrates the scalar base-two binary
relative entropy, proves the exact entropy/edge-density decomposition, treats
the two endpoint densities without extending the fixed-density classification,
and reduces an induced-star-free graphon to the scalar rate at its edge
density.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace InducedStars

/-! ## The graphon relative-entropy functional -/

/-- The paper's graphon relative entropy, in bits. -/
noncomputable def graphonRelativeEntropy (p : ℝ) (W : Graphon) : ℝ :=
  graphonValueFunctional (binaryRelativeEntropy p) W

/-- The graphon relative-entropy integrand is integrable for an interior
reference probability. -/
theorem integrable_binaryRelativeEntropy_value
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (W : Graphon) :
    Integrable (fun z : UnitSquare ↦ binaryRelativeEntropy p (W.value z))
      unitSquareMeasure := by
  have hpointwise :
      (fun z : UnitSquare ↦ binaryRelativeEntropy p (W.value z)) =
        fun z ↦ -binaryEntropy (W.value z) +
          W.value z * log2 ((1 - p) / p) - log2 (1 - p) := by
    funext z
    exact binaryRelativeEntropy_eq_negEntropy_add hp (W.value_mem_Icc z)
  rw [hpointwise]
  exact ((integrable_binaryEntropy_value W).neg.add
      (W.integrable_value.mul_const _)).sub (integrable_const _)

/-- Graphon relative entropy is nonnegative. -/
theorem graphonRelativeEntropy_nonneg
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (W : Graphon) :
    0 ≤ graphonRelativeEntropy p W := by
  exact integral_nonneg fun z ↦
    binaryRelativeEntropy_nonneg hp (W.value_mem_Icc z)

/-- Exact graphon version of the relative-entropy/entropy decomposition in
the proof of Paper Equation `eqn:sup-gamma-calc`. -/
theorem graphonRelativeEntropy_eq_negEntropy_add_edge
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (W : Graphon) :
    graphonRelativeEntropy p W =
      -graphonEntropy W +
        graphonEdgeDensity W * log2 ((1 - p) / p) -
          log2 (1 - p) := by
  unfold graphonRelativeEntropy graphonEntropy graphonValueFunctional
  calc
    (∫ z : UnitSquare, binaryRelativeEntropy p (W.value z)
        ∂unitSquareMeasure) =
        ∫ z : UnitSquare,
          (-binaryEntropy (W.value z) +
            W.value z * log2 ((1 - p) / p) - log2 (1 - p))
            ∂unitSquareMeasure := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact binaryRelativeEntropy_eq_negEntropy_add hp (W.value_mem_Icc z)
    _ = -(∫ z : UnitSquare, binaryEntropy (W.value z)
            ∂unitSquareMeasure) +
          (∫ z : UnitSquare, W.value z ∂unitSquareMeasure) *
            log2 ((1 - p) / p) - log2 (1 - p) := by
      rw [integral_sub, integral_add, integral_neg, integral_mul_const,
        integral_const]
      · simp
      · exact (integrable_binaryEntropy_value W).neg
      · exact W.integrable_value.mul_const _
      · exact ((integrable_binaryEntropy_value W).neg.add
          (W.integrable_value.mul_const _))
      · exact integrable_const _
    _ = -(∫ z : UnitSquare, binaryEntropy (W.value z)
            ∂unitSquareMeasure) +
          graphonEdgeDensity W * log2 ((1 - p) / p) -
            log2 (1 - p) := by
      rw [graphonEdgeDensity_eq_integral_value]

/-- Relative entropy vanishes precisely for the constant graphon at the
reference probability. -/
theorem graphonRelativeEntropy_eq_zero_iff
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (W : Graphon) :
    graphonRelativeEntropy p W = 0 ↔
      W = constantGraphon p ⟨hp.1.le, hp.2.le⟩ := by
  constructor
  · intro hzero
    have hae :
        (fun z : UnitSquare ↦ binaryRelativeEntropy p (W.value z))
          =ᵐ[unitSquareMeasure] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun z ↦ binaryRelativeEntropy_nonneg hp (W.value_mem_Icc z))
        (integrable_binaryRelativeEntropy_value hp W)).1 hzero
    apply Graphon.ext
    filter_upwards [hae, W.value_ae_eq,
      constantGraphon_ae_eq p ⟨hp.1.le, hp.2.le⟩] with z hz hW hconst
    have hvalue : W.value z = p :=
      (binaryRelativeEntropy_eq_zero_iff hp (W.value_mem_Icc z)).1 hz
    rw [← hW, hvalue, hconst]
  · rintro rfl
    unfold graphonRelativeEntropy graphonValueFunctional
    apply integral_eq_zero_of_ae
    filter_upwards [
      (constantGraphon p ⟨hp.1.le, hp.2.le⟩).value_ae_eq,
      constantGraphon_ae_eq p ⟨hp.1.le, hp.2.le⟩] with z hzValue hzConst
    rw [hzValue, hzConst]
    exact (binaryRelativeEntropy_eq_zero_iff hp ⟨hp.1.le, hp.2.le⟩).2 rfl

/-! ## Constant graphons and edge-density endpoints -/

@[simp] theorem graphonEdgeDensity_zeroGraphon :
    graphonEdgeDensity zeroGraphon = 0 := by
  rw [graphonEdgeDensity_eq_integral_value]
  apply integral_eq_zero_of_ae
  filter_upwards [zeroGraphon.value_ae_eq, zeroGraphon_ae_eq] with z hzValue hzZero
  exact hzValue.trans hzZero

@[simp] theorem graphonEdgeDensity_oneGraphon :
    graphonEdgeDensity oneGraphon = 1 := by
  rw [graphonEdgeDensity_eq_integral_value]
  calc
    (∫ z : UnitSquare, oneGraphon.value z ∂unitSquareMeasure) =
        ∫ _z : UnitSquare, (1 : ℝ) ∂unitSquareMeasure := by
      apply integral_congr_ae
      filter_upwards [oneGraphon.value_ae_eq, oneGraphon_ae_eq]
        with z hzValue hzOne
      rw [hzValue, hzOne]
    _ = 1 := by simp

/-- Exact relative entropy of the zero graphon. -/
theorem graphonRelativeEntropy_zeroGraphon
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    graphonRelativeEntropy p zeroGraphon = log2 (1 / (1 - p)) := by
  unfold graphonRelativeEntropy graphonValueFunctional
  calc
    (∫ z : UnitSquare, binaryRelativeEntropy p (zeroGraphon.value z)
        ∂unitSquareMeasure) =
        ∫ _z : UnitSquare, binaryRelativeEntropy p 0
          ∂unitSquareMeasure := by
      apply integral_congr_ae
      filter_upwards [zeroGraphon.value_ae_eq, zeroGraphon_ae_eq]
        with z hzValue hzZero
      rw [hzValue, hzZero]
    _ = log2 (1 / (1 - p)) := by
      rw [binaryRelativeEntropy_zero_eq_log2_inv hp]
      simp

/-- Exact relative entropy of the one graphon. -/
theorem graphonRelativeEntropy_oneGraphon
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    graphonRelativeEntropy p oneGraphon = log2 (1 / p) := by
  unfold graphonRelativeEntropy graphonValueFunctional
  calc
    (∫ z : UnitSquare, binaryRelativeEntropy p (oneGraphon.value z)
        ∂unitSquareMeasure) =
        ∫ _z : UnitSquare, binaryRelativeEntropy p 1
          ∂unitSquareMeasure := by
      apply integral_congr_ae
      filter_upwards [oneGraphon.value_ae_eq, oneGraphon_ae_eq]
        with z hzValue hzOne
      rw [hzValue, hzOne]
    _ = log2 (1 / p) := by
      rw [binaryRelativeEntropy_one_eq_log2_inv hp]
      simp

/-- Graphon relative entropy is invariant under cut-distance-zero
equivalence. -/
theorem graphonRelativeEntropy_eq_of_cutDist_eq_zero
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (U W : Graphon) (hcut : cutDist U W = 0) :
    graphonRelativeEntropy p U = graphonRelativeEntropy p W := by
  rw [graphonRelativeEntropy_eq_negEntropy_add_edge hp,
    graphonRelativeEntropy_eq_negEntropy_add_edge hp,
    graphonEntropy_eq_of_cutDist_eq_zero U W hcut,
    graphonEdgeDensity_eq_of_cutDist_eq_zero U W hcut]

/-- Every graphon's ordered-square edge density lies in the unit interval. -/
theorem graphonEdgeDensity_mem_Icc (W : Graphon) :
    graphonEdgeDensity W ∈ Icc (0 : ℝ) 1 :=
  graphonHomDensity_mem_Icc oneEdgeGraph W

/-- Edge density zero rigidly determines the zero graphon as an `L¹` object. -/
theorem graphonEdgeDensity_eq_zero_iff (W : Graphon) :
    graphonEdgeDensity W = 0 ↔ W = zeroGraphon := by
  constructor
  · intro hedge
    have hint : ∫ z : UnitSquare, W.value z ∂unitSquareMeasure = 0 := by
      rw [← graphonEdgeDensity_eq_integral_value]
      exact hedge
    have hae : W.value =ᵐ[unitSquareMeasure]
        (fun _ : UnitSquare ↦ (0 : ℝ)) :=
      (integral_eq_zero_iff_of_nonneg
        (fun z ↦ W.value_nonneg z) W.integrable_value).1 hint
    apply Graphon.ext
    filter_upwards [hae, W.value_ae_eq, zeroGraphon_ae_eq]
      with z hz hW hzero
    rw [← hW, hz, hzero]
  · rintro rfl
    exact graphonEdgeDensity_zeroGraphon

/-- Edge density one rigidly determines the one graphon as an `L¹` object. -/
theorem graphonEdgeDensity_eq_one_iff (W : Graphon) :
    graphonEdgeDensity W = 1 ↔ W = oneGraphon := by
  constructor
  · intro hedge
    have hint :
        ∫ z : UnitSquare, (1 - W.value z) ∂unitSquareMeasure = 0 := by
      rw [integral_sub (integrable_const (1 : ℝ)) W.integrable_value,
        ← graphonEdgeDensity_eq_integral_value]
      simp [hedge]
    have hae : (fun z : UnitSquare ↦ 1 - W.value z)
        =ᵐ[unitSquareMeasure] (fun _ : UnitSquare ↦ (0 : ℝ)) :=
      (integral_eq_zero_iff_of_nonneg
        (fun z ↦ sub_nonneg.mpr (W.value_le_one z))
        ((integrable_const (1 : ℝ)).sub W.integrable_value)).1 hint
    apply Graphon.ext
    filter_upwards [hae, W.value_ae_eq, oneGraphon_ae_eq]
      with z hz hW hone
    have hvalue : W.value z = 1 := by linarith
    rw [← hW, hvalue, hone]
  · rintro rfl
    exact graphonEdgeDensity_oneGraphon

/-! ## Endpoint induced-star freeness -/

/-- The zero graphon has zero induced-star density as soon as the star has an
edge. -/
theorem graphonInducedDensity_inducedStar_zeroGraphon
    (k : ℕ) (hk : 1 ≤ k) :
    graphonInducedDensity (inducedStar k) zeroGraphon = 0 := by
  classical
  let a : Fin k := ⟨0, by omega⟩
  have hne : (0 : Fin (k + 1)) ≠ a.succ := (Fin.succ_ne_zero a).symm
  have hvalue : zeroGraphon.value =ᵐ[unitSquareMeasure]
      (fun _ : UnitSquare ↦ (0 : ℝ)) :=
    Filter.EventuallyEq.trans zeroGraphon.value_ae_eq zeroGraphon_ae_eq
  have hpull :
      (fun x : Fin (k + 1) → UnitInterval ↦
          zeroGraphon.value (x 0, x a.succ)) =ᵐ[volume]
        fun _ ↦ (0 : ℝ) := by
    change (zeroGraphon.value ∘
      fun x : Fin (k + 1) → UnitInterval ↦ (x 0, x a.succ))
        =ᵐ[volume]
      ((fun _ : UnitSquare ↦ (0 : ℝ)) ∘
        fun x : Fin (k + 1) → UnitInterval ↦ (x 0, x a.succ))
    exact (measurePreserving_pairProjection hne).quasiMeasurePreserving.ae_eq_comp hvalue
  unfold graphonInducedDensity
  apply integral_eq_zero_of_ae
  filter_upwards [hpull] with x hx
  have hEdge : s(0, a.succ) ∈ finiteGraphEdges (inducedStar k) := by
    simpa using inducedStar_center_adj_leaf a
  unfold graphonInducedIntegrand
  rw [show (∏ e ∈ finiteGraphEdges (inducedStar k),
      graphonPairValue zeroGraphon x e) = 0 by
    apply Finset.prod_eq_zero hEdge
    simpa using hx]
  simp

/-- The one graphon has zero induced-star density once the star has two
distinct leaves. -/
theorem graphonInducedDensity_inducedStar_oneGraphon
    (k : ℕ) (hk : 2 ≤ k) :
    graphonInducedDensity (inducedStar k) oneGraphon = 0 := by
  classical
  let a : Fin k := ⟨0, by omega⟩
  let b : Fin k := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  have hne : a.succ ≠ b.succ := by simpa using hab
  have hvalue : oneGraphon.value =ᵐ[unitSquareMeasure]
      (fun _ : UnitSquare ↦ (1 : ℝ)) :=
    Filter.EventuallyEq.trans oneGraphon.value_ae_eq oneGraphon_ae_eq
  have hpull :
      (fun x : Fin (k + 1) → UnitInterval ↦
          oneGraphon.value (x a.succ, x b.succ)) =ᵐ[volume]
        fun _ ↦ (1 : ℝ) := by
    change (oneGraphon.value ∘
      fun x : Fin (k + 1) → UnitInterval ↦ (x a.succ, x b.succ))
        =ᵐ[volume]
      ((fun _ : UnitSquare ↦ (1 : ℝ)) ∘
        fun x : Fin (k + 1) → UnitInterval ↦ (x a.succ, x b.succ))
    exact (measurePreserving_pairProjection hne).quasiMeasurePreserving.ae_eq_comp hvalue
  unfold graphonInducedDensity
  apply integral_eq_zero_of_ae
  filter_upwards [hpull] with x hx
  have hNonedge : s(a.succ, b.succ) ∈
      finiteGraphEdges (inducedStar k)ᶜ := by
    simp [hne]
  unfold graphonInducedIntegrand
  rw [show (∏ e ∈ finiteGraphEdges (inducedStar k)ᶜ,
      (1 - graphonPairValue oneGraphon x e)) = 0 by
    apply Finset.prod_eq_zero hNonedge
    rw [graphonPairValue_mk, hx]
    ring]
  simp

/-! ## The conditioned graphon variational problem -/

/-- Graphons with zero induced `K_{1,k}` density. -/
def inducedStarFreeGraphons (k : ℕ) : Set Graphon :=
  {W | graphonInducedDensity (inducedStar k) W = 0}

@[simp] theorem mem_inducedStarFreeGraphons {k : ℕ} {W : Graphon} :
    W ∈ inducedStarFreeGraphons k ↔
      graphonInducedDensity (inducedStar k) W = 0 :=
  Iff.rfl

/-- The literal infimum in the graphon variational problem `Ψ_k(p)`. -/
noncomputable def gnpGraphonVariationalValue (k : ℕ) (p : ℝ) : ℝ :=
  sInf (graphonRelativeEntropy p '' inducedStarFreeGraphons k)

/-- A conditioned graphon optimizer is feasible and minimizes graphon
relative entropy over the entire induced-star-free feasible set. -/
def IsGnpGraphonOptimizer (k : ℕ) (p : ℝ) (W : Graphon) : Prop :=
  W ∈ inducedStarFreeGraphons k ∧
    ∀ U ∈ inducedStarFreeGraphons k,
      graphonRelativeEntropy p W ≤ graphonRelativeEntropy p U

/-- The set of optimizers of the conditioned graphon variational problem. -/
def gnpGraphonOptimizers (k : ℕ) (p : ℝ) : Set Graphon :=
  {W | IsGnpGraphonOptimizer k p W}

@[simp] theorem mem_gnpGraphonOptimizers {k : ℕ} {p : ℝ} {W : Graphon} :
    W ∈ gnpGraphonOptimizers k p ↔ IsGnpGraphonOptimizer k p W :=
  Iff.rfl

theorem IsGnpGraphonOptimizer.feasible
    {k : ℕ} {p : ℝ} {W : Graphon}
    (hW : IsGnpGraphonOptimizer k p W) :
    W ∈ inducedStarFreeGraphons k :=
  hW.1

theorem IsGnpGraphonOptimizer.relativeEntropy_le
    {k : ℕ} {p : ℝ} {W : Graphon}
    (hW : IsGnpGraphonOptimizer k p W)
    {U : Graphon} (hU : U ∈ inducedStarFreeGraphons k) :
    graphonRelativeEntropy p W ≤ graphonRelativeEntropy p U :=
  hW.2 U hU

/-- Cut-distance-zero transport of induced-star freeness. -/
theorem mem_inducedStarFreeGraphons_of_cutDist_eq_zero
    {k : ℕ} {U W : Graphon}
    (hU : U ∈ inducedStarFreeGraphons k) (hcut : cutDist U W = 0) :
    W ∈ inducedStarFreeGraphons k := by
  rw [mem_inducedStarFreeGraphons,
    ← graphonInducedDensity_eq_of_cutDist_eq_zero (inducedStar k) U W hcut]
  exact hU

/-- Elementwise cut-zero invariance of induced-star-free feasibility. -/
theorem mem_inducedStarFreeGraphons_iff_of_cutDist_eq_zero
    {k : ℕ} {U W : Graphon} (hcut : cutDist U W = 0) :
    U ∈ inducedStarFreeGraphons k ↔ W ∈ inducedStarFreeGraphons k := by
  constructor
  · intro hU
    exact mem_inducedStarFreeGraphons_of_cutDist_eq_zero hU hcut
  · intro hW
    exact mem_inducedStarFreeGraphons_of_cutDist_eq_zero hW (by
      rw [cutDist_comm]
      exact hcut)

/-- Conditioned optimizer status is preserved by cut-distance-zero
equivalence. -/
theorem IsGnpGraphonOptimizer.of_cutDist_eq_zero
    {k : ℕ} {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    {U W : Graphon} (hU : IsGnpGraphonOptimizer k p U)
    (hcut : cutDist U W = 0) :
    IsGnpGraphonOptimizer k p W := by
  refine ⟨mem_inducedStarFreeGraphons_of_cutDist_eq_zero hU.1 hcut, ?_⟩
  intro V hV
  rw [← graphonRelativeEntropy_eq_of_cutDist_eq_zero hp U W hcut]
  exact hU.2 V hV

/-- Elementwise cut-zero invariance of conditioned optimizer membership. -/
theorem mem_gnpGraphonOptimizers_iff_of_cutDist_eq_zero
    {k : ℕ} {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    {U W : Graphon} (hcut : cutDist U W = 0) :
    U ∈ gnpGraphonOptimizers k p ↔ W ∈ gnpGraphonOptimizers k p := by
  constructor
  · intro hU
    exact hU.of_cutDist_eq_zero hp hcut
  · intro hW
    exact hW.of_cutDist_eq_zero hp (by
      rw [cutDist_comm]
      exact hcut)

/-! ## Reduction at a fixed interior edge density -/

/-- Exact relative-entropy formula on a fixed-density feasible fiber. -/
theorem graphonRelativeEntropy_eq_of_mem_fixedDensityFeasible
    {k : ℕ} {p γ : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    {W : Graphon} (hW : W ∈ fixedDensityFeasible k γ) :
    graphonRelativeEntropy p W =
      -graphonEntropy W + γ * log2 ((1 - p) / p) - log2 (1 - p) := by
  rw [graphonRelativeEntropy_eq_negEntropy_add_edge hp W, hW.2]

/-- At fixed edge density, graphon relative entropy is bounded below by the
one-dimensional rate objective. -/
theorem graphonRelativeEntropy_ge_rateAtDensity
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (W : Graphon) (hW : W ∈ fixedDensityFeasible k γ) :
    rateAtDensity k p γ ≤ graphonRelativeEntropy p W := by
  rw [graphonRelativeEntropy_eq_negEntropy_add_edge hp W, hW.2,
    rateAtDensity, rateCoreObjective]
  have hent := graphonEntropy_le_entropyDensity k hk γ hγ W hW
  linarith

/-- Equality in the fixed-density relative-entropy bound is exactly
fixed-density entropy optimality. -/
theorem graphonRelativeEntropy_eq_rateAtDensity_iff_optimizer
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (W : Graphon) (hW : W ∈ fixedDensityFeasible k γ) :
    graphonRelativeEntropy p W = rateAtDensity k p γ ↔
      W ∈ fixedDensityOptimizers k γ := by
  constructor
  · intro heq
    have hent : graphonEntropy W = entropyDensity k γ := by
      rw [graphonRelativeEntropy_eq_negEntropy_add_edge hp W, hW.2,
        rateAtDensity, rateCoreObjective] at heq
      linarith
    refine ⟨hW, ?_⟩
    intro U hU
    calc
      graphonEntropy U ≤ entropyDensity k γ :=
        graphonEntropy_le_entropyDensity k hk γ hγ U hU
      _ = graphonEntropy W := hent.symm
  · intro hopt
    have hent := hopt.entropy_eq_entropyDensity hk hγ
    rw [graphonRelativeEntropy_eq_negEntropy_add_edge hp W, hW.2,
      rateAtDensity, rateCoreObjective, hent]

/-- Interior equality in the edge-density reduction can be read directly as
fixed-density optimizer membership. -/
theorem graphonRelativeEntropy_eq_rateAt_edgeDensity_iff_optimizer
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (W : Graphon) (hfree : W ∈ inducedStarFreeGraphons k)
    (hedge : graphonEdgeDensity W ∈ Ioo (0 : ℝ) 1) :
    graphonRelativeEntropy p W =
        rateAtDensity k p (graphonEdgeDensity W) ↔
      W ∈ fixedDensityOptimizers k (graphonEdgeDensity W) := by
  exact graphonRelativeEntropy_eq_rateAtDensity_iff_optimizer
    k hk p hp (graphonEdgeDensity W) hedge W ⟨hfree, rfl⟩

/-! ## Reduction at every edge density -/

/-- Every induced-star-free graphon has relative entropy at least the scalar
rate at its own edge density.  The endpoint cases use rigidity, rather than an
extension of the fixed-density optimizer theorem beyond its stated interior
domain. -/
theorem graphonRelativeEntropy_ge_rateAt_edgeDensity
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (W : Graphon) (hfree : W ∈ inducedStarFreeGraphons k) :
    rateAtDensity k p (graphonEdgeDensity W) ≤
      graphonRelativeEntropy p W := by
  have hedge := graphonEdgeDensity_mem_Icc W
  by_cases hzero : graphonEdgeDensity W = 0
  · have hW : W = zeroGraphon :=
      (graphonEdgeDensity_eq_zero_iff W).1 hzero
    subst W
    rw [graphonEdgeDensity_zeroGraphon, rateAtDensity_zero k p hk]
    exact le_of_eq <| calc
      -log2 (1 - p) = binaryRelativeEntropy p 0 :=
        (binaryRelativeEntropy_zero hp).symm
      _ = log2 (1 / (1 - p)) :=
        binaryRelativeEntropy_zero_eq_log2_inv hp
      _ = graphonRelativeEntropy p zeroGraphon :=
        (graphonRelativeEntropy_zeroGraphon hp).symm
  · by_cases hone : graphonEdgeDensity W = 1
    · have hW : W = oneGraphon :=
        (graphonEdgeDensity_eq_one_iff W).1 hone
      subst W
      rw [graphonEdgeDensity_oneGraphon, rateAtDensity_one k p hk hp]
      exact le_of_eq <| calc
        -log2 p = binaryRelativeEntropy p 1 :=
          (binaryRelativeEntropy_one hp).symm
        _ = log2 (1 / p) := binaryRelativeEntropy_one_eq_log2_inv hp
        _ = graphonRelativeEntropy p oneGraphon :=
          (graphonRelativeEntropy_oneGraphon hp).symm
    · have hinterior : graphonEdgeDensity W ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne hedge.1 (Ne.symm hzero),
          lt_of_le_of_ne hedge.2 hone⟩
      exact graphonRelativeEntropy_ge_rateAtDensity k hk p hp
        (graphonEdgeDensity W) hinterior W ⟨hfree, rfl⟩

/-- Equality in the all-density reduction consists of the two rigid endpoint
graphons, or fixed-density entropy optimality at an interior edge density. -/
theorem graphonRelativeEntropy_eq_rateAt_edgeDensity_iff
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (W : Graphon) (hfree : W ∈ inducedStarFreeGraphons k) :
    graphonRelativeEntropy p W =
        rateAtDensity k p (graphonEdgeDensity W) ↔
      graphonEdgeDensity W = 0 ∨
        graphonEdgeDensity W = 1 ∨
          (graphonEdgeDensity W ∈ Ioo (0 : ℝ) 1 ∧
            W ∈ fixedDensityOptimizers k (graphonEdgeDensity W)) := by
  constructor
  · intro heq
    by_cases hzero : graphonEdgeDensity W = 0
    · exact Or.inl hzero
    · by_cases hone : graphonEdgeDensity W = 1
      · exact Or.inr (Or.inl hone)
      · have hedge := graphonEdgeDensity_mem_Icc W
        have hinterior : graphonEdgeDensity W ∈ Ioo (0 : ℝ) 1 :=
          ⟨lt_of_le_of_ne hedge.1 (Ne.symm hzero),
            lt_of_le_of_ne hedge.2 hone⟩
        exact Or.inr <| Or.inr ⟨hinterior,
          (graphonRelativeEntropy_eq_rateAt_edgeDensity_iff_optimizer
            k hk p hp W hfree hinterior).1 heq⟩
  · rintro (hzero | hone | ⟨hinterior, hopt⟩)
    · have hW : W = zeroGraphon :=
        (graphonEdgeDensity_eq_zero_iff W).1 hzero
      subst W
      rw [graphonEdgeDensity_zeroGraphon, rateAtDensity_zero k p hk,
        graphonRelativeEntropy_zeroGraphon hp]
      calc
        log2 (1 / (1 - p)) = binaryRelativeEntropy p 0 :=
          (binaryRelativeEntropy_zero_eq_log2_inv hp).symm
        _ = -log2 (1 - p) := binaryRelativeEntropy_zero hp
    · have hW : W = oneGraphon :=
        (graphonEdgeDensity_eq_one_iff W).1 hone
      subst W
      rw [graphonEdgeDensity_oneGraphon, rateAtDensity_one k p hk hp,
        graphonRelativeEntropy_oneGraphon hp]
      calc
        log2 (1 / p) = binaryRelativeEntropy p 1 :=
          (binaryRelativeEntropy_one_eq_log2_inv hp).symm
        _ = -log2 p := binaryRelativeEntropy_one hp
    · exact (graphonRelativeEntropy_eq_rateAt_edgeDensity_iff_optimizer
        k hk p hp W hfree hinterior).2 hopt

end InducedStars
