import InducedStars.Graphon.Functionals
import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# The canonical induced star and the fixed-density variational sets

The paper's `K_{1,k}` is represented by Mathlib's star graph on `Fin (k+1)`,
centered at `0`.  Thus it has one center and exactly `k` leaves.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace InducedStars

/-! ## The star `K_{1,k}` -/

/-- The canonical copy of the paper's `K_{1,k}`: center `0` and leaves
`Fin.succ i`, for `i : Fin k`. -/
def inducedStar (k : ℕ) : SimpleGraph (Fin (k + 1)) :=
  SimpleGraph.starGraph 0

/-- Transparent adjacency characterization of the canonical induced star. -/
@[simp] theorem inducedStar_adj {k : ℕ} {i j : Fin (k + 1)} :
    (inducedStar k).Adj i j ↔ i ≠ j ∧ (i = 0 ∨ j = 0) := by
  exact SimpleGraph.starGraph_adj

/-- The paper's `K_{1,k}` has `k+1` vertices. -/
@[simp] theorem inducedStar_vertexCount (k : ℕ) :
    Fintype.card (Fin (k + 1)) = k + 1 := by
  simp

/-- Every designated leaf is adjacent to the center. -/
theorem inducedStar_center_adj_leaf {k : ℕ} (i : Fin k) :
    (inducedStar k).Adj 0 i.succ := by
  rw [inducedStar_adj]
  exact ⟨(Fin.succ_ne_zero i).symm, Or.inl rfl⟩

/-- The center is adjacent to every non-center vertex. -/
theorem inducedStar_center_adj_of_ne {k : ℕ} {v : Fin (k + 1)} (hv : v ≠ 0) :
    (inducedStar k).Adj 0 v := by
  rw [inducedStar_adj]
  exact ⟨hv.symm, Or.inl rfl⟩

/-- Two designated leaves are never adjacent. -/
theorem inducedStar_leaf_nonadj_leaf {k : ℕ} (i j : Fin k) :
    ¬(inducedStar k).Adj i.succ j.succ := by
  simp

/-- The canonical induced star is connected. -/
theorem inducedStar_connected (k : ℕ) : (inducedStar k).Connected := by
  exact SimpleGraph.connected_starGraph 0

/-! ## Induced densities of matrix graphons -/

/-- Evaluate a symmetric matrix on an unordered pair of labels. -/
def matrixMapPairValue {f q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ)
    (hM : M.IsSymm) (φ : Fin f → Fin q) : Sym2 (Fin f) → ℝ :=
  Sym2.lift ⟨fun i j ↦ M (φ i) (φ j), fun i j ↦ by
    simpa only [Matrix.transpose_apply] using hM.apply (φ j) (φ i)⟩

@[simp] theorem matrixMapPairValue_mk {f q : ℕ}
    (M : Matrix (Fin q) (Fin q) ℝ) (hM : M.IsSymm)
    (φ : Fin f → Fin q) (i j : Fin f) :
    matrixMapPairValue M hM φ s(i, j) = M (φ i) (φ j) :=
  rfl

/-- The weight of one vertex-label map in the induced-density formula for a
matrix graphon. -/
def matrixInducedMapWeight {f q : ℕ} (F : SimpleGraph (Fin f))
    (M : Matrix (Fin q) (Fin q) ℝ) (hM : M.IsSymm)
    (φ : Fin f → Fin q) : ℝ :=
  (∏ e ∈ finiteGraphEdges F, matrixMapPairValue M hM φ e) *
    ∏ e ∈ finiteGraphEdges Fᶜ, (1 - matrixMapPairValue M hM φ e)

/-- On one equal-cell cube, a matrix graphon's induced-density integrand is
almost everywhere the corresponding finite matrix weight. -/
theorem graphonInducedIntegrand_matrixGraphon_ae_on_cube {f q : ℕ}
    (F : SimpleGraph (Fin f)) (M : Matrix (Fin q) (Fin q) ℝ)
    (hM : M.IsSymm) (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (φ : Fin f → Fin q) :
    ∀ᵐ x : Fin f → UnitInterval ∂volume,
      x ∈ equalCellCube φ →
        graphonInducedIntegrand F (matrixGraphon M hM hM₀ hM₁) x =
          matrixInducedMapWeight F M hM φ := by
  let W := matrixGraphon M hM hM₀ hM₁
  have hedge (e : Sym2 (Fin f)) : e ∈ finiteGraphEdges F →
      ∀ᵐ x : Fin f → UnitInterval ∂volume,
        x ∈ equalCellCube φ →
          graphonPairValue W x e = matrixMapPairValue M hM φ e := by
    refine Sym2.inductionOn e ?_
    intro i j he
    have hF : F.Adj i j := by simpa using he
    have hsquare : ∀ᵐ z ∂unitSquareMeasure,
        z ∈ equalCell (φ i) ×ˢ equalCell (φ j) →
          W.value z = M (φ i) (φ j) := by
      filter_upwards [W.value_ae_eq,
        matrixGraphon_ae_eq_on_cell M hM hM₀ hM₁ (φ i) (φ j)]
        with z hzValue hzCell
      intro hz
      exact hzValue.trans (hzCell hz)
    have hpull := (measurePreserving_pairProjection (F.ne_of_adj hF)).quasiMeasurePreserving.ae
      hsquare
    filter_upwards [hpull] with x hx
    intro hxcube
    exact hx ⟨hxcube i (Set.mem_univ i), hxcube j (Set.mem_univ j)⟩
  have hnonedge (e : Sym2 (Fin f)) : e ∈ finiteGraphEdges Fᶜ →
      ∀ᵐ x : Fin f → UnitInterval ∂volume,
        x ∈ equalCellCube φ →
          graphonPairValue W x e = matrixMapPairValue M hM φ e := by
    refine Sym2.inductionOn e ?_
    intro i j he
    have hFc : Fᶜ.Adj i j := by simpa using he
    have hsquare : ∀ᵐ z ∂unitSquareMeasure,
        z ∈ equalCell (φ i) ×ˢ equalCell (φ j) →
          W.value z = M (φ i) (φ j) := by
      filter_upwards [W.value_ae_eq,
        matrixGraphon_ae_eq_on_cell M hM hM₀ hM₁ (φ i) (φ j)]
        with z hzValue hzCell
      intro hz
      exact hzValue.trans (hzCell hz)
    have hpull :=
      (measurePreserving_pairProjection (Fᶜ.ne_of_adj hFc)).quasiMeasurePreserving.ae hsquare
    filter_upwards [hpull] with x hx
    intro hxcube
    exact hx ⟨hxcube i (Set.mem_univ i), hxcube j (Set.mem_univ j)⟩
  have hallEdges := (Filter.eventually_all_finset (finiteGraphEdges F)).2
    fun e he ↦ hedge e he
  have hallNonedges := (Filter.eventually_all_finset (finiteGraphEdges Fᶜ)).2
    fun e he ↦ hnonedge e he
  filter_upwards [hallEdges, hallNonedges] with x hxEdge hxNonedge
  intro hxcube
  unfold graphonInducedIntegrand matrixInducedMapWeight
  congr 1
  · apply Finset.prod_congr rfl
    intro e he
    exact hxEdge e he hxcube
  · apply Finset.prod_congr rfl
    intro e he
    rw [hxNonedge e he hxcube]

/-- Exact contribution of one label cube to the induced density of a matrix
graphon. -/
theorem setIntegral_graphonInducedIntegrand_matrixGraphon_equalCellCube
    {f q : ℕ} (F : SimpleGraph (Fin f)) (M : Matrix (Fin q) (Fin q) ℝ)
    (hM : M.IsSymm) (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (φ : Fin f → Fin q) :
    ∫ x in equalCellCube φ,
        graphonInducedIntegrand F (matrixGraphon M hM hM₀ hM₁) x =
      (1 / (q : ℝ)) ^ f * matrixInducedMapWeight F M hM φ := by
  calc
    _ = ∫ _x in equalCellCube φ, matrixInducedMapWeight F M hM φ :=
      setIntegral_congr_ae (measurableSet_equalCellCube φ)
        (graphonInducedIntegrand_matrixGraphon_ae_on_cube F M hM hM₀ hM₁ φ)
    _ = (1 / (q : ℝ)) ^ f * matrixInducedMapWeight F M hM φ := by
      rw [setIntegral_const, smul_eq_mul, Measure.real, volume_equalCellCube,
        ENNReal.toReal_pow, ENNReal.toReal_ofReal]
      positivity

/-- Induced density of an equal-cell matrix graphon as an explicit finite sum
over all vertex-label maps. -/
theorem graphonInducedDensity_matrixGraphon_eq_sum {f q : ℕ} (hq : 0 < q)
    (F : SimpleGraph (Fin f)) (M : Matrix (Fin q) (Fin q) ℝ)
    (hM : M.IsSymm) (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1) :
    graphonInducedDensity F (matrixGraphon M hM hM₀ hM₁) =
      ∑ φ : Fin f → Fin q,
        (1 / (q : ℝ)) ^ f * matrixInducedMapWeight F M hM φ := by
  unfold graphonInducedDensity
  rw [integral_eq_setIntegral (ae_mem_iUnion_equalCellCube (f := f) hq)]
  rw [integral_iUnion_fintype]
  · simp_rw [setIntegral_graphonInducedIntegrand_matrixGraphon_equalCellCube]
  · exact measurableSet_equalCellCube
  · exact pairwise_disjoint_equalCellCube
  · intro φ
    exact (integrable_graphonInducedIntegrand F
      (matrixGraphon M hM hM₀ hM₁)).integrableOn

/-- If every finite map has zero induced weight, then the corresponding
matrix graphon has zero induced density. -/
theorem graphonInducedDensity_matrixGraphon_eq_zero_of_weights {f q : ℕ}
    (hq : 0 < q) (F : SimpleGraph (Fin f))
    (M : Matrix (Fin q) (Fin q) ℝ) (hM : M.IsSymm)
    (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (hzero : ∀ φ : Fin f → Fin q, matrixInducedMapWeight F M hM φ = 0) :
    graphonInducedDensity F (matrixGraphon M hM hM₀ hM₁) = 0 := by
  rw [graphonInducedDensity_matrixGraphon_eq_sum hq]
  simp [hzero]

/-! ## Fixed-density feasible and optimizer sets -/

/-- Graphons with edge density `γ` and zero induced `K_{1,k}` density. -/
def fixedDensityFeasible (k : ℕ) (γ : ℝ) : Set Graphon :=
  {W | graphonInducedDensity (inducedStar k) W = 0 ∧ graphonEdgeDensity W = γ}

@[simp] theorem mem_fixedDensityFeasible {k : ℕ} {γ : ℝ} {W : Graphon} :
    W ∈ fixedDensityFeasible k γ ↔
      graphonInducedDensity (inducedStar k) W = 0 ∧ graphonEdgeDensity W = γ :=
  Iff.rfl

/-- A fixed-density optimizer is a feasible graphon whose entropy dominates
that of every other feasible graphon.  This definition does not presuppose
that an optimizer exists. -/
def IsFixedDensityOptimizer (k : ℕ) (γ : ℝ) (W : Graphon) : Prop :=
  W ∈ fixedDensityFeasible k γ ∧
    ∀ U ∈ fixedDensityFeasible k γ, graphonEntropy U ≤ graphonEntropy W

/-- The set of entropy maximizers in the fixed-density feasible set. -/
def fixedDensityOptimizers (k : ℕ) (γ : ℝ) : Set Graphon :=
  {W | IsFixedDensityOptimizer k γ W}

@[simp] theorem mem_fixedDensityOptimizers {k : ℕ} {γ : ℝ} {W : Graphon} :
    W ∈ fixedDensityOptimizers k γ ↔ IsFixedDensityOptimizer k γ W :=
  Iff.rfl

theorem IsFixedDensityOptimizer.feasible {k : ℕ} {γ : ℝ} {W : Graphon}
    (hW : IsFixedDensityOptimizer k γ W) :
    W ∈ fixedDensityFeasible k γ :=
  hW.1

theorem IsFixedDensityOptimizer.entropy_le {k : ℕ} {γ : ℝ} {W : Graphon}
    (hW : IsFixedDensityOptimizer k γ W) {U : Graphon}
    (hU : U ∈ fixedDensityFeasible k γ) :
    graphonEntropy U ≤ graphonEntropy W :=
  hW.2 U hU

end InducedStars
