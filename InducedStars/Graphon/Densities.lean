import InducedStars.Graphon.Step
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.HasLaw

/-!
# Graph and graphon homomorphism densities

This file defines the ordinary and induced density integrands of a finite
simple graph in a graphon.  The integration domain for a graph on `Fin f` is
the probability cube `Fin f → UnitInterval`.

The finite-graph density uses all vertex maps (not only embeddings) and is
normalized by the total number `|V(G)| ^ |V(F)|` of such maps.
-/

open scoped BigOperators ENNReal
open MeasureTheory
open ProbabilityTheory

namespace InducedStars

noncomputable section

noncomputable local instance finiteGraphEdgeSetFintype {V : Type*} [Finite V]
    (F : SimpleGraph V) : Fintype F.edgeSet :=
  Fintype.ofFinite F.edgeSet

/-- The edge finset of a graph on a finite type, with the finite and decidable
instances chosen internally.  This keeps graphon density declarations
independent of a particular `DecidableRel` instance. -/
def finiteGraphEdges {V : Type*} [Finite V] (F : SimpleGraph V) : Finset (Sym2 V) :=
  F.edgeFinset

@[simp] lemma mem_finiteGraphEdges {V : Type*} [Finite V] (F : SimpleGraph V)
    (e : Sym2 V) :
    e ∈ finiteGraphEdges F ↔ e ∈ F.edgeSet := by
  classical
  unfold finiteGraphEdges
  exact SimpleGraph.mem_edgeFinset

@[simp] lemma mk_mem_finiteGraphEdges {V : Type*} [Finite V] (F : SimpleGraph V)
    (i j : V) :
    s(i, j) ∈ finiteGraphEdges F ↔ F.Adj i j := by
  simp [SimpleGraph.mem_edgeSet]

/-- Distinct coordinate projections from a finite probability cube have the
product law. -/
theorem measurePreserving_pairProjection {f : ℕ} {i j : Fin f} (hij : i ≠ j) :
    MeasurePreserving (fun x : Fin f → UnitInterval ↦ (x i, x j))
      (volume : Measure (Fin f → UnitInterval)) unitSquareMeasure := by
  have hIndep : iIndepFun (fun k (x : Fin f → UnitInterval) ↦ x k)
      (volume : Measure (Fin f → UnitInterval)) :=
    iIndepFun_pi (X := fun _ : Fin f ↦ id) (fun _ ↦ aemeasurable_id)
  have hi : HasLaw (fun x : Fin f → UnitInterval ↦ x i)
      (volume : Measure UnitInterval) (volume : Measure (Fin f → UnitInterval)) :=
    (measurePreserving_eval (fun _ : Fin f ↦ (volume : Measure UnitInterval)) i).hasLaw
  have hj : HasLaw (fun x : Fin f → UnitInterval ↦ x j)
      (volume : Measure UnitInterval) (volume : Measure (Fin f → UnitInterval)) :=
    (measurePreserving_eval (fun _ : Fin f ↦ (volume : Measure UnitInterval)) j).hasLaw
  exact ((hIndep.indepFun hij).hasLaw_prod hi hj).measurePreserving (by fun_prop)

/-! ## Factors indexed by unordered vertex pairs -/

/-- Evaluate a graphon on an unordered pair of coordinates in a cube. -/
def graphonPairValue {f : ℕ} (W : Graphon) (x : Fin f → UnitInterval) : Sym2 (Fin f) → ℝ :=
  Sym2.lift ⟨fun i j ↦ W.value (x i, x j), fun i j ↦ W.value_symm (x i) (x j)⟩

@[simp]
lemma graphonPairValue_mk {f : ℕ} (W : Graphon) (x : Fin f → UnitInterval)
    (i j : Fin f) :
    graphonPairValue W x s(i, j) = W.value (x i, x j) :=
  rfl

lemma measurable_graphonPairValue {f : ℕ} (W : Graphon) (e : Sym2 (Fin f)) :
    Measurable (fun x : Fin f → UnitInterval ↦ graphonPairValue W x e) := by
  refine Sym2.inductionOn e ?_
  intro i j
  change Measurable (W.value ∘ fun x : Fin f → UnitInterval ↦ (x i, x j))
  exact W.measurable_value.comp
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j))

lemma graphonPairValue_nonneg {f : ℕ} (W : Graphon) (x : Fin f → UnitInterval)
    (e : Sym2 (Fin f)) :
    0 ≤ graphonPairValue W x e := by
  refine Sym2.inductionOn e ?_
  intro i j
  exact W.value_nonneg (x i, x j)

lemma graphonPairValue_le_one {f : ℕ} (W : Graphon) (x : Fin f → UnitInterval)
    (e : Sym2 (Fin f)) :
    graphonPairValue W x e ≤ 1 := by
  refine Sym2.inductionOn e ?_
  intro i j
  exact W.value_le_one (x i, x j)

/-- On two distinct coordinates, the canonical pointwise representative gives
the same factor almost everywhere as the underlying `L¹` representative. -/
lemma graphonPairValue_ae_eq_of_ne {f : ℕ} (W : Graphon) {i j : Fin f} (hij : i ≠ j) :
    (fun x : Fin f → UnitInterval ↦ graphonPairValue W x s(i, j)) =ᵐ[volume]
      fun x ↦ W (x i, x j) := by
  have h := (measurePreserving_pairProjection hij).quasiMeasurePreserving.ae_eq_comp W.value_ae_eq
  change (W.value ∘ fun x : Fin f → UnitInterval ↦ (x i, x j)) =ᵐ[volume]
    ((W : UnitSquare → ℝ) ∘ fun x : Fin f → UnitInterval ↦ (x i, x j))
  exact h

/-! ## Equal-cell cubes -/

/-- Every point below the right endpoint belongs to one equal cell. -/
lemma exists_mem_equalCell {q : ℕ} (hq : 0 < q) (x : UnitInterval)
    (hx : (x : ℝ) < 1) :
    ∃ i : Fin q, x ∈ equalCell i := by
  let a : ℝ := (q : ℝ) * (x : ℝ)
  have ha_nonneg : 0 ≤ a := mul_nonneg (Nat.cast_nonneg q) x.2.1
  have ha_lt : a < q := by
    dsimp [a]
    nlinarith [show (0 : ℝ) < q by exact_mod_cast hq]
  have hi_lt : ⌊a⌋₊ < q := (Nat.floor_lt ha_nonneg).2 (by exact_mod_cast ha_lt)
  let i : Fin q := ⟨⌊a⌋₊, hi_lt⟩
  refine ⟨i, ?_⟩
  simp only [equalCell, Set.mem_Ico]
  have hq_real : (0 : ℝ) < q := by exact_mod_cast hq
  constructor
  · apply Subtype.coe_le_coe.mp
    change ((i : ℕ) : ℝ) / q ≤ (x : ℝ)
    rw [div_le_iff₀ hq_real]
    simpa [i, a, mul_comm] using Nat.floor_le ha_nonneg
  · apply Subtype.coe_lt_coe.mp
    simp only [equalCellRight]
    rw [lt_div_iff₀ hq_real]
    simpa [i, a, mul_comm] using Nat.lt_floor_add_one a

/-- The product cell of the vertex cube indexed by a map into `Fin q`. -/
def equalCellCube {f q : ℕ} (φ : Fin f → Fin q) : Set (Fin f → UnitInterval) :=
  Set.univ.pi fun i ↦ equalCell (φ i)

@[measurability]
lemma measurableSet_equalCellCube {f q : ℕ} (φ : Fin f → Fin q) :
    MeasurableSet (equalCellCube φ) := by
  exact MeasurableSet.univ_pi fun i ↦ measurableSet_equalCell (φ i)

/-- Distinct cell labels determine disjoint product cells. -/
lemma pairwise_disjoint_equalCellCube {f q : ℕ} :
    Pairwise fun φ ψ : Fin f → Fin q ↦ Disjoint (equalCellCube φ) (equalCellCube ψ) := by
  intro φ ψ hφψ
  rw [Set.disjoint_left]
  intro x hxφ hxψ
  apply hφψ
  funext i
  exact equalCell_eq_of_mem
    (hxφ i (Set.mem_univ i)) (hxψ i (Set.mem_univ i))

/-- Except for the null endpoint hyperplanes, the equal-cell product cubes
cover the whole vertex cube. -/
lemma ae_mem_iUnion_equalCellCube {f q : ℕ} (hq : 0 < q) :
    ∀ᵐ x : Fin f → UnitInterval ∂volume,
      x ∈ ⋃ φ : Fin f → Fin q, equalCellCube φ := by
  have hne : ∀ᵐ x : Fin f → UnitInterval ∂volume,
      ∀ i : Fin f, x i ≠ (1 : UnitInterval) := by
    exact Filter.eventually_all.2 fun i ↦
      Measure.ae_eval_ne (fun _ : Fin f ↦ (volume : Measure UnitInterval)) i 1
  filter_upwards [hne] with x hx
  have hcell (i : Fin f) : ∃ j : Fin q, x i ∈ equalCell j := by
    apply exists_mem_equalCell hq
    apply lt_of_le_of_ne (x i).2.2
    intro heq
    apply hx i
    exact Subtype.ext heq
  choose φ hφ using hcell
  exact Set.mem_iUnion.2 ⟨φ, fun i _ ↦ hφ i⟩

/-- Every equal-cell product cube has volume `q⁻ᶠ`. -/
lemma volume_equalCellCube {f q : ℕ} (φ : Fin f → Fin q) :
    volume (equalCellCube φ) = ENNReal.ofReal (1 / (q : ℝ)) ^ f := by
  rw [equalCellCube, volume_pi_pi]
  simp [volume_equalCell]

/-! ## Finite-map indicators -/

/-- The `0`-`1` adjacency value of a vertex map on an unordered pair. -/
def graphMapPairValue {f n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (φ : Fin f → Fin n) : Sym2 (Fin f) → ℝ :=
  Sym2.lift ⟨fun i j ↦ if G.Adj (φ i) (φ j) then 1 else 0,
    fun i j ↦ by
      dsimp
      by_cases hij : G.Adj (φ i) (φ j)
      · simp [hij, G.adj_symm hij]
      · have hji : ¬G.Adj (φ j) (φ i) := fun h ↦ hij (G.adj_symm h)
        simp [hij, hji]⟩

@[simp]
lemma graphMapPairValue_mk {f n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (φ : Fin f → Fin n) (i j : Fin f) :
    graphMapPairValue G φ s(i, j) = if G.Adj (φ i) (φ j) then 1 else 0 :=
  rfl

/-- The `0`-`1` indicator that a vertex map preserves every edge. -/
def graphMapIndicator {f n : ℕ} (F : SimpleGraph (Fin f))
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (φ : Fin f → Fin n) : ℝ :=
  ∏ e ∈ finiteGraphEdges F, graphMapPairValue G φ e

/-- The proposition that an underlying vertex map is a graph homomorphism. -/
def IsGraphHomMap {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W)
    (φ : V → W) : Prop :=
  ∀ {i j : V}, F.Adj i j → G.Adj (φ i) (φ j)

lemma graphMapIndicator_eq_ite {f n : ℕ} (F : SimpleGraph (Fin f))
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (φ : Fin f → Fin n)
    [Decidable (IsGraphHomMap F G φ)] :
    graphMapIndicator F G φ = if IsGraphHomMap F G φ then 1 else 0 := by
  classical
  by_cases hφ : IsGraphHomMap F G φ
  · have hprod : graphMapIndicator F G φ = 1 := by
      apply Finset.prod_eq_one
      intro e he
      revert he
      refine Sym2.inductionOn e ?_
      intro i j he
      have hF : F.Adj i j := by simpa using he
      simp [graphMapPairValue_mk, hφ hF]
    rw [hprod]
    simp [hφ]
  · have hnot := hφ
    simp only [IsGraphHomMap] at hnot
    push Not at hnot
    rcases hnot with ⟨i, j, hF, hG⟩
    have hprod : graphMapIndicator F G φ = 0 := by
      apply Finset.prod_eq_zero (i := s(i, j))
      · simp [hF]
      · simp [graphMapPairValue_mk, hG]
    rw [hprod]
    simp [hφ]

/-! ## Ordinary homomorphism density -/

/-- The product of graphon values over the edges of a finite graph. -/
def graphonHomIntegrand {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon)
    (x : Fin f → UnitInterval) : ℝ :=
  ∏ e ∈ finiteGraphEdges F, graphonPairValue W x e

/-- On a fixed equal-cell cube, an adjacency graphon's edge-product agrees
almost everywhere with the corresponding finite-map indicator. -/
lemma graphonHomIntegrand_graphGraphon_ae_on_cube {f n : ℕ}
    (F : SimpleGraph (Fin f)) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (φ : Fin f → Fin n) :
    ∀ᵐ x : Fin f → UnitInterval ∂volume,
      x ∈ equalCellCube φ →
        graphonHomIntegrand F (graphGraphon G) x = graphMapIndicator F G φ := by
  have hpair (e : Sym2 (Fin f)) : e ∈ finiteGraphEdges F →
      ∀ᵐ x : Fin f → UnitInterval ∂volume,
        x ∈ equalCellCube φ →
          graphonPairValue (graphGraphon G) x e = graphMapPairValue G φ e := by
    refine Sym2.inductionOn e ?_
    intro i j he
    have hF : F.Adj i j := by simpa using he
    have hsquare : ∀ᵐ z ∂unitSquareMeasure,
        z ∈ equalCell (φ i) ×ˢ equalCell (φ j) →
          (graphGraphon G).value z = graphMapPairValue G φ s(i, j) := by
      filter_upwards [(graphGraphon G).value_ae_eq,
        graphGraphon_ae_eq_on_cell G (φ i) (φ j)] with z hzValue hzCell
      intro hz
      exact hzValue.trans (by simpa using hzCell hz)
    have hpull := (measurePreserving_pairProjection (F.ne_of_adj hF)).quasiMeasurePreserving.ae
      hsquare
    filter_upwards [hpull] with x hx
    intro hxcube
    exact hx ⟨hxcube i (Set.mem_univ i), hxcube j (Set.mem_univ j)⟩
  have hall := (Filter.eventually_all_finset (finiteGraphEdges F)).2 fun e he ↦ hpair e he
  filter_upwards [hall] with x hx
  intro hxcube
  apply Finset.prod_congr rfl
  intro e he
  exact hx e he hxcube

lemma measurable_graphonHomIntegrand {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon) :
    Measurable (graphonHomIntegrand F W) := by
  classical
  exact (finiteGraphEdges F).measurable_prod fun e _ ↦ measurable_graphonPairValue W e

lemma graphonHomIntegrand_nonneg {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon)
    (x : Fin f → UnitInterval) :
    0 ≤ graphonHomIntegrand F W x := by
  classical
  exact Finset.prod_nonneg fun e _ ↦ graphonPairValue_nonneg W x e

lemma graphonHomIntegrand_le_one {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon)
    (x : Fin f → UnitInterval) :
    graphonHomIntegrand F W x ≤ 1 := by
  classical
  exact Finset.prod_le_one
    (fun e _ ↦ graphonPairValue_nonneg W x e)
    (fun e _ ↦ graphonPairValue_le_one W x e)

lemma integrable_graphonHomIntegrand {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon) :
    Integrable (graphonHomIntegrand F W) := by
  refine (integrable_const (1 : ℝ)).mono
    (measurable_graphonHomIntegrand F W).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (graphonHomIntegrand_nonneg F W x)]
  simpa using graphonHomIntegrand_le_one F W x

/-- The contribution of one equal-cell cube to a finite adjacency graphon's
homomorphism integral. -/
lemma setIntegral_graphonHomIntegrand_equalCellCube {f n : ℕ}
    (F : SimpleGraph (Fin f)) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (φ : Fin f → Fin n) :
    ∫ x in equalCellCube φ, graphonHomIntegrand F (graphGraphon G) x =
      (1 / (n : ℝ)) ^ f * graphMapIndicator F G φ := by
  calc
    _ = ∫ _x in equalCellCube φ, graphMapIndicator F G φ :=
      setIntegral_congr_ae (measurableSet_equalCellCube φ)
        (graphonHomIntegrand_graphGraphon_ae_on_cube F G φ)
    _ = (1 / (n : ℝ)) ^ f * graphMapIndicator F G φ := by
      rw [setIntegral_const, smul_eq_mul, Measure.real, volume_equalCellCube,
        ENNReal.toReal_pow, ENNReal.toReal_ofReal]
      positivity

/-- The ordinary homomorphism density `t(F,W)`. -/
def graphonHomDensity {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon) : ℝ :=
  ∫ x : Fin f → UnitInterval, graphonHomIntegrand F W x

/-- Partitioning the unit cube into equal cells turns the adjacency-graphon
integral into the finite sum over all vertex maps. -/
lemma graphonHomDensity_graphGraphon_eq_sum {f n : ℕ} (hn : 0 < n)
    (F : SimpleGraph (Fin f)) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    graphonHomDensity F (graphGraphon G) =
      ∑ φ : Fin f → Fin n, (1 / (n : ℝ)) ^ f * graphMapIndicator F G φ := by
  unfold graphonHomDensity
  rw [integral_eq_setIntegral (ae_mem_iUnion_equalCellCube (f := f) hn)]
  rw [integral_iUnion_fintype]
  · simp_rw [setIntegral_graphonHomIntegrand_equalCellCube]
  · exact measurableSet_equalCellCube
  · exact pairwise_disjoint_equalCellCube
  · intro φ
    exact (integrable_graphonHomIntegrand F (graphGraphon G)).integrableOn

lemma graphonHomDensity_nonneg {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon) :
    0 ≤ graphonHomDensity F W :=
  integral_nonneg (graphonHomIntegrand_nonneg F W)

lemma graphonHomDensity_le_one {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon) :
    graphonHomDensity F W ≤ 1 := by
  unfold graphonHomDensity
  calc
    _ ≤ ∫ _ : Fin f → UnitInterval, (1 : ℝ) :=
      integral_mono (integrable_graphonHomIntegrand F W) (integrable_const 1)
        (graphonHomIntegrand_le_one F W)
    _ = 1 := by simp

lemma graphonHomDensity_mem_Icc {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon) :
    graphonHomDensity F W ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨graphonHomDensity_nonneg F W, graphonHomDensity_le_one F W⟩

/-! ## Induced homomorphism density -/

/-- The induced-density integrand: edge factors are `W`, and nonedge factors
are `1 - W`.  The complement graph enumerates exactly the unordered pairs of
distinct vertices that are nonedges of `F`. -/
def graphonInducedIntegrand {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon)
    (x : Fin f → UnitInterval) : ℝ :=
  (∏ e ∈ finiteGraphEdges F, graphonPairValue W x e) *
    ∏ e ∈ finiteGraphEdges Fᶜ, (1 - graphonPairValue W x e)

lemma measurable_graphonInducedIntegrand {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon) :
    Measurable (graphonInducedIntegrand F W) := by
  classical
  refine ((finiteGraphEdges F).measurable_prod fun e _ ↦ measurable_graphonPairValue W e).mul ?_
  exact (finiteGraphEdges Fᶜ).measurable_prod fun e _ ↦
    measurable_const.sub (measurable_graphonPairValue W e)

lemma graphonInducedIntegrand_nonneg {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon)
    (x : Fin f → UnitInterval) :
    0 ≤ graphonInducedIntegrand F W x := by
  classical
  exact mul_nonneg
    (Finset.prod_nonneg fun e _ ↦ graphonPairValue_nonneg W x e)
    (Finset.prod_nonneg fun e _ ↦ sub_nonneg.mpr (graphonPairValue_le_one W x e))

lemma graphonInducedIntegrand_le_one {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon)
    (x : Fin f → UnitInterval) :
    graphonInducedIntegrand F W x ≤ 1 := by
  classical
  have hedge_nonneg : 0 ≤ ∏ e ∈ finiteGraphEdges F, graphonPairValue W x e :=
    Finset.prod_nonneg fun e _ ↦ graphonPairValue_nonneg W x e
  have hedge_le : (∏ e ∈ finiteGraphEdges F, graphonPairValue W x e) ≤ 1 :=
    Finset.prod_le_one
      (fun e _ ↦ graphonPairValue_nonneg W x e)
      (fun e _ ↦ graphonPairValue_le_one W x e)
  have hnonedge_nonneg : 0 ≤ ∏ e ∈ finiteGraphEdges Fᶜ, (1 - graphonPairValue W x e) :=
    Finset.prod_nonneg fun e _ ↦ sub_nonneg.mpr (graphonPairValue_le_one W x e)
  have hnonedge_le : (∏ e ∈ finiteGraphEdges Fᶜ, (1 - graphonPairValue W x e)) ≤ 1 :=
    Finset.prod_le_one
      (fun e _ ↦ sub_nonneg.mpr (graphonPairValue_le_one W x e))
      (fun e _ ↦ by linarith [graphonPairValue_nonneg W x e])
  simpa only [graphonInducedIntegrand, one_mul] using
    mul_le_mul hedge_le hnonedge_le hnonedge_nonneg zero_le_one

lemma integrable_graphonInducedIntegrand {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon) :
    Integrable (graphonInducedIntegrand F W) := by
  refine (integrable_const (1 : ℝ)).mono
    (measurable_graphonInducedIntegrand F W).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (graphonInducedIntegrand_nonneg F W x)]
  simpa using graphonInducedIntegrand_le_one F W x

/-- The induced homomorphism density `t_ind(F,W)`. -/
def graphonInducedDensity {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon) : ℝ :=
  ∫ x : Fin f → UnitInterval, graphonInducedIntegrand F W x

lemma graphonInducedDensity_nonneg {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon) :
    0 ≤ graphonInducedDensity F W :=
  integral_nonneg (graphonInducedIntegrand_nonneg F W)

lemma graphonInducedDensity_le_one {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon) :
    graphonInducedDensity F W ≤ 1 := by
  unfold graphonInducedDensity
  calc
    _ ≤ ∫ _ : Fin f → UnitInterval, (1 : ℝ) :=
      integral_mono (integrable_graphonInducedIntegrand F W) (integrable_const 1)
        (graphonInducedIntegrand_le_one F W)
    _ = 1 := by simp

lemma graphonInducedDensity_mem_Icc {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon) :
    graphonInducedDensity F W ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨graphonInducedDensity_nonneg F W, graphonInducedDensity_le_one F W⟩

/-! ## Finite-graph homomorphism density -/

/-- The ordinary finite-graph homomorphism density.  The numerator counts all
adjacency-preserving vertex maps, and the denominator counts all vertex maps. -/
def graphHomDensity {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (G : SimpleGraph W) : ℝ :=
  (Nat.card (F →g G) : ℝ) / (Fintype.card W : ℝ) ^ Fintype.card V

/-- A graph homomorphism is equivalently an underlying vertex map satisfying
the edge-preservation predicate. -/
def graphHomEquivSubtype {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) :
    (F →g G) ≃ {φ : V → W // IsGraphHomMap F G φ} where
  toFun φ := ⟨φ, fun {_ _} h ↦ map_rel φ h⟩
  invFun φ := ⟨φ, φ.2⟩
  left_inv _ := RelHom.coe_fn_injective rfl
  right_inv _ := Subtype.ext rfl

/-- Summing the finite-map indicators counts graph homomorphisms. -/
lemma sum_graphMapIndicator_eq_card {f n : ℕ} (F : SimpleGraph (Fin f))
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∑ φ : Fin f → Fin n, graphMapIndicator F G φ) = (Nat.card (F →g G) : ℝ) := by
  classical
  have hcard : (Finset.univ.filter fun φ : Fin f → Fin n ↦
      IsGraphHomMap F G φ).card = Nat.card (F →g G) := by
    calc
      _ = Fintype.card {φ : Fin f → Fin n // IsGraphHomMap F G φ} :=
        (Fintype.card_subtype _).symm
      _ = Fintype.card (F →g G) :=
        Fintype.card_congr (graphHomEquivSubtype F G).symm
      _ = Nat.card (F →g G) := Fintype.card_eq_nat_card
  calc
    _ = ∑ φ : Fin f → Fin n, if IsGraphHomMap F G φ then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro φ _
      exact graphMapIndicator_eq_ite F G φ
    _ = ((Finset.univ.filter fun φ : Fin f → Fin n ↦
        IsGraphHomMap F G φ).card : ℝ) := by simp
    _ = (Nat.card (F →g G) : ℝ) := by exact_mod_cast hcard

lemma card_graphHom_le_card_maps {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (G : SimpleGraph W) :
    Nat.card (F →g G) ≤ Fintype.card W ^ Fintype.card V := by
  have h := Nat.card_le_card_of_injective
    (fun φ : F →g G ↦ (φ : V → W)) RelHom.coe_fn_injective
  simpa [Nat.card_fun, Nat.card_eq_fintype_card] using h

lemma graphHomDensity_nonneg {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (G : SimpleGraph W) :
    0 ≤ graphHomDensity F G := by
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)

lemma graphHomDensity_le_one {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (G : SimpleGraph W) :
    graphHomDensity F G ≤ 1 := by
  let d : ℕ := Fintype.card W ^ Fintype.card V
  have hcard : Nat.card (F →g G) ≤ d := by
    simpa [d] using card_graphHom_le_card_maps F G
  by_cases hd : d = 0
  · have hnum : Nat.card (F →g G) = 0 := Nat.eq_zero_of_le_zero (hd ▸ hcard)
    simp [graphHomDensity, hnum]
  · rw [graphHomDensity, div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hd)]
    exact_mod_cast hcard

lemma graphHomDensity_mem_Icc {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (G : SimpleGraph W) :
    graphHomDensity F G ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨graphHomDensity_nonneg F G, graphHomDensity_le_one F G⟩

/-- The step graphon of a nonempty finite graph has exactly the same ordinary
homomorphism density as the all-map finite normalization.

The hypothesis `0 < n` is necessary for this normalization.  If `n = 0`,
`f > 0`, and `F` is edgeless, the graphon integrand is the empty product `1`,
whereas there are no vertex maps and `graphHomDensity` evaluates `0 / 0` as
`0`. -/
theorem graphonHomDensity_graphGraphon {f n : ℕ} (hn : 0 < n)
    (F : SimpleGraph (Fin f)) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    graphonHomDensity F (graphGraphon G) = graphHomDensity F G := by
  rw [graphonHomDensity_graphGraphon_eq_sum hn, ← Finset.mul_sum,
    sum_graphMapIndicator_eq_card]
  simp [graphHomDensity, div_eq_mul_inv, mul_comm]

end

end InducedStars
