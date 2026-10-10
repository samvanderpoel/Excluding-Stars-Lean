import DenseGraph.Graphon.Inputs
import InducedStars.Graphon.Functionals
import Mathlib.Probability.IdentDistrib

/-!
# Axiom-free cut-zero equivalence cores

Every theorem that needs a published graph-limit result receives the exact
theorem-valued capability explicitly.  Project-facing wrappers instantiate
those capabilities in `InducedStars.Graphon.Equivalence`.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace InducedStars

/-- Apply the same interval map to both coordinates of the unit square. -/
def diagonalProductMap (φ : UnitInterval → UnitInterval) : UnitSquare → UnitSquare :=
  fun z ↦ (φ z.1, φ z.2)

/-- The diagonal product of a measure-preserving interval map preserves
product volume.  This is the project-facing specialization of Mathlib's
`MeasurePreserving.prod`. -/
theorem measurePreserving_diagonalProductMap
    {φ : UnitInterval → UnitInterval}
    (hφ : MeasurePreserving φ volume volume) :
    MeasurePreserving (diagonalProductMap φ)
      unitSquareMeasure unitSquareMeasure := by
  convert hφ.prod hφ using 1
  ext z <;> rfl

/-- Cut-distance zero supplies a common probability space on which canonical
representatives of the two graphons agree after measure-preserving pullback. -/
theorem commonPullback_of_cutDist_eq_zero_of_inputs
    (homInput : DenseGraph.CutZeroHomDensityInput)
    (pullbackInput : DenseGraph.CommonPullbackInput)
    (U W : Graphon) (hcut : cutDist U W = 0) :
    ∃ φ ψ : UnitInterval → UnitInterval,
      MeasurePreserving φ volume volume ∧
      MeasurePreserving ψ volume volume ∧
      ∀ᵐ z ∂unitSquareMeasure,
        U.value (φ z.1, φ z.2) = W.value (ψ z.1, ψ z.2) :=
  pullbackInput.commonPullback U W
    (homInput.homDensity_eq U W hcut)

/-- Graphons at cut distance zero have the same pushforward law of their
canonical `[0,1]`-valued representatives on the unit square. -/
theorem graphonValueLaw_eq_of_cutDist_eq_zero_of_inputs
    (homInput : DenseGraph.CutZeroHomDensityInput)
    (pullbackInput : DenseGraph.CommonPullbackInput)
    (U W : Graphon) (hcut : cutDist U W = 0) :
    Measure.map U.value unitSquareMeasure =
      Measure.map W.value unitSquareMeasure := by
  obtain ⟨φ, ψ, hφ, hψ, heq⟩ :=
    commonPullback_of_cutDist_eq_zero_of_inputs
      homInput pullbackInput U W hcut
  let Φ := diagonalProductMap φ
  let Ψ := diagonalProductMap ψ
  have hΦ : MeasurePreserving Φ unitSquareMeasure unitSquareMeasure :=
    measurePreserving_diagonalProductMap hφ
  have hΨ : MeasurePreserving Ψ unitSquareMeasure unitSquareMeasure :=
    measurePreserving_diagonalProductMap hψ
  have hU : HasLaw U.value (Measure.map U.value unitSquareMeasure)
      unitSquareMeasure := ⟨U.measurable_value.aemeasurable, rfl⟩
  have hW : HasLaw W.value (Measure.map W.value unitSquareMeasure)
      unitSquareMeasure := ⟨W.measurable_value.aemeasurable, rfl⟩
  have hUΦ : HasLaw (U.value ∘ Φ) (Measure.map U.value unitSquareMeasure)
      unitSquareMeasure := hU.comp hΦ.hasLaw
  have hWΨ : HasLaw (W.value ∘ Ψ) (Measure.map W.value unitSquareMeasure)
      unitSquareMeasure := hW.comp hΨ.hasLaw
  have hcomp : (U.value ∘ Φ) =ᵐ[unitSquareMeasure] (W.value ∘ Ψ) := by
    filter_upwards [heq] with z hz
    simpa [Φ, Ψ, diagonalProductMap, Function.comp_def] using hz
  calc
    Measure.map U.value unitSquareMeasure =
        Measure.map (U.value ∘ Φ) unitSquareMeasure := hUΦ.map_eq.symm
    _ = Measure.map (W.value ∘ Ψ) unitSquareMeasure :=
      Measure.map_congr hcomp
    _ = Measure.map W.value unitSquareMeasure := hWΨ.map_eq

/-- Equality in cut distance zero preserves the integral of every measurable
scalar observable of the canonical graphon value.  No separate integrability
hypothesis is needed: identically distributed Bochner integrands have equal
integrals, including under Mathlib's non-integrable-value convention. -/
theorem graphonValueIntegral_eq_of_cutDist_eq_zero_of_inputs
    (homInput : DenseGraph.CutZeroHomDensityInput)
    (pullbackInput : DenseGraph.CommonPullbackInput)
    (U W : Graphon) (hcut : cutDist U W = 0)
    (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ z : UnitSquare, g (U.value z) ∂unitSquareMeasure) =
      ∫ z : UnitSquare, g (W.value z) ∂unitSquareMeasure := by
  have hident : IdentDistrib U.value W.value
      unitSquareMeasure unitSquareMeasure :=
    ⟨U.measurable_value.aemeasurable, W.measurable_value.aemeasurable,
      graphonValueLaw_eq_of_cutDist_eq_zero_of_inputs
        homInput pullbackInput U W hcut⟩
  exact (hident.comp hg).integral_eq

/-- Graphon entropy depends only on the cut-distance-zero equivalence class. -/
theorem graphonEntropy_eq_of_cutDist_eq_zero_of_inputs
    (homInput : DenseGraph.CutZeroHomDensityInput)
    (pullbackInput : DenseGraph.CommonPullbackInput)
    (U W : Graphon) (hcut : cutDist U W = 0) :
    graphonEntropy U = graphonEntropy W := by
  exact graphonValueIntegral_eq_of_cutDist_eq_zero_of_inputs
    homInput pullbackInput U W hcut binaryEntropy
      binaryEntropy_continuous.measurable

/-- Edge density depends only on the cut-distance-zero equivalence class. -/
theorem graphonEdgeDensity_eq_of_cutDist_eq_zero_of_input
    (homInput : DenseGraph.CutZeroHomDensityInput)
    (U W : Graphon) (hcut : cutDist U W = 0) :
    graphonEdgeDensity U = graphonEdgeDensity W := by
  exact homInput.homDensity_eq U W hcut 2 oneEdgeGraph

/-! ## Induced densities by finite inclusion--exclusion -/

/-- Add a selected finite set of unordered pairs to a graph.  In the
inclusion--exclusion formula below the selected pairs are all nonedges of the
original graph, so no loops are introduced and the union is disjoint. -/
def inducedExpansionGraph {f : ℕ} (F : SimpleGraph (Fin f))
    (t : Finset (Sym2 (Fin f))) : SimpleGraph (Fin f) :=
  F ⊔ SimpleGraph.fromEdgeSet (t : Set (Sym2 (Fin f)))

private lemma finiteGraphEdges_inducedExpansionGraph {f : ℕ}
    (F : SimpleGraph (Fin f)) (t : Finset (Sym2 (Fin f)))
    (ht : t ⊆ finiteGraphEdges Fᶜ) :
    finiteGraphEdges (inducedExpansionGraph F t) =
      finiteGraphEdges F ∪ t := by
  classical
  ext e
  simp only [mem_finiteGraphEdges, inducedExpansionGraph,
    SimpleGraph.edgeSet_sup, Set.mem_union, SimpleGraph.edgeSet_fromEdgeSet,
    Set.mem_sdiff, Finset.mem_coe, Finset.mem_union]
  constructor
  · rintro (he | ⟨he, _⟩)
    · exact Or.inl he
    · exact Or.inr he
  · rintro (he | he)
    · exact Or.inl he
    · refine Or.inr ⟨he, ?_⟩
      have hec : e ∈ (Fᶜ).edgeSet := (mem_finiteGraphEdges (F := Fᶜ) e).mp (ht he)
      exact ((Fᶜ).not_isDiag_of_mem_edgeSet hec)

private lemma disjoint_finiteGraphEdges_nonedgeSubset {f : ℕ}
    (F : SimpleGraph (Fin f)) (t : Finset (Sym2 (Fin f)))
    (ht : t ⊆ finiteGraphEdges Fᶜ) :
    Disjoint (finiteGraphEdges F) t := by
  rw [Finset.disjoint_left]
  intro e heF het
  have heFc := ht het
  rw [mem_finiteGraphEdges] at heF heFc
  have hdisj : Disjoint F.edgeSet (Fᶜ).edgeSet :=
    SimpleGraph.disjoint_edgeSet.mpr disjoint_compl_right
  exact hdisj.le_bot ⟨heF, heFc⟩

private lemma graphonHomIntegrand_inducedExpansionGraph {f : ℕ}
    (F : SimpleGraph (Fin f)) (W : Graphon)
    (x : Fin f → UnitInterval) (t : Finset (Sym2 (Fin f)))
    (ht : t ⊆ finiteGraphEdges Fᶜ) :
    graphonHomIntegrand (inducedExpansionGraph F t) W x =
      ( ∏ e ∈ finiteGraphEdges F, graphonPairValue W x e) *
        ∏ e ∈ t, graphonPairValue W x e := by
  classical
  rw [graphonHomIntegrand, finiteGraphEdges_inducedExpansionGraph F t ht,
    Finset.prod_union (disjoint_finiteGraphEdges_nonedgeSubset F t ht)]

/-- Pointwise finite inclusion--exclusion expansion of the induced-density
integrand into ordinary homomorphism integrands of supergraphs of `F`. -/
theorem graphonInducedIntegrand_inclusionExclusion {f : ℕ}
    (F : SimpleGraph (Fin f)) (W : Graphon) (x : Fin f → UnitInterval) :
    graphonInducedIntegrand F W x =
      ∑ t ∈ (finiteGraphEdges Fᶜ).powerset,
        (-1 : ℝ) ^ t.card * graphonHomIntegrand (inducedExpansionGraph F t) W x := by
  classical
  unfold graphonInducedIntegrand
  rw [Finset.prod_sub (fun _ ↦ (1 : ℝ)) (graphonPairValue W x)
    (finiteGraphEdges Fᶜ), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have htsub : t ⊆ finiteGraphEdges Fᶜ := Finset.mem_powerset.mp ht
  rw [graphonHomIntegrand_inducedExpansionGraph F W x t htsub]
  simp only [Finset.prod_const_one]
  ring

/-- The induced density is the finite inclusion--exclusion combination of
ordinary homomorphism densities of edge-supergraphs. -/
theorem graphonInducedDensity_inclusionExclusion {f : ℕ}
    (F : SimpleGraph (Fin f)) (W : Graphon) :
    graphonInducedDensity F W =
      ∑ t ∈ (finiteGraphEdges Fᶜ).powerset,
        (-1 : ℝ) ^ t.card *
          graphonHomDensity (inducedExpansionGraph F t) W := by
  unfold graphonInducedDensity
  simp_rw [graphonInducedIntegrand_inclusionExclusion F W]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t _ht
    rw [integral_const_mul]
    rfl
  · intro t _ht
    exact (integrable_graphonHomIntegrand (inducedExpansionGraph F t) W).const_mul _

/-- Every finite induced homomorphism density depends only on the
cut-distance-zero equivalence class. -/
theorem graphonInducedDensity_eq_of_cutDist_eq_zero_of_input
    (homInput : DenseGraph.CutZeroHomDensityInput) {f : ℕ}
    (F : SimpleGraph (Fin f)) (U W : Graphon)
    (hcut : cutDist U W = 0) :
    graphonInducedDensity F U = graphonInducedDensity F W := by
  rw [graphonInducedDensity_inclusionExclusion,
    graphonInducedDensity_inclusionExclusion]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [homInput.homDensity_eq U W hcut]

end InducedStars
