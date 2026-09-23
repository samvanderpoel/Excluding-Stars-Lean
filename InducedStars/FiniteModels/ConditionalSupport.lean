import InducedStars.FiniteModels.WRandom
import InducedStars.Regularity.Basic
import Mathlib.Tactic

/-!
# Conditional support of the graphon sampling law

This file proves the local support fact behind sampling from an induced-free
graphon.  If the induced density of `H` in `W` vanishes, then for almost every
latent configuration every labeled graph with positive conditional mass is
induced-`H`-free.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace InducedStars

/-! ## Restricting a finite probability cube to injectively chosen coordinates -/

/-- Restriction of a latent configuration to injectively chosen coordinates. -/
def coordinateRestriction {h n : ℕ} (f : Fin h ↪ Fin n)
    (x : Fin n → UnitInterval) : Fin h → UnitInterval :=
  fun i ↦ x (f i)

/-- An injective coordinate restriction of a finite product of unit-interval
volume measures again has product volume. -/
theorem measurePreserving_coordinateRestriction {h n : ℕ} (f : Fin h ↪ Fin n) :
    MeasurePreserving (coordinateRestriction f)
      (volume : Measure (Fin n → UnitInterval))
      (volume : Measure (Fin h → UnitInterval)) := by
  have hIndep : iIndepFun
      (fun i : Fin h ↦ fun x : Fin n → UnitInterval ↦ x (f i))
      (volume : Measure (Fin n → UnitInterval)) :=
    iIndepFun.precomp f.injective
      (iIndepFun_pi (X := fun _ : Fin n ↦ id) (fun _ ↦ aemeasurable_id))
  have hLaw (i : Fin h) :
      HasLaw (fun x : Fin n → UnitInterval ↦ x (f i))
        (volume : Measure UnitInterval)
        (volume : Measure (Fin n → UnitInterval)) :=
    (measurePreserving_eval
      (fun _ : Fin n ↦ (volume : Measure UnitInterval)) (f i)).hasLaw
  exact (hIndep.hasLaw_pi hLaw).measurePreserving (by
    simpa only [coordinateRestriction] using
      (measurable_pi_lambda _ fun i ↦ measurable_pi_apply (f i)))

private theorem graphonPairValue_coordinateRestriction {h n : ℕ}
    (W : Graphon) (f : Fin h ↪ Fin n) (x : Fin n → UnitInterval)
    (e : Sym2 (Fin h)) :
    graphonPairValue W (coordinateRestriction f x) e =
      graphonPairValue W x (Sym2.map f e) := by
  induction e using Sym2.inductionOn with
  | _ i j => simp [coordinateRestriction]

/-! ## Positive conditional mass forces every selected pair factor to be positive -/

private theorem edgeFactor_pos_of_conditionalWeight_pos {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (G : SimpleGraph (Fin n))
    (hpos : 0 < wRandomConditionalWeight W x G)
    (e : Sym2 (Fin n)) (he : e ∈ finiteGraphEdges G) :
    0 < graphonPairValue W x e := by
  have hproduct :
      0 < (∏ a ∈ finiteGraphEdges G, graphonPairValue W x a) *
        ∏ a ∈ finiteGraphEdges Gᶜ, (1 - graphonPairValue W x a) := by
    simpa only [wRandomConditionalWeight, graphonInducedIntegrand] using hpos
  have hnonedge_nonneg :
      0 ≤ ∏ a ∈ finiteGraphEdges Gᶜ, (1 - graphonPairValue W x a) :=
    Finset.prod_nonneg fun a _ ↦
      sub_nonneg.mpr (graphonPairValue_le_one W x a)
  have hedge_pos : 0 < ∏ a ∈ finiteGraphEdges G, graphonPairValue W x a :=
    pos_of_mul_pos_left hproduct hnonedge_nonneg
  have hne : graphonPairValue W x e ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hedge_pos.ne') e he
  exact lt_of_le_of_ne (graphonPairValue_nonneg W x e) hne.symm

private theorem nonedgeFactor_pos_of_conditionalWeight_pos {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (G : SimpleGraph (Fin n))
    (hpos : 0 < wRandomConditionalWeight W x G)
    (e : Sym2 (Fin n)) (he : e ∈ finiteGraphEdges Gᶜ) :
    0 < 1 - graphonPairValue W x e := by
  have hproduct :
      0 < (∏ a ∈ finiteGraphEdges G, graphonPairValue W x a) *
        ∏ a ∈ finiteGraphEdges Gᶜ, (1 - graphonPairValue W x a) := by
    simpa only [wRandomConditionalWeight, graphonInducedIntegrand] using hpos
  have hedge_nonneg :
      0 ≤ ∏ a ∈ finiteGraphEdges G, graphonPairValue W x a :=
    Finset.prod_nonneg fun a _ ↦ graphonPairValue_nonneg W x a
  have hnonedge_pos :
      0 < ∏ a ∈ finiteGraphEdges Gᶜ, (1 - graphonPairValue W x a) :=
    pos_of_mul_pos_right hproduct hedge_nonneg
  have hne : 1 - graphonPairValue W x e ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hnonedge_pos.ne') e he
  exact lt_of_le_of_ne
    (sub_nonneg.mpr (graphonPairValue_le_one W x e)) hne.symm

/-- Along an induced embedding, positive conditional mass of the host graph
forces the forbidden graph's induced-density integrand to be positive on the
restricted latent coordinates. -/
private theorem graphonInducedIntegrand_pos_of_embedding {h n : ℕ}
    (H : SimpleGraph (Fin h)) (W : Graphon) (x : Fin n → UnitInterval)
    (G : SimpleGraph (Fin n)) (φ : H ↪g G)
    (hpos : 0 < wRandomConditionalWeight W x G) :
    0 < graphonInducedIntegrand H W
      (coordinateRestriction φ.toEmbedding x) := by
  unfold graphonInducedIntegrand
  apply mul_pos
  · apply Finset.prod_pos
    intro e he
    rw [graphonPairValue_coordinateRestriction]
    apply edgeFactor_pos_of_conditionalWeight_pos W x G hpos
    change Sym2.map (φ : Fin h → Fin n) e ∈ finiteGraphEdges G
    simpa only [mem_finiteGraphEdges] using
      (SimpleGraph.Embedding.map_mem_edgeSet_iff φ).2
        (by simpa only [mem_finiteGraphEdges] using he)
  · apply Finset.prod_pos
    intro e he
    rw [graphonPairValue_coordinateRestriction]
    apply nonedgeFactor_pos_of_conditionalWeight_pos W x G hpos
    change Sym2.map (φ : Fin h → Fin n) e ∈ finiteGraphEdges Gᶜ
    let φc : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv φ
    have hemapped : Sym2.map φc e ∈ finiteGraphEdges Gᶜ := by
      simpa only [mem_finiteGraphEdges] using
        (SimpleGraph.Embedding.map_mem_edgeSet_iff φc).2
          (by simpa only [mem_finiteGraphEdges] using he)
    have hcoe : (φc : Fin h → Fin n) = (φ : Fin h → Fin n) := rfl
    rw [hcoe] at hemapped
    exact hemapped

/-! ## Almost-everywhere conditional support -/

/-- A nonnegative induced-density integrand with zero integral vanishes
almost everywhere. -/
theorem ae_graphonInducedIntegrand_eq_zero {h : ℕ}
    (H : SimpleGraph (Fin h)) (W : Graphon)
    (hfree : graphonInducedDensity H W = 0) :
    ∀ᵐ y : Fin h → UnitInterval,
      graphonInducedIntegrand H W y = 0 := by
  apply (integral_eq_zero_iff_of_nonneg
    (graphonInducedIntegrand_nonneg H W)
    (integrable_graphonInducedIntegrand H W)).1
  simpa only [graphonInducedDensity] using hfree

/-- If `H` has zero induced density in `W`, then almost every latent
configuration gives positive conditional mass only to induced-`H`-free
labeled graphs. -/
theorem ae_conditionalSupport_inducedFree {h n : ℕ}
    (H : SimpleGraph (Fin h)) (W : Graphon)
    (hfree : graphonInducedDensity H W = 0) :
    ∀ᵐ x : Fin n → UnitInterval, ∀ G : SimpleGraph (Fin n),
      0 < wRandomConditionalWeight W x G →
        ¬Regularity.InducedEmbeds H G := by
  have hzero := ae_graphonInducedIntegrand_eq_zero H W hfree
  refine eventually_countable_forall.2 fun G ↦ ?_
  have hallEmbeddings :
      ∀ᵐ x : Fin n → UnitInterval, ∀ φ : H ↪g G,
        graphonInducedIntegrand H W
          (coordinateRestriction φ.toEmbedding x) = 0 :=
    eventually_countable_forall.2 fun φ ↦ by
      have hpull :=
        (measurePreserving_coordinateRestriction φ.toEmbedding).quasiMeasurePreserving
          |>.ae_eq_comp hzero
      filter_upwards [hpull] with x hx
      simpa only [Function.comp_def, Pi.zero_apply] using hx
  filter_upwards [hallEmbeddings] with x hx
  intro hpos hEmbeds
  rcases hEmbeds with ⟨φ⟩
  have hpositive :=
    graphonInducedIntegrand_pos_of_embedding H W x G φ hpos
  rw [hx φ] at hpositive
  exact (lt_irrefl 0) hpositive

end InducedStars
