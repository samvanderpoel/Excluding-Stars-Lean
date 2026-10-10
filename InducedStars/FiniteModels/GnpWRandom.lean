import InducedStars.FiniteModels.GnpCore
import InducedStars.FiniteModels.WRandom
import InducedStars.Graphon.Functionals

/-!
# The binomial random graph as a constant-graphon sample

This file identifies the two exact finite probability models already exposed by
the library.  Sampling a labeled graph from the constant graphon with value
`p ∈ [0,1]` gives precisely the labeled `G(n,p)` law: every unordered edge
is present independently with probability `p`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace InducedStars

private theorem graphonPairValue_constantGraphon_ae_eq {n : ℕ}
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (e : Sym2 (Fin n))
    (he : ¬e.IsDiag) :
    (fun x : Fin n → UnitInterval ↦
      graphonPairValue (constantGraphon p hp) x e) =ᵐ[volume]
        fun _ ↦ p := by
  induction e using Sym2.inductionOn with
  | _ i j =>
      have hij : i ≠ j := by
        simpa only [Sym2.mk_isDiag_iff] using he
      calc
        (fun x : Fin n → UnitInterval ↦
            graphonPairValue (constantGraphon p hp) x s(i, j)) =ᵐ[volume]
            (fun x ↦ constantGraphon p hp (x i, x j)) :=
          graphonPairValue_ae_eq_of_ne (constantGraphon p hp) hij
        _ =ᵐ[volume] (fun _ ↦ p) :=
          (measurePreserving_pairProjection hij).quasiMeasurePreserving.ae_eq_comp
            (constantGraphon_ae_eq p hp)

private theorem finiteGraphEdges_compl_card {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    (finiteGraphEdges Gᶜ).card =
      completeEdgeCount n - (finiteGraphEdges G).card := by
  classical
  have hcompl : finiteGraphEdges Gᶜ =
      finiteGraphEdges (⊤ : SimpleGraph (Fin n)) \ finiteGraphEdges G := by
    ext e
    induction e using Sym2.inductionOn with
    | _ i j => simp [SimpleGraph.compl_adj]
  have hsubset : finiteGraphEdges G ⊆
      finiteGraphEdges (⊤ : SimpleGraph (Fin n)) := by
    intro e he
    exact (mem_finiteGraphEdges (⊤ : SimpleGraph (Fin n)) e).mpr
      (SimpleGraph.edgeSet_mono le_top ((mem_finiteGraphEdges G e).mp he))
  have htop : (finiteGraphEdges (⊤ : SimpleGraph (Fin n))).card =
      completeEdgeCount n := by
    have hedgeSet : finiteGraphEdges (⊤ : SimpleGraph (Fin n)) =
        (Sym2.diagSetᶜ : Set (Sym2 (Fin n))).toFinset := by
      ext e
      induction e using Sym2.inductionOn with
      | _ i j => simp
    rw [hedgeSet, Set.toFinset_card, Sym2.card_diagSet_compl]
    simp only [Fintype.card_fin, completeEdgeCount]
  rw [hcompl, Finset.card_sdiff, Finset.inter_eq_left.mpr hsubset, htop]

/-- The marginal mass of a labeled graph sampled from the constant graphon
`p` is exactly its labeled `G(n,p)` mass. -/
theorem wRandomGraphMass_constantGraphon {n : ℕ}
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (G : SimpleGraph (Fin n)) :
    wRandomGraphMass (constantGraphon p hp) G = gnpGraphWeight p G := by
  classical
  calc
    wRandomGraphMass (constantGraphon p hp) G =
        ∫ _x : Fin n → UnitInterval, gnpGraphWeight p G := by
      unfold wRandomGraphMass
      apply integral_congr_ae
      have hedge : ∀ᵐ x : Fin n → UnitInterval ∂volume,
        ∀ e ∈ finiteGraphEdges G,
          graphonPairValue (constantGraphon p hp) x e = p :=
        (finiteGraphEdges G).eventually_all.2 fun e he ↦
          graphonPairValue_constantGraphon_ae_eq p hp e
            (G.not_isDiag_of_mem_edgeSet ((mem_finiteGraphEdges G e).mp he))
      have hnonedge : ∀ᵐ x : Fin n → UnitInterval ∂volume,
        ∀ e ∈ finiteGraphEdges Gᶜ,
          graphonPairValue (constantGraphon p hp) x e = p :=
        (finiteGraphEdges Gᶜ).eventually_all.2 fun e he ↦
          graphonPairValue_constantGraphon_ae_eq p hp e
            (Gᶜ.not_isDiag_of_mem_edgeSet ((mem_finiteGraphEdges Gᶜ e).mp he))
      filter_upwards [hedge, hnonedge] with x hx hxc
      unfold wRandomConditionalWeight graphonInducedIntegrand
      rw [Finset.prod_congr rfl hx, Finset.prod_congr rfl fun e he ↦
        congrArg (1 - ·) (hxc e he)]
      simp only [Finset.prod_const]
      rw [finiteGraphEdges_compl_card,
        finiteGraphEdges_card_eq_edgeFinset_card]
      unfold gnpGraphWeight
      rfl
    _ = gnpGraphWeight p G := by simp

/-- On a finite graph event, the constant-graphon probability is exactly the
`G(n,p)` event probability. -/
theorem wRandomGraphEventProbability_constantGraphon {n : ℕ}
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (Q : Finset (SimpleGraph (Fin n))) :
    wRandomGraphEventProbability (constantGraphon p hp) {G | G ∈ Q} =
      gnpGraphEventProbability p Q := by
  classical
  simp [wRandomGraphEventProbability, gnpGraphEventProbability,
    wRandomGraphMass_constantGraphon p hp]

end InducedStars
