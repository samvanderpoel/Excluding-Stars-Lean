import InducedStars.C4.HighDegreeA
import InducedStars.C4.CompanionMatching
import InducedStars.C4.CountingFamilies

/-!
# Constructing the high-A frozen-star witness from actual vertex sets

Paper: Lemma `lemma:FPi1`, Case 2. The auxiliary graph is exactly the
complement of the defect induced on its neighborhood. Nothing about its
candidate count, geometry, or sampling event is assumed.
-/

noncomputable section
open Finset
open scoped Classical
namespace InducedStars

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem c4HighA_star_cross {D : C4Division V} {v : V} (hv : v ∈ D.independentPart)
    {Z : Finset V} (hZ : Z ⊆ D.cliquePart) :
    ∀ z ∈ Z, s(v, z) ∈ c4CrossPotentialEdges D := by
  intro z hz
  exact (mk_mem_c4CrossPotentialEdges D v z).mpr (Or.inl ⟨hv, hZ hz⟩)

def c4HighAConfigurationOfSets {D : C4Division V} (T : SimpleGraph V)
    (v : V) (hv : v ∈ D.independentPart) (N Z : Finset V)
    (hN : N ⊆ D.independentPart) (hNT : ∀ x ∈ N, T.Adj v x)
    (hZ : Z ⊆ D.cliquePart) :
    C4HighAConfiguration (c4FrozenCrossStar D v Z (c4HighA_star_cross hv hZ) false)
      T (T.induce (N : Set V))ᶜ ↥Z := by
  refine ⟨v, hv, Function.Embedding.subtype _, fun x ↦ hN x.prop,
    fun x ↦ hNT x.val x.prop, Function.Embedding.subtype _, fun z ↦ hZ z.prop,
    ?_, ?_, ?_, ?_⟩
  · intro x y h
    exact h.2
  · intro z
    exact (mk_mem_c4CrossStar v Z v z.val).mpr (Or.inl ⟨rfl, z.prop⟩)
  · intro z
    simp
  · intro x z
    change s(x.val, z.val) ∈ c4CrossPotentialEdges D \ c4CrossStar v Z
    refine Finset.mem_sdiff.mpr ⟨(mk_mem_c4CrossPotentialEdges D _ _).mpr
      (Or.inl ⟨hN x.prop, hZ z.prop⟩), ?_⟩
    intro he
    rcases (mk_mem_c4CrossStar v Z _ _).mp he with ⟨hx, _⟩ | ⟨hz, _⟩
    · exact (hNT x.val x.prop).ne hx.symm
    · exact Finset.disjoint_left.mp D.disjoint hv (hz ▸ hZ z.prop)

/-- The complement-density estimate includes the finite `|N| >= 4`
threshold needed for the paper's `|N|²/8` reserve. -/
theorem c4HighA_complement_dense (T : SimpleGraph V) (N : Finset V)
    (hN : 4 ≤ N.card)
    (hsmall : ((finiteGraphEdges (T.induce (N : Set V))).card : ℝ) ≤ (N.card : ℝ) ^ 2 / 4) :
    (N.card : ℝ) ^ 2 / 8 ≤ (finiteGraphEdges (T.induce (N : Set V))ᶜ).card := by
  have hc := c4Within_complement_edgeCount_add T N
  rw [card_finiteGraphEdges_c4WithinGraph, card_finiteGraphEdges_c4WithinGraph] at hc
  have hind : Tᶜ.induce (N : Set V) = (T.induce (N : Set V))ᶜ := by
    ext x y
    simp only [SimpleGraph.induce_adj, SimpleGraph.compl_adj, Subtype.val_injective.ne_iff]
  rw [hind] at hc
  have hcR : ((finiteGraphEdges (T.induce (N : Set V))ᶜ).card : ℝ) +
      (finiteGraphEdges (T.induce (N : Set V))).card = (N.card.choose 2 : ℝ) := by
    exact_mod_cast hc
  rw [Nat.cast_choose_two] at hcR
  have hNR : (4 : ℝ) ≤ N.card := by exact_mod_cast hN
  nlinarith

/-- Finite source-shaped frozen-family penalty, with actual `N,Z` and the
exact reduced binomial slice. The final exponent is quadratic in the
common linear-size lower bound `nu`. -/
theorem c4HighA_starFiber_le {n : ℕ} (D : C4Division (Fin n))
    (T : SimpleGraph (Fin n)) (v : Fin n) (hv : v ∈ D.independentPart)
    (N Z : Finset (Fin n)) (hN : N ⊆ D.independentPart)
    (hNT : ∀ x ∈ N, T.Adj v x) (hZ : Z ⊆ D.cliquePart) (m : ℕ) {nu beta : ℝ}
    (hnu : 0 < nu) (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hn : 4 ≤ nu * n)
    (hNsize : nu * n ≤ (N.card : ℝ)) (hZsize : nu * n ≤ (Z.card : ℝ))
    (hsmall : ((finiteGraphEdges (T.induce (N : Set (Fin n)))).card : ℝ) ≤ (N.card : ℝ) ^ 2 / 4)
    (hq : (c4FrozenCrossStar D v Z (c4HighA_star_cross hv hZ) false).quota T m ≤
      (c4FrozenCrossStar D v Z (c4HighA_star_cross hv hZ) false).optional.card)
    (hband : beta ≤ DenseGraph.FixedCardinalityBlockModel.quotaParameter
      (c4FrozenCrossStar D v Z (c4HighA_star_cross hv hZ) false).optional.card
      ((c4FrozenCrossStar D v Z (c4HighA_star_cross hv hZ) false).quota T m)) :
    let W := c4FrozenCrossStar D v Z (c4HighA_star_cross hv hZ) false
    ((W.freeFiber T m).card : ℝ) ≤
      (W.optional.card.choose (W.quota T m) : ℝ) * ((W.optional.card : ℝ) + 1) *
        Real.exp (-(beta ^ 4 * nu ^ 2 / 64) * (n : ℝ) ^ 2) := by
  let H := (T.induce (N : Set (Fin n)))ᶜ
  letI : LinearOrder (C4StarCandidate H ↥Z) :=
    LinearOrder.lift' (Fintype.equivFin (C4StarCandidate H ↥Z))
      (Fintype.equivFin (C4StarCandidate H ↥Z)).injective
  let K := c4HighAConfigurationOfSets T v hv N Z hN hNT hZ
  have hN4 : 4 ≤ N.card := by exact_mod_cast (show (4 : ℝ) ≤ N.card by linarith)
  have hZpos : 0 < Z.card := by exact_mod_cast (show (0 : ℝ) < Z.card by linarith)
  have hdense := c4HighA_complement_dense T N hN4 hsmall
  have h := K.fixedFiber_le PriorInstances.principalJansonInput m hq hbeta hbeta1 hband
    (by simpa using (show 1 ≤ N.card by omega)) (by simpa using hZpos) (by simpa using hdense)
  have hprod := mul_le_mul hNsize hZsize (by positivity : 0 ≤ nu * (n : ℝ))
    (by positivity : 0 ≤ (N.card : ℝ))
  have hscaled := mul_le_mul_of_nonneg_left hprod (show 0 ≤ beta ^ 4 / 64 by positivity)
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
  have hcardN : Fintype.card (N : Set (Fin n)) = N.card := by simp
  rw [hcardN, Fintype.card_coe]
  nlinarith only [hscaled]

end InducedStars
