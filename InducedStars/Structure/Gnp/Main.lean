import InducedStars.Structure.Gnp.CriticalTypical
import InducedStars.Structure.Gnp.SupercriticalTransfer

/-!
# The complete conditioned induced-star typical-structure theorem

This is the public assembly point for the conditioned `G(n,p)` chapter.
All probabilities use the labeled binomial law conditioned on induced-star
freeness. The high-probability branch gives co-multipartite structure jointly
with the unordered-edge density. The complementary branch includes the
critical point itself and asserts sparse edge mass, not literal emptiness.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The sparse branch includes equality at the critical probability.
For each positive edge-mass tolerance, the corresponding finite event has
conditional probability tending to one. -/
theorem inducedStarGnpSparse_of_le_pK
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hsub : p ≤ pK k) (ξ : ℝ) (hξ : 0 < ξ) :
    Tendsto (fun n ↦ gnpConditionedInducedStarProbability k n p
      (gnpSparseGraphFinset n ξ)) atTop (𝓝 1) := by
  rcases lt_or_eq_of_le hsub with hlt | rfl
  · exact inducedStarGnpSparse_of_lt_pK k hk p hp hlt ξ hξ
  · exact inducedStarGnpSparse_at_pK k hk ξ hξ

/-- Paper: Theorem `thm:gnp-typ-struc`.

For the actual induced-star-free conditioned `G(n,p)` law:
* if `pK k < p`, the graph is co-`(k-1)`-partite and its unordered-edge
  density tends to `gammaFromProbability k p = p + (1-p)/(k-1)`, jointly;
* if `p ≤ pK k`, including equality, it has `o(n²)` edges.

Each asymptotic assertion means that every fixed positive tolerance has
probability tending to one. No edge-count conditioning or uniform graph law
is substituted for the binomial conditional law in either branch. -/
theorem inducedStarGnpTypicalStructure
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    (pK k < p → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n ↦ gnpConditionedInducedStarProbability k n p
        (gnpSupercriticalStructuredGraphFinset k n p ε)) atTop (𝓝 1)) ∧
    (p ≤ pK k → ∀ ξ : ℝ, 0 < ξ →
      Tendsto (fun n ↦ gnpConditionedInducedStarProbability k n p
        (gnpSparseGraphFinset n ξ)) atTop (𝓝 1)) :=
  ⟨fun hsuper ε hε ↦ inducedStarGnpSupercriticalTypicalStructure k hk p hp hsuper ε hε,
    fun hsub ξ hξ ↦ inducedStarGnpSparse_of_le_pK k hk p hp hsub ξ hξ⟩

/-- A single finite event displaying the phase dichotomy. At equality the
definition deliberately takes the sparse branch. -/
noncomputable def gnpTypicalStructureGraphFinset (k n : ℕ) (p ξ : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  if p ≤ pK k then gnpSparseGraphFinset n ξ
  else gnpSupercriticalStructuredGraphFinset k n p ξ

/-- Equivalent one-event formulation of the complete conditioned theorem.
The tolerance is arbitrary and positive, and all regimes use the same exact
finite conditional probability. -/
theorem inducedStarGnpTypicalStructure_probability
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (ξ : ℝ) (hξ : 0 < ξ) :
    Tendsto (fun n ↦ gnpConditionedInducedStarProbability k n p
      (gnpTypicalStructureGraphFinset k n p ξ)) atTop (𝓝 1) := by
  by_cases hsub : p ≤ pK k
  · simpa only [gnpTypicalStructureGraphFinset, if_pos hsub] using
      (inducedStarGnpTypicalStructure k hk p hp).2 hsub ξ hξ
  · simpa only [gnpTypicalStructureGraphFinset, if_neg hsub] using
      (inducedStarGnpTypicalStructure k hk p hp).1 (lt_of_not_ge hsub) ξ hξ

end InducedStars
