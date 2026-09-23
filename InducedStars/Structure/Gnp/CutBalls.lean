import InducedStars.Structure.Gnp.OptimizerGeometry
import InducedStars.FiniteModels.GnpConditioned
import InducedStars.Structure.Subcritical.Closeness

/-!
# Weighted cut balls and their exact-edge fibers

Separation from zero supplies the finite positive-density hypothesis needed
by the profile cores, including at the full complete-core endpoint. No
strict-subcritical classification is used in this finite bridge.
-/

noncomputable section

open Finset Set
open scoped Classical

namespace InducedStars

noncomputable local instance cutBallsEdgeSetFintype {n : ℕ}
    (G : SimpleGraph (Fin n)) : Fintype G.edgeSet := graphFamiliesEdgeSetFintype G

theorem graphFamilyEdgeSlice_gnpInducedStarCutBall
    (k n m : ℕ) (W : Graphon) (tau : ℝ) :
    graphFamilyEdgeSlice (gnpInducedStarCutBallFinset k W tau n) m =
      subcriticalCandidateCutBallGraphFinset k n m W tau := by
  ext G
  simp only [mem_graphFamilyEdgeSlice, mem_gnpInducedStarCutBallFinset,
    mem_subcriticalCandidateCutBallGraphFinset, mem_inducedStarFreeGraphFinsetWithEdges]
  tauto

/-- A positive separation from zero forces positive finite edge density in
a sufficiently small cut ball, independently of the candidate representation. -/
theorem edgeCount_lower_of_cutBall_separated_zero
    {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) (W : Graphon)
    {gamma tau : ℝ} (hgamma : 0 ≤ gamma)
    (hseparated : gamma ≤ cutDist W zeroGraphon)
    (htau : tau ≤ gamma / 2) (hcut : cutDist (graphGraphon G) W < tau) :
    gamma / 4 * (n : ℝ)^2 ≤ G.edgeFinset.card := by
  have hedge := abs_graphonEdgeDensity_sub_le_cutDist_via_relabeling (graphGraphon G) W
  rw [DenseGraph.cutDist_zeroGraphon] at hseparated
  have hden : gamma / 2 ≤ graphonEdgeDensity (graphGraphon G) := by
    have hh := (abs_le.mp hedge).1
    linarith
  rw [graphonEdgeDensity_graphGraphon hn] at hden
  have hn2 : (0 : ℝ) < (n : ℝ)^2 := by positivity
  have hmul := (le_div_iff₀ hn2).mp hden
  have heq : finiteGraphEdges G = G.edgeFinset := by
    ext e
    rw [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  rw [heq] at hmul
  linarith

/-- Small edge-count fibers of a separated cut ball are empty. This is the
uniformity needed before summing finite profile estimates over all `m`. -/
theorem subcriticalCandidateCutBall_eq_empty_of_edgeCount_lt
    {k n m : ℕ} (hn : 0 < n) (W : Graphon)
    {gamma tau : ℝ} (hgamma : 0 ≤ gamma)
    (hseparated : gamma ≤ cutDist W zeroGraphon) (htau : tau ≤ gamma / 2)
    (hm : (m : ℝ) < gamma / 4 * (n : ℝ)^2) :
    subcriticalCandidateCutBallGraphFinset k n m W tau = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨G, hG⟩
  obtain ⟨hfree, hcut⟩ := mem_subcriticalCandidateCutBallGraphFinset.mp hG
  have he := (mem_inducedStarFreeGraphFinsetWithEdges.mp hfree).2
  have hbound := edgeCount_lower_of_cutBall_separated_zero hn G W hgamma hseparated htau hcut
  rw [he] at hbound
  exact (not_lt_of_ge hbound) hm

end InducedStars
