import DenseGraph.Graphon.Inputs
import Mathlib.Data.Fintype.Basic

/-!
# Finite representative-centred cut covers

Sequential compactness of the cut pseudometric implies a finite net in
every subset. No topology on a particular family of representatives, nor
literal L1 compactness of that family, is used.
-/

noncomputable section
open Filter Set Topology
open InducedStars
namespace DenseGraph

/-- A finite cut net whose centres belong to the requested subset. The
published compactness capability is explicit and no new axiom is declared. -/
theorem SequentialCompactnessInput.exists_finite_cut_cover
    (C : SequentialCompactnessInput) (S : Set Graphon) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ F : Finset Graphon, (∀ W ∈ F, W ∈ S) ∧
      ∀ W ∈ S, ∃ U ∈ F, cutDist W U < epsilon := by
  classical
  by_contra hcover
  push_neg at hcover
  obtain ⟨f, hf, hseparated⟩ := exists_seq_of_forall_finset_exists
    (fun W : Graphon ↦ W ∈ S) (fun U W ↦ epsilon ≤ cutDist U W) (by
      intro F hF
      obtain ⟨W, hW, hfar⟩ := hcover F hF
      refine ⟨W, hW, ?_⟩
      intro U hU
      rw [cutDist_comm]
      exact hfar U hU)
  obtain ⟨sigma, hsigma, U, hlimit⟩ := C.compact_subsequence f
  have hclose : ∀ᶠ n : ℕ in atTop, cutDist (f (sigma n)) U < epsilon / 2 :=
    hlimit.eventually (gt_mem_nhds (half_pos hepsilon))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hclose
  have hleft := hN N le_rfl
  have hright := hN (N + 1) (by omega)
  have hfar := hseparated (sigma N) (sigma (N + 1)) (hsigma (by omega))
  have htriangle := cutDist_triangle (f (sigma N)) U (f (sigma (N + 1)))
  rw [cutDist_comm U] at htriangle
  linarith

end DenseGraph
