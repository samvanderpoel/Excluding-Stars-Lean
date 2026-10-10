import InducedStars.Structure.Subcritical.ResidualStarCandidates
import DenseGraph.FiniteModels.DefectFreeSelections

/-!
# Abundance of actual endpoint-clean residual selections

Each fixed matching edge has `k-1` free roles.  Cleaning its two endpoints
uses their actual defect degrees, and a second union bound removes defects
between free vertices.  The surviving candidate rate depends only on the
retained-part scale, not on the later defect parameters.
-/

noncomputable section

open Finset
open scoped Classical BigOperators

namespace InducedStars

/-- Candidate rate after endpoint cleaning and free-pair exclusion. -/
def subcriticalResidualCandidateRate (k : ℕ) (lambda : ℝ) : ℝ :=
  (lambda / 2) ^ (k - 1) / 2

theorem subcriticalResidualCandidateRate_pos (k : ℕ) {lambda : ℝ}
    (hlambda : 0 < lambda) : 0 < subcriticalResidualCandidateRate k lambda := by
  unfold subcriticalResidualCandidateRate
  positivity

/-- The full selection space gives the sharp upper bound of `n^(k-1)` per
matching edge, irrespective of all cleaning conditions. -/
theorem subcriticalResidualCleanSelectionFiber_card_upper
    {Role : Type*} [Fintype Role] [DecidableEq Role] {k n : ℕ}
    (hroles : Fintype.card Role = k - 1)
    (R : SimpleGraph (Fin n)) (x y : Fin n) (S : Role → Finset (Fin n)) :
    (DenseGraph.defectFreeSelections
      (fun r ↦ DenseGraph.endpointCleanTarget R x y (S r)) R).card ≤ n ^ (k - 1) := by
  calc
    _ ≤ Fintype.card (Role → Fin n) := Finset.card_le_univ _
    _ = _ := by simp [hroles]

/-- Quantitative abundance for the actual endpoint-clean fiber.  In
particular, the adjacency status of the matching edge itself is unrestricted.
Only additional defects are excluded. -/
theorem subcriticalResidualCleanSelectionFiber_card_lower
    {Role : Type*} [Fintype Role] [DecidableEq Role] {k n : ℕ}
    (hroles : Fintype.card Role = k - 1)
    (R : SimpleGraph (Fin n)) (x y : Fin n) (S : Role → Finset (Fin n))
    {lambda defectRate : ℝ} (hlambda : 0 ≤ lambda) (hdefect : 0 ≤ defectRate)
    (hsize : ∀ r, lambda * n ≤ ((S r).card : ℝ))
    (hdegree : ∀ v, (R.degree v : ℝ) ≤ defectRate * n)
    (hendpoint : 2 * defectRate ≤ lambda / 2)
    (hfree : ((k - 1 : ℕ) : ℝ) ^ 2 * defectRate ≤
      (lambda / 2) ^ (k - 1) / 2) :
    subcriticalResidualCandidateRate k lambda * (n : ℝ) ^ (k - 1) ≤
      ((DenseGraph.defectFreeSelections
        (fun r ↦ DenseGraph.endpointCleanTarget R x y (S r)) R).card : ℝ) := by
  have htarget (r : Role) : lambda / 2 * n ≤
      ((DenseGraph.endpointCleanTarget R x y (S r)).card : ℝ) := by
    have h := DenseGraph.endpointCleanTarget_card_lower_of_degree R x y (S r)
      (by simpa using hdegree x) (by simpa using hdegree y)
    have hs := hsize r
    have he := mul_le_mul_of_nonneg_right hendpoint (Nat.cast_nonneg n)
    simp only [Fintype.card_fin] at h
    linarith
  have hcount := DenseGraph.defectFreeSelections_card_lower_half
    (fun r ↦ DenseGraph.endpointCleanTarget R x y (S r)) R
    (lambda := lambda / 2) (D := defectRate)
    (div_nonneg hlambda (by norm_num)) hdefect
    (by simpa using htarget) (by simpa using hdegree) (by simpa [hroles] using hfree)
  rw [Fintype.card_fin, hroles] at hcount
  calc
    subcriticalResidualCandidateRate k lambda * (n : ℝ) ^ (k - 1) =
        (lambda / 2 * (n : ℝ)) ^ (k - 1) / 2 := by
      rw [mul_pow]
      unfold subcriticalResidualCandidateRate
      ring
    _ ≤ _ := hcount

namespace SubcriticalHomogeneousResidualMatching

variable {k n R₀ : ℕ} {D : SubcriticalDivision k (Fin n)} {eta : ℝ}
  {R : SimpleGraph (Fin n)} {B : Finset (Fin n)}
  (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)

/-- The actual finite residual-star family: an anchor in the selected
homogeneous matching and an endpoint-clean, free-pair-clean selection. -/
abbrev Candidate := Σ e : M.Edge, M.Selection e

theorem candidateSelections_card_upper (hk : 3 ≤ k) (e : M.Edge) :
    (M.candidateSelections e).card ≤ n ^ (k - 1) :=
  subcriticalResidualCleanSelectionFiber_card_upper
    (card_subcriticalResidualFreeRole hk M.placement.leftPart)
    R (M.firstEndpoint e) (M.secondEndpoint e) M.freeTarget

/-- Every tuple chooses exactly `k-1` free vertices after its matching anchor. -/
theorem candidate_card_upper (hk : 3 ≤ k) :
    Fintype.card M.Candidate ≤ M.edges.card * n ^ (k - 1) := by
  calc
    _ = ∑ e : M.Edge, (M.candidateSelections e).card := by
      simp [Candidate, Selection]
    _ ≤ ∑ _e : M.Edge, n ^ (k - 1) :=
      Finset.sum_le_sum fun e _ ↦ M.candidateSelections_card_upper hk e
    _ = _ := by simp [Edge]

/-- Actual retained free targets have uniform room after removing roots and
all selected matching endpoints. -/
theorem freeTarget_card_lower
    (heta : 0 < eta) (hR : 1 ≤ R₀)
    (hpart : ∀ a ∈ D.retainedPartIndices eta R₀,
      eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ))
    (hB : (B.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 2)
    (hsmall : (M.edges.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 8)
    (r : M.FreeRole) :
    subcriticalResidualMatchingLambda eta R₀ * n ≤ ((M.freeTarget r).card : ℝ) :=
  subcriticalResidualMatching_part_room M heta hR hpart hB hsmall
    (subcriticalResidualFreeParent M.placement.leftPart r)
    (subcriticalResidualFreeParent_retained _ M.placement.leftPart_mem_retained r)

/-- The per-anchor candidate abundance is proved from the actual clean
selection definition and the retained-part room estimate. -/
theorem candidateSelections_card_lower
    (hk : 3 ≤ k) (heta : 0 < eta) (hR : 1 ≤ R₀)
    (hpart : ∀ a ∈ D.retainedPartIndices eta R₀,
      eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ))
    (hB : (B.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 2)
    (hsmall : (M.edges.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 8)
    {defectRate : ℝ} (hdefect : 0 ≤ defectRate)
    (hdegree : ∀ v, (R.degree v : ℝ) ≤ defectRate * n)
    (hendpoint : 2 * defectRate ≤ subcriticalResidualMatchingLambda eta R₀ / 2)
    (hfree : ((k - 1 : ℕ) : ℝ) ^ 2 * defectRate ≤
      (subcriticalResidualMatchingLambda eta R₀ / 2) ^ (k - 1) / 2)
    (e : M.Edge) :
    subcriticalResidualCandidateRate k (subcriticalResidualMatchingLambda eta R₀) *
        (n : ℝ) ^ (k - 1) ≤ ((M.candidateSelections e).card : ℝ) :=
  subcriticalResidualCleanSelectionFiber_card_lower
    (card_subcriticalResidualFreeRole hk M.placement.leftPart)
    R (M.firstEndpoint e) (M.secondEndpoint e) M.freeTarget
    (subcriticalResidualMatchingLambda_pos heta hR).le hdefect
    (M.freeTarget_card_lower heta hR hpart hB hsmall) hdegree hendpoint hfree

/-- Summing the proved fiber lower bound gives the actual candidate abundance.
The constant is fixed by `k,eta,R₀`, before any defect parameter is chosen. -/
theorem candidate_card_lower
    (hk : 3 ≤ k) (heta : 0 < eta) (hR : 1 ≤ R₀)
    (hpart : ∀ a ∈ D.retainedPartIndices eta R₀,
      eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ))
    (hB : (B.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 2)
    (hsmall : (M.edges.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 8)
    {defectRate : ℝ} (hdefect : 0 ≤ defectRate)
    (hdegree : ∀ v, (R.degree v : ℝ) ≤ defectRate * n)
    (hendpoint : 2 * defectRate ≤ subcriticalResidualMatchingLambda eta R₀ / 2)
    (hfree : ((k - 1 : ℕ) : ℝ) ^ 2 * defectRate ≤
      (subcriticalResidualMatchingLambda eta R₀ / 2) ^ (k - 1) / 2) :
    subcriticalResidualCandidateRate k (subcriticalResidualMatchingLambda eta R₀) *
        (M.edges.card : ℝ) * (n : ℝ) ^ (k - 1) ≤ (Fintype.card M.Candidate : ℝ) := by
  have hsum := Finset.sum_le_sum fun e (_ : e ∈ (Finset.univ : Finset M.Edge)) ↦
    M.candidateSelections_card_lower hk heta hR hpart hB hsmall hdefect hdegree hendpoint hfree e
  simpa [Candidate, Selection, Edge, Nat.cast_sum, mul_assoc, mul_left_comm, mul_comm] using hsum

end SubcriticalHomogeneousResidualMatching

end InducedStars
