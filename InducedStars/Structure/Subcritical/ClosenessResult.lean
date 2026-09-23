import InducedStars.Structure.Subcritical.CompatibilityAlignment
import InducedStars.Structure.Subcritical.AlignmentConsequences
import InducedStars.Structure.Subcritical.ClosenessParameters
import InducedStars.Structure.Subcritical.Defect

/-!
# The finite subcritical close-structure result

This module collects the five conclusions of the subcritical cut-to-division
bridge while retaining the single permutation and component alignment from
which they are derived.  The constructor below is entirely finite: its
inputs are one explicit alignment witness, its labeled-cut estimate, and the
rounding inequalities supplied by the uniform setup.
-/

noncomputable section

open Finset Set DenseGraph DenseGraph.FiniteWeightedGraph
open scoped BigOperators Classical

namespace InducedStars

universe u

/-- The transparent output of the finite subcritical close-structure bridge.

The first four fields retain the common numerical package, relabeling, and
cell alignment.  The final five fields are precisely the small-edit,
compatibility, bounded-order balance, visible balance, and visible-density
conclusions used in the paper. -/
structure SubcriticalCloseStructureResult
    {k n : ℕ} (hk : 3 ≤ k)
    (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n))
    (L : AdmissibleBlockSequence k) (R₀ : ℕ)
    (omega eta theta alpha delta epsilon : ℝ) where
  parameters :
    SubcriticalClosenessParameters k R₀ omega eta theta alpha delta epsilon
  pi : Equiv.Perm (Fin n)
  alignment : SubcriticalComponentAlignment D L pi parameters.t
    (parameters.zeta * n) parameters.B
  reference_cut :
    finiteLabeledCutDist (ofSimpleGraph G)
      ((subcriticalReferenceWeightedGraph hk L n).permute pi) ≤ parameters.beta

  defect_cost_le :
    (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ) ^ 2
  compatibility : D.CandidateCompatibility L eta delta R₀
  bounded_order_balance : ∀ (i : Fin D.componentCount),
    (D.core i).order ≤ R₀ →
    eta * n / (4 * (R₀ : ℝ)) ≤ (D.componentSupport i).card →
    ∀ u : Fin (D.core i).order,
      |((D.parts i u).card : ℝ) -
          (D.componentSupport i).card / (D.core i).order| ≤
          min alpha (omega / (4 * (D.core i).order)) *
            (D.componentSupport i).card ∧
        (D.componentSupport i).card / (2 * (R₀ : ℝ)) ≤
          (D.parts i u).card
  visible_component_ratio : ∀ (i : Fin D.componentCount),
    i ∈ D.visibleComponentIndices theta →
    ∀ u v : Fin (D.core i).order,
      ((D.parts i u).card : ℝ) ≤ (1 + omega) * (D.parts i v).card
  visible_subset_density :
    ∀ (a b : {a : D.PartIndex // a ∈ D.visiblePartIndices theta})
      (X Y : Finset (Fin n)),
      Disjoint X Y → X ⊆ D.part a.val → Y ⊆ D.part b.val →
      alpha * theta * n / 4 ≤ (X.card : ℝ) →
      alpha * theta * n / 4 ≤ (Y.card : ℝ) →
      |Regularity.graphDensity G X Y -
          subcriticalDivisionPartWeight D a.val b.val| ≤ delta

namespace SubcriticalCloseStructureResult

variable {k n R₀ : ℕ} {hk : 3 ≤ k}
  {G : SimpleGraph (Fin n)} {D : SubcriticalDivision k (Fin n)}
  {L : AdmissibleBlockSequence k}
  {omega eta theta alpha delta epsilon : ℝ}

/-- The cell-loss scale retained by a close-structure result. -/
abbrev alignmentError
    (R : SubcriticalCloseStructureResult hk G D L R₀
      omega eta theta alpha delta epsilon) : ℝ :=
  R.parameters.alignmentError

private theorem zeta_mul_n_le_alignmentError_mul_n
    (R : SubcriticalCloseStructureResult hk G D L R₀
      omega eta theta alpha delta epsilon) :
    R.parameters.zeta * n ≤ R.alignmentError * n := by
  have hcoeff : (1 : ℝ) ≤ (((R.parameters.B + 3 : ℕ) : ℝ)) := by
    exact_mod_cast (show 1 ≤ R.parameters.B + 3 by omega)
  have hz : 0 ≤ R.parameters.zeta * (n : ℝ) :=
    mul_nonneg R.parameters.zeta_pos.le (Nat.cast_nonneg n)
  have h := mul_le_mul_of_nonneg_right hcoeff hz
  simpa only [one_mul, alignmentError,
    SubcriticalClosenessParameters.alignmentError, mul_assoc] using h

/-- Quantitative `cor:cut-closeness` on any finite injected family of
visible parts.  The comparison is on the same restricted vertex set and
uses the single reference permutation retained in the result. -/
theorem visibleSetCutCloseness
    (R : SubcriticalCloseStructureResult hk G D L R₀
      omega eta theta alpha delta epsilon)
    (halpha : 0 < alpha) (htheta : 0 < theta)
    {I : Type u} [Fintype I] [DecidableEq I]
    (partIndex : I ↪ {a : D.PartIndex // a ∈ D.visiblePartIndices theta})
    (part : I → Finset (Fin n))
    (hpart : ∀ q, part q ⊆ D.part (partIndex q).val)
    (hsize : ∀ q, alpha * theta * n / 4 ≤ ((part q).card : ℝ)) :
    finiteLabeledCutDist
        ((ofSimpleGraph G).restrictToFinset (visibleCutPartUnion part))
        ((subcriticalDivisionWeightedGraph hk D).restrictToFinset
          (visibleCutPartUnion part)) ≤ delta := by
  have ha0 : 0 < alpha * theta / 4 := by positivity
  have hmain := R.alignment.selectedVisibleParts_restrictedLabeledCutDist_le
    hk G R.parameters.t_le_theta R.parameters.beta_pos.le
      R.parameters.alignmentError_pos.le ha0
      R.zeta_mul_n_le_alignmentError_mul_n R.reference_cut
      partIndex part hpart (by
        intro q
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsize q)
  exact hmain.trans R.parameters.density_reserve

end SubcriticalCloseStructureResult

/-! ## Finite construction from one actual alignment -/

set_option maxHeartbeats 800000 in
/-- Assemble all five bridge conclusions from one explicitly constructed
component alignment.  This theorem has no graphon or asymptotic input. -/
def subcriticalCloseStructureResult_of_alignment
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n))
    (L : AdmissibleBlockSequence k) (R₀ : ℕ)
    (omega eta theta alpha delta epsilon : ℝ) (hR₀ : 1 ≤ R₀)
    (homega : 0 < omega) (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha)
    (P : SubcriticalClosenessParameters
      k R₀ omega eta theta alpha delta epsilon)
    (pi : Equiv.Perm (Fin n))
    (A : SubcriticalComponentAlignment D L pi P.t (P.zeta * n) P.B)
    (hdefect : (subcriticalDefectCost G D : ℝ) ≤
      P.epsilonWork * (n : ℝ) ^ 2)
    (hcut : finiteLabeledCutDist (ofSimpleGraph G)
      ((subcriticalReferenceWeightedGraph hk L n).permute pi) ≤ P.beta)
    (hround : 4 ≤ P.t * n / 4)
    (hdiag : 2 ≤ subcriticalPaletteGap k * (P.zeta * n)) :
    SubcriticalCloseStructureResult hk G D L R₀
      omega eta theta alpha delta epsilon := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let err := P.alignmentError
  have herrPos : 0 < err := by
    dsimp [err]
    exact P.alignmentError_pos
  have hmPos : 0 < P.zeta * (n : ℝ) := mul_pos P.zeta_pos hnR
  have hgapLe : subcriticalPaletteGap k ≤ 1 :=
    (min_le_left (pK k) (1 - pK k)).trans (pK_mem_Icc k).2
  have htwo : 2 ≤ P.zeta * (n : ℝ) := by
    calc
      2 ≤ subcriticalPaletteGap k * (P.zeta * n) := hdiag
      _ ≤ 1 * (P.zeta * n) :=
        mul_le_mul_of_nonneg_right hgapLe hmPos.le
      _ = _ := one_mul _
  have herror : ((P.B : ℝ) + 2) * (P.zeta * n) + 2 ≤ err * n := by
    dsimp [err, SubcriticalClosenessParameters.alignmentError]
    push_cast
    nlinarith
  have hmError : P.zeta * n ≤ err * n := by
    have hcoeff : (1 : ℝ) ≤ (((P.B + 3 : ℕ) : ℝ)) := by
      exact_mod_cast (show 1 ≤ P.B + 3 by omega)
    have h := mul_le_mul_of_nonneg_right hcoeff hmPos.le
    simpa only [one_mul, err,
      SubcriticalClosenessParameters.alignmentError, mul_assoc] using h
  have hcompat : D.CandidateCompatibility L eta delta R₀ :=
    A.toCandidateCompatibility hn P.t_pos heta hR₀ P.t_le_eta hround
      hmPos herror P.component_delta_reserve P.component_eta_reserve
  refine
    { parameters := P
      pi := pi
      alignment := A
      reference_cut := hcut
      defect_cost_le := ?_
      compatibility := hcompat
      bounded_order_balance := ?_
      visible_component_ratio := ?_
      visible_subset_density := ?_ }
  · exact hdefect.trans
      (mul_le_mul_of_nonneg_right P.epsilonWork_le (sq_nonneg (n : ℝ)))
  · intro i horder hlarge u
    have hvis : i ∈ D.visibleComponentIndices P.t := by
      apply subcritical_smallOrder_large_component_visible D i P.t_pos.le
        hR₀ P.t_le_eta horder
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlarge
    let ii : {i : Fin D.componentCount //
        i ∈ D.visibleComponentIndices P.t} := ⟨i, hvis⟩
    let z : ℝ := L.alpha (A.assignment ii).val * n / (D.core i).order
    have hparts : ∀ v : Fin (D.core i).order,
        |((D.parts i v).card : ℝ) - z| ≤ err * n := by
      intro v
      simpa only [ii, z] using A.part_size_error_le hn herror ii v
    apply subcritical_bounded_order_balance_of_part_errors D i
      halpha.le homega.le horder
      (lambda := eta / (4 * (R₀ : ℝ)))
      (z := z) (err := err)
    · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlarge
    · exact P.bounded_balance_reserve
    · exact P.bounded_lower_reserve
    · exact hparts
  · intro i hi u v
    have hiLower : i ∈ D.visibleComponentIndices P.t :=
      D.visibleComponentIndices_mono P.t_le_theta hi
    let ii : {i : Fin D.componentCount //
        i ∈ D.visibleComponentIndices P.t} := ⟨i, hiLower⟩
    let z : ℝ := L.alpha (A.assignment ii).val * n / (D.core i).order
    have hparts : ∀ w : Fin (D.core i).order,
        |((D.parts i w).card : ℝ) - z| ≤ err * n := by
      intro w
      simpa only [ii, z] using A.part_size_error_le hn herror ii w
    have hsmall : err ≤ theta / 4 := by
      calc
        err ≤ P.t / 8 := P.alignmentError_le_t_div_eight
        _ ≤ theta / 4 := by linarith [P.t_le_theta, P.t_pos]
    have hvis : ∃ w, theta * (n : ℝ) ≤ ((D.parts i w).card : ℝ) := by
      simpa only [Fintype.card_fin] using
        (D.mem_visibleComponentIndices theta i).mp hi
    exact subcritical_visible_ratio_of_part_errors D i homega.le hsmall
      P.visible_ratio_reserve hparts hvis u v
  · intro a b X Y hXY hX hY hXsize hYsize
    have hmain := A.abs_graphDensity_sub_partWeight_le hk hn G
      P.t_le_theta htheta halpha P.beta_pos.le herrPos.le hmError hcut
      a b X Y hXY hX hY hXsize hYsize
    exact hmain.trans P.density_reserve

end InducedStars
