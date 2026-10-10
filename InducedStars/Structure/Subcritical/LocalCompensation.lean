import InducedStars.Structure.Subcritical.UnifiedRootPenalty
import InducedStars.Structure.Subcritical.OutsideRootPenalty
import InducedStars.Structure.Subcritical.LocalPenaltyParameters

/-!
# Common local compensation for every profile root

The compensation proof uses the high/medium target deficit and its
zero-deficit placement comparison, followed by the sparse support budget
for roots outside the retained set.
-/

noncomputable section
open Finset
open scoped Classical
namespace InducedStars

variable {k n R₀ : ℕ} {D : SubcriticalDivision k (Fin n)}
  {eta theta : ℝ}

section Geometry
variable {G : SimpleGraph (Fin n)} {L : AdmissibleBlockSequence k}
  {omega alpha delta epsilon : ℝ}

/-- Unified retained-root compensation and component compensation outside
the retained set, derived from one common scalar parameter package. -/
theorem subcriticalLocalCompensation_retained_outside_of_geometry
    (hk : 3 ≤ k)
    (P : SubcriticalLocalPenaltyParameters k R₀ eta theta alpha delta epsilon n)
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (homega : omega ≤ 1)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hminimal : ∀ E : SubcriticalDivision k (Fin n),
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    {p : SubcriticalProfile D eta R₀ theta} (hp : RealizesSubcriticalProfile G alpha p)
    (hB : (p.roots.card : ℝ) ≤ subcriticalProfileRootFraction alpha theta epsilon * n)
    (m : ℕ) (C : ℝ) :
    (∀ v ∈ p.retainedRoots, subcriticalProfileLocalExponent p m C alpha delta epsilon v ≤
      -(subcriticalLocalPenaltyUnit k * eta * n / (R₀ : ℝ))) ∧
    (∀ v ∈ p.outsideRoots, subcriticalProfileLocalExponent p m C alpha delta epsilon v ≤
      -(subcriticalLocalPenaltyUnit k * eta * n / (R₀ : ℝ))) := by
  have hret := D.retainedPartIndices_subset_visiblePartIndices P.retained_order
    P.theta_pos.le P.retained_visible
  have hRpos : (0 : ℝ) < R₀ := by exact_mod_cast (show 0 < R₀ by have := P.retained_order; omega)
  have hA := subcriticalLocalA_Nat_pos hk
  have hretained (v : Fin n) (hv : v ∈ p.retainedRoots) :=
    subcriticalRetainedRootUnifiedPenalty R hfree homega P.alpha_pos
      (by linarith [P.alpha_small]) P.relocation_alpha P.theta_pos P.delta_nonneg
      P.row_counting (by linarith [P.density_lower, P.delta_nonneg])
      (by linarith [P.density_upper, P.delta_nonneg]) P.order_pos P.row_scale
      P.root_fraction_nonneg P.retained_order P.eta_pos hret hp hB
      (P.roots_add_one_le_part R homega hB) P.trim_lt_one P.entropy_band P.tail_band
      P.zero_probability_reserve P.total_error hminimal v hv
      (R.retainedPart_card_two_le P.retained_order P.eta_pos.le
        (D.retainedVertexPart_mem_retained eta R₀ v (p.retainedRoots_subset hv)) P.source_scale)
      (by
        intro b hb
        let a := D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)
        have hvis := (D.mem_visiblePartIndices theta a).mp
          (hret (D.retainedVertexPart_mem_retained eta R₀ v (p.retainedRoots_subset hv)))
        rcases b with ⟨i, b⟩
        change i = a.1 at hb
        subst i
        exact (R.visible_component_ratio a.1 hvis b a.2).trans
          (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))) m C
  have hconvert (v : Fin n) (hv : v ∈ p.retainedRoots) :
      -(subcriticalLocalA_Nat k / 2) *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card ≤
          -(subcriticalLocalPenaltyUnit k * eta * n / (R₀ : ℝ)) := by
    have hs := R.retainedPart_card_lower_bound P.retained_order P.eta_pos.le
      (D.retainedVertexPart_mem_retained eta R₀ v (p.retainedRoots_subset hv))
    have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ subcriticalLocalA_Nat k / 2 by positivity)
    have heq : subcriticalLocalA_Nat k / 2 * (eta * n / (2 * (R₀ : ℝ))) =
        subcriticalLocalA_Nat k * eta * n / (4 * (R₀ : ℝ)) := by ring
    rw [heq] at h
    have hz : 0 ≤ subcriticalLocalA_Nat k * eta * n / (R₀ : ℝ) := by
      have := P.eta_pos; positivity
    unfold subcriticalLocalPenaltyUnit
    ring_nf at h hz ⊢
    nlinarith only [h, hz]
  refine ⟨?_, ?_⟩
  · intro v hv
    exact (hretained v hv).trans (hconvert v hv)
  · intro v hv
    have hdom := subcriticalTotalErrorNat_component_le (R₀ := R₀) hk P.eta_pos.le P.alpha_pos.le
      P.alpha_quarter P.delta_nonneg P.trim_nonneg P.trim_lt_one P.inside_error_nonneg
      P.entropy_band P.tail_band
    have herr := hdom.2.2.1.trans P.total_error
    have htrim : 4 * subcriticalProfileRootFraction alpha theta epsilon ≤ theta := by
      have h := P.root_fraction
      have ha := P.alpha_quarter
      have ht := P.theta_pos
      nlinarith
    have hout := subcriticalOutsideRootCompensation P.sparseRowParameters R hfree hminimal
      P.retained_order P.eta_pos.le homega P.delta_nonneg P.row_counting P.order_pos
      P.row_scale P.sparse_scale P.root_fraction_nonneg htrim hp hB
      (by
        dsimp [SubcriticalLocalPenaltyParameters.sparseRowParameters]
        linarith only [herr, hA]) m C v hv
    change subcriticalProfileLocalExponent p m C alpha delta epsilon v ≤ _ at hout
    have hz : 0 ≤ subcriticalLocalA_Nat k * eta * n / (R₀ : ℝ) := by
      have := P.eta_pos; positivity
    unfold subcriticalLocalPenaltyUnit
    ring_nf at hout hz ⊢
    nlinarith only [hout, hz]

/-- Paper: Lemma `lemma:local-compensation-K1k`. Retained roots use the
unified component deficit and its zero-deficit entropy loss; outside roots
use the strict sparse support budget. No matching input is used. -/
theorem subcriticalLocalCompensation_of_geometry
    (hk : 3 ≤ k)
    (P : SubcriticalLocalPenaltyParameters k R₀ eta theta alpha delta epsilon n)
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (homega : omega ≤ 1)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hminimal : ∀ E : SubcriticalDivision k (Fin n),
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    {p : SubcriticalProfile D eta R₀ theta} (hp : RealizesSubcriticalProfile G alpha p)
    (hB : (p.roots.card : ℝ) ≤ subcriticalProfileRootFraction alpha theta epsilon * n)
    (m : ℕ) (C : ℝ) (v : Fin n) (hv : v ∈ p.roots) :
    subcriticalProfileLocalExponent p m C alpha delta epsilon v ≤
      -(subcriticalLocalPenaltyUnit k * eta * n / (R₀ : ℝ)) := by
  obtain ⟨hr, ho⟩ := subcriticalLocalCompensation_retained_outside_of_geometry
    hk P R homega hfree hminimal hp hB m C
  rcases Finset.mem_union.mp hv with hv | hv
  · exact hr v hv
  · exact ho v hv

end Geometry
end InducedStars
