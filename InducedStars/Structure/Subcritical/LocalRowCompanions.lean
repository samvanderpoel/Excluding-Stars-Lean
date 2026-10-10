import InducedStars.Structure.Subcritical.LocalNonlow
import InducedStars.Structure.Subcritical.ProfileRootEnergy
import InducedStars.Structure.Subcritical.DeterministicRows

/-!
# Realized component rows and trimming bounds

Paper: supporting finite bookkeeping for the proof of
`lemma:local-compensation-K1k`. Recorded high targets remain high after
the roots are removed, and external visible components consist of eligible
profile targets. These are inputs to the current full-density support deficit.
-/

noncomputable section
open Finset
open scoped Classical BigOperators

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}

def subcriticalComponentRows (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (i : Fin D.componentCount) : Finset D.PartIndex :=
  (subcriticalProfileRowIndices p v).filter fun a ↦ a.1 = i

@[simp] theorem mem_subcriticalComponentRows
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (i : Fin D.componentCount)
    (a : D.PartIndex) : a ∈ subcriticalComponentRows p v i ↔
      a ∈ subcriticalProfileRowIndices p v ∧ a.1 = i := by
  simp only [subcriticalComponentRows, Finset.mem_filter]

theorem RealizesSubcriticalProfile.rowCount_eq_degree_of_mem
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) {v : V} {a : D.PartIndex}
    (ha : a ∈ subcriticalProfileRowIndices p v) :
    p.rowCount v a = degreeInFinset G v (D.part a \ p.roots) := by
  cases he : p.rows v a with
  | none => simp [subcriticalProfileRowIndices, he] at ha
  | some r =>
    simpa only [SubcriticalProfile.rowCount, he, Option.getD_some] using
      h.row_count_eq_degree_of_some he

/-- Exact deletion bookkeeping, charging only vertices actually in the
target. This permits the half-target reserve in both high/medium adapters. -/
theorem subcriticalDegree_le_trimmed_add_inter (G : SimpleGraph V) (v : V)
    (Y B : Finset V) :
    degreeInFinset G v Y ≤ degreeInFinset G v (Y \ B) + (Y ∩ B).card := by
  have h := subcriticalDegree_le_sdiff_add_card G v Y (Y ∩ B)
  have he : Y \ (Y ∩ B) = Y \ B := by ext x; simp
  simpa only [he] using h

theorem subcriticalFullHigh_implies_trimmedHigh
    (G : SimpleGraph V) (v : V) (Y B : Finset V) (ha : 0 ≤ alpha)
    (htrim : 2 * (B.card : ℝ) ≤ Y.card)
    (hhigh : (1 - alpha) * Y.card ≤ (degreeInFinset G v Y : ℝ)) :
    (1 - 2 * alpha) * (Y \ B).card ≤ (degreeInFinset G v (Y \ B) : ℝ) := by
  have hd : (degreeInFinset G v Y : ℝ) ≤
      degreeInFinset G v (Y \ B) + (Y ∩ B).card := by
    exact_mod_cast subcriticalDegree_le_trimmed_add_inter G v Y B
  have hi : ((Y ∩ B).card : ℝ) ≤ B.card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : Y ∩ B ⊆ B)
  have he : ((Y \ B).card : ℝ) + (Y ∩ B).card = Y.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter Y B
  nlinarith

theorem RealizesSubcriticalProfile.recorded_row_full_lower
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) {v : V} {a : D.PartIndex}
    (ha : a ∈ subcriticalProfileRowIndices p v) :
    4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ) := by
  cases he : p.rows v a with
  | none => simp [subcriticalProfileRowIndices, he] at ha
  | some r =>
    rcases (p.rows_valid v a r he).1 with hv | hv
    · exact ((h.retained_row_iff v hv.1 a).mp ha).2
    · exact ((h.outside_row_iff v hv.1 a).mp ha).2

theorem RealizesSubcriticalProfile.recorded_row_visible
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {v : V} {a : D.PartIndex} (ha : a ∈ subcriticalProfileRowIndices p v) :
    a ∈ D.visiblePartIndices theta := by
  cases he : p.rows v a with
  | none => simp [subcriticalProfileRowIndices, he] at ha
  | some r =>
    rcases (p.rows_valid v a r he).1 with hv | hv
    · exact ((D.mem_eligibleVisibleTargets eta R₀ theta v
        (p.retainedRoots_subset hv.1) a).mp ((h.retained_row_iff v hv.1 a).mp ha).1).1
    · exact hret hv.2

theorem RealizesSubcriticalProfile.high_allowed_recorded
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) {v : V} {a : D.PartIndex}
    (halpha : 0 ≤ alpha) (halphaFifth : 5 * alpha ≤ 1)
    (htrim : 2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (hallowed : (v ∈ p.retainedRoots ∧ D.EligibleProfileTarget eta R₀ theta v a) ∨
      (v ∈ p.outsideRoots ∧ a ∈ D.retainedPartIndices eta R₀))
    (hhigh : (1 - alpha) * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)) :
    a ∈ subcriticalProfileRowIndices p v ∧
      (1 - 2 * alpha) * (D.part a \ p.roots).card ≤ (p.rowCount v a : ℝ) := by
  have hfour : 4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right halphaFifth (Nat.cast_nonneg (D.part a).card)
    nlinarith
  have ha : a ∈ subcriticalProfileRowIndices p v := by
    rcases hallowed with ⟨hv, ⟨hvr, ha⟩⟩ | ⟨hv, ha⟩
    · exact (h.retained_row_iff v hv a).mpr ⟨ha, hfour⟩
    · exact (h.outside_row_iff v hv a).mpr ⟨ha, hfour⟩
  refine ⟨ha, ?_⟩
  rw [h.rowCount_eq_degree_of_mem ha]
  exact subcriticalFullHigh_implies_trimmedHigh G v (D.part a) p.roots halpha htrim hhigh

section Finite
variable {n : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
  {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
  {omega eta theta alpha delta epsilon : ℝ} {R₀ : ℕ}

theorem subcriticalExternalComponent_targets_allowed
    (p : SubcriticalProfile D eta R₀ theta) (v : Fin n) (hv : v ∈ p.retainedRoots)
    (i : Fin D.componentCount) (hi : i ∈ D.visibleComponentIndices theta)
    (hio : i ≠ (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1)
    (a : D.PartIndex) (hai : a.1 = i) :
    (v ∈ p.retainedRoots ∧ D.EligibleProfileTarget eta R₀ theta v a) ∨
      (v ∈ p.outsideRoots ∧ a ∈ D.retainedPartIndices eta R₀) := by
  refine Or.inl ⟨hv, p.retainedRoots_subset hv, ?_⟩
  apply (D.mem_eligibleVisibleTargets eta R₀ theta v (p.retainedRoots_subset hv) a).mpr
  refine ⟨(D.mem_visiblePartIndices theta a).mpr (hai ▸ hi), ?_, ?_⟩
  · intro he
    exact hio (hai.symm.trans (congrArg Sigma.fst he))
  · intro ha
    exact hio (hai.symm.trans (SubcriticalDivision.activePart_same_component ha).symm)

end Finite
end InducedStars
