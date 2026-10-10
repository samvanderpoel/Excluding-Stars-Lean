import InducedStars.Structure.Subcritical.RetainedMassParameters
import InducedStars.Graphon.SupercriticalClassification

/-!
# Uniform near-equality structure for retained quadratic mass

Small omitted normalized mass is retained throughout. Only the
other retained blocks are claimed to have small total length.
-/

noncomputable section
open Set
namespace InducedStars

/-- Near equality in the retained length lower bound identifies a positive
complete-core block with explicit length error. The tolerance is independent
of the candidate and the finite division. -/
theorem subcriticalRetainedMass_nearEquality_complete
    {k : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    {eta mu t : ℝ} {R₀ : ℕ}
    (heta : 0 < eta) (hmu : 0 < mu) (ht : 0 < t)
    (hmass : L.mass = mu ^ 2 / (k - 1 : ℕ))
    (hetaSmall : eta ≤ t / 4) (hR : Nat.ceil (2 / t) ≤ R₀)
    (hsmall : (k - 1 : ℕ) * t < mu ^ 2)
    (hgap : subcriticalRetainedMassOrderBound k mu t < mu ^ 2 / (k - 1 : ℕ))
    (hlength : subcriticalRetainedBlockLength L eta R₀ ≤ mu + t) :
    ∃ j : ℕ, 0 < L.alpha j ∧ L.core j = RegularBlockCore.complete k hk ∧
      |L.alpha j - mu| ≤ subcriticalRetainedMassLengthError k mu t := by
  have homit := subcriticalOmittedBlockMass_le_tolerance L heta ht hetaSmall hR
  obtain ⟨j, hj, _, herr, hothers⟩ := subcriticalRetainedMass_dominant hk L
    hmu ht.le ht.le hmass homit hsmall hlength
  have hupper : L.alpha j ≤ mu + t := by
    exact (Finset.single_le_sum (fun i _ ↦ L.alpha_nonneg i) hj).trans hlength
  have horder := subcriticalRetainedDominantCore_order_eq hk L hmu ht.le ht.le
    hj hmass homit hupper hothers hgap
  refine ⟨j, ?_, RegularBlockCore.eq_complete_of_order_eq_k_sub_one _ hk horder, herr⟩
  have hjlength := ((mem_subcriticalMassRetainedBlockIndices L heta R₀ j).mp hj).1
  linarith

/-- For a complete distinguished block, the discarded normalized mass is
controlled by its length error, not by discarded total vertex length. -/
theorem subcriticalMass_sub_completeBlock_le
    {k : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    {mu B : ℝ} {j : ℕ} (hmu : 0 ≤ mu) (hmuOne : mu ≤ 1)
    (hB : 0 ≤ B) (hmass : L.mass = mu ^ 2 / (k - 1 : ℕ))
    (hcore : L.core j = RegularBlockCore.complete k hk)
    (herr : |L.alpha j - mu| ≤ B) :
    L.mass - L.massTerm j ≤ 2 * B / (k - 1 : ℕ) := by
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hterm : L.massTerm j = L.alpha j ^ 2 / (k - 1 : ℕ) := by
    simp only [AdmissibleBlockSequence.massTerm, hcore, RegularBlockCore.complete]
  rw [hmass, hterm, ← sub_div]
  apply div_le_div_of_nonneg_right _ hr.le
  have ha0 := L.alpha_nonneg j
  have ha1 := L.alpha_le_one j
  have habs := (abs_le.mp herr).1
  by_cases hle : mu ≤ L.alpha j
  · nlinarith
  · have hdiff : 0 ≤ mu - L.alpha j := by linarith
    have hsum : mu + L.alpha j ≤ 2 := by linarith
    have hprod := mul_le_mul_of_nonneg_left hsum hdiff
    nlinarith

/-- The natural edge-mass coefficient is at most k-1. -/
theorem subcriticalEdgeMassCoefficient_le {k : ℕ} (hk : 3 ≤ k) :
    1 + (k - 2 : ℕ) * pK k ≤ (k - 1 : ℕ) := by
  have hp := (pK_mem_Ioo (show 2 ≤ k by omega)).2.le
  have hn : (k - 2 : ℕ) + 1 = k - 1 := by omega
  have h := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (k - 2))
  have hnR : ((k - 2 : ℕ) : ℝ) + 1 = (k - 1 : ℕ) := by exact_mod_cast hn
  nlinarith

/-- Numeric graphon-alignment budget after the near-equality step. -/
theorem subcriticalCompleteBlock_alignmentBudget_le
    {k : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    {mu B : ℝ} {j : ℕ} (hmu : 0 ≤ mu) (hmuOne : mu ≤ 1)
    (hB : 0 ≤ B) (hmass : L.mass = mu ^ 2 / (k - 1 : ℕ))
    (hcore : L.core j = RegularBlockCore.complete k hk)
    (herr : |L.alpha j - mu| ≤ B) :
    (1 + (k - 2 : ℕ) * pK k) * (L.mass - L.massTerm j) +
      4 * (k - 1 : ℕ) * |L.alpha j - mu| ≤ (4 * (k - 1 : ℕ) + 2) * B := by
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hc0 : 0 ≤ 1 + (k - 2 : ℕ) * pK k := by
    have hp := (pK_mem_Ioo (show 2 ≤ k by omega)).1.le
    positivity
  have hmassBound := subcriticalMass_sub_completeBlock_le hk L hmu hmuOne hB hmass hcore herr
  have h1 := mul_le_mul_of_nonneg_left hmassBound hc0
  have h2 := mul_le_mul_of_nonneg_right (subcriticalEdgeMassCoefficient_le hk)
    (by positivity : 0 ≤ 2 * B / (k - 1 : ℕ))
  have hcancel : (k - 1 : ℕ) * (2 * B / (k - 1 : ℕ)) = 2 * B := by
    field_simp
  have h3 := mul_le_mul_of_nonneg_left herr (by positivity : 0 ≤ (4 : ℝ) * (k - 1 : ℕ))
  rw [hcancel] at h2
  nlinarith

end InducedStars
