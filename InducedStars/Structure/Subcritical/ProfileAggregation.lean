import InducedStars.Structure.Subcritical.ProfilePenalty
import InducedStars.Structure.Subcritical.CleanFamilies
import InducedStars.Structure.Subcritical.ProfileEnumeration
import DenseGraph.Combinatorics.ProfileSums

/-!
# Summing the nonclean subcritical profile classes

Paper: Lemma `lemma:NtaunmWUpperBdK1k`, exceptional-family estimate.
The fixed polynomial prefactor is retained during summation and is
paid from the common positive-complexity penalty. This includes root-free
profiles of positive matching complexity. Every profile estimate uses the
same ambient family, and no positivity of the clean partition function is
required.
-/

noncomputable section
open Finset
open scoped BigOperators Classical

namespace InducedStars

/-- Deterministic covering by positive-complexity classes in the original
ambient family. No disjointness of profile classes is assumed. -/
theorem subcriticalNonclean_card_le_sum_profiles
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (SimpleGraph V)) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ) (ha : 0 < alpha) (haHalf : alpha < 1 / 2) :
    (subcriticalNoncleanDivisionGraphFinset F D eta R₀).card ≤
      ∑ r ∈ Finset.Icc 1 (2 * Fintype.card V),
        ∑ p ∈ subcriticalProfilesOfComplexity D eta R₀ theta r,
          (subcriticalProfileClassGraphFinset F alpha p).card := by
  have hcover : subcriticalNoncleanDivisionGraphFinset F D eta R₀ ⊆
      (Finset.Icc 1 (2 * Fintype.card V)).biUnion (fun r ↦
        (subcriticalProfilesOfComplexity D eta R₀ theta r).biUnion fun p ↦
          subcriticalProfileClassGraphFinset F alpha p) := by
    intro G hG
    obtain ⟨hGF, hnon⟩ := (mem_subcriticalNoncleanDivisionGraphFinset F G).mp hG
    obtain ⟨p, hp⟩ := subcriticalProfileCovering F D eta R₀ theta alpha ha haHalf G hGF
    have hrealizes := (mem_subcriticalProfileClassGraphFinset.mp hp).2
    apply Finset.mem_biUnion.mpr
    refine ⟨subcriticalProfileComplexity p,
      Finset.mem_Icc.mpr ⟨hrealizes.complexity_pos_of_nonclean ha hnon,
        subcriticalProfileComplexity_le p⟩, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨p, by simp, hp⟩
  calc
    _ ≤ _ := Finset.card_le_card hcover
    _ ≤ ∑ r ∈ Finset.Icc 1 (2 * Fintype.card V),
        ((subcriticalProfilesOfComplexity D eta R₀ theta r).biUnion fun p ↦
          subcriticalProfileClassGraphFinset F alpha p).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun _ _ ↦ Finset.card_biUnion_le

variable {k n R₀ m : ℕ} {gamma omega eta theta alpha delta epsilon : ℝ}
  {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}

/-- Paper: Lemma `lemma:NtaunmWUpperBdK1k`, the nonclean contribution.
The finite aggregation keeps the active-coordinate polynomial and
uses the uniform profile enumeration before absorbing it. All geometric
assumptions concern the actual original graphs. -/
theorem subcriticalNoncleanDivision_card_le
    (hk : 3 ≤ k) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (F : Finset (SimpleGraph (Fin n)))
    (P : SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n)
    (hetaOne : eta ≤ 1) (homega : omega ≤ 1)
    (hdensity : gamma / 8 * (n : ℝ) ^ 2 ≤ m)
    (A : SubcriticalAggregationGeometry hk F D L R₀ m omega eta theta alpha delta epsilon)
    (hpoly : ((n : ℝ) + 1) ^
        (2 * subcriticalProfileEnumerationConstant (subcriticalVisibleIndexBound theta) +
          6 * subcriticalActiveIndexBound eta R₀ + 2) ≤
      Real.exp (subcriticalAggregationConstant k eta R₀ * n)) :
    ((subcriticalNoncleanDivisionGraphFinset F D eta R₀).card : ℝ) ≤
      Real.exp (-subcriticalAggregationConstant k eta R₀ * n) *
        (cleanRetainedPartitionFunction D eta R₀ m delta : ℝ) := by
  by_cases hF : F.Nonempty
  swap
  · have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp only [hzero, subcriticalNoncleanDivisionGraphFinset, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨G₀, hG₀⟩ := hF
  let R := (A.close G₀ hG₀).some
  let c := subcriticalAggregationConstant k eta R₀
  let Qvis := subcriticalVisibleIndexBound theta
  let Qact := subcriticalActiveIndexBound eta R₀
  let Cprof := subcriticalProfileEnumerationConstant Qvis
  let Z : ℝ := cleanRetainedPartitionFunction D eta R₀ m delta
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hc : 0 < c := subcriticalAggregationConstant_pos hk
    P.localConditions.eta_pos P.localConditions.retained_order
  have hbase : (1 : ℝ) ≤ n + 1 := by exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hvisible : ∀ a ∈ D.visiblePartIndices theta,
      theta * Fintype.card (Fin n) / 2 ≤ ((D.part a).card : ℝ) := by
    intro a ha
    simpa only [Fintype.card_fin] using R.visible_part_card_ge_half homega a ha
  have hvis := subcriticalVisiblePartIndices_card_le D P.localConditions.theta_pos hvisible
  have hret := D.retainedPartIndices_subset_visiblePartIndices
    P.localConditions.retained_order P.localConditions.theta_pos.le
    P.localConditions.retained_visible
  have hact := subcriticalRetainedActivePair_card_le D R₀ P.localConditions.eta_pos
  have hpolyAct : (n : ℝ) ^ (6 * Fintype.card (RetainedActivePair D eta R₀)) ≤
      ((n : ℝ) + 1) ^ (6 * Qact) := by
    calc
      _ ≤ ((n : ℝ) + 1) ^ (6 * Fintype.card (RetainedActivePair D eta R₀)) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ hbase (Nat.mul_le_mul_left 6 hact)
  have hprofile (r : ℕ) (p : SubcriticalProfile D eta R₀ theta)
      (hp : p ∈ subcriticalProfilesOfComplexity D eta R₀ theta r) :
      ((subcriticalProfileClassGraphFinset F alpha p).card : ℝ) ≤
        ((n : ℝ) + 1) ^ (6 * Qact) * Z * Real.exp (-(32 * c) * r * n) := by
    have hcount := subcriticalProfilePenaltyCore hk J F p P hetaOne homega hdensity A
    have hr := (mem_subcriticalProfilesOfComplexity D eta R₀ theta r p).mp hp
    rw [hr] at hcount
    have hexp : Real.exp (-(48 * c) * r * n) ≤ Real.exp (-(32 * c) * r * n) := by
      apply Real.exp_le_exp.mpr
      nlinarith [show 0 ≤ c * r * n by positivity]
    exact hcount.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right hpolyAct hZ) hexp
      (Real.exp_pos _).le (by positivity))
  have hlevel (r : ℕ) :
      (∑ p ∈ subcriticalProfilesOfComplexity D eta R₀ theta r,
        ((subcriticalProfileClassGraphFinset F alpha p).card : ℝ)) ≤
      Z * (((n : ℝ) + 1) ^ (Cprof * (r + 1) + 6 * Qact) *
        Real.exp (-(32 * c) * r * n)) := by
    have hcount : ((subcriticalProfilesOfComplexity D eta R₀ theta r).card : ℝ) ≤
        ((n : ℝ) + 1) ^ (Cprof * (r + 1)) := by
      have hh := subcriticalProfilesOfComplexity_card_le D eta R₀ theta r Qvis hret hvis
      simp only [Fintype.card_fin] at hh
      exact_mod_cast hh
    calc
      _ ≤ ∑ _p ∈ subcriticalProfilesOfComplexity D eta R₀ theta r,
          ((n : ℝ) + 1) ^ (6 * Qact) * Z * Real.exp (-(32 * c) * r * n) :=
        Finset.sum_le_sum (hprofile r)
      _ = ((subcriticalProfilesOfComplexity D eta R₀ theta r).card : ℝ) *
          (((n : ℝ) + 1) ^ (6 * Qact) * Z * Real.exp (-(32 * c) * r * n)) := by simp
      _ ≤ ((n : ℝ) + 1) ^ (Cprof * (r + 1)) *
          (((n : ℝ) + 1) ^ (6 * Qact) * Z * Real.exp (-(32 * c) * r * n)) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hcover : ((subcriticalNoncleanDivisionGraphFinset F D eta R₀).card : ℝ) ≤
      ∑ r ∈ Finset.Icc 1 (2 * n),
        ∑ p ∈ subcriticalProfilesOfComplexity D eta R₀ theta r,
          ((subcriticalProfileClassGraphFinset F alpha p).card : ℝ) := by
    have hh := subcriticalNonclean_card_le_sum_profiles F D eta R₀ theta alpha
      P.localConditions.alpha_pos (by have := P.localConditions.alpha_small; linarith)
    simp only [Fintype.card_fin] at hh
    exact_mod_cast hh
  have hsum := DenseGraph.sum_profileComplexity_pow_mul_exp_le Cprof (6 * Qact) n hc.le hpoly
  calc
    _ ≤ _ := hcover
    _ ≤ ∑ r ∈ Finset.Icc 1 (2 * n),
        Z * (((n : ℝ) + 1) ^ (Cprof * (r + 1) + 6 * Qact) *
          Real.exp (-(32 * c) * r * n)) := Finset.sum_le_sum fun r _ ↦ hlevel r
    _ = Z * ∑ r ∈ Finset.Icc 1 (2 * n),
        ((n : ℝ) + 1) ^ (Cprof * (r + 1) + 6 * Qact) *
          Real.exp (-(32 * c) * r * n) := (Finset.mul_sum _ _ _).symm
    _ ≤ Z * Real.exp (-c * n) := mul_le_mul_of_nonneg_left hsum hZ
    _ = _ := mul_comm _ _

end InducedStars
