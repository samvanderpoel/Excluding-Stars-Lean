import InducedStars.Structure.Subcritical.DistinguishedReferenceUniform

/-!
# Exact remainder room for separated-candidate matching transfers

Paper: `lemma:CompareBallsInCutMetricNlogNK1k`. The reference uses the actual
finite density `(m-b)/choose n 2`; convergence has no imposed rate. The
linear room is uniform in the original key and the remainder-edge level.
Only retained keys, not nonretained decorations, enter the comparison.
-/

noncomputable section
open Finset Set Filter Topology
open scoped Classical
namespace InducedStars

def subcriticalSeparatedMatchingSize (gap : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (gap * n / 16)

theorem subcriticalSeparatedMatchingSize_le {gap : ℝ} (hg : 0 ≤ gap) (n : ℕ) :
    (subcriticalSeparatedMatchingSize gap n : ℝ) ≤ gap * n / 16 :=
  Nat.floor_le (by positivity)

theorem eventually_subcriticalSeparatedMatchingSize_lower {gap : ℝ} (hg : 0 < gap) :
    ∀ᶠ n : ℕ in atTop,
      gap * n / 32 ≤ (subcriticalSeparatedMatchingSize gap n : ℝ) := by
  filter_upwards [eventually_ge_atTop (Nat.ceil (32 / gap))] with n hn
  have hlarge : 32 / gap ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hmul := (div_le_iff₀ hg).mp hlarge
  have hf := Nat.lt_floor_add_one (gap * n / 16)
  change gap * n / 16 < (subcriticalSeparatedMatchingSize gap n : ℝ) + 1 at hf
  linarith

theorem subcritical_remainder_room_of_linear_gap {n s s' : ℕ} {mu gap : ℝ}
    (hg : 0 ≤ gap)
    (hs : (s : ℝ) ≤ (1 - mu - gap / 2) * n)
    (hs' : (1 - mu - gap / 8) * n ≤ (s' : ℝ)) :
    s + 2 * subcriticalSeparatedMatchingSize gap n ≤ s' := by
  have hf := subcriticalSeparatedMatchingSize_le hg n
  have hn : (0 : ℝ) ≤ n := by positivity
  have hgn := mul_nonneg hg hn
  have h : (s : ℝ) + 2 * subcriticalSeparatedMatchingSize gap n ≤ s' := by
    nlinarith
  exact_mod_cast h

/-- Upper mass control needs only the original density convergence and
nonnegativity of `b`. It is uniform over all remainder levels. -/
theorem eventually_subcriticalReferenceMass_le_oneBlock_add {k : ℕ} (hk : 3 ≤ k)
    {gamma gap : ℝ} (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (hgap : 0 < gap)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n : ℕ in atTop, ∀ b : ℕ,
      subcriticalReferenceMass k n (m n) b ≤ subcriticalOneBlockLength k gamma + gap / 8 := by
  let mu := subcriticalOneBlockLength k gamma
  have hmu : 0 < mu := subcriticalOneBlockLength_pos hk hgamma.1
  have hgk := gammaK_pos hk
  have hsq : gammaK k * mu^2 = gamma := by
    dsimp [mu]
    rw [subcriticalOneBlockLength_eq_sqrt_div_gammaK hk, Real.sq_sqrt
      (div_nonneg hgamma.1.le hgk.le)]
    exact mul_div_cancel₀ _ hgk.ne'
  have hcut : gamma < gammaK k * (mu + gap / 8)^2 := by
    have hprod := mul_pos hgk (show 0 < (mu + gap / 8)^2 - mu^2 by nlinarith)
    nlinarith
  have hlim := hm.eventually (Iio_mem_nhds hcut)
  filter_upwards [hlim, eventually_ge_atTop 2] with n hn hn2
  intro b
  have hN : (0 : ℝ) < (n.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hn2
  have hdensity : subcriticalReferenceDensity n (m n) b ≤ (m n : ℝ) / (n.choose 2 : ℝ) := by
    unfold subcriticalReferenceDensity
    exact div_le_div_of_nonneg_right (sub_le_self _ (Nat.cast_nonneg _)) hN.le
  change Real.sqrt _ ≤ mu + gap / 8
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  apply (div_le_iff₀ hgk).2
  nlinarith [hdensity.trans hn.le]

/-- The floor-sized reference is valid and leaves the required linear
remainder, uniformly over every allowed sparse-edge count. -/
theorem eventually_subcriticalReference_remainder_lower {k : ℕ} (hk : 3 ≤ k)
    {gamma gap B : ℝ} (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (hgap : 0 < gap)
    (hB : 0 ≤ B) (hsmall : 16 * B ≤ gamma)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n : ℕ in atTop, ∀ b : ℕ, (b : ℝ) ≤ B * (n : ℝ)^2 →
      k - 1 ≤ subcriticalReferenceSupportSize k n (m n) b ∧
      subcriticalReferenceSupportSize k n (m n) b ≤ n ∧
      gamma / 2 ≤ subcriticalReferenceDensity n (m n) b ∧
      subcriticalReferenceDensity n (m n) b ≤ (gamma + gammaK k) / 2 ∧
      (1 - subcriticalOneBlockLength k gamma - gap / 8) * n ≤
        ((subcriticalDistinguishedReferenceKey hk n (m n) b).remainder.card : ℝ) := by
  let a := Real.sqrt ((gamma / 2) / gammaK k)
  have ha : 0 < a := Real.sqrt_pos.mpr (div_pos (half_pos hgamma.1) (gammaK_pos hk))
  filter_upwards [eventually_subcriticalReferenceDensity_band hk hgamma hB hsmall m hm,
    eventually_subcriticalReferenceMass_le_oneBlock_add hk hgamma hgap m hm,
    eventually_subcriticalReference_scale (k := k) ha zero_lt_one] with n hband hmass hscale
  intro b hb
  have hg := hband b hb
  have hactual : subcriticalReferenceDensity n (m n) b ∈ Ioo (0 : ℝ) (gammaK k) :=
    ⟨(half_pos hgamma.1).trans_le hg.1, hg.2.trans_lt (by linarith [hgamma.2])⟩
  have hmuLower : a ≤ subcriticalReferenceMass k n (m n) b :=
    Real.sqrt_le_sqrt ((div_le_div_iff_of_pos_right (gammaK_pos hk)).mpr hg.1)
  have hq := subcriticalReference_support_lower hk ha hmuLower hscale.2.1
  have hrq : k - 1 ≤ subcriticalReferenceSupportSize k n (m n) b := by omega
  have hqn := subcriticalReferenceSupportSize_le (subcriticalReferenceMass_mem_Ioo hk hactual).2.le
  refine ⟨hrq, hqn, hg.1, hg.2, ?_⟩
  unfold subcriticalDistinguishedReferenceKey
  rw [dif_pos ⟨hrq, hqn⟩, balancedRetainedReferenceKey_remainder_card, Nat.cast_sub hqn]
  have hf := (subcriticalReferenceSupportSize_floor_bounds k n (m n) b).1
  have hh := mul_le_mul_of_nonneg_right (hmass b) (show (0 : ℝ) ≤ n by positivity)
  linarith

/-- Exact room for adding the matching used to compare a separated key
against the reference denominator. All counting remains in separate modules. -/
theorem eventually_subcriticalReference_remainder_room {k : ℕ} (hk : 3 ≤ k)
    {gamma gap B : ℝ} (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (hgap : 0 < gap)
    (hB : 0 ≤ B) (hsmall : 16 * B ≤ gamma)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n : ℕ in atTop, ∀ b s : ℕ, (b : ℝ) ≤ B * (n : ℝ)^2 →
      (s : ℝ) ≤ (1 - subcriticalOneBlockLength k gamma - gap / 2) * n →
      s + 2 * subcriticalSeparatedMatchingSize gap n ≤
        (subcriticalDistinguishedReferenceKey hk n (m n) b).remainder.card := by
  filter_upwards [eventually_subcriticalReference_remainder_lower hk hgamma hgap hB hsmall m hm]
    with n hn
  intro b s hb hs
  exact subcritical_remainder_room_of_linear_gap hgap.le hs (hn b hb).2.2.2.2

end InducedStars
