import InducedStars.FiniteModels.GraphFamiliesCore
import InducedStars.Graphon.Functionals
import InducedStars.FiniteModels.WRandom
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Finite Shannon entropy

This file develops base-two Shannon entropy for a real-valued probability
mass on a finite type.  The definition is deliberately independent of a
particular `PMF` representation; its hypotheses record nonnegativity and
normalization exactly where they are used.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

/-- Base-two Shannon entropy of a real mass function on a finite type. -/
noncomputable def finiteShannonEntropy {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) : ℝ :=
  -∑ ω, μ ω * log2 (μ ω)

/-- Entropy contributed by a finite set of outcomes. -/
noncomputable def finitePartialShannonEntropy {Ω : Type*}
    (s : Finset Ω) (μ : Ω → ℝ) : ℝ :=
  -∑ ω ∈ s, μ ω * log2 (μ ω)

/-- Total mass assigned to a finite event. -/
noncomputable def finiteEventMass {Ω : Type*}
    (s : Finset Ω) (μ : Ω → ℝ) : ℝ :=
  ∑ ω ∈ s, μ ω

/-- The (strictly) positive support of a finite nonnegative mass. -/
noncomputable def finiteMassSupport {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω ↦ 0 < μ ω

@[simp] theorem mem_finiteMassSupport {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (ω : Ω) :
    ω ∈ finiteMassSupport μ ↔ 0 < μ ω := by
  classical
  simp [finiteMassSupport]

theorem mass_le_one_of_nonneg_of_sum_eq_one {Ω : Type*} [Fintype Ω]
    {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) (hsum : ∑ ω, μ ω = 1)
    (ω : Ω) : μ ω ≤ 1 := by
  classical
  calc
    μ ω ≤ ∑ x, μ x :=
      Finset.single_le_sum (fun x _ ↦ hμ x) (Finset.mem_univ ω)
    _ = 1 := hsum

private theorem neg_mul_log2_eq_negMulLog_div (p : ℝ) :
    -(p * log2 p) = Real.negMulLog p / Real.log 2 := by
  simp only [log2, Real.negMulLog]
  ring

theorem finitePartialShannonEntropy_eq_negMulLog {Ω : Type*}
    (s : Finset Ω) (μ : Ω → ℝ) :
    finitePartialShannonEntropy s μ =
      (∑ ω ∈ s, Real.negMulLog (μ ω)) / Real.log 2 := by
  unfold finitePartialShannonEntropy
  rw [← Finset.sum_neg_distrib]
  simp_rw [neg_mul_log2_eq_negMulLog_div]
  rw [Finset.sum_div]

theorem finiteShannonEntropy_eq_negMulLog {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) :
    finiteShannonEntropy μ =
      (∑ ω, Real.negMulLog (μ ω)) / Real.log 2 := by
  classical
  rw [finiteShannonEntropy, ← finitePartialShannonEntropy]
  exact finitePartialShannonEntropy_eq_negMulLog Finset.univ μ

/-- Shannon entropy is nonnegative for a normalized finite mass. -/
theorem finiteShannonEntropy_nonneg {Ω : Type*} [Fintype Ω]
    {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω)
    (hsum : ∑ ω, μ ω = 1) :
    0 ≤ finiteShannonEntropy μ := by
  rw [finiteShannonEntropy_eq_negMulLog]
  exact div_nonneg
    (Finset.sum_nonneg fun ω _ ↦
      Real.negMulLog_nonneg (hμ ω)
        (mass_le_one_of_nonneg_of_sum_eq_one hμ hsum ω))
    realLogTwo_pos.le

/-- Zero-mass outcomes contribute no entropy, so the full entropy is the
partial entropy on the positive support. -/
theorem finiteShannonEntropy_eq_support {Ω : Type*} [Fintype Ω]
    {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) :
    finiteShannonEntropy μ =
      finitePartialShannonEntropy (finiteMassSupport μ) μ := by
  classical
  simp only [finiteShannonEntropy, finitePartialShannonEntropy, finiteMassSupport,
    Finset.sum_filter, Finset.sum_neg_distrib]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hp : 0 < μ ω
  · simp [hp]
  · have hz : μ ω = 0 := le_antisymm (not_lt.mp hp) (hμ ω)
    simp [hp, hz]

private theorem card_mul_negMulLog_div_card {k : ℕ} (hk : 0 < k) (p : ℝ) :
    (k : ℝ) * Real.negMulLog (p / (k : ℝ)) =
      Real.negMulLog p + p * Real.log (k : ℝ) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [div_eq_mul_inv, Real.negMulLog_mul]
  have hlog : Real.negMulLog ((k : ℝ)⁻¹) =
      (k : ℝ)⁻¹ * Real.log (k : ℝ) := by
    simp [Real.negMulLog, Real.log_inv]
  rw [hlog]
  field_simp
  <;> ring

/-- A finite Jensen bound for a nonnegative (not necessarily normalized)
mass on a nonempty finite set.  This is the log-sum inequality in the exact
form used for event entropy estimates. -/
theorem partial_negMulLog_le {Ω : Type*} (s : Finset Ω) (μ : Ω → ℝ)
    (hs : s.Nonempty) (hμ : ∀ ω ∈ s, 0 ≤ μ ω) :
    ∑ ω ∈ s, Real.negMulLog (μ ω) ≤
      Real.negMulLog (∑ ω ∈ s, μ ω) +
        (∑ ω ∈ s, μ ω) * Real.log (s.card : ℝ) := by
  let k : ℝ := s.card
  have hcard : 0 < s.card := Finset.card_pos.mpr hs
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast hcard
  have hweights : ∑ _ ∈ s, k⁻¹ = 1 := by
    simp [k, hk.ne']
  have hj := Real.concaveOn_negMulLog.le_map_sum
    (t := s) (w := fun _ ↦ k⁻¹) (p := μ)
    (fun _ _ ↦ inv_nonneg.mpr hk.le) hweights
    (fun ω hω ↦ hμ ω hω)
  simp only [smul_eq_mul, Function.comp_apply] at hj
  have hleft :
      ∑ ω ∈ s, k⁻¹ * Real.negMulLog (μ ω) =
        k⁻¹ * ∑ ω ∈ s, Real.negMulLog (μ ω) := by
    rw [Finset.mul_sum]
  have hright :
      ∑ ω ∈ s, k⁻¹ * μ ω =
        (∑ ω ∈ s, μ ω) / k := by
    rw [← Finset.mul_sum]
    simp [div_eq_mul_inv, mul_comm]
  rw [hleft, hright] at hj
  have hscaled := (mul_le_mul_of_nonneg_left hj hk.le)
  have hcancel : k * (k⁻¹ * ∑ ω ∈ s, Real.negMulLog (μ ω)) =
      ∑ ω ∈ s, Real.negMulLog (μ ω) := by
    field_simp
  rw [hcancel] at hscaled
  simpa [k] using
    hscaled.trans_eq (card_mul_negMulLog_div_card hcard (∑ ω ∈ s, μ ω))

/-- The log-sum bound, including the empty-event boundary. -/
theorem partial_negMulLog_le_card {Ω : Type*} (s : Finset Ω) (μ : Ω → ℝ)
    (hμ : ∀ ω ∈ s, 0 ≤ μ ω) :
    ∑ ω ∈ s, Real.negMulLog (μ ω) ≤
      Real.negMulLog (finiteEventMass s μ) +
        finiteEventMass s μ * Real.log (s.card : ℝ) := by
  by_cases hs : s.Nonempty
  · simpa only [finiteEventMass] using partial_negMulLog_le s μ hs hμ
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he, finiteEventMass]

/-- Base-two partial-entropy form of the finite log-sum inequality. -/
theorem finitePartialShannonEntropy_le {Ω : Type*}
    (s : Finset Ω) (μ : Ω → ℝ) (hμ : ∀ ω ∈ s, 0 ≤ μ ω) :
    finitePartialShannonEntropy s μ ≤
      Real.negMulLog (finiteEventMass s μ) / Real.log 2 +
        finiteEventMass s μ * log2 (s.card : ℝ) := by
  rw [finitePartialShannonEntropy_eq_negMulLog, log2]
  have h := partial_negMulLog_le_card s μ hμ
  calc
    (∑ ω ∈ s, Real.negMulLog (μ ω)) / Real.log 2 ≤
        (Real.negMulLog (finiteEventMass s μ) +
          finiteEventMass s μ * Real.log (s.card : ℝ)) / Real.log 2 :=
      div_le_div_of_nonneg_right h realLogTwo_pos.le
    _ = Real.negMulLog (finiteEventMass s μ) / Real.log 2 +
        finiteEventMass s μ *
          (Real.log (s.card : ℝ) / Real.log 2) := by ring

theorem finiteEventMass_nonneg {Ω : Type*} {s : Finset Ω} {μ : Ω → ℝ}
    (hμ : ∀ ω, 0 ≤ μ ω) :
    0 ≤ finiteEventMass s μ := by
  exact Finset.sum_nonneg fun ω _ ↦ hμ ω

theorem finiteEventMass_le_one {Ω : Type*} [Fintype Ω]
    {s : Finset Ω} {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω)
    (hsum : ∑ ω, μ ω = 1) :
    finiteEventMass s μ ≤ 1 := by
  rw [← hsum]
  exact Finset.sum_le_univ_sum_of_nonneg hμ

private theorem finiteShannonEntropy_event_partition {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω]
    (s : Finset Ω) (μ : Ω → ℝ) :
    finiteShannonEntropy μ = finitePartialShannonEntropy s μ +
      finitePartialShannonEntropy (Finset.univ \ s) μ := by
  classical
  simp only [finiteShannonEntropy, finitePartialShannonEntropy]
  rw [← neg_add, ← Finset.sum_union]
  · congr 2
    exact (Finset.union_sdiff_of_subset (Finset.subset_univ s)).symm
  · exact Finset.disjoint_sdiff

private theorem finiteEventMass_compl {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω]
    (s : Finset Ω) (μ : Ω → ℝ) (hsum : ∑ ω, μ ω = 1) :
    finiteEventMass (Finset.univ \ s) μ = 1 - finiteEventMass s μ := by
  classical
  have hu : (∑ ω, μ ω) =
      (∑ ω ∈ s, μ ω) + ∑ ω ∈ (Finset.univ \ s), μ ω := by
    rw [← Finset.sum_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (Finset.subset_univ s)]
  unfold finiteEventMass
  rw [hsum] at hu
  linarith

/-- The binary entropy of the indicator of an event, in neg-log form. -/
theorem negMulLog_add_compl_div_logTwo (p : ℝ) :
    Real.negMulLog p / Real.log 2 +
      Real.negMulLog (1 - p) / Real.log 2 = binaryEntropy p := by
  rw [binaryEntropy_eq_formula]
  simp only [log2, Real.negMulLog]
  ring

/-- Split a normalized finite distribution according to an event.  This is
the finite entropy chain-rule inequality, with the exact event and
complement cardinalities. -/
theorem finiteShannonEntropy_le_event_split {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω]
    (s : Finset Ω) {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω)
    (hsum : ∑ ω, μ ω = 1) :
    finiteShannonEntropy μ ≤
      binaryEntropy (finiteEventMass s μ) +
        finiteEventMass s μ * log2 (s.card : ℝ) +
        (1 - finiteEventMass s μ) *
          log2 ((Finset.univ \ s).card : ℝ) := by
  classical
  rw [finiteShannonEntropy_event_partition s μ]
  have hs := finitePartialShannonEntropy_le s μ (fun ω _ ↦ hμ ω)
  have hc := finitePartialShannonEntropy_le (Finset.univ \ s) μ
    (fun ω _ ↦ hμ ω)
  rw [finiteEventMass_compl s μ hsum] at hc
  calc
    finitePartialShannonEntropy s μ +
        finitePartialShannonEntropy (Finset.univ \ s) μ ≤
      (Real.negMulLog (finiteEventMass s μ) / Real.log 2 +
          finiteEventMass s μ * log2 (s.card : ℝ)) +
        (Real.negMulLog (1 - finiteEventMass s μ) / Real.log 2 +
          (1 - finiteEventMass s μ) *
            log2 ((Finset.univ \ s).card : ℝ)) := add_le_add hs hc
    _ = _ := by
      rw [← negMulLog_add_compl_div_logTwo]
      ring

private theorem one_sub_eventMass_nonneg {Ω : Type*} [Fintype Ω]
    (s : Finset Ω) {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω)
    (hsum : ∑ ω, μ ω = 1) :
    0 ≤ 1 - finiteEventMass s μ := by
  linarith [finiteEventMass_le_one (s := s) hμ hsum]

/-- Coarse high-probability-event entropy bound.  The complement is bounded
by the full finite outcome space and binary event entropy is at most one. -/
theorem finiteShannonEntropy_le_event {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω]
    (s : Finset Ω) {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω)
    (hsum : ∑ ω, μ ω = 1) :
    finiteShannonEntropy μ ≤
      1 + finiteEventMass s μ * log2 (s.card : ℝ) +
        (1 - finiteEventMass s μ) * log2 (Fintype.card Ω : ℝ) := by
  classical
  refine (finiteShannonEntropy_le_event_split s hμ hsum).trans ?_
  have hbin := binaryEntropy_le_one (finiteEventMass s μ)
  have hcompCard : (Finset.univ \ s).card ≤ Fintype.card Ω := by
    simpa using Finset.card_le_card
      (show Finset.univ \ s ⊆ (Finset.univ : Finset Ω) from Finset.sdiff_subset)
  have hlog : log2 ((Finset.univ \ s).card : ℝ) ≤
      log2 (Fintype.card Ω : ℝ) := by
    by_cases hc : (Finset.univ \ s).Nonempty
    · unfold log2
      apply div_le_div_of_nonneg_right _ realLogTwo_pos.le
      apply Real.strictMonoOn_log.monotoneOn
      · simp only [Set.mem_Ioi]
        exact_mod_cast Finset.card_pos.mpr hc
      · simp only [Set.mem_Ioi]
        exact_mod_cast Fintype.card_pos
      · exact_mod_cast hcompCard
    · have he : Finset.univ \ s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hc
      simp [he, log2_nonneg (show (1 : ℝ) ≤ Fintype.card Ω by exact_mod_cast Fintype.card_pos)]
  have hmul := mul_le_mul_of_nonneg_left hlog
    (one_sub_eventMass_nonneg s hμ hsum)
  linarith

/-- Entropy of a normalized finite mass is at most the base-two logarithm
of the cardinality of its positive support. -/
theorem finiteShannonEntropy_le_log2_support {Ω : Type*} [Fintype Ω]
    {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω)
    (hsum : ∑ ω, μ ω = 1) :
    finiteShannonEntropy μ ≤ log2 ((finiteMassSupport μ).card : ℝ) := by
  classical
  have hs : (finiteMassSupport μ).Nonempty := by
    by_contra hne
    have hempty : finiteMassSupport μ = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    have hzero : ∀ ω, μ ω = 0 := by
      intro ω
      have hnpos : ¬ 0 < μ ω := by
        intro hp
        have hmem : ω ∈ finiteMassSupport μ :=
          (mem_finiteMassSupport μ ω).2 hp
        simpa [hempty] using hmem
      exact le_antisymm (not_lt.mp hnpos) (hμ ω)
    simpa [hzero] using hsum
  have hsumSupport : ∑ ω ∈ finiteMassSupport μ, μ ω = 1 := by
    rw [← hsum]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro ω _ hnot
    have hnpos : ¬ 0 < μ ω := by
      simpa [finiteMassSupport] using hnot
    exact le_antisymm (not_lt.mp hnpos) (hμ ω)
  rw [finiteShannonEntropy_eq_support hμ,
    finitePartialShannonEntropy_eq_negMulLog]
  have hbound := partial_negMulLog_le (finiteMassSupport μ) μ hs
    (fun ω _ ↦ hμ ω)
  rw [hsumSupport, Real.negMulLog_one, zero_add] at hbound
  rw [log2]
  exact div_le_div_of_nonneg_right (by simpa using hbound) realLogTwo_pos.le

/-- Coarser ambient-space entropy bound. -/
theorem finiteShannonEntropy_le_log2_card {Ω : Type*} [Fintype Ω]
    [Nonempty Ω] {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω)
    (hsum : ∑ ω, μ ω = 1) :
    finiteShannonEntropy μ ≤ log2 (Fintype.card Ω : ℝ) := by
  have hs : (finiteMassSupport μ).Nonempty := by
    by_contra hne
    have hempty : finiteMassSupport μ = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    have hzero : ∀ ω, μ ω = 0 := by
      intro ω
      have hnpos : ¬0 < μ ω := by
        intro hp
        have := (mem_finiteMassSupport μ ω).2 hp
        simpa [hempty] using this
      exact le_antisymm (not_lt.mp hnpos) (hμ ω)
    simpa [hzero] using hsum
  refine (finiteShannonEntropy_le_log2_support hμ hsum).trans ?_
  unfold log2
  apply div_le_div_of_nonneg_right _ realLogTwo_pos.le
  apply Real.strictMonoOn_log.monotoneOn
  · simp only [Set.mem_Ioi]
    exact_mod_cast Finset.card_pos.mpr hs
  · simp only [Set.mem_Ioi]
    exact_mod_cast Fintype.card_pos
  · exact_mod_cast Finset.card_le_card
      (Finset.subset_univ (finiteMassSupport μ))

/-! ## Entropy of the graphon-sampling marginal -/

/-- Base-two Shannon entropy of the labeled `W`-random graph on `Fin n`. -/
noncomputable def wRandomGraphEntropy (W : Graphon) (n : ℕ) : ℝ :=
  finiteShannonEntropy fun G : SimpleGraph (Fin n) ↦ wRandomGraphMass W G

theorem wRandomGraphEntropy_nonneg (W : Graphon) (n : ℕ) :
    0 ≤ wRandomGraphEntropy W n := by
  unfold wRandomGraphEntropy
  apply finiteShannonEntropy_nonneg
  · exact fun G ↦ wRandomGraphMass_nonneg W G
  · exact wRandomGraphMass_sum W

theorem wRandomGraphEntropy_le_log2_card (W : Graphon) (n : ℕ) :
    wRandomGraphEntropy W n ≤
      log2 (Fintype.card (SimpleGraph (Fin n)) : ℝ) := by
  unfold wRandomGraphEntropy
  apply finiteShannonEntropy_le_log2_card
  · exact fun G ↦ wRandomGraphMass_nonneg W G
  · exact wRandomGraphMass_sum W

end InducedStars
