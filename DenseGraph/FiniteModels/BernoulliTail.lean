import DenseGraph.FiniteModels.BernoulliEvents
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Finite Bernoulli tails with an untrimmed threshold

The elementary cylinder proof gives sharp Hamming-ball entropy bounds and
tail bounds for arbitrary inhomogeneous Bernoulli coordinates. The number
of available coordinates may be smaller than the size used in the threshold;
the lower-tail estimate records this loss explicitly.
-/

noncomputable section
open Finset Set
open scoped BigOperators

namespace DenseGraph.FiniteBernoulliProduct

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Successful-coordinate count in a fixed support. -/
def successCountAtMost (A : Finset Ω) (r : ℝ) : Finset (Finset Ω) :=
  Finset.univ.filter fun S ↦ ((S ∩ A).card : ℝ) ≤ r

def successCountAtLeast (A : Finset Ω) (r : ℝ) : Finset (Finset Ω) :=
  Finset.univ.filter fun S ↦ r ≤ ((S ∩ A).card : ℝ)

@[simp] theorem mem_successCountAtMost (A S : Finset Ω) (r : ℝ) :
    S ∈ successCountAtMost A r ↔ ((S ∩ A).card : ℝ) ≤ r := by
  classical
  simp [successCountAtMost]

@[simp] theorem mem_successCountAtLeast (A S : Finset Ω) (r : ℝ) :
    S ∈ successCountAtLeast A r ↔ r ≤ ((S ∩ A).card : ℝ) := by
  classical
  simp [successCountAtLeast]

theorem successCountAtMost_supportedOn (A : Finset Ω) (r : ℝ) :
    EventSupportedOn (successCountAtMost A r) A := by
  intro S T h
  simp only [mem_successCountAtMost, h]

theorem successCountAtLeast_supportedOn (A : Finset Ω) (r : ℝ) :
    EventSupportedOn (successCountAtLeast A r) A := by
  intro S T h
  simp only [mem_successCountAtLeast, h]

/-- All support patterns of relative size at most `t`. -/
def smallPatterns (A : Finset Ω) (t : ℝ) : Finset (Finset Ω) :=
  A.powerset.filter fun a ↦ (a.card : ℝ) ≤ t * A.card

@[simp] theorem mem_smallPatterns (A a : Finset Ω) (t : ℝ) :
    a ∈ smallPatterns A t ↔ a ⊆ A ∧ (a.card : ℝ) ≤ t * A.card := by
  classical
  simp [smallPatterns]

theorem eventPatterns_successCountAtMost (A : Finset Ω) (r : ℝ) :
    eventPatterns (successCountAtMost A r) A =
      A.powerset.filter fun a ↦ (a.card : ℝ) ≤ r := by
  classical
  ext a
  simp only [mem_eventPatterns, mem_successCountAtMost, Finset.mem_filter,
    Finset.mem_powerset]
  exact and_congr_right fun ha ↦ by rw [Finset.inter_eq_left.mpr ha]

theorem eventPatterns_successCountAtLeast (A : Finset Ω) (r : ℝ) :
    eventPatterns (successCountAtLeast A r) A =
      A.powerset.filter fun a ↦ r ≤ (a.card : ℝ) := by
  classical
  ext a
  simp only [mem_eventPatterns, mem_successCountAtLeast, Finset.mem_filter,
    Finset.mem_powerset]
  exact and_congr_right fun ha ↦ by rw [Finset.inter_eq_left.mpr ha]

private theorem prod_pattern_const {A a : Finset Ω} (ha : a ⊆ A) (q r : ℝ) :
    (∏ e ∈ A, if e ∈ a then q else r) = q ^ a.card * r ^ (A \ a).card := by
  classical
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr ha, ← Finset.sdiff_eq_filter]
  simp only [Finset.prod_const]

/-- Exact homogeneous cylinder mass, available when only coordinates in
the specified support have a common parameter. -/
theorem eventProbability_cylinderEvent_eq_pow
    (P : FiniteBernoulliProduct Ω) {A a : Finset Ω} (ha : a ⊆ A)
    {q : ℝ} (hq : ∀ e ∈ A, P.probability e = q) :
    P.eventProbability (cylinderEvent A a) = q ^ a.card * (1 - q) ^ (A \ a).card := by
  rw [eventProbability_cylinderEvent P ha, ← prod_pattern_const ha q (1 - q)]
  exact Finset.prod_congr rfl (fun e he ↦ by rw [hq e he])

private theorem pow_eq_exp_log_mul {q : ℝ} (hq : 0 < q) (r : ℕ) :
    q ^ r = Real.exp (Real.log q * r) := by
  rw [mul_comm, Real.exp_nat_mul, Real.exp_log hq]

/-- Summing the masses of all patterns on one support gives one. -/
theorem sum_cylinderEvent_probability (P : FiniteBernoulliProduct Ω) (A : Finset Ω) :
    (∑ a ∈ A.powerset, P.eventProbability (cylinderEvent A a)) = 1 := by
  classical
  have h := P.eventProbability_eq_sum_patterns (EventSupportedOn.universal A)
  have heq : eventPatterns (Finset.univ : Finset (Finset Ω)) A = A.powerset := by
    ext a
    simp
  rw [eventProbability_univ, heq] at h
  exact h.symm

/-- Sharp Hamming-ball entropy bound, with natural logarithms. Zero support
and zero relative radius are included. -/
theorem card_smallPatterns_le_exp_binEntropy (A : Finset Ω) {t : ℝ}
    (ht : 0 ≤ t) (htHalf : t ≤ 1 / 2) :
    ((smallPatterns A t).card : ℝ) ≤ Real.exp (A.card * Real.binEntropy t) := by
  classical
  rcases ht.eq_or_lt with ht | ht
  · have hz : smallPatterns A t = {∅} := by
      ext a
      simp only [← ht, mem_smallPatterns, zero_mul, Nat.cast_nonpos,
        Nat.le_zero, Finset.card_eq_zero, Finset.mem_singleton]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ Finset.empty_subset _, h⟩⟩
    rw [hz]
    simp [← ht]
  have ht1 : t < 1 := by linarith
  let P : FiniteBernoulliProduct Ω :=
    ⟨fun _ ↦ t, fun _ ↦ ⟨ht.le, ht1.le⟩⟩
  have hlog : Real.log t ≤ Real.log (1 - t) :=
    Real.log_le_log ht (by linarith)
  have hmass (a : Finset Ω) (ha : a ∈ smallPatterns A t) :
      Real.exp (-(A.card * Real.binEntropy t)) ≤ P.eventProbability (cylinderEvent A a) := by
    obtain ⟨haA, hac⟩ := mem_smallPatterns A a t |>.mp ha
    have hcard : ((A \ a).card : ℝ) + a.card = A.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card haA
    rw [eventProbability_cylinderEvent_eq_pow P haA (fun _ _ ↦ rfl),
      pow_eq_exp_log_mul ht, pow_eq_exp_log_mul (by linarith : 0 < 1 - t), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonpos_right hac (sub_nonpos.mpr hlog)
    have hd : ((A \ a).card : ℝ) = A.card - a.card := by linarith
    calc
      _ = t * A.card * (Real.log t - Real.log (1 - t)) +
          A.card * Real.log (1 - t) := by
        rw [Real.binEntropy, Real.log_inv, Real.log_inv]
        ring
      _ ≤ a.card * (Real.log t - Real.log (1 - t)) +
          A.card * Real.log (1 - t) := add_le_add hmul le_rfl
      _ = _ := by rw [hd]; ring
  have hsum : (smallPatterns A t).card * Real.exp (-(A.card * Real.binEntropy t)) ≤ 1 := by
    calc
      _ = ∑ _a ∈ smallPatterns A t, Real.exp (-(A.card * Real.binEntropy t)) := by simp
      _ ≤ ∑ a ∈ smallPatterns A t, P.eventProbability (cylinderEvent A a) :=
        Finset.sum_le_sum hmass
      _ ≤ ∑ a ∈ A.powerset, P.eventProbability (cylinderEvent A a) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun a _ _ ↦ P.eventProbability_nonneg _)
      _ = 1 := sum_cylinderEvent_probability P A
  have h := mul_le_mul_of_nonneg_right hsum (Real.exp_pos (A.card * Real.binEntropy t)).le
  simpa only [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one,
    one_mul] using h

/-- A cylinder with many successes is bounded using only upper bounds on
the successful-coordinate probabilities; failures cost at most one. -/
theorem cylinderEvent_probability_le_exp_successes
    (P : FiniteBernoulliProduct Ω) {A a : Finset Ω} (ha : a ⊆ A)
    {q : ℝ} (hq : 0 < q) (hprob : ∀ e ∈ A, P.probability e ≤ q) :
    P.eventProbability (cylinderEvent A a) ≤ Real.exp (Real.log q * a.card) := by
  rw [eventProbability_cylinderEvent P ha]
  calc
    _ ≤ ∏ e ∈ A, if e ∈ a then q else (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro e he
        split_ifs
        · exact (P.probability_mem_Icc e).1
        · exact sub_nonneg.mpr (P.probability_mem_Icc e).2
      · intro e he
        split_ifs
        · exact hprob e he
        · linarith [(P.probability_mem_Icc e).1]
    _ = q ^ a.card := by rw [prod_pattern_const ha]; simp
    _ = _ := pow_eq_exp_log_mul hq _

/-- The complementary cylinder estimate needs only lower bounds on the
successful-coordinate probabilities. -/
theorem cylinderEvent_probability_le_exp_failures
    (P : FiniteBernoulliProduct Ω) {A a : Finset Ω} (ha : a ⊆ A)
    {q : ℝ} (hq : q < 1) (hprob : ∀ e ∈ A, q ≤ P.probability e) :
    P.eventProbability (cylinderEvent A a) ≤ Real.exp (Real.log (1 - q) * (A \ a).card) := by
  rw [eventProbability_cylinderEvent P ha]
  calc
    _ ≤ ∏ e ∈ A, if e ∈ a then (1 : ℝ) else 1 - q := by
      apply Finset.prod_le_prod
      · intro e he
        split_ifs
        · exact (P.probability_mem_Icc e).1
        · exact sub_nonneg.mpr (P.probability_mem_Icc e).2
      · intro e he
        split_ifs
        · exact (P.probability_mem_Icc e).2
        · linarith [hprob e he]
    _ = (1 - q) ^ (A \ a).card := by rw [prod_pattern_const ha]; simp
    _ = _ := pow_eq_exp_log_mul (by linarith) _

/-- Counting accepted patterns bounds a supported event once every cylinder
has the same upper bound. -/
theorem eventProbability_le_card_patterns_mul
    (P : FiniteBernoulliProduct Ω) {event : Finset (Finset Ω)} {A : Finset Ω}
    (hsupport : EventSupportedOn event A) {b : ℝ}
    (hbound : ∀ a ∈ eventPatterns event A, P.eventProbability (cylinderEvent A a) ≤ b) :
    P.eventProbability event ≤ (eventPatterns event A).card * b := by
  rw [P.eventProbability_eq_sum_patterns hsupport]
  simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hbound

/-- An upper success tail with a threshold scaled by a possibly larger
untrimmed size. There is no assumption that the event is nonempty. -/
theorem probability_successCountAtLeast_le
    (P : FiniteBernoulliProduct Ω) (A : Finset Ω) (Nfull : ℕ)
    {beta q : ℝ} (hbeta : 0 ≤ beta) (hbetaHalf : beta ≤ 1 / 2)
    (hq : 0 < q) (hqOne : q ≤ 1)
    (hprob : ∀ e ∈ A, P.probability e ≤ q) (hfull : A.card ≤ Nfull) :
    P.eventProbability (successCountAtLeast A ((1 - beta) * Nfull)) ≤
      Real.exp ((Real.binEntropy beta + (1 - beta) * Real.log q) * Nfull) := by
  classical
  let E := eventPatterns (successCountAtLeast A ((1 - beta) * Nfull)) A
  have hmem (a : Finset Ω) : a ∈ E ↔ a ⊆ A ∧ (1 - beta) * Nfull ≤ (a.card : ℝ) := by
    simp only [E, eventPatterns_successCountAtLeast, Finset.mem_filter, Finset.mem_powerset]
  have hfullR : (A.card : ℝ) ≤ Nfull := by exact_mod_cast hfull
  have hcomp : E.card ≤ (smallPatterns A beta).card := by
    apply Finset.card_le_card_of_injOn (fun a ↦ A \ a)
    · intro a ha
      obtain ⟨haA, har⟩ := (hmem a).mp ha
      have hc : ((A \ a).card : ℝ) + a.card = A.card := by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card haA
      have ht := mul_le_mul_of_nonneg_left hfullR (show 0 ≤ 1 - beta by linarith)
      exact (mem_smallPatterns A _ beta).mpr ⟨Finset.sdiff_subset, by nlinarith⟩
    · intro a ha b hb hab
      obtain ⟨haA, _⟩ := (hmem a).mp ha
      obtain ⟨hbA, _⟩ := (hmem b).mp hb
      ext e
      have he := Finset.ext_iff.mp hab e
      simp only [Finset.mem_sdiff] at he
      by_cases heA : e ∈ A
      · simpa only [heA, true_and, not_iff_not] using he
      · have hea : e ∉ a := fun h ↦ heA (haA h)
        have heb : e ∉ b := fun h ↦ heA (hbA h)
        simp [hea, heb]
  have hcard : (E.card : ℝ) ≤ Real.exp (Nfull * Real.binEntropy beta) := by
    apply (show (E.card : ℝ) ≤ (smallPatterns A beta).card by exact_mod_cast hcomp).trans
    apply (card_smallPatterns_le_exp_binEntropy A hbeta hbetaHalf).trans
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hfullR
      (Real.binEntropy_nonneg hbeta (by linarith)))
  have hlog : Real.log q ≤ 0 := Real.log_nonpos hq.le hqOne
  have hmass : ∀ a ∈ E, P.eventProbability (cylinderEvent A a) ≤
      Real.exp (Real.log q * ((1 - beta) * Nfull)) := by
    intro a ha
    obtain ⟨haA, har⟩ := (hmem a).mp ha
    exact (cylinderEvent_probability_le_exp_successes P haA hq hprob).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left har hlog))
  calc
    _ ≤ E.card * Real.exp (Real.log q * ((1 - beta) * Nfull)) :=
      P.eventProbability_le_card_patterns_mul (successCountAtLeast_supportedOn _ _) hmass
    _ ≤ Real.exp (Nfull * Real.binEntropy beta) *
        Real.exp (Real.log q * ((1 - beta) * Nfull)) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- A lower success tail whose threshold is expressed in the untrimmed
size. The entropy radius and missing-coordinate loss both retain `xi`. -/
theorem probability_successCountAtMost_le
    (P : FiniteBernoulliProduct Ω) (A : Finset Ω) (Nfull : ℕ)
    {beta xi q : ℝ} (hbeta : 0 ≤ beta) (hxi : xi < 1)
    (hband : beta / (1 - xi) ≤ 1 / 2) (hq : 0 ≤ q) (hqOne : q < 1)
    (hprob : ∀ e ∈ A, q ≤ P.probability e)
    (hfull : A.card ≤ Nfull) (htrim : (1 - xi) * Nfull ≤ (A.card : ℝ)) :
    P.eventProbability (successCountAtMost A (beta * Nfull)) ≤
      Real.exp ((Real.binEntropy (beta / (1 - xi)) +
        (1 - xi - beta) * Real.log (1 - q)) * Nfull) := by
  classical
  let E := eventPatterns (successCountAtMost A (beta * Nfull)) A
  have hmem (a : Finset Ω) : a ∈ E ↔ a ⊆ A ∧ (a.card : ℝ) ≤ beta * Nfull := by
    simp only [E, eventPatterns_successCountAtMost, Finset.mem_filter, Finset.mem_powerset]
  have hden : 0 < 1 - xi := by linarith
  have ht : 0 ≤ beta / (1 - xi) := div_nonneg hbeta hden.le
  have hsubset : E ⊆ smallPatterns A (beta / (1 - xi)) := by
    intro a ha
    obtain ⟨haA, har⟩ := (hmem a).mp ha
    apply (mem_smallPatterns A a _).mpr
    refine ⟨haA, har.trans ?_⟩
    calc
      beta * Nfull = beta / (1 - xi) * ((1 - xi) * Nfull) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left htrim ht
  have hcard : (E.card : ℝ) ≤ Real.exp (Nfull * Real.binEntropy (beta / (1 - xi))) := by
    apply (show (E.card : ℝ) ≤ (smallPatterns A (beta / (1 - xi))).card by
      exact_mod_cast Finset.card_le_card hsubset).trans
    apply (card_smallPatterns_le_exp_binEntropy A ht hband).trans
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (show (A.card : ℝ) ≤ Nfull by exact_mod_cast hfull)
      (Real.binEntropy_nonneg ht (by linarith)))
  have hlog : Real.log (1 - q) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hmass : ∀ a ∈ E, P.eventProbability (cylinderEvent A a) ≤
      Real.exp (Real.log (1 - q) * ((1 - xi - beta) * Nfull)) := by
    intro a ha
    obtain ⟨haA, har⟩ := (hmem a).mp ha
    have hc : ((A \ a).card : ℝ) + a.card = A.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card haA
    have hf : (1 - xi - beta) * Nfull ≤ ((A \ a).card : ℝ) := by nlinarith
    exact (cylinderEvent_probability_le_exp_failures P haA hqOne hprob).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hf hlog))
  calc
    _ ≤ E.card * Real.exp (Real.log (1 - q) * ((1 - xi - beta) * Nfull)) :=
      P.eventProbability_le_card_patterns_mul (successCountAtMost_supportedOn _ _) hmass
    _ ≤ Real.exp (Nfull * Real.binEntropy (beta / (1 - xi))) *
        Real.exp (Real.log (1 - q) * ((1 - xi - beta) * Nfull)) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end DenseGraph.FiniteBernoulliProduct
