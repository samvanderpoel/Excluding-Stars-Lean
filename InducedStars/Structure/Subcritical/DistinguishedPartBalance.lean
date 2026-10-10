import InducedStars.Structure.Subcritical.OneComponentCapacity

/-!
# Part balance forced by a feasible distinguished level

Paper: the preliminary geometry in `lemma:sub-combined`. The support-size
information alone does not imply balance. Here the unchanged wide level's
exact edge equation supplies the missing nonnegative imbalance penalty.
The geometry concerns the actual single-core retained key.
-/

noncomputable section
open Finset Set
open scoped Classical BigOperators
namespace InducedStars

/-- The exact count equation bounds the squared imbalance. The remainder
edge count is nonnegative, and is not silently discarded from an equality. -/
theorem oneCompleteCore_part_deviation_of_level {k n m b : ℕ} (hk : 3 ≤ k)
    (D : SubcriticalDivision k (Fin n)) (hcount : D.componentCount = 1)
    (hcore : ∀ i, D.core i = RegularBlockCore.complete k hk)
    {delta : ℝ} (hd : 0 ≤ delta)
    (v : RetainedEdgeCountVector D 0 (Fintype.card (Fin n)))
    (hv : v ∈ retainedEdgeCountLevel D 0 (Fintype.card (Fin n)) m delta (b : ℤ))
    (a : D.PartIndex) :
    (1 - pK k) * (((D.part a).card : ℝ) - D.support.card / (k - 1 : ℕ)) ^ 2 ≤
      2 * (m : ℝ) - gammaK k * (D.support.card : ℝ)^2 +
        2 * delta * (D.support.card : ℝ)^2 + D.support.card := by
  have hp : 0 < 1 - pK k := sub_pos.mpr (pK_lt_one (by omega))
  have hid : (retainedCliqueCapacity D 0 (Fintype.card (Fin n)) : ℝ) +
      retainedEdgeCountTotal v + b = m := by
    exact_mod_cast (mem_retainedEdgeCountLevel.mp hv).1
  have hlo : (pK k - 2 * delta) * retainedActiveTotalCapacity D 0 (Fintype.card (Fin n)) ≤
      (retainedEdgeCountTotal v : ℝ) := by
    rw [retainedActiveTotalCapacity, retainedEdgeCountTotal, Nat.cast_sum,
      Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    have hN : (0 : ℝ) < retainedActiveCapacity D 0 (Fintype.card (Fin n)) e := by
      exact_mod_cast retainedActiveCapacity_pos D 0 _ e
    exact (le_div_iff₀ hN).mp ((mem_retainedEdgeCountLevel.mp hv).2 e).1
  have hcap : (retainedCliqueCapacity D 0 (Fintype.card (Fin n)) : ℝ) +
      retainedActiveTotalCapacity D 0 (Fintype.card (Fin n)) =
      (D.support.card : ℝ) * (D.support.card - 1) / 2 := by
    have h := congrArg (Nat.cast (R := ℝ)) (oneCompleteCore_capacity_add hk D hcount hcore)
    simpa only [Nat.cast_add, Nat.cast_choose_two] using h
  have hA : (2 : ℝ) * retainedActiveTotalCapacity D 0 (Fintype.card (Fin n)) ≤
      (D.support.card : ℝ)^2 := by
    have hc : (0 : ℝ) ≤ retainedCliqueCapacity D 0 (Fintype.card (Fin n)) := by positivity
    have hq : (0 : ℝ) ≤ D.support.card := by positivity
    nlinarith
  have hs := Finset.single_le_sum (s := Finset.univ) (a := a)
    (fun a _ ↦ sq_nonneg (((D.part a).card : ℝ) - D.support.card / (k - 1 : ℕ)))
    (Finset.mem_univ a)
  have hm := mul_le_mul_of_nonneg_left hs hp.le
  rw [oneCompleteCore_variance_identity hk D hcount hcore] at hm
  have hmul := mul_le_mul_of_nonneg_left hA hd
  have hb : (0 : ℝ) ≤ b := by positivity
  nlinarith [hid, hlo, hmul]

/-- Explicit finite part lower bound. Compatibility is used only through
the support error; the substantive balance information comes from `hv`.
The displayed reserve is a routine scalar smallness/large-order condition. -/
theorem oneCompleteCore_part_lower_of_level {k n m b : ℕ} (hk : 3 ≤ k)
    (hn : 1 ≤ n) (D : SubcriticalDivision k (Fin n))
    (hcount : D.componentCount = 1)
    (hcore : ∀ i, D.core i = RegularBlockCore.complete k hk)
    {mu delta : ℝ} (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (hd : 0 ≤ delta) (hdmu : delta ≤ mu / 2)
    (hsupport : |(D.support.card : ℝ) - mu * n| ≤ delta * n)
    (hm : 2 * (m : ℝ) ≤ gammaK k * mu^2 * (n : ℝ)^2 + delta * (n : ℝ)^2)
    (hlarge : 5 * delta * (n : ℝ)^2 + n ≤
      (1 - pK k) * (mu * n / (4 * (k - 1 : ℕ)))^2)
    (v : RetainedEdgeCountVector D 0 (Fintype.card (Fin n)))
    (hv : v ∈ retainedEdgeCountLevel D 0 (Fintype.card (Fin n)) m delta (b : ℤ)) :
    ∀ a : D.PartIndex,
      (D.support.card : ℝ) / (2 * (k - 1 : ℕ)) ≤ (D.part a).card ∧
      mu / (4 * (k - 1 : ℕ)) * n ≤ ((D.part a).card : ℝ) := by
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq0 : (0 : ℝ) ≤ D.support.card := by positivity
  have hqn : (D.support.card : ℝ) ≤ n := by
    exact_mod_cast (show D.support.card ≤ n by simpa using Finset.card_le_univ D.support)
  have hqlo : mu * n / 2 ≤ (D.support.card : ℝ) := by
    have h := (abs_le.mp hsupport).1
    have hd' := mul_le_mul_of_nonneg_right hdmu hnR.le
    nlinarith
  have hmuN : mu * n ≤ (n : ℝ) := by nlinarith
  have hsquare : mu^2 * (n : ℝ)^2 - (D.support.card : ℝ)^2 ≤
      2 * delta * (n : ℝ)^2 := by
    have h1 := mul_nonneg
      (show 0 ≤ delta * n - (mu * n - D.support.card) by
        have h := (abs_le.mp hsupport).1; linarith)
      (show 0 ≤ mu * n + D.support.card by positivity)
    have h2 := mul_nonneg (show 0 ≤ delta * n by positivity)
      (show 0 ≤ 2 * n - (mu * n + D.support.card) by linarith)
    nlinarith
  have hg := gammaK_pos hk
  have hg1 := gammaK_lt_one hk
  have hgamma : gammaK k * mu^2 * (n : ℝ)^2 - gammaK k * (D.support.card : ℝ)^2 ≤
      2 * delta * (n : ℝ)^2 := by
    have h1 := mul_le_mul_of_nonneg_left hsquare hg.le
    have h2 := mul_nonneg (show 0 ≤ 1 - gammaK k by linarith)
      (show 0 ≤ 2 * delta * (n : ℝ)^2 by positivity)
    nlinarith
  have hq2 : (D.support.card : ℝ)^2 ≤ (n : ℝ)^2 := sq_le_sq₀ hq0 hnR.le |>.2 hqn
  have hdq := mul_le_mul_of_nonneg_left hq2 (show 0 ≤ 2 * delta by positivity)
  intro a
  have hdev := oneCompleteCore_part_deviation_of_level hk D hcount hcore hd v hv a
  have hbound : (1 - pK k) *
      (((D.part a).card : ℝ) - D.support.card / (k - 1 : ℕ))^2 ≤
      (1 - pK k) * (mu * n / (4 * (k - 1 : ℕ)))^2 := by
    nlinarith [hdev, hm, hgamma, hdq, hlarge]
  have hp : 0 < 1 - pK k := sub_pos.mpr (pK_lt_one (by omega))
  have habs := abs_le_of_sq_le_sq ((mul_le_mul_iff_right₀ hp).mp hbound)
    (show 0 ≤ mu * n / (4 * (k - 1 : ℕ)) by positivity)
  have hlow : mu * n / (2 * (k - 1 : ℕ)) ≤ D.support.card / (k - 1 : ℕ) := by
    simpa only [div_div] using (div_le_div_iff_of_pos_right hr).2 hqlo
  have heq : mu * n / (2 * (k - 1 : ℕ)) =
      2 * (mu * n / (4 * (k - 1 : ℕ))) := by ring
  have h := (abs_le.mp habs).1
  constructor
  · rw [show (D.support.card : ℝ) / (2 * (k - 1 : ℕ)) =
      (D.support.card : ℝ) / (k - 1 : ℕ) / 2 by ring]
    linarith
  · rw [show mu / (4 * (k - 1 : ℕ)) * n = mu * n / (4 * (k - 1 : ℕ)) by ring]
    linarith

end InducedStars
