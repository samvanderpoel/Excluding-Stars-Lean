import InducedStars.Analysis.Entropy
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Scalar optimization

The elementary real-analysis layer behind the fixed-density graphon problem:
the critical probability and density, the explicit entropy and rate profiles,
and the paper's two-variable entropy maximization.
-/

namespace InducedStars

open Set

/-- The real parameter `Δ = k - 2` used throughout the scalar problem. -/
def deltaK (k : ℕ) : ℝ := (k - 2 : ℕ)

lemma deltaK_pos {k : ℕ} (hk : 3 ≤ k) : 0 < deltaK k := by
  dsimp [deltaK]
  exact_mod_cast (show 0 < k - 2 by omega)

lemma kSubOne_pos {k : ℕ} (hk : 3 ≤ k) : (0 : ℝ) < (k - 1 : ℕ) := by
  exact_mod_cast (show 0 < k - 1 by omega)

lemma deltaK_add_one {k : ℕ} (hk : 3 ≤ k) : deltaK k + 1 = (k - 1 : ℕ) := by
  dsimp [deltaK]
  norm_num [Nat.cast_sub (show 2 ≤ k by omega), Nat.cast_sub (show 1 ≤ k by omega)]
  ring

private theorem exists_criticalRoot (k : ℕ) :
    ∃ p : ℝ, p ∈ Icc 0 1 ∧ p = (1 - p) ^ (k - 1) := by
  let f : ℝ → ℝ := fun p ↦ p - (1 - p) ^ (k - 1)
  have hf : Continuous f := by fun_prop
  have hz : (0 : ℝ) ∈ Icc (f 0) (f 1) := by
    dsimp [f]
    by_cases hk : k - 1 = 0
    · simp [hk]
    · simp [hk]
  obtain ⟨p, hp, hp0⟩ :=
    (intermediate_value_Icc (a := (0 : ℝ)) (b := 1) zero_le_one hf.continuousOn) hz
  refine ⟨p, hp, ?_⟩
  dsimp [f] at hp0
  linarith

/-- The proof-independent critical probability `p_k`. -/
noncomputable def pK (k : ℕ) : ℝ := Classical.choose (exists_criticalRoot k)

theorem pK_mem_Icc (k : ℕ) : pK k ∈ Icc (0 : ℝ) 1 :=
  (Classical.choose_spec (exists_criticalRoot k)).1

/-- The defining equation `p_k = (1-p_k)^(k-1)`. -/
theorem pK_equation (k : ℕ) : pK k = (1 - pK k) ^ (k - 1) :=
  (Classical.choose_spec (exists_criticalRoot k)).2

theorem pK_unique_Icc (k : ℕ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (heq : p = (1 - p) ^ (k - 1)) : p = pK k := by
  apply le_antisymm
  · by_contra hnot
    have hpkp : pK k < p := lt_of_not_ge hnot
    have hbase : 1 - p ≤ 1 - pK k := by linarith
    have hpow : (1 - p) ^ (k - 1) ≤ (1 - pK k) ^ (k - 1) :=
      pow_le_pow_left₀ (by linarith [hp.2]) hbase _
    rw [← heq, ← pK_equation] at hpow
    exact (not_le_of_gt hpkp) hpow
  · by_contra hnot
    have hppk : p < pK k := lt_of_not_ge hnot
    have hbase : 1 - pK k ≤ 1 - p := by linarith
    have hpow : (1 - pK k) ^ (k - 1) ≤ (1 - p) ^ (k - 1) :=
      pow_le_pow_left₀ (by linarith [(pK_mem_Icc k).2]) hbase _
    rw [← pK_equation, ← heq] at hpow
    exact (not_le_of_gt hppk) hpow

theorem pK_pos {k : ℕ} (_hk : 2 ≤ k) : 0 < pK k := by
  refine lt_of_le_of_ne (pK_mem_Icc k).1 (Ne.symm ?_)
  intro hp0
  have h := pK_equation k
  simp [hp0] at h

theorem pK_lt_one {k : ℕ} (hk : 2 ≤ k) : pK k < 1 := by
  have hnonzero : k - 1 ≠ 0 := by omega
  refine lt_of_le_of_ne (pK_mem_Icc k).2 ?_
  intro hp1
  have h := pK_equation k
  simp [hp1, hnonzero] at h

theorem pK_mem_Ioo {k : ℕ} (hk : 2 ≤ k) : pK k ∈ Ioo (0 : ℝ) 1 :=
  ⟨pK_pos hk, pK_lt_one hk⟩

/-- Uniqueness of the critical probability in the paper's parameter range. -/
theorem pK_unique {k : ℕ} (_hk : 2 ≤ k) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (heq : p = (1 - p) ^ (k - 1)) : p = pK k :=
  pK_unique_Icc k ⟨hp.1.le, hp.2.le⟩ heq

/-- Existence and uniqueness in the exact form used to characterize `pK`. -/
theorem existsUnique_criticalProbability (k : ℕ) (hk : 2 ≤ k) :
    ∃! p : ℝ, p ∈ Ioo (0 : ℝ) 1 ∧ p = (1 - p) ^ (k - 1) := by
  refine ⟨pK k, ⟨pK_mem_Ioo hk, pK_equation k⟩, ?_⟩
  intro p hp
  exact pK_unique hk hp.1 hp.2

theorem pK_eq_iff {k : ℕ} {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    p = pK k ↔ p = (1 - p) ^ (k - 1) := by
  constructor
  · rintro rfl
    exact pK_equation k
  · exact pK_unique_Icc k hp

theorem lt_pK_iff_lt_pow {k : ℕ} (hk : 2 ≤ k) {p : ℝ} (hp1 : p < 1) :
    p < pK k ↔ p < (1 - p) ^ (k - 1) := by
  constructor
  · intro hp
    have hn : k - 1 ≠ 0 := by omega
    have hbase : 1 - pK k < 1 - p := by linarith
    have hpow : (1 - pK k) ^ (k - 1) < (1 - p) ^ (k - 1) :=
      pow_lt_pow_left₀ hbase (by linarith [(pK_mem_Icc k).2]) hn
    rw [← pK_equation] at hpow
    exact hp.trans hpow
  · intro hsign
    by_contra hnot
    have hpkp : pK k ≤ p := le_of_not_gt hnot
    have hbase : 1 - p ≤ 1 - pK k := by linarith
    have hpow : (1 - p) ^ (k - 1) ≤ (1 - pK k) ^ (k - 1) :=
      pow_le_pow_left₀ (by linarith) hbase _
    rw [← pK_equation] at hpow
    exact (not_lt_of_ge hpkp) (hsign.trans_le hpow)

theorem pK_lt_iff_pow_lt {k : ℕ} (hk : 2 ≤ k) {p : ℝ} (hp1 : p < 1) :
    pK k < p ↔ (1 - p) ^ (k - 1) < p := by
  constructor
  · intro hp
    have hn : k - 1 ≠ 0 := by omega
    have hbase : 1 - p < 1 - pK k := by linarith
    have hpow : (1 - p) ^ (k - 1) < (1 - pK k) ^ (k - 1) :=
      pow_lt_pow_left₀ hbase (by linarith) hn
    rw [← pK_equation] at hpow
    exact hpow.trans hp
  · intro hsign
    by_contra hnot
    have hppk : p ≤ pK k := le_of_not_gt hnot
    have hbase : 1 - pK k ≤ 1 - p := by linarith
    have hpow : (1 - pK k) ^ (k - 1) ≤ (1 - p) ^ (k - 1) :=
      pow_le_pow_left₀ (by linarith [(pK_mem_Icc k).2]) hbase _
    rw [← pK_equation] at hpow
    exact (not_lt_of_ge hppk) (hpow.trans_lt hsign)

theorem log_pK_eq (k : ℕ) :
    Real.log (pK k) = ((k - 1 : ℕ) : ℝ) * Real.log (1 - pK k) := by
  calc
    Real.log (pK k) = Real.log ((1 - pK k) ^ (k - 1)) :=
      congrArg Real.log (pK_equation k)
    _ = ((k - 1 : ℕ) : ℝ) * Real.log (1 - pK k) := Real.log_pow _ _

theorem log2_pK_eq (k : ℕ) :
    log2 (pK k) = ((k - 1 : ℕ) : ℝ) * log2 (1 - pK k) := by
  rw [log2, log2, log_pK_eq]
  ring

theorem log_one_sub_div_pK {k : ℕ} (hk : 2 ≤ k) :
    Real.log ((1 - pK k) / pK k) =
      -((k - 2 : ℕ) : ℝ) * Real.log (1 - pK k) := by
  have hp0 : pK k ≠ 0 := (pK_pos hk).ne'
  have hq0 : 1 - pK k ≠ 0 := by linarith [pK_lt_one hk]
  rw [Real.log_div hq0 hp0, log_pK_eq k]
  norm_num [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_sub hk]
  ring

/-- The natural-log expression controlling the reduced objective's derivative. -/
noncomputable def criticalLogBalance (k : ℕ) (p : ℝ) : ℝ :=
  ((k - 1 : ℕ) : ℝ) * Real.log (1 - p) - Real.log p

@[simp] theorem criticalLogBalance_pK (k : ℕ) :
    criticalLogBalance k (pK k) = 0 := by
  rw [criticalLogBalance, ← log_pK_eq k]
  ring

theorem criticalLogBalance_pos {k : ℕ} (hk : 2 ≤ k) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hlt : p < pK k) : 0 < criticalLogBalance k p := by
  have hroot : p < (1 - p) ^ (k - 1) := (lt_pK_iff_lt_pow hk hp.2).mp hlt
  have hlog : Real.log p < Real.log ((1 - p) ^ (k - 1)) :=
    Real.log_lt_log hp.1 hroot
  rw [Real.log_pow] at hlog
  exact sub_pos.mpr hlog

theorem criticalLogBalance_neg {k : ℕ} (hk : 2 ≤ k) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hlt : pK k < p) : criticalLogBalance k p < 0 := by
  have hroot : (1 - p) ^ (k - 1) < p := (pK_lt_iff_pow_lt hk hp.2).mp hlt
  have hpowpos : 0 < (1 - p) ^ (k - 1) := pow_pos (sub_pos.mpr hp.2) _
  have hlog : Real.log ((1 - p) ^ (k - 1)) < Real.log p :=
    Real.log_lt_log hpowpos hroot
  rw [Real.log_pow] at hlog
  exact sub_neg.mpr hlog

/-- The critical edge density `(1 + (k-2) p_k)/(k-1)`. -/
noncomputable def gammaK (k : ℕ) : ℝ :=
  (1 + (k - 2 : ℕ) * pK k) / (k - 1 : ℕ)

theorem gammaK_pos {k : ℕ} (hk : 3 ≤ k) : 0 < gammaK k := by
  have hd : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hn : (0 : ℝ) < 1 + (k - 2 : ℕ) * pK k := by
    have hp := pK_pos (show 2 ≤ k by omega)
    positivity
  exact div_pos hn hd

theorem gammaK_lt_one {k : ℕ} (hk : 3 ≤ k) : gammaK k < 1 := by
  have hdelta : (0 : ℝ) < (k - 2 : ℕ) := by
    exact_mod_cast (show 0 < k - 2 by omega)
  have hp := pK_lt_one (show 2 ≤ k by omega)
  have hmul : ((k - 2 : ℕ) : ℝ) * pK k < ((k - 2 : ℕ) : ℝ) := by nlinarith
  have hden : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  rw [gammaK, div_lt_one hden]
  norm_num [Nat.cast_sub (show 2 ≤ k by omega), Nat.cast_sub (show 1 ≤ k by omega)] at hmul ⊢
  linarith

theorem gammaK_mem_Ioo {k : ℕ} (hk : 3 ≤ k) : gammaK k ∈ Ioo (0 : ℝ) 1 :=
  ⟨gammaK_pos hk, gammaK_lt_one hk⟩

theorem gammaK_mul_sub_one_div (k : ℕ) (hk : 3 ≤ k) :
    (gammaK k * (k - 1 : ℕ) - 1) / (k - 2 : ℕ) = pK k := by
  have hd1 : ((k - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show k - 1 ≠ 0 by omega)
  have hd2 : ((k - 2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show k - 2 ≠ 0 by omega)
  rw [gammaK]
  field_simp [hd1, hd2]
  ring

theorem gammaK_mul_denominator (k : ℕ) (hk : 3 ≤ k) :
    gammaK k * (k - 1 : ℕ) = 1 + (k - 2 : ℕ) * pK k := by
  have hd1 : ((k - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show k - 1 ≠ 0 by omega)
  rw [gammaK]
  field_simp [hd1]

theorem gammaK_div_one_add (k : ℕ) (hk : 3 ≤ k) :
    gammaK k / (1 + (k - 2 : ℕ) * pK k) = 1 / (k - 1 : ℕ) := by
  have hd1 : ((k - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show k - 1 ≠ 0 by omega)
  have hn : 1 + ((k - 2 : ℕ) : ℝ) * pK k ≠ 0 := by
    have hp := pK_pos (show 2 ≤ k by omega)
    positivity
  rw [gammaK]
  field_simp [hd1, hn]

theorem gammaK_delta_mul_div_one_add (k : ℕ) (hk : 3 ≤ k) :
    (k - 2 : ℕ) * gammaK k / (1 + (k - 2 : ℕ) * pK k) =
      (k - 2 : ℕ) / (k - 1 : ℕ) := by
  rw [mul_div_assoc, gammaK_div_one_add k hk]
  ring

theorem pK_ge_phaseLower_iff {k : ℕ} (hk : 3 ≤ k) (γ : ℝ) :
    (γ * (k - 1 : ℕ) - 1) / (k - 2 : ℕ) ≤ pK k ↔ γ ≤ gammaK k := by
  have hd : (0 : ℝ) < (k - 2 : ℕ) := by
    exact_mod_cast (show 0 < k - 2 by omega)
  have he : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  rw [gammaK, div_le_iff₀ hd, le_div_iff₀ he]
  constructor <;> intro h <;> nlinarith

/-- The lower-density formula in the paper's entropy profile. -/
noncomputable def entropyDensityLower (k : ℕ) (γ : ℝ) : ℝ :=
  ((k - 2 : ℕ) * γ / (1 + (k - 2 : ℕ) * pK k)) * binaryEntropy (pK k)

/-- The upper-density formula in the paper's entropy profile. -/
noncomputable def entropyDensityUpper (k : ℕ) (γ : ℝ) : ℝ :=
  (1 - 1 / (k - 1 : ℕ)) *
    binaryEntropy (((k - 1 : ℕ) * γ - 1) / (k - 2 : ℕ))

/-- The paper's explicit entropy-density function `𝓔_k`. -/
noncomputable def entropyDensity (k : ℕ) (γ : ℝ) : ℝ :=
  if γ ≤ gammaK k then entropyDensityLower k γ else entropyDensityUpper k γ

theorem entropyDensity_of_le {k : ℕ} {γ : ℝ} (hγ : γ ≤ gammaK k) :
    entropyDensity k γ = entropyDensityLower k γ := by
  simp [entropyDensity, hγ]

theorem entropyDensity_pieces_agree (k : ℕ) (hk : 3 ≤ k) :
    entropyDensityLower k (gammaK k) = entropyDensityUpper k (gammaK k) := by
  rw [entropyDensityLower, entropyDensityUpper]
  have harg :
      (((k - 1 : ℕ) : ℝ) * gammaK k - 1) / (k - 2 : ℕ) = pK k := by
    rw [mul_comm]
    exact gammaK_mul_sub_one_div k hk
  rw [harg]
  have hd1 : ((k - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show k - 1 ≠ 0 by omega)
  rw [gammaK_delta_mul_div_one_add k hk]
  congr 1
  field_simp [hd1]
  norm_num [Nat.cast_sub (show 2 ≤ k by omega), Nat.cast_sub (show 1 ≤ k by omega)]
  ring

@[simp] theorem entropyDensity_at_gammaK (k : ℕ) :
    entropyDensity k (gammaK k) = entropyDensityLower k (gammaK k) := by
  simp [entropyDensity]

theorem entropyDensity_of_ge {k : ℕ} (hk : 3 ≤ k) {γ : ℝ} (hγ : gammaK k ≤ γ) :
    entropyDensity k γ = entropyDensityUpper k γ := by
  rcases hγ.eq_or_lt with rfl | hγ
  · calc
      entropyDensity k (gammaK k) = entropyDensityLower k (gammaK k) :=
        entropyDensity_at_gammaK k
      _ = entropyDensityUpper k (gammaK k) := entropyDensity_pieces_agree k hk
  · simp [entropyDensity, not_le_of_gt hγ]

/-- The paper's explicit large-deviation rate function `𝓡_k`. -/
noncomputable def rateFunction (k : ℕ) (p : ℝ) : ℝ :=
  if p ≤ pK k then log2 (1 / (1 - p)) else (1 / (k - 1 : ℕ)) * log2 (1 / p)

theorem rateFunction_of_le {k : ℕ} {p : ℝ} (hp : p ≤ pK k) :
    rateFunction k p = log2 (1 / (1 - p)) := by
  simp [rateFunction, hp]

theorem rateFunction_pieces_agree (k : ℕ) (hk : 2 ≤ k) :
    log2 (1 / (1 - pK k)) = (1 / (k - 1 : ℕ)) * log2 (1 / pK k) := by
  have hd : ((k - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show k - 1 ≠ 0 by omega)
  simp only [one_div]
  rw [log2_inv, log2_inv, log2_pK_eq]
  field_simp [hd]

theorem rateFunction_of_ge {k : ℕ} (hk : 2 ≤ k) {p : ℝ} (hp : pK k ≤ p) :
    rateFunction k p = (1 / (k - 1 : ℕ)) * log2 (1 / p) := by
  rcases hp.eq_or_lt with rfl | hp
  · rw [rateFunction_of_le le_rfl, rateFunction_pieces_agree k hk]
  · simp [rateFunction, not_le_of_gt hp]

/-! ## The scalar feasible set and objective -/

/--
The intended feasible region of Paper Lemma `lemma:k1k-calc-prob`.

The quotient constraints are represented without division as
`x ≤ γ ≤ x + y`, and `y` is strictly positive.  This makes the ordinary
real-analysis domain explicit instead of admitting Lean's totalized `y = 0`
values.
-/
structure ScalarFeasible (k : ℕ) (γ x y : ℝ) : Prop where
  x_nonneg : 0 ≤ x
  x_le_one : x ≤ 1
  y_pos : 0 < y
  y_le_one_sub_x : y ≤ 1 - x
  y_le_delta_mul_x : y ≤ deltaK k * x
  x_le_gamma : x ≤ γ
  gamma_le_x_add_y : γ ≤ x + y

/-- The quotient occurring in the scalar entropy objective. -/
noncomputable def scalarRatio (γ x y : ℝ) : ℝ := (γ - x) / y

/-- The objective in Paper Lemma `lemma:k1k-calc-prob`. -/
noncomputable def scalarObjective (γ x y : ℝ) : ℝ :=
  y * binaryEntropy (scalarRatio γ x y)

theorem scalarObjective_eq_entropyPerspective (γ x y : ℝ) :
    scalarObjective γ x y = entropyPerspective (γ - x) y := by
  rfl

/-- For fixed `x`, the objective is nondecreasing in the allowed `y` range. -/
theorem scalarObjective_mono_y {γ x y₁ y₂ : ℝ}
    (hnum : 0 ≤ γ - x) (hy₁ : 0 < y₁) (hnum_le : γ - x ≤ y₁) (hyy : y₁ ≤ y₂) :
    scalarObjective γ x y₁ ≤ scalarObjective γ x y₂ := by
  rw [scalarObjective_eq_entropyPerspective, scalarObjective_eq_entropyPerspective]
  exact entropyPerspective_mono hnum hy₁ hnum_le hyy

/-- Strictness in `y` holds exactly away from the zero-numerator degeneracy. -/
theorem scalarObjective_strictMono_y {γ x y₁ y₂ : ℝ}
    (hnum : 0 < γ - x) (hy₁ : 0 < y₁) (hnum_le : γ - x ≤ y₁) (hyy : y₁ < y₂) :
    scalarObjective γ x y₁ < scalarObjective γ x y₂ := by
  rw [scalarObjective_eq_entropyPerspective, scalarObjective_eq_entropyPerspective]
  exact entropyPerspective_strictMono hnum hy₁ hnum_le hyy

theorem scalarObjective_y_eq_iff {γ x y₁ y₂ : ℝ}
    (hnum : 0 ≤ γ - x) (hy₁ : 0 < y₁) (hnum_le : γ - x ≤ y₁) (hyy : y₁ ≤ y₂) :
    scalarObjective γ x y₁ = scalarObjective γ x y₂ ↔ γ - x = 0 ∨ y₁ = y₂ := by
  rw [scalarObjective_eq_entropyPerspective, scalarObjective_eq_entropyPerspective]
  exact entropyPerspective_eq_iff hnum hy₁ hnum_le hyy

theorem ScalarFeasible.ratio_nonneg {k : ℕ} {γ x y : ℝ}
    (h : ScalarFeasible k γ x y) : 0 ≤ scalarRatio γ x y := by
  rw [scalarRatio]
  exact div_nonneg (sub_nonneg.mpr h.x_le_gamma) h.y_pos.le

theorem ScalarFeasible.ratio_le_one {k : ℕ} {γ x y : ℝ}
    (h : ScalarFeasible k γ x y) : scalarRatio γ x y ≤ 1 := by
  rw [scalarRatio, div_le_one h.y_pos]
  linarith [h.gamma_le_x_add_y]

theorem ScalarFeasible.ratio_mem_Icc {k : ℕ} {γ x y : ℝ}
    (h : ScalarFeasible k γ x y) : scalarRatio γ x y ∈ Icc (0 : ℝ) 1 :=
  ⟨h.ratio_nonneg, h.ratio_le_one⟩

theorem ScalarFeasible.x_eq_gamma_sub {k : ℕ} {γ x y : ℝ}
    (h : ScalarFeasible k γ x y) : x = γ - y * scalarRatio γ x y := by
  rw [scalarRatio]
  field_simp [h.y_pos.ne']
  ring

/-- Coordinates on the saturated boundary `y = (k-2)x`, after the paper's
change of variables `p = (γ-x)/y`. -/
theorem ScalarFeasible.deltaBoundary_coordinates {k : ℕ} {γ x y : ℝ}
    (h : ScalarFeasible k γ x y) (hy : y = deltaK k * x) :
    x = γ / (1 + deltaK k * scalarRatio γ x y) ∧
      y = deltaK k * γ / (1 + deltaK k * scalarRatio γ x y) := by
  let p := scalarRatio γ x y
  have hp : 0 ≤ p := h.ratio_nonneg
  have hd : 0 ≤ deltaK k := by simp [deltaK]
  have hden : 0 < 1 + deltaK k * p := by nlinarith [mul_nonneg hd hp]
  have hxsub : x = γ - y * p := h.x_eq_gamma_sub
  have hxmul : x * (1 + deltaK k * p) = γ := by
    nlinarith [hxsub, hy]
  have hx : x = γ / (1 + deltaK k * p) :=
    (eq_div_iff hden.ne').2 hxmul
  constructor
  · simpa only [p] using hx
  · calc
      y = deltaK k * x := hy
      _ = deltaK k * (γ / (1 + deltaK k * p)) := by rw [hx]
      _ = deltaK k * γ / (1 + deltaK k * p) := by ring
      _ = deltaK k * γ / (1 + deltaK k * scalarRatio γ x y) := by rfl

/-- The inverse direction of the `y = (k-2)x` change of variables. -/
theorem scalarRatio_deltaBoundary {k : ℕ} (hk : 3 ≤ k) {γ p : ℝ}
    (hγ : γ ≠ 0) (hp : 0 ≤ p) :
    scalarRatio γ
        (γ / (1 + deltaK k * p))
        (deltaK k * γ / (1 + deltaK k * p)) = p := by
  have hDelta : deltaK k ≠ 0 := (deltaK_pos hk).ne'
  have hden : 1 + deltaK k * p ≠ 0 := by
    have hd := deltaK_pos hk
    positivity
  rw [scalarRatio]
  field_simp [hγ, hDelta, hden]
  ring

theorem ScalarFeasible.delta_scale_mul_le {k : ℕ} {γ x y : ℝ}
    (h : ScalarFeasible k γ x y) :
    y * (1 + (k - 2 : ℕ) * scalarRatio γ x y) ≤ (k - 2 : ℕ) * γ := by
  have hy := h.y_le_delta_mul_x
  rw [h.x_eq_gamma_sub] at hy
  dsimp [deltaK] at hy
  nlinarith

theorem ScalarFeasible.delta_denominator_pos {k : ℕ} {γ x y : ℝ}
    (h : ScalarFeasible k γ x y) :
    0 < 1 + (k - 2 : ℕ) * scalarRatio γ x y := by
  have hdelta : (0 : ℝ) ≤ (k - 2 : ℕ) := by positivity
  have hp := h.ratio_nonneg
  positivity

theorem ScalarFeasible.y_le_delta_scale {k : ℕ} {γ x y : ℝ}
    (h : ScalarFeasible k γ x y) :
    y ≤ (k - 2 : ℕ) * γ / (1 + (k - 2 : ℕ) * scalarRatio γ x y) := by
  rw [le_div_iff₀ h.delta_denominator_pos]
  exact h.delta_scale_mul_le

theorem ScalarFeasible.complement_scale_mul_le {k : ℕ} {γ x y : ℝ}
    (h : ScalarFeasible k γ x y) :
    y * (1 - scalarRatio γ x y) ≤ 1 - γ := by
  have hy := h.y_le_one_sub_x
  rw [h.x_eq_gamma_sub] at hy
  nlinarith

theorem ScalarFeasible.y_le_complement_scale {k : ℕ} {γ x y : ℝ}
    (h : ScalarFeasible k γ x y) (hp : scalarRatio γ x y < 1) :
    y ≤ (1 - γ) / (1 - scalarRatio γ x y) := by
  rw [le_div_iff₀ (sub_pos.mpr hp)]
  exact h.complement_scale_mul_le

theorem scalarFeasible_iff_quotient {k : ℕ} {γ x y : ℝ} :
    ScalarFeasible k γ x y ↔
      0 ≤ x ∧ x ≤ 1 ∧ 0 < y ∧ y ≤ 1 - x ∧ y ≤ deltaK k * x ∧
        0 ≤ scalarRatio γ x y ∧ scalarRatio γ x y ≤ 1 := by
  constructor
  · intro h
    exact ⟨h.x_nonneg, h.x_le_one, h.y_pos, h.y_le_one_sub_x,
      h.y_le_delta_mul_x, h.ratio_nonneg, h.ratio_le_one⟩
  · rintro ⟨hx0, hx1, hy, hy1, hyD, hp0, hp1⟩
    have hxγ : x ≤ γ := by
      rw [scalarRatio, div_nonneg_iff] at hp0
      rcases hp0 with hp0 | hp0
      · linarith [hp0.1]
      · linarith [hp0.2, hy]
    have hγxy : γ ≤ x + y := by
      rw [scalarRatio, div_le_one hy] at hp1
      linarith
    exact ⟨hx0, hx1, hy, hy1, hyD, hxγ, hγxy⟩

/-- The lower endpoint in the reduced `p`-coordinate. -/
noncomputable def phaseLower (k : ℕ) (γ : ℝ) : ℝ :=
  (γ * (k - 1 : ℕ) - 1) / (k - 2 : ℕ)

@[simp] theorem phaseLower_at_gammaK (k : ℕ) (hk : 3 ≤ k) :
    phaseLower k (gammaK k) = pK k :=
  gammaK_mul_sub_one_div k hk

theorem phaseLower_le_pK_iff {k : ℕ} (hk : 3 ≤ k) (γ : ℝ) :
    phaseLower k γ ≤ pK k ↔ γ ≤ gammaK k :=
  pK_ge_phaseLower_iff hk γ

theorem pK_lt_phaseLower_iff {k : ℕ} (hk : 3 ≤ k) (γ : ℝ) :
    pK k < phaseLower k γ ↔ gammaK k < γ := by
  rw [← not_le, phaseLower_le_pK_iff hk, not_le]

theorem phaseLower_nonneg {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : gammaK k ≤ γ) : 0 ≤ phaseLower k γ := by
  rcases hγ.eq_or_lt with rfl | hγ
  · rw [phaseLower_at_gammaK k hk]
    exact (pK_pos (show 2 ≤ k by omega)).le
  · exact (pK_pos (show 2 ≤ k by omega)).le.trans
      ((pK_lt_phaseLower_iff hk γ).2 hγ).le

theorem phaseLower_lt_one {k : ℕ} (hk : 3 ≤ k) {γ : ℝ} (hγ : γ < 1) :
    phaseLower k γ < 1 := by
  have hd : (0 : ℝ) < (k - 2 : ℕ) := by
    exact_mod_cast (show 0 < k - 2 by omega)
  have he : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hmul := mul_lt_mul_of_pos_right hγ he
  rw [phaseLower, div_lt_iff₀ hd]
  norm_num [Nat.cast_sub (show 1 ≤ k by omega),
    Nat.cast_sub (show 2 ≤ k by omega)] at hmul ⊢
  linarith

theorem phaseLower_denominator (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) :
    1 + (k - 2 : ℕ) * phaseLower k γ = (k - 1 : ℕ) * γ := by
  have hd : ((k - 2 : ℕ) : ℝ) ≠ 0 := (deltaK_pos hk).ne'
  rw [phaseLower]
  field_simp [hd]
  ring

theorem phaseLower_one_sub (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) :
    (k - 2 : ℕ) * (1 - phaseLower k γ) = (k - 1 : ℕ) * (1 - γ) := by
  have hd : ((k - 2 : ℕ) : ℝ) ≠ 0 := (deltaK_pos hk).ne'
  rw [phaseLower]
  field_simp [hd]
  norm_num [Nat.cast_sub (show 2 ≤ k by omega), Nat.cast_sub (show 1 ≤ k by omega)]
  ring

theorem phaseLower_delta_scale (k : ℕ) (hk : 3 ≤ k) {γ : ℝ} (hγ : 0 < γ) :
    (k - 2 : ℕ) * γ / (1 + (k - 2 : ℕ) * phaseLower k γ) =
      (k - 2 : ℕ) / (k - 1 : ℕ) := by
  rw [phaseLower_denominator k hk γ]
  have hk1 : ((k - 1 : ℕ) : ℝ) ≠ 0 := (kSubOne_pos hk).ne'
  field_simp [hk1, hγ.ne']

theorem phaseLower_complement_scale (k : ℕ) (hk : 3 ≤ k) {γ : ℝ} (hγ : γ < 1) :
    (1 - γ) / (1 - phaseLower k γ) = (k - 2 : ℕ) / (k - 1 : ℕ) := by
  have h1γ : 1 - γ ≠ 0 := (sub_pos.mpr hγ).ne'
  have hp1 : 1 - phaseLower k γ ≠ 0 := (sub_pos.mpr (phaseLower_lt_one hk hγ)).ne'
  have hk1 : ((k - 1 : ℕ) : ℝ) ≠ 0 := (kSubOne_pos hk).ne'
  have hd : ((k - 2 : ℕ) : ℝ) ≠ 0 := (deltaK_pos hk).ne'
  have hid := phaseLower_one_sub k hk γ
  field_simp [h1γ, hp1, hk1, hd]
  nlinarith

/-- The objective after saturating the constraint `y ≤ (k-2)x`. -/
noncomputable def reducedObjective (k : ℕ) (γ p : ℝ) : ℝ :=
  ((k - 2 : ℕ) * γ / (1 + (k - 2 : ℕ) * p)) * binaryEntropy p

/-- The objective after saturating the constraint `y ≤ 1-x`. -/
noncomputable def complementBoundaryObjective (γ p : ℝ) : ℝ :=
  ((1 - γ) / (1 - p)) * binaryEntropy p

theorem ScalarFeasible.objective_le_reduced {k : ℕ} {γ x y : ℝ}
    (h : ScalarFeasible k γ x y) :
    scalarObjective γ x y ≤ reducedObjective k γ (scalarRatio γ x y) := by
  have hH := binaryEntropy_nonneg h.ratio_nonneg h.ratio_le_one
  exact mul_le_mul_of_nonneg_right h.y_le_delta_scale hH

theorem ScalarFeasible.objective_le_complement {k : ℕ} {γ x y : ℝ}
    (h : ScalarFeasible k γ x y) (hp : scalarRatio γ x y < 1) :
    scalarObjective γ x y ≤ complementBoundaryObjective γ (scalarRatio γ x y) := by
  have hH := binaryEntropy_nonneg h.ratio_nonneg h.ratio_le_one
  exact mul_le_mul_of_nonneg_right (h.y_le_complement_scale hp) hH

theorem reducedObjective_at_pK (k : ℕ) (γ : ℝ) :
    reducedObjective k γ (pK k) = entropyDensityLower k γ := by
  rfl

/-- The optimizer's `x` coordinate from Paper Equation `eqn:xsys-opt-coords`. -/
noncomputable def scalarOptimizerX (k : ℕ) (γ : ℝ) : ℝ :=
  if γ ≤ gammaK k then γ / (1 + (k - 2 : ℕ) * pK k) else 1 / (k - 1 : ℕ)

/-- The optimizer's `y` coordinate from Paper Equation `eqn:xsys-opt-coords`. -/
noncomputable def scalarOptimizerY (k : ℕ) (γ : ℝ) : ℝ :=
  if γ ≤ gammaK k then
    (k - 2 : ℕ) * γ / (1 + (k - 2 : ℕ) * pK k)
  else
    (k - 2 : ℕ) / (k - 1 : ℕ)

theorem scalarRatio_upperBoundary (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) :
    scalarRatio γ (1 / (k - 1 : ℕ)) ((k - 2 : ℕ) / (k - 1 : ℕ)) =
      phaseLower k γ := by
  have hd1 : ((k - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show k - 1 ≠ 0 by omega)
  have hd2 : ((k - 2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show k - 2 ≠ 0 by omega)
  rw [scalarRatio, phaseLower]
  field_simp [hd1, hd2]

theorem lowerScalarCandidate_feasible {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ0 : 0 < γ) (hγcrit : γ ≤ gammaK k) :
    ScalarFeasible k γ
      (γ / (1 + (k - 2 : ℕ) * pK k))
      ((k - 2 : ℕ) * γ / (1 + (k - 2 : ℕ) * pK k)) := by
  have hDelta : (0 : ℝ) < (k - 2 : ℕ) := by
    exact_mod_cast (show 0 < k - 2 by omega)
  have hp0 : 0 < pK k := pK_pos (by omega)
  have hp1 : pK k < 1 := pK_lt_one (by omega)
  have hden : 0 < 1 + (k - 2 : ℕ) * pK k := by positivity
  have hkden : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hsum :
      γ / (1 + (k - 2 : ℕ) * pK k) +
          (k - 2 : ℕ) * γ / (1 + (k - 2 : ℕ) * pK k) ≤ 1 := by
    rw [← add_div]
    rw [div_le_one hden]
    have hcrit := (le_div_iff₀ hkden).mp (show γ ≤
        (1 + (k - 2 : ℕ) * pK k) / (k - 1 : ℕ) by
      exact hγcrit)
    norm_num [Nat.cast_sub (show 2 ≤ k by omega),
      Nat.cast_sub (show 1 ≤ k by omega)] at hcrit ⊢
    nlinarith
  refine
    { x_nonneg := (div_pos hγ0 hden).le
      x_le_one := ?_
      y_pos := div_pos (mul_pos hDelta hγ0) hden
      y_le_one_sub_x := by linarith
      y_le_delta_mul_x := by dsimp [deltaK]; ring_nf; exact le_rfl
      x_le_gamma := ?_
      gamma_le_x_add_y := ?_ }
  · have hypos : 0 < (k - 2 : ℕ) * γ / (1 + (k - 2 : ℕ) * pK k) :=
      div_pos (mul_pos hDelta hγ0) hden
    linarith
  · rw [div_le_iff₀ hden]
    have hden_ge : 1 ≤ 1 + (k - 2 : ℕ) * pK k := by
      nlinarith [mul_pos hDelta hp0]
    nlinarith
  · rw [← add_div, le_div_iff₀ hden]
    norm_num [Nat.cast_sub (show 2 ≤ k by omega)]
    have hp1' : pK k ≤ 1 := hp1.le
    have hgp : γ * pK k ≤ γ := by
      simpa using mul_le_mul_of_nonneg_left hp1' hγ0.le
    have hDgp := mul_le_mul_of_nonneg_left hgp hDelta.le
    norm_num [Nat.cast_sub (show 2 ≤ k by omega)] at hDgp
    nlinarith

theorem upperScalarCandidate_feasible {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγcrit : gammaK k ≤ γ) (hγ1 : γ < 1) :
    ScalarFeasible k γ
      (1 / (k - 1 : ℕ)) ((k - 2 : ℕ) / (k - 1 : ℕ)) := by
  have hDelta : (0 : ℝ) < (k - 2 : ℕ) := by
    exact_mod_cast (show 0 < k - 2 by omega)
  have hkden : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hxcrit : 1 / ((k - 1 : ℕ) : ℝ) ≤ gammaK k := by
    rw [gammaK]
    exact (div_le_div_iff_of_pos_right hkden).2 (by
      have hp0 : 0 < pK k := pK_pos (by omega)
      nlinarith [mul_pos hDelta hp0])
  have hsum :
      1 / ((k - 1 : ℕ) : ℝ) + (k - 2 : ℕ) / (k - 1 : ℕ) = 1 := by
    field_simp [hkden.ne']
    norm_num [Nat.cast_sub (show 2 ≤ k by omega),
      Nat.cast_sub (show 1 ≤ k by omega)]
    ring
  refine
    { x_nonneg := (one_div_pos.mpr hkden).le
      x_le_one := by linarith [hsum, div_pos hDelta hkden]
      y_pos := div_pos hDelta hkden
      y_le_one_sub_x := by linarith
      y_le_delta_mul_x := by dsimp [deltaK]; ring_nf; exact le_rfl
      x_le_gamma := hxcrit.trans hγcrit
      gamma_le_x_add_y := by linarith }

theorem scalarOptimizer_feasible {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ScalarFeasible k γ (scalarOptimizerX k γ) (scalarOptimizerY k γ) := by
  by_cases hcrit : γ ≤ gammaK k
  · simpa [scalarOptimizerX, scalarOptimizerY, hcrit] using
      lowerScalarCandidate_feasible hk hγ.1 hcrit
  · have hge : gammaK k ≤ γ := le_of_not_ge hcrit
    simpa [scalarOptimizerX, scalarOptimizerY, hcrit] using
      upperScalarCandidate_feasible hk hge hγ.2

@[simp] theorem scalarOptimizer_at_gammaK (k : ℕ) (hk : 3 ≤ k) :
    scalarOptimizerX k (gammaK k) = 1 / (k - 1 : ℕ) ∧
      scalarOptimizerY k (gammaK k) = (k - 2 : ℕ) / (k - 1 : ℕ) := by
  simp only [scalarOptimizerX, scalarOptimizerY, le_refl, ↓reduceIte]
  exact ⟨gammaK_div_one_add k hk, gammaK_delta_mul_div_one_add k hk⟩

/-! ## Calculus of the reduced objectives -/

/-- The logarithmic identity exposing the sign of the reduced derivative. -/
theorem reducedSlope_identity {k : ℕ} (hk : 3 ≤ k) {p : ℝ}
    (hp₀ : 0 < p) (hp₁ : p < 1) :
    (1 + ((k - 2 : ℕ) : ℝ) * p) * log2 ((1 - p) / p) -
        ((k - 2 : ℕ) : ℝ) * binaryEntropy p =
      log2 (((1 - p) ^ (k - 1)) / p) := by
  have hp_ne : p ≠ 0 := hp₀.ne'
  have hq_ne : 1 - p ≠ 0 := by linarith
  have hpow_ne : (1 - p) ^ (k - 1) ≠ 0 := pow_ne_zero _ hq_ne
  rw [binaryEntropy_eq_formula, log2_div hq_ne hp_ne,
    log2_div hpow_ne hp_ne, log2_pow]
  have hk₂ : 2 ≤ k := by omega
  have hk₁ : 1 ≤ k := by omega
  norm_num [Nat.cast_sub hk₂, Nat.cast_sub hk₁]
  ring

theorem hasDerivAt_reducedObjective {k : ℕ} (hk : 3 ≤ k) (γ : ℝ) {p : ℝ}
    (hp₀ : 0 < p) (hp₁ : p < 1) :
    HasDerivAt (reducedObjective k γ)
      (((k - 2 : ℕ) * γ / (1 + (k - 2 : ℕ) * p) ^ 2) *
        log2 (((1 - p) ^ (k - 1)) / p)) p := by
  have hd_pos : (0 : ℝ) < (k - 2 : ℕ) := by
    exact_mod_cast (show 0 < k - 2 by omega)
  have hden_pos : (0 : ℝ) < 1 + (k - 2 : ℕ) * p := by positivity
  have hden_ne : (1 : ℝ) + (k - 2 : ℕ) * p ≠ 0 := hden_pos.ne'
  have hnum :
      HasDerivAt (fun q : ℝ ↦ ((k - 2 : ℕ) : ℝ) * γ * binaryEntropy q)
        (((k - 2 : ℕ) : ℝ) * γ * log2 ((1 - p) / p)) p :=
    (hasDerivAt_binaryEntropy hp₀ hp₁).const_mul
      (((k - 2 : ℕ) : ℝ) * γ)
  have hden :
      HasDerivAt (fun q : ℝ ↦ 1 + ((k - 2 : ℕ) : ℝ) * q)
        ((k - 2 : ℕ) : ℝ) p :=
    by simpa only [id_eq, mul_one] using
      ((hasDerivAt_id p).const_mul (((k - 2 : ℕ) : ℝ))).const_add 1
  have hquot := hnum.div hden hden_ne
  have hslope := reducedSlope_identity hk hp₀ hp₁
  have hfun :
      ((fun q : ℝ ↦ ((k - 2 : ℕ) : ℝ) * γ * binaryEntropy q) /
          fun q : ℝ ↦ 1 + ((k - 2 : ℕ) : ℝ) * q) =
        reducedObjective k γ := by
    funext q
    simp only [reducedObjective, Pi.div_apply]
    ring
  rw [← hfun]
  apply hquot.congr_deriv
  rw [← hslope]
  field_simp [hden_ne]

theorem deriv_reducedObjective {k : ℕ} (hk : 3 ≤ k) (γ : ℝ) {p : ℝ}
    (hp₀ : 0 < p) (hp₁ : p < 1) :
    deriv (reducedObjective k γ) p =
      (((k - 2 : ℕ) * γ / (1 + (k - 2 : ℕ) * p) ^ 2) *
        log2 (((1 - p) ^ (k - 1)) / p)) :=
  (hasDerivAt_reducedObjective hk γ hp₀ hp₁).deriv

theorem log2_pos_iff_of_pos {x : ℝ} (hx : 0 < x) :
    0 < log2 x ↔ 1 < x := by
  rw [log2, div_pos_iff]
  constructor
  · rintro (h | h)
    · exact (Real.log_pos_iff hx.le).mp h.1
    · exact (not_lt_of_ge realLogTwo_pos.le h.2).elim
  · intro h
    exact Or.inl ⟨(Real.log_pos_iff hx.le).mpr h, realLogTwo_pos⟩

theorem log2_neg_iff_of_pos {x : ℝ} (hx : 0 < x) :
    log2 x < 0 ↔ x < 1 := by
  rw [log2, div_neg_iff]
  constructor
  · rintro (h | h)
    · exact (not_lt_of_ge realLogTwo_pos.le h.2).elim
    · exact (Real.log_neg_iff hx).mp h.1
  · intro h
    exact Or.inr ⟨(Real.log_neg_iff hx).mpr h, realLogTwo_pos⟩

theorem reducedDerivative_pos {k : ℕ} (hk : 3 ≤ k) {γ p : ℝ}
    (hγ : 0 < γ) (hp₀ : 0 < p) (hpK : p < pK k) :
    0 < deriv (reducedObjective k γ) p := by
  have hk₂ : 2 ≤ k := by omega
  have hp₁ : p < 1 := hpK.trans (pK_lt_one hk₂)
  rw [deriv_reducedObjective hk γ hp₀ hp₁]
  have hd_pos : (0 : ℝ) < (k - 2 : ℕ) := by
    exact_mod_cast (show 0 < k - 2 by omega)
  have hden_pos : (0 : ℝ) < 1 + (k - 2 : ℕ) * p := by positivity
  have hpow_pos : 0 < (1 - p) ^ (k - 1) := by positivity
  have hratio_pos : 0 < ((1 - p) ^ (k - 1)) / p := div_pos hpow_pos hp₀
  have hpow : p < (1 - p) ^ (k - 1) :=
    (lt_pK_iff_lt_pow hk₂ hp₁).mp hpK
  have hlog : 0 < log2 (((1 - p) ^ (k - 1)) / p) := by
    rw [log2_pos_iff_of_pos hratio_pos, one_lt_div hp₀]
    exact hpow
  positivity

theorem reducedDerivative_neg {k : ℕ} (hk : 3 ≤ k) {γ p : ℝ}
    (hγ : 0 < γ) (hpK : pK k < p) (hp₁ : p < 1) :
    deriv (reducedObjective k γ) p < 0 := by
  have hk₂ : 2 ≤ k := by omega
  have hp₀ : 0 < p := (pK_pos hk₂).trans hpK
  rw [deriv_reducedObjective hk γ hp₀ hp₁]
  have hd_pos : (0 : ℝ) < (k - 2 : ℕ) := by
    exact_mod_cast (show 0 < k - 2 by omega)
  have hden_pos : (0 : ℝ) < 1 + (k - 2 : ℕ) * p := by positivity
  have hpow_pos : 0 < (1 - p) ^ (k - 1) := by positivity
  have hratio_pos : 0 < ((1 - p) ^ (k - 1)) / p := div_pos hpow_pos hp₀
  have hpow : (1 - p) ^ (k - 1) < p :=
    (pK_lt_iff_pow_lt hk₂ hp₁).mp hpK
  have hlog : log2 (((1 - p) ^ (k - 1)) / p) < 0 := by
    rw [log2_neg_iff_of_pos hratio_pos, div_lt_one hp₀]
    exact hpow
  exact mul_neg_of_pos_of_neg
    (div_pos (mul_pos hd_pos hγ) (sq_pos_of_pos hden_pos)) hlog

@[simp] theorem reducedDerivative_at_pK {k : ℕ} (hk : 3 ≤ k) (γ : ℝ) :
    deriv (reducedObjective k γ) (pK k) = 0 := by
  rw [deriv_reducedObjective hk γ (pK_pos (show 2 ≤ k by omega))
    (pK_lt_one (show 2 ≤ k by omega)), ← pK_equation, div_self
    (pK_pos (show 2 ≤ k by omega)).ne', log2_one, mul_zero]

theorem reducedDerivative_eq_zero_iff {k : ℕ} (hk : 3 ≤ k) {γ p : ℝ}
    (hγ : 0 < γ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    deriv (reducedObjective k γ) p = 0 ↔ p = pK k := by
  constructor
  · intro hzero
    rcases lt_trichotomy p (pK k) with hlt | heq | hgt
    · exact (ne_of_gt (reducedDerivative_pos hk hγ hp.1 hlt) hzero).elim
    · exact heq
    · exact (ne_of_lt (reducedDerivative_neg hk hγ hgt hp.2) hzero).elim
  · rintro rfl
    exact reducedDerivative_at_pK hk γ

theorem reducedObjective_continuousOn {k : ℕ} (hk : 3 ≤ k) (γ : ℝ) :
    ContinuousOn (reducedObjective k γ) (Icc 0 1) := by
  have hd_pos : (0 : ℝ) < (k - 2 : ℕ) := by
    exact_mod_cast (show 0 < k - 2 by omega)
  apply ContinuousOn.mul
  · apply ContinuousOn.div continuousOn_const
      (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
    intro p hp hzero
    have hmul : (0 : ℝ) ≤ (k - 2 : ℕ) * p := mul_nonneg hd_pos.le hp.1
    have : (0 : ℝ) < 1 + (k - 2 : ℕ) * p := by linarith
    exact this.ne' hzero
  · exact binaryEntropy_continuous.continuousOn

/-- The reduced objective rises strictly up to the critical probability. -/
theorem reducedObjective_strictMonoOn {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : 0 < γ) :
    StrictMonoOn (reducedObjective k γ) (Icc 0 (pK k)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (pK k))
  · exact (reducedObjective_continuousOn hk γ).mono (by
      intro p hp
      exact ⟨hp.1, hp.2.trans (pK_mem_Icc k).2⟩)
  · intro p hp
    rw [interior_Icc] at hp
    exact reducedDerivative_pos hk hγ hp.1 hp.2

/-- The reduced objective falls strictly after the critical probability. -/
theorem reducedObjective_strictAntiOn {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : 0 < γ) :
    StrictAntiOn (reducedObjective k γ) (Icc (pK k) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc (pK k) 1)
  · exact (reducedObjective_continuousOn hk γ).mono (by
      intro p hp
      exact ⟨(pK_mem_Icc k).1.trans hp.1, hp.2⟩)
  · intro p hp
    rw [interior_Icc] at hp
    exact reducedDerivative_neg hk hγ hp.1 hp.2

theorem complementSlope_identity {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    (1 - p) * log2 ((1 - p) / p) + binaryEntropy p =
      log2 (1 / p) := by
  have hp_ne : p ≠ 0 := hp₀.ne'
  have hq_ne : 1 - p ≠ 0 := by linarith
  rw [binaryEntropy_eq_formula, log2_div hq_ne hp_ne,
    log2_div one_ne_zero hp_ne, log2_one]
  ring

theorem hasDerivAt_complementBoundaryObjective (γ : ℝ) {p : ℝ}
    (hp₀ : 0 < p) (hp₁ : p < 1) :
    HasDerivAt (complementBoundaryObjective γ)
      (((1 - γ) / (1 - p) ^ 2) * log2 (1 / p)) p := by
  have hden_ne : 1 - p ≠ 0 := by linarith
  have hnum :
      HasDerivAt (fun q : ℝ ↦ (1 - γ) * binaryEntropy q)
        ((1 - γ) * log2 ((1 - p) / p)) p :=
    (hasDerivAt_binaryEntropy hp₀ hp₁).const_mul (1 - γ)
  have hden : HasDerivAt (fun q : ℝ ↦ 1 - q) (-1) p :=
    (hasDerivAt_id p).const_sub 1
  have hquot := hnum.div hden hden_ne
  have hslope := complementSlope_identity hp₀ hp₁
  have hfun :
      ((fun q : ℝ ↦ (1 - γ) * binaryEntropy q) / fun q : ℝ ↦ 1 - q) =
        complementBoundaryObjective γ := by
    funext q
    simp only [complementBoundaryObjective, Pi.div_apply]
    ring
  rw [← hfun]
  apply hquot.congr_deriv
  rw [← hslope]
  field_simp [hden_ne]
  ring

theorem deriv_complementBoundaryObjective (γ : ℝ) {p : ℝ}
    (hp₀ : 0 < p) (hp₁ : p < 1) :
    deriv (complementBoundaryObjective γ) p =
      ((1 - γ) / (1 - p) ^ 2) * log2 (1 / p) :=
  (hasDerivAt_complementBoundaryObjective γ hp₀ hp₁).deriv

/-- The complementary boundary objective is strictly increasing below one. -/
theorem complementBoundaryObjective_strictMonoOn {γ b : ℝ} (hγ : γ < 1)
    (_hb₀ : 0 < b) (hb₁ : b < 1) :
    StrictMonoOn (complementBoundaryObjective γ) (Icc 0 b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 b)
  · apply ContinuousOn.mul
    · apply ContinuousOn.div continuousOn_const
        (continuousOn_const.sub continuousOn_id)
      intro p hp hzero
      have : 0 < 1 - p := by linarith [hp.2]
      exact this.ne' hzero
    · exact binaryEntropy_continuous.continuousOn
  · intro p hp
    rw [interior_Icc] at hp
    have hp₁ : p < 1 := hp.2.trans hb₁
    rw [deriv_complementBoundaryObjective γ hp.1 hp₁]
    have hratio_pos : 0 < 1 / p := one_div_pos.mpr hp.1
    have hlog : 0 < log2 (1 / p) := by
      rw [log2_pos_iff_of_pos hratio_pos, one_lt_div hp.1]
      exact hp₁
    have hden_pos : 0 < 1 - p := by linarith
    positivity

theorem scalarRatio_oneBoundary_strictAnti {γ x₁ x₂ : ℝ}
    (hγ : γ < 1) (hx₁ : x₁ < x₂) (hx₂ : x₂ < 1) :
    scalarRatio γ x₂ (1 - x₂) < scalarRatio γ x₁ (1 - x₁) := by
  rw [scalarRatio, scalarRatio,
    div_lt_div_iff₀ (sub_pos.mpr hx₂) (sub_pos.mpr (hx₁.trans hx₂))]
  nlinarith

theorem scalarObjective_oneBoundary_eq_complement {γ x : ℝ}
    (hγ : γ < 1) (hx : x < 1) :
    scalarObjective γ x (1 - x) =
      complementBoundaryObjective γ (scalarRatio γ x (1 - x)) := by
  rw [scalarObjective, complementBoundaryObjective]
  congr 1
  rw [scalarRatio]
  have hx0 : 1 - x ≠ 0 := (sub_pos.mpr hx).ne'
  have hγ0 : 1 - γ ≠ 0 := (sub_pos.mpr hγ).ne'
  field_simp [hx0, hγ0]
  ring

/-- Along the feasible boundary `y = 1-x`, the objective strictly decreases
as `x` increases. -/
theorem scalarObjective_strictAnti_oneBoundary {k : ℕ} {γ x₁ x₂ : ℝ}
    (hγ : γ < 1) (h₁ : ScalarFeasible k γ x₁ (1 - x₁))
    (h₂ : ScalarFeasible k γ x₂ (1 - x₂)) (hx : x₁ < x₂) :
    scalarObjective γ x₂ (1 - x₂) < scalarObjective γ x₁ (1 - x₁) := by
  let p₁ := scalarRatio γ x₁ (1 - x₁)
  let p₂ := scalarRatio γ x₂ (1 - x₂)
  have hx₂one : x₂ < 1 := by linarith [h₂.y_pos]
  have hp₂p₁ : p₂ < p₁ := scalarRatio_oneBoundary_strictAnti hγ hx hx₂one
  have hp₁pos : 0 < p₁ := by
    simp only [p₁, scalarRatio]
    exact div_pos (sub_pos.mpr (hx.trans_le h₂.x_le_gamma)) h₁.y_pos
  have hp₁one : p₁ < 1 := by
    simp only [p₁, scalarRatio]
    rw [div_lt_one h₁.y_pos]
    linarith
  have hp₂mem : p₂ ∈ Icc (0 : ℝ) p₁ := ⟨h₂.ratio_nonneg, hp₂p₁.le⟩
  have hp₁mem : p₁ ∈ Icc (0 : ℝ) p₁ := ⟨hp₁pos.le, le_rfl⟩
  have hmono := complementBoundaryObjective_strictMonoOn hγ hp₁pos hp₁one
    hp₂mem hp₁mem hp₂p₁
  rw [scalarObjective_oneBoundary_eq_complement hγ hx₂one,
    scalarObjective_oneBoundary_eq_complement hγ (hx.trans hx₂one)]
  exact hmono

/-! ### Consequences for the one-variable maxima -/

/-- The critical probability globally maximizes the reduced objective. -/
theorem reducedObjective_le_at_pK {k : ℕ} (hk : 3 ≤ k) {γ p : ℝ}
    (hγ : 0 < γ) (hp : p ∈ Icc (0 : ℝ) 1) :
    reducedObjective k γ p ≤ reducedObjective k γ (pK k) := by
  rcases le_total p (pK k) with hpK | hKp
  · have hp_low : p ∈ Icc (0 : ℝ) (pK k) := ⟨hp.1, hpK⟩
    have hpk_low : pK k ∈ Icc (0 : ℝ) (pK k) :=
      ⟨(pK_mem_Icc k).1, le_rfl⟩
    exact (reducedObjective_strictMonoOn hk hγ).monotoneOn
      hp_low hpk_low hpK
  · have hpk_high : pK k ∈ Icc (pK k) 1 :=
      ⟨le_rfl, (pK_mem_Icc k).2⟩
    have hp_high : p ∈ Icc (pK k) 1 := ⟨hKp, hp.2⟩
    exact (reducedObjective_strictAntiOn hk hγ).antitoneOn
      hpk_high hp_high hKp

theorem reducedObjective_eq_at_pK_iff {k : ℕ} (hk : 3 ≤ k) {γ p : ℝ}
    (hγ : 0 < γ) (hp : p ∈ Icc (0 : ℝ) 1) :
    reducedObjective k γ p = reducedObjective k γ (pK k) ↔ p = pK k := by
  constructor
  · intro heq
    rcases lt_trichotomy p (pK k) with hpK | hpK | hpK
    · have hp_low : p ∈ Icc (0 : ℝ) (pK k) := ⟨hp.1, hpK.le⟩
      have hpk_low : pK k ∈ Icc (0 : ℝ) (pK k) :=
        ⟨(pK_mem_Icc k).1, le_rfl⟩
      have hlt := reducedObjective_strictMonoOn hk hγ hp_low hpk_low hpK
      linarith
    · exact hpK
    · have hpk_high : pK k ∈ Icc (pK k) 1 :=
        ⟨le_rfl, (pK_mem_Icc k).2⟩
      have hp_high : p ∈ Icc (pK k) 1 := ⟨hpK.le, hp.2⟩
      have hlt := reducedObjective_strictAntiOn hk hγ hpk_high hp_high hpK
      linarith
  · rintro rfl
    rfl

/-- Beyond `pK`, the left endpoint maximizes the reduced objective. -/
theorem reducedObjective_le_at_leftEndpoint {k : ℕ} (hk : 3 ≤ k)
    {γ p₀ p : ℝ} (hγ : 0 < γ) (hp₀ : p₀ ∈ Ioo (pK k) 1)
    (hp : p ∈ Icc p₀ 1) :
    reducedObjective k γ p ≤ reducedObjective k γ p₀ := by
  have hp₀_mem : p₀ ∈ Icc (pK k) 1 := ⟨hp₀.1.le, hp₀.2.le⟩
  have hp_mem : p ∈ Icc (pK k) 1 := ⟨hp₀.1.le.trans hp.1, hp.2⟩
  exact (reducedObjective_strictAntiOn hk hγ).antitoneOn
    hp₀_mem hp_mem hp.1

theorem reducedObjective_eq_at_leftEndpoint_iff {k : ℕ} (hk : 3 ≤ k)
    {γ p₀ p : ℝ} (hγ : 0 < γ) (hp₀ : p₀ ∈ Ioo (pK k) 1)
    (hp : p ∈ Icc p₀ 1) :
    reducedObjective k γ p = reducedObjective k γ p₀ ↔ p = p₀ := by
  have hp₀_mem : p₀ ∈ Icc (pK k) 1 := ⟨hp₀.1.le, hp₀.2.le⟩
  have hp_mem : p ∈ Icc (pK k) 1 := ⟨hp₀.1.le.trans hp.1, hp.2⟩
  constructor
  · intro heq
    by_contra hne
    have hp₀p : p₀ < p := lt_of_le_of_ne hp.1 (Ne.symm hne)
    have hlt := reducedObjective_strictAntiOn hk hγ hp₀_mem hp_mem hp₀p
    linarith
  · rintro rfl
    rfl

/-- The right endpoint maximizes the complementary boundary objective. -/
theorem complementBoundaryObjective_le_at_rightEndpoint {γ b p : ℝ}
    (hγ : γ < 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Icc 0 b) :
    complementBoundaryObjective γ p ≤ complementBoundaryObjective γ b := by
  have hb_mem : b ∈ Icc (0 : ℝ) b := ⟨hb.1.le, le_rfl⟩
  exact (complementBoundaryObjective_strictMonoOn hγ hb.1 hb.2).monotoneOn
    hp hb_mem hp.2

theorem complementBoundaryObjective_eq_at_rightEndpoint_iff {γ b p : ℝ}
    (hγ : γ < 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Icc 0 b) :
    complementBoundaryObjective γ p = complementBoundaryObjective γ b ↔ p = b := by
  have hb_mem : b ∈ Icc (0 : ℝ) b := ⟨hb.1.le, le_rfl⟩
  constructor
  · intro heq
    by_contra hne
    have hpb : p < b := lt_of_le_of_ne hp.2 hne
    have hlt := complementBoundaryObjective_strictMonoOn hγ hb.1 hb.2
      hp hb_mem hpb
    linarith
  · rintro rfl
    rfl

/-! ### Exact boundary values -/

theorem upperScale_eq (k : ℕ) (hk : 3 ≤ k) :
    ((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ) = 1 - 1 / (k - 1 : ℕ) := by
  have hk1 : ((k - 1 : ℕ) : ℝ) ≠ 0 := (kSubOne_pos hk).ne'
  field_simp [hk1]
  norm_num [Nat.cast_sub (show 2 ≤ k by omega),
    Nat.cast_sub (show 1 ≤ k by omega)]
  ring

theorem scalarRatio_lowerCandidate {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ≠ 0) :
    scalarRatio γ
        (γ / (1 + (k - 2 : ℕ) * pK k))
        ((k - 2 : ℕ) * γ / (1 + (k - 2 : ℕ) * pK k)) =
      pK k := by
  have hDelta : ((k - 2 : ℕ) : ℝ) ≠ 0 := (deltaK_pos hk).ne'
  have hden : (1 : ℝ) + (k - 2 : ℕ) * pK k ≠ 0 := by
    have hp0 := pK_pos (show 2 ≤ k by omega)
    have hd := deltaK_pos hk
    rw [deltaK] at hd
    positivity
  rw [scalarRatio]
  field_simp [hγ, hDelta, hden]
  ring

theorem reducedObjective_at_phaseLower {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ≠ 0) :
    reducedObjective k γ (phaseLower k γ) = entropyDensityUpper k γ := by
  have hk1 : ((k - 1 : ℕ) : ℝ) ≠ 0 := (kSubOne_pos hk).ne'
  have harg :
      ((((k - 1 : ℕ) : ℝ) * γ - 1) / (k - 2 : ℕ)) = phaseLower k γ := by
    rw [phaseLower]
    ring
  rw [reducedObjective, entropyDensityUpper, phaseLower_denominator k hk γ, harg]
  congr 1
  calc
    ((k - 2 : ℕ) : ℝ) * γ / (((k - 1 : ℕ) : ℝ) * γ) =
        ((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ) := by
      field_simp [hk1, hγ]
    _ = 1 - 1 / (k - 1 : ℕ) := upperScale_eq k hk

theorem complementBoundaryObjective_at_phaseLower {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ < 1) :
    complementBoundaryObjective γ (phaseLower k γ) = entropyDensityUpper k γ := by
  have harg :
      ((((k - 1 : ℕ) : ℝ) * γ - 1) / (k - 2 : ℕ)) = phaseLower k γ := by
    rw [phaseLower]
    ring
  rw [complementBoundaryObjective, entropyDensityUpper,
    phaseLower_complement_scale k hk hγ, harg, upperScale_eq k hk]

theorem scalarOptimizer_objective_eq {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    scalarObjective γ (scalarOptimizerX k γ) (scalarOptimizerY k γ) =
      entropyDensity k γ := by
  by_cases hcrit : γ ≤ gammaK k
  · simp only [scalarOptimizerX, scalarOptimizerY, hcrit, ↓reduceIte]
    rw [entropyDensity_of_le hcrit, scalarObjective,
      scalarRatio_lowerCandidate hk hγ.1.ne']
    rfl
  · have hge : gammaK k ≤ γ := le_of_not_ge hcrit
    have harg : phaseLower k γ =
        ((((k - 1 : ℕ) : ℝ) * γ - 1) / (k - 2 : ℕ)) := by
      rw [phaseLower]
      ring
    simp only [scalarOptimizerX, scalarOptimizerY, hcrit, ↓reduceIte]
    rw [entropyDensity_of_ge hk hge, scalarObjective,
      scalarRatio_upperBoundary k hk γ, entropyDensityUpper, upperScale_eq k hk,
      harg]

/-! ## Solution of the two-variable problem -/

theorem ScalarFeasible.objective_le_entropyDensity {k : ℕ} (hk : 3 ≤ k)
    {γ x y : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (h : ScalarFeasible k γ x y) :
    scalarObjective γ x y ≤ entropyDensity k γ := by
  by_cases hcrit : γ ≤ gammaK k
  · calc
      scalarObjective γ x y ≤ reducedObjective k γ (scalarRatio γ x y) :=
        h.objective_le_reduced
      _ ≤ reducedObjective k γ (pK k) :=
        reducedObjective_le_at_pK hk hγ.1 h.ratio_mem_Icc
      _ = entropyDensityLower k γ := reducedObjective_at_pK k γ
      _ = entropyDensity k γ := (entropyDensity_of_le hcrit).symm
  · have hcrit' : gammaK k < γ := lt_of_not_ge hcrit
    have hp₀ : phaseLower k γ ∈ Ioo (pK k) 1 :=
      ⟨(pK_lt_phaseLower_iff hk γ).2 hcrit', phaseLower_lt_one hk hγ.2⟩
    have hp₀unit : phaseLower k γ ∈ Ioo (0 : ℝ) 1 :=
      ⟨(pK_pos (show 2 ≤ k by omega)).trans hp₀.1, hp₀.2⟩
    have hdensity : entropyDensity k γ = entropyDensityUpper k γ :=
      entropyDensity_of_ge hk hcrit'.le
    rcases le_total (scalarRatio γ x y) (phaseLower k γ) with hp | hp
    · have hp_mem : scalarRatio γ x y ∈ Icc (0 : ℝ) (phaseLower k γ) :=
        ⟨h.ratio_nonneg, hp⟩
      calc
        scalarObjective γ x y ≤
            complementBoundaryObjective γ (scalarRatio γ x y) :=
          h.objective_le_complement (hp.trans_lt hp₀.2)
        _ ≤ complementBoundaryObjective γ (phaseLower k γ) :=
          complementBoundaryObjective_le_at_rightEndpoint hγ.2 hp₀unit hp_mem
        _ = entropyDensityUpper k γ :=
          complementBoundaryObjective_at_phaseLower hk hγ.2
        _ = entropyDensity k γ := hdensity.symm
    · have hp_mem : scalarRatio γ x y ∈ Icc (phaseLower k γ) 1 :=
        ⟨hp, h.ratio_le_one⟩
      calc
        scalarObjective γ x y ≤ reducedObjective k γ (scalarRatio γ x y) :=
          h.objective_le_reduced
        _ ≤ reducedObjective k γ (phaseLower k γ) :=
          reducedObjective_le_at_leftEndpoint hk hγ.1 hp₀ hp_mem
        _ = entropyDensityUpper k γ := reducedObjective_at_phaseLower hk hγ.1.ne'
        _ = entropyDensity k γ := hdensity.symm

theorem ScalarFeasible.eq_lowerCandidate_of_objective_eq {k : ℕ} (hk : 3 ≤ k)
    {γ x y : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (h : ScalarFeasible k γ x y) (hcrit : γ ≤ gammaK k)
    (heq : scalarObjective γ x y = entropyDensity k γ) :
    x = γ / (1 + (k - 2 : ℕ) * pK k) ∧
      y = (k - 2 : ℕ) * γ / (1 + (k - 2 : ℕ) * pK k) := by
  have htop : reducedObjective k γ (pK k) = entropyDensity k γ := by
    rw [reducedObjective_at_pK, entropyDensity_of_le hcrit]
  have hred_le :
      reducedObjective k γ (scalarRatio γ x y) ≤ reducedObjective k γ (pK k) :=
    reducedObjective_le_at_pK hk hγ.1 h.ratio_mem_Icc
  have hred_eq :
      reducedObjective k γ (scalarRatio γ x y) = reducedObjective k γ (pK k) :=
    le_antisymm hred_le (by
      calc
        reducedObjective k γ (pK k) = entropyDensity k γ := htop
        _ = scalarObjective γ x y := heq.symm
        _ ≤ reducedObjective k γ (scalarRatio γ x y) := h.objective_le_reduced)
  have hratio : scalarRatio γ x y = pK k :=
    (reducedObjective_eq_at_pK_iff hk hγ.1 h.ratio_mem_Icc).mp hred_eq
  have hobjred :
      scalarObjective γ x y = reducedObjective k γ (scalarRatio γ x y) :=
    le_antisymm h.objective_le_reduced (by
      calc
        reducedObjective k γ (scalarRatio γ x y) = reducedObjective k γ (pK k) :=
          hred_eq
        _ = entropyDensity k γ := htop
        _ ≤ scalarObjective γ x y := heq.symm.le)
  have hH : 0 < binaryEntropy (pK k) :=
    binaryEntropy_pos (pK_pos (show 2 ≤ k by omega))
      (pK_lt_one (show 2 ≤ k by omega))
  have hy : y = (k - 2 : ℕ) * γ / (1 + (k - 2 : ℕ) * pK k) := by
    rw [scalarObjective, reducedObjective, hratio] at hobjred
    nlinarith
  have hxraw := h.x_eq_gamma_sub
  rw [hratio, hy] at hxraw
  have hden : (1 : ℝ) + (k - 2 : ℕ) * pK k ≠ 0 := by
    have hd := deltaK_pos hk
    rw [deltaK] at hd
    have hp := pK_pos (show 2 ≤ k by omega)
    positivity
  have hx : x = γ / (1 + (k - 2 : ℕ) * pK k) := by
    calc
      x = γ - ((k - 2 : ℕ) * γ / (1 + (k - 2 : ℕ) * pK k)) * pK k :=
        hxraw
      _ = γ / (1 + (k - 2 : ℕ) * pK k) := by
        field_simp [hden]
        ring
  exact ⟨hx, hy⟩

theorem ScalarFeasible.eq_upperCandidate_of_objective_eq {k : ℕ} (hk : 3 ≤ k)
    {γ x y : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (h : ScalarFeasible k γ x y) (hcrit : gammaK k < γ)
    (heq : scalarObjective γ x y = entropyDensity k γ) :
    x = 1 / (k - 1 : ℕ) ∧ y = (k - 2 : ℕ) / (k - 1 : ℕ) := by
  have hp₀ : phaseLower k γ ∈ Ioo (pK k) 1 :=
    ⟨(pK_lt_phaseLower_iff hk γ).2 hcrit, phaseLower_lt_one hk hγ.2⟩
  have hp₀unit : phaseLower k γ ∈ Ioo (0 : ℝ) 1 :=
    ⟨(pK_pos (show 2 ≤ k by omega)).trans hp₀.1, hp₀.2⟩
  have hdensity : entropyDensity k γ = entropyDensityUpper k γ :=
    entropyDensity_of_ge hk hcrit.le
  have htopComp :
      complementBoundaryObjective γ (phaseLower k γ) = entropyDensity k γ := by
    rw [complementBoundaryObjective_at_phaseLower hk hγ.2, hdensity]
  have htopRed : reducedObjective k γ (phaseLower k γ) = entropyDensity k γ := by
    rw [reducedObjective_at_phaseLower hk hγ.1.ne', hdensity]
  have hratio : scalarRatio γ x y = phaseLower k γ := by
    rcases le_total (scalarRatio γ x y) (phaseLower k γ) with hp | hp
    · have hp_mem : scalarRatio γ x y ∈ Icc (0 : ℝ) (phaseLower k γ) :=
        ⟨h.ratio_nonneg, hp⟩
      have hobjComp := h.objective_le_complement (hp.trans_lt hp₀.2)
      have hcomp_le :=
        complementBoundaryObjective_le_at_rightEndpoint hγ.2 hp₀unit hp_mem
      have hcomp_eq :
          complementBoundaryObjective γ (scalarRatio γ x y) =
            complementBoundaryObjective γ (phaseLower k γ) :=
        le_antisymm hcomp_le (by
          calc
            complementBoundaryObjective γ (phaseLower k γ) = entropyDensity k γ :=
              htopComp
            _ = scalarObjective γ x y := heq.symm
            _ ≤ complementBoundaryObjective γ (scalarRatio γ x y) := hobjComp)
      exact (complementBoundaryObjective_eq_at_rightEndpoint_iff
        hγ.2 hp₀unit hp_mem).mp hcomp_eq
    · have hp_mem : scalarRatio γ x y ∈ Icc (phaseLower k γ) 1 :=
        ⟨hp, h.ratio_le_one⟩
      have hred_le := reducedObjective_le_at_leftEndpoint hk hγ.1 hp₀ hp_mem
      have hred_eq :
          reducedObjective k γ (scalarRatio γ x y) =
            reducedObjective k γ (phaseLower k γ) :=
        le_antisymm hred_le (by
          calc
            reducedObjective k γ (phaseLower k γ) = entropyDensity k γ := htopRed
            _ = scalarObjective γ x y := heq.symm
            _ ≤ reducedObjective k γ (scalarRatio γ x y) := h.objective_le_reduced)
      exact (reducedObjective_eq_at_leftEndpoint_iff hk hγ.1 hp₀ hp_mem).mp hred_eq
  have hcrit_not : ¬γ ≤ gammaK k := not_le_of_gt hcrit
  have hcandidate :
      scalarObjective γ (1 / (k - 1 : ℕ)) ((k - 2 : ℕ) / (k - 1 : ℕ)) =
        entropyDensity k γ := by
    simpa only [scalarOptimizerX, scalarOptimizerY, hcrit_not, ↓reduceIte] using
      scalarOptimizer_objective_eq hk hγ
  have hobjCandidate :
      scalarObjective γ x y =
        scalarObjective γ (1 / (k - 1 : ℕ)) ((k - 2 : ℕ) / (k - 1 : ℕ)) :=
    heq.trans hcandidate.symm
  simp only [scalarObjective] at hobjCandidate
  rw [hratio, scalarRatio_upperBoundary k hk γ] at hobjCandidate
  have hH : 0 < binaryEntropy (phaseLower k γ) :=
    binaryEntropy_pos hp₀unit.1 hp₀unit.2
  have hy : y = (k - 2 : ℕ) / (k - 1 : ℕ) := by
    nlinarith
  have hxraw := h.x_eq_gamma_sub
  rw [hratio, hy] at hxraw
  have hDelta : ((k - 2 : ℕ) : ℝ) ≠ 0 := (deltaK_pos hk).ne'
  have hk1 : ((k - 1 : ℕ) : ℝ) ≠ 0 := (kSubOne_pos hk).ne'
  have hx : x = 1 / (k - 1 : ℕ) := by
    calc
      x = γ - (((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ)) * phaseLower k γ := hxraw
      _ = 1 / (k - 1 : ℕ) := by
        rw [phaseLower]
        field_simp [hDelta, hk1]
        ring
  exact ⟨hx, hy⟩

theorem ScalarFeasible.objective_eq_entropyDensity_iff {k : ℕ} (hk : 3 ≤ k)
    {γ x y : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (h : ScalarFeasible k γ x y) :
    scalarObjective γ x y = entropyDensity k γ ↔
      x = scalarOptimizerX k γ ∧ y = scalarOptimizerY k γ := by
  constructor
  · intro heq
    by_cases hcrit : γ ≤ gammaK k
    · simpa only [scalarOptimizerX, scalarOptimizerY, hcrit, ↓reduceIte] using
        h.eq_lowerCandidate_of_objective_eq hk hγ hcrit heq
    · have hcrit' : gammaK k < γ := lt_of_not_ge hcrit
      simpa only [scalarOptimizerX, scalarOptimizerY, hcrit, ↓reduceIte] using
        h.eq_upperCandidate_of_objective_eq hk hγ hcrit' heq
  · rintro ⟨rfl, rfl⟩
    exact scalarOptimizer_objective_eq hk hγ

/--
Paper: Lemma `lemma:k1k-calc-prob`.

The division-free feasibility predicate has positive scale `y`, and the
quotient constraint
is expressed as `x ≤ γ ≤ x + y`.
-/
theorem k1kCalcProb
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ScalarFeasible k γ (scalarOptimizerX k γ) (scalarOptimizerY k γ) ∧
    scalarObjective γ (scalarOptimizerX k γ) (scalarOptimizerY k γ) =
      entropyDensity k γ ∧
    ∀ x y,
      ScalarFeasible k γ x y →
      scalarObjective γ x y ≤ entropyDensity k γ ∧
      (scalarObjective γ x y = entropyDensity k γ ↔
        x = scalarOptimizerX k γ ∧ y = scalarOptimizerY k γ) := by
  refine ⟨scalarOptimizer_feasible hk hγ, scalarOptimizer_objective_eq hk hγ, ?_⟩
  intro x y h
  exact ⟨h.objective_le_entropyDensity hk hγ,
    h.objective_eq_entropyDensity_iff hk hγ⟩

end InducedStars
