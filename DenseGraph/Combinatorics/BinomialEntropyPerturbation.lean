import DenseGraph.Combinatorics.BinomialEntropy

/-!
# One-sided entropy stability for exact binomial slices

Concavity chords from an interior density to the endpoints give a global
one-sided linear perturbation bound. This avoids differentiating entropy
at the endpoints, which are permitted for an exact finite slice.
-/

noncomputable section
open Set Finset
open scoped BigOperators
namespace DenseGraph

theorem binEntropy_chord_zero {p q : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ Icc (0 : ℝ) p) :
    q / p * Real.binEntropy p ≤ Real.binEntropy q := by
  have hw : 0 ≤ q / p := div_nonneg hq.1 hp.1.le
  have hw1 : q / p ≤ 1 := (div_le_one hp.1).mpr hq.2
  have h := Real.strictConcave_binEntropy.concaveOn.2
    ⟨hp.1.le, hp.2.le⟩ (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    hw (sub_nonneg.mpr hw1) (show q / p + (1 - q / p) = 1 by ring)
  have he : q / p * p = q := div_mul_cancel₀ q hp.1.ne'
  simpa only [smul_eq_mul, Real.binEntropy_zero, mul_zero, add_zero, he] using h

/-- The binary entropy can decrease at most linearly from any fixed
interior density. The perturbed density may be either endpoint. -/
theorem binEntropy_sub_le_linear_abs {p q : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ Icc (0 : ℝ) 1) :
    Real.binEntropy p - Real.binEntropy q ≤
      (Real.binEntropy p / p + Real.binEntropy p / (1 - p)) * |q - p| := by
  have hh : 0 ≤ Real.binEntropy p := Real.binEntropy_nonneg hp.1.le hp.2.le
  have hpos : 0 < 1 - p := sub_pos.mpr hp.2
  have ha := div_nonneg hh hp.1.le
  have hb := div_nonneg hh hpos.le
  rcases le_total q p with hqp | hpq
  · have hc := binEntropy_chord_zero hp ⟨hq.1, hqp⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hqp)]
    have hid : Real.binEntropy p - (q / p * Real.binEntropy p) =
        Real.binEntropy p / p * (p - q) := by field_simp [hp.1.ne'] <;> ring
    have hm := mul_nonneg hb (sub_nonneg.mpr hqp)
    nlinarith
  · have hc := binEntropy_chord_zero
      (p := 1 - p) (q := 1 - q) ⟨hpos, by linarith [hp.1]⟩
      ⟨by linarith [hq.2], by linarith⟩
    rw [Real.binEntropy_one_sub, Real.binEntropy_one_sub] at hc
    rw [abs_of_nonneg (sub_nonneg.mpr hpq)]
    have hid : Real.binEntropy p - ((1 - q) / (1 - p) * Real.binEntropy p) =
        Real.binEntropy p / (1 - p) * (q - p) := by field_simp [hpos.ne'] <;> ring
    have hm := mul_nonneg ha (sub_nonneg.mpr hpq)
    nlinarith

/-- Count-form entropy loss; zero-capacity coordinates are handled exactly. -/
theorem binomialEntropyPerspective_lower_of_count_error {N m : ℕ} (hm : m ≤ N)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    (N : ℝ) * Real.binEntropy p -
        (Real.binEntropy p / p + Real.binEntropy p / (1 - p)) * |(m : ℝ) - p * N| ≤
      binomialEntropyPerspective N m := by
  by_cases hN : N = 0
  · have hm0 : m = 0 := by omega
    simp [hN, hm0, binomialEntropyPerspective]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hq : (m : ℝ) / N ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by positivity) hNpos.le,
      (div_le_one hNpos).mpr (by exact_mod_cast hm)⟩
  have h := mul_le_mul_of_nonneg_left (binEntropy_sub_le_linear_abs hp hq) hNpos.le
  have habs : (N : ℝ) * |(m : ℝ) / N - p| = |(m : ℝ) - p * N| := by
    calc
      _ = |(N : ℝ) * ((m : ℝ) / N - p)| := by rw [abs_mul, abs_of_pos hNpos]
      _ = _ := by congr 1; field_simp <;> ring
  dsimp [binomialEntropyPerspective]
  have h' : (N : ℝ) * Real.binEntropy p - (N : ℝ) * Real.binEntropy ((m : ℝ) / N) ≤
      (Real.binEntropy p / p + Real.binEntropy p / (1 - p)) * |(m : ℝ) - p * N| := by
    calc
      _ = (N : ℝ) * (Real.binEntropy p - Real.binEntropy ((m : ℝ) / N)) := by ring
      _ ≤ (N : ℝ) * ((Real.binEntropy p / p + Real.binEntropy p / (1 - p)) *
          |(m : ℝ) / N - p|) := h
      _ = (Real.binEntropy p / p + Real.binEntropy p / (1 - p)) *
          ((N : ℝ) * |(m : ℝ) / N - p|) := by ring
      _ = _ := by rw [habs]
  linarith

end DenseGraph
