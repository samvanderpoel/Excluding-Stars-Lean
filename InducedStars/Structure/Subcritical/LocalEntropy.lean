import InducedStars.Structure.Subcritical.ActiveLevelComparison
import InducedStars.Analysis.RelativeEntropy

/-!
# Finite local entropy estimates in natural units

Paper: `eqn:local-ent-estimates-K1k` and `eqn:local-own-entropy-K1k`.
The base-two formulas are converted consistently to natural logarithms.
The estimates retain explicit finite errors.
-/

noncomputable section

namespace InducedStars

open Set

/-- The natural-unit local row maximum. -/
def subcriticalLocalA_Nat (k : ℕ) : ℝ := -Real.log (1 - pK k)

/-- The natural-unit local own-part maximum. -/
def subcriticalLocalU_Nat (k : ℕ) : ℝ := -Real.log (pK k)

theorem subcriticalLocalA_Nat_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < subcriticalLocalA_Nat k := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hp1 := pK_lt_one (show 2 ≤ k by omega)
  exact neg_pos.mpr (Real.log_neg (by linarith) (by linarith))

theorem subcriticalLocalU_Nat_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < subcriticalLocalU_Nat k :=
  neg_pos.mpr (Real.log_neg (pK_pos (by omega)) (pK_lt_one (by omega)))

theorem subcriticalLogOddsNat_eq_delta_mul_A {k : ℕ} (hk : 3 ≤ k) :
    subcriticalLogOddsNat k = ((k - 2 : ℕ) : ℝ) * subcriticalLocalA_Nat k := by
  rw [subcriticalLogOddsNat, log_one_sub_div_pK (by omega), subcriticalLocalA_Nat]
  ring

theorem subcriticalLogOddsNat_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < subcriticalLogOddsNat k := by
  rw [subcriticalLogOddsNat_eq_delta_mul_A hk]
  exact mul_pos (by exact_mod_cast (show 0 < k - 2 by omega))
    (subcriticalLocalA_Nat_pos hk)

theorem subcriticalLocalU_Nat_eq_L_add_A {k : ℕ} (hk : 3 ≤ k) :
    subcriticalLocalU_Nat k = subcriticalLogOddsNat k + subcriticalLocalA_Nat k := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hp1 := pK_lt_one (show 2 ≤ k by omega)
  rw [subcriticalLocalU_Nat, subcriticalLogOddsNat, subcriticalLocalA_Nat,
    Real.log_div (by linarith : 1 - pK k ≠ 0) hp.ne']
  ring

/-- The Gibbs inequality already proved from entropy concavity, converted
exactly from bits to natural units. -/
private theorem binEntropy_sub_logOdds_le {p x : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    Real.binEntropy x - Real.log ((1 - p) / p) * x ≤ -Real.log (1 - p) := by
  have h := mul_nonneg realLogTwo_pos.le (binaryRelativeEntropy_nonneg hp hx)
  have hc : Real.log 2 * binaryRelativeEntropy p x =
      -Real.binEntropy x + x * Real.log ((1 - p) / p) - Real.log (1 - p) := by
    rw [binaryRelativeEntropy_eq_negEntropy_add hp hx, binaryEntropy, log2, log2]
    field_simp
  rw [hc] at h
  linarith

/-- Natural-unit row maximum from `eqn:local-ent-estimates-K1k`. -/
theorem subcriticalLocalEntropy_sub_le {k : ℕ} (hk : 3 ≤ k)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Real.binEntropy x - subcriticalLogOddsNat k * x ≤ subcriticalLocalA_Nat k :=
  binEntropy_sub_logOdds_le ⟨pK_pos (by omega), pK_lt_one (by omega)⟩ hx

/-- The own-part entropy is its maximum minus the Bernoulli relative-entropy
loss. This is `eqn:local-own-entropy-K1k`, converted from bits to natural units. -/
theorem subcriticalLocalEntropy_own_relativeEntropy (hk : 3 ≤ k)
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    Real.binEntropy (1 - z) + subcriticalLogOddsNat k * (1 - z) =
      subcriticalLocalU_Nat k - Real.log 2 * binaryRelativeEntropy (pK k) z := by
  have hp : pK k ∈ Ioo (0 : ℝ) 1 := ⟨pK_pos (by omega), pK_lt_one (by omega)⟩
  have hc : Real.log 2 * binaryRelativeEntropy (pK k) z =
      -Real.binEntropy z + z * subcriticalLogOddsNat k + subcriticalLocalA_Nat k := by
    rw [binaryRelativeEntropy_eq_negEntropy_add hp hz, binaryEntropy, log2, log2]
    unfold subcriticalLogOddsNat subcriticalLocalA_Nat
    field_simp
    <;> ring
  rw [hc, Real.binEntropy_one_sub, subcriticalLocalU_Nat_eq_L_add_A hk]
  ring

/-- Finite own-part entropy with its exact relative-entropy loss, including
zero capacity. The density is measured after deleting profile roots. -/
theorem subcriticalLocalEntropy_own_eq_max_sub_loss (hk : 3 ≤ k)
    {N I : ℝ} (hI : 0 ≤ I) (hIN : I ≤ N) :
    N * Real.binEntropy (I / N) + subcriticalLogOddsNat k * I =
      subcriticalLocalU_Nat k * N -
        N * Real.log 2 * binaryRelativeEntropy (pK k) (1 - I / N) := by
  have hN : 0 ≤ N := hI.trans hIN
  rcases hN.eq_or_lt with hN | hN
  · have hI0 : I = 0 := by linarith
    simp [← hN, hI0]
  have hz : 1 - I / N ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [(div_le_one hN).mpr hIN], by linarith [div_nonneg hI hN.le]⟩
  have h := congrArg (fun x : ℝ ↦ N * x) (subcriticalLocalEntropy_own_relativeEntropy hk hz)
  have hc : N * (I / N) = I := mul_div_cancel₀ _ hN.ne'
  simp only [sub_sub_cancel] at h
  have hc' : N * (subcriticalLogOddsNat k * (I / N)) = subcriticalLogOddsNat k * I := by
    calc
      _ = subcriticalLogOddsNat k * (N * (I / N)) := by ring
      _ = _ := by rw [hc]
  rw [mul_add, mul_sub, hc'] at h
  nlinarith only [h]

/-- The row maximum is attained at `pK k`, with no limiting argument. -/
theorem subcriticalLocalEntropy_sub_eq_at_pK {k : ℕ} (hk : 3 ≤ k) :
    Real.binEntropy (pK k) - subcriticalLogOddsNat k * pK k =
      subcriticalLocalA_Nat k := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hp1 := pK_lt_one (show 2 ≤ k by omega)
  rw [Real.binEntropy, Real.log_inv, Real.log_inv, subcriticalLogOddsNat,
    Real.log_div (by linarith : 1 - pK k ≠ 0) hp.ne', subcriticalLocalA_Nat]
  ring

/-- Natural-unit own-part maximum from `eqn:local-ent-estimates-K1k`. -/
theorem subcriticalLocalEntropy_add_le {k : ℕ} (hk : 3 ≤ k)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Real.binEntropy x + subcriticalLogOddsNat k * x ≤ subcriticalLocalU_Nat k := by
  have h := subcriticalLocalEntropy_sub_le hk (x := 1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [Real.binEntropy_one_sub] at h
  rw [subcriticalLocalU_Nat_eq_L_add_A hk]
  linarith

/-- The own-part maximum is attained at `1 - pK k`. -/
theorem subcriticalLocalEntropy_add_eq_at_one_sub_pK {k : ℕ} (hk : 3 ≤ k) :
    Real.binEntropy (1 - pK k) + subcriticalLogOddsNat k * (1 - pK k) =
      subcriticalLocalU_Nat k := by
  rw [Real.binEntropy_one_sub, subcriticalLocalU_Nat_eq_L_add_A hk]
  linarith [subcriticalLocalEntropy_sub_eq_at_pK hk]

/-- Exact finite own-part estimate; `N = 0` is included. -/
theorem subcriticalLocalEntropy_own_le {k : ℕ} (hk : 3 ≤ k)
    {N I : ℝ} (hI : 0 ≤ I) (hIN : I ≤ N) :
    N * Real.binEntropy (I / N) + subcriticalLogOddsNat k * I ≤
      subcriticalLocalU_Nat k * N := by
  have hN : 0 ≤ N := hI.trans hIN
  rcases hN.eq_or_lt with hN | hN
  · have hI0 : I = 0 := by linarith
    simp [← hN, hI0]
  have h := mul_le_mul_of_nonneg_left
    (subcriticalLocalEntropy_add_le hk ⟨div_nonneg hI hN.le, (div_le_one hN).mpr hIN⟩) hN.le
  have hcancel : N * (I / N) = I := mul_div_cancel₀ _ hN.ne'
  have heq : N * (subcriticalLogOddsNat k * (I / N)) = subcriticalLogOddsNat k * I := by
    calc
      _ = subcriticalLogOddsNat k * (N * (I / N)) := by ring
      _ = _ := by rw [hcancel]
  simpa only [mul_add, heq, mul_comm N (subcriticalLocalU_Nat k)] using h

theorem subcriticalLocalEntropy_own_le_untrimmed {k : ℕ} (hk : 3 ≤ k)
    {N N' I : ℝ} (hI : 0 ≤ I) (hIN : I ≤ N') (htrim : N' ≤ N) :
    N' * Real.binEntropy (I / N') + subcriticalLogOddsNat k * I ≤
      subcriticalLocalU_Nat k * N :=
  (subcriticalLocalEntropy_own_le hk hI hIN).trans
    (mul_le_mul_of_nonneg_left htrim (subcriticalLocalU_Nat_pos hk).le)

/-- Exact finite present-row estimate; zero-size trimmed targets are included. -/
theorem subcriticalLocalEntropy_row_le {k : ℕ} (hk : 3 ≤ k)
    {N r : ℝ} (hr : 0 ≤ r) (hrN : r ≤ N) :
    N * Real.binEntropy (r / N) - subcriticalLogOddsNat k * r ≤
      subcriticalLocalA_Nat k * N := by
  have hN : 0 ≤ N := hr.trans hrN
  rcases hN.eq_or_lt with hN | hN
  · have hr0 : r = 0 := by linarith
    simp [← hN, hr0]
  have h := mul_le_mul_of_nonneg_left
    (subcriticalLocalEntropy_sub_le hk ⟨div_nonneg hr hN.le, (div_le_one hN).mpr hrN⟩) hN.le
  have hcancel : N * (r / N) = r := mul_div_cancel₀ _ hN.ne'
  have heq : N * (subcriticalLogOddsNat k * (r / N)) = subcriticalLogOddsNat k * r := by
    calc
      _ = subcriticalLogOddsNat k * (N * (r / N)) := by ring
      _ = _ := by rw [hcancel]
  simpa only [mul_sub, heq, mul_comm N (subcriticalLocalA_Nat k)] using h

/-- Entropy of a high-density row is controlled by its small complement.
The range is `alpha ≤ 1/4`, so the complement is in the
interval on which entropy is increasing. -/
theorem subcriticalLocalEntropy_high_entropy_le {alpha x : ℝ}
    (ha : 0 ≤ alpha) (haQuarter : alpha ≤ 1 / 4)
    (hx : 1 - 2 * alpha ≤ x) (hx1 : x ≤ 1) :
    Real.binEntropy x ≤ Real.binEntropy (2 * alpha) := by
  rw [← Real.binEntropy_one_sub x]
  apply Real.binEntropy_strictMonoOn.monotoneOn
  · exact ⟨by linarith, by norm_num; linarith⟩
  · exact ⟨by linarith, by norm_num; linarith⟩
  · linarith

/-- Paper: `eqn:high-row-ent-K1k`, in natural units, with the
compact high-row range `alpha ≤ 1/4`. -/
theorem subcriticalLocalEntropy_high_row_le {k : ℕ} (hk : 3 ≤ k)
    {alpha x : ℝ} (ha : 0 ≤ alpha) (haQuarter : alpha ≤ 1 / 4)
    (hx : 1 - 2 * alpha ≤ x) (hx1 : x ≤ 1) :
    Real.binEntropy x - subcriticalLogOddsNat k * x ≤
      -subcriticalLogOddsNat k + Real.binEntropy (2 * alpha) +
        2 * subcriticalLogOddsNat k * alpha := by
  have h := subcriticalLocalEntropy_high_entropy_le ha haQuarter hx hx1
  have hmul := mul_le_mul_of_nonneg_left hx (subcriticalLogOddsNat_pos hk).le
  linarith

/-- Finite high-own-count estimate in natural units; the zero-size case
is retained rather than hidden in an eventual positivity assumption. -/
theorem subcriticalLocalEntropy_high_own_le {k : ℕ} (hk : 3 ≤ k)
    {alpha N I : ℝ} (ha : 0 ≤ alpha) (haQuarter : alpha ≤ 1 / 4)
    (hI : 0 ≤ I) (hIN : I ≤ N) (hhigh : (1 - 2 * alpha) * N ≤ I) :
    N * Real.binEntropy (I / N) + subcriticalLogOddsNat k * I ≤
      (subcriticalLogOddsNat k + Real.binEntropy (2 * alpha)) * N := by
  have hN : 0 ≤ N := hI.trans hIN
  rcases hN.eq_or_lt with hN | hN
  · have hI0 : I = 0 := by linarith
    simp [← hN, hI0]
  have hent := mul_le_mul_of_nonneg_left (subcriticalLocalEntropy_high_entropy_le
    ha haQuarter ((le_div_iff₀ hN).mpr hhigh) ((div_le_one hN).mpr hIN)) hN.le
  have hlin := mul_le_mul_of_nonneg_left hIN (subcriticalLogOddsNat_pos hk).le
  nlinarith

/-- Exact finite high-row estimate, using the explicit small-alpha range. -/
theorem subcriticalLocalEntropy_high_row_scaled_le {k : ℕ} (hk : 3 ≤ k)
    {alpha N r : ℝ} (ha : 0 ≤ alpha) (haQuarter : alpha ≤ 1 / 4)
    (hr : 0 ≤ r) (hrN : r ≤ N) (hhigh : (1 - 2 * alpha) * N ≤ r) :
    N * Real.binEntropy (r / N) - subcriticalLogOddsNat k * r ≤
      (-subcriticalLogOddsNat k + Real.binEntropy (2 * alpha) +
        2 * subcriticalLogOddsNat k * alpha) * N := by
  have hN : 0 ≤ N := hr.trans hrN
  rcases hN.eq_or_lt with hN | hN
  · have hr0 : r = 0 := by linarith
    simp [← hN, hr0]
  have h := mul_le_mul_of_nonneg_left (subcriticalLocalEntropy_high_row_le hk
    ha haQuarter ((le_div_iff₀ hN).mpr hhigh) ((div_le_one hN).mpr hrN)) hN.le
  have hcancel : N * (r / N) = r := mul_div_cancel₀ _ hN.ne'
  have heq : N * (subcriticalLogOddsNat k * (r / N)) = subcriticalLogOddsNat k * r := by
    calc
      _ = subcriticalLogOddsNat k * (N * (r / N)) := by ring
      _ = _ := by rw [hcancel]
  simp only [mul_sub, heq] at h
  nlinarith

/-- Small own counts have an explicit entropy error. The hypotheses state
the compact range and both trimming bounds needed for the finite estimate;
there is no asymptotic `o(N)` convention. -/
theorem subcriticalLocalEntropy_small_own_le {k : ℕ} (hk : 3 ≤ k)
    {C alpha xi N N' I : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ alpha)
    (hxi : xi < 1) (hband : C * alpha / (1 - xi) ≤ 1 / 2)
    (hI : 0 ≤ I) (hIN : I ≤ N') (htrim : N' ≤ N)
    (htrimLower : (1 - xi) * N ≤ N') (hsmall : I ≤ C * alpha * N) :
    N' * Real.binEntropy (I / N') + subcriticalLogOddsNat k * I ≤
      N * (Real.binEntropy (C * alpha / (1 - xi)) +
        subcriticalLogOddsNat k * C * alpha) := by
  have hN' : 0 ≤ N' := hI.trans hIN
  have hN : 0 ≤ N := hN'.trans htrim
  have hd : 0 < 1 - xi := by linarith
  have ht : 0 ≤ C * alpha / (1 - xi) := div_nonneg (mul_nonneg hC ha) hd.le
  have hent0 := Real.binEntropy_nonneg ht (show C * alpha / (1 - xi) ≤ 1 by linarith)
  rcases hN'.eq_or_lt with hN' | hN'
  · have hI0 : I = 0 := by linarith
    simp only [← hN', hI0, zero_div, Real.binEntropy_zero, mul_zero, zero_add]
    exact mul_nonneg hN (add_nonneg hent0
      (mul_nonneg (mul_nonneg (subcriticalLogOddsNat_pos hk).le hC) ha))
  have hdens : I / N' ≤ C * alpha / (1 - xi) := by
    apply (div_le_div_iff₀ hN' hd).mpr
    have hmul := mul_le_mul_of_nonneg_left htrimLower (mul_nonneg hC ha)
    have hsmall' := mul_le_mul_of_nonneg_right hsmall hd.le
    nlinarith
  have hent := Real.binEntropy_strictMonoOn.monotoneOn
    (show I / N' ∈ Icc (0 : ℝ) 2⁻¹ from
      ⟨div_nonneg hI hN'.le, by norm_num; linarith⟩)
    (show C * alpha / (1 - xi) ∈ Icc (0 : ℝ) 2⁻¹ from
      ⟨ht, by norm_num; linarith⟩) hdens
  have hent' := (mul_le_mul_of_nonneg_left hent hN'.le).trans
    (mul_le_mul_of_nonneg_right htrim hent0)
  have hlin := mul_le_mul_of_nonneg_left hsmall (subcriticalLogOddsNat_pos hk).le
  nlinarith

/-- The Goal-9b average-deviation bound implies a concrete pairwise ratio.
Only a local scalar consequence of that bound is used here. -/
theorem subcriticalLocal_size_deviation_of_average {mu N Y omega : ℝ}
    (hmu : 0 ≤ mu) (hw : 0 ≤ omega) (hw2 : omega ≤ 2)
    (hN : |N - mu| ≤ omega / 4 * mu)
    (hY : |Y - mu| ≤ omega / 4 * mu) :
    |Y - N| ≤ omega * N := by
  have hNlow := (abs_le.mp hN).1
  have hwtwo := mul_le_mul_of_nonneg_right hw2 hmu
  have hmuN : mu ≤ 2 * N := by nlinarith
  have hd : |Y - N| ≤ omega / 2 * mu := by
    have h := (abs_sub_le Y mu N).trans (add_le_add hY (by simpa [abs_sub_comm] using hN))
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hmuN hw
  nlinarith

/-- Explicit same-component part-size comparison from exactly the
Goal-9b bounded-order balance hypothesis, retaining its `min alpha ...`. -/
theorem subcriticalLocal_sameComponent_size_deviation
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SubcriticalDivision k V) (i : Fin D.componentCount)
    {alpha omega : ℝ} (hw : 0 ≤ omega) (hw2 : omega ≤ 2)
    (hbal : ∀ j : Fin (D.core i).order,
      |((D.parts i j).card : ℝ) - (D.componentSupport i).card / (D.core i).order| ≤
        min alpha (omega / (4 * (D.core i).order)) * (D.componentSupport i).card)
    (a b : Fin (D.core i).order) :
    |((D.parts i b).card : ℝ) - (D.parts i a).card| ≤
      omega * (D.parts i a).card := by
  have hq : (0 : ℝ) < (D.core i).order := by exact_mod_cast (D.core i).order_pos
  have hbound : min alpha (omega / (4 * (D.core i).order)) *
      (D.componentSupport i).card ≤
        omega / 4 * ((D.componentSupport i).card / (D.core i).order) := by
    calc
      _ ≤ omega / (4 * (D.core i).order) * (D.componentSupport i).card :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)
      _ = _ := by ring
  exact subcriticalLocal_size_deviation_of_average (by positivity) hw hw2
    ((hbal a).trans hbound) ((hbal b).trans hbound)

/-- Removing a common root set gives the concrete relative scale error
`omega + 2*rho/theta`; this includes all finite trimming losses. -/
theorem subcriticalLocal_trimmed_size_deviation
    {V : Type*} [DecidableEq V] (Y B : Finset V)
    {N n omega rho theta : ℝ} (htheta : 0 < theta) (hrho : 0 ≤ rho)
    (hN : theta * n / 2 ≤ N) (hB : (B.card : ℝ) ≤ rho * n)
    (hY : |(Y.card : ℝ) - N| ≤ omega * N) :
    |((Y \ B).card : ℝ) - N| ≤ (omega + 2 * rho / theta) * N := by
  have htrim : ((Y \ B).card : ℝ) ≤ Y.card := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : Y \ B ⊆ Y)
  have htrim' : (Y.card : ℝ) ≤ (Y \ B).card + (B.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := Y) (t := B))
  have hroot : (B.card : ℝ) ≤ (2 * rho / theta) * N := by
    have hmul := mul_le_mul_of_nonneg_left hN hrho
    have hmulB := mul_le_mul_of_nonneg_right hB htheta.le
    calc
      _ ≤ 2 * rho * N / theta := (le_div_iff₀ htheta).mpr (by nlinarith)
      _ = _ := by ring
  obtain ⟨hlo, hhi⟩ := abs_le.mp hY
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- Present-row contribution at the root's own scale, with explicit
relative balance/trimming error `zeta`. -/
theorem subcriticalLocalEntropy_row_le_of_scale_error {k : ℕ} (hk : 3 ≤ k)
    {N N' r zeta : ℝ} (hr : 0 ≤ r) (hrN : r ≤ N')
    (hscale : |N' - N| ≤ zeta * N) :
    N' * Real.binEntropy (r / N') - subcriticalLogOddsNat k * r ≤
      (subcriticalLocalA_Nat k + subcriticalLocalA_Nat k * zeta) * N := by
  have h := mul_le_mul_of_nonneg_left (abs_le.mp hscale).2
    (subcriticalLocalA_Nat_pos hk).le
  have he := subcriticalLocalEntropy_row_le hk hr hrN
  nlinarith

/-- High-row contribution at the root's own scale. Unlike multiplication
by a positive maximum, this controls both sides of the target-size error.
The estimate uses natural units and requires `alpha ≤ 1/4`. -/
theorem subcriticalLocalEntropy_high_row_le_of_scale_error {k : ℕ} (hk : 3 ≤ k)
    {alpha N N' r zeta : ℝ} (ha : 0 ≤ alpha) (haQuarter : alpha ≤ 1 / 4)
    (hr : 0 ≤ r) (hrN : r ≤ N') (hhigh : (1 - 2 * alpha) * N' ≤ r)
    (hscale : |N' - N| ≤ zeta * N) :
    N' * Real.binEntropy (r / N') - subcriticalLogOddsNat k * r ≤
      (-subcriticalLogOddsNat k +
        (Real.binEntropy (2 * alpha) + 2 * subcriticalLogOddsNat k * alpha) +
        (subcriticalLogOddsNat k + Real.binEntropy (2 * alpha) +
          2 * subcriticalLogOddsNat k * alpha) * zeta) * N := by
  have hL := (subcriticalLogOddsNat_pos hk).le
  have hE : 0 ≤ Real.binEntropy (2 * alpha) + 2 * subcriticalLogOddsNat k * alpha :=
    add_nonneg (Real.binEntropy_nonneg (by linarith) (by linarith)) (by positivity)
  have hlo := mul_le_mul_of_nonneg_left (abs_le.mp hscale).1 hL
  have hhi := mul_le_mul_of_nonneg_left (abs_le.mp hscale).2 hE
  have h := subcriticalLocalEntropy_high_row_scaled_le hk ha haQuarter hr hrN hhigh
  nlinarith

end InducedStars
