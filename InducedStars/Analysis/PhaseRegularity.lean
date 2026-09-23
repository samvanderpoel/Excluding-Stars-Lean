import InducedStars.Analysis.RateMinimization
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Piecewise

/-!
# Regularity at the two star phase transitions

Paper: the phase-regularity assertions in `paper/introduction.tex`.
All derivatives below use the paper's base-two normalization, retaining the
factor `Real.log 2` explicitly.
-/

noncomputable section
open Set Filter
open scoped Topology Classical
namespace InducedStars

theorem hasDerivWithinAt_rateFunction_left {k : ℕ} (hk : 3 ≤ k) :
    HasDerivWithinAt (rateFunction k) (1 / ((1 - pK k) * Real.log 2))
      (Iic (pK k)) (pK k) := by
  have hp := pK_mem_Ioo (show 2 ≤ k by omega)
  have h : HasDerivAt (fun p : ℝ ↦ -log2 (1 - p))
      (1 / ((1 - pK k) * Real.log 2)) (pK k) := by
    convert (((hasDerivAt_log2 (sub_pos.mpr hp.2).ne').comp (pK k)
      ((hasDerivAt_id (pK k)).const_sub 1)).neg) using 1 <;> try rfl
    simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
  exact h.hasDerivWithinAt.congr_of_mem
    (fun x hx ↦ rateFunction_eq_neg_log2_one_sub_of_le_pK hx) (by simp)

theorem hasDerivWithinAt_rateFunction_right {k : ℕ} (hk : 3 ≤ k) :
    HasDerivWithinAt (rateFunction k)
      (-1 / ((k - 1 : ℕ) * pK k * Real.log 2)) (Ici (pK k)) (pK k) := by
  have hp := pK_mem_Ioo (show 2 ≤ k by omega)
  have h : HasDerivAt (fun p : ℝ ↦ -(log2 p) / (k - 1 : ℕ))
      (-1 / ((k - 1 : ℕ) * pK k * Real.log 2)) (pK k) := by
    convert ((hasDerivAt_log2 hp.1.ne').neg.div_const ((k - 1 : ℕ) : ℝ)) using 1 <;> try rfl
    simp [div_eq_mul_inv, mul_inv_rev] <;> ring
  apply h.hasDerivWithinAt.congr_of_mem _ (by simp)
  intro x hx
  rw [rateFunction_of_ge (show 2 ≤ k by omega) hx]
  simp only [one_div, log2_inv]
  ring

theorem continuousAt_rateFunction_pK {k : ℕ} (hk : 3 ≤ k) :
    ContinuousAt (rateFunction k) (pK k) := by
  simpa only [Iic_union_Ici, continuousWithinAt_univ] using
    (hasDerivWithinAt_rateFunction_left hk).continuousWithinAt.union
      (hasDerivWithinAt_rateFunction_right hk).continuousWithinAt

/-- The left slope is positive and the right slope negative: this is the
first-order nonanalyticity of the conditioned-model rate function. -/
theorem not_differentiableAt_rateFunction_pK {k : ℕ} (hk : 3 ≤ k) :
    ¬DifferentiableAt ℝ (rateFunction k) (pK k) := by
  intro h
  have hl := (h.hasDerivAt.hasDerivWithinAt (s := Iic (pK k))).derivWithin
    (uniqueDiffWithinAt_Iic _)
  have hr := (h.hasDerivAt.hasDerivWithinAt (s := Ici (pK k))).derivWithin
    (uniqueDiffWithinAt_Ici _)
  rw [(hasDerivWithinAt_rateFunction_left hk).derivWithin (uniqueDiffWithinAt_Iic _)] at hl
  rw [(hasDerivWithinAt_rateFunction_right hk).derivWithin (uniqueDiffWithinAt_Ici _)] at hr
  have hp := pK_mem_Ioo (show 2 ≤ k by omega)
  have hkpos := kSubOne_pos hk
  have hlpos : 0 < 1 / ((1 - pK k) * Real.log 2) := by
    exact one_div_pos.mpr (mul_pos (sub_pos.mpr hp.2) realLogTwo_pos)
  have hrneg : -1 / (((k - 1 : ℕ) : ℝ) * pK k * Real.log 2) < 0 := by
    exact div_neg_of_neg_of_pos (by norm_num) (mul_pos (mul_pos hkpos hp.1) realLogTwo_pos)
  linarith

private lemma hasDerivAt_phaseLower (k : ℕ) (x : ℝ) :
    HasDerivAt (phaseLower k) (((k - 1 : ℕ) : ℝ) / (k - 2 : ℕ)) x := by
  change HasDerivAt (fun y : ℝ ↦ (y * (k - 1 : ℕ) - 1) / (k - 2 : ℕ)) _ _
  simpa only [one_mul, id_eq] using
    (((hasDerivAt_id x).mul_const ((k - 1 : ℕ) : ℝ)).sub_const 1).div_const
      ((k - 2 : ℕ) : ℝ)

def entropyPhaseUpperSlope (k : ℕ) (x : ℝ) : ℝ :=
  log2 (1 - phaseLower k x) - log2 (phaseLower k x)

def entropyPhaseSlope (k : ℕ) (x : ℝ) : ℝ :=
  if x ≤ gammaK k then entropyPhaseUpperSlope k (gammaK k)
  else entropyPhaseUpperSlope k x

theorem hasDerivAt_entropyDensityLower {k : ℕ} (hk : 3 ≤ k) (x : ℝ) :
    HasDerivAt (entropyDensityLower k) (entropyPhaseUpperSlope k (gammaK k)) x := by
  have hp := pK_mem_Ioo (show 2 ≤ k by omega)
  have hslope := criticalEntropySlope_identity k hk
  rw [log2_div (sub_pos.mpr hp.2).ne' hp.1.ne'] at hslope
  have h := ((((hasDerivAt_id x).const_mul ((k - 2 : ℕ) : ℝ)).div_const
    (1 + (k - 2 : ℕ) * pK k)).mul_const (binaryEntropy (pK k)))
  change HasDerivAt (fun y : ℝ ↦ ((k - 2 : ℕ) * y /
    (1 + (k - 2 : ℕ) * pK k)) * binaryEntropy (pK k)) _ _
  simpa only [entropyPhaseUpperSlope, phaseLower_at_gammaK k hk,
    mul_one, hslope, id_eq] using h

theorem hasDerivAt_entropyDensityUpper {k : ℕ} (hk : 3 ≤ k) {x : ℝ}
    (hx : phaseLower k x ∈ Ioo 0 1) :
    HasDerivAt (entropyDensityUpper k) (entropyPhaseUpperSlope k x) x := by
  have hd : (0 : ℝ) < (k - 2 : ℕ) := by exact_mod_cast (show 0 < k - 2 by omega)
  have hr : (0 : ℝ) < (k - 1 : ℕ) := kSubOne_pos hk
  have hcast : ((k - 1 : ℕ) : ℝ) = (k - 2 : ℕ) + 1 := by
    exact_mod_cast (show k - 1 = (k - 2) + 1 by omega)
  have heq : entropyDensityUpper k = fun y ↦ (1 - 1 / (k - 1 : ℕ)) *
      binaryEntropy (phaseLower k y) := by
    funext y
    simp only [entropyDensityUpper, phaseLower, mul_comm y]
  rw [heq]
  have h := ((hasDerivAt_binaryEntropy hx.1 hx.2).comp x
    (hasDerivAt_phaseLower k x)).const_mul (1 - 1 / ((k - 1 : ℕ) : ℝ))
  convert h using 1 <;> try rfl
  rw [entropyPhaseUpperSlope, log2_div (sub_pos.mpr hx.2).ne' hx.1.ne']
  field_simp [hd.ne', hr.ne']
  rw [hcast]
  ring

theorem hasDerivAt_entropyDensity_gammaK {k : ℕ} (hk : 3 ≤ k) :
    HasDerivAt (entropyDensity k) (entropyPhaseUpperSlope k (gammaK k)) (gammaK k) := by
  have hl := (hasDerivAt_entropyDensityLower hk (gammaK k)).hasDerivWithinAt
    (s := Iic (gammaK k))
  have hr := (hasDerivAt_entropyDensityUpper hk
    (show phaseLower k (gammaK k) ∈ Ioo 0 1 by
      rw [phaseLower_at_gammaK k hk]; exact pK_mem_Ioo (by omega))).hasDerivWithinAt
        (s := Ici (gammaK k))
  have hl' := hl.congr_of_mem (fun x hx ↦ entropyDensity_of_le hx) (by simp)
  have hr' := hr.congr_of_mem (fun x hx ↦ entropyDensity_of_ge hk hx) (by simp)
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl'.union hr'

theorem hasDerivAt_entropyDensity_of_phaseInterior {k : ℕ} (hk : 3 ≤ k) {x : ℝ}
    (hx : phaseLower k x ∈ Ioo 0 1) :
    HasDerivAt (entropyDensity k) (entropyPhaseSlope k x) x := by
  rcases lt_trichotomy x (gammaK k) with h | rfl | h
  · rw [entropyPhaseSlope, if_pos h.le]
    apply (hasDerivAt_entropyDensityLower hk x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h] with y hy
    exact entropyDensity_of_le hy.le
  · simpa only [entropyPhaseSlope, le_refl, ite_true] using hasDerivAt_entropyDensity_gammaK hk
  · rw [entropyPhaseSlope, if_neg h.not_ge]
    apply (hasDerivAt_entropyDensityUpper hk hx).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds h] with y hy
    exact entropyDensity_of_ge hk hy.le

/-- The upper entropy branch has strictly negative curvature. -/
theorem hasDerivAt_entropyPhaseUpperSlope {k : ℕ} (hk : 3 ≤ k) {x : ℝ}
    (hx : phaseLower k x ∈ Ioo 0 1) :
    HasDerivAt (entropyPhaseUpperSlope k)
      (-((k - 1 : ℕ) : ℝ) /
        ((k - 2 : ℕ) * phaseLower k x * (1 - phaseLower k x) * Real.log 2)) x := by
  have hp := hasDerivAt_phaseLower k x
  have h := ((hasDerivAt_log2 (sub_pos.mpr hx.2).ne').comp x (hp.const_sub 1)).sub
    ((hasDerivAt_log2 hx.1.ne').comp x hp)
  convert h using 1 <;> try rfl
  have hd : ((k - 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show k - 2 ≠ 0 by omega)
  field_simp [hd, hx.1.ne', (sub_pos.mpr hx.2).ne', realLogTwo_pos.ne']
  ring

private theorem continuousOn_entropyPhaseSlope {k : ℕ} (hk : 3 ≤ k) :
    ContinuousOn (entropyPhaseSlope k) (phaseLower k ⁻¹' Ioo 0 1) := by
  change ContinuousOn ((Iic (gammaK k)).piecewise
    (fun _ ↦ entropyPhaseUpperSlope k (gammaK k)) (entropyPhaseUpperSlope k)) _
  apply ContinuousOn.piecewise
  · intro x hx
    have hx' : x = gammaK k := mem_singleton_iff.mp (frontier_Iic_subset _ hx.2)
    subst x
    rfl
  · exact continuousOn_const
  · intro x hx
    exact (hasDerivAt_entropyPhaseUpperSlope hk hx.1).continuousAt.continuousWithinAt

private theorem entropyPhaseInterior_mem_nhds {k : ℕ} (hk : 3 ≤ k) :
    phaseLower k ⁻¹' Ioo 0 1 ∈ 𝓝 (gammaK k) := by
  have hp := pK_mem_Ioo (show 2 ≤ k by omega)
  apply (hasDerivAt_phaseLower k (gammaK k)).continuousAt.preimage_mem_nhds
  simpa only [phaseLower_at_gammaK k hk] using Ioo_mem_nhds hp.1 hp.2

/-- The entropy profile is genuinely `C¹` on a neighborhood of the critical
density; the first derivative is not merely defined at the junction. -/
theorem contDiffAt_entropyDensity_gammaK {k : ℕ} (hk : 3 ≤ k) :
    ContDiffAt ℝ 1 (entropyDensity k) (gammaK k) := by
  let U : Set ℝ := phaseLower k ⁻¹' Ioo 0 1
  have hU : IsOpen U := isOpen_Ioo.preimage (by unfold phaseLower; fun_prop)
  have hderiv : ContinuousOn (deriv (entropyDensity k)) U :=
    (continuousOn_entropyPhaseSlope hk).congr
      (fun x hx ↦ (hasDerivAt_entropyDensity_of_phaseInterior hk hx).deriv)
  have hcd : ContDiffOn ℝ (0 + 1) (entropyDensity k) U :=
    (contDiffOn_succ_iff_deriv_of_isOpen hU).mpr
      ⟨fun x hx ↦ (hasDerivAt_entropyDensity_of_phaseInterior hk hx).differentiableAt.differentiableWithinAt,
        by simp, contDiffOn_zero.mpr hderiv⟩
  have hmem : gammaK k ∈ U := by
    change phaseLower k (gammaK k) ∈ Ioo 0 1
    rw [phaseLower_at_gammaK k hk]
    exact pK_mem_Ioo (by omega)
  exact (hcd _ hmem).contDiffAt (hU.mem_nhds hmem)

theorem continuousAt_deriv_entropyDensity_gammaK {k : ℕ} (hk : 3 ≤ k) :
    ContinuousAt (deriv (entropyDensity k)) (gammaK k) :=
  ((contDiffAt_entropyDensity_gammaK hk).derivWithin (m := 0) (by norm_num)).continuousAt

theorem hasDerivWithinAt_deriv_entropyDensity_left {k : ℕ} (hk : 3 ≤ k) :
    HasDerivWithinAt (deriv (entropyDensity k)) 0 (Iic (gammaK k)) (gammaK k) := by
  apply (hasDerivAt_const (gammaK k) (entropyPhaseUpperSlope k (gammaK k))).hasDerivWithinAt.congr_of_eventuallyEq_of_mem _ (by simp)
  have hU : ∀ᶠ x in 𝓝 (gammaK k), phaseLower k x ∈ Ioo 0 1 := entropyPhaseInterior_mem_nhds hk
  filter_upwards [hU.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with x hx hside
  rw [(hasDerivAt_entropyDensity_of_phaseInterior hk hx).deriv,
    entropyPhaseSlope, if_pos (show x ≤ gammaK k from hside)]

/-- The unequal right-hand second derivative in the paper's base-two
normalization. Its strict negativity proves concavity of the upper entropy
piece. -/
theorem hasDerivWithinAt_deriv_entropyDensity_right {k : ℕ} (hk : 3 ≤ k) :
    HasDerivWithinAt (deriv (entropyDensity k))
      (-((k - 1 : ℕ) : ℝ) / ((k - 2 : ℕ) * pK k * (1 - pK k) * Real.log 2))
        (Ici (gammaK k)) (gammaK k) := by
  have h := hasDerivAt_entropyPhaseUpperSlope hk
    (show phaseLower k (gammaK k) ∈ Ioo 0 1 by
      rw [phaseLower_at_gammaK k hk]; exact pK_mem_Ioo (by omega))
  rw [phaseLower_at_gammaK k hk] at h
  apply h.hasDerivWithinAt.congr_of_eventuallyEq_of_mem _ (by simp)
  have hU : ∀ᶠ x in 𝓝 (gammaK k), phaseLower k x ∈ Ioo 0 1 := entropyPhaseInterior_mem_nhds hk
  filter_upwards [hU.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with x hx hside
  rw [(hasDerivAt_entropyDensity_of_phaseInterior hk hx).deriv, entropyPhaseSlope]
  split_ifs with hle
  · have heq : x = gammaK k := le_antisymm hle hside
    rw [heq]
  · rfl

/-- The entropy profile has no second derivative at the critical density. -/
theorem not_differentiableAt_deriv_entropyDensity_gammaK {k : ℕ} (hk : 3 ≤ k) :
    ¬DifferentiableAt ℝ (deriv (entropyDensity k)) (gammaK k) := by
  intro h
  have hl := (h.hasDerivAt.hasDerivWithinAt (s := Iic (gammaK k))).derivWithin
    (uniqueDiffWithinAt_Iic _)
  have hr := (h.hasDerivAt.hasDerivWithinAt (s := Ici (gammaK k))).derivWithin
    (uniqueDiffWithinAt_Ici _)
  rw [(hasDerivWithinAt_deriv_entropyDensity_left hk).derivWithin
    (uniqueDiffWithinAt_Iic _)] at hl
  rw [(hasDerivWithinAt_deriv_entropyDensity_right hk).derivWithin
    (uniqueDiffWithinAt_Ici _)] at hr
  have hp := pK_mem_Ioo (show 2 ≤ k by omega)
  have hd : (0 : ℝ) < (k - 2 : ℕ) := by exact_mod_cast (show 0 < k - 2 by omega)
  have hnegative : -((k - 1 : ℕ) : ℝ) /
      ((k - 2 : ℕ) * pK k * (1 - pK k) * Real.log 2) < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos (kSubOne_pos hk))
      (mul_pos (mul_pos (mul_pos hd hp.1) (sub_pos.mpr hp.2)) realLogTwo_pos)
  linarith

theorem not_contDiffAt_two_entropyDensity_gammaK {k : ℕ} (hk : 3 ≤ k) :
    ¬ContDiffAt ℝ 2 (entropyDensity k) (gammaK k) := by
  intro h
  exact not_differentiableAt_deriv_entropyDensity_gammaK hk
    ((h.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))

end InducedStars
