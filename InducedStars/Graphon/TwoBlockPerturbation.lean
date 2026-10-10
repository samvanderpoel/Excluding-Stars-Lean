import InducedStars.Graphon.GnpDomains
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Two-block graphon perturbations

This file constructs weighted direct sums and joins of arbitrary graphons on
two affine subintervals of the unit interval.  It proves the exact integral
formula needed for relative entropy and uses connectivity of a finite graph
or its complement to preserve induced-freeness.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology unitInterval

namespace InducedStars

/-! ## Affine coordinates on the two blocks -/

/-- Totalized affine coordinate on the lower block.  On `x < a` its value is
exactly `x / a`; outside that block the projection is harmless. -/
def lowerBlockCoordinate (a : ℝ) (x : UnitInterval) : UnitInterval :=
  Set.projIcc 0 1 zero_le_one ((x : ℝ) / a)

/-- Totalized affine coordinate on the upper block.  On `a ≤ x` its value is
exactly `(x - a) / (1 - a)`; outside that block the projection is harmless. -/
def upperBlockCoordinate (a : ℝ) (x : UnitInterval) : UnitInterval :=
  Set.projIcc 0 1 zero_le_one (((x : ℝ) - a) / (1 - a))

@[fun_prop, measurability]
theorem measurable_lowerBlockCoordinate (a : ℝ) :
    Measurable (lowerBlockCoordinate a) := by
  exact continuous_projIcc.comp
    (continuous_subtype_val.div_const a) |>.measurable

@[fun_prop, measurability]
theorem measurable_upperBlockCoordinate (a : ℝ) :
    Measurable (upperBlockCoordinate a) := by
  exact continuous_projIcc.comp
    ((continuous_subtype_val.sub continuous_const).div_const (1 - a)) |>.measurable

theorem coe_lowerBlockCoordinate {a : ℝ} (ha : 0 < a)
    (x : UnitInterval) (hx : (x : ℝ) ≤ a) :
    (lowerBlockCoordinate a x : ℝ) = (x : ℝ) / a := by
  rw [lowerBlockCoordinate, Set.projIcc_of_mem]
  exact ⟨div_nonneg x.property.1 ha.le, (div_le_one ha).2 hx⟩

theorem coe_upperBlockCoordinate {a : ℝ} (ha : a < 1)
    (x : UnitInterval) (hx : a ≤ (x : ℝ)) :
    (upperBlockCoordinate a x : ℝ) = ((x : ℝ) - a) / (1 - a) := by
  rw [upperBlockCoordinate, Set.projIcc_of_mem]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr ha.le)
  · apply (div_le_one (sub_pos.mpr ha)).2
    linarith [x.property.2]

/-- A real point of `[0,1]`, regarded as a point of the unit interval. -/
def unitIntervalPoint (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) : UnitInterval :=
  ⟨a, ha⟩

/-- The affine embedding of the unit interval onto the lower block. -/
def lowerBlockMap (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (x : UnitInterval) : UnitInterval :=
  ⟨a * (x : ℝ), by
      constructor
      · exact mul_nonneg ha.1 x.property.1
      · calc
          a * (x : ℝ) ≤ a * 1 :=
            mul_le_mul_of_nonneg_left x.property.2 ha.1
          _ ≤ 1 := by simpa using ha.2⟩

/-- The affine embedding of the unit interval onto the upper block. -/
def upperBlockMap (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (x : UnitInterval) : UnitInterval :=
  ⟨a + (1 - a) * (x : ℝ), by
      constructor
      · exact ha.1.trans (le_add_of_nonneg_right
          (mul_nonneg (sub_nonneg.mpr ha.2) x.property.1))
      · calc
          a + (1 - a) * (x : ℝ) ≤ a + (1 - a) * 1 :=
            by
              simpa [add_comm] using
                add_le_add_left
                  (mul_le_mul_of_nonneg_left x.property.2 (sub_nonneg.mpr ha.2)) a
          _ = 1 := by ring⟩

@[fun_prop]
theorem measurable_lowerBlockMap (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
    Measurable (lowerBlockMap a ha) := by
  exact Measurable.subtype_mk (by fun_prop)

@[fun_prop]
theorem measurable_upperBlockMap (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
    Measurable (upperBlockMap a ha) := by
  exact Measurable.subtype_mk (by fun_prop)

@[simp] theorem coe_lowerBlockMap (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (x : UnitInterval) :
    (lowerBlockMap a ha x : ℝ) = a * (x : ℝ) := by
  simp [lowerBlockMap]

@[simp] theorem coe_upperBlockMap (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (x : UnitInterval) :
    (upperBlockMap a ha x : ℝ) = a + (1 - a) * (x : ℝ) := by
  simp [upperBlockMap]

@[simp] theorem lowerBlockCoordinate_lowerBlockMap {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (ha0 : 0 < a) (x : UnitInterval) :
    lowerBlockCoordinate a (lowerBlockMap a ha x) = x := by
  apply Subtype.ext
  have hle : (lowerBlockMap a ha x : ℝ) ≤ a := by
    rw [coe_lowerBlockMap]
    exact mul_le_of_le_one_right ha0.le x.property.2
  rw [coe_lowerBlockCoordinate ha0 _ hle, coe_lowerBlockMap]
  exact mul_div_cancel_left₀ (x : ℝ) ha0.ne'

@[simp] theorem upperBlockCoordinate_upperBlockMap {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (ha1 : a < 1) (x : UnitInterval) :
    upperBlockCoordinate a (upperBlockMap a ha x) = x := by
  apply Subtype.ext
  have hge : a ≤ (upperBlockMap a ha x : ℝ) := by
    rw [coe_upperBlockMap]
    exact le_add_of_nonneg_right
      (mul_nonneg (sub_nonneg.mpr ha.2) x.property.1)
  rw [coe_upperBlockCoordinate ha1 _ hge, coe_upperBlockMap]
  apply (div_eq_iff (sub_ne_zero.mpr ha1.ne')).2
  ring

private theorem map_lower_real_restrict {a : ℝ} (ha : 0 < a) :
    Measure.map (a * ·)
        (ENNReal.ofReal a • volume.restrict (Icc (0 : ℝ) 1)) =
      volume.restrict (Icc (0 : ℝ) a) := by
  have hpre : (a * ·) ⁻¹' Icc (0 : ℝ) a = Icc (0 : ℝ) 1 := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor
    · rintro ⟨hx0, hxa⟩
      constructor <;> nlinarith
    · rintro ⟨hx0, hx1⟩
      constructor <;> nlinarith
  rw [Measure.map_smul, ← hpre,
    ← Measure.restrict_map (measurable_const_mul a) measurableSet_Icc,
    Real.map_volume_mul_left ha.ne', abs_of_pos (inv_pos.mpr ha),
    Measure.restrict_smul, smul_smul]
  simp [← ENNReal.ofReal_mul ha.le, ha.ne']

/-- Lebesgue measure on the lower block is the image of `a` times normalized
unit-interval measure under the lower affine map. -/
theorem measurePreserving_lowerBlockMap {a : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    MeasurePreserving (lowerBlockMap a ⟨ha.1.le, ha.2.le⟩)
      (ENNReal.ofReal a • volume)
      (volume.restrict (Iic (unitIntervalPoint a ⟨ha.1.le, ha.2.le⟩))) := by
  let ha' : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1.le, ha.2.le⟩
  let A : UnitInterval := unitIntervalPoint a ha'
  have hpre : ((↑) : UnitInterval → ℝ) ⁻¹' Icc (0 : ℝ) a = Iic A := by
    ext x
    simp only [mem_preimage, mem_Icc, mem_Iic]
    change (0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ a) ↔ (x : ℝ) ≤ a
    exact and_iff_right x.property.1
  refine ⟨measurable_lowerBlockMap a ha', ?_⟩
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
  rw [Measure.map_map measurable_subtype_coe
      (measurable_lowerBlockMap a ha')]
  change Measure.map ((a * ·) ∘ ((↑) : UnitInterval → ℝ))
      (ENNReal.ofReal a • volume) =
    Measure.map ((↑) : UnitInterval → ℝ) (volume.restrict (Iic A))
  rw [← Measure.map_map (measurable_const_mul a) measurable_subtype_coe,
    Measure.map_smul, unitInterval.measurePreserving_coe.map_eq,
    map_lower_real_restrict ha.1, ← hpre,
    ← Measure.restrict_map measurable_subtype_coe measurableSet_Icc,
    unitInterval.measurePreserving_coe.map_eq,
    Measure.restrict_restrict measurableSet_Icc]
  rw [inter_eq_left.mpr]
  intro x hx
  exact ⟨hx.1, hx.2.trans ha.2.le⟩

private theorem map_upper_real_restrict {a : ℝ} (ha : a < 1) :
    Measure.map (fun x : ℝ ↦ a + (1 - a) * x)
        (ENNReal.ofReal (1 - a) • volume.restrict (Icc (0 : ℝ) 1)) =
      volume.restrict (Icc a 1) := by
  have hb : 0 < 1 - a := sub_pos.mpr ha
  have hmeas : Measurable (fun x : ℝ ↦ a + (1 - a) * x) := by fun_prop
  have hpre : (fun x : ℝ ↦ a + (1 - a) * x) ⁻¹' Icc a 1 =
      Icc (0 : ℝ) 1 := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor
    · rintro ⟨hx0, hx1⟩
      constructor <;> nlinarith
    · rintro ⟨hx0, hx1⟩
      constructor <;> nlinarith
  have hmap : Measure.map (fun x : ℝ ↦ a + (1 - a) * x) volume =
      ENNReal.ofReal (1 - a)⁻¹ • volume := by
    change Measure.map ((a + ·) ∘ ((1 - a) * ·)) volume = _
    rw [← Measure.map_map (measurable_const_add a)
        (measurable_const_mul (1 - a)),
      Real.map_volume_mul_left hb.ne', abs_of_pos (inv_pos.mpr hb),
      Measure.map_smul, map_add_left_eq_self]
  rw [Measure.map_smul, ← hpre,
    ← Measure.restrict_map hmeas measurableSet_Icc,
    hmap, Measure.restrict_smul, smul_smul]
  simp [← ENNReal.ofReal_mul hb.le, hb.ne']

/-- Lebesgue measure on the upper block is the image of `1-a` times
normalized unit-interval measure under the upper affine map. -/
theorem measurePreserving_upperBlockMap {a : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    MeasurePreserving (upperBlockMap a ⟨ha.1.le, ha.2.le⟩)
      (ENNReal.ofReal (1 - a) • volume)
      (volume.restrict (Ici (unitIntervalPoint a ⟨ha.1.le, ha.2.le⟩))) := by
  let ha' : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1.le, ha.2.le⟩
  let A : UnitInterval := unitIntervalPoint a ha'
  have hmeas : Measurable (fun x : ℝ ↦ a + (1 - a) * x) := by fun_prop
  have hpre : ((↑) : UnitInterval → ℝ) ⁻¹' Icc a 1 = Ici A := by
    ext x
    simp only [mem_preimage, mem_Icc, mem_Ici]
    change (a ≤ (x : ℝ) ∧ (x : ℝ) ≤ 1) ↔ a ≤ (x : ℝ)
    exact and_iff_left x.property.2
  refine ⟨measurable_upperBlockMap a ha', ?_⟩
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
  rw [Measure.map_map measurable_subtype_coe
      (measurable_upperBlockMap a ha')]
  change Measure.map ((fun x : ℝ ↦ a + (1 - a) * x) ∘
      ((↑) : UnitInterval → ℝ)) (ENNReal.ofReal (1 - a) • volume) =
    Measure.map ((↑) : UnitInterval → ℝ) (volume.restrict (Ici A))
  rw [← Measure.map_map hmeas measurable_subtype_coe,
    Measure.map_smul, unitInterval.measurePreserving_coe.map_eq,
    map_upper_real_restrict ha.2, ← hpre,
    ← Measure.restrict_map measurable_subtype_coe measurableSet_Icc,
    unitInterval.measurePreserving_coe.map_eq,
    Measure.restrict_restrict measurableSet_Icc]
  rw [inter_eq_left.mpr]
  intro x hx
  exact ⟨ha.1.le.trans hx.1, hx.2⟩

/-- One-dimensional change of variables on the lower affine block. -/
theorem integral_lowerBlockCoordinate {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (f : UnitInterval → ℝ) (hf : Measurable f) :
    (∫ x in Iio (unitIntervalPoint a ⟨ha.1.le, ha.2.le⟩),
        f (lowerBlockCoordinate a x) ∂volume) =
      a * ∫ x, f x ∂volume := by
  let ha' : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1.le, ha.2.le⟩
  let A : UnitInterval := unitIntervalPoint a ha'
  rw [setIntegral_congr_set (Iio_ae_eq_Iic : Iio A =ᵐ[volume] Iic A)]
  change (∫ x, f (lowerBlockCoordinate a x) ∂volume.restrict (Iic A)) = _
  let mp := measurePreserving_lowerBlockMap ha
  calc
    (∫ x, f (lowerBlockCoordinate a x) ∂volume.restrict (Iic A)) =
        ∫ x, f (lowerBlockCoordinate a x) ∂Measure.map
          (lowerBlockMap a ha') (ENNReal.ofReal a • volume) := by
            rw [mp.map_eq]
    _ = ∫ x, f (lowerBlockCoordinate a (lowerBlockMap a ha' x))
          ∂(ENNReal.ofReal a • volume) := by
            apply integral_map (measurable_lowerBlockMap a ha').aemeasurable
            exact (hf.comp (measurable_lowerBlockCoordinate a)).aestronglyMeasurable
    _ = a * ∫ x, f x ∂volume := by
      simp_rw [lowerBlockCoordinate_lowerBlockMap ha' ha.1]
      rw [integral_smul_measure]
      simp [ha.1.le]

/-- One-dimensional change of variables on the upper affine block. -/
theorem integral_upperBlockCoordinate {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (f : UnitInterval → ℝ) (hf : Measurable f) :
    (∫ x in Ici (unitIntervalPoint a ⟨ha.1.le, ha.2.le⟩),
        f (upperBlockCoordinate a x) ∂volume) =
      (1 - a) * ∫ x, f x ∂volume := by
  let ha' : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1.le, ha.2.le⟩
  let A : UnitInterval := unitIntervalPoint a ha'
  change (∫ x, f (upperBlockCoordinate a x) ∂volume.restrict (Ici A)) = _
  let mp := measurePreserving_upperBlockMap ha
  calc
    (∫ x, f (upperBlockCoordinate a x) ∂volume.restrict (Ici A)) =
        ∫ x, f (upperBlockCoordinate a x) ∂Measure.map
          (upperBlockMap a ha') (ENNReal.ofReal (1 - a) • volume) := by
            rw [mp.map_eq]
    _ = ∫ x, f (upperBlockCoordinate a (upperBlockMap a ha' x))
          ∂(ENNReal.ofReal (1 - a) • volume) := by
            apply integral_map (measurable_upperBlockMap a ha').aemeasurable
            exact (hf.comp (measurable_upperBlockCoordinate a)).aestronglyMeasurable
    _ = (1 - a) * ∫ x, f x ∂volume := by
      simp_rw [upperBlockCoordinate_upperBlockMap ha' ha.2]
      rw [integral_smul_measure]
      simp [sub_nonneg.mpr ha.2.le]

/-- Split a one-dimensional integral across the two affine blocks.  The
boundedness hypotheses are only used to justify Bochner integrability. -/
theorem integral_twoBlockLine {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (f g : UnitInterval → ℝ) (hf : Measurable f) (hg : Measurable g)
    (C : ℝ) (hfC : ∀ x, ‖f x‖ ≤ C) (hgC : ∀ x, ‖g x‖ ≤ C) :
    (∫ x : UnitInterval,
        if (x : ℝ) < a then f (lowerBlockCoordinate a x)
        else g (upperBlockCoordinate a x) ∂volume) =
      a * ∫ x, f x ∂volume + (1 - a) * ∫ x, g x ∂volume := by
  let A : UnitInterval := unitIntervalPoint a ⟨ha.1.le, ha.2.le⟩
  have hfl : Integrable (fun x : UnitInterval ↦
      f (lowerBlockCoordinate a x)) := by
    refine Integrable.of_bound
      ((hf.comp (measurable_lowerBlockCoordinate a)).aestronglyMeasurable) C ?_
    exact ae_of_all _ fun x ↦ hfC _
  have hgu : Integrable (fun x : UnitInterval ↦
      g (upperBlockCoordinate a x)) := by
    refine Integrable.of_bound
      ((hg.comp (measurable_upperBlockCoordinate a)).aestronglyMeasurable) C ?_
    exact ae_of_all _ fun x ↦ hgC _
  change (∫ x : UnitInterval, (Iio A).piecewise
      (fun x ↦ f (lowerBlockCoordinate a x))
      (fun x ↦ g (upperBlockCoordinate a x)) x ∂volume) = _
  rw [integral_piecewise measurableSet_Iio hfl.integrableOn hgu.integrableOn]
  simp only [compl_Iio]
  rw [integral_lowerBlockCoordinate ha f hf,
    integral_upperBlockCoordinate ha g hg]

/-! ## The raw two-block kernel and graphon -/

/-- A rescaled copy of `U` on the lower block, a rescaled copy of `V` on the
upper block, and the constant `c` on the two cross rectangles. -/
def twoBlockKernel (U V : Graphon) (a c : ℝ) (z : UnitSquare) : ℝ :=
  if (z.1 : ℝ) < a then
    if (z.2 : ℝ) < a then
      U.value (lowerBlockCoordinate a z.1, lowerBlockCoordinate a z.2)
    else c
  else if (z.2 : ℝ) < a then c
  else V.value (upperBlockCoordinate a z.1, upperBlockCoordinate a z.2)

@[fun_prop, measurability]
theorem measurable_twoBlockKernel (U V : Graphon) (a c : ℝ) :
    Measurable (twoBlockKernel U V a c) := by
  unfold twoBlockKernel
  have hx : MeasurableSet {z : UnitSquare | (z.1 : ℝ) < a} :=
    measurableSet_lt (measurable_subtype_coe.comp measurable_fst) measurable_const
  have hy : MeasurableSet {z : UnitSquare | (z.2 : ℝ) < a} :=
    measurableSet_lt (measurable_subtype_coe.comp measurable_snd) measurable_const
  refine Measurable.ite hx ?_ ?_
  · refine Measurable.ite hy ?_ measurable_const
    exact U.measurable_value.comp
      (((measurable_lowerBlockCoordinate a).comp measurable_fst).prodMk
        ((measurable_lowerBlockCoordinate a).comp measurable_snd))
  · refine Measurable.ite hy measurable_const ?_
    exact V.measurable_value.comp
      (((measurable_upperBlockCoordinate a).comp measurable_fst).prodMk
        ((measurable_upperBlockCoordinate a).comp measurable_snd))

theorem twoBlockKernel_nonneg (U V : Graphon) {a c : ℝ}
    (hc : 0 ≤ c) (z : UnitSquare) : 0 ≤ twoBlockKernel U V a c z := by
  by_cases hx : (z.1 : ℝ) < a <;> by_cases hy : (z.2 : ℝ) < a <;>
    simp [twoBlockKernel, hx, hy, hc, U.value_nonneg, V.value_nonneg]

theorem twoBlockKernel_le_one (U V : Graphon) {a c : ℝ}
    (hc : c ≤ 1) (z : UnitSquare) : twoBlockKernel U V a c z ≤ 1 := by
  by_cases hx : (z.1 : ℝ) < a <;> by_cases hy : (z.2 : ℝ) < a <;>
    simp [twoBlockKernel, hx, hy, hc, U.value_le_one, V.value_le_one]

theorem twoBlockKernel_swap (U V : Graphon) (a c : ℝ) (z : UnitSquare) :
    twoBlockKernel U V a c (z.2, z.1) = twoBlockKernel U V a c z := by
  by_cases hx : (z.1 : ℝ) < a <;> by_cases hy : (z.2 : ℝ) < a <;>
    simp [twoBlockKernel, hx, hy, U.value_symm, V.value_symm]

theorem integrable_twoBlockKernel (U V : Graphon) {a c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) :
    Integrable (twoBlockKernel U V a c) unitSquareMeasure := by
  refine Integrable.of_bound
    (measurable_twoBlockKernel U V a c).aestronglyMeasurable 1 ?_
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (twoBlockKernel_nonneg U V hc.1 z)]
  exact twoBlockKernel_le_one U V hc.2 z

/-- The arbitrary-graphon two-block construction with constant cross value
`c`. -/
def graphonTwoBlock (U V : Graphon) (a c : ℝ)
    (hc : c ∈ Icc (0 : ℝ) 1) : Graphon :=
  Graphon.ofFun (twoBlockKernel U V a c)
    (integrable_twoBlockKernel U V hc)
    (ae_of_all _ (twoBlockKernel_nonneg U V hc.1))
    (ae_of_all _ (twoBlockKernel_le_one U V hc.2))
    (twoBlockKernel_swap U V a c)

/-- Direct sum: the cross rectangles have value zero. -/
def graphonDirectSum (U V : Graphon) (a : ℝ) : Graphon :=
  graphonTwoBlock U V a 0 ⟨le_rfl, zero_le_one⟩

/-- Join: the cross rectangles have value one. -/
def graphonJoin (U V : Graphon) (a : ℝ) : Graphon :=
  graphonTwoBlock U V a 1 ⟨zero_le_one, le_rfl⟩

theorem graphonTwoBlock_ae_eq_kernel (U V : Graphon) (a c : ℝ)
    (hc : c ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂unitSquareMeasure,
      graphonTwoBlock U V a c hc z = twoBlockKernel U V a c z :=
  Graphon.coe_ofFun _ _ _ _ _

theorem graphonTwoBlock_value_ae_eq_kernel (U V : Graphon) (a c : ℝ)
    (hc : c ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂unitSquareMeasure,
      (graphonTwoBlock U V a c hc).value z = twoBlockKernel U V a c z := by
  filter_upwards [(graphonTwoBlock U V a c hc).value_ae_eq,
    graphonTwoBlock_ae_eq_kernel U V a c hc] with z hzValue hzKernel
  exact hzValue.trans hzKernel

/-! ## Exact integral formulas -/

/-- Exact formula for any bounded measurable scalar observable of a two-block
kernel.  This is the common change-of-variables engine for entropy and random
mass. -/
theorem integral_comp_twoBlockKernel {a c : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Icc (0 : ℝ) 1) (U V : Graphon)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (C : ℝ)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖φ t‖ ≤ C) :
    (∫ z : UnitSquare, φ (twoBlockKernel U V a c z) ∂unitSquareMeasure) =
      a ^ 2 * (∫ z : UnitSquare, φ (U.value z) ∂unitSquareMeasure) +
      (1 - a) ^ 2 * (∫ z : UnitSquare, φ (V.value z) ∂unitSquareMeasure) +
      2 * a * (1 - a) * φ c := by
  let rowU : UnitInterval → ℝ := fun x ↦
    ∫ y : UnitInterval, φ (U.value (x, y)) ∂volume
  let rowV : UnitInterval → ℝ := fun x ↦
    ∫ y : UnitInterval, φ (V.value (x, y)) ∂volume
  have hφU : Measurable (fun z : UnitSquare ↦ φ (U.value z)) :=
    hφ.comp U.measurable_value
  have hφV : Measurable (fun z : UnitSquare ↦ φ (V.value z)) :=
    hφ.comp V.measurable_value
  have hφK : Measurable (fun z : UnitSquare ↦
      φ (twoBlockKernel U V a c z)) :=
    hφ.comp (measurable_twoBlockKernel U V a c)
  have hIntU : Integrable (fun z : UnitSquare ↦ φ (U.value z))
      unitSquareMeasure := by
    refine Integrable.of_bound hφU.aestronglyMeasurable C ?_
    exact ae_of_all _ fun z ↦ hC _ (U.value_mem_Icc z)
  have hIntV : Integrable (fun z : UnitSquare ↦ φ (V.value z))
      unitSquareMeasure := by
    refine Integrable.of_bound hφV.aestronglyMeasurable C ?_
    exact ae_of_all _ fun z ↦ hC _ (V.value_mem_Icc z)
  have hIntK : Integrable (fun z : UnitSquare ↦
      φ (twoBlockKernel U V a c z)) unitSquareMeasure := by
    refine Integrable.of_bound hφK.aestronglyMeasurable C ?_
    exact ae_of_all _ fun z ↦ hC _ ⟨twoBlockKernel_nonneg U V hc.1 z,
      twoBlockKernel_le_one U V hc.2 z⟩
  have hrowUMeas : Measurable rowU :=
    hφU.stronglyMeasurable.integral_prod_right'.measurable
  have hrowVMeas : Measurable rowV :=
    hφV.stronglyMeasurable.integral_prod_right'.measurable
  have hrowUBound : ∀ x, ‖rowU x‖ ≤ C := by
    intro x
    have h := norm_integral_le_of_norm_le_const
      (μ := (volume : Measure UnitInterval))
      (ae_of_all _ fun y ↦ hC _ (U.value_mem_Icc (x, y)))
    simpa [rowU] using h
  have hrowVBound : ∀ x, ‖rowV x‖ ≤ C := by
    intro x
    have h := norm_integral_le_of_norm_le_const
      (μ := (volume : Measure UnitInterval))
      (ae_of_all _ fun y ↦ hC _ (V.value_mem_Icc (x, y)))
    simpa [rowV] using h
  have hinner : ∀ x : UnitInterval,
      (∫ y : UnitInterval, φ (twoBlockKernel U V a c (x, y)) ∂volume) =
        if (x : ℝ) < a then
          a * rowU (lowerBlockCoordinate a x) + (1 - a) * φ c
        else
          a * φ c + (1 - a) * rowV (upperBlockCoordinate a x) := by
    intro x
    by_cases hx : (x : ℝ) < a
    · have hline := integral_twoBlockLine ha
        (fun y : UnitInterval ↦
          φ (U.value (lowerBlockCoordinate a x, y)))
        (fun _ : UnitInterval ↦ φ c)
        (hφ.comp (U.measurable_value.comp
          (measurable_const.prodMk measurable_id))) measurable_const C
        (fun y ↦ hC _ (U.value_mem_Icc (lowerBlockCoordinate a x, y)))
        (fun _ ↦ hC _ hc)
      simpa [twoBlockKernel, hx, rowU, apply_ite] using hline
    · have hline := integral_twoBlockLine ha
        (fun _ : UnitInterval ↦ φ c)
        (fun y : UnitInterval ↦
          φ (V.value (upperBlockCoordinate a x, y)))
        measurable_const
        (hφ.comp (V.measurable_value.comp
          (measurable_const.prodMk measurable_id))) C
        (fun _ ↦ hC _ hc)
        (fun y ↦ hC _ (V.value_mem_Icc (upperBlockCoordinate a x, y)))
      simpa [twoBlockKernel, hx, rowV, apply_ite] using hline
  have hC0 : 0 ≤ C :=
    norm_nonneg (φ 0) |>.trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  let f : UnitInterval → ℝ := fun x ↦
    a * rowU x + (1 - a) * φ c
  let g : UnitInterval → ℝ := fun x ↦
    a * φ c + (1 - a) * rowV x
  have hfMeas : Measurable f := by
    exact (measurable_const.mul hrowUMeas).add measurable_const
  have hgMeas : Measurable g := by
    exact measurable_const.add (measurable_const.mul hrowVMeas)
  have hfBound : ∀ x, ‖f x‖ ≤ C := by
    intro x
    calc
      ‖f x‖ ≤ ‖a * rowU x‖ + ‖(1 - a) * φ c‖ := norm_add_le _ _
      _ = a * ‖rowU x‖ + (1 - a) * ‖φ c‖ := by
        simp [abs_of_nonneg ha.1.le, abs_of_nonneg (sub_nonneg.mpr ha.2.le)]
      _ ≤ a * C + (1 - a) * C := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hrowUBound x) ha.1.le)
          (mul_le_mul_of_nonneg_left (hC _ hc) (sub_nonneg.mpr ha.2.le))
      _ = C := by ring
  have hgBound : ∀ x, ‖g x‖ ≤ C := by
    intro x
    calc
      ‖g x‖ ≤ ‖a * φ c‖ + ‖(1 - a) * rowV x‖ := norm_add_le _ _
      _ = a * ‖φ c‖ + (1 - a) * ‖rowV x‖ := by
        simp [abs_of_nonneg ha.1.le, abs_of_nonneg (sub_nonneg.mpr ha.2.le)]
      _ ≤ a * C + (1 - a) * C := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hC _ hc) ha.1.le)
          (mul_le_mul_of_nonneg_left (hrowVBound x) (sub_nonneg.mpr ha.2.le))
      _ = C := by ring
  rw [MeasureTheory.integral_prod _ hIntK]
  rw [integral_congr_ae (ae_of_all _ hinner)]
  change (∫ x : UnitInterval,
      if (x : ℝ) < a then f (lowerBlockCoordinate a x)
      else g (upperBlockCoordinate a x) ∂volume) = _
  rw [integral_twoBlockLine ha f g hfMeas hgMeas C hfBound hgBound]
  have hrowUInt : (∫ x, rowU x ∂volume) =
      ∫ z : UnitSquare, φ (U.value z) ∂unitSquareMeasure := by
    exact (MeasureTheory.integral_prod _ hIntU).symm
  have hrowVInt : (∫ x, rowV x ∂volume) =
      ∫ z : UnitSquare, φ (V.value z) ∂unitSquareMeasure := by
    exact (MeasureTheory.integral_prod _ hIntV).symm
  have hrowUIntg : Integrable rowU := hIntU.integral_prod_left
  have hrowVIntg : Integrable rowV := hIntV.integral_prod_left
  have hfInt : (∫ x, f x ∂volume) =
      a * (∫ x, rowU x ∂volume) + (1 - a) * φ c := by
    simp only [f]
    rw [integral_add (hrowUIntg.const_mul a) (integrable_const _),
      integral_const_mul, integral_const]
    simp
  have hgInt : (∫ x, g x ∂volume) =
      a * φ c + (1 - a) * (∫ x, rowV x ∂volume) := by
    simp only [g]
    rw [integral_add (integrable_const _) (hrowVIntg.const_mul (1 - a)),
      integral_const, integral_const_mul]
    simp
  rw [hfInt, hgInt, hrowUInt, hrowVInt]
  ring

/-- Exact relative-entropy formula for the arbitrary two-block graphon. -/
theorem graphonRelativeEntropy_graphonTwoBlock {p a c : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (ha : a ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Icc (0 : ℝ) 1) (U V : Graphon) :
    graphonRelativeEntropy p (graphonTwoBlock U V a c hc) =
      a ^ 2 * graphonRelativeEntropy p U +
      (1 - a) ^ 2 * graphonRelativeEntropy p V +
      2 * a * (1 - a) * binaryRelativeEntropy p c := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (binaryRelativeEntropy_continuousOn hp).norm
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖binaryRelativeEntropy p t‖ ≤ C := by
    intro t ht
    exact hC ⟨t, ht, rfl⟩
  have hlog2 : Measurable log2 := by
    unfold log2
    exact Real.measurable_log.div_const _
  have hrel : Measurable (binaryRelativeEntropy p) := by
    unfold binaryRelativeEntropy
    exact (measurable_id.mul
      (hlog2.comp (measurable_id.div_const p))).add
      ((measurable_const.sub measurable_id).mul
        (hlog2.comp
          ((measurable_const.sub measurable_id).div_const (1 - p))))
  unfold graphonRelativeEntropy graphonValueFunctional
  calc
    (∫ z : UnitSquare,
        binaryRelativeEntropy p ((graphonTwoBlock U V a c hc).value z)
        ∂unitSquareMeasure) =
        ∫ z : UnitSquare, binaryRelativeEntropy p
          (twoBlockKernel U V a c z) ∂unitSquareMeasure := by
      apply integral_congr_ae
      filter_upwards [graphonTwoBlock_value_ae_eq_kernel U V a c hc] with z hz
      rw [hz]
    _ = a ^ 2 *
          (∫ z : UnitSquare, binaryRelativeEntropy p (U.value z)
            ∂unitSquareMeasure) +
        (1 - a) ^ 2 *
          (∫ z : UnitSquare, binaryRelativeEntropy p (V.value z)
            ∂unitSquareMeasure) +
        2 * a * (1 - a) * binaryRelativeEntropy p c := by
      exact integral_comp_twoBlockKernel ha hc U V (binaryRelativeEntropy p)
        hrel C hbound

/-- Relative entropy of a direct sum (zero cross block). -/
theorem graphonRelativeEntropy_graphonDirectSum {p a : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (ha : a ∈ Ioo (0 : ℝ) 1)
    (U V : Graphon) :
    graphonRelativeEntropy p (graphonDirectSum U V a) =
      a ^ 2 * graphonRelativeEntropy p U +
      (1 - a) ^ 2 * graphonRelativeEntropy p V +
      2 * a * (1 - a) * binaryRelativeEntropy p 0 := by
  exact graphonRelativeEntropy_graphonTwoBlock hp ha
    ⟨le_rfl, zero_le_one⟩ U V

/-- Relative entropy of a join (one cross block). -/
theorem graphonRelativeEntropy_graphonJoin {p a : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (ha : a ∈ Ioo (0 : ℝ) 1)
    (U V : Graphon) :
    graphonRelativeEntropy p (graphonJoin U V a) =
      a ^ 2 * graphonRelativeEntropy p U +
      (1 - a) ^ 2 * graphonRelativeEntropy p V +
      2 * a * (1 - a) * binaryRelativeEntropy p 1 := by
  exact graphonRelativeEntropy_graphonTwoBlock hp ha
    ⟨zero_le_one, le_rfl⟩ U V

/-- A direct-sum perturbation converges back to its lower-block graphon as the
lower block fills the unit interval. -/
theorem graphonRelativeEntropy_graphonDirectSum_tendsto_one {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (U V : Graphon) :
    Tendsto (fun a : ℝ ↦ graphonRelativeEntropy p (graphonDirectSum U V a))
      (𝓝[<] (1 : ℝ)) (𝓝 (graphonRelativeEntropy p U)) := by
  let q : ℝ → ℝ := fun a ↦
    a ^ 2 * graphonRelativeEntropy p U +
      (1 - a) ^ 2 * graphonRelativeEntropy p V +
      2 * a * (1 - a) * binaryRelativeEntropy p 0
  have hqcont : ContinuousAt q 1 := by
    dsimp [q]
    fun_prop
  have hq : Tendsto q (𝓝[<] (1 : ℝ))
      (𝓝 (graphonRelativeEntropy p U)) := by
    have hqone : q 1 = graphonRelativeEntropy p U := by
      dsimp [q]
      ring
    rw [← hqone]
    exact hqcont.tendsto.mono_left inf_le_left
  have hpos_nhds : ∀ᶠ a : ℝ in 𝓝 (1 : ℝ), a ∈ Ioi (0 : ℝ) :=
    Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)
  have hpos : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), 0 < a :=
    Filter.Eventually.filter_mono inf_le_left hpos_nhds
  have heq :
      (fun a : ℝ ↦ graphonRelativeEntropy p (graphonDirectSum U V a))
        =ᶠ[𝓝[<] (1 : ℝ)] q := by
    filter_upwards [eventually_mem_nhdsWithin, hpos] with a ha1 ha0
    exact graphonRelativeEntropy_graphonDirectSum hp ⟨ha0, ha1⟩ U V
  exact hq.congr' heq.symm

/-- The analogous one-sided convergence for join perturbations. -/
theorem graphonRelativeEntropy_graphonJoin_tendsto_one {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (U V : Graphon) :
    Tendsto (fun a : ℝ ↦ graphonRelativeEntropy p (graphonJoin U V a))
      (𝓝[<] (1 : ℝ)) (𝓝 (graphonRelativeEntropy p U)) := by
  let q : ℝ → ℝ := fun a ↦
    a ^ 2 * graphonRelativeEntropy p U +
      (1 - a) ^ 2 * graphonRelativeEntropy p V +
      2 * a * (1 - a) * binaryRelativeEntropy p 1
  have hqcont : ContinuousAt q 1 := by
    dsimp [q]
    fun_prop
  have hq : Tendsto q (𝓝[<] (1 : ℝ))
      (𝓝 (graphonRelativeEntropy p U)) := by
    have hqone : q 1 = graphonRelativeEntropy p U := by
      dsimp [q]
      ring
    rw [← hqone]
    exact hqcont.tendsto.mono_left inf_le_left
  have hpos_nhds : ∀ᶠ a : ℝ in 𝓝 (1 : ℝ), a ∈ Ioi (0 : ℝ) :=
    Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)
  have hpos : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), 0 < a :=
    Filter.Eventually.filter_mono inf_le_left hpos_nhds
  have heq :
      (fun a : ℝ ↦ graphonRelativeEntropy p (graphonJoin U V a))
        =ᶠ[𝓝[<] (1 : ℝ)] q := by
    filter_upwards [eventually_mem_nhdsWithin, hpos] with a ha1 ha0
    exact graphonRelativeEntropy_graphonJoin hp ⟨ha0, ha1⟩ U V
  exact hq.congr' heq.symm

/-! ## Random mass -/

/-- Indicator of genuinely random graphon values. -/
def randomValueIndicator (t : ℝ) : ℝ :=
  if t ∈ Ioo (0 : ℝ) 1 then 1 else 0

@[fun_prop]
theorem measurable_randomValueIndicator : Measurable randomValueIndicator := by
  unfold randomValueIndicator
  exact Measurable.ite measurableSet_Ioo measurable_const measurable_const

theorem norm_randomValueIndicator_le_one (t : ℝ) :
    ‖randomValueIndicator t‖ ≤ 1 := by
  unfold randomValueIndicator
  split_ifs <;> norm_num

/-- Random mass is the integral of the open-unit-interval indicator. -/
theorem graphonRandomMass_eq_integral_randomValueIndicator (W : Graphon) :
    graphonRandomMass W =
      ∫ z : UnitSquare, randomValueIndicator (W.value z) ∂unitSquareMeasure := by
  unfold graphonRandomMass
  rw [← integral_indicator_one
    (μ := unitSquareMeasure)
    (measurableSet_graphonRandomRegion W)]
  unfold graphonRandomRegion randomValueIndicator
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [Set.indicator, Pi.one_apply, mem_setOf_eq, mem_Ioo]

/-- Exact random-mass formula for the arbitrary two-block graphon. -/
theorem graphonRandomMass_graphonTwoBlock {a c : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1)
    (U V : Graphon) :
    graphonRandomMass (graphonTwoBlock U V a c hc) =
      a ^ 2 * graphonRandomMass U +
      (1 - a) ^ 2 * graphonRandomMass V +
      2 * a * (1 - a) * randomValueIndicator c := by
  rw [graphonRandomMass_eq_integral_randomValueIndicator]
  calc
    (∫ z : UnitSquare,
        randomValueIndicator ((graphonTwoBlock U V a c hc).value z)
        ∂unitSquareMeasure) =
        ∫ z : UnitSquare, randomValueIndicator
          (twoBlockKernel U V a c z) ∂unitSquareMeasure := by
      apply integral_congr_ae
      filter_upwards [graphonTwoBlock_value_ae_eq_kernel U V a c hc] with z hz
      rw [hz]
    _ = a ^ 2 *
          (∫ z : UnitSquare, randomValueIndicator (U.value z)
            ∂unitSquareMeasure) +
        (1 - a) ^ 2 *
          (∫ z : UnitSquare, randomValueIndicator (V.value z)
            ∂unitSquareMeasure) +
        2 * a * (1 - a) * randomValueIndicator c := by
      exact integral_comp_twoBlockKernel ha hc U V randomValueIndicator
        measurable_randomValueIndicator 1
        (fun t _ ↦ norm_randomValueIndicator_le_one t)
    _ = _ := by
      rw [← graphonRandomMass_eq_integral_randomValueIndicator U,
        ← graphonRandomMass_eq_integral_randomValueIndicator V]

@[simp] theorem graphonRandomMass_graphonDirectSum {a : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (U V : Graphon) :
    graphonRandomMass (graphonDirectSum U V a) =
      a ^ 2 * graphonRandomMass U +
      (1 - a) ^ 2 * graphonRandomMass V := by
  simpa [graphonDirectSum, randomValueIndicator] using
    graphonRandomMass_graphonTwoBlock ha ⟨le_rfl, zero_le_one⟩ U V

@[simp] theorem graphonRandomMass_graphonJoin {a : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (U V : Graphon) :
    graphonRandomMass (graphonJoin U V a) =
      a ^ 2 * graphonRandomMass U +
      (1 - a) ^ 2 * graphonRandomMass V := by
  simpa [graphonJoin, randomValueIndicator] using
    graphonRandomMass_graphonTwoBlock ha ⟨zero_le_one, le_rfl⟩ U V

/-- The upper copy gives a quantitative random-mass lower bound. -/
theorem one_sub_sq_mul_graphonRandomMass_le_directSum {a : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (U V : Graphon) :
    (1 - a) ^ 2 * graphonRandomMass V ≤
      graphonRandomMass (graphonDirectSum U V a) := by
  rw [graphonRandomMass_graphonDirectSum ha]
  exact le_add_of_nonneg_left
    (mul_nonneg (sq_nonneg a) (graphonRandomMass_nonneg U))

/-- A positive-random upper copy makes the direct sum positive-random. -/
theorem graphonRandomMass_graphonDirectSum_pos {a : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (U V : Graphon)
    (hV : 0 < graphonRandomMass V) :
    0 < graphonRandomMass (graphonDirectSum U V a) := by
  exact lt_of_lt_of_le
    (mul_pos (sq_pos_of_pos (sub_pos.mpr ha.2)) hV)
    (one_sub_sq_mul_graphonRandomMass_le_directSum ha U V)

/-- The same quantitative lower bound holds for joins. -/
theorem one_sub_sq_mul_graphonRandomMass_le_join {a : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (U V : Graphon) :
    (1 - a) ^ 2 * graphonRandomMass V ≤
      graphonRandomMass (graphonJoin U V a) := by
  rw [graphonRandomMass_graphonJoin ha]
  exact le_add_of_nonneg_left
    (mul_nonneg (sq_nonneg a) (graphonRandomMass_nonneg U))

/-- A positive-random upper copy makes the join positive-random. -/
theorem graphonRandomMass_graphonJoin_pos {a : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (U V : Graphon)
    (hV : 0 < graphonRandomMass V) :
    0 < graphonRandomMass (graphonJoin U V a) := by
  exact lt_of_lt_of_le
    (mul_pos (sq_pos_of_pos (sub_pos.mpr ha.2)) hV)
    (one_sub_sq_mul_graphonRandomMass_le_join ha U V)

/-! ## Finite-cube change of variables -/

/-- Scaling every marginal of a finite product measure scales the product by
the corresponding power. -/
theorem pi_const_smul {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (c : ℝ≥0∞) [∀ i, SigmaFinite (c • μ i)] :
    Measure.pi (fun i ↦ c • μ i) =
      c ^ Fintype.card ι • Measure.pi μ := by
  refine Measure.pi_eq (μ := fun i ↦ c • μ i) fun s hs ↦ ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp only [Finset.card_univ]

/-- An almost-everywhere zero function stays zero after coordinatewise
measure-preserving affine changes of variables. -/
theorem ae_zero_of_pi_coordinate_change
    {ι : Type*} [Fintype ι] {α β : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]
    (μ : ∀ i, Measure (α i)) (ν : ∀ i, Measure (β i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (c : ℝ≥0∞) [∀ i, SigmaFinite (c • μ i)]
    (g : ∀ i, α i → β i) (f : ∀ i, β i → α i)
    (hg : ∀ i, MeasurePreserving (g i) (c • μ i) (ν i))
    (hf : ∀ i, Measurable (f i))
    (hleft : ∀ i x, f i (g i x) = x)
    (q : (∀ i, α i) → ℝ) (hqmeas : Measurable q)
    (hq : q =ᵐ[Measure.pi μ] 0) :
    (fun x : ∀ i, β i ↦ q (fun i ↦ f i (x i))) =ᵐ[Measure.pi ν] 0 := by
  let mp : MeasurePreserving
      (fun x : ∀ i, α i ↦ fun i ↦ g i (x i))
      (Measure.pi (fun i ↦ c • μ i)) (Measure.pi ν) :=
    MeasureTheory.measurePreserving_pi (fun i ↦ c • μ i) ν hg
  have hq' : q =ᵐ[Measure.pi (fun i ↦ c • μ i)] 0 := by
    rw [pi_const_smul μ c]
    exact Measure.ae_smul_measure hq _
  have hsource :
      (fun x : ∀ i, α i ↦ q (fun i ↦ f i (g i (x i)))) =ᵐ[
        Measure.pi (fun i ↦ c • μ i)] 0 := by
    filter_upwards [hq'] with x hx
    simpa only [hleft] using hx
  have hcoord : Measurable (fun x : ∀ i, β i ↦ fun i ↦ f i (x i)) :=
    measurable_pi_lambda _ fun i ↦ (hf i).comp (measurable_pi_apply i)
  have hset : MeasurableSet {x : ∀ i, β i |
      q (fun i ↦ f i (x i)) = 0} :=
    measurableSet_eq_fun (hqmeas.comp hcoord) measurable_const
  rw [← mp.map_eq]
  exact (ae_map_iff mp.measurable.aemeasurable hset).2 hsource

theorem ae_zero_on_pi_restrict_of_coordinate_change
    {ι : Type*} [Fintype ι] {α β : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]
    (μ : ∀ i, Measure (α i)) (ν : ∀ i, Measure (β i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (s : ∀ i, Set (β i)) (c : ℝ≥0∞) [∀ i, SigmaFinite (c • μ i)]
    (g : ∀ i, α i → β i) (f : ∀ i, β i → α i)
    (hg : ∀ i, MeasurePreserving (g i) (c • μ i) ((ν i).restrict (s i)))
    (hf : ∀ i, Measurable (f i)) (hleft : ∀ i x, f i (g i x) = x)
    (q : (∀ i, α i) → ℝ) (hqmeas : Measurable q)
    (hq : q =ᵐ[Measure.pi μ] 0) :
    (fun x : ∀ i, β i ↦ q (fun i ↦ f i (x i))) =ᵐ[
      (Measure.pi ν).restrict (Set.univ.pi s)] 0 := by
  have hresult := ae_zero_of_pi_coordinate_change μ
    (fun i ↦ (ν i).restrict (s i)) c g f hg hf hleft q hqmeas hq
  rw [← Measure.restrict_pi_pi] at hresult
  exact hresult

theorem ae_zero_on_ae_eq_pi_restrict_of_coordinate_change
    {ι : Type*} [Fintype ι] {α β : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]
    (μ : ∀ i, Measure (α i)) (ν : ∀ i, Measure (β i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (s t : ∀ i, Set (β i))
    (hst : (Set.univ.pi s) =ᵐ[Measure.pi ν] (Set.univ.pi t))
    (c : ℝ≥0∞) [∀ i, SigmaFinite (c • μ i)]
    (g : ∀ i, α i → β i) (f : ∀ i, β i → α i)
    (hg : ∀ i, MeasurePreserving (g i) (c • μ i) ((ν i).restrict (t i)))
    (hf : ∀ i, Measurable (f i)) (hleft : ∀ i x, f i (g i x) = x)
    (q : (∀ i, α i) → ℝ) (hqmeas : Measurable q)
    (hq : q =ᵐ[Measure.pi μ] 0) :
    (fun x : ∀ i, β i ↦ q (fun i ↦ f i (x i))) =ᵐ[
      (Measure.pi ν).restrict (Set.univ.pi s)] 0 := by
  apply (ae_restrict_congr_set hst).2
  exact ae_zero_on_pi_restrict_of_coordinate_change
    μ ν t c g f hg hf hleft q hqmeas hq

/-- Unit-interval specialization of the change of variables on the all-lower
vertex cube. -/
theorem ae_zero_on_lower_cube {h : ℕ}
    (A : UnitInterval) (c : ℝ≥0∞) (g f : UnitInterval → UnitInterval)
    (hc : c ≠ ∞)
    (hg : MeasurePreserving g (c • volume) (volume.restrict (Iic A)))
    (hf : Measurable f) (hleft : ∀ x, f (g x) = x)
    (q : (Fin h → UnitInterval) → ℝ) (hqmeas : Measurable q)
    (hq : q =ᵐ[volume] 0) :
    (fun x : Fin h → UnitInterval ↦ q (fun i ↦ f (x i))) =ᵐ[
      (volume : Measure (Fin h → UnitInterval)).restrict
        (Set.univ.pi fun _ : Fin h ↦ Iio A)] 0 := by
  letI : IsFiniteMeasure (c • (volume : Measure UnitInterval)) :=
    Measure.smul_finite volume hc
  have hst : (Set.univ.pi fun _ : Fin h ↦ Iio A) =ᵐ[
      Measure.pi fun _ : Fin h ↦ (volume : Measure UnitInterval)]
      (Set.univ.pi fun _ : Fin h ↦ Iic A) := Measure.pi_Iio_ae_eq_pi_Iic
  simpa only [MeasureTheory.volume_pi] using
    (ae_zero_on_ae_eq_pi_restrict_of_coordinate_change
      (fun _ : Fin h ↦ (volume : Measure UnitInterval))
      (fun _ : Fin h ↦ (volume : Measure UnitInterval))
      (fun _ : Fin h ↦ Iio A) (fun _ : Fin h ↦ Iic A) hst c
      (fun _ : Fin h ↦ g) (fun _ : Fin h ↦ f) (fun _ ↦ hg)
      (fun _ ↦ hf) (fun _ ↦ hleft) q hqmeas hq)

/-- Unit-interval specialization of the change of variables on the all-upper
vertex cube. -/
theorem ae_zero_on_upper_cube {h : ℕ}
    (A : UnitInterval) (c : ℝ≥0∞) (g f : UnitInterval → UnitInterval)
    (hc : c ≠ ∞)
    (hg : MeasurePreserving g (c • volume) (volume.restrict (Ici A)))
    (hf : Measurable f) (hleft : ∀ x, f (g x) = x)
    (q : (Fin h → UnitInterval) → ℝ) (hqmeas : Measurable q)
    (hq : q =ᵐ[volume] 0) :
    (fun x : Fin h → UnitInterval ↦ q (fun i ↦ f (x i))) =ᵐ[
      (volume : Measure (Fin h → UnitInterval)).restrict
        (Set.univ.pi fun _ : Fin h ↦ Ici A)] 0 := by
  letI : IsFiniteMeasure (c • (volume : Measure UnitInterval)) :=
    Measure.smul_finite volume hc
  simpa only [MeasureTheory.volume_pi] using
    (ae_zero_on_pi_restrict_of_coordinate_change
      (fun _ : Fin h ↦ (volume : Measure UnitInterval))
      (fun _ : Fin h ↦ (volume : Measure UnitInterval))
      (fun _ : Fin h ↦ Ici A) c
      (fun _ : Fin h ↦ g) (fun _ : Fin h ↦ f) (fun _ ↦ hg)
      (fun _ ↦ hf) (fun _ ↦ hleft) q hqmeas hq)

/-! ## Raw induced integrands for the two-block kernel -/

/-- Evaluate the raw two-block kernel on an unordered pair of vertex
coordinates. -/
def twoBlockPairValue {h : ℕ} (U V : Graphon) (a c : ℝ)
    (x : Fin h → UnitInterval) : Sym2 (Fin h) → ℝ :=
  Sym2.lift ⟨fun i j ↦ twoBlockKernel U V a c (x i, x j), by
    intro i j
    exact (twoBlockKernel_swap U V a c (x i, x j)).symm⟩

@[simp] theorem twoBlockPairValue_mk {h : ℕ}
    (U V : Graphon) (a c : ℝ) (x : Fin h → UnitInterval)
    (i j : Fin h) :
    twoBlockPairValue U V a c x s(i, j) =
      twoBlockKernel U V a c (x i, x j) := rfl

theorem graphonPairValue_graphonTwoBlock_ae_eq {h : ℕ}
    (U V : Graphon) (a c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1)
    {i j : Fin h} (hij : i ≠ j) :
    (fun x : Fin h → UnitInterval ↦
      graphonPairValue (graphonTwoBlock U V a c hc) x s(i, j))
      =ᵐ[volume]
    (fun x ↦ twoBlockPairValue U V a c x s(i, j)) := by
  have hpull := (measurePreserving_pairProjection hij).quasiMeasurePreserving.ae
    (graphonTwoBlock_value_ae_eq_kernel U V a c hc)
  filter_upwards [hpull] with x hx
  simpa only [graphonPairValue_mk, twoBlockPairValue_mk] using hx

/-- The induced-density integrand formed directly from the raw two-block
kernel. -/
def twoBlockInducedIntegrand {h : ℕ}
    (H : SimpleGraph (Fin h)) (U V : Graphon) (a c : ℝ)
    (x : Fin h → UnitInterval) : ℝ :=
  (∏ e ∈ finiteGraphEdges H, twoBlockPairValue U V a c x e) *
    ∏ e ∈ finiteGraphEdges Hᶜ, (1 - twoBlockPairValue U V a c x e)

/-- The canonical graphon representative and its raw kernel give the same
induced integrand almost everywhere. -/
theorem graphonInducedIntegrand_graphonTwoBlock_ae_eq {h : ℕ}
    (H : SimpleGraph (Fin h)) (U V : Graphon) (a c : ℝ)
    (hc : c ∈ Icc (0 : ℝ) 1) :
    (fun x : Fin h → UnitInterval ↦
      graphonInducedIntegrand H (graphonTwoBlock U V a c hc) x)
      =ᵐ[volume]
    twoBlockInducedIntegrand H U V a c := by
  classical
  have hedge (e : Sym2 (Fin h)) (he : e ∈ finiteGraphEdges H) :
      (fun x : Fin h → UnitInterval ↦
        graphonPairValue (graphonTwoBlock U V a c hc) x e)
        =ᵐ[volume]
      (fun x ↦ twoBlockPairValue U V a c x e) := by
    revert he
    refine Sym2.inductionOn e ?_
    intro i j he
    exact graphonPairValue_graphonTwoBlock_ae_eq U V a c hc
      (H.ne_of_adj (by simpa using he))
  have hnonedge (e : Sym2 (Fin h)) (he : e ∈ finiteGraphEdges Hᶜ) :
      (fun x : Fin h → UnitInterval ↦
        graphonPairValue (graphonTwoBlock U V a c hc) x e)
        =ᵐ[volume]
      (fun x ↦ twoBlockPairValue U V a c x e) := by
    revert he
    refine Sym2.inductionOn e ?_
    intro i j he
    exact graphonPairValue_graphonTwoBlock_ae_eq U V a c hc
      (Hᶜ.ne_of_adj (by simpa using he))
  have hallEdges := (Filter.eventually_all_finset (finiteGraphEdges H)).2 hedge
  have hallNonedges :=
    (Filter.eventually_all_finset (finiteGraphEdges Hᶜ)).2 hnonedge
  filter_upwards [hallEdges, hallNonedges] with x hxEdge hxNonedge
  unfold graphonInducedIntegrand twoBlockInducedIntegrand
  congr 1
  · apply Finset.prod_congr rfl
    intro e he
    exact hxEdge e he
  · apply Finset.prod_congr rfl
    intro e he
    rw [hxNonedge e he]

/-- On the all-lower cube, the raw two-block induced integrand is the induced
integrand of the rescaled lower graphon. -/
theorem twoBlockInducedIntegrand_eq_lower {h : ℕ}
    (H : SimpleGraph (Fin h)) (U V : Graphon) {a c : ℝ}
    (x : Fin h → UnitInterval) (hx : ∀ i, (x i : ℝ) < a) :
    twoBlockInducedIntegrand H U V a c x =
      graphonInducedIntegrand H U (fun i ↦ lowerBlockCoordinate a (x i)) := by
  classical
  have hpair (e : Sym2 (Fin h)) :
      twoBlockPairValue U V a c x e =
        graphonPairValue U (fun i ↦ lowerBlockCoordinate a (x i)) e := by
    refine Sym2.inductionOn e ?_
    intro i j
    simp [twoBlockKernel, hx i, hx j]
  unfold twoBlockInducedIntegrand graphonInducedIntegrand
  congr 1
  · apply Finset.prod_congr rfl
    intro e _he
    exact hpair e
  · apply Finset.prod_congr rfl
    intro e _he
    rw [hpair e]

/-- On the all-upper cube, the raw two-block induced integrand is the induced
integrand of the rescaled upper graphon. -/
theorem twoBlockInducedIntegrand_eq_upper {h : ℕ}
    (H : SimpleGraph (Fin h)) (U V : Graphon) {a c : ℝ}
    (x : Fin h → UnitInterval) (hx : ∀ i, a ≤ (x i : ℝ)) :
    twoBlockInducedIntegrand H U V a c x =
      graphonInducedIntegrand H V (fun i ↦ upperBlockCoordinate a (x i)) := by
  classical
  have hpair (e : Sym2 (Fin h)) :
      twoBlockPairValue U V a c x e =
        graphonPairValue V (fun i ↦ upperBlockCoordinate a (x i)) e := by
    refine Sym2.inductionOn e ?_
    intro i j
    simp [twoBlockKernel, not_lt.mpr (hx i), not_lt.mpr (hx j)]
  unfold twoBlockInducedIntegrand graphonInducedIntegrand
  congr 1
  · apply Finset.prod_congr rfl
    intro e _he
    exact hpair e
  · apply Finset.prod_congr rfl
    intro e _he
    rw [hpair e]

/-! ## Connectivity preliminaries -/

/-- The induced density of the unique graph on one vertex is one. -/
theorem graphonInducedDensity_fin_one (H : SimpleGraph (Fin 1))
    (W : Graphon) :
    graphonInducedDensity H W = 1 := by
  classical
  have hEdges (G : SimpleGraph (Fin 1)) : finiteGraphEdges G = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro e he
    refine Sym2.inductionOn e ?_
    intro i j
    have hadj : G.Adj i j := by simpa using he
    exact (G.ne_of_adj hadj) (Subsingleton.elim i j)
  simp [graphonInducedDensity, graphonInducedIntegrand, hEdges]

/-- A positive-random induced-free graphon can exist only when the forbidden
graph has at least two vertices. -/
theorem two_le_of_positiveRandomInducedFreeGraphons_nonempty {h : ℕ}
    (H : SimpleGraph (Fin h))
    (hne : (positiveRandomInducedFreeGraphons H).Nonempty) :
    2 ≤ h := by
  rcases hne with ⟨W, hfree, _hrandom⟩
  by_contra hnot
  have hh : h = 0 ∨ h = 1 := by omega
  rcases hh with rfl | rfl
  · simpa [graphonInducedDensity_fin_zero] using hfree
  · simpa [graphonInducedDensity_fin_one] using hfree

/-- Every finite graph with at least two vertices is connected, or its
complement is connected. -/
theorem connected_or_complement_connected {h : ℕ}
    (H : SimpleGraph (Fin h)) (hh : 2 ≤ h) :
    H.Connected ∨ Hᶜ.Connected := by
  let _ : Nonempty (Fin h) := Fin.pos_iff_nonempty.mp (by omega)
  exact H.connected_or_connected_compl

/-- A nonconstant two-coloring of a connected graph has a bichromatic
edge. -/
theorem exists_crossing_adj {V : Type*} [Nonempty V]
    (G : SimpleGraph V) (hG : G.Connected) (b : V → Bool)
    {u v : V} (huv : b u ≠ b v) :
    ∃ i j, G.Adj i j ∧ b i ≠ b j := by
  by_contra! h
  have walk_eq {i j : V} (p : G.Walk i j) : b i = b j := by
    induction p with
    | nil => rfl
    | cons hadj p ih => exact (h _ _ hadj).trans ih
  exact huv ((hG u v).elim walk_eq)

/-- A mixed assignment kills the raw direct-sum integrand when the forbidden
graph is connected. -/
theorem twoBlockInducedIntegrand_directSum_eq_zero_of_mixed {h : ℕ}
    (H : SimpleGraph (Fin h)) (hH : H.Connected)
    (U V : Graphon) (a : ℝ) (x : Fin h → UnitInterval)
    (hlower : ¬∀ i, (x i : ℝ) < a)
    (hupper : ¬∀ i, a ≤ (x i : ℝ)) :
    twoBlockInducedIntegrand H U V a 0 x = 0 := by
  classical
  push_neg at hlower hupper
  rcases hlower with ⟨v, hv⟩
  rcases hupper with ⟨u, hu⟩
  let b : Fin h → Bool := fun i ↦ decide ((x i : ℝ) < a)
  have hbu : b u = true := by simp [b, hu]
  have hbv : b v = false := by simp [b, not_lt.mpr hv]
  have huv : b u ≠ b v := by simp [hbu, hbv]
  let _ : Nonempty (Fin h) := ⟨u⟩
  rcases exists_crossing_adj H hH b huv with ⟨i, j, hij, hbij⟩
  have hzero : twoBlockPairValue U V a 0 x s(i, j) = 0 := by
    by_cases hi : (x i : ℝ) < a <;> by_cases hj : (x j : ℝ) < a
    · exfalso
      exact hbij (by simp [b, hi, hj])
    · simp [twoBlockKernel, hi, hj]
    · simp [twoBlockKernel, hi, hj]
    · exfalso
      exact hbij (by simp [b, hi, hj])
  have hEdge : s(i, j) ∈ finiteGraphEdges H := by simpa using hij
  unfold twoBlockInducedIntegrand
  rw [show (∏ e ∈ finiteGraphEdges H,
      twoBlockPairValue U V a 0 x e) = 0 by
    apply Finset.prod_eq_zero hEdge
    exact hzero]
  simp

/-- A mixed assignment kills the raw join integrand when the complement of
the forbidden graph is connected. -/
theorem twoBlockInducedIntegrand_join_eq_zero_of_mixed {h : ℕ}
    (H : SimpleGraph (Fin h)) (hH : Hᶜ.Connected)
    (U V : Graphon) (a : ℝ) (x : Fin h → UnitInterval)
    (hlower : ¬∀ i, (x i : ℝ) < a)
    (hupper : ¬∀ i, a ≤ (x i : ℝ)) :
    twoBlockInducedIntegrand H U V a 1 x = 0 := by
  classical
  push_neg at hlower hupper
  rcases hlower with ⟨v, hv⟩
  rcases hupper with ⟨u, hu⟩
  let b : Fin h → Bool := fun i ↦ decide ((x i : ℝ) < a)
  have hbu : b u = true := by simp [b, hu]
  have hbv : b v = false := by simp [b, not_lt.mpr hv]
  have huv : b u ≠ b v := by simp [hbu, hbv]
  let _ : Nonempty (Fin h) := ⟨u⟩
  rcases exists_crossing_adj Hᶜ hH b huv with ⟨i, j, hij, hbij⟩
  have hone : twoBlockPairValue U V a 1 x s(i, j) = 1 := by
    by_cases hi : (x i : ℝ) < a <;> by_cases hj : (x j : ℝ) < a
    · exfalso
      exact hbij (by simp [b, hi, hj])
    · simp [twoBlockKernel, hi, hj]
    · simp [twoBlockKernel, hi, hj]
    · exfalso
      exact hbij (by simp [b, hi, hj])
  have hNonedge : s(i, j) ∈ finiteGraphEdges Hᶜ := by simpa using hij
  unfold twoBlockInducedIntegrand
  rw [show (∏ e ∈ finiteGraphEdges Hᶜ,
      (1 - twoBlockPairValue U V a 1 x e)) = 0 by
    apply Finset.prod_eq_zero hNonedge
    rw [hone]
    ring]
  simp

/-! ## Preservation of induced-freeness -/

/-- Direct sums preserve induced-`H`-freeness when `H` is connected. -/
theorem graphonInducedDensity_graphonDirectSum_eq_zero_of_connected {h : ℕ}
    (H : SimpleGraph (Fin h)) (hH : H.Connected)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (U V : Graphon)
    (hU : graphonInducedDensity H U = 0)
    (hV : graphonInducedDensity H V = 0) :
    graphonInducedDensity H (graphonDirectSum U V a) = 0 := by
  let ha' : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1.le, ha.2.le⟩
  let A : UnitInterval := unitIntervalPoint a ha'
  have hUae : graphonInducedIntegrand H U =ᵐ[volume] 0 := by
    apply (integral_eq_zero_iff_of_nonneg
      (graphonInducedIntegrand_nonneg H U)
      (integrable_graphonInducedIntegrand H U)).1
    exact hU
  have hVae : graphonInducedIntegrand H V =ᵐ[volume] 0 := by
    apply (integral_eq_zero_iff_of_nonneg
      (graphonInducedIntegrand_nonneg H V)
      (integrable_graphonInducedIntegrand H V)).1
    exact hV
  have hLower :
      (fun x : Fin h → UnitInterval ↦
        graphonInducedIntegrand H U
          (fun i ↦ lowerBlockCoordinate a (x i))) =ᵐ[
        (volume : Measure (Fin h → UnitInterval)).restrict
          (Set.univ.pi fun _ : Fin h ↦ Iio A)] 0 := by
    exact ae_zero_on_lower_cube A (ENNReal.ofReal a)
      (lowerBlockMap a ha') (lowerBlockCoordinate a)
      ENNReal.ofReal_ne_top (measurePreserving_lowerBlockMap ha)
      (measurable_lowerBlockCoordinate a)
      (lowerBlockCoordinate_lowerBlockMap ha' ha.1)
      (graphonInducedIntegrand H U)
      (measurable_graphonInducedIntegrand H U) hUae
  have hUpper :
      (fun x : Fin h → UnitInterval ↦
        graphonInducedIntegrand H V
          (fun i ↦ upperBlockCoordinate a (x i))) =ᵐ[
        (volume : Measure (Fin h → UnitInterval)).restrict
          (Set.univ.pi fun _ : Fin h ↦ Ici A)] 0 := by
    exact ae_zero_on_upper_cube A (ENNReal.ofReal (1 - a))
      (upperBlockMap a ha') (upperBlockCoordinate a)
      ENNReal.ofReal_ne_top (measurePreserving_upperBlockMap ha)
      (measurable_upperBlockCoordinate a)
      (upperBlockCoordinate_upperBlockMap ha' ha.2)
      (graphonInducedIntegrand H V)
      (measurable_graphonInducedIntegrand H V) hVae
  have hLowerImp := ae_imp_of_ae_restrict hLower
  have hUpperImp := ae_imp_of_ae_restrict hUpper
  have hRaw : twoBlockInducedIntegrand H U V a 0 =ᵐ[volume] 0 := by
    filter_upwards [hLowerImp, hUpperImp] with x hxLower hxUpper
    by_cases hxL : ∀ i, (x i : ℝ) < a
    · rw [twoBlockInducedIntegrand_eq_lower H U V x hxL]
      apply hxLower
      intro i _hi
      change (x i : ℝ) < a
      exact hxL i
    · by_cases hxU : ∀ i, a ≤ (x i : ℝ)
      · rw [twoBlockInducedIntegrand_eq_upper H U V x hxU]
        apply hxUpper
        intro i _hi
        change a ≤ (x i : ℝ)
        exact hxU i
      · exact twoBlockInducedIntegrand_directSum_eq_zero_of_mixed
          H hH U V a x hxL hxU
  unfold graphonInducedDensity graphonDirectSum
  apply integral_eq_zero_of_ae
  filter_upwards [graphonInducedIntegrand_graphonTwoBlock_ae_eq
    H U V a 0 ⟨le_rfl, zero_le_one⟩, hRaw] with x hx hzero
  rw [hx, hzero]

/-- Joins preserve induced-`H`-freeness when the complement of `H` is
connected. -/
theorem graphonInducedDensity_graphonJoin_eq_zero_of_complement_connected
    {h : ℕ} (H : SimpleGraph (Fin h)) (hH : Hᶜ.Connected)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (U V : Graphon)
    (hU : graphonInducedDensity H U = 0)
    (hV : graphonInducedDensity H V = 0) :
    graphonInducedDensity H (graphonJoin U V a) = 0 := by
  let ha' : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1.le, ha.2.le⟩
  let A : UnitInterval := unitIntervalPoint a ha'
  have hUae : graphonInducedIntegrand H U =ᵐ[volume] 0 := by
    apply (integral_eq_zero_iff_of_nonneg
      (graphonInducedIntegrand_nonneg H U)
      (integrable_graphonInducedIntegrand H U)).1
    exact hU
  have hVae : graphonInducedIntegrand H V =ᵐ[volume] 0 := by
    apply (integral_eq_zero_iff_of_nonneg
      (graphonInducedIntegrand_nonneg H V)
      (integrable_graphonInducedIntegrand H V)).1
    exact hV
  have hLower :
      (fun x : Fin h → UnitInterval ↦
        graphonInducedIntegrand H U
          (fun i ↦ lowerBlockCoordinate a (x i))) =ᵐ[
        (volume : Measure (Fin h → UnitInterval)).restrict
          (Set.univ.pi fun _ : Fin h ↦ Iio A)] 0 := by
    exact ae_zero_on_lower_cube A (ENNReal.ofReal a)
      (lowerBlockMap a ha') (lowerBlockCoordinate a)
      ENNReal.ofReal_ne_top (measurePreserving_lowerBlockMap ha)
      (measurable_lowerBlockCoordinate a)
      (lowerBlockCoordinate_lowerBlockMap ha' ha.1)
      (graphonInducedIntegrand H U)
      (measurable_graphonInducedIntegrand H U) hUae
  have hUpper :
      (fun x : Fin h → UnitInterval ↦
        graphonInducedIntegrand H V
          (fun i ↦ upperBlockCoordinate a (x i))) =ᵐ[
        (volume : Measure (Fin h → UnitInterval)).restrict
          (Set.univ.pi fun _ : Fin h ↦ Ici A)] 0 := by
    exact ae_zero_on_upper_cube A (ENNReal.ofReal (1 - a))
      (upperBlockMap a ha') (upperBlockCoordinate a)
      ENNReal.ofReal_ne_top (measurePreserving_upperBlockMap ha)
      (measurable_upperBlockCoordinate a)
      (upperBlockCoordinate_upperBlockMap ha' ha.2)
      (graphonInducedIntegrand H V)
      (measurable_graphonInducedIntegrand H V) hVae
  have hLowerImp := ae_imp_of_ae_restrict hLower
  have hUpperImp := ae_imp_of_ae_restrict hUpper
  have hRaw : twoBlockInducedIntegrand H U V a 1 =ᵐ[volume] 0 := by
    filter_upwards [hLowerImp, hUpperImp] with x hxLower hxUpper
    by_cases hxL : ∀ i, (x i : ℝ) < a
    · rw [twoBlockInducedIntegrand_eq_lower H U V x hxL]
      apply hxLower
      intro i _hi
      change (x i : ℝ) < a
      exact hxL i
    · by_cases hxU : ∀ i, a ≤ (x i : ℝ)
      · rw [twoBlockInducedIntegrand_eq_upper H U V x hxU]
        apply hxUpper
        intro i _hi
        change a ≤ (x i : ℝ)
        exact hxU i
      · exact twoBlockInducedIntegrand_join_eq_zero_of_mixed
          H hH U V a x hxL hxU
  unfold graphonInducedDensity graphonJoin
  apply integral_eq_zero_of_ae
  filter_upwards [graphonInducedIntegrand_graphonTwoBlock_ae_eq
    H U V a 1 ⟨zero_le_one, le_rfl⟩, hRaw] with x hx hzero
  rw [hx, hzero]

/-! ## Density of the positive-random variational domain -/

/-- Every induced-free graphon is arbitrarily well approximated in relative
entropy by a positive-random induced-free graphon, provided that this domain
is nonempty. -/
theorem exists_positiveRandomInducedFreeGraphon_relativeEntropy_close
    {h : ℕ} (H : SimpleGraph (Fin h)) (p : ℝ)
    (hp : p ∈ Ioo (0 : ℝ) 1)
    (hne : (positiveRandomInducedFreeGraphons H).Nonempty)
    (U : Graphon) (hU : graphonInducedDensity H U = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ W : Graphon,
      W ∈ positiveRandomInducedFreeGraphons H ∧
      |graphonRelativeEntropy p W - graphonRelativeEntropy p U| < ε := by
  have hh : 2 ≤ h :=
    two_le_of_positiveRandomInducedFreeGraphons_nonempty H hne
  rcases hne with ⟨V, hVfree, hVrandom⟩
  have hposNhds : ∀ᶠ a : ℝ in 𝓝 (1 : ℝ), a ∈ Ioi (0 : ℝ) :=
    Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)
  have hpos : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ), 0 < a :=
    Filter.Eventually.filter_mono inf_le_left hposNhds
  rcases connected_or_complement_connected H hh with hH | hH
  · have hclose : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ),
        dist (graphonRelativeEntropy p (graphonDirectSum U V a))
          (graphonRelativeEntropy p U) < ε :=
      Metric.tendsto_nhds.mp
        (graphonRelativeEntropy_graphonDirectSum_tendsto_one hp U V) ε hε
    rcases (hclose.and (hpos.and eventually_mem_nhdsWithin)).exists with
      ⟨a, haClose, ha0, ha1⟩
    have ha : a ∈ Ioo (0 : ℝ) 1 := ⟨ha0, ha1⟩
    refine ⟨graphonDirectSum U V a, ?_, ?_⟩
    · exact ⟨graphonInducedDensity_graphonDirectSum_eq_zero_of_connected
        H hH ha U V hU hVfree,
        graphonRandomMass_graphonDirectSum_pos ha U V hVrandom⟩
    · simpa [Real.dist_eq] using haClose
  · have hclose : ∀ᶠ a : ℝ in 𝓝[<] (1 : ℝ),
        dist (graphonRelativeEntropy p (graphonJoin U V a))
          (graphonRelativeEntropy p U) < ε :=
      Metric.tendsto_nhds.mp
        (graphonRelativeEntropy_graphonJoin_tendsto_one hp U V) ε hε
    rcases (hclose.and (hpos.and eventually_mem_nhdsWithin)).exists with
      ⟨a, haClose, ha0, ha1⟩
    have ha : a ∈ Ioo (0 : ℝ) 1 := ⟨ha0, ha1⟩
    refine ⟨graphonJoin U V a, ?_, ?_⟩
    · exact ⟨graphonInducedDensity_graphonJoin_eq_zero_of_complement_connected
        H hH ha U V hU hVfree,
        graphonRandomMass_graphonJoin_pos ha U V hVrandom⟩
    · simpa [Real.dist_eq] using haClose

/-- Restricting the induced-free variational problem to graphons with
positive random mass does not change its value, provided that restricted
domain is nonempty. -/
theorem positiveRandomInducedFreeRateValue_eq_full
    {h : ℕ} (H : SimpleGraph (Fin h)) (p : ℝ)
    (hp : p ∈ Ioo (0 : ℝ) 1)
    (hne : (positiveRandomInducedFreeGraphons H).Nonempty) :
    positiveRandomInducedFreeRateValue H p =
      inducedFreeGraphonRateValue H p := by
  apply le_antisymm
  · have hfullNonempty : (inducedFreeGraphons H).Nonempty :=
      hne.mono (positiveRandomInducedFreeGraphons_subset H)
    apply le_csInf
      (inducedFreeGraphonRateValues_nonempty H p hfullNonempty)
    rintro _ ⟨U, hU, rfl⟩
    apply le_of_forall_pos_le_add
    intro ε hε
    rcases exists_positiveRandomInducedFreeGraphon_relativeEntropy_close
        H p hp hne U hU ε hε with ⟨W, hW, hclose⟩
    calc
      positiveRandomInducedFreeRateValue H p ≤
          graphonRelativeEntropy p W :=
        positiveRandomInducedFreeRateValue_le H p hp hW
      _ ≤ graphonRelativeEntropy p U + ε := by
        linarith [abs_lt.mp hclose]
  · apply le_csInf
      (positiveRandomInducedFreeRateValues_nonempty H p hne)
    rintro _ ⟨W, hW, rfl⟩
    exact inducedFreeGraphonRateValue_le H p hp hW.1

end InducedStars
