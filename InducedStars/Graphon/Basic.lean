import InducedStars.Analysis.Entropy
import InducedStars.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Graphon basics

This file fixes the analytic carrier used throughout the project. A graphon is
an `L¹` (hence almost-everywhere) equivalence class on the unit square, together
with the almost-everywhere range and symmetry properties. Using `L¹` as the
carrier makes invariance under changes on null sets part of the definition.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal unitInterval

namespace InducedStars

/-- The closed real unit interval, equipped with Mathlib's normalized volume. -/
abbrev UnitInterval := unitInterval

/-- The unit square with its product measurable and probability structures. -/
abbrev UnitSquare := UnitInterval × UnitInterval

/-- The product of normalized interval volume with itself.

Naming this measure explicitly keeps the graphon carrier on Mathlib's canonical
product measurable space and avoids a product-measure typeclass diamond. -/
abbrev unitSquareMeasure : Measure UnitSquare :=
  (volume : Measure UnitInterval).prod (volume : Measure UnitInterval)

/-- Normalized volume of the unit interval has total mass one. -/
@[simp] theorem volume_unitInterval_univ :
    (volume : Measure UnitInterval) univ = 1 :=
  measure_univ

/-- Product volume on the unit square has total mass one. -/
@[simp] theorem volume_unitSquare_univ :
    unitSquareMeasure univ = 1 := by
  rw [Measure.prod_apply MeasurableSet.univ]
  simp

/-- A graphon is a symmetric, `[0,1]`-valued `L¹` function on the unit square.

All three side conditions are deliberately almost-everywhere statements: the
underlying object is insensitive to the choice of measurable representative.
-/
structure Graphon where
  toL1 : UnitSquare →₁[unitSquareMeasure] ℝ
  ae_nonneg : ∀ᵐ z ∂unitSquareMeasure, 0 ≤ toL1 z
  ae_le_one : ∀ᵐ z ∂unitSquareMeasure, toL1 z ≤ 1
  ae_symm : ∀ᵐ z ∂unitSquareMeasure, toL1 (z.2, z.1) = toL1 z

namespace Graphon

instance : CoeFun Graphon fun _ => UnitSquare → ℝ :=
  ⟨fun W ↦ W.toL1⟩

@[simp] theorem coe_toL1 (W : Graphon) :
    ((W.toL1 : UnitSquare → ℝ)) = W :=
  rfl

/-- Equality of graphons is equality almost everywhere of their representatives. -/
@[ext] theorem ext {W U : Graphon}
    (h : ∀ᵐ z ∂unitSquareMeasure, W z = U z) : W = U := by
  cases W with
  | mk f hf₀ hf₁ hfs =>
      cases U with
      | mk g hg₀ hg₁ hgs =>
          have hfg : f = g := Lp.ext h
          subst g
          rfl

/-- The chosen representative of a graphon is integrable. -/
@[fun_prop] theorem integrable (W : Graphon) : Integrable W unitSquareMeasure :=
  L1.integrable_coeFn W.toL1

/-- The chosen representative of a graphon is strongly measurable. -/
@[fun_prop] theorem stronglyMeasurable (W : Graphon) : StronglyMeasurable W :=
  L1.stronglyMeasurable_coeFn W.toL1

/-- The chosen representative of a graphon is almost everywhere strongly measurable. -/
@[fun_prop] theorem aestronglyMeasurable (W : Graphon) :
    AEStronglyMeasurable W unitSquareMeasure :=
  W.stronglyMeasurable.aestronglyMeasurable

/-- A graphon lies in the closed unit interval almost everywhere. -/
theorem ae_mem_Icc (W : Graphon) :
    ∀ᵐ z ∂unitSquareMeasure, W z ∈ Icc (0 : ℝ) 1 :=
  W.ae_nonneg.and W.ae_le_one

/-- A pointwise symmetric version of the chosen representative. -/
def rawSymm (W : Graphon) (z : UnitSquare) : ℝ :=
  (W z + W (z.2, z.1)) / 2

/-- The canonical measurable, pointwise symmetric, `[0,1]`-valued representative.

Clipping occurs after symmetrization.  This representative is convenient for
finite products, while `value_ae_eq` shows that it represents the same `L¹`
class as `W`.
-/
def value (W : Graphon) (z : UnitSquare) : ℝ :=
  max 0 (min 1 (W.rawSymm z))

@[fun_prop] theorem measurable_rawSymm (W : Graphon) : Measurable W.rawSymm := by
  unfold rawSymm
  fun_prop

@[fun_prop] theorem measurable_value (W : Graphon) : Measurable W.value := by
  unfold value
  fun_prop

theorem value_nonneg (W : Graphon) (z : UnitSquare) : 0 ≤ W.value z :=
  le_max_left _ _

theorem value_le_one (W : Graphon) (z : UnitSquare) : W.value z ≤ 1 := by
  exact max_le zero_le_one (min_le_left _ _)

theorem value_mem_Icc (W : Graphon) (z : UnitSquare) : W.value z ∈ Icc (0 : ℝ) 1 :=
  ⟨W.value_nonneg z, W.value_le_one z⟩

theorem rawSymm_swap (W : Graphon) (z : UnitSquare) :
    W.rawSymm (z.2, z.1) = W.rawSymm z := by
  simp only [rawSymm]
  rw [add_comm]

theorem value_swap (W : Graphon) (z : UnitSquare) :
    W.value (z.2, z.1) = W.value z := by
  simp only [value, W.rawSymm_swap]

/-- Two-argument form of pointwise symmetry for the canonical representative. -/
theorem value_symm (W : Graphon) (x y : UnitInterval) :
    W.value (x, y) = W.value (y, x) := by
  symm
  exact W.value_swap (x, y)

/-- The canonical pointwise-bounded representative equals the `L¹` representative a.e. -/
theorem value_ae_eq (W : Graphon) :
    ∀ᵐ z ∂unitSquareMeasure, W.value z = W z := by
  filter_upwards [W.ae_nonneg, W.ae_le_one, W.ae_symm] with z h₀ h₁ hs
  simp [value, rawSymm, hs, h₀, h₁]

/-- Build a graphon from an integrable representative and pointwise/a.e. graphon laws. -/
def ofFun (f : UnitSquare → ℝ) (hf : Integrable f unitSquareMeasure)
    (h₀ : ∀ᵐ z ∂unitSquareMeasure, 0 ≤ f z)
    (h₁ : ∀ᵐ z ∂unitSquareMeasure, f z ≤ 1)
    (hs : ∀ z, f (z.2, z.1) = f z) : Graphon where
  toL1 := hf.toL1 f
  ae_nonneg := by
    filter_upwards [hf.coeFn_toL1, h₀] with z hz h₀z
    rw [hz]
    exact h₀z
  ae_le_one := by
    filter_upwards [hf.coeFn_toL1, h₁] with z hz h₁z
    rw [hz]
    exact h₁z
  ae_symm := by
    have hmp : MeasurePreserving Prod.swap
        ((volume : Measure UnitInterval).prod (volume : Measure UnitInterval))
        ((volume : Measure UnitInterval).prod (volume : Measure UnitInterval)) :=
      Measure.measurePreserving_swap
    have hswap := hmp.quasiMeasurePreserving.ae_eq_comp hf.coeFn_toL1
    filter_upwards [hf.coeFn_toL1, hswap] with z hz hzswap
    simp only [Function.comp_apply, Prod.swap] at hzswap
    rw [hzswap, hs, hz]

/-- The `L¹` representative selected by `ofFun` agrees a.e. with the input. -/
theorem coe_ofFun (f : UnitSquare → ℝ) (hf : Integrable f unitSquareMeasure)
    (h₀ : ∀ᵐ z ∂unitSquareMeasure, 0 ≤ f z)
    (h₁ : ∀ᵐ z ∂unitSquareMeasure, f z ≤ 1)
    (hs : ∀ z, f (z.2, z.1) = f z) :
    ∀ᵐ z ∂unitSquareMeasure, ofFun f hf h₀ h₁ hs z = f z :=
  hf.coeFn_toL1

end Graphon

end InducedStars
