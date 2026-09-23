import InducedStars.Graphon.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Graphon distances

This file develops the analytic distances used by the graph-limit bridge.  The
cut norm is the literal supremum over measurable rectangles.  The cut distance
is the orbit pseudodistance obtained by precomposing with measure-preserving
measurable equivalences of the unit interval.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal unitInterval

namespace InducedStars

/-- Integrable real kernels on the unit square, modulo almost-everywhere equality. -/
abbrev IntegrableKernel := UnitSquare →₁[unitSquareMeasure] ℝ

/-- The `L¹` distance between graphons. -/
def graphonL1Dist (U W : Graphon) : ℝ := dist U.toL1 W.toL1

theorem graphonL1Dist_nonneg (U W : Graphon) : 0 ≤ graphonL1Dist U W :=
  dist_nonneg

theorem graphonL1Dist_comm (U W : Graphon) :
    graphonL1Dist U W = graphonL1Dist W U :=
  dist_comm _ _

theorem graphonL1Dist_triangle (U W Z : Graphon) :
    graphonL1Dist U Z ≤ graphonL1Dist U W + graphonL1Dist W Z :=
  dist_triangle _ _ _

@[simp] theorem graphonL1Dist_self (W : Graphon) : graphonL1Dist W W = 0 :=
  dist_self _

theorem graphonL1Dist_eq_zero {U W : Graphon} :
    graphonL1Dist U W = 0 ↔ U = W := by
  rw [graphonL1Dist, dist_eq_zero]
  constructor
  · intro h
    apply Graphon.ext
    exact Lp.ext_iff.mp h
  · exact congrArg Graphon.toL1

theorem graphonL1Dist_eq_integral (U W : Graphon) :
    graphonL1Dist U W = ∫ z, |U z - W z| ∂unitSquareMeasure := by
  rw [graphonL1Dist, L1.dist_eq_integral_dist]
  simp only [Real.dist_eq]

/-- Dominated convergence specialized to `[0,1]`-valued graphons. -/
theorem graphonL1Dist_tendsto_zero_of_ae
    (W : ℕ → Graphon) (U : Graphon)
    (hlim : ∀ᵐ z ∂unitSquareMeasure,
      Tendsto (fun n ↦ W n z) atTop (𝓝 (U z))) :
    Tendsto (fun n ↦ graphonL1Dist (W n) U) atTop (𝓝 0) := by
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun z : UnitSquare ↦ dist (W n z) (U z)) unitSquareMeasure := fun n ↦
    (W n).aestronglyMeasurable.dist U.aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ z ∂unitSquareMeasure,
      ‖dist (W n z) (U z)‖ ≤ (1 : UnitSquare → ℝ) z := by
    intro n
    filter_upwards [(W n).ae_mem_Icc, U.ae_mem_Icc] with z hzW hzU
    simp only [Pi.one_apply, Real.norm_eq_abs, abs_dist]
    simpa using Real.dist_le_of_mem_Icc hzW hzU
  have hpoint : ∀ᵐ z ∂unitSquareMeasure,
      Tendsto (fun n ↦ dist (W n z) (U z)) atTop (𝓝 0) := by
    filter_upwards [hlim] with z hz
    have hc : Tendsto (fun _ : ℕ ↦ U z) atTop (𝓝 (U z)) := tendsto_const_nhds
    simpa using hz.dist hc
  have hdc := tendsto_integral_of_dominated_convergence
    (μ := unitSquareMeasure) (fun _ ↦ (1 : ℝ)) hmeas
    (integrable_const 1) hbound hpoint
  simpa only [graphonL1Dist, L1.dist_eq_integral_dist,
    integral_zero] using hdc

/-- A pair of measurable vertex sets indexing a graphon cut. -/
structure MeasurableCut where
  left : Set UnitInterval
  right : Set UnitInterval
  measurable_left : MeasurableSet left
  measurable_right : MeasurableSet right

instance : Nonempty MeasurableCut :=
  ⟨⟨∅, ∅, MeasurableSet.empty, MeasurableSet.empty⟩⟩

namespace MeasurableCut

/-- The measurable rectangle belonging to a cut. -/
def rectangle (C : MeasurableCut) : Set UnitSquare := C.left ×ˢ C.right

theorem measurable_rectangle (C : MeasurableCut) : MeasurableSet C.rectangle :=
  C.measurable_left.prod C.measurable_right

/-- The empty cut, used to witness nonemptiness of the family of cut integrals. -/
def empty : MeasurableCut where
  left := ∅
  right := ∅
  measurable_left := MeasurableSet.empty
  measurable_right := MeasurableSet.empty

end MeasurableCut

/-- Integral of a kernel on a measurable cut rectangle. -/
def cutIntegral (K : IntegrableKernel) (C : MeasurableCut) : ℝ :=
  ∫ z in C.rectangle, K z ∂unitSquareMeasure

theorem abs_cutIntegral_le_norm (K : IntegrableKernel) (C : MeasurableCut) :
    |cutIntegral K C| ≤ ‖K‖ := by
  calc
    |cutIntegral K C| ≤ ∫ z in C.rectangle, |K z| ∂unitSquareMeasure :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, |K z| ∂unitSquareMeasure :=
      setIntegral_le_integral (L1.integrable_coeFn K).abs (Eventually.of_forall (by simp))
    _ = ‖K‖ := by
      rw [L1.norm_eq_integral_norm]
      simp only [Real.norm_eq_abs]

private theorem cutValues_nonempty (K : IntegrableKernel) :
    (Set.range fun C : MeasurableCut ↦ |cutIntegral K C|).Nonempty :=
  Set.range_nonempty _

private theorem cutValues_bddAbove (K : IntegrableKernel) :
    BddAbove (Set.range fun C : MeasurableCut ↦ |cutIntegral K C|) := by
  refine ⟨‖K‖, ?_⟩
  rintro _ ⟨C, rfl⟩
  exact abs_cutIntegral_le_norm K C

/-- The graphon cut norm, as a supremum over measurable rectangles. -/
def cutNorm (K : IntegrableKernel) : ℝ :=
  sSup (Set.range fun C : MeasurableCut ↦ |cutIntegral K C|)

theorem abs_cutIntegral_le_cutNorm (K : IntegrableKernel) (C : MeasurableCut) :
    |cutIntegral K C| ≤ cutNorm K := by
  exact le_csSup (cutValues_bddAbove K) ⟨C, rfl⟩

theorem cutNorm_nonneg (K : IntegrableKernel) : 0 ≤ cutNorm K := by
  exact (abs_nonneg (cutIntegral K MeasurableCut.empty)).trans
    (abs_cutIntegral_le_cutNorm K MeasurableCut.empty)

/-- The cut norm is bounded by the `L¹` norm. -/
theorem cutNorm_le_l1 (K : IntegrableKernel) : cutNorm K ≤ ‖K‖ := by
  apply csSup_le (cutValues_nonempty K)
  rintro _ ⟨C, rfl⟩
  exact abs_cutIntegral_le_norm K C

@[simp] theorem cutIntegral_zero (C : MeasurableCut) :
    cutIntegral (0 : IntegrableKernel) C = 0 := by
  simp [cutIntegral]

@[simp] theorem cutNorm_zero : cutNorm (0 : IntegrableKernel) = 0 := by
  apply le_antisymm
  · simpa using cutNorm_le_l1 (0 : IntegrableKernel)
  · exact cutNorm_nonneg _

theorem cutIntegral_add (K L : IntegrableKernel) (C : MeasurableCut) :
    cutIntegral (K + L) C = cutIntegral K C + cutIntegral L C := by
  rw [cutIntegral, cutIntegral, cutIntegral]
  calc
    (∫ z in C.rectangle, (K + L) z ∂unitSquareMeasure) =
        ∫ z in C.rectangle, (K z + L z) ∂unitSquareMeasure := by
      apply integral_congr_ae
      exact ae_restrict_of_ae (Lp.coeFn_add K L)
    _ = _ := integral_add
      (L1.integrable_coeFn K).integrableOn
      (L1.integrable_coeFn L).integrableOn

theorem cutNorm_add_le (K L : IntegrableKernel) :
    cutNorm (K + L) ≤ cutNorm K + cutNorm L := by
  apply csSup_le (cutValues_nonempty (K + L))
  rintro _ ⟨C, rfl⟩
  change |cutIntegral (K + L) C| ≤ cutNorm K + cutNorm L
  rw [cutIntegral_add]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_cutIntegral_le_cutNorm K C) (abs_cutIntegral_le_cutNorm L C))

@[simp] theorem cutIntegral_neg (K : IntegrableKernel) (C : MeasurableCut) :
    cutIntegral (-K) C = -cutIntegral K C := by
  rw [cutIntegral, cutIntegral]
  calc
    (∫ z in C.rectangle, (-K) z ∂unitSquareMeasure) =
        ∫ z in C.rectangle, -K z ∂unitSquareMeasure := by
      apply integral_congr_ae
      exact ae_restrict_of_ae (Lp.coeFn_neg K)
    _ = _ := by
      simpa only using
        (integral_neg (μ := unitSquareMeasure.restrict C.rectangle)
          (fun z : UnitSquare ↦ K z))

@[simp] theorem cutNorm_neg (K : IntegrableKernel) : cutNorm (-K) = cutNorm K := by
  simp only [cutNorm, cutIntegral_neg, abs_neg]

theorem cutNorm_sub_le (K L M : IntegrableKernel) :
    cutNorm (K - M) ≤ cutNorm (K - L) + cutNorm (L - M) := by
  have hker : K - M = (K - L) + (L - M) := by abel
  rw [hker]
  exact cutNorm_add_le _ _

theorem cutNorm_graphon_sub_le_l1 (U W : Graphon) :
    cutNorm (U.toL1 - W.toL1) ≤ graphonL1Dist U W := by
  simpa [graphonL1Dist, dist_eq_norm] using cutNorm_le_l1 (U.toL1 - W.toL1)

/-- A measure-preserving measurable bijection of the unit interval. -/
structure GraphonRelabeling where
  toMeasurableEquiv : UnitInterval ≃ᵐ UnitInterval
  measurePreserving : MeasurePreserving toMeasurableEquiv volume volume

namespace GraphonRelabeling

instance : CoeFun GraphonRelabeling fun _ ↦ UnitInterval → UnitInterval :=
  ⟨fun e ↦ e.toMeasurableEquiv⟩

@[ext] theorem ext {e f : GraphonRelabeling}
    (h : e.toMeasurableEquiv = f.toMeasurableEquiv) : e = f := by
  cases e
  cases f
  cases h
  rfl

/-- The identity relabeling. -/
def refl : GraphonRelabeling where
  toMeasurableEquiv := MeasurableEquiv.refl UnitInterval
  measurePreserving := MeasurePreserving.id volume

instance : Nonempty GraphonRelabeling := ⟨refl⟩

/-- The inverse of a measure-preserving relabeling. -/
def symm (e : GraphonRelabeling) : GraphonRelabeling where
  toMeasurableEquiv := e.toMeasurableEquiv.symm
  measurePreserving := e.measurePreserving.symm

/-- Composition of relabelings, in measurable-equivalence order. -/
def trans (e e' : GraphonRelabeling) : GraphonRelabeling where
  toMeasurableEquiv := e.toMeasurableEquiv.trans e'.toMeasurableEquiv
  measurePreserving := e.measurePreserving.trans e'.measurePreserving

/-- The diagonal action of a relabeling on the unit square. -/
def prodEquiv (e : GraphonRelabeling) : UnitSquare ≃ᵐ UnitSquare :=
  e.toMeasurableEquiv.prodCongr e.toMeasurableEquiv

@[simp] theorem prodEquiv_apply (e : GraphonRelabeling) (z : UnitSquare) :
    e.prodEquiv z = (e z.1, e z.2) := rfl

/-- The diagonal action preserves product volume. -/
theorem measurePreserving_prodEquiv (e : GraphonRelabeling) :
    MeasurePreserving e.prodEquiv unitSquareMeasure unitSquareMeasure := by
  convert e.measurePreserving.prod e.measurePreserving using 1
  ext z <;> simp

@[simp] theorem refl_apply (x : UnitInterval) : refl x = x := rfl

@[simp] theorem symm_apply_apply (e : GraphonRelabeling) (x : UnitInterval) :
    e.symm (e x) = x :=
  e.toMeasurableEquiv.left_inv x

@[simp] theorem apply_symm_apply (e : GraphonRelabeling) (x : UnitInterval) :
    e (e.symm x) = x :=
  e.toMeasurableEquiv.right_inv x

@[simp] theorem trans_symm_cancel_right (e g : GraphonRelabeling) :
    (g.trans e.symm).trans e = g := by
  apply GraphonRelabeling.ext
  apply MeasurableEquiv.ext
  funext x
  simp [trans]

@[simp] theorem trans_cancel_right_symm (e g : GraphonRelabeling) :
    (g.trans e).trans e.symm = g := by
  apply GraphonRelabeling.ext
  apply MeasurableEquiv.ext
  funext x
  simp [trans]

end GraphonRelabeling

/-- Pull an integrable kernel back by a measure-preserving relabeling. -/
def relabelKernel (K : IntegrableKernel) (e : GraphonRelabeling) : IntegrableKernel :=
  Lp.compMeasurePreserving e.prodEquiv e.measurePreserving_prodEquiv K

theorem coeFn_relabelKernel (K : IntegrableKernel) (e : GraphonRelabeling) :
    ∀ᵐ z ∂unitSquareMeasure, relabelKernel K e z = K (e z.1, e z.2) := by
  filter_upwards [Lp.coeFn_compMeasurePreserving K e.measurePreserving_prodEquiv] with z hz
  simpa [relabelKernel, Function.comp_apply] using hz

@[simp] theorem norm_relabelKernel (K : IntegrableKernel) (e : GraphonRelabeling) :
    ‖relabelKernel K e‖ = ‖K‖ := by
  exact Lp.norm_compMeasurePreserving K e.measurePreserving_prodEquiv

@[simp] theorem relabelKernel_zero (e : GraphonRelabeling) :
    relabelKernel (0 : IntegrableKernel) e = 0 := by
  simp [relabelKernel]

theorem relabelKernel_add (K L : IntegrableKernel) (e : GraphonRelabeling) :
    relabelKernel (K + L) e = relabelKernel K e + relabelKernel L e := by
  exact map_add _ _ _

theorem relabelKernel_neg (K : IntegrableKernel) (e : GraphonRelabeling) :
    relabelKernel (-K) e = -relabelKernel K e := by
  exact map_neg _ _

theorem relabelKernel_sub (K L : IntegrableKernel) (e : GraphonRelabeling) :
    relabelKernel (K - L) e = relabelKernel K e - relabelKernel L e := by
  exact map_sub _ _ _

@[simp] theorem relabelKernel_refl (K : IntegrableKernel) :
    relabelKernel K GraphonRelabeling.refl = K := by
  apply Lp.ext
  filter_upwards [coeFn_relabelKernel K GraphonRelabeling.refl] with z hz
  simpa using hz

/-- Pulling back twice composes the relabelings in action order. -/
theorem relabelKernel_relabelKernel (K : IntegrableKernel)
    (e e' : GraphonRelabeling) :
    relabelKernel (relabelKernel K e) e' =
      relabelKernel K (e'.trans e) := by
  apply Lp.ext
  have hpull := e'.measurePreserving_prodEquiv.quasiMeasurePreserving.ae
    (coeFn_relabelKernel K e)
  filter_upwards [coeFn_relabelKernel (relabelKernel K e) e', hpull,
    coeFn_relabelKernel K (e'.trans e)] with z hz hp hz'
  have hp' : relabelKernel K e (e' z.1, e' z.2) =
      K (e (e' z.1), e (e' z.2)) := by simpa using hp
  rw [hz, hp', hz']
  rfl

@[simp] theorem relabelKernel_symm_relabelKernel (K : IntegrableKernel)
    (e : GraphonRelabeling) :
    relabelKernel (relabelKernel K e.symm) e = K := by
  apply Lp.ext
  have hpull := e.measurePreserving_prodEquiv.quasiMeasurePreserving.ae
    (coeFn_relabelKernel K e.symm)
  filter_upwards [coeFn_relabelKernel (relabelKernel K e.symm) e, hpull] with z hz hp
  have hp' : relabelKernel K e.symm (e z.1, e z.2) =
      K (e.symm (e z.1), e.symm (e z.2)) := by simpa using hp
  rw [hz, hp']
  simp

@[simp] theorem relabelKernel_relabelKernel_symm (K : IntegrableKernel)
    (e : GraphonRelabeling) :
    relabelKernel (relabelKernel K e) e.symm = K := by
  apply Lp.ext
  have hpull := e.symm.measurePreserving_prodEquiv.quasiMeasurePreserving.ae
    (coeFn_relabelKernel K e)
  filter_upwards [coeFn_relabelKernel (relabelKernel K e) e.symm, hpull] with z hz hp
  have hp' : relabelKernel K e (e.symm z.1, e.symm z.2) =
      K (e (e.symm z.1), e (e.symm z.2)) := by simpa using hp
  rw [hz, hp']
  simp

namespace MeasurableCut

/-- Pull a measurable cut back along a relabeling. -/
def preimage (C : MeasurableCut) (e : GraphonRelabeling) : MeasurableCut where
  left := e ⁻¹' C.left
  right := e ⁻¹' C.right
  measurable_left := C.measurable_left.preimage e.toMeasurableEquiv.measurable
  measurable_right := C.measurable_right.preimage e.toMeasurableEquiv.measurable

/-- Push a measurable cut forward along a relabeling. -/
def image (C : MeasurableCut) (e : GraphonRelabeling) : MeasurableCut where
  left := e '' C.left
  right := e '' C.right
  measurable_left := e.toMeasurableEquiv.measurableEmbedding.measurableSet_image' C.measurable_left
  measurable_right := e.toMeasurableEquiv.measurableEmbedding.measurableSet_image' C.measurable_right

theorem rectangle_preimage (C : MeasurableCut) (e : GraphonRelabeling) :
    (C.preimage e).rectangle = e.prodEquiv ⁻¹' C.rectangle := by
  exact Set.preimage_prod_map_prod _ _ _ _

@[simp] theorem preimage_image (C : MeasurableCut) (e : GraphonRelabeling) :
    (C.image e).preimage e = C := by
  cases C
  simp only [image, preimage, Set.preimage_image_eq _ e.toMeasurableEquiv.injective]

end MeasurableCut

/-- Pullback preserves every cut integral. -/
theorem cutIntegral_relabelKernel_preimage
    (K : IntegrableKernel) (e : GraphonRelabeling) (C : MeasurableCut) :
    cutIntegral (relabelKernel K e) (C.preimage e) = cutIntegral K C := by
  rw [cutIntegral, cutIntegral, ← integral_indicator (C.preimage e).measurable_rectangle,
    ← integral_indicator C.measurable_rectangle]
  calc
    (∫ z, (C.preimage e).rectangle.indicator (relabelKernel K e) z
        ∂unitSquareMeasure) =
        ∫ z, C.rectangle.indicator K (e.prodEquiv z) ∂unitSquareMeasure := by
      apply integral_congr_ae
      filter_upwards [coeFn_relabelKernel K e] with z hz
      rw [MeasurableCut.rectangle_preimage]
      by_cases h : e.prodEquiv z ∈ C.rectangle
      · have hpre : z ∈ e.prodEquiv ⁻¹' C.rectangle := h
        rw [Set.indicator_of_mem hpre, Set.indicator_of_mem h, hz,
          GraphonRelabeling.prodEquiv_apply]
      · have hpre : z ∉ e.prodEquiv ⁻¹' C.rectangle := h
        have hpair : (e z.1, e z.2) ∉ C.rectangle := by simpa using h
        simp [Set.indicator, hpre, hpair]
    _ = ∫ z, C.rectangle.indicator K z ∂unitSquareMeasure :=
      e.measurePreserving_prodEquiv.integral_comp' _

/-- Relabeling preserves the cut norm. -/
@[simp] theorem cutNorm_relabelKernel (K : IntegrableKernel) (e : GraphonRelabeling) :
    cutNorm (relabelKernel K e) = cutNorm K := by
  apply le_antisymm
  · apply csSup_le (cutValues_nonempty (relabelKernel K e))
    rintro _ ⟨C, rfl⟩
    change |cutIntegral (relabelKernel K e) C| ≤ cutNorm K
    rw [← MeasurableCut.preimage_image C e,
      cutIntegral_relabelKernel_preimage]
    exact abs_cutIntegral_le_cutNorm K (C.image e)
  · apply csSup_le (cutValues_nonempty K)
    rintro _ ⟨C, rfl⟩
    change |cutIntegral K C| ≤ cutNorm (relabelKernel K e)
    rw [← cutIntegral_relabelKernel_preimage K e C]
    exact abs_cutIntegral_le_cutNorm (relabelKernel K e) (C.preimage e)

/-- The cut norm packaged as a nonnegative real. -/
def cutNormNN (K : IntegrableKernel) : NNReal := ⟨cutNorm K, cutNorm_nonneg K⟩

@[simp, norm_cast] theorem coe_cutNormNN (K : IntegrableKernel) :
    (cutNormNN K : ℝ) = cutNorm K := rfl

@[simp] theorem cutNormNN_zero : cutNormNN (0 : IntegrableKernel) = 0 := by
  ext
  simp

@[simp] theorem cutNormNN_neg (K : IntegrableKernel) :
    cutNormNN (-K) = cutNormNN K := by
  ext
  simp

/-- Cost of matching `U` to `W` through a specified relabeling. -/
def cutCostNN (U W : Graphon) (e : GraphonRelabeling) : NNReal :=
  cutNormNN (relabelKernel U.toL1 e - W.toL1)

/-- Cut distance as the infimum over measure-preserving interval relabelings. -/
def cutDistNN (U W : Graphon) : NNReal :=
  ⨅ e : GraphonRelabeling, cutCostNN U W e

/-- Real-valued graphon cut distance. -/
def cutDist (U W : Graphon) : ℝ := cutDistNN U W

theorem cutDistNN_le_cost (U W : Graphon) (e : GraphonRelabeling) :
    cutDistNN U W ≤ cutCostNN U W e := by
  unfold cutDistNN
  exact ciInf_le (OrderBot.bddBelow _) e

theorem cutDist_le_cost (U W : Graphon) (e : GraphonRelabeling) :
    cutDist U W ≤ cutNorm (relabelKernel U.toL1 e - W.toL1) := by
  exact_mod_cast cutDistNN_le_cost U W e

/-- The identity alignment bounds cut distance by cut norm. -/
theorem cutDist_le_cutNorm (U W : Graphon) :
    cutDist U W ≤ cutNorm (U.toL1 - W.toL1) := by
  simpa [cutCostNN] using cutDist_le_cost U W GraphonRelabeling.refl

/-- The cut distance is no larger than the `L¹` distance. -/
theorem cutDist_le_graphonL1Dist (U W : Graphon) :
    cutDist U W ≤ graphonL1Dist U W :=
  (cutDist_le_cutNorm U W).trans (cutNorm_graphon_sub_le_l1 U W)

theorem cutDist_nonneg (U W : Graphon) : 0 ≤ cutDist U W :=
  (cutDistNN U W).property

@[simp] theorem cutDist_self (W : Graphon) : cutDist W W = 0 := by
  apply le_antisymm
  · simpa using cutDist_le_cutNorm W W
  · exact cutDist_nonneg W W

/-- Inverting an alignment exchanges its two endpoints. -/
theorem cutCostNN_symm (U W : Graphon) (e : GraphonRelabeling) :
    cutCostNN W U e.symm = cutCostNN U W e := by
  apply NNReal.eq
  change cutNorm (relabelKernel W.toL1 e.symm - U.toL1) =
    cutNorm (relabelKernel U.toL1 e - W.toL1)
  calc
    cutNorm (relabelKernel W.toL1 e.symm - U.toL1) =
        cutNorm (relabelKernel
          (relabelKernel W.toL1 e.symm - U.toL1) e) :=
      (cutNorm_relabelKernel _ e).symm
    _ = cutNorm (W.toL1 - relabelKernel U.toL1 e) := by
      rw [relabelKernel_sub, relabelKernel_symm_relabelKernel]
    _ = cutNorm (-(relabelKernel U.toL1 e - W.toL1)) := by
      congr 1
      abel
    _ = cutNorm (relabelKernel U.toL1 e - W.toL1) := cutNorm_neg _

theorem cutDistNN_comm (U W : Graphon) : cutDistNN U W = cutDistNN W U := by
  apply le_antisymm
  · unfold cutDistNN
    apply le_ciInf
    intro e
    calc
      (⨅ e' : GraphonRelabeling, cutCostNN U W e') ≤ cutCostNN U W e.symm :=
        ciInf_le (OrderBot.bddBelow _) e.symm
      _ = cutCostNN W U e := cutCostNN_symm W U e
  · unfold cutDistNN
    apply le_ciInf
    intro e
    calc
      (⨅ e' : GraphonRelabeling, cutCostNN W U e') ≤ cutCostNN W U e.symm :=
        ciInf_le (OrderBot.bddBelow _) e.symm
      _ = cutCostNN U W e := cutCostNN_symm U W e

theorem cutDist_comm (U W : Graphon) : cutDist U W = cutDist W U := by
  exact congrArg (fun r : NNReal ↦ (r : ℝ)) (cutDistNN_comm U W)

/-- Composing two specified alignments gives the cut-cost triangle estimate. -/
theorem cutCostNN_trans_le (U W Z : Graphon) (e f : GraphonRelabeling) :
    cutCostNN U Z (f.trans e) ≤ cutCostNN U W e + cutCostNN W Z f := by
  apply NNReal.coe_le_coe.mp
  change cutNorm (relabelKernel U.toL1 (f.trans e) - Z.toL1) ≤
    cutNorm (relabelKernel U.toL1 e - W.toL1) +
      cutNorm (relabelKernel W.toL1 f - Z.toL1)
  calc
    cutNorm (relabelKernel U.toL1 (f.trans e) - Z.toL1) ≤
        cutNorm (relabelKernel U.toL1 (f.trans e) - relabelKernel W.toL1 f) +
          cutNorm (relabelKernel W.toL1 f - Z.toL1) :=
      cutNorm_sub_le _ _ _
    _ = cutNorm (relabelKernel U.toL1 e - W.toL1) +
          cutNorm (relabelKernel W.toL1 f - Z.toL1) := by
      congr 1
      rw [← cutNorm_relabelKernel (relabelKernel U.toL1 e - W.toL1) f,
        relabelKernel_sub, relabelKernel_relabelKernel]

theorem cutDistNN_triangle (U W Z : Graphon) :
    cutDistNN U Z ≤ cutDistNN U W + cutDistNN W Z := by
  unfold cutDistNN
  apply NNReal.le_iInf_add_iInf
  intro e f
  exact (ciInf_le (OrderBot.bddBelow _) (f.trans e)).trans
    (cutCostNN_trans_le U W Z e f)

theorem cutDist_triangle (U W Z : Graphon) :
    cutDist U Z ≤ cutDist U W + cutDist W Z := by
  exact_mod_cast cutDistNN_triangle U W Z

namespace Graphon

/-- The canonical pointwise representative after a vertex relabeling. -/
def relabelValue (W : Graphon) (e : GraphonRelabeling) (z : UnitSquare) : ℝ :=
  W.value (e z.1, e z.2)

theorem measurable_relabelValue (W : Graphon) (e : GraphonRelabeling) :
    Measurable (W.relabelValue e) := by
  exact W.measurable_value.comp e.prodEquiv.measurable

theorem integrable_relabelValue (W : Graphon) (e : GraphonRelabeling) :
    Integrable (W.relabelValue e) unitSquareMeasure := by
  apply Integrable.of_bound (W.measurable_relabelValue e).aestronglyMeasurable 1
  filter_upwards [] with z
  change |W.value (e z.1, e z.2)| ≤ 1
  rw [abs_of_nonneg (W.value_nonneg _)]
  exact W.value_le_one _

theorem relabelValue_nonneg (W : Graphon) (e : GraphonRelabeling) (z : UnitSquare) :
    0 ≤ W.relabelValue e z :=
  W.value_nonneg _

theorem relabelValue_le_one (W : Graphon) (e : GraphonRelabeling) (z : UnitSquare) :
    W.relabelValue e z ≤ 1 :=
  W.value_le_one _

theorem relabelValue_swap (W : Graphon) (e : GraphonRelabeling) (z : UnitSquare) :
    W.relabelValue e (z.2, z.1) = W.relabelValue e z :=
  W.value_symm _ _

/-- Pull a graphon back along a measure-preserving interval equivalence. -/
def relabel (W : Graphon) (e : GraphonRelabeling) : Graphon :=
  Graphon.ofFun (W.relabelValue e) (W.integrable_relabelValue e)
    (ae_of_all _ (W.relabelValue_nonneg e))
    (ae_of_all _ (W.relabelValue_le_one e))
    (W.relabelValue_swap e)

theorem relabel_ae_eq_value (W : Graphon) (e : GraphonRelabeling) :
    ∀ᵐ z ∂unitSquareMeasure, W.relabel e z = W.relabelValue e z :=
  Graphon.coe_ofFun _ _ _ _ _

/-- The graphon relabeling agrees with pullback on the `L¹` carrier. -/
theorem relabel_toL1 (W : Graphon) (e : GraphonRelabeling) :
    (W.relabel e).toL1 = relabelKernel W.toL1 e := by
  apply Lp.ext
  have hpull := e.measurePreserving_prodEquiv.quasiMeasurePreserving.ae W.value_ae_eq
  filter_upwards [W.relabel_ae_eq_value e, hpull,
    coeFn_relabelKernel W.toL1 e] with z hz hp hz'
  rw [hz, hz']
  simpa [relabelValue] using hp

@[simp] theorem relabel_refl (W : Graphon) :
    W.relabel GraphonRelabeling.refl = W := by
  apply Graphon.ext
  filter_upwards [W.relabel_ae_eq_value GraphonRelabeling.refl,
    W.value_ae_eq] with z hz hv
  simpa [relabelValue] using hz.trans hv

end Graphon

/-- A graphon and any relabeling of it have cut distance zero. -/
@[simp] theorem cutDist_relabel_self (W : Graphon) (e : GraphonRelabeling) :
    cutDist (W.relabel e) W = 0 := by
  apply le_antisymm
  · calc
      cutDist (W.relabel e) W ≤
          cutNorm (relabelKernel (W.relabel e).toL1 e.symm - W.toL1) :=
        cutDist_le_cost _ _ e.symm
      _ = 0 := by
        rw [Graphon.relabel_toL1, relabelKernel_relabelKernel_symm,
          sub_self, cutNorm_zero]
  · exact cutDist_nonneg _ _

@[simp] theorem cutDist_self_relabel (W : Graphon) (e : GraphonRelabeling) :
    cutDist W (W.relabel e) = 0 := by
  rw [cutDist_comm, cutDist_relabel_self]

theorem cutCostNN_relabel_left (U W : Graphon)
    (e f : GraphonRelabeling) :
    cutCostNN (U.relabel e) W f = cutCostNN U W (f.trans e) := by
  apply NNReal.eq
  change cutNorm (relabelKernel (U.relabel e).toL1 f - W.toL1) =
    cutNorm (relabelKernel U.toL1 (f.trans e) - W.toL1)
  rw [Graphon.relabel_toL1, relabelKernel_relabelKernel]

/-- Cut distance is invariant under relabeling its left endpoint. -/
theorem cutDist_relabel_left (U W : Graphon) (e : GraphonRelabeling) :
    cutDist (U.relabel e) W = cutDist U W := by
  have hNN : cutDistNN (U.relabel e) W = cutDistNN U W := by
    unfold cutDistNN
    apply le_antisymm
    · apply le_ciInf
      intro g
      calc
        (⨅ f : GraphonRelabeling, cutCostNN (U.relabel e) W f) ≤
            cutCostNN (U.relabel e) W (g.trans e.symm) :=
          ciInf_le (OrderBot.bddBelow _) _
        _ = cutCostNN U W g := by
          rw [cutCostNN_relabel_left, GraphonRelabeling.trans_symm_cancel_right]
    · apply le_ciInf
      intro f
      calc
        (⨅ g : GraphonRelabeling, cutCostNN U W g) ≤
            cutCostNN U W (f.trans e) :=
          ciInf_le (OrderBot.bddBelow _) _
        _ = cutCostNN (U.relabel e) W f :=
          (cutCostNN_relabel_left U W e f).symm
  exact congrArg (fun r : NNReal ↦ (r : ℝ)) hNN

/-- Cut distance is invariant under relabeling its right endpoint. -/
theorem cutDist_relabel_right (U W : Graphon) (e : GraphonRelabeling) :
    cutDist U (W.relabel e) = cutDist U W := by
  rw [cutDist_comm, cutDist_relabel_left, cutDist_comm]

/-- Simultaneous independent relabelings leave cut distance unchanged. -/
theorem cutDist_relabel (U W : Graphon) (e f : GraphonRelabeling) :
    cutDist (U.relabel e) (W.relabel f) = cutDist U W := by
  rw [cutDist_relabel_left, cutDist_relabel_right]


end InducedStars
