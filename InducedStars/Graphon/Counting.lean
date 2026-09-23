import InducedStars.FiniteModels.GraphonLimits
import InducedStars.Graphon.Star
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.HasLaw

/-!
# Counting estimates for graphons

This file contains the assumption-free analytic and finite counting bridges
used when passing from labeled finite induced-free graph families to their
cut-distance limits.
-/

noncomputable section

open Asymptotics Filter MeasureTheory Set Topology
open ProbabilityTheory
open scoped BigOperators ENNReal

namespace InducedStars

/-- Two distinct coordinate projections from any finite product of copies of
the unit interval have the unit-square product law. -/
theorem measurePreserving_pairProjection_fintype
    {ι : Type*} [Fintype ι] {i j : ι} (hij : i ≠ j) :
    MeasurePreserving (fun x : ι → UnitInterval ↦ (x i, x j))
      (volume : Measure (ι → UnitInterval)) unitSquareMeasure := by
  have hIndep : iIndepFun (fun k (x : ι → UnitInterval) ↦ x k)
      (volume : Measure (ι → UnitInterval)) :=
    iIndepFun_pi (X := fun _ : ι ↦ id) (fun _ ↦ aemeasurable_id)
  have hi : HasLaw (fun x : ι → UnitInterval ↦ x i)
      (volume : Measure UnitInterval) (volume : Measure (ι → UnitInterval)) :=
    (measurePreserving_eval (fun _ : ι ↦
      (volume : Measure UnitInterval)) i).hasLaw
  have hj : HasLaw (fun x : ι → UnitInterval ↦ x j)
      (volume : Measure UnitInterval) (volume : Measure (ι → UnitInterval)) :=
    (measurePreserving_eval (fun _ : ι ↦
      (volume : Measure UnitInterval)) j).hasLaw
  exact ((hIndep.indepFun hij).hasLaw_prod hi hj).measurePreserving (by fun_prop)

/-- The two selected coordinates of a finite cube. -/
private def pairCoordinatePredicate {ι : Type*} (i j : ι) (k : ι) : Prop :=
  k = i ∨ k = j

private def pairCoordinateLeft {ι : Type*} (i j : ι) :
    {k // pairCoordinatePredicate i j k} :=
  ⟨i, Or.inl rfl⟩

private def pairCoordinateRight {ι : Type*} (i j : ι) :
    {k // pairCoordinatePredicate i j k} :=
  ⟨j, Or.inr rfl⟩

/-- Restriction to two distinct coordinates, identified with an ordered
pair. -/
private def pairCoordinateEquiv {ι : Type*} [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) :
    ((k : {k // pairCoordinatePredicate i j k}) → UnitInterval) ≃ᵐ
      UnitSquare where
  toFun x :=
    (x (pairCoordinateLeft i j), x (pairCoordinateRight i j))
  invFun z k := if k.1 = i then z.1 else z.2
  left_inv x := by
    funext k
    rcases k.2 with hki | hkj
    · have hk : k = pairCoordinateLeft i j := Subtype.ext hki
      rw [hk]
      simp [pairCoordinateLeft]
    · have hk : k = pairCoordinateRight i j := Subtype.ext hkj
      rw [hk]
      simp [pairCoordinateRight, hij.symm]
  right_inv z := by
    ext <;> simp [pairCoordinateLeft, pairCoordinateRight, hij.symm]
  measurable_toFun :=
    (measurable_pi_apply (pairCoordinateLeft i j)).prodMk
      (measurable_pi_apply (pairCoordinateRight i j))
  measurable_invFun := by
    rw [measurable_pi_iff]
    intro k
    by_cases hki : k.1 = i
    · simpa [hki] using measurable_fst
    · simpa [hki] using measurable_snd

private theorem measurePreserving_pairCoordinateEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) [DecidablePred (pairCoordinatePredicate i j)]
    (hij : i ≠ j) :
    MeasurePreserving (pairCoordinateEquiv i j hij)
      (Measure.pi fun _ : {k // pairCoordinatePredicate i j k} ↦
        (volume : Measure UnitInterval))
      unitSquareMeasure := by
  have hsub :
      pairCoordinateLeft i j ≠ pairCoordinateRight i j := by
    intro h
    exact hij (congrArg Subtype.val h)
  let μ : {k // pairCoordinatePredicate i j k} → Measure UnitInterval :=
    fun _ ↦ volume
  have hIndep : iIndepFun
      (fun k (x : (k : {k // pairCoordinatePredicate i j k}) →
        UnitInterval) ↦ x k) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ : {k // pairCoordinatePredicate i j k} ↦ id)
      (fun _ ↦ aemeasurable_id)
  have hi : HasLaw
      (fun x : (k : {k // pairCoordinatePredicate i j k}) → UnitInterval ↦
        x (pairCoordinateLeft i j)) volume (Measure.pi μ) :=
    (measurePreserving_eval μ (pairCoordinateLeft i j)).hasLaw
  have hj : HasLaw
      (fun x : (k : {k // pairCoordinatePredicate i j k}) → UnitInterval ↦
        x (pairCoordinateRight i j)) volume (Measure.pi μ) :=
    (measurePreserving_eval μ (pairCoordinateRight i j)).hasLaw
  exact ((hIndep.indepFun hsub).hasLaw_prod hi hj).measurePreserving
    (pairCoordinateEquiv i j hij).measurable

/-- Split a finite cube into two selected coordinates and all remaining
coordinates. -/
private noncomputable def cubePairRestEquiv {f : ℕ}
    (i j : Fin f) (hij : i ≠ j) :
    (Fin f → UnitInterval) ≃ᵐ
      UnitSquare ×
        ((k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval) := by
  classical
  exact (MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin f ↦ UnitInterval) (pairCoordinatePredicate i j)).trans
      (MeasurableEquiv.prodCongr (pairCoordinateEquiv i j hij)
        (MeasurableEquiv.refl _))

private theorem measurePreserving_cubePairRestEquiv
    {f : ℕ} (i j : Fin f) (hij : i ≠ j)
    [DecidablePred (pairCoordinatePredicate i j)] :
    MeasurePreserving (cubePairRestEquiv i j hij)
      (Measure.pi fun _ : Fin f ↦ (volume : Measure UnitInterval))
      (unitSquareMeasure.prod
        (Measure.pi fun _ : {k // ¬pairCoordinatePredicate i j k} ↦
          (volume : Measure UnitInterval))) := by
  classical
  have hsplit := volume_preserving_piEquivPiSubtypeProd
    (fun _ : Fin f ↦ UnitInterval) (pairCoordinatePredicate i j)
  have hpair := measurePreserving_pairCoordinateEquiv i j hij
  have hprod := hpair.prod (MeasurePreserving.id
    (Measure.pi fun _ : {k // ¬pairCoordinatePredicate i j k} ↦
      (volume : Measure UnitInterval)))
  exact hsplit.trans hprod

@[simp] private theorem cubePairRestEquiv_symm_apply_i
    {f : ℕ} (i j : Fin f) (hij : i ≠ j)
    (z : UnitSquare)
    (y : (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval) :
    (cubePairRestEquiv i j hij).symm (z, y) i = z.1 := by
  have h := congrArg (fun q ↦ q.1.1)
    ((cubePairRestEquiv i j hij).apply_symm_apply (z, y))
  change (cubePairRestEquiv i j hij).symm (z, y) i = z.1 at h
  exact h

@[simp] private theorem cubePairRestEquiv_symm_apply_j
    {f : ℕ} (i j : Fin f) (hij : i ≠ j)
    (z : UnitSquare)
    (y : (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval) :
    (cubePairRestEquiv i j hij).symm (z, y) j = z.2 := by
  have h := congrArg (fun q ↦ q.1.2)
    ((cubePairRestEquiv i j hij).apply_symm_apply (z, y))
  change (cubePairRestEquiv i j hij).symm (z, y) j = z.2 at h
  exact h

@[simp] private theorem cubePairRestEquiv_symm_apply_rest
    {f : ℕ} (i j : Fin f) (hij : i ≠ j)
    (z : UnitSquare)
    (y : (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval)
    (k : Fin f) (hk : ¬pairCoordinatePredicate i j k) :
    (cubePairRestEquiv i j hij).symm (z, y) k = y ⟨k, hk⟩ := by
  have h := congrArg (fun q ↦ q.2 ⟨k, hk⟩)
    ((cubePairRestEquiv i j hij).apply_symm_apply (z, y))
  change (cubePairRestEquiv i j hij).symm (z, y) k = y ⟨k, hk⟩ at h
  exact h

private theorem graphonPairValue_cubePairRest_independent_snd_of_mem
    {f : ℕ} (i j : Fin f) (hij : i ≠ j) (W : Graphon)
    (e : Sym2 (Fin f)) (hi : i ∈ e) (hne : e ≠ s(i, j))
    (z : UnitSquare)
    (y : (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval) :
    graphonPairValue W ((cubePairRestEquiv i j hij).symm (z, y)) e =
      graphonPairValue W
        ((cubePairRestEquiv i j hij).symm ((z.1, 0), y)) e := by
  classical
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [← Sym2.mem_iff_mem, Sym2.mem_iff'] at hi
      rcases hi with hai | hbi
      · subst a
        have hbj : b ≠ j := by
          intro hbj
          subst b
          exact hne rfl
        by_cases hbi : b = i
        · subst b
          simp
        · have hbrest : ¬pairCoordinatePredicate i j b := by
            simp [pairCoordinatePredicate, hbi, hbj]
          simp [graphonPairValue_mk,
            cubePairRestEquiv_symm_apply_rest i j hij _ _ b hbrest]
      · subst b
        have haj : a ≠ j := by
          intro haj
          subst a
          exact hne Sym2.eq_swap
        by_cases hai : a = i
        · subst a
          simp
        · have harest : ¬pairCoordinatePredicate i j a := by
            simp [pairCoordinatePredicate, hai, haj]
          simp [graphonPairValue_mk,
            cubePairRestEquiv_symm_apply_rest i j hij _ _ a harest]

private theorem graphonPairValue_cubePairRest_independent_fst_of_not_mem
    {f : ℕ} (i j : Fin f) (hij : i ≠ j) (W : Graphon)
    (e : Sym2 (Fin f)) (hi : i ∉ e)
    (z : UnitSquare)
    (y : (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval) :
    graphonPairValue W ((cubePairRestEquiv i j hij).symm (z, y)) e =
      graphonPairValue W
        ((cubePairRestEquiv i j hij).symm ((0, z.2), y)) e := by
  classical
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [← Sym2.mem_iff_mem, Sym2.mem_iff'] at hi
      have hai : a ≠ i := fun h ↦ hi (Or.inl h.symm)
      have hbi : b ≠ i := fun h ↦ hi (Or.inr h.symm)
      by_cases haj : a = j
      · subst a
        by_cases hbj : b = j
        · subst b
          simp
        · have hbrest : ¬pairCoordinatePredicate i j b := by
            simp [pairCoordinatePredicate, hbi, hbj]
          simp [graphonPairValue_mk,
            cubePairRestEquiv_symm_apply_rest i j hij _ _ b hbrest]
      · have harest : ¬pairCoordinatePredicate i j a := by
          simp [pairCoordinatePredicate, hai, haj]
        by_cases hbj : b = j
        · subst b
          simp [graphonPairValue_mk,
            cubePairRestEquiv_symm_apply_rest i j hij _ _ a harest]
        · have hbrest : ¬pairCoordinatePredicate i j b := by
            simp [pairCoordinatePredicate, hbi, hbj]
          simp [graphonPairValue_mk,
            cubePairRestEquiv_symm_apply_rest i j hij _ _ a harest,
            cubePairRestEquiv_symm_apply_rest i j hij _ _ b hbrest]

/-- A product whose unordered pairs may use independently chosen graphons.
This is the telescoping summand left after one edge factor is removed. -/
private def mixedGraphonPairProduct {f : ℕ}
    (S : Finset (Sym2 (Fin f))) (A : Sym2 (Fin f) → Graphon)
    (x : Fin f → UnitInterval) : ℝ :=
  ∏ e ∈ S, graphonPairValue (A e) x e

private def mixedGraphonLeftWeight {f : ℕ}
    (i j : Fin f) (hij : i ≠ j)
    (S : Finset (Sym2 (Fin f))) (A : Sym2 (Fin f) → Graphon)
    (y : (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval)
    (u : UnitInterval) : ℝ :=
  ∏ e ∈ S with i ∈ e,
    graphonPairValue (A e)
      ((cubePairRestEquiv i j hij).symm ((u, 0), y)) e

private def mixedGraphonRightWeight {f : ℕ}
    (i j : Fin f) (hij : i ≠ j)
    (S : Finset (Sym2 (Fin f))) (A : Sym2 (Fin f) → Graphon)
    (y : (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval)
    (v : UnitInterval) : ℝ :=
  ∏ e ∈ S with i ∉ e,
    graphonPairValue (A e)
      ((cubePairRestEquiv i j hij).symm ((0, v), y)) e

private theorem mixedGraphonPairProduct_cubePairRest_factor
    {f : ℕ} (i j : Fin f) (hij : i ≠ j)
    (S : Finset (Sym2 (Fin f))) (A : Sym2 (Fin f) → Graphon)
    (hijS : s(i, j) ∉ S) (z : UnitSquare)
    (y : (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval) :
    mixedGraphonPairProduct S A
        ((cubePairRestEquiv i j hij).symm (z, y)) =
      mixedGraphonLeftWeight i j hij S A y z.1 *
        mixedGraphonRightWeight i j hij S A y z.2 := by
  classical
  rw [mixedGraphonPairProduct, mixedGraphonLeftWeight,
    mixedGraphonRightWeight]
  calc
    (∏ e ∈ S,
        graphonPairValue (A e)
          ((cubePairRestEquiv i j hij).symm (z, y)) e) =
        (∏ e ∈ S with i ∈ e,
          graphonPairValue (A e)
            ((cubePairRestEquiv i j hij).symm (z, y)) e) *
        ∏ e ∈ S with i ∉ e,
          graphonPairValue (A e)
            ((cubePairRestEquiv i j hij).symm (z, y)) e :=
      (Finset.prod_filter_mul_prod_filter_not S (fun e ↦ i ∈ e)
        (fun e ↦ graphonPairValue (A e)
          ((cubePairRestEquiv i j hij).symm (z, y)) e)).symm
    _ = _ := by
      congr 1
      · apply Finset.prod_congr rfl
        intro e he
        have heS : e ∈ S := (Finset.mem_filter.mp he).1
        have hi : i ∈ e := (Finset.mem_filter.mp he).2
        exact graphonPairValue_cubePairRest_independent_snd_of_mem
          i j hij (A e) e hi (fun heq ↦ hijS (heq ▸ heS)) z y
      · apply Finset.prod_congr rfl
        intro e he
        have hi : i ∉ e := (Finset.mem_filter.mp he).2
        exact graphonPairValue_cubePairRest_independent_fst_of_not_mem
          i j hij (A e) e hi z y

private theorem measurable_mixedGraphonLeftWeight
    {f : ℕ} (i j : Fin f) (hij : i ≠ j)
    (S : Finset (Sym2 (Fin f))) (A : Sym2 (Fin f) → Graphon)
    (y : (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval) :
    Measurable (mixedGraphonLeftWeight i j hij S A y) := by
  classical
  have hmerge : Measurable (fun u : UnitInterval ↦
      (cubePairRestEquiv i j hij).symm ((u, 0), y)) :=
    (cubePairRestEquiv i j hij).symm.measurable.comp
      ((measurable_id.prodMk measurable_const).prodMk measurable_const)
  apply Finset.measurable_prod
  intro e _he
  exact (measurable_graphonPairValue (A e) e).comp hmerge

private theorem measurable_mixedGraphonRightWeight
    {f : ℕ} (i j : Fin f) (hij : i ≠ j)
    (S : Finset (Sym2 (Fin f))) (A : Sym2 (Fin f) → Graphon)
    (y : (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval) :
    Measurable (mixedGraphonRightWeight i j hij S A y) := by
  classical
  have hmerge : Measurable (fun v : UnitInterval ↦
      (cubePairRestEquiv i j hij).symm ((0, v), y)) :=
    (cubePairRestEquiv i j hij).symm.measurable.comp
      ((measurable_const.prodMk measurable_id).prodMk measurable_const)
  apply Finset.measurable_prod
  intro e _he
  exact (measurable_graphonPairValue (A e) e).comp hmerge

private theorem mixedGraphonLeftWeight_nonneg
    {f : ℕ} (i j : Fin f) (hij : i ≠ j)
    (S : Finset (Sym2 (Fin f))) (A : Sym2 (Fin f) → Graphon)
    (y : (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval)
    (u : UnitInterval) :
    0 ≤ mixedGraphonLeftWeight i j hij S A y u := by
  exact Finset.prod_nonneg fun e _ ↦ graphonPairValue_nonneg (A e) _ e

private theorem mixedGraphonLeftWeight_le_one
    {f : ℕ} (i j : Fin f) (hij : i ≠ j)
    (S : Finset (Sym2 (Fin f))) (A : Sym2 (Fin f) → Graphon)
    (y : (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval)
    (u : UnitInterval) :
    mixedGraphonLeftWeight i j hij S A y u ≤ 1 := by
  apply Finset.prod_le_one
  · exact fun e _ ↦ graphonPairValue_nonneg (A e) _ e
  · exact fun e _ ↦ graphonPairValue_le_one (A e) _ e

private theorem mixedGraphonRightWeight_nonneg
    {f : ℕ} (i j : Fin f) (hij : i ≠ j)
    (S : Finset (Sym2 (Fin f))) (A : Sym2 (Fin f) → Graphon)
    (y : (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval)
    (v : UnitInterval) :
    0 ≤ mixedGraphonRightWeight i j hij S A y v := by
  exact Finset.prod_nonneg fun e _ ↦ graphonPairValue_nonneg (A e) _ e

private theorem mixedGraphonRightWeight_le_one
    {f : ℕ} (i j : Fin f) (hij : i ≠ j)
    (S : Finset (Sym2 (Fin f))) (A : Sym2 (Fin f) → Graphon)
    (y : (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval)
    (v : UnitInterval) :
    mixedGraphonRightWeight i j hij S A y v ≤ 1 := by
  apply Finset.prod_le_one
  · exact fun e _ ↦ graphonPairValue_nonneg (A e) _ e
  · exact fun e _ ↦ graphonPairValue_le_one (A e) _ e

private theorem measurable_mixedGraphonPairProduct
    {f : ℕ} (S : Finset (Sym2 (Fin f)))
    (A : Sym2 (Fin f) → Graphon) :
    Measurable (mixedGraphonPairProduct S A) := by
  classical
  exact S.measurable_prod fun e _ ↦ measurable_graphonPairValue (A e) e

private theorem mixedGraphonPairProduct_nonneg
    {f : ℕ} (S : Finset (Sym2 (Fin f)))
    (A : Sym2 (Fin f) → Graphon) (x : Fin f → UnitInterval) :
    0 ≤ mixedGraphonPairProduct S A x := by
  exact Finset.prod_nonneg fun e _ ↦ graphonPairValue_nonneg (A e) x e

private theorem mixedGraphonPairProduct_le_one
    {f : ℕ} (S : Finset (Sym2 (Fin f)))
    (A : Sym2 (Fin f) → Graphon) (x : Fin f → UnitInterval) :
    mixedGraphonPairProduct S A x ≤ 1 := by
  apply Finset.prod_le_one
  · exact fun e _ ↦ graphonPairValue_nonneg (A e) x e
  · exact fun e _ ↦ graphonPairValue_le_one (A e) x e

private theorem integrable_mixedGraphonPairProduct
    {f : ℕ} (S : Finset (Sym2 (Fin f)))
    (A : Sym2 (Fin f) → Graphon) :
    Integrable (mixedGraphonPairProduct S A) := by
  refine (integrable_const (1 : ℝ)).mono
    (measurable_mixedGraphonPairProduct S A).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mixedGraphonPairProduct_nonneg S A x)]
  simpa using mixedGraphonPairProduct_le_one S A x

private theorem integrable_mixedGraphonPairProduct_mul_pairValue_sub
    {f : ℕ} (S : Finset (Sym2 (Fin f)))
    (A : Sym2 (Fin f) → Graphon) (U W : Graphon)
    (e : Sym2 (Fin f)) :
    Integrable (fun x : Fin f → UnitInterval ↦
      mixedGraphonPairProduct S A x *
        (graphonPairValue U x e - graphonPairValue W x e)) := by
  have hmeas : Measurable (fun x : Fin f → UnitInterval ↦
      mixedGraphonPairProduct S A x *
        (graphonPairValue U x e - graphonPairValue W x e)) :=
    (measurable_mixedGraphonPairProduct S A).mul
      ((measurable_graphonPairValue U e).sub
        (measurable_graphonPairValue W e))
  refine (integrable_const (1 : ℝ)).mono hmeas.aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  have hprodabs : |mixedGraphonPairProduct S A x| ≤ 1 := by
    rw [abs_of_nonneg (mixedGraphonPairProduct_nonneg S A x)]
    exact mixedGraphonPairProduct_le_one S A x
  have hdiffabs :
      |graphonPairValue U x e - graphonPairValue W x e| ≤ 1 := by
    have hU0 := graphonPairValue_nonneg U x e
    have hU1 := graphonPairValue_le_one U x e
    have hW0 := graphonPairValue_nonneg W x e
    have hW1 := graphonPairValue_le_one W x e
    rw [abs_le]
    constructor <;> linarith
  simpa using mul_le_one₀ hprodabs
    (abs_nonneg (graphonPairValue U x e - graphonPairValue W x e)) hdiffabs

/-! ## Bounded weights and the rectangle cut norm -/

/-- If every measurable-set integral of an integrable real function is
bounded by `B`, then multiplying by a measurable `[0,1]`-valued weight does
not increase that bound.  The proof chooses the positive and negative sets
of the integrand; this is the measure-theoretic convexity step behind the
weighted cut-norm estimate. -/
theorem abs_integral_mul_le_of_abs_setIntegral_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {h w : X → ℝ} (hh : Integrable h μ) (hh_meas : Measurable h)
    (hw : Measurable w)
    (hw_nonneg : ∀ x, 0 ≤ w x) (hw_le_one : ∀ x, w x ≤ 1)
    {B : ℝ}
    (hB : ∀ s : Set X, MeasurableSet s → |∫ x in s, h x ∂μ| ≤ B) :
    |∫ x, w x * h x ∂μ| ≤ B := by
  let p : Set X := {x | 0 ≤ h x}
  let n : Set X := {x | h x < 0}
  have hp : MeasurableSet p := measurableSet_le measurable_const hh_meas
  have hn : MeasurableSet n := measurableSet_lt hh_meas measurable_const
  have hwh : Integrable (fun x ↦ w x * h x) μ := by
    refine hh.mono (hw.mul hh_meas).aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    have hwabs : |w x| ≤ 1 := by
      rw [abs_of_nonneg (hw_nonneg x)]
      exact hw_le_one x
    nlinarith [abs_nonneg (h x)]
  have hupper_point : ∀ x, w x * h x ≤ p.indicator h x := by
    intro x
    by_cases hx : 0 ≤ h x
    · rw [indicator_of_mem (show x ∈ p from hx)]
      nlinarith [hw_le_one x]
    · rw [indicator_of_notMem (show x ∉ p from hx)]
      exact mul_nonpos_of_nonneg_of_nonpos (hw_nonneg x) (le_of_not_ge hx)
  have hlower_point : ∀ x, n.indicator h x ≤ w x * h x := by
    intro x
    by_cases hx : h x < 0
    · rw [indicator_of_mem (show x ∈ n from hx)]
      nlinarith [hw_le_one x]
    · rw [indicator_of_notMem (show x ∉ n from hx)]
      exact mul_nonneg (hw_nonneg x) (le_of_not_gt hx)
  have hupper : (∫ x, w x * h x ∂μ) ≤ ∫ x in p, h x ∂μ := by
    rw [← integral_indicator hp]
    exact integral_mono hwh (hh.indicator hp) hupper_point
  have hlower : (∫ x in n, h x ∂μ) ≤ ∫ x, w x * h x ∂μ := by
    rw [← integral_indicator hn]
    exact integral_mono (hh.indicator hn) hwh hlower_point
  have hpB := hB p hp
  have hnB := hB n hn
  rw [abs_le]
  constructor <;> linarith [le_abs_self (∫ x in p, h x ∂μ),
    neg_abs_le (∫ x in n, h x ∂μ)]

/-- Multiplying an integrable real function by a measurable `[0,1]`-valued
weight preserves integrability. -/
private theorem integrable_mul_of_integrable_of_unitInterval
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {h w : X → ℝ} (hh : Integrable h μ) (hh_meas : Measurable h)
    (hw : Measurable w) (hw_nonneg : ∀ x, 0 ≤ w x)
    (hw_le_one : ∀ x, w x ≤ 1) :
    Integrable (fun x ↦ w x * h x) μ := by
  refine hh.mono (hw.mul hh_meas).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  have hwabs : |w x| ≤ 1 := by
    rw [abs_of_nonneg (hw_nonneg x)]
    exact hw_le_one x
  nlinarith [abs_nonneg (h x)]

/-- Rectangle cut norm controls a kernel tested against a product of two
measurable `[0,1]`-valued weights.  Unlike the more common signed
`[-1,1]` formulation, no factor four is needed because both weights are
nonnegative. -/
theorem abs_integral_mul_fst_mul_snd_le_cutNorm
    (K : IntegrableKernel) {k : UnitSquare → ℝ}
    (hk : Integrable k unitSquareMeasure) (hk_meas : Measurable k)
    (hK : (fun z ↦ K z) =ᵐ[unitSquareMeasure] k)
    {f g : UnitInterval → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_le_one : ∀ x, f x ≤ 1)
    (hg_nonneg : ∀ x, 0 ≤ g x) (hg_le_one : ∀ x, g x ≤ 1) :
    |∫ z : UnitSquare, f z.1 * k z * g z.2 ∂unitSquareMeasure| ≤ cutNorm K := by
  let kg : UnitSquare → ℝ := fun z ↦ g z.2 * k z
  have hkg_meas : Measurable kg :=
    (hg.comp measurable_snd).mul hk_meas
  have hkg : Integrable kg unitSquareMeasure :=
    integrable_mul_of_integrable_of_unitInterval hk hk_meas
      (hg.comp measurable_snd) (fun z ↦ hg_nonneg z.2) (fun z ↦ hg_le_one z.2)
  let q : UnitInterval → ℝ := fun x ↦ ∫ y, kg (x, y) ∂volume
  have hq_meas : Measurable q :=
    hkg_meas.stronglyMeasurable.integral_prod_right'.measurable
  have hq : Integrable q volume := hkg.integral_prod_left
  have hq_set (A : Set UnitInterval) (hA : MeasurableSet A) :
      |∫ x in A, q x ∂volume| ≤ cutNorm K := by
    let hAfun : UnitInterval → ℝ := fun y ↦ ∫ x in A, k (x, y) ∂volume
    let kA : UnitSquare → ℝ := (A ×ˢ (Set.univ : Set UnitInterval)).indicator k
    have hkA_meas : Measurable kA :=
      hk_meas.indicator (hA.prod MeasurableSet.univ)
    have hkA : Integrable kA unitSquareMeasure :=
      hk.indicator (hA.prod MeasurableSet.univ)
    have hAfun_eq : hAfun = fun y ↦ ∫ x, kA (x, y) ∂volume := by
      funext y
      simp only [hAfun, kA, Set.mem_prod, Set.mem_univ, and_true]
      rw [← integral_indicator hA]
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ A <;> simp [Set.indicator, hx]
    have hAfun_meas : Measurable hAfun := by
      rw [hAfun_eq]
      exact hkA_meas.stronglyMeasurable.integral_prod_left'.measurable
    have hAfun_int : Integrable hAfun volume := by
      rw [hAfun_eq]
      exact hkA.integral_prod_right
    have hAfun_set (B : Set UnitInterval) (hB : MeasurableSet B) :
        |∫ y in B, hAfun y ∂volume| ≤ cutNorm K := by
      let C : MeasurableCut :=
        { left := A
          right := B
          measurable_left := hA
          measurable_right := hB }
      have hrect :
          (∫ y in B, hAfun y ∂volume) =
            ∫ z in A ×ˢ B, k z ∂unitSquareMeasure := by
        simp only [hAfun]
        calc
          (∫ y in B, ∫ x in A, k (x, y) ∂volume ∂volume) =
              ∫ z : UnitInterval × UnitInterval in B ×ˢ A,
                k z.swap ∂unitSquareMeasure := by
                symm
                apply setIntegral_prod
                exact hk.swap.integrableOn
          _ = ∫ z in A ×ˢ B, k z ∂unitSquareMeasure :=
            setIntegral_prod_swap A B k
      rw [hrect]
      calc
        |∫ z in A ×ˢ B, k z ∂unitSquareMeasure| = |cutIntegral K C| := by
          congr 1
          rw [cutIntegral]
          exact (integral_congr_ae (ae_restrict_of_ae hK)).symm
        _ ≤ cutNorm K := abs_cutIntegral_le_cutNorm K C
    have hweighted :
        |∫ y, g y * hAfun y ∂volume| ≤ cutNorm K :=
      abs_integral_mul_le_of_abs_setIntegral_le hAfun_int hAfun_meas hg
        hg_nonneg hg_le_one hAfun_set
    calc
      |∫ x in A, q x ∂volume| = |∫ y, g y * hAfun y ∂volume| := by
        congr 1
        simp only [q, hAfun]
        calc
          (∫ x in A, ∫ y, kg (x, y) ∂volume ∂volume) =
              ∫ z in A ×ˢ (Set.univ : Set UnitInterval), kg z
                ∂unitSquareMeasure := by
                  simpa only [setIntegral_univ] using
                    (setIntegral_prod kg (s := A)
                      (t := (Set.univ : Set UnitInterval)) hkg.integrableOn).symm
          _ = ∫ z : UnitInterval × UnitInterval in
                (Set.univ : Set UnitInterval) ×ˢ A, kg z.swap
                ∂unitSquareMeasure :=
              (setIntegral_prod_swap A Set.univ kg).symm
          _ = ∫ y, ∫ x in A, kg (x, y) ∂volume ∂volume := by
              rw [setIntegral_prod]
              · simp only [setIntegral_univ, Prod.swap_prod_mk]
              · exact hkg.swap.integrableOn
          _ = ∫ y, g y * (∫ x in A, k (x, y) ∂volume) ∂volume := by
              apply integral_congr_ae
              filter_upwards [] with y
              simp only [kg]
              rw [← integral_const_mul]
      _ ≤ cutNorm K := hweighted
  have hweighted_q :
      |∫ x, f x * q x ∂volume| ≤ cutNorm K :=
    abs_integral_mul_le_of_abs_setIntegral_le hq hq_meas hf
      hf_nonneg hf_le_one hq_set
  calc
    |∫ z : UnitSquare, f z.1 * k z * g z.2 ∂unitSquareMeasure| =
        |∫ x, f x * q x ∂volume| := by
      congr 1
      simp only [q]
      let fkg : UnitSquare → ℝ := fun z ↦ f z.1 * kg z
      have hfkg : Integrable fkg unitSquareMeasure :=
        integrable_mul_of_integrable_of_unitInterval hkg hkg_meas
          (hf.comp measurable_fst) (fun z ↦ hf_nonneg z.1)
          (fun z ↦ hf_le_one z.1)
      calc
        (∫ z : UnitSquare, f z.1 * k z * g z.2 ∂unitSquareMeasure) =
            ∫ z, fkg z ∂unitSquareMeasure := by
              apply integral_congr_ae
              filter_upwards [] with z
              simp only [fkg, kg]
              ring
        _ = ∫ x, ∫ y, fkg (x, y) ∂volume ∂volume := integral_prod fkg hfkg
        _ = ∫ x, f x * (∫ y, kg (x, y) ∂volume) ∂volume := by
              apply integral_congr_ae
              filter_upwards [] with x
              simp only [fkg]
              rw [integral_const_mul]
    _ ≤ cutNorm K := hweighted_q

/-! ## Edge density is Lipschitz in cut distance -/

private theorem integrable_graphonValue (W : Graphon) :
    Integrable W.value unitSquareMeasure :=
  W.integrable.congr (Filter.EventuallyEq.symm W.value_ae_eq)

private theorem abs_integral_mixedGraphonPairProduct_cubePairRest_le_cutNorm
    {f : ℕ} (i j : Fin f) (hij : i ≠ j)
    (S : Finset (Sym2 (Fin f))) (A : Sym2 (Fin f) → Graphon)
    (hijS : s(i, j) ∉ S) (U W : Graphon)
    (y : (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval) :
    |∫ z : UnitSquare,
        mixedGraphonPairProduct S A
            ((cubePairRestEquiv i j hij).symm (z, y)) *
          (U.value z - W.value z) ∂unitSquareMeasure| ≤
      cutNorm (U.toL1 - W.toL1) := by
  let K : IntegrableKernel := U.toL1 - W.toL1
  let k : UnitSquare → ℝ := fun z ↦ U.value z - W.value z
  have hk_meas : Measurable k := U.measurable_value.sub W.measurable_value
  have hk : Integrable k unitSquareMeasure :=
    (integrable_graphonValue U).sub (integrable_graphonValue W)
  have hK : (fun z ↦ K z) =ᵐ[unitSquareMeasure] k := by
    filter_upwards [Lp.coeFn_sub U.toL1 W.toL1,
      U.value_ae_eq, W.value_ae_eq] with z hzsub hzU hzW
    simp only [K, k]
    rw [hzsub]
    change U.toL1 z - W.toL1 z = U.value z - W.value z
    rw [← hzU, ← hzW]
  have htest := abs_integral_mul_fst_mul_snd_le_cutNorm K hk hk_meas hK
    (measurable_mixedGraphonLeftWeight i j hij S A y)
    (measurable_mixedGraphonRightWeight i j hij S A y)
    (mixedGraphonLeftWeight_nonneg i j hij S A y)
    (mixedGraphonLeftWeight_le_one i j hij S A y)
    (mixedGraphonRightWeight_nonneg i j hij S A y)
    (mixedGraphonRightWeight_le_one i j hij S A y)
  calc
    |∫ z : UnitSquare,
        mixedGraphonPairProduct S A
            ((cubePairRestEquiv i j hij).symm (z, y)) *
          (U.value z - W.value z) ∂unitSquareMeasure| =
        |∫ z : UnitSquare,
          mixedGraphonLeftWeight i j hij S A y z.1 * k z *
            mixedGraphonRightWeight i j hij S A y z.2
          ∂unitSquareMeasure| := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      rw [mixedGraphonPairProduct_cubePairRest_factor
        i j hij S A hijS z y]
      simp only [k]
      ring
    _ ≤ cutNorm K := htest
    _ = cutNorm (U.toL1 - W.toL1) := rfl

/-- One telescoping edge replacement changes a mixed homomorphism integral
by at most the cut norm of the two graphons being exchanged. -/
private theorem abs_integral_mixedGraphonPairProduct_mul_pairValue_sub_le_cutNorm
    {f : ℕ} (i j : Fin f) (hij : i ≠ j)
    (S : Finset (Sym2 (Fin f))) (A : Sym2 (Fin f) → Graphon)
    (hijS : s(i, j) ∉ S) (U W : Graphon) :
    |∫ x : Fin f → UnitInterval,
        mixedGraphonPairProduct S A x *
          (graphonPairValue U x s(i, j) -
            graphonPairValue W x s(i, j))| ≤
      cutNorm (U.toL1 - W.toL1) := by
  classical
  let μrest : Measure
      ((k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval) :=
    Measure.pi fun _ ↦ volume
  let T : (Fin f → UnitInterval) → ℝ := fun x ↦
    mixedGraphonPairProduct S A x *
      (graphonPairValue U x s(i, j) - graphonPairValue W x s(i, j))
  let q : UnitSquare ×
      ((k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval) → ℝ :=
    fun p ↦ T ((cubePairRestEquiv i j hij).symm p)
  have hT : Integrable T :=
    integrable_mixedGraphonPairProduct_mul_pairValue_sub S A U W s(i, j)
  have hmp := measurePreserving_cubePairRestEquiv i j hij
  have hvol : (volume : Measure (Fin f → UnitInterval)) =
      Measure.pi (fun _ : Fin f ↦ (volume : Measure UnitInterval)) :=
    volume_pi
  have hcomp : q ∘ (cubePairRestEquiv i j hij) = T := by
    funext x
    simp only [q, T, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  have hq : Integrable q (unitSquareMeasure.prod μrest) := by
    apply (hmp.integrable_comp_emb
      (cubePairRestEquiv i j hij).measurableEmbedding).mp
    rw [hcomp, ← hvol]
    exact hT
  have hintegral : (∫ x : Fin f → UnitInterval, T x) =
      ∫ p, q p ∂(unitSquareMeasure.prod μrest) := by
    have hraw := hmp.integral_comp' q
    change (∫ x, (q ∘ (cubePairRestEquiv i j hij)) x
      ∂(Measure.pi fun _ : Fin f ↦ (volume : Measure UnitInterval))) = _ at hraw
    rw [hcomp, ← hvol] at hraw
    simpa only [μrest] using hraw
  have hinner (y :
      (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval) :
      (∫ z : UnitSquare, q (z, y) ∂unitSquareMeasure) =
        ∫ z : UnitSquare,
          mixedGraphonPairProduct S A
              ((cubePairRestEquiv i j hij).symm (z, y)) *
            (U.value z - W.value z) ∂unitSquareMeasure := by
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [q, T, graphonPairValue_mk]
    rw [cubePairRestEquiv_symm_apply_i i j hij z y,
      cubePairRestEquiv_symm_apply_j i j hij z y]
  have hinner_bound (y :
      (k : {k // ¬pairCoordinatePredicate i j k}) → UnitInterval) :
      |∫ z : UnitSquare, q (z, y) ∂unitSquareMeasure| ≤
        cutNorm (U.toL1 - W.toL1) := by
    rw [hinner y]
    exact abs_integral_mixedGraphonPairProduct_cubePairRest_le_cutNorm
      i j hij S A hijS U W y
  have houter : Integrable
      (fun y ↦ ∫ z : UnitSquare, q (z, y) ∂unitSquareMeasure) μrest :=
    hq.integral_prod_right
  calc
    |∫ x : Fin f → UnitInterval,
        mixedGraphonPairProduct S A x *
          (graphonPairValue U x s(i, j) -
            graphonPairValue W x s(i, j))| =
        |∫ y, ∫ z : UnitSquare, q (z, y) ∂unitSquareMeasure ∂μrest| := by
      change |∫ x : Fin f → UnitInterval, T x| = _
      rw [hintegral, integral_prod_symm q hq]
    _ ≤ ∫ y, |∫ z : UnitSquare, q (z, y) ∂unitSquareMeasure| ∂μrest :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _y, cutNorm (U.toL1 - W.toL1) ∂μrest := by
      exact integral_mono houter.abs (integrable_const _) hinner_bound
    _ = cutNorm (U.toL1 - W.toL1) := by simp [μrest]

private theorem abs_integral_common_mixedGraphonPairProduct_mul_sub_le
    {f : ℕ} (C S : Finset (Sym2 (Fin f)))
    (hCS : Disjoint C S)
    (hSdiag : ∀ e ∈ S, ¬e.IsDiag)
    (A : Sym2 (Fin f) → Graphon) (U W : Graphon) :
    |∫ x : Fin f → UnitInterval,
        mixedGraphonPairProduct C A x *
          (mixedGraphonPairProduct S (fun _ ↦ U) x -
            mixedGraphonPairProduct S (fun _ ↦ W) x)| ≤
      (S.card : ℝ) * cutNorm (U.toL1 - W.toL1) := by
  classical
  induction S using Finset.induction_on generalizing C A with
  | empty => simp [mixedGraphonPairProduct]
  | @insert e S he ih =>
      induction e using Sym2.inductionOn with
      | _ i j =>
          have hij : i ≠ j := by
            simpa only [Sym2.mk_isDiag_iff] using hSdiag s(i, j) (by simp)
          have heC : s(i, j) ∉ C := by
            intro heC
            exact (Finset.disjoint_left.mp hCS heC (by simp))
          have hCSrest : Disjoint C S :=
            hCS.mono_right (Finset.subset_insert _ _)
          let D : Finset (Sym2 (Fin f)) := C ∪ S
          let B : Sym2 (Fin f) → Graphon :=
            fun q ↦ if q ∈ C then A q else U
          have hijD : s(i, j) ∉ D := by
            simp [D, heC, he]
          have hDfactor (x : Fin f → UnitInterval) :
              mixedGraphonPairProduct D B x =
                mixedGraphonPairProduct C A x *
                  mixedGraphonPairProduct S (fun _ ↦ U) x := by
            simp only [mixedGraphonPairProduct, D]
            rw [Finset.prod_union hCSrest]
            congr 1
            · apply Finset.prod_congr rfl
              intro q hq
              simp [B, hq]
            · apply Finset.prod_congr rfl
              intro q hq
              have hqC : q ∉ C := fun hqC ↦
                Finset.disjoint_left.mp hCSrest hqC hq
              simp [B, hqC]
          let C' : Finset (Sym2 (Fin f)) := insert s(i, j) C
          let A' : Sym2 (Fin f) → Graphon :=
            fun q ↦ if q = s(i, j) then W else A q
          have hC'S : Disjoint C' S := by
            simp only [C', Finset.disjoint_insert_left]
            exact ⟨he, hCSrest⟩
          have hC'factor (x : Fin f → UnitInterval) :
              mixedGraphonPairProduct C' A' x =
                graphonPairValue W x s(i, j) *
                  mixedGraphonPairProduct C A x := by
            simp only [mixedGraphonPairProduct, C']
            rw [Finset.prod_insert heC]
            congr 1
            · simp [A']
            · apply Finset.prod_congr rfl
              intro q hq
              have hqne : q ≠ s(i, j) := fun hqeq ↦ heC (hqeq ▸ hq)
              simp [A', hqne]
          have hUinsert (x : Fin f → UnitInterval) :
              mixedGraphonPairProduct (insert s(i, j) S) (fun _ ↦ U) x =
                graphonPairValue U x s(i, j) *
                  mixedGraphonPairProduct S (fun _ ↦ U) x := by
            simp [mixedGraphonPairProduct, he]
          have hWinsert (x : Fin f → UnitInterval) :
              mixedGraphonPairProduct (insert s(i, j) S) (fun _ ↦ W) x =
                graphonPairValue W x s(i, j) *
                  mixedGraphonPairProduct S (fun _ ↦ W) x := by
            simp [mixedGraphonPairProduct, he]
          let first : (Fin f → UnitInterval) → ℝ := fun x ↦
            mixedGraphonPairProduct D B x *
              (graphonPairValue U x s(i, j) -
                graphonPairValue W x s(i, j))
          let second : (Fin f → UnitInterval) → ℝ := fun x ↦
            mixedGraphonPairProduct C' A' x *
              (mixedGraphonPairProduct S (fun _ ↦ U) x -
                mixedGraphonPairProduct S (fun _ ↦ W) x)
          have hpoint (x : Fin f → UnitInterval) :
              mixedGraphonPairProduct C A x *
                  (mixedGraphonPairProduct (insert s(i, j) S) (fun _ ↦ U) x -
                    mixedGraphonPairProduct (insert s(i, j) S) (fun _ ↦ W) x) =
                first x + second x := by
            rw [hUinsert x, hWinsert x]
            simp only [first, second, hDfactor x, hC'factor x]
            ring
          have hfirstInt : Integrable first :=
            integrable_mixedGraphonPairProduct_mul_pairValue_sub
              D B U W s(i, j)
          have hsecondInt : Integrable second := by
            have hmeas : Measurable second :=
              (measurable_mixedGraphonPairProduct C' A').mul
                ((measurable_mixedGraphonPairProduct S (fun _ ↦ U)).sub
                  (measurable_mixedGraphonPairProduct S (fun _ ↦ W)))
            refine (integrable_const (1 : ℝ)).mono hmeas.aestronglyMeasurable ?_
            filter_upwards [] with x
            rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
            have hleft : |mixedGraphonPairProduct C' A' x| ≤ 1 := by
              rw [abs_of_nonneg (mixedGraphonPairProduct_nonneg C' A' x)]
              exact mixedGraphonPairProduct_le_one C' A' x
            have hright :
                |mixedGraphonPairProduct S (fun _ ↦ U) x -
                    mixedGraphonPairProduct S (fun _ ↦ W) x| ≤ 1 := by
              rw [abs_le]
              constructor
              · have hU0 := mixedGraphonPairProduct_nonneg S (fun _ ↦ U) x
                have hW1 := mixedGraphonPairProduct_le_one S (fun _ ↦ W) x
                linarith
              · have hW0 := mixedGraphonPairProduct_nonneg S (fun _ ↦ W) x
                have hU1 := mixedGraphonPairProduct_le_one S (fun _ ↦ U) x
                linarith
            simpa only [second, abs_one] using
              mul_le_one₀ hleft
                (abs_nonneg (mixedGraphonPairProduct S (fun _ ↦ U) x -
                  mixedGraphonPairProduct S (fun _ ↦ W) x)) hright
          have hfirst : |∫ x, first x| ≤ cutNorm (U.toL1 - W.toL1) :=
            abs_integral_mixedGraphonPairProduct_mul_pairValue_sub_le_cutNorm
              i j hij D B hijD U W
          have hsecond : |∫ x, second x| ≤
              (S.card : ℝ) * cutNorm (U.toL1 - W.toL1) := by
            exact ih C' hC'S
              (fun q hq ↦ hSdiag q (Finset.mem_insert_of_mem hq)) A'
          calc
            |∫ x : Fin f → UnitInterval,
                mixedGraphonPairProduct C A x *
                  (mixedGraphonPairProduct (insert s(i, j) S) (fun _ ↦ U) x -
                    mixedGraphonPairProduct (insert s(i, j) S) (fun _ ↦ W) x)| =
                |∫ x, first x + second x| := by
              congr 1
              apply integral_congr_ae
              exact Eventually.of_forall hpoint
            _ = |(∫ x, first x) + ∫ x, second x| := by
              rw [integral_add hfirstInt hsecondInt]
            _ ≤ |∫ x, first x| + |∫ x, second x| := abs_add_le _ _
            _ ≤ cutNorm (U.toL1 - W.toL1) +
                (S.card : ℝ) * cutNorm (U.toL1 - W.toL1) :=
              add_le_add hfirst hsecond
            _ = ((insert s(i, j) S).card : ℝ) *
                cutNorm (U.toL1 - W.toL1) := by
              rw [Finset.card_insert_of_notMem he]
              push_cast
              ring

/-- The ordinary homomorphism density of a fixed finite graph is Lipschitz in
the cut norm when the two graphons are represented on the same probability
space.  The (deliberately simple) Lipschitz constant is the number of edges of
the finite graph. -/
theorem abs_graphonHomDensity_sub_le_card_mul_cutNorm
    {f : ℕ} (F : SimpleGraph (Fin f)) (U W : Graphon) :
    |graphonHomDensity F U - graphonHomDensity F W| ≤
      ((finiteGraphEdges F).card : ℝ) * cutNorm (U.toL1 - W.toL1) := by
  classical
  rw [graphonHomDensity, graphonHomDensity,
    ← integral_sub (integrable_graphonHomIntegrand F U)
      (integrable_graphonHomIntegrand F W)]
  simpa [graphonHomIntegrand, mixedGraphonPairProduct] using
    abs_integral_common_mixedGraphonPairProduct_mul_sub_le
      (∅ : Finset (Sym2 (Fin f))) (finiteGraphEdges F)
      (Finset.disjoint_empty_left (finiteGraphEdges F))
      (fun e he ↦ F.not_isDiag_of_mem_edgeSet
        ((mem_finiteGraphEdges F e).mp he))
      (fun _ ↦ U) U W

/-- Ordinary homomorphism densities are invariant under a common
measure-preserving relabeling of the graphon coordinates. -/
theorem graphonHomDensity_relabel
    {f : ℕ} (F : SimpleGraph (Fin f)) (U : Graphon)
    (e : GraphonRelabeling) :
    graphonHomDensity F (U.relabel e) = graphonHomDensity F U := by
  classical
  let Φ : (Fin f → UnitInterval) ≃ᵐ (Fin f → UnitInterval) :=
    MeasurableEquiv.piCongrRight (fun _ ↦ e.toMeasurableEquiv)
  have hΦ : MeasurePreserving Φ := by
    change MeasurePreserving (fun x : Fin f → UnitInterval ↦
      fun i ↦ e (x i)) volume volume
    exact volume_preserving_pi (fun _ ↦ e.measurePreserving)
  have hrelabel : ∀ᵐ z ∂unitSquareMeasure,
      (U.relabel e).value z = U.value (e.prodEquiv z) := by
    filter_upwards [(U.relabel e).value_ae_eq,
      U.relabel_ae_eq_value e] with z hzValue hzRelabel
    rw [hzValue, hzRelabel]
    rfl
  have hpair (q : Sym2 (Fin f)) (hq : q ∈ finiteGraphEdges F) :
      ∀ᵐ x : Fin f → UnitInterval ∂volume,
        graphonPairValue (U.relabel e) x q =
          graphonPairValue U (Φ x) q := by
    induction q using Sym2.inductionOn with
    | _ i j =>
        have hij : i ≠ j :=
          F.ne_of_adj ((mk_mem_finiteGraphEdges F i j).mp hq)
        have hpull :=
          (measurePreserving_pairProjection hij).quasiMeasurePreserving.ae
            hrelabel
        filter_upwards [hpull] with x hx
        change (U.relabel e).value (x i, x j) =
          U.value (e (x i), e (x j))
        simpa only [GraphonRelabeling.prodEquiv_apply] using hx
  have hall := (Filter.eventually_all_finset (finiteGraphEdges F)).2 hpair
  have hintegrand : ∀ᵐ x : Fin f → UnitInterval ∂volume,
      graphonHomIntegrand F (U.relabel e) x =
        graphonHomIntegrand F U (Φ x) := by
    filter_upwards [hall] with x hx
    exact Finset.prod_congr rfl fun q hq ↦ hx q hq
  unfold graphonHomDensity
  calc
    (∫ x : Fin f → UnitInterval,
        graphonHomIntegrand F (U.relabel e) x) =
        ∫ x, graphonHomIntegrand F U (Φ x) :=
      integral_congr_ae hintegrand
    _ = ∫ x, graphonHomIntegrand F U x := by
      simpa only [Function.comp_apply] using
        hΦ.integral_comp' (graphonHomIntegrand F U)

/-- The ordinary homomorphism density of a fixed finite graph is Lipschitz for
the cut pseudometric. -/
theorem abs_graphonHomDensity_sub_le_card_mul_cutDist
    {f : ℕ} (F : SimpleGraph (Fin f)) (U W : Graphon) :
    |graphonHomDensity F U - graphonHomDensity F W| ≤
      ((finiteGraphEdges F).card : ℝ) * cutDist U W := by
  classical
  by_cases hcard : (finiteGraphEdges F).card = 0
  · have hempty : finiteGraphEdges F = ∅ := Finset.card_eq_zero.mp hcard
    simp [graphonHomDensity, graphonHomIntegrand, hempty]
  · let a : NNReal :=
      ⟨|graphonHomDensity F U - graphonHomDensity F W|, abs_nonneg _⟩
    let k : NNReal := (finiteGraphEdges F).card
    have hk : 0 < k := by
      dsimp only [k]
      exact_mod_cast Nat.pos_of_ne_zero hcard
    have hdiv : a / k ≤ cutDistNN U W := by
      unfold cutDistNN
      apply le_ciInf
      intro e
      rw [div_le_iff₀ hk]
      apply NNReal.coe_le_coe.mp
      change |graphonHomDensity F U - graphonHomDensity F W| ≤
        cutNorm (relabelKernel U.toL1 e - W.toL1) *
          ((finiteGraphEdges F).card : ℝ)
      simpa only [graphonHomDensity_relabel F U e,
        Graphon.relabel_toL1, mul_comm] using
        abs_graphonHomDensity_sub_le_card_mul_cutNorm
          F (U.relabel e) W
    have ha : a ≤ k * cutDistNN U W := by
      have ha' : a ≤ cutDistNN U W * k :=
        (div_le_iff₀ hk).mp hdiv
      simpa only [mul_comm] using ha'
    exact_mod_cast ha

/-- Cut convergence implies convergence of every fixed finite ordinary
homomorphism density. -/
theorem graphonHomDensity_tendsto_of_cutDist_tendsto_zero
    {f : ℕ} (F : SimpleGraph (Fin f))
    {ι : Type*} {l : Filter ι} (W : ι → Graphon) (U : Graphon)
    (hcut : Tendsto (fun i ↦ cutDist (W i) U) l (nhds 0)) :
    Tendsto (fun i ↦ graphonHomDensity F (W i)) l
      (nhds (graphonHomDensity F U)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hdist : ∀ i,
      dist (graphonHomDensity F (W i)) (graphonHomDensity F U) ≤
        ((finiteGraphEdges F).card : ℝ) * cutDist (W i) U := by
    intro i
    simpa only [Real.dist_eq] using
      abs_graphonHomDensity_sub_le_card_mul_cutDist F (W i) U
  exact squeeze_zero (fun _ ↦ dist_nonneg) hdist (by
    simpa using
      (tendsto_const_nhds.mul hcut :
        Tendsto
          (fun i ↦ ((finiteGraphEdges F).card : ℝ) * cutDist (W i) U)
          l (nhds (((finiteGraphEdges F).card : ℝ) * 0))))

/-! ## Induced densities by local finite inclusion--exclusion -/

/-- Add a selected finite set of unordered pairs to a graph.  This counting
module uses its own name so that the construction remains independent of the
published-reference adapters in `Graphon.Equivalence`. -/
def countingInducedExpansionGraph {f : ℕ} (F : SimpleGraph (Fin f))
    (t : Finset (Sym2 (Fin f))) : SimpleGraph (Fin f) :=
  F ⊔ SimpleGraph.fromEdgeSet (t : Set (Sym2 (Fin f)))

private lemma finiteGraphEdges_countingInducedExpansionGraph {f : ℕ}
    (F : SimpleGraph (Fin f)) (t : Finset (Sym2 (Fin f)))
    (ht : t ⊆ finiteGraphEdges Fᶜ) :
    finiteGraphEdges (countingInducedExpansionGraph F t) =
      finiteGraphEdges F ∪ t := by
  classical
  ext e
  simp only [mem_finiteGraphEdges, countingInducedExpansionGraph,
    SimpleGraph.edgeSet_sup, Set.mem_union, SimpleGraph.edgeSet_fromEdgeSet,
    Set.mem_sdiff, Finset.mem_coe, Finset.mem_union]
  constructor
  · rintro (he | ⟨he, -⟩)
    · exact Or.inl he
    · exact Or.inr he
  · rintro (he | he)
    · exact Or.inl he
    · refine Or.inr ⟨he, ?_⟩
      have hec : e ∈ (Fᶜ).edgeSet :=
        (mem_finiteGraphEdges (F := Fᶜ) e).mp (ht he)
      exact (Fᶜ).not_isDiag_of_mem_edgeSet hec

private lemma disjoint_finiteGraphEdges_countingNonedgeSubset {f : ℕ}
    (F : SimpleGraph (Fin f)) (t : Finset (Sym2 (Fin f)))
    (ht : t ⊆ finiteGraphEdges Fᶜ) :
    Disjoint (finiteGraphEdges F) t := by
  rw [Finset.disjoint_left]
  intro e heF het
  have heFc := ht het
  rw [mem_finiteGraphEdges] at heF heFc
  have hdisj : Disjoint F.edgeSet (Fᶜ).edgeSet :=
    SimpleGraph.disjoint_edgeSet.mpr disjoint_compl_right
  exact hdisj.le_bot ⟨heF, heFc⟩

private lemma graphonHomIntegrand_countingInducedExpansionGraph {f : ℕ}
    (F : SimpleGraph (Fin f)) (W : Graphon)
    (x : Fin f → UnitInterval) (t : Finset (Sym2 (Fin f)))
    (ht : t ⊆ finiteGraphEdges Fᶜ) :
    graphonHomIntegrand (countingInducedExpansionGraph F t) W x =
      (∏ e ∈ finiteGraphEdges F, graphonPairValue W x e) *
        ∏ e ∈ t, graphonPairValue W x e := by
  classical
  rw [graphonHomIntegrand,
    finiteGraphEdges_countingInducedExpansionGraph F t ht,
    Finset.prod_union
      (disjoint_finiteGraphEdges_countingNonedgeSubset F t ht)]

/-- Pointwise inclusion--exclusion for the induced-density integrand, stated
inside the neutral counting layer. -/
theorem graphonInducedIntegrand_countingInclusionExclusion {f : ℕ}
    (F : SimpleGraph (Fin f)) (W : Graphon)
    (x : Fin f → UnitInterval) :
    graphonInducedIntegrand F W x =
      ∑ t ∈ (finiteGraphEdges Fᶜ).powerset,
        (-1 : ℝ) ^ t.card *
          graphonHomIntegrand (countingInducedExpansionGraph F t) W x := by
  classical
  unfold graphonInducedIntegrand
  rw [Finset.prod_sub (fun _ ↦ (1 : ℝ)) (graphonPairValue W x)
    (finiteGraphEdges Fᶜ), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have htsub : t ⊆ finiteGraphEdges Fᶜ := Finset.mem_powerset.mp ht
  rw [graphonHomIntegrand_countingInducedExpansionGraph F W x t htsub]
  simp only [Finset.prod_const_one]
  ring

/-- The induced density is a finite signed sum of ordinary homomorphism
densities, proved locally without any graph-limit assumption. -/
theorem graphonInducedDensity_countingInclusionExclusion {f : ℕ}
    (F : SimpleGraph (Fin f)) (W : Graphon) :
    graphonInducedDensity F W =
      ∑ t ∈ (finiteGraphEdges Fᶜ).powerset,
        (-1 : ℝ) ^ t.card *
          graphonHomDensity (countingInducedExpansionGraph F t) W := by
  unfold graphonInducedDensity
  simp_rw [graphonInducedIntegrand_countingInclusionExclusion F W]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t _ht
    rw [integral_const_mul]
    rfl
  · intro t _ht
    exact (integrable_graphonHomIntegrand
      (countingInducedExpansionGraph F t) W).const_mul _

/-- Cut convergence implies convergence of every fixed finite induced
homomorphism density. -/
theorem graphonInducedDensity_tendsto_of_cutDist_tendsto_zero
    {f : ℕ} (F : SimpleGraph (Fin f))
    {ι : Type*} {l : Filter ι} (W : ι → Graphon) (U : Graphon)
    (hcut : Tendsto (fun i ↦ cutDist (W i) U) l (nhds 0)) :
    Tendsto (fun i ↦ graphonInducedDensity F (W i)) l
      (nhds (graphonInducedDensity F U)) := by
  rw [graphonInducedDensity_countingInclusionExclusion F U]
  have hsum : Tendsto
      (fun i ↦ ∑ t ∈ (finiteGraphEdges Fᶜ).powerset,
        (-1 : ℝ) ^ t.card *
          graphonHomDensity (countingInducedExpansionGraph F t) (W i))
      l (nhds (∑ t ∈ (finiteGraphEdges Fᶜ).powerset,
        (-1 : ℝ) ^ t.card *
          graphonHomDensity (countingInducedExpansionGraph F t) U)) := by
    apply tendsto_finset_sum
    intro t _ht
    exact tendsto_const_nhds.mul
      (graphonHomDensity_tendsto_of_cutDist_tendsto_zero
        (countingInducedExpansionGraph F t) W U hcut)
  exact hsum.congr' (Eventually.of_forall fun i ↦
    (graphonInducedDensity_countingInclusionExclusion F (W i)).symm)

/-- For a specified relabeling, the edge-density discrepancy is bounded by
its cut cost. -/
theorem abs_graphonEdgeDensity_sub_le_cutCost
    (U W : Graphon) (e : GraphonRelabeling) :
    |graphonEdgeDensity U - graphonEdgeDensity W| ≤
      cutNorm (relabelKernel U.toL1 e - W.toL1) := by
  let K : IntegrableKernel := relabelKernel U.toL1 e - W.toL1
  let k : UnitSquare → ℝ := fun z ↦ U.relabelValue e z - W.value z
  have hk_meas : Measurable k :=
    (U.measurable_relabelValue e).sub W.measurable_value
  have hk : Integrable k unitSquareMeasure :=
    (U.integrable_relabelValue e).sub (integrable_graphonValue W)
  have hK : (fun z ↦ K z) =ᵐ[unitSquareMeasure] k := by
    have hUvalue := e.measurePreserving_prodEquiv.quasiMeasurePreserving.ae U.value_ae_eq
    filter_upwards [Lp.coeFn_sub (relabelKernel U.toL1 e) W.toL1,
      coeFn_relabelKernel U.toL1 e, hUvalue, W.value_ae_eq] with z hzsub hzrel hzU hzW
    simp only [K, k]
    rw [hzsub]
    change relabelKernel U.toL1 e z - W.toL1 z =
      U.relabelValue e z - W.value z
    have hzU' : U.value (e z.1, e z.2) = U.toL1 (e z.1, e z.2) := by
      simpa only [GraphonRelabeling.prodEquiv_apply] using hzU
    rw [hzrel, ← hzU', ← hzW]
    rfl
  have htest := abs_integral_mul_fst_mul_snd_le_cutNorm K hk hk_meas hK
    (f := fun _ ↦ 1) (g := fun _ ↦ 1) measurable_const measurable_const
    (fun _ ↦ zero_le_one) (fun _ ↦ le_rfl)
    (fun _ ↦ zero_le_one) (fun _ ↦ le_rfl)
  have hUintegral :
      (∫ z : UnitSquare, U.relabelValue e z ∂unitSquareMeasure) =
        ∫ z : UnitSquare, U.value z ∂unitSquareMeasure := by
    exact e.measurePreserving_prodEquiv.integral_comp' U.value
  have hkIntegral :
      (∫ z : UnitSquare, k z ∂unitSquareMeasure) =
        graphonEdgeDensity U - graphonEdgeDensity W := by
    simp only [k]
    rw [integral_sub (U.integrable_relabelValue e) (integrable_graphonValue W),
      hUintegral, graphonEdgeDensity_eq_integral_value U,
      graphonEdgeDensity_eq_integral_value W]
  simpa only [one_mul, mul_one, K, hkIntegral] using htest

/-- Edge density is `1`-Lipschitz for the graphon cut pseudometric. -/
theorem abs_graphonEdgeDensity_sub_le_cutDist_via_relabeling (U W : Graphon) :
    |graphonEdgeDensity U - graphonEdgeDensity W| ≤ cutDist U W := by
  let a : NNReal := ⟨|graphonEdgeDensity U - graphonEdgeDensity W|, abs_nonneg _⟩
  have ha : a ≤ cutDistNN U W := by
    unfold cutDistNN
    apply le_ciInf
    intro e
    apply NNReal.coe_le_coe.mp
    change |graphonEdgeDensity U - graphonEdgeDensity W| ≤
      cutNorm (relabelKernel U.toL1 e - W.toL1)
    exact abs_graphonEdgeDensity_sub_le_cutCost U W e
  exact_mod_cast ha

/-- Cut convergence implies exact convergence of edge densities. -/
theorem graphonEdgeDensity_tendsto_of_cutDist_tendsto_zero
    {ι : Type*} {l : Filter ι} (W : ι → Graphon) (U : Graphon)
    (hcut : Tendsto (fun i ↦ cutDist (W i) U) l (nhds 0)) :
    Tendsto (fun i ↦ graphonEdgeDensity (W i)) l
      (nhds (graphonEdgeDensity U)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hdist : ∀ i,
      dist (graphonEdgeDensity (W i)) (graphonEdgeDensity U) ≤
        cutDist (W i) U := by
    intro i
    simpa only [Real.dist_eq] using
      abs_graphonEdgeDensity_sub_le_cutDist_via_relabeling (W i) U
  exact squeeze_zero (fun _ ↦ dist_nonneg) hdist hcut

/-! ## Elementary limit-set and edge-normalization bridges -/

/-- Eventual membership is enough to exhibit a labeled-family limit: discard
the finite exceptional prefix and retain the shifted strictly increasing
extraction. -/
theorem mem_labeledGraphFamilyLimitSet_of_eventually_mem
    {Q : (n : ℕ) → Finset (SimpleGraph (Fin n))}
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (G : (j : ℕ) → SimpleGraph (Fin (σ j)))
    (hG : ∀ᶠ j in atTop, G j ∈ Q (σ j)) {W : Graphon}
    (hcut : Tendsto (fun j ↦ cutDist (graphGraphon (G j)) W)
      atTop (nhds 0)) :
    W ∈ labeledGraphFamilyLimitSet Q := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hG
  refine ⟨fun j ↦ σ (j + N),
    hσ.comp (strictMono_id.add_const N), fun j ↦ G (j + N), ?_, ?_⟩
  · intro j
    exact hN (j + N) (Nat.le_add_left N j)
  · exact (tendsto_add_atTop_iff_nat N).2 hcut

/-- If finite edge counts converge in the `n.choose 2` normalization, the
edge densities of the associated adjacency graphons converge to the same
limit. -/
theorem graphonEdgeDensity_graphGraphon_tendsto_of_normalizedEdgeCount
    {n : ℕ → ℕ} (hn : Tendsto n atTop atTop)
    (G : (j : ℕ) → SimpleGraph (Fin (n j))) {γ : ℝ}
    (hcount : Tendsto
      (fun j ↦ ((finiteGraphEdges (G j)).card : ℝ) /
        (completeEdgeCount (n j) : ℝ)) atTop (nhds γ)) :
    Tendsto (fun j ↦ graphonEdgeDensity (graphGraphon (G j)))
      atTop (nhds γ) := by
  have hfactor : Tendsto
      (fun j ↦ 2 * (completeEdgeCount (n j) : ℝ) /
        (n j : ℝ) ^ 2) atTop (nhds 1) :=
    completeEdgeCount_orderedSquareFactor_tendsto_one.comp hn
  have hprod := hcount.mul hfactor
  apply (show Tendsto
    (fun j ↦ (((finiteGraphEdges (G j)).card : ℝ) /
        (completeEdgeCount (n j) : ℝ)) *
      (2 * (completeEdgeCount (n j) : ℝ) / (n j : ℝ) ^ 2))
    atTop (nhds γ) by simpa using hprod).congr'
  filter_upwards [hn.eventually (eventually_atTop.2 ⟨2, fun _ hk ↦ hk⟩)]
    with j hj
  rw [graphonEdgeDensity_graphGraphon (by omega : 0 < n j)]
  have hchoose : (completeEdgeCount (n j) : ℝ) ≠ 0 := by
    rw [completeEdgeCount]
    exact_mod_cast (Nat.choose_pos hj).ne'
  field_simp

/-- Every cut limit of an exact-edge family has the prescribed limiting
edge density.  This is the direct representative-level feasibility bridge
for `exactEdgeInducedFreeLimitSet`. -/
theorem graphonEdgeDensity_eq_of_mem_exactEdgeInducedFreeLimitSet
    {h : ℕ} {H : SimpleGraph (Fin h)} {γ : ℝ} {m : ℕ → ℕ}
    (hm : HasAsymptoticEdgeDensity m γ) {W : Graphon}
    (hW : W ∈ exactEdgeInducedFreeLimitSet H γ m) :
    graphonEdgeDensity W = γ := by
  classical
  obtain ⟨σ, hσ, G, hG, hcut⟩ := hW
  have hedge (j : ℕ) :
      finiteGraphEdges (G j) =
        @SimpleGraph.edgeFinset (Fin (σ j)) (G j)
          (graphFamiliesEdgeSetFintype (G j)) := by
    ext e
    constructor
    · intro he
      exact (@SimpleGraph.mem_edgeFinset (Fin (σ j)) (G j) e
        (graphFamiliesEdgeSetFintype (G j))).2
        ((mem_finiteGraphEdges (G j) e).1 he)
    · intro he
      exact (mem_finiteGraphEdges (G j) e).2
        ((@SimpleGraph.mem_edgeFinset (Fin (σ j)) (G j) e
          (graphFamiliesEdgeSetFintype (G j))).1 he)
  have hcount : Tendsto
      (fun j ↦ ((finiteGraphEdges (G j)).card : ℝ) /
        (completeEdgeCount (σ j) : ℝ)) atTop (nhds γ) := by
    apply (hm.comp hσ.tendsto_atTop).congr'
    filter_upwards [] with j
    rw [hedge]
    exact congrArg
      (fun e : ℕ ↦ (e : ℝ) / (completeEdgeCount (σ j) : ℝ))
      (mem_inducedFreeGraphFinsetWithEdges.mp (hG j)).2.symm
  have hfinite :=
    graphonEdgeDensity_graphGraphon_tendsto_of_normalizedEdgeCount
      hσ.tendsto_atTop G hcount
  have hlimit :=
    graphonEdgeDensity_tendsto_of_cutDist_tendsto_zero
      (fun j ↦ graphGraphon (G j)) W hcut
  exact tendsto_nhds_unique hlimit hfinite

/-! ## Finite induced-density collision bound -/

/-- A vertex map realizes `H` as an induced labeled pattern in `G` when it
preserves and reflects adjacency.  Injectivity is deliberately kept
separate: noninjective maps are exactly the finite collision error in an
adjacency graphon. -/
def IsInducedGraphMap {h n : ℕ} (H : SimpleGraph (Fin h))
    (G : SimpleGraph (Fin n)) (φ : Fin h → Fin n) : Prop :=
  ∀ i j, H.Adj i j ↔ G.Adj (φ i) (φ j)

/-- The matrix induced-map weight of an adjacency matrix is the `0`-`1`
indicator of adjacency preservation and reflection. -/
theorem matrixInducedMapWeight_graphAdjacencyMatrix_eq_ite
    {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (φ : Fin h → Fin n)
    [Decidable (IsInducedGraphMap H G φ)] :
    matrixInducedMapWeight H (graphAdjacencyMatrix G)
        (graphAdjacencyMatrix_isSymm G) φ =
      if IsInducedGraphMap H G φ then 1 else 0 := by
  classical
  by_cases hφ : IsInducedGraphMap H G φ
  · have hedge :
        (∏ e ∈ finiteGraphEdges H,
          matrixMapPairValue (graphAdjacencyMatrix G)
            (graphAdjacencyMatrix_isSymm G) φ e) = 1 := by
      apply Finset.prod_eq_one
      intro e he
      revert he
      refine Sym2.inductionOn e ?_
      intro i j hij
      have hHij : H.Adj i j := by simpa using hij
      simp [matrixMapPairValue_mk, graphAdjacencyMatrix_apply,
        (hφ i j).mp hHij]
    have hnonedge :
        (∏ e ∈ finiteGraphEdges Hᶜ,
          (1 - matrixMapPairValue (graphAdjacencyMatrix G)
            (graphAdjacencyMatrix_isSymm G) φ e)) = 1 := by
      apply Finset.prod_eq_one
      intro e he
      revert he
      refine Sym2.inductionOn e ?_
      intro i j hij
      have hHcij : Hᶜ.Adj i j := by simpa using hij
      have hHcij' : i ≠ j ∧ ¬H.Adj i j := by
        simpa only [SimpleGraph.compl_adj] using hHcij
      have hnH : ¬H.Adj i j := hHcij'.2
      have hnG : ¬G.Adj (φ i) (φ j) := fun hG ↦ hnH ((hφ i j).mpr hG)
      simp [matrixMapPairValue_mk, graphAdjacencyMatrix_apply, hnG]
    simp [matrixInducedMapWeight, hedge, hnonedge, hφ]
  · have hbad_exists :
        ∃ i j, ¬(H.Adj i j ↔ G.Adj (φ i) (φ j)) := by
      simpa only [IsInducedGraphMap, not_forall] using hφ
    obtain ⟨i, j, hbad⟩ := hbad_exists
    by_cases hH : H.Adj i j
    · have hnG : ¬G.Adj (φ i) (φ j) := by
        intro hG
        exact hbad ⟨fun _ ↦ hG, fun _ ↦ hH⟩
      have hedge :
          (∏ e ∈ finiteGraphEdges H,
            matrixMapPairValue (graphAdjacencyMatrix G)
              (graphAdjacencyMatrix_isSymm G) φ e) = 0 := by
        apply Finset.prod_eq_zero (i := s(i, j))
        · simp [hH]
        · simp [matrixMapPairValue_mk, graphAdjacencyMatrix_apply, hnG]
      simp [matrixInducedMapWeight, hedge, hφ]
    · have hG : G.Adj (φ i) (φ j) := by
        by_contra hnG
        exact hbad ⟨fun h ↦ (hH h).elim, fun h ↦ (hnG h).elim⟩
      have hne : i ≠ j := by
        intro hij
        subst j
        exact G.loopless.irrefl _ hG
      have hHc : Hᶜ.Adj i j := by simp [hne, hH]
      have hnonedge :
          (∏ e ∈ finiteGraphEdges Hᶜ,
            (1 - matrixMapPairValue (graphAdjacencyMatrix G)
              (graphAdjacencyMatrix_isSymm G) φ e)) = 0 := by
        apply Finset.prod_eq_zero (i := s(i, j))
        · simp [hHc]
        · simp [matrixMapPairValue_mk, graphAdjacencyMatrix_apply, hG]
      simp [matrixInducedMapWeight, hnonedge, hφ]

/-- An injective induced-pattern map is a Mathlib strong graph embedding. -/
theorem inducedEmbeds_of_isInducedGraphMap_of_injective
    {h n : ℕ} {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)}
    {φ : Fin h → Fin n} (hφ : IsInducedGraphMap H G φ)
    (hinj : Function.Injective φ) :
    Regularity.InducedEmbeds H G := by
  exact ⟨{
    toFun := φ
    inj' := hinj
    map_rel_iff' := (hφ _ _).symm }⟩

/-- The finite set of noninjective maps from `Fin h` to `Fin n`. -/
def noninjectiveMapFinset (h n : ℕ) : Finset (Fin h → Fin n) := by
  classical
  exact Finset.univ.filter fun φ ↦ ¬Function.Injective φ

@[simp] theorem mem_noninjectiveMapFinset {h n : ℕ} {φ : Fin h → Fin n} :
    φ ∈ noninjectiveMapFinset h n ↔ ¬Function.Injective φ := by
  classical
  simp [noninjectiveMapFinset]

/-- Bundled embeddings are equivalent to functions equipped with an
injectivity proof. -/
def embeddingEquivInjectiveFunctions (h n : ℕ) :
    (Fin h ↪ Fin n) ≃ {φ : Fin h → Fin n // Function.Injective φ} where
  toFun φ := ⟨φ, φ.injective⟩
  invFun φ := ⟨φ, φ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact number of collision maps. -/
theorem card_noninjectiveMapFinset (h n : ℕ) :
    (noninjectiveMapFinset h n).card = n ^ h - n.descFactorial h := by
  classical
  have hinjCard :
      (Finset.univ.filter fun φ : Fin h → Fin n ↦ Function.Injective φ).card =
        n.descFactorial h := by
    calc
      _ = Fintype.card {φ : Fin h → Fin n // Function.Injective φ} :=
        (Fintype.card_subtype _).symm
      _ = Fintype.card (Fin h ↪ Fin n) :=
        Fintype.card_congr (embeddingEquivInjectiveFunctions h n).symm
      _ = n.descFactorial h := by simp
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin h → Fin n)))
    (p := fun φ ↦ Function.Injective φ)
  have hall : Fintype.card (Fin h → Fin n) = n ^ h := by simp
  rw [Finset.card_univ, hall, hinjCard] at hpartition
  rw [noninjectiveMapFinset]
  omega

/-- The collision proportion among all maps `Fin h → Fin n`. -/
noncomputable def collisionMapProportion (h n : ℕ) : ℝ :=
  ((n ^ h - n.descFactorial h : ℕ) : ℝ) / (n : ℝ) ^ h

/-- For an induced-`H`-free finite graph, all induced-pattern maps counted by
its adjacency graphon are noninjective.  The resulting density is bounded by
the exact collision proportion. -/
theorem graphonInducedDensity_graphGraphon_le_collisionMapProportion
    {h n : ℕ} (hn : 0 < n) (H : SimpleGraph (Fin h))
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : ¬Regularity.InducedEmbeds H G) :
    graphonInducedDensity H (graphGraphon G) ≤ collisionMapProportion h n := by
  classical
  rw [graphGraphon]
  rw [graphonInducedDensity_matrixGraphon_eq_sum hn]
  have hweight (φ : Fin h → Fin n) :
      matrixInducedMapWeight H (graphAdjacencyMatrix G)
          (graphAdjacencyMatrix_isSymm G) φ ≤
        if ¬Function.Injective φ then 1 else 0 := by
    rw [matrixInducedMapWeight_graphAdjacencyMatrix_eq_ite]
    by_cases hmap : IsInducedGraphMap H G φ
    · have hninj : ¬Function.Injective φ := fun hinj ↦
        hfree (inducedEmbeds_of_isInducedGraphMap_of_injective hmap hinj)
      simp [hmap, hninj]
    · rw [if_neg hmap]
      split <;> norm_num
  calc
    (∑ φ : Fin h → Fin n,
        (1 / (n : ℝ)) ^ h *
          matrixInducedMapWeight H (graphAdjacencyMatrix G)
            (graphAdjacencyMatrix_isSymm G) φ) ≤
        ∑ φ : Fin h → Fin n,
          (1 / (n : ℝ)) ^ h *
            (if ¬Function.Injective φ then 1 else 0) := by
      apply Finset.sum_le_sum
      intro φ _
      exact mul_le_mul_of_nonneg_left (hweight φ) (by positivity)
    _ = (1 / (n : ℝ)) ^ h *
          ((noninjectiveMapFinset h n).card : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      calc
        (∑ φ : Fin h → Fin n,
            if ¬Function.Injective φ then (1 : ℝ) else 0) =
            (((Finset.univ.filter fun φ : Fin h → Fin n ↦
              ¬Function.Injective φ).card : ℕ) : ℝ) := by
                simpa only [Finset.sum_boole]
        _ = ((noninjectiveMapFinset h n).card : ℝ) := rfl
    _ = collisionMapProportion h n := by
      rw [card_noninjectiveMapFinset]
      simp only [collisionMapProportion, one_div, inv_pow]
      rw [mul_comm]
      rfl

/-- The exact collision proportion tends to zero for every fixed source
order. -/
theorem collisionMapProportion_tendsto_zero (h : ℕ) :
    Tendsto (collisionMapProportion h) atTop (nhds 0) := by
  have hpow_ne : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ h ≠ 0 := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hn ↦ hn⟩] with n hn
    positivity
  have hratio : Tendsto
      (fun n : ℕ ↦ (n.descFactorial h : ℝ) / (n : ℝ) ^ h)
      atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one hpow_ne).mp (isEquivalent_descFactorial h)
  have heq : ∀ᶠ n : ℕ in atTop,
      collisionMapProportion h n =
        1 - (n.descFactorial h : ℝ) / (n : ℝ) ^ h := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hn ↦ hn⟩] with n hn
    rw [collisionMapProportion, Nat.cast_sub (Nat.descFactorial_le_pow n h)]
    push_cast
    have hn0 : (n : ℝ) ^ h ≠ 0 := by positivity
    field_simp
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hsub : Tendsto
      (fun n : ℕ ↦ (1 : ℝ) -
        (n.descFactorial h : ℝ) / (n : ℝ) ^ h)
      atTop (nhds 0) := by
    simpa using (hone.sub hratio)
  exact hsub.congr' (heq.mono fun _ hn ↦ hn.symm)

/-- Along any sequence whose orders tend to infinity, induced-free finite
adjacency graphons have induced `H`-density tending to zero. -/
theorem graphonInducedDensity_graphGraphon_tendsto_zero_of_inducedFree
    {h : ℕ} (H : SimpleGraph (Fin h)) {n : ℕ → ℕ}
    (hn : Tendsto n atTop atTop)
    (G : (j : ℕ) → SimpleGraph (Fin (n j)))
    (hfree : ∀ j, ¬Regularity.InducedEmbeds H (G j)) :
    Tendsto (fun j ↦ graphonInducedDensity H (graphGraphon (G j)))
      atTop (nhds 0) := by
  have hcollision :
      Tendsto (fun j ↦ collisionMapProportion h (n j)) atTop (nhds 0) :=
    (collisionMapProportion_tendsto_zero h).comp hn
  apply squeeze_zero'
  · exact Eventually.of_forall fun j ↦ graphonInducedDensity_nonneg H _
  · filter_upwards [hn.eventually (eventually_atTop.2 ⟨1, fun _ hk ↦ hk⟩)] with j hj
    letI : DecidableRel (G j).Adj := Classical.decRel _
    exact graphonInducedDensity_graphGraphon_le_collisionMapProportion
      hj H (G j) (hfree j)
  · exact hcollision

/-- Every cut limit of the exact-edge induced-`H`-free finite family has
zero induced `H`-density.  This combines the axiom-free cut-continuity
theorem with the explicit finite collision bound. -/
theorem graphonInducedDensity_eq_zero_of_mem_exactEdgeInducedFreeLimitSet
    {h : ℕ} {H : SimpleGraph (Fin h)} {γ : ℝ} {m : ℕ → ℕ}
    {W : Graphon} (hW : W ∈ exactEdgeInducedFreeLimitSet H γ m) :
    graphonInducedDensity H W = 0 := by
  obtain ⟨σ, hσ, G, hG, hcut⟩ :=
    (mem_exactEdgeInducedFreeLimitSet.mp hW)
  have hfree : ∀ j, ¬Regularity.InducedEmbeds H (G j) := fun j ↦
    (mem_inducedFreeGraphFinsetWithEdges.mp (hG j)).1
  have hfinite :=
    graphonInducedDensity_graphGraphon_tendsto_zero_of_inducedFree
      H hσ.tendsto_atTop G hfree
  have hlimit :=
    graphonInducedDensity_tendsto_of_cutDist_tendsto_zero
      H (fun j ↦ graphGraphon (G j)) W hcut
  exact tendsto_nhds_unique hlimit hfinite

end InducedStars
