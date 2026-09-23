import InducedStars.Structure.Subcritical.ResidualGraphCount

/-!
# From residual safety to the existing matching exponent

The residual family is counted by the actual graph bound. The only
probability input is a uniform estimate for the already-defined residual
safe maximum. The outer rooted-pattern maximum costs no counting factor.
The safe-log zero branch is treated with its actual negative cubic value.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

/-- The exact finite residual-enumeration coefficient in natural units.
It is used only at positive order, so its final division is not totalized
to hide a zero denominator. Weighted residual enumeration supplies the entropy term. -/
def subcriticalResidualEnumerationCoefficient (k : ℕ) (alpha theta : ℝ) (n : ℕ) : ℝ :=
  2 * (Real.binEntropy (subcriticalResidualDegreeCoefficient k alpha theta) +
    subcriticalResidualWeightConstant k * subcriticalResidualDegreeCoefficient k alpha theta +
    Real.log (n + 1) / n)

theorem subcriticalResidualEnumerationCoefficient_mul {k n : ℕ}
    (alpha theta : ℝ) (hn : 0 < n) (ell : ℕ) :
    subcriticalResidualEnumerationCoefficient k alpha theta n * ell * n =
      (2 * ell : ℕ) * ((n : ℝ) *
        (Real.binEntropy (subcriticalResidualDegreeCoefficient k alpha theta) +
          subcriticalResidualWeightConstant k * subcriticalResidualDegreeCoefficient k alpha theta) +
        Real.log (n + 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold subcriticalResidualEnumerationCoefficient
  push_cast
  field_simp
  <;> ring

/-- Exact safe-log upper bound, with the fallback checked separately. -/
theorem subcriticalLogWeight_le_of_le_exp (n : ℕ) {x a : ℝ}
    (hx : 0 ≤ x) (hbound : x ≤ Real.exp a) (hzero : -((n + 1 : ℝ) ^ 3) ≤ a) :
    subcriticalLogWeight n x ≤ a := by
  unfold subcriticalLogWeight
  split_ifs with hz
  · exact hzero
  · have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    exact (Real.log_le_log hpos hbound).trans_eq (Real.log_exp a)

/-- The profile's exact matching cardinality bound controls the negative
cubic fallback after a simple explicit order reserve. -/
theorem subcriticalMatching_zero_fallback_le {n ell : ℕ} {c : ℝ}
    (hc : 0 ≤ c) (hmatching : 2 * ell ≤ n) (horder : c ≤ n + 1) :
    -((n + 1 : ℝ) ^ 3) ≤ -(c / 2) * ell * n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hmatch : 2 * (ell : ℝ) ≤ n := by exact_mod_cast hmatching
  have h₁ := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmatch hc) hn
  have h₂ := mul_le_mul_of_nonneg_right horder (sq_nonneg (n : ℝ))
  nlinarith only [h₁, h₂, hn, sq_nonneg (n : ℝ)]

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}

/-- Uniform safety is multiplied into the whole residual weighted sum;
the enumeration factor is paid exactly once. -/
theorem subcriticalResidualMatchingWeightedSum_le
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C delta epsilon : ℝ) (TB : SimpleGraph V) (c : ℝ)
    (hn : 0 < Fintype.card V) (ha : 0 ≤ alpha) (ht : 0 ≤ theta)
    (hhalf : subcriticalResidualDegreeCoefficient k alpha theta ≤ 1 / 2)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hsmall : ∀ G ∈ F, ∀ v,
      (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
        subcriticalSparseSideConstant k * theta * Fintype.card V)
    (hprob : ∀ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
      subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R ≤
        Real.exp (-c * p.ell * Fintype.card V)) :
    (∑ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
      Real.exp (subcriticalResidualWeightConstant k * (finiteGraphEdges R).card) *
        subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R) ≤
      Real.exp ((subcriticalResidualEnumerationCoefficient k alpha theta (Fintype.card V) - c) *
        p.ell * Fintype.card V) := by
  have hcount := subcriticalResidualWeightedGraphCount_le F p TB ha ht hhalf hret hsmall
  rw [← subcriticalResidualEnumerationCoefficient_mul alpha theta hn p.ell] at hcount
  calc
    _ ≤ ∑ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
        Real.exp (subcriticalResidualWeightConstant k * (finiteGraphEdges R).card) *
          Real.exp (-c * p.ell * Fintype.card V) :=
      Finset.sum_le_sum (fun R hR ↦ mul_le_mul_of_nonneg_left (hprob R hR) (Real.exp_pos _).le)
    _ = (∑ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
        Real.exp (subcriticalResidualWeightConstant k * (finiteGraphEdges R).card)) *
          Real.exp (-c * p.ell * Fintype.card V) := (Finset.sum_mul ..).symm
    _ ≤ Real.exp (subcriticalResidualEnumerationCoefficient k alpha theta (Fintype.card V) *
        p.ell * Fintype.card V) * Real.exp (-c * p.ell * Fintype.card V) :=
      mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The maximum over rooted patterns introduces no additional entropy.
This is an estimate of the existing matching weight, not a replacement
surrogate or a separate pointwise residual estimate. -/
theorem subcriticalProfileMatchingWeight_le_of_safeMaximum
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C delta epsilon c : ℝ)
    (hn : 0 < Fintype.card V) (ha : 0 ≤ alpha) (ht : 0 ≤ theta)
    (hhalf : subcriticalResidualDegreeCoefficient k alpha theta ≤ 1 / 2)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hsmall : ∀ G ∈ F, ∀ v,
      (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
        subcriticalSparseSideConstant k * theta * Fintype.card V)
    (hprob : ∀ TB ∈ subcriticalRootedDefectPatternFinset F alpha p,
      ∀ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
        subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R ≤
          Real.exp (-c * p.ell * Fintype.card V))
    (herror : subcriticalResidualEnumerationCoefficient k alpha theta (Fintype.card V) ≤ c / 2) :
    subcriticalProfileMatchingWeight F p m C alpha delta epsilon ≤
      Real.exp (-(c / 2) * p.ell * Fintype.card V) := by
  unfold subcriticalProfileMatchingWeight
  apply subcriticalFiniteMax_le (Real.exp_pos _).le
  intro TB hTB
  apply (subcriticalResidualMatchingWeightedSum_le F p m C delta epsilon TB c hn ha ht
    hhalf hret hsmall (hprob TB hTB)).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith :
      subcriticalResidualEnumerationCoefficient k alpha theta (Fintype.card V) - c ≤ -(c / 2))
      (Nat.cast_nonneg p.ell)) (Nat.cast_nonneg (Fintype.card V))

/-- Algebraic matching-exponent endpoint. The probability input is explicitly
the actual residual-safe maximum; all pattern enumeration is proved above.
The zero weight case uses `p.two_mul_ell_le` and the finite cubic reserve. -/
theorem subcriticalProfileMatchingExponent_le_of_safeMaximum
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C delta epsilon c : ℝ) (hc : 0 ≤ c)
    (hn : 0 < Fintype.card V) (ha : 0 ≤ alpha) (ht : 0 ≤ theta)
    (hhalf : subcriticalResidualDegreeCoefficient k alpha theta ≤ 1 / 2)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hsmall : ∀ G ∈ F, ∀ v,
      (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
        subcriticalSparseSideConstant k * theta * Fintype.card V)
    (hprob : ∀ TB ∈ subcriticalRootedDefectPatternFinset F alpha p,
      ∀ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
        subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R ≤
          Real.exp (-c * p.ell * Fintype.card V))
    (herror : subcriticalResidualEnumerationCoefficient k alpha theta (Fintype.card V) ≤ c / 2)
    (horder : c ≤ Fintype.card V + 1) :
    subcriticalProfileMatchingExponent F p m C alpha delta epsilon ≤
      -(c / 2) * p.ell * Fintype.card V := by
  apply subcriticalLogWeight_le_of_le_exp
    (Fintype.card V) (subcriticalFiniteMax_nonneg _ _)
    (subcriticalProfileMatchingWeight_le_of_safeMaximum F p m C delta epsilon c hn ha ht
      hhalf hret hsmall hprob herror)
  exact subcriticalMatching_zero_fallback_le hc p.two_mul_ell_le horder

/-- `cMat/kappa` specialization of the preceding algebra. Candidate geometry
and Janson will discharge `hprob`; they are not postulated by this theorem. -/
theorem subcriticalResidualMatchingExponent_le_of_safeMaximum
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C delta epsilon cMat : ℝ) (kappa : ℕ)
    (hcMat : 0 < cMat) (hkappa : 1 ≤ kappa)
    (hn : 0 < Fintype.card V) (ha : 0 ≤ alpha) (ht : 0 ≤ theta)
    (hhalf : subcriticalResidualDegreeCoefficient k alpha theta ≤ 1 / 2)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hsmall : ∀ G ∈ F, ∀ v,
      (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
        subcriticalSparseSideConstant k * theta * Fintype.card V)
    (hprob : ∀ TB ∈ subcriticalRootedDefectPatternFinset F alpha p,
      ∀ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
        subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R ≤
          Real.exp (-(cMat / kappa) * p.ell * Fintype.card V))
    (herror : subcriticalResidualEnumerationCoefficient k alpha theta (Fintype.card V) ≤
      cMat / (2 * kappa))
    (horder : cMat / kappa ≤ Fintype.card V + 1) :
    subcriticalProfileMatchingExponent F p m C alpha delta epsilon ≤
      -(cMat / (2 * kappa)) * p.ell * Fintype.card V := by
  have hkappaPos : (0 : ℝ) < kappa := by
    exact_mod_cast (show 0 < kappa by omega)
  have heq : cMat / (2 * (kappa : ℝ)) = (cMat / kappa) / 2 := by ring
  rw [heq] at herror ⊢
  exact subcriticalProfileMatchingExponent_le_of_safeMaximum F p m C delta epsilon
    (cMat / kappa) (div_pos hcMat hkappaPos).le hn ha ht hhalf hret
    hsmall hprob herror horder

end InducedStars
