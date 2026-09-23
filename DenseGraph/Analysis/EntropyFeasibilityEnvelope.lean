import DenseGraph.Analysis
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform finite entropy envelopes

An ideal selected count can lie just outside the feasible interval even when
the actual count is feasible. Its entropy is not then used as a bound on the
actual family. Instead, the feasible entropy envelope is zero outside the
interval, and a uniformly small perturbation has a small scaled entropy cost.
All entropy values are in bits.
-/

open Set

namespace DenseGraph

/-- The finite feasible entropy value, with zero used as an *upper-envelope
reference* outside the feasible interval, not as an assertion of feasibility. -/
noncomputable def feasibleEntropyEnvelope (R B target : ℝ) : ℝ :=
  if target ∈ Icc B (B + R) then R * binaryEntropy ((target - B) / R) else 0

@[simp] theorem feasibleEntropyEnvelope_zero (B target : ℝ) :
    feasibleEntropyEnvelope 0 B target = 0 := by
  simp [feasibleEntropyEnvelope]

theorem feasibleEntropyEnvelope_eq_of_mem {R B target : ℝ}
    (h : target ∈ Icc B (B + R)) :
    feasibleEntropyEnvelope R B target = R * binaryEntropy ((target - B) / R) := by
  simp only [feasibleEntropyEnvelope, if_pos h]

theorem feasibleEntropyEnvelope_eq_zero_of_not_mem {R B target : ℝ}
    (h : target ∉ Icc B (B + R)) : feasibleEntropyEnvelope R B target = 0 := by
  simp only [feasibleEntropyEnvelope, if_neg h]

/-- At zero capacity the only feasible target is exactly the forced count. -/
theorem zero_capacity_feasible_target {B target : ℝ}
    (h : target ∈ Icc B (B + 0)) : target = B := by
  exact le_antisymm (by simpa only [add_zero] using h.2) h.1

private theorem entropy_le_one (q : ℝ) : binaryEntropy q ≤ 1 := by
  rw [binaryEntropy]
  exact (div_le_one realLogTwo_pos).2 Real.binEntropy_le_log_two

private theorem feasible_density {R B target : ℝ} (hR : 0 < R)
    (ht : target ∈ Icc B (B + R)) : (target - B) / R ∈ Icc (0 : ℝ) 1 := by
  exact ⟨div_nonneg (sub_nonneg.mpr ht.1) hR.le,
    (div_le_one hR).2 (by linarith [ht.2])⟩

/-- Uniform continuity for entropy multiplied by an arbitrary capacity at most
the ambient scale. The modulus does not depend on either count or capacity. -/
theorem entropy_scaled_feasible_uniform {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ N R B actual ideal : ℝ,
      0 < N → 0 ≤ R → R ≤ N →
      actual ∈ Icc B (B + R) → ideal ∈ Icc B (B + R) →
      |actual - ideal| ≤ delta * N →
      |R * binaryEntropy ((actual - B) / R) -
        R * binaryEntropy ((ideal - B) / R)| ≤ epsilon * N := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous
    (binaryEntropy_continuous.continuousOn : ContinuousOn binaryEntropy (Icc (0 : ℝ) 1))
  obtain ⟨u, hu, hmod⟩ := Metric.uniformContinuousOn_iff_le.mp huc epsilon he
  refine ⟨u * epsilon, mul_pos hu he, ?_⟩
  intro N R B actual ideal hN hR hRN hactual hideal hclose
  rcases hR.eq_or_lt with rfl | hRpos
  · simpa using (mul_nonneg he.le hN.le)
  have hqa := feasible_density hRpos hactual
  have hqi := feasible_density hRpos hideal
  have hHa0 := binaryEntropy_nonneg hqa.1 hqa.2
  have hHi0 := binaryEntropy_nonneg hqi.1 hqi.2
  have hHa1 := entropy_le_one ((actual - B) / R)
  have hHi1 := entropy_le_one ((ideal - B) / R)
  by_cases hsmall : R ≤ epsilon * N
  · have ha0 := mul_nonneg hRpos.le hHa0
    have hi0 := mul_nonneg hRpos.le hHi0
    have ha1 := mul_le_mul_of_nonneg_left hHa1 hRpos.le
    have hi1 := mul_le_mul_of_nonneg_left hHi1 hRpos.le
    apply abs_le.mpr
    constructor <;> nlinarith only [hsmall, ha0, hi0, ha1, hi1]
  have hratio : dist ((actual - B) / R) ((ideal - B) / R) ≤ u := by
    rw [Real.dist_eq, ← sub_div]
    have heq : actual - B - (ideal - B) = actual - ideal := by ring
    rw [heq, abs_div, abs_of_pos hRpos]
    apply (div_le_iff₀ hRpos).2
    have hmul := mul_le_mul_of_nonneg_left (lt_of_not_ge hsmall).le hu.le
    nlinarith only [hclose, hmul]
  have hentropy := hmod _ hqa _ hqi hratio
  rw [Real.dist_eq] at hentropy
  rw [← mul_sub, abs_mul, abs_of_pos hRpos]
  exact (mul_le_mul_of_nonneg_left hentropy hRpos.le).trans
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hRN he.le)

/-- A nearby ideal count is either feasible with a small entropy error, or
infeasible and the actual feasible entropy itself is small. The zero-capacity
case is included without relying on totalized division for feasibility. -/
theorem entropy_feasibility_envelope {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ N R B actual ideal : ℝ,
      0 < N → 0 ≤ R → R ≤ N → actual ∈ Icc B (B + R) →
      |actual - ideal| ≤ delta * N →
      (ideal ∈ Icc B (B + R) ∧
        |R * binaryEntropy ((actual - B) / R) -
          R * binaryEntropy ((ideal - B) / R)| ≤ epsilon * N) ∨
      (ideal ∉ Icc B (B + R) ∧
        R * binaryEntropy ((actual - B) / R) ≤ epsilon * N) := by
  obtain ⟨delta, hd, hmod⟩ := entropy_scaled_feasible_uniform he
  refine ⟨delta, hd, ?_⟩
  intro N R B actual ideal hN hR hRN hactual hclose
  by_cases hideal : ideal ∈ Icc B (B + R)
  · exact Or.inl ⟨hideal, hmod N R B actual ideal hN hR hRN hactual hideal hclose⟩
  refine Or.inr ⟨hideal, ?_⟩
  rcases hR.eq_or_lt with rfl | hRpos
  · have hactualEq := zero_capacity_feasible_target hactual
    subst actual
    simpa using (mul_nonneg he.le hN.le)
  by_cases hlo : ideal < B
  · have hendpoint : B ∈ Icc B (B + R) := ⟨le_rfl, by linarith⟩
    have hdist : |actual - B| ≤ delta * N := by
      rw [abs_of_nonneg (sub_nonneg.mpr hactual.1)]
      have hh := le_abs_self (actual - ideal)
      linarith only [hlo, hh, hclose]
    have hh := hmod N R B actual B hN hR hRN hactual hendpoint hdist
    simpa only [sub_self, zero_div, InducedStars.binaryEntropy_zero, mul_zero, sub_zero]
      using (le_abs_self _).trans hh
  · have hhi : B + R < ideal := by
      by_contra hhi
      exact hideal ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩
    have hendpoint : B + R ∈ Icc B (B + R) := ⟨by linarith, le_rfl⟩
    have hdist : |actual - (B + R)| ≤ delta * N := by
      rw [abs_of_nonpos (sub_nonpos.mpr hactual.2), neg_sub]
      have hh := neg_le_abs (actual - ideal)
      linarith only [hhi, hh, hclose]
    have hh := hmod N R B actual (B + R) hN hR hRN hactual hendpoint hdist
    simpa only [add_sub_cancel_left, div_self hRpos.ne', InducedStars.binaryEntropy_one,
      mul_zero, sub_zero] using (le_abs_self _).trans hh

/-- A convenient one-sided feasible-envelope estimate for entropy-gap and
finite counting arguments. An infeasible ideal count contributes zero, but
its nearby nonempty slice retains the explicit error term. -/
theorem entropy_le_feasibleEnvelope_add_error {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ N R B actual ideal : ℝ,
      0 < N → 0 ≤ R → R ≤ N → actual ∈ Icc B (B + R) →
      |actual - ideal| ≤ delta * N →
      R * binaryEntropy ((actual - B) / R) ≤
        feasibleEntropyEnvelope R B ideal + epsilon * N := by
  obtain ⟨delta, hd, hmod⟩ := entropy_feasibility_envelope he
  refine ⟨delta, hd, ?_⟩
  intro N R B actual ideal hN hR hRN hactual hclose
  rcases hmod N R B actual ideal hN hR hRN hactual hclose with
    ⟨hideal, herr⟩ | ⟨hideal, herr⟩
  · rw [feasibleEntropyEnvelope_eq_of_mem hideal]
    linarith only [le_of_abs_le herr]
  · rw [feasibleEntropyEnvelope_eq_zero_of_not_mem hideal, zero_add]
    exact herr

end DenseGraph
