import InducedStars.Structure.Supercritical.CoverMultiplicity
import DenseGraph.Combinatorics.ExponentialSums

/-!
# Cover uniqueness from a forced-edge probability capability

The deterministic competing-cover geometry from the supercritical proof is
independent of the random model. This adapter isolates its union bound so
independent fixed counts on the individual active pairs can use it as well.
-/

noncomputable section
open Finset Filter
open scoped BigOperators Classical
namespace InducedStars

private theorem exp_forced_near {k n t q : ℕ} (hk : 3 ≤ k) {c : ℝ}
    (hc : 0 ≤ c) (h : t * n ≤ 4 * (k - 1) * q) :
    Real.exp (-(c * q)) ≤ Real.exp (-(c / (4 * (k - 1 : ℕ)) * t * n)) := by
  have hr : (0 : ℝ) < 4 * (k - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < 4 * (k - 1))
  have hh : (t : ℝ) * n ≤ (4 * (k - 1 : ℕ) : ℝ) * q := by exact_mod_cast h
  have hd := (div_le_iff₀ hr).mpr (show (t : ℝ) * n ≤ (q : ℝ) *
      (4 * (k - 1 : ℕ)) by simpa only [mul_comm] using hh)
  have hm := mul_le_mul_of_nonneg_left hd hc
  apply Real.exp_le_exp.mpr
  have heq : c * ((t : ℝ) * n / (4 * (k - 1 : ℕ))) =
      c / (4 * (k - 1 : ℕ)) * t * n := by ring
  rw [heq] at hm
  exact neg_le_neg hm

private theorem exp_forced_far {k n q : ℕ} (hk : 3 ≤ k) {c : ℝ}
    (hc : 0 ≤ c) (h : n ^ 2 ≤ 16 * (k - 1) ^ 8 * q) :
    Real.exp (-(c * q)) ≤ Real.exp (-(c / (16 * (k - 1 : ℕ)^8) * (n:ℝ)^2)) := by
  have hr : (0 : ℝ) < 16 * (k - 1 : ℕ)^8 := by
    have : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (by omega : 0 < k - 1)
    positivity
  have hh : (n : ℝ)^2 ≤ (16 * (k - 1 : ℕ)^8 : ℝ) * q := by exact_mod_cast h
  have hd := (div_le_iff₀ hr).mpr (show (n : ℝ)^2 ≤ (q : ℝ) *
      (16 * (k - 1 : ℕ)^8) by simpa only [mul_comm] using hh)
  have hm := mul_le_mul_of_nonneg_left hd hc
  apply Real.exp_le_exp.mpr
  have heq : c * ((n : ℝ)^2 / (16 * (k - 1 : ℕ)^8)) =
      c / (16 * (k - 1 : ℕ)^8) * (n : ℝ)^2 := by ring
  rw [heq] at hm
  exact neg_le_neg hm

/-- The actual finite sum over every competing ordered clique cover.
No event-probability estimate is an assumption of this deterministic lemma. -/
theorem sum_competingCover_exp_forced_le_near_far
    {k n a : ℕ} (hk : 3 ≤ k) (D : SupercriticalDivision k (Fin n))
    (hD : D.IsFull) (hpart : ∀ i, a ≤ (D.parts i).card)
    (hscale : n ≤ 2 * (k - 1) * a) {c : ℝ} (hc : 0 ≤ c) :
    (∑ E ∈ competingFullSupercriticalDivisions D,
      Real.exp (-(c * (forcedCrossEdgesBySecondCover D E).card))) ≤
      (∑ t ∈ Finset.Icc 1 n,
        (((k - 1).factorial * n.choose t * (k - 1)^t : ℕ) : ℝ) *
          Real.exp (-(c / (4 * (k - 1 : ℕ)) * t * n))) +
      (k : ℝ)^n * Real.exp (-(c / (16 * (k - 1 : ℕ)^8) * (n:ℝ)^2)) := by
  let S := competingFullSupercriticalDivisions D
  let N := S.filter fun E ↦ 2 * fullDivisionMoveDistance D E ≤ a
  let F := S.filter fun E ↦ ¬ 2 * fullDivisionMoveDistance D E ≤ a
  let near : ℕ → ℝ := fun t ↦ Real.exp (-(c / (4 * (k - 1 : ℕ)) * t * n))
  let far : ℝ := Real.exp (-(c / (16 * (k - 1 : ℕ)^8) * (n:ℝ)^2))
  have hsplit : (∑ E ∈ S, Real.exp (-(c * (forcedCrossEdgesBySecondCover D E).card))) =
      (∑ E ∈ N, Real.exp (-(c * (forcedCrossEdgesBySecondCover D E).card))) +
      (∑ E ∈ F, Real.exp (-(c * (forcedCrossEdgesBySecondCover D E).card))) := by
    exact (Finset.sum_filter_add_sum_filter_not S _ _).symm
  have hnear E (hE : E ∈ N) :
      Real.exp (-(c * (forcedCrossEdgesBySecondCover D E).card)) ≤
        near (fullDivisionMoveDistance D E) := by
    obtain ⟨hES, hn⟩ := Finset.mem_filter.mp hE
    obtain ⟨hfull, hneq⟩ := mem_competingFullSupercriticalDivisions.mp hES
    have hd := forcedCrossEdges_near_or_far hk D E hD hfull a hpart
      (by simpa using hscale) hneq
    apply exp_forced_near hk hc
    rcases hd with hd | hd
    · simpa using hd.2.2
    · omega
  have hfar E (hE : E ∈ F) :
      Real.exp (-(c * (forcedCrossEdgesBySecondCover D E).card)) ≤ far := by
    obtain ⟨hES, hn⟩ := Finset.mem_filter.mp hE
    obtain ⟨hfull, hneq⟩ := mem_competingFullSupercriticalDivisions.mp hES
    have hd := forcedCrossEdges_near_or_far hk D E hD hfull a hpart
      (by simpa using hscale) hneq
    apply exp_forced_far hk hc
    rcases hd with hd | hd
    · exact False.elim (hn hd.2.1)
    · simpa using hd.2
  have hmem E (hE : E ∈ N) : fullDivisionMoveDistance D E ∈ Finset.Icc 1 n := by
    have hneq := (mem_competingFullSupercriticalDivisions.mp (Finset.mem_filter.mp hE).1).2
    refine Finset.mem_Icc.mpr ⟨?_, by simpa using fullDivisionMoveDistance_le_card D E⟩
    by_contra h
    exact hneq ((fullDivisionMoveDistance_eq_zero_iff D E).mp (by omega))
  have hgroup : (∑ E ∈ N, near (fullDivisionMoveDistance D E)) =
      ∑ t ∈ Finset.Icc 1 n,
        ((N.filter fun E ↦ fullDivisionMoveDistance D E = t).card : ℝ) * near t := by
    calc
      _ = ∑ E ∈ N, ∑ t ∈ Finset.Icc 1 n,
          if fullDivisionMoveDistance D E = t then near t else 0 := by
        apply Finset.sum_congr rfl
        intro E hE
        rw [Finset.sum_eq_single (fullDivisionMoveDistance D E)]
        · simp
        · intro t _ ht
          simp [ht.symm]
        · exact fun h ↦ (h (hmem E hE)).elim
      _ = ∑ t ∈ Finset.Icc 1 n, ∑ E ∈ N,
          if fullDivisionMoveDistance D E = t then near t else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [← Finset.sum_filter]
        simp
  have hnearCard t : (N.filter fun E ↦ fullDivisionMoveDistance D E = t).card ≤
      (k - 1).factorial * n.choose t * (k - 1)^t := by
    apply (Finset.card_le_card (t := fullDivisionsAtMoveDistance D t) ?_).trans
      (card_fullDivisionsAtMoveDistance_le D hD t)
    intro E hE
    obtain ⟨hEN, hdist⟩ := Finset.mem_filter.mp hE
    exact mem_fullDivisionsAtMoveDistance.mpr
      ⟨(mem_competingFullSupercriticalDivisions.mp (Finset.mem_filter.mp hEN).1).1, hdist⟩
  have hfarCard : F.card ≤ k^n := by
    apply (Finset.card_le_card (t := allSupercriticalDivisions k n)
      (fun E _ ↦ mem_allSupercriticalDivisions E)).trans
    exact card_allSupercriticalDivisions_le (by omega)
  rw [hsplit]
  apply add_le_add
  · calc
      _ ≤ ∑ E ∈ N, near (fullDivisionMoveDistance D E) := Finset.sum_le_sum hnear
      _ = _ := hgroup
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro t ht
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact_mod_cast hnearCard t
  · calc
      _ ≤ ∑ _E ∈ F, far := Finset.sum_le_sum hfar
      _ = (F.card : ℝ) * far := by simp
      _ ≤ (k : ℝ)^n * far := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact_mod_cast hfarCard

/-- The same estimate for arbitrary nonnegative finite event weights.
The supplied capability is only a pointwise forced-edge bound, so it is
available for independent fixed-cardinality blocks without pooling quotas. -/
theorem sum_competingCoverWeights_le_near_far
    {k n a : ℕ} (hk : 3 ≤ k) (D : SupercriticalDivision k (Fin n))
    (hD : D.IsFull) (hpart : ∀ i, a ≤ (D.parts i).card)
    (hscale : n ≤ 2 * (k - 1) * a) {c w : ℝ} (hc : 0 ≤ c) (hw : 0 ≤ w)
    (f : SupercriticalDivision k (Fin n) → ℝ)
    (hf : ∀ E ∈ competingFullSupercriticalDivisions D,
      f E ≤ w * Real.exp (-(c * (forcedCrossEdgesBySecondCover D E).card))) :
    (∑ E ∈ competingFullSupercriticalDivisions D, f E) ≤ w *
      ((∑ t ∈ Finset.Icc 1 n,
        (((k - 1).factorial * n.choose t * (k - 1)^t : ℕ) : ℝ) *
          Real.exp (-(c / (4 * (k - 1 : ℕ)) * t * n))) +
      (k : ℝ)^n * Real.exp (-(c / (16 * (k - 1 : ℕ)^8) * (n:ℝ)^2))) := by
  calc
    _ ≤ ∑ E ∈ competingFullSupercriticalDivisions D,
        w * Real.exp (-(c * (forcedCrossEdgesBySecondCover D E).card)) :=
      Finset.sum_le_sum hf
    _ = w * ∑ E ∈ competingFullSupercriticalDivisions D,
        Real.exp (-(c * (forcedCrossEdgesBySecondCover D E).card)) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_competingCover_exp_forced_le_near_far hk D hD hpart hscale hc) hw

end InducedStars
