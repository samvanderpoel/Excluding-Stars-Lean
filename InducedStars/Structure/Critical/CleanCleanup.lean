import InducedStars.Structure.Critical.AggregationFamilies
import InducedStars.Structure.Critical.AggregationParameters
import InducedStars.Structure.Critical.BinomialComparison
import InducedStars.Structure.Critical.DivisionCounting

/-!
# Critical clean sparse-set cleanup

This file sums the uniform critical binomial-slice estimate over every
ordered canonical division whose sparse set lies above the logarithmic
cutoff.  Nonempty clean fibers inherit the small-sparse bound from the
close-structure theorem; empty fibers contribute zero.  Division counting
then turns the balanced reference-fiber factor into the exact global
co-multipartite count, leaving precisely the Gaussian tail selected in
`CriticalAggregationParameters`.
-/

noncomputable section

open Filter Finset Set Topology
open scoped BigOperators

namespace InducedStars

noncomputable local instance criticalCleanCleanupGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) := Classical.decEq _

/-! ## Uniform slice input -/

/-- The clean critical slice estimate at one vertex size, with the constants
from a fixed aggregation package. -/
def CriticalCleanSliceBoundAt
    (k : ℕ) (P : CriticalAggregationParameters k) (n : ℕ) : Prop :=
  ∀ s ≤ n,
    (s : ℝ) ≤ criticalCombinedSliceDelta k * (n : ℝ) →
    (Nat.choose (criticalMaximumCombinedCapacity k n s)
      (criticalMaximumCombinedSelectedCount k n s) : ℝ) ≤
      (criticalReferenceFiberCard k n : ℝ) *
        Real.exp (-P.cCrit * (s : ℝ) ^ 2 +
          P.cleanErrorConstant * (s : ℝ) +
          P.cleanErrorConstant * Real.log ((n + 1 : ℕ) : ℝ))

/-- The proved four-reserve binomial estimate supplies the weaker single-gap
Gaussian exponent stored in every critical aggregation package. -/
theorem eventually_criticalCleanSliceBoundAt
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∀ᶠ n : ℕ in atTop, CriticalCleanSliceBoundAt k P n := by
  filter_upwards [
    eventually_criticalCleanCombinedSlice_le_referenceFiber_with_errors k hk]
      with n hslice
  intro s _hs hsmall
  apply (hslice s hsmall).trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  rw [P.cCrit_eq, P.cleanErrorConstant_eq]
  unfold criticalCombinedSliceExponent
  have hnonneg := mul_nonneg (criticalSparsePenaltyConstant_pos hk).le
    (sq_nonneg (s : ℝ))
  nlinarith

/-! ## Active clean divisions -/

/-- Clean critical divisions above the logarithmic cutoff whose canonical
fiber is nonempty.  Restricting to this finite set allows the close-structure
theorem to be invoked without imposing a false condition on empty fibers. -/
noncomputable def criticalCleanLargeSparseActiveDivisions
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    (n : ℕ) (hn : k - 1 ≤ n) :
    Finset (SupercriticalDivision k (Fin n)) := by
  classical
  exact (allSupercriticalDivisions k n).filter fun D ↦
    criticalLogarithmicSparseCutoff P.sparseCutoffConstant n ≤
        D.sparse.card ∧
      (criticalCleanDivisionGraphFinset k hk n P.tau hn D).Nonempty

@[simp] theorem mem_criticalCleanLargeSparseActiveDivisions
    {k n : ℕ} {hk : 3 ≤ k} {P : CriticalAggregationParameters k}
    {hn : k - 1 ≤ n} {D : SupercriticalDivision k (Fin n)} :
    D ∈ criticalCleanLargeSparseActiveDivisions k hk P n hn ↔
      criticalLogarithmicSparseCutoff P.sparseCutoffConstant n ≤
          D.sparse.card ∧
        (criticalCleanDivisionGraphFinset k hk n P.tau hn D).Nonempty := by
  classical
  simp [criticalCleanLargeSparseActiveDivisions]

/-! ## Finite Gaussian majorant -/

set_option maxHeartbeats 100000 in
-- The dependent finite regrouping expands several nested division-family sums.
/-- Conditional only on the uniform clean-slice estimate, the complete clean
large-sparse sum is bounded by the exact co-multipartite count times the
Gaussian cutoff sum. -/
theorem
    eventually_criticalCleanLargeSparseTotal_le_gaussian_of_sliceBound
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    (hslice : ∀ᶠ n : ℕ in atTop, CriticalCleanSliceBoundAt k P n) :
    ∀ᶠ n : ℕ in atTop,
      (criticalCleanLargeSparseTotal k hk n P.tau
          P.sparseCutoffConstant : ℝ) ≤
        ((2 * (k - 1).factorial : ℕ) : ℝ) *
          (coMultipartiteGraphCountWithEdges (k - 1) n
            (criticalEdgeCount k n) : ℝ) *
          (∑ s ∈ Finset.Icc
              (criticalLogarithmicSparseCutoff
                P.sparseCutoffConstant n) n,
            DenseGraph.sparseGaussianWeight (k - 1) P.cCrit
              P.cleanErrorConstant n s) := by
  classical
  have hdivisionCount :=
    eventually_card_supercriticalDivisionsWithSparseCard_mul_reference_le
      k hk
  let nClose := supercriticalCloseStructureVertexThreshold k hk (gammaK k)
    (gammaK_mem_supercritical_Ico k hk) P.alpha P.alpha_mem_Ioo
      P.delta P.delta_pos P.delta_lt_alpha P.rho_three_lower
        P.rho_three_upper P.epsilon P.epsilon_pos
  filter_upwards [hslice, hdivisionCount, eventually_ge_atTop nClose]
      with n hsliceN hdivisionCountN hnClose
  let hn : k - 1 ≤ n :=
    (supercriticalCloseStructureVertexThreshold_large k hk (gammaK k)
      (gammaK_mem_supercritical_Ico k hk) P.alpha P.alpha_mem_Ioo
        P.delta P.delta_pos P.delta_lt_alpha P.rho_three_lower
          P.rho_three_upper P.epsilon P.epsilon_pos).trans hnClose
  let active := criticalCleanLargeSparseActiveDivisions k hk P n hn
  let weight : ℕ → ℝ := fun s ↦
    (criticalReferenceFiberCard k n : ℝ) *
      Real.exp (-P.cCrit * (s : ℝ) ^ 2 +
        P.cleanErrorConstant * (s : ℝ) +
        P.cleanErrorConstant * Real.log ((n + 1 : ℕ) : ℝ))
  have hactiveBound (D : SupercriticalDivision k (Fin n))
      (hD : D ∈ active) :
      ((criticalCleanDivisionGraphFinset k hk n P.tau hn D).card : ℝ) ≤
        weight D.sparse.card := by
    have hmem : D ∈ criticalCleanLargeSparseActiveDivisions k hk P n hn := by
      simpa only [active] using hD
    obtain ⟨_hcut, hnonempty⟩ :=
      mem_criticalCleanLargeSparseActiveDivisions.mp hmem
    obtain ⟨G, hG⟩ := hnonempty
    have hclose := (mem_supercriticalCleanDivisionGraphFinset.mp hG).1
    have hfamily : G ∈
        inducedFreeGraphFinsetWithEdges (inducedStar k) n
            (criticalEdgeCount k n) \
          supercriticalFarGraphFinset k hk (gammaK k)
            (gammaK_mem_supercritical_Ico k hk)
              (criticalEdgeCount k n) n P.tau := by
      rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
      exact hclose
    obtain ⟨R⟩ := superCloseStructureK1k k hk (gammaK k)
      (gammaK_mem_supercritical_Ico k hk)
        P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
          P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
            (criticalEdgeCount k n) hnClose G
              (by simpa [P.tau_eq] using hfamily)
    have hcanonical :=
      (mem_supercriticalCleanDivisionGraphFinset.mp hG).2.1
    have hsparse : (D.sparse.card : ℝ) ≤ P.delta * (n : ℝ) / 2 := by
      simpa only [hcanonical] using R.sparse_card_le
    have hsle : D.sparse.card ≤ n := by
      simpa using Finset.card_le_univ D.sparse
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hsmall : (D.sparse.card : ℝ) ≤
        criticalCombinedSliceDelta k * (n : ℝ) := by
      calc
        (D.sparse.card : ℝ) ≤ P.delta * (n : ℝ) / 2 := hsparse
        _ ≤ P.delta * (n : ℝ) := by
          have := mul_nonneg P.delta_pos.le hn0
          linarith
        _ ≤ criticalCombinedSliceDelta k * (n : ℝ) :=
          mul_le_mul_of_nonneg_right P.critical_slice_delta.le hn0
    have hcard :=
      card_criticalCleanDivisionGraphFinset_le_choose_maximum_selected
        (show (criticalCleanDivisionGraphFinset k hk n P.tau hn D).Nonempty
          from ⟨G, hG⟩)
    calc
      ((criticalCleanDivisionGraphFinset k hk n P.tau hn D).card : ℝ) ≤
          (Nat.choose
            (criticalMaximumCombinedCapacity k n D.sparse.card)
            (criticalMaximumCombinedSelectedCount k n D.sparse.card) : ℝ) := by
        exact_mod_cast hcard
      _ ≤ weight D.sparse.card := by
        simpa [weight] using hsliceN D.sparse.card hsle hsmall
  have hfirst :
      (criticalCleanLargeSparseTotal k hk n P.tau
          P.sparseCutoffConstant : ℝ) ≤
        ∑ D ∈ active, weight D.sparse.card := by
    rw [criticalCleanLargeSparseTotal, dif_pos hn, Nat.cast_sum]
    calc
      ∑ D ∈ allSupercriticalDivisions k n,
          ((if criticalLogarithmicSparseCutoff P.sparseCutoffConstant n ≤
              D.sparse.card then
            (criticalCleanDivisionGraphFinset k hk n P.tau hn D).card
          else 0 : ℕ) : ℝ) ≤
          ∑ D ∈ allSupercriticalDivisions k n,
            if D ∈ active then weight D.sparse.card else 0 := by
        apply Finset.sum_le_sum
        intro D hDall
        by_cases hD : D ∈ active
        · rw [if_pos hD]
          have hcut :=
            (mem_criticalCleanLargeSparseActiveDivisions.mp
              (by simpa only [active] using hD)).1
          rw [if_pos hcut]
          exact hactiveBound D hD
        · rw [if_neg hD]
          by_cases hcut :
              criticalLogarithmicSparseCutoff
                P.sparseCutoffConstant n ≤ D.sparse.card
          · rw [if_pos hcut]
            have hempty :
                criticalCleanDivisionGraphFinset k hk n P.tau hn D = ∅ := by
              apply Finset.not_nonempty_iff_eq_empty.mp
              intro hne
              apply hD
              rw [show active =
                  criticalCleanLargeSparseActiveDivisions k hk P n hn by rfl,
                mem_criticalCleanLargeSparseActiveDivisions]
              exact ⟨hcut, hne⟩
            simp [hempty]
          · simp [hcut]
      _ = ∑ D ∈ active, weight D.sparse.card := by
        rw [← Finset.sum_filter]
        simp [active, criticalCleanLargeSparseActiveDivisions]
  have hmaps : ∀ D ∈ active,
      D.sparse.card ∈ Finset.Icc
        (criticalLogarithmicSparseCutoff P.sparseCutoffConstant n) n := by
    intro D hD
    have hmem := mem_criticalCleanLargeSparseActiveDivisions.mp
      (by simpa only [active] using hD)
    exact Finset.mem_Icc.mpr ⟨hmem.1, by
      simpa using Finset.card_le_univ D.sparse⟩
  have hregroup :
      (∑ D ∈ active, weight D.sparse.card) =
        ∑ s ∈ Finset.Icc
            (criticalLogarithmicSparseCutoff
              P.sparseCutoffConstant n) n,
          ∑ D ∈ active with D.sparse.card = s, weight s :=
    (Finset.sum_fiberwise_of_maps_to' hmaps weight).symm
  rw [hregroup] at hfirst
  let good : ℝ :=
    coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n)
  let gaussian : ℕ → ℝ := fun s ↦
    DenseGraph.sparseGaussianWeight (k - 1) P.cCrit
      P.cleanErrorConstant n s
  have hsBound (s : ℕ)
      (hs : s ∈ Finset.Icc
        (criticalLogarithmicSparseCutoff P.sparseCutoffConstant n) n) :
      (∑ D ∈ active with D.sparse.card = s, weight s) ≤
        ((2 * (k - 1).factorial : ℕ) : ℝ) * good * gaussian s := by
    let fiber := active.filter fun D ↦ D.sparse.card = s
    have hfiberSubset : fiber ⊆
        supercriticalDivisionsWithSparseCard k n s := by
      intro D hD
      exact mem_supercriticalDivisionsWithSparseCard.mpr
        (Finset.mem_filter.mp hD).2
    have hcard : fiber.card ≤
        (supercriticalDivisionsWithSparseCard k n s).card :=
      Finset.card_le_card hfiberSubset
    have hcardReal : (fiber.card : ℝ) ≤
        (supercriticalDivisionsWithSparseCard k n s).card := by
      exact_mod_cast hcard
    have hlocalReference :
        (fiber.card : ℝ) * (criticalReferenceFiberCard k n : ℝ) ≤
          ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
            (2 * (k - 1).factorial : ℕ) * (Nat.choose n s : ℝ) * good := by
      calc
        (fiber.card : ℝ) * (criticalReferenceFiberCard k n : ℝ) ≤
            ((supercriticalDivisionsWithSparseCard k n s).card : ℝ) *
              (criticalReferenceFiberCard k n : ℝ) :=
          mul_le_mul_of_nonneg_right hcardReal (by positivity)
        _ ≤ ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
            (2 * (k - 1).factorial : ℕ) * (Nat.choose n s : ℝ) * good := by
          simpa [good] using hdivisionCountN s (Finset.mem_Icc.mp hs).2
    have hsumEq :
        (∑ D ∈ active with D.sparse.card = s, weight s) =
          (fiber.card : ℝ) * weight s := by
      dsimp [fiber]
      simp
    rw [hsumEq]
    calc
      (fiber.card : ℝ) * weight s =
          ((fiber.card : ℝ) * (criticalReferenceFiberCard k n : ℝ)) *
            Real.exp (-P.cCrit * (s : ℝ) ^ 2 +
              P.cleanErrorConstant * (s : ℝ) +
              P.cleanErrorConstant * Real.log ((n + 1 : ℕ) : ℝ)) := by
        dsimp [weight]
        ring
      _ ≤ (((n + 1 : ℕ) : ℝ) ^ (k - 1) *
            (2 * (k - 1).factorial : ℕ) * (Nat.choose n s : ℝ) * good) *
              Real.exp (-P.cCrit * (s : ℝ) ^ 2 +
                P.cleanErrorConstant * (s : ℝ) +
                P.cleanErrorConstant * Real.log ((n + 1 : ℕ) : ℝ)) := by
        gcongr
      _ = ((2 * (k - 1).factorial : ℕ) : ℝ) * good * gaussian s := by
        dsimp [gaussian, DenseGraph.sparseGaussianWeight]
        ring
  calc
    (criticalCleanLargeSparseTotal k hk n P.tau
        P.sparseCutoffConstant : ℝ) ≤
      ∑ s ∈ Finset.Icc
          (criticalLogarithmicSparseCutoff P.sparseCutoffConstant n) n,
        ∑ D ∈ active with D.sparse.card = s, weight s := hfirst
    _ ≤ ∑ s ∈ Finset.Icc
        (criticalLogarithmicSparseCutoff P.sparseCutoffConstant n) n,
      ((2 * (k - 1).factorial : ℕ) : ℝ) * good * gaussian s :=
        Finset.sum_le_sum fun s hs ↦ hsBound s hs
    _ = ((2 * (k - 1).factorial : ℕ) : ℝ) * good *
        (∑ s ∈ Finset.Icc
            (criticalLogarithmicSparseCutoff P.sparseCutoffConstant n) n,
          gaussian s) := by
      rw [Finset.mul_sum]
    _ = ((2 * (k - 1).factorial : ℕ) : ℝ) *
          (coMultipartiteGraphCountWithEdges (k - 1) n
            (criticalEdgeCount k n) : ℝ) *
          (∑ s ∈ Finset.Icc
              (criticalLogarithmicSparseCutoff
                P.sparseCutoffConstant n) n,
            DenseGraph.sparseGaussianWeight (k - 1) P.cCrit
              P.cleanErrorConstant n s) := by
      rfl

/-- The unconditional finite Gaussian majorant obtained from the locally
proved second-order critical slice comparison. -/
theorem eventually_criticalCleanLargeSparseTotal_le_gaussian
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∀ᶠ n : ℕ in atTop,
      (criticalCleanLargeSparseTotal k hk n P.tau
          P.sparseCutoffConstant : ℝ) ≤
        ((2 * (k - 1).factorial : ℕ) : ℝ) *
          (coMultipartiteGraphCountWithEdges (k - 1) n
            (criticalEdgeCount k n) : ℝ) *
          (∑ s ∈ Finset.Icc
              (criticalLogarithmicSparseCutoff
                P.sparseCutoffConstant n) n,
            DenseGraph.sparseGaussianWeight (k - 1) P.cCrit
              P.cleanErrorConstant n s) :=
  eventually_criticalCleanLargeSparseTotal_le_gaussian_of_sliceBound
    k hk P (eventually_criticalCleanSliceBoundAt k hk P)

/-! ## Vanishing normalized clean contribution -/

/-- For synchronized parameters, the clean large-sparse total is negligible
relative to the exact critical co-multipartite count. -/
theorem criticalCleanLargeSparseTotal_ratio_tendsto_zero
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    Tendsto
      (fun n : ℕ ↦
        (criticalCleanLargeSparseTotal k hk n P.tau
          P.sparseCutoffConstant : ℝ) /
          (coMultipartiteGraphCountWithEdges (k - 1) n
            (criticalEdgeCount k n) : ℝ))
      atTop (nhds 0) := by
  let tail : ℕ → ℝ := fun n ↦
    ∑ s ∈ Finset.Icc
        (criticalLogarithmicSparseCutoff P.sparseCutoffConstant n) n,
      DenseGraph.sparseGaussianWeight (k - 1) P.cCrit
        P.cleanErrorConstant n s
  let C : ℝ := (2 * (k - 1).factorial : ℕ)
  have hbound := eventually_criticalCleanLargeSparseTotal_le_gaussian k hk P
  have hgood : ∀ᶠ n : ℕ in atTop,
      0 < coMultipartiteGraphCountWithEdges (k - 1) n
        (criticalEdgeCount k n) := by
    filter_upwards [eventually_criticalReferenceFiber_nonempty k hk]
      with n href
    obtain ⟨G, hG⟩ := href
    exact Finset.card_pos.mpr
      ⟨G, criticalReferenceFiber_subset_coMultipartite k hk n hG⟩
  have hupper : ∀ᶠ n : ℕ in atTop,
      (criticalCleanLargeSparseTotal k hk n P.tau
          P.sparseCutoffConstant : ℝ) /
          (coMultipartiteGraphCountWithEdges (k - 1) n
            (criticalEdgeCount k n) : ℝ) ≤ C * tail n := by
    filter_upwards [hbound, hgood] with n hn hgoodN
    have hgoodR : (0 : ℝ) <
        coMultipartiteGraphCountWithEdges (k - 1) n
          (criticalEdgeCount k n) := by exact_mod_cast hgoodN
    apply (div_le_iff₀ hgoodR).2
    calc
      (criticalCleanLargeSparseTotal k hk n P.tau
          P.sparseCutoffConstant : ℝ) ≤
        ((2 * (k - 1).factorial : ℕ) : ℝ) *
          (coMultipartiteGraphCountWithEdges (k - 1) n
            (criticalEdgeCount k n) : ℝ) * tail n := by
        simpa [tail] using hn
      _ = (C * tail n) *
          (coMultipartiteGraphCountWithEdges (k - 1) n
            (criticalEdgeCount k n) : ℝ) := by
        dsimp [C]
        ring
  have htail : Tendsto tail atTop (nhds 0) := by
    simpa [tail, criticalLogarithmicSparseCutoff] using P.sparse_cutoff_tendsto
  have hright : Tendsto (fun n ↦ C * tail n) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul htail
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ by positivity
  · exact hupper
  · exact hright

/-- Clean sparse-set cleanup at the exact critical density.

At the exact floor critical edge count, there are a positive cut radius and
a logarithmic sparse-set cutoff, both depending only on `k`, above which the
sum of clean canonical-division fibers is negligible compared with the exact
co-`(k-1)`-partite count. -/
theorem criticalCleanSparseK1k
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ L : ℝ, 0 < L ∧
      ∃ tau : ℝ, 0 < tau ∧
        Tendsto
          (fun n : ℕ ↦
            (criticalCleanLargeSparseTotal k hk n tau L : ℝ) /
              (coMultipartiteGraphCountWithEdges (k - 1) n
                (criticalEdgeCount k n) : ℝ))
          atTop (nhds 0) := by
  let P : CriticalAggregationParameters k :=
    Classical.choice (exists_criticalAggregationParameters k hk)
  exact ⟨P.sparseCutoffConstant, P.sparseCutoffConstant_pos,
    P.tau, P.tau_pos,
    criticalCleanLargeSparseTotal_ratio_tendsto_zero k hk P⟩

end InducedStars
