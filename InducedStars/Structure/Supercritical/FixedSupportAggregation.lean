import InducedStars.Structure.Supercritical.FixedDefectAggregation

/-!
# Aggregation at fixed support-incident defect

This file completes the second finite regrouping in the supercritical
fixed-defect branch.  Combined defect patterns with the same support-incident
part are first grouped by their sparse-induced edge count, and the resulting
binomial sum is exactly the shifted profile aggregate.
-/

noncomputable section

-- The nested support/sparse/profile regrouping is expensive to elaborate.
set_option maxHeartbeats 800000

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance fixedSupportAggregationGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) := Classical.decEq _

/-! ## The finite support fibers -/

/-- Combined patterns whose support-incident part is exactly `T₀`. -/
noncomputable def supercriticalCombinedSupportFiber
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) (T₀ : SimpleGraph (Fin n)) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (supercriticalCombinedDefectPatternFinset
    k hk gamma hgamma m n tau hn D).filter fun T ↦
      supercriticalSupportIncidentGraph D T = T₀

@[simp] theorem mem_supercriticalCombinedSupportFiber
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T₀ T : SimpleGraph (Fin n)} :
    T ∈ supercriticalCombinedSupportFiber
        (hk := hk) (gamma := gamma) (hgamma := hgamma)
          (m := m) (tau := tau) (hn := hn) D T₀ ↔
      T ∈ supercriticalCombinedDefectPatternFinset
          k hk gamma hgamma m n tau hn D ∧
        supercriticalSupportIncidentGraph D T = T₀ := by
  classical
  simp [supercriticalCombinedSupportFiber]

/-- The real-valued fixed-defect contribution over one support fiber. -/
noncomputable def supercriticalFixedSupportTotal
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) (T₀ : SimpleGraph (Fin n)) : ℝ :=
  ∑ T ∈ supercriticalCombinedSupportFiber
      (hk := hk) (gamma := gamma) (hgamma := hgamma)
        (m := m) (tau := tau) (hn := hn) D T₀,
    ((supercriticalFixedDefectGraphFinset
      k hk gamma hgamma alpha m n tau hn D T).card : ℝ)

/-! ## Exact sparse-index regrouping -/

/-- At a fixed support graph, a pointwise profile-mass estimate sums to the
single shifted aggregate based at the literal signed support shift. -/
theorem supercriticalFixedSupportTotal_le_shiftedAggregate_mul_exp
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha rho delta c : ℝ} {m n : ℕ} {tau : ℝ}
    {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) (T₀ : SimpleGraph (Fin n))
    (hpointwise : ∀ T ∈ supercriticalCombinedSupportFiber
        (hk := hk) (gamma := gamma) (hgamma := hgamma)
          (m := m) (tau := tau) (hn := hn) D T₀,
      ((supercriticalFixedDefectGraphFinset
        k hk gamma hgamma alpha m n tau hn D T).card : ℝ) ≤
        (supercriticalProfileMassAtShift D m rho delta
          (supercriticalDefectShift T D) : ℝ) * Real.exp c) :
    supercriticalFixedSupportTotal hk hgamma alpha m n tau hn D T₀ ≤
      (supercriticalShiftedProfileAggregate D m rho delta
        (supercriticalSupportDefectShift D T₀) : ℝ) * Real.exp c := by
  classical
  let S := supercriticalCombinedSupportFiber
    (hk := hk) (gamma := gamma) (hgamma := hgamma)
      (m := m) (tau := tau) (hn := hn) D T₀
  let q := supercriticalSparsePotentialCapacity D
  let idx := supercriticalSparsePatternIndex D
  let w : SimpleGraph (Fin n) → ℝ := fun T ↦
    ((supercriticalFixedDefectGraphFinset
      k hk gamma hgamma alpha m n tau hn D T).card : ℝ)
  let mass : ℤ → ℝ := fun u ↦
    (supercriticalProfileMassAtShift D m rho delta u : ℝ)
  have hregroup :
      ∑ T ∈ S, w T =
        ∑ t : Fin (q + 1), ∑ T ∈ S with idx T = t, w T := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (by simp) w
  have hfiber (t : Fin (q + 1)) :
      ∑ T ∈ S with idx T = t, w T ≤
        (Nat.choose q t : ℝ) *
          (mass (supercriticalSupportDefectShift D T₀ + (t : ℤ)) *
            Real.exp c) := by
    calc
      ∑ T ∈ S with idx T = t, w T ≤
          ∑ T ∈ S with idx T = t,
            mass (supercriticalSupportDefectShift D T₀ + (t : ℤ)) *
              Real.exp c := by
        apply Finset.sum_le_sum
        intro T hT
        have hTS : T ∈ S := (Finset.mem_filter.mp hT).1
        have hidx : idx T = t := (Finset.mem_filter.mp hT).2
        have hsupp : supercriticalSupportIncidentGraph D T = T₀ :=
          (mem_supercriticalCombinedSupportFiber.mp hTS).2
        have hval := congrArg Fin.val hidx
        have hshift := supercriticalDefectShift_eq_support_add_sparse D T
        have hshift' : supercriticalDefectShift T D =
            supercriticalSupportDefectShift D T₀ + (t : ℤ) := by
          rw [hshift, hsupp]
          congr 1
          exact_mod_cast hval
        have hp := hpointwise T hTS
        rw [hshift'] at hp
        exact hp
      _ = (((S.filter fun T ↦ idx T = t).card : ℕ) : ℝ) *
          (mass (supercriticalSupportDefectShift D T₀ + (t : ℤ)) *
            Real.exp c) := by simp
      _ ≤ (Nat.choose q t : ℝ) *
          (mass (supercriticalSupportDefectShift D T₀ + (t : ℤ)) *
            Real.exp c) := by
        apply mul_le_mul_of_nonneg_right
        · have hfiberEq : (S.filter fun T ↦ idx T = t) =
              supercriticalSupportSparseIndexFiber D
                (supercriticalCombinedDefectPatternFinset
                  k hk gamma hgamma m n tau hn D) T₀ t := by
            ext T
            constructor
            · intro hT
              have hfilter := Finset.mem_filter.mp hT
              have hsupp := mem_supercriticalCombinedSupportFiber.mp hfilter.1
              exact (mem_supercriticalSupportSparseIndexFiber D
                (supercriticalCombinedDefectPatternFinset
                  k hk gamma hgamma m n tau hn D) T₀ t T).mpr
                    ⟨hsupp.1, hsupp.2, hfilter.2⟩
            · intro hT
              have hfiber :=
                (mem_supercriticalSupportSparseIndexFiber D
                  (supercriticalCombinedDefectPatternFinset
                    k hk gamma hgamma m n tau hn D) T₀ t T).mp hT
              exact Finset.mem_filter.mpr
                ⟨mem_supercriticalCombinedSupportFiber.mpr
                  ⟨hfiber.1, hfiber.2.1⟩, hfiber.2.2⟩
          rw [hfiberEq]
          exact_mod_cast (card_filter_support_sparseIndex_le_choose
            D (supercriticalCombinedDefectPatternFinset
              k hk gamma hgamma m n tau hn D) T₀ t)
        · positivity
  calc
    supercriticalFixedSupportTotal hk hgamma alpha m n tau hn D T₀ =
        ∑ T ∈ S, w T := rfl
    _ = ∑ t : Fin (q + 1), ∑ T ∈ S with idx T = t, w T := hregroup
    _ ≤ ∑ t : Fin (q + 1),
        (Nat.choose q t : ℝ) *
          (mass (supercriticalSupportDefectShift D T₀ + (t : ℤ)) *
            Real.exp c) := Finset.sum_le_sum fun t _ht ↦ hfiber t
    _ = (∑ t ∈ Finset.range (q + 1),
        (mass (supercriticalSupportDefectShift D T₀ + (t : ℤ)) : ℝ) *
          Nat.choose q t) * Real.exp c := by
      rw [← Fin.sum_univ_eq_sum_range]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = (supercriticalShiftedProfileAggregate D m rho delta
          (supercriticalSupportDefectShift D T₀) : ℝ) * Real.exp c := by
      rw [supercriticalShiftedProfileAggregate_eq_sum_profileMass]
      rw [Nat.cast_sum]
      push_cast
      rfl

end InducedStars
