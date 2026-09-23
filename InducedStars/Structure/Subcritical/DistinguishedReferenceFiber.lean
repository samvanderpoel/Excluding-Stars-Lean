import InducedStars.Structure.Subcritical.DistinguishedFiniteReference
import InducedStars.Structure.Subcritical.BalancedRetainedFeasibility

/-!
# Feasible exact-edge distinguished reference fibers

The numerical headroom is checked against the finite density and balanced
capacities. No unproved feasibility or prescribed vector is an input.
-/

noncomputable section
open Filter Finset Set Topology
open scoped Classical BigOperators
namespace InducedStars

/-- A total deterministic reference key. Early infeasible support sizes
use the permitted empty key; the theorems below prove eventual feasibility. -/
def subcriticalDistinguishedReferenceKey {k : ℕ} (hk : 3 ≤ k) (n m b : ℕ) :
    SubcriticalRetainedKey k (Fin n) :=
  if h : k - 1 ≤ subcriticalReferenceSupportSize k n m b ∧
      subcriticalReferenceSupportSize k n m b ≤ n then
    balancedRetainedReferenceKey hk h.1 h.2 else none

/-- A genuinely constructed exact vector in the unchanged wide level.
The density error remains explicit before using quadratic headroom. -/
theorem subcriticalReferenceVector_exists {k n m b : ℕ} (hk : 3 ≤ k)
    (hn : 2 ≤ n)
    (hgamma : subcriticalReferenceDensity n m b ∈ Ioo (0 : ℝ) (gammaK k))
    (hrq : k - 1 ≤ subcriticalReferenceSupportSize k n m b)
    (hqn : subcriticalReferenceSupportSize k n m b ≤ n)
    (delta : ℝ) (hd : 0 ≤ delta)
    (hdp : delta ≤ pK k / 2) (hdq : delta ≤ (1 - pK k) / 2)
    (hroom : (4 : ℝ) * k * n ≤ delta * retainedActiveTotalCapacity
      (balancedRetainedDivision hk hrq hqn) 0 n)
    (hpair : ∀ e : RetainedActivePair (balancedRetainedDivision hk hrq hqn) 0 n,
      1 / (retainedActiveCapacity (balancedRetainedDivision hk hrq hqn) 0 n e : ℝ) ≤ delta) :
    ∃ v : RetainedEdgeCountVector (balancedRetainedDivision hk hrq hqn) 0 n,
      v ∈ retainedEdgeCountLevel (balancedRetainedDivision hk hrq hqn) 0 n m delta (b : ℤ) ∧
      (∀ e, |retainedEdgeCountDensity v e - pK k| ≤
        (4 : ℝ) * k * n /
          retainedActiveTotalCapacity (balancedRetainedDivision hk hrq hqn) 0 n +
        1 / (retainedActiveCapacity (balancedRetainedDivision hk hrq hqn) 0 n e : ℝ)) ∧
      0 < retainedKeyPartitionFunction (subcriticalDistinguishedReferenceKey hk n m b)
        m delta (b : ℤ) := by
  let D := balancedRetainedDivision hk hrq hqn
  let A : ℝ := retainedActiveTotalCapacity D 0 n
  let I : ℕ := retainedCliqueCapacity D 0 n
  let z : ℝ := ((m : ℝ) - b - I) / A
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hA : 0 < A := by
    have he : 0 < (4 : ℝ) * k * n := by positivity
    have hh : 0 < delta * A := he.trans_le hroom
    exact (mul_pos_iff.mp hh).elim (fun h ↦ h.2) (fun h ↦ False.elim (not_lt_of_ge hd h.1))
  have hp := pK_pos (by omega : 2 ≤ k)
  have hp1 := pK_lt_one (by omega : 2 ≤ k)
  have herr : |((m : ℝ) - b) - ((I : ℝ) + pK k * A)| ≤ (4 : ℝ) * k * n := by
    simpa only [I, A, D, balancedRetainedDivision_cliqueCapacity,
      balancedRetainedDivision_activeTotalCapacity] using
        subcriticalReference_expectedCapacity_error hk hn hgamma
  have hzerr : |z - pK k| ≤ (4 : ℝ) * k * n / A := by
    rw [show z - pK k = (((m : ℝ) - b) - ((I : ℝ) + pK k * A)) / A by
      dsimp [z]; field_simp; ring]
    rw [abs_div, abs_of_pos hA]
    exact div_le_div_of_nonneg_right herr hA.le
  have hzd : |z - pK k| ≤ delta :=
    hzerr.trans ((div_le_iff₀ hA).2 hroom)
  have hz0 : 0 < z := by have h := abs_le.mp hzd; linarith
  have hz1 : z < 1 := by have h := abs_le.mp hzd; linarith
  have hnum : 0 < (m : ℝ) - b - I := by
    have h := mul_pos hz0 hA
    simpa only [z, div_mul_cancel₀ _ hA.ne'] using h
  have hI0 : (0 : ℝ) ≤ I := by positivity
  have hbm : b ≤ m := by
    have h : (b : ℝ) ≤ m := by linarith
    exact_mod_cast h
  have hIm : I ≤ m - b := by
    have hcast : ((m - b : ℕ) : ℝ) = (m : ℝ) - b := Nat.cast_sub hbm
    exact_mod_cast (show (I : ℝ) ≤ (m - b : ℕ) by rw [hcast]; linarith)
  let M := m - b - I
  have hM : (M : ℝ) = (m : ℝ) - b - I := by
    simp only [M, Nat.cast_sub hIm, Nat.cast_sub hbm]
  have hmean : z * retainedActiveTotalCapacity D 0 n = (M : ℝ) := by
    change z * A = _
    rw [hM]
    exact div_mul_cancel₀ _ hA.ne'
  have hid : (retainedCliqueCapacity D 0 n : ℤ) + M + (b : ℤ) = (m : ℤ) := by
    have hnat : I + M + b = m := by dsimp [M]; omega
    exact_mod_cast hnat
  obtain ⟨v, hv, hbnd, hpos⟩ := retainedPartitionFunction_pos_of_mean_headroom
    D 0 n m M delta (b : ℤ) hz0.le hz1 hmean hid hzd hpair
  refine ⟨v, hv, ?_, ?_⟩
  · intro e
    exact (hbnd e).trans (add_le_add hzerr le_rfl)
  · unfold subcriticalDistinguishedReferenceKey
    rw [dif_pos ⟨hrq, hqn⟩, balancedRetainedReferenceKey,
      retainedKeyPartitionFunction_retainedKey]
    exact hpos

end InducedStars
