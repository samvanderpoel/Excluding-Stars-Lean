import InducedStars.Structure.Subcritical.DistinguishedDenominatorShift
import InducedStars.Structure.Subcritical.DistinguishedFeasibleGeometry

/-!
# Full-slice shifts for feasible distinguished keys

Paper: the sparse-side lower-tail denominator in `lemma:sub-combined`. An actual positive wide level supplies its mean density, while
the proved feasible-key geometry supplies its part sizes. Compatibility
alone is never used as a balance assumption.
-/

noncomputable section
open Filter Finset Set Topology
open scoped BigOperators Classical
namespace InducedStars

theorem retainedKeyPartitionFunction_some_le {k n m b : ℕ}
    (D : SubcriticalDivision k (Fin n)) (delta : ℝ) :
    retainedKeyPartitionFunction (some D) m delta (b : ℤ) ≤
      retainedPartitionFunction D 0 (Fintype.card (Fin n)) m delta (b : ℤ) := by
  unfold retainedKeyPartitionFunction retainedPartitionFunction
  apply Finset.sum_le_sum_of_injOn (retainedKeySomeVector D)
  · intro v hv w hw h
    funext e
    apply Fin.ext
    exact congrArg (fun u ↦ u.count e) h
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact retainedKeySomeVector_mem_level D hw
  · intro v hv
    exact (retainedKeySomeVector_multiplicity D v).symm.le
  · intro v hv hn
    exact Nat.zero_le _

theorem completeCore_activeCapacity_lower {k n : ℕ} (hk : 3 ≤ k)
    (D : SubcriticalDivision k (Fin n))
    (hcore : ∀ i, D.core i = RegularBlockCore.complete k hk)
    {a : ℝ} (ha : 0 ≤ a)
    (hpart : ∀ j : D.PartIndex, a * n ≤ ((D.part j).card : ℝ)) :
    a^2 * (n : ℝ)^2 ≤ retainedActiveTotalCapacity D 0 (Fintype.card (Fin n)) := by
  let i : Fin D.componentCount := ⟨0, D.componentCount_pos⟩
  have ho : 2 ≤ (D.core i).order := by rw [hcore i, RegularBlockCore.complete_order]; omega
  let u : Fin (D.core i).order := ⟨0, by omega⟩
  let v : Fin (D.core i).order := ⟨1, by omega⟩
  have hgraph : ∀ x y, (D.core i).graph.Adj x y ↔ x ≠ y := by
    rw [hcore i]
    intro x y
    rfl
  let e : RetainedActivePair D 0 (Fintype.card (Fin n)) := {
    component := i
    component_retained := by rw [D.retainedComponentIndices_all]; exact Finset.mem_univ _
    left := u
    right := v
    left_lt_right := by change (0 : ℕ) < 1; omega
    active := (hgraph u v).mpr (by intro h; have := congrArg Fin.val h; change 0 = 1 at this; omega) }
  have hm := mul_le_mul (hpart e.leftPart) (hpart e.rightPart)
    (mul_nonneg ha (by positivity)) (by positivity)
  have hc : (retainedActiveCapacity D 0 (Fintype.card (Fin n)) e : ℝ) ≤
      retainedActiveTotalCapacity D 0 (Fintype.card (Fin n)) := by
    exact_mod_cast Finset.single_le_sum (fun e (_ : e ∈ Finset.univ) ↦
      Nat.zero_le (retainedActiveCapacity D 0 (Fintype.card (Fin n)) e)) (Finset.mem_univ e)
  rw [retainedActiveCapacity, Nat.cast_mul] at hc
  nlinarith

theorem retainedWideVector_mean_bounds {k n m b : ℕ}
    {D : SubcriticalDivision k (Fin n)} {delta : ℝ}
    (v : RetainedEdgeCountVector D 0 (Fintype.card (Fin n)))
    (hv : v ∈ retainedEdgeCountLevel D 0 (Fintype.card (Fin n)) m delta (b : ℤ)) :
    (pK k - 2*delta) * retainedActiveTotalCapacity D 0 (Fintype.card (Fin n)) ≤
        (retainedEdgeCountTotal v : ℝ) ∧
      (retainedEdgeCountTotal v : ℝ) ≤
        (pK k + 2*delta) * retainedActiveTotalCapacity D 0 (Fintype.card (Fin n)) := by
  rw [retainedActiveTotalCapacity, retainedEdgeCountTotal, Nat.cast_sum, Nat.cast_sum,
    Finset.mul_sum, Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro e he
    exact (le_div_iff₀ (by exact_mod_cast retainedActiveCapacity_pos D 0 _ e)).mp
      ((mem_retainedEdgeCountLevel.mp hv).2 e).1
  · apply Finset.sum_le_sum
    intro e he
    exact (div_le_iff₀ (by exact_mod_cast retainedActiveCapacity_pos D 0 _ e)).mp
      ((mem_retainedEdgeCountLevel.mp hv).2 e).2

/-- Finite scalar and geometric endpoint for any actual complete-core key. -/
theorem completeKey_denominator_shift {k n m b q : ℕ} (hk : 3 ≤ k)
    (D : SubcriticalDivision k (Fin n))
    (hcore : ∀ i, D.core i = RegularBlockCore.complete k hk)
    {a delta Qmax : ℝ} (ha : 0 ≤ a) (hdBand : delta ≤ subcriticalReferenceShiftBand k / 2)
    (hpart : ∀ j : D.PartIndex, a*n ≤ ((D.part j).card : ℝ))
    (hroom : Qmax ≤ subcriticalReferenceShiftBand k * a^2 * n)
    (hq : (q : ℝ) ≤ Qmax*n) :
    (retainedKeyPartitionFunction (some D) m delta (b : ℤ) : ℝ) *
        inducedStarFreeGraphCountWithEdges k
          (SubcriticalRetainedKey.remainder (some D)).card (b+q) ≤
      (inducedStarFreeGraphCountWithEdges k n m : ℝ) *
        Real.exp (DenseGraph.binomialCompactBandShiftConstant
          (subcriticalReferenceShiftBand k) * q) := by
  by_cases hZ : retainedKeyPartitionFunction (some D) m delta (b : ℤ) = 0
  · simp only [hZ, Nat.cast_zero, zero_mul]
    positivity
  have hne : (retainedKeyEdgeCountLevel (some D) m delta (b : ℤ)).Nonempty := by
    by_contra h
    exact hZ (by simp only [retainedKeyPartitionFunction, Finset.not_nonempty_iff_eq_empty.mp h,
      Finset.sum_empty])
  obtain ⟨w, hw⟩ := hne
  let v := retainedKeySomeVector D w
  have hv := retainedKeySomeVector_mem_level D hw
  let M := retainedEdgeCountTotal v
  let A := retainedActiveTotalCapacity D 0 (Fintype.card (Fin n))
  have hid : retainedCliqueCapacity D 0 (Fintype.card (Fin n)) + M + b = m := by
    have h := (mem_retainedEdgeCountLevel.mp hv).1
    change (retainedCliqueCapacity D 0 (Fintype.card (Fin n)) : ℤ) + (M : ℤ) + b = m at h
    exact_mod_cast h
  obtain ⟨hlo, hhi⟩ := retainedWideVector_mean_bounds v hv
  obtain ⟨hlambda, hlambdaHalf, hlp, hlq⟩ := subcriticalReferenceShiftBand_bounds hk
  have hlp4 : 4 * subcriticalReferenceShiftBand k ≤ pK k := by
    unfold subcriticalReferenceShiftBand
    linarith [min_le_left (pK k) (1-pK k)]
  have hA : (0 : ℝ) ≤ A := by positivity
  have hlA := mul_nonneg hlambda.le hA
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hAlow := completeCore_activeCapacity_lower hk D hcore ha hpart
  have hqA : (q : ℝ) ≤ subcriticalReferenceShiftBand k * A := by
    have h₁ := mul_le_mul_of_nonneg_right hroom (show (0 : ℝ) ≤ n by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hAlow hlambda.le
    dsimp [A]
    nlinarith
  have hdA := mul_le_mul_of_nonneg_right hdBand hA
  have hpA := mul_le_mul_of_nonneg_right hlp4 hA
  have hpcA := mul_le_mul_of_nonneg_right hlq hA
  change (pK k - 2*delta) * A ≤ (M : ℝ) at hlo
  change (M : ℝ) ≤ (pK k + 2*delta) * A at hhi
  have hM : M ≤ A := by exact_mod_cast (show (M : ℝ) ≤ A by nlinarith)
  have hqM : q ≤ M := by exact_mod_cast (show (q : ℝ) ≤ M by nlinarith)
  have htargetLo : subcriticalReferenceShiftBand k * A ≤ ((M-q : ℕ) : ℝ) := by
    rw [Nat.cast_sub hqM]
    nlinarith
  have htargetHi : ((M-q : ℕ) : ℝ) ≤ (1-subcriticalReferenceShiftBand k) * A := by
    rw [Nat.cast_sub hqM]
    nlinarith
  have hbound := retainedPartitionFunction_mul_remainder_le_shifted_total hk D 0
    (Fintype.card (Fin n)) delta hid hM hqM hlambda hlambdaHalf htargetLo htargetHi
  have hrem : SubcriticalRetainedKey.remainder (some D) =
      D.nonretainedVertices 0 (Fintype.card (Fin n)) := by
    simp only [SubcriticalRetainedKey.remainder, SubcriticalRetainedKey.support,
      Option.elim_some, SubcriticalDivision.nonretainedVertices, D.retainedVertices_all]
  rw [hrem]
  apply le_trans _ hbound
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast retainedKeyPartitionFunction_some_le (m := m) (b := b) D delta)
    (by positivity)

/-- Uniform denominator shift for all feasible keys compatible with the
distinguished one-block optimizer, not only the balanced reference key. -/
theorem eventually_compatibleRetainedKeys_denominator_shift {k R₀ : ℕ} (hk : 3 ≤ k)
    {mu eta delta Qmax : ℝ} (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (heta : 0 ≤ eta) (hd : 0 < delta) (hsize : eta+delta ≤ mu)
    (horder : k-1 ≤ R₀) (hdmu : delta ≤ mu/2)
    (hsmall : delta ≤ (1-pK k) * (mu / (4*(k-1 : ℕ)))^2 / 10)
    (hdBand : delta ≤ subcriticalReferenceShiftBand k / 2)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m (gammaK k * mu^2)) :
    ∀ᶠ n : ℕ in atTop, ∀ K : SubcriticalRetainedKey k (Fin n),
      K ∈ compatibleRetainedKeys k n (oneBlockSequence k hk mu hmu hmu1) eta delta R₀ →
      ∀ b q : ℕ, (q : ℝ) ≤ Qmax*n →
        (retainedKeyPartitionFunction K (m n) delta (b : ℤ) : ℝ) *
          inducedStarFreeGraphCountWithEdges k K.remainder.card (b+q) ≤
        (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) *
          Real.exp (DenseGraph.binomialCompactBandShiftConstant
            (subcriticalReferenceShiftBand k) * q) := by
  let a := mu / (4*(k-1 : ℕ))
  have ha : 0 < a := by
    have hr : 0 < k-1 := by omega
    dsimp [a]
    positivity
  have hcoef : 0 < subcriticalReferenceShiftBand k * a^2 :=
    mul_pos (subcriticalReferenceShiftBand_bounds hk).1 (sq_pos_of_pos ha)
  have hroom : ∀ᶠ n : ℕ in atTop, Qmax ≤ subcriticalReferenceShiftBand k * a^2 * n := by
    filter_upwards [(tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (Qmax / (subcriticalReferenceShiftBand k * a^2)))] with n hn
    exact (div_le_iff₀ hcoef).mp hn |>.trans_eq (by ring)
  filter_upwards [eventually_compatibleRetainedKeys_part_lower hk hmu hmu1 heta hd hsize
    horder hdmu hsmall m hm, hroom] with n hgeom hroom
  intro K hK b q hq
  by_cases hZ : retainedKeyPartitionFunction K (m n) delta (b : ℤ) = 0
  · simp only [hZ, Nat.cast_zero, zero_mul]
    positivity
  obtain ⟨D, rfl, hcount, hcore, hpart⟩ := hgeom K hK b (Nat.pos_of_ne_zero hZ)
  exact completeKey_denominator_shift hk D hcore ha.le hdBand (fun j ↦ (hpart j).2) hroom hq

end InducedStars
