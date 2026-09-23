import InducedStars.Structure.Subcritical.RetainedCounts
import InducedStars.Structure.Subcritical.RetainedShift
import DenseGraph.Combinatorics.BinomialLevelShift

/-!
# Integer headroom for signed active edge-count levels

Finite prerequisites for Paper: Lemma `lemma:active-level-comparison-K1k`.
The log-odds definitions use natural units for natural-exponential bounds.
Integer headroom is supplied by an explicit per-coordinate rounding reserve.
The finite comparison uses only these allocations and exact adjacent
binomial ratios, including when the active index set is empty.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The total number of optional retained active coordinates. -/
def retainedActiveTotalCapacity (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) : ℕ :=
  ∑ e : RetainedActivePair D eta R₀, retainedActiveCapacity D eta R₀ e

theorem retainedActiveTotalCapacity_eq_card (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) :
    retainedActiveTotalCapacity D eta R₀ = (retainedActiveEdgeUniverse D eta R₀).card :=
  (retainedActiveEdgeUniverse_card D eta R₀).symm

theorem retainedActiveTotalCapacity_le_choose (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) :
    retainedActiveTotalCapacity D eta R₀ ≤ (Fintype.card V).choose 2 := by
  rw [retainedActiveTotalCapacity_eq_card,
    ← SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  apply Finset.card_le_card
  intro z hz
  induction z using Sym2.inductionOn with
  | _ x y =>
      have ha := ((mk_mem_retainedActiveEdgeUniverse_iff D eta R₀ x y).mp hz).1
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
      intro hxy
      subst y
      exact D.not_activePair_self x ha

theorem retainedActiveCapacity_le_sq (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (e : RetainedActivePair D eta R₀) :
    retainedActiveCapacity D eta R₀ e ≤ (Fintype.card V)^2 := by
  unfold retainedActiveCapacity
  simpa [pow_two] using Nat.mul_le_mul
    (Finset.card_le_univ (D.part e.leftPart)) (Finset.card_le_univ (D.part e.rightPart))

/-- A concrete finite size threshold supplies the reserve needed by the
integer allocator; no rounding assumption is inferred from real headroom. -/
theorem retainedActiveCapacity_rounding_reserve
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) {delta c : ℝ}
    (hd : 0 ≤ delta) (hc : 0 ≤ c)
    (hparts : ∀ a ∈ D.retainedPartIndices eta R₀,
      c * Fintype.card V ≤ ((D.part a).card : ℝ))
    (hlarge : 2 ≤ delta * (c * Fintype.card V)^2)
    (e : RetainedActivePair D eta R₀) :
    2 ≤ delta * retainedActiveCapacity D eta R₀ e := by
  have hmul := mul_le_mul (hparts e.leftPart e.leftPart_mem_retained)
    (hparts e.rightPart e.rightPart_mem_retained) (by positivity)
    (by positivity : (0 : ℝ) ≤ (D.part e.leftPart).card)
  have hm := mul_le_mul_of_nonneg_left hmul hd
  simp only [retainedActiveCapacity, Nat.cast_mul]
  nlinarith

/-- An explicit graph-order threshold for integer headroom. -/
def subcriticalActiveRoundingThreshold (delta c : ℝ) : ℕ :=
  max 2 ⌈2 / (delta * c^2)⌉₊

theorem retainedActiveCapacity_rounding_reserve_of_order_ge
    {n : ℕ} (D : SubcriticalDivision k (Fin n)) (eta : ℝ) (R₀ : ℕ)
    {delta c : ℝ} (hd : 0 < delta) (hc : 0 < c)
    (hn : subcriticalActiveRoundingThreshold delta c ≤ n)
    (hparts : ∀ a ∈ D.retainedPartIndices eta R₀,
      c * n ≤ ((D.part a).card : ℝ))
    (e : RetainedActivePair D eta R₀) :
    2 ≤ delta * retainedActiveCapacity D eta R₀ e := by
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnc : ⌈2 / (delta * c^2)⌉₊ ≤ n := (le_max_right _ _).trans hn
  have hreal : 2 / (delta * c^2) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnc)
  have hcoeff : 0 < delta * c^2 := mul_pos hd (sq_pos_of_pos hc)
  have hnum : 2 ≤ (n : ℝ) * (delta * c^2) := (div_le_iff₀ hcoeff).mp hreal
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnSq : (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  have hsq := mul_le_mul_of_nonneg_right hnSq hcoeff.le
  apply retainedActiveCapacity_rounding_reserve D eta R₀ hd.le hc.le
    (by simpa only [Fintype.card_fin] using hparts) _ e
  simpa only [Fintype.card_fin] using (show 2 ≤ delta * (c * n)^2 by nlinarith)

theorem eventually_retainedActiveCapacity_rounding_reserve
    (k : ℕ) (eta : ℝ) (R₀ : ℕ) {delta c : ℝ} (hd : 0 < delta) (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ D : SubcriticalDivision k (Fin n),
      (∀ a ∈ D.retainedPartIndices eta R₀, c * n ≤ ((D.part a).card : ℝ)) →
      ∀ e, 2 ≤ delta * retainedActiveCapacity D eta R₀ e := by
  filter_upwards [Filter.eventually_ge_atTop (subcriticalActiveRoundingThreshold delta c)] with n hn
  exact fun D hparts e ↦ retainedActiveCapacity_rounding_reserve_of_order_ge
    D eta R₀ hd hc hn hparts e

/-- The binary-log odds used in the paper's entropy formulas. -/
def subcriticalLogOddsBits (k : ℕ) : ℝ := log2 ((1 - pK k) / pK k)

/-- The compatible natural-log coefficient for `Real.exp`. -/
def subcriticalLogOddsNat (k : ℕ) : ℝ := Real.log ((1 - pK k) / pK k)

theorem subcriticalLogOddsNat_eq_log_two_mul_bits (k : ℕ) :
    subcriticalLogOddsNat k = Real.log 2 * subcriticalLogOddsBits k := by
  unfold subcriticalLogOddsNat subcriticalLogOddsBits log2
  field_simp

/-- A uniform coefficient depending only on `k`, not on any coordinate,
division, graph order, or signed level. -/
def subcriticalActiveLevelConstant (k : ℕ) : ℝ :=
  max 3 (DenseGraph.binomialLogOddsConstant (pK k))

theorem subcriticalActiveLevelConstant_pos (k : ℕ) :
    0 < subcriticalActiveLevelConstant k :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

private theorem nat_sq_add_one_le_cube {n : ℕ} (hn : 2 ≤ n) : n^2 + 1 ≤ n^3 := by
  have : n^2 * 2 ≤ n^2 * n := Nat.mul_le_mul_left _ hn
  nlinarith [sq_nonneg (n : ℤ)]

/-- All bounded coordinate vectors, and hence all possible adjustment
vectors, have the paper's polynomial-in-order cardinality overhead. -/
theorem card_retainedEdgeCountVector_le_order_pow
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (hn : 2 ≤ Fintype.card V) :
    Fintype.card (RetainedEdgeCountVector D eta R₀) ≤
      (Fintype.card V) ^ (3 * Fintype.card (RetainedActivePair D eta R₀)) := by
  let f : RetainedEdgeCountVector D eta R₀ →
      RetainedActivePair D eta R₀ → Fin ((Fintype.card V)^2 + 1) :=
    fun v e ↦ ⟨v.count e, Nat.lt_succ_iff.mpr
      ((v.count_le_capacity e).trans (retainedActiveCapacity_le_sq D eta R₀ e))⟩
  have hf : Function.Injective f := by
    intro v w heq
    apply RetainedEdgeCountVector.ext
    funext e
    exact congrArg (fun z ↦ (z e).val) heq
  calc
    Fintype.card (RetainedEdgeCountVector D eta R₀) ≤
        ((Fintype.card V)^2 + 1) ^ Fintype.card (RetainedActivePair D eta R₀) := by
      simpa only [Fintype.card_fun, Fintype.card_fin] using Fintype.card_le_of_injective f hf
    _ ≤ ((Fintype.card V)^3) ^ Fintype.card (RetainedActivePair D eta R₀) :=
      Nat.pow_le_pow_left (nat_sq_add_one_le_cube hn) _
    _ = _ := by rw [← pow_mul]

/-- The possible capacity-bounded integer adjustments of a prescribed
total size. They are count vectors, not edge subsets. -/
def retainedAdjustmentVectorFinset (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ d : ℕ) : Finset (RetainedEdgeCountVector D eta R₀) :=
  Finset.univ.filter (fun a ↦ retainedEdgeCountTotal a = d)

@[simp] theorem mem_retainedAdjustmentVectorFinset
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ d : ℕ)
    (a : RetainedEdgeCountVector D eta R₀) :
    a ∈ retainedAdjustmentVectorFinset D eta R₀ d ↔ retainedEdgeCountTotal a = d := by
  simp [retainedAdjustmentVectorFinset]

theorem card_retainedAdjustmentVectorFinset_le_order_pow
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ d : ℕ)
    (hn : 2 ≤ Fintype.card V) :
    (retainedAdjustmentVectorFinset D eta R₀ d).card ≤
      (Fintype.card V) ^ (3 * Fintype.card (RetainedActivePair D eta R₀)) :=
  (Finset.card_le_univ _).trans (card_retainedEdgeCountVector_le_order_pow D eta R₀ hn)

/-- Adding integer headroom moves a narrow signed level down to its wide
target. The allocation is nonnegative; the levels themselves need not be. -/
theorem retainedNarrowLevel_exists_add
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m : ℕ)
    {delta : ℝ} (hd : 0 ≤ delta) (hupper : pK k + 2 * delta ≤ 1)
    (hreserve : ∀ e, 2 ≤ delta * retainedActiveCapacity D eta R₀ e)
    {u u' : ℤ} (d : ℕ) (hshift : u' - u = d)
    (hdist : (d : ℝ) ≤ delta * retainedActiveTotalCapacity D eta R₀ / 4)
    {v : RetainedEdgeCountVector D eta R₀}
    (hv : v ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta u') :
    ∃ w : RetainedEdgeCountVector D eta R₀,
      w ∈ retainedEdgeCountLevel D eta R₀ m delta u ∧
      (∀ e, v.count e ≤ w.count e) ∧
      ∑ e, (w.count e - v.count e) = d := by
  obtain ⟨a, ha, hsum⟩ := DenseGraph.exists_allocation_le_floor_density
    (retainedActiveCapacity D eta R₀) d hreserve hdist
  have hband := (mem_retainedNarrowEdgeCountLevel.mp hv).2
  have hac : ∀ e, (a e : ℝ) ≤ delta * retainedActiveCapacity D eta R₀ e := by
    intro e
    exact (show (a e : ℝ) ≤ (⌊delta * retainedActiveCapacity D eta R₀ e⌋₊ : ℝ) by
      exact_mod_cast ha e).trans (Nat.floor_le (by positivity))
  have hN : ∀ e, (0 : ℝ) < retainedActiveCapacity D eta R₀ e :=
    fun e ↦ by exact_mod_cast retainedActiveCapacity_pos D eta R₀ e
  have hup : ∀ e, (v.count e + a e : ℝ) ≤
      (pK k + 2 * delta) * retainedActiveCapacity D eta R₀ e := by
    intro e
    have hx := (div_le_iff₀ (hN e)).mp (hband e).2
    change (v.count e : ℝ) ≤ _ at hx
    linarith [hac e]
  let w : RetainedEdgeCountVector D eta R₀ :=
    ⟨fun e ↦ v.count e + a e, fun e ↦ by
      have h := (hup e).trans (mul_le_of_le_one_left (hN e).le hupper)
      exact_mod_cast h⟩
  refine ⟨w, mem_retainedEdgeCountLevel.mpr ⟨?_, ?_⟩, ?_, ?_⟩
  · have ht : retainedEdgeCountTotal w = retainedEdgeCountTotal v + d := by
      simp only [retainedEdgeCountTotal, w, Finset.sum_add_distrib, hsum]
    rw [ht, Nat.cast_add]
    have hv := (mem_retainedNarrowEdgeCountLevel.mp hv).1
    omega
  · intro e
    constructor
    · apply (le_div_iff₀ (hN e)).mpr
      have hx := (le_div_iff₀ (hN e)).mp (hband e).1
      change (pK k - delta) * _ ≤ (v.count e : ℝ) at hx
      dsimp [retainedEdgeCountDensity, w]
      push_cast
      nlinarith [hN e, show (0 : ℝ) ≤ a e by positivity]
    · exact (div_le_iff₀ (hN e)).mpr (by simpa [w] using hup e)
  · intro e
    exact Nat.le_add_right _ _
  · simpa [w] using hsum

/-- Subtracting integer headroom moves a narrow signed level up to its
wide target, without natural-subtraction truncation. -/
theorem retainedNarrowLevel_exists_sub
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m : ℕ)
    {delta : ℝ} (hd : 0 ≤ delta) (hlower : 0 ≤ pK k - 2 * delta)
    (hreserve : ∀ e, 2 ≤ delta * retainedActiveCapacity D eta R₀ e)
    {u u' : ℤ} (d : ℕ) (hshift : u - u' = d)
    (hdist : (d : ℝ) ≤ delta * retainedActiveTotalCapacity D eta R₀ / 4)
    {v : RetainedEdgeCountVector D eta R₀}
    (hv : v ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta u') :
    ∃ w : RetainedEdgeCountVector D eta R₀,
      w ∈ retainedEdgeCountLevel D eta R₀ m delta u ∧
      (∀ e, w.count e ≤ v.count e) ∧
      ∑ e, (v.count e - w.count e) = d := by
  obtain ⟨a, ha, hsum⟩ := DenseGraph.exists_allocation_le_floor_density
    (retainedActiveCapacity D eta R₀) d hreserve hdist
  have hband := (mem_retainedNarrowEdgeCountLevel.mp hv).2
  have hac : ∀ e, (a e : ℝ) ≤ delta * retainedActiveCapacity D eta R₀ e := by
    intro e
    exact (show (a e : ℝ) ≤ (⌊delta * retainedActiveCapacity D eta R₀ e⌋₊ : ℝ) by
      exact_mod_cast ha e).trans (Nat.floor_le (by positivity))
  have hN : ∀ e, (0 : ℝ) < retainedActiveCapacity D eta R₀ e :=
    fun e ↦ by exact_mod_cast retainedActiveCapacity_pos D eta R₀ e
  have hal : ∀ e, a e ≤ v.count e := by
    intro e
    have hx := (le_div_iff₀ (hN e)).mp (hband e).1
    change (pK k - delta) * _ ≤ (v.count e : ℝ) at hx
    have hnon := mul_nonneg hlower (hN e).le
    have : (a e : ℝ) ≤ v.count e := by nlinarith [hac e]
    exact_mod_cast this
  let w : RetainedEdgeCountVector D eta R₀ :=
    ⟨fun e ↦ v.count e - a e,
      fun e ↦ (Nat.sub_le _ _).trans (v.count_le_capacity e)⟩
  have hsumw : retainedEdgeCountTotal w + d = retainedEdgeCountTotal v := by
    rw [← hsum]
    change (∑ e, (v.count e - a e)) + ∑ e, a e = ∑ e, v.count e
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun e _ ↦ Nat.sub_add_cancel (hal e))
  refine ⟨w, mem_retainedEdgeCountLevel.mpr ⟨?_, ?_⟩, ?_, ?_⟩
  · have ht : (retainedEdgeCountTotal w : ℤ) + d = retainedEdgeCountTotal v := by
      exact_mod_cast hsumw
    have hv := (mem_retainedNarrowEdgeCountLevel.mp hv).1
    omega
  · intro e
    have hwe : (w.count e : ℝ) = (v.count e : ℝ) - a e := by
      simp only [w, Nat.cast_sub (hal e)]
    change _ ≤ (w.count e : ℝ) / _ ∧ (w.count e : ℝ) / _ ≤ _
    constructor
    · apply (le_div_iff₀ (hN e)).mpr
      rw [hwe]
      have hx := (le_div_iff₀ (hN e)).mp (hband e).1
      change (pK k - delta) * _ ≤ (v.count e : ℝ) at hx
      linarith [hac e]
    · apply (div_le_iff₀ (hN e)).mpr
      rw [hwe]
      have hx := (div_le_iff₀ (hN e)).mp (hband e).2
      change (v.count e : ℝ) ≤ _ at hx
      nlinarith [hN e, show (0 : ℝ) ≤ a e by positivity]
  · exact fun e ↦ Nat.sub_le _ _
  · simpa only [w, Nat.sub_sub_self (hal _)] using hsum

/-- Product version of the upward adjacent-ratio estimate. -/
theorem retainedEdgeCountMultiplicity_up_le
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (hk : 3 ≤ k) {delta : ℝ} (hd : 0 ≤ delta)
    (hdp : 6 * delta ≤ pK k) (hdq : 6 * delta ≤ 1 - pK k)
    (v w : RetainedEdgeCountVector D eta R₀)
    (hvw : ∀ e, v.count e ≤ w.count e)
    (hw : ∀ e, retainedEdgeCountDensity w e ≤ pK k + 2 * delta)
    (d : ℕ) (hsum : ∑ e, (w.count e - v.count e) = d) :
    (retainedEdgeCountMultiplicity v : ℝ) ≤
      (retainedEdgeCountMultiplicity w : ℝ) *
        Real.exp ((-subcriticalLogOddsNat k + subcriticalActiveLevelConstant k * delta) * d) := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hp1 := pK_lt_one (show 2 ≤ k by omega)
  let c := -subcriticalLogOddsNat k + DenseGraph.binomialLogOddsConstant (pK k) * delta
  have hpoint : ∀ e, (Nat.choose (retainedActiveCapacity D eta R₀ e) (v.count e) : ℝ) ≤
      (Nat.choose (retainedActiveCapacity D eta R₀ e) (w.count e) : ℝ) *
        Real.exp (c * (w.count e - v.count e : ℕ)) := by
    intro e
    exact DenseGraph.choose_up_le_mul_exp_logOdds hp hp1 hd hdp hdq
      (retainedActiveCapacity_pos D eta R₀ e) (hvw e) (w.count_le_capacity e) (hw e)
  have hprod := Finset.prod_le_prod (fun e (_ : e ∈ (Finset.univ : Finset
    (RetainedActivePair D eta R₀))) ↦ by
      positivity : ∀ e ∈ (Finset.univ : Finset (RetainedActivePair D eta R₀)),
        (0 : ℝ) ≤ Nat.choose (retainedActiveCapacity D eta R₀ e) (v.count e))
    (fun e _ ↦ hpoint e)
  have hprod' : (retainedEdgeCountMultiplicity v : ℝ) ≤
      (retainedEdgeCountMultiplicity w : ℝ) * Real.exp (c * d) := by
    simpa only [retainedEdgeCountMultiplicity, Nat.cast_prod,
      Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum,
      ← Nat.cast_sum, hsum] using hprod
  have hc : c ≤ -subcriticalLogOddsNat k + subcriticalActiveLevelConstant k * delta := by
    dsimp [c, subcriticalActiveLevelConstant]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_right _ _) hd)
  exact hprod'.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc (by positivity))) (by positivity))

/-- Product version of the downward adjacent-ratio estimate. -/
theorem retainedEdgeCountMultiplicity_down_le
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (hk : 3 ≤ k) {delta : ℝ} (hd : 0 ≤ delta)
    (hdp : 6 * delta ≤ pK k) (hdq : 6 * delta ≤ 1 - pK k)
    (hreserve : ∀ e, 2 ≤ delta * retainedActiveCapacity D eta R₀ e)
    (v w : RetainedEdgeCountVector D eta R₀)
    (hwv : ∀ e, w.count e ≤ v.count e)
    (hw : ∀ e, pK k - 2 * delta ≤ retainedEdgeCountDensity w e)
    (d : ℕ) (hsum : ∑ e, (v.count e - w.count e) = d) :
    (retainedEdgeCountMultiplicity v : ℝ) ≤
      (retainedEdgeCountMultiplicity w : ℝ) *
        Real.exp ((subcriticalLogOddsNat k + subcriticalActiveLevelConstant k * delta) * d) := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hp1 := pK_lt_one (show 2 ≤ k by omega)
  let c := subcriticalLogOddsNat k + DenseGraph.binomialLogOddsConstant (pK k) * delta
  have hpoint : ∀ e, (Nat.choose (retainedActiveCapacity D eta R₀ e) (v.count e) : ℝ) ≤
      (Nat.choose (retainedActiveCapacity D eta R₀ e) (w.count e) : ℝ) *
        Real.exp (c * (v.count e - w.count e : ℕ)) := by
    intro e
    exact DenseGraph.choose_down_le_mul_exp_logOdds hp hp1 hd hdp hdq
      (retainedActiveCapacity_pos D eta R₀ e) (hwv e) (v.count_le_capacity e) (hw e)
      (by linarith [hreserve e])
  have hprod := Finset.prod_le_prod (fun e (_ : e ∈ (Finset.univ : Finset
    (RetainedActivePair D eta R₀))) ↦ by
      positivity : ∀ e ∈ (Finset.univ : Finset (RetainedActivePair D eta R₀)),
        (0 : ℝ) ≤ Nat.choose (retainedActiveCapacity D eta R₀ e) (v.count e))
    (fun e _ ↦ hpoint e)
  have hprod' : (retainedEdgeCountMultiplicity v : ℝ) ≤
      (retainedEdgeCountMultiplicity w : ℝ) * Real.exp (c * d) := by
    simpa only [retainedEdgeCountMultiplicity, Nat.cast_prod,
      Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum,
      ← Nat.cast_sum, hsum] using hprod
  have hc : c ≤ subcriticalLogOddsNat k + subcriticalActiveLevelConstant k * delta := by
    dsimp [c, subcriticalActiveLevelConstant]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_right _ _) hd)
  exact hprod'.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc (by positivity))) (by positivity))

/-- Every vector in the narrow source level has its multiplicity controlled
by the wide target partition function. Both shifts are arbitrary integers. -/
theorem retainedNarrowMultiplicity_le_partitionFunction
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m : ℕ)
    (hk : 3 ≤ k) {delta : ℝ} (hd : 0 ≤ delta)
    (hdp : 6 * delta ≤ pK k) (hdq : 6 * delta ≤ 1 - pK k)
    (hreserve : ∀ e, 2 ≤ delta * retainedActiveCapacity D eta R₀ e)
    {u u' : ℤ} (aPlus aMinus : ℕ) (hshift : u' - u = (aPlus : ℤ) - aMinus)
    (hdist : |(u' - u : ℤ)| ≤ delta * retainedActiveTotalCapacity D eta R₀ / 4)
    {v : RetainedEdgeCountVector D eta R₀}
    (hv : v ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta u') :
    (retainedEdgeCountMultiplicity v : ℝ) ≤
      Real.exp (-(subcriticalLogOddsNat k - subcriticalActiveLevelConstant k * delta) * aPlus +
        (subcriticalLogOddsNat k + subcriticalActiveLevelConstant k * delta) * aMinus) *
      (retainedPartitionFunction D eta R₀ m delta u : ℝ) := by
  have hc := mul_nonneg (subcriticalActiveLevelConstant_pos k).le hd
  have hshiftR : (u' : ℝ) - u = (aPlus : ℝ) - aMinus := by exact_mod_cast hshift
  by_cases hnonneg : 0 ≤ u' - u
  · let d := (u' - u).toNat
    have hdZ : (d : ℤ) = u' - u := Int.toNat_of_nonneg hnonneg
    have hdR : (d : ℝ) = (u' : ℝ) - u := by exact_mod_cast hdZ
    have hdist' : (d : ℝ) ≤ delta * retainedActiveTotalCapacity D eta R₀ / 4 := by
      rw [abs_of_nonneg hnonneg] at hdist
      simpa only [← hdZ, Int.cast_natCast] using hdist
    obtain ⟨w, hw, hvw, hsum⟩ := retainedNarrowLevel_exists_add D eta R₀ m hd
      (by linarith) hreserve d hdZ.symm hdist' hv
    have hmul := retainedEdgeCountMultiplicity_up_le D eta R₀ hk hd hdp hdq v w hvw
      (fun e ↦ ((mem_retainedEdgeCountLevel.mp hw).2 e).2) d hsum
    have hexp : Real.exp ((-subcriticalLogOddsNat k + subcriticalActiveLevelConstant k * delta) * d) ≤
        Real.exp (-(subcriticalLogOddsNat k - subcriticalActiveLevelConstant k * delta) * aPlus +
          (subcriticalLogOddsNat k + subcriticalActiveLevelConstant k * delta) * aMinus) := by
      apply Real.exp_le_exp.mpr
      rw [hdR, hshiftR]
      nlinarith [mul_nonneg hc (show (0 : ℝ) ≤ aMinus by positivity)]
    have hwZ : (retainedEdgeCountMultiplicity w : ℝ) ≤
        retainedPartitionFunction D eta R₀ m delta u := by
      exact_mod_cast retainedEdgeCountMultiplicity_le_partitionFunction hw
    exact hmul.trans (by simpa only [mul_comm] using mul_le_mul hwZ hexp (by positivity) (by positivity))
  · let d := (u - u').toNat
    have hdZ : (d : ℤ) = u - u' := Int.toNat_of_nonneg (by omega)
    have hdR : (d : ℝ) = (u : ℝ) - u' := by exact_mod_cast hdZ
    have hdist' : (d : ℝ) ≤ delta * retainedActiveTotalCapacity D eta R₀ / 4 := by
      have hn : (u' - u : ℤ) ≤ 0 := by omega
      rw [abs_of_nonpos hn] at hdist
      simpa only [Int.cast_neg, Int.cast_sub, neg_sub, ← hdR] using hdist
    obtain ⟨w, hw, hwv, hsum⟩ := retainedNarrowLevel_exists_sub D eta R₀ m hd
      (by linarith) hreserve d hdZ.symm hdist' hv
    have hmul := retainedEdgeCountMultiplicity_down_le D eta R₀ hk hd hdp hdq hreserve v w hwv
      (fun e ↦ ((mem_retainedEdgeCountLevel.mp hw).2 e).1) d hsum
    have hexp : Real.exp ((subcriticalLogOddsNat k + subcriticalActiveLevelConstant k * delta) * d) ≤
        Real.exp (-(subcriticalLogOddsNat k - subcriticalActiveLevelConstant k * delta) * aPlus +
          (subcriticalLogOddsNat k + subcriticalActiveLevelConstant k * delta) * aMinus) := by
      apply Real.exp_le_exp.mpr
      have hdr : (d : ℝ) = (aMinus : ℝ) - aPlus := by linarith
      rw [hdr]
      nlinarith [mul_nonneg hc (show (0 : ℝ) ≤ aPlus by positivity)]
    have hwZ : (retainedEdgeCountMultiplicity w : ℝ) ≤
        retainedPartitionFunction D eta R₀ m delta u := by
      exact_mod_cast retainedEdgeCountMultiplicity_le_partitionFunction hw
    exact hmul.trans (by simpa only [mul_comm] using mul_le_mul hwZ hexp (by positivity) (by positivity))

/-- Paper: Lemma `lemma:active-level-comparison-K1k`, with the natural-log
natural-unit normalization. The explicit `n^(3|I|)` prefactor is at least as
strong as the unspecified polynomial prefactor in the paper. A reserve of
two units per coordinate makes the paper's exact quarter-capacity range
valid after integer rounding. No feasibility, nonempty-index, or sign
assumption is imposed on the two signed levels. -/
theorem subcriticalActiveLevelComparison
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m : ℕ)
    (hk : 3 ≤ k) (hn : 2 ≤ Fintype.card V) {delta : ℝ} (hd : 0 ≤ delta)
    (hdp : 6 * delta ≤ pK k) (hdq : 6 * delta ≤ 1 - pK k)
    (hreserve : ∀ e, 2 ≤ delta * retainedActiveCapacity D eta R₀ e)
    {u u' : ℤ} (aPlus aMinus : ℕ) (hshift : u' - u = (aPlus : ℤ) - aMinus)
    (hdist : |(u' - u : ℤ)| ≤ delta * retainedActiveTotalCapacity D eta R₀ / 4) :
    (retainedNarrowPartitionFunction D eta R₀ m delta u' : ℝ) ≤
      (Fintype.card V : ℝ) ^ (3 * Fintype.card (RetainedActivePair D eta R₀)) *
        Real.exp (-(subcriticalLogOddsNat k - subcriticalActiveLevelConstant k * delta) * aPlus +
          (subcriticalLogOddsNat k + subcriticalActiveLevelConstant k * delta) * aMinus) *
        (retainedPartitionFunction D eta R₀ m delta u : ℝ) := by
  let A := retainedNarrowEdgeCountLevel D eta R₀ m delta u'
  let Q := Real.exp (-(subcriticalLogOddsNat k - subcriticalActiveLevelConstant k * delta) * aPlus +
    (subcriticalLogOddsNat k + subcriticalActiveLevelConstant k * delta) * aMinus) *
      (retainedPartitionFunction D eta R₀ m delta u : ℝ)
  have hpoint : ∀ v ∈ A, (retainedEdgeCountMultiplicity v : ℝ) ≤ Q := by
    intro v hv
    exact retainedNarrowMultiplicity_le_partitionFunction D eta R₀ m hk hd hdp hdq
      hreserve aPlus aMinus hshift hdist hv
  have hs : (retainedNarrowPartitionFunction D eta R₀ m delta u' : ℝ) ≤ (A.card : ℝ) * Q := by
    simpa only [retainedNarrowPartitionFunction, Nat.cast_sum, Finset.sum_const,
      nsmul_eq_mul, A] using Finset.sum_le_sum hpoint
  have hcard : A.card ≤ (Fintype.card V) ^ (3 * Fintype.card (RetainedActivePair D eta R₀)) :=
    (Finset.card_le_univ A).trans (card_retainedEdgeCountVector_le_order_pow D eta R₀ hn)
  have hcardR : (A.card : ℝ) ≤
      (Fintype.card V : ℝ) ^ (3 * Fintype.card (RetainedActivePair D eta R₀)) := by
    exact_mod_cast hcard
  exact hs.trans (by simpa only [Q, mul_assoc] using
    mul_le_mul_of_nonneg_right hcardR (show 0 ≤ Q by dsimp [Q]; positivity))

end InducedStars
