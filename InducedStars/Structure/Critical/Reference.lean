import DenseGraph.FiniteModels.BalancedAssignments
import InducedStars.Structure.Critical.FiniteGeometry
import InducedStars.Structure.Supercritical.CoverMultiplicity
import InducedStars.Structure.Supercritical.ReferenceFiber

/-!
# Balanced reference families at the critical density

This file isolates the exactly balanced ordered divisions and their
exact-critical-edge co-multipartite fibers.  The definitions are total for
every `n`; statements requiring nonempty parts explicitly retain or
eventually discharge the condition `k - 1 ≤ n`.
-/

noncomputable section

open Filter Finset Set Topology
open scoped BigOperators

namespace InducedStars

noncomputable local instance criticalReferenceDivisionDecidableEq
    (k n : ℕ) : DecidableEq (SupercriticalDivision k (Fin n)) :=
  Classical.decEq _

noncomputable local instance criticalReferenceGraphDecidableEq
    (n : ℕ) : DecidableEq (SimpleGraph (Fin n)) :=
  Classical.decEq _

/-! ## Exactly balanced full divisions -/

/-- A full ordered division whose `i`th part has the cardinality of the
`i`th canonical balanced part.  Fixing the ordered size vector makes the
finite family correspond exactly to balanced assignments. -/
def IsExactlyBalancedFullDivision
    {k n : ℕ} (D : SupercriticalDivision k (Fin n)) : Prop :=
  D.IsFull ∧ ∀ i : Fin (k - 1),
    (D.parts i).card =
      (DenseGraph.balancedFinPartition (k - 1) n i).card

instance {k n : ℕ} (D : SupercriticalDivision k (Fin n)) :
    Decidable (IsExactlyBalancedFullDivision D) :=
  Classical.propDecidable _

/-- The finite family of exactly balanced full ordered divisions. -/
noncomputable def exactlyBalancedFullSupercriticalDivisions
    (k n : ℕ) : Finset (SupercriticalDivision k (Fin n)) :=
  (allSupercriticalDivisions k n).filter IsExactlyBalancedFullDivision

@[simp] theorem mem_exactlyBalancedFullSupercriticalDivisions
    {k n : ℕ} {D : SupercriticalDivision k (Fin n)} :
    D ∈ exactlyBalancedFullSupercriticalDivisions k n ↔
      IsExactlyBalancedFullDivision D := by
  simp [exactlyBalancedFullSupercriticalDivisions]

/-- The consecutive balanced division belongs to the exact balanced family. -/
theorem supercriticalBalancedDivision_isExactlyBalanced
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    IsExactlyBalancedFullDivision (supercriticalBalancedDivision hk hn) := by
  refine ⟨supercriticalBalancedDivision_isFull hk hn, ?_⟩
  intro i
  rw [supercriticalBalancedDivision_parts]
  rfl

@[simp] theorem supercriticalBalancedDivision_mem_exactlyBalanced
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    supercriticalBalancedDivision hk hn ∈
      exactlyBalancedFullSupercriticalDivisions k n :=
  mem_exactlyBalancedFullSupercriticalDivisions.mpr
    (supercriticalBalancedDivision_isExactlyBalanced hk hn)

/-! ## Balanced assignments and exactly balanced divisions -/

/-- Decode a balanced full assignment into its ordered supercritical
division.  The hypothesis `k - 1 ≤ n` ensures every prescribed balanced
fiber is nonempty. -/
noncomputable def balancedAssignmentDivision
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (f : {f : Fin n → Fin (k - 1) //
      DenseGraph.IsBalancedAssignment (k - 1) n f}) :
    SupercriticalDivision k (Fin n) :=
  SupercriticalDivision.ofAssignment (fun v ↦ some (f.1 v)) (by
    intro i
    have hr : 0 < k - 1 := by omega
    have hsize : 0 < DenseGraph.balancedPartSize (k - 1) n i := by
      rw [DenseGraph.balancedPartSize_eq_card_balancedFinPartition hr]
      exact Finset.card_pos.mpr
        (DenseGraph.balancedFinPartition_nonempty hr hn i)
    have hfiber := DenseGraph.isBalancedAssignment_fiberSize f.2 i
    unfold DenseGraph.assignmentFiberSize at hfiber
    have hnonempty :
        (Finset.univ.filter fun v ↦ f.1 v = i).Nonempty := by
      rw [← Finset.card_pos, hfiber]
      exact hsize
    obtain ⟨v, hv⟩ := hnonempty
    exact ⟨v, by simpa using (Finset.mem_filter.mp hv).2⟩)

@[simp] theorem balancedAssignmentDivision_parts
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (f : {f : Fin n → Fin (k - 1) //
      DenseGraph.IsBalancedAssignment (k - 1) n f})
    (i : Fin (k - 1)) :
    (balancedAssignmentDivision hk hn f).parts i =
      Finset.univ.filter fun v ↦ f.1 v = i := by
  ext v
  simp [balancedAssignmentDivision, SupercriticalDivision.ofAssignment]

theorem balancedAssignmentDivision_isFull
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (f : {f : Fin n → Fin (k - 1) //
      DenseGraph.IsBalancedAssignment (k - 1) n f}) :
    (balancedAssignmentDivision hk hn f).IsFull := by
  rw [SupercriticalDivision.isFull_iff_support_eq_univ]
  ext v
  simp only [SupercriticalDivision.mem_support, Finset.mem_univ, iff_true]
  exact ⟨f.1 v, by simp⟩

/-- Decoding a balanced assignment produces an exactly balanced full
division with the same ordered size vector. -/
theorem balancedAssignmentDivision_isExactlyBalanced
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (f : {f : Fin n → Fin (k - 1) //
      DenseGraph.IsBalancedAssignment (k - 1) n f}) :
    IsExactlyBalancedFullDivision (balancedAssignmentDivision hk hn f) := by
  refine ⟨balancedAssignmentDivision_isFull hk hn f, ?_⟩
  intro i
  rw [balancedAssignmentDivision_parts]
  have hfiber := DenseGraph.isBalancedAssignment_fiberSize f.2 i
  unfold DenseGraph.assignmentFiberSize at hfiber
  rw [hfiber, DenseGraph.balancedPartSize_eq_card_balancedFinPartition
    (by omega : 0 < k - 1)]

/-- Distinct balanced assignments decode to distinct ordered divisions. -/
theorem balancedAssignmentDivision_injective
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    Function.Injective (@balancedAssignmentDivision k n hk hn) := by
  intro f g hfg
  apply Subtype.ext
  funext v
  have hvf : v ∈ (balancedAssignmentDivision hk hn f).parts (f.1 v) := by
    simp
  rw [hfg] at hvf
  have hvg : v ∈ (balancedAssignmentDivision hk hn g).parts (g.1 v) := by
    simp
  exact (balancedAssignmentDivision hk hn g).mem_part_unique hvf hvg

/-- The generic balanced-assignment family injects into the exactly balanced
ordered divisions. -/
theorem card_balancedAssignments_le_exactlyBalancedDivisions
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    (DenseGraph.balancedAssignments (k - 1) n).card ≤
      (exactlyBalancedFullSupercriticalDivisions k n).card := by
  let source := DenseGraph.balancedAssignments (k - 1) n
  let decode : {f // f ∈ source} → SupercriticalDivision k (Fin n) :=
    fun f ↦ balancedAssignmentDivision hk hn
      ⟨f.1, DenseGraph.mem_balancedAssignments.mp f.2⟩
  have hmaps : Set.MapsTo decode (source.attach :
      Set {f // f ∈ source})
      (exactlyBalancedFullSupercriticalDivisions k n :
        Set (SupercriticalDivision k (Fin n))) := by
    intro f _hf
    exact mem_exactlyBalancedFullSupercriticalDivisions.mpr
      (balancedAssignmentDivision_isExactlyBalanced hk hn
        ⟨f.1, DenseGraph.mem_balancedAssignments.mp f.2⟩)
  have hinjective : Function.Injective decode := by
    intro f g hfg
    apply Subtype.ext
    have hsub := balancedAssignmentDivision_injective hk hn hfg
    exact congrArg
      (fun h : {a : Fin n → Fin (k - 1) //
        DenseGraph.IsBalancedAssignment (k - 1) n a} ↦ h.1) hsub
  have hcard := Finset.card_le_card_of_injOn decode hmaps hinjective.injOn
  simpa [source] using hcard

/-- No-Stirling lower bound for exactly balanced full ordered divisions. -/
theorem pow_le_succ_pow_mul_card_exactlyBalancedDivisions
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    (k - 1) ^ n ≤ (n + 1) ^ (k - 1) *
      (exactlyBalancedFullSupercriticalDivisions k n).card := by
  calc
    (k - 1) ^ n ≤ (n + 1) ^ (k - 1) *
        (DenseGraph.balancedAssignments (k - 1) n).card :=
      DenseGraph.pow_le_succ_pow_mul_card_balancedAssignments (by omega)
    _ ≤ (n + 1) ^ (k - 1) *
        (exactlyBalancedFullSupercriticalDivisions k n).card :=
      Nat.mul_le_mul_left _
        (card_balancedAssignments_le_exactlyBalancedDivisions hk hn)

/-- Eventual form of the balanced-division lower bound. -/
theorem eventually_pow_le_succ_pow_mul_card_exactlyBalancedDivisions
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      (k - 1) ^ n ≤ (n + 1) ^ (k - 1) *
        (exactlyBalancedFullSupercriticalDivisions k n).card := by
  filter_upwards [eventually_ge_atTop (k - 1)] with n hn
  exact pow_le_succ_pow_mul_card_exactlyBalancedDivisions hk hn

/-! ## Balanced capacities -/

/-- Every exactly balanced full division has the canonical balanced internal
capacity. -/
theorem exactlyBalancedDivision_internalCapacity_eq
    {k n : ℕ} {D : SupercriticalDivision k (Fin n)}
    (hk : 3 ≤ k) (hD : IsExactlyBalancedFullDivision D) :
    divisionInternalCliqueCapacity D =
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n := by
  have hr : 0 < k - 1 := by omega
  rw [DenseGraph.balancedMultipartiteInternalCapacity_eq_sum_choose hr]
  unfold divisionInternalCliqueCapacity
  apply Finset.sum_congr rfl
  intro i _hi
  rw [hD.2 i]

/-- Every exactly balanced full division has the canonical balanced cross
capacity. -/
theorem exactlyBalancedDivision_crossCapacity_eq
    {k n : ℕ} {D : SupercriticalDivision k (Fin n)}
    (hk : 3 ≤ k) (hD : IsExactlyBalancedFullDivision D) :
    supercriticalTotalCrossCapacity D =
      DenseGraph.balancedMultipartiteCrossCapacity (k - 1) n := by
  have htotal := supercriticalTotalCrossCapacity_add_internal D
  rw [D.support_eq_univ hD.1] at htotal
  simp only [Finset.card_univ, Fintype.card_fin] at htotal
  have hbalanced := DenseGraph.balancedCross_add_internal (k - 1) n
  rw [exactlyBalancedDivision_internalCapacity_eq hk hD] at htotal
  omega

@[simp] theorem supercriticalBalancedDivision_internalCapacity_eq
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    divisionInternalCliqueCapacity (supercriticalBalancedDivision hk hn) =
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n :=
  exactlyBalancedDivision_internalCapacity_eq hk
    (supercriticalBalancedDivision_isExactlyBalanced hk hn)

@[simp] theorem supercriticalBalancedDivision_crossCapacity_eq
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    supercriticalTotalCrossCapacity (supercriticalBalancedDivision hk hn) =
      DenseGraph.balancedMultipartiteCrossCapacity (k - 1) n :=
  exactlyBalancedDivision_crossCapacity_eq hk
    (supercriticalBalancedDivision_isExactlyBalanced hk hn)

/-- The number of available optional cross-edge coordinates in an exactly
balanced critical reference division. -/
def criticalTargetCapacity (k n : ℕ) : ℕ :=
  DenseGraph.balancedMultipartiteCrossCapacity (k - 1) n

/-- The number of optional cross edges selected in a balanced critical
reference graph. -/
def criticalTargetSelectedCount (k n : ℕ) : ℕ :=
  criticalEdgeCount k n -
    DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n

/-- Exact binomial size of one feasible exactly balanced critical fiber. -/
def criticalReferenceFiberCard (k n : ℕ) : ℕ :=
  if DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
      criticalEdgeCount k n then
    Nat.choose (criticalTargetCapacity k n) (criticalTargetSelectedCount k n)
  else 0

/-- In the feasible range, the guarded reference count is the expected
binomial coefficient. -/
theorem criticalReferenceFiberCard_eq_choose_of_feasible
    {k n : ℕ}
    (hfeasible :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
        criticalEdgeCount k n) :
    criticalReferenceFiberCard k n =
      Nat.choose (criticalTargetCapacity k n)
        (criticalTargetSelectedCount k n) := by
  simp [criticalReferenceFiberCard, hfeasible]

/-- Outside the feasible range, the total reference count is zero. -/
theorem criticalReferenceFiberCard_eq_zero_of_not_feasible
    {k n : ℕ}
    (hfeasible :
      ¬DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
        criticalEdgeCount k n) :
    criticalReferenceFiberCard k n = 0 := by
  simp [criticalReferenceFiberCard, hfeasible]

/-- Compatibility spelling emphasizing that the selected coordinates belong
to the balanced critical reference fiber. -/
abbrev criticalBalancedSelectedEdgeCount (k n : ℕ) : ℕ :=
  criticalTargetSelectedCount k n

/-- The cross-edge density selected by the balanced critical reference
fiber.  The total definition uses the usual real convention `x / 0 = 0`. -/
def criticalBalancedSelectedDensity (k n : ℕ) : ℝ :=
  (criticalTargetSelectedCount k n : ℝ) /
    (criticalTargetCapacity k n : ℝ)

/-- Ordered-square normalization of the balanced cross capacity converges to
the off-diagonal area of a balanced `(k-1)`-partition. -/
theorem criticalTargetCapacity_orderedSquare_tendsto
    (k : ℕ) (hk : 3 ≤ k) :
    Tendsto
      (fun n : ℕ ↦
        2 * (criticalTargetCapacity k n : ℝ) / (n : ℝ) ^ 2)
      atTop
      (nhds (((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ))) := by
  have hr : 0 < k - 1 := by omega
  have hrReal : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast hr
  have hinvN : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ))
      atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hinvSq : Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹)
      atTop (nhds 0) := by
    simpa only [one_div, inv_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      hinvN.pow 2
  have hbound : Tendsto
      (fun n : ℕ ↦ (2 * ((k - 1 : ℕ) : ℝ)) / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hinvSq)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hbound ε hε
  refine ⟨max N 1, fun n hn ↦ ?_⟩
  have hnN : N ≤ n := (Nat.le_max_left _ _).trans hn
  have hnOne : 1 ≤ n := (Nat.le_max_right _ _).trans hn
  have hnReal : (n : ℝ) ≠ 0 := by positivity
  have happ := DenseGraph.balancedMultipartiteCrossCapacity_approx
    (r := k - 1) (q := n) hr
  have htargetCast :
      (((k - 1 : ℕ) : ℝ) - 1) / ((k - 1 : ℕ) : ℝ) =
        ((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ) := by
    have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      norm_num
    have hkm2 : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ k)]
      norm_num
    rw [hkm1, hkm2]
    ring
  rw [Real.dist_eq]
  rw [← htargetCast]
  have hrearrange :
      2 * (criticalTargetCapacity k n : ℝ) / (n : ℝ) ^ 2 -
          (((k - 1 : ℕ) : ℝ) - 1) / ((k - 1 : ℕ) : ℝ) =
        2 * ((criticalTargetCapacity k n : ℝ) -
          (((k - 1 : ℕ) : ℝ) - 1) * (n : ℝ) ^ 2 /
            (2 * ((k - 1 : ℕ) : ℝ))) / (n : ℝ) ^ 2 := by
    field_simp
  rw [hrearrange]
  calc
    |2 * ((criticalTargetCapacity k n : ℝ) -
          (((k - 1 : ℕ) : ℝ) - 1) * (n : ℝ) ^ 2 /
            (2 * ((k - 1 : ℕ) : ℝ))) / (n : ℝ) ^ 2| =
        2 * |(criticalTargetCapacity k n : ℝ) -
          (((k - 1 : ℕ) : ℝ) - 1) * (n : ℝ) ^ 2 /
            (2 * ((k - 1 : ℕ) : ℝ))| / (n : ℝ) ^ 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (sq_nonneg (n : ℝ))]
    _ ≤ 2 * ((k - 1 : ℕ) : ℝ) / (n : ℝ) ^ 2 := by
      gcongr
      simpa only [criticalTargetCapacity] using happ
    _ < ε := by
      have hnonneg :
          0 ≤ 2 * ((k - 1 : ℕ) : ℝ) / (n : ℝ) ^ 2 := by positivity
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hN n hnN

/-- Ordered-square normalization of the complementary balanced internal
capacity converges to the diagonal area. -/
theorem criticalBalancedInternalCapacity_orderedSquare_tendsto
    (k : ℕ) (hk : 3 ≤ k) :
    Tendsto
      (fun n : ℕ ↦
        2 * (DenseGraph.balancedMultipartiteInternalCapacity
          (k - 1) n : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds (1 / ((k - 1 : ℕ) : ℝ))) := by
  have hrNat : 0 < k - 1 := by omega
  have hrReal : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast hrNat
  have htarget :
      1 - ((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ) =
        1 / ((k - 1 : ℕ) : ℝ) := by
    have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      norm_num
    have hkm2 : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ k)]
      norm_num
    have hkReal : (3 : ℝ) ≤ k := by exact_mod_cast hk
    have hdenK : (k : ℝ) - 1 ≠ 0 := by linarith
    rw [hkm1, hkm2]
    field_simp [hdenK]
    ring
  rw [← htarget]
  apply (completeEdgeCount_orderedSquareFactor_tendsto_one.sub
    (criticalTargetCapacity_orderedSquare_tendsto k hk)).congr'
  filter_upwards with n
  have htotal := congrArg (fun q : ℕ ↦ (q : ℝ))
    (DenseGraph.balancedCross_add_internal (k - 1) n)
  push_cast at htotal
  simp only [criticalTargetCapacity, completeEdgeCount]
  rw [← htotal]
  ring

/-- The exact critical edge count has the expected ordered-square
normalization. -/
theorem criticalEdgeCount_orderedSquare_tendsto
    (k : ℕ) (hk : 3 ≤ k) :
    Tendsto
      (fun n : ℕ ↦ 2 * (criticalEdgeCount k n : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds (gammaK k)) := by
  have hprod := (criticalEdgeCount_hasAsymptoticEdgeDensity hk).mul
    completeEdgeCount_orderedSquareFactor_tendsto_one
  apply (show Tendsto
      (fun n ↦ ((criticalEdgeCount k n : ℝ) /
          (completeEdgeCount n : ℝ)) *
        (2 * (completeEdgeCount n : ℝ) / (n : ℝ) ^ 2))
      atTop (nhds (gammaK k)) by simpa using hprod).congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hN : (completeEdgeCount n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  field_simp

/-- Ordered-square normalization of the selected critical cross coordinates
converges to the critical density minus the diagonal area. -/
theorem criticalTargetSelectedCount_orderedSquare_tendsto
    (k : ℕ) (hk : 3 ≤ k) :
    Tendsto
      (fun n : ℕ ↦
        2 * (criticalTargetSelectedCount k n : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds (gammaK k - 1 / ((k - 1 : ℕ) : ℝ))) := by
  have hraw := eventually_balancedDivision_internal_le_of_density_gt
    k hk (gammaK k) (one_div_parts_lt_gammaK hk)
      (criticalEdgeCount k) (criticalEdgeCount_hasAsymptoticEdgeDensity hk)
  have hfeasible : ∀ᶠ n : ℕ in atTop,
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
        criticalEdgeCount k n := by
    filter_upwards [hraw, eventually_ge_atTop (k - 1)] with n hraw hn
    simpa only [supercriticalBalancedDivision_internalCapacity_eq hk hn] using
      hraw hn
  apply ((criticalEdgeCount_orderedSquare_tendsto k hk).sub
    (criticalBalancedInternalCapacity_orderedSquare_tendsto k hk)).congr'
  filter_upwards [hfeasible] with n hnfeasible
  rw [criticalTargetSelectedCount, Nat.cast_sub hnfeasible]
  ring

/-- The selected cross-edge density in the exact balanced critical reference
fiber converges to the distinguished probability `pK k`. -/
theorem criticalBalancedSelectedDensity_tendsto
    (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (criticalBalancedSelectedDensity k) atTop (nhds (pK k)) := by
  have hrPos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hsPos : (0 : ℝ) < ((k - 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - 2 by omega)
  have hden :
      ((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ) ≠ 0 :=
    div_ne_zero hsPos.ne' hrPos.ne'
  have hratio :=
    (criticalTargetSelectedCount_orderedSquare_tendsto k hk).div
      (criticalTargetCapacity_orderedSquare_tendsto k hk) hden
  have hcapacityEventual :
      ∀ᶠ n : ℕ in atTop, 0 < criticalTargetCapacity k n := by
    filter_upwards [eventually_ge_atTop (k - 1)] with n hn
    have hcross := supercriticalTotalCrossCapacity_pos hk
      (supercriticalBalancedDivision hk hn)
    simpa only [criticalTargetCapacity,
      supercriticalBalancedDivision_crossCapacity_eq hk hn] using hcross
  have htarget :
      (gammaK k - 1 / ((k - 1 : ℕ) : ℝ)) /
          (((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) = pK k := by
    calc
      (gammaK k - 1 / ((k - 1 : ℕ) : ℝ)) /
          (((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) =
          (gammaK k * ((k - 1 : ℕ) : ℝ) - 1) /
            ((k - 2 : ℕ) : ℝ) := by
              field_simp [hrPos.ne', hsPos.ne']
      _ = pK k := gammaK_mul_sub_one_div k hk
  rw [← htarget]
  apply hratio.congr'
  filter_upwards [hcapacityEventual,
    eventually_ge_atTop 1] with n hcapacity hn
  have hcapacityReal : (criticalTargetCapacity k n : ℝ) ≠ 0 := by
    exact_mod_cast hcapacity.ne'
  have hnReal : (n : ℝ) ≠ 0 := by positivity
  change
    (2 * (criticalTargetSelectedCount k n : ℝ) / (n : ℝ) ^ 2) /
        (2 * (criticalTargetCapacity k n : ℝ) / (n : ℝ) ^ 2) =
      (criticalTargetSelectedCount k n : ℝ) /
        (criticalTargetCapacity k n : ℝ)
  field_simp [hcapacityReal, hnReal]

/-- A fixed lower compactness endpoint for the critical reference density. -/
def criticalReferenceDensityLower (k : ℕ) : ℝ := pK k / 2

/-- A fixed upper compactness endpoint for the critical reference density. -/
def criticalReferenceDensityUpper (k : ℕ) : ℝ := (pK k + 1) / 2

theorem criticalReferenceDensityLower_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalReferenceDensityLower k := by
  exact div_pos (pK_pos (by omega)) (by norm_num)

theorem criticalReferenceDensityLower_lt_pK
    {k : ℕ} (hk : 3 ≤ k) :
    criticalReferenceDensityLower k < pK k := by
  unfold criticalReferenceDensityLower
  linarith [pK_pos (by omega : 2 ≤ k)]

theorem pK_lt_criticalReferenceDensityUpper
    {k : ℕ} (hk : 3 ≤ k) :
    pK k < criticalReferenceDensityUpper k := by
  unfold criticalReferenceDensityUpper
  linarith [pK_lt_one (by omega : 2 ≤ k)]

theorem criticalReferenceDensityUpper_lt_one
    {k : ℕ} (hk : 3 ≤ k) :
    criticalReferenceDensityUpper k < 1 := by
  unfold criticalReferenceDensityUpper
  linarith [pK_lt_one (by omega : 2 ≤ k)]

/-- The selected density eventually lies in a fixed compact subinterval of
`(0,1)`, with endpoints depending only on `k`. -/
theorem eventually_criticalBalancedSelectedDensity_mem_Icc
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      criticalBalancedSelectedDensity k n ∈
        Set.Icc (criticalReferenceDensityLower k)
          (criticalReferenceDensityUpper k) := by
  have h := criticalBalancedSelectedDensity_tendsto k hk
  filter_upwards [
    (tendsto_order.1 h).1 _ (criticalReferenceDensityLower_lt_pK hk),
    (tendsto_order.1 h).2 _ (pK_lt_criticalReferenceDensityUpper hk)] with
      n hlower hupper
  exact ⟨hlower.le, hupper.le⟩

/-! ## The canonical critical reference fiber -/

/-- The exact critical-edge fiber associated with a displayed ordered
division.  Balance is a hypothesis of the cardinality theorems, not part of
this finite-family definition. -/
noncomputable abbrev criticalBalancedCoPartiteFiber
    {n : ℕ} (k : ℕ) (D : SupercriticalDivision k (Fin n)) :
    Finset (SimpleGraph (Fin n)) :=
  supercriticalCoPartiteFiber D (criticalEdgeCount k n)

/-- The canonical balanced exact-critical-edge fiber.  It is empty only in
the finite initial range where `Fin n` cannot support `k-1` nonempty parts. -/
noncomputable def criticalReferenceFiber
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact if hn : k - 1 ≤ n then
    supercriticalCoPartiteFiber
      (supercriticalBalancedDivision hk hn) (criticalEdgeCount k n)
  else ∅

@[simp] theorem criticalReferenceFiber_eq_of_le
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    criticalReferenceFiber k hk n =
      supercriticalCoPartiteFiber
        (supercriticalBalancedDivision hk hn) (criticalEdgeCount k n) := by
  simp [criticalReferenceFiber, hn]

@[simp] theorem criticalReferenceFiber_eq_empty_of_not_le
    {k n : ℕ} (hk : 3 ≤ k) (hn : ¬k - 1 ≤ n) :
    criticalReferenceFiber k hk n = ∅ := by
  simp [criticalReferenceFiber, hn]

/-- Exact, finite cardinality of the reference fiber before rewriting its
two capacities into the balanced-capacity API. -/
theorem card_criticalReferenceFiber
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    (criticalReferenceFiber k hk n).card =
      if divisionInternalCliqueCapacity
          (supercriticalBalancedDivision hk hn) ≤ criticalEdgeCount k n then
        Nat.choose
          (supercriticalTotalCrossCapacity
            (supercriticalBalancedDivision hk hn))
          (criticalEdgeCount k n - divisionInternalCliqueCapacity
            (supercriticalBalancedDivision hk hn))
      else 0 := by
  rw [criticalReferenceFiber_eq_of_le hk hn,
    card_supercriticalCoPartiteFiber _
      (supercriticalBalancedDivision_isFull hk hn)]

/-- Capacity-normalized exact cardinality of the critical reference fiber. -/
theorem card_criticalReferenceFiber_eq_balanced_choose
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    (criticalReferenceFiber k hk n).card =
      criticalReferenceFiberCard k n := by
  rw [card_criticalReferenceFiber hk hn,
    supercriticalBalancedDivision_internalCapacity_eq hk hn,
    supercriticalBalancedDivision_crossCapacity_eq hk hn]
  rfl

/-- Under the sole lower-feasibility condition, the canonical critical
reference fiber has exactly the advertised binomial size. -/
theorem card_criticalReferenceFiber_eq_criticalReferenceFiberCard
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    (criticalReferenceFiber k hk n).card =
      criticalReferenceFiberCard k n :=
  card_criticalReferenceFiber_eq_balanced_choose hk hn

/-- Every feasible exactly balanced division has the same exact critical
fiber cardinality. -/
theorem card_supercriticalCoPartiteFiber_eq_criticalReferenceFiberCard
    {k n : ℕ} (hk : 3 ≤ k) {D : SupercriticalDivision k (Fin n)}
    (hD : IsExactlyBalancedFullDivision D) :
    (supercriticalCoPartiteFiber D (criticalEdgeCount k n)).card =
      criticalReferenceFiberCard k n := by
  rw [card_supercriticalCoPartiteFiber D hD.1,
    exactlyBalancedDivision_internalCapacity_eq hk hD,
    exactlyBalancedDivision_crossCapacity_eq hk hD]
  rfl

/-- Balanced-fiber spelling of the common exact critical cardinality. -/
theorem card_criticalBalancedCoPartiteFiber_eq_criticalReferenceFiberCard
    {k n : ℕ} (hk : 3 ≤ k) {D : SupercriticalDivision k (Fin n)}
    (hD : IsExactlyBalancedFullDivision D) :
    (criticalBalancedCoPartiteFiber k D).card =
      criticalReferenceFiberCard k n :=
  card_supercriticalCoPartiteFiber_eq_criticalReferenceFiberCard
    hk hD

/-- The balanced internal clique budget is eventually feasible at the
critical edge count. -/
theorem eventually_balancedInternalCapacity_le_criticalEdgeCount
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
        criticalEdgeCount k n := by
  have hfeasible := eventually_balancedDivision_internal_le_of_density_gt
    k hk (gammaK k) (one_div_parts_lt_gammaK hk)
      (criticalEdgeCount k) (criticalEdgeCount_hasAsymptoticEdgeDensity hk)
  filter_upwards [hfeasible, eventually_ge_atTop (k - 1)] with n hfeasible hn
  simpa only [supercriticalBalancedDivision_internalCapacity_eq hk hn] using
    hfeasible hn

/-- Eventually the selected coordinate count lies within the balanced cross
capacity. -/
theorem eventually_criticalTargetSelectedCount_le_capacity
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      criticalTargetSelectedCount k n ≤ criticalTargetCapacity k n := by
  filter_upwards [eventually_balancedInternalCapacity_le_criticalEdgeCount k hk]
    with n hfeasible
  have htotal := DenseGraph.balancedCross_add_internal (k - 1) n
  have hm := criticalEdgeCount_le_completeEdgeCount hk n
  unfold completeEdgeCount at hm
  simp only [criticalTargetSelectedCount, criticalTargetCapacity]
  omega

/-- The balanced cross-coordinate universe is eventually nonempty. -/
theorem eventually_criticalTargetCapacity_pos
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, 0 < criticalTargetCapacity k n := by
  filter_upwards [eventually_ge_atTop (k - 1)] with n hn
  have hcross := supercriticalTotalCrossCapacity_pos hk
    (supercriticalBalancedDivision hk hn)
  simpa only [criticalTargetCapacity,
    supercriticalBalancedDivision_crossCapacity_eq hk hn] using hcross

/-- Since the limiting selected density is `pK k > 0`, the critical target
selects at least one cross edge for all sufficiently large orders. -/
theorem eventually_criticalTargetSelectedCount_pos
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, 0 < criticalTargetSelectedCount k n := by
  have hpositiveDensity :
      ∀ᶠ n : ℕ in atTop, 0 < criticalBalancedSelectedDensity k n :=
    (tendsto_order.1 (criticalBalancedSelectedDensity_tendsto k hk)).1
      0 (pK_pos (by omega))
  filter_upwards [hpositiveDensity] with n hn
  apply Nat.pos_of_ne_zero
  intro hzero
  simp [criticalBalancedSelectedDensity, hzero] at hn

/-- Since the limiting selected density is strictly below one, the target
eventually leaves at least one cross coordinate unselected. -/
theorem eventually_criticalTargetSelectedCount_lt_capacity
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      criticalTargetSelectedCount k n < criticalTargetCapacity k n := by
  have hbelow :
      ∀ᶠ n : ℕ in atTop, criticalBalancedSelectedDensity k n < 1 :=
    (tendsto_order.1 (criticalBalancedSelectedDensity_tendsto k hk)).2
      1 (pK_lt_one (by omega))
  filter_upwards [hbelow, eventually_criticalTargetCapacity_pos k hk] with
      n hbelow hcapacity
  have hcapacityReal : (0 : ℝ) < criticalTargetCapacity k n := by
    exact_mod_cast hcapacity
  rw [criticalBalancedSelectedDensity, div_lt_one hcapacityReal] at hbelow
  exact_mod_cast hbelow

/-- Eventual strict feasibility of the critical binomial slice. -/
theorem eventually_criticalTargetSelectedCount_mem_Ioo
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      criticalTargetSelectedCount k n ∈
        Set.Ioo 0 (criticalTargetCapacity k n) := by
  filter_upwards [eventually_criticalTargetSelectedCount_pos k hk,
    eventually_criticalTargetSelectedCount_lt_capacity k hk] with n hpos hlt
  exact ⟨hpos, hlt⟩

/-- The canonical reference fiber has its exact binomial cardinality for all
sufficiently large orders. -/
theorem eventually_card_criticalReferenceFiber_eq
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      (criticalReferenceFiber k hk n).card = criticalReferenceFiberCard k n := by
  filter_upwards [eventually_ge_atTop (k - 1),
    eventually_balancedInternalCapacity_le_criticalEdgeCount k hk] with
      n hn hfeasible
  exact card_criticalReferenceFiber_eq_criticalReferenceFiberCard hk hn

/-- Eventual positivity of the closed-form critical reference fiber count. -/
theorem eventually_criticalReferenceFiberCard_pos
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, 0 < criticalReferenceFiberCard k n := by
  filter_upwards [eventually_balancedInternalCapacity_le_criticalEdgeCount k hk,
    eventually_criticalTargetSelectedCount_le_capacity k hk] with
      n hfeasible hselected
  rw [criticalReferenceFiberCard_eq_choose_of_feasible hfeasible]
  exact Nat.choose_pos hselected

/-- The reference fiber is a subfamily of the global critical
co-`(k-1)`-partite family. -/
theorem criticalReferenceFiber_subset_coMultipartite
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) :
    criticalReferenceFiber k hk n ⊆
      coMultipartiteGraphFinsetWithEdges (k - 1) n
        (criticalEdgeCount k n) := by
  intro G hG
  by_cases hn : k - 1 ≤ n
  · rw [criticalReferenceFiber_eq_of_le hk hn] at hG
    exact supercriticalCoPartiteFiber_subset_global _ hG
  · rw [criticalReferenceFiber_eq_empty_of_not_le hk hn] at hG
    simp at hG

/-- At the critical density, the canonical balanced reference fiber is
eventually nonempty. -/
theorem eventually_criticalReferenceFiber_nonempty
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n in atTop, (criticalReferenceFiber k hk n).Nonempty := by
  have href := eventually_supercriticalBalancedFiber_nonempty
    k hk (gammaK k) ⟨one_div_parts_lt_gammaK hk, gammaK_lt_one hk⟩
    (criticalEdgeCount k) (criticalEdgeCount_hasAsymptoticEdgeDensity hk)
  filter_upwards [href] with n hnref
  obtain ⟨hn, hfiber⟩ := hnref
  simpa [criticalReferenceFiber, hn] using hfiber

/-- Eventual positivity of the exact critical reference count. -/
theorem eventually_card_criticalReferenceFiber_pos
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n in atTop, 0 < (criticalReferenceFiber k hk n).card := by
  filter_upwards [eventually_criticalReferenceFiber_nonempty k hk] with n hn
  exact Finset.card_pos.mpr hn

/-! ## Exactly balanced critical cover pairs -/

/-- Pairs consisting of an exactly balanced ordered division and a graph in
its exact critical co-multipartite fiber. -/
noncomputable def criticalBalancedCoverPairFinset
    (k n : ℕ) :
    Finset (SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)) :=
  (exactlyBalancedFullSupercriticalDivisions k n).biUnion fun D ↦
    (supercriticalCoPartiteFiber D (criticalEdgeCount k n)).image
      fun G ↦ (D, G)

@[simp] theorem mem_criticalBalancedCoverPairFinset
    {k n : ℕ}
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)} :
    p ∈ criticalBalancedCoverPairFinset k n ↔
      IsExactlyBalancedFullDivision p.1 ∧
        p.2 ∈ supercriticalCoPartiteFiber p.1
          (criticalEdgeCount k n) := by
  classical
  constructor
  · intro hp
    rw [criticalBalancedCoverPairFinset, Finset.mem_biUnion] at hp
    obtain ⟨D, hD, hp⟩ := hp
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨mem_exactlyBalancedFullSupercriticalDivisions.mp hD, hG⟩
  · rintro ⟨hD, hG⟩
    rw [criticalBalancedCoverPairFinset, Finset.mem_biUnion]
    exact ⟨p.1, mem_exactlyBalancedFullSupercriticalDivisions.mpr hD,
      Finset.mem_image.mpr ⟨p.2, hG, Prod.eta p⟩⟩

/-- Exact dependent-sum formula for critical balanced cover pairs. -/
theorem card_criticalBalancedCoverPairFinset (k n : ℕ) :
    (criticalBalancedCoverPairFinset k n).card =
      ∑ D ∈ exactlyBalancedFullSupercriticalDivisions k n,
        (supercriticalCoPartiteFiber D (criticalEdgeCount k n)).card := by
  classical
  rw [criticalBalancedCoverPairFinset, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro D _hD
    rw [Finset.card_image_iff.mpr]
    intro G _ H _ h
    exact Prod.mk.inj h |>.2
  · intro D _hD E _hE hDE
    change Disjoint
      ((supercriticalCoPartiteFiber D (criticalEdgeCount k n)).image
        fun G ↦ (D, G))
      ((supercriticalCoPartiteFiber E (criticalEdgeCount k n)).image
        fun G ↦ (E, G))
    rw [Finset.disjoint_left]
    rintro p hpD hpE
    obtain ⟨G, _, rfl⟩ := Finset.mem_image.mp hpD
    obtain ⟨H, _, heq⟩ := Finset.mem_image.mp hpE
    exact hDE (Prod.mk.inj heq.symm).1

/-- Once the critical internal budget is feasible, every summand in the
balanced cover-pair count is the same exact binomial fiber size. -/
theorem card_criticalBalancedCoverPairFinset_eq_mul
    {k n : ℕ} (hk : 3 ≤ k) :
    (criticalBalancedCoverPairFinset k n).card =
      (exactlyBalancedFullSupercriticalDivisions k n).card *
        criticalReferenceFiberCard k n := by
  rw [card_criticalBalancedCoverPairFinset]
  calc
    (∑ D ∈ exactlyBalancedFullSupercriticalDivisions k n,
        (supercriticalCoPartiteFiber D (criticalEdgeCount k n)).card) =
        ∑ _D ∈ exactlyBalancedFullSupercriticalDivisions k n,
          criticalReferenceFiberCard k n := by
      apply Finset.sum_congr rfl
      intro D hD
      exact card_supercriticalCoPartiteFiber_eq_criticalReferenceFiberCard hk
        (mem_exactlyBalancedFullSupercriticalDivisions.mp hD)
    _ = (exactlyBalancedFullSupercriticalDivisions k n).card *
        criticalReferenceFiberCard k n := by simp

/-- Eventual exact product formula for critical balanced cover pairs. -/
theorem eventually_card_criticalBalancedCoverPairFinset_eq_mul
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      (criticalBalancedCoverPairFinset k n).card =
        (exactlyBalancedFullSupercriticalDivisions k n).card *
          criticalReferenceFiberCard k n := by
  exact Eventually.of_forall fun _n ↦
    card_criticalBalancedCoverPairFinset_eq_mul hk

/-! ## Comparison with the permanent balanced-cover family -/

/-- Every canonical balanced part has real cardinality within one of the
common average. -/
theorem abs_card_balancedFinPartition_sub_average_le_one
    {r n : ℕ} (hr : 0 < r) (i : Fin r) :
    |((DenseGraph.balancedFinPartition r n i).card : ℝ) -
        (n : ℝ) / (r : ℝ)| ≤ 1 := by
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hfloor : ((n / r : ℕ) : ℝ) ≤ (n : ℝ) / (r : ℝ) := by
    rw [le_div_iff₀ hrReal]
    exact_mod_cast Nat.div_mul_le_self n r
  have hceil : (n : ℝ) / (r : ℝ) < ((n / r : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hrReal]
    have hnat : n < (n / r + 1) * r :=
      (Nat.div_lt_iff_lt_mul hr).mp (Nat.lt_succ_self (n / r))
    exact_mod_cast hnat
  rw [DenseGraph.card_balancedFinPartition hr]
  split_ifs <;> rw [abs_le] <;> constructor <;> norm_num <;> linarith

/-- For large `n`, exact balance implies the fixed real balance window used
by the cover-multiplicity theorem. -/
theorem eventually_exactlyBalanced_isBalancedFullDivision
    {k : ℕ} (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ∀ D : SupercriticalDivision k (Fin n),
      IsExactlyBalancedFullDivision D →
        IsBalancedFullDivision D (supercriticalCoverBalanceRadius k) := by
  have hr : 0 < k - 1 := by omega
  filter_upwards [eventually_ge_atTop (8 * (k - 1))] with n hn D hD
  refine ⟨hD.1, ?_⟩
  intro i
  rw [hD.2 i]
  calc
    |((DenseGraph.balancedFinPartition (k - 1) n i).card : ℝ) -
        (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ 1 :=
      abs_card_balancedFinPartition_sub_average_le_one hr i
    _ ≤ supercriticalCoverBalanceRadius k * n := by
      rw [supercriticalCoverBalanceRadius]
      have hden : (0 : ℝ) < 8 * ((k - 1 : ℕ) : ℝ) := by positivity
      rw [one_div]
      calc
        (1 : ℝ) = (8 * ((k - 1 : ℕ) : ℝ))⁻¹ *
            (8 * ((k - 1 : ℕ) : ℝ)) := by field_simp
        _ ≤ (8 * ((k - 1 : ℕ) : ℝ))⁻¹ * n := by
          apply mul_le_mul_of_nonneg_left
          · exact_mod_cast hn
          · exact (inv_nonneg.mpr hden.le)

/-- Eventually every exactly balanced critical cover pair is also a member
of the permanent balanced-cover family. -/
theorem eventually_criticalBalancedCoverPairFinset_subset
    {k : ℕ} (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      criticalBalancedCoverPairFinset k n ⊆
        balancedCoMultipartiteCoverPairFinset k n (criticalEdgeCount k n)
          (supercriticalCoverBalanceRadius k) := by
  filter_upwards [eventually_exactlyBalanced_isBalancedFullDivision hk] with
    n hbalanced
  intro p hp
  rw [mem_criticalBalancedCoverPairFinset] at hp
  rw [mem_balancedCoMultipartiteCoverPairFinset]
  exact ⟨hbalanced p.1 hp.1, hp.2⟩

/-- A fixed density just above the phase boundary, used only to invoke the
open-supercritical cover-multiplicity estimate at the endpoint. -/
def criticalCoverComparisonDensity (k : ℕ) : ℝ :=
  gammaK k + (1 - gammaK k) / 4

theorem criticalCoverComparisonDensity_mem_Ioo
    {k : ℕ} (hk : 3 ≤ k) :
    criticalCoverComparisonDensity k ∈ Set.Ioo (gammaK k) 1 := by
  unfold criticalCoverComparisonDensity
  constructor <;> linarith [gammaK_lt_one hk]

/-- The critical density itself lies strictly within the cover theorem's
density window centered at the comparison density. -/
theorem criticalDensity_mem_coverComparison_window
    {k : ℕ} (hk : 3 ≤ k) :
    |gammaK k - criticalCoverComparisonDensity k| <
      supercriticalCoverDensityTolerance
        (criticalCoverComparisonDensity k) := by
  have hle : gammaK k - criticalCoverComparisonDensity k ≤ 0 := by
    unfold criticalCoverComparisonDensity
    linarith [gammaK_lt_one hk]
  rw [abs_of_nonpos hle]
  unfold criticalCoverComparisonDensity supercriticalCoverDensityTolerance
  linarith [gammaK_lt_one hk]

/-- The exact critical edge-density sequence is eventually in the comparison
window used by the open-supercritical cover theorem. -/
theorem eventually_criticalEdgeDensity_mem_coverComparison_window
    {k : ℕ} (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      |(criticalEdgeCount k n : ℝ) / (completeEdgeCount n : ℝ) -
          criticalCoverComparisonDensity k| <
        supercriticalCoverDensityTolerance
          (criticalCoverComparisonDensity k) := by
  let gap : ℝ :=
    supercriticalCoverDensityTolerance (criticalCoverComparisonDensity k) -
      |gammaK k - criticalCoverComparisonDensity k|
  have hgap : 0 < gap := sub_pos.mpr
    (criticalDensity_mem_coverComparison_window hk)
  have hdensity := criticalEdgeCount_hasAsymptoticEdgeDensity hk
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdensity gap hgap
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnear :
      |(criticalEdgeCount k n : ℝ) / (completeEdgeCount n : ℝ) -
        gammaK k| < gap := by
    simpa only [Real.dist_eq] using hN n hn
  calc
    |(criticalEdgeCount k n : ℝ) / (completeEdgeCount n : ℝ) -
        criticalCoverComparisonDensity k| =
      |((criticalEdgeCount k n : ℝ) / (completeEdgeCount n : ℝ) -
          gammaK k) +
        (gammaK k - criticalCoverComparisonDensity k)| := by ring_nf
    _ ≤
        |(criticalEdgeCount k n : ℝ) / (completeEdgeCount n : ℝ) -
          gammaK k| +
        |gammaK k - criticalCoverComparisonDensity k| := abs_add_le _ _
    _ < gap + |gammaK k - criticalCoverComparisonDensity k| := by
      gcongr
    _ = supercriticalCoverDensityTolerance
        (criticalCoverComparisonDensity k) := by
      dsimp [gap]
      linarith

/-- Endpoint critical balanced-cover comparison.  The proof invokes the
open-supercritical theorem at a fixed nearby density and uses convergence of
the exact critical edge sequence into its density window. -/
theorem eventually_card_criticalBalancedCoverPairFinset_le
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      ((criticalBalancedCoverPairFinset k n).card : ℝ) ≤
        (2 * (k - 1).factorial : ℕ) *
          (coMultipartiteGraphCountWithEdges (k - 1) n
            (criticalEdgeCount k n) : ℝ) := by
  have hcomparison :=
    eventually_card_balancedCoMultipartiteCoverPairFinset_le hk
      (criticalCoverComparisonDensity k)
      (criticalCoverComparisonDensity_mem_Ioo hk)
  filter_upwards [hcomparison,
    eventually_criticalEdgeDensity_mem_coverComparison_window hk,
    eventually_criticalBalancedCoverPairFinset_subset hk] with
      n hcomparison hdensity hsubset
  calc
    ((criticalBalancedCoverPairFinset k n).card : ℝ) ≤
        ((balancedCoMultipartiteCoverPairFinset k n (criticalEdgeCount k n)
          (supercriticalCoverBalanceRadius k)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ (2 * (k - 1).factorial : ℕ) *
        (coMultipartiteGraphCountWithEdges (k - 1) n
          (criticalEdgeCount k n) : ℝ) :=
      hcomparison (criticalEdgeCount k n) hdensity

/-- Public critical-endpoint spelling of the balanced cover-pair upper
comparison. -/
theorem eventually_criticalBalancedCoverPair_le
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      ((criticalBalancedCoverPairFinset k n).card : ℝ) ≤
        (2 * (k - 1).factorial : ℕ) *
          (coMultipartiteGraphCountWithEdges (k - 1) n
            (criticalEdgeCount k n) : ℝ) :=
  eventually_card_criticalBalancedCoverPairFinset_le k hk

/-- Lower-bound form of the endpoint cover-pair comparison. -/
theorem eventually_criticalCoMultipartiteCount_lower_coverPairs
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      ((∑ D ∈ exactlyBalancedFullSupercriticalDivisions k n,
          (supercriticalCoPartiteFiber D
            (criticalEdgeCount k n)).card : ℕ) : ℝ) /
          (2 * (k - 1).factorial : ℕ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n
          (criticalEdgeCount k n) : ℝ) := by
  have hfactor : (0 : ℝ) < (2 * (k - 1).factorial : ℕ) := by
    positivity
  filter_upwards [eventually_card_criticalBalancedCoverPairFinset_le k hk] with
    n hn
  rw [div_le_iff₀ hfactor]
  simpa [card_criticalBalancedCoverPairFinset, mul_comm] using hn

/-- The balanced-assignment lower bound and the endpoint cover-multiplicity
upper bound combine to compare the canonical critical binomial fiber with the
whole exact-edge co-multipartite family.  The only loss is the explicit
polynomial factor `(n+1)^(k-1)` and the permanent ordered-cover constant. -/
theorem
    eventually_criticalReferenceFiberCard_mul_pow_le_coMultipartiteCount_mul_poly
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      ((k - 1 : ℕ) : ℝ) ^ n * (criticalReferenceFiberCard k n : ℝ) ≤
        ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
          (2 * (k - 1).factorial : ℕ) *
            (coMultipartiteGraphCountWithEdges (k - 1) n
              (criticalEdgeCount k n) : ℝ) := by
  filter_upwards [
    eventually_pow_le_succ_pow_mul_card_exactlyBalancedDivisions k hk,
    eventually_criticalBalancedCoverPair_le k hk] with n hdiv hcover
  have hdivReal :
      ((k - 1 : ℕ) : ℝ) ^ n ≤
        ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
          ((exactlyBalancedFullSupercriticalDivisions k n).card : ℝ) := by
    exact_mod_cast hdiv
  calc
    ((k - 1 : ℕ) : ℝ) ^ n * (criticalReferenceFiberCard k n : ℝ) ≤
        (((n + 1 : ℕ) : ℝ) ^ (k - 1) *
          ((exactlyBalancedFullSupercriticalDivisions k n).card : ℝ)) *
            (criticalReferenceFiberCard k n : ℝ) :=
      mul_le_mul_of_nonneg_right hdivReal (by positivity)
    _ = ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
        ((criticalBalancedCoverPairFinset k n).card : ℝ) := by
      rw [card_criticalBalancedCoverPairFinset_eq_mul hk]
      push_cast
      ring
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
        ((2 * (k - 1).factorial : ℕ) *
          (coMultipartiteGraphCountWithEdges (k - 1) n
            (criticalEdgeCount k n) : ℝ)) :=
      mul_le_mul_of_nonneg_left hcover (by positivity)
    _ = ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
          (2 * (k - 1).factorial : ℕ) *
            (coMultipartiteGraphCountWithEdges (k - 1) n
              (criticalEdgeCount k n) : ℝ) := by ring

/-- Concise public spelling of the critical co-multipartite reference lower
bound. -/
theorem eventually_criticalCoMultipartiteCount_lower
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      ((k - 1 : ℕ) : ℝ) ^ n * (criticalReferenceFiberCard k n : ℝ) ≤
        ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
          (2 * (k - 1).factorial : ℕ) *
            (coMultipartiteGraphCountWithEdges (k - 1) n
              (criticalEdgeCount k n) : ℝ) :=
  eventually_criticalReferenceFiberCard_mul_pow_le_coMultipartiteCount_mul_poly
    k hk

end InducedStars
