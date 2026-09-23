import DenseGraph.Combinatorics.BinomialCapacity
import DenseGraph.Combinatorics.GaussianLattice
import DenseGraph.FiniteModels.PartitionImbalance
import InducedStars.Structure.Critical.CanonicalSparse
import InducedStars.Structure.Critical.DivisionCounting
import InducedStars.Structure.Critical.FineBalanceDensity
import Mathlib.Tactic

/-!
# Fine balance of critical clean divisions

This file supplies the finite counting core of the general-`k` exact-critical
fixed-sparse fine-balance theorem.
For a fixed sparse set and fixed sparse induced graph, ordered displayed
cover slices are grouped by the vector of main-part sizes.  Moving mass from
a largest part to a smallest part gives a quadratic loss in multipartite
capacity, and an exact binomial comparison turns that loss into a Gaussian
weight.  The separate canonical-cover and denominator comparison modules
turn this displayed-cover estimate into the canonical fixed-sparse
almost-all assertion.

The argument is local and finite.  In particular, the unpublished
claw-free calculation is not used as an assumption.
-/

noncomputable section

open Filter Finset Set Topology
open scoped BigOperators


namespace InducedStars

noncomputable local instance criticalFineBalanceGraphDecidableEq
    (n : ℕ) : DecidableEq (SimpleGraph (Fin n)) :=
  Classical.decEq _

/-! ## Size vectors and their range -/

/-- The ordered main-part size vector of a division. -/
def criticalMainPartSizeVector {k n : ℕ}
    (D : SupercriticalDivision k (Fin n)) : Fin (k - 1) → ℕ :=
  fun i ↦ (D.parts i).card

/-- The range `max_i |P_i| - min_i |P_i|` of the main-part size vector.
The explicit positivity argument is harmless because this quantity is used
only for `k ≥ 3`. -/
def criticalMainPartSizeRange {k n : ℕ} (hk : 3 ≤ k)
    (D : SupercriticalDivision k (Fin n)) : ℕ :=
  DenseGraph.sizeVectorRange (by omega : 0 < k - 1)
    (criticalMainPartSizeVector D)

/-- The literal paper cutoff: every pair of main-part sizes differs by at
most `sqrt (log₂ n)`. -/
def IsCriticalFineBalanced {k n : ℕ} (hk : 3 ≤ k)
    (D : SupercriticalDivision k (Fin n)) : Prop :=
  (criticalMainPartSizeRange hk D : ℝ) ≤
    Real.sqrt (Real.logb 2 (n : ℝ))

/-- `IsCriticalFineBalanced` is exactly the paper's pairwise condition:
every two displayed main parts differ in size by at most
`sqrt (log₂ n)`. -/
theorem isCriticalFineBalanced_iff_pairwise_card_sub_le
    {k n : ℕ} (hk : 3 ≤ k)
    (D : SupercriticalDivision k (Fin n)) :
    IsCriticalFineBalanced hk D ↔
      ∀ i j : Fin (k - 1),
        |((D.parts i).card : ℝ) - ((D.parts j).card : ℝ)| ≤
          Real.sqrt (Real.logb 2 (n : ℝ)) := by
  simpa [IsCriticalFineBalanced, criticalMainPartSizeRange,
    criticalMainPartSizeVector] using
      (DenseGraph.sizeVectorRange_cast_le_iff_pairwise_abs_sub_le
        (by omega : 0 < k - 1) (criticalMainPartSizeVector D)
        (Real.sqrt (Real.logb 2 (n : ℝ))))

instance {k n : ℕ} (hk : 3 ≤ k) (D : SupercriticalDivision k (Fin n)) :
    Decidable (IsCriticalFineBalanced hk D) :=
  Classical.propDecidable _

/-! ## The fixed-sparse-set canonical family -/

/-- Divisions having one prescribed sparse set. -/
noncomputable def criticalDivisionsWithSparseSet
    (k n : ℕ) (S : Finset (Fin n)) :
    Finset (SupercriticalDivision k (Fin n)) :=
  (allSupercriticalDivisions k n).filter fun D ↦ D.sparse = S

@[simp] theorem mem_criticalDivisionsWithSparseSet
    {k n : ℕ} {S : Finset (Fin n)}
    {D : SupercriticalDivision k (Fin n)} :
    D ∈ criticalDivisionsWithSparseSet k n S ↔ D.sparse = S := by
  classical
  simp [criticalDivisionsWithSparseSet]

/-- The canonical clean graphs with prescribed sparse set whose canonical
division is not fine-balanced.  The union is disjoint because the division
stored in every clean fiber is the canonical one. -/
noncomputable def criticalFixedSparseUnbalancedCleanGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n)) : Finset (SimpleGraph (Fin n)) :=
  ((criticalDivisionsWithSparseSet k n S).filter fun D ↦
      ¬ IsCriticalFineBalanced hk D).biUnion fun D ↦
    criticalCleanDivisionGraphFinset k hk n tau hn D

/-- Cardinality of the fixed-sparse-set, fine-unbalanced canonical clean
family. -/
def criticalFixedSparseUnbalancedCleanTotal
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n)) : ℕ :=
  (criticalFixedSparseUnbalancedCleanGraphFinset k hk n tau hn S).card

/-! ## The exact capacity penalty on one canonical clean fiber -/

/-- Gaussian rate produced by the uniform critical missing-coordinate
density and the elementary range-smoothing inequality. -/
noncomputable def criticalFineBalanceGaussianRate (k : ℕ) : ℝ :=
  criticalFineBalanceMissingDensity k / 9

theorem criticalFineBalanceGaussianRate_pos
    {k : ℕ} (hk : 3 ≤ k) : 0 < criticalFineBalanceGaussianRate k := by
  unfold criticalFineBalanceGaussianRate
  positivity [criticalFineBalanceMissingDensity_pos hk]

/-! ## Fixed sparse-graph cross-coordinate parameters -/

/-- After fixing the graph induced by a sparse set of size `s` and with `t`
edges, this is the number of *missing cross coordinates*.  It is independent
of the ordered main-part sizes.  Natural subtraction is the intended guard
outside the feasible range. -/
def criticalFixedSparseCrossMissingCount
    (k n s t : ℕ) : ℕ :=
  Nat.choose (n - s) 2 + t - criticalEdgeCount k n

/-- A uniform lower density of missing cross coordinates after the sparse
induced graph itself has been fixed. -/
noncomputable def criticalFineBalanceCrossMissingDensity (k : ℕ) : ℝ :=
  (1 - gammaK k) / 16

theorem criticalFineBalanceCrossMissingDensity_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalFineBalanceCrossMissingDensity k := by
  unfold criticalFineBalanceCrossMissingDensity
  positivity [gammaK_lt_one hk]

/-- The Gaussian coefficient for the fixed-sparse-graph calculation. -/
noncomputable def criticalFineBalanceCrossGaussianRate (k : ℕ) : ℝ :=
  criticalFineBalanceCrossMissingDensity k / 9

theorem criticalFineBalanceCrossGaussianRate_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalFineBalanceCrossGaussianRate k := by
  unfold criticalFineBalanceCrossGaussianRate
  positivity [criticalFineBalanceCrossMissingDensity_pos hk]

/-- Uniform missing-density bound for the literal fixed-sparse-graph cross
slice.  The estimate is uniform in the edge level `t`; only nonnegativity of
`t` is used. -/
theorem criticalFineBalanceCrossMissingDensity_mul_capacity_le
    {k n s t : ℕ} (hk : 3 ≤ k) (hn : 2 ≤ n) (hs : s ≤ n)
    (hsSmall : (s : ℝ) ≤
      criticalFineBalanceSparseFraction k * (n : ℝ)) :
    criticalFineBalanceCrossMissingDensity k *
        (DenseGraph.balancedMultipartiteCrossCapacity
          (k - 1) (n - s) : ℝ) ≤
      (criticalFixedSparseCrossMissingCount k n s t : ℝ) := by
  let a : ℝ := 1 - gammaK k
  let C : ℕ := Nat.choose n 2
  let Q : ℕ := Nat.choose (n - s) 2
  let R : ℕ := (n - s) * s + Nat.choose s 2
  let T : ℕ := Q + t
  let B : ℕ := DenseGraph.balancedMultipartiteCrossCapacity
    (k - 1) (n - s)
  have ha : 0 < a := by
    dsimp [a]
    exact sub_pos.mpr (gammaK_lt_one hk)
  have haLe : a ≤ 1 := by
    dsimp [a]
    linarith [gammaK_pos hk]
  have hsReal : (s : ℝ) ≤ (n : ℝ) := by exact_mod_cast hs
  have hnReal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnNonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hsNonneg : (0 : ℝ) ≤ (s : ℝ) := by positivity
  have hqLe : ((n - s : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n s
  have hsSmall' : (s : ℝ) ≤ a / 16 * (n : ℝ) := by
    simpa [criticalFineBalanceSparseFraction, a] using hsSmall
  have hsn : (s : ℝ) * (n : ℝ) ≤ a / 16 * (n : ℝ) ^ 2 := by
    calc
      (s : ℝ) * (n : ℝ) ≤ (a / 16 * (n : ℝ)) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hsSmall' hnNonneg
      _ = a / 16 * (n : ℝ) ^ 2 := by ring
  have hcrossLoss : (((n - s) * s : ℕ) : ℝ) ≤
      a / 16 * (n : ℝ) ^ 2 := by
    calc
      (((n - s) * s : ℕ) : ℝ) =
          (s : ℝ) * ((n - s : ℕ) : ℝ) := by
        push_cast
        ring
      _ ≤ (s : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hqLe hsNonneg
      _ ≤ a / 16 * (n : ℝ) ^ 2 := hsn
  have hchooseS : (Nat.choose s 2 : ℝ) ≤
      a / 32 * (n : ℝ) ^ 2 := by
    rw [Nat.cast_choose_two]
    have hsSq : (s : ℝ) ^ 2 ≤ (s : ℝ) * (n : ℝ) := by
      nlinarith
    calc
      (s : ℝ) * ((s : ℝ) - 1) / 2 ≤ (s : ℝ) ^ 2 / 2 := by
        nlinarith
      _ ≤ ((s : ℝ) * (n : ℝ)) / 2 := by nlinarith
      _ ≤ (a / 16 * (n : ℝ) ^ 2) / 2 := by nlinarith
      _ = a / 32 * (n : ℝ) ^ 2 := by ring
  have hRfirst : (R : ℝ) ≤ 3 * a / 32 * (n : ℝ) ^ 2 := by
    dsimp [R]
    push_cast
    nlinarith [hcrossLoss, hchooseS]
  have hCformula : (C : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    simp [C, Nat.cast_choose_two]
  have hsquare : (n : ℝ) ^ 2 / 4 ≤ (C : ℝ) := by
    rw [hCformula]
    nlinarith
  have hRbound : (R : ℝ) ≤ 3 * a / 8 * (C : ℝ) := by
    calc
      (R : ℝ) ≤ 3 * a / 32 * (n : ℝ) ^ 2 := hRfirst
      _ = (3 * a / 8) * ((n : ℝ) ^ 2 / 4) := by ring
      _ ≤ (3 * a / 8) * (C : ℝ) :=
        mul_le_mul_of_nonneg_left hsquare (by positivity)
  have hdecompNat : C = Q + R := by
    have hadd := DenseGraph.choose_two_add (n - s) s
    rw [Nat.sub_add_cancel hs] at hadd
    dsimp [C, Q, R]
    omega
  have hdecomp : (C : ℝ) = (Q : ℝ) + (R : ℝ) := by
    exact_mod_cast hdecompNat
  have hTgeQ : (Q : ℝ) ≤ (T : ℝ) := by
    dsimp [T]
    push_cast
    exact le_add_of_nonneg_right (Nat.cast_nonneg t)
  have hBq : B ≤ Q := by
    have htotal := DenseGraph.balancedCross_add_internal
      (k - 1) (n - s)
    dsimp [B, Q] at htotal ⊢
    omega
  have hBC : (B : ℝ) ≤ (C : ℝ) := by
    have hBQ : (B : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hBq
    linarith
  have hgap : a / 16 * (B : ℝ) ≤
      (T : ℝ) - gammaK k * (C : ℝ) := by
    have hCnonneg : (0 : ℝ) ≤ (C : ℝ) := by positivity
    have hmain : 5 * a / 8 * (C : ℝ) ≤
        (T : ℝ) - gammaK k * (C : ℝ) := by
      dsimp [a]
      nlinarith
    have hsmall : a / 16 * (B : ℝ) ≤ 5 * a / 8 * (C : ℝ) := by
      have := mul_le_mul_of_nonneg_left hBC ha.le
      nlinarith
    exact hsmall.trans hmain
  have hedgeReal : (criticalEdgeCount k n : ℝ) ≤ (T : ℝ) := by
    have htarget : (criticalEdgeCount k n : ℝ) ≤
        gammaK k * (C : ℝ) := by
      simpa [C, completeEdgeCount] using criticalEdgeCount_cast_le hk n
    have hgapNonneg : 0 ≤ a / 16 * (B : ℝ) := by positivity
    linarith
  have hedgeNat : criticalEdgeCount k n ≤ T := by exact_mod_cast hedgeReal
  have hedgeNat' : criticalEdgeCount k n ≤ Nat.choose (n - s) 2 + t := by
    simpa [T, Q] using hedgeNat
  have hmissingCast :
      (criticalFixedSparseCrossMissingCount k n s t : ℝ) =
        (T : ℝ) - (criticalEdgeCount k n : ℝ) := by
    rw [criticalFixedSparseCrossMissingCount, Nat.cast_sub hedgeNat']
  rw [hmissingCast]
  simpa [criticalFineBalanceCrossMissingDensity, a, C, B] using
    hgap.trans (sub_le_sub_left (by
      simpa [C, completeEdgeCount] using criticalEdgeCount_cast_le hk n) (T : ℝ))

/-- Exact Gaussian comparison for one fixed-sparse-graph cross slice and one
ordered main-part size vector.  Infeasible slices vanish automatically. -/
theorem criticalFixedSparseCrossSlice_le_fineBalanceWeight
    {k n s t : ℕ} (hk : 3 ≤ k) (hn : 2 ≤ n) (hs : s ≤ n)
    (hsSmall : (s : ℝ) ≤
      criticalFineBalanceSparseFraction k * (n : ℝ))
    (a : Fin (k - 1) → ℕ) (hsum : ∑ i, a i = n - s)
    (hrange : 2 ≤ DenseGraph.sizeVectorRange
      (by omega : 0 < k - 1) a) :
    (Nat.choose (DenseGraph.multipartiteCrossCapacity a)
        (criticalFixedSparseCrossMissingCount k n s t) : ℝ) ≤
      (Nat.choose
          (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) (n - s))
          (criticalFixedSparseCrossMissingCount k n s t) : ℝ) *
        Real.exp (-(criticalFineBalanceCrossGaussianRate k *
          (DenseGraph.sizeVectorRange
            (by omega : 0 < k - 1) a : ℝ) ^ 2)) := by
  let A := DenseGraph.multipartiteCrossCapacity a
  let B := DenseGraph.balancedMultipartiteCrossCapacity (k - 1) (n - s)
  let z := criticalFixedSparseCrossMissingCount k n s t
  let d := DenseGraph.sizeVectorRange (by omega : 0 < k - 1) a
  by_cases hzA : z ≤ A
  · have hAB : A ≤ B := by
      dsimp [A, B]
      simpa [hsum] using DenseGraph.multipartiteCrossCapacity_le_balanced a
    have hgapNat := DenseGraph.sizeVectorRange_sq_le_nine_mul_balancedCross_gap
      (by omega : 0 < k - 1) a hsum hrange
    have hBpos : 0 < B := by
      by_contra hnot
      have hBzero : B = 0 := Nat.eq_zero_of_not_pos hnot
      have hAzero : A = 0 := by omega
      have hdSqPos : 0 < d ^ 2 := by
        apply pow_pos
        dsimp [d]
        omega
      dsimp [A, B, d] at hgapNat hAzero hBzero ⊢
      dsimp [d] at hdSqPos
      omega
    have hsumAB : A + (B - A) = B := Nat.add_sub_of_le hAB
    have hbinom := DenseGraph.choose_le_choose_add_mul_exp_neg
      (N := A) (Q := B - A) (m := z) hzA (by omega)
    rw [hsumAB] at hbinom
    have hsumReal : (A : ℝ) + (B - A : ℕ) = (B : ℝ) := by
      exact_mod_cast hsumAB
    rw [hsumReal] at hbinom
    have hBreal : (0 : ℝ) < B := by exact_mod_cast hBpos
    have hdensity :=
      criticalFineBalanceCrossMissingDensity_mul_capacity_le
        (t := t) hk hn hs hsSmall
    have hgapNonneg : (0 : ℝ) ≤ (B - A : ℕ) := by positivity
    have hratio : criticalFineBalanceCrossMissingDensity k *
        (B - A : ℕ) ≤ (z : ℝ) * (B - A : ℕ) / (B : ℝ) := by
      apply (le_div_iff₀ hBreal).2
      have hmul := mul_le_mul_of_nonneg_right hdensity hgapNonneg
      dsimp [z, B] at hmul ⊢
      nlinarith
    have hgapReal : (d : ℝ) ^ 2 / 9 ≤ (B - A : ℕ) := by
      have hcast : ((d ^ 2 : ℕ) : ℝ) ≤ (9 * (B - A) : ℕ) := by
        dsimp [d, A, B] at hgapNat ⊢
        exact_mod_cast hgapNat
      push_cast at hcast
      nlinarith
    have hrate : criticalFineBalanceCrossGaussianRate k * (d : ℝ) ^ 2 ≤
        criticalFineBalanceCrossMissingDensity k * (B - A : ℕ) := by
      calc
        criticalFineBalanceCrossGaussianRate k * (d : ℝ) ^ 2 =
            criticalFineBalanceCrossMissingDensity k * ((d : ℝ) ^ 2 / 9) := by
          rw [criticalFineBalanceCrossGaussianRate]
          ring
        _ ≤ criticalFineBalanceCrossMissingDensity k * (B - A : ℕ) :=
          mul_le_mul_of_nonneg_left hgapReal
            (criticalFineBalanceCrossMissingDensity_pos hk).le
    have hexp : Real.exp (-((z : ℝ) * (B - A : ℕ) / (B : ℝ))) ≤
        Real.exp (-(criticalFineBalanceCrossGaussianRate k * (d : ℝ) ^ 2)) := by
      apply Real.exp_le_exp.mpr
      linarith
    exact hbinom.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  · have hlt : A < z := Nat.lt_of_not_ge hzA
    rw [Nat.choose_eq_zero_of_lt hlt]
    have hnonneg : (0 : ℝ) ≤
        (Nat.choose B z : ℝ) *
          Real.exp (-(criticalFineBalanceCrossGaussianRate k * (d : ℝ) ^ 2)) :=
      mul_nonneg (Nat.cast_nonneg _)
        (Real.exp_pos _).le
    simpa [B, z, d] using hnonneg

/-! ## Multinomial size-vector shells -/

/-- Positive main-part size vectors with total support size `n-s` and exact
range `d`.  Positivity is precisely the nonempty-part condition in a
supercritical division. -/
def criticalFixedSparseSizeVectorShell
    (k n s d : ℕ) (hk : 3 ≤ k) : Finset (Fin (k - 1) → ℕ) :=
  (DenseGraph.sizeVectorsWithSumAndRange (k - 1) (n - s)
    (by omega) d).filter fun a ↦ ∀ i, 0 < a i

@[simp] theorem mem_criticalFixedSparseSizeVectorShell
    {k n s d : ℕ} {hk : 3 ≤ k} {a : Fin (k - 1) → ℕ} :
    a ∈ criticalFixedSparseSizeVectorShell k n s d hk ↔
      (∑ i, a i = n - s) ∧
      DenseGraph.sizeVectorRange (by omega : 0 < k - 1) a = d ∧
      ∀ i, 0 < a i := by
  simp [criticalFixedSparseSizeVectorShell, and_assoc]

/-- The number of admissible size vectors in one range shell is at most the
same `(d+1)^(k-1)` lattice-box bound as for unrestricted weak
compositions. -/
theorem card_criticalFixedSparseSizeVectorShell_le
    (k n s d : ℕ) (hk : 3 ≤ k) :
    (criticalFixedSparseSizeVectorShell k n s d hk).card ≤
      (d + 1) ^ (k - 1) := by
  calc
    (criticalFixedSparseSizeVectorShell k n s d hk).card ≤
        (DenseGraph.sizeVectorsWithSumAndRange (k - 1) (n - s)
          (by omega) d).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ (d + 1) ^ (k - 1) :=
      DenseGraph.card_sizeVectorsWithSumAndRange_le
        (k - 1) (n - s) (by omega) d

/-- Raw ordered-cover mass in one exact size-vector shell after a sparse
graph with `t` edges has been fixed.  The multinomial counts the labeled
ordered divisions on the complement of the prescribed sparse set, and the
binomial coefficient counts the missing cross coordinates. -/
noncomputable def criticalFixedSparseCrossSliceShellMass
    (k : ℕ) (hk : 3 ≤ k) (n s t d : ℕ) : ℝ :=
  ∑ a ∈ criticalFixedSparseSizeVectorShell k n s d hk,
    (Nat.multinomial Finset.univ a : ℝ) *
      (Nat.choose (DenseGraph.multipartiteCrossCapacity a)
        (criticalFixedSparseCrossMissingCount k n s t) : ℝ)

/-- The balanced ordered-cover reference mass for a fixed sparse graph with
`t` edges. -/
noncomputable def criticalFixedSparseBalancedCrossSliceMass
    (k n s t : ℕ) : ℝ :=
  (Nat.multinomial Finset.univ
      (DenseGraph.balancedPartSize (k - 1) (n - s)) : ℝ) *
    (Nat.choose
      (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) (n - s))
      (criticalFixedSparseCrossMissingCount k n s t) : ℝ)

/-- Total raw ordered-cover mass above the paper's literal
`sqrt (log₂ n)` range cutoff. -/
noncomputable def criticalFixedSparseUnbalancedCrossSliceMass
    (k : ℕ) (hk : 3 ≤ k) (n s t : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 0 n).filter
      (fun d : ℕ ↦ Real.sqrt (Real.logb 2 (n : ℝ)) < (d : ℝ)),
    criticalFixedSparseCrossSliceShellMass k hk n s t d

/-- The same raw unbalanced mass with the sparse edge level obtained from a
fixed ambient sparse graph.  Only the induced graph on `S` is relevant. -/
noncomputable def criticalFixedSparseGraphUnbalancedCrossSliceMass
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (S : Finset (Fin n))
    (H : SimpleGraph (Fin n)) : ℝ :=
  criticalFixedSparseUnbalancedCrossSliceMass k hk n S.card
    (inducedEdgeCount H S)

/-- Fixed-sparse-graph balanced reference mass. -/
noncomputable def criticalFixedSparseGraphBalancedCrossSliceMass
    (k n : ℕ) (S : Finset (Fin n)) (H : SimpleGraph (Fin n)) : ℝ :=
  criticalFixedSparseBalancedCrossSliceMass k n S.card
    (inducedEdgeCount H S)

/-- One exact range shell is bounded by the balanced reference mass times
its polynomially weighted Gaussian factor. -/
theorem criticalFixedSparseCrossSliceShellMass_le
    {k n s t d : ℕ} (hk : 3 ≤ k) (hn : 2 ≤ n) (hs : s ≤ n)
    (hsSmall : (s : ℝ) ≤
      criticalFineBalanceSparseFraction k * (n : ℝ))
    (hd : 2 ≤ d) :
    criticalFixedSparseCrossSliceShellMass k hk n s t d ≤
      criticalFixedSparseBalancedCrossSliceMass k n s t *
        DenseGraph.gaussianLatticeWeight (k - 1)
          (criticalFineBalanceCrossGaussianRate k) d := by
  let shell := criticalFixedSparseSizeVectorShell k n s d hk
  let balancedMult : ℝ := Nat.multinomial Finset.univ
    (DenseGraph.balancedPartSize (k - 1) (n - s))
  let balancedChoose : ℝ := Nat.choose
    (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) (n - s))
    (criticalFixedSparseCrossMissingCount k n s t)
  let gaussian : ℝ := Real.exp
    (-(criticalFineBalanceCrossGaussianRate k * (d : ℝ) ^ 2))
  have hpointwise : ∀ a ∈ shell,
      (Nat.multinomial Finset.univ a : ℝ) *
          (Nat.choose (DenseGraph.multipartiteCrossCapacity a)
            (criticalFixedSparseCrossMissingCount k n s t) : ℝ) ≤
        balancedMult * (balancedChoose * gaussian) := by
    intro a ha
    have haData := mem_criticalFixedSparseSizeVectorShell.mp ha
    have hmultNat := DenseGraph.multinomial_le_balancedPartSize
      (by omega : 0 < k - 1) a haData.1
    have hmult : (Nat.multinomial Finset.univ a : ℝ) ≤ balancedMult := by
      dsimp [balancedMult]
      exact_mod_cast hmultNat
    have hrange : 2 ≤ DenseGraph.sizeVectorRange
        (by omega : 0 < k - 1) a := by
      rw [haData.2.1]
      exact hd
    have hslice := criticalFixedSparseCrossSlice_le_fineBalanceWeight
      (t := t) hk hn hs hsSmall a haData.1 hrange
    have hslice' :
        (Nat.choose (DenseGraph.multipartiteCrossCapacity a)
            (criticalFixedSparseCrossMissingCount k n s t) : ℝ) ≤
          balancedChoose * gaussian := by
      simpa [balancedChoose, gaussian, haData.2.1] using hslice
    exact mul_le_mul hmult hslice'
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcardNat := card_criticalFixedSparseSizeVectorShell_le k n s d hk
  have hcardReal : (shell.card : ℝ) ≤ (((d + 1) ^ (k - 1) : ℕ) : ℝ) := by
    dsimp [shell]
    exact_mod_cast hcardNat
  have hconstantNonneg : 0 ≤ balancedMult * (balancedChoose * gaussian) := by
    dsimp [balancedMult, balancedChoose, gaussian]
    positivity
  calc
    criticalFixedSparseCrossSliceShellMass k hk n s t d =
        ∑ a ∈ shell,
          (Nat.multinomial Finset.univ a : ℝ) *
            (Nat.choose (DenseGraph.multipartiteCrossCapacity a)
              (criticalFixedSparseCrossMissingCount k n s t) : ℝ) := by
      rfl
    _ ≤ ∑ _a ∈ shell, balancedMult * (balancedChoose * gaussian) :=
      Finset.sum_le_sum fun a ha ↦ hpointwise a ha
    _ = (shell.card : ℝ) * (balancedMult * (balancedChoose * gaussian)) := by
      simp
    _ ≤ (((d + 1) ^ (k - 1) : ℕ) : ℝ) *
          (balancedMult * (balancedChoose * gaussian)) :=
      mul_le_mul_of_nonneg_right hcardReal hconstantNonneg
    _ = criticalFixedSparseBalancedCrossSliceMass k n s t *
        DenseGraph.gaussianLatticeWeight (k - 1)
          (criticalFineBalanceCrossGaussianRate k) d := by
      dsimp [criticalFixedSparseBalancedCrossSliceMass,
        DenseGraph.gaussianLatticeWeight, balancedMult, balancedChoose,
        gaussian]
      push_cast
      ring

/-- Above `n = 2`, exceeding the literal `sqrt (log₂ n)` cutoff forces an
integer range of at least two, as required by the quadratic smoothing
estimate. -/
theorem two_le_of_sqrt_logb_two_lt_natCast
    {n d : ℕ} (hn : 2 ≤ n)
    (hcutoff : Real.sqrt (Real.logb 2 (n : ℝ)) < (d : ℝ)) :
    2 ≤ d := by
  have hnCast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : (1 : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    calc
      (1 : ℝ) = Real.logb 2 2 :=
        (Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)).symm
      _ ≤ Real.logb 2 (n : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
          (by norm_num : (0 : ℝ) < 2) hnCast
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (Real.logb 2 (n : ℝ)) := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt (Real.logb 2 (n : ℝ)) := Real.sqrt_le_sqrt hlog
  have hd : (1 : ℝ) < (d : ℝ) := hsqrt.trans_lt hcutoff
  exact_mod_cast hd

/-- Exact finite general-`k` fine-balance estimate for a fixed sparse set
size and a fixed sparse graph edge level.  The unbalanced ordered-cover mass
is at most the balanced reference mass times the coefficient-one
`sqrt (log₂ n)` Gaussian tail. -/
theorem criticalFixedSparseUnbalancedCrossSliceMass_le
    {k n s t : ℕ} (hk : 3 ≤ k) (hn : 2 ≤ n) (hs : s ≤ n)
    (hsSmall : (s : ℝ) ≤
      criticalFineBalanceSparseFraction k * (n : ℝ)) :
    criticalFixedSparseUnbalancedCrossSliceMass k hk n s t ≤
      criticalFixedSparseBalancedCrossSliceMass k n s t *
        DenseGraph.gaussianRangeShellTail (k - 1)
          (criticalFineBalanceCrossGaussianRate k) n := by
  let shell := (Finset.Icc 0 n).filter
    (fun d : ℕ ↦ Real.sqrt (Real.logb 2 (n : ℝ)) < (d : ℝ))
  let reference := criticalFixedSparseBalancedCrossSliceMass k n s t
  have hpointwise : ∀ d ∈ shell,
      criticalFixedSparseCrossSliceShellMass k hk n s t d ≤
        reference * DenseGraph.gaussianLatticeWeight (k - 1)
          (criticalFineBalanceCrossGaussianRate k) d := by
    intro d hd
    have hcutoff := (Finset.mem_filter.mp hd).2
    exact criticalFixedSparseCrossSliceShellMass_le hk hn hs hsSmall
      (two_le_of_sqrt_logb_two_lt_natCast hn hcutoff)
  calc
    criticalFixedSparseUnbalancedCrossSliceMass k hk n s t =
        ∑ d ∈ shell,
          criticalFixedSparseCrossSliceShellMass k hk n s t d := by
      rfl
    _ ≤ ∑ d ∈ shell,
          reference * DenseGraph.gaussianLatticeWeight (k - 1)
            (criticalFineBalanceCrossGaussianRate k) d :=
      Finset.sum_le_sum fun d hd ↦ hpointwise d hd
    _ = reference *
        (∑ d ∈ shell, DenseGraph.gaussianLatticeWeight (k - 1)
          (criticalFineBalanceCrossGaussianRate k) d) := by
      rw [Finset.mul_sum]
    _ = criticalFixedSparseBalancedCrossSliceMass k n s t *
        DenseGraph.gaussianRangeShellTail (k - 1)
          (criticalFineBalanceCrossGaussianRate k) n := by
      rfl

/-- Paper-facing fixed-sparse-graph specialization.  The estimate is uniform
in the prescribed set and graph; the graph enters only through its exact
induced edge count on that set. -/
theorem criticalFixedSparseGraphUnbalancedCrossSliceMass_le
    {k n : ℕ} (hk : 3 ≤ k) (hn : 2 ≤ n)
    (S : Finset (Fin n)) (H : SimpleGraph (Fin n))
    (hsSmall : (S.card : ℝ) ≤
      criticalFineBalanceSparseFraction k * (n : ℝ)) :
    criticalFixedSparseGraphUnbalancedCrossSliceMass k hk n S H ≤
      criticalFixedSparseGraphBalancedCrossSliceMass k n S H *
        DenseGraph.gaussianRangeShellTail (k - 1)
          (criticalFineBalanceCrossGaussianRate k) n := by
  exact criticalFixedSparseUnbalancedCrossSliceMass_le hk hn
    (by simpa using Finset.card_le_univ S) hsSmall

/-- The uniform multiplicative error in the raw fixed-sparse-graph
fine-balance comparison. -/
noncomputable def criticalFineBalanceRawError (k n : ℕ) : ℝ :=
  DenseGraph.gaussianRangeShellTail (k - 1)
    (criticalFineBalanceCrossGaussianRate k) n

theorem criticalFineBalanceRawError_nonneg (k n : ℕ) :
    0 ≤ criticalFineBalanceRawError k n := by
  unfold criticalFineBalanceRawError DenseGraph.gaussianRangeShellTail
  exact Finset.sum_nonneg fun d _ ↦
    DenseGraph.gaussianLatticeWeight_nonneg (k - 1)
      (criticalFineBalanceCrossGaussianRate k) d

/-- The raw fixed-sparse-graph fine-balance error tends to zero for every
fixed `k ≥ 3`. -/
theorem criticalFineBalanceRawError_tendsto_zero
    {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (criticalFineBalanceRawError k) atTop (nhds 0) := by
  exact DenseGraph.gaussianRangeShellTail_tendsto_zero (k - 1)
    (criticalFineBalanceCrossGaussianRate_pos hk)

/-- The quadratic multipartite capacity loss of a division, expressed in
the combined coordinate universe used by critical clean fibers. -/
theorem criticalMainPartSizeRange_sq_le_nine_mul_combinedCapacityGap
    {k n : ℕ} (hk : 3 ≤ k) (D : SupercriticalDivision k (Fin n))
    (hrange : 2 ≤ criticalMainPartSizeRange hk D) :
    (criticalMainPartSizeRange hk D) ^ 2 ≤
      9 * (criticalMaximumCombinedCapacity k n D.sparse.card -
        criticalCombinedVariableCapacity D) := by
  have hsum : ∑ i : Fin (k - 1), (D.parts i).card =
      n - D.sparse.card := by
    have h := D.card_parts_add_card_sparse
    simp only [Fintype.card_fin] at h
    omega
  have hgap := DenseGraph.sizeVectorRange_sq_le_nine_mul_balancedCross_gap
    (by omega : 0 < k - 1) (criticalMainPartSizeVector D) hsum
    hrange
  have hmax := DenseGraph.balancedMultipartiteCrossCapacity_max
    (criticalMainPartSizeVector D) hsum
  unfold criticalMaximumCombinedCapacity criticalCombinedVariableCapacity
  rw [supercriticalTotalCrossCapacity_eq_multipartiteCrossCapacity]
  have hcancel :
      (DenseGraph.balancedMultipartiteCrossCapacity (k - 1)
          (n - D.sparse.card) + Nat.choose D.sparse.card 2) -
        (DenseGraph.multipartiteCrossCapacity (criticalMainPartSizeVector D) +
          Nat.choose D.sparse.card 2) =
      DenseGraph.balancedMultipartiteCrossCapacity (k - 1)
          (n - D.sparse.card) -
        DenseGraph.multipartiteCrossCapacity (criticalMainPartSizeVector D) := by
    omega
  change DenseGraph.sizeVectorRange (by omega : 0 < k - 1)
      (criticalMainPartSizeVector D) ^ 2 ≤
    9 * ((DenseGraph.balancedMultipartiteCrossCapacity (k - 1)
          (n - D.sparse.card) + Nat.choose D.sparse.card 2) -
      (DenseGraph.multipartiteCrossCapacity (criticalMainPartSizeVector D) +
        Nat.choose D.sparse.card 2))
  rw [hcancel]
  exact hgap

/-- Raw clean-fiber encoding in the common missing-coordinate convention. -/
theorem card_criticalCleanDivisionGraphFinset_le_choose_variable_missing
    {k n : ℕ} {hk : 3 ≤ k} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (hD : (criticalCleanDivisionGraphFinset k hk n tau hn D).Nonempty) :
    (criticalCleanDivisionGraphFinset k hk n tau hn D).card ≤
      Nat.choose (criticalCombinedVariableCapacity D)
        (criticalCombinedMissingCount k n D.sparse.card) := by
  obtain ⟨_hlower, hselected⟩ :=
    criticalCombinedSelectedCount_feasible_of_nonempty hD
  have hidentity :=
    criticalCombinedVariableCapacity_sub_selected_eq_missing_of_nonempty hD
  calc
    (criticalCleanDivisionGraphFinset k hk n tau hn D).card ≤
        Nat.choose (criticalCombinedVariableCapacity D)
          (criticalCombinedSelectedCount k n D) := by
      simpa only [criticalCleanDivisionGraphFinset,
        criticalCombinedVariableCapacity, criticalCombinedSelectedCount,
        supercriticalPreAbsorptionVariableCapacity,
        supercriticalSparsePotentialCapacity] using
          (card_supercriticalCleanDivisionGraphFinset_le_preAbsorptionChoose
            (hk := hk) (hgamma := gammaK_mem_supercritical_Ico k hk)
              (m := criticalEdgeCount k n) (tau := tau) (hn := hn) D)
    _ = Nat.choose (criticalCombinedVariableCapacity D)
          (criticalCombinedMissingCount k n D.sparse.card) := by
      rw [← hidentity]
      exact (Nat.choose_symm hselected).symm

/-- Exact finite Gaussian suppression of one nonempty canonical clean fiber.
The hypotheses are uniform in the sparse set; only its cardinality enters. -/
theorem criticalCleanDivisionGraphFinset_card_le_fineBalanceWeight
    {k n : ℕ} (hk : 3 ≤ k) (hn : 2 ≤ n) (hnParts : k - 1 ≤ n)
    {tau : ℝ} (D : SupercriticalDivision k (Fin n))
    (hD : (criticalCleanDivisionGraphFinset k hk n tau hnParts D).Nonempty)
    (hsSmall : (D.sparse.card : ℝ) ≤
      criticalFineBalanceSparseFraction k * (n : ℝ))
    (hrange : 2 ≤ criticalMainPartSizeRange hk D) :
    ((criticalCleanDivisionGraphFinset k hk n tau hnParts D).card : ℝ) ≤
      (Nat.choose (criticalMaximumCombinedCapacity k n D.sparse.card)
          (criticalCombinedMissingCount k n D.sparse.card) : ℝ) *
        Real.exp (-(criticalFineBalanceGaussianRate k *
          (criticalMainPartSizeRange hk D : ℝ) ^ 2)) := by
  let A := criticalCombinedVariableCapacity D
  let B := criticalMaximumCombinedCapacity k n D.sparse.card
  let z := criticalCombinedMissingCount k n D.sparse.card
  let d := criticalMainPartSizeRange hk D
  let missingRate := criticalFineBalanceMissingDensity k
  have hdata := criticalFineBalance_missing_coordinate_data_of_nonempty
    hk hn hnParts D hD hsSmall
  have hAB : A ≤ B := criticalCombinedVariableCapacity_le_maximum D
  have hidentity :=
    criticalCombinedVariableCapacity_sub_selected_eq_missing_of_nonempty hD
  have hzA : z ≤ A := by
    dsimp [z, A]
    rw [← hidentity]
    exact Nat.sub_le _ _
  have hsum : A + (B - A) = B := Nat.add_sub_of_le hAB
  have hbinom := DenseGraph.choose_le_choose_add_mul_exp_neg
    (N := A) (Q := B - A) (m := z) hzA (by omega)
  rw [hsum] at hbinom
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hdata.1
  have hgapNonneg : (0 : ℝ) ≤ (B - A : ℕ) := by positivity
  have hratio : missingRate * (B - A : ℕ) ≤
      (z : ℝ) * (B - A : ℕ) / (B : ℝ) := by
    apply (le_div_iff₀ hBreal).2
    have hmul := mul_le_mul_of_nonneg_right hdata.2.2 hgapNonneg
    dsimp [missingRate, z, B] at hmul ⊢
    nlinarith
  have hgapNat :=
    criticalMainPartSizeRange_sq_le_nine_mul_combinedCapacityGap hk D hrange
  have hgapReal : (d : ℝ) ^ 2 / 9 ≤ (B - A : ℕ) := by
    have hcast : ((d ^ 2 : ℕ) : ℝ) ≤
        (9 * (B - A) : ℕ) := by
      exact_mod_cast hgapNat
    push_cast at hcast
    nlinarith
  have hrate : criticalFineBalanceGaussianRate k * (d : ℝ) ^ 2 ≤
      missingRate * (B - A : ℕ) := by
    calc
      criticalFineBalanceGaussianRate k * (d : ℝ) ^ 2 =
          criticalFineBalanceMissingDensity k * ((d : ℝ) ^ 2 / 9) := by
        rw [criticalFineBalanceGaussianRate]
        ring
      _ ≤ criticalFineBalanceMissingDensity k * (B - A : ℕ) :=
        mul_le_mul_of_nonneg_left hgapReal
          (criticalFineBalanceMissingDensity_pos hk).le
      _ = missingRate * (B - A : ℕ) := by rfl
  have hexp : Real.exp (-((z : ℝ) * (B - A : ℕ) / (B : ℝ))) ≤
      Real.exp (-(criticalFineBalanceGaussianRate k * (d : ℝ) ^ 2)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hraw := card_criticalCleanDivisionGraphFinset_le_choose_variable_missing hD
  have hrawReal :
      ((criticalCleanDivisionGraphFinset k hk n tau hnParts D).card : ℝ) ≤
        (Nat.choose A z : ℝ) := by
    exact_mod_cast hraw
  have hsumReal : (A : ℝ) + (B - A : ℕ) = (B : ℝ) := by
    exact_mod_cast hsum
  rw [hsumReal] at hbinom
  calc
    ((criticalCleanDivisionGraphFinset k hk n tau hnParts D).card : ℝ) ≤
        (Nat.choose A z : ℝ) := hrawReal
    _ ≤ (Nat.choose B z : ℝ) *
        Real.exp (-((z : ℝ) * (B - A : ℕ) / (B : ℝ))) := hbinom
    _ ≤ (Nat.choose B z : ℝ) *
        Real.exp (-(criticalFineBalanceGaussianRate k * (d : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)

end InducedStars
