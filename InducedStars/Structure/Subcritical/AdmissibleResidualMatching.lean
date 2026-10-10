import InducedStars.Structure.Subcritical.ResidualMatchingSelection
import DenseGraph.Combinatorics.BoundedDegreeCounting

/-!
# Matching selection and enumeration for every admissible residual graph

Paper: `lemma:residual-matching-estimate-K1k` and
`eqn:residual-graph-count-K1k` in the current subcritical section.
The family contains every graph satisfying the stated edge, root, degree,
and matching conditions. No realization by a profile is required.
All exponential rates and entropy terms use natural units.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact residual-graph conditions in the current paper. -/
structure SubcriticalAdmissibleResidualGraph
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (B : Finset V) (d : ℝ) (ell : ℕ) (R : SimpleGraph V) : Prop where
  allowed : ∀ x y, R.Adj x y →
    (x ∈ D.retainedVertices eta R₀ ∨ y ∈ D.retainedVertices eta R₀) ∧ ¬ D.ActivePair x y
  avoids : ∀ x y, R.Adj x y → x ∉ B ∧ y ∉ B
  degree_le : ∀ v, (R.degree v : ℝ) ≤ d * Fintype.card V
  matching : DenseGraph.matchingNumber R = ell

/-- All admissible residual graphs, independently of any profile family. -/
def subcriticalAdmissibleResidualFinset
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (B : Finset V) (d : ℝ) (ell : ℕ) : Finset (SimpleGraph V) :=
  Finset.univ.filter (SubcriticalAdmissibleResidualGraph D eta R₀ B d ell)

@[simp] theorem mem_subcriticalAdmissibleResidualFinset
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (B : Finset V) (d : ℝ) (ell : ℕ) (R : SimpleGraph V) :
    R ∈ subcriticalAdmissibleResidualFinset D eta R₀ B d ell ↔
      SubcriticalAdmissibleResidualGraph D eta R₀ B d ell R := by
  simp [subcriticalAdmissibleResidualFinset]

/-- At matching number zero, the complete admissible family is the
singleton empty graph, including when the root set is nonempty. -/
theorem subcriticalAdmissibleResidualFinset_zero
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (B : Finset V) (d : ℝ) (hd : 0 ≤ d) :
    subcriticalAdmissibleResidualFinset D eta R₀ B d 0 = {⊥} := by
  ext R
  rw [mem_subcriticalAdmissibleResidualFinset, Finset.mem_singleton]
  constructor
  · intro hR
    exact (DenseGraph.matchingNumber_eq_zero_iff R).mp hR.matching
  · rintro rfl
    refine ⟨?_, ?_, ?_, DenseGraph.matchingNumber_bot⟩
    · intro x y hxy
      exact False.elim ((SimpleGraph.bot_adj x y).mp hxy)
    · intro x y hxy
      exact False.elim ((SimpleGraph.bot_adj x y).mp hxy)
    · intro v
      have hnonneg : 0 ≤ d * (Fintype.card V : ℝ) := mul_nonneg hd (Nat.cast_nonneg _)
      simpa [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] using hnonneg

/-- The zero-matching weighted sum equals one when the empty residual
graph has safety probability one. -/
theorem subcriticalAdmissibleResidualWeightedSum_zero
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (B : Finset V) (d C : ℝ) (q : SimpleGraph V → ℝ)
    (hd : 0 ≤ d) (hzero : q ⊥ = 1) :
    (∑ R ∈ subcriticalAdmissibleResidualFinset D eta R₀ B d 0,
      Real.exp (C * (finiteGraphEdges R).card) * q R) = 1 := by
  rw [subcriticalAdmissibleResidualFinset_zero D eta R₀ B d hd]
  have hempty : finiteGraphEdges (⊥ : SimpleGraph V) = ∅ := by
    ext e
    simp only [mem_finiteGraphEdges, Finset.notMem_empty, SimpleGraph.edgeSet_bot,
      Set.mem_empty_iff_false]
  simp [hempty, hzero]

variable {D : SubcriticalDivision k V} {eta d : ℝ} {R₀ ell : ℕ}
  {B : Finset V} {R : SimpleGraph V}

/-- The maximum-matching pigeonhole argument and exact ceiling thinning
apply to every admissible residual graph. -/
theorem subcriticalAdmissibleResidual_exists_matching
    (hR : SubcriticalAdmissibleResidualGraph D eta R₀ B d ell R)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hR₀ : 1 ≤ R₀) (hell : 1 ≤ ell)
    (hscale : 16 ≤ subcriticalResidualMatchingLambda eta R₀ * Fintype.card V) :
    ∃ M : SubcriticalHomogeneousResidualMatching D eta R₀ R B,
      subcriticalResidualMatchingLambda eta R₀ * ell /
        (8 * (subcriticalResidualMatchingKappa eta R₀ : ℝ)) ≤ (M.edges.card : ℝ) ∧
      (M.edges.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * Fintype.card V / 8 := by
  obtain ⟨M₀, hM₀⟩ := exists_subcriticalHomogeneousResidualMatching R B
    heta hetaOne hR₀ hR.allowed hR.avoids (by simpa only [hR.matching] using hell)
  rw [hR.matching] at hM₀
  obtain ⟨M, _, _, _, hlow, hhigh⟩ := M₀.exists_thin heta hetaOne hR₀ ell hM₀ hscale
  exact ⟨M, hlow, hhigh⟩

/-- The matching-cover degree estimate also controls the edge weight. -/
theorem SubcriticalAdmissibleResidualGraph.edgeCount_le
    (hR : SubcriticalAdmissibleResidualGraph D eta R₀ B d ell R) :
    ((finiteGraphEdges R).card : ℝ) ≤ (2 * ell : ℕ) * (d * Fintype.card V) := by
  have hedge : finiteGraphEdges R = R.edgeFinset := by
    ext e
    simp only [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  simpa only [hedge, hR.matching] using
    DenseGraph.edgeFinset_card_le_matching_degree R hR.degree_le

/-- Uniform weighted enumeration for any family with the prescribed
matching number and maximum degree. The coefficient `C` is arbitrary. -/
theorem subcriticalResidualFamilyWeightedCount_le
    (F : Finset (SimpleGraph V)) (ell : ℕ) (d C : ℝ)
    (hd : 0 ≤ d) (hdHalf : d ≤ 1 / 2) (hC : 0 ≤ C)
    (hmatching : ∀ R ∈ F, DenseGraph.matchingNumber R = ell)
    (hdegree : ∀ R ∈ F, ∀ v, (R.degree v : ℝ) ≤ d * Fintype.card V) :
    (∑ R ∈ F, Real.exp (C * (finiteGraphEdges R).card)) ≤
      Real.exp ((2 * ell : ℕ) * ((Fintype.card V : ℝ) *
        (Real.binEntropy d + C * d) + Real.log (Fintype.card V + 1))) := by
  have hedge (R : SimpleGraph V) : finiteGraphEdges R = R.edgeFinset := by
    ext e
    simp only [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  simp_rw [hedge]
  exact DenseGraph.sum_exp_edges_le_of_matching_degree F ell hd hdHalf hC hmatching hdegree

/-- Weighted enumeration over the paper's entire admissible domain. -/
theorem subcriticalAdmissibleResidualWeightedCount_le
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (B : Finset V) (ell : ℕ) (d C : ℝ)
    (hd : 0 ≤ d) (hdHalf : d ≤ 1 / 2) (hC : 0 ≤ C) :
    (∑ R ∈ subcriticalAdmissibleResidualFinset D eta R₀ B d ell,
      Real.exp (C * (finiteGraphEdges R).card)) ≤
      Real.exp ((2 * ell : ℕ) * ((Fintype.card V : ℝ) *
        (Real.binEntropy d + C * d) + Real.log (Fintype.card V + 1))) := by
  apply subcriticalResidualFamilyWeightedCount_le _ ell d C hd hdHalf hC
  · intro R hR
    exact ((mem_subcriticalAdmissibleResidualFinset D eta R₀ B d ell R).mp hR).matching
  · intro R hR
    exact ((mem_subcriticalAdmissibleResidualFinset D eta R₀ B d ell R).mp hR).degree_le

/-- Exact finite enumeration coefficient, with arbitrary edge weight. -/
def subcriticalAdmissibleResidualEnumerationCoefficient (d C : ℝ) (n : ℕ) : ℝ :=
  2 * (Real.binEntropy d + C * d + Real.log (n + 1) / n)

theorem subcriticalAdmissibleResidualEnumerationCoefficient_mul
    (d C : ℝ) {n : ℕ} (hn : 0 < n) (ell : ℕ) :
    subcriticalAdmissibleResidualEnumerationCoefficient d C n * ell * n =
      (2 * ell : ℕ) * ((n : ℝ) * (Real.binEntropy d + C * d) + Real.log (n + 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold subcriticalAdmissibleResidualEnumerationCoefficient
  push_cast
  field_simp
  <;> ring

/-- Multiply a uniform residual-safety estimate into the complete weighted
enumeration. The probability estimate remains explicit for the Janson step. -/
theorem subcriticalResidualFamilyWeightedSum_le
    (F : Finset (SimpleGraph V)) (ell : ℕ) (d C c : ℝ)
    (q : SimpleGraph V → ℝ)
    (hn : 0 < Fintype.card V) (hd : 0 ≤ d) (hdHalf : d ≤ 1 / 2) (hC : 0 ≤ C)
    (hmatching : ∀ R ∈ F, DenseGraph.matchingNumber R = ell)
    (hdegree : ∀ R ∈ F, ∀ v, (R.degree v : ℝ) ≤ d * Fintype.card V)
    (hprob : ∀ R ∈ F, q R ≤ Real.exp (-c * ell * Fintype.card V)) :
    (∑ R ∈ F, Real.exp (C * (finiteGraphEdges R).card) * q R) ≤
      Real.exp ((subcriticalAdmissibleResidualEnumerationCoefficient d C
        (Fintype.card V) - c) * ell * Fintype.card V) := by
  have hcount := subcriticalResidualFamilyWeightedCount_le F ell d C hd hdHalf hC
    hmatching hdegree
  rw [← subcriticalAdmissibleResidualEnumerationCoefficient_mul d C hn ell] at hcount
  calc
    _ ≤ ∑ R ∈ F, Real.exp (C * (finiteGraphEdges R).card) *
        Real.exp (-c * ell * Fintype.card V) :=
      Finset.sum_le_sum (fun R hR ↦
        mul_le_mul_of_nonneg_left (hprob R hR) (Real.exp_pos _).le)
    _ = (∑ R ∈ F, Real.exp (C * (finiteGraphEdges R).card)) *
        Real.exp (-c * ell * Fintype.card V) := (Finset.sum_mul ..).symm
    _ ≤ Real.exp (subcriticalAdmissibleResidualEnumerationCoefficient d C
        (Fintype.card V) * ell * Fintype.card V) *
        Real.exp (-c * ell * Fintype.card V) :=
      mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The weighted residual sum ranges over every admissible graph, with no
profile restriction. Uniform safety is the only remaining probabilistic input. -/
theorem subcriticalAdmissibleResidualWeightedSum_le
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (B : Finset V) (ell : ℕ) (d C c : ℝ) (q : SimpleGraph V → ℝ)
    (hn : 0 < Fintype.card V) (hd : 0 ≤ d) (hdHalf : d ≤ 1 / 2) (hC : 0 ≤ C)
    (hprob : ∀ R, SubcriticalAdmissibleResidualGraph D eta R₀ B d ell R →
      q R ≤ Real.exp (-c * ell * Fintype.card V)) :
    (∑ R ∈ subcriticalAdmissibleResidualFinset D eta R₀ B d ell,
      Real.exp (C * (finiteGraphEdges R).card) * q R) ≤
      Real.exp ((subcriticalAdmissibleResidualEnumerationCoefficient d C
        (Fintype.card V) - c) * ell * Fintype.card V) := by
  apply subcriticalResidualFamilyWeightedSum_le _ ell d C c q hn hd hdHalf hC
  · intro R hR
    exact ((mem_subcriticalAdmissibleResidualFinset D eta R₀ B d ell R).mp hR).matching
  · intro R hR
    exact ((mem_subcriticalAdmissibleResidualFinset D eta R₀ B d ell R).mp hR).degree_le
  · intro R hR
    exact hprob R ((mem_subcriticalAdmissibleResidualFinset D eta R₀ B d ell R).mp hR)

/-- The paper's entropy reserve leaves half the uniform matching penalty. -/
theorem subcriticalAdmissibleResidualWeightedSum_le_half
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (B : Finset V) (ell : ℕ) (d C c : ℝ) (q : SimpleGraph V → ℝ)
    (hn : 0 < Fintype.card V) (hd : 0 ≤ d) (hdHalf : d ≤ 1 / 2) (hC : 0 ≤ C)
    (hprob : ∀ R, SubcriticalAdmissibleResidualGraph D eta R₀ B d ell R →
      q R ≤ Real.exp (-c * ell * Fintype.card V))
    (herror : subcriticalAdmissibleResidualEnumerationCoefficient d C (Fintype.card V) ≤ c / 2) :
    (∑ R ∈ subcriticalAdmissibleResidualFinset D eta R₀ B d ell,
      Real.exp (C * (finiteGraphEdges R).card) * q R) ≤
      Real.exp (-(c / 2) * ell * Fintype.card V) := by
  apply (subcriticalAdmissibleResidualWeightedSum_le D eta R₀ B ell d C c q
    hn hd hdHalf hC hprob).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith :
      subcriticalAdmissibleResidualEnumerationCoefficient d C (Fintype.card V) - c ≤ -(c / 2))
      (Nat.cast_nonneg ell)) (Nat.cast_nonneg (Fintype.card V))

end InducedStars
