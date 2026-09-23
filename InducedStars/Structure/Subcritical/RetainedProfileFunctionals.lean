import InducedStars.Structure.Subcritical.RetainedProfileGraphon
import DenseGraph.Combinatorics.BinomialEntropy

/-!
# Exact retained-profile density and entropy

Paper: `lemma:clean-retained-comparison-K1k`. The clique diagonal
is retained in the density, whereas it contributes zero entropy. Binomial
bounds use natural logarithms and graphon entropy uses bits.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

section FiniteSums
variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem retainedCliqueCapacity_all_square_identity
    (D : SubcriticalDivision k V) :
    (∑ a : D.PartIndex, ((D.part a).card : ℝ)^2) =
      2 * (retainedCliqueCapacity D 0 (Fintype.card V) : ℝ) + D.support.card := by
  have hall : D.retainedPartIndices 0 (Fintype.card V) = Finset.univ := by
    ext a
    simp only [D.mem_retainedPartIndices, D.retainedComponentIndices_all, Finset.mem_univ]
  rw [retainedCliqueCapacity, hall, D.card_support]
  simp only [Nat.cast_sum, Nat.cast_choose_two, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem retainedProfileMatrix_sum
    (D : SubcriticalDivision k V)
    (v : RetainedEdgeCountVector D 0 (Fintype.card V)) :
    (∑ x : V, ∑ y : V, retainedProfileMatrix D v x y) =
      2 * (retainedCliqueCapacity D 0 (Fintype.card V) : ℝ) + D.support.card +
        2 * (retainedEdgeCountTotal v : ℝ) := by
  have h := retainedProfileMatrix_sum_function D v id rfl
  simp only [id_eq, mul_one] at h
  rw [h, retainedCliqueCapacity_all_square_identity]
  congr 1
  rw [retainedEdgeCountTotal, Nat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  unfold retainedEdgeCountDensity
  rw [mul_div_cancel₀]
  exact_mod_cast (retainedActiveCapacity_pos D 0 (Fintype.card V) e).ne'

theorem retainedProfileMatrix_entropy_sum
    (D : SubcriticalDivision k V)
    (v : RetainedEdgeCountVector D 0 (Fintype.card V)) :
    (∑ x : V, ∑ y : V, binaryEntropy (retainedProfileMatrix D v x y)) =
      2 * ∑ e : RetainedActivePair D 0 (Fintype.card V),
        (retainedActiveCapacity D 0 (Fintype.card V) e : ℝ) *
          binaryEntropy (retainedEdgeCountDensity v e) := by
  simpa using retainedProfileMatrix_sum_function D v binaryEntropy binaryEntropy_zero

/-- Natural-log entropy of the exact finite active-coordinate vector. -/
def retainedProfileEntropyNat {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (v : RetainedEdgeCountVector D eta R₀) : ℝ :=
  ∑ e : RetainedActivePair D eta R₀,
    (retainedActiveCapacity D eta R₀ e : ℝ) * Real.binEntropy (retainedEdgeCountDensity v e)

theorem retainedEdgeCountMultiplicity_le_exp_profileEntropy
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (v : RetainedEdgeCountVector D eta R₀) :
    (retainedEdgeCountMultiplicity v : ℝ) ≤ Real.exp (retainedProfileEntropyNat v) := by
  rw [retainedEdgeCountMultiplicity, Nat.cast_prod, retainedProfileEntropyNat,
    Real.exp_sum]
  apply Finset.prod_le_prod (fun e he ↦ by positivity)
  intro e he
  exact DenseGraph.choose_le_exp_binomialEntropyPerspective (v.count_le_capacity e)

end FiniteSums

variable {k n : ℕ}

theorem retainedProfileGraphon_edgeDensity
    (hn : 0 < n) (D : SubcriticalDivision k (Fin n))
    (v : RetainedEdgeCountVector D 0 (Fintype.card (Fin n))) :
    graphonEdgeDensity (retainedProfileGraphon D v) =
      (2 * (retainedCliqueCapacity D 0 (Fintype.card (Fin n)) : ℝ) + D.support.card +
        2 * (retainedEdgeCountTotal v : ℝ)) / (n : ℝ)^2 := by
  rw [retainedProfileGraphon, graphonEdgeDensity_matrixGraphon hn, retainedProfileMatrix_sum]
  ring

theorem retainedProfileGraphon_entropy
    (hn : 0 < n) (D : SubcriticalDivision k (Fin n))
    (v : RetainedEdgeCountVector D 0 (Fintype.card (Fin n))) :
    graphonEntropy (retainedProfileGraphon D v) =
      2 / (n : ℝ)^2 * ∑ e : RetainedActivePair D 0 (Fintype.card (Fin n)),
        (retainedActiveCapacity D 0 (Fintype.card (Fin n)) e : ℝ) *
          binaryEntropy (retainedEdgeCountDensity v e) := by
  rw [retainedProfileGraphon, graphonEntropy_matrixGraphon hn, retainedProfileMatrix_entropy_sum]
  ring

theorem retainedProfileEntropyNat_eq_graphonEntropy
    (hn : 0 < n) (D : SubcriticalDivision k (Fin n))
    (v : RetainedEdgeCountVector D 0 (Fintype.card (Fin n))) :
    retainedProfileEntropyNat v =
      Real.log 2 * (n : ℝ)^2 / 2 * graphonEntropy (retainedProfileGraphon D v) := by
  rw [retainedProfileGraphon_entropy hn, retainedProfileEntropyNat]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hl : Real.log 2 ≠ 0 := realLogTwo_pos.ne'
  simp_rw [binaryEntropy, ← mul_div_assoc]
  rw [← Finset.sum_div]
  field_simp

end InducedStars
