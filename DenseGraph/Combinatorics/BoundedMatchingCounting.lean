import DenseGraph.Combinatorics.BoundedDegreeCounting

/-!
# Bounded matching-number graph families

The exact matching-number neighborhood encoding extends to an upper bound
on the matching number by summing its finitely many possible values. The
extra factor is bounded by `exp(ell)`, uniformly even for zero vertices.
-/

noncomputable section
open Finset
open scoped Classical
namespace DenseGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem card_graphFamily_le_exp_of_matching_le_degree
    (F : Finset (SimpleGraph V)) (ell : ℕ) {d : ℝ}
    (hd : 0 ≤ d) (hdHalf : d ≤ 1/2)
    (hmatching : ∀ G ∈ F, matchingNumber G ≤ ell)
    (hdegree : ∀ G ∈ F, ∀ v, (G.degree v : ℝ) ≤ d*Fintype.card V) :
    (F.card : ℝ) ≤ Real.exp ((2*ell : ℕ)*
      ((Fintype.card V : ℝ)*Real.binEntropy d+Real.log (Fintype.card V+1))+ell) := by
  let fiber (i : ℕ) := F.filter fun G ↦ matchingNumber G=i
  let A := (Fintype.card V : ℝ)*Real.binEntropy d+Real.log (Fintype.card V+1)
  have hA : 0 ≤ A := by
    have hh := Real.binEntropy_nonneg hd (hdHalf.trans (by norm_num))
    dsimp [A]
    exact add_nonneg (mul_nonneg (by positivity) hh)
      (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (Fintype.card V); linarith))
  have hcover : F ⊆ (range (ell+1)).biUnion fiber := by
    intro G hG
    exact mem_biUnion.mpr ⟨matchingNumber G, mem_range.mpr (by have := hmatching G hG; omega),
      mem_filter.mpr ⟨hG,rfl⟩⟩
  have hF (i : ℕ) (hi : i ∈ range (ell+1)) :
      ((fiber i).card : ℝ) ≤ Real.exp ((2*ell : ℕ)*A) := by
    apply (card_graphFamily_le_exp_of_matching_degree (fiber i) i hd hdHalf
      (fun G hG ↦ (mem_filter.mp hG).2)
      (fun G hG ↦ hdegree G (mem_filter.mp hG).1)).trans
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ hA
    exact_mod_cast (by have := mem_range.mp hi; omega : 2*i ≤ 2*ell)
  have hcount : (F.card : ℝ) ≤ (ell+1)*Real.exp ((2*ell : ℕ)*A) := by
    calc
      _ ≤ ∑ i ∈ range (ell+1), ((fiber i).card : ℝ) := by
        exact_mod_cast (card_le_card hcover).trans card_biUnion_le
      _ ≤ ∑ _i ∈ range (ell+1), Real.exp ((2*ell : ℕ)*A) := sum_le_sum hF
      _ = _ := by simp
  calc
    _ ≤ _ := hcount
    _ ≤ Real.exp (ell : ℝ)*Real.exp ((2*ell : ℕ)*A) :=
      mul_le_mul_of_nonneg_right (Real.add_one_le_exp (ell : ℝ)) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [A]; ring

end DenseGraph
