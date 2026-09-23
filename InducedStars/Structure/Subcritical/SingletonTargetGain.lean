import InducedStars.Structure.Subcritical.SingletonSource
import InducedStars.Structure.Subcritical.SingletonSourceBudget

/-!
# Target gains after a singleton-safe sparse comparison

First construct a valid comparison division with the source vertex
in its sparse set and the target part unchanged. Only then apply the valid
sparse-to-part move. Its comparison cost is bounded while every resulting division part remains nonempty.
-/

noncomputable section
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- A bounded-cost valid sparse placement gives the exact corresponding
target-gain bound in a minimizing division. -/
theorem subcriticalMinimal_target_gain_le_of_sparse_comparison
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (hminimal : ∀ E : SubcriticalDivision k V,
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : V) (target : D.PartIndex) (C : ℕ)
    (hcomparison : ∃ E : SubcriticalDivision k V, v ∈ E.sparse ∧
      (∃ b : E.PartIndex, E.part b = D.part target) ∧
      subcriticalDefectCost G E ≤ subcriticalDefectCost G D + C) :
    2 * degreeInFinset G v (D.part target) ≤ (D.part target).card + C := by
  classical
  obtain ⟨E, hv, ⟨b, hb⟩, hcost⟩ := hcomparison
  have hmove := subcriticalDefectCost_moveVertex G E v (some b)
    (fun a _ ↦ E.erase_nonempty_of_sparse hv a)
  have hnew := subcriticalMoveSparseToPart_degree_bound G E hv b
  have hmin := hminimal (E.moveSparseToPart v hv b)
  rw [subcriticalCombinedDefectGraph_degree_of_sparse G E hv] at hmove
  change subcriticalDefectCost G (E.moveSparseToPart v hv b) + G.degree v =
    subcriticalDefectCost G E +
      (subcriticalCombinedDefectGraph G (E.moveSparseToPart v hv b)).degree v at hmove
  rw [hb] at hnew
  omega

/-- The all-singleton case of the singleton-safe comparison. The comparison
cost depends only on `k`, not on the number of core vertices. Small cores
are dissolved; large cores are repaired after deleting two vertices. -/
theorem subcriticalMinimal_singleton_component_target_gain_le
    (hk : 3 ≤ k) (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (hminimal : ∀ E : SubcriticalDivision k V,
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (i : Fin D.componentCount) (hsingle : ∀ j, (D.parts i j).card = 1)
    (v : V) (hv : v ∈ D.componentSupport i)
    (target : D.PartIndex) (htarget : target.1 ≠ i) :
    2 * degreeInFinset G v (D.part target) ≤ (D.part target).card + 4 * k ^ 3 := by
  classical
  apply subcriticalMinimal_target_gain_le_of_sparse_comparison G D hminimal v target (4 * k ^ 3)
  have hother : ∃ j : Fin D.componentCount, j ≠ i := ⟨target.1, htarget⟩
  by_cases hlarge : 4 * (k - 2) + 8 < (D.core i).order
  · obtain ⟨E, hvE, hkeep, hcost⟩ :=
      subcriticalSingleton_large_core_sparse_comparison hk G D i hsingle hlarge v hv hother
    refine ⟨E, hvE, hkeep target htarget, hcost.trans (Nat.add_le_add_left ?_ _)⟩
    have hquadratic : 9 ≤ k * k := Nat.mul_le_mul hk hk
    have hcubic := Nat.mul_le_mul_right k hquadratic
    nlinarith [Nat.sub_le k 2]
  · obtain ⟨E, hvE, hkeep, hcost⟩ :=
      subcriticalSmallSingletonSourceComparison G D hk i hsingle (le_of_not_gt hlarge)
        hother v hv
    exact ⟨E, hvE, hkeep target htarget, hcost⟩

end InducedStars
