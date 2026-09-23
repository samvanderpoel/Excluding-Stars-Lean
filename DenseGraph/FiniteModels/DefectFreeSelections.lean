import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Counting defect-free selections from finite target sets

The roles have arbitrary finite type.  A union bound over pairs of roles
removes tuples containing a defect edge.  The count is absolute, over the
full function space, so no independence or random-graph input is needed.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DenseGraph

variable {I V : Type*} [Fintype I] [DecidableEq I]
  [Fintype V] [DecidableEq V]

/-- Selections with no defect edge between distinct roles. -/
def defectFreeSelections (S : I → Finset V) (R : SimpleGraph V) :
    Finset (I → V) := by
  classical
  exact (Fintype.piFinset S).filter fun f ↦ ∀ i j, i ≠ j → ¬R.Adj (f i) (f j)

@[simp] theorem mem_defectFreeSelections (S : I → Finset V) (R : SimpleGraph V)
    (f : I → V) :
    f ∈ defectFreeSelections S R ↔
      (∀ i, f i ∈ S i) ∧ ∀ i j, i ≠ j → ¬R.Adj (f i) (f j) := by
  classical
  simp [defectFreeSelections, Fintype.mem_piFinset]

private theorem card_roles_except_two (i j : I) (hij : i ≠ j) :
    Fintype.card {a : I // a ≠ i ∧ a ≠ j} = Fintype.card I - 2 := by
  rw [Fintype.card_subtype]
  have heq : (Finset.univ.filter fun a : I ↦ a ≠ i ∧ a ≠ j) =
      (Finset.univ.erase i).erase j := by
    ext a
    simp [and_comm]
  rw [heq, Finset.card_erase_of_mem (by simp [hij.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  omega

/-- A pair constraint consumes two distinct entries of a function.  The
remaining entries contribute exactly the full function-space upper bound. -/
theorem card_adjacent_selections_le
    (R : SimpleGraph V) [DecidableRel R.Adj] (i j : I) (hij : i ≠ j) :
    ((Finset.univ.filter fun f : I → V ↦ R.Adj (f i) (f j)).card : ℝ) ≤
      (∑ x : V, (R.degree x : ℝ)) *
        (Fintype.card V : ℝ) ^ (Fintype.card I - 2) := by
  classical
  let B := Finset.univ.filter fun f : I → V ↦ R.Adj (f i) (f j)
  let encode : B → Σ x : V, R.neighborSet x ×
      ({a : I // a ≠ i ∧ a ≠ j} → V) := fun f ↦
    ⟨f.1 i, ⟨f.1 j, (Finset.mem_filter.mp f.2).2⟩, fun a ↦ f.1 a.1⟩
  have hinj : Function.Injective encode := by
    intro f g hfg
    apply Subtype.ext
    funext a
    by_cases hai : a = i
    · subst a
      exact congrArg Sigma.fst hfg
    by_cases haj : a = j
    · subst a
      exact congrArg (fun q ↦ q.2.1.1) hfg
    exact congrFun (congrArg (fun q ↦ q.2.2) hfg) ⟨a, hai, haj⟩
  have hcard := Fintype.card_le_of_injective encode hinj
  have hrhs : Fintype.card (Σ x : V, R.neighborSet x ×
      ({a : I // a ≠ i ∧ a ≠ j} → V)) =
      (∑ x : V, R.degree x) * Fintype.card V ^ (Fintype.card I - 2) := by
    simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fun,
      R.card_neighborSet_eq_degree, card_roles_except_two i j hij,
      Finset.sum_mul]
  rw [Fintype.card_coe, hrhs] at hcard
  exact_mod_cast hcard

/-- Maximum defect degree bounds one pair of role coordinates. -/
theorem card_adjacent_selections_le_of_degree
    (R : SimpleGraph V) [DecidableRel R.Adj] (i j : I) (hij : i ≠ j)
    {D : ℝ} (hdegree : ∀ x, (R.degree x : ℝ) ≤ D * Fintype.card V) :
    ((Finset.univ.filter fun f : I → V ↦ R.Adj (f i) (f j)).card : ℝ) ≤
      D * (Fintype.card V : ℝ) ^ Fintype.card I := by
  have hI : 2 ≤ Fintype.card I := by
    have h := Finset.card_le_card
      (Finset.subset_univ ({i, j} : Finset I))
    simpa [hij] using h
  calc
    _ ≤ (∑ x : V, (R.degree x : ℝ)) *
        (Fintype.card V : ℝ) ^ (Fintype.card I - 2) :=
      card_adjacent_selections_le R i j hij
    _ ≤ ((Fintype.card V : ℝ) * (D * Fintype.card V)) *
        (Fintype.card V : ℝ) ^ (Fintype.card I - 2) := by
      gcongr
      simpa using Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset V)) ↦
        hdegree x)
    _ = D * (Fintype.card V : ℝ) ^ Fintype.card I := by
      have hp : (Fintype.card V : ℝ) ^ Fintype.card I =
          (Fintype.card V : ℝ) ^ 2 *
            (Fintype.card V : ℝ) ^ (Fintype.card I - 2) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hp]
      ring

/-- The total number of bad tuples is at most `d² D n^d`.  Ordered role pairs
overcount and are used only for this upper bound. -/
theorem card_bad_selections_le
    (S : I → Finset V) (R : SimpleGraph V) [DecidableRel R.Adj]
    {D : ℝ} (hD : 0 ≤ D)
    (hdegree : ∀ x, (R.degree x : ℝ) ≤ D * Fintype.card V) :
    (((Fintype.piFinset S).filter fun f ↦
      ∃ i j, i ≠ j ∧ R.Adj (f i) (f j)).card : ℝ) ≤
      (Fintype.card I : ℝ) ^ 2 * D *
        (Fintype.card V : ℝ) ^ Fintype.card I := by
  classical
  let B (i j : I) := Finset.univ.filter fun f : I → V ↦
    i ≠ j ∧ R.Adj (f i) (f j)
  have hsubset : ((Fintype.piFinset S).filter fun f ↦
      ∃ i j, i ≠ j ∧ R.Adj (f i) (f j)) ⊆
      Finset.univ.biUnion (fun i ↦ Finset.univ.biUnion (B i)) := by
    intro f hf
    obtain ⟨i, j, hij, hR⟩ := (Finset.mem_filter.mp hf).2
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by simp [B, hij, hR]⟩⟩
  have hpair (i j : I) : ((B i j).card : ℝ) ≤
      D * (Fintype.card V : ℝ) ^ Fintype.card I := by
    by_cases hij : i = j
    · simp [B, hij]
      positivity
    · simpa [B, hij] using card_adjacent_selections_le_of_degree R i j hij hdegree
  have hcount : ((Fintype.piFinset S).filter fun f ↦
      ∃ i j, i ≠ j ∧ R.Adj (f i) (f j)).card ≤ ∑ i : I, ∑ j : I, (B i j).card :=
    (Finset.card_le_card hsubset).trans <|
      Finset.card_biUnion_le.trans <|
        Finset.sum_le_sum fun i _ ↦ Finset.card_biUnion_le
  calc
    _ ≤ ∑ i : I, ∑ j : I, ((B i j).card : ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ _i : I, ∑ _j : I,
        D * (Fintype.card V : ℝ) ^ Fintype.card I :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hpair i j
    _ = _ := by simp; ring

/-- Quantitative clean-selection lower bound.  The target sets may have
already excluded fixed forbidden endpoints and their defect neighbors. -/
theorem defectFreeSelections_card_lower
    (S : I → Finset V) (R : SimpleGraph V) [DecidableRel R.Adj]
    {lambda D : ℝ} (hlambda : 0 ≤ lambda) (hD : 0 ≤ D)
    (hsize : ∀ i, lambda * Fintype.card V ≤ (S i).card)
    (hdegree : ∀ x, (R.degree x : ℝ) ≤ D * Fintype.card V) :
    (lambda * Fintype.card V) ^ Fintype.card I -
        (Fintype.card I : ℝ) ^ 2 * D *
          (Fintype.card V : ℝ) ^ Fintype.card I ≤
      ((defectFreeSelections S R).card : ℝ) := by
  classical
  have hprod : (lambda * Fintype.card V) ^ Fintype.card I ≤
      ((Fintype.piFinset S).card : ℝ) := by
    rw [Fintype.card_piFinset, Nat.cast_prod]
    simpa using Finset.prod_le_prod
      (fun _ (_ : _ ∈ (Finset.univ : Finset I)) ↦ mul_nonneg hlambda (Nat.cast_nonneg _))
      (fun i (_ : i ∈ (Finset.univ : Finset I)) ↦ hsize i)
  have hbad := card_bad_selections_le S R hD hdegree
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Fintype.piFinset S) (p := fun f ↦ ∀ i j, i ≠ j → ¬R.Adj (f i) (f j))
  have hpart : (defectFreeSelections S R).card +
      ((Fintype.piFinset S).filter fun f ↦
        ∃ i j, i ≠ j ∧ R.Adj (f i) (f j)).card = (Fintype.piFinset S).card := by
    simpa [defectFreeSelections, not_forall] using hpartition
  have hpartR : ((defectFreeSelections S R).card : ℝ) +
      (((Fintype.piFinset S).filter fun f ↦
        ∃ i j, i ≠ j ∧ R.Adj (f i) (f j)).card : ℝ) =
      ((Fintype.piFinset S).card : ℝ) := by exact_mod_cast hpart
  linarith

/-- Half the full target-product lower bound survives a sufficiently small
maximum defect degree. -/
theorem defectFreeSelections_card_lower_half
    (S : I → Finset V) (R : SimpleGraph V) [DecidableRel R.Adj]
    {lambda D : ℝ} (hlambda : 0 ≤ lambda) (hD : 0 ≤ D)
    (hsize : ∀ i, lambda * Fintype.card V ≤ (S i).card)
    (hdegree : ∀ x, (R.degree x : ℝ) ≤ D * Fintype.card V)
    (hsmall : (Fintype.card I : ℝ) ^ 2 * D ≤ lambda ^ Fintype.card I / 2) :
    (lambda * Fintype.card V) ^ Fintype.card I / 2 ≤
      ((defectFreeSelections S R).card : ℝ) := by
  have h := defectFreeSelections_card_lower S R hlambda hD hsize hdegree
  have he := mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ (Fintype.card V : ℝ) ^ Fintype.card I by positivity)
  rw [mul_pow] at h ⊢
  nlinarith

/-- Disjoint targets ensure that a selection uses distinct vertices. -/
theorem defectFreeSelections_injective
    {S : I → Finset V} {R : SimpleGraph V}
    (hdisjoint : Pairwise fun i j ↦ Disjoint (S i) (S j))
    {f : I → V} (hf : f ∈ defectFreeSelections S R) : Function.Injective f := by
  intro i j hij
  by_contra hne
  have hm := (mem_defectFreeSelections S R f).mp hf |>.1
  exact Finset.disjoint_left.mp (hdisjoint hne) (hm i) (hij ▸ hm j)

/-- Remove defects incident with the two fixed matching endpoints. -/
def endpointCleanTarget (R : SimpleGraph V) (x y : V) (S : Finset V) : Finset V := by
  classical
  exact S.filter fun v ↦ ¬R.Adj x v ∧ ¬R.Adj y v

@[simp] theorem mem_endpointCleanTarget (R : SimpleGraph V) (x y v : V) (S : Finset V) :
    v ∈ endpointCleanTarget R x y S ↔ v ∈ S ∧ ¬R.Adj x v ∧ ¬R.Adj y v := by
  classical
  simp [endpointCleanTarget]

/-- Endpoint cleaning loses at most the sum of their defect degrees. -/
theorem endpointCleanTarget_card_lower
    (R : SimpleGraph V) [DecidableRel R.Adj] (x y : V) (S : Finset V) :
    (S.card : ℝ) - R.degree x - R.degree y ≤
      ((endpointCleanTarget R x y S).card : ℝ) := by
  classical
  have hsubset : S ⊆ (endpointCleanTarget R x y S ∪ R.neighborFinset x) ∪
      R.neighborFinset y := by
    intro v hv
    by_cases hx : R.Adj x v
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simpa using hx))
    by_cases hy : R.Adj y v
    · exact Finset.mem_union_right _ (by simpa using hy)
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      ((mem_endpointCleanTarget R x y v S).mpr ⟨hv, hx, hy⟩))
  have hcard : S.card ≤ (endpointCleanTarget R x y S).card +
      R.degree x + R.degree y := by
    calc
      _ ≤ _ := Finset.card_le_card hsubset
      _ ≤ (endpointCleanTarget R x y S ∪ R.neighborFinset x).card +
          (R.neighborFinset y).card := Finset.card_union_le _ _
      _ ≤ (endpointCleanTarget R x y S).card +
          (R.neighborFinset x).card + (R.neighborFinset y).card := by
        exact Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = _ := by simp
  have hR : (S.card : ℝ) ≤ (endpointCleanTarget R x y S).card +
      (R.degree x : ℝ) + R.degree y := by exact_mod_cast hcard
  linarith

/-- Endpoint degree bounds are enough for cleaning; no condition is imposed
on the adjacency between the two fixed endpoints themselves. -/
theorem endpointCleanTarget_card_lower_of_degree
    (R : SimpleGraph V) [DecidableRel R.Adj] (x y : V) (S : Finset V)
    {D : ℝ} (hx : (R.degree x : ℝ) ≤ D * Fintype.card V)
    (hy : (R.degree y : ℝ) ≤ D * Fintype.card V) :
    (S.card : ℝ) - 2 * D * Fintype.card V ≤
      ((endpointCleanTarget R x y S).card : ℝ) := by
  have h := endpointCleanTarget_card_lower R x y S
  linarith

end DenseGraph
