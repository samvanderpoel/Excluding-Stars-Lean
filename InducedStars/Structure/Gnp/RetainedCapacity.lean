import DenseGraph.Combinatorics.RegularWeightedCapacity
import InducedStars.Structure.Subcritical.RetainedProfileFunctionals

/-!
# Exact regular-core capacity bounds for retained keys

Paper: the retained-factor estimate in the proof of
`lemma:critical-gnp-comparison-K1k` in `paper/gnp.tex`.
The actual active coordinates are counted once as unordered core edges.
The regular-core quadratic bound gives an exact linear correction, with no
balance hypothesis and no spectral assumption.
-/

noncomputable section
open Finset Set
open scoped Classical BigOperators

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

private def retainedAllActiveCoreEdgeMap (D : SubcriticalDivision k V)
    (e : RetainedActivePair D 0 (Fintype.card V)) :
    Σ i : Fin D.componentCount, ↥(D.core i).graph.edgeFinset :=
  ⟨e.component, ⟨s(e.left, e.right), by simpa using e.active⟩⟩

private theorem retainedAllActiveCoreEdgeMap_bijective
    (D : SubcriticalDivision k V) :
    Function.Bijective (retainedAllActiveCoreEdgeMap D) := by
  constructor
  · rintro ⟨i, hi, a, b, hab, hadj⟩ ⟨j, hj, c, d, hcd, hcadj⟩ he
    have hij : i = j := congrArg Sigma.fst he
    subst j
    have hp : s(a, b) = s(c, d) := by
      simpa only [retainedAllActiveCoreEdgeMap, Sigma.mk.inj_iff, heq_eq_eq,
        true_and, Subtype.mk.injEq] using he
    rcases (Sym2.mk_eq_mk_iff (p := (a, b)) (q := (c, d))).mp hp with h | h
    · have hac : a = c := congrArg Prod.fst h
      have hbd : b = d := congrArg Prod.snd h
      subst c
      subst d
      rfl
    · have had : a = d := congrArg Prod.fst h
      have hbc : b = c := congrArg Prod.snd h
      subst d
      subst c
      exact (lt_asymm hab hcd).elim
  · rintro ⟨i, ⟨z, hz⟩⟩
    induction z using Sym2.inductionOn with
    | _ a b =>
      have hab : (D.core i).graph.Adj a b := by simpa using hz
      have hi : i ∈ D.retainedComponentIndices 0 (Fintype.card V) := by
        rw [D.retainedComponentIndices_all]
        exact Finset.mem_univ _
      rcases lt_or_gt_of_ne hab.ne with hlt | hgt
      · exact ⟨⟨i, hi, a, b, hlt, hab⟩, rfl⟩
      · refine ⟨⟨i, hi, b, a, hgt, hab.symm⟩, ?_⟩
        simp only [retainedAllActiveCoreEdgeMap, Sigma.mk.inj_iff, heq_eq_eq,
          true_and, Subtype.mk.injEq, Sym2.eq_swap]

/-- Each actual active coordinate is precisely one unordered core edge;
its capacity is the product of the two actual part sizes. -/
theorem retainedActiveCapacity_all_eq_sum_weightedEdgeCapacity
    (D : SubcriticalDivision k V) :
    (∑ e : RetainedActivePair D 0 (Fintype.card V),
      (retainedActiveCapacity D 0 (Fintype.card V) e : ℝ)) =
      ∑ i : Fin D.componentCount,
        DenseGraph.weightedEdgeCapacity (D.core i).graph
          (fun j ↦ ((D.parts i j).card : ℝ)) := by
  let E := Equiv.ofBijective (retainedAllActiveCoreEdgeMap D)
    (retainedAllActiveCoreEdgeMap_bijective D)
  calc
    _ = ∑ p : Σ i : Fin D.componentCount, ↥(D.core i).graph.edgeFinset,
        Sym2.lift ⟨(fun u v ↦ ((D.parts p.1 u).card : ℝ) * (D.parts p.1 v).card),
          fun _ _ ↦ mul_comm _ _⟩ p.2.val := by
      apply Fintype.sum_equiv E
      intro e
      change (((D.parts e.component e.left).card *
        (D.parts e.component e.right).card : ℕ) : ℝ) =
        ((D.parts e.component e.left).card : ℝ) * (D.parts e.component e.right).card
      exact Nat.cast_mul _ _
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_coe_sort _
        (Sym2.lift ⟨fun u v ↦ ((D.parts i u).card : ℝ) * (D.parts i v).card,
          fun _ _ ↦ mul_comm _ _⟩)

/-- The degree-based quadratic estimate, summed over all retained cores. -/
theorem retainedActiveCapacity_all_le_half_sum_sq
    (D : SubcriticalDivision k V) :
    (∑ e : RetainedActivePair D 0 (Fintype.card V),
      (retainedActiveCapacity D 0 (Fintype.card V) e : ℝ)) ≤
      ((k - 2 : ℕ) : ℝ) / 2 * ∑ a : D.PartIndex, ((D.part a).card : ℝ)^2 := by
  rw [retainedActiveCapacity_all_eq_sum_weightedEdgeCapacity]
  calc
    _ ≤ ∑ i : Fin D.componentCount,
        ((k - 2 : ℕ) : ℝ) / 2 * ∑ j, ((D.parts i j).card : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro i _
      exact DenseGraph.weightedEdgeCapacity_le_regular_half_sum_sq
        (D.core i).graph (D.core i).regular _
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact (Fintype.sum_sigma (fun a : D.PartIndex ↦ ((D.part a).card : ℝ)^2)).symm

/-- Exact active/clique comparison for a retained key, including the empty
key. The error is `((k - 2) / 2) * |support|`, not an unspecified `O(n)`. -/
theorem retainedKey_activeCapacity_le_cliqueCapacity_add_linear
    (K : SubcriticalRetainedKey k V) :
    (∑ e : K.ActiveIndex, (K.activeCapacity e : ℝ)) ≤
      ((k - 2 : ℕ) : ℝ) * K.cliqueCapacity +
        ((k - 2 : ℕ) : ℝ) / 2 * K.support.card := by
  cases K with
  | none =>
    have hz : (∑ e : SubcriticalRetainedKey.ActiveIndex (none : SubcriticalRetainedKey k V),
        (SubcriticalRetainedKey.activeCapacity none e : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      exact Empty.elim e
    rw [hz]
    simp [SubcriticalRetainedKey.cliqueCapacity, SubcriticalRetainedKey.cliqueEdges,
      SubcriticalRetainedKey.support]
  | some D =>
    have h := retainedActiveCapacity_all_le_half_sum_sq D
    rw [retainedCliqueCapacity_all_square_identity] at h
    have hcap : (∑ e : SubcriticalRetainedKey.ActiveIndex (some D),
        (SubcriticalRetainedKey.activeCapacity (some D) e : ℝ)) =
        ∑ e : RetainedActivePair D 0 (Fintype.card V),
          (retainedActiveCapacity D 0 (Fintype.card V) e : ℝ) := by
      apply Finset.sum_congr rfl
      intro e _
      change ((retainedActivePotentialEdges D 0 (Fintype.card V) e).card : ℝ) = _
      exact congrArg (Nat.cast (R := ℝ))
        (retainedActivePotentialEdges_card D 0 (Fintype.card V) e)
    rw [hcap]
    change _ ≤ ((k - 2 : ℕ) : ℝ) *
      (retainedCliquePotentialEdges D 0 (Fintype.card V)).card +
        ((k - 2 : ℕ) : ℝ) / 2 * D.support.card
    rw [retainedCliquePotentialEdges_card]
    nlinarith

end InducedStars
