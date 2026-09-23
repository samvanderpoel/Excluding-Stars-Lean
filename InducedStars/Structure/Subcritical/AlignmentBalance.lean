import InducedStars.Structure.Subcritical.RealizedCells
import InducedStars.Structure.Subcritical.Compatibility
import Mathlib.Data.Finset.SymmDiff

/-!
# Balance consequences of constructed cell matching

Paper: the balance and visible-component conclusions in
`lemma:WtoWtildeMetricsK1k`.  These are finite numerical consequences of
explicit symmetric-difference bounds and one actual core isomorphism.
The rounding error comes from the existing literal sampled-cell estimate.
-/

noncomputable section

open Finset
open scoped BigOperators Classical symmDiff

namespace InducedStars

variable {k n : ℕ} {V : Type*} [DecidableEq V]

/-- Changing a finite set changes its cardinality by at most the number of
vertices in the symmetric difference. -/
theorem subcritical_abs_card_sub_le_card_symmDiff (A B : Finset V) :
    |(A.card : ℝ) - B.card| ≤ (A ∆ B).card := by
  have ha : (A.card : ℝ) ≤ (A \ B).card + (B.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := A) (t := B))
  have hb : (B.card : ℝ) ≤ (B \ A).card + (A.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := B) (t := A))
  have had : ((A \ B).card : ℝ) ≤ (A ∆ B).card := by
    exact_mod_cast (Finset.card_le_card (Finset.symmDiff_subset_sdiff (s := A) (t := B)))
  have hbd : ((B \ A).card : ℝ) ≤ (A ∆ B).card := by
    exact_mod_cast (Finset.card_le_card (Finset.symmDiff_subset_sdiff' (s := A) (t := B)))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable [Fintype V]

/-- The absolute, rather than normalized, rounding error of an aligned
sampled candidate cell is at most two vertices. -/
theorem subcritical_aligned_cell_size_error_le_two
    (hn : 0 < n) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) (j : ℕ) (u : Fin (L.core j).order) :
    |((subcriticalAlignedReferenceCellVertices L n pi ⟨j, u⟩).card : ℝ) -
      L.alpha j * n / (L.core j).order| ≤ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : (0 : ℝ) < (L.core j).order := by exact_mod_cast (L.core j).order_pos
  have h := abs_card_subcriticalAlignedReferenceCellVertices_div_sub_le hn L pi j u
  have heq : ((subcriticalAlignedReferenceCellVertices L n pi ⟨j, u⟩).card : ℝ) / n -
      L.alpha j / (L.core j).order =
      (((subcriticalAlignedReferenceCellVertices L n pi ⟨j, u⟩).card : ℝ) -
        L.alpha j * n / (L.core j).order) / n := by
    field_simp
  rw [heq, abs_div, abs_of_pos hnR] at h
  have h' := (div_le_iff₀ hnR).mp h
  simpa only [div_mul_cancel₀ _ hnR.ne'] using h'

/-- A matched part differs from the exact common candidate-cell size by
the symmetric-difference error plus the two-vertex sampling error. -/
theorem subcritical_part_size_error_of_cell_matching
    (hn : 0 < n) (D : SubcriticalDivision k (Fin n))
    (L : AdmissibleBlockSequence k) (pi : Equiv.Perm (Fin n))
    (i : Fin D.componentCount) (j : ℕ)
    (e : (D.core i).graph ≃g (L.core j).graph) {s : ℝ}
    (hmatch : ∀ u,
      ((D.parts i u ∆ subcriticalAlignedReferenceCellVertices L n pi ⟨j, e u⟩).card : ℝ)
        ≤ s)
    (u : Fin (D.core i).order) :
    |((D.parts i u).card : ℝ) - L.alpha j * n / (D.core i).order| ≤ s + 2 := by
  have horder : (D.core i).order = (L.core j).order := by simpa using e.card_eq
  have hc := subcritical_aligned_cell_size_error_le_two hn L pi j (e u)
  have hc' :
      |((subcriticalAlignedReferenceCellVertices L n pi ⟨j, e u⟩).card : ℝ) -
        L.alpha j * n / (D.core i).order| ≤ 2 := by
    simpa only [horder] using hc
  exact (abs_sub_le _ _ _).trans
    (add_le_add ((subcritical_abs_card_sub_le_card_symmDiff _ _).trans (hmatch u)) hc')

/-- A common absolute error for all part sizes sums to the order times
that error for the total component size. -/
theorem subcritical_component_total_error_of_part_errors
    (D : SubcriticalDivision k V) (i : Fin D.componentCount) {z E : ℝ}
    (herr : ∀ u, |((D.parts i u).card : ℝ) - z| ≤ E) :
    |((D.componentSupport i).card : ℝ) - (D.core i).order * z| ≤
      (D.core i).order * E := by
  have heq : ((D.componentSupport i).card : ℝ) - (D.core i).order * z =
      ∑ u : Fin (D.core i).order, (((D.parts i u).card : ℝ) - z) := by
    simp [D.card_componentSupport i, Finset.sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ u : Fin (D.core i).order, |((D.parts i u).card : ℝ) - z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u : Fin (D.core i).order, E := Finset.sum_le_sum fun u _ ↦ herr u
    _ = _ := by simp

/-- The mean of the parts stays within their common error of the reference
center; consequently every part is within twice that error of its mean. -/
theorem subcritical_part_mean_error_of_part_errors
    (D : SubcriticalDivision k V) (i : Fin D.componentCount) {z E : ℝ}
    (herr : ∀ u, |((D.parts i u).card : ℝ) - z| ≤ E)
    (u : Fin (D.core i).order) :
    |((D.parts i u).card : ℝ) -
      (D.componentSupport i).card / (D.core i).order| ≤ 2 * E := by
  have hr : (0 : ℝ) < (D.core i).order := by exact_mod_cast (D.core i).order_pos
  have ht := subcritical_component_total_error_of_part_errors D i herr
  have hm : |(D.componentSupport i).card / (D.core i).order - z| ≤ E := by
    have heq : (D.componentSupport i).card / ((D.core i).order : ℝ) - z =
        ((D.componentSupport i).card - (D.core i).order * z) / (D.core i).order := by
      field_simp
    rw [heq, abs_div, abs_of_pos hr]
    apply (div_le_iff₀ hr).mpr
    nlinarith
  calc
    _ = |(((D.parts i u).card : ℝ) - z) -
        ((D.componentSupport i).card / (D.core i).order - z)| := by ring_nf
    _ ≤ |((D.parts i u).card : ℝ) - z| +
        |(D.componentSupport i).card / (D.core i).order - z| := abs_sub _ _
    _ ≤ 2 * E := by linarith [herr u]

/-- The candidate-block specialization of the summed part-error bound. -/
theorem subcritical_component_size_error_of_part_errors
    (D : SubcriticalDivision k (Fin n)) (i : Fin D.componentCount)
    {a err : ℝ}
    (herr : ∀ u, |((D.parts i u).card : ℝ) -
      a * n / (D.core i).order| ≤ err * n) :
    |((D.componentSupport i).card : ℝ) - a * n| ≤
      (D.core i).order * err * n := by
  have hr : ((D.core i).order : ℝ) ≠ 0 := by
    exact_mod_cast (D.core i).order_pos.ne'
  have h := subcritical_component_total_error_of_part_errors D i herr
  have heq : ((D.core i).order : ℝ) * (a * n / (D.core i).order) = a * n := by
    field_simp
  simpa only [heq, mul_assoc] using h

/-- Any two parts with the same reference center differ by at most twice
their common absolute error. -/
theorem subcritical_part_pair_error_of_part_errors
    (D : SubcriticalDivision k V) (i : Fin D.componentCount) {z E : ℝ}
    (herr : ∀ u, |((D.parts i u).card : ℝ) - z| ≤ E)
    (u v : Fin (D.core i).order) :
    |((D.parts i u).card : ℝ) - (D.parts i v).card| ≤ 2 * E := by
  calc
    _ ≤ |((D.parts i u).card : ℝ) - z| + |z - (D.parts i v).card| := abs_sub_le _ _ _
    _ = |((D.parts i u).card : ℝ) - z| + |((D.parts i v).card : ℝ) - z| := by
      rw [abs_sub_comm z]
    _ ≤ 2 * E := by linarith [herr u, herr v]

/-- The two requested bounded-order balance conclusions follow from one
explicit common-center error and the displayed numerical reserves. -/
theorem subcritical_bounded_order_balance_of_part_errors
    (D : SubcriticalDivision k (Fin n)) (i : Fin D.componentCount)
    {R₀ : ℕ} {z err lambda alpha omega : ℝ}
    (halpha : 0 ≤ alpha) (homega : 0 ≤ omega)
    (horder : (D.core i).order ≤ R₀)
    (hlarge : lambda * n ≤ (D.componentSupport i).card)
    (hbalance : 2 * err ≤ min alpha (omega / (4 * R₀)) * lambda)
    (hlower : 2 * err ≤ lambda / (2 * R₀))
    (herr : ∀ u, |((D.parts i u).card : ℝ) - z| ≤ err * n)
    (u : Fin (D.core i).order) :
    |((D.parts i u).card : ℝ) -
        (D.componentSupport i).card / (D.core i).order| ≤
        min alpha (omega / (4 * (D.core i).order)) * (D.componentSupport i).card ∧
      (D.componentSupport i).card / (2 * (R₀ : ℝ)) ≤ (D.parts i u).card := by
  have hr : (0 : ℝ) < (D.core i).order := by exact_mod_cast (D.core i).order_pos
  have hR : (0 : ℝ) < R₀ := by exact_mod_cast lt_of_lt_of_le (D.core i).order_pos horder
  have hrR : ((D.core i).order : ℝ) ≤ R₀ := by exact_mod_cast horder
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hv0 : (0 : ℝ) ≤ (D.componentSupport i).card := Nat.cast_nonneg _
  have hmin0 : 0 ≤ min alpha (omega / (4 * R₀)) :=
    le_min halpha (div_nonneg homega (by positivity))
  have hquot : omega / (4 * (R₀ : ℝ)) ≤ omega / (4 * (D.core i).order) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * R₀)
      (by positivity : (0 : ℝ) < 4 * (D.core i).order)).mpr
    nlinarith
  have hmin := min_le_min_left alpha hquot
  have hbudget : 2 * err * n ≤
      min alpha (omega / (4 * (D.core i).order)) * (D.componentSupport i).card := by
    calc
      _ ≤ min alpha (omega / (4 * R₀)) * lambda * n :=
        mul_le_mul_of_nonneg_right hbalance hn0
      _ = min alpha (omega / (4 * R₀)) * (lambda * n) := by ring
      _ ≤ min alpha (omega / (4 * R₀)) * (D.componentSupport i).card :=
        mul_le_mul_of_nonneg_left hlarge hmin0
      _ ≤ _ := mul_le_mul_of_nonneg_right hmin hv0
  have hm := subcritical_part_mean_error_of_part_errors D i herr u
  constructor
  · nlinarith
  · have hbudget' : 2 * err * n ≤
        (D.componentSupport i).card / (2 * (R₀ : ℝ)) := by
      calc
        _ ≤ lambda / (2 * R₀) * n := mul_le_mul_of_nonneg_right hlower hn0
        _ = (lambda * n) / (2 * R₀) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hlarge (by positivity)
    have hmean : (D.componentSupport i).card / (R₀ : ℝ) ≤
        (D.componentSupport i).card / ((D.core i).order : ℝ) := by
      apply (div_le_div_iff₀ hR hr).mpr
      exact mul_le_mul_of_nonneg_left hrR hv0
    have hsplit : (D.componentSupport i).card / (R₀ : ℝ) =
        2 * ((D.componentSupport i).card / (2 * (R₀ : ℝ))) := by ring
    linarith [(abs_le.mp hm).1]

/-- A large part and a sufficiently small common-center error force every
part to have at least half its visibility threshold, and then give the
paper's `(1+omega)` ratio estimate. -/
theorem subcritical_visible_ratio_of_part_errors
    (D : SubcriticalDivision k (Fin n)) (i : Fin D.componentCount)
    {z err theta omega : ℝ} (homega : 0 ≤ omega)
    (hsmall : err ≤ theta / 4) (hratio : 2 * err ≤ omega * theta / 2)
    (herr : ∀ u, |((D.parts i u).card : ℝ) - z| ≤ err * n)
    (hvisible : ∃ u, theta * n ≤ (D.parts i u).card)
    (u v : Fin (D.core i).order) :
    ((D.parts i u).card : ℝ) ≤ (1 + omega) * (D.parts i v).card := by
  obtain ⟨w, hw⟩ := hvisible
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hdiff := subcritical_part_pair_error_of_part_errors D i herr w v
  have hsmall' := mul_le_mul_of_nonneg_right hsmall hn0
  have hv : theta * n / 2 ≤ ((D.parts i v).card : ℝ) := by
    linarith [(abs_le.mp hdiff).2]
  have hratio' := mul_le_mul_of_nonneg_right hratio hn0
  have hmul := mul_le_mul_of_nonneg_left hv homega
  have huv := subcritical_part_pair_error_of_part_errors D i herr u v
  nlinarith [(abs_le.mp huv).2]

end InducedStars
