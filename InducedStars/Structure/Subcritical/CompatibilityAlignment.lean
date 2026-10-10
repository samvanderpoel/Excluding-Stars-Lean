import InducedStars.Structure.Subcritical.AlignmentWitness
import InducedStars.Structure.Subcritical.AlignmentBalance

/-!
# Candidate compatibility from constructed component alignment

Paper: the compatibility conclusion of `lemma:WtoWtildeMetricsK1k`.
The assignment is a restriction of the one constructed component injection.
Coverage of every large bounded-order candidate block proves the exact
unmatched-block clause of the existing compatibility definition.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

variable {k n : ℕ}

/-- A component whose total size reaches its order times a part threshold
has a part reaching that threshold. -/
theorem subcritical_visible_of_order_mul_threshold_le_size
    (D : SubcriticalDivision k (Fin n)) (i : Fin D.componentCount) (t : ℝ)
    (hsize : (D.core i).order * (t * n) ≤ (D.componentSupport i).card) :
    i ∈ D.visibleComponentIndices t := by
  apply (D.mem_visibleComponentIndices t i).mpr
  simp only [Fintype.card_fin]
  by_contra h
  have hall (u : Fin (D.core i).order) : ((D.parts i u).card : ℝ) < t * n :=
    lt_of_not_ge (fun hu ↦ h ⟨u, hu⟩)
  have hsum : (∑ u : Fin (D.core i).order, ((D.parts i u).card : ℝ)) <
      ∑ _u : Fin (D.core i).order, t * n := by
    apply Finset.sum_lt_sum (fun u _ ↦ (hall u).le)
    exact ⟨⟨0, (D.core i).order_pos⟩, Finset.mem_univ _, hall _⟩
  have heq : (∑ u : Fin (D.core i).order, ((D.parts i u).card : ℝ)) =
      (D.componentSupport i).card := by simp [D.card_componentSupport i]
  rw [heq] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith

/-- The stronger bounded-order size threshold used for balance already
forces visibility at the common auxiliary scale `t`. -/
theorem subcritical_smallOrder_large_component_visible
    (D : SubcriticalDivision k (Fin n)) (i : Fin D.componentCount)
    {R₀ : ℕ} {t eta : ℝ} (ht : 0 ≤ t) (hR : 1 ≤ R₀)
    (hteta : t ≤ eta / (8 * (R₀ : ℝ) ^ 2))
    (horder : (D.core i).order ≤ R₀)
    (hsize : eta * n / (4 * (R₀ : ℝ)) ≤ (D.componentSupport i).card) :
    i ∈ D.visibleComponentIndices t := by
  have hR1 : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < R₀ := by linarith
  have hbound := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (R₀ : ℝ) ^ 2)).mp hteta
  have hfour : 4 * (R₀ : ℝ) ^ 2 * t ≤ eta := by
    nlinarith [sq_nonneg (R₀ : ℝ)]
  have hcoeff : (R₀ : ℝ) * t ≤ eta / (4 * (R₀ : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * R₀)).mpr
    nlinarith
  apply subcritical_visible_of_order_mul_threshold_le_size D i t
  calc
    _ ≤ (R₀ : ℝ) * (t * n) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast horder) (mul_nonneg ht (Nat.cast_nonneg n))
    _ = ((R₀ : ℝ) * t) * n := by ring
    _ ≤ (eta / (4 * (R₀ : ℝ))) * n :=
      mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg n)
    _ = eta * n / (4 * (R₀ : ℝ)) := by ring
    _ ≤ _ := hsize

/-- Every cell of a large bounded-order candidate block reaches the
coverage threshold.  The literal two-vertex rounding error is retained. -/
theorem subcritical_large_smallOrder_block_cells_large
    (hn : 0 < n) (L : AdmissibleBlockSequence k) (pi : Equiv.Perm (Fin n))
    (j : ℕ) {R₀ : ℕ} {t eta : ℝ}
    (ht : 0 < t) (heta : 0 < eta) (hR : 1 ≤ R₀)
    (hteta : t ≤ eta / (8 * (R₀ : ℝ) ^ 2))
    (hround : 4 ≤ t * n / 4)
    (hlarge : eta ≤ L.alpha j) (horder : (L.core j).order ≤ R₀)
    (u : Fin (L.core j).order) :
    2 * t * n ≤ (subcriticalAlignedComponentCells L n pi j u).card := by
  have hR1 : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < R₀ := by linarith
  have hrpos : (0 : ℝ) < (L.core j).order := by exact_mod_cast (L.core j).order_pos
  have hrR : ((L.core j).order : ℝ) ≤ R₀ := by exact_mod_cast horder
  have hbound := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (R₀ : ℝ) ^ 2)).mp hteta
  have hpoly : 4 * (R₀ : ℝ) ≤ 8 * (R₀ : ℝ) ^ 2 := by nlinarith
  have hfour : 4 * t ≤ eta / (R₀ : ℝ) := by
    apply (le_div_iff₀ hRpos).mpr
    have hm := mul_le_mul_of_nonneg_left hpoly ht.le
    nlinarith
  have hquot : eta / (R₀ : ℝ) ≤ L.alpha j / (L.core j).order := by
    calc
      _ ≤ eta / ((L.core j).order : ℝ) := by
        apply (div_le_div_iff₀ hRpos hrpos).mpr
        exact mul_le_mul_of_nonneg_left hrR heta.le
      _ ≤ _ := div_le_div_of_nonneg_right hlarge hrpos.le
  have hmass := mul_le_mul_of_nonneg_right (hfour.trans hquot) (Nat.cast_nonneg n)
  have herr := subcritical_aligned_cell_size_error_le_two hn L pi j u
  have hsame : L.alpha j / ((L.core j).order : ℝ) * n =
      L.alpha j * n / (L.core j).order := by ring
  rw [hsame] at hmass
  change 2 * t * n ≤ (subcriticalAlignedReferenceCellVertices L n pi ⟨j, u⟩).card
  linarith [(abs_le.mp herr).1]

namespace SubcriticalComponentAlignment

variable {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
  {pi : Equiv.Perm (Fin n)} {t m : ℝ} {B : ℕ}

/-- The constructed symmetric-difference bound supplies the common
candidate-cell size error, including its actual rounding allowance. -/
theorem part_size_error_le
    (A : SubcriticalComponentAlignment D L pi t m B) (hn : 0 < n)
    {err : ℝ} (herror : ((B : ℝ) + 2) * m + 2 ≤ err * n)
    (i : {i // i ∈ D.visibleComponentIndices t}) (u : Fin (D.core i.val).order) :
    |((D.parts i.val u).card : ℝ) -
      L.alpha (A.assignment i).val * n / (D.core i.val).order| ≤ err * n := by
  exact (subcritical_part_size_error_of_cell_matching hn D L pi i.val
    (A.assignment i).val (A.coreIso i) (A.symmetric_difference i) u).trans herror

/-- Summing the matched part-size errors bounds the component's total
size against its assigned candidate block length. -/
theorem component_size_error_le
    (A : SubcriticalComponentAlignment D L pi t m B) (hn : 0 < n)
    {err : ℝ} (herror : ((B : ℝ) + 2) * m + 2 ≤ err * n)
    (i : {i // i ∈ D.visibleComponentIndices t}) :
    |((D.componentSupport i.val).card : ℝ) - L.alpha (A.assignment i).val * n| ≤
      (D.core i.val).order * err * n :=
  subcritical_component_size_error_of_part_errors D i.val
    (A.part_size_error_le hn herror i)

/-- Paper: the exact candidate compatibility in
`lemma:WtoWtildeMetricsK1k`, obtained by restricting the already constructed
component injection.  No independent choices of matches are made. -/
def toCandidateCompatibility
    (A : SubcriticalComponentAlignment D L pi t m B)
    (hn : 0 < n) {eta delta err : ℝ} {R₀ : ℕ}
    (ht : 0 < t) (heta : 0 < eta) (hR : 1 ≤ R₀)
    (hteta : t ≤ eta / (8 * (R₀ : ℝ) ^ 2))
    (hround : 4 ≤ t * n / 4) (hm : 0 < m)
    (herror : ((B : ℝ) + 2) * m + 2 ≤ err * n)
    (hdelta : (R₀ : ℝ) * err ≤ delta)
    (hetaerror : (R₀ : ℝ) * err ≤ eta / 2) : D.CandidateCompatibility L eta delta R₀ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hR1 : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < R₀ := by linarith
  have herrpos : 0 < err :=
    pos_of_mul_pos_left (lt_of_lt_of_le (by positivity) herror) hnR.le
  have hvis (i : Fin D.componentCount) (hi : i ∈ D.compatibilityComponentIndices eta R₀) :
      i ∈ D.visibleComponentIndices t := by
    obtain ⟨hlarge, horder⟩ := (D.mem_compatibilityComponentIndices eta R₀ i).mp hi
    apply subcritical_smallOrder_large_component_visible D i ht.le hR hteta horder
    have hfrac : eta * n / (4 * (R₀ : ℝ)) ≤ eta * n / 2 := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * R₀) (by norm_num)).mpr
      have hpos : 0 ≤ eta * (n : ℝ) := mul_nonneg heta.le hnR.le
      nlinarith
    exact hfrac.trans (by simpa only [Fintype.card_fin] using hlarge)
  let inc : {i // i ∈ D.compatibilityComponentIndices eta R₀} ↪
      {i // i ∈ D.visibleComponentIndices t} :=
    ⟨fun i ↦ ⟨i.val, hvis i.val i.property⟩, by
      intro i j hij
      exact Subtype.ext (congrArg
        (fun a : {i // i ∈ D.visibleComponentIndices t} ↦ a.val) hij)⟩
  refine
    { assignment := inc.trans A.assignment
      coreIso := fun i ↦ A.coreIso (inc i)
      size_error := ?_
      unmatched := ?_ }
  · intro i
    have horder := ((D.mem_compatibilityComponentIndices eta R₀ i.val).mp i.property).2
    have hbound : ((D.core i.val).order : ℝ) * err * n ≤ delta * n := by
      calc
        _ ≤ (R₀ : ℝ) * err * n := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by exact_mod_cast horder) herrpos.le) hnR.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hdelta hnR.le
    have hival : (inc i).val = i.val := rfl
    have htotal := A.component_size_error_le hn herror (inc i)
    rw [hival] at htotal
    simpa only [Function.Embedding.trans_apply, Fintype.card_fin] using
      htotal.trans hbound
  · intro j hj
    by_cases hsmall : L.alpha j.val < eta
    · exact Or.inl hsmall
    by_cases hlargeOrder : R₀ < (L.core j.val).order
    · exact Or.inr hlargeOrder
    have hlarge : eta ≤ L.alpha j.val := le_of_not_gt hsmall
    have horder : (L.core j.val).order ≤ R₀ := le_of_not_gt hlargeOrder
    obtain ⟨i, hi⟩ := A.covers_large_blocks j
      (subcritical_large_smallOrder_block_cells_large hn L pi j.val
        ht heta hR hteta hround hlarge horder)
    have heq : (D.core i.val).order = (L.core j.val).order := by
      have he := (A.coreIso i).card_eq
      simpa only [Fintype.card_fin, hi] using he
    have hiorder : (D.core i.val).order ≤ R₀ := heq.trans_le horder
    have htotal : |((D.componentSupport i.val).card : ℝ) - L.alpha j.val * n| ≤
        (D.core i.val).order * err * n := by
      simpa only [hi] using A.component_size_error_le hn herror i
    have hbound : ((D.core i.val).order : ℝ) * err * n ≤ eta / 2 * n := by
      calc
        _ ≤ (R₀ : ℝ) * err * n := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hiorder) herrpos.le) hnR.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hetaerror hnR.le
    have hisize : eta * n / 2 ≤ ((D.componentSupport i.val).card : ℝ) := by
      have hm := mul_le_mul_of_nonneg_right hlarge hnR.le
      linarith [(abs_le.mp htotal).1]
    let i' : {i // i ∈ D.compatibilityComponentIndices eta R₀} :=
      ⟨i.val, (D.mem_compatibilityComponentIndices eta R₀ i.val).mpr
        ⟨by simpa only [Fintype.card_fin] using hisize, hiorder⟩⟩
    have hinc : inc i' = i := Subtype.ext rfl
    apply False.elim
    apply hj i'
    change A.assignment (inc i') = j
    rw [hinc]
    exact hi

end SubcriticalComponentAlignment

end InducedStars
