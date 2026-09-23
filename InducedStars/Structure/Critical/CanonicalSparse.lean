import InducedStars.Structure.Critical.FiniteGeometry

/-!
# Canonical sparse sets for clean critical divisions

This file records a deterministic transfer from a displayed zero-defect
division to a defect-cost-minimizing division.  The proof uses only the exact
one-vertex move identities for the minimizing division.

The two inclusions use different elementary observations.  A displayed sparse
vertex has no neighbours in the displayed support, so it cannot occupy a large
canonical main part.  Conversely, a displayed main-part vertex has many
neighbours in that displayed clique; if the canonical sparse set is small,
putting it there contradicts the sum of the sparse-to-main move inequalities.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The displayed sparse set is canonical-sparse -/

/-- A defect-cost-minimizing division cannot put a vertex of a displayed
zero-defect sparse set into a main part whose size is more than twice the
displayed sparse size.

This statement is deliberately formulated for an arbitrary minimizer; the
canonical specialization below supplies `minimal` from `argminOn`. -/
theorem displayedSparse_subset_sparse_of_clean_minimal
    (G : SimpleGraph V) (D E : SupercriticalDivision k V)
    (hclean : supercriticalDefectGraph G D = ⊥)
    (minimal : ∀ F : SupercriticalDivision k V,
      supercriticalDefectCost G E ≤ supercriticalDefectCost G F)
    (hpart : ∀ i : Fin (k - 1),
      2 * D.sparse.card < (E.parts i).card) :
    D.sparse ⊆ E.sparse := by
  classical
  intro v hvD
  rw [SupercriticalDivision.mem_sparse]
  intro hvSupport
  obtain ⟨i, hvi⟩ := SupercriticalDivision.mem_support.mp hvSupport
  have hsPos : 0 < D.sparse.card := Finset.card_pos.mpr ⟨v, hvD⟩
  have hiLarge := hpart i
  have hremain : ((E.parts i).erase v).Nonempty := by
    rw [← Finset.card_pos]
    rw [Finset.card_erase_of_mem hvi]
    omega
  have hmove :=
    SupercriticalDivision.supercriticalDefectCost_moveMainToSparse_add
      G E i v hvi hremain
  have hmin := minimal (E.moveMainToSparse i v hvi hremain)
  have hcomp_le_degree :
      complementDegreeInFinset G v (E.parts i) ≤
        degreeInFinset G v E.support := by
    omega
  have hdegree_le : degreeInFinset G v E.support ≤ D.sparse.card := by
    unfold degreeInFinset
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter] at hx
    have hxSupportE : x ∈ E.support := hx.1
    have hxAdj : G.Adj v x := hx.2
    by_contra hxSparseD
    have hxSupportD : x ∈ D.support := by
      simpa [SupercriticalDivision.mem_sparse] using hxSparseD
    exact (not_adj_support_sparse_of_supercriticalDefectGraph_eq_bot
      G D hclean hxSupportD hvD) hxAdj.symm
  let B : Finset V := E.parts i \ D.sparse
  have hBcomp : B.card ≤ complementDegreeInFinset G v (E.parts i) := by
    unfold complementDegreeInFinset
    apply Finset.card_le_card
    intro x hx
    simp only [B, Finset.mem_sdiff] at hx
    simp only [Finset.mem_filter]
    have hxSupportD : x ∈ D.support := by
      simpa [SupercriticalDivision.mem_sparse] using hx.2
    have hxne : x ≠ v := by
      intro hxv
      subst x
      exact (SupercriticalDivision.mem_sparse.mp hvD) hxSupportD
    have hnonadj : ¬G.Adj x v :=
      not_adj_support_sparse_of_supercriticalDefectGraph_eq_bot
        G D hclean hxSupportD hvD
    exact ⟨hx.1, hxne, by simpa [G.adj_comm] using hnonadj⟩
  have hpart_card : (E.parts i).card ≤ B.card + D.sparse.card := by
    have hsubset : E.parts i ⊆ B ∪ D.sparse := by
      intro x hx
      by_cases hxs : x ∈ D.sparse
      · exact Finset.mem_union_right B hxs
      · exact Finset.mem_union_left D.sparse (by
          exact Finset.mem_sdiff.mpr ⟨hx, hxs⟩)
    exact (Finset.card_le_card hsubset).trans (Finset.card_union_le B D.sparse)
  have : (E.parts i).card ≤ 2 * D.sparse.card := by
    calc
      (E.parts i).card ≤ B.card + D.sparse.card := hpart_card
      _ ≤ complementDegreeInFinset G v (E.parts i) + D.sparse.card :=
        Nat.add_le_add_right hBcomp _
      _ ≤ degreeInFinset G v E.support + D.sparse.card :=
        Nat.add_le_add_right hcomp_le_degree _
      _ ≤ D.sparse.card + D.sparse.card :=
        Nat.add_le_add_right hdegree_le _
      _ = 2 * D.sparse.card := by omega
  exact (Nat.not_lt_of_ge this) (hpart i)

/-! ## The canonical sparse set lies in the displayed sparse set -/

/-- If every displayed main part remains large after paying for the whole
minimizer sparse set and one distinguished vertex, a minimizer cannot put a
displayed support vertex into its sparse set.

The quantitative hypothesis is the exact natural-number inequality used by
the proof.  Coarse balance of `D`, smallness of `E.sparse`, and sufficiently
large ambient size imply it in the critical application. -/
theorem sparse_subset_displayedSparse_of_clean_minimal
    (G : SimpleGraph V) (D E : SupercriticalDivision k V)
    (hk : 3 ≤ k)
    (hclean : supercriticalDefectGraph G D = ⊥)
    (minimal : ∀ F : SupercriticalDivision k V,
      supercriticalDefectCost G E ≤ supercriticalDefectCost G F)
    (hpart : ∀ i : Fin (k - 1),
      Fintype.card V <
        k * ((D.parts i).card - (E.sparse.card + 1))) :
    E.sparse ⊆ D.sparse := by
  classical
  intro v hvE
  rw [SupercriticalDivision.mem_sparse]
  intro hvSupportD
  obtain ⟨a, hva⟩ := SupercriticalDivision.mem_support.mp hvSupportD
  have hdegree_le_comp : ∀ i : Fin (k - 1),
      degreeInFinset G v E.support ≤
        complementDegreeInFinset G v (E.parts i) := by
    intro i
    have hmove :=
      SupercriticalDivision.supercriticalDefectCost_moveSparseToMain_add
        G E i v hvE
    have hmin := minimal (E.moveSparseToMain i v hvE)
    omega
  have hsum :
      (k - 1) * degreeInFinset G v E.support ≤
        complementDegreeInFinset G v E.support := by
    calc
      (k - 1) * degreeInFinset G v E.support =
          ∑ _i : Fin (k - 1), degreeInFinset G v E.support := by simp
      _ ≤ ∑ i : Fin (k - 1),
          complementDegreeInFinset G v (E.parts i) :=
        Finset.sum_le_sum fun i _ ↦ hdegree_le_comp i
      _ = complementDegreeInFinset G v E.support := by
        rw [complementDegreeInFinset_support_eq_sum]
  have hvNotSupportE : v ∉ E.support :=
    SupercriticalDivision.mem_sparse.mp hvE
  have hdegree_add :=
    degreeInFinset_add_complementDegreeInFinset G v E.support
  rw [Finset.erase_eq_self.mpr hvNotSupportE] at hdegree_add
  have hkSplit : (k - 1) + 1 = k := by omega
  have hkdegree :
      k * degreeInFinset G v E.support ≤ E.support.card := by
    calc
      k * degreeInFinset G v E.support =
          ((k - 1) + 1) * degreeInFinset G v E.support := by rw [hkSplit]
      _ = (k - 1) * degreeInFinset G v E.support +
          degreeInFinset G v E.support := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ complementDegreeInFinset G v E.support +
          degreeInFinset G v E.support := Nat.add_le_add_right hsum _
      _ = E.support.card := by omega
  have hkdegree_ambient :
      k * degreeInFinset G v E.support ≤ Fintype.card V :=
    hkdegree.trans (Finset.card_le_card (Finset.subset_univ E.support))
  let A : Finset V := D.parts a \ insert v E.sparse
  have hAdegree : A.card ≤ degreeInFinset G v E.support := by
    unfold degreeInFinset
    apply Finset.card_le_card
    intro x hx
    simp only [A, Finset.mem_sdiff, Finset.mem_insert] at hx
    simp only [Finset.mem_filter]
    have hxne : x ≠ v := fun hxv ↦ hx.2 (Or.inl hxv)
    have hxNotSparseE : x ∉ E.sparse := fun hxs ↦ hx.2 (Or.inr hxs)
    have hxSupportE : x ∈ E.support := by
      simpa [SupercriticalDivision.mem_sparse] using hxNotSparseE
    have hxAdj : G.Adj v x :=
      mainParts_clique_of_supercriticalDefectGraph_eq_bot
        G D hclean a hva hx.1 (Ne.symm hxne)
    exact ⟨hxSupportE, hxAdj⟩
  have hDpart_card :
      (D.parts a).card ≤ A.card + (E.sparse.card + 1) := by
    have hsubset : D.parts a ⊆ A ∪ insert v E.sparse := by
      intro x hx
      by_cases hxin : x ∈ insert v E.sparse
      · exact Finset.mem_union_right A hxin
      · exact Finset.mem_union_left (insert v E.sparse)
          (Finset.mem_sdiff.mpr ⟨hx, hxin⟩)
    calc
      (D.parts a).card ≤ (A ∪ insert v E.sparse).card :=
        Finset.card_le_card hsubset
      _ ≤ A.card + (insert v E.sparse).card :=
        Finset.card_union_le A (insert v E.sparse)
      _ ≤ A.card + (E.sparse.card + 1) := by
        exact Nat.add_le_add_left (Finset.card_insert_le v E.sparse) A.card
  have hlower :
      (D.parts a).card - (E.sparse.card + 1) ≤
        degreeInFinset G v E.support := by
    have hsub : (D.parts a).card - (E.sparse.card + 1) ≤ A.card := by
      omega
    exact hsub.trans hAdegree
  have hmul := Nat.mul_le_mul_left k hlower
  have hambient_lt :
      Fintype.card V < k * degreeInFinset G v E.support :=
    (hpart a).trans_le hmul
  exact (Nat.not_lt_of_ge hkdegree_ambient) hambient_lt

/-! ## Canonical specialization -/

/-- Under the two explicit size inequalities, a displayed clean division and
the canonical minimizing division have exactly the same sparse set. -/
theorem canonicalSupercriticalDivision_sparse_eq_of_clean
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (hk : 3 ≤ k) (hcard : k - 1 ≤ Fintype.card V)
    (hclean : supercriticalDefectGraph G D = ⊥)
    (hcanonicalParts : ∀ i : Fin (k - 1),
      2 * D.sparse.card <
        ((canonicalSupercriticalDivision G hcard).parts i).card)
    (hdisplayedParts : ∀ i : Fin (k - 1),
      Fintype.card V <
        k * ((D.parts i).card -
          ((canonicalSupercriticalDivision G hcard).sparse.card + 1))) :
    (canonicalSupercriticalDivision G hcard).sparse = D.sparse := by
  apply Finset.Subset.antisymm
  · exact sparse_subset_displayedSparse_of_clean_minimal
      G D (canonicalSupercriticalDivision G hcard) hk hclean
      (fun F ↦ canonicalSupercriticalDivision_minimal G hcard F)
      hdisplayedParts
  · exact displayedSparse_subset_sparse_of_clean_minimal
      G D (canonicalSupercriticalDivision G hcard) hclean
      (fun F ↦ canonicalSupercriticalDivision_minimal G hcard F)
      hcanonicalParts

end InducedStars
