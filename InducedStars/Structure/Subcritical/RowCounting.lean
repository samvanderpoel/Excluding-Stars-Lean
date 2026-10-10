import InducedStars.Structure.Subcritical.ClosenessResult

/-!
# Local counting scales and grouped visible role sets

The deterministic row arguments count only free vertices, retaining
the prescribed root separately. Repeated parent parts are grouped before
using the visible-set cut corollary; the roles themselves remain disjoint.
-/

noncomputable section

open Finset DenseGraph DenseGraph.FiniteWeightedGraph
open scoped BigOperators Classical

namespace InducedStars

/-- Distinct parent parts have weight zero or `pK`, never the forced
clique value. This applies to every required nonedge of a row pattern. -/
theorem subcriticalDivisionPartWeight_le_pK_of_ne
    {k n : ℕ} (D : SubcriticalDivision k (Fin n))
    {a b : D.PartIndex} (hab : a ≠ b) :
    subcriticalDivisionPartWeight D a b ≤ pK k := by
  unfold subcriticalDivisionPartWeight
  simp only [hab, ite_false]
  split_ifs
  · exact le_rfl
  · exact (pK_mem_Icc k).1

/-- An auxiliary scalar inequality, independent of the current non-low proof. -/
theorem subcritical_one_quarter_lt_pK_five : (1 / 4 : ℝ) < pK 5 := by
  apply (lt_pK_iff_lt_pow (by norm_num : 2 ≤ 5) (by norm_num : (1 / 4 : ℝ) < 1)).mpr
  norm_num

/-- The same root comparison places the elementary tripartite counterexample
above the inverse-core-degree threshold at `k=3`. -/
theorem subcritical_three_tenths_lt_pK_three : (3 / 10 : ℝ) < pK 3 := by
  apply (lt_pK_iff_lt_pow (by norm_num : 2 ≤ 3) (by norm_num : (3 / 10 : ℝ) < 1)).mpr
  norm_num

/-- The role-volume factor is included: `k` equal disjoint classes in their
union each have mass `1/k`. -/
def subcriticalRowCountingLower (k : ℕ) : ℝ :=
  (1 / (k : ℝ)) ^ k * (subcriticalPaletteGap k) ^ (Nat.choose k 2)

/-- One safe error tolerance for all three `k`-free-vertex configurations. -/
def subcriticalRowCountingTolerance (k : ℕ) : ℝ :=
  subcriticalRowCountingLower k / (4 * ((Nat.choose k 2 : ℝ) + 1))

theorem subcriticalRowCountingLower_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < subcriticalRowCountingLower k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  unfold subcriticalRowCountingLower
  exact mul_pos (pow_pos (div_pos zero_lt_one hkR) _) (pow_pos (subcriticalPaletteGap_pos hk) _)

theorem subcriticalRowCountingTolerance_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < subcriticalRowCountingTolerance k := by
  exact div_pos (subcriticalRowCountingLower_pos hk) (by positivity)

theorem subcriticalRowCountingTolerance_preserves_positive {k : ℕ} (hk : 3 ≤ k) :
    (Nat.choose k 2 : ℝ) * subcriticalRowCountingTolerance k <
      subcriticalRowCountingLower k := by
  have hL := subcriticalRowCountingLower_pos hk
  have hM : (0 : ℝ) ≤ Nat.choose k 2 := Nat.cast_nonneg _
  unfold subcriticalRowCountingTolerance
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * ((Nat.choose k 2 : ℝ) + 1))).mpr
  nlinarith

namespace SubcriticalCloseStructureResult

variable {k n R₀ : ℕ} {hk : 3 ≤ k}
  {G : SimpleGraph (Fin n)} {D : SubcriticalDivision k (Fin n)}
  {L : AdmissibleBlockSequence k} {omega eta theta alpha delta epsilon : ℝ}

/-- Group any repeated parent indices before invoking the visible-set
corollary. There is one selected subset per parent, even if several free
roles are contained in that parent part. No new relabeling is used. -/
theorem groupedRoles_visibleSetCutCloseness
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (halpha : 0 < alpha) (htheta : 0 < theta)
    {I : Type*} [Fintype I] [DecidableEq I]
    (parent : I → {a : D.PartIndex // a ∈ D.visiblePartIndices theta})
    (S : I → Finset (Fin n))
    (hpart : ∀ i, S i ⊆ D.part (parent i).val)
    (hsize : ∀ i, alpha * theta * n / 4 ≤ ((S i).card : ℝ)) :
    finiteLabeledCutDist
      ((ofSimpleGraph G).restrictToFinset (visibleCutPartUnion S))
      ((subcriticalDivisionWeightedGraph hk D).restrictToFinset
        (visibleCutPartUnion S)) ≤ delta := by
  classical
  let J := Finset.univ.image parent
  let index : J ↪ {a : D.PartIndex // a ∈ D.visiblePartIndices theta} :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let grouped (a : J) : Finset (Fin n) :=
    Finset.univ.biUnion fun i ↦ if parent i = a.val then S i else ∅
  have hsub (i : I) (a : J) (h : parent i = a.val) : S i ⊆ grouped a := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa [h] using hx⟩
  have hgpart (a : J) : grouped a ⊆ D.part (index a).val := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    by_cases h : parent i = a.val
    · have hi' : x ∈ S i := by simpa [h] using hi
      simpa only [index, Function.Embedding.coeFn_mk, h] using hpart i hi'
    · simp [h] at hi
  have hgsize (a : J) : alpha * theta * n / 4 ≤ ((grouped a).card : ℝ) := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp a.property
    exact (hsize i).trans (by exact_mod_cast Finset.card_le_card (hsub i a hi))
  have hunion : visibleCutPartUnion grouped = visibleCutPartUnion S := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
      by_cases h : parent i = a.val
      · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simpa [h] using hi⟩
      · simp [h] at hi
    · intro hx
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
      let a : J := ⟨parent i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hsub i a rfl hi⟩
  have h := R.visibleSetCutCloseness halpha htheta index grouped hgpart hgsize
  rwa [hunion] at h

end SubcriticalCloseStructureResult
end InducedStars
