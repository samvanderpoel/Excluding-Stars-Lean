import InducedStars.Structure.Subcritical.RetainedKeyFamilies

/-!
# One-block compatibility and the actual retained core

Only the retained key is identified. Nonretained components of a full
division remain unrestricted. These finite facts use the actual compatibility
injection, including its unmatched-block clause, not positivity of a model
partition function or an assumed uniqueness of the full division.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta delta mu : ℝ} {R₀ : ℕ}

namespace SubcriticalDivision.CandidateCompatibility

private theorem oneBlock_assignment_zero (hk : 3 ≤ k)
    (hmu0 : 0 < mu) (hmu1 : mu ≤ 1)
    (C : D.CandidateCompatibility (oneBlockSequence k hk mu hmu0 hmu1) eta delta R₀)
    (i : {i // i ∈ D.compatibilityComponentIndices eta R₀}) :
    (C.assignment i).val = 0 := by
  have h := (C.assignment i).property
  simpa only [oneBlockSequence, blockIndexActive, Nat.lt_one_iff] using h

theorem oneBlock_compatibilityComponentIndices_card_le_one (hk : 3 ≤ k)
    (hmu0 : 0 < mu) (hmu1 : mu ≤ 1)
    (C : D.CandidateCompatibility (oneBlockSequence k hk mu hmu0 hmu1) eta delta R₀) :
    (D.compatibilityComponentIndices eta R₀).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have h := C.assignment.injective (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩)
    (Subtype.ext ((C.oneBlock_assignment_zero hk hmu0 hmu1 _).trans
      (C.oneBlock_assignment_zero hk hmu0 hmu1 _).symm))
  exact congrArg Subtype.val h

theorem oneBlock_core_eq_complete (hk : 3 ≤ k)
    (hmu0 : 0 < mu) (hmu1 : mu ≤ 1)
    (C : D.CandidateCompatibility (oneBlockSequence k hk mu hmu0 hmu1) eta delta R₀)
    (i : Fin D.componentCount) (hi : i ∈ D.compatibilityComponentIndices eta R₀) :
    D.core i = RegularBlockCore.complete k hk := by
  apply RegularBlockCore.eq_complete_of_order_eq_k_sub_one _ hk
  have h := Fintype.card_congr (C.coreIso ⟨i, hi⟩).toEquiv
  change Fintype.card (Fin (D.core i).order) = Fintype.card (Fin (k - 1)) at h
  simpa only [Fintype.card_fin] using h

theorem oneBlock_component_size_error (hk : 3 ≤ k)
    (hmu0 : 0 < mu) (hmu1 : mu ≤ 1)
    (C : D.CandidateCompatibility (oneBlockSequence k hk mu hmu0 hmu1) eta delta R₀)
    (i : Fin D.componentCount) (hi : i ∈ D.compatibilityComponentIndices eta R₀) :
    |((D.componentSupport i).card : ℝ) - mu * Fintype.card V| ≤
      delta * Fintype.card V := by
  have h := C.size_error ⟨i, hi⟩
  rw [C.oneBlock_assignment_zero hk hmu0 hmu1] at h
  simpa only [oneBlockSequence_alpha_zero] using h

private theorem retained_subset_compatibility (heta : 0 ≤ eta) :
    D.retainedComponentIndices eta R₀ ⊆ D.compatibilityComponentIndices eta R₀ := by
  intro i hi
  have h := (D.mem_retainedComponentIndices eta R₀ i).mp hi
  apply (D.mem_compatibilityComponentIndices eta R₀ i).mpr
  refine ⟨?_, h.2⟩
  have : 0 ≤ eta * (Fintype.card V : ℝ) := mul_nonneg heta (Nat.cast_nonneg _)
  linarith

theorem oneBlock_retainedComponentIndices_card_eq_one (hk : 3 ≤ k)
    (hmu0 : 0 < mu) (hmu1 : mu ≤ 1)
    (C : D.CandidateCompatibility (oneBlockSequence k hk mu hmu0 hmu1) eta delta R₀)
    (heta : 0 ≤ eta) (hdelta : 0 ≤ delta) (hsize : eta + delta ≤ mu)
    (horder : k - 1 ≤ R₀) :
    (D.retainedComponentIndices eta R₀).card = 1 := by
  have hle : (D.retainedComponentIndices eta R₀).card ≤ 1 :=
    (Finset.card_le_card (retained_subset_compatibility heta)).trans
      (C.oneBlock_compatibilityComponentIndices_card_le_one hk hmu0 hmu1)
  let j : {j : ℕ // blockIndexActive
      (oneBlockSequence k hk mu hmu0 hmu1).count j} := ⟨0, by simp [oneBlockSequence, blockIndexActive]⟩
  obtain ⟨i, _⟩ := C.large_smallOrder_block_matched j (by
    dsimp [j]
    rw [oneBlockSequence_alpha_zero]
    linarith) (by simpa [j, oneBlockSequence] using horder)
  have hs := C.oneBlock_component_size_error hk hmu0 hmu1 i.val i.property
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hsize hn
  have hi : i.val ∈ D.retainedComponentIndices eta R₀ := by
    apply (D.mem_retainedComponentIndices eta R₀ i.val).mpr
    refine ⟨?_, ?_⟩
    · have := (abs_le.mp hs).1
      nlinarith
    · rw [C.oneBlock_core_eq_complete hk hmu0 hmu1 i.val i.property]
      exact horder
  have hpos : 0 < (D.retainedComponentIndices eta R₀).card :=
    Finset.card_pos.mpr ⟨i.val, hi⟩
  omega

/-- There is exactly one retained component, and its core is literally the
complete core. The support-size control remains the original compatibility
error; no balance of its individual parts is asserted here. -/
theorem oneBlock_retainedKey_exists (hk : 3 ≤ k)
    (hmu0 : 0 < mu) (hmu1 : mu ≤ 1)
    (C : D.CandidateCompatibility (oneBlockSequence k hk mu hmu0 hmu1) eta delta R₀)
    (heta : 0 ≤ eta) (hdelta : 0 ≤ delta) (hsize : eta + delta ≤ mu)
    (horder : k - 1 ≤ R₀) :
    ∃ E : SubcriticalDivision k V, retainedKey D eta R₀ = some E ∧
      E.componentCount = 1 ∧ (∀ i, E.core i = RegularBlockCore.complete k hk) ∧
      |((E.support).card : ℝ) - mu * Fintype.card V| ≤ delta * Fintype.card V := by
  have hc := C.oneBlock_retainedComponentIndices_card_eq_one
    hk hmu0 hmu1 heta hdelta hsize horder
  have hI : (D.retainedComponentIndices eta R₀).Nonempty :=
    Finset.card_pos.mp (by omega)
  let E := D.restrictComponents (D.retainedComponentIndices eta R₀) hI
  refine ⟨E, by simp only [retainedKey, dif_pos hI]; rfl, hc, ?_, ?_⟩
  · intro i
    exact C.oneBlock_core_eq_complete hk hmu0 hmu1 _
      (retained_subset_compatibility heta
        ((D.retainedComponentIndices eta R₀).orderIsoOfFin rfl i).property)
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    have his : i ∈ D.retainedComponentIndices eta R₀ := by rw [hi]; simp
    have hsupport : E.support = D.componentSupport i := by
      ext x
      rw [D.restrictComponents_mem_support]
      simp only [hi, Finset.mem_singleton, exists_eq_left]
    rw [hsupport]
    exact C.oneBlock_component_size_error hk hmu0 hmu1 i
      (retained_subset_compatibility heta his)

end SubcriticalDivision.CandidateCompatibility

theorem compatibleRetainedKeys_oneBlock_geometry (hk : 3 ≤ k)
    {n : ℕ} (hmu0 : 0 < mu) (hmu1 : mu ≤ 1)
    (heta : 0 ≤ eta) (hdelta : 0 ≤ delta) (hsize : eta + delta ≤ mu)
    (horder : k - 1 ≤ R₀) {K : SubcriticalRetainedKey k (Fin n)}
    (hK : K ∈ compatibleRetainedKeys k n
      (oneBlockSequence k hk mu hmu0 hmu1) eta delta R₀) :
    ∃ E : SubcriticalDivision k (Fin n), K = some E ∧ E.componentCount = 1 ∧
      (∀ i, E.core i = RegularBlockCore.complete k hk) ∧
      |((E.support).card : ℝ) - mu * n| ≤ delta * n := by
  obtain ⟨D, hD, rfl⟩ := mem_compatibleRetainedKeys.mp hK
  obtain ⟨_, ⟨C⟩⟩ := mem_subcriticalCompatibleDivisions D |>.mp hD
  simpa only [Fintype.card_fin] using
    C.oneBlock_retainedKey_exists hk hmu0 hmu1 heta hdelta hsize horder

end InducedStars
