import InducedStars.Structure.Subcritical.ProfileData
import InducedStars.Structure.Subcritical.RetainedCounts

/-!
# Uniform index bounds and profile complexity

Paper: the profile enumeration in Lemma `lemma:NtaunmWUpperBdK1k`.
The number of visible indices is controlled by disjoint actual vertex parts,
not by bounding the total number of parts of a division.
-/

noncomputable section
open Finset
open scoped BigOperators

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

def subcriticalVisibleIndexBound (theta : ℝ) : ℕ := Nat.ceil (2 / theta)

def subcriticalRetainedIndexBound (eta : ℝ) (R₀ : ℕ) : ℕ :=
  Nat.ceil ((R₀ : ℝ) / eta)

def subcriticalActiveIndexBound (eta : ℝ) (R₀ : ℕ) : ℕ :=
  Nat.ceil ((R₀ : ℝ) ^ 2 / eta ^ 2)

/-- A uniform finite visible-index bound from the actual lower part sizes. -/
theorem subcriticalVisiblePartIndices_card_le
    (D : SubcriticalDivision k V) {theta : ℝ} (htheta : 0 < theta)
    (hvisible : ∀ a ∈ D.visiblePartIndices theta,
      theta * Fintype.card V / 2 ≤ ((D.part a).card : ℝ)) :
    (D.visiblePartIndices theta).card ≤ subcriticalVisibleIndexBound theta := by
  have hn : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast D.componentCount_pos.trans_le D.componentCount_le_card
  have hsum := Finset.sum_le_sum hvisible
  have hparts : (∑ a ∈ D.visiblePartIndices theta, ((D.part a).card : ℝ)) ≤
      Fintype.card V := by
    have heq : ((D.visiblePartIndices theta).biUnion D.part).card =
        ∑ a ∈ D.visiblePartIndices theta, (D.part a).card := by
      rw [Finset.card_biUnion]
      intro a _ b _ hab
      exact D.part_disjoint hab
    exact_mod_cast heq ▸ Finset.card_le_univ ((D.visiblePartIndices theta).biUnion D.part)
  have hprod : ((D.visiblePartIndices theta).card : ℝ) * theta ≤ 2 := by
    have hh := hsum.trans hparts
    simp only [Finset.sum_const, nsmul_eq_mul] at hh
    nlinarith
  have hreal := (le_div_iff₀ htheta).mpr hprod
  exact_mod_cast hreal.trans (Nat.le_ceil (2 / theta))

theorem subcriticalRetainedPartIndices_card_le
    (D : SubcriticalDivision k V) {eta : ℝ} (R₀ : ℕ) (heta : 0 < eta) :
    (D.retainedPartIndices eta R₀).card ≤ subcriticalRetainedIndexBound eta R₀ := by
  have hh : ((D.retainedPartIndices eta R₀).card : ℝ) ≤ R₀ / eta := by
    apply (le_div_iff₀ heta).mpr
    simpa only [mul_comm] using D.eta_mul_card_retainedPartIndices_le R₀ heta.le
  exact_mod_cast hh.trans (Nat.le_ceil ((R₀ : ℝ) / eta))

theorem subcriticalRetainedActivePair_card_le
    (D : SubcriticalDivision k V) {eta : ℝ} (R₀ : ℕ) (heta : 0 < eta) :
    Fintype.card (RetainedActivePair D eta R₀) ≤ subcriticalActiveIndexBound eta R₀ := by
  exact Nat.cast_le.mp (show (Fintype.card (RetainedActivePair D eta R₀) : ℝ) ≤
      subcriticalActiveIndexBound eta R₀ from
    (card_retainedActivePair_le_uniform D R₀ heta).trans
      (Nat.le_ceil ((R₀ : ℝ) ^ 2 / eta ^ 2)))

/-- Root-plus-matching complexity; no matching itself is stored. -/
def subcriticalProfileComplexity {D : SubcriticalDivision k V}
    {eta theta : ℝ} {R₀ : ℕ} (p : SubcriticalProfile D eta R₀ theta) : ℕ :=
  p.roots.card + p.ell

theorem subcriticalProfileComplexity_le {D : SubcriticalDivision k V}
    {eta theta : ℝ} {R₀ : ℕ} (p : SubcriticalProfile D eta R₀ theta) :
    subcriticalProfileComplexity p ≤ 2 * Fintype.card V := by
  have hroot := Finset.card_le_univ p.roots
  have hell := p.two_mul_ell_le
  unfold subcriticalProfileComplexity
  omega

@[simp] theorem subcriticalProfileComplexity_eq_zero_iff
    {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}
    (p : SubcriticalProfile D eta R₀ theta) :
    subcriticalProfileComplexity p = 0 ↔ p.roots = ∅ ∧ p.ell = 0 := by
  simp [subcriticalProfileComplexity]

/-- All syntactically valid profiles of the given complexity. -/
def subcriticalProfilesOfComplexity (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta : ℝ) (r : ℕ) :
    Finset (SubcriticalProfile D eta R₀ theta) :=
  Finset.univ.filter fun p ↦ subcriticalProfileComplexity p = r

@[simp] theorem mem_subcriticalProfilesOfComplexity (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta : ℝ) (r : ℕ) (p : SubcriticalProfile D eta R₀ theta) :
    p ∈ subcriticalProfilesOfComplexity D eta R₀ theta r ↔
      subcriticalProfileComplexity p = r := by
  classical
  simp [subcriticalProfilesOfComplexity]

end InducedStars
