import InducedStars.Structure.Subcritical.DistinguishedReference
import InducedStars.Structure.Subcritical.RetainedMass

/-!
# Finite retained-index and quadratic-mass estimates

Paper: the initial quadratic estimate in the proof of
`lemma:sub-retained-mass-gap-K1k`. The omitted quantity in this file is
normalized quadratic mass, not total block length.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

/-- A concrete finite encoding of the blocks with length at least 2 eta
and core order at most R₀. The rank cutoff follows from summability. -/
def subcriticalMassRetainedBlockIndices {k : ℕ} (L : AdmissibleBlockSequence k)
    (eta : ℝ) (R₀ : ℕ) : Finset ℕ :=
  subcriticalRetainedBlockIndices L (2 * eta) R₀

theorem mem_subcriticalMassRetainedBlockIndices {k : ℕ}
    (L : AdmissibleBlockSequence k) {eta : ℝ} (heta : 0 < eta) (R₀ i : ℕ) :
    i ∈ subcriticalMassRetainedBlockIndices L eta R₀ ↔
      2 * eta ≤ L.alpha i ∧ (L.core i).order ≤ R₀ := by
  constructor
  · intro h
    exact (mem_subcriticalRetainedBlockIndices.mp h).2
  · intro h
    by_contra hi
    rcases subcriticalRetainedBlockIndices_omitted L (by positivity : 0 < 2 * eta) R₀ i hi with ha | hr
    · exact (not_lt_of_ge h.1) ha
    · exact (not_lt_of_ge h.2) hr

theorem subcriticalMassRetainedBlockIndices_active {k : ℕ}
    (L : AdmissibleBlockSequence k) {eta : ℝ} (heta : 0 < eta) {R₀ i : ℕ}
    (hi : i ∈ subcriticalMassRetainedBlockIndices L eta R₀) : blockIndexActive L.count i := by
  by_contra h
  have ha := ((mem_subcriticalMassRetainedBlockIndices L heta R₀ i).mp hi).1
  rw [L.alpha_eq_zero_of_inactive i h] at ha
  linarith

/-- The retained sum of lengths; omitted lengths are not bounded by the
quadratic estimate below. -/
def subcriticalRetainedBlockLength {k : ℕ} (L : AdmissibleBlockSequence k)
    (eta : ℝ) (R₀ : ℕ) : ℝ :=
  ∑ i ∈ subcriticalMassRetainedBlockIndices L eta R₀, L.alpha i

def subcriticalOmittedBlockMass {k : ℕ} (L : AdmissibleBlockSequence k)
    (eta : ℝ) (R₀ : ℕ) : ℝ :=
  ∑' i : {i : ℕ // i ∉ subcriticalMassRetainedBlockIndices L eta R₀}, L.massTerm i

theorem subcriticalRetainedBlockLength_le_one {k : ℕ}
    (L : AdmissibleBlockSequence k) (eta : ℝ) (R₀ : ℕ) :
    subcriticalRetainedBlockLength L eta R₀ ≤ 1 :=
  (L.summable_alpha.sum_le_tsum _ (fun i _ ↦ L.alpha_nonneg i)).trans L.tsum_alpha_le_one

theorem subcriticalMassRetainedBlockIndices_card_le {k : ℕ}
    (L : AdmissibleBlockSequence k) {eta : ℝ} (heta : 0 < eta) (R₀ : ℕ) :
    2 * eta * (subcriticalMassRetainedBlockIndices L eta R₀).card ≤ 1 := by
  calc
    _ = ∑ i ∈ subcriticalMassRetainedBlockIndices L eta R₀, 2 * eta := by simp [mul_comm]
    _ ≤ subcriticalRetainedBlockLength L eta R₀ :=
      Finset.sum_le_sum (fun i hi ↦ ((mem_subcriticalMassRetainedBlockIndices L heta R₀ i).mp hi).1)
    _ ≤ 1 := subcriticalRetainedBlockLength_le_one L eta R₀

theorem subcriticalMass_eq_retained_add_omitted {k : ℕ}
    (L : AdmissibleBlockSequence k) (eta : ℝ) (R₀ : ℕ) :
    L.mass = (∑ i ∈ subcriticalMassRetainedBlockIndices L eta R₀, L.massTerm i) +
      subcriticalOmittedBlockMass L eta R₀ :=
  (L.summable_massTerm.sum_add_tsum_subtype_compl _).symm

theorem subcriticalOmittedBlockMass_nonneg {k : ℕ}
    (L : AdmissibleBlockSequence k) (eta : ℝ) (R₀ : ℕ) :
    0 ≤ subcriticalOmittedBlockMass L eta R₀ :=
  tsum_nonneg (fun i ↦ L.massTerm_nonneg i)

/-- A pointwise domination that uses either small length or large core
order. It never infers that a large-order block has small vertex length. -/
theorem subcriticalOmittedBlockMassTerm_le {k : ℕ}
    (L : AdmissibleBlockSequence k) {eta : ℝ} (heta : 0 < eta) (R₀ i : ℕ)
    (hi : i ∉ subcriticalMassRetainedBlockIndices L eta R₀) :
    L.massTerm i ≤ (2 * eta + 1 / ((R₀ + 1 : ℕ) : ℝ)) * L.alpha i := by
  have ha0 := L.alpha_nonneg i
  have ha1 := L.alpha_le_one i
  have hrpos : (0 : ℝ) < (L.core i).order := by exact_mod_cast (L.core i).order_pos
  have hRpos : (0 : ℝ) < ((R₀ + 1 : ℕ) : ℝ) := by positivity
  by_cases ha : 2 * eta ≤ L.alpha i
  · have horder : R₀ < (L.core i).order := by
      by_contra h
      exact hi ((mem_subcriticalMassRetainedBlockIndices L heta R₀ i).mpr ⟨ha, by omega⟩)
    have horderR : ((R₀ + 1 : ℕ) : ℝ) ≤ (L.core i).order := by exact_mod_cast horder
    calc
      L.massTerm i ≤ L.alpha i ^ 2 / ((R₀ + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hRpos horderR
      _ ≤ L.alpha i / ((R₀ + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right (by nlinarith) hRpos.le
      _ ≤ _ := by
        rw [add_mul, one_div_mul_eq_div]
        exact le_add_of_nonneg_left (by positivity)
  · have hsmall : L.alpha i < 2 * eta := lt_of_not_ge ha
    calc
      L.massTerm i ≤ L.alpha i ^ 2 :=
        div_le_self (sq_nonneg _) (by exact_mod_cast (L.core i).order_pos)
      _ ≤ 2 * eta * L.alpha i := by nlinarith
      _ ≤ _ := by
        rw [add_mul]
        exact le_add_of_nonneg_right (by positivity)

/-- Uniform omitted quadratic mass bound; no total-length conclusion is
asserted. This tends to zero as eta and 1/R₀ tend to zero. -/
theorem subcriticalOmittedBlockMass_le {k : ℕ}
    (L : AdmissibleBlockSequence k) {eta : ℝ} (heta : 0 < eta) (R₀ : ℕ) :
    subcriticalOmittedBlockMass L eta R₀ ≤ 2 * eta + 1 / ((R₀ + 1 : ℕ) : ℝ) := by
  let I := subcriticalMassRetainedBlockIndices L eta R₀
  let C : ℝ := 2 * eta + 1 / ((R₀ + 1 : ℕ) : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum : (∑' i : {i : ℕ // i ∉ I}, L.alpha i) ≤ 1 := by
    have heq := L.summable_alpha.sum_add_tsum_subtype_compl I
    have hnon : 0 ≤ ∑ i ∈ I, L.alpha i := Finset.sum_nonneg (fun i _ ↦ L.alpha_nonneg i)
    linarith [L.tsum_alpha_le_one]
  calc
    subcriticalOmittedBlockMass L eta R₀ ≤
        ∑' i : {i : ℕ // i ∉ I}, C * L.alpha i := by
      exact Summable.tsum_le_tsum
        (fun i ↦ subcriticalOmittedBlockMassTerm_le L heta R₀ i i.property)
        (L.summable_massTerm.subtype _) ((L.summable_alpha.subtype _).mul_left C)
    _ = C * ∑' i : {i : ℕ // i ∉ I}, L.alpha i := tsum_mul_left
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hsum hC
    _ = _ := mul_one C

end InducedStars
