import InducedStars.Structure.Subcritical.RetainedMassScalars

/-!
# Concentration of retained lengths from their quadratic mass

The length bound applies only to the other retained blocks.
Unretained blocks are controlled by their normalized quadratic mass.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

theorem subcriticalBlockMassTerm_le_sq_div {k : ℕ} (hk : 3 ≤ k)
    (L : AdmissibleBlockSequence k) (i : ℕ) :
    L.massTerm i ≤ L.alpha i ^ 2 / (k - 1 : ℕ) := by
  exact div_le_div_of_nonneg_left (sq_nonneg _)
    (by exact_mod_cast (show 0 < k - 1 by omega))
    (by exact_mod_cast RegularBlockCore.k_sub_one_le_order hk (L.core i))

theorem subcriticalFiniteBlockMass_le_sq_length {k : ℕ} (hk : 3 ≤ k)
    (L : AdmissibleBlockSequence k) (I : Finset ℕ) :
    (∑ i ∈ I, L.massTerm i) ≤ (∑ i ∈ I, L.alpha i) ^ 2 / (k - 1 : ℕ) := by
  calc
    _ ≤ ∑ i ∈ I, L.alpha i ^ 2 / (k - 1 : ℕ) :=
      Finset.sum_le_sum (fun i _ ↦ subcriticalBlockMassTerm_le_sq_div hk L i)
    _ = (∑ i ∈ I, L.alpha i ^ 2) / (k - 1 : ℕ) := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right
      (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ ↦ L.alpha_nonneg i)) (by positivity)

theorem subcriticalFiniteBlockMass_le_max_mul_length {k : ℕ} (hk : 3 ≤ k)
    (L : AdmissibleBlockSequence k) (I : Finset ℕ) (j : ℕ)
    (hj : ∀ i ∈ I, L.alpha i ≤ L.alpha j) :
    (∑ i ∈ I, L.massTerm i) ≤
      L.alpha j * (∑ i ∈ I, L.alpha i) / (k - 1 : ℕ) := by
  calc
    _ ≤ ∑ i ∈ I, (L.alpha j * L.alpha i) / (k - 1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (subcriticalBlockMassTerm_le_sq_div hk L i).trans
        (div_le_div_of_nonneg_right (by nlinarith [hj i hi, L.alpha_nonneg i]) (by positivity))
    _ = _ := by rw [← Finset.sum_div, ← Finset.mul_sum]

/-- Explicit dominant retained block. The omitted mass budget E and the
excess retained length d control the length error by d+(k-1)E/mu.
The bound on other lengths is deliberately restricted to the retained set. -/
theorem subcriticalRetainedMass_dominant
    {k : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    {eta mu d E : ℝ} {R₀ : ℕ}
    (hmu : 0 < mu) (hd : 0 ≤ d) (hE : 0 ≤ E)
    (hmass : L.mass = mu ^ 2 / (k - 1 : ℕ))
    (homit : subcriticalOmittedBlockMass L eta R₀ ≤ E)
    (hsmall : (k - 1 : ℕ) * E < mu ^ 2)
    (hlength : subcriticalRetainedBlockLength L eta R₀ ≤ mu + d) :
    ∃ j ∈ subcriticalMassRetainedBlockIndices L eta R₀,
      (∀ i ∈ subcriticalMassRetainedBlockIndices L eta R₀, L.alpha i ≤ L.alpha j) ∧
      |L.alpha j - mu| ≤ d + (k - 1 : ℕ) * E / mu ∧
      (∑ i ∈ (subcriticalMassRetainedBlockIndices L eta R₀).erase j, L.alpha i) ≤
        2 * d + (k - 1 : ℕ) * E / mu := by
  let I := subcriticalMassRetainedBlockIndices L eta R₀
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hsplit := subcriticalMass_eq_retained_add_omitted L eta R₀
  rw [hmass] at hsplit
  have hmassle : mu ^ 2 / (k - 1 : ℕ) ≤ (∑ i ∈ I, L.massTerm i) + E := by
    dsimp [I]
    linarith
  have hI : I.Nonempty := by
    by_contra h
    have hempty := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hempty, Finset.sum_empty, zero_add] at hmassle
    have h := (div_le_iff₀ hr).mp hmassle
    nlinarith
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image I L.alpha hI
  have hmaxbound := subcriticalFiniteBlockMass_le_max_mul_length hk L I j hmax
  have hratio : mu ^ 2 / (k - 1 : ℕ) ≤
      L.alpha j * (∑ i ∈ I, L.alpha i) / (k - 1 : ℕ) + E := hmassle.trans (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hratio hr.le
  have hprod : mu ^ 2 ≤ L.alpha j * (∑ i ∈ I, L.alpha i) + (k - 1 : ℕ) * E := by
    field_simp at hmul
    nlinarith
  have ha0 := L.alpha_nonneg j
  have hleSum : L.alpha j ≤ ∑ i ∈ I, L.alpha i :=
    Finset.single_le_sum (fun i _ ↦ L.alpha_nonneg i) hj
  have htotal : (∑ i ∈ I, L.alpha i) ≤ mu + d := hlength
  have hupper : L.alpha j ≤ mu + d := hleSum.trans htotal
  have herror0 : 0 ≤ (k - 1 : ℕ) * E / mu := by positivity
  have hdiv : ((k - 1 : ℕ) * E / mu) * mu = (k - 1 : ℕ) * E := div_mul_cancel₀ _ hmu.ne'
  have hlower : mu - d - (k - 1 : ℕ) * E / mu ≤ L.alpha j := by
    by_cases ha : mu ≤ L.alpha j
    · linarith
    · have ha' : L.alpha j ≤ mu := (lt_of_not_ge ha).le
      have h1 := mul_le_mul_of_nonneg_left htotal ha0
      have h2 := mul_le_mul_of_nonneg_right ha' hd
      nlinarith
  refine ⟨j, hj, hmax, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> linarith
  · have herase := Finset.sum_erase_add I L.alpha hj
    nlinarith

/-- The integer gap in core order forces the dominant core to be complete
once the displayed finite error budget is below the order-gap threshold.
All denominators and the strict gap are explicit. -/
theorem subcriticalRetainedDominantCore_order_eq
    {k : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    {eta mu d E : ℝ} {R₀ j : ℕ}
    (hmu : 0 < mu) (hd : 0 ≤ d) (hE : 0 ≤ E)
    (hj : j ∈ subcriticalMassRetainedBlockIndices L eta R₀)
    (hmass : L.mass = mu ^ 2 / (k - 1 : ℕ))
    (homit : subcriticalOmittedBlockMass L eta R₀ ≤ E)
    (hupper : L.alpha j ≤ mu + d)
    (hothers : (∑ i ∈ (subcriticalMassRetainedBlockIndices L eta R₀).erase j, L.alpha i) ≤
      2 * d + (k - 1 : ℕ) * E / mu)
    (hgap : (mu + d) ^ 2 / ((k - 1 : ℕ) + 1 : ℝ) +
      (2 * d + (k - 1 : ℕ) * E / mu) ^ 2 / (k - 1 : ℕ) + E <
        mu ^ 2 / (k - 1 : ℕ)) :
    (L.core j).order = k - 1 := by
  have hr := RegularBlockCore.k_sub_one_le_order hk (L.core j)
  by_contra hne
  have hlarge : (k - 1 : ℕ) + 1 ≤ (L.core j).order := by omega
  have hlargeR : ((k - 1 : ℕ) : ℝ) + 1 ≤ (L.core j).order := by exact_mod_cast hlarge
  have hmain : L.massTerm j ≤ (mu + d) ^ 2 / ((k - 1 : ℕ) + 1 : ℝ) := by
    calc
      _ ≤ L.alpha j ^ 2 / ((k - 1 : ℕ) + 1 : ℝ) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hlargeR
      _ ≤ _ := div_le_div_of_nonneg_right
        (by nlinarith [L.alpha_nonneg j]) (by positivity)
  have hrest := subcriticalFiniteBlockMass_le_sq_length hk L
    ((subcriticalMassRetainedBlockIndices L eta R₀).erase j)
  have hrest0 : 0 ≤ ∑ i ∈ (subcriticalMassRetainedBlockIndices L eta R₀).erase j, L.alpha i :=
    Finset.sum_nonneg (fun i _ ↦ L.alpha_nonneg i)
  have hrestBound : (∑ i ∈ (subcriticalMassRetainedBlockIndices L eta R₀).erase j, L.massTerm i) ≤
      (2 * d + (k - 1 : ℕ) * E / mu) ^ 2 / (k - 1 : ℕ) :=
    hrest.trans (div_le_div_of_nonneg_right (by nlinarith) (by positivity))
  have herase := Finset.sum_erase_add (subcriticalMassRetainedBlockIndices L eta R₀) L.massTerm hj
  have hsplit := subcriticalMass_eq_retained_add_omitted L eta R₀
  rw [hmass] at hsplit
  linarith

end InducedStars
