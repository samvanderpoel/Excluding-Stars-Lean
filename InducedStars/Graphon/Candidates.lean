import InducedStars.Graphon.CandidateBlocks
import InducedStars.Graphon.Star
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic

/-!
# Explicit candidate graphons for the fixed-density problem

This file packages the subcritical block-sequence family and constructs the
paper's distinguished supercritical graphon.  The critical density belongs to
the supercritical singleton branch.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal unitInterval

namespace InducedStars

/-! ## The distinguished supercritical graphon -/

/-- The off-diagonal value of the paper's supercritical candidate. -/
abbrev supercriticalOffDiagonal (k : ℕ) (γ : ℝ) : ℝ :=
  phaseLower k γ

@[simp] theorem supercriticalOffDiagonal_at_gammaK (k : ℕ) (hk : 3 ≤ k) :
    supercriticalOffDiagonal k (gammaK k) = pK k :=
  phaseLower_at_gammaK k hk

theorem supercriticalOffDiagonal_nonneg {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : gammaK k ≤ γ) : 0 ≤ supercriticalOffDiagonal k γ :=
  phaseLower_nonneg hk hγ

theorem supercriticalOffDiagonal_lt_one {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ < 1) : supercriticalOffDiagonal k γ < 1 :=
  phaseLower_lt_one hk hγ

theorem pK_le_supercriticalOffDiagonal {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : gammaK k ≤ γ) : pK k ≤ supercriticalOffDiagonal k γ := by
  rcases hγ.eq_or_lt with rfl | hγ
  · rw [supercriticalOffDiagonal_at_gammaK k hk]
  · exact ((pK_lt_phaseLower_iff hk γ).2 hγ).le

/-- The `(k-1) × (k-1)` matrix of the distinguished supercritical graphon. -/
def WstarMatrix (k : ℕ) (γ : ℝ) : Matrix (Fin (k - 1)) (Fin (k - 1)) ℝ :=
  fun i j ↦ if i = j then 1 else supercriticalOffDiagonal k γ

theorem WstarMatrix_isSymm (k : ℕ) (γ : ℝ) : (WstarMatrix k γ).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [WstarMatrix]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

theorem WstarMatrix_nonneg {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : gammaK k ≤ γ) (i j : Fin (k - 1)) :
    0 ≤ WstarMatrix k γ i j := by
  simp only [WstarMatrix]
  split
  · norm_num
  · exact supercriticalOffDiagonal_nonneg hk hγ

theorem WstarMatrix_le_one {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ < 1) (i j : Fin (k - 1)) :
    WstarMatrix k γ i j ≤ 1 := by
  simp only [WstarMatrix]
  split
  · exact le_rfl
  · exact (supercriticalOffDiagonal_lt_one hk hγ).le

/-- The paper's balanced `(k-1)`-block graphon `Wγ∗`.

The proof argument records precisely its paper domain
`gammaK k ≤ γ < 1`; proof irrelevance makes the resulting graphon independent
of the particular proof supplied.
-/
def Wstar (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) (hγ : γ ∈ Ico (gammaK k) 1) : Graphon :=
  matrixGraphon (WstarMatrix k γ) (WstarMatrix_isSymm k γ)
    (WstarMatrix_nonneg hk hγ.1) (WstarMatrix_le_one hk hγ.2)

@[simp] theorem WstarMatrix_apply_self (k : ℕ) (γ : ℝ) (i : Fin (k - 1)) :
    WstarMatrix k γ i i = 1 := by
  simp [WstarMatrix]

theorem WstarMatrix_apply_of_ne (k : ℕ) (γ : ℝ) {i j : Fin (k - 1)}
    (hij : i ≠ j) : WstarMatrix k γ i j = supercriticalOffDiagonal k γ := by
  simp [WstarMatrix, hij]

private theorem sum_WstarMatrix_row {k : ℕ} (hk : 3 ≤ k) (γ : ℝ)
    (i : Fin (k - 1)) :
    ∑ j : Fin (k - 1), WstarMatrix k γ i j =
      1 + (k - 2 : ℕ) * supercriticalOffDiagonal k γ := by
  classical
  let a := supercriticalOffDiagonal k γ
  calc
    ∑ j : Fin (k - 1), WstarMatrix k γ i j =
        ∑ j : Fin (k - 1), ((if i = j then 1 - a else 0) + a) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hij : i = j <;> simp [WstarMatrix, hij, a]
    _ = (∑ j : Fin (k - 1), if i = j then 1 - a else 0) +
        ∑ _j : Fin (k - 1), a := by
          rw [Finset.sum_add_distrib]
    _ = 1 + (k - 2 : ℕ) * a := by
          have hcard : Fintype.card (Fin (k - 1)) = k - 1 := by simp
          rw [show (∑ j : Fin (k - 1), if i = j then 1 - a else 0) = 1 - a by
            simpa only [eq_comm] using Fintype.sum_ite_eq' i (fun _ ↦ 1 - a)]
          simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
          norm_num [Nat.cast_sub (show 2 ≤ k by omega),
            Nat.cast_sub (show 1 ≤ k by omega)]
          ring

private theorem sum_WstarMatrix {k : ℕ} (hk : 3 ≤ k) (γ : ℝ) :
    ∑ i : Fin (k - 1), ∑ j : Fin (k - 1), WstarMatrix k γ i j =
      (k - 1 : ℕ) * (1 + (k - 2 : ℕ) * supercriticalOffDiagonal k γ) := by
  simp_rw [sum_WstarMatrix_row hk γ]
  simp
  ring

/-- The distinguished supercritical graphon has the prescribed edge density. -/
theorem graphonEdgeDensity_Wstar (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ico (gammaK k) 1) :
    graphonEdgeDensity (Wstar k hk γ hγ) = γ := by
  rw [show Wstar k hk γ hγ = matrixGraphon (WstarMatrix k γ)
      (WstarMatrix_isSymm k γ) (WstarMatrix_nonneg hk hγ.1)
        (WstarMatrix_le_one hk hγ.2) from rfl]
  rw [graphonEdgeDensity_matrixGraphon (show 0 < k - 1 by omega),
    sum_WstarMatrix hk γ, phaseLower_denominator k hk γ]
  have hq : ((k - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show k - 1 ≠ 0 by omega)
  field_simp [hq]

private theorem sum_binaryEntropy_WstarMatrix_row {k : ℕ} (hk : 3 ≤ k)
    (γ : ℝ) (i : Fin (k - 1)) :
    ∑ j : Fin (k - 1), binaryEntropy (WstarMatrix k γ i j) =
      (k - 2 : ℕ) * binaryEntropy (supercriticalOffDiagonal k γ) := by
  classical
  let b := binaryEntropy (supercriticalOffDiagonal k γ)
  calc
    ∑ j : Fin (k - 1), binaryEntropy (WstarMatrix k γ i j) =
        ∑ j : Fin (k - 1), ((if i = j then -b else 0) + b) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hij : i = j
          · subst j
            simp [WstarMatrix, b]
          · simp [WstarMatrix, hij, b]
    _ = (∑ j : Fin (k - 1), if i = j then -b else 0) +
        ∑ _j : Fin (k - 1), b := by
          rw [Finset.sum_add_distrib]
    _ = (k - 2 : ℕ) * b := by
          rw [show (∑ j : Fin (k - 1), if i = j then -b else 0) = -b by
            simpa only [eq_comm] using Fintype.sum_ite_eq' i (fun _ ↦ -b)]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num [Nat.cast_sub (show 2 ≤ k by omega),
            Nat.cast_sub (show 1 ≤ k by omega)]
          ring

private theorem sum_binaryEntropy_WstarMatrix {k : ℕ} (hk : 3 ≤ k) (γ : ℝ) :
    ∑ i : Fin (k - 1), ∑ j : Fin (k - 1),
        binaryEntropy (WstarMatrix k γ i j) =
      (k - 1 : ℕ) * ((k - 2 : ℕ) *
        binaryEntropy (supercriticalOffDiagonal k γ)) := by
  simp_rw [sum_binaryEntropy_WstarMatrix_row hk γ]
  simp

/-- Entropy of `Wγ∗` is the upper branch of the paper's entropy profile. -/
theorem graphonEntropy_Wstar_eq_upper (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ico (gammaK k) 1) :
    graphonEntropy (Wstar k hk γ hγ) = entropyDensityUpper k γ := by
  rw [show Wstar k hk γ hγ = matrixGraphon (WstarMatrix k γ)
      (WstarMatrix_isSymm k γ) (WstarMatrix_nonneg hk hγ.1)
        (WstarMatrix_le_one hk hγ.2) from rfl]
  rw [graphonEntropy_matrixGraphon (show 0 < k - 1 by omega),
    sum_binaryEntropy_WstarMatrix hk γ]
  rw [entropyDensityUpper, ← upperScale_eq k hk]
  rw [show supercriticalOffDiagonal k γ =
      (((k - 1 : ℕ) : ℝ) * γ - 1) / (k - 2 : ℕ) by
    simp only [supercriticalOffDiagonal, phaseLower]
    congr 2
    ring]
  have hq : ((k - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show k - 1 ≠ 0 by omega)
  field_simp [hq]

/-- Entropy of `Wγ∗` agrees with the piecewise profile, including at the
critical density where `entropyDensity` is definitionally on its lower branch. -/
theorem graphonEntropy_Wstar (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ico (gammaK k) 1) :
    graphonEntropy (Wstar k hk γ hγ) = entropyDensity k γ := by
  rw [graphonEntropy_Wstar_eq_upper k hk γ hγ,
    entropyDensity_of_ge hk hγ.1]

/-- Every finite star-label map into the `k-1` matrix blocks has zero induced
weight: two leaves receive the same label, and their nonedge factor vanishes. -/
private theorem matrixInducedMapWeight_inducedStar_WstarMatrix_zero
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (φ : Fin (k + 1) → Fin (k - 1)) :
    matrixInducedMapWeight (inducedStar k) (WstarMatrix k γ)
      (WstarMatrix_isSymm k γ) φ = 0 := by
  obtain ⟨i, j, hij, hφ⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun t : Fin k ↦ φ t.succ) (by simp; omega)
  have hleaves : i.succ ≠ j.succ := by
    exact fun h ↦ hij (Fin.succ_injective k h)
  have hnonedge : s(i.succ, j.succ) ∈ finiteGraphEdges (inducedStar k)ᶜ := by
    simp [hleaves]
  unfold matrixInducedMapWeight
  rw [show (∏ e ∈ finiteGraphEdges (inducedStar k)ᶜ,
      (1 - matrixMapPairValue (WstarMatrix k γ) (WstarMatrix_isSymm k γ) φ e)) = 0 by
    apply Finset.prod_eq_zero hnonedge
    simp [matrixMapPairValue_mk, hφ, WstarMatrix]]
  simp

/-- The distinguished supercritical graphon is induced-`K_{1,k}`-free. -/
theorem Wstar_inducedStar_free (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ico (gammaK k) 1) :
    graphonInducedDensity (inducedStar k) (Wstar k hk γ hγ) = 0 := by
  exact graphonInducedDensity_matrixGraphon_eq_zero_of_weights
    (show 0 < k - 1 by omega) (inducedStar k) (WstarMatrix k γ)
      (WstarMatrix_isSymm k γ) (WstarMatrix_nonneg hk hγ.1)
      (WstarMatrix_le_one hk hγ.2)
      (matrixInducedMapWeight_inducedStar_WstarMatrix_zero k hk γ)

/-! ## Subcritical block-sequence candidates -/

/-- The scalar mass controlling both edge density and entropy of a block
sequence candidate. -/
noncomputable def blockSequenceMass {k : ℕ} (L : AdmissibleBlockSequence k) : ℝ :=
  ∑' i : ℕ, L.alpha i ^ 2 / (L.core i).order

/-- Compatibility with the intrinsic mass carried by an admissible block
sequence. -/
@[simp] theorem blockSequenceMass_eq_mass {k : ℕ}
    (L : AdmissibleBlockSequence k) : blockSequenceMass L = L.mass :=
  rfl

/-- The exact paper mass constraint in the subcritical regime. -/
def IsSubcriticalCandidate (k : ℕ) (γ : ℝ) (L : AdmissibleBlockSequence k) : Prop :=
  blockSequenceMass L = γ / (1 + (k - 2 : ℕ) * pK k)

/-- Graphons obtained from admissible block sequences satisfying the exact
subcritical mass constraint. -/
def subcriticalCandidateFamily (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) : Set Graphon :=
  {W | ∃ L : AdmissibleBlockSequence k,
    IsSubcriticalCandidate k γ L ∧ W = WLambda hk L}

@[simp] theorem mem_subcriticalCandidateFamily {k : ℕ} {hk : 3 ≤ k} {γ : ℝ}
    {W : Graphon} :
    W ∈ subcriticalCandidateFamily k hk γ ↔
      ∃ L : AdmissibleBlockSequence k,
        IsSubcriticalCandidate k γ L ∧ W = WLambda hk L :=
  Iff.rfl

/-! ## A one-block subcritical witness -/

/-- An admissible sequence with one block of length `α`, labeled by the
complete `(k-2)`-regular core on `k-1` vertices. -/
def oneBlockSequence (k : ℕ) (hk : 3 ≤ k) (α : ℝ)
    (hα₀ : 0 < α) (hα₁ : α ≤ 1) : AdmissibleBlockSequence k where
  count := some 1
  count_pos := by
    intro n hn
    have : 1 = n := by simpa using hn
    omega
  alpha := fun i ↦ if i = 0 then α else 0
  core := fun _ ↦ RegularBlockCore.complete k hk
  alpha_pos_of_active := by
    intro i hi
    have hi₀ : i = 0 := by
      simpa [blockIndexActive] using hi
    simp [hi₀, hα₀]
  alpha_eq_zero_of_inactive := by
    intro i hi
    have hi₀ : i ≠ 0 := by
      intro hi₀
      subst i
      exact hi (by simp [blockIndexActive])
    simp [hi₀]
  alpha_antitone := by
    intro i j hij
    by_cases hi₀ : i = 0
    · subst i
      by_cases hj₀ : j = 0 <;> simp [hj₀, hα₀.le]
    · have hj₀ : j ≠ 0 := by
        intro hj₀
        subst j
        exact hi₀ (Nat.eq_zero_of_le_zero hij)
      simp [hi₀, hj₀]
  summable_alpha := by
    simpa only [eq_comm] using (hasSum_ite_eq (0 : ℕ) α).summable
  tsum_alpha_le_one := by
    simpa only [eq_comm, tsum_ite_eq] using hα₁

@[simp] theorem oneBlockSequence_alpha_zero (k : ℕ) (hk : 3 ≤ k) (α : ℝ)
    (hα₀ : 0 < α) (hα₁ : α ≤ 1) :
    (oneBlockSequence k hk α hα₀ hα₁).alpha 0 = α := by
  simp [oneBlockSequence]

theorem blockSequenceMass_oneBlockSequence (k : ℕ) (hk : 3 ≤ k) (α : ℝ)
    (hα₀ : 0 < α) (hα₁ : α ≤ 1) :
    blockSequenceMass (oneBlockSequence k hk α hα₀ hα₁) =
      α ^ 2 / (k - 1 : ℕ) := by
  rw [blockSequenceMass, tsum_eq_single 0]
  · simp [oneBlockSequence]
  · intro i hi
    simp [oneBlockSequence, hi]

private theorem subcriticalDenominator_pos {k : ℕ} (hk : 3 ≤ k) :
    (0 : ℝ) < 1 + (k - 2 : ℕ) * pK k := by
  have hp : 0 < pK k := pK_pos (by omega)
  positivity

/-- A block sequence satisfying the subcritical mass constraint has exactly
the prescribed edge density. -/
theorem graphonEdgeDensity_WLambda_of_isSubcriticalCandidate
    {k : ℕ} (hk : 3 ≤ k) {γ : ℝ} {L : AdmissibleBlockSequence k}
    (hL : IsSubcriticalCandidate k γ L) :
    graphonEdgeDensity (WLambda hk L) = γ := by
  rw [WLambda_edgeDensity]
  change (1 + ((k - 2 : ℕ) : ℝ) * pK k) * blockSequenceMass L = γ
  rw [hL]
  field_simp [(subcriticalDenominator_pos hk).ne']

/-- A subcritical block candidate has the lower-branch entropy prescribed by
the paper's scalar profile. -/
theorem graphonEntropy_WLambda_of_isSubcriticalCandidate
    {k : ℕ} (hk : 3 ≤ k) {γ : ℝ} (hγ : γ < gammaK k)
    {L : AdmissibleBlockSequence k} (hL : IsSubcriticalCandidate k γ L) :
    graphonEntropy (WLambda hk L) = entropyDensity k γ := by
  rw [WLambda_entropy]
  change (((k - 2 : ℕ) : ℝ) * binaryEntropy (pK k)) *
    blockSequenceMass L = entropyDensity k γ
  rw [hL, entropyDensity_of_le hγ.le, entropyDensityLower]
  ring

/-- Length of the canonical one-block witness below the critical density. -/
noncomputable def subcriticalOneBlockLength (k : ℕ) (γ : ℝ) : ℝ :=
  Real.sqrt (((k - 1 : ℕ) : ℝ) * γ /
    (1 + (k - 2 : ℕ) * pK k))

theorem subcriticalOneBlockLength_pos {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ₀ : 0 < γ) : 0 < subcriticalOneBlockLength k γ := by
  rw [subcriticalOneBlockLength, Real.sqrt_pos]
  exact div_pos (mul_pos (by exact_mod_cast (show 0 < k - 1 by omega)) hγ₀)
    (subcriticalDenominator_pos hk)

theorem subcriticalOneBlockLength_lt_one {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ < gammaK k) : subcriticalOneBlockLength k γ < 1 := by
  have hq : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hD := subcriticalDenominator_pos hk
  have hnum : ((k - 1 : ℕ) : ℝ) * γ < 1 + (k - 2 : ℕ) * pK k := by
    rw [gammaK] at hγ
    have := (lt_div_iff₀ hq).mp hγ
    nlinarith
  rw [subcriticalOneBlockLength, Real.sqrt_lt' zero_lt_one, one_pow]
  exact (div_lt_one hD).2 hnum

theorem subcriticalOneBlockSequence_isCandidate {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ₀ : 0 < γ) (hγ : γ < gammaK k) :
    IsSubcriticalCandidate k γ
      (oneBlockSequence k hk (subcriticalOneBlockLength k γ)
        (subcriticalOneBlockLength_pos hk hγ₀)
        (subcriticalOneBlockLength_lt_one hk hγ).le) := by
  rw [IsSubcriticalCandidate, blockSequenceMass_oneBlockSequence,
    subcriticalOneBlockLength, Real.sq_sqrt]
  · have hq : ((k - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (show k - 1 ≠ 0 by omega)
    have hD : (1 + ((k - 2 : ℕ) : ℝ) * pK k) ≠ 0 :=
      (subcriticalDenominator_pos hk).ne'
    field_simp [hq, hD]
  · exact div_nonneg
      (mul_nonneg (by positivity) hγ₀.le) (subcriticalDenominator_pos hk).le

theorem subcriticalCandidateFamily_nonempty (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ₀ : 0 < γ) (hγ : γ < gammaK k) :
    (subcriticalCandidateFamily k hk γ).Nonempty := by
  let α := subcriticalOneBlockLength k γ
  let L := oneBlockSequence k hk α
    (subcriticalOneBlockLength_pos hk hγ₀)
    (subcriticalOneBlockLength_lt_one hk hγ).le
  refine ⟨WLambda hk L, L, ?_, rfl⟩
  exact subcriticalOneBlockSequence_isCandidate hk hγ₀ hγ

/-! ## The full piecewise candidate family -/

/-- The paper's family `Vγ`.  It is empty outside the paper domain
`k ≥ 3`, `0 < γ < 1`; inside that domain it is the exact block-sequence
family for `γ < gammaK k` and the singleton `{Wγ∗}` otherwise. -/
noncomputable def candidateOptimizerFamily (k : ℕ) (γ : ℝ) : Set Graphon :=
  if hk : 3 ≤ k then
    if hγ : γ ∈ Ioo (0 : ℝ) 1 then
      if hsub : γ < gammaK k then
        subcriticalCandidateFamily k hk γ
      else
        {Wstar k hk γ ⟨le_of_not_gt hsub, hγ.2⟩}
    else ∅
  else ∅

theorem candidateOptimizerFamily_of_lt {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hsub : γ < gammaK k) :
    candidateOptimizerFamily k γ = subcriticalCandidateFamily k hk γ := by
  simp [candidateOptimizerFamily, hk, hγ, hsub]

theorem candidateOptimizerFamily_of_ge {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hcrit : gammaK k ≤ γ) :
    candidateOptimizerFamily k γ = {Wstar k hk γ ⟨hcrit, hγ.2⟩} := by
  simp [candidateOptimizerFamily, hk, hγ, not_lt.mpr hcrit]

theorem candidateOptimizerFamily_at_gammaK (k : ℕ) (hk : 3 ≤ k) :
    candidateOptimizerFamily k (gammaK k) =
      {Wstar k hk (gammaK k) ⟨le_rfl, gammaK_lt_one hk⟩} := by
  exact candidateOptimizerFamily_of_ge hk (gammaK_mem_Ioo hk) le_rfl

theorem candidateOptimizerFamily_nonempty (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) : (candidateOptimizerFamily k γ).Nonempty := by
  by_cases hsub : γ < gammaK k
  · rw [candidateOptimizerFamily_of_lt hk hγ hsub]
    exact subcriticalCandidateFamily_nonempty k hk γ hγ.1 hsub
  · rw [candidateOptimizerFamily_of_ge hk hγ (le_of_not_gt hsub)]
    exact Set.singleton_nonempty _

end InducedStars
