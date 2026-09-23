import InducedStars.Structure.Supercritical.CleanSparseMultiplicity
import Mathlib.Tactic

/-!
# Quantitative bounds for clean sparse-set absorption

This file isolates the elementary geometry and entropy estimates used by the
supercritical clean sparse-set penalty.  The incident profile count imported
from `CleanSparseMultiplicity` is indexed by the other main parts, so every
cross-cell meeting the absorbed part occurs exactly once.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

variable {k n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Incident profile counts -/

/-- Sorting a pair of distinct part labels does not change its cross-cell
capacity. -/
@[simp] theorem crossEdgeCapacity_ofDistinct
    (D : SupercriticalDivision k V) (i j : Fin (k - 1)) (hij : i ≠ j) :
    crossEdgeCapacity D (SupercriticalPartPair.ofDistinct i j hij) =
      (D.parts i).card * (D.parts j).card := by
  by_cases hlt : i < j
  · simp [SupercriticalPartPair.ofDistinct, hlt, crossEdgeCapacity]
  · simp [SupercriticalPartPair.ofDistinct, hlt, crossEdgeCapacity,
      Nat.mul_comm]

/-- A coordinatewise lower density bound gives the exact expected lower bound
for the sum of profile counts incident with the smallest part. -/
theorem supercriticalIncidentProfileCount_lower
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (profile : SupercriticalEdgeProfile D) {rho delta : ℝ}
    (hlower : ∀ e, rho - delta ≤ profileDensity profile e) :
    (rho - delta) *
          ((D.parts (supercriticalSmallestPartIndex hk D)).card : ℝ) *
          (∑ j : {j : Fin (k - 1) //
              j ≠ supercriticalSmallestPartIndex hk D},
            ((D.parts j.1).card : ℝ)) ≤
      (supercriticalIncidentProfileCount hk D profile : ℝ) := by
  classical
  let iStar := supercriticalSmallestPartIndex hk D
  have hcoordinate
      (j : {j : Fin (k - 1) // j ≠ iStar}) :
      (rho - delta) * ((D.parts iStar).card : ℝ) *
          ((D.parts j.1).card : ℝ) ≤
        (profile.count
          (SupercriticalPartPair.ofDistinct iStar j.1 j.2.symm) : ℝ) := by
    let e := SupercriticalPartPair.ofDistinct iStar j.1 j.2.symm
    have hcap : (0 : ℝ) < crossEdgeCapacity D e := by
      exact_mod_cast crossEdgeCapacity_pos D e
    have h := (le_div_iff₀ hcap).mp (hlower e)
    simpa [profileDensity, e, iStar, Nat.cast_mul, mul_assoc] using h
  rw [supercriticalIncidentProfileCount]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ ↦ by
    simpa [iStar, mul_assoc] using hcoordinate j

/-! ## Explicit capacity and penalty constants -/

/-- A conservative fraction of the cross-cell gain created by absorbing one
sparse vertex into a balanced smallest part. -/
def supercriticalSparseCapacityConstant (k : ℕ) (gamma : ℝ) : ℝ :=
  ((k - 2 : ℕ) : ℝ) * supercriticalOffDiagonal k gamma /
    (8 * (((k - 1 : ℕ) : ℝ) ^ 2))

/-- Half of the available capacity gain, leaving the other half to absorb the
entropy of the arbitrary graph on the sparse set. -/
def supercriticalSparsePenaltyConstant (k : ℕ) (gamma : ℝ) : ℝ :=
  supercriticalSparseCapacityConstant k gamma / 2

theorem supercriticalSparseCapacityConstant_pos
    (hk : 3 ≤ k) {gamma : ℝ} (hgamma : gammaK k < gamma) :
    0 < supercriticalSparseCapacityConstant k gamma := by
  unfold supercriticalSparseCapacityConstant
  have hkm2 : (0 : ℝ) < (k - 2 : ℕ) := by
    exact_mod_cast (by omega : 0 < k - 2)
  have hrho : 0 < supercriticalOffDiagonal k gamma :=
    supercriticalOffDiagonal_pos hk hgamma.le
  have hkm1 : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  positivity

theorem supercriticalSparsePenaltyConstant_pos
    (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    0 < supercriticalSparsePenaltyConstant k gamma := by
  exact div_pos (supercriticalSparseCapacityConstant_pos hk hgamma.1) (by norm_num)

/-- A basic smallness threshold sufficient for balance, positive lower cell
density, and absorption of sparse-graph entropy. -/
def supercriticalSparseDeltaBound (k : ℕ) (gamma : ℝ) : ℝ :=
  min (supercriticalOffDiagonal k gamma / 2)
    (min (1 / (6 * ((k - 1 : ℕ) : ℝ)))
      (supercriticalSparseCapacityConstant k gamma / Real.log 2))

theorem supercriticalSparseDeltaBound_pos
    (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    0 < supercriticalSparseDeltaBound k gamma := by
  unfold supercriticalSparseDeltaBound
  have hrho := supercriticalOffDiagonal_pos hk hgamma.1.le
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hcap := supercriticalSparseCapacityConstant_pos hk hgamma.1
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem supercriticalSparseDeltaBound_spec
    {gamma delta : ℝ} (hdelta : delta < supercriticalSparseDeltaBound k gamma) :
    delta < supercriticalOffDiagonal k gamma / 2 ∧
      delta < 1 / (6 * ((k - 1 : ℕ) : ℝ)) ∧
      delta < supercriticalSparseCapacityConstant k gamma / Real.log 2 := by
  simpa [supercriticalSparseDeltaBound, lt_min_iff] using hdelta

/-- The paper-facing radius also preserves the density margins required by
close structure and is small compared with the preceding medium scale. -/
def supercriticalCleanSparseDeltaBound
    (k : ℕ) (gamma alpha : ℝ) : ℝ :=
  min (alpha / 100)
    (min (supercriticalOffDiagonal k gamma / 4)
      (min ((1 - supercriticalOffDiagonal k gamma) / 4)
        (supercriticalSparseDeltaBound k gamma)))

theorem supercriticalCleanSparseDeltaBound_pos
    (hk : 3 ≤ k) {gamma alpha : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) (halpha : 0 < alpha) :
    0 < supercriticalCleanSparseDeltaBound k gamma alpha := by
  unfold supercriticalCleanSparseDeltaBound
  have hrho := supercriticalOffDiagonal_pos hk hgamma.1.le
  have hrhoOne := supercriticalOffDiagonal_lt_one hk hgamma.2
  have hbasic := supercriticalSparseDeltaBound_pos hk hgamma
  positivity

theorem supercriticalCleanSparseDeltaBound_spec
    (hk : 3 ≤ k) {gamma alpha delta : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (hdelta : delta < supercriticalCleanSparseDeltaBound k gamma alpha) :
    delta < alpha / 100 ∧
      3 * delta < supercriticalOffDiagonal k gamma ∧
      supercriticalOffDiagonal k gamma + 3 * delta < 1 ∧
      delta < supercriticalOffDiagonal k gamma / 2 ∧
      delta < 1 / (6 * ((k - 1 : ℕ) : ℝ)) ∧
      delta < supercriticalSparseCapacityConstant k gamma / Real.log 2 := by
  have hsplit :
      delta < alpha / 100 ∧
        delta < supercriticalOffDiagonal k gamma / 4 ∧
        delta < (1 - supercriticalOffDiagonal k gamma) / 4 ∧
        delta < supercriticalSparseDeltaBound k gamma := by
    simpa [supercriticalCleanSparseDeltaBound, lt_min_iff] using hdelta
  have hbasic := supercriticalSparseDeltaBound_spec hsplit.2.2.2
  have hrho := supercriticalOffDiagonal_pos hk hgamma.1.le
  have hrhoOne := supercriticalOffDiagonal_lt_one hk hgamma.2
  refine ⟨hsplit.1, ?_, ?_, hbasic.1, hbasic.2.1, hbasic.2.2⟩
  · linarith [hsplit.2.1]
  · linarith [hsplit.2.2.1]

/-! ## From balanced geometry to a linear-in-`s n` gain -/

/-- Every other part contributes at least half the balanced average. -/
theorem sum_other_supercriticalPart_card_lower
    (hk : 3 ≤ k) (D : SupercriticalDivision k (Fin n))
    {delta : ℝ} (_hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)))
    (hclose : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n) :
    ((k - 2 : ℕ) : ℝ) *
          ((n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ))) ≤
      ∑ j : {j : Fin (k - 1) //
          j ≠ supercriticalSmallestPartIndex hk D},
        ((D.parts j.1).card : ℝ) := by
  classical
  let iStar := supercriticalSmallestPartIndex hk D
  have hpart (j : {j : Fin (k - 1) // j ≠ iStar}) :
      (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
        ((D.parts j.1).card : ℝ) := by
    have hraw := hclose j.1
    have hr : (0 : ℝ) < (k - 1 : ℕ) := by
      exact_mod_cast (by omega : 0 < k - 1)
    have hn0 : (0 : ℝ) ≤ n := by positivity
    rw [abs_le] at hraw
    have hcoeff : delta ≤ 1 / (2 * ((k - 1 : ℕ) : ℝ)) := by
      calc
        delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)) := hdelta
        _ ≤ 1 / (2 * ((k - 1 : ℕ) : ℝ)) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          nlinarith
    have hscaled := mul_le_mul_of_nonneg_right hcoeff hn0
    have hid : (n : ℝ) / ((k - 1 : ℕ) : ℝ) -
          1 / (2 * ((k - 1 : ℕ) : ℝ)) * n =
        (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) := by
      field_simp
      ring
    rw [← hid]
    linarith
  have hsum := Finset.sum_le_sum
    (s := Finset.univ)
    (f := fun _ : {j : Fin (k - 1) // j ≠ iStar} ↦
      (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)))
    (g := fun j ↦ ((D.parts j.1).card : ℝ))
    (fun j _ ↦ hpart j)
  have hcard : Fintype.card {j : Fin (k - 1) // j ≠ iStar} = k - 2 := by
    calc
      Fintype.card {j : Fin (k - 1) // j ≠ iStar} =
          Fintype.card (Fin (k - 1)) - 1 := Set.card_ne_eq iStar
      _ = k - 2 := by simp; omega
  simpa [iStar, hcard] using hsum

/-- Balanced parts and positive cell density turn the absorbed capacity into
an explicit `c s n` gain.  No asymptotic notation or large-`n` loss is used. -/
theorem supercriticalSparseCapacityExponent_lower
    (hk : 3 ≤ k) {gamma delta : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (D : SupercriticalDivision k (Fin n))
    (profile : SupercriticalEdgeProfile D)
    (hdelta0 : 0 ≤ delta)
    (hdeltaRho : delta ≤ supercriticalOffDiagonal k gamma / 2)
    (hdeltaBalance : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)))
    (hclose : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hlower : ∀ e,
      supercriticalOffDiagonal k gamma - delta ≤ profileDensity profile e) :
    supercriticalSparseCapacityConstant k gamma *
          (D.sparse.card : ℝ) * n ≤
      (D.sparse.card : ℝ) /
          ((D.parts (supercriticalSmallestPartIndex hk D)).card +
            D.sparse.card : ℕ) *
        (supercriticalIncidentProfileCount hk D profile : ℝ) := by
  let rho := supercriticalOffDiagonal k gamma
  let r : ℝ := (k - 1 : ℕ)
  let a : ℝ := (D.parts (supercriticalSmallestPartIndex hk D)).card
  let s : ℝ := D.sparse.card
  let bsum : ℝ := ∑ j : {j : Fin (k - 1) //
      j ≠ supercriticalSmallestPartIndex hk D}, ((D.parts j.1).card : ℝ)
  let q : ℝ := supercriticalIncidentProfileCount hk D profile
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (by omega : 0 < k - 1)
  have hrho : 0 < rho := supercriticalOffDiagonal_pos hk hgamma.1.le
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast (D.parts_nonempty
      (supercriticalSmallestPartIndex hk D)).card_pos
  have has : 0 < a + s := by positivity
  have hs : 0 ≤ s := by positivity
  have hn : 0 < (n : ℝ) := by
    have hi := D.parts_nonempty (supercriticalSmallestPartIndex hk D)
    have hu : (Finset.univ : Finset (Fin n)).Nonempty :=
      hi.mono (Finset.subset_univ _)
    exact_mod_cast (by simpa using hu.card_pos)
  have haLower : n / (2 * r) ≤ a := by
    have hraw := hclose (supercriticalSmallestPartIndex hk D)
    rw [abs_le] at hraw
    have hcoeff : delta ≤ 1 / (2 * r) := by
      calc
        delta ≤ 1 / (6 * r) := by simpa [r] using hdeltaBalance
        _ ≤ 1 / (2 * r) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          nlinarith
    have hscaled := mul_le_mul_of_nonneg_right hcoeff hn.le
    have hid : (n : ℝ) / r - 1 / (2 * r) * n = n / (2 * r) := by
      field_simp
      ring
    rw [← hid]
    dsimp [a, r]
    linarith
  have hbLower : ((k - 2 : ℕ) : ℝ) * (n / (2 * r)) ≤ bsum := by
    simpa [bsum, r] using sum_other_supercriticalPart_card_lower
      hk D hdelta0 hdeltaBalance hclose
  have hcount : (rho - delta) * a * bsum ≤ q := by
    simpa [rho, a, bsum, q] using
      supercriticalIncidentProfileCount_lower hk D profile hlower
  have hrhoDelta : rho / 2 ≤ rho - delta := by
    dsimp [rho] at hdeltaRho ⊢
    linarith
  have hrhoDelta0 : 0 ≤ rho - delta := by
    have : 0 ≤ rho / 2 := by positivity
    exact this.trans hrhoDelta
  have hbsum : 0 ≤ bsum := by dsimp [bsum]; positivity
  have hcountCoarse :
      rho / 2 * a * (((k - 2 : ℕ) : ℝ) * (n / (2 * r))) ≤ q := by
    calc
      rho / 2 * a * (((k - 2 : ℕ) : ℝ) * (n / (2 * r))) ≤
          (rho - delta) * a * bsum := by
        gcongr
      _ ≤ q := hcount
  have haPlusSLe : a + s ≤ n := by
    have hnat :
        (D.parts (supercriticalSmallestPartIndex hk D)).card + D.sparse.card ≤ n := by
      have hcard := Finset.card_le_card
        (show D.parts (supercriticalSmallestPartIndex hk D) ∪ D.sparse ⊆
          (Finset.univ : Finset (Fin n)) from Finset.subset_univ _)
      rw [Finset.card_union_of_disjoint
        (D.part_disjoint_sparse (supercriticalSmallestPartIndex hk D)),
        Finset.card_univ] at hcard
      simpa using hcard
    dsimp [a, s]
    exact_mod_cast hnat
  have hratio : 1 / (2 * r) ≤ a / (a + s) := by
    have hdiv : a / n ≤ a / (a + s) :=
      (div_le_div_iff₀ hn has).2 (by nlinarith)
    have hdivLower : 1 / (2 * r) ≤ a / n := by
      apply (le_div_iff₀ hn).2
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using haLower
    exact hdivLower.trans hdiv
  let B : ℝ := ((k - 2 : ℕ) : ℝ) * (n / (2 * r))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    supercriticalSparseCapacityConstant k gamma * s * n =
        s * (1 / (2 * r)) * (rho / 2 * B) := by
      dsimp [supercriticalSparseCapacityConstant, rho, r, B]
      field_simp
      ring
    _ ≤ s * (a / (a + s)) * (rho / 2 * B) := by gcongr
    _ = s / (a + s) * (rho / 2 * a * B) := by
      field_simp
    _ ≤ s / (a + s) * q := by
      exact mul_le_mul_of_nonneg_left (by simpa [B] using hcountCoarse)
        (div_nonneg hs has.le)
    _ = (D.sparse.card : ℝ) /
          ((D.parts (supercriticalSmallestPartIndex hk D)).card +
            D.sparse.card : ℕ) *
        (supercriticalIncidentProfileCount hk D profile : ℝ) := by
      simp [s, a, q]

/-! ## Entropy of the sparse induced graph -/

/-- The arbitrary graph on `s` sparse vertices contributes at most the stated
quadratic exponential. -/
theorem two_pow_choose_two_le_exp_half_log_sq (s : ℕ) :
    ((2 : ℝ) ^ Nat.choose s 2) ≤
      Real.exp (Real.log 2 / 2 * (s : ℝ) ^ 2) := by
  calc
    ((2 : ℝ) ^ Nat.choose s 2) =
        Real.exp ((Nat.choose s 2 : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (Real.log 2 / 2 * (s : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
      have hchoose : (Nat.choose s 2 : ℝ) ≤ (s : ℝ) ^ 2 / 2 := by
        rw [Nat.cast_choose_two]
        have hs : (0 : ℝ) ≤ s := by positivity
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hchoose hlog]

/-- Under the explicit sparse-size and delta conditions, the quadratic sparse
graph entropy consumes at most half the capacity gain. -/
theorem two_pow_choose_two_le_exp_sparsePenalty
    {gamma delta : ℝ} (D : SupercriticalDivision k (Fin n))
    (hdelta0 : 0 ≤ delta)
    (hdeltaEntropy :
      delta ≤ supercriticalSparseCapacityConstant k gamma / Real.log 2)
    (hsparse : (D.sparse.card : ℝ) ≤ delta * n / 2) :
    ((2 : ℝ) ^ Nat.choose D.sparse.card 2) ≤
      Real.exp (supercriticalSparsePenaltyConstant k gamma *
        (D.sparse.card : ℝ) * n) := by
  apply (two_pow_choose_two_le_exp_half_log_sq D.sparse.card).trans
  apply Real.exp_le_exp.mpr
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : (0 : ℝ) ≤ D.sparse.card := by positivity
  have hn : (0 : ℝ) ≤ n := by positivity
  have hdeltaLog : delta * Real.log 2 ≤
      supercriticalSparseCapacityConstant k gamma := by
    have := (le_div_iff₀' hlog).mp hdeltaEntropy
    simpa [mul_comm] using this
  have hsScaled := mul_le_mul_of_nonneg_left hsparse hs
  have hhalfLog : (0 : ℝ) ≤ Real.log 2 / 2 :=
    div_nonneg hlog.le (by norm_num)
  have hsqScaled := mul_le_mul_of_nonneg_left hsScaled hhalfLog
  have hcap0 : 0 ≤ supercriticalSparseCapacityConstant k gamma := by
    have hdeltaLog0 : 0 ≤ delta * Real.log 2 :=
      mul_nonneg hdelta0 hlog.le
    exact hdeltaLog0.trans hdeltaLog
  unfold supercriticalSparsePenaltyConstant
  calc
    Real.log 2 / 2 * (D.sparse.card : ℝ) ^ 2 ≤
        Real.log 2 / 2 *
          ((D.sparse.card : ℝ) * (delta * n / 2)) := by
      simpa [pow_two] using hsqScaled
    _ = (delta * Real.log 2) / 4 * (D.sparse.card : ℝ) * n := by ring
    _ ≤ supercriticalSparseCapacityConstant k gamma / 4 *
          (D.sparse.card : ℝ) * n := by
      gcongr
    _ ≤ supercriticalSparseCapacityConstant k gamma / 2 *
          (D.sparse.card : ℝ) * n := by
      have hcapSparseN : 0 ≤ supercriticalSparseCapacityConstant k gamma *
          (D.sparse.card : ℝ) * n :=
        mul_nonneg (mul_nonneg hcap0 hs) hn
      nlinarith

end InducedStars
