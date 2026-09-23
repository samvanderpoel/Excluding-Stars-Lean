import InducedStars.Structure.Supercritical.AggregateChoices
import InducedStars.Structure.Supercritical.JointAbsorptionScalars
import Mathlib.Tactic

/-!
# Finite geometry for the joint supercritical absorption comparison

This file packages the exact natural-number bookkeeping and the two selected-
density lower bounds needed by the sharp joint binomial comparison.  The
estimates use only balance of the main parts, the small sparse-set bound, and
one feasible density-band profile.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

variable {k n : ℕ}

/-! ## Selected counts -/

/-- The number of variable edges selected before sparse absorption. -/
def supercriticalCleanSelectedCount
    (D : SupercriticalDivision k (Fin n)) (m : ℕ) : ℕ :=
  m - divisionInternalCliqueCapacity D

/-- The number of cross edges selected after the sparse set has been absorbed. -/
def supercriticalAbsorbedSelectedCount
    (hk : 3 ≤ k) (D : SupercriticalDivision k (Fin n)) (m : ℕ) : ℕ :=
  m - divisionInternalCliqueCapacity (supercriticalAbsorbSparseDivision hk D)

/-! ## A uniform smallness threshold -/

/-- A conservative smallness threshold which leaves ample room in every
finite capacity estimate. -/
noncomputable def supercriticalJointAbsorptionGeometryDeltaBound
    (k : ℕ) (gamma : ℝ) : ℝ :=
  let r : ℝ := ((k - 1 : ℕ) : ℝ)
  let d := supercriticalOffDiagonal k gamma -
    supercriticalAbsorptionLowerDensity k gamma
  min (supercriticalJointAbsorptionDeltaBound k gamma)
    (min (1 / (2 * r)) (min (d / 2) (d / (100 * r ^ 2))))

theorem supercriticalJointAbsorptionGeometryDeltaBound_pos
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    0 < supercriticalJointAbsorptionGeometryDeltaBound k gamma := by
  have hr : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hd : 0 < supercriticalOffDiagonal k gamma -
      supercriticalAbsorptionLowerDensity k gamma := sub_pos.mpr
    (supercriticalAbsorptionLowerDensity_lt_rho hk hgamma)
  simp only [supercriticalJointAbsorptionGeometryDeltaBound]
  exact lt_min (supercriticalJointAbsorptionDeltaBound_pos hk hgamma)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity)))

theorem supercriticalJointAbsorptionGeometryDeltaBound_le_scalar
    (k : ℕ) (gamma : ℝ) :
    supercriticalJointAbsorptionGeometryDeltaBound k gamma ≤
      supercriticalJointAbsorptionDeltaBound k gamma :=
  min_le_left _ _

private theorem jointGeometry_delta_le_inv
    {k : ℕ} {gamma delta : ℝ}
    (hdelta : delta < supercriticalJointAbsorptionGeometryDeltaBound k gamma) :
    delta ≤ 1 / (2 * ((k - 1 : ℕ) : ℝ)) := by
  exact hdelta.le.trans <| (min_le_right _ _).trans (min_le_left _ _)

private theorem jointGeometry_delta_le_half_gap
    {k : ℕ} {gamma delta : ℝ}
    (hdelta : delta < supercriticalJointAbsorptionGeometryDeltaBound k gamma) :
    delta ≤ (supercriticalOffDiagonal k gamma -
      supercriticalAbsorptionLowerDensity k gamma) / 2 := by
  exact hdelta.le.trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans (min_le_left _ _)

private theorem jointGeometry_delta_le_gap_div
    {k : ℕ} {gamma delta : ℝ}
    (hdelta : delta < supercriticalJointAbsorptionGeometryDeltaBound k gamma) :
    delta ≤ (supercriticalOffDiagonal k gamma -
      supercriticalAbsorptionLowerDensity k gamma) /
        (100 * (((k - 1 : ℕ) : ℝ) ^ 2)) := by
  exact hdelta.le.trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans (min_le_right _ _)

/-! ## Elementary consequences of balance -/

private theorem jointGeometry_part_lower
    {k n : ℕ} (hk : 3 ≤ k) {gamma delta : ℝ}
    (hdelta : delta < supercriticalJointAbsorptionGeometryDeltaBound k gamma)
    (D : SupercriticalDivision k (Fin n))
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (i : Fin (k - 1)) :
    (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
      ((D.parts i).card : ℝ) := by
  let r : ℝ := ((k - 1 : ℕ) : ℝ)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (by omega : 0 < k - 1)
  have hn : (0 : ℝ) ≤ n := by positivity
  have hdeltaInv : delta ≤ 1 / (2 * r) := by
    simpa [r] using jointGeometry_delta_le_inv hdelta
  have hdn : delta * (n : ℝ) ≤ (n : ℝ) / (2 * r) := by
    have := mul_le_mul_of_nonneg_right hdeltaInv hn
    calc
      delta * (n : ℝ) ≤ (1 / (2 * r)) * (n : ℝ) := this
      _ = (n : ℝ) / (2 * r) := by ring
  have hlower := (abs_le.mp (hbalanced i)).1
  have hid : (n : ℝ) / r - (n : ℝ) / (2 * r) =
      (n : ℝ) / (2 * r) := by
    field_simp
    ring
  have hlower' : (n : ℝ) / r - delta * n ≤
      ((D.parts i).card : ℝ) := by
    simpa [r] using (show
      (n : ℝ) / ((k - 1 : ℕ) : ℝ) - delta * n ≤
        ((D.parts i).card : ℝ) by linarith)
  have hresult : (n : ℝ) / (2 * r) ≤ ((D.parts i).card : ℝ) := by
    rw [← hid]
    exact (sub_le_sub_left hdn ((n : ℝ) / r)).trans hlower'
  simpa [r] using hresult

private theorem jointGeometry_otherSupport_lower
    {k n : ℕ} (hk : 3 ≤ k) {gamma delta : ℝ}
    (hdelta : delta < supercriticalJointAbsorptionGeometryDeltaBound k gamma)
    (D : SupercriticalDivision k (Fin n))
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n) :
    (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
      (D.support.card -
        (D.parts (supercriticalSmallestPartIndex hk D)).card : ℕ) := by
  let iStar := supercriticalSmallestPartIndex hk D
  have hcardFin : 1 < Fintype.card (Fin (k - 1)) := by simp; omega
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcardFin iStar
  have hsub : D.parts j ⊆ D.support \ D.parts iStar := by
    intro v hv
    rw [Finset.mem_sdiff]
    refine ⟨D.part_subset_support j hv, ?_⟩
    intro hvi
    exact hj (D.mem_part_unique hv hvi)
  have hcard : (D.parts j).card ≤ D.support.card - (D.parts iStar).card := by
    have := Finset.card_le_card hsub
    simpa [Finset.card_sdiff_of_subset (D.part_subset_support iStar)] using this
  exact (jointGeometry_part_lower hk hdelta D hbalanced j).trans
    (by exact_mod_cast hcard)

private theorem jointGeometry_totalCross_lower
    {k n : ℕ} (hk : 3 ≤ k) {gamma delta : ℝ}
    (hdelta : delta < supercriticalJointAbsorptionGeometryDeltaBound k gamma)
    (D : SupercriticalDivision k (Fin n))
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n) :
    (n : ℝ) ^ 2 /
        (4 * (((k - 1 : ℕ) : ℝ) ^ 2)) ≤
      (supercriticalTotalCrossCapacity D : ℝ) := by
  let i : Fin (k - 1) := ⟨0, by omega⟩
  let j : Fin (k - 1) := ⟨1, by omega⟩
  let e : SupercriticalPartPair k := ⟨i, j, by simp [i, j]⟩
  let r : ℝ := ((k - 1 : ℕ) : ℝ)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (by omega : 0 < k - 1)
  have hi := jointGeometry_part_lower hk hdelta D hbalanced i
  have hj := jointGeometry_part_lower hk hdelta D hbalanced j
  have hcap : (n : ℝ) ^ 2 / (4 * r ^ 2) ≤
      (crossEdgeCapacity D e : ℝ) := by
    calc
      (n : ℝ) ^ 2 / (4 * r ^ 2) =
          ((n : ℝ) / (2 * r)) * ((n : ℝ) / (2 * r)) := by ring
      _ ≤ ((D.parts i).card : ℝ) * ((D.parts j).card : ℝ) :=
        mul_le_mul hi hj (by positivity) (by positivity)
      _ = (crossEdgeCapacity D e : ℝ) := by
        simp [crossEdgeCapacity, e]
  have hterm : crossEdgeCapacity D e ≤
      supercriticalTotalCrossCapacity D := by
    unfold supercriticalTotalCrossCapacity
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ e)
  exact hcap.trans (by exact_mod_cast hterm)

private theorem jointGeometry_profileTotal_lower
    {k n : ℕ} {rho delta : ℝ}
    (D : SupercriticalDivision k (Fin n))
    (profile : SupercriticalEdgeProfile D)
    (hdensity : ∀ e : SupercriticalPartPair k,
      rho - delta ≤ profileDensity profile e) :
    (rho - delta) * (supercriticalTotalCrossCapacity D : ℝ) ≤
      (profileTotal profile : ℝ) := by
  rw [supercriticalTotalCrossCapacity, Nat.cast_sum, Finset.mul_sum,
    profileTotal, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro e _
  have hcap : (0 : ℝ) < (crossEdgeCapacity D e : ℕ) := by
    exact_mod_cast crossEdgeCapacity_pos D e
  have h := (le_div_iff₀ hcap).mp (hdensity e)
  simpa [profileDensity, crossEdgeCapacity, Nat.cast_mul] using h

private theorem jointGeometry_profileTotal_le
    {k n : ℕ} (D : SupercriticalDivision k (Fin n))
    (profile : SupercriticalEdgeProfile D) :
    profileTotal profile ≤ supercriticalTotalCrossCapacity D := by
  unfold profileTotal supercriticalTotalCrossCapacity
  exact Finset.sum_le_sum fun e _ ↦ profile.count_le_capacity e

private theorem jointGeometry_choose_add_two (x y : ℕ) :
    Nat.choose (x + y) 2 =
      Nat.choose x 2 + x * y + Nat.choose y 2 := by
  induction y with
  | zero => simp
  | succ y ih =>
      change Nat.choose ((x + y) + 1) 2 =
        Nat.choose x 2 + x * (y + 1) + Nat.choose (y + 1) 2
      rw [Nat.choose_succ_succ, ih, Nat.choose_succ_succ]
      simp [Nat.choose_one_right, Nat.mul_succ] at *
      omega

/-- Exact cross-capacity gain under sparse absorption, in the form used by
the geometry package. -/
private theorem jointGeometry_totalCross_absorbSparse_eq
    {k n : ℕ} (hk : 3 ≤ k) (D : SupercriticalDivision k (Fin n)) :
    supercriticalTotalCrossCapacity (supercriticalAbsorbSparseDivision hk D) =
      supercriticalTotalCrossCapacity D + D.sparse.card *
        (D.support.card -
          (D.parts (supercriticalSmallestPartIndex hk D)).card) := by
  exact supercriticalTotalCrossCapacity_absorbSparse_eq hk D

/-! ## Exact capacity and selected-count package -/

/-- All arithmetic facts consumed by the sharp clean joint comparison.  The
structure is deliberately transparent: later proofs can project precisely the
identity or inequality they need without reopening the geometric estimates. -/
structure SupercriticalJointAbsorptionGeometry
    {k n : ℕ} (hk : 3 ≤ k) (D : SupercriticalDivision k (Fin n))
    (m t : ℕ) (profile : SupercriticalEdgeProfile D) (lambda : ℝ) : Prop where
  sparseChoice_le_gain :
    Nat.choose D.sparse.card 2 ≤
      D.sparse.card *
        (D.support.card -
          (D.parts (supercriticalSmallestPartIndex hk D)).card)
  preAbsorption_le_absorbed :
    supercriticalPreAbsorptionVariableCapacity D ≤
      supercriticalTotalCrossCapacity (supercriticalAbsorbSparseDivision hk D)
  cleanSelected_eq :
    supercriticalCleanSelectedCount D m = profileTotal profile + t
  absorbedSelected_add_edgeShift :
    supercriticalAbsorbedSelectedCount hk D m +
        supercriticalAbsorptionEdgeShift hk D =
      supercriticalCleanSelectedCount D m
  absorbedSelected_le_clean :
    supercriticalAbsorbedSelectedCount hk D m ≤
      supercriticalCleanSelectedCount D m
  cleanSelected_le_preAbsorption :
    supercriticalCleanSelectedCount D m ≤
      supercriticalPreAbsorptionVariableCapacity D
  cleanSelected_le_absorbed :
    supercriticalCleanSelectedCount D m ≤
      supercriticalTotalCrossCapacity (supercriticalAbsorbSparseDivision hk D)
  absorbedInternal_le_m :
    divisionInternalCliqueCapacity (supercriticalAbsorbSparseDivision hk D) ≤ m
  absorbedSelected_le_absorbed :
    supercriticalAbsorbedSelectedCount hk D m ≤
      supercriticalTotalCrossCapacity (supercriticalAbsorbSparseDivision hk D)
  absorbedDensity_lower :
    lambda *
        (supercriticalTotalCrossCapacity
          (supercriticalAbsorbSparseDivision hk D) : ℝ) ≤
      (supercriticalAbsorbedSelectedCount hk D m : ℝ)
  cleanDensity_lower :
    lambda *
        (supercriticalTotalCrossCapacity
          (supercriticalAbsorbSparseDivision hk D) : ℝ) ≤
      (supercriticalCleanSelectedCount D m : ℝ)

/-- Balance, a small sparse set, and one valid clean profile imply every
capacity and density condition needed by both sharp binomial ratios. -/
theorem supercriticalJointAbsorptionGeometry_of_profile
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hdelta : delta < supercriticalJointAbsorptionGeometryDeltaBound k gamma)
    {m t : ℕ} (D : SupercriticalDivision k (Fin n))
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hsparse : (D.sparse.card : ℝ) ≤ delta * n / 2)
    (profile : SupercriticalEdgeProfile D)
    (hprofile : SupercriticalProfileAtShift D m
      (supercriticalOffDiagonal k gamma) delta (t : ℤ) profile)
    (ht : t ≤ Nat.choose D.sparse.card 2) :
    SupercriticalJointAbsorptionGeometry hk D m t profile
      (supercriticalAbsorptionLowerDensity k gamma) := by
  let rho := supercriticalOffDiagonal k gamma
  let lambda := supercriticalAbsorptionLowerDensity k gamma
  let r : ℝ := ((k - 1 : ℕ) : ℝ)
  let C := supercriticalTotalCrossCapacity D
  let A := supercriticalPreAbsorptionVariableCapacity D
  let B := supercriticalTotalCrossCapacity
    (supercriticalAbsorbSparseDivision hk D)
  let a := (D.parts (supercriticalSmallestPartIndex hk D)).card
  let s := D.sparse.card
  let b := D.support.card - a
  let q := Nat.choose s 2
  let E := supercriticalAbsorptionEdgeShift hk D
  let X := profileTotal profile
  let L := supercriticalCleanSelectedCount D m
  let LStar := supercriticalAbsorbedSelectedCount hk D m
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (by omega : 0 < k - 1)
  have hlambda0 : 0 < lambda := by
    simpa [lambda] using supercriticalAbsorptionLowerDensity_pos hk hgamma
  have hlambda1 : lambda < 1 := by
    simpa [lambda] using supercriticalAbsorptionLowerDensity_lt_one hk hgamma
  have hd : 0 < rho - lambda := by
    dsimp [rho, lambda]
    exact sub_pos.mpr (supercriticalAbsorptionLowerDensity_lt_rho hk hgamma)
  have hs_nonneg : (0 : ℝ) ≤ s := by positivity
  have hn_nonneg : (0 : ℝ) ≤ n := by positivity
  have hb_nonneg : (0 : ℝ) ≤ b := by positivity
  have ha_le_n_nat : a ≤ n := by
    dsimp [a]
    simpa using Finset.card_le_univ
      (D.parts (supercriticalSmallestPartIndex hk D))
  have hs_le_n_nat : s ≤ n := by
    dsimp [s]
    simpa using Finset.card_le_univ D.sparse
  have hb_le_n_nat : b ≤ n := by
    dsimp [b, a]
    exact (Nat.sub_le _ _).trans (by simpa using Finset.card_le_univ D.support)
  have ha_le_n : (a : ℝ) ≤ n := by exact_mod_cast ha_le_n_nat
  have hs_le_n : (s : ℝ) ≤ n := by exact_mod_cast hs_le_n_nat
  have hb_le_n : (b : ℝ) ≤ n := by exact_mod_cast hb_le_n_nat
  have hdeltaInv : delta ≤ 1 / (2 * r) := by
    simpa [r] using jointGeometry_delta_le_inv hdelta
  have hs_le_partReal : (s : ℝ) ≤ (a : ℝ) := by
    have hpart := jointGeometry_part_lower hk hdelta D hbalanced
      (supercriticalSmallestPartIndex hk D)
    have hs' : (s : ℝ) ≤ (n : ℝ) / (4 * r) := by
      have hmul := mul_le_mul_of_nonneg_right hdeltaInv hn_nonneg
      have hdn : delta * (n : ℝ) ≤ (n : ℝ) / (2 * r) := by
        calc
          delta * (n : ℝ) ≤ (1 / (2 * r)) * (n : ℝ) := hmul
          _ = (n : ℝ) / (2 * r) := by ring
      calc
        (s : ℝ) ≤ delta * (n : ℝ) / 2 := by simpa [s] using hsparse
        _ ≤ ((n : ℝ) / (2 * r)) / 2 := by
          exact div_le_div_of_nonneg_right hdn (by norm_num)
        _ = (n : ℝ) / (4 * r) := by ring
    have hhalf : (n : ℝ) / (4 * r) ≤ (n : ℝ) / (2 * r) := by
      have hnr : 0 ≤ (n : ℝ) / r := by positivity
      calc
        (n : ℝ) / (4 * r) = ((n : ℝ) / r) / 4 := by ring
        _ ≤ ((n : ℝ) / r) / 2 := by linarith
        _ = (n : ℝ) / (2 * r) := by ring
    exact hs'.trans (hhalf.trans (by simpa [r, a] using hpart))
  have ha_le_b_nat : a ≤ b := by
    let iStar := supercriticalSmallestPartIndex hk D
    have hcardFin : 1 < Fintype.card (Fin (k - 1)) := by simp; omega
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcardFin iStar
    have hsub : D.parts j ⊆ D.support \ D.parts iStar := by
      intro v hv
      rw [Finset.mem_sdiff]
      refine ⟨D.part_subset_support j hv, ?_⟩
      intro hvi
      exact hj (D.mem_part_unique hv hvi)
    have hjcard : (D.parts j).card ≤ D.support.card - (D.parts iStar).card := by
      have := Finset.card_le_card hsub
      simpa [Finset.card_sdiff_of_subset (D.part_subset_support iStar)] using this
    exact (supercriticalSmallestPartIndex_card_le hk D j).trans hjcard
  have hs_le_b_nat : s ≤ b := by
    exact (by exact_mod_cast hs_le_partReal : s ≤ a).trans ha_le_b_nat
  have hq_le : q ≤ s * b := by
    calc
      q = Nat.choose s 2 := rfl
      _ ≤ s ^ 2 := Nat.choose_le_pow s 2
      _ = s * s := by ring
      _ ≤ s * b := Nat.mul_le_mul_left s hs_le_b_nat
  have hB : B = C + s * b := by
    simpa [B, C, s, b, a] using
      jointGeometry_totalCross_absorbSparse_eq hk D
  have hA : A = C + q := by
    rfl
  have hA_le_B : A ≤ B := by omega
  have hX_le_C : X ≤ C := by
    simpa [X, C] using jointGeometry_profileTotal_le D profile
  have hmNat : X + divisionInternalCliqueCapacity D + t = m := by
    dsimp [X]
    exact_mod_cast hprofile.1
  have hL : L = X + t := by
    dsimp [L, supercriticalCleanSelectedCount]
    omega
  have hL_le_A : L ≤ A := by
    rw [hL, hA]
    exact Nat.add_le_add hX_le_C (by simpa [q, s] using ht)
  have hL_le_B : L ≤ B := hL_le_A.trans hA_le_B
  have hC_lower : (n : ℝ) ^ 2 / (4 * r ^ 2) ≤ (C : ℝ) := by
    simpa [C, r] using jointGeometry_totalCross_lower hk hdelta D hbalanced
  have hX_lower : (rho - delta) * (C : ℝ) ≤ (X : ℝ) := by
    simpa [rho, C, X] using jointGeometry_profileTotal_lower D profile
      (fun e ↦ (hprofile.2 e).1)
  have hq_real : (q : ℝ) ≤ (s : ℝ) ^ 2 / 2 := by
    dsimp [q]
    rw [Nat.cast_choose_two]
    nlinarith
  have hq_half_sn : (q : ℝ) ≤ (s : ℝ) * n / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hs_le_n hs_nonneg]
  have hlambda_sb : lambda * ((s * b : ℕ) : ℝ) ≤ (s : ℝ) * n := by
    push_cast
    calc
      lambda * ((s : ℝ) * (b : ℝ)) ≤
          1 * ((s : ℝ) * (b : ℝ)) := by
        gcongr
      _ ≤ (s : ℝ) * n := by
        simpa using mul_le_mul_of_nonneg_left hb_le_n hs_nonneg
  have has : (((a * s : ℕ) : ℝ)) ≤ (s : ℝ) * n := by
    push_cast
    simpa [mul_comm] using mul_le_mul_of_nonneg_right ha_le_n hs_nonneg
  have herror : (((a * s + q : ℕ) : ℝ)) +
      lambda * ((s * b : ℕ) : ℝ) ≤
        (5 / 2 : ℝ) * (s : ℝ) * n := by
    have has' : (a : ℝ) * (s : ℝ) ≤ (s : ℝ) * n := by
      simpa only [Nat.cast_mul] using has
    have hlambda_sb' : lambda * ((s : ℝ) * (b : ℝ)) ≤
        (s : ℝ) * n := by
      simpa only [Nat.cast_mul] using hlambda_sb
    simp only [Nat.cast_add, Nat.cast_mul]
    calc
      (a : ℝ) * (s : ℝ) + (q : ℝ) +
          lambda * ((s : ℝ) * (b : ℝ)) ≤
          (s : ℝ) * n + (s : ℝ) * n / 2 + (s : ℝ) * n := by
        exact add_le_add (add_le_add has' hq_half_sn) hlambda_sb'
      _ = (5 / 2 : ℝ) * (s : ℝ) * n := by ring
  have hsdelta : (s : ℝ) ≤ delta * n / 2 := by
    simpa [s] using hsparse
  have herrorDelta : (((a * s + q : ℕ) : ℝ)) +
      lambda * ((s * b : ℕ) : ℝ) ≤
        (5 / 4 : ℝ) * delta * (n : ℝ) ^ 2 := by
    calc
      (((a * s + q : ℕ) : ℝ)) + lambda * ((s * b : ℕ) : ℝ) ≤
          (5 / 2 : ℝ) * (s : ℝ) * n := herror
      _ ≤ (5 / 4 : ℝ) * delta * (n : ℝ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hsdelta hn_nonneg]
  have hdeltaGap : delta ≤ (rho - lambda) / (100 * r ^ 2) := by
    simpa [rho, lambda, r] using jointGeometry_delta_le_gap_div hdelta
  have herrorGap : (5 / 4 : ℝ) * delta * (n : ℝ) ^ 2 ≤
      (rho - lambda) * (n : ℝ) ^ 2 / (8 * r ^ 2) := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
    calc
      (5 / 4 : ℝ) * delta * (n : ℝ) ^ 2 =
          delta * ((5 / 4 : ℝ) * (n : ℝ) ^ 2) := by ring
      _ ≤ ((rho - lambda) / (100 * r ^ 2)) *
          ((5 / 4 : ℝ) * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hdeltaGap (by positivity)
      _ = (rho - lambda) * (n : ℝ) ^ 2 / (80 * r ^ 2) := by ring
      _ ≤ (rho - lambda) * (n : ℝ) ^ 2 / (8 * r ^ 2) := by
        have hbase : 0 ≤
            (rho - lambda) * (n : ℝ) ^ 2 / (r ^ 2) := by positivity
        rw [show (rho - lambda) * (n : ℝ) ^ 2 / (80 * r ^ 2) =
            ((rho - lambda) * (n : ℝ) ^ 2 / (r ^ 2)) / 80 by ring,
          show (rho - lambda) * (n : ℝ) ^ 2 / (8 * r ^ 2) =
            ((rho - lambda) * (n : ℝ) ^ 2 / (r ^ 2)) / 8 by ring]
        exact div_le_div_of_nonneg_left hbase (by norm_num) (by norm_num)
  have hgapHalf : (rho - lambda) / 2 ≤ rho - delta - lambda := by
    have hsmall : delta ≤ (rho - lambda) / 2 := by
      simpa [rho, lambda] using jointGeometry_delta_le_half_gap hdelta
    linarith
  have hsurplus : (rho - lambda) * (n : ℝ) ^ 2 / (8 * r ^ 2) ≤
      (rho - delta - lambda) * (C : ℝ) := by
    have hgapNonneg : 0 ≤ (rho - lambda) / 2 := by positivity
    calc
      (rho - lambda) * (n : ℝ) ^ 2 / (8 * r ^ 2) =
          ((rho - lambda) / 2) *
            ((n : ℝ) ^ 2 / (4 * r ^ 2)) := by ring
      _ ≤ ((rho - lambda) / 2) * (C : ℝ) := by gcongr
      _ ≤ (rho - delta - lambda) * (C : ℝ) := by
        gcongr
  have hjoint : (((a * s + q : ℕ) : ℝ)) + lambda * (B : ℝ) ≤
      (X + t : ℕ) := by
    rw [hB]
    simp only [Nat.cast_add, Nat.cast_mul]
    have ht0 : (0 : ℝ) ≤ t := by positivity
    calc
      (a : ℝ) * (s : ℝ) + (q : ℝ) +
          lambda * ((C : ℝ) + (s : ℝ) * (b : ℝ)) =
          lambda * (C : ℝ) +
            ((((a * s + q : ℕ) : ℝ)) + lambda * ((s * b : ℕ) : ℝ)) := by
        push_cast
        ring
      _ ≤ lambda * (C : ℝ) +
          (rho - delta - lambda) * (C : ℝ) := by
        gcongr
        exact herrorDelta.trans (herrorGap.trans hsurplus)
      _ = (rho - delta) * (C : ℝ) := by ring
      _ ≤ (X : ℝ) := hX_lower
      _ ≤ (X : ℝ) + (t : ℝ) := by linarith
  have hE : E = a * s + q := by rfl
  have hE_le_Xt : E ≤ X + t := by
    have hnonneg : 0 ≤ lambda * (B : ℝ) := by positivity
    have hreal : (E : ℝ) ≤ ((X + t : ℕ) : ℝ) := by
      rw [hE]
      linarith
    exact_mod_cast hreal
  have hInternal :=
    divisionInternalCliqueCapacity_absorbSparse_eq_add_shift hk D
  have hLStarEq : LStar + E = L := by
    dsimp [LStar, supercriticalAbsorbedSelectedCount,
      L, supercriticalCleanSelectedCount]
    rw [hInternal]
    omega
  have hlowerStar : lambda * (B : ℝ) ≤ (LStar : ℝ) := by
    have hcastEq : (LStar : ℝ) + (E : ℝ) = (X + t : ℕ) := by
      exact_mod_cast (hLStarEq.trans hL)
    have hEcast : (E : ℝ) = ((a * s + q : ℕ) : ℝ) := by
      exact_mod_cast hE
    linarith
  have hStarLeL : LStar ≤ L := by omega
  have hStarLeLReal : (LStar : ℝ) ≤ (L : ℝ) := by exact_mod_cast hStarLeL
  refine {
    sparseChoice_le_gain := ?_
    preAbsorption_le_absorbed := ?_
    cleanSelected_eq := ?_
    absorbedSelected_add_edgeShift := ?_
    absorbedSelected_le_clean := ?_
    cleanSelected_le_preAbsorption := ?_
    cleanSelected_le_absorbed := ?_
    absorbedInternal_le_m := ?_
    absorbedSelected_le_absorbed := ?_
    absorbedDensity_lower := ?_
    cleanDensity_lower := ?_ }
  · simpa [q, s, b, a] using hq_le
  · simpa [A, B] using hA_le_B
  · simpa [L, X] using hL
  · simpa [LStar, E, L] using hLStarEq
  · omega
  · simpa [L, A] using hL_le_A
  · simpa [L, B] using hL_le_B
  · rw [hInternal]
    omega
  · omega
  · simpa [lambda, B, LStar] using hlowerStar
  · simpa [lambda, B, L] using hlowerStar.trans hStarLeLReal

end InducedStars
