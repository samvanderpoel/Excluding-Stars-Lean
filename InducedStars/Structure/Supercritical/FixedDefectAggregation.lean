import InducedStars.Structure.Supercritical.AggregationParameters
import InducedStars.Structure.Supercritical.SupportPatternCounting

/-!
# Aggregating the nonmedium fixed-defect family

This file performs the finite bookkeeping which is specific to the matching-
defect branch of the supercritical argument.  In particular, the sparse part
of a combined defect pattern is summed before the support-incident part, so
the repaired shifted joint-absorption comparison applies with its literal
signed support shift.
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance fixedDefectAggregationGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) := Classical.decEq _

/-! ## Signed-shift absorption geometry -/

/-- Exact finite hypotheses which turn a profile at a signed shift into all
the capacity and compact-band side conditions of the repaired shifted
joint-absorption comparison.  The three displayed inequalities are the
lower absorbed-density, lower shift-band, and upper shift-band margins.
They are numerical geometry conditions, not counting assumptions. -/
structure SupercriticalSignedShiftGeometryHypotheses
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (delta : ℝ) (D : SupercriticalDivision k (Fin n)) (u : ℤ) : Prop where
  sparseChoice_le_gain :
    Nat.choose D.sparse.card 2 ≤
      D.sparse.card *
        (D.support.card -
          (D.parts (supercriticalSmallestPartIndex hk D)).card)
  absorbedMargin :
    supercriticalAbsorptionLowerDensity k gamma *
          (supercriticalTotalCrossCapacity
            (supercriticalAbsorbSparseDivision hk D) : ℝ) +
        (u.natAbs : ℝ) +
        (supercriticalAbsorptionEdgeShift hk D : ℝ) ≤
      (supercriticalOffDiagonal k gamma -
          delta) * (supercriticalTotalCrossCapacity D : ℝ)
  shiftBandLowerMargin :
    supercriticalShiftBandDensity k gamma *
          (supercriticalPreAbsorptionVariableCapacity D : ℝ) +
        (u.natAbs : ℝ) ≤
      (supercriticalOffDiagonal k gamma - delta) *
        (supercriticalTotalCrossCapacity D : ℝ)
  shiftBandUpperMargin :
    (supercriticalOffDiagonal k gamma + delta) *
          (supercriticalTotalCrossCapacity D : ℝ) +
        (Nat.choose D.sparse.card 2 : ℝ) + (u.natAbs : ℝ) ≤
      (1 - supercriticalShiftBandDensity k gamma) *
        (supercriticalPreAbsorptionVariableCapacity D : ℝ)

/-! ## A uniform constructor from close-structure bounds -/

set_option maxHeartbeats 1600000 in
/-- A balance bound, the close-structure sparse bound, and a signed shift of
size at most `eta * n^2` imply the three uniform margins above.  Both
`delta` and `eta` are compared with the same public scalar threshold.  This
form is shared by the fixed-defect branch (`eta = 2(alpha+delta)`) and the
medium branch (`eta = epsilon`). -/
theorem supercriticalSignedShiftGeometryHypotheses_of_uniform_bound
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    {delta eta : ℝ} (hdelta0 : 0 ≤ delta)
    (hdeltaGeometry :
      delta < supercriticalJointAbsorptionGeometryDeltaBound k gamma)
    (hdeltaSigned :
      delta < supercriticalSignedShiftEpsilonBound k gamma)
    (heta0 : 0 ≤ eta)
    (heta : eta < supercriticalSignedShiftEpsilonBound k gamma)
    (D : SupercriticalDivision k (Fin n))
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hsparse : (D.sparse.card : ℝ) ≤ delta * n / 2)
    {u : ℤ} (hu : (u.natAbs : ℝ) ≤ eta * (n : ℝ) ^ 2) :
    SupercriticalSignedShiftGeometryHypotheses
      (gamma := gamma) hk delta D u := by
  let r : ℝ := ((k - 1 : ℕ) : ℝ)
  let rho := supercriticalOffDiagonal k gamma
  let lambda := supercriticalAbsorptionLowerDensity k gamma
  let lambdaShift := supercriticalShiftBandDensity k gamma
  let d := rho - lambda
  let c := 1 - rho
  let C := supercriticalTotalCrossCapacity D
  let A := supercriticalPreAbsorptionVariableCapacity D
  let B := supercriticalTotalCrossCapacity
    (supercriticalAbsorbSparseDivision hk D)
  let a := (D.parts (supercriticalSmallestPartIndex hk D)).card
  let s := D.sparse.card
  let b := D.support.card - a
  let q := Nat.choose s 2
  let E := supercriticalAbsorptionEdgeShift hk D
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (by omega : 0 < k - 1)
  have hrTwo : (2 : ℝ) ≤ r := by
    dsimp [r]
    exact_mod_cast (by omega : 2 ≤ k - 1)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hd : 0 < d := by
    dsimp [d, rho, lambda]
    exact sub_pos.mpr (supercriticalAbsorptionLowerDensity_lt_rho hk hgamma)
  have hc : 0 < c := by
    dsimp [c, rho]
    exact sub_pos.mpr (supercriticalOffDiagonal_lt_one hk hgamma.2)
  have hlambda0 : 0 ≤ lambda :=
    (supercriticalAbsorptionLowerDensity_pos hk hgamma).le
  have hlambda1 : lambda ≤ 1 :=
    (supercriticalAbsorptionLowerDensity_lt_one hk hgamma).le
  have hshift0 : 0 ≤ lambdaShift :=
    (supercriticalShiftBandDensity_pos hk hgamma).le
  have hshiftLambda : lambdaShift ≤ lambda / 2 := by
    dsimp [lambdaShift, supercriticalShiftBandDensity]
    exact min_le_left _ _
  have hshiftComp : lambdaShift ≤ c / 4 := by
    dsimp [lambdaShift, supercriticalShiftBandDensity, c, rho]
    exact min_le_right _ _

  have hdeltaRank : delta ≤ 1 / (2 * r) := by
    have h := hdeltaGeometry.le.trans
      ((min_le_right
        (supercriticalJointAbsorptionDeltaBound k gamma)
        (min (1 / (2 * r))
          (min (d / 2) (d / (100 * r ^ 2))))).trans
        (min_le_left _ _))
    simpa [supercriticalJointAbsorptionGeometryDeltaBound, r, d, rho,
      lambda] using h
  have hdeltaHalf : delta ≤ d / 2 := by
    have h := hdeltaGeometry.le.trans
      ((min_le_right
        (supercriticalJointAbsorptionDeltaBound k gamma)
        (min (1 / (2 * r))
          (min (d / 2) (d / (100 * r ^ 2))))).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
    simpa [supercriticalJointAbsorptionGeometryDeltaBound, r, d, rho,
      lambda] using h
  have hdeltaD : delta ≤ d / (100 * r ^ 2) := by
    have h := hdeltaSigned.le.trans
      (min_le_left
        ((supercriticalOffDiagonal k gamma -
            supercriticalAbsorptionLowerDensity k gamma) /
          (100 * (((k - 1 : ℕ) : ℝ) ^ 2)))
        ((1 - supercriticalOffDiagonal k gamma) /
          (100 * (((k - 1 : ℕ) : ℝ) ^ 2))))
    simpa [supercriticalSignedShiftEpsilonBound, d, r, rho, lambda] using h
  have hdeltaC : delta ≤ c / (100 * r ^ 2) := by
    have h := hdeltaSigned.le.trans
      (min_le_right
        ((supercriticalOffDiagonal k gamma -
            supercriticalAbsorptionLowerDensity k gamma) /
          (100 * (((k - 1 : ℕ) : ℝ) ^ 2)))
        ((1 - supercriticalOffDiagonal k gamma) /
          (100 * (((k - 1 : ℕ) : ℝ) ^ 2))))
    simpa [supercriticalSignedShiftEpsilonBound, c, r, rho] using h
  have hetaD : eta ≤ d / (100 * r ^ 2) := by
    have h := heta.le.trans
      (min_le_left
        ((supercriticalOffDiagonal k gamma -
            supercriticalAbsorptionLowerDensity k gamma) /
          (100 * (((k - 1 : ℕ) : ℝ) ^ 2)))
        ((1 - supercriticalOffDiagonal k gamma) /
          (100 * (((k - 1 : ℕ) : ℝ) ^ 2))))
    simpa [supercriticalSignedShiftEpsilonBound, d, r, rho, lambda] using h
  have hetaC : eta ≤ c / (100 * r ^ 2) := by
    have h := heta.le.trans
      (min_le_right
        ((supercriticalOffDiagonal k gamma -
            supercriticalAbsorptionLowerDensity k gamma) /
          (100 * (((k - 1 : ℕ) : ℝ) ^ 2)))
        ((1 - supercriticalOffDiagonal k gamma) /
          (100 * (((k - 1 : ℕ) : ℝ) ^ 2))))
    simpa [supercriticalSignedShiftEpsilonBound, c, r, rho] using h

  have hpartLower (i : Fin (k - 1)) :
      (n : ℝ) / (2 * r) ≤ ((D.parts i).card : ℝ) := by
    have hdn : delta * (n : ℝ) ≤ (n : ℝ) / (2 * r) := by
      have h := mul_le_mul_of_nonneg_right hdeltaRank hn0
      calc
        delta * (n : ℝ) ≤ (1 / (2 * r)) * (n : ℝ) := h
        _ = (n : ℝ) / (2 * r) := by ring
    have hlower := (abs_le.mp (hbalanced i)).1
    have hid : (n : ℝ) / r - (n : ℝ) / (2 * r) =
        (n : ℝ) / (2 * r) := by field_simp; ring
    rw [← hid]
    have hlower' : (n : ℝ) / r - delta * n ≤
        ((D.parts i).card : ℝ) := by
      simpa [r] using (show
        (n : ℝ) / ((k - 1 : ℕ) : ℝ) - delta * n ≤
          ((D.parts i).card : ℝ) by linarith)
    exact (sub_le_sub_left hdn ((n : ℝ) / r)).trans hlower'
  have hsPart : (s : ℝ) ≤ (a : ℝ) := by
    have hs' : (s : ℝ) ≤ (n : ℝ) / (4 * r) := by
      calc
        (s : ℝ) ≤ delta * n / 2 := by simpa [s] using hsparse
        _ ≤ ((1 / (2 * r)) * n) / 2 := by gcongr
        _ = (n : ℝ) / (4 * r) := by ring
    have hhalf : (n : ℝ) / (4 * r) ≤ (n : ℝ) / (2 * r) := by
      have : 0 ≤ (n : ℝ) / r := by positivity
      calc
        (n : ℝ) / (4 * r) = ((n : ℝ) / r) / 4 := by ring
        _ ≤ ((n : ℝ) / r) / 2 := by linarith
        _ = (n : ℝ) / (2 * r) := by ring
    exact hs'.trans (hhalf.trans (by
      simpa [a] using hpartLower (supercriticalSmallestPartIndex hk D)))
  have haB : a ≤ b := by
    let iStar := supercriticalSmallestPartIndex hk D
    have hcardFin : 1 < Fintype.card (Fin (k - 1)) := by simp; omega
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcardFin iStar
    have hsub : D.parts j ⊆ D.support \ D.parts iStar := by
      intro v hv
      rw [Finset.mem_sdiff]
      refine ⟨D.part_subset_support j hv, ?_⟩
      intro hvi
      exact hj (D.mem_part_unique hv hvi)
    have hjcard : (D.parts j).card ≤
        D.support.card - (D.parts iStar).card := by
      have hcard := Finset.card_le_card hsub
      simpa [Finset.card_sdiff_of_subset (D.part_subset_support iStar)]
        using hcard
    exact (supercriticalSmallestPartIndex_card_le hk D j).trans hjcard
  have hsB : s ≤ b := (by exact_mod_cast hsPart : s ≤ a).trans haB
  have hcapacity : q ≤ s * b := by
    calc
      q = Nat.choose s 2 := rfl
      _ ≤ s ^ 2 := Nat.choose_le_pow s 2
      _ = s * s := by ring
      _ ≤ s * b := Nat.mul_le_mul_left s hsB

  let i : Fin (k - 1) := ⟨0, by omega⟩
  let j : Fin (k - 1) := ⟨1, by omega⟩
  let e : SupercriticalPartPair k := ⟨i, j, by simp [i, j]⟩
  have hC : (n : ℝ) ^ 2 / (4 * r ^ 2) ≤ (C : ℝ) := by
    have hcap : (n : ℝ) ^ 2 / (4 * r ^ 2) ≤
        (crossEdgeCapacity D e : ℝ) := by
      calc
        (n : ℝ) ^ 2 / (4 * r ^ 2) =
            ((n : ℝ) / (2 * r)) * ((n : ℝ) / (2 * r)) := by ring
        _ ≤ ((D.parts i).card : ℝ) * ((D.parts j).card : ℝ) :=
          mul_le_mul (hpartLower i) (hpartLower j) (by positivity)
            (by positivity)
        _ = (crossEdgeCapacity D e : ℝ) := by
          simp [crossEdgeCapacity, e]
    have hterm : crossEdgeCapacity D e ≤ C := by
      dsimp [C, supercriticalTotalCrossCapacity]
      exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ e)
    exact hcap.trans (by exact_mod_cast hterm)
  have haN : (a : ℝ) ≤ n := by
    exact_mod_cast (show a ≤ n by
      dsimp [a]
      simpa using Finset.card_le_univ
        (D.parts (supercriticalSmallestPartIndex hk D)))
  have hsN : (s : ℝ) ≤ n := by
    exact_mod_cast (show s ≤ n by
      dsimp [s]
      simpa using Finset.card_le_univ D.sparse)
  have hbN : (b : ℝ) ≤ n := by
    exact_mod_cast (show b ≤ n by
      dsimp [b]
      exact (Nat.sub_le _ _).trans (by
        simpa using Finset.card_le_univ D.support))
  have hq : (q : ℝ) ≤ (s : ℝ) * n / 2 := by
    dsimp [q]
    rw [Nat.cast_choose_two]
    nlinarith [mul_le_mul_of_nonneg_left hsN hs0]
  have hsDelta : (s : ℝ) * n ≤ delta * (n : ℝ) ^ 2 / 2 := by
    have h := mul_le_mul_of_nonneg_right hsparse hn0
    calc
      (s : ℝ) * n ≤ (delta * n / 2) * n := h
      _ = delta * (n : ℝ) ^ 2 / 2 := by ring
  have hB : B = C + s * b := by
    simpa [B, C, s, b, a] using
      supercriticalTotalCrossCapacity_absorbSparse_eq hk D
  have hA : A = C + q := by rfl
  have hE : E = a * s + q := by rfl

  have hsmallD :
      (5 / 4 : ℝ) * delta + eta ≤ d / (8 * r ^ 2) := by
    have hx0 : 0 ≤ d / (100 * r ^ 2) := by positivity
    calc
      (5 / 4 : ℝ) * delta + eta ≤
          (9 / 4 : ℝ) * (d / (100 * r ^ 2)) := by linarith
      _ ≤ d / (8 * r ^ 2) := by
        rw [show (9 / 4 : ℝ) * (d / (100 * r ^ 2)) =
            (9 / 400 : ℝ) * (d / r ^ 2) by ring,
          show d / (8 * r ^ 2) = (1 / 8 : ℝ) * (d / r ^ 2) by ring]
        have : 0 ≤ d / r ^ 2 := by positivity
        nlinarith
  have hsmallC :
      delta / 4 + eta ≤ c / (8 * r ^ 2) := by
    have hx0 : 0 ≤ c / (100 * r ^ 2) := by positivity
    calc
      delta / 4 + eta ≤ (5 / 4 : ℝ) *
          (c / (100 * r ^ 2)) := by linarith
      _ ≤ c / (8 * r ^ 2) := by
        rw [show (5 / 4 : ℝ) * (c / (100 * r ^ 2)) =
            (1 / 80 : ℝ) * (c / r ^ 2) by ring,
          show c / (8 * r ^ 2) = (1 / 8 : ℝ) * (c / r ^ 2) by ring]
        have : 0 ≤ c / r ^ 2 := by positivity
        nlinarith
  have hsmallD' :
      delta / 4 + eta ≤ d / (8 * r ^ 2) := by
    have hx0 : 0 ≤ d / (100 * r ^ 2) := by positivity
    calc
      delta / 4 + eta ≤ (5 / 4 : ℝ) *
          (d / (100 * r ^ 2)) := by linarith
      _ ≤ d / (8 * r ^ 2) := by
        rw [show (5 / 4 : ℝ) * (d / (100 * r ^ 2)) =
            (1 / 80 : ℝ) * (d / r ^ 2) by ring,
          show d / (8 * r ^ 2) = (1 / 8 : ℝ) * (d / r ^ 2) by ring]
        have : 0 ≤ d / r ^ 2 := by positivity
        nlinarith
  have hsurplusD : d * (n : ℝ) ^ 2 / (8 * r ^ 2) ≤
      (rho - delta - lambda) * (C : ℝ) := by
    have hgap : d / 2 ≤ rho - delta - lambda := by
      dsimp [d]
      linarith
    calc
      d * (n : ℝ) ^ 2 / (8 * r ^ 2) =
          (d / 2) * ((n : ℝ) ^ 2 / (4 * r ^ 2)) := by ring
      _ ≤ (d / 2) * (C : ℝ) := by gcongr
      _ ≤ (rho - delta - lambda) * (C : ℝ) := by gcongr
  have hsurplusLower : d * (n : ℝ) ^ 2 / (8 * r ^ 2) ≤
      (rho - delta - lambdaShift) * (C : ℝ) := by
    have hgap : d / 2 ≤ rho - delta - lambdaShift := by
      dsimp [d]
      linarith
    calc
      d * (n : ℝ) ^ 2 / (8 * r ^ 2) =
          (d / 2) * ((n : ℝ) ^ 2 / (4 * r ^ 2)) := by ring
      _ ≤ (d / 2) * (C : ℝ) := by gcongr
      _ ≤ (rho - delta - lambdaShift) * (C : ℝ) := by gcongr
  have hdeltaQuarterC : delta ≤ c / 4 := by
    have hr2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith [hrTwo]
    have hden : c / (100 * r ^ 2) ≤ c / 4 := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 100 * r ^ 2)
        (by norm_num : (0 : ℝ) < 4)).2
      nlinarith
    exact hdeltaC.trans hden
  have hsurplusUpper : c * (n : ℝ) ^ 2 / (8 * r ^ 2) ≤
      (1 - rho - delta - lambdaShift) * (C : ℝ) := by
    have hgap : c / 2 ≤ 1 - rho - delta - lambdaShift := by
      dsimp [c]
      linarith
    calc
      c * (n : ℝ) ^ 2 / (8 * r ^ 2) =
          (c / 2) * ((n : ℝ) ^ 2 / (4 * r ^ 2)) := by ring
      _ ≤ (c / 2) * (C : ℝ) := by gcongr
      _ ≤ (1 - rho - delta - lambdaShift) * (C : ℝ) := by gcongr

  have habsorptionError :
      lambda * ((s * b : ℕ) : ℝ) + (u.natAbs : ℝ) +
          ((a * s + q : ℕ) : ℝ) ≤
        ((5 / 4 : ℝ) * delta + eta) * (n : ℝ) ^ 2 := by
    have hlsb : lambda * ((s * b : ℕ) : ℝ) ≤ (s : ℝ) * n := by
      push_cast
      calc
        lambda * ((s : ℝ) * (b : ℝ)) ≤
            1 * ((s : ℝ) * (b : ℝ)) :=
          mul_le_mul_of_nonneg_right hlambda1 (by positivity)
        _ = (s : ℝ) * (b : ℝ) := one_mul _
        _ ≤ (s : ℝ) * n :=
          mul_le_mul_of_nonneg_left hbN hs0
    have has : ((a * s : ℕ) : ℝ) ≤ (s : ℝ) * n := by
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right haN hs0]
    push_cast
    have hlsb' : lambda * ((s : ℝ) * (b : ℝ)) ≤ (s : ℝ) * n := by
      simpa only [Nat.cast_mul] using hlsb
    have has' : (a : ℝ) * (s : ℝ) ≤ (s : ℝ) * n := by
      simpa only [Nat.cast_mul] using has
    calc
      lambda * ((s : ℝ) * (b : ℝ)) + (u.natAbs : ℝ) +
          ((a : ℝ) * (s : ℝ) + (q : ℝ)) ≤
        (5 / 2 : ℝ) * ((s : ℝ) * n) + eta * (n : ℝ) ^ 2 := by
          linarith [hlsb', has', hq, hu]
      _ ≤ ((5 / 4 : ℝ) * delta + eta) * (n : ℝ) ^ 2 := by
        nlinarith [hsDelta]
  have hbandErrorD : lambdaShift * (q : ℝ) + (u.natAbs : ℝ) ≤
      (delta / 4 + eta) * (n : ℝ) ^ 2 := by
    have hshiftOne : lambdaShift ≤ 1 :=
      hshiftLambda.trans (by linarith)
    have hqDelta : (q : ℝ) ≤ delta * (n : ℝ) ^ 2 / 4 := by
      nlinarith [hq, hsDelta]
    calc
      lambdaShift * (q : ℝ) + (u.natAbs : ℝ) ≤
          (q : ℝ) + eta * (n : ℝ) ^ 2 := by
        have hmul : lambdaShift * (q : ℝ) ≤ (q : ℝ) := by
          simpa using (mul_le_mul_of_nonneg_right hshiftOne
            (show (0 : ℝ) ≤ (q : ℝ) by positivity))
        exact add_le_add hmul hu
      _ ≤ delta * (n : ℝ) ^ 2 / 4 + eta * (n : ℝ) ^ 2 :=
        add_le_add hqDelta le_rfl
      _ = (delta / 4 + eta) * (n : ℝ) ^ 2 := by ring
  refine {
    sparseChoice_le_gain := by simpa [q, s, b, a] using hcapacity
    absorbedMargin := ?_
    shiftBandLowerMargin := ?_
    shiftBandUpperMargin := ?_ }
  · change lambda * (B : ℝ) + (u.natAbs : ℝ) + (E : ℝ) ≤
      (rho - delta) * (C : ℝ)
    rw [hB, hE]
    push_cast
    have herr :
        lambda * ((s * b : ℕ) : ℝ) + (u.natAbs : ℝ) +
            ((a * s + q : ℕ) : ℝ) ≤
          (rho - delta - lambda) * (C : ℝ) :=
      habsorptionError.trans <| by
        have hmul := mul_le_mul_of_nonneg_right hsmallD (sq_nonneg (n : ℝ))
        apply hmul.trans
        rw [show d / (8 * r ^ 2) * (n : ℝ) ^ 2 =
          d * (n : ℝ) ^ 2 / (8 * r ^ 2) by ring]
        exact hsurplusD
    push_cast at herr
    dsimp [rho, lambda, B, C, E, s, b, a, q] at herr ⊢
    linarith

  · change lambdaShift * (A : ℝ) + (u.natAbs : ℝ) ≤
      (rho - delta) * (C : ℝ)
    rw [hA]
    push_cast
    have herr : lambdaShift * (q : ℝ) + (u.natAbs : ℝ) ≤
        (rho - delta - lambdaShift) * (C : ℝ) :=
      hbandErrorD.trans <| by
        have hmul := mul_le_mul_of_nonneg_right hsmallD' (sq_nonneg (n : ℝ))
        apply hmul.trans
        rw [show d / (8 * r ^ 2) * (n : ℝ) ^ 2 =
          d * (n : ℝ) ^ 2 / (8 * r ^ 2) by ring]
        exact hsurplusLower
    dsimp [rho, lambdaShift, A, C, q] at herr ⊢
    linarith
  · change (rho + delta) * (C : ℝ) + (q : ℝ) +
      (u.natAbs : ℝ) ≤ (1 - lambdaShift) * (A : ℝ)
    rw [hA]
    push_cast
    have herr : lambdaShift * (q : ℝ) + (u.natAbs : ℝ) ≤
        (1 - rho - delta - lambdaShift) * (C : ℝ) :=
      hbandErrorD.trans <| by
        have hmul := mul_le_mul_of_nonneg_right hsmallC (sq_nonneg (n : ℝ))
        apply hmul.trans
        rw [show c / (8 * r ^ 2) * (n : ℝ) ^ 2 =
          c * (n : ℝ) ^ 2 / (8 * r ^ 2) by ring]
        exact hsurplusUpper
    dsimp [rho, lambdaShift, A, C, q] at herr ⊢
    linarith

/-! ## Parameter-specialized shift bounds -/

/-- The aggregation hierarchy places `delta` inside the common signed-shift
margin. -/
theorem SupercriticalAggregationParameters.delta_lt_signedShiftBound
    {k : ℕ} {gamma : ℝ}
    (P : SupercriticalAggregationParameters k gamma) :
    P.delta < supercriticalSignedShiftEpsilonBound k gamma := by
  have hsum : P.delta < P.alpha + P.delta := by linarith [P.alpha_pos]
  have hsum0 : 0 < P.alpha + P.delta := by linarith [P.alpha_pos, P.delta_pos]
  have htwice : P.alpha + P.delta < 2 * (P.alpha + P.delta) := by
    nlinarith
  exact hsum.trans (htwice.trans P.support_signed_shift)

/-- Parameter-specialized form of the uniform signed-shift constructor. -/
theorem supercriticalSignedShiftGeometryHypotheses_of_parameters
    {k n : ℕ} {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (P : SupercriticalAggregationParameters k gamma)
    {eta : ℝ} (heta0 : 0 ≤ eta)
    (heta : eta < supercriticalSignedShiftEpsilonBound k gamma)
    (D : SupercriticalDivision k (Fin n))
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n)
    (hsparse : (D.sparse.card : ℝ) ≤ P.delta * n / 2)
    {u : ℤ} (hu : (u.natAbs : ℝ) ≤ eta * (n : ℝ) ^ 2) :
    SupercriticalSignedShiftGeometryHypotheses
      (gamma := gamma) P.rank P.delta D u :=
  supercriticalSignedShiftGeometryHypotheses_of_uniform_bound
    P.rank hgamma P.delta_pos.le P.joint_absorption_delta
      P.delta_lt_signedShiftBound heta0 heta D hbalanced hsparse hu

/-- A low support pattern has a signed support shift inside the fixed-branch
budget selected by `SupercriticalAggregationParameters`. -/
theorem supercriticalSupportDefectShift_le_parameter_budget
    {k n : ℕ} {gamma : ℝ}
    (P : SupercriticalAggregationParameters k gamma)
    (D : SupercriticalDivision k (Fin n)) (h : ℕ)
    (T : SimpleGraph (Fin n))
    (hsparse : (D.sparse.card : ℝ) ≤ P.delta * n / 2)
    (hT : T ∈ supercriticalLowSupportPatternFinset D P.alpha h) :
    ((supercriticalSupportDefectShift D T).natAbs : ℝ) ≤
      (2 * (P.alpha + P.delta)) * (n : ℝ) ^ 2 := by
  have hmem := mem_supercriticalLowSupportPatternFinset.mp hT
  have hshiftNat := supercriticalSupportDefectShift_natAbs_le_edgeCount D T
  rw [hmem.1] at hshiftNat
  have hedge := supercriticalSupportPattern_edgeCount_le D
    P.alpha_pos.le P.delta_pos.le hsparse hT
  have hmatchingEndpoints : 2 * h ≤ n := by
    have hcard := Finset.card_le_univ
      (s := supercriticalCanonicalMatchingEndpoints D T)
    simpa [hmem.2.1] using hcard
  have hmatchingReal : (2 : ℝ) * h ≤ n := by exact_mod_cast hmatchingEndpoints
  calc
    ((supercriticalSupportDefectShift D T).natAbs : ℝ) ≤
        ((finiteGraphEdges T).card : ℝ) := by exact_mod_cast hshiftNat
    _ ≤ 2 * (h : ℝ) * (P.alpha + P.delta) * (n : ℝ) := hedge
    _ ≤ (P.alpha + P.delta) * (n : ℝ) ^ 2 := by
      have hsum0 : 0 ≤ P.alpha + P.delta := by
        linarith [P.alpha_pos, P.delta_pos]
      nlinarith [mul_le_mul_of_nonneg_right hmatchingReal
        (mul_nonneg hsum0 (by positivity : (0 : ℝ) ≤ n))]
    _ ≤ (2 * (P.alpha + P.delta)) * (n : ℝ) ^ 2 := by
      have hsum0 : 0 ≤ P.alpha + P.delta := by
        linarith [P.alpha_pos, P.delta_pos]
      nlinarith [sq_nonneg (n : ℝ)]

/-- The fixed-branch support shift satisfies all signed absorption geometry
conditions with no additional parameter choice. -/
theorem supercriticalSignedShiftGeometryHypotheses_of_supportPattern
    {k n : ℕ} {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (P : SupercriticalAggregationParameters k gamma)
    (D : SupercriticalDivision k (Fin n))
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n)
    (hsparse : (D.sparse.card : ℝ) ≤ P.delta * n / 2)
    (h : ℕ) (T : SimpleGraph (Fin n))
    (hT : T ∈ supercriticalLowSupportPatternFinset D P.alpha h) :
    SupercriticalSignedShiftGeometryHypotheses
      (gamma := gamma) P.rank P.delta D
        (supercriticalSupportDefectShift D T) := by
  exact supercriticalSignedShiftGeometryHypotheses_of_parameters hgamma P
    (by linarith [P.alpha_pos, P.delta_pos]) P.support_signed_shift
      D hbalanced hsparse
      (supercriticalSupportDefectShift_le_parameter_budget
        P D h T hsparse hT)

/-- The exact data consumed by
`supercriticalShiftedProfileAggregate_le_absorbedCoPartite`. -/
structure SupercriticalShiftedAbsorptionData
    {k n : ℕ} (hk : 3 ≤ k)
    (gamma : ℝ) (D : SupercriticalDivision k (Fin n))
    (m LShift : ℕ) (u : ℤ) : Prop where
  aggregate_count : (LShift : ℤ) +
    (divisionInternalCliqueCapacity D : ℤ) + u = (m : ℤ)
  sparseChoice_le_gain :
    Nat.choose D.sparse.card 2 ≤
      D.sparse.card *
        (D.support.card -
          (D.parts (supercriticalSmallestPartIndex hk D)).card)
  absorbedInternal_le_m :
    divisionInternalCliqueCapacity
      (supercriticalAbsorbSparseDivision hk D) ≤ m
  shiftSelected_le_preAbsorption :
    LShift ≤ supercriticalPreAbsorptionVariableCapacity D
  cleanSelected_le_preAbsorption :
    supercriticalCleanSelectedCount D m ≤
      supercriticalPreAbsorptionVariableCapacity D
  absorbedSelected_le_capacity :
    supercriticalAbsorbedSelectedCount hk D m ≤
      supercriticalTotalCrossCapacity
        (supercriticalAbsorbSparseDivision hk D)
  absorbedDensity_lower :
    supercriticalAbsorptionLowerDensity k gamma *
        (supercriticalTotalCrossCapacity
          (supercriticalAbsorbSparseDivision hk D) : ℝ) ≤
      (supercriticalAbsorbedSelectedCount hk D m : ℝ)
  shiftBand_lower :
    supercriticalShiftBandDensity k gamma *
        (supercriticalPreAbsorptionVariableCapacity D : ℝ) ≤
      (supercriticalCleanSelectedCount D m : ℝ)
  shiftBand_upper :
    (supercriticalCleanSelectedCount D m : ℝ) ≤
      (1 - supercriticalShiftBandDensity k gamma) *
        (supercriticalPreAbsorptionVariableCapacity D : ℝ)
  selected_distance :
    Nat.dist LShift (supercriticalCleanSelectedCount D m) = u.natAbs

private theorem fixedAggregation_profileTotal_lower
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

private theorem fixedAggregation_profileTotal_le
    {k n : ℕ} (D : SupercriticalDivision k (Fin n))
    (profile : SupercriticalEdgeProfile D) :
    profileTotal profile ≤ supercriticalTotalCrossCapacity D := by
  unfold profileTotal supercriticalTotalCrossCapacity
  exact Finset.sum_le_sum fun e _ ↦ profile.count_le_capacity e

private theorem fixedAggregation_profileTotal_upper
    {k n : ℕ} {rho delta : ℝ}
    (D : SupercriticalDivision k (Fin n))
    (profile : SupercriticalEdgeProfile D)
    (hdensity : ∀ e : SupercriticalPartPair k,
      profileDensity profile e ≤ rho + delta) :
    (profileTotal profile : ℝ) ≤
      (rho + delta) * (supercriticalTotalCrossCapacity D : ℝ) := by
  rw [supercriticalTotalCrossCapacity, Nat.cast_sum, Finset.mul_sum,
    profileTotal, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro e _
  have hcap : (0 : ℝ) < (crossEdgeCapacity D e : ℕ) := by
    exact_mod_cast crossEdgeCapacity_pos D e
  have h := (div_le_iff₀ hcap).mp (hdensity e)
  simpa [profileDensity, crossEdgeCapacity, Nat.cast_mul] using h

/-- A profile at the literal signed support shift, together with the three
finite density margins, supplies all side conditions of the repaired shifted
comparison. -/
theorem supercriticalShiftedAbsorptionData_of_profile
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    {delta : ℝ} {m t : ℕ}
    (D : SupercriticalDivision k (Fin n)) {u : ℤ}
    (profile : SupercriticalEdgeProfile D)
    (hprofile : SupercriticalProfileAtShift D m
      (supercriticalOffDiagonal k gamma) delta (u + (t : ℤ)) profile)
    (ht : t ≤ Nat.choose D.sparse.card 2)
    (H : SupercriticalSignedShiftGeometryHypotheses
      (gamma := gamma) hk delta D u) :
    SupercriticalShiftedAbsorptionData hk gamma D m
      (profileTotal profile + t) u := by
  let X := profileTotal profile
  let q := Nat.choose D.sparse.card 2
  let I := divisionInternalCliqueCapacity D
  let E := supercriticalAbsorptionEdgeShift hk D
  let A := supercriticalPreAbsorptionVariableCapacity D
  let B := supercriticalTotalCrossCapacity
    (supercriticalAbsorbSparseDivision hk D)
  let LShift := X + t
  let L := supercriticalCleanSelectedCount D m
  let LStar := supercriticalAbsorbedSelectedCount hk D m
  let rho := supercriticalOffDiagonal k gamma
  let lambda := supercriticalAbsorptionLowerDensity k gamma
  let lambdaShift := supercriticalShiftBandDensity k gamma
  have hlambda0 : 0 ≤ lambda :=
    (supercriticalAbsorptionLowerDensity_pos hk hgamma).le
  have hXlower : (rho - delta) *
      (supercriticalTotalCrossCapacity D : ℝ) ≤ (X : ℝ) := by
    simpa [rho, X] using fixedAggregation_profileTotal_lower D profile
      (fun e ↦ (hprofile.2 e).1)
  have hXupper : X ≤ supercriticalTotalCrossCapacity D := by
    simpa [X] using fixedAggregation_profileTotal_le D profile
  have hXupperDensity : (X : ℝ) ≤ (rho + delta) *
      (supercriticalTotalCrossCapacity D : ℝ) := by
    simpa [rho, X] using fixedAggregation_profileTotal_upper D profile
      (fun e ↦ (hprofile.2 e).2)
  have hUEreal : (u.natAbs : ℝ) + (E : ℝ) ≤ (X : ℝ) := by
    have hnonneg : 0 ≤ lambda * (B : ℝ) := by positivity
    calc
      (u.natAbs : ℝ) + (E : ℝ) ≤
          lambda * (B : ℝ) + (u.natAbs : ℝ) + (E : ℝ) := by linarith
      _ ≤ (rho - delta) *
          (supercriticalTotalCrossCapacity D : ℝ) := H.absorbedMargin
      _ ≤ (X : ℝ) := hXlower
  have hUE : u.natAbs + E ≤ X := by exact_mod_cast hUEreal
  have hcount : (LShift : ℤ) + (I : ℤ) + u = (m : ℤ) := by
    have hpcount := hprofile.1
    dsimp [LShift, X, I] at hpcount ⊢
    omega
  have hInternal :
      divisionInternalCliqueCapacity
          (supercriticalAbsorbSparseDivision hk D) = I + E := by
    simpa [I, E] using
      divisionInternalCliqueCapacity_absorbSparse_eq_add_shift hk D
  have hIE : I + E ≤ m := by
    have hUEInt : (u.natAbs : ℤ) + (E : ℤ) ≤ (X : ℤ) := by
      exact_mod_cast hUE
    have hIEInt : ((I + E : ℕ) : ℤ) ≤ (m : ℤ) := by
      rw [Nat.cast_add]
      by_cases hu : 0 ≤ u
      · have huNat : (u.natAbs : ℤ) = u := Int.natAbs_of_nonneg hu
        omega
      · have hu' : u ≤ 0 := le_of_not_ge hu
        have huNat : (u.natAbs : ℤ) = -u :=
          Int.ofNat_natAbs_of_nonpos hu'
        omega
    exact_mod_cast hIEInt
  have hIL : I ≤ m := (Nat.le_add_right I E).trans hIE
  have hLShiftA : LShift ≤ A := by
    dsimp [LShift, A, X, q]
    exact Nat.add_le_add hXupper ht
  have hLcast : (L : ℤ) = (LShift : ℤ) + u := by
    dsimp [L, supercriticalCleanSelectedCount]
    rw [Nat.cast_sub hIL]
    omega
  have hLStarCast : (LStar : ℤ) = (LShift : ℤ) + u - E := by
    dsimp [LStar, supercriticalAbsorbedSelectedCount]
    rw [hInternal]
    rw [Nat.cast_sub hIE, Nat.cast_add]
    omega
  have hLlower : lambdaShift * (A : ℝ) ≤ (L : ℝ) := by
    have hXBand : lambdaShift * (A : ℝ) + (u.natAbs : ℝ) ≤
        (X : ℝ) := by
      calc
        lambdaShift * (A : ℝ) + (u.natAbs : ℝ) ≤
            (rho - delta) *
              (supercriticalTotalCrossCapacity D : ℝ) :=
          H.shiftBandLowerMargin
        _ ≤ (X : ℝ) := hXlower
    have hShiftLe : LShift ≤ L + u.natAbs := by
      have hcast : (LShift : ℤ) ≤ (L : ℤ) + (u.natAbs : ℤ) := by
        by_cases hu : 0 ≤ u
        · rw [Int.natAbs_of_nonneg hu]
          omega
        · rw [Int.ofNat_natAbs_of_nonpos (le_of_not_ge hu)]
          omega
      exact_mod_cast hcast
    have hXL : X ≤ LShift := by
      dsimp [LShift]
      omega
    have hreal : (X : ℝ) ≤ (L : ℝ) + (u.natAbs : ℝ) := by
      exact_mod_cast hXL.trans hShiftLe
    linarith
  have hLupper : (L : ℝ) ≤ (1 - lambdaShift) * (A : ℝ) := by
    have hLLe : L ≤ LShift + u.natAbs := by
      have hcast : (L : ℤ) ≤ (LShift : ℤ) + (u.natAbs : ℤ) := by
        by_cases hu : 0 ≤ u
        · rw [Int.natAbs_of_nonneg hu]
          omega
        · rw [Int.ofNat_natAbs_of_nonpos (le_of_not_ge hu)]
          omega
      exact_mod_cast hcast
    have hLt : (LShift : ℝ) ≤
        (rho + delta) * (supercriticalTotalCrossCapacity D : ℝ) +
          (q : ℝ) := by
      dsimp [LShift]
      push_cast
      exact add_le_add hXupperDensity (by exact_mod_cast ht)
    have hLLeReal : (L : ℝ) ≤
        (LShift : ℝ) + (u.natAbs : ℝ) := by exact_mod_cast hLLe
    have hHupper := H.shiftBandUpperMargin
    simpa [q] using (show (L : ℝ) ≤
        (1 - lambdaShift) * (A : ℝ) by
      linarith [hHupper])
  have hStarLower : lambda * (B : ℝ) ≤ (LStar : ℝ) := by
    have hXStar : lambda * (B : ℝ) + (u.natAbs : ℝ) + (E : ℝ) ≤
        (X : ℝ) := by
      exact H.absorbedMargin.trans hXlower
    have hShiftLe : LShift ≤ LStar + E + u.natAbs := by
      have hcast : (LShift : ℤ) ≤
          (LStar : ℤ) + (E : ℤ) + (u.natAbs : ℤ) := by
        by_cases hu : 0 ≤ u
        · rw [Int.natAbs_of_nonneg hu]
          omega
        · rw [Int.ofNat_natAbs_of_nonpos (le_of_not_ge hu)]
          omega
      exact_mod_cast hcast
    have hXL : X ≤ LShift := by dsimp [LShift]; omega
    have hreal : (X : ℝ) ≤
        (LStar : ℝ) + (E : ℝ) + (u.natAbs : ℝ) := by
      exact_mod_cast hXL.trans hShiftLe
    linarith
  have hLA : L ≤ A := by
    have hnonneg : (0 : ℝ) ≤ 1 - lambdaShift := by
      have := supercriticalShiftBandDensity_lt_half hk hgamma
      dsimp [lambdaShift]
      linarith
    have hcoef : (1 - lambdaShift) * (A : ℝ) ≤ (A : ℝ) := by
      have hshift0 := (supercriticalShiftBandDensity_pos hk hgamma).le
      dsimp [lambdaShift] at hshift0 ⊢
      nlinarith
    exact_mod_cast hLupper.trans hcoef
  have hA_le_B : A ≤ B := by
    have hgain := H.sparseChoice_le_gain
    simpa [A, B] using
      (show supercriticalPreAbsorptionVariableCapacity D ≤
          supercriticalTotalCrossCapacity
            (supercriticalAbsorbSparseDivision hk D) by
        rw [supercriticalTotalCrossCapacity_absorbSparse_eq hk D]
        exact Nat.add_le_add_left hgain _)
  have hStarB : LStar ≤ B := by
    have hStarL : LStar ≤ L := by
      dsimp [LStar, L, supercriticalAbsorbedSelectedCount,
        supercriticalCleanSelectedCount]
      rw [hInternal]
      omega
    exact hStarL.trans (hLA.trans hA_le_B)
  have hdist : Nat.dist LShift L = u.natAbs := by
    by_cases hu : 0 ≤ u
    · have huNat : (u.natAbs : ℤ) = u := Int.natAbs_of_nonneg hu
      have hNat : L = LShift + u.natAbs := by
        exact_mod_cast (show (L : ℤ) =
          (LShift : ℤ) + (u.natAbs : ℤ) by omega)
      rw [hNat]
      simp [Nat.dist]
    · have hu' : u ≤ 0 := le_of_not_ge hu
      have huNat : (u.natAbs : ℤ) = -u :=
        Int.ofNat_natAbs_of_nonpos hu'
      have hNat : LShift = L + u.natAbs := by
        exact_mod_cast (show (LShift : ℤ) =
          (L : ℤ) + (u.natAbs : ℤ) by omega)
      rw [hNat]
      simp [Nat.dist]
  refine {
    aggregate_count := hcount
    sparseChoice_le_gain := H.sparseChoice_le_gain
    absorbedInternal_le_m := by simpa [hInternal] using hIE
    shiftSelected_le_preAbsorption := hLShiftA
    cleanSelected_le_preAbsorption := hLA
    absorbedSelected_le_capacity := hStarB
    absorbedDensity_lower := by simpa [lambda, B, LStar] using hStarLower
    shiftBand_lower := by simpa [lambdaShift, A, L] using hLlower
    shiftBand_upper := by simpa [lambdaShift, A, L] using hLupper
    selected_distance := by simpa [LShift, L] using hdist }

/-! ## Fixed-pattern profile aggregation -/

/-- Total multiplicity of all cross profiles at one literal signed shift. -/
noncomputable def supercriticalProfileMassAtShift
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) (m : ℕ) (rho delta : ℝ)
    (u : ℤ) : ℕ := by
  classical
  exact ∑ profile ∈ supercriticalAllEdgeProfilesFinset D,
    if SupercriticalProfileAtShift D m rho delta u profile then
      supercriticalProfileMultiplicity profile else 0

/-- A fixed combined-defect fiber is covered by its exact cross-profile
fibers.  The statement is deliberately an inequality, so it does not depend
on a separate disjoint-union API. -/
theorem card_supercriticalFixedDefectGraphFinset_le_sum_profiles
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n)) :
    ((supercriticalFixedDefectGraphFinset
        k hk gamma hgamma alpha m n tau hn D T).card : ℝ) ≤
      ∑ profile ∈ supercriticalAllEdgeProfilesFinset D,
        ((supercriticalFixedDefectProfileGraphFinset
          k hk gamma hgamma alpha m n tau hn D T profile).card : ℝ) := by
  classical
  let F := supercriticalFixedDefectGraphFinset
    k hk gamma hgamma alpha m n tau hn D T
  let fibers := fun profile : SupercriticalEdgeProfile D ↦
    supercriticalFixedDefectProfileGraphFinset
      k hk gamma hgamma alpha m n tau hn D T profile
  have hsubset : F ⊆
      (supercriticalAllEdgeProfilesFinset D).biUnion fibers := by
    intro G hG
    rw [Finset.mem_biUnion]
    refine ⟨crossEdgeProfile G D,
      mem_supercriticalAllEdgeProfilesFinset D _, ?_⟩
    rw [mem_supercriticalFixedDefectProfileGraphFinset]
    exact ⟨hG, rfl⟩
  have hnat : F.card ≤
      ∑ profile ∈ supercriticalAllEdgeProfilesFinset D,
        (fibers profile).card :=
    (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
  exact_mod_cast hnat

/-- Extract a common matching penalty from all admissible profiles of one
fixed combined-defect pattern.  The two hypotheses isolate the geometric
and probabilistic inputs; all profile bookkeeping is proved here. -/
theorem card_supercriticalFixedDefectGraphFinset_le_profileMass_mul_exp
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha rho delta : ℝ} {m n : ℕ} {tau : ℝ}
    {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (c : ℝ)
    (hadmissible : ∀ G ∈ supercriticalFixedDefectGraphFinset
      k hk gamma hgamma alpha m n tau hn D T,
      SupercriticalProfileAtShift D m rho delta
        (supercriticalDefectShift T D) (crossEdgeProfile G D))
    (hprofilePenalty : ∀ profile : SupercriticalEdgeProfile D,
      SupercriticalProfileAtShift D m rho delta
          (supercriticalDefectShift T D) profile →
      ((supercriticalFixedDefectProfileGraphFinset
        k hk gamma hgamma alpha m n tau hn D T profile).card : ℝ) ≤
        (supercriticalProfileMultiplicity profile : ℝ) * Real.exp c) :
    ((supercriticalFixedDefectGraphFinset
        k hk gamma hgamma alpha m n tau hn D T).card : ℝ) ≤
      (supercriticalProfileMassAtShift D m rho delta
        (supercriticalDefectShift T D) : ℝ) *
        Real.exp c := by
  classical
  have hpartition := card_supercriticalFixedDefectGraphFinset_le_sum_profiles
    (hk := hk) (gamma := gamma) (hgamma := hgamma)
      (alpha := alpha) (m := m) (tau := tau) (hn := hn) D T
  calc
    ((supercriticalFixedDefectGraphFinset
        k hk gamma hgamma alpha m n tau hn D T).card : ℝ) ≤
        ∑ profile ∈ supercriticalAllEdgeProfilesFinset D,
          ((supercriticalFixedDefectProfileGraphFinset
            k hk gamma hgamma alpha m n tau hn D T profile).card : ℝ) :=
      hpartition
    _ ≤ ∑ profile ∈ supercriticalAllEdgeProfilesFinset D,
        ((if SupercriticalProfileAtShift D m rho delta
              (supercriticalDefectShift T D) profile then
            supercriticalProfileMultiplicity profile else 0 : ℕ) : ℝ) *
          Real.exp c := by
      apply Finset.sum_le_sum
      intro profile _hprofileAll
      by_cases hp : SupercriticalProfileAtShift D m rho delta
          (supercriticalDefectShift T D) profile
      · change ((supercriticalFixedDefectProfileGraphFinset
            k hk gamma hgamma alpha m n tau hn D T profile).card : ℝ) ≤
          ((if SupercriticalProfileAtShift D m rho delta
              (supercriticalDefectShift T D) profile then
            supercriticalProfileMultiplicity profile else 0 : ℕ) : ℝ) *
              Real.exp c
        rw [if_pos hp]
        exact hprofilePenalty profile hp
      · have hempty : supercriticalFixedDefectProfileGraphFinset
            k hk gamma hgamma alpha m n tau hn D T profile = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          rintro ⟨G, hG⟩
          have hfixed :=
            (mem_supercriticalFixedDefectProfileGraphFinset.mp hG).1
          have hactual := hadmissible G hfixed
          rw [(mem_supercriticalFixedDefectProfileGraphFinset.mp hG).2] at hactual
          exact hp hactual
        change ((supercriticalFixedDefectProfileGraphFinset
            k hk gamma hgamma alpha m n tau hn D T profile).card : ℝ) ≤
          ((if SupercriticalProfileAtShift D m rho delta
              (supercriticalDefectShift T D) profile then
            supercriticalProfileMultiplicity profile else 0 : ℕ) : ℝ) *
              Real.exp c
        rw [if_neg hp, hempty]
        simp
    _ = ((∑ profile ∈ supercriticalAllEdgeProfilesFinset D,
          if SupercriticalProfileAtShift D m rho delta
              (supercriticalDefectShift T D) profile then
            supercriticalProfileMultiplicity profile else 0 : ℕ) : ℝ) *
          Real.exp c := by
      rw [Nat.cast_sum]
      push_cast
      symm
      exact Finset.sum_mul _ _ _
    _ = (supercriticalProfileMassAtShift D m rho delta
          (supercriticalDefectShift T D) : ℝ) * Real.exp c := by
      rfl

/-- Regroup the repaired shifted aggregate by the multiplicity mass at each
sparse-edge count. -/
theorem supercriticalShiftedProfileAggregate_eq_sum_profileMass
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) (m : ℕ) (rho delta : ℝ)
    (u : ℤ) :
    supercriticalShiftedProfileAggregate D m rho delta u =
      ∑ t ∈ Finset.range (supercriticalSparsePotentialCapacity D + 1),
        supercriticalProfileMassAtShift D m rho delta (u + (t : ℤ)) *
          Nat.choose (supercriticalSparsePotentialCapacity D) t := by
  classical
  unfold supercriticalShiftedProfileAggregate
  apply Finset.sum_congr rfl
  intro t _ht
  unfold supercriticalProfileMassAtShift
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro profile _hprofile
  by_cases hp : SupercriticalProfileAtShift D m rho delta
      (u + (t : ℤ)) profile <;> simp [hp]

/-! ## Regrouping combined patterns by their sparse-induced edge set -/

/-- The sparse-induced edge count, packaged as an index in the full range of
possible sparse edge counts. -/
def supercriticalSparsePatternIndex
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    Fin (supercriticalSparsePotentialCapacity D + 1) := by
  let t := inducedEdgeCount (supercriticalSparseInducedPattern D T) D.sparse
  have ht : t ≤ supercriticalSparsePotentialCapacity D := by
    have hsum := inducedEdgeCount_add_compl T D.sparse
    simpa [t, supercriticalSparsePotentialCapacity] using
      (show inducedEdgeCount T D.sparse ≤ D.sparse.card.choose 2 by omega)
  exact ⟨t, by omega⟩

@[simp] theorem supercriticalSparsePatternIndex_val
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    (supercriticalSparsePatternIndex D T : ℕ) =
      inducedEdgeCount (supercriticalSparseInducedPattern D T) D.sparse :=
  rfl

/-- On a fixed support-incident fiber, the sparse-induced edge set determines
the original combined pattern. -/
theorem supercriticalSparseInducedEdges_injectiveOn_supportFiber
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) (T₀ : SimpleGraph V) :
    Set.InjOn (fun T : SimpleGraph V ↦ supercriticalSparseInducedEdges T D)
      {T | supercriticalSupportIncidentGraph D T = T₀} := by
  classical
  intro T hT U hU hedges
  have hsparse : supercriticalSparseInducedPattern D T =
      supercriticalSparseInducedPattern D U := by
    ext x y
    have hmem := congrArg
      (fun E : Finset (Sym2 V) ↦ s(x, y) ∈ E) hedges
    simpa [sparseInducedGraph_adj] using hmem
  calc
    T = supercriticalSupportIncidentGraph D T ⊔
          supercriticalSparseInducedPattern D T :=
      (supercriticalSupportIncident_sup_sparseInduced D T).symm
    _ = T₀ ⊔ supercriticalSparseInducedPattern D T := by rw [hT]
    _ = T₀ ⊔ supercriticalSparseInducedPattern D U := by rw [hsparse]
    _ = supercriticalSupportIncidentGraph D U ⊔
          supercriticalSparseInducedPattern D U := by rw [hU]
    _ = U := supercriticalSupportIncident_sup_sparseInduced D U

/-- At fixed support graph and fixed sparse-edge count, the number of
combined patterns is at most the corresponding binomial coefficient. -/
noncomputable def supercriticalSupportSparseIndexFiber
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) (patterns : Finset (SimpleGraph V))
    (T₀ : SimpleGraph V)
    (t : Fin (supercriticalSparsePotentialCapacity D + 1)) :
    Finset (SimpleGraph V) := by
  classical
  exact patterns.filter fun T ↦
    supercriticalSupportIncidentGraph D T = T₀ ∧
      supercriticalSparsePatternIndex D T = t

@[simp] theorem mem_supercriticalSupportSparseIndexFiber
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) (patterns : Finset (SimpleGraph V))
    (T₀ : SimpleGraph V)
    (t : Fin (supercriticalSparsePotentialCapacity D + 1))
    (T : SimpleGraph V) :
    T ∈ supercriticalSupportSparseIndexFiber D patterns T₀ t ↔
      T ∈ patterns ∧ supercriticalSupportIncidentGraph D T = T₀ ∧
        supercriticalSparsePatternIndex D T = t := by
  classical
  simp only [supercriticalSupportSparseIndexFiber, Finset.mem_filter]

theorem card_filter_support_sparseIndex_le_choose
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) (patterns : Finset (SimpleGraph V))
    (T₀ : SimpleGraph V)
    (t : Fin (supercriticalSparsePotentialCapacity D + 1)) :
    (supercriticalSupportSparseIndexFiber D patterns T₀ t).card ≤
      Nat.choose (supercriticalSparsePotentialCapacity D) t := by
  classical
  let F := supercriticalSupportSparseIndexFiber D patterns T₀ t
  let encode := fun T : SimpleGraph V ↦ supercriticalSparseInducedEdges T D
  let codes := (supercriticalSparsePotentialEdges D).powersetCard (t : ℕ)
  have hinj : Set.InjOn encode (F : Set (SimpleGraph V)) := by
    apply (supercriticalSparseInducedEdges_injectiveOn_supportFiber D T₀).mono
    intro T hT
    exact (mem_supercriticalSupportSparseIndexFiber D patterns T₀ t T).mp hT |>.2.1
  have hsubset : F.image encode ⊆ codes := by
    intro E hE
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hE
    have hmem :=
      (mem_supercriticalSupportSparseIndexFiber D patterns T₀ t T).mp hT
    rw [Finset.mem_powersetCard]
    constructor
    · exact supercriticalSparseInducedEdges_subset_potential T D
    · rw [card_supercriticalSparseInducedEdges]
      have hindex := congrArg Fin.val hmem.2.2
      simpa using hindex
  calc
    F.card = (F.image encode).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ codes.card := Finset.card_le_card hsubset
    _ = Nat.choose (supercriticalSparsePotentialCapacity D) t := by
      simp [codes, card_supercriticalSparsePotentialEdges_eq_capacity]

end InducedStars
