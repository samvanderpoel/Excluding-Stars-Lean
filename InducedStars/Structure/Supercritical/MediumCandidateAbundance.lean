import InducedStars.Structure.Supercritical.MediumCandidateCounting

/-!
# Quantitative abundance of medium-star candidates

This module turns the exact finite candidate count into the explicit
`c_k * alpha^k * n^k` lower bound used by the medium-degree Janson argument.
All losses are deliberately conservative: every selected vertex set is
bounded below by the same quantity `alpha * n / (4 * (k-1))`.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

/-- A conservative positive density of potential medium stars. -/
def supercriticalMediumCandidateRate (k : ℕ) (alpha : ℝ) : ℝ :=
  alpha ^ k /
    (2 * (4 * ((k - 1 : ℕ) : ℝ)) ^ k)

theorem supercriticalMediumCandidateRate_pos
    {k : ℕ} (hk : 3 ≤ k) {alpha : ℝ} (halpha : 0 < alpha) :
    0 < supercriticalMediumCandidateRate k alpha := by
  unfold supercriticalMediumCandidateRate
  have hrNat : 0 < k - 1 := by omega
  have hr : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hrNat
  exact div_pos (pow_pos halpha k) (by positivity)

/-! ## Consequences of balanced part cardinalities -/

/-- If every part is `delta*n`-close to the average and
`delta ≤ 1/(6(k-1))`, every part has at least half the average size. -/
theorem supercriticalPart_card_lower_of_abs_close
    {k n : ℕ} (hk : 3 ≤ k) {delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)))
    {D : SupercriticalDivision k (Fin n)}
    (hclose : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (i : Fin (k - 1)) :
    (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
      ((D.parts i).card : ℝ) := by
  have hrNat : 0 < k - 1 := by omega
  have hr : 0 < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hrNat
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hlower :
      (n : ℝ) / ((k - 1 : ℕ) : ℝ) - delta * n ≤
        ((D.parts i).card : ℝ) := by
    have := hclose i
    rw [abs_le] at this
    linarith
  have hsix : 0 < 6 * ((k - 1 : ℕ) : ℝ) := by positivity
  have htwo : 0 < 2 * ((k - 1 : ℕ) : ℝ) := by positivity
  have hcoeff : 1 / (6 * ((k - 1 : ℕ) : ℝ)) ≤
      1 / (2 * ((k - 1 : ℕ) : ℝ)) := by
    rw [div_le_div_iff₀ hsix htwo]
    nlinarith
  have hdelta' : delta * (n : ℝ) ≤
      1 / (2 * ((k - 1 : ℕ) : ℝ)) * n :=
    mul_le_mul_of_nonneg_right (hdelta.trans hcoeff) hn0
  have hid : (n : ℝ) / ((k - 1 : ℕ) : ℝ) -
      1 / (2 * ((k - 1 : ℕ) : ℝ)) * n =
        (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) := by
    field_simp
    ring
  calc
    (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
        (n : ℝ) / ((k - 1 : ℕ) : ℝ) - delta * n := by
      linarith
    _ ≤ ((D.parts i).card : ℝ) := hlower

/-- The same balance assumptions imply the factor-two comparison required
by the canonical vertex-move estimate. -/
theorem supercriticalPart_card_le_two_mul_of_abs_close
    {k n : ℕ} (hk : 3 ≤ k) {delta : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)))
    {D : SupercriticalDivision k (Fin n)}
    (hclose : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (i j : Fin (k - 1)) :
    (D.parts j).card ≤ 2 * (D.parts i).card := by
  have hrNat : 0 < k - 1 := by omega
  have hr : 0 < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hrNat
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hi :
      (n : ℝ) / ((k - 1 : ℕ) : ℝ) - delta * n ≤
        ((D.parts i).card : ℝ) := by
    have := hclose i
    rw [abs_le] at this
    linarith
  have hj : ((D.parts j).card : ℝ) ≤
      (n : ℝ) / ((k - 1 : ℕ) : ℝ) + delta * n := by
    have := hclose j
    rw [abs_le] at this
    linarith
  have hsix : 0 < 6 * ((k - 1 : ℕ) : ℝ) := by positivity
  have hthreeCoeff : 3 * (1 / (6 * ((k - 1 : ℕ) : ℝ))) ≤
      1 / ((k - 1 : ℕ) : ℝ) := by
    have heq : 3 * (1 / (6 * ((k - 1 : ℕ) : ℝ))) =
        1 / (2 * ((k - 1 : ℕ) : ℝ)) := by
      field_simp
      ring
    rw [heq, div_le_div_iff₀ (by positivity) hr]
    nlinarith
  have hthreeDelta : 3 * delta ≤
      1 / ((k - 1 : ℕ) : ℝ) :=
    (mul_le_mul_of_nonneg_left hdelta (by norm_num : (0 : ℝ) ≤ 3)).trans
      hthreeCoeff
  have hthree := mul_le_mul_of_nonneg_right hthreeDelta hn0
  have hthree' : 3 * delta * (n : ℝ) ≤
      (n : ℝ) / ((k - 1 : ℕ) : ℝ) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hthree
  have hreal : ((D.parts j).card : ℝ) ≤
      2 * ((D.parts i).card : ℝ) := by linarith [hthree']
  exact_mod_cast hreal

/-! ## Canonical move data -/

/-- Canonical minimality, together with two vertices in the distinguished
part, supplies exactly the move certificate used for all `N_j` estimates. -/
noncomputable def canonicalSupercriticalMediumMoveData
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {alpha : ℝ}
    (hn : k - 1 ≤ n)
    (w : SupercriticalMediumWitness G alpha
      (canonicalSupercriticalDivision G (by simpa using hn)))
    (hpartTwo : 2 ≤
      ((canonicalSupercriticalDivision G (by simpa using hn)).parts
        w.part).card) :
    SupercriticalMediumMoveData G alpha
      (canonicalSupercriticalDivision G (by simpa using hn)) where
  witness := w
  minimal := fun E ↦
    canonicalSupercriticalDivision_minimal G (by simpa using hn) E
  main_remainder := by
    intro hv
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hv]
    omega

/-- The three uniform set-size estimates, packaged with the canonical move
certificate from which the other-part estimate is derived. -/
structure SupercriticalMediumUniformBounds
    {k n : ℕ} (hk : 3 ≤ k) (G : SimpleGraph (Fin n)) (alpha : ℝ)
    (D : SupercriticalDivision k (Fin n))
    (w : SupercriticalMediumWitness G alpha D) (q : ℝ) where
  moveData : SupercriticalMediumMoveData G alpha D
  moveData_witness : moveData.witness = w
  neighbor_lower : q ≤ ((mediumNeighborSet w).card : ℝ)
  complement_lower : q ≤ ((mediumComplementSet w).card : ℝ)
  other_lower : ∀ r : Fin (k - 2),
    q ≤ ((otherPartNonneighbors w
      (otherSupercriticalPartEquiv hk w.part r)).card : ℝ)

/-- Balanced canonical parts and the finite-size loss needed for `Z` give
the common lower bound `alpha*n/(4(k-1))` for `N`, `Z`, and every `N_j`.
The proof constructs the move data using canonical minimality. -/
noncomputable def canonicalSupercriticalMediumUniformBounds_of_abs_close
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)}
    {alpha delta : ℝ} (halpha : 0 < alpha) (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)))
    (hn : k - 1 ≤ n)
    (hnlarge : (4 * ((k - 1 : ℕ) : ℝ)) ≤ (n : ℝ))
    (halphaN : (4 * ((k - 1 : ℕ) : ℝ)) ≤ alpha * n)
    (w : SupercriticalMediumWitness G alpha
      (canonicalSupercriticalDivision G (by simpa using hn)))
    (hclose : ∀ i : Fin (k - 1),
      |(((canonicalSupercriticalDivision G (by simpa using hn)).parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n) :
    SupercriticalMediumUniformBounds hk G alpha
      (canonicalSupercriticalDivision G (by simpa using hn)) w
      (alpha * n / (4 * ((k - 1 : ℕ) : ℝ))) := by
  let D := canonicalSupercriticalDivision G (by simpa using hn)
  let q := alpha * (n : ℝ) / (4 * ((k - 1 : ℕ) : ℝ))
  have hrNat : 0 < k - 1 := by omega
  have hr : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hrNat
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hpartLower : ∀ i : Fin (k - 1),
      (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
        ((D.parts i).card : ℝ) := by
    intro i
    exact supercriticalPart_card_lower_of_abs_close hk hdelta0 hdelta
      (by simpa [D] using hclose) i
  have htwoReal : (2 : ℝ) ≤ ((D.parts w.part).card : ℝ) := by
    have havg : (2 : ℝ) ≤
        (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) := by
      apply (le_div_iff₀ (by positivity)).2
      nlinarith
    exact havg.trans (hpartLower w.part)
  have htwo : 2 ≤ (D.parts w.part).card := by exact_mod_cast htwoReal
  let C : SupercriticalMediumMoveData G alpha D := by
    simpa [D] using canonicalSupercriticalMediumMoveData hk hn w htwo
  have hCw : C.witness = w := by
    rfl
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq1 : 1 ≤ q := by
    dsimp [q]
    apply (le_div_iff₀ (by positivity)).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using halphaN
  have hdouble : alpha *
      ((n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ))) = 2 * q := by
    dsimp [q]
    field_simp
    ring
  have hNbase := (supercriticalMediumN_card_bounds w).1
  have hN : q ≤ ((mediumNeighborSet w).card : ℝ) := by
    calc
      q ≤ alpha * ((n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ))) := by
        rw [hdouble]
        linarith
      _ ≤ alpha * ((D.parts w.part).card : ℝ) :=
        mul_le_mul_of_nonneg_left (hpartLower w.part) halpha.le
      _ ≤ ((mediumNeighborSet w).card : ℝ) := hNbase
  have hZbase := supercriticalMediumZ_card_lower w
  have hZ : q ≤ ((mediumComplementSet w).card : ℝ) := by
    calc
      q ≤ alpha *
          ((n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ))) - 1 := by
        rw [hdouble]
        linarith
      _ ≤ alpha * ((D.parts w.part).card : ℝ) - 1 :=
        sub_le_sub_right
          (mul_le_mul_of_nonneg_left (hpartLower w.part) halpha.le) 1
      _ ≤ ((mediumComplementSet w).card : ℝ) := hZbase
  have hother : ∀ r : Fin (k - 2),
      q ≤ ((otherPartNonneighbors w
        (otherSupercriticalPartEquiv hk w.part r)).card : ℝ) := by
    intro r
    let j : Fin (k - 1) := otherSupercriticalPartEquiv hk w.part r
    have hbalance : (D.parts j).card ≤ 2 * (D.parts w.part).card :=
      supercriticalPart_card_le_two_mul_of_abs_close hk hdelta0 hdelta
        (by simpa [D] using hclose) w.part j
    have hj := supercriticalMediumOtherN_card_lower halpha.le C j
      (otherSupercriticalPartEquiv_ne hk w.part r) hbalance
    have hjw : (alpha / 2) * ((D.parts j).card : ℝ) ≤
        ((otherPartNonneighbors w j).card : ℝ) := by
      change (alpha / 2) * ((D.parts j).card : ℝ) ≤
        ((otherPartNonneighbors C.witness j).card : ℝ) at hj
      rw [hCw] at hj
      exact hj
    have heq : (alpha / 2) *
        ((n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ))) = q := by
      dsimp [q]
      field_simp
      ring
    calc
      q = (alpha / 2) *
          ((n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ))) := heq.symm
      _ ≤ (alpha / 2) * ((D.parts j).card : ℝ) :=
        mul_le_mul_of_nonneg_left (hpartLower j) (by positivity)
      _ ≤ ((otherPartNonneighbors w j).card : ℝ) := hjw
  exact {
    moveData := C
    moveData_witness := hCw
    neighbor_lower := by simpa [q, D] using hN
    complement_lower := by simpa [q, D] using hZ
    other_lower := by simpa [q, D] using hother }

/-! ## A real-valued form of the exact finite count -/

/-- Cast the exact natural-number deletion estimate to the reals.  The
separate branch where the deletion budget exceeds the raw product is needed
because Lean's natural subtraction is truncated. -/
theorem mediumStarCandidate_card_lower_real
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {alpha : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G alpha D) :
    ((mediumNeighborSet w).card : ℝ) *
          ((mediumComplementSet w).card : ℝ) *
          (∏ r : Fin (k - 2),
            ((otherPartNonneighbors w
              (otherSupercriticalPartEquiv hk w.part r)).card : ℝ)) -
        2 * (supercriticalDefectCost G D : ℝ) * (n : ℝ) ^ (k - 2) ≤
      ((mediumStarCandidateFinset hk w).card : ℝ) := by
  let A : ℕ := (mediumNeighborSet w).card *
    (mediumComplementSet w).card *
      ∏ r : Fin (k - 2),
        (otherPartNonneighbors w
          (otherSupercriticalPartEquiv hk w.part r)).card
  let B : ℕ := 2 * supercriticalDefectCost G D * n ^ (k - 2)
  have hcount : A - B ≤ (mediumStarCandidateFinset hk w).card := by
    simpa [A, B] using mediumStarCandidate_card_lower hk w
  by_cases hBA : B ≤ A
  · have hcast : ((A - B : ℕ) : ℝ) ≤
        ((mediumStarCandidateFinset hk w).card : ℝ) := by
      exact_mod_cast hcount
    rw [Nat.cast_sub hBA] at hcast
    simpa [A, B] using hcast
  · have hAB : (A : ℝ) - (B : ℝ) ≤ 0 := by
      have hlt : A < B := Nat.lt_of_not_ge hBA
      exact sub_nonpos.mpr (by exact_mod_cast hlt.le)
    have hzero : (0 : ℝ) ≤
        ((mediumStarCandidateFinset hk w).card : ℝ) := by positivity
    have := hAB.trans hzero
    simpa [A, B] using this

/-! ## Explicit candidate abundance -/

/-- The paper's candidate-abundance estimate with explicit finite
hypotheses.  The division is canonical, part balance is supplied in the
absolute-error form produced by close structure, and the defect-cost and
finite-size losses are stated without asymptotic notation. -/
theorem canonicalMediumStarCandidate_card_lower_rate
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)}
    {alpha delta epsilon : ℝ}
    (halpha : 0 < alpha) (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)))
    (hepsilon0 : 0 ≤ epsilon)
    (hepsilon : epsilon ≤ supercriticalMediumCandidateRate k alpha / 2)
    (hn : k - 1 ≤ n)
    (hnlarge : (4 * ((k - 1 : ℕ) : ℝ)) ≤ (n : ℝ))
    (halphaN : (4 * ((k - 1 : ℕ) : ℝ)) ≤ alpha * n)
    (w : SupercriticalMediumWitness G alpha
      (canonicalSupercriticalDivision G (by simpa using hn)))
    (hclose : ∀ i : Fin (k - 1),
      |(((canonicalSupercriticalDivision G (by simpa using hn)).parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hcost :
      (supercriticalDefectCost G
        (canonicalSupercriticalDivision G (by simpa using hn)) : ℝ) ≤
          epsilon * (n : ℝ) ^ 2) :
    supercriticalMediumCandidateRate k alpha * (n : ℝ) ^ k ≤
      ((mediumStarCandidateFinset hk w).card : ℝ) := by
  let D := canonicalSupercriticalDivision G (by simpa using hn)
  let q := alpha * (n : ℝ) / (4 * ((k - 1 : ℕ) : ℝ))
  let rate := supercriticalMediumCandidateRate k alpha
  have hrNat : 0 < k - 1 := by omega
  have hr : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hrNat
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hrate0 : 0 ≤ rate := by
    exact (supercriticalMediumCandidateRate_pos hk halpha).le
  let B : SupercriticalMediumUniformBounds hk G alpha D w q := by
    simpa [D, q] using canonicalSupercriticalMediumUniformBounds_of_abs_close
      hk halpha hdelta0 hdelta hn hnlarge halphaN w hclose
  have hprod : q ^ (k - 2) ≤
      ∏ r : Fin (k - 2),
        ((otherPartNonneighbors w
          (otherSupercriticalPartEquiv hk w.part r)).card : ℝ) := by
    calc
      q ^ (k - 2) = ∏ _r : Fin (k - 2), q := by simp
      _ ≤ ∏ r : Fin (k - 2),
          ((otherPartNonneighbors w
            (otherSupercriticalPartEquiv hk w.part r)).card : ℝ) := by
        exact Finset.prod_le_prod (fun _ _ ↦ hq0)
          (fun r _ ↦ B.other_lower r)
  have hraw : q ^ k ≤
      ((mediumNeighborSet w).card : ℝ) *
        ((mediumComplementSet w).card : ℝ) *
          (∏ r : Fin (k - 2),
            ((otherPartNonneighbors w
              (otherSupercriticalPartEquiv hk w.part r)).card : ℝ)) := by
    have hmul : q * q * q ^ (k - 2) ≤
        ((mediumNeighborSet w).card : ℝ) *
          ((mediumComplementSet w).card : ℝ) *
            (∏ r : Fin (k - 2),
              ((otherPartNonneighbors w
                (otherSupercriticalPartEquiv hk w.part r)).card : ℝ)) := by
      exact mul_le_mul
        (mul_le_mul B.neighbor_lower B.complement_lower hq0
          (by positivity)) hprod (by positivity) (by positivity)
    have hpow : q * q * q ^ (k - 2) = q ^ k := by
      calc
        q * q * q ^ (k - 2) = q ^ 2 * q ^ (k - 2) := by ring
        _ = q ^ (2 + (k - 2)) := (pow_add q 2 (k - 2)).symm
        _ = q ^ k := by congr 1 <;> omega
    rwa [hpow] at hmul
  have hqRate : q ^ k = 2 * rate * (n : ℝ) ^ k := by
    dsimp [q, rate, supercriticalMediumCandidateRate]
    rw [div_pow, mul_pow]
    field_simp
  have hnPow : (n : ℝ) ^ 2 * (n : ℝ) ^ (k - 2) =
      (n : ℝ) ^ k := by
    rw [← pow_add]
    congr 1
    omega
  have hdelete :
      2 * (supercriticalDefectCost G D : ℝ) * (n : ℝ) ^ (k - 2) ≤
        2 * epsilon * (n : ℝ) ^ k := by
    calc
      2 * (supercriticalDefectCost G D : ℝ) * (n : ℝ) ^ (k - 2) ≤
          2 * (epsilon * (n : ℝ) ^ 2) * (n : ℝ) ^ (k - 2) := by
        gcongr
      _ = 2 * epsilon * (n : ℝ) ^ k := by rw [← hnPow]; ring
  have hepsilonRate : 2 * epsilon ≤ rate := by
    dsimp [rate]
    linarith
  have hnPow0 : 0 ≤ (n : ℝ) ^ k := by positivity
  have hpay : 2 * epsilon * (n : ℝ) ^ k ≤
      rate * (n : ℝ) ^ k := by
    exact mul_le_mul_of_nonneg_right hepsilonRate hnPow0
  have hnet : rate * (n : ℝ) ^ k ≤
      q ^ k -
        2 * (supercriticalDefectCost G D : ℝ) * (n : ℝ) ^ (k - 2) := by
    rw [hqRate]
    linarith
  calc
    supercriticalMediumCandidateRate k alpha * (n : ℝ) ^ k =
        rate * (n : ℝ) ^ k := rfl
    _ ≤ q ^ k -
        2 * (supercriticalDefectCost G D : ℝ) * (n : ℝ) ^ (k - 2) := hnet
    _ ≤ ((mediumNeighborSet w).card : ℝ) *
          ((mediumComplementSet w).card : ℝ) *
          (∏ r : Fin (k - 2),
            ((otherPartNonneighbors w
              (otherSupercriticalPartEquiv hk w.part r)).card : ℝ)) -
        2 * (supercriticalDefectCost G D : ℝ) * (n : ℝ) ^ (k - 2) :=
      sub_le_sub_right hraw _
    _ ≤ ((mediumStarCandidateFinset hk w).card : ℝ) := by
      simpa [D] using mediumStarCandidate_card_lower_real hk w

/-- Transport the abundance theorem to a division supplied by downstream
refinement data together with a proof that it is the canonical division. -/
theorem mediumStarCandidate_card_lower_rate_of_canonical
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)}
    {alpha delta epsilon : ℝ}
    (halpha : 0 < alpha) (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)))
    (hepsilon0 : 0 ≤ epsilon)
    (hepsilon : epsilon ≤ supercriticalMediumCandidateRate k alpha / 2)
    (hn : k - 1 ≤ n)
    (hnlarge : (4 * ((k - 1 : ℕ) : ℝ)) ≤ (n : ℝ))
    (halphaN : (4 * ((k - 1 : ℕ) : ℝ)) ≤ alpha * n)
    {D : SupercriticalDivision k (Fin n)}
    (hcanonical : canonicalSupercriticalDivision G (by simpa using hn) = D)
    (w : SupercriticalMediumWitness G alpha D)
    (hclose : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hcost : (supercriticalDefectCost G D : ℝ) ≤
      epsilon * (n : ℝ) ^ 2) :
    supercriticalMediumCandidateRate k alpha * (n : ℝ) ^ k ≤
      ((mediumStarCandidateFinset hk w).card : ℝ) := by
  subst D
  exact canonicalMediumStarCandidate_card_lower_rate hk halpha hdelta0
    hdelta hepsilon0 hepsilon hn hnlarge halphaN w hclose hcost

end InducedStars
