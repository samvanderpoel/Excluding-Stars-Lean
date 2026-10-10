import InducedStars.C4.CompanionMatching
import InducedStars.C4.NondegenerateScalars
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform C4 matching-defect penalty

Paper: Lemma `lemma:c4-matching`. Actual matchings on either defect side
are paired with linear companion matchings. The polynomial loss in the
fixed-cardinality probability comparison is absorbed with a finite reserve.
-/

noncomputable section
open Finset Filter Set
open scoped Classical Topology

namespace InducedStars

theorem c4CrossPotentialEdges_card_le_sq {n : ℕ} (D : C4Division (Fin n)) :
    (c4CrossPotentialEdges D).card ≤ n ^ 2 := by
  rw [card_c4CrossPotentialEdges]
  have h := D.card_add
  simp only [Fintype.card_fin] at h
  nlinarith

theorem eventually_c4Polynomial_le_linearExp {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 + 1 ≤ Real.exp (c * n) := by
  have hlittle : (fun x : ℝ ↦ 2 * x ^ 2) =o[atTop] (fun x ↦ Real.exp (c * x)) :=
    (isLittleO_pow_exp_pos_mul_atTop 2 hc).const_mul_left 2
  have hgrowth := (hlittle.bound (c := 1) zero_lt_one).natCast_atTop
  filter_upwards [hgrowth, eventually_ge_atTop 1] with n hg hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 2 * (n : ℝ) ^ 2 ≤ Real.exp (c * n) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg] using hg
  nlinarith [sq_nonneg ((n : ℝ) - 1)]

/-- Finite matching penalty with explicit side-size, defect, quota and
polynomial-absorption hypotheses. A matching of any smaller size can be
used, rather than requiring an equality with the maximum matching number. -/
theorem c4Matching_finite_uniform_le {n : ℕ} (D : C4Division (Fin n))
    (T : SimpleGraph (Fin n)) (m q : ℕ) {beta : ℝ}
    (hbeta : 0 < beta) (hn : 4 ≤ beta * n)
    (hA : beta * n ≤ (D.independentPart.card : ℝ))
    (hB : beta * n ≤ (D.cliquePart.card : ℝ))
    (hsmall : ((finiteGraphEdges T).card : ℝ) ≤ beta ^ 2 * (n : ℝ) ^ 2 / 8)
    (hq : 1 ≤ q)
    (hmatching : q ≤ DenseGraph.matchingNumber (c4WithinGraph T D.independentPart) ∨
      q ≤ DenseGraph.matchingNumber (c4WithinGraph T D.cliquePart))
    (hquota : c4FixedDefectQuota D T m ≤ (c4CrossPotentialEdges D).card)
    (hband : beta ≤ DenseGraph.FixedCardinalityBlockModel.quotaParameter
        (c4CrossPotentialEdges D).card (c4FixedDefectQuota D T m) ∧
      DenseGraph.FixedCardinalityBlockModel.quotaParameter
        (c4CrossPotentialEdges D).card (c4FixedDefectQuota D T m) ≤ 1 - beta)
    (hpoly : (n : ℝ) ^ 2 + 1 ≤ Real.exp (beta ^ 6 / 32 * n)) :
    ((c4FixedDefectFreeFiber D T m).card : ℝ) ≤
      (Nat.choose (c4CrossPotentialEdges D).card (c4FixedDefectQuota D T m) : ℝ) *
        Real.exp (-(beta ^ 6 / 32) * q * n) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hcombine {a b : ℕ} (W : C4MatchingSides D a b) (present : Bool)
      (hstatus : W.InternalStatus T present)
      (hprod : (q : ℝ) * (beta ^ 2 * n / 16) ≤ (a : ℝ) * b) :
      ((c4FixedDefectFreeFiber D T m).card : ℝ) ≤
        (Nat.choose (c4CrossPotentialEdges D).card (c4FixedDefectQuota D T m) : ℝ) *
          Real.exp (-(beta ^ 6 / 32) * q * n) := by
    have hcap : ((c4CrossPotentialEdges D).card : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast c4CrossPotentialEdges_card_le_sq D
    have hfac : ((c4CrossPotentialEdges D).card : ℝ) + 1 ≤
        Real.exp (beta ^ 6 / 32 * q * n) := by
      apply (show ((c4CrossPotentialEdges D).card : ℝ) + 1 ≤ (n : ℝ) ^ 2 + 1 by linarith).trans
      apply hpoly.trans
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (show 0 ≤ beta ^ 6 / 32 * (n : ℝ) by positivity) (sub_nonneg.mpr hqR)]
    have hexp : beta ^ 6 / 32 * q * n - beta ^ 4 * a * b ≤
        -(beta ^ 6 / 32) * q * n := by
      have hmul := mul_le_mul_of_nonneg_left hprod (show 0 ≤ beta ^ 4 by positivity)
      nlinarith [hmul]
    have h := c4Matching_fixedDefectFiber_le W T present hstatus m hquota hbeta.le hband
    calc
      _ ≤ _ := h
      _ ≤ (Nat.choose (c4CrossPotentialEdges D).card (c4FixedDefectQuota D T m) : ℝ) *
          Real.exp (beta ^ 6 / 32 * q * n) * Real.exp (-(beta ^ 4) * a * b) := by
        gcongr
      _ = (Nat.choose (c4CrossPotentialEdges D).card (c4FixedDefectQuota D T m) : ℝ) *
          Real.exp (beta ^ 6 / 32 * q * n - beta ^ 4 * a * b) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (Nat.cast_nonneg _)
  rcases hmatching with hmatch | hmatch
  · obtain ⟨fA, hmemA, hadjA⟩ := c4_exists_orientedWithinMatching T D.independentPart q hmatch
    obtain ⟨fB, hmemB, hadjB⟩ := c4_exists_orientedMaximumWithinMatching Tᶜ D.cliquePart
    let W : C4MatchingSides D q (DenseGraph.matchingNumber (c4WithinGraph Tᶜ D.cliquePart)) :=
      ⟨fA, fB, hmemA, hmemB⟩
    refine hcombine W true ?_ ?_
    · constructor
      · intro i
        simpa [W] using (iff_true_intro (hadjA i))
      · intro i
        simpa [W] using (iff_false_intro (hadjB i).2)
    · exact mul_le_mul_of_nonneg_left
        (c4Within_complement_matchingNumber_ge T D.cliquePart hbeta hn hB hsmall)
        (Nat.cast_nonneg q)
  · obtain ⟨fA, hmemA, hadjA⟩ := c4_exists_orientedMaximumWithinMatching Tᶜ D.independentPart
    obtain ⟨fB, hmemB, hadjB⟩ := c4_exists_orientedWithinMatching T D.cliquePart q hmatch
    let W : C4MatchingSides D (DenseGraph.matchingNumber (c4WithinGraph Tᶜ D.independentPart)) q :=
      ⟨fA, fB, hmemA, hmemB⟩
    refine hcombine W false ?_ ?_
    · constructor
      · intro i
        simpa [W] using (iff_false_intro (hadjA i).2)
      · intro i
        simpa [W] using (iff_true_intro (hadjB i))
    · simpa [mul_comm] using mul_le_mul_of_nonneg_left
        (c4Within_complement_matchingNumber_ge T D.independentPart hbeta hn hA hsmall)
        (Nat.cast_nonneg q)

/-- The exact signed defect shift; it has either sign. -/
def c4MatchingSignedShift {n : ℕ} (D : C4Division (Fin n)) (T : SimpleGraph (Fin n)) : ℤ :=
  ((finiteGraphEdges (T.induce (D.independentPart : Set (Fin n)))).card : ℤ) -
    ((finiteGraphEdges (T.induce (D.cliquePart : Set (Fin n)))).card : ℤ)

theorem c4MatchingSignedShift_abs_le {n : ℕ} (D : C4Division (Fin n))
    (T : SimpleGraph (Fin n)) :
    |(c4MatchingSignedShift D T : ℝ)| ≤ (finiteGraphEdges T).card := by
  have hA := c4Within_edgeCount_le T D.independentPart
  have hB := c4Within_edgeCount_le T D.cliquePart
  rw [card_finiteGraphEdges_c4WithinGraph] at hA hB
  have hAR : ((finiteGraphEdges (T.induce (D.independentPart : Set (Fin n)))).card : ℝ) ≤
      (finiteGraphEdges T).card := by exact_mod_cast hA
  have hBR : ((finiteGraphEdges (T.induce (D.cliquePart : Set (Fin n)))).card : ℝ) ≤
      (finiteGraphEdges T).card := by exact_mod_cast hB
  dsimp [c4MatchingSignedShift]
  push_cast
  have hA0 : (0 : ℝ) ≤ (finiteGraphEdges (T.induce (D.independentPart : Set (Fin n)))).card := by positivity
  have hB0 : (0 : ℝ) ≤ (finiteGraphEdges (T.induce (D.cliquePart : Set (Fin n)))).card := by positivity
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem c4Matching_quotaBand_of_samplingBounds {n m : ℕ} (D : C4Division (Fin n))
    (T : SimpleGraph (Fin n)) {beta : ℝ}
    (h : C4NondegenerateSamplingBounds n m D.cliquePart.card 0
      (c4MatchingSignedShift D T) beta) :
    c4FixedDefectInternalCount D T ≤ m ∧
      c4FixedDefectQuota D T m ≤ (c4CrossPotentialEdges D).card ∧
      beta ≤ DenseGraph.FixedCardinalityBlockModel.quotaParameter
        (c4CrossPotentialEdges D).card (c4FixedDefectQuota D T m) ∧
      DenseGraph.FixedCardinalityBlockModel.quotaParameter
        (c4CrossPotentialEdges D).card (c4FixedDefectQuota D T m) ≤ 1 - beta := by
  have hparts := D.card_add
  simp only [Fintype.card_fin] at hparts
  have hA : D.independentPart.card = n - D.cliquePart.card := by omega
  have hcap : ((c4CrossPotentialEdges D).card : ℝ) =
      ((D.cliquePart.card * (n - D.cliquePart.card) : ℕ) : ℝ) := by
    rw [card_c4CrossPotentialEdges, hA, Nat.mul_comm]
  have hcount := c4FixedDefectInternalCount_signed D T
  have hcountR : (c4FixedDefectInternalCount D T : ℝ) +
      (finiteGraphEdges (T.induce (D.cliquePart : Set (Fin n)))).card =
      (D.cliquePart.card.choose 2 : ℝ) +
      (finiteGraphEdges (T.induce (D.independentPart : Set (Fin n)))).card := by
    exact_mod_cast hcount
  have hshift : (c4MatchingSignedShift D T : ℝ) =
      (c4FixedDefectInternalCount D T : ℝ) - (D.cliquePart.card.choose 2 : ℝ) := by
    dsimp [c4MatchingSignedShift]
    push_cast
    linarith
  have hmR : (c4FixedDefectInternalCount D T : ℝ) ≤ m := by
    have hp := h.selected_pos
    rw [hshift] at hp
    linarith
  have hm : c4FixedDefectInternalCount D T ≤ m := by exact_mod_cast hmR
  have hquotaR : (c4FixedDefectQuota D T m : ℝ) =
      (m : ℝ) - (D.cliquePart.card.choose 2 : ℝ) - (c4MatchingSignedShift D T : ℝ) := by
    rw [c4FixedDefectQuota, Nat.cast_sub hm, hshift]
    ring
  refine ⟨hm, ?_, ?_⟩
  · have hle : (c4FixedDefectQuota D T m : ℝ) ≤ (c4CrossPotentialEdges D).card := by
      rw [hquotaR, hcap]
      simpa using h.selected_lt_capacity.le
    exact_mod_cast hle
  · simpa only [DenseGraph.FixedCardinalityBlockModel.quotaParameter,
      hquotaR, hcap, Nat.cast_zero, sub_zero, Set.mem_Icc] using h.ratio_mem

/-- Paper: Lemma `lemma:c4-matching`.

The constants depend only on the limiting density and are selected before
the edge-count sequence. This bounds the full induced-C4-free fixed-defect
fiber, and hence in particular the paper's canonical-division subfamily.
The exponential uses natural units; division by `Real.log 2` converts the
constant to the paper's base-two notation. -/
theorem inducedC4MatchingPenalty {gamma : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1) :
    ∃ zeta > 0, ∃ epsilon > 0, ∃ c > 0,
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
        ∀ᶠ n in atTop, ∀ D : C4Division (Fin n),
          |(D.cliquePart.card : ℝ) / n - c4Lambda gamma| ≤ zeta →
          ∀ T : SimpleGraph (Fin n),
            ((finiteGraphEdges T).card : ℝ) ≤ epsilon * (n : ℝ) ^ 2 →
            ∀ q : ℕ, 1 ≤ q →
              (q ≤ DenseGraph.matchingNumber (c4WithinGraph T D.independentPart) ∨
                q ≤ DenseGraph.matchingNumber (c4WithinGraph T D.cliquePart)) →
              ((c4FixedDefectFreeFiber D T (m n)).card : ℝ) ≤
                (Nat.choose (c4CrossPotentialEdges D).card
                  (c4FixedDefectQuota D T (m n)) : ℝ) * Real.exp (-c * q * n) := by
  obtain ⟨zeta, hzeta, eps, heps, beta, hbeta, hhalf, hband⟩ :=
    exists_c4NondegenerateSamplingBand hgamma
  let epsilon := min eps (beta ^ 2 / 8)
  have hepsilon : 0 < epsilon := lt_min heps (by positivity)
  have hc : 0 < beta ^ 6 / 32 := by positivity
  refine ⟨zeta, hzeta, epsilon, hepsilon, beta ^ 6 / 32, hc, ?_⟩
  intro m hm
  have hlarge : ∀ᶠ n : ℕ in atTop, 4 ≤ beta * n := by
    filter_upwards [(eventually_ge_atTop (4 / beta)).natCast_atTop] with n hn
    have h := (div_le_iff₀ hbeta).mp hn
    nlinarith
  filter_upwards [hband m hm, hlarge, eventually_c4Polynomial_le_linearExp hc] with n hn hlarge hpoly
  intro D hclose T hsmall q hq hmatching
  have hparts := D.card_add
  simp only [Fintype.card_fin] at hparts
  have hb : D.cliquePart.card ≤ n := by omega
  have hshift : |(c4MatchingSignedShift D T : ℝ)| ≤ eps * (n : ℝ) ^ 2 + n := by
    have hepsR : epsilon * (n : ℝ) ^ 2 ≤ eps * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
    exact (c4MatchingSignedShift_abs_le D T).trans (by linarith)
  have hsamp := hn.2 D.cliquePart.card hb hclose (c4MatchingSignedShift D T) hshift 0 (Nat.zero_le n)
  obtain ⟨hforced, hquota, hlow, hhigh⟩ := c4Matching_quotaBand_of_samplingBounds D T hsamp
  apply c4Matching_finite_uniform_le D T (m n) q hbeta hlarge _ hsamp.clique_size.le _
    hq hmatching hquota ⟨hlow, hhigh⟩ hpoly
  · have hA : n - D.cliquePart.card = D.independentPart.card := by omega
    simpa only [hA] using hsamp.independent_size.le
  · exact hsmall.trans (by
      have hmin := mul_le_mul_of_nonneg_right (min_le_right eps (beta ^ 2 / 8))
        (sq_nonneg (n : ℝ))
      dsimp [epsilon] at *
      nlinarith)

end InducedStars
