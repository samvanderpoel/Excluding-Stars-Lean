import InducedStars.Structure.Critical.FineBalanceCanonicalGeometry

/-!
# Restricting the critical close radius

The fixed-sparse fine-balance comparison first chooses an auxiliary positive
cut radius and only afterwards obtains a sparse-size radius.  This file
supplies the converse piece needed for the final aggregation: after a desired
sparse-size radius is prescribed, the close-structure radius can be reduced
below any earlier auxiliary radius.  No conditional counting estimate is
transferred between the two radii.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- Given a desired sparse fraction and an auxiliary cut radius, there is a
positive smaller cut radius at which every sufficiently large graph has the
required canonical sparse bound.  We retain coarse control of every main part
for later canonical-cover arguments.

The quantifier order is the point of the statement: `sigma` and `tauCap` are
fixed before `tauFinal` is chosen. -/
theorem exists_criticalFineBalanceRestrictedCutRadius
    (k : ℕ) (hk : 3 ≤ k) (sigma tauCap : ℝ)
    (hsigma : 0 < sigma) (htauCap : 0 < tauCap) :
    ∃ tauFinal : ℝ, 0 < tauFinal ∧ tauFinal ≤ tauCap ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ (G : SimpleGraph (Fin n)) (hn : k - 1 ≤ n),
          cutDist (graphGraphon G)
              (Wstar k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)) <
                tauFinal →
            ((canonicalSupercriticalDivision G
                (by simpa using hn)).sparse.card : ℝ) ≤
                sigma * n ∧
              (∀ i : Fin (k - 1),
                |(((canonicalSupercriticalDivision G
                    (by simpa using hn)).parts i).card : ℝ) -
                    (n : ℝ) / (k - 1 : ℝ)| ≤ sigma * n) ∧
              ∀ i : Fin (k - 1),
                (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
                  ((canonicalSupercriticalDivision G
                    (by simpa using hn)).parts i).card := by
  have hkR : (0 : ℝ) < k := by
    exact_mod_cast (by omega : 0 < k)
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  let alpha : ℝ := 1 / (200 * (k : ℝ))
  have halpha : 0 < alpha := by
    dsimp [alpha]
    positivity
  have halphaUpper : alpha < 1 / (100 * (k : ℝ)) := by
    dsimp [alpha]
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  let rho := supercriticalOffDiagonal k (gammaK k)
  have hrho : 0 < rho := supercriticalOffDiagonal_pos hk le_rfl
  have hrhoOne : rho < 1 :=
    supercriticalOffDiagonal_lt_one hk (gammaK_lt_one hk)
  let delta : ℝ := min sigma
    (min (alpha / 200) (min (rho / 6) (min ((1 - rho) / 6)
      (1 / (2 * ((k - 1 : ℕ) : ℝ))))))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hsigma
      (lt_min (by positivity) (lt_min (by positivity)
        (lt_min (by positivity) (by positivity))))
  have hdeltaSigma : delta ≤ sigma := min_le_left _ _
  have hdeltaOther := min_le_right sigma
    (min (alpha / 200) (min (rho / 6) (min ((1 - rho) / 6)
      (1 / (2 * ((k - 1 : ℕ) : ℝ))))))
  change delta ≤ _ at hdeltaOther
  have hdeltaAlpha : delta < alpha / 100 := lt_of_le_of_lt
    (hdeltaOther.trans (min_le_left _ _)) (by linarith)
  have hdeltaRho := hdeltaOther.trans (min_le_right _ _)
  have hrhoLower : 3 * delta < rho := by
    have h := hdeltaRho.trans (min_le_left _ _)
    linarith
  have hdeltaLast := hdeltaRho.trans (min_le_right _ _)
  have hrhoUpper : rho + 3 * delta < 1 := by
    have h := hdeltaLast.trans (min_le_left _ _)
    linarith
  have hdeltaPart : delta ≤ 1 / (2 * ((k - 1 : ℕ) : ℝ)) :=
    hdeltaLast.trans (min_le_right _ _)
  let hgamma := gammaK_mem_supercritical_Ico k hk
  let halphaI : alpha ∈ Ioo (0 : ℝ) (1 / (100 * k : ℝ)) :=
    ⟨halpha, halphaUpper⟩
  let tauStructure := supercriticalCloseStructureCutRadius
    k hk (gammaK k) hgamma alpha halphaI delta hdelta hdeltaAlpha
      hrhoLower hrhoUpper 1 zero_lt_one
  have htauStructure : 0 < tauStructure :=
    supercriticalCloseStructureCutRadius_pos
      k hk (gammaK k) hgamma alpha halphaI delta hdelta hdeltaAlpha
        hrhoLower hrhoUpper 1 zero_lt_one
  let tauFinal := min tauCap tauStructure
  have htauFinal : 0 < tauFinal := lt_min htauCap htauStructure
  refine ⟨tauFinal, htauFinal, min_le_left _ _, ?_⟩
  filter_upwards [eventually_ge_atTop
    (supercriticalCloseStructureVertexThreshold
      k hk (gammaK k) hgamma alpha halphaI delta hdelta hdeltaAlpha
        hrhoLower hrhoUpper 1 zero_lt_one)] with n hnLarge
  intro G hn hclose
  have hcloseStructure : cutDist (graphGraphon G)
      (Wstar k hk (gammaK k) hgamma) < tauStructure :=
    hclose.trans_le (min_le_right _ _)
  obtain ⟨A⟩ := supercriticalCloseStructure
    k hk (gammaK k) hgamma alpha halphaI delta hdelta hdeltaAlpha
      hrhoLower hrhoUpper 1 zero_lt_one hnLarge G hcloseStructure
  have hnNonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hdeltaSigmaN : delta * (n : ℝ) ≤ sigma * n :=
    mul_le_mul_of_nonneg_right hdeltaSigma hnNonneg
  refine ⟨?_, ?_, ?_⟩
  · exact A.sparse_card_le.trans (by nlinarith [hdeltaSigmaN])
  · intro i
    exact (A.part_card_close i).trans hdeltaSigmaN
  · intro i
    have hpart := (abs_le.mp (A.part_card_close i)).1
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      simpa using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ k))
    rw [← hcast] at hpart
    have hsplit : (n : ℝ) / ((k - 1 : ℕ) : ℝ) =
        2 * ((n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ))) := by ring
    have hdeltaPartN :=
      mul_le_mul_of_nonneg_right hdeltaPart hnNonneg
    have heq : 1 / (2 * ((k - 1 : ℕ) : ℝ)) * (n : ℝ) =
        (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) := by ring
    rw [heq] at hdeltaPartN
    linarith [hsplit]

end InducedStars
