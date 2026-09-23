import DenseGraph.Combinatorics.BinomialJointShift
import InducedStars.Structure.Supercritical.AggregateBounds
import InducedStars.Structure.Supercritical.JointAbsorptionGeometry
import Mathlib.Tactic

/-!
# Joint binomial absorption comparisons

This module proves the finite joint binomial comparison used in `lemma:super-Fstar`.
The capacity enlargement and selected-count reduction are deliberately
applied before either loss is estimated.  Their logarithms therefore combine
into the sharp strict-supercritical exponent.
-/

noncomputable section

namespace InducedStars

/-- The two sharp adjacent-ratio estimates combine without any asymptotic
loss.  This low-level form is shared by the clean and signed-shift wrappers. -/
theorem supercriticalJointBinomialComparison_of_bounds
    {A B L LStar : ℕ} {lambda c s n : ℝ}
    (hAB : A ≤ B) (hLA : L ≤ A) (hStarL : LStar ≤ L)
    (hLB : L ≤ B) (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (hLower : lambda * (B : ℝ) ≤ (LStar : ℝ))
    (hexponent :
      ((B - A : ℕ) : ℝ) * Real.log (1 - lambda) +
          ((L - LStar : ℕ) : ℝ) *
            (Real.log (1 - lambda) - Real.log lambda) ≤
        -(c * s * n)) :
    (Nat.choose A L : ℝ) ≤
      (Nat.choose B LStar : ℝ) * Real.exp (-(c * s * n)) := by
  have hcap := DenseGraph.choose_capacity_enlargement_sharp
    hAB hLA hlambda0 hlambda1
    (hLower.trans (by exact_mod_cast hStarL))
  have hselected := DenseGraph.choose_selected_count_reduction_sharp
    hStarL hLB hlambda0 hlambda1 hLower
  have hone : 0 < 1 - lambda := sub_pos.mpr hlambda1
  have hratio : 0 < (1 - lambda) / lambda := div_pos hone hlambda0
  have hpowCap :
      (1 - lambda) ^ (B - A) =
        Real.exp (((B - A : ℕ) : ℝ) * Real.log (1 - lambda)) := by
    rw [← Real.exp_log (pow_pos hone _), Real.log_pow]
  have hpowSelected :
      ((1 - lambda) / lambda) ^ (L - LStar) =
        Real.exp (((L - LStar : ℕ) : ℝ) *
          (Real.log (1 - lambda) - Real.log lambda)) := by
    rw [← Real.exp_log (pow_pos hratio _), Real.log_pow,
      Real.log_div hone.ne' hlambda0.ne']
  calc
    (Nat.choose A L : ℝ) ≤
        (Nat.choose B L : ℝ) * (1 - lambda) ^ (B - A) := hcap
    _ ≤ ((Nat.choose B LStar : ℝ) *
          ((1 - lambda) / lambda) ^ (L - LStar)) *
        (1 - lambda) ^ (B - A) := by
      exact mul_le_mul_of_nonneg_right hselected (by positivity)
    _ = (Nat.choose B LStar : ℝ) *
        Real.exp (
          ((B - A : ℕ) : ℝ) * Real.log (1 - lambda) +
          ((L - LStar : ℕ) : ℝ) *
            (Real.log (1 - lambda) - Real.log lambda)) := by
      rw [hpowCap, hpowSelected, Real.exp_add]
      ring
    _ ≤ (Nat.choose B LStar : ℝ) * Real.exp (-(c * s * n)) := by
      gcongr

/-- A signed change of the selected count costs only an exponential in its
integer absolute value.  `Nat.dist` makes both signs and zero uniform. -/
theorem supercriticalShiftedCombinedSlice_le_cleanSlice
    {A LShift L : ℕ} {u : ℤ} {lambda : ℝ}
    (hShiftA : LShift ≤ A) (hLA : L ≤ A)
    (hlambda0 : 0 < lambda) (hlambdaHalf : lambda < 1 / 2)
    (hLower : lambda * (A : ℝ) ≤ (L : ℝ))
    (hUpper : (L : ℝ) ≤ (1 - lambda) * (A : ℝ))
    (hdist : Nat.dist LShift L = u.natAbs) :
    (Nat.choose A LShift : ℝ) ≤
      (Nat.choose A L : ℝ) *
        Real.exp (DenseGraph.binomialCompactBandShiftConstant lambda *
          (u.natAbs : ℝ)) := by
  simpa [hdist] using
    DenseGraph.choose_le_choose_mul_exp_abs_shift_of_compact_band
      hShiftA hLA hlambda0 hlambdaHalf hLower hUpper

/-- Numerical shifted joint comparison.  It does not require an actual
zero-shift profile, only a valid reference selected count. -/
theorem supercriticalShiftedJointBinomialComparison_of_bounds
    {A B LShift L LStar : ℕ} {u : ℤ}
    {lambdaAbs lambdaShift c s n : ℝ}
    (hShiftA : LShift ≤ A) (hLA : L ≤ A)
    (hShift0 : 0 < lambdaShift) (hShiftHalf : lambdaShift < 1 / 2)
    (hBandLower : lambdaShift * (A : ℝ) ≤ (L : ℝ))
    (hBandUpper : (L : ℝ) ≤ (1 - lambdaShift) * (A : ℝ))
    (hdist : Nat.dist LShift L = u.natAbs)
    (hAB : A ≤ B) (hStarL : LStar ≤ L) (hLB : L ≤ B)
    (hlambda0 : 0 < lambdaAbs) (hlambda1 : lambdaAbs < 1)
    (hLower : lambdaAbs * (B : ℝ) ≤ (LStar : ℝ))
    (hexponent :
      ((B - A : ℕ) : ℝ) * Real.log (1 - lambdaAbs) +
          ((L - LStar : ℕ) : ℝ) *
            (Real.log (1 - lambdaAbs) - Real.log lambdaAbs) ≤
        -(c * s * n)) :
    (Nat.choose A LShift : ℝ) ≤
      (Nat.choose B LStar : ℝ) *
        Real.exp (-(c * s * n) +
          DenseGraph.binomialCompactBandShiftConstant lambdaShift *
            (u.natAbs : ℝ)) := by
  have hshift := supercriticalShiftedCombinedSlice_le_cleanSlice
    hShiftA hLA hShift0 hShiftHalf hBandLower hBandUpper hdist
  have hclean := supercriticalJointBinomialComparison_of_bounds
    hAB hLA hStarL hLB hlambda0 hlambda1 hLower hexponent
  calc
    (Nat.choose A LShift : ℝ) ≤
        (Nat.choose A L : ℝ) *
          Real.exp (DenseGraph.binomialCompactBandShiftConstant lambdaShift *
            (u.natAbs : ℝ)) := hshift
    _ ≤ ((Nat.choose B LStar : ℝ) * Real.exp (-(c * s * n))) *
          Real.exp (DenseGraph.binomialCompactBandShiftConstant lambdaShift *
            (u.natAbs : ℝ)) := by
      gcongr
    _ = (Nat.choose B LStar : ℝ) *
        Real.exp (-(c * s * n) +
          DenseGraph.binomialCompactBandShiftConstant lambdaShift *
            (u.natAbs : ℝ)) := by
      rw [Real.exp_add]
      ring

/-! ## Clean division comparison -/

/-- The repaired clean comparison acts on the entire cross-plus-sparse
binomial slice.  Both the capacity enlargement and selected-count reduction
are charged before the strict-supercritical logarithmic gap is applied. -/
theorem supercriticalCleanJointBinomialComparison
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hdelta : delta <
      supercriticalJointAbsorptionGeometryDeltaBound k gamma)
    {m t : ℕ} (D : SupercriticalDivision k (Fin n))
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hsparse : (D.sparse.card : ℝ) ≤ delta * n / 2)
    (profile : SupercriticalEdgeProfile D)
    (hprofile : SupercriticalProfileAtShift D m
      (supercriticalOffDiagonal k gamma) delta (t : ℤ) profile)
    (ht : t ≤ Nat.choose D.sparse.card 2) :
    (Nat.choose (supercriticalPreAbsorptionVariableCapacity D)
        (supercriticalCleanSelectedCount D m) : ℝ) ≤
      (Nat.choose
          (supercriticalTotalCrossCapacity
            (supercriticalAbsorbSparseDivision hk D))
          (supercriticalAbsorbedSelectedCount hk D m) : ℝ) *
        Real.exp (-(supercriticalJointAbsorptionPenalty k gamma *
          (D.sparse.card : ℝ) * n)) := by
  let A := supercriticalPreAbsorptionVariableCapacity D
  let B := supercriticalTotalCrossCapacity
    (supercriticalAbsorbSparseDivision hk D)
  let L := supercriticalCleanSelectedCount D m
  let LStar := supercriticalAbsorbedSelectedCount hk D m
  let a := (D.parts (supercriticalSmallestPartIndex hk D)).card
  let s := D.sparse.card
  let b := D.support.card - a
  let q := Nat.choose s 2
  let lambda := supercriticalAbsorptionLowerDensity k gamma
  have g := supercriticalJointAbsorptionGeometry_of_profile hk hgamma
    hdelta0 hdelta D hbalanced hsparse profile hprofile ht
  have hBA : B - A = s * b - q := by
    simpa [A, B, s, b, a, q] using
      supercriticalAbsorbedCapacity_sub_preAbsorption hk D
        g.sparseChoice_le_gain
  have hLL : L - LStar = a * s + q := by
    have h := g.absorbedSelected_add_edgeShift
    dsimp [L, LStar, supercriticalAbsorptionEdgeShift, a, s, q] at h ⊢
    omega
  have habNat : a + b = n - s := by
    have hpartition := D.card_support_add_card_sparse
    simp only [Fintype.card_fin] at hpartition
    have ha : a ≤ D.support.card := by
      dsimp [a]
      exact Finset.card_le_card
        (D.part_subset_support (supercriticalSmallestPartIndex hk D))
    dsimp [b, s]
    omega
  have habReal : (a : ℝ) + (b : ℝ) = (n : ℝ) - (s : ℝ) := by
    have hsle : s ≤ n := by
      have hpartition := D.card_support_add_card_sparse
      simp only [Fintype.card_fin] at hpartition
      dsimp [s]
      omega
    rw [← Nat.cast_add, ← Nat.cast_sub hsle]
    exact_mod_cast habNat
  have hbalanceA :
      |(a : ℝ) - (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤
        delta * n := by
    simpa [a] using hbalanced (supercriticalSmallestPartIndex hk D)
  have hqReal : (q : ℝ) ≤ (s : ℝ) ^ 2 / 2 := by
    dsimp [q]
    rw [Nat.cast_choose_two]
    nlinarith
  have hdeltaScalar :
      delta ≤ supercriticalJointAbsorptionDeltaBound k gamma :=
    hdelta.le.trans
      (supercriticalJointAbsorptionGeometryDeltaBound_le_scalar k gamma)
  have hexponentReal := supercriticalJointAbsorptionRatioExponent_le
    hk hgamma hdelta0 hdeltaScalar (by positivity : (0 : ℝ) ≤ n)
      (by positivity : (0 : ℝ) ≤ s) habReal hbalanceA
      (by simpa [s] using hsparse) hqReal
  have hqle : q ≤ s * b := by
    simpa [q, s, b, a] using g.sparseChoice_le_gain
  have hexponent :
      ((B - A : ℕ) : ℝ) * Real.log (1 - lambda) +
          ((L - LStar : ℕ) : ℝ) *
            (Real.log (1 - lambda) - Real.log lambda) ≤
        -(supercriticalJointAbsorptionPenalty k gamma *
          (s : ℝ) * n) := by
    rw [hBA, hLL, Nat.cast_sub hqle]
    push_cast
    simpa [lambda] using hexponentReal
  exact supercriticalJointBinomialComparison_of_bounds
    g.preAbsorption_le_absorbed g.cleanSelected_le_preAbsorption
      g.absorbedSelected_le_clean g.cleanSelected_le_absorbed
      (supercriticalAbsorptionLowerDensity_pos hk hgamma)
      (supercriticalAbsorptionLowerDensity_lt_one hk hgamma)
      g.absorbedDensity_lower hexponent

/-! ## Signed support shifts -/

/-- Two exact integer edge equations turn a signed support shift into the
natural-number distance between their selected counts. -/
theorem supercriticalShiftedSelectedCount_dist
    {LShift L internal m : ℕ} {u : ℤ}
    (hshift : (LShift : ℤ) + (internal : ℤ) + u = (m : ℤ))
    (hclean : (L : ℤ) + (internal : ℤ) = (m : ℤ)) :
    Nat.dist LShift L = u.natAbs := by
  have hu : (L : ℤ) - (LShift : ℤ) = u := by omega
  rcases le_total LShift L with hle | hle
  · rw [Nat.dist_eq_sub_of_le hle]
    have hu0 : 0 ≤ u := by omega
    have huabs : (u.natAbs : ℤ) = u := Int.natAbs_of_nonneg hu0
    exact_mod_cast hu.trans huabs.symm
  · rw [Nat.dist_eq_sub_of_le_right hle]
    have hu0 : u ≤ 0 := by omega
    have huabs : (u.natAbs : ℤ) = -u := Int.ofNat_natAbs_of_nonpos hu0
    rw [← Int.ofNat_inj]
    rw [Int.ofNat_sub hle]
    omega

/-- The profile-free shifted comparison used by the later fixed-defect
aggregation.  `LShift` is tied to the signed shift numerically; no actual
zero-shift profile is assumed.  The explicit validity and compact-band
hypotheses are precisely the data the later aggregation will supply. -/
theorem supercriticalShiftedJointBinomialComparison
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ supercriticalJointAbsorptionDeltaBound k gamma)
    {m LShift : ℕ} (D : SupercriticalDivision k (Fin n)) {u : ℤ}
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hsparse : (D.sparse.card : ℝ) ≤ delta * n / 2)
    (hcapacity : Nat.choose D.sparse.card 2 ≤
      D.sparse.card *
        (D.support.card -
          (D.parts (supercriticalSmallestPartIndex hk D)).card))
    (habsorbedInternal :
      divisionInternalCliqueCapacity
        (supercriticalAbsorbSparseDivision hk D) ≤ m)
    (hShiftValid : LShift ≤ supercriticalPreAbsorptionVariableCapacity D)
    (hCleanValid : supercriticalCleanSelectedCount D m ≤
      supercriticalPreAbsorptionVariableCapacity D)
    (hAbsorbedValid : supercriticalAbsorbedSelectedCount hk D m ≤
      supercriticalTotalCrossCapacity
        (supercriticalAbsorbSparseDivision hk D))
    (hAbsorbedLower :
      supercriticalAbsorptionLowerDensity k gamma *
          (supercriticalTotalCrossCapacity
            (supercriticalAbsorbSparseDivision hk D) : ℝ) ≤
        (supercriticalAbsorbedSelectedCount hk D m : ℝ))
    (hBandLower :
      supercriticalShiftBandDensity k gamma *
          (supercriticalPreAbsorptionVariableCapacity D : ℝ) ≤
        (supercriticalCleanSelectedCount D m : ℝ))
    (hBandUpper :
      (supercriticalCleanSelectedCount D m : ℝ) ≤
        (1 - supercriticalShiftBandDensity k gamma) *
          (supercriticalPreAbsorptionVariableCapacity D : ℝ))
    (hdist : Nat.dist LShift (supercriticalCleanSelectedCount D m) =
      u.natAbs) :
    (Nat.choose (supercriticalPreAbsorptionVariableCapacity D) LShift : ℝ) ≤
      (Nat.choose
          (supercriticalTotalCrossCapacity
            (supercriticalAbsorbSparseDivision hk D))
          (supercriticalAbsorbedSelectedCount hk D m) : ℝ) *
        Real.exp (-(supercriticalJointAbsorptionPenalty k gamma *
            (D.sparse.card : ℝ) * n) +
          supercriticalJointShiftConstant k gamma * (u.natAbs : ℝ)) := by
  let A := supercriticalPreAbsorptionVariableCapacity D
  let B := supercriticalTotalCrossCapacity
    (supercriticalAbsorbSparseDivision hk D)
  let L := supercriticalCleanSelectedCount D m
  let LStar := supercriticalAbsorbedSelectedCount hk D m
  let a := (D.parts (supercriticalSmallestPartIndex hk D)).card
  let s := D.sparse.card
  let b := D.support.card - a
  let q := Nat.choose s 2
  have hAB : A ≤ B := by
    have hB := supercriticalTotalCrossCapacity_absorbSparse_eq hk D
    dsimp [A, B, supercriticalPreAbsorptionVariableCapacity,
      supercriticalSparsePotentialCapacity, a, s, b, q] at hB ⊢
    omega
  have hInternal :=
    divisionInternalCliqueCapacity_absorbSparse_eq_add_shift hk D
  have hInternalLe :
      divisionInternalCliqueCapacity D +
          supercriticalAbsorptionEdgeShift hk D ≤ m := by
    rw [← hInternal]
    exact habsorbedInternal
  have hShiftLe :
      supercriticalAbsorptionEdgeShift hk D ≤
        m - divisionInternalCliqueCapacity D :=
    Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hInternalLe)
  have hStarAdd : LStar + a * s + q = L := by
    dsimp [LStar, supercriticalAbsorbedSelectedCount,
      L, supercriticalCleanSelectedCount, a, s, q]
    rw [hInternal, tsub_add_eq_tsub_tsub]
    simpa [supercriticalAbsorptionEdgeShift, Nat.add_assoc] using
      Nat.sub_add_cancel hShiftLe
  have hStarL : LStar ≤ L := by omega
  have hBA : B - A = s * b - q := by
    simpa [A, B, s, b, a, q] using
      supercriticalAbsorbedCapacity_sub_preAbsorption hk D hcapacity
  have hLL : L - LStar = a * s + q := by omega
  have habNat : a + b = n - s := by
    have hpartition := D.card_support_add_card_sparse
    simp only [Fintype.card_fin] at hpartition
    have ha : a ≤ D.support.card := by
      dsimp [a]
      exact Finset.card_le_card
        (D.part_subset_support (supercriticalSmallestPartIndex hk D))
    dsimp [b, s]
    omega
  have habReal : (a : ℝ) + (b : ℝ) = (n : ℝ) - (s : ℝ) := by
    have hsle : s ≤ n := by
      have hpartition := D.card_support_add_card_sparse
      simp only [Fintype.card_fin] at hpartition
      dsimp [s]
      omega
    rw [← Nat.cast_add, ← Nat.cast_sub hsle]
    exact_mod_cast habNat
  have hbalanceA :
      |(a : ℝ) - (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤
        delta * n := by
    simpa [a] using hbalanced (supercriticalSmallestPartIndex hk D)
  have hqReal : (q : ℝ) ≤ (s : ℝ) ^ 2 / 2 := by
    dsimp [q]
    rw [Nat.cast_choose_two]
    nlinarith
  have hexponentReal := supercriticalJointAbsorptionRatioExponent_le
    hk hgamma hdelta0 hdelta (by positivity : (0 : ℝ) ≤ n)
      (by positivity : (0 : ℝ) ≤ s) habReal hbalanceA
      (by simpa [s] using hsparse) hqReal
  have hqle : q ≤ s * b := by
    simpa [q, s, b, a] using hcapacity
  have hexponent :
      ((B - A : ℕ) : ℝ) *
          Real.log (1 - supercriticalAbsorptionLowerDensity k gamma) +
        ((L - LStar : ℕ) : ℝ) *
          (Real.log (1 - supercriticalAbsorptionLowerDensity k gamma) -
            Real.log (supercriticalAbsorptionLowerDensity k gamma)) ≤
        -(supercriticalJointAbsorptionPenalty k gamma *
          (s : ℝ) * n) := by
    rw [hBA, hLL, Nat.cast_sub hqle]
    push_cast
    simpa [neg_mul] using hexponentReal
  have hcompare := supercriticalShiftedJointBinomialComparison_of_bounds
    hShiftValid hCleanValid
    (supercriticalShiftBandDensity_pos hk hgamma)
    (supercriticalShiftBandDensity_lt_half hk hgamma)
    hBandLower hBandUpper hdist hAB hStarL (hCleanValid.trans hAB)
    (supercriticalAbsorptionLowerDensity_pos hk hgamma)
    (supercriticalAbsorptionLowerDensity_lt_one hk hgamma)
    hAbsorbedLower hexponent
  simpa [A, B, L, LStar, s, supercriticalJointShiftConstant] using hcompare

/-! ## Cardinality-level repair theorems -/

/-- The complete clean family for one fixed division is exponentially smaller
than the exact-edge co-multipartite fiber for the absorbed division.  The
right-hand family uses the displayed absorbed cover only; it imposes no
canonicality or uniqueness condition. -/
theorem card_supercriticalCleanDivisionGraphFinset_le_absorbedCoPartite
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hdelta : delta <
      supercriticalJointAbsorptionGeometryDeltaBound k gamma)
    {m t : ℕ} (D : SupercriticalDivision k (Fin n))
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hsparse : (D.sparse.card : ℝ) ≤ delta * n / 2)
    (profile : SupercriticalEdgeProfile D)
    (hprofile : SupercriticalProfileAtShift D m
      (supercriticalOffDiagonal k gamma) delta (t : ℤ) profile)
    (ht : t ≤ Nat.choose D.sparse.card 2)
    {tau : ℝ} (hn : k - 1 ≤ n) :
    ((supercriticalCleanDivisionGraphFinset
        k hk gamma ⟨hgamma.1.le, hgamma.2⟩ m n tau hn D).card : ℝ) ≤
      (supercriticalAbsorbedCoPartiteGraphFinset hk D m).card *
        Real.exp (-(supercriticalJointAbsorptionPenalty k gamma *
          (D.sparse.card : ℝ) * n)) := by
  have g := supercriticalJointAbsorptionGeometry_of_profile hk hgamma
    hdelta0 hdelta D hbalanced hsparse profile hprofile ht
  have hcleanNat := card_supercriticalCleanDivisionGraphFinset_le_preAbsorptionChoose
    (hk := hk) (hgamma := ⟨hgamma.1.le, hgamma.2⟩)
      (m := m) (n := n) (tau := tau) (hn := hn) D
  have hcleanReal :
      ((supercriticalCleanDivisionGraphFinset
          k hk gamma ⟨hgamma.1.le, hgamma.2⟩ m n tau hn D).card : ℝ) ≤
        (Nat.choose (supercriticalPreAbsorptionVariableCapacity D)
          (supercriticalCleanSelectedCount D m) : ℝ) := by
    simpa [supercriticalCleanSelectedCount] using
      (show
        ((supercriticalCleanDivisionGraphFinset
            k hk gamma ⟨hgamma.1.le, hgamma.2⟩ m n tau hn D).card : ℝ) ≤
          (Nat.choose (supercriticalPreAbsorptionVariableCapacity D)
            (m - divisionInternalCliqueCapacity D) : ℝ) by
        exact_mod_cast hcleanNat)
  have hcompare := supercriticalCleanJointBinomialComparison hk hgamma
    hdelta0 hdelta D hbalanced hsparse profile hprofile ht
  have hfiber := card_supercriticalAbsorbedCoPartiteGraphFinset
    hk D m g.absorbedInternal_le_m
  calc
    ((supercriticalCleanDivisionGraphFinset
        k hk gamma ⟨hgamma.1.le, hgamma.2⟩ m n tau hn D).card : ℝ) ≤
        (Nat.choose (supercriticalPreAbsorptionVariableCapacity D)
          (supercriticalCleanSelectedCount D m) : ℝ) := hcleanReal
    _ ≤ (Nat.choose
          (supercriticalTotalCrossCapacity
            (supercriticalAbsorbSparseDivision hk D))
          (supercriticalAbsorbedSelectedCount hk D m) : ℝ) *
        Real.exp (-(supercriticalJointAbsorptionPenalty k gamma *
          (D.sparse.card : ℝ) * n)) := hcompare
    _ = (supercriticalAbsorbedCoPartiteGraphFinset hk D m).card *
        Real.exp (-(supercriticalJointAbsorptionPenalty k gamma *
          (D.sparse.card : ℝ) * n)) := by
      rw [hfiber]
      rfl

/-- The shifted profile aggregate is controlled by the same absorbed fiber,
with exactly the compact-band exponential cost in the absolute integer shift.
This is the numerical interface reserved for the later nonclean aggregation. -/
theorem supercriticalShiftedProfileAggregate_le_absorbedCoPartite
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    {rho delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ supercriticalJointAbsorptionDeltaBound k gamma)
    {m LShift : ℕ} (D : SupercriticalDivision k (Fin n)) {u : ℤ}
    (haggregate : (LShift : ℤ) +
      (divisionInternalCliqueCapacity D : ℤ) + u = (m : ℤ))
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hsparse : (D.sparse.card : ℝ) ≤ delta * n / 2)
    (hcapacity : Nat.choose D.sparse.card 2 ≤
      D.sparse.card *
        (D.support.card -
          (D.parts (supercriticalSmallestPartIndex hk D)).card))
    (habsorbedInternal :
      divisionInternalCliqueCapacity
        (supercriticalAbsorbSparseDivision hk D) ≤ m)
    (hShiftValid : LShift ≤ supercriticalPreAbsorptionVariableCapacity D)
    (hCleanValid : supercriticalCleanSelectedCount D m ≤
      supercriticalPreAbsorptionVariableCapacity D)
    (hAbsorbedValid : supercriticalAbsorbedSelectedCount hk D m ≤
      supercriticalTotalCrossCapacity
        (supercriticalAbsorbSparseDivision hk D))
    (hAbsorbedLower :
      supercriticalAbsorptionLowerDensity k gamma *
          (supercriticalTotalCrossCapacity
            (supercriticalAbsorbSparseDivision hk D) : ℝ) ≤
        (supercriticalAbsorbedSelectedCount hk D m : ℝ))
    (hBandLower :
      supercriticalShiftBandDensity k gamma *
          (supercriticalPreAbsorptionVariableCapacity D : ℝ) ≤
        (supercriticalCleanSelectedCount D m : ℝ))
    (hBandUpper :
      (supercriticalCleanSelectedCount D m : ℝ) ≤
        (1 - supercriticalShiftBandDensity k gamma) *
          (supercriticalPreAbsorptionVariableCapacity D : ℝ))
    (hdist : Nat.dist LShift (supercriticalCleanSelectedCount D m) =
      u.natAbs) :
    (supercriticalShiftedProfileAggregate D m rho delta u : ℝ) ≤
      (supercriticalAbsorbedCoPartiteGraphFinset hk D m).card *
        Real.exp (-(supercriticalJointAbsorptionPenalty k gamma *
            (D.sparse.card : ℝ) * n) +
          supercriticalJointShiftConstant k gamma * (u.natAbs : ℝ)) := by
  have haggregateNat := supercriticalShiftedProfileAggregate_le_choose
    D m LShift rho delta u haggregate
  have haggregateReal :
      (supercriticalShiftedProfileAggregate D m rho delta u : ℝ) ≤
        (Nat.choose (supercriticalPreAbsorptionVariableCapacity D) LShift : ℝ) := by
    exact_mod_cast haggregateNat
  have hcompare := supercriticalShiftedJointBinomialComparison hk hgamma
    hdelta0 hdelta D hbalanced hsparse hcapacity habsorbedInternal
      hShiftValid hCleanValid hAbsorbedValid hAbsorbedLower
      hBandLower hBandUpper hdist
  have hfiber := card_supercriticalAbsorbedCoPartiteGraphFinset
    hk D m habsorbedInternal
  calc
    (supercriticalShiftedProfileAggregate D m rho delta u : ℝ) ≤
        (Nat.choose (supercriticalPreAbsorptionVariableCapacity D) LShift : ℝ) :=
      haggregateReal
    _ ≤ (Nat.choose
          (supercriticalTotalCrossCapacity
            (supercriticalAbsorbSparseDivision hk D))
          (supercriticalAbsorbedSelectedCount hk D m) : ℝ) *
        Real.exp (-(supercriticalJointAbsorptionPenalty k gamma *
            (D.sparse.card : ℝ) * n) +
          supercriticalJointShiftConstant k gamma * (u.natAbs : ℝ)) := hcompare
    _ = (supercriticalAbsorbedCoPartiteGraphFinset hk D m).card *
        Real.exp (-(supercriticalJointAbsorptionPenalty k gamma *
            (D.sparse.card : ℝ) * n) +
          supercriticalJointShiftConstant k gamma * (u.natAbs : ℝ)) := by
      rw [hfiber]
      rfl

end InducedStars
