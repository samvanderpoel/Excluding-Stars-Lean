import InducedStars.Structure.Subcritical.SeparatedKeyAlgebra
import InducedStars.Structure.Subcritical.RetainedEntropyComparisonMain
import InducedStars.Structure.Subcritical.DistinguishedDenominatorShift
import InducedStars.Structure.Subcritical.RetainedKeyCounting
import InducedStars.Structure.Subcritical.SparseMatchingTransfer

/-!
# Negligible clean-key sums for separated candidates

Paper: the counting calculation in `lemma:CompareBallsInCutMetricNlogNK1k`.
The sum is over distinct retained keys. Entropy and matching
transfers are instantiated with the actual finite-density reference, and
its shifted full slice is a concrete subset of the total exact-edge family.
-/

noncomputable section
open Finset Set Filter Topology
open scoped Classical BigOperators
namespace InducedStars

theorem compatibleRetainedKey_activeIndex_card_le {k n R₀ : ℕ}
    {eta delta : ℝ} (heta : 0 < eta) (L : AdmissibleBlockSequence k)
    {K : SubcriticalRetainedKey k (Fin n)}
    (hK : K ∈ compatibleRetainedKeys k n L eta delta R₀) :
    Fintype.card K.ActiveIndex ≤ Nat.ceil ((R₀ : ℝ)^2 / eta^2) := by
  obtain ⟨D, hD, rfl⟩ := mem_compatibleRetainedKeys.mp hK
  rw [Fintype.card_congr (retainedKeyActiveEquiv D eta R₀)]
  exact_mod_cast (card_retainedActivePair_le_uniform D R₀ heta).trans (Nat.le_ceil _)

theorem retainedKey_remainder_card_upper_of_support {k n : ℕ}
    (K : SubcriticalRetainedKey k (Fin n)) {mu gap : ℝ}
    (hK : (mu + gap / 2) * n ≤ K.support.card) :
    (K.remainder.card : ℝ) ≤ (1 - mu - gap / 2) * n := by
  have hs : K.support.card ≤ n := by simpa using Finset.card_le_univ K.support
  rw [SubcriticalRetainedKey.remainder, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, Nat.cast_sub hs]
  linarith

private theorem separatedKey_term_comparison {k n m b q : ℕ} (hk : 3 ≤ k)
    {K Kref : SubcriticalRetainedKey k (Fin n)} {delta E S : ℝ}
    (hroom : K.remainder.card + 2 * q ≤ Kref.remainder.card)
    (hentropy : (retainedKeyPartitionFunction K m delta (b : ℤ) : ℝ) ≤
      (retainedKeyPartitionFunction Kref m delta (b : ℤ) : ℝ) * Real.exp E)
    (hshift : (retainedKeyPartitionFunction Kref m delta (b : ℤ) : ℝ) *
      inducedStarFreeGraphCountWithEdges k Kref.remainder.card (b+q) ≤
      (inducedStarFreeGraphCountWithEdges k n m : ℝ) * Real.exp S) :
    (DenseGraph.labeledMatchingCoefficient (2*q) q : ℝ) *
      ((inducedStarFreeGraphCountWithEdges k K.remainder.card b : ℝ) *
        retainedKeyPartitionFunction K m delta (b : ℤ)) ≤
      (inducedStarFreeGraphCountWithEdges k n m : ℝ) * Real.exp (E + S) := by
  have htransfer : (DenseGraph.labeledMatchingCoefficient (2*q) q : ℝ) *
      inducedStarFreeGraphCountWithEdges k K.remainder.card b ≤
      inducedStarFreeGraphCountWithEdges k Kref.remainder.card (b+q) := by
    exact_mod_cast (show DenseGraph.labeledMatchingCoefficient (2*q) q *
        inducedStarFreeGraphCountWithEdges k K.remainder.card b ≤ _ by
      simpa [DenseGraph.labeledMatchingCoefficient] using subcriticalSparseMatchingTransfer hk hroom)
  have h₁ := mul_le_mul_of_nonneg_left hentropy (show 0 ≤
    (DenseGraph.labeledMatchingCoefficient (2*q) q : ℝ) *
      inducedStarFreeGraphCountWithEdges k K.remainder.card b by positivity)
  have h₂ := mul_le_mul_of_nonneg_right htransfer (show 0 ≤
    (retainedKeyPartitionFunction Kref m delta (b : ℤ) : ℝ) * Real.exp E by positivity)
  have h₃ := mul_le_mul_of_nonneg_right hshift (Real.exp_pos E).le
  calc
    _ ≤ (DenseGraph.labeledMatchingCoefficient (2*q) q : ℝ) *
        inducedStarFreeGraphCountWithEdges k K.remainder.card b *
        ((retainedKeyPartitionFunction Kref m delta (b : ℤ) : ℝ) * Real.exp E) := by
      simpa only [mul_assoc] using h₁
    _ ≤ (inducedStarFreeGraphCountWithEdges k Kref.remainder.card (b+q) : ℝ) *
        ((retainedKeyPartitionFunction Kref m delta (b : ℤ) : ℝ) * Real.exp E) := h₂
    _ ≤ (inducedStarFreeGraphCountWithEdges k n m : ℝ) * Real.exp S * Real.exp E := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using h₃
    _ = _ := by rw [Real.exp_add]; ring

/-- Actual clean-key sum bound, conditional only on the finite support gap.
The subsequent candidate theorem supplies that gap from cut separation.
All reference feasibility, entropy, transfer, and denominator estimates are
proved within this theorem's dependencies, not assumed as count bounds. -/
theorem eventually_subcriticalSeparatedCleanKeySum
    {k R₀ : ℕ} (hk : 3 ≤ k) {gamma gap eta delta : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (hgap : 0 < gap)
    (heta : 0 < eta) (hd : 0 < delta)
    (hdp : delta ≤ pK k / 2) (hdq : delta ≤ (1-pK k) / 2)
    (hbudget : 16 * (subcriticalSparseSideConstant k * eta) ≤ gamma)
    (L : AdmissibleBlockSequence k)
    (hmass : ∀ n (K : SubcriticalRetainedKey k (Fin n)),
      K ∈ compatibleRetainedKeys k n L eta delta R₀ →
      (subcriticalOneBlockLength k gamma + gap / 2) * n ≤ K.support.card)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n : ℕ in atTop,
      (∑ K ∈ compatibleRetainedKeys k n L eta delta R₀,
        (retainedKeyCleanPartitionFunction K eta (m n) delta : ℝ)) ≤
      (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) *
        Real.exp (-subcriticalSeparatedComparisonRate gap * n * Real.log n) := by
  let B := subcriticalSparseSideConstant k * eta
  have hB : 0 ≤ B := by dsimp [B, subcriticalSparseSideConstant]; positivity
  let gLower := gamma / 2
  let gUpper := (gamma + gammaK k) / 2
  have hgl : 0 < gLower := half_pos hgamma.1
  have hgu : gUpper < gammaK k := by dsimp [gUpper]; linarith [hgamma.2]
  have hband : gLower ≤ gUpper := by dsimp [gLower, gUpper]; linarith [gammaK_pos hk]
  let Q := Nat.ceil ((R₀ : ℝ)^2 / eta^2)
  obtain ⟨C, hC, hentropy⟩ := eventually_retainedKeyPartitionFunction_le_reference
    hk Q hgl hband hgu hd hdp hdq
  obtain ⟨Cshift, hCshift, hshift⟩ := eventually_subcriticalReference_denominator_shift
    hk hgl hband hgu hd hdp hdq (show 0 ≤ gap / 16 by positivity)
  let coverC := retainedKeyCountingConstant k eta R₀
  let totalC := 2*C + Cshift*gap/16 + coverC + B + 3
  filter_upwards [hentropy, hshift,
    eventually_subcriticalReferenceDensity_band hk hgamma hB hbudget m hm,
    eventually_subcriticalReference_remainder_room hk hgamma hgap hB hbudget m hm,
    eventually_separatedMatching_absorbs_linear hgap totalC,
    eventually_ge_atTop (1 : ℕ)] with n he hs hbandn hroom hgain hn
  let q := subcriticalSeparatedMatchingSize gap n
  let M := DenseGraph.labeledMatchingCoefficient (2*q) q
  let F := compatibleRetainedKeys k n L eta delta R₀
  let J := Finset.range (Nat.floor (B * (n : ℝ)^2) + 1)
  let N : ℝ := inducedStarFreeGraphCountWithEdges k n (m n)
  let termC := 2*C + Cshift*gap/16
  have hq : (q : ℝ) ≤ gap / 16 * n := by
    simpa only [mul_div_assoc, div_mul_eq_mul_div] using subcriticalSeparatedMatchingSize_le hgap.le n
  have hlog : Real.log ((n : ℝ)+1) ≤ n := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (n : ℝ)+1 by positivity)
    linarith
  have hterm (K : SubcriticalRetainedKey k (Fin n)) (hK : K ∈ F)
      (b : ℕ) (hb : b ∈ J) :
      (M : ℝ) * ((inducedStarFreeGraphCountWithEdges k K.remainder.card b : ℝ) *
        retainedKeyPartitionFunction K (m n) delta (b : ℤ)) ≤ N * Real.exp (termC*n) := by
    have hbB : (b : ℝ) ≤ B * (n : ℝ)^2 :=
      (show (b : ℝ) ≤ Nat.floor (B * (n : ℝ)^2) by
        exact_mod_cast (show b ≤ Nat.floor (B * (n : ℝ)^2) by simpa [J] using hb)).trans
        (Nat.floor_le (by positivity))
    have hg := hbandn b hbB
    have hsmall := retainedKey_remainder_card_upper_of_support K (hmass n K hK)
    have hpoint := separatedKey_term_comparison hk (hroom b K.remainder.card hbB hsmall)
      (he (m n) b hg.1 hg.2 K (compatibleRetainedKey_activeIndex_card_le heta L hK))
      (hs (m n) b q hg.1 hg.2 hq)
    apply hpoint.trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (show 0 ≤ N by positivity)
    dsimp [termC]
    nlinarith [mul_le_mul_of_nonneg_left hlog hC.le,
      mul_le_mul_of_nonneg_left hq hCshift.le]
  have hsum : (M : ℝ) * (∑ K ∈ F, (retainedKeyCleanPartitionFunction K eta (m n) delta : ℝ)) ≤
      (F.card : ℝ) * J.card * N * Real.exp (termC*n) := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ K ∈ F, (J.card : ℝ) * N * Real.exp (termC*n) := by
        apply Finset.sum_le_sum
        intro K hK
        rw [retainedKeyCleanPartitionFunction, Nat.cast_sum]
        simp only [Fintype.card_fin]
        change (M : ℝ) * (∑ b ∈ J, (_ : ℝ)) ≤ _
        rw [Finset.mul_sum]
        calc
          _ ≤ ∑ b ∈ J, N * Real.exp (termC*n) := by
            apply Finset.sum_le_sum
            intro b hb
            simpa only [Nat.cast_mul] using hterm K hK b hb
          _ = _ := by simp [mul_assoc]
      _ = _ := by simp [mul_assoc]
  have hcounts : (F.card : ℝ) * J.card * Real.exp (termC*n) ≤ Real.exp (totalC*n) := by
    have hF := card_compatibleRetainedKeys_le_exp k n L heta delta R₀
    have hJ : (J.card : ℝ) ≤ Real.exp ((B+3)*n) := by
      simpa only [J, Finset.card_range] using sparseLevelCount_le_exp hB hn
    calc
      _ ≤ Real.exp (coverC*n) * Real.exp ((B+3)*n) * Real.exp (termC*n) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hF hJ (by positivity) (by positivity)) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [totalC, termC]; ring
  have hfinal : (M : ℝ) * (∑ K ∈ F, (retainedKeyCleanPartitionFunction K eta (m n) delta : ℝ)) ≤
      (M : ℝ) * (N * Real.exp (-subcriticalSeparatedComparisonRate gap*n*Real.log n)) := by
    calc
      _ ≤ (F.card : ℝ) * J.card * N * Real.exp (termC*n) := hsum
      _ ≤ N * Real.exp (totalC*n) := by nlinarith [mul_le_mul_of_nonneg_left hcounts (show 0 ≤ N by positivity)]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hgain (show 0 ≤ N by positivity)]
  have hM : (0 : ℝ) < M := by exact_mod_cast perfectMatchingCoefficient_pos q
  exact (mul_le_mul_iff_right₀ hM).mp hfinal

end InducedStars
