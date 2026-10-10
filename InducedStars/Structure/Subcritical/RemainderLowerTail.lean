import InducedStars.Structure.Subcritical.LowRemainderModels
import InducedStars.Structure.Subcritical.RemainderMatchingGain
import InducedStars.Structure.Subcritical.DistinguishedKeyDenominatorShift
import InducedStars.Structure.Subcritical.RetainedKeyCounting
import InducedStars.Asymptotics.RoughStructure

/-!
# An accuracy-independent linear lower bound for remainder edges

Paper: lemma:sub-Wstar-sparse-lower-tail-K1k. The coefficient
(1-mu)/32 is fixed before all accuracy parameters. Marked isolated
matchings absorb the exponential key count and the full-slice shift cost.
The denominator is the total exact-edge induced-free family.
-/

noncomputable section
open Filter Finset Set Topology
open scoped Classical BigOperators
namespace InducedStars

theorem subcriticalOneBlockLength_density_identity {k : ℕ} (hk : 3 ≤ k)
    {gamma : ℝ} (hg : 0 ≤ gamma) :
    gammaK k * (subcriticalOneBlockLength k gamma)^2 = gamma := by
  rw [subcriticalOneBlockLength_eq_sqrt_div_gammaK hk,
    Real.sq_sqrt (div_nonneg hg (gammaK_pos hk).le)]
  exact mul_div_cancel₀ _ (gammaK_pos hk).ne'

theorem compatibleRetainedKey_remainder_lower {k n R₀ : ℕ} (hk : 3 ≤ k)
    {gamma eta delta : ℝ} (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (heta : 0 ≤ eta) (hd : 0 ≤ delta)
    (hsize : eta + delta ≤ subcriticalOneBlockLength k gamma) (hR : k - 1 ≤ R₀)
    (hdrem : delta ≤ (1 - subcriticalOneBlockLength k gamma) / 2)
    {K : SubcriticalRetainedKey k (Fin n)}
    (hK : K ∈ compatibleRetainedKeys k n
      (subcriticalDistinguishedBlockSequence k hk gamma hgamma) eta delta R₀) :
    (1 - subcriticalOneBlockLength k gamma) / 2 * n ≤ (K.remainder.card : ℝ) := by
  obtain ⟨E, rfl, _, _, hsupport⟩ := compatibleRetainedKeys_oneBlock_geometry hk
    (subcriticalOneBlockLength_pos hk hgamma.1)
    (subcriticalOneBlockLength_lt_one hk hgamma.2).le heta hd hsize hR hK
  have hs : E.support.card ≤ n := by simpa using Finset.card_le_univ E.support
  have he : (SubcriticalRetainedKey.remainder (some E : SubcriticalRetainedKey k (Fin n))).card =
      n - E.support.card := by
    simp only [SubcriticalRetainedKey.remainder, SubcriticalRetainedKey.support,
      Option.elim_some, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin]
  rw [he, Nat.cast_sub hs]
  have h := (abs_le.mp hsupport).2
  have hh := mul_le_mul_of_nonneg_right hdrem (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  linarith

/-- The smallness requirements concern the adjustable finite hierarchy,
not the coefficient in the linear lower bound. -/
theorem eventually_subcriticalLowRemainderGraphFinset_bound
    {k R₀ : ℕ} (hk : 3 ≤ k) {gamma eta delta : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (heta : 0 < eta) (hd : 0 < delta)
    (hsize : eta + delta ≤ subcriticalOneBlockLength k gamma) (hR : k - 1 ≤ R₀)
    (hdmu : delta ≤ subcriticalOneBlockLength k gamma / 2)
    (hdrem : delta ≤ (1 - subcriticalOneBlockLength k gamma) / 2)
    (hsmall : delta ≤ (1 - pK k) *
      (subcriticalOneBlockLength k gamma / (4 * (k - 1 : ℕ)))^2 / 10)
    (hdBand : delta ≤ subcriticalReferenceShiftBand k / 2)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      ((subcriticalLowRemainderGraphFinset k n (m n)
        (subcriticalDistinguishedBlockSequence k hk gamma hgamma) eta delta R₀
        (Nat.floor (subcriticalRemainderLowerCoefficient k gamma * n))).card : ℝ) ≤
      (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) *
        ((subcriticalRemainderLowerCoefficient k gamma * n + 1) *
          Real.exp (C * n - (subcriticalRemainderLowerCoefficient k gamma / 8) * n * Real.log n)) := by
  let mu := subcriticalOneBlockLength k gamma
  let rate := subcriticalRemainderMatchingRate k gamma
  let c := subcriticalRemainderLowerCoefficient k gamma
  let shift := DenseGraph.binomialCompactBandShiftConstant (subcriticalReferenceShiftBand k)
  let keyCost := retainedKeyCountingConstant k eta R₀
  have hshift : 0 < shift := DenseGraph.binomialCompactBandShiftConstant_pos
    (subcriticalReferenceShiftBand_bounds hk).1 (subcriticalReferenceShiftBand_bounds hk).2.1
  have hmu : 0 < mu := subcriticalOneBlockLength_pos hk hgamma.1
  have hmu1 : mu ≤ 1 := (subcriticalOneBlockLength_lt_one hk hgamma.2).le
  have hm' : HasAsymptoticEdgeDensity m (gammaK k * mu^2) := by
    simpa only [mu, subcriticalOneBlockLength_density_identity hk hgamma.1.le] using hm
  refine ⟨keyCost + shift * rate, ?_⟩
  filter_upwards [eventually_compatibleRetainedKeys_denominator_shift
    (Qmax := rate) hk hmu hmu1 heta.le hd hsize hR hdmu hsmall hdBand m hm',
    eventually_subcriticalRemainderMatchingSize_lower hk hgamma,
    eventually_subcriticalRemainderMatching_gain hk hgamma] with n hden hqLower hgain
  let L := subcriticalDistinguishedBlockSequence k hk gamma hgamma
  let Ks := compatibleRetainedKeys k n L eta delta R₀
  let q := subcriticalRemainderMatchingSize k gamma n
  let B := Nat.floor (c * n)
  let N : ℝ := inducedStarFreeGraphCountWithEdges k n (m n)
  let E := shift * rate * n - (c / 8) * n * Real.log n
  have hterm : ∀ K ∈ Ks, ∀ b ∈ Finset.range (B + 1),
      (inducedStarFreeGraphCountWithEdges k K.remainder.card b : ℝ) *
        retainedKeyPartitionFunction K (m n) delta (b : ℤ) ≤ N * Real.exp E := by
    intro K hK b hb
    have hbf : (B : ℝ) ≤ c * n := Nat.floor_le (by
      have := (subcriticalRemainderLowerCoefficient_pos hk hgamma).le
      dsimp [c]; positivity)
    have hbq : b ≤ q := by
      have hh : (b : ℝ) ≤ q :=
        (show (b : ℝ) ≤ B by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)).trans
          (hbf.trans hqLower)
      exact_mod_cast hh
    have hs := four_mul_subcriticalRemainderMatchingSize_le hk hgamma
      (compatibleRetainedKey_remainder_lower hk hgamma heta.le hd.le hsize hR hdrem hK)
    have hq := subcriticalRemainderMatchingSize_cast_le hk hgamma n
    have hg := hgain (K.remainder.card - 2 * q) (by omega)
    have hh := subcriticalLowRemainderTerm_le_of_shifted_denominator hk hbq hs
      (by positivity : (0 : ℝ) ≤ retainedKeyPartitionFunction K (m n) delta (b : ℤ))
      hg (hden K hK b q hq)
    have hcost : shift * q - (c / 8) * n * Real.log n ≤ E := by
      have := mul_le_mul_of_nonneg_left hq hshift.le
      dsimp [E]
      nlinarith
    have hh' : (inducedStarFreeGraphCountWithEdges k K.remainder.card b : ℝ) *
        retainedKeyPartitionFunction K (m n) delta (b : ℤ) ≤
        N * Real.exp (shift * q - (c / 8) * n * Real.log n) := by
      simpa only [mul_comm] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcost) (by positivity))
  have hcount := card_subcriticalLowRemainderGraphFinset_le k n (m n) L eta delta R₀ B
  have hcountR : ((subcriticalLowRemainderGraphFinset k n (m n) L eta delta R₀ B).card : ℝ) ≤
      ∑ K ∈ Ks, ∑ b ∈ Finset.range (B + 1),
        (inducedStarFreeGraphCountWithEdges k K.remainder.card b : ℝ) *
          retainedKeyPartitionFunction K (m n) delta (b : ℤ) := by
    exact_mod_cast hcount
  have hsum := Finset.sum_le_sum fun K hK ↦ Finset.sum_le_sum (hterm K hK)
  have hbase : ((subcriticalLowRemainderGraphFinset k n (m n) L eta delta R₀ B).card : ℝ) ≤
      (Ks.card : ℝ) * ((B : ℝ) + 1) * (N * Real.exp E) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one, mul_assoc] using hcountR.trans hsum
  have hkeys := card_compatibleRetainedKeys_le_exp k n L heta delta R₀
  have hB : (B : ℝ) + 1 ≤ c * n + 1 := by
    have hcn : 0 ≤ c * (n : ℝ) :=
      mul_nonneg (subcriticalRemainderLowerCoefficient_pos hk hgamma).le (Nat.cast_nonneg n)
    simpa only [B, add_comm] using add_le_add_right (Nat.floor_le hcn) 1
  calc
    _ ≤ (Ks.card : ℝ) * ((B : ℝ) + 1) * (N * Real.exp E) := hbase
    _ ≤ Real.exp (keyCost * n) * (c * n + 1) * (N * Real.exp E) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hkeys hB (by positivity) (Real.exp_pos _).le)
        (by positivity)
    _ = N * ((c * n + 1) * Real.exp ((keyCost + shift * rate) * n - (c / 8) * n * Real.log n)) := by
      rw [show (keyCost + shift * rate) * n - (c / 8) * n * Real.log n = keyCost * n + E by
        dsimp [E]; ring, Real.exp_add]
      ring

/-- Paper: Lemma lemma:sub-Wstar-sparse-lower-tail-K1k, in its approved
retained-key form. The coefficient is fixed from k and gamma before
the hierarchy or structural accuracy; the original edge sequence is arbitrary. -/
theorem subcriticalRemainderLinearLowerTail
    {k R₀ : ℕ} (hk : 3 ≤ k) {gamma eta delta : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (heta : 0 < eta) (hd : 0 < delta)
    (hsize : eta + delta ≤ subcriticalOneBlockLength k gamma) (hR : k - 1 ≤ R₀)
    (hdmu : delta ≤ subcriticalOneBlockLength k gamma / 2)
    (hdrem : delta ≤ (1 - subcriticalOneBlockLength k gamma) / 2)
    (hsmall : delta ≤ (1 - pK k) *
      (subcriticalOneBlockLength k gamma / (4 * (k - 1 : ℕ)))^2 / 10)
    (hdBand : delta ≤ subcriticalReferenceShiftBand k / 2)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    Tendsto (fun n ↦ uniformSubfamilyProbability (inducedStarFreeGraphFinsetWithEdges k n (m n))
      (subcriticalLowRemainderGraphFinset k n (m n)
        (subcriticalDistinguishedBlockSequence k hk gamma hgamma) eta delta R₀
        (Nat.floor (subcriticalRemainderLowerCoefficient k gamma * n)))) atTop (𝓝 0) := by
  obtain ⟨C,hC⟩ := eventually_subcriticalLowRemainderGraphFinset_bound hk hgamma heta hd
    hsize hR hdmu hdrem hsmall hdBand m hm
  let c := subcriticalRemainderLowerCoefficient k gamma
  have hc : 0 < c := subcriticalRemainderLowerCoefficient_pos hk hgamma
  apply squeeze_zero' (g := fun n : ℕ ↦ (c * n + 1) * Real.exp (C * n - (c / 8) * n * Real.log n))
  · exact Eventually.of_forall fun n ↦ by unfold uniformSubfamilyProbability; positivity
  · filter_upwards [hC, eventually_inducedStarFreeGraphFinsetWithEdges_nonempty k hk gamma
      ⟨hgamma.1,hgamma.2.trans (gammaK_lt_one hk)⟩ m hm] with n hn hne
    have hpos : (0 : ℝ) < (inducedStarFreeGraphFinsetWithEdges k n (m n)).card := by
      exact_mod_cast Finset.card_pos.mpr hne
    unfold uniformSubfamilyProbability
    apply (div_le_iff₀ hpos).mpr
    simpa only [c, inducedStarFreeGraphCountWithEdges, inducedFreeGraphCountWithEdges,
      inducedStarFreeGraphFinsetWithEdges, mul_comm] using hn
  · exact DenseGraph.tendsto_linear_mul_exp_linear_sub_mul_log (by positivity) C c

end InducedStars
