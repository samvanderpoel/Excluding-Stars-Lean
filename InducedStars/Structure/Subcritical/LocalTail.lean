import InducedStars.Structure.Subcritical.ProfileEventSupport
import InducedStars.Structure.Subcritical.LocalTailCoordinates
import InducedStars.Structure.Subcritical.LocalNonlow
import InducedStars.Structure.Subcritical.LocalEntropy
import DenseGraph.FiniteModels.BernoulliTail

/-!
# Explicit local tail losses

Paper: Claim `claim:local-tail-estimate-K1k`.
Every logarithm is natural. Lower tails retain the full-size
threshold and an explicit loss for the deleted roots. The finite zero
probability convention is controlled separately, without a positivity
assumption on an event or a quota window.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Finset Set
open scoped BigOperators Classical
open DenseGraph.FiniteBernoulliProduct

namespace InducedStars

/-- Uniform logarithmic loss on the two one-sided narrow density bands. -/
def subcriticalTailLogConstant (k : ℕ) : ℝ := 1 / pK k + 1 / (1 - pK k)

/-- Tail loss before comparing two main-part sizes. -/
def subcriticalTailBaseErrorNat (k : ℕ) (alpha delta xi : ℝ) : ℝ :=
  Real.binEntropy (2 * alpha / (1 - xi)) +
    (xi + 2 * alpha) * subcriticalLocalU_Nat k + subcriticalTailLogConstant k * delta

/-- Tail loss including the relative same-component size error `zeta`. -/
def subcriticalTailErrorNat (k : ℕ) (alpha delta xi zeta : ℝ) : ℝ :=
  subcriticalLocalU_Nat k * zeta +
    subcriticalTailBaseErrorNat k alpha delta xi * (1 + zeta)

theorem subcriticalTailLogConstant_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < subcriticalTailLogConstant k := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hp1 := pK_lt_one (show 2 ≤ k by omega)
  unfold subcriticalTailLogConstant
  positivity

theorem subcriticalTailBaseErrorNat_nonneg {k : ℕ} (hk : 3 ≤ k)
    {alpha delta xi : ℝ} (ha : 0 ≤ alpha) (hd : 0 ≤ delta)
    (hxi : 0 ≤ xi) (hxi1 : xi < 1) (hband : 2 * alpha / (1 - xi) ≤ 1 / 2) :
    0 ≤ subcriticalTailBaseErrorNat k alpha delta xi := by
  have hden : 0 < 1 - xi := by linarith
  have hh := Real.binEntropy_nonneg (div_nonneg (by linarith : 0 ≤ 2 * alpha) hden.le)
    (show 2 * alpha / (1 - xi) ≤ 1 by linarith)
  have hU := (subcriticalLocalU_Nat_pos hk).le
  have hC := (subcriticalTailLogConstant_pos hk).le
  unfold subcriticalTailBaseErrorNat
  positivity

theorem subcriticalTailErrorNat_nonneg {k : ℕ} (hk : 3 ≤ k)
    {alpha delta xi zeta : ℝ} (ha : 0 ≤ alpha) (hd : 0 ≤ delta)
    (hxi : 0 ≤ xi) (hxi1 : xi < 1) (hband : 2 * alpha / (1 - xi) ≤ 1 / 2)
    (hz : 0 ≤ zeta) : 0 ≤ subcriticalTailErrorNat k alpha delta xi zeta := by
  have hE := subcriticalTailBaseErrorNat_nonneg hk ha hd hxi hxi1 hband
  have hU := (subcriticalLocalU_Nat_pos hk).le
  unfold subcriticalTailErrorNat
  positivity

/-- The upper and lower extreme log probabilities each lose at most the
same explicit linear amount in the narrow-window width. -/
theorem subcriticalTail_log_losses {k : ℕ} (hk : 3 ≤ k) {delta : ℝ}
    (hd : 0 ≤ delta) :
    Real.log (pK k + delta) - Real.log (pK k) ≤ subcriticalTailLogConstant k * delta ∧
    Real.log (1 - pK k + delta) - Real.log (1 - pK k) ≤
      subcriticalTailLogConstant k * delta := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hp1 := pK_lt_one (show 2 ≤ k by omega)
  have hq : 0 < 1 - pK k := by linarith
  have hu := DenseGraph.abs_log_sub_log_le_div_of_lower hp
    (show pK k ≤ pK k + delta by linarith) le_rfl
  have hl := DenseGraph.abs_log_sub_log_le_div_of_lower hq
    (show 1 - pK k ≤ 1 - pK k + delta by linarith) le_rfl
  rw [add_sub_cancel_left, abs_of_nonneg hd] at hu hl
  have hdu : 0 ≤ delta / pK k := div_nonneg hd hp.le
  have hdl : 0 ≤ delta / (1 - pK k) := div_nonneg hd hq.le
  have he : subcriticalTailLogConstant k * delta =
      delta / pK k + delta / (1 - pK k) := by
    unfold subcriticalTailLogConstant
    ring
  constructor
  · exact (le_abs_self _).trans (hu.trans (by rw [he]; linarith))
  · exact (le_abs_self _).trans (hl.trans (by rw [he]; linarith))

/-- Uniform natural negative-log bounds for an arbitrary density in the
narrow interval. Compactness proves both logarithm arguments positive. -/
theorem subcriticalTail_negLog_bounds_of_narrow {k : ℕ} (hk : 3 ≤ k)
    {delta q : ℝ} (hd : 0 ≤ delta)
    (hdp : 2 * delta ≤ pK k) (hdq : 2 * delta ≤ 1 - pK k)
    (hq : q ∈ Icc (pK k - delta) (pK k + delta)) :
    subcriticalLocalU_Nat k - subcriticalTailLogConstant k * delta ≤ -Real.log q ∧
    subcriticalLocalA_Nat k - subcriticalTailLogConstant k * delta ≤ -Real.log (1 - q) := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hp1 := pK_lt_one (show 2 ≤ k by omega)
  have hq0 : 0 < q := by linarith [hq.1]
  have hq1 : 0 < 1 - q := by linarith [hq.2]
  have hu := Real.log_le_log hq0 hq.2
  have hl := Real.log_le_log hq1 (show 1 - q ≤ 1 - pK k + delta by linarith [hq.1])
  obtain ⟨hlu, hll⟩ := subcriticalTail_log_losses hk hd
  unfold subcriticalLocalU_Nat subcriticalLocalA_Nat
  constructor <;> linarith

private theorem tail_entropy_radius {alpha xi : ℝ} (ha : 0 ≤ alpha)
    (hxi : 0 ≤ xi) (hxi1 : xi < 1) (hband : 2 * alpha / (1 - xi) ≤ 1 / 2) :
    2 * alpha ≤ 1 / 2 ∧
      Real.binEntropy (2 * alpha) ≤ Real.binEntropy (2 * alpha / (1 - xi)) := by
  have hden : 0 < 1 - xi := by linarith
  have hr : 2 * alpha ≤ 2 * alpha / (1 - xi) :=
    (le_div_iff₀ hden).mpr (by nlinarith)
  refine ⟨hr.trans hband, ?_⟩
  apply Real.binEntropy_strictMonoOn.monotoneOn
    ⟨by linarith, by norm_num; linarith [hr.trans hband]⟩
    ⟨div_nonneg (by linarith) hden.le, by norm_num; linarith⟩ hr

/-- Uniform coefficient estimate for the full-target upper tail. -/
theorem subcriticalTail_upper_coefficient_le {k : ℕ} (hk : 3 ≤ k)
    {alpha delta xi : ℝ} (ha : 0 ≤ alpha) (hd : 0 ≤ delta)
    (hxi : 0 ≤ xi) (hxi1 : xi < 1) (hband : 2 * alpha / (1 - xi) ≤ 1 / 2) :
    Real.binEntropy (2 * alpha) + (1 - 2 * alpha) * Real.log (pK k + delta) ≤
      subcriticalTailBaseErrorNat k alpha delta xi - subcriticalLocalU_Nat k := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hlog := Real.log_le_log hp (show pK k ≤ pK k + delta by linarith)
  have hu := (subcriticalTail_log_losses hk hd).1
  have hh := (tail_entropy_radius ha hxi hxi1 hband).2
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * alpha by linarith)
  have hxU := mul_nonneg hxi (subcriticalLocalU_Nat_pos hk).le
  unfold subcriticalTailBaseErrorNat subcriticalLocalU_Nat at hxU ⊢
  nlinarith

/-- Uniform coefficient estimate for the lower tail after deleting roots. -/
theorem subcriticalTail_lower_coefficient_le {k : ℕ} (hk : 3 ≤ k)
    {alpha delta xi : ℝ} (ha : 0 ≤ alpha) (hd : 0 ≤ delta) (hxi : 0 ≤ xi) :
    Real.binEntropy (2 * alpha / (1 - xi)) +
      (1 - xi - 2 * alpha) * Real.log (1 - pK k + delta) ≤
      subcriticalTailBaseErrorNat k alpha delta xi - subcriticalLocalA_Nat k := by
  have hp1 := pK_lt_one (show 2 ≤ k by omega)
  have hlog := Real.log_le_log (show 0 < 1 - pK k by linarith)
    (show 1 - pK k ≤ 1 - pK k + delta by linarith)
  have hl := (subcriticalTail_log_losses hk hd).2
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ xi + 2 * alpha by linarith)
  have hUA : subcriticalLocalA_Nat k ≤ subcriticalLocalU_Nat k := by
    rw [subcriticalLocalU_Nat_eq_L_add_A hk]
    linarith [subcriticalLogOddsNat_pos hk]
  have hscale := mul_le_mul_of_nonneg_left hUA (show 0 ≤ xi + 2 * alpha by linarith)
  unfold subcriticalTailBaseErrorNat subcriticalLocalA_Nat at hscale ⊢
  nlinarith

/-- A size comparison transports either positive tail coefficient to the
own-part scale. No positivity of the error-subtracted coefficient is needed. -/
theorem subcriticalTail_scale_loss {k : ℕ} {alpha delta xi zeta N Y c : ℝ}
    (hE : 0 ≤ subcriticalTailBaseErrorNat k alpha delta xi)
    (hc : 0 ≤ c) (hcU : c ≤ subcriticalLocalU_Nat k) (hz : 0 ≤ zeta)
    (hN : 0 ≤ N) (hsize : |Y - N| ≤ zeta * N) :
    (subcriticalTailBaseErrorNat k alpha delta xi - c) * Y ≤
      (subcriticalTailErrorNat k alpha delta xi zeta - c) * N := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hsize
  have h1 := mul_le_mul_of_nonneg_left (show Y ≤ (1 + zeta) * N by linarith) hE
  have h2 := mul_le_mul_of_nonneg_left (show N - zeta * N ≤ Y by linarith) hc
  have h3 := mul_le_mul_of_nonneg_right hcU (mul_nonneg hz hN)
  unfold subcriticalTailErrorNat
  nlinarith

/-- Safe negative-log reversal, including probability zero. The only extra
reserve is the explicit domination of the finite cubic zero sentinel. -/
theorem subcriticalNegLogProbability_ge_of_le_exp
    (n : ℕ) {probability B : ℝ} (hp : 0 ≤ probability)
    (hbound : probability ≤ Real.exp (-B)) (hsentinel : B ≤ (n + 1 : ℝ) ^ 3) :
    B ≤ subcriticalNegLogProbability n probability := by
  unfold subcriticalNegLogProbability
  split_ifs with hzero
  · exact hsentinel
  · have hp0 : 0 < probability := lt_of_le_of_ne hp (Ne.symm hzero)
    have h := Real.log_le_log hp0 hbound
    rw [Real.log_exp] at h
    linarith

/-- Finite upper-tail estimate at the actual source-part scale. Coordinate
probabilities need only lie below the upper edge of the narrow band. -/
theorem subcriticalTail_upper_probability_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {k : ℕ} (hk : 3 ≤ k) (P : DenseGraph.FiniteBernoulliProduct Ω)
    (A : Finset Ω) (Nfull N : ℕ) {alpha delta xi zeta : ℝ}
    (ha : 0 ≤ alpha) (hd : 0 ≤ delta) (hdq : 2 * delta ≤ 1 - pK k)
    (hxi : 0 ≤ xi) (hxi1 : xi < 1) (hband : 2 * alpha / (1 - xi) ≤ 1 / 2)
    (hz : 0 ≤ zeta) (hprob : ∀ e ∈ A, P.probability e ≤ pK k + delta)
    (hfull : A.card ≤ Nfull) (hsize : |(Nfull : ℝ) - N| ≤ zeta * N) :
    P.eventProbability (successCountAtLeast A ((1 - 2 * alpha) * Nfull)) ≤
      Real.exp ((subcriticalTailErrorNat k alpha delta xi zeta -
        subcriticalLocalU_Nat k) * N) := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hp1 := pK_lt_one (show 2 ≤ k by omega)
  have htail := P.probability_successCountAtLeast_le A Nfull
    (show 0 ≤ 2 * alpha by linarith) (tail_entropy_radius ha hxi hxi1 hband).1
    (show 0 < pK k + delta by linarith) (show pK k + delta ≤ 1 by linarith)
    hprob hfull
  apply htail.trans
  apply Real.exp_le_exp.mpr
  apply (mul_le_mul_of_nonneg_right
    (subcriticalTail_upper_coefficient_le hk ha hd hxi hxi1 hband)
    (Nat.cast_nonneg Nfull)).trans
  exact subcriticalTail_scale_loss
    (subcriticalTailBaseErrorNat_nonneg hk ha hd hxi hxi1 hband)
    (subcriticalLocalU_Nat_pos hk).le le_rfl hz (Nat.cast_nonneg N) hsize

/-- Finite lower-tail estimate at the source scale, including deletion of
up to `xi` of the full target. -/
theorem subcriticalTail_lower_probability_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {k : ℕ} (hk : 3 ≤ k) (P : DenseGraph.FiniteBernoulliProduct Ω)
    (A : Finset Ω) (Nfull N : ℕ) {alpha delta xi zeta : ℝ}
    (ha : 0 ≤ alpha) (hd : 0 ≤ delta) (hdp : 2 * delta ≤ pK k)
    (hxi : 0 ≤ xi) (hxi1 : xi < 1) (hband : 2 * alpha / (1 - xi) ≤ 1 / 2)
    (hz : 0 ≤ zeta) (hprob : ∀ e ∈ A, pK k - delta ≤ P.probability e)
    (hfull : A.card ≤ Nfull) (htrim : (1 - xi) * Nfull ≤ (A.card : ℝ))
    (hsize : |(Nfull : ℝ) - N| ≤ zeta * N) :
    P.eventProbability (successCountAtMost A (2 * alpha * Nfull)) ≤
      Real.exp ((subcriticalTailErrorNat k alpha delta xi zeta -
        subcriticalLocalA_Nat k) * N) := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hp1 := pK_lt_one (show 2 ≤ k by omega)
  have htail := P.probability_successCountAtMost_le A Nfull
    (show 0 ≤ 2 * alpha by linarith) hxi1 hband
    (show 0 ≤ pK k - delta by linarith) (show pK k - delta < 1 by linarith)
    hprob hfull htrim
  rw [show 1 - (pK k - delta) = 1 - pK k + delta by ring] at htail
  apply htail.trans
  apply Real.exp_le_exp.mpr
  apply (mul_le_mul_of_nonneg_right
    (subcriticalTail_lower_coefficient_le hk ha hd hxi)
    (Nat.cast_nonneg Nfull)).trans
  apply subcriticalTail_scale_loss
    (subcriticalTailBaseErrorNat_nonneg hk ha hd hxi hxi1 hband)
    (subcriticalLocalA_Nat_pos hk).le _ hz (Nat.cast_nonneg N) hsize
  rw [subcriticalLocalU_Nat_eq_L_add_A hk]
  linarith [subcriticalLogOddsNat_pos hk]

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}

/-- The exact leading-minus-error bound used for one retained root. -/
def subcriticalTailLowerBound (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (hv : v ∈ p.retainedRoots) (E : ℝ) : ℝ :=
  ((subcriticalUpperNeighborIndices p v hv).card * (subcriticalLocalU_Nat k - E) +
    (subcriticalLowerNeighborIndices p v hv).card * (subcriticalLocalA_Nat k - E)) *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card

theorem subcriticalTailLowerBound_le_zeroSentinel
    (hk : 3 ≤ k) (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (hv : v ∈ p.retainedRoots) {E : ℝ} (hE : 0 ≤ E)
    (hsentinel : ((k - 2 : ℕ) : ℝ) * subcriticalLocalU_Nat k ≤
      (Fintype.card V + 1 : ℝ) ^ 2) :
    subcriticalTailLowerBound p v hv E ≤ (Fintype.card V + 1 : ℝ) ^ 3 := by
  let u := (subcriticalUpperNeighborIndices p v hv).card
  let l := (subcriticalLowerNeighborIndices p v hv).card
  let N := (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card
  have hN : N ≤ Fintype.card V := Finset.card_le_univ _
  have hul : u + l ≤ k - 2 := by
    have h := subcriticalNeighborIndices_card_eq p v hv
    dsimp [u, l]
    omega
  have hU := (subcriticalLocalU_Nat_pos hk).le
  have hA := (subcriticalLocalA_Nat_pos hk).le
  have hAU : subcriticalLocalA_Nat k ≤ subcriticalLocalU_Nat k := by
    rw [subcriticalLocalU_Nat_eq_L_add_A hk]
    linarith [subcriticalLogOddsNat_pos hk]
  have h1 : (u : ℝ) * (subcriticalLocalU_Nat k - E) +
      l * (subcriticalLocalA_Nat k - E) ≤ (u + l) * subcriticalLocalU_Nat k := by
    have he1 := mul_nonneg (Nat.cast_nonneg u) hE
    have he2 := mul_nonneg (Nat.cast_nonneg l) hE
    have ha := mul_le_mul_of_nonneg_left hAU (Nat.cast_nonneg l)
    nlinarith
  have hulR : (u : ℝ) + l ≤ ((k - 2 : ℕ) : ℝ) := by exact_mod_cast hul
  have h2 := mul_le_mul_of_nonneg_right hulR hU
  have h3 := mul_le_mul_of_nonneg_right (h1.trans h2) (Nat.cast_nonneg N)
  have h4 := mul_le_mul_of_nonneg_left (show (N : ℝ) ≤ Fintype.card V by exact_mod_cast hN)
    (mul_nonneg (Nat.cast_nonneg (k - 2)) hU)
  have h5 := mul_le_mul_of_nonneg_right hsentinel (Nat.cast_nonneg (Fintype.card V))
  change ((u : ℝ) * _ + l * _) * N ≤ _
  apply h3.trans (h4.trans (h5.trans ?_))
  nlinarith [sq_nonneg (Fintype.card V + 1 : ℝ)]

/-- A genuine probability bound over the whole narrow window implies the
actual profile penalty bound, including empty windows and zero probabilities. -/
theorem subcriticalProfileRootTailPenalty_ge_of_probability_le
    (hk : 3 ≤ k) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C alpha delta epsilon : ℝ) (v : V) (hv : v ∈ p.retainedRoots)
    {E : ℝ} (hE : 0 ≤ E)
    (hsentinel : ((k - 2 : ℕ) : ℝ) * subcriticalLocalU_Nat k ≤
      (Fintype.card V + 1 : ℝ) ^ 2)
    (hprob : ∀ mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon,
      subcriticalRootTailProbability p alpha v mvec ≤
        Real.exp (-subcriticalTailLowerBound p v hv E)) :
    subcriticalTailLowerBound p v hv E ≤
      subcriticalProfileRootTailPenalty p m C alpha delta epsilon v := by
  by_cases ht : p.HasTail v
  · rw [subcriticalProfileRootTailPenalty, if_pos ⟨hv, ht⟩]
    apply subcriticalNegLogProbability_ge_of_le_exp _ (subcriticalFiniteMax_nonneg _ _)
      (subcriticalFiniteMax_le (Real.exp_pos _).le hprob)
      (subcriticalTailLowerBound_le_zeroSentinel hk p v hv hE hsentinel)
  · have hu : subcriticalUpperNeighborIndices p v hv = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact ht ⟨a, .upper, (mem_subcriticalUpperNeighborIndices p v hv a).mp ha |>.2⟩
    have hl : subcriticalLowerNeighborIndices p v hv = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact ht ⟨a, .lower, (mem_subcriticalLowerNeighborIndices p v hv a).mp ha |>.2⟩
    simp [subcriticalTailLowerBound, hu, hl, subcriticalProfileRootTailPenalty, ht]

/-- Every active coordinate in the narrow quota window lies in the
literal compact probability interval, regardless of its tagged block. -/
theorem subcriticalActiveBernoulli_probability_mem_narrow
    {m : ℕ} {C delta epsilon : ℝ} (mvec : RetainedEdgeCountVector D eta R₀)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon)
    (e : SubcriticalActiveCoordinate D eta R₀) :
    pK k - delta ≤ (subcriticalActiveBernoulliModel mvec).probability e ∧
      (subcriticalActiveBernoulliModel mvec).probability e ≤ pK k + delta := by
  rw [subcriticalActiveBernoulliModel_probability]
  exact (mem_retainedNarrowEdgeCountLevel.mp (mem_retainedNarrowEdgeCountWindow.mp hm).1).2 e.1

/-- The actual labeled-tail event obeys the explicit finite estimate. The
scale and deleted-root hypotheses concern literal full target sizes. -/
theorem subcriticalTailEvent_probability_le
    (hk : 3 ≤ k) (p : SubcriticalProfile D eta R₀ theta)
    {m : ℕ} {C alpha delta epsilon xi zeta : ℝ}
    (mvec : RetainedEdgeCountVector D eta R₀)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon)
    (ha : 0 ≤ alpha) (hd : 0 ≤ delta)
    (hdp : 2 * delta ≤ pK k) (hdq : 2 * delta ≤ 1 - pK k)
    (hxi : 0 ≤ xi) (hxi1 : xi < 1) (hband : 2 * alpha / (1 - xi) ≤ 1 / 2)
    (hz : 0 ≤ zeta) (v : V) (a : D.PartIndex) (N : ℕ)
    {t : SubcriticalTailDirection} (ht : p.tails v a = some t)
    (hroot : (p.roots.card : ℝ) ≤ xi * (D.part a).card)
    (hsize : |((D.part a).card : ℝ) - N| ≤ zeta * N) :
    (subcriticalActiveBernoulliModel mvec).eventProbability (subcriticalTailEvent p alpha v a t) ≤
      Real.exp ((subcriticalTailErrorNat k alpha delta xi zeta -
        (match t with | .upper => subcriticalLocalU_Nat k | .lower => subcriticalLocalA_Nat k)) * N) := by
  have hc := subcriticalTailCoordinates_card p v a mvec ht
  have hfull : (subcriticalTailCoordinates p v a).card ≤ (D.part a).card := by
    rw [hc]
    exact Finset.card_le_card Finset.sdiff_subset
  have htrim : (1 - xi) * (D.part a).card ≤ ((subcriticalTailCoordinates p v a).card : ℝ) := by
    rw [hc]
    have hdel : ((D.part a).card : ℝ) ≤ (D.part a \ p.roots).card + p.roots.card := by
      exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := D.part a) (t := p.roots))
    nlinarith
  cases t with
  | upper =>
    rw [subcriticalTailEvent_upper_eq_count p alpha v a mvec]
    exact subcriticalTail_upper_probability_le hk (subcriticalActiveBernoulliModel mvec)
      _ _ N ha hd hdq hxi hxi1 hband hz
      (fun e _ ↦ (subcriticalActiveBernoulli_probability_mem_narrow mvec hm e).2)
      hfull hsize
  | lower =>
    rw [subcriticalTailEvent_lower_eq_count p alpha v a mvec]
    exact subcriticalTail_lower_probability_le hk (subcriticalActiveBernoulliModel mvec)
      _ _ N ha hd hdp hxi hxi1 hband hz
      (fun e _ ↦ (subcriticalActiveBernoulli_probability_mem_narrow mvec hm e).1)
      hfull htrim hsize

/-- The whole root-tail probability is bounded with an error per recorded
tail, uniformly over every quota vector in the narrow window. -/
theorem subcriticalRootTailProbability_le_exp_explicit
    (hk : 3 ≤ k) (p : SubcriticalProfile D eta R₀ theta)
    {m : ℕ} {C alpha delta epsilon xi zeta : ℝ}
    (mvec : RetainedEdgeCountVector D eta R₀)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon)
    (ha : 0 ≤ alpha) (hd : 0 ≤ delta)
    (hdp : 2 * delta ≤ pK k) (hdq : 2 * delta ≤ 1 - pK k)
    (hxi : 0 ≤ xi) (hxi1 : xi < 1) (hband : 2 * alpha / (1 - xi) ≤ 1 / 2)
    (hz : 0 ≤ zeta) (v : V) (hv : v ∈ p.retainedRoots)
    (hroot : ∀ a t, p.tails v a = some t → (p.roots.card : ℝ) ≤ xi * (D.part a).card)
    (hsize : ∀ a t, p.tails v a = some t →
      |((D.part a).card : ℝ) -
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card| ≤
      zeta * (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card) :
    subcriticalRootTailProbability p alpha v mvec ≤
      Real.exp (-subcriticalTailLowerBound p v hv (subcriticalTailErrorNat k alpha delta xi zeta)) := by
  let N := (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card
  let E := subcriticalTailErrorNat k alpha delta xi zeta
  let P := subcriticalActiveBernoulliModel mvec
  have hup : (∏ a ∈ subcriticalUpperNeighborIndices p v hv,
      P.eventProbability (subcriticalTailEvent p alpha v a .upper)) ≤
      Real.exp ((E - subcriticalLocalU_Nat k) * N) ^
        (subcriticalUpperNeighborIndices p v hv).card := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro a _; exact P.eventProbability_nonneg _
    · intro a ha'
      have ht := (subcriticalUpperNeighborIndices_mem_iff_tail p v hv a).mp ha'
      exact subcriticalTailEvent_probability_le hk p mvec hm ha hd hdp hdq hxi hxi1 hband hz
        v a N ht (hroot a .upper ht) (hsize a .upper ht)
  have hlo : (∏ a ∈ subcriticalLowerNeighborIndices p v hv,
      P.eventProbability (subcriticalTailEvent p alpha v a .lower)) ≤
      Real.exp ((E - subcriticalLocalA_Nat k) * N) ^
        (subcriticalLowerNeighborIndices p v hv).card := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro a _; exact P.eventProbability_nonneg _
    · intro a ha'
      have ht := (subcriticalLowerNeighborIndices_mem_iff_tail p v hv a).mp ha'
      exact subcriticalTailEvent_probability_le hk p mvec hm ha hd hdp hdq hxi hxi1 hband hz
        v a N ht (hroot a .lower ht) (hsize a .lower ht)
  rw [subcriticalRootTailProbability_eq_target_product p alpha v hv mvec]
  apply (mul_le_mul hup hlo
    (Finset.prod_nonneg (fun a _ ↦ P.eventProbability_nonneg _)) (by positivity)).trans
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  apply le_of_eq
  congr 1
  unfold subcriticalTailLowerBound
  dsimp [N, E]
  ring

/-- Paper: Claim `claim:local-tail-estimate-K1k`.
Explicit natural-unit error replaces the
paper's `o(1)`. This is the actual finite profile penalty `J_v`, not an
auxiliary negative logarithm. Zero probabilities require no positivity
assumption: the displayed finite threshold controls their cubic sentinel. -/
theorem subcriticalLocalTailPenalty_lower
    (hk : 3 ≤ k) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C alpha delta epsilon xi zeta : ℝ)
    (ha : 0 ≤ alpha) (hd : 0 ≤ delta)
    (hdp : 2 * delta ≤ pK k) (hdq : 2 * delta ≤ 1 - pK k)
    (hxi : 0 ≤ xi) (hxi1 : xi < 1) (hband : 2 * alpha / (1 - xi) ≤ 1 / 2)
    (hz : 0 ≤ zeta) (v : V) (hv : v ∈ p.retainedRoots)
    (hroot : ∀ a t, p.tails v a = some t → (p.roots.card : ℝ) ≤ xi * (D.part a).card)
    (hsize : ∀ a t, p.tails v a = some t →
      |((D.part a).card : ℝ) -
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card| ≤
      zeta * (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hsentinel : ((k - 2 : ℕ) : ℝ) * subcriticalLocalU_Nat k ≤
      (Fintype.card V + 1 : ℝ) ^ 2) :
    subcriticalTailLowerBound p v hv (subcriticalTailErrorNat k alpha delta xi zeta) ≤
      subcriticalProfileRootTailPenalty p m C alpha delta epsilon v := by
  apply subcriticalProfileRootTailPenalty_ge_of_probability_le hk p m C alpha delta epsilon v hv
    (subcriticalTailErrorNat_nonneg hk ha hd hxi hxi1 hband hz) hsentinel
  intro mvec hm
  exact subcriticalRootTailProbability_le_exp_explicit hk p mvec hm ha hd hdp hdq
    hxi hxi1 hband hz v hv hroot hsize

end InducedStars
