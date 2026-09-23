import InducedStars.Structure.Subcritical.LocalSupportGeometry
import InducedStars.Structure.Subcritical.LocalSupportAccounting
import InducedStars.Structure.Subcritical.LocalPenaltyErrors

/-!
# Unified retained-root compensation

The common exponent is controlled by the full-degree component deficit.
Its sole zero-deficit configuration is handled by one placement comparison
and the own-part entropy loss. No previous per-root case penalty is used.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace InducedStars
variable {k n R₀ : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
  {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
  {omega eta theta alpha delta epsilon rho : ℝ}

set_option maxHeartbeats 2500000 in
/-- The unified local-compensation proof at a retained root, with all finite
error reserves explicit and the unchanged own-part-scale conclusion. -/
theorem subcriticalRetainedRootUnifiedPenalty
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (ha5 : 5 * alpha ≤ 1)
    (hsmall : (4 * (k : ℝ) + 8) * alpha ≤ 1)
    (htheta : 0 < theta) (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hdp : 2 * delta ≤ pK k) (hdq : 2 * delta ≤ 1 - pK k)
    (hn : 0 < n) (hscale : 8 ≤ alpha * theta * n)
    (hrho : 0 ≤ rho) (hR : 1 ≤ R₀) (heta : 0 < eta)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (hp : RealizesSubcriticalProfile G alpha p)
    (hB : (p.roots.card : ℝ) ≤ rho * n)
    (hBalpha : ∀ a ∈ D.visiblePartIndices theta,
      (p.roots.card : ℝ) + 1 ≤ alpha * (D.part a).card)
    (hxi1 : subcriticalTrimErrorNat rho theta < 1)
    (hownband : subcriticalSmallOwnConstant k * alpha /
      (1 - subcriticalTrimErrorNat rho theta) ≤ 1 / 2)
    (htailband : 2 * alpha / (1 - subcriticalTrimErrorNat rho theta) ≤ 1 / 2)
    (hsentinel : ((k - 2 : ℕ) : ℝ) * subcriticalLocalU_Nat k ≤ (n + 1 : ℝ) ^ 2)
    (herror : subcriticalTotalErrorNat k R₀ eta alpha delta
      (subcriticalTrimErrorNat rho theta) (subcriticalInsideScaleErrorNat alpha delta theta n) ≤
        subcriticalLocalA_Nat k / 4)
    (hminimal : ∀ E : SubcriticalDivision k (Fin n),
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : Fin n) (hv : v ∈ p.retainedRoots)
    (hsource : 2 ≤ (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hbalance : ∀ b : D.PartIndex,
      b.1 = (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1 →
      ((D.part b).card : ℝ) ≤ 2 *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (m : ℕ) (C : ℝ) :
    subcriticalProfileLocalExponent p m C alpha delta epsilon v ≤
      -(subcriticalLocalA_Nat k / 2) *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card := by
  let own := D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)
  let N := ((D.part own).card : ℝ)
  let A := subcriticalLocalA_Nat k
  let U := subcriticalLocalU_Nat k
  let Z := subcriticalLogOddsNat k
  let xi := subcriticalTrimErrorNat rho theta
  let zeta := subcriticalInsideScaleErrorNat alpha delta theta n
  let Er := subcriticalRowErrorNat k alpha (zeta + xi)
  let Et := subcriticalTailErrorNat k alpha delta xi zeta
  let Es := subcriticalSmallOwnErrorNat k alpha xi
  let Eh := Real.binEntropy (2 * alpha)
  let Ex := subcriticalExternalComponentErrorNat k R₀ eta alpha (zeta + xi)
  let E := subcriticalTotalErrorNat k R₀ eta alpha delta xi zeta
  let q := (subcriticalProfileInsideRows p v hv).card
  let u := (subcriticalUpperNeighborIndices p v hv).card
  let l := (subcriticalLowerNeighborIndices p v hv).card
  let h := (subcriticalProfileHighInsideRows p alpha v hv).card
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hA : 0 < A := subcriticalLocalA_Nat_pos hk
  have hU : 0 < U := subcriticalLocalU_Nat_pos hk
  have hZ : 0 < Z := subcriticalLogOddsNat_pos hk
  have hUA : U = Z + A := subcriticalLocalU_Nat_eq_L_add_A hk
  have ha4 : alpha ≤ 1 / 4 := by linarith
  have hxi : 0 ≤ xi := by dsimp [xi, subcriticalTrimErrorNat]; positivity
  have hz : 0 ≤ zeta := by dsimp [zeta, subcriticalInsideScaleErrorNat]; positivity
  have her : 0 ≤ Er := subcriticalRowErrorNat_nonneg hk halpha.le ha4 (add_nonneg hz hxi)
  have het : 0 ≤ Et := subcriticalTailErrorNat_nonneg hk halpha.le hdelta0 hxi hxi1 htailband hz
  obtain ⟨hes, heh, _, hex, _⟩ := subcriticalTotalErrorNat_components_nonneg hk heta.le
    halpha.le ha4 hdelta0 hxi hxi1 hz hownband htailband
  have hvis : own ∈ D.visiblePartIndices theta :=
    hret (D.retainedVertexPart_mem_retained eta R₀ v (p.retainedRoots_subset hv))
  have htrim : ∀ a ∈ D.visiblePartIndices theta,
      2 * (p.roots.card : ℝ) ≤ (D.part a).card := by
    intro a ha
    have hN : (0 : ℝ) ≤ (D.part a).card := Nat.cast_nonneg _
    nlinarith [hBalpha a ha]
  have hBsmall : ∀ a ∈ D.visiblePartIndices theta,
      (p.roots.card : ℝ) ≤ alpha * (D.part a).card := by
    intro a ha
    linarith [hBalpha a ha]
  have hrootXi : ∀ a ∈ D.visiblePartIndices theta,
      (p.roots.card : ℝ) ≤ xi * (D.part a).card := by
    intro a ha
    have hpart := R.visible_part_card_ge_half homega a ha
    have hmul := mul_le_mul_of_nonneg_left hpart hxi
    have heq : xi * (theta * n / 2) = rho * n := by
      dsimp [xi, subcriticalTrimErrorNat]
      field_simp
      <;> ring
    rw [heq] at hmul
    exact hB.trans hmul
  have htrimOwn : (1 - xi) * N ≤ ((D.part own \ p.roots).card : ℝ) := by
    have hc : N ≤ (D.part own \ p.roots).card + (p.roots.card : ℝ) := by
      dsimp [N]
      exact_mod_cast Finset.card_le_card_sdiff_add_card (s := D.part own) (t := p.roots)
    have hh := hrootXi own hvis
    change (p.roots.card : ℝ) ≤ xi * N at hh
    nlinarith
  have hinsideSize : ∀ a ∈ subcriticalProfileInsideRows p v hv,
      |((D.part a \ p.roots).card : ℝ) - N| ≤ (zeta + xi) * N := by
    intro a ha
    have hai := ((mem_subcriticalProfileInsideRows p v hv a).mp ha).2
    rcases a with ⟨i, a⟩
    change i = own.1 at hai
    subst i
    exact R.local_trimmed_visible_part_deviation homega halpha htheta hdelta0 hn hrho
      p hB own.1 ((D.mem_visiblePartIndices theta own).mp hvis) own.2 a
  have hins := subcriticalInsideRowsEntropy hk p v hv halpha.le ha4 (add_nonneg hz hxi) hinsideSize
  have hout := subcriticalExternalRowsEntropy R hfree homega halpha (by linarith) htheta
    hdelta0 hdelta hn hscale hrho hR heta hret hp hB htrim v hv
  have htail := subcriticalLocalTailPenalty_lower hk p m C alpha delta epsilon xi zeta
    halpha.le hdelta0 hdp hdq hxi hxi1 htailband hz v hv
    (by
      intro a t ht
      obtain ⟨hv', hact⟩ := p.tails_valid v a t ht
      apply hrootXi a
      apply subcriticalActiveNeighbor_visible p v hv hret
      exact (mem_subcriticalActiveNeighborIndices p v hv a).mpr hact)
    (by
      intro a t ht
      obtain ⟨hv', hact⟩ := p.tails_valid v a t ht
      have hai := (SubcriticalDivision.activePart_same_component hact).symm
      rcases a with ⟨i, a⟩
      change i = own.1 at hai
      subst i
      exact R.local_visible_part_size_deviation homega halpha htheta hdelta0 hn own.1
        ((D.mem_visiblePartIndices theta own).mp hvis) own.2 a)
    (by simpa using hsentinel)
  have hbudget := subcriticalLocalNonlowBudget R hfree homega halpha (by linarith)
    htheta hdelta hscale hret hp v hv
  have hq : q ≤ k - 1 := by dsimp [q]; omega
  have hul : u + l ≤ k - 2 := by
    have hc := subcriticalNeighborIndices_card_eq p v hv
    dsimp [u, l]
    omega
  have hqR : (q : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast hq
  have hulR : (u : ℝ) + l ≤ (k - 2 : ℕ) := by exact_mod_cast hul
  have hrowErr := mul_le_mul_of_nonneg_right hqR her
  have htailErr := mul_le_mul_of_nonneg_right hulR het
  have hdecomp := subcriticalRootEntropy_decomposition p v hv
  let T : ℝ := (D.part own \ p.roots).card
  let ownLoss : ℝ := U * (N - T) + T * Real.log 2 *
    binaryRelativeEntropy (pK k) (1 - (p.ownCount v).val / T)
  have hownIdentity : subcriticalProfileOwnMissingEntropyNat p v = U * N - ownLoss := by
    rw [subcriticalProfileOwnMissingEntropyNat, dif_pos hv]
    have hh := subcriticalLocalEntropy_own_eq_max_sub_loss hk
      (Nat.cast_nonneg (p.ownCount v).val)
      (show ((p.ownCount v).val : ℝ) ≤ T by
        dsimp [T, own]
        exact_mod_cast subcriticalProfileOwnCount_le_trimmed p v hv)
    change T * Real.binEntropy ((p.ownCount v).val / T) + Z * (p.ownCount v).val = _
    dsimp [ownLoss]
    change T * Real.binEntropy ((p.ownCount v).val / T) + Z * (p.ownCount v).val =
      U * T - T * Real.log 2 * binaryRelativeEntropy (pK k) (1 - (p.ownCount v).val / T) at hh
    nlinarith only [hh]
  have hmaster (b : ℝ)
      (hb : subcriticalProfileOwnMissingEntropyNat p v ≤ (b + Es + Eh) * N) :
      subcriticalProfileLocalExponent p m C alpha delta epsilon v ≤
        (b + ((q : ℝ) - l) * A - ((u : ℝ) + h) * U + E) * N := by
    rw [hownIdentity] at hb
    rw [hownIdentity] at hdecomp
    change _ ≤ (A * q - U * h + Er * q) * N at hins
    change _ ≤ Ex * N at hout
    change ((u : ℝ) * (U - Et) + l * (A - Et)) * N ≤ _ at htail
    have hrowErrN := mul_le_mul_of_nonneg_right hrowErr hN
    have htailErrN := mul_le_mul_of_nonneg_right htailErr hN
    change subcriticalProfileRootEntropyNat p v - _ ≤ _
    dsimp [E, subcriticalTotalErrorNat]
    change _ ≤ (b + ((q : ℝ) - l) * A - ((u : ℝ) + h) * U +
      (Es + Eh + (k - 1 : ℕ) * Er + Ex + (k - 2 : ℕ) * Et)) * N
    nlinarith only [hb, hins, hout, htail, hdecomp, hrowErrN, htailErrN]
  have hfinish (b : ℝ)
      (hb : subcriticalProfileOwnMissingEntropyNat p v ≤ (b + Es + Eh) * N)
      (hlead : b + ((q : ℝ) - l) * A - ((u : ℝ) + h) * U ≤ -A) :
      subcriticalProfileLocalExponent p m C alpha delta epsilon v ≤ -(A / 2) * N := by
    apply (hmaster b hb).trans
    apply mul_le_mul_of_nonneg_right _ hN
    change E ≤ A / 4 at herror
    linarith
  have hsmallOwn (hI : ((p.ownCount v).val : ℝ) ≤ subcriticalSmallOwnConstant k * alpha * N) :
      subcriticalProfileOwnMissingEntropyNat p v ≤ (0 + Es + Eh) * N := by
    have hh := subcriticalOwnEntropy_small_le hk p v hv halpha.le hxi1 hownband htrimOwn hI
    change _ ≤ Es * N at hh
    have hEhN : 0 ≤ Eh * N := mul_nonneg heh hN
    nlinarith only [hh, hEhN]
  let H := subcriticalHighTargets G D alpha theta v own.1
  let M := subcriticalMediumTargets G D alpha theta v own.1
  let eH : ℕ := if own ∈ H then 1 else 0
  let eM : ℕ := if own ∈ M then 1 else 0
  let B₀ : ℝ := Z * (1 - eH) + A * eM
  let deficit : ℝ := ((k - 2 : ℕ) : ℝ) * H.card - M.card
  have hdisjoint : Disjoint H M := subcriticalHighMediumTargets_disjoint G D alpha theta v own.1
  have hindicator : (if own ∈ H ∪ M then 1 else 0) = eH + eM := by
    by_cases hH : own ∈ H <;> by_cases hM : own ∈ M
    · exact False.elim (Finset.disjoint_left.mp hdisjoint hH hM)
    all_goals simp [eH, eM, hH, hM]
  have hcounts := subcriticalUnifiedRootCounts hp halpha ha5 hret htrim v hv
  change q + u + (subcriticalMediumNeighborIndices p v hv).card +
      (if own ∈ H ∪ M then 1 else 0) ≤ H.card + M.card ∧
    H.card ≤ u + h + (if own ∈ H then 1 else 0) at hcounts
  rw [hindicator] at hcounts
  have hcR : (q : ℝ) + u + (subcriticalMediumNeighborIndices p v hv).card +
      (eH + eM) ≤ H.card + M.card := by exact_mod_cast hcounts.1
  have hhR : (H.card : ℝ) ≤ u + h + eH := by exact_mod_cast hcounts.2
  have hnR : (u : ℝ) + l + (subcriticalMediumNeighborIndices p v hv).card =
      (k - 2 : ℕ) := by exact_mod_cast subcriticalNeighborIndices_card_eq p v hv
  have hZA : Z = ((k - 2 : ℕ) : ℝ) * A := subcriticalLogOddsNat_eq_delta_mul_A hk
  have hleading : B₀ + ((q : ℝ) - l) * A - ((u : ℝ) + h) * U ≤ -A * deficit := by
    have h1 := mul_le_mul_of_nonneg_right hcR hA.le
    have h2 := mul_le_mul_of_nonneg_right hhR hU.le
    have hN := congrArg (fun x : ℝ ↦ x * A) hnR
    dsimp [B₀, deficit]
    rw [hUA, hZA] at h2 ⊢
    nlinarith only [h1, h2, hN]
  have hcomp := subcriticalMediumTargets_high_companion R hfree homega halpha htheta
    hdelta hscale v own.1
  have hD : 0 ≤ subcriticalTargetDeficit G D alpha theta v own.1 :=
    subcriticalTargetDeficit_nonneg G D alpha theta v own.1 hcomp
  have hDcast : (subcriticalTargetDeficit G D alpha theta v own.1 : ℝ) = deficit := by
    simp only [subcriticalTargetDeficit, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    rfl
  have hNpos : 0 < N := by dsimp [N]; exact_mod_cast (D.part_nonempty own).card_pos
  have hIcomp : ((p.ownCount v).val : ℝ) ≤
      complementDegreeInFinset G v (D.part own) := by
    rw [hp.own_counts v hv]
    exact_mod_cast (subcriticalComplement_trim_bounds G v (D.part own) p.roots).1
  have hfull : (degreeInFinset G v (D.part own) : ℝ) +
      complementDegreeInFinset G v (D.part own) + 1 = N := by
    dsimp [N]
    exact_mod_cast subcriticalOwn_degree_complement_add_one G v (D.part own)
      (D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))
  have hsmallFactor : 1 ≤ subcriticalSmallOwnConstant k := by
    unfold subcriticalSmallOwnConstant
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hbase : subcriticalProfileOwnMissingEntropyNat p v ≤ (B₀ + Es + Eh) * N := by
    by_cases hH : own ∈ H
    · have hM : own ∉ M := fun hM ↦ Finset.disjoint_left.mp hdisjoint hH hM
      have hd := (mem_subcriticalHighTargets G D alpha theta v own.1 own).mp hH |>.2.2
      have hI : ((p.ownCount v).val : ℝ) ≤ subcriticalSmallOwnConstant k * alpha * N := by
        have hm := mul_le_mul_of_nonneg_right hsmallFactor (mul_nonneg halpha.le hN)
        change (1 - alpha) * N ≤ _ at hd
        nlinarith only [hm, hIcomp, hfull, hd]
      simpa only [B₀, eH, eM, if_pos hH, if_neg hM, Nat.cast_one, Nat.cast_zero,
        sub_self, mul_zero, add_zero, zero_add] using hsmallOwn hI
    · by_cases hM : own ∈ M
      · have hh := subcriticalOwnEntropy_le hk p v hv
        have heN : 0 ≤ (Es + Eh) * N := mul_nonneg (add_nonneg hes heh) hN
        have hbaseEq : B₀ = U := by simp only [B₀, eH, eM, if_neg hH,
          if_pos hM, Nat.cast_one, Nat.cast_zero, sub_zero, mul_one]; linarith only [hUA]
        rw [hbaseEq]
        change _ ≤ U * N at hh
        nlinarith only [hh, heN]
      · have hd : (degreeInFinset G v (D.part own) : ℝ) ≤ alpha * N := by
          apply le_of_not_gt
          intro hd
          have hh := subcriticalDensitySupport_mem_of_degree_gt G D v own.1 own hvis rfl hd
          rcases Finset.mem_union.mp hh with hh | hh
          · exact hH hh
          · exact hM hh
        have htrimN : N ≤ 2 * ((D.part own \ p.roots).card : ℝ) := by
          have hc : N ≤ (D.part own \ p.roots).card + (p.roots.card : ℝ) := by
            dsimp [N]
            exact_mod_cast Finset.card_le_card_sdiff_add_card (s := D.part own) (t := p.roots)
          linarith only [hc, htrim own hvis]
        have hsum : (degreeInFinset G v (D.part own \ p.roots) : ℝ) +
            (p.ownCount v).val = (D.part own \ p.roots).card := by
          rw [hp.own_counts v hv]
          exact_mod_cast subcriticalOwn_trimmed_degree_add_count G v (D.part own) p.roots
            (Finset.mem_union_left _ hv)
        have hdtrim : (degreeInFinset G v (D.part own \ p.roots) : ℝ) ≤
            degreeInFinset G v (D.part own) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter (G.Adj v)
            (Finset.sdiff_subset : D.part own \ p.roots ⊆ D.part own))
        have hI : (1 - 2 * alpha) * (D.part own \ p.roots).card ≤
            ((p.ownCount v).val : ℝ) := by
          have hm := mul_le_mul_of_nonneg_left htrimN halpha.le
          nlinarith only [hd, hdtrim, hsum, hm]
        have hh := subcriticalOwnEntropy_high_le hk p v hv halpha.le ha4 hI
        have hEsN := mul_nonneg hes hN
        have hbaseEq : B₀ = Z := by simp [B₀, eH, eM, hH, hM]
        rw [hbaseEq]
        change _ ≤ (Z + Eh) * N at hh
        nlinarith only [hh, hEsN]
  by_cases hpositive : 1 ≤ subcriticalTargetDeficit G D alpha theta v own.1
  · have hpR : (1 : ℝ) ≤ deficit := by
      rw [← hDcast]
      exact_mod_cast hpositive
    apply hfinish B₀ hbase
    have hm := mul_le_mul_of_nonneg_left hpR hA.le
    linarith only [hleading, hm]
  · have hzD : subcriticalTargetDeficit G D alpha theta v own.1 = 0 := by omega
    have hzero : deficit = 0 := by rw [← hDcast, hzD, Int.cast_zero]
    have hownLoop : 1 ≤ alpha * N := by
      have hb := hBalpha own hvis
      have hp0 : (0 : ℝ) ≤ p.roots.card := Nat.cast_nonneg _
      linarith
    have hS := subcriticalOwnDensitySupport_nonempty hk G D halpha hsmall hminimal v own
      (D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) hsource hownLoop hvis hbalance
    have hbudget := subcriticalNonlowVisibleParts_card_le hk R hfree homega halpha htheta hdelta hscale v
    have hScard := (Finset.card_le_card
      (subcriticalDensitySupport_subset_nonlow G D (by linarith : alpha ≤ 1 / 2) v own.1)).trans hbudget
    obtain ⟨t, hH, hM, hSat⟩ := subcriticalTargetDeficit_zero_structure hk G D alpha theta
      v own.1 hcomp hS hScard hzD
    have ht : t ∈ subcriticalHighTargets G D alpha theta v own.1 := by rw [hH]; simp
    obtain ⟨htvis, hti, hthigh⟩ := (mem_subcriticalHighTargets G D alpha theta v own.1 t).mp ht
    have hlow := subcriticalZeroDeficit_outside_closed_low G D
      (by linarith : alpha ≤ 1 / 2) v own.1 t hH hM hSat hbudget
    have htne := subcriticalZeroDeficit_high_ne_own G D hp halpha v hv t hthigh hlow
    have hzalpha : zeta ≤ 2 * alpha := by
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hden : 0 < theta * n := mul_pos htheta hnpos
      have hdiv : 8 / (theta * n) ≤ alpha := (div_le_iff₀ hden).mpr (by nlinarith only [hscale])
      have hdp1 : delta ≤ 1 := by linarith only [hdp, (pK_mem_Icc k).2]
      have hh := mul_le_mul_of_nonneg_right hdp1 halpha.le
      dsimp [zeta, subcriticalInsideScaleErrorNat]
      nlinarith only [hdiv, hh, halpha]
    have hdev : N - (D.part t).card ≤ 2 * alpha * N := by
      have hh : |((D.part t).card : ℝ) - N| ≤ zeta * N := by
        rcases t with ⟨i, t⟩
        change i = own.1 at hti
        subst i
        exact R.local_visible_part_size_deviation homega halpha htheta hdelta0 hn own.1
          ((D.mem_visiblePartIndices theta own).mp hvis) own.2 t
      have hm := mul_le_mul_of_nonneg_right hzalpha hN
      linarith only [hm, neg_le_of_abs_le hh]
    have hcompSmall := subcriticalZeroDeficit_own_complement_le hk G D halpha.le hminimal
      v own t (D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) hsource htne
      hthigh (hbalance t hti) hdev (by
        intro b hb
        obtain ⟨_, hb⟩ := Finset.mem_erase.mp hb
        obtain ⟨hb, hbnot⟩ := Finset.mem_sdiff.mp hb
        have hbi : b.1 = own.1 := by
          rcases (D.mem_closedPartIndices_iff own b).mp hb with heq | hab
          · exact congrArg Sigma.fst heq
          · exact (SubcriticalDivision.activePart_same_component hab).symm
        have hbvis : b ∈ D.visiblePartIndices theta := (D.mem_visiblePartIndices theta b).mpr
          (hbi ▸ (D.mem_visiblePartIndices theta own).mp hvis)
        have hh := hlow b hbvis hbnot
        have hsize := mul_le_mul_of_nonneg_left (hbalance b hbi) halpha.le
        nlinarith only [hh, hsize])
    have hI : ((p.ownCount v).val : ℝ) ≤ subcriticalSmallOwnConstant k * alpha * N := by
      dsimp [subcriticalSmallOwnConstant]
      change (complementDegreeInFinset G v (D.part own) : ℝ) ≤ 4 * alpha * k * N at hcompSmall
      have hkN : 0 ≤ alpha * k * N :=
        mul_nonneg (mul_nonneg halpha.le (Nat.cast_nonneg k)) hN
      nlinarith only [hIcomp, hcompSmall, hkN]
    have hHown : own ∉ H := by
      change own ∉ subcriticalHighTargets G D alpha theta v own.1
      rw [hH, Finset.mem_singleton]
      exact Ne.symm htne
    have hMown : own ∈ M := by
      have hband : subcriticalSmallOwnConstant k * alpha ≤ 1 / 2 := by
        have hh := (div_le_iff₀ (by linarith : 0 < 1 - xi)).mp hownband
        linarith only [hh, hxi]
      have hcHalf : (complementDegreeInFinset G v (D.part own) : ℝ) ≤ N / 2 := by
        have hh := mul_le_mul_of_nonneg_right hband hN
        dsimp [subcriticalSmallOwnConstant] at hh
        change (complementDegreeInFinset G v (D.part own) : ℝ) ≤ 4 * alpha * k * N at hcompSmall
        nlinarith only [hh, hcompSmall, hN]
      have hd : alpha * N < (degreeInFinset G v (D.part own) : ℝ) := by
        have hm := mul_le_mul_of_nonneg_right ha5 hN
        nlinarith only [hcHalf, hfull, hownLoop, hNpos, hm]
      have hs := subcriticalDensitySupport_mem_of_degree_gt G D v own.1 own hvis rfl hd
      exact (Finset.mem_union.mp hs).resolve_left hHown
    have hbaseEq : B₀ = U := by
      simp only [B₀, eH, eM, if_neg hHown, if_pos hMown, Nat.cast_zero,
        Nat.cast_one, sub_zero, mul_one]
      linarith only [hUA]
    apply hfinish 0 (hsmallOwn hI)
    rw [hbaseEq, hzero, mul_zero] at hleading
    linarith only [hleading, hUA, hZ]

end InducedStars
