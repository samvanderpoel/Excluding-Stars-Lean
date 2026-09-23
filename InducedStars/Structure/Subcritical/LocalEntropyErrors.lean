import InducedStars.Structure.Subcritical.LocalEntropy
import InducedStars.Structure.Subcritical.LocalRowData
import InducedStars.Structure.Subcritical.RowWitnesses

/-!
# Explicit finite errors for local entropy compensation

Natural units and the explicit small-alpha range are used throughout.
The quantitative alignment already retained by the close-structure bridge
gives a stronger visible-part comparison than its outer omega ratio. Thus
external errors can be summed at a retained-root scale without assuming
that the outer balance tolerance is small relative to eta/R₀.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace InducedStars

/-- Common positive local reserve; constants are deliberately not optimized. -/
def subcriticalLocalPenaltyUnit (k : ℕ) : ℝ := subcriticalLocalA_Nat k / 100

theorem subcriticalLocalPenaltyUnit_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < subcriticalLocalPenaltyUnit k := div_pos (subcriticalLocalA_Nat_pos hk) (by norm_num)

/-- Loss in the high-row entropy estimate before target-size comparison. -/
def subcriticalHighRowErrorNat (k : ℕ) (alpha : ℝ) : ℝ :=
  Real.binEntropy (2 * alpha) + 2 * subcriticalLogOddsNat k * alpha

/-- Relative visible-part size error supplied by the actual alignment. -/
def subcriticalInsideScaleErrorNat (alpha delta theta : ℝ) (n : ℕ) : ℝ :=
  delta * alpha / 2 + 8 / (theta * n)

/-- Relative root-deletion error at the visible-part lower bound. -/
def subcriticalTrimErrorNat (rho theta : ℝ) : ℝ := 2 * rho / theta

/-- One explicit bound covering ordinary and high present-row losses. -/
def subcriticalRowErrorNat (k : ℕ) (alpha zeta : ℝ) : ℝ :=
  subcriticalHighRowErrorNat k alpha +
    (subcriticalLocalA_Nat k + subcriticalLogOddsNat k +
      subcriticalHighRowErrorNat k alpha) * zeta

theorem subcriticalHighRowErrorNat_nonneg {k : ℕ} (hk : 3 ≤ k)
    {alpha : ℝ} (ha : 0 ≤ alpha) (haQuarter : alpha ≤ 1 / 4) :
    0 ≤ subcriticalHighRowErrorNat k alpha := by
  unfold subcriticalHighRowErrorNat
  exact add_nonneg (Real.binEntropy_nonneg (by linarith) (by linarith))
    (mul_nonneg (mul_nonneg (by norm_num) (subcriticalLogOddsNat_pos hk).le) ha)

theorem subcriticalRowErrorNat_nonneg {k : ℕ} (hk : 3 ≤ k)
    {alpha zeta : ℝ} (ha : 0 ≤ alpha) (haQuarter : alpha ≤ 1 / 4)
    (hz : 0 ≤ zeta) : 0 ≤ subcriticalRowErrorNat k alpha zeta := by
  have hE := subcriticalHighRowErrorNat_nonneg hk ha haQuarter
  have hA := (subcriticalLocalA_Nat_pos hk).le
  have hL := (subcriticalLogOddsNat_pos hk).le
  unfold subcriticalRowErrorNat
  positivity

namespace SubcriticalCloseStructureResult

/-- The retained alignment bounds the difference of any two visible parts
in one component by `delta*alpha/2 + 8/(theta*n)` times either part size.
The additive four vertices account explicitly for both cell roundings. -/
theorem local_visible_part_size_deviation
    {k n R₀ : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
    {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
    {omega eta theta alpha delta epsilon : ℝ}
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hdelta : 0 ≤ delta) (hn : 0 < n)
    (i : Fin D.componentCount) (hi : i ∈ D.visibleComponentIndices theta)
    (a b : Fin (D.core i).order) :
    |((D.parts i b).card : ℝ) - (D.parts i a).card| ≤
      subcriticalInsideScaleErrorNat alpha delta theta n * (D.parts i a).card := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let P := R.parameters
  let e := P.alignmentError + 2 / (n : ℝ)
  have hen : e * n = P.alignmentError * n + 2 := by
    dsimp [e]
    rw [add_mul, div_mul_cancel₀ _ hnR.ne']
  have herror : ((P.B : ℝ) + 2) * (P.zeta * n) + 2 ≤ e * n := by
    rw [hen]
    dsimp [SubcriticalClosenessParameters.alignmentError]
    push_cast
    nlinarith [mul_nonneg P.zeta_pos.le hnR.le]
  let ii : {i // i ∈ D.visibleComponentIndices P.t} :=
    ⟨i, D.visibleComponentIndices_mono P.t_le_theta hi⟩
  have ha := R.alignment.part_size_error_le hn herror ii a
  have hb := R.alignment.part_size_error_le hn herror ii b
  have hdiff : |((D.parts i b).card : ℝ) - (D.parts i a).card| ≤
      2 * (P.alignmentError * n + 2) := by
    have h := (abs_sub_le ((D.parts i b).card : ℝ)
      (L.alpha (R.alignment.assignment ii).val * n / (D.core i).order)
      ((D.parts i a).card : ℝ)).trans
        (add_le_add hb (by simpa only [abs_sub_comm] using ha))
    simpa only [hen, two_mul] using h
  have hden : 0 < subcriticalVisibleScale alpha theta := by
    unfold subcriticalVisibleScale
    positivity
  have herr : 2 * P.alignmentError ≤ delta * subcriticalVisibleScale alpha theta := by
    apply (div_le_iff₀ hden).mp
    have h := P.density_reserve
    have hz : 0 ≤ P.beta / (subcriticalVisibleScale alpha theta) ^ 2 :=
      div_nonneg P.beta_pos.le (sq_nonneg _)
    change P.beta / (subcriticalVisibleScale alpha theta) ^ 2 +
      2 * P.alignmentError / subcriticalVisibleScale alpha theta ≤ delta at h
    linarith
  have hbound : 2 * (P.alignmentError * n + 2) ≤ delta * alpha * theta * n / 4 + 4 := by
    have h := mul_le_mul_of_nonneg_right herr hnR.le
    dsimp [subcriticalVisibleScale] at h
    nlinarith
  have hpart := R.visible_part_card_ge_half homega (⟨i, a⟩ : D.PartIndex)
    ((D.mem_visiblePartIndices theta ⟨i, a⟩).mpr hi)
  have hscale0 : 0 ≤ subcriticalInsideScaleErrorNat alpha delta theta n := by
    unfold subcriticalInsideScaleErrorNat
    positivity
  calc
    _ ≤ delta * alpha * theta * n / 4 + 4 := hdiff.trans hbound
    _ = subcriticalInsideScaleErrorNat alpha delta theta n * (theta * n / 2) := by
      unfold subcriticalInsideScaleErrorNat
      field_simp
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpart hscale0

end SubcriticalCloseStructureResult

/-- Ordinary present-row entropy with the shared explicit error. -/
theorem subcriticalLocalEntropy_row_le_with_error {k : ℕ} (hk : 3 ≤ k)
    {alpha N N' r zeta : ℝ} (ha : 0 ≤ alpha) (haQuarter : alpha ≤ 1 / 4)
    (hN : 0 ≤ N) (hz : 0 ≤ zeta) (hr : 0 ≤ r) (hrN : r ≤ N')
    (hscale : |N' - N| ≤ zeta * N) :
    N' * Real.binEntropy (r / N') - subcriticalLogOddsNat k * r ≤
      (subcriticalLocalA_Nat k + subcriticalRowErrorNat k alpha zeta) * N := by
  have hE := subcriticalHighRowErrorNat_nonneg hk ha haQuarter
  have hL := (subcriticalLogOddsNat_pos hk).le
  have h := subcriticalLocalEntropy_row_le_of_scale_error hk hr hrN hscale
  have he : subcriticalLocalA_Nat k * zeta ≤ subcriticalRowErrorNat k alpha zeta := by
    unfold subcriticalRowErrorNat
    nlinarith
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hN)

/-- High present-row entropy with the same error. -/
theorem subcriticalLocalEntropy_high_row_le_with_error {k : ℕ} (hk : 3 ≤ k)
    {alpha N N' r zeta : ℝ} (ha : 0 ≤ alpha) (haQuarter : alpha ≤ 1 / 4)
    (hN : 0 ≤ N) (hz : 0 ≤ zeta) (hr : 0 ≤ r) (hrN : r ≤ N')
    (hhigh : (1 - 2 * alpha) * N' ≤ r) (hscale : |N' - N| ≤ zeta * N) :
    N' * Real.binEntropy (r / N') - subcriticalLogOddsNat k * r ≤
      (-subcriticalLogOddsNat k + subcriticalRowErrorNat k alpha zeta) * N := by
  have h := subcriticalLocalEntropy_high_row_le_of_scale_error hk ha haQuarter hr hrN hhigh hscale
  have hA := (subcriticalLocalA_Nat_pos hk).le
  have he : subcriticalHighRowErrorNat k alpha +
      (subcriticalLogOddsNat k + subcriticalHighRowErrorNat k alpha) * zeta ≤
        subcriticalRowErrorNat k alpha zeta := by
    unfold subcriticalRowErrorNat
    nlinarith
  exact h.trans (mul_le_mul_of_nonneg_right (by
    dsimp [subcriticalHighRowErrorNat] at he
    linarith) hN)

/-- Finite entropy bookkeeping with a distinguished subset of high rows.
No sign is assumed for a row contribution or its high-row upper bound. -/
theorem subcriticalEntropySum_le_high_improvement
    {ι : Type*} [DecidableEq ι] {k : ℕ} (hk : 3 ≤ k)
    (S H : Finset ι) (hHS : H ⊆ S) (f : ι → ℝ) (N E : ℝ)
    (hrow : ∀ a ∈ S, f a ≤ (subcriticalLocalA_Nat k + E) * N)
    (hhigh : ∀ a ∈ H, f a ≤ (-subcriticalLogOddsNat k + E) * N) :
    ∑ a ∈ S, f a ≤
      (subcriticalLocalA_Nat k * S.card - subcriticalLocalU_Nat k * H.card +
        E * S.card) * N := by
  have hM := Finset.sum_le_sum (s := S \ H) (fun a ha ↦ hrow a (Finset.mem_sdiff.mp ha).1)
  have hH := Finset.sum_le_sum hhigh
  have hcard : ((S \ H).card : ℝ) + H.card = S.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hHS
  have h := add_le_add hM hH
  rw [Finset.sum_sdiff hHS] at h
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  have heq : ((S \ H).card : ℝ) * ((subcriticalLocalA_Nat k + E) * N) +
      H.card * ((-subcriticalLogOddsNat k + E) * N) =
      (subcriticalLocalA_Nat k * S.card - subcriticalLocalU_Nat k * H.card +
        E * S.card) * N := by
    rw [← hcard, subcriticalLocalU_Nat_eq_L_add_A hk]
    ring
  exact h.trans_eq heq

/-- Degree-bounded companion multiplicity cancels the entire leading
external entropy, leaving only the explicitly counted row error. -/
theorem subcriticalExternalEntropySum_le_error
    {ι : Type*} [DecidableEq ι] {k : ℕ} (hk : 3 ≤ k)
    (S H : Finset ι) (hHS : H ⊆ S) (f : ι → ℝ) {N E : ℝ}
    (hN : 0 ≤ N) (hcomp : (S \ H).card ≤ (k - 2) * H.card)
    (hrow : ∀ a ∈ S, f a ≤ (subcriticalLocalA_Nat k + E) * N)
    (hhigh : ∀ a ∈ H, f a ≤ (-subcriticalLogOddsNat k + E) * N) :
    ∑ a ∈ S, f a ≤ E * S.card * N := by
  have h := subcriticalEntropySum_le_high_improvement hk S H hHS f N E hrow hhigh
  have hc : (S.card : ℝ) ≤ ((k - 2 : ℕ) : ℝ) * H.card + H.card := by
    have hsum := Finset.card_sdiff_add_card_eq_card hHS
    exact_mod_cast (show S.card ≤ (k - 2) * H.card + H.card by omega)
  have hA := (subcriticalLocalA_Nat_pos hk).le
  have hL := subcriticalLogOddsNat_eq_delta_mul_A hk
  have hU := subcriticalLocalU_Nat_eq_L_add_A hk
  have hlead : subcriticalLocalA_Nat k * S.card - subcriticalLocalU_Nat k * H.card ≤ 0 := by
    nlinarith
  calc
    _ ≤ (subcriticalLocalA_Nat k * S.card - subcriticalLocalU_Nat k * H.card +
        E * S.card) * N := h
    _ ≤ (0 + E * S.card) * N := mul_le_mul_of_nonneg_right (by linarith) hN
    _ = _ := by ring

/-- A nonempty high-row subset and the stronger sparse retained-row budget
give a full `A*N` leading saving, before the finite row error. -/
theorem subcriticalOutsideEntropySum_le_negative
    {ι : Type*} [DecidableEq ι] {k : ℕ} (hk : 3 ≤ k)
    (S H : Finset ι) (hHS : H ⊆ S) (hH : H.Nonempty) (f : ι → ℝ) {N E : ℝ}
    (hN : 0 ≤ N) (hcard : S.card ≤ k - 2)
    (hrow : ∀ a ∈ S, f a ≤ (subcriticalLocalA_Nat k + E) * N)
    (hhigh : ∀ a ∈ H, f a ≤ (-subcriticalLogOddsNat k + E) * N) :
    ∑ a ∈ S, f a ≤ (-subcriticalLocalA_Nat k + E * S.card) * N := by
  have h := subcriticalEntropySum_le_high_improvement hk S H hHS f N E hrow hhigh
  have hc : (S.card : ℝ) ≤ ((k - 2 : ℕ) : ℝ) := by exact_mod_cast hcard
  have hh : (1 : ℝ) ≤ H.card := by exact_mod_cast hH.card_pos
  have hA := (subcriticalLocalA_Nat_pos hk).le
  have hUpos := (subcriticalLocalU_Nat_pos hk).le
  have hL := subcriticalLogOddsNat_eq_delta_mul_A hk
  have hU := subcriticalLocalU_Nat_eq_L_add_A hk
  have hlead : subcriticalLocalA_Nat k * S.card - subcriticalLocalU_Nat k * H.card ≤
      -subcriticalLocalA_Nat k := by nlinarith
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hN)

end InducedStars
