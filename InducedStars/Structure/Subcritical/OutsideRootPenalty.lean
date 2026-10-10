import InducedStars.Structure.Subcritical.ExternalRows
import InducedStars.Structure.Subcritical.SparseRowBudget

/-!
# Finite outside-root compensation

Paper: Lemma `lemma:local-compensation-K1k`. The sparse retained-row
budget makes the full-degree component deficit positive in each nonempty
row component. The shared component estimate then leaves one full `A` of
leading entropy, before the explicit balance and root-trimming errors.
-/

noncomputable section
open Finset
open scoped Classical BigOperators

namespace InducedStars

variable {k n R₀ : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
  {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
  {omega eta theta alpha delta epsilon rho : ℝ}

theorem RealizesSubcriticalProfile.outside_rows_nonempty
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    (v : Fin n) (hv : v ∈ p.outsideRoots) :
    (subcriticalProfileRowIndices p v).Nonempty := by
  have hb : v ∈ subcriticalBadOutsideRoots G D eta R₀ theta alpha := by
    rwa [← h.outside_roots]
  obtain ⟨_, a, ha, hrow⟩ := (mem_subcriticalBadOutsideRoots G D eta R₀ theta alpha v).mp hb
  exact ⟨a, (h.outside_row_iff v hv a).mpr ⟨ha, hrow⟩⟩

/-- The stronger sparse row bound applies to the entire recorded row set,
not merely to one component. -/
theorem RealizesSubcriticalProfile.outside_rows_card_le
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    (halpha : 0 ≤ alpha)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hbudget : SubcriticalSparseRetainedRowBudget G D eta theta alpha R₀)
    (v : Fin n) (hv : v ∈ p.outsideRoots) :
    (subcriticalProfileRowIndices p v).card ≤ k - 2 := by
  have hb : v ∈ subcriticalBadOutsideRoots G D eta R₀ theta alpha := by
    rwa [← h.outside_roots]
  obtain ⟨hvn, hr⟩ := (mem_subcriticalBadOutsideRoots G D eta R₀ theta alpha v).mp hb
  apply (Finset.card_le_card (show subcriticalProfileRowIndices p v ⊆
    subcriticalNonlowVisibleParts G D alpha theta v ∩ D.retainedPartIndices eta R₀ from ?_)).trans
      (hbudget v hvn hr).2.2
  intro a ha
  obtain ⟨har, hd⟩ := (h.outside_row_iff v hv a).mp ha
  refine Finset.mem_inter.mpr ⟨(mem_subcriticalNonlowVisibleParts G D alpha theta v a).mpr
    ⟨hret har, ?_⟩, har⟩
  have hz : (0 : ℝ) ≤ alpha * (D.part a).card := mul_nonneg halpha (Nat.cast_nonneg _)
  linarith

theorem subcriticalOutsideRootLocalExponent_eq_sum_components
    (p : SubcriticalProfile D eta R₀ theta) (m : ℕ) (C alpha delta epsilon : ℝ)
    (v : Fin n) (hv : v ∈ p.outsideRoots) :
    subcriticalProfileLocalExponent p m C alpha delta epsilon v =
      ∑ i : Fin D.componentCount, subcriticalComponentRowEntropyNat p v i := by
  have hnret : v ∉ p.retainedRoots := fun hr ↦ Finset.disjoint_left.mp p.roots_disjoint hr hv
  simp only [subcriticalProfileLocalExponent, subcriticalProfileRootEntropyNat,
    subcriticalProfileOwnMissingEntropyNat, hnret, ↓reduceDIte,
    subcriticalProfileRootTailPenalty, false_and, ↓reduceIte, add_zero, sub_zero]
  rw [subcriticalProfilePresentRowEntropyNat_sum_eq_rows, subcriticalProfileRows_sum_components]

/-- Finite outside-root penalty using the already-proved deterministic
sparse row budget. No probability or entropy conclusion is assumed.
The error is exactly the shared balance-plus-trimming row error. -/
theorem subcriticalOutsideRootCompensation_of_rowBudget
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hR₀ : 1 ≤ R₀) (heta : 0 ≤ eta) (homega : omega ≤ 1)
    (halpha : 0 < alpha) (halphaFifth : 5 * alpha ≤ 1) (htheta : 0 < theta)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hn : 0 < n) (hscale : 8 ≤ alpha * theta * n)
    (hrho : 0 ≤ rho) (hrhoTrim : 4 * rho ≤ theta)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hbudget : SubcriticalSparseRetainedRowBudget G D eta theta alpha R₀)
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    (hB : (p.roots.card : ℝ) ≤ rho * n)
    (herror : ((k - 1 : ℕ) : ℝ) * subcriticalRowErrorNat k alpha
      (subcriticalInsideScaleErrorNat alpha delta theta n + subcriticalTrimErrorNat rho theta) ≤
        subcriticalLocalA_Nat k / 2)
    (m : ℕ) (C : ℝ) (v : Fin n) (hv : v ∈ p.outsideRoots) :
    subcriticalProfileLocalExponent p m C alpha delta epsilon v ≤
      -(subcriticalLocalA_Nat k * eta * n / (8 * (R₀ : ℝ))) := by
  let zeta := subcriticalInsideScaleErrorNat alpha delta theta n + subcriticalTrimErrorNat rho theta
  let E := subcriticalRowErrorNat k alpha zeta
  have ha4 : alpha ≤ 1 / 4 := by linarith
  have hz : 0 ≤ zeta := by
    dsimp [zeta, subcriticalInsideScaleErrorNat, subcriticalTrimErrorNat]
    positivity
  have hE : 0 ≤ E := subcriticalRowErrorNat_nonneg hk halpha.le ha4 hz
  have hA : 0 < subcriticalLocalA_Nat k := subcriticalLocalA_Nat_pos hk
  have hRpos : (0 : ℝ) < R₀ := by exact_mod_cast (show 0 < R₀ by omega)
  have htrim (a : D.PartIndex) (ha : a ∈ D.visiblePartIndices theta) :
      2 * (p.roots.card : ℝ) ≤ (D.part a).card := by
    have hp := R.visible_part_card_ge_half homega a ha
    have hh := mul_le_mul_of_nonneg_right hrhoTrim (Nat.cast_nonneg n)
    linarith
  have hcard := h.outside_rows_card_le halpha.le hret hbudget v hv
  have hbad : v ∈ subcriticalBadOutsideRoots G D eta R₀ theta alpha := by
    rwa [← h.outside_roots]
  obtain ⟨hvn, hrow⟩ := (mem_subcriticalBadOutsideRoots G D eta R₀ theta alpha v).mp hbad
  have hnonlow := (hbudget v hvn hrow).2.2
  have hcomponent (i : Fin D.componentCount)
      (hne : (subcriticalComponentRows p v i).Nonempty) :
      subcriticalComponentRowEntropyNat p v i ≤
        -(subcriticalLocalA_Nat k * eta * n / (8 * (R₀ : ℝ))) := by
    obtain ⟨a, ha⟩ := hne
    obtain ⟨har, hai⟩ := (mem_subcriticalComponentRows p v i a).mp ha
    have haret := ((h.outside_row_iff v hv a).mp har).1
    have hiret : i ∈ D.retainedComponentIndices eta R₀ := by
      rw [← hai]
      exact (D.mem_retainedPartIndices eta R₀ a).mp haret
    have hivis : i ∈ D.visibleComponentIndices theta := by
      rw [← hai]
      exact (D.mem_visiblePartIndices theta a).mp (hret haret)
    have hcomp := subcriticalMediumTargets_high_companion R hfree homega halpha
      htheta hdelta hscale v i
    have hsupport : (subcriticalDensitySupport G D alpha theta v i).Nonempty := by
      refine ⟨a, subcriticalDensitySupport_mem_of_degree_gt G D v i a (hret haret) hai ?_⟩
      have hd := h.recorded_row_full_lower har
      have hapos : (0 : ℝ) < (D.part a).card := by exact_mod_cast (D.part_nonempty a).card_pos
      nlinarith [mul_pos halpha hapos]
    have hsupportCard : (subcriticalDensitySupport G D alpha theta v i).card ≤ k - 2 := by
      apply (Finset.card_le_card (show subcriticalDensitySupport G D alpha theta v i ⊆
        subcriticalNonlowVisibleParts G D alpha theta v ∩ D.retainedPartIndices eta R₀ from ?_)).trans hnonlow
      intro b hb
      refine Finset.mem_inter.mpr ⟨subcriticalDensitySupport_subset_nonlow G D
        (by linarith : alpha ≤ 1 / 2) v i hb, ?_⟩
      have hbi : b.1 = i := by
        rcases Finset.mem_union.mp hb with hb | hb
        · exact ((mem_subcriticalHighTargets G D alpha theta v i b).mp hb).2.1
        · exact ((mem_subcriticalMediumTargets G D alpha theta v i b).mp hb).2.1
      exact (D.mem_retainedPartIndices eta R₀ b).mpr (hbi ▸ hiret)
    have hdeficit := subcriticalTargetDeficit_pos_of_support_card_le G D alpha theta
      v i hcomp hsupport hsupportCard
    have hdeficitR : (1 : ℝ) ≤ (subcriticalTargetDeficit G D alpha theta v i : ℝ) := by
      exact_mod_cast hdeficit
    have hci : (subcriticalComponentRows p v i).card ≤ k - 2 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans hcard
    have hhFull := subcriticalComponentRowEntropy_le_fullDeficit hk p h v i
      halpha halphaFifth (Nat.cast_nonneg (D.part a).card) hz hret
      (fun b hbi ↦ htrim b ((D.mem_visiblePartIndices theta b).mpr (hbi ▸ hivis)))
      (fun b hbi ↦ Or.inr ⟨hv, (D.mem_retainedPartIndices eta R₀ b).mpr (hbi ▸ hiret)⟩)
      (fun b hb ↦ ?_)
    · have hh : subcriticalComponentRowEntropyNat p v i ≤
          (-subcriticalLocalA_Nat k + subcriticalRowErrorNat k alpha zeta *
            (subcriticalComponentRows p v i).card) * (D.part a).card := by
        apply hhFull.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
        nlinarith [mul_le_mul_of_nonneg_left hdeficitR hA.le]
      have hciR : ((subcriticalComponentRows p v i).card : ℝ) ≤ (k - 1 : ℕ) := by
        exact_mod_cast (show (subcriticalComponentRows p v i).card ≤ k - 1 by omega)
      have hEi : E * (subcriticalComponentRows p v i).card ≤ subcriticalLocalA_Nat k / 2 := by
        have hh := mul_le_mul_of_nonneg_left hciR hE
        dsimp [E, zeta] at hh ⊢
        linarith
      have hsize := R.retainedPart_card_lower_bound hR₀ heta haret
      have hhalf : subcriticalComponentRowEntropyNat p v i ≤
          -(subcriticalLocalA_Nat k / 2) * (D.part a).card := by
        dsimp [E, zeta] at hEi
        apply hh.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
        linarith
      have hstep := mul_le_mul_of_nonpos_left hsize (by linarith : -(subcriticalLocalA_Nat k / 2) ≤ 0)
      apply hhalf.trans (hstep.trans ?_)
      have hnon : 0 ≤ subcriticalLocalA_Nat k * eta * n := by positivity
      have heq : -(subcriticalLocalA_Nat k / 2) * (eta * n / (2 * (R₀ : ℝ))) =
          -(subcriticalLocalA_Nat k * eta * n / (4 * (R₀ : ℝ))) := by
        field_simp
        <;> ring
      rw [heq]
      apply neg_le_neg
      exact div_le_div_of_nonneg_left hnon (by positivity) (by nlinarith)
    · obtain ⟨hbr, hbi⟩ := (mem_subcriticalComponentRows p v i b).mp hb
      rcases a with ⟨ia, aa⟩
      rcases b with ⟨ib, bb⟩
      dsimp at hai hbi
      subst ia
      subst ib
      exact R.local_trimmed_visible_part_deviation homega halpha htheta hdelta0 hn
        hrho p hB i hivis aa bb
  have hnonpos (i : Fin D.componentCount) : subcriticalComponentRowEntropyNat p v i ≤ 0 := by
    by_cases hh : (subcriticalComponentRows p v i).Nonempty
    · exact (hcomponent i hh).trans (neg_nonpos.mpr (by positivity))
    · have he := Finset.not_nonempty_iff_eq_empty.mp hh
      simp only [subcriticalComponentRowEntropyNat, he, Finset.sum_empty, le_refl]
  obtain ⟨a, ha⟩ := h.outside_rows_nonempty v hv
  have hne : (subcriticalComponentRows p v a.1).Nonempty :=
    ⟨a, (mem_subcriticalComponentRows p v a.1 a).mpr ⟨ha, rfl⟩⟩
  rw [subcriticalOutsideRootLocalExponent_eq_sum_components p m C alpha delta epsilon v hv]
  have hs : ∑ i ∈ (Finset.univ : Finset (Fin D.componentCount)).erase a.1,
      subcriticalComponentRowEntropyNat p v i ≤ 0 := by
    exact (Finset.sum_le_sum (fun i _ ↦ hnonpos i)).trans_eq (Finset.sum_const_zero)
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin D.componentCount))
    (subcriticalComponentRowEntropyNat p v) (Finset.mem_univ a.1)
  linarith [hcomponent a.1 hne]

/-- Outside-root specialization of local compensation, the finite
geometric theorem. The flexible sparse-row parameter package is used at
its actual alpha, not at any earlier illustrative feasibility value.
The sparse retained-row bound is derived locally from minimality. -/
theorem subcriticalOutsideRootCompensation
    (P : SubcriticalSparseRowParameters k R₀ eta)
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta P.theta P.alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hminimal : ∀ E : SubcriticalDivision k (Fin n),
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (hR₀ : 1 ≤ R₀) (heta : 0 ≤ eta) (homega : omega ≤ 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hn : 0 < n) (hscale : 8 ≤ P.alpha * P.theta * n)
    (hcoreScale : 32 * (k : ℝ) ^ 3 ≤ P.theta * n)
    (hrho : 0 ≤ rho) (hrhoTrim : 4 * rho ≤ P.theta)
    {p : SubcriticalProfile D eta R₀ P.theta} (h : RealizesSubcriticalProfile G P.alpha p)
    (hB : (p.roots.card : ℝ) ≤ rho * n)
    (herror : ((k - 1 : ℕ) : ℝ) * subcriticalRowErrorNat k P.alpha
      (subcriticalInsideScaleErrorNat P.alpha delta P.theta n + subcriticalTrimErrorNat rho P.theta) ≤
        subcriticalLocalA_Nat k / 2)
    (m : ℕ) (C : ℝ) (v : Fin n) (hv : v ∈ p.outsideRoots) :
    subcriticalProfileLocalExponent p m C P.alpha delta epsilon v ≤
      -(subcriticalLocalA_Nat k * eta * n / (8 * (R₀ : ℝ))) := by
  have Crows := subcriticalRowConstraints_of_closeStructure hk R hfree homega
    P.alpha_pos P.theta_pos hdelta hscale
  have hbudget := subcriticalSparseRetainedRowBudget_of_closeStructure hk P R Crows hminimal
    hR₀ heta homega hcoreScale
  have hfifth : 5 * P.alpha ≤ 1 := by
    have hk1 : (2 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ k - 1 by omega)
    have hp := P.alpha_budget
    have hm := mul_le_mul_of_nonneg_left hk1 P.alpha_pos.le
    nlinarith
  exact subcriticalOutsideRootCompensation_of_rowBudget R hfree hR₀ heta homega
    P.alpha_pos hfifth P.theta_pos hdelta0 hdelta hn hscale hrho hrhoTrim
    (D.retainedPartIndices_subset_visiblePartIndices hR₀ P.theta_pos.le P.retained_visible)
    hbudget h hB herror m C v hv

end InducedStars
