import InducedStars.Structure.Subcritical.LocalEntropyErrors
import InducedStars.Structure.Subcritical.LocalRowCompanions
import InducedStars.Structure.Subcritical.LocalSupport

/-!
# Explicit component and total external-row entropy bounds

Paper: `eqn:local-component-deficit-K1k`. High-row companions are
actual core neighbors and their bounded fibers are proved separately.
Here the exact finite multiplicity cancels the leading entropy, leaving a
visible error per recorded row. The global sum is bounded at the root scale,
not by a sum of unquantified little-oh terms.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}

theorem subcriticalProfile_rowCount_le_trimmed
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (a : D.PartIndex) :
    p.rowCount v a ≤ (D.part a \ p.roots).card := by
  cases h : p.rows v a with
  | none => simp [SubcriticalProfile.rowCount, h]
  | some r =>
    simpa only [SubcriticalProfile.rowCount, h, Option.getD_some, SubcriticalProfile.roots]
      using (p.rows_valid v a r h).2

theorem subcriticalProfilePresentRowEntropyNat_eq_rowCount
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (a : D.PartIndex) :
    subcriticalProfilePresentRowEntropyNat p v a =
      (D.part a \ p.roots).card *
        Real.binEntropy ((p.rowCount v a : ℝ) / (D.part a \ p.roots).card) -
          subcriticalLogOddsNat k * p.rowCount v a := by
  cases h : p.rows v a <;>
    simp [subcriticalProfilePresentRowEntropyNat, SubcriticalProfile.rowCount, h]

theorem subcriticalProfilePresentRowEntropyNat_sum_eq_rows
    (p : SubcriticalProfile D eta R₀ theta) (v : V) :
    (∑ a : D.PartIndex, subcriticalProfilePresentRowEntropyNat p v a) =
      ∑ a ∈ subcriticalProfileRowIndices p v, subcriticalProfilePresentRowEntropyNat p v a := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  cases h : p.rows v a with
  | none => simp [subcriticalProfilePresentRowEntropyNat, h]
  | some r => exact (ha (by simp [subcriticalProfileRowIndices, h])).elim

/-- The natural entropy of all recorded targets in one actual component. -/
def subcriticalComponentRowEntropyNat
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (i : Fin D.componentCount) : ℝ :=
  ∑ a ∈ subcriticalComponentRows p v i, subcriticalProfilePresentRowEntropyNat p v a

/-- Explicit total external loss at a retained root's own-part scale. -/
def subcriticalExternalComponentErrorNat (k R₀ : ℕ) (eta alpha zeta : ℝ) : ℝ :=
  4 * R₀ / eta * (k - 1 : ℕ) * subcriticalRowErrorNat k alpha zeta

/-- The full-degree component deficit controls every admissible positive-row
component. Unrecorded medium targets only increase the upper bound. -/
theorem subcriticalComponentRowEntropy_le_fullDeficit
    {G : SimpleGraph V} (hk : 3 ≤ k) {alpha : ℝ}
    (p : SubcriticalProfile D eta R₀ theta) (hp : RealizesSubcriticalProfile G alpha p)
    (v : V) (i : Fin D.componentCount) {N zeta : ℝ}
    (ha : 0 < alpha) (ha5 : 5 * alpha ≤ 1) (hN : 0 ≤ N) (hz : 0 ≤ zeta)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (htrim : ∀ a : D.PartIndex, a.1 = i → 2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (hallowed : ∀ a : D.PartIndex, a.1 = i →
      (v ∈ p.retainedRoots ∧ D.EligibleProfileTarget eta R₀ theta v a) ∨
      (v ∈ p.outsideRoots ∧ a ∈ D.retainedPartIndices eta R₀))
    (hscale : ∀ a ∈ subcriticalComponentRows p v i,
      |((D.part a \ p.roots).card : ℝ) - N| ≤ zeta * N) :
    subcriticalComponentRowEntropyNat p v i ≤
      (-subcriticalLocalA_Nat k * (subcriticalTargetDeficit G D alpha theta v i : ℝ) +
        subcriticalRowErrorNat k alpha zeta * (subcriticalComponentRows p v i).card) * N := by
  let H := subcriticalHighTargets G D alpha theta v i
  let M := subcriticalMediumTargets G D alpha theta v i
  let S := subcriticalComponentRows p v i
  have hH : ∀ a ∈ H, a ∈ S ∧
      (1 - 2 * alpha) * (D.part a \ p.roots).card ≤ (p.rowCount v a : ℝ) := by
    intro a hh
    obtain ⟨_, hai, hd⟩ := (mem_subcriticalHighTargets G D alpha theta v i a).mp hh
    obtain ⟨hr, hh⟩ := hp.high_allowed_recorded ha.le ha5 (htrim a hai) (hallowed a hai) hd
    exact ⟨(mem_subcriticalComponentRows p v i a).mpr ⟨hr, hai⟩, hh⟩
  have hS : S ⊆ H ∪ M := by
    intro a hs
    obtain ⟨hr, hai⟩ := (mem_subcriticalComponentRows p v i a).mp hs
    have hd := hp.recorded_row_full_lower hr
    have hn : (0 : ℝ) < (D.part a).card := by exact_mod_cast (D.part_nonempty a).card_pos
    exact subcriticalDensitySupport_mem_of_degree_gt G D v i a
      (hp.recorded_row_visible hret hr) hai (by nlinarith [mul_pos ha hn])
  have hcard : (S.card : ℝ) ≤ H.card + M.card := by
    have hc := Finset.card_le_card hS
    rw [Finset.card_union_of_disjoint (subcriticalHighMediumTargets_disjoint G D alpha theta v i)] at hc
    exact_mod_cast hc
  have he := subcriticalEntropySum_le_high_improvement hk S H
    (fun a ha ↦ (hH a ha).1) (subcriticalProfilePresentRowEntropyNat p v) N
    (subcriticalRowErrorNat k alpha zeta) (by
      intro a haS
      rw [subcriticalProfilePresentRowEntropyNat_eq_rowCount]
      exact subcriticalLocalEntropy_row_le_with_error hk ha.le (by linarith) hN hz
        (Nat.cast_nonneg _) (by exact_mod_cast subcriticalProfile_rowCount_le_trimmed p v a)
        (hscale a haS)) (by
      intro a haH
      rw [subcriticalProfilePresentRowEntropyNat_eq_rowCount]
      exact subcriticalLocalEntropy_high_row_le_with_error hk ha.le (by linarith) hN hz
        (Nat.cast_nonneg _) (by exact_mod_cast subcriticalProfile_rowCount_le_trimmed p v a)
        (hH a haH).2 (hscale a (hH a haH).1))
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ hN
  have hc := mul_le_mul_of_nonneg_left hcard (subcriticalLocalA_Nat_pos hk).le
  simp only [subcriticalTargetDeficit, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  rw [subcriticalLocalU_Nat_eq_L_add_A hk, subcriticalLogOddsNat_eq_delta_mul_A hk]
  change subcriticalLocalA_Nat k * S.card -
    (((k - 2 : ℕ) : ℝ) * subcriticalLocalA_Nat k + subcriticalLocalA_Nat k) * H.card +
    subcriticalRowErrorNat k alpha zeta * S.card ≤
    -subcriticalLocalA_Nat k * (((k - 2 : ℕ) : ℝ) * H.card - M.card) +
    subcriticalRowErrorNat k alpha zeta * S.card
  nlinarith only [hc]

/-- Generic finite component estimate. The companion hypothesis is an
exact cardinality statement, not an assumed entropy or probability bound. -/
theorem subcriticalComponentRowEntropy_le_error
    (hk : 3 ≤ k) (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (i : Fin D.componentCount) {alpha N zeta : ℝ}
    (ha : 0 ≤ alpha) (haQuarter : alpha ≤ 1 / 4) (hN : 0 ≤ N) (hz : 0 ≤ zeta)
    (hscale : ∀ a ∈ subcriticalComponentRows p v i,
      |((D.part a \ p.roots).card : ℝ) - N| ≤ zeta * N)
    (hcomp : (subcriticalComponentMediumRows p alpha v i).card ≤
      (k - 2) * (subcriticalComponentHighRows p alpha v i).card) :
    subcriticalComponentRowEntropyNat p v i ≤
      subcriticalRowErrorNat k alpha zeta * (subcriticalComponentRows p v i).card * N := by
  apply subcriticalExternalEntropySum_le_error hk (subcriticalComponentRows p v i)
    (subcriticalComponentHighRows p alpha v i) (Finset.filter_subset _ _)
    (subcriticalProfilePresentRowEntropyNat p v) hN hcomp
  · intro a haS
    rw [subcriticalProfilePresentRowEntropyNat_eq_rowCount]
    exact subcriticalLocalEntropy_row_le_with_error hk ha haQuarter hN hz
      (Nat.cast_nonneg _) (by exact_mod_cast subcriticalProfile_rowCount_le_trimmed p v a)
      (hscale a haS)
  · intro a haH
    obtain ⟨haS, hahigh⟩ := (mem_subcriticalComponentHighRows p alpha v i a).mp haH
    rw [subcriticalProfilePresentRowEntropyNat_eq_rowCount]
    exact subcriticalLocalEntropy_high_row_le_with_error hk ha haQuarter hN hz
      (Nat.cast_nonneg _) (by exact_mod_cast subcriticalProfile_rowCount_le_trimmed p v a)
      hahigh (hscale a haS)

/-- A nonempty high subset under the sparse retained-row budget gives a
strict leading component saving, with the full row error still visible. -/
theorem subcriticalComponentRowEntropy_le_negative
    (hk : 3 ≤ k) (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (i : Fin D.componentCount) {alpha N zeta : ℝ}
    (ha : 0 ≤ alpha) (haQuarter : alpha ≤ 1 / 4) (hN : 0 ≤ N) (hz : 0 ≤ zeta)
    (hscale : ∀ a ∈ subcriticalComponentRows p v i,
      |((D.part a \ p.roots).card : ℝ) - N| ≤ zeta * N)
    (hhigh : (subcriticalComponentHighRows p alpha v i).Nonempty)
    (hcard : (subcriticalComponentRows p v i).card ≤ k - 2) :
    subcriticalComponentRowEntropyNat p v i ≤
      (-subcriticalLocalA_Nat k + subcriticalRowErrorNat k alpha zeta *
        (subcriticalComponentRows p v i).card) * N := by
  apply subcriticalOutsideEntropySum_le_negative hk (subcriticalComponentRows p v i)
    (subcriticalComponentHighRows p alpha v i) (Finset.filter_subset _ _) hhigh
    (subcriticalProfilePresentRowEntropyNat p v) hN hcard
  · intro a haS
    rw [subcriticalProfilePresentRowEntropyNat_eq_rowCount]
    exact subcriticalLocalEntropy_row_le_with_error hk ha haQuarter hN hz
      (Nat.cast_nonneg _) (by exact_mod_cast subcriticalProfile_rowCount_le_trimmed p v a)
      (hscale a haS)
  · intro a haH
    obtain ⟨haS, hahigh⟩ := (mem_subcriticalComponentHighRows p alpha v i a).mp haH
    rw [subcriticalProfilePresentRowEntropyNat_eq_rowCount]
    exact subcriticalLocalEntropy_high_row_le_with_error hk ha haQuarter hN hz
      (Nat.cast_nonneg _) (by exact_mod_cast subcriticalProfile_rowCount_le_trimmed p v a)
      hahigh (hscale a haS)

/-- Exact decomposition by target component, including empty fibers. -/
theorem subcriticalProfileRows_sum_components
    (p : SubcriticalProfile D eta R₀ theta) (v : V) :
    (∑ a ∈ subcriticalProfileRowIndices p v, subcriticalProfilePresentRowEntropyNat p v a) =
      ∑ i : Fin D.componentCount, subcriticalComponentRowEntropyNat p v i := by
  exact (Finset.sum_fiberwise_of_maps_to (g := fun a : D.PartIndex ↦ a.1)
    (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _) _).symm

/-- Exact external-row sum, without introducing an own part for an
outside root. This statement is only for a retained root. -/
theorem subcriticalProfileOutsideRows_sum_components
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots) :
    (∑ a ∈ subcriticalProfileOutsideRows p v hv, subcriticalProfilePresentRowEntropyNat p v a) =
      ∑ i ∈ Finset.univ.filter
        (fun i ↦ i ≠ (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1),
          subcriticalComponentRowEntropyNat p v i := by
  have h := Finset.sum_fiberwise_eq_sum_filter (subcriticalProfileRowIndices p v)
    (Finset.univ.filter
      (fun i ↦ i ≠ (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1))
    (fun a : D.PartIndex ↦ a.1) (subcriticalProfilePresentRowEntropyNat p v)
  have he : (subcriticalProfileRowIndices p v).filter
      (fun a ↦ a.1 ∈ Finset.univ.filter
        (fun i ↦ i ≠ (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1)) =
      subcriticalProfileOutsideRows p v hv := by ext a; simp
  rw [he] at h
  exact h.symm

/-- Componentwise external losses can be summed against the actual number
of recorded rows. No ambient number of components enters the error. -/
theorem subcriticalExternalRowEntropy_sum_le
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots)
    {E n : ℝ}
    (hcomponent : ∀ i : Fin D.componentCount,
      i ≠ (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1 →
      subcriticalComponentRowEntropyNat p v i ≤ E * (subcriticalComponentRows p v i).card * n) :
    (∑ a ∈ subcriticalProfileOutsideRows p v hv, subcriticalProfilePresentRowEntropyNat p v a) ≤
      E * (subcriticalProfileOutsideRows p v hv).card * n := by
  rw [subcriticalProfileOutsideRows_sum_components]
  have hsum := Finset.sum_le_sum (s := Finset.univ.filter
    (fun i ↦ i ≠ (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1))
    (fun i hi ↦ hcomponent i (Finset.mem_filter.mp hi).2)
  have hcard : (∑ i ∈ Finset.univ.filter
      (fun i ↦ i ≠ (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1),
      (subcriticalComponentRows p v i).card) = (subcriticalProfileOutsideRows p v hv).card := by
    have h := Finset.sum_card_fiberwise_eq_card_filter (subcriticalProfileRowIndices p v)
      (Finset.univ.filter
        (fun i ↦ i ≠ (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1))
      (fun a : D.PartIndex ↦ a.1)
    have he : (subcriticalProfileRowIndices p v).filter
        (fun a ↦ a.1 ∈ Finset.univ.filter
          (fun i ↦ i ≠ (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1)) =
        subcriticalProfileOutsideRows p v hv := by ext a; simp
    rw [he] at h
    exact h
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter
        (fun i ↦ i ≠ (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1),
        E * (subcriticalComponentRows p v i).card * n := hsum
    _ = E * (subcriticalProfileOutsideRows p v hv).card * n := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← Nat.cast_sum, hcard]

section Finite
variable {n : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
  {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
  {omega eta theta alpha delta epsilon rho : ℝ} {R₀ : ℕ}

/-- The actual aligned visible part sizes, including the exact root trim.
The `8/(theta*n)` term is the finite rounding loss of the alignment. -/
theorem SubcriticalCloseStructureResult.local_trimmed_visible_part_deviation
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hdelta : 0 ≤ delta) (hn : 0 < n) (hrho : 0 ≤ rho)
    (p : SubcriticalProfile D eta R₀ theta) (hB : (p.roots.card : ℝ) ≤ rho * n)
    (i : Fin D.componentCount) (hi : i ∈ D.visibleComponentIndices theta)
    (a b : Fin (D.core i).order) :
    |((D.parts i b \ p.roots).card : ℝ) - (D.parts i a).card| ≤
      (subcriticalInsideScaleErrorNat alpha delta theta n +
        subcriticalTrimErrorNat rho theta) * (D.parts i a).card := by
  exact subcriticalLocal_trimmed_size_deviation (D.parts i b) p.roots htheta hrho
    (R.visible_part_card_ge_half homega ⟨i, a⟩ ((D.mem_visiblePartIndices theta _).mpr hi))
    hB (R.local_visible_part_size_deviation homega halpha htheta hdelta hn i hi a b)

/-- Paper: `eqn:local-component-deficit-K1k`, with a concrete
uniform error and an arbitrary comparison part in the external component.
The actual high companion map is derived from the realized graph. The
full-degree deficit is nonnegative, leaving the finite balance and trim error. -/
theorem subcriticalExternalComponentEntropy
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (ha : alpha ≤ 1 / 5)
    (htheta : 0 < theta) (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ subcriticalRowCountingTolerance k) (hn : 0 < n)
    (hscale : 8 ≤ alpha * theta * n) (hrho : 0 ≤ rho)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (hp : RealizesSubcriticalProfile G alpha p)
    (hB : (p.roots.card : ℝ) ≤ rho * n)
    (v : Fin n) (hv : v ∈ p.retainedRoots) (i : Fin D.componentCount)
    (hi : i ∈ D.visibleComponentIndices theta)
    (hio : i ≠ (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1)
    (htrim : ∀ a : D.PartIndex, a.1 = i → 2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (a : Fin (D.core i).order) :
    subcriticalComponentRowEntropyNat p v i ≤
      subcriticalRowErrorNat k alpha
        (subcriticalInsideScaleErrorNat alpha delta theta n +
          subcriticalTrimErrorNat rho theta) *
        (subcriticalComponentRows p v i).card * (D.parts i a).card := by
  have hz : 0 ≤ subcriticalInsideScaleErrorNat alpha delta theta n +
      subcriticalTrimErrorNat rho theta := by
    unfold subcriticalInsideScaleErrorNat subcriticalTrimErrorNat
    positivity
  have hh := subcriticalComponentRowEntropy_le_fullDeficit hk p hp v i halpha (by linarith)
    (Nat.cast_nonneg (D.parts i a).card) hz hret htrim
    (subcriticalExternalComponent_targets_allowed p v hv i hi hio) (by
      intro b hb
      have hbi := ((mem_subcriticalComponentRows p v i b).mp hb).2
      rcases b with ⟨ib, b⟩
      dsimp at hbi
      subst ib
      exact R.local_trimmed_visible_part_deviation homega halpha htheta hdelta0 hn
        hrho p hB i hi a b)
  have hD := subcriticalTargetDeficit_nonneg G D alpha theta v i
    (subcriticalMediumTargets_high_companion R hfree homega halpha htheta hdelta hscale v i)
  have hDr : (0 : ℝ) ≤ (subcriticalTargetDeficit G D alpha theta v i : ℝ) := by
    exact_mod_cast hD
  have hloss := mul_nonneg (subcriticalLocalA_Nat_pos hk).le hDr
  apply hh.trans
  nlinarith only [mul_nonneg hloss (Nat.cast_nonneg (D.parts i a).card)]

/-- The complete sum of external rows, at the retained root scale. The
factor `4*R₀/eta` is explicit and the number of rows is at most `k-1`. -/
theorem subcriticalExternalRowsEntropy
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (ha : alpha ≤ 1 / 5)
    (htheta : 0 < theta) (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ subcriticalRowCountingTolerance k) (hn : 0 < n)
    (hscale : 8 ≤ alpha * theta * n) (hrho : 0 ≤ rho)
    (hR : 1 ≤ R₀) (heta : 0 < eta)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (hp : RealizesSubcriticalProfile G alpha p)
    (hB : (p.roots.card : ℝ) ≤ rho * n)
    (htrim : ∀ a ∈ D.visiblePartIndices theta, 2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (v : Fin n) (hv : v ∈ p.retainedRoots) :
    (∑ a ∈ subcriticalProfileOutsideRows p v hv, subcriticalProfilePresentRowEntropyNat p v a) ≤
      subcriticalExternalComponentErrorNat k R₀ eta alpha
        (subcriticalInsideScaleErrorNat alpha delta theta n + subcriticalTrimErrorNat rho theta) *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card := by
  let zeta := subcriticalInsideScaleErrorNat alpha delta theta n + subcriticalTrimErrorNat rho theta
  let E := subcriticalRowErrorNat k alpha zeta
  have hz : 0 ≤ zeta := by
    dsimp [zeta, subcriticalInsideScaleErrorNat, subcriticalTrimErrorNat]
    positivity
  have hE : 0 ≤ E := subcriticalRowErrorNat_nonneg hk halpha.le (by linarith) hz
  have hcomp : ∀ i : Fin D.componentCount,
      i ≠ (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1 →
      subcriticalComponentRowEntropyNat p v i ≤ E * (subcriticalComponentRows p v i).card * n := by
    intro i hio
    by_cases hi : i ∈ D.visibleComponentIndices theta
    · let a : Fin (D.core i).order := ⟨0, (D.core i).order_pos⟩
      have h := subcriticalExternalComponentEntropy R hfree homega halpha ha htheta hdelta0
        hdelta hn hscale hrho hret hp hB v hv i hi hio (fun b hb ↦
          htrim b ((D.mem_visiblePartIndices theta b).mpr (hb ▸ hi))) a
      exact h.trans (mul_le_mul_of_nonneg_left
        (by exact_mod_cast (show (D.parts i a).card ≤ n by
          simpa using Finset.card_le_univ (D.parts i a)) : ((D.parts i a).card : ℝ) ≤ n)
        (mul_nonneg hE (Nat.cast_nonneg _)))
    · have he : subcriticalComponentRows p v i = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        obtain ⟨har, hai⟩ := (mem_subcriticalComponentRows p v i a).mp ha
        have hvis := (D.mem_visiblePartIndices theta a).mp (hp.recorded_row_visible hret har)
        exact hi (hai ▸ hvis)
      simp [subcriticalComponentRowEntropyNat, he]
  have hsum := subcriticalExternalRowEntropy_sum_le p v hv hcomp
  have hc : ((subcriticalProfileOutsideRows p v hv).card : ℝ) ≤ (k - 1 : ℕ) := by
    have hh := (subcriticalLocalNonlowBudget R hfree homega halpha (by linarith) htheta
      hdelta hscale hret hp v hv).1
    exact_mod_cast (show (subcriticalProfileOutsideRows p v hv).card ≤ k - 1 by omega)
  have hsize := R.retainedPart_card_lower_bound hR heta.le
    (D.retainedVertexPart_mem_retained eta R₀ v (p.retainedRoots_subset hv))
  have hRpos : (0 : ℝ) < R₀ := by exact_mod_cast (show 0 < R₀ by omega)
  have hnN : (n : ℝ) ≤ 4 * R₀ / eta *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card := by
    have hmul := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * R₀)).mp hsize
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ heta).mpr
    have hP : (0 : ℝ) ≤ (D.part (D.retainedVertexPart eta R₀ v
      (p.retainedRoots_subset hv))).card := Nat.cast_nonneg _
    nlinarith
  calc
    _ ≤ E * (subcriticalProfileOutsideRows p v hv).card * n := hsum
    _ ≤ E * (k - 1 : ℕ) * n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hE) (Nat.cast_nonneg _)
    _ ≤ E * (k - 1 : ℕ) * (4 * R₀ / eta *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card) :=
      mul_le_mul_of_nonneg_left hnN (mul_nonneg hE (Nat.cast_nonneg _))
    _ = _ := by unfold subcriticalExternalComponentErrorNat; dsimp [E, zeta]; ring

end Finite

end InducedStars
