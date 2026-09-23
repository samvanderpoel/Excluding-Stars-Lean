import InducedStars.Structure.Subcritical.LocalNonlow
import InducedStars.Structure.Subcritical.ProfileRootEnergy
import InducedStars.Structure.Subcritical.DeterministicRows

/-!
# Actual medium-row companions and their finite multiplicities

Paper: the companion steps in `claim:external-component-ent-K1k` and
the local root-penalty proofs. The medium/high partition retains every
recorded row, including `some 0`; realization and finite trimming, not a
change of the profile data, provide the full-target degree bounds.
-/

noncomputable section
open Finset
open scoped Classical BigOperators

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}

def subcriticalComponentRows (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (i : Fin D.componentCount) : Finset D.PartIndex :=
  (subcriticalProfileRowIndices p v).filter fun a ↦ a.1 = i

def subcriticalComponentHighRows (p : SubcriticalProfile D eta R₀ theta)
    (alpha : ℝ) (v : V) (i : Fin D.componentCount) : Finset D.PartIndex :=
  (subcriticalComponentRows p v i).filter fun a ↦
    (1 - 2 * alpha) * (D.part a \ p.roots).card ≤ (p.rowCount v a : ℝ)

def subcriticalComponentMediumRows (p : SubcriticalProfile D eta R₀ theta)
    (alpha : ℝ) (v : V) (i : Fin D.componentCount) : Finset D.PartIndex :=
  subcriticalComponentRows p v i \ subcriticalComponentHighRows p alpha v i

@[simp] theorem mem_subcriticalComponentRows
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (i : Fin D.componentCount)
    (a : D.PartIndex) : a ∈ subcriticalComponentRows p v i ↔
      a ∈ subcriticalProfileRowIndices p v ∧ a.1 = i := by
  simp only [subcriticalComponentRows, Finset.mem_filter]

@[simp] theorem mem_subcriticalComponentHighRows
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V)
    (i : Fin D.componentCount) (a : D.PartIndex) :
    a ∈ subcriticalComponentHighRows p alpha v i ↔
      a ∈ subcriticalComponentRows p v i ∧
        (1 - 2 * alpha) * (D.part a \ p.roots).card ≤ (p.rowCount v a : ℝ) := by
  simp only [subcriticalComponentHighRows, Finset.mem_filter]

@[simp] theorem mem_subcriticalComponentMediumRows
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V)
    (i : Fin D.componentCount) (a : D.PartIndex) :
    a ∈ subcriticalComponentMediumRows p alpha v i ↔
      a ∈ subcriticalComponentRows p v i ∧
        (p.rowCount v a : ℝ) < (1 - 2 * alpha) * (D.part a \ p.roots).card := by
  simp only [subcriticalComponentMediumRows, Finset.mem_sdiff,
    mem_subcriticalComponentHighRows, not_and, not_le]
  tauto

theorem subcriticalComponentRows_partition
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V)
    (i : Fin D.componentCount) :
    subcriticalComponentMediumRows p alpha v i ∪ subcriticalComponentHighRows p alpha v i =
      subcriticalComponentRows p v i :=
  Finset.sdiff_union_of_subset (Finset.filter_subset _ _)

theorem subcriticalComponentRows_card_decomposition
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V)
    (i : Fin D.componentCount) :
    (subcriticalComponentMediumRows p alpha v i).card +
      (subcriticalComponentHighRows p alpha v i).card =
        (subcriticalComponentRows p v i).card := by
  rw [← Finset.card_union_of_disjoint disjoint_sdiff_self_left,
    subcriticalComponentRows_partition]

theorem subcriticalActivePart_symm {a b : D.PartIndex} (h : D.ActivePart a b) :
    D.ActivePart b a := by
  obtain ⟨i, u, v, rfl, rfl, h⟩ := h
  exact ⟨i, v, u, rfl, rfl, h.symm⟩

theorem RealizesSubcriticalProfile.rowCount_eq_degree_of_mem
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) {v : V} {a : D.PartIndex}
    (ha : a ∈ subcriticalProfileRowIndices p v) :
    p.rowCount v a = degreeInFinset G v (D.part a \ p.roots) := by
  cases he : p.rows v a with
  | none => simp [subcriticalProfileRowIndices, he] at ha
  | some r =>
    simpa only [SubcriticalProfile.rowCount, he, Option.getD_some] using
      h.row_count_eq_degree_of_some he

/-- Exact deletion bookkeeping, charging only vertices actually in the
target. This permits the half-target reserve in both high/medium adapters. -/
theorem subcriticalDegree_le_trimmed_add_inter (G : SimpleGraph V) (v : V)
    (Y B : Finset V) :
    degreeInFinset G v Y ≤ degreeInFinset G v (Y \ B) + (Y ∩ B).card := by
  have h := subcriticalDegree_le_sdiff_add_card G v Y (Y ∩ B)
  have he : Y \ (Y ∩ B) = Y \ B := by ext x; simp
  simpa only [he] using h

theorem subcriticalFullHigh_implies_trimmedHigh
    (G : SimpleGraph V) (v : V) (Y B : Finset V) (ha : 0 ≤ alpha)
    (htrim : 2 * (B.card : ℝ) ≤ Y.card)
    (hhigh : (1 - alpha) * Y.card ≤ (degreeInFinset G v Y : ℝ)) :
    (1 - 2 * alpha) * (Y \ B).card ≤ (degreeInFinset G v (Y \ B) : ℝ) := by
  have hd : (degreeInFinset G v Y : ℝ) ≤
      degreeInFinset G v (Y \ B) + (Y ∩ B).card := by
    exact_mod_cast subcriticalDegree_le_trimmed_add_inter G v Y B
  have hi : ((Y ∩ B).card : ℝ) ≤ B.card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : Y ∩ B ⊆ B)
  have he : ((Y \ B).card : ℝ) + (Y ∩ B).card = Y.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter Y B
  nlinarith

theorem subcriticalTrimmedMedium_implies_fullUpper
    (G : SimpleGraph V) (v : V) (Y B : Finset V) (ha : 0 ≤ alpha)
    (htrim : 2 * (B.card : ℝ) ≤ Y.card)
    (hmedium : (degreeInFinset G v (Y \ B) : ℝ) < (1 - 2 * alpha) * (Y \ B).card) :
    (degreeInFinset G v Y : ℝ) < (1 - alpha) * Y.card := by
  have hd : (degreeInFinset G v Y : ℝ) ≤
      degreeInFinset G v (Y \ B) + (Y ∩ B).card := by
    exact_mod_cast subcriticalDegree_le_trimmed_add_inter G v Y B
  have hi : ((Y ∩ B).card : ℝ) ≤ B.card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : Y ∩ B ⊆ B)
  have he : ((Y \ B).card : ℝ) + (Y ∩ B).card = Y.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter Y B
  nlinarith

theorem RealizesSubcriticalProfile.recorded_row_full_lower
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) {v : V} {a : D.PartIndex}
    (ha : a ∈ subcriticalProfileRowIndices p v) :
    4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ) := by
  cases he : p.rows v a with
  | none => simp [subcriticalProfileRowIndices, he] at ha
  | some r =>
    rcases (p.rows_valid v a r he).1 with hv | hv
    · exact ((h.retained_row_iff v hv.1 a).mp ha).2
    · exact ((h.outside_row_iff v hv.1 a).mp ha).2

theorem RealizesSubcriticalProfile.medium_recorded_full_degree
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) {v : V} {a : D.PartIndex}
    (ha : a ∈ subcriticalProfileRowIndices p v) (halpha : 0 ≤ alpha)
    (htrim : 2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (hmedium : (p.rowCount v a : ℝ) < (1 - 2 * alpha) * (D.part a \ p.roots).card) :
    alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ) ∧
      (degreeInFinset G v (D.part a) : ℝ) < (1 - alpha) * (D.part a).card := by
  have hlow := h.recorded_row_full_lower ha
  have hz : 0 ≤ alpha * ((D.part a).card : ℝ) := mul_nonneg halpha (Nat.cast_nonneg _)
  refine ⟨by linarith, ?_⟩
  rw [h.rowCount_eq_degree_of_mem ha] at hmedium
  exact subcriticalTrimmedMedium_implies_fullUpper G v (D.part a) p.roots halpha htrim hmedium

theorem RealizesSubcriticalProfile.recorded_row_visible
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {v : V} {a : D.PartIndex} (ha : a ∈ subcriticalProfileRowIndices p v) :
    a ∈ D.visiblePartIndices theta := by
  cases he : p.rows v a with
  | none => simp [subcriticalProfileRowIndices, he] at ha
  | some r =>
    rcases (p.rows_valid v a r he).1 with hv | hv
    · exact ((D.mem_eligibleVisibleTargets eta R₀ theta v
        (p.retainedRoots_subset hv.1) a).mp ((h.retained_row_iff v hv.1 a).mp ha).1).1
    · exact hret hv.2

theorem RealizesSubcriticalProfile.recorded_root_not_coreNeighborUnion
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) {v : V} {a : D.PartIndex}
    (ha : a ∈ subcriticalProfileRowIndices p v) :
    v ∉ subcriticalCoreNeighborUnion D a.1 a.2 := by
  intro hv
  obtain ⟨j, hj, hvj⟩ := (mem_subcriticalCoreNeighborUnion D a.1 a.2 v).mp hv
  cases he : p.rows v a with
  | none => simp [subcriticalProfileRowIndices, he] at ha
  | some r =>
    rcases (p.rows_valid v a r he).1 with hv | hv
    · have hna := ((D.mem_eligibleVisibleTargets eta R₀ theta v
        (p.retainedRoots_subset hv.1) a).mp ((h.retained_row_iff v hv.1 a).mp ha).1).2.2
      have hown := D.retainedVertexPart_eq_of_mem eta R₀ v (p.retainedRoots_subset hv.1)
        (a := ⟨a.1, j⟩) hvj
      apply hna
      rw [hown]
      exact ⟨a.1, j, a.2, rfl, rfl, hj.symm⟩
    · have hnj : (⟨a.1, j⟩ : D.PartIndex) ∈ D.retainedPartIndices eta R₀ := by
        simpa only [D.mem_retainedPartIndices] using hv.2
      have hvr := D.part_subset_retainedVertices hnj hvj
      have hvn := p.outsideRoots_subset hv.1
      simp only [SubcriticalDivision.nonretainedVertices, Finset.mem_sdiff,
        Finset.mem_univ, true_and] at hvn
      exact hvn hvr

theorem RealizesSubcriticalProfile.high_allowed_recorded
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) {v : V} {a : D.PartIndex}
    (halpha : 0 ≤ alpha) (halphaFifth : 5 * alpha ≤ 1)
    (htrim : 2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (hallowed : (v ∈ p.retainedRoots ∧ D.EligibleProfileTarget eta R₀ theta v a) ∨
      (v ∈ p.outsideRoots ∧ a ∈ D.retainedPartIndices eta R₀))
    (hhigh : (1 - alpha) * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)) :
    a ∈ subcriticalProfileRowIndices p v ∧
      (1 - 2 * alpha) * (D.part a \ p.roots).card ≤ (p.rowCount v a : ℝ) := by
  have hfour : 4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right halphaFifth (Nat.cast_nonneg (D.part a).card)
    nlinarith
  have ha : a ∈ subcriticalProfileRowIndices p v := by
    rcases hallowed with ⟨hv, ⟨hvr, ha⟩⟩ | ⟨hv, ha⟩
    · exact (h.retained_row_iff v hv a).mpr ⟨ha, hfour⟩
    · exact (h.outside_row_iff v hv a).mpr ⟨ha, hfour⟩
  refine ⟨ha, ?_⟩
  rw [h.rowCount_eq_degree_of_mem ha]
  exact subcriticalFullHigh_implies_trimmedHigh G v (D.part a) p.roots halpha htrim hhigh

/-- Choose one of the actual adjacent high targets for each medium row. -/
def subcriticalComponentCompanionMap
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V)
    (i : Fin D.componentCount)
    (hc : ∀ a ∈ subcriticalComponentMediumRows p alpha v i,
      ∃ b ∈ subcriticalComponentHighRows p alpha v i, D.ActivePart a b)
    (a : {a // a ∈ subcriticalComponentMediumRows p alpha v i}) : D.PartIndex :=
  (hc a.val a.property).choose

theorem subcriticalComponentCompanionMap_spec
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V)
    (i : Fin D.componentCount)
    (hc : ∀ a ∈ subcriticalComponentMediumRows p alpha v i,
      ∃ b ∈ subcriticalComponentHighRows p alpha v i, D.ActivePart a b)
    (a : {a // a ∈ subcriticalComponentMediumRows p alpha v i}) :
    subcriticalComponentCompanionMap p alpha v i hc a ∈
        subcriticalComponentHighRows p alpha v i ∧
      D.ActivePart a.val (subcriticalComponentCompanionMap p alpha v i hc a) :=
  (hc a.val a.property).choose_spec

/-- A fiber of the chosen companion map injects by its source target into
the actual core-neighbor set of its image. -/
theorem subcriticalComponentCompanionMap_fiber_card_le
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V)
    (i : Fin D.componentCount)
    (hc : ∀ a ∈ subcriticalComponentMediumRows p alpha v i,
      ∃ b ∈ subcriticalComponentHighRows p alpha v i, D.ActivePart a b)
    (b : D.PartIndex) :
    (Finset.univ.filter fun a ↦ subcriticalComponentCompanionMap p alpha v i hc a = b).card ≤
      k - 2 := by
  apply (Finset.card_le_card_of_injOn
    (fun a : {a // a ∈ subcriticalComponentMediumRows p alpha v i} ↦ a.val)
    (t := Finset.univ.filter (D.ActivePart b)) ?_ ?_).trans
      (subcriticalActivePartIndices_card b).le
  · intro a ha
    have he := (Finset.mem_filter.mp ha).2
    have hactive := (subcriticalComponentCompanionMap_spec p alpha v i hc a).2
    rw [he] at hactive
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, subcriticalActivePart_symm hactive⟩
  · intro a _ a' _ he
    exact Subtype.ext he

theorem subcriticalComponentMediumRows_card_le_of_companion
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V)
    (i : Fin D.componentCount)
    (hc : ∀ a ∈ subcriticalComponentMediumRows p alpha v i,
      ∃ b ∈ subcriticalComponentHighRows p alpha v i, D.ActivePart a b) :
    (subcriticalComponentMediumRows p alpha v i).card ≤
      (k - 2) * (subcriticalComponentHighRows p alpha v i).card := by
  let f := subcriticalComponentCompanionMap p alpha v i hc
  have he := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset {a // a ∈ subcriticalComponentMediumRows p alpha v i}))
    (t := subcriticalComponentHighRows p alpha v i)
    (f := f) (fun a _ ↦ (subcriticalComponentCompanionMap_spec p alpha v i hc a).1)
  have hh : ∑ b ∈ subcriticalComponentHighRows p alpha v i,
      (Finset.univ.filter fun a ↦ f a = b).card ≤
        ∑ _b ∈ subcriticalComponentHighRows p alpha v i, (k - 2) :=
    Finset.sum_le_sum fun b _ ↦ subcriticalComponentCompanionMap_fiber_card_le p alpha v i hc b
  rw [← he] at hh
  simpa only [Finset.card_univ, Fintype.card_coe, Finset.sum_const, smul_eq_mul,
    Nat.mul_comm] using hh

section Finite
variable {n : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
  {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
  {omega eta theta alpha delta epsilon : ℝ} {R₀ : ℕ}

/-- A recorded medium row has an actual full-high adjacent core target.
No profile symbol or target is chosen before applying the deterministic
companion theorem to the original graph. -/
theorem subcriticalRecordedMedium_high_companion
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hdelta : delta ≤ subcriticalRowCountingTolerance k) (hscale : 8 ≤ alpha * theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    {v : Fin n} {a : D.PartIndex} (ha : a ∈ subcriticalProfileRowIndices p v)
    (htrim : 2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (hmedium : (p.rowCount v a : ℝ) < (1 - 2 * alpha) * (D.part a \ p.roots).card) :
    ∃ b : D.PartIndex, D.ActivePart a b ∧
      (1 - alpha) * (D.part b).card ≤ (degreeInFinset G v (D.part b) : ℝ) := by
  have hdeg := h.medium_recorded_full_degree ha halpha.le htrim hmedium
  have hvis := h.recorded_row_visible hret ha
  obtain ⟨j, hj, hhigh⟩ := subcriticalMediumDegree_companion R hfree homega halpha htheta
    hdelta hscale a.1 ((D.mem_visiblePartIndices theta a).mp hvis) a.2 v
    (h.recorded_root_not_coreNeighborUnion ha) hdeg.1 hdeg.2.le
  exact ⟨⟨a.1, j⟩, ⟨a.1, a.2, j, rfl, rfl, hj⟩, hhigh⟩

/-- Actual high-row companions when every target in the chosen component
is eligible. This one interface handles retained external components and
retained components viewed from an outside root. -/
theorem subcriticalComponentMedium_high_companion
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (halphaFifth : 5 * alpha ≤ 1)
    (htheta : 0 < theta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    (v : Fin n) (i : Fin D.componentCount)
    (htrim : ∀ a : D.PartIndex, a.1 = i → 2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (hallowed : ∀ a : D.PartIndex, a.1 = i →
      (v ∈ p.retainedRoots ∧ D.EligibleProfileTarget eta R₀ theta v a) ∨
      (v ∈ p.outsideRoots ∧ a ∈ D.retainedPartIndices eta R₀)) :
    ∀ a ∈ subcriticalComponentMediumRows p alpha v i,
      ∃ b ∈ subcriticalComponentHighRows p alpha v i, D.ActivePart a b := by
  intro a ha
  obtain ⟨ha', ham⟩ := (mem_subcriticalComponentMediumRows p alpha v i a).mp ha
  obtain ⟨har, hai⟩ := (mem_subcriticalComponentRows p v i a).mp ha'
  obtain ⟨b, hab, hhigh⟩ := subcriticalRecordedMedium_high_companion R hfree homega halpha
    htheta hdelta hscale hret h har (htrim a hai) ham
  have hbi : b.1 = i := (SubcriticalDivision.activePart_same_component hab).symm.trans hai
  have hb := h.high_allowed_recorded halpha.le halphaFifth (htrim b hbi) (hallowed b hbi) hhigh
  exact ⟨b, (mem_subcriticalComponentHighRows p alpha v i b).mpr
    ⟨(mem_subcriticalComponentRows p v i b).mpr ⟨hb.1, hbi⟩, hb.2⟩, hab⟩

/-- The finite bounded-fiber comparison for any component all of whose
targets are eligible. Its hypotheses are geometry and realization only. -/
theorem subcriticalComponentMediumRows_card_le
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (halphaFifth : 5 * alpha ≤ 1)
    (htheta : 0 < theta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    (v : Fin n) (i : Fin D.componentCount)
    (htrim : ∀ a : D.PartIndex, a.1 = i → 2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (hallowed : ∀ a : D.PartIndex, a.1 = i →
      (v ∈ p.retainedRoots ∧ D.EligibleProfileTarget eta R₀ theta v a) ∨
      (v ∈ p.outsideRoots ∧ a ∈ D.retainedPartIndices eta R₀)) :
    (subcriticalComponentMediumRows p alpha v i).card ≤
      (k - 2) * (subcriticalComponentHighRows p alpha v i).card :=
  subcriticalComponentMediumRows_card_le_of_companion p alpha v i
    (subcriticalComponentMedium_high_companion R hfree homega halpha halphaFifth
      htheta hdelta hscale hret h v i htrim hallowed)

theorem subcriticalExternalComponent_targets_allowed
    (p : SubcriticalProfile D eta R₀ theta) (v : Fin n) (hv : v ∈ p.retainedRoots)
    (i : Fin D.componentCount) (hi : i ∈ D.visibleComponentIndices theta)
    (hio : i ≠ (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1)
    (a : D.PartIndex) (hai : a.1 = i) :
    (v ∈ p.retainedRoots ∧ D.EligibleProfileTarget eta R₀ theta v a) ∨
      (v ∈ p.outsideRoots ∧ a ∈ D.retainedPartIndices eta R₀) := by
  refine Or.inl ⟨hv, p.retainedRoots_subset hv, ?_⟩
  apply (D.mem_eligibleVisibleTargets eta R₀ theta v (p.retainedRoots_subset hv) a).mpr
  refine ⟨(D.mem_visiblePartIndices theta a).mpr (hai ▸ hi), ?_, ?_⟩
  · intro he
    exact hio (hai.symm.trans (congrArg Sigma.fst he))
  · intro ha
    exact hio (hai.symm.trans (SubcriticalDivision.activePart_same_component ha).symm)

/-- Paper: the finite companion multiplicity in
`claim:external-component-ent-K1k`, for an external visible component. -/
theorem subcriticalExternalMediumRows_card_le
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (halphaFifth : 5 * alpha ≤ 1)
    (htheta : 0 < theta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    (v : Fin n) (hv : v ∈ p.retainedRoots) (i : Fin D.componentCount)
    (hi : i ∈ D.visibleComponentIndices theta)
    (hio : i ≠ (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1)
    (htrim : ∀ a : D.PartIndex, a.1 = i → 2 * (p.roots.card : ℝ) ≤ (D.part a).card) :
    (subcriticalComponentMediumRows p alpha v i).card ≤
      (k - 2) * (subcriticalComponentHighRows p alpha v i).card :=
  subcriticalComponentMediumRows_card_le R hfree homega halpha halphaFifth htheta hdelta
    hscale hret h v i htrim (subcriticalExternalComponent_targets_allowed p v hv i hi hio)

/-- The same actual companion fibers for an outside root and a retained
component; no fictitious own part is introduced for an outside root. -/
theorem subcriticalOutsideMediumRows_card_le
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (halphaFifth : 5 * alpha ≤ 1)
    (htheta : 0 < theta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    (v : Fin n) (hv : v ∈ p.outsideRoots) (i : Fin D.componentCount)
    (hi : i ∈ D.retainedComponentIndices eta R₀)
    (htrim : ∀ a : D.PartIndex, a.1 = i → 2 * (p.roots.card : ℝ) ≤ (D.part a).card) :
    (subcriticalComponentMediumRows p alpha v i).card ≤
      (k - 2) * (subcriticalComponentHighRows p alpha v i).card := by
  apply subcriticalComponentMediumRows_card_le R hfree homega halpha halphaFifth htheta hdelta
    hscale hret h v i htrim
  intro a hai
  exact Or.inr ⟨hv, (D.mem_retainedPartIndices eta R₀ a).mpr (hai ▸ hi)⟩

end Finite
end InducedStars
