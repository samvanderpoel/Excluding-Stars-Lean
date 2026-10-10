import InducedStars.Structure.Subcritical.DeterministicRows
import InducedStars.Structure.Subcritical.LocalNonlow

/-!
# High and medium target support in local compensation

The target sets use full degrees into visible parts. Companion inclusion and
regularity give the deficit `Delta * h - m`; the global support budget
identifies its only nonempty zero-deficit configuration.
-/

noncomputable section
open Finset
open scoped Classical BigOperators
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Full-degree high targets in a visible component. -/
def subcriticalHighTargets (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (alpha theta : ℝ) (v : V) (i : Fin D.componentCount) : Finset D.PartIndex :=
  (D.visiblePartIndices theta).filter fun a ↦ a.1 = i ∧
    (1 - alpha) * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)

/-- Full-degree medium targets, with both thresholds strict. -/
def subcriticalMediumTargets (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (alpha theta : ℝ) (v : V) (i : Fin D.componentCount) : Finset D.PartIndex :=
  (D.visiblePartIndices theta).filter fun a ↦ a.1 = i ∧
    alpha * (D.part a).card < (degreeInFinset G v (D.part a) : ℝ) ∧
    (degreeInFinset G v (D.part a) : ℝ) < (1 - alpha) * (D.part a).card

/-- Component support above the low-density threshold. -/
def subcriticalDensitySupport (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (alpha theta : ℝ) (v : V) (i : Fin D.componentCount) : Finset D.PartIndex :=
  subcriticalHighTargets G D alpha theta v i ∪ subcriticalMediumTargets G D alpha theta v i

/-- The signed cardinality deficit, in the paper's normalization. -/
def subcriticalTargetDeficit (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (alpha theta : ℝ) (v : V) (i : Fin D.componentCount) : ℤ :=
  (k - 2 : ℕ) * (subcriticalHighTargets G D alpha theta v i).card -
    (subcriticalMediumTargets G D alpha theta v i).card

@[simp] theorem mem_subcriticalHighTargets
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (alpha theta : ℝ)
    (v : V) (i : Fin D.componentCount) (a : D.PartIndex) :
    a ∈ subcriticalHighTargets G D alpha theta v i ↔
      a ∈ D.visiblePartIndices theta ∧ a.1 = i ∧
        (1 - alpha) * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ) := by
  simp only [subcriticalHighTargets, Finset.mem_filter]

@[simp] theorem mem_subcriticalMediumTargets
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (alpha theta : ℝ)
    (v : V) (i : Fin D.componentCount) (a : D.PartIndex) :
    a ∈ subcriticalMediumTargets G D alpha theta v i ↔
      a ∈ D.visiblePartIndices theta ∧ a.1 = i ∧
        alpha * (D.part a).card < (degreeInFinset G v (D.part a) : ℝ) ∧
        (degreeInFinset G v (D.part a) : ℝ) < (1 - alpha) * (D.part a).card := by
  simp only [subcriticalMediumTargets, Finset.mem_filter]

theorem subcriticalHighMediumTargets_disjoint
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (alpha theta : ℝ)
    (v : V) (i : Fin D.componentCount) :
    Disjoint (subcriticalHighTargets G D alpha theta v i)
      (subcriticalMediumTargets G D alpha theta v i) := by
  apply Finset.disjoint_left.mpr
  intro a ha hm
  exact (mem_subcriticalMediumTargets G D alpha theta v i a |>.mp hm).2.2.2.not_ge
    (mem_subcriticalHighTargets G D alpha theta v i a |>.mp ha).2.2

theorem subcriticalDensitySupport_card
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (alpha theta : ℝ)
    (v : V) (i : Fin D.componentCount) :
    (subcriticalDensitySupport G D alpha theta v i).card =
      (subcriticalHighTargets G D alpha theta v i).card +
        (subcriticalMediumTargets G D alpha theta v i).card :=
  Finset.card_union_of_disjoint (subcriticalHighMediumTargets_disjoint G D alpha theta v i)

theorem subcriticalDensitySupport_subset_nonlow
    (G : SimpleGraph V) (D : SubcriticalDivision k V) {alpha theta : ℝ}
    (ha : alpha ≤ 1 / 2) (v : V) (i : Fin D.componentCount) :
    subcriticalDensitySupport G D alpha theta v i ⊆
      subcriticalNonlowVisibleParts G D alpha theta v := by
  intro a haS
  apply (mem_subcriticalNonlowVisibleParts G D alpha theta v a).mpr
  rcases Finset.mem_union.mp haS with hh | hm
  · obtain ⟨hvis, _, hh⟩ := (mem_subcriticalHighTargets G D alpha theta v i a).mp hh
    refine ⟨hvis, ?_⟩
    have hn : (0 : ℝ) ≤ (D.part a).card := Nat.cast_nonneg _
    nlinarith
  · obtain ⟨hvis, _, hm, _⟩ := (mem_subcriticalMediumTargets G D alpha theta v i a).mp hm
    exact ⟨hvis, hm.le⟩

theorem subcriticalDensitySupport_mem_of_degree_gt
    (G : SimpleGraph V) (D : SubcriticalDivision k V) {alpha theta : ℝ}
    (v : V) (i : Fin D.componentCount) (a : D.PartIndex)
    (hvis : a ∈ D.visiblePartIndices theta) (hai : a.1 = i)
    (hdeg : alpha * (D.part a).card < (degreeInFinset G v (D.part a) : ℝ)) :
    a ∈ subcriticalDensitySupport G D alpha theta v i := by
  by_cases hh : (1 - alpha) * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)
  · exact Finset.mem_union_left _ ((mem_subcriticalHighTargets G D alpha theta v i a).mpr
      ⟨hvis, hai, hh⟩)
  · exact Finset.mem_union_right _ ((mem_subcriticalMediumTargets G D alpha theta v i a).mpr
      ⟨hvis, hai, hdeg, lt_of_not_ge hh⟩)

section Geometry
variable {n R₀ : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
  {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
  {omega eta theta alpha delta epsilon : ℝ}

/-- The support budget is inherited from the deterministic induced-star count. -/
theorem subcriticalDensitySupport_card_le
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (ha : alpha ≤ 1 / 2)
    (htheta : 0 < theta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n) (v : Fin n) (i : Fin D.componentCount) :
    (subcriticalDensitySupport G D alpha theta v i).card ≤ k - 1 :=
  (Finset.card_le_card (subcriticalDensitySupport_subset_nonlow G D ha v i)).trans
    (subcriticalNonlowVisibleParts_card_le hk R hfree homega halpha htheta hdelta hscale v)

/-- Every medium target is adjacent to a full-degree high target. -/
theorem subcriticalMediumTargets_high_companion
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n) (v : Fin n) (i : Fin D.componentCount) :
    ∀ a ∈ subcriticalMediumTargets G D alpha theta v i,
      ∃ b ∈ subcriticalHighTargets G D alpha theta v i, D.ActivePart a b := by
  intro a ha
  obtain ⟨hvis, hai, hlo, hhi⟩ := (mem_subcriticalMediumTargets G D alpha theta v i a).mp ha
  obtain ⟨t, ht, hhigh⟩ := subcriticalMediumDegree_companion_allRoots R hfree homega halpha
    htheta hdelta hscale a.1 ((D.mem_visiblePartIndices theta a).mp hvis) a.2 v hlo.le hhi.le
  refine ⟨⟨a.1, t⟩, ?_, ⟨a.1, a.2, t, rfl, rfl, ht⟩⟩
  exact (mem_subcriticalHighTargets G D alpha theta v i ⟨a.1, t⟩).mpr
    ⟨(D.mem_visiblePartIndices theta ⟨a.1, t⟩).mpr
      ((D.mem_visiblePartIndices theta a).mp hvis), hai, hhigh⟩

end Geometry

/-- Bounded companion multiplicity gives the nonnegative deficit. -/
theorem subcriticalMediumTargets_card_le
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (alpha theta : ℝ)
    (v : V) (i : Fin D.componentCount)
    (hc : ∀ a ∈ subcriticalMediumTargets G D alpha theta v i,
      ∃ b ∈ subcriticalHighTargets G D alpha theta v i, D.ActivePart a b) :
    (subcriticalMediumTargets G D alpha theta v i).card ≤
      (k - 2) * (subcriticalHighTargets G D alpha theta v i).card := by
  have hsub : subcriticalMediumTargets G D alpha theta v i ⊆
      (subcriticalHighTargets G D alpha theta v i).biUnion
        (fun b ↦ Finset.univ.filter (D.ActivePart b)) := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hc a ha
    obtain ⟨j, u, w, rfl, rfl, huw⟩ := hab
    exact Finset.mem_biUnion.mpr ⟨_, hb, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨j, w, u, rfl, rfl, huw.symm⟩⟩⟩
  apply (Finset.card_le_card hsub).trans
  simpa only [Nat.mul_comm] using Finset.card_biUnion_le_card_mul
    (subcriticalHighTargets G D alpha theta v i)
    (fun b ↦ Finset.univ.filter (D.ActivePart b)) (k - 2)
    (fun b _ ↦ (subcriticalActivePartIndices_card b).le)

theorem subcriticalTargetDeficit_nonneg
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (alpha theta : ℝ)
    (v : V) (i : Fin D.componentCount)
    (hc : ∀ a ∈ subcriticalMediumTargets G D alpha theta v i,
      ∃ b ∈ subcriticalHighTargets G D alpha theta v i, D.ActivePart a b) :
    0 ≤ subcriticalTargetDeficit G D alpha theta v i := by
  have h := subcriticalMediumTargets_card_le G D alpha theta v i hc
  dsimp [subcriticalTargetDeficit]
  exact sub_nonneg.mpr (by exact_mod_cast h)

/-- A nonempty support with at most `Delta` targets has positive deficit. -/
theorem subcriticalTargetDeficit_pos_of_support_card_le
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (alpha theta : ℝ)
    (v : V) (i : Fin D.componentCount)
    (hc : ∀ a ∈ subcriticalMediumTargets G D alpha theta v i,
      ∃ b ∈ subcriticalHighTargets G D alpha theta v i, D.ActivePart a b)
    (hne : (subcriticalDensitySupport G D alpha theta v i).Nonempty)
    (hcard : (subcriticalDensitySupport G D alpha theta v i).card ≤ k - 2) :
    1 ≤ subcriticalTargetDeficit G D alpha theta v i := by
  have hb := subcriticalMediumTargets_card_le G D alpha theta v i hc
  have hp := Finset.card_pos.mpr hne
  rw [subcriticalDensitySupport_card] at hcard hp
  have hh : 1 ≤ (subcriticalHighTargets G D alpha theta v i).card := by
    by_contra hh
    have hh0 : (subcriticalHighTargets G D alpha theta v i).card = 0 := by omega
    simp only [hh0, Nat.mul_zero] at hb
    omega
  have hmul := Nat.mul_le_mul_left (k - 2) hh
  dsimp [subcriticalTargetDeficit]
  push_cast
  omega

/-- Zero deficit saturates the support budget and determines all medium targets. -/
theorem subcriticalTargetDeficit_zero_structure
    (hk : 3 ≤ k) (G : SimpleGraph V) (D : SubcriticalDivision k V) (alpha theta : ℝ)
    (v : V) (i : Fin D.componentCount)
    (hc : ∀ a ∈ subcriticalMediumTargets G D alpha theta v i,
      ∃ b ∈ subcriticalHighTargets G D alpha theta v i, D.ActivePart a b)
    (hne : (subcriticalDensitySupport G D alpha theta v i).Nonempty)
    (hcard : (subcriticalDensitySupport G D alpha theta v i).card ≤ k - 1)
    (hz : subcriticalTargetDeficit G D alpha theta v i = 0) :
    ∃ t : D.PartIndex, subcriticalHighTargets G D alpha theta v i = {t} ∧
      subcriticalMediumTargets G D alpha theta v i = Finset.univ.filter (D.ActivePart t) ∧
      (subcriticalDensitySupport G D alpha theta v i).card = k - 1 := by
  have hb := subcriticalMediumTargets_card_le G D alpha theta v i hc
  have hp := Finset.card_pos.mpr hne
  rw [subcriticalDensitySupport_card] at hcard hp
  have hh : 1 ≤ (subcriticalHighTargets G D alpha theta v i).card := by
    by_contra hh
    have hh0 : (subcriticalHighTargets G D alpha theta v i).card = 0 := by omega
    simp only [hh0, Nat.mul_zero] at hb
    omega
  have heq : (k - 2) * (subcriticalHighTargets G D alpha theta v i).card =
      (subcriticalMediumTargets G D alpha theta v i).card := by
    dsimp [subcriticalTargetDeficit] at hz
    exact_mod_cast (sub_eq_zero.mp hz)
  have hh1 : (subcriticalHighTargets G D alpha theta v i).card = 1 := by
    have hm := Nat.mul_le_mul_right (subcriticalHighTargets G D alpha theta v i).card
      (show 1 ≤ k - 2 by omega)
    by_contra hh1
    have hh2 : 2 ≤ (subcriticalHighTargets G D alpha theta v i).card := by omega
    have hm2 := Nat.mul_le_mul_left (k - 2) hh2
    omega
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hh1
  refine ⟨t, ht, ?_, ?_⟩
  · apply Finset.eq_of_subset_of_card_le
    · intro a ha
      obtain ⟨b, hb, hab⟩ := hc a ha
      rw [ht, Finset.mem_singleton] at hb
      subst b
      obtain ⟨j, u, w, rfl, rfl, huw⟩ := hab
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨j, w, u, rfl, rfl, huw.symm⟩⟩
    · rw [subcriticalActivePartIndices_card, ← heq, hh1, Nat.mul_one]
  · rw [subcriticalDensitySupport_card, ← heq, hh1]
    omega

end InducedStars
