import InducedStars.Structure.Subcritical.RoleTransfer
import InducedStars.Structure.Subcritical.RowWitnesses
import InducedStars.Structure.Subcritical.CompanionRoles

/-!
# Deterministic companion and opposite-row constraints

Paper: Lemma `lemma:deterministic-medium-companion-K1k`. Count the free
star, then append the prescribed root using its actual incidences. The
opposite-row constraint is an auxiliary specialization of this construction.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

variable {k n R₀ : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
  {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
  {omega eta theta alpha delta epsilon : ℝ}

/-- Shared finite contradiction witness. A medium row in one visible part,
together with enough loopless nonneighbors in all adjacent core parts,
produces an induced star having the prescribed root as a leaf. -/
theorem subcriticalCompanionRows_force_inducedStar
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (i : Fin D.componentCount) (hi : i ∈ D.visibleComponentIndices theta)
    (j : Fin (D.core i).order) (root : Fin n)
    (hlower : alpha * (D.parts i j).card ≤ (degreeInFinset G root (D.parts i j) : ℝ))
    (hupper : (degreeInFinset G root (D.parts i j) : ℝ) ≤
      (1 - alpha) * (D.parts i j).card)
    (hcomp : ∀ t, (D.core i).graph.Adj j t →
      alpha * (D.parts i t).card - 1 ≤
        (complementDegreeInFinset G root (D.parts i t) : ℝ)) :
    Regularity.InducedEmbeds (inducedStar k) G := by
  have hvisible (t : Fin (D.core i).order) :
      (⟨i, t⟩ : D.PartIndex) ∈ D.visiblePartIndices theta :=
    (D.mem_visiblePartIndices theta ⟨i, t⟩).mpr hi
  have hpart (t : Fin (D.core i).order) :
      theta * n / 2 ≤ ((D.parts i t).card : ℝ) :=
    R.visible_part_card_ge_half homega ⟨i, t⟩ (hvisible t)
  obtain ⟨X, hX, hXcard, hXroot, hXadj⟩ :=
    subcritical_exists_neighbor_roleSet G root (D.parts i j)
      halpha (hpart j) hscale hlower
  obtain ⟨Y, hY, hYcard, hYroot, hYnon⟩ :=
    subcritical_exists_nonneighbor_roleSet_of_degree_upper G root (D.parts i j)
      halpha (hpart j) hscale hupper
  choose Z hZ hZcard hZroot hZnon using fun t : SubcriticalCoreNeighbor D i j ↦
    subcritical_exists_nonneighbor_roleSet_of_complement_lower G root (D.parts i t.val)
      halpha (hpart t.val) hscale (hcomp t.val t.property)
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr fun x hx hy ↦
    hYnon x hy (hXadj x hx)
  let e := subcriticalCompanionRoleEquiv hk D i j
  let c : Fin k := e.symm (Sum.inl 0)
  let T := subcriticalCompanionRoleSets D i j X Y Z
  let S : Fin k → Finset (Fin n) := fun a ↦ T (e a)
  let parent : Fin k → {a : D.PartIndex // a ∈ D.visiblePartIndices theta} :=
    fun a ↦ ⟨subcriticalCompanionParent D i j (e a), by
      cases e a with
      | inl b => exact hvisible j
      | inr b => exact hvisible b.val⟩
  have hec (a : Fin k) : e a = Sum.inl 0 ↔ a = c :=
    e.apply_eq_iff_eq_symm_apply
  have hcard (a : Fin k) : (S a).card = subcriticalRoleSize alpha theta n :=
    subcriticalCompanionRoleSets_card D i j X Y Z hXcard hYcard hZcard (e a)
  have hdisjoint : Set.PairwiseDisjoint Set.univ S := by
    intro a _ b _ hab
    exact subcriticalCompanionRoleSets_disjoint D i j X Y Z hX hY hZ hXY
      (e.injective.ne hab)
  have hsubset (a : Fin k) : S a ⊆ D.part (parent a).val :=
    subcriticalCompanionRoleSets_subset D i j X Y Z hX hY hZ (e a)
  have hfactor (a b : Fin k) (hab : a ≠ b) :
      subcriticalPaletteGap k ≤
        if (SimpleGraph.starGraph c).Adj a b then
          subcriticalDivisionPartWeight D (parent a).val (parent b).val
        else 1 - subcriticalDivisionPartWeight D (parent a).val (parent b).val := by
    have h := subcriticalCompanionRole_factor_lower D i j (e a) (e b)
      (e.injective.ne hab)
    simpa only [SimpleGraph.starGraph_adj, e.injective.eq_iff, ne_eq, hec] using h
  obtain ⟨f, hf, hpattern⟩ := subcritical_exists_transversal_of_roleFactors hk R
    (SimpleGraph.starGraph c) parent S halpha htheta hdelta
    (subcriticalRoleSize_pos hscale) hcard hdisjoint hsubset
    (fun a ↦ by rw [hcard]; exact le_subcriticalRoleSize alpha theta n) (by
      intro a b hab
      by_cases h : (SimpleGraph.starGraph c).Adj a b <;>
        simpa only [h, ↓reduceIte] using hfactor a b hab)
  have hrootfree (a : SubcriticalCompanionRole D i j) : root ∉ T a := by
    cases a with
    | inl a =>
        change root ∉ if a = 0 then X else Y
        split_ifs <;> assumption
    | inr a => exact hZroot a
  have hrootadj (a : SubcriticalCompanionRole D i j) (x : Fin n) (hx : x ∈ T a) :
      G.Adj root x ↔ a = Sum.inl 0 := by
    cases a with
    | inl a =>
        by_cases ha : a = 0
        · subst a
          have hx' : x ∈ X := hx
          exact iff_of_true (hXadj x hx') rfl
        · have hx' : x ∈ Y := by simpa [T, subcriticalCompanionRoleSets, ha] using hx
          simp [hYnon x hx', ha]
    | inr a => simp [hZnon a x hx]
  apply inducedEmbeds_inducedStar_of_fixed_leaf G root f c
  · intro a h
    exact hrootfree (e a) (h ▸ hf a)
  · intro a b
    exact (hpattern a b).symm
  · intro a
    exact (hrootadj (e a) (f a) (hf a)).trans (hec a)

/-- Paper: Lemma `lemma:deterministic-medium-companion-K1k`.
The companion row meets the weak high threshold `≥ (1-alpha)|P|`.
The root may lie in any part; free role sets exclude it explicitly. -/
theorem subcriticalMediumDegree_companion_allRoots
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (i : Fin D.componentCount) (hi : i ∈ D.visibleComponentIndices theta)
    (j : Fin (D.core i).order) (v : Fin n)
    (hlower : alpha * (D.parts i j).card ≤ (degreeInFinset G v (D.parts i j) : ℝ))
    (hupper : (degreeInFinset G v (D.parts i j) : ℝ) ≤
      (1 - alpha) * (D.parts i j).card) :
    ∃ j', (D.core i).graph.Adj j j' ∧
      (1 - alpha) * (D.parts i j').card ≤ (degreeInFinset G v (D.parts i j') : ℝ) := by
  by_contra hnone
  push_neg at hnone
  apply hfree (subcriticalCompanionRows_force_inducedStar R homega halpha htheta
    hdelta hscale i hi j v hlower hupper ?_)
  intro t ht
  have hrow := hnone t ht
  have hc := complementDegreeInFinset_ge_card_sub_degree_sub_one G v (D.parts i t)
  nlinarith

/-- Compatibility interface retaining a redundant root-position hypothesis.
The unrestricted companion theorem supplies the current paper statement. -/
theorem subcriticalMediumDegree_companion
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (i : Fin D.componentCount) (hi : i ∈ D.visibleComponentIndices theta)
    (j : Fin (D.core i).order) (v : Fin n)
    (_hv : v ∉ subcriticalCoreNeighborUnion D i j)
    (hlower : alpha * (D.parts i j).card ≤ (degreeInFinset G v (D.parts i j) : ℝ))
    (hupper : (degreeInFinset G v (D.parts i j) : ℝ) ≤
      (1 - alpha) * (D.parts i j).card) :
    ∃ j', (D.core i).graph.Adj j j' ∧
      (1 - alpha) * (D.parts i j').card ≤ (degreeInFinset G v (D.parts i j') : ℝ) :=
  subcriticalMediumDegree_companion_allRoots R hfree homega halpha htheta hdelta
    hscale i hi j v hlower hupper

/-- No opposite-row configuration with the stated loopless complementary
degrees exists. Count the free pattern and append the prescribed leaf. -/
theorem subcriticalOppositeRow_impossible
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (i : Fin D.componentCount) (hi : i ∈ D.visibleComponentIndices theta)
    (j s : Fin (D.core i).order) (hjs : (D.core i).graph.Adj j s)
    (v : Fin n) (_hv : v ∈ D.parts i j)
    (hown : alpha * (D.parts i j).card ≤ (complementDegreeInFinset G v (D.parts i j) : ℝ))
    (hlower : alpha * (D.parts i s).card ≤ (degreeInFinset G v (D.parts i s) : ℝ))
    (hupper : (degreeInFinset G v (D.parts i s) : ℝ) ≤
      (1 - alpha) * (D.parts i s).card)
    (hothers : ∀ t, (D.core i).graph.Adj s t → t ≠ j →
      alpha * (D.parts i t).card ≤ (complementDegreeInFinset G v (D.parts i t) : ℝ)) :
    False := by
  have _hsj : (D.core i).graph.Adj s j := hjs.symm
  apply hfree (subcriticalCompanionRows_force_inducedStar R homega halpha htheta
    hdelta hscale i hi s v hlower hupper ?_)
  intro t ht
  by_cases htj : t = j
  · subst t
    linarith
  · have h := hothers t ht htj
    linarith

end InducedStars
