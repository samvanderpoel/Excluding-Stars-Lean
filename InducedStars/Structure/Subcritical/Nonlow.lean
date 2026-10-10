import InducedStars.Structure.Subcritical.RowWitnesses
import InducedStars.Structure.Subcritical.RowCounting
import InducedStars.Structure.Subcritical.RoleTransfer

/-!
# The deterministic subcritical non-low-part bound

Paper: Lemma `lemma:deterministic-nonlow-bound-K1k`.  The proof uses a localized count of an edgeless pattern on the free vertices. The prescribed center is not averaged or relabeled.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

variable {k n : ℕ}

/-- Every required nonedge between distinct division parts has a uniformly
positive palette factor, without any comparison of `pK k` with `1/(k-1)`.
-/
theorem subcriticalPaletteGap_le_one_sub_partWeight_of_ne
    (D : SubcriticalDivision k (Fin n))
    {a b : D.PartIndex} (hab : a ≠ b) :
    subcriticalPaletteGap k ≤ 1 - subcriticalDivisionPartWeight D a b := by
  have hw := subcriticalDivisionPartWeight_le_pK_of_ne D hab
  have hp := pK_le_one_sub_subcriticalPaletteGap k
  linarith

/-- If a prescribed vertex has `k` non-low visible rows, the local finite
counting theorem produces an induced star centered at that same vertex.
Only the `k` free leaves are counted. -/
theorem subcriticalNonlowRows_force_inducedStar
    {R₀ : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)}
    {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
    {omega eta theta alpha delta epsilon : ℝ}
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n) (root : Fin n)
    (hcard : k ≤ (subcriticalNonlowVisibleParts G D alpha theta root).card) :
    Regularity.InducedEmbeds (inducedStar k) G := by
  obtain ⟨parent, S, hvisible, hpart, hsize, hdisjoint, _, hadj⟩ :=
    subcritical_exists_nonlow_neighbor_roles R homega halpha hscale root hcard
  let visibleParent (a : Fin k) : {a : D.PartIndex // a ∈ D.visiblePartIndices theta} :=
    ⟨parent a, hvisible a⟩
  have hsizeLower (a : Fin k) : alpha * theta * n / 4 ≤ ((S a).card : ℝ) := by
    rw [hsize]
    exact le_subcriticalRoleSize alpha theta n
  have hfactor (a b : Fin k) (hab : a ≠ b) :
      subcriticalPaletteGap k ≤
        if (⊥ : SimpleGraph (Fin k)).Adj a b then
          subcriticalDivisionPartWeight D (visibleParent a).val (visibleParent b).val
        else 1 - subcriticalDivisionPartWeight D
          (visibleParent a).val (visibleParent b).val := by
    simpa only [SimpleGraph.bot_adj, ↓reduceIte, visibleParent] using
      subcriticalPaletteGap_le_one_sub_partWeight_of_ne D (parent.injective.ne hab)
  obtain ⟨f, hf, hind⟩ := subcritical_exists_transversal_of_roleFactors hk R
    (⊥ : SimpleGraph (Fin k)) visibleParent S halpha htheta hdelta
    (subcriticalRoleSize_pos hscale) hsize (fun a _ b _ hab ↦ hdisjoint hab)
    hpart hsizeLower (by
      intro a b hab
      simpa only [SimpleGraph.bot_adj, ↓reduceIte] using hfactor a b hab)
  apply inducedEmbeds_inducedStar_of_fixed_center G root f
  · intro a
    exact hadj a (f a) (hf a)
  · intro a b
    exact fun hab ↦ (hind a b).mpr hab

/-- Paper: Lemma `lemma:deterministic-nonlow-bound-K1k`.
Every fixed vertex has at most `k-1` non-low visible parts. The statement
follows from the locally proved induced-pattern counting
step on the free vertices. -/
theorem subcriticalNonlowVisibleParts_card_le
    {R₀ : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)}
    {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
    {omega eta theta alpha delta epsilon : ℝ}
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n) (root : Fin n) :
    (subcriticalNonlowVisibleParts G D alpha theta root).card ≤ k - 1 := by
  by_contra h
  exact hfree (subcriticalNonlowRows_force_inducedStar hk R homega halpha htheta
    hdelta hscale root (by omega))

end InducedStars
