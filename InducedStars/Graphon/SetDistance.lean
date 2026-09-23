import InducedStars.Graphon.Metric
import InducedStars.Graphon.Step

/-!
# Cut distance to a set of graphons

This file defines the representative-level distance from a graphon to a set
of graphons.  None of the arguments assumes that the defining infimum is
attained.  The one-Lipschitz estimate is the compactness bridge used by the
rough-structure theorems.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The cut distance from `W` to a set of graphons.  Rough-structure results
use this only for nonempty optimizer sets. -/
noncomputable def cutDistToSet (W : Graphon) (S : Set Graphon) : ℝ :=
  sInf ((fun U ↦ cutDist W U) '' S)

private theorem cutDist_image_nonempty (W : Graphon) {S : Set Graphon}
    (hS : S.Nonempty) :
    ((fun U ↦ cutDist W U) '' S).Nonempty :=
  hS.image _

private theorem cutDist_image_bddBelow (W : Graphon) (S : Set Graphon) :
    BddBelow ((fun U ↦ cutDist W U) '' S) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨U, -, rfl⟩
  exact cutDist_nonneg W U

/-- Distance to a nonempty graphon set is nonnegative. -/
theorem cutDistToSet_nonneg (W : Graphon) {S : Set Graphon}
    (hS : S.Nonempty) :
    0 ≤ cutDistToSet W S := by
  unfold cutDistToSet
  apply le_csInf (cutDist_image_nonempty W hS)
  rintro _ ⟨U, -, rfl⟩
  exact cutDist_nonneg W U

/-- The distance to a set is at most the distance to any member. -/
theorem cutDistToSet_le (W : Graphon) {S : Set Graphon}
    {U : Graphon} (hU : U ∈ S) :
    cutDistToSet W S ≤ cutDist W U := by
  unfold cutDistToSet
  exact csInf_le (cutDist_image_bddBelow W S) ⟨U, hU, rfl⟩

/-- A member of a nonempty graphon set has distance zero from that set. -/
theorem cutDistToSet_self_eq_zero {W : Graphon} {S : Set Graphon}
    (hW : W ∈ S) :
    cutDistToSet W S = 0 := by
  apply le_antisymm
  · simpa using cutDistToSet_le W hW
  · exact cutDistToSet_nonneg W ⟨W, hW⟩

/-- Exact lower-bound characterization of distance to a nonempty set. -/
theorem le_cutDistToSet_iff {W : Graphon} {S : Set Graphon}
    (hS : S.Nonempty) (a : ℝ) :
    a ≤ cutDistToSet W S ↔ ∀ U ∈ S, a ≤ cutDist W U := by
  constructor
  · intro ha U hU
    exact ha.trans (cutDistToSet_le W hU)
  · intro ha
    unfold cutDistToSet
    apply le_csInf (cutDist_image_nonempty W hS)
    rintro _ ⟨U, hU, rfl⟩
    exact ha U hU

/-- Triangle inequality with the second endpoint replaced by a nonempty set.
The proof uses approximate minimizers and therefore does not assume that the
infimum defining `cutDistToSet` is attained. -/
theorem cutDistToSet_le_cutDist_add (U W : Graphon) {S : Set Graphon}
    (hS : S.Nonempty) :
    cutDistToSet U S ≤ cutDist U W + cutDistToSet W S := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨d, hd, hdlt⟩ :=
    Real.lt_sInf_add_pos (cutDist_image_nonempty W hS) hδ
  obtain ⟨Z, hZ, rfl⟩ := hd
  calc
    cutDistToSet U S ≤ cutDist U Z := cutDistToSet_le U hZ
    _ ≤ cutDist U W + cutDist W Z := cutDist_triangle U W Z
    _ ≤ cutDist U W + (cutDistToSet W S + δ) :=
      add_le_add le_rfl (le_of_lt hdlt)
    _ = cutDist U W + cutDistToSet W S + δ := by ring

/-- Distance to a fixed nonempty set is one-Lipschitz in cut distance. -/
theorem abs_cutDistToSet_sub_le (U W : Graphon) {S : Set Graphon}
    (hS : S.Nonempty) :
    |cutDistToSet U S - cutDistToSet W S| ≤ cutDist U W := by
  have hUW := cutDistToSet_le_cutDist_add U W hS
  have hWU := cutDistToSet_le_cutDist_add W U hS
  rw [cutDist_comm W U] at hWU
  rw [abs_le]
  constructor <;> linarith

/-- The graphon-to-set distance converges along every cut-convergent
sequence. -/
theorem cutDistToSet_tendsto
    (Wseq : ℕ → Graphon) (W : Graphon) {S : Set Graphon}
    (hS : S.Nonempty)
    (hcut : Tendsto (fun n ↦ cutDist (Wseq n) W) atTop (nhds 0)) :
    Tendsto (fun n ↦ cutDistToSet (Wseq n) S) atTop
      (nhds (cutDistToSet W S)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ ↦ dist_nonneg)
    (fun n ↦ by
      simpa only [Real.dist_eq] using
        abs_cutDistToSet_sub_le (Wseq n) W hS)
    hcut

/-- A uniform lower bound on distance from a nonempty graphon set survives
cut convergence. -/
theorem le_cutDistToSet_of_tendsto
    (Wseq : ℕ → Graphon) (W : Graphon) {S : Set Graphon}
    (hS : S.Nonempty)
    (hcut : Tendsto (fun n ↦ cutDist (Wseq n) W) atTop (nhds 0))
    {a : ℝ} (hfar : ∀ n, a ≤ cutDistToSet (Wseq n) S) :
    a ≤ cutDistToSet W S := by
  exact ge_of_tendsto (cutDistToSet_tendsto Wseq W hS hcut)
    (Eventually.of_forall hfar)

/-! ## Finite adjacency graphons -/

/-- A finite labeled graph is `ε`-far from a graphon set when its existing
zero-diagonal adjacency graphon is at least `ε` away in cut distance. -/
def finiteGraphFarFromSet {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Set Graphon) (ε : ℝ) : Prop :=
  ε ≤ cutDistToSet (graphGraphon G) S

@[simp] theorem finiteGraphFarFromSet_iff {n : ℕ}
    {G : SimpleGraph (Fin n)} {S : Set Graphon} {ε : ℝ} :
    finiteGraphFarFromSet G S ε ↔
      ε ≤ cutDistToSet (graphGraphon G) S :=
  Iff.rfl

end InducedStars
