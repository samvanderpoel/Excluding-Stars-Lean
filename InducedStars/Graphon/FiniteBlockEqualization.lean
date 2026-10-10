import InducedStars.Graphon.ExtremalProfileRefinement
import InducedStars.Graphon.RelabelingValueMass
import InducedStars.Graphon.TypeProfileApproximation
import Mathlib.Tactic

/-!
# Finite block equalization

This downstream module composes the coordinate-safe common-refinement
construction with the ambient-profile comparison.  It also records the
vanishing error scales used when the finite equalization is applied along an
optimizer approximation sequence.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace InducedStars

/-! ## Vanishing equalization errors -/

/-- Total finite equalization error budget for an exact extremal coloring on
`q` vertices.  Its literal `L¹` endpoint is the balanced original-coordinate
model; after the explicit relabeling, the same budget bounds cut distance to
the canonical block model.  The summand `1/q` accounts for the ambient coarse
diagonal; `8(k-1)/q` accounts for balancing the literal core clusters. -/
def blockEqualizationError (k q : ℕ) : ℝ :=
  (((8 * (k - 1) + 1 : ℕ) : ℝ) / (q : ℝ))

theorem blockEqualizationError_nonneg (k : ℕ) {q : ℕ}
    (_hq : 0 < q) :
    0 ≤ blockEqualizationError k q := by
  unfold blockEqualizationError
  positivity

theorem blockEqualizationError_pos (k : ℕ) {q : ℕ}
    (hq : 0 < q) :
    0 < blockEqualizationError k q := by
  unfold blockEqualizationError
  positivity

/-- The equalization error vanishes along every sequence of ambient orders
tending to infinity. -/
theorem blockEqualizationError_tendsto_zero (k : ℕ)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    Tendsto (fun m ↦ blockEqualizationError k (q m))
      atTop (nhds 0) := by
  apply ((tendsto_const_div_atTop_nhds_zero_nat
    (((8 * (k - 1) + 1 : ℕ) : ℝ))).comp hq).congr'
  filter_upwards [] with m
  rfl

/-- Error budget for the one-valued and random-valued region masses of a
three-valued palette `{0,p,1}`. -/
def blockEqualizationMassError (k q : ℕ) (p : ℝ) : ℝ :=
  blockEqualizationError k q / min p (1 - p)

theorem blockEqualizationMassError_nonneg (k : ℕ) {q : ℕ}
    (hq : 0 < q) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 ≤ blockEqualizationMassError k q p := by
  unfold blockEqualizationMassError
  exact div_nonneg (blockEqualizationError_nonneg k hq)
    (le_of_lt (lt_min hp.1 (sub_pos.mpr hp.2)))

theorem blockEqualizationMassError_pos (k : ℕ) {q : ℕ}
    (hq : 0 < q) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 < blockEqualizationMassError k q p := by
  unfold blockEqualizationMassError
  exact div_pos (blockEqualizationError_pos k hq)
    (lt_min hp.1 (sub_pos.mpr hp.2))

/-- Palette separation is fixed in the optimizer application, so the mass
error also vanishes as the ambient order tends to infinity. -/
theorem blockEqualizationMassError_tendsto_zero (k : ℕ)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    Tendsto (fun m ↦ blockEqualizationMassError k (q m) p)
      atTop (nhds 0) := by
  have hsep : min p (1 - p) ≠ 0 :=
    (lt_min hp.1 (sub_pos.mpr hp.2)).ne'
  have h := (blockEqualizationError_tendsto_zero k hq).div
    (tendsto_const_nhds (x := min p (1 - p))) hsep
  rw [zero_div] at h
  apply h.congr'
  filter_upwards [] with m
  rfl

/-! ## The finite quantitative comparison -/

namespace FiniteExtremalBlockModel

variable {k q : ℕ} {C : ColoredGraph (Fin q)}
    (M : FiniteExtremalBlockModel k q C)

/-- The literal refined-core graphon and the balanced-coordinate graphon are
within `8(k-1)/q` in `L¹`. -/
theorem graphonL1Dist_refinedExtremalCoreGraphon_balancedExtremalCoreGraphon_le
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    graphonL1Dist (M.refinedExtremalCoreGraphon p hp)
        (M.balancedExtremalCoreGraphon p hp) ≤
      ((8 * (k - 1) : ℕ) : ℝ) / (q : ℝ) := by
  simpa only [refinedExtremalCoreGraphon] using
    M.graphonL1Dist_matrixGraphon_refinedExtremalCoreMatrix_balancedExtremalCoreGraphon_le
      hp

/-- In the original finite coordinates, the ambient profile is within the
full equalization budget of the balanced core graphon. -/
theorem graphonL1Dist_profileColoringGraphon_balancedExtremalCoreGraphon_le
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    graphonL1Dist (profileColoringGraphon p C hp)
        (M.balancedExtremalCoreGraphon p hp) ≤
      blockEqualizationError k q := by
  calc
    graphonL1Dist (profileColoringGraphon p C hp)
        (M.balancedExtremalCoreGraphon p hp) ≤
      graphonL1Dist (profileColoringGraphon p C hp)
          (M.refinedExtremalCoreGraphon p hp) +
        graphonL1Dist (M.refinedExtremalCoreGraphon p hp)
          (M.balancedExtremalCoreGraphon p hp) :=
      graphonL1Dist_triangle _ _ _
    _ ≤ 1 / (q : ℝ) + ((8 * (k - 1) : ℕ) : ℝ) / (q : ℝ) :=
      add_le_add
        (M.graphonL1Dist_profileColoringGraphon_refinedExtremalCoreGraphon_le hp)
        (M.graphonL1Dist_refinedExtremalCoreGraphon_balancedExtremalCoreGraphon_le hp)
    _ = blockEqualizationError k q := by
      unfold blockEqualizationError
      push_cast
      ring

/-- The original extremal profile and the canonical finite block graphon are
within the explicit equalization budget in cut distance. -/
theorem cutDist_extremalProfile_blockModel_le
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    cutDist (profileColoringGraphon p C hp) (M.profileGraphon p hp) ≤
      blockEqualizationError k q := by
  rw [← M.canonicalExtremalCoreGraphon_eq_profileGraphon p hp]
  calc
    cutDist (profileColoringGraphon p C hp)
        (M.canonicalExtremalCoreGraphon p hp) ≤
      cutDist (profileColoringGraphon p C hp)
          (M.balancedExtremalCoreGraphon p hp) +
        cutDist (M.balancedExtremalCoreGraphon p hp)
          (M.canonicalExtremalCoreGraphon p hp) :=
      cutDist_triangle _ _ _
    _ = cutDist (profileColoringGraphon p C hp)
        (M.balancedExtremalCoreGraphon p hp) := by
      rw [cutDist_comm (M.balancedExtremalCoreGraphon p hp),
        M.cutDist_canonicalExtremalCoreGraphon_balancedExtremalCoreGraphon_eq_zero,
        add_zero]
    _ ≤ graphonL1Dist (profileColoringGraphon p C hp)
        (M.balancedExtremalCoreGraphon p hp) :=
      cutDist_le_graphonL1Dist _ _
    _ ≤ blockEqualizationError k q :=
      M.graphonL1Dist_profileColoringGraphon_balancedExtremalCoreGraphon_le hp

/-- The canonical and balanced coordinate presentations have the same exact
one-valued mass. -/
theorem graphonOneMass_profileGraphon_eq_balancedExtremalCoreGraphon
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    graphonOneMass (M.profileGraphon p hp) =
      graphonOneMass (M.balancedExtremalCoreGraphon p hp) := by
  rw [← M.canonicalExtremalCoreGraphon_eq_profileGraphon p hp,
    M.canonicalExtremalCoreGraphon_eq_relabel,
    Graphon.graphonOneMass_relabel]

/-- The canonical and balanced coordinate presentations have the same exact
random-valued mass. -/
theorem graphonRandomMass_profileGraphon_eq_balancedExtremalCoreGraphon
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    graphonRandomMass (M.profileGraphon p hp) =
      graphonRandomMass (M.balancedExtremalCoreGraphon p hp) := by
  rw [← M.canonicalExtremalCoreGraphon_eq_profileGraphon p hp,
    M.canonicalExtremalCoreGraphon_eq_relabel,
    Graphon.graphonRandomMass_relabel]

/-- Equalization controls the canonical block graphon's one-valued mass by
the common separated-palette error. -/
theorem graphonOneMass_profileGraphon_sub_normalizedBlueDiagonalArea_abs_le
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    |graphonOneMass (M.profileGraphon p ⟨hp.1.le, hp.2.le⟩) -
        C.normalizedBlueDiagonalArea| ≤
      blockEqualizationMassError k q p := by
  let hpIcc : p ∈ Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  let H := profileColoringGraphon p C hpIcc
  let B := M.balancedExtremalCoreGraphon p hpIcc
  have hpaletteH := profileColoringGraphon_ae_threeValued
    M.ambientOrder_pos p C hpIcc
  have hpaletteB := M.balancedExtremalCoreGraphon_ae_threeValued p hpIcc
  have hmass := graphonOneMass_sub_abs_le_graphonL1Dist_div_min
    B H hp.1 hp.2 hpaletteB hpaletteH
  have hL1 :=
    M.graphonL1Dist_profileColoringGraphon_balancedExtremalCoreGraphon_le hpIcc
  have hsep : 0 ≤ min p (1 - p) :=
    (lt_min hp.1 (sub_pos.mpr hp.2)).le
  calc
    |graphonOneMass (M.profileGraphon p hpIcc) -
        C.normalizedBlueDiagonalArea| =
      |graphonOneMass B - graphonOneMass H| := by
        rw [M.graphonOneMass_profileGraphon_eq_balancedExtremalCoreGraphon,
          graphonOneMass_profileColoringGraphon M.ambientOrder_pos hp C]
    _ ≤ graphonL1Dist B H / min p (1 - p) := hmass
    _ = graphonL1Dist H B / min p (1 - p) := by
      rw [graphonL1Dist_comm]
    _ ≤ blockEqualizationError k q / min p (1 - p) := by
      exact div_le_div_of_nonneg_right hL1 hsep
    _ = blockEqualizationMassError k q p := rfl

/-- Equalization controls the canonical block graphon's random-valued mass by
the common separated-palette error. -/
theorem graphonRandomMass_profileGraphon_sub_normalizedRedArea_abs_le
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    |graphonRandomMass (M.profileGraphon p ⟨hp.1.le, hp.2.le⟩) -
        C.normalizedRedArea| ≤ blockEqualizationMassError k q p := by
  let hpIcc : p ∈ Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  let H := profileColoringGraphon p C hpIcc
  let B := M.balancedExtremalCoreGraphon p hpIcc
  have hpaletteH := profileColoringGraphon_ae_threeValued
    M.ambientOrder_pos p C hpIcc
  have hpaletteB := M.balancedExtremalCoreGraphon_ae_threeValued p hpIcc
  have hmass := graphonRandomMass_sub_abs_le_graphonL1Dist_div_min
    B H hp.1 hp.2 hpaletteB hpaletteH
  have hL1 :=
    M.graphonL1Dist_profileColoringGraphon_balancedExtremalCoreGraphon_le hpIcc
  have hsep : 0 ≤ min p (1 - p) :=
    (lt_min hp.1 (sub_pos.mpr hp.2)).le
  calc
    |graphonRandomMass (M.profileGraphon p hpIcc) -
        C.normalizedRedArea| =
      |graphonRandomMass B - graphonRandomMass H| := by
        rw [M.graphonRandomMass_profileGraphon_eq_balancedExtremalCoreGraphon,
          graphonRandomMass_profileColoringGraphon M.ambientOrder_pos hp C]
    _ ≤ graphonL1Dist B H / min p (1 - p) := hmass
    _ = graphonL1Dist H B / min p (1 - p) := by
      rw [graphonL1Dist_comm]
    _ ≤ blockEqualizationError k q / min p (1 - p) := by
      exact div_le_div_of_nonneg_right hL1 hsep
    _ = blockEqualizationMassError k q p := rfl

end FiniteExtremalBlockModel

/-! ## Bundled finite output -/

/-- The coordinate-safe output of equalizing one exact finite extremal
witness.  It retains the common-grid permutation and its induced relabeling,
the original-coordinate `L¹` estimate, the canonical cut estimate, and the
two separated-palette mass estimates. -/
structure FiniteBlockEqualizationResult
    {k q : ℕ} {C : ColoredGraph (Fin q)}
    (M : FiniteExtremalBlockModel k q C)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) where
  refinementFactor : ℕ
  refinementFactor_eq : refinementFactor = M.refinementFactor
  refinementOrder : ℕ
  refinementOrder_eq : refinementOrder = M.refinementOrder
  fineCellPerm : Equiv.Perm (Fin M.refinementOrder)
  fineCellPerm_eq : fineCellPerm = M.canonicalToBalancedPerm
  relabeling : GraphonRelabeling
  relabeling_eq : relabeling = cellPermRelabeling fineCellPerm
  equalizedGraphon : Graphon
  equalizedGraphon_eq :
    equalizedGraphon =
      M.balancedExtremalCoreGraphon p ⟨hp.1.le, hp.2.le⟩
  profile_eq_relabel :
    M.profileGraphon p ⟨hp.1.le, hp.2.le⟩ =
      equalizedGraphon.relabel relabeling
  cut_eq_zero :
    cutDist (M.profileGraphon p ⟨hp.1.le, hp.2.le⟩)
      equalizedGraphon = 0
  l1_le :
    graphonL1Dist
      (profileColoringGraphon p C ⟨hp.1.le, hp.2.le⟩)
      equalizedGraphon ≤ blockEqualizationError k q
  cutDist_le :
    cutDist (profileColoringGraphon p C ⟨hp.1.le, hp.2.le⟩)
      (M.profileGraphon p ⟨hp.1.le, hp.2.le⟩) ≤
        blockEqualizationError k q
  oneMass_sub_abs_le :
    |graphonOneMass (M.profileGraphon p ⟨hp.1.le, hp.2.le⟩) -
      C.normalizedBlueDiagonalArea| ≤ blockEqualizationMassError k q p
  randomMass_sub_abs_le :
    |graphonRandomMass (M.profileGraphon p ⟨hp.1.le, hp.2.le⟩) -
      C.normalizedRedArea| ≤ blockEqualizationMassError k q p

/-- Construct the complete finite equalization package from the retained
exact witness model. -/
noncomputable def exists_finiteBlockEqualization
    {k q : ℕ} {C : ColoredGraph (Fin q)}
    (M : FiniteExtremalBlockModel k q C)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    FiniteBlockEqualizationResult M p hp where
  refinementFactor := M.refinementFactor
  refinementFactor_eq := rfl
  refinementOrder := M.refinementOrder
  refinementOrder_eq := rfl
  fineCellPerm := M.canonicalToBalancedPerm
  fineCellPerm_eq := rfl
  relabeling := cellPermRelabeling M.canonicalToBalancedPerm
  relabeling_eq := rfl
  equalizedGraphon :=
    M.balancedExtremalCoreGraphon p ⟨hp.1.le, hp.2.le⟩
  equalizedGraphon_eq := rfl
  profile_eq_relabel := by
    exact
      (M.canonicalExtremalCoreGraphon_eq_profileGraphon p
        ⟨hp.1.le, hp.2.le⟩).symm.trans
        (M.canonicalExtremalCoreGraphon_eq_relabel p
          ⟨hp.1.le, hp.2.le⟩)
  cut_eq_zero := by
    calc
      cutDist (M.profileGraphon p ⟨hp.1.le, hp.2.le⟩)
          (M.balancedExtremalCoreGraphon p ⟨hp.1.le, hp.2.le⟩) =
        cutDist (M.canonicalExtremalCoreGraphon p ⟨hp.1.le, hp.2.le⟩)
          (M.balancedExtremalCoreGraphon p ⟨hp.1.le, hp.2.le⟩) := by
            exact congrArg
              (fun U ↦ cutDist U
                (M.balancedExtremalCoreGraphon p ⟨hp.1.le, hp.2.le⟩))
              (M.canonicalExtremalCoreGraphon_eq_profileGraphon p
                ⟨hp.1.le, hp.2.le⟩).symm
      _ = 0 :=
        M.cutDist_canonicalExtremalCoreGraphon_balancedExtremalCoreGraphon_eq_zero
          p ⟨hp.1.le, hp.2.le⟩
  l1_le :=
    M.graphonL1Dist_profileColoringGraphon_balancedExtremalCoreGraphon_le
      ⟨hp.1.le, hp.2.le⟩
  cutDist_le := M.cutDist_extremalProfile_blockModel_le
    ⟨hp.1.le, hp.2.le⟩
  oneMass_sub_abs_le :=
    M.graphonOneMass_profileGraphon_sub_normalizedBlueDiagonalArea_abs_le hp
  randomMass_sub_abs_le :=
    M.graphonRandomMass_profileGraphon_sub_normalizedRedArea_abs_le hp

end InducedStars
