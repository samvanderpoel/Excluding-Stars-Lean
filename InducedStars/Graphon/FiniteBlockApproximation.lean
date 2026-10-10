import InducedStars.Graphon.Candidates
import InducedStars.Graphon.ExtremalApproximation
import InducedStars.Graphon.FiniteBlockEqualization
import Mathlib.Tactic

/-!
# Canonical finite block approximations of graphon optimizers

This file applies the finite component model and coordinate-safe block
equalization at every stage of an `OptimizerExtremalApproximationResult`.
It retains the ordered finite block data and proves the convergence statements
needed before the later compactness and concentration arguments.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace InducedStars

namespace OptimizerExtremalApproximationResult

variable {k : ℕ} {γ : ℝ} {W : Graphon}

/-- The bundled finite component model obtained from the exact witness retained
at stage `m`. -/
noncomputable def finiteBlockModel
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) :
    FiniteExtremalBlockModel k (R.selectedClusterCount m)
      (R.extremalColoring m) :=
  finiteExtremalBlockModel hk (R.selectedClusterCount_pos m)
    (R.extremalWitness m) (R.extremal_coreCount_pos m)

/-- The canonical finite admissible block sequence extracted from the exact
extremal witness retained at stage `m`. -/
noncomputable def blockSequence
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) : AdmissibleBlockSequence k :=
  (R.finiteBlockModel hk m).blockSequence

/-- The canonical arbitrary-profile finite block graphon at stage `m`. -/
noncomputable def blockProfileGraphon
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) : Graphon :=
  profileWLambda R.profile.randomMean (R.blockSequence hk m)
    ⟨R.profile.randomMean_pos.le, R.profile.randomMean_lt_one.le⟩

/-- The number of exact core components at stage `m`. -/
abbrev componentCount
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) : ℕ :=
  (R.finiteBlockModel hk m).componentCount

/-- The normalized length of the component in canonical ordered position
`a` at stage `m`. -/
def orderedComponentLength
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) (a : Fin (R.componentCount hk m)) : ℝ :=
  (R.finiteBlockModel hk m).orderedLength a

/-- The reduced regular core in canonical ordered position `a`. -/
noncomputable def orderedComponentCore
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) (a : Fin (R.componentCount hk m)) : RegularBlockCore k :=
  (R.finiteBlockModel hk m).orderedCore a

/-- The order of the reduced core in canonical ordered position `a`. -/
noncomputable def orderedComponentCoreOrder
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) (a : Fin (R.componentCount hk m)) : ℕ :=
  (R.orderedComponentCore hk m a).order

/-- Largest normalized component length at stage `m`. -/
def largestBlockLength
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) : ℝ :=
  (R.finiteBlockModel hk m).largestBlockLength

/-- Total normalized tail length after the largest component. -/
def tailBlockLength
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) : ℝ :=
  (R.finiteBlockModel hk m).tailBlockLength

/-- Sum of the normalized component lengths at stage `m`. -/
def blockLengthSum
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) : ℝ :=
  (R.finiteBlockModel hk m).blockLengthSum

/-- Sum of squared normalized component lengths at stage `m`. -/
def blockLengthSquareSum
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) : ℝ :=
  (R.finiteBlockModel hk m).blockLengthSquareSum

/-- Exact scalar block mass at stage `m`. -/
def blockMass
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) : ℝ :=
  (R.finiteBlockModel hk m).blockMass

@[simp] theorem blockSequence_count
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) :
    (R.blockSequence hk m).count = some (R.componentCount hk m) :=
  rfl

@[simp] theorem blockSequence_alpha
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m i : ℕ) :
    (R.blockSequence hk m).alpha i =
      (R.extremalWitness m).finiteBlockAlpha i :=
  rfl

@[simp] theorem blockSequence_core
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m i : ℕ) :
    (R.blockSequence hk m).core i =
      (R.extremalWitness m).finiteBlockCore hk i :=
  rfl

@[simp] theorem blockMass_eq_sequence_mass
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) :
    R.blockMass hk m = (R.blockSequence hk m).mass :=
  rfl

/-- Exact one-valued mass of every canonical finite block graphon. -/
theorem graphonOneMass_blockProfileGraphon
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) :
    graphonOneMass (R.blockProfileGraphon hk m) = R.blockMass hk m := by
  rw [blockProfileGraphon,
    graphonOneMass_profileWLambda hk
      ⟨R.profile.randomMean_pos, R.profile.randomMean_lt_one⟩]
  rfl

/-- Exact random-valued mass of every canonical finite block graphon. -/
theorem graphonRandomMass_blockProfileGraphon
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) :
    graphonRandomMass (R.blockProfileGraphon hk m) =
      ((k - 2 : ℕ) : ℝ) * R.blockMass hk m := by
  rw [blockProfileGraphon,
    graphonRandomMass_profileWLambda hk
      ⟨R.profile.randomMean_pos, R.profile.randomMean_lt_one⟩]
  rfl

/-- Exact nonzero mass of every canonical finite block graphon. -/
theorem graphonNonzeroMass_blockProfileGraphon
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) :
    graphonNonzeroMass (R.blockProfileGraphon hk m) =
      ((k - 1 : ℕ) : ℝ) * R.blockMass hk m := by
  rw [blockProfileGraphon,
    graphonNonzeroMass_profileWLambda hk
      ⟨R.profile.randomMean_pos, R.profile.randomMean_lt_one⟩]
  rfl

/-- Exact edge density of every canonical finite block graphon. -/
theorem graphonEdgeDensity_blockProfileGraphon
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) :
    graphonEdgeDensity (R.blockProfileGraphon hk m) =
      (1 + ((k - 2 : ℕ) : ℝ) * R.profile.randomMean) *
        R.blockMass hk m := by
  rw [blockProfileGraphon,
    graphonEdgeDensity_profileWLambda hk
      ⟨R.profile.randomMean_pos, R.profile.randomMean_lt_one⟩]
  rfl

/-- Exact entropy of every canonical finite block graphon. -/
theorem graphonEntropy_blockProfileGraphon
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) :
    graphonEntropy (R.blockProfileGraphon hk m) =
      (((k - 2 : ℕ) : ℝ) * binaryEntropy R.profile.randomMean) *
        R.blockMass hk m := by
  rw [blockProfileGraphon,
    graphonEntropy_profileWLambda hk
      ⟨R.profile.randomMean_pos, R.profile.randomMean_lt_one⟩]
  rfl

/-- Stagewise finite equalization in the coordinate-safe form used for cut
convergence. -/
theorem cutDist_extremalProfile_blockProfileGraphon_le
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) :
    cutDist (R.extremalProfileGraphon m) (R.blockProfileGraphon hk m) ≤
      blockEqualizationError k (R.selectedClusterCount m) := by
  exact (R.finiteBlockModel hk m).cutDist_extremalProfile_blockModel_le
    ⟨R.profile.randomMean_pos.le, R.profile.randomMean_lt_one.le⟩

/-- The stage block mass differs from the retained exact coloring's blue
diagonal area by at most the separated-palette equalization error. -/
theorem blockMass_sub_normalizedBlueDiagonalArea_abs_le
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) :
    |R.blockMass hk m -
        (R.extremalColoring m).normalizedBlueDiagonalArea| ≤
      blockEqualizationMassError k (R.selectedClusterCount m)
        R.profile.randomMean := by
  rw [← R.graphonOneMass_blockProfileGraphon hk m]
  exact (R.finiteBlockModel hk m)
    |>.graphonOneMass_profileGraphon_sub_normalizedBlueDiagonalArea_abs_le
      ⟨R.profile.randomMean_pos, R.profile.randomMean_lt_one⟩

/-- The stage random-valued mass differs from the retained exact coloring's
red area by at most the separated-palette equalization error. -/
theorem randomBlockMass_sub_normalizedRedArea_abs_le
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (m : ℕ) :
    |((k - 2 : ℕ) : ℝ) * R.blockMass hk m -
        (R.extremalColoring m).normalizedRedArea| ≤
      blockEqualizationMassError k (R.selectedClusterCount m)
        R.profile.randomMean := by
  rw [← R.graphonRandomMass_blockProfileGraphon hk m]
  exact (R.finiteBlockModel hk m)
    |>.graphonRandomMass_profileGraphon_sub_normalizedRedArea_abs_le
      ⟨R.profile.randomMean_pos, R.profile.randomMean_lt_one⟩

/-- In the subcritical regime the stage graphon is literally the existing
`WLambda` graphon of its finite admissible sequence. -/
theorem blockProfileGraphon_eq_WLambda_of_lt_gammaK
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hsub : γ < gammaK k) (m : ℕ) :
    R.blockProfileGraphon hk m = WLambda hk (R.blockSequence hk m) := by
  have hmean := R.profile.randomMean_eq_of_lt_gammaK hk hγ hsub
  simpa only [blockProfileGraphon, hmean] using
    profileWLambda_pK hk (R.blockSequence hk m)

end OptimizerExtremalApproximationResult

/-! ## Principal stagewise package -/

/-- Canonically ordered finite block approximations associated with one fixed
graphon optimizer.  The package retains the literal model at every stage and
records the convergence statements before any infinite component extraction
or optimizer classification is attempted. -/
structure OptimizerFiniteBlockApproximationResult
    (k : ℕ) (γ : ℝ) (W : Graphon) where
  three_le_k : 3 ≤ k
  extremalApproximation : OptimizerExtremalApproximationResult k γ W
  model : (m : ℕ) →
    FiniteExtremalBlockModel k
      (extremalApproximation.selectedClusterCount m)
      (extremalApproximation.extremalColoring m)
  model_eq : ∀ m,
    model m = extremalApproximation.finiteBlockModel three_le_k m
  blockSequence : ℕ → AdmissibleBlockSequence k
  blockSequence_eq : ∀ m, blockSequence m = (model m).blockSequence
  blockGraphon : ℕ → Graphon
  blockGraphon_eq : ∀ m,
    blockGraphon m =
      profileWLambda extremalApproximation.profile.randomMean
        (blockSequence m)
        ⟨extremalApproximation.profile.randomMean_pos.le,
          extremalApproximation.profile.randomMean_lt_one.le⟩
  cut_tendsto :
    Tendsto
      (fun m ↦ cutDist (blockGraphon m) extremalApproximation.target)
      atTop (𝓝 0)
  blockMass_tendsto :
    Tendsto (fun m ↦ (blockSequence m).mass) atTop
      (𝓝 (graphonOneMass extremalApproximation.target))
  randomMass_tendsto :
    Tendsto
      (fun m ↦ ((k - 2 : ℕ) : ℝ) * (blockSequence m).mass)
      atTop (𝓝 (graphonRandomMass extremalApproximation.target))
  edgeDensity_tendsto :
    Tendsto (fun m ↦ graphonEdgeDensity (blockGraphon m))
      atTop (𝓝 γ)
  entropy_tendsto :
    Tendsto (fun m ↦ graphonEntropy (blockGraphon m))
      atTop (𝓝 (entropyDensity k γ))
  nonzeroMass_tendsto :
    Tendsto (fun m ↦ graphonNonzeroMass (blockGraphon m))
      atTop (𝓝 (graphonNonzeroMass extremalApproximation.target))
  componentCount_pos : ∀ m, 0 < (model m).componentCount

namespace OptimizerFiniteBlockApproximationResult

variable {k : ℕ} {γ : ℝ} {W : Graphon}

/-- Ordered normalized component length exposed directly from the retained
finite model. -/
def orderedComponentLength
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ)
    (a : Fin (A.model m).componentCount) : ℝ :=
  (A.model m).orderedLength a

/-- Ordered reduced core exposed directly from the retained finite model. -/
noncomputable def orderedComponentCore
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ)
    (a : Fin (A.model m).componentCount) : RegularBlockCore k :=
  (A.model m).orderedCore a

/-- Order of the ordered reduced core. -/
def orderedComponentCoreOrder
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ)
    (a : Fin (A.model m).componentCount) : ℕ :=
  (A.model m).orderedCoreOrder a

/-- Largest normalized component length. -/
def largestBlockLength
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) : ℝ :=
  (A.model m).largestBlockLength

/-- Total normalized tail length after the largest component. -/
def tailBlockLength
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) : ℝ :=
  (A.model m).tailBlockLength

/-- Sum of all normalized component lengths. -/
def blockLengthSum
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) : ℝ :=
  (A.model m).blockLengthSum

/-- Sum of squared normalized component lengths. -/
def blockLengthSquareSum
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) : ℝ :=
  (A.model m).blockLengthSquareSum

/-- Exact scalar mass of the retained finite block sequence. -/
def blockMass
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) : ℝ :=
  (A.blockSequence m).mass

@[simp] theorem blockMass_eq_model_blockMass
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) :
    A.blockMass m = (A.model m).blockMass := by
  rw [blockMass, A.blockSequence_eq]
  rfl

/-- Exact one-valued mass at every retained finite stage. -/
theorem graphonOneMass_blockGraphon
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) :
    graphonOneMass (A.blockGraphon m) = A.blockMass m := by
  rw [A.blockGraphon_eq]
  simpa only [blockMass] using
    graphonOneMass_profileWLambda A.three_le_k
      ⟨A.extremalApproximation.profile.randomMean_pos,
        A.extremalApproximation.profile.randomMean_lt_one⟩
      (A.blockSequence m)

/-- Exact random-valued mass at every retained finite stage. -/
theorem graphonRandomMass_blockGraphon
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) :
    graphonRandomMass (A.blockGraphon m) =
      ((k - 2 : ℕ) : ℝ) * A.blockMass m := by
  rw [A.blockGraphon_eq]
  simpa only [blockMass] using
    graphonRandomMass_profileWLambda A.three_le_k
      ⟨A.extremalApproximation.profile.randomMean_pos,
        A.extremalApproximation.profile.randomMean_lt_one⟩
      (A.blockSequence m)

/-- Exact nonzero mass at every retained finite stage. -/
theorem graphonNonzeroMass_blockGraphon
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) :
    graphonNonzeroMass (A.blockGraphon m) =
      ((k - 1 : ℕ) : ℝ) * A.blockMass m := by
  rw [A.blockGraphon_eq]
  simpa only [blockMass] using
    graphonNonzeroMass_profileWLambda A.three_le_k
      ⟨A.extremalApproximation.profile.randomMean_pos,
        A.extremalApproximation.profile.randomMean_lt_one⟩
      (A.blockSequence m)

/-- Every retained block graphon is almost everywhere valued in the same
three-point palette as the optimizer profile. -/
theorem blockGraphon_ae_threeValued
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) :
    ∀ᵐ z ∂unitSquareMeasure,
      (A.blockGraphon m).value z = 0 ∨
        (A.blockGraphon m).value z =
          A.extremalApproximation.profile.randomMean ∨
            (A.blockGraphon m).value z = 1 := by
  rw [A.blockGraphon_eq]
  exact profileWLambda_ae_threeValued
    A.extremalApproximation.profile.randomMean (A.blockSequence m)
    ⟨A.extremalApproximation.profile.randomMean_pos.le,
      A.extremalApproximation.profile.randomMean_lt_one.le⟩

/-- The actual one-valued regions of the retained block graphons converge to
the target one-valued mass. -/
theorem graphonOneMass_tendsto
    (A : OptimizerFiniteBlockApproximationResult k γ W) :
    Tendsto (fun m ↦ graphonOneMass (A.blockGraphon m)) atTop
      (𝓝 (graphonOneMass A.extremalApproximation.target)) := by
  apply A.blockMass_tendsto.congr'
  filter_upwards [] with m
  exact (A.graphonOneMass_blockGraphon m).symm

/-- The actual random-valued regions of the retained block graphons converge
to the target random-valued mass. -/
theorem graphonRandomMass_tendsto
    (A : OptimizerFiniteBlockApproximationResult k γ W) :
    Tendsto (fun m ↦ graphonRandomMass (A.blockGraphon m)) atTop
      (𝓝 (graphonRandomMass A.extremalApproximation.target)) := by
  apply A.randomMass_tendsto.congr'
  filter_upwards [] with m
  exact (A.graphonRandomMass_blockGraphon m).symm

/-- The scaled block mass converges to the target's exact nonzero mass. -/
theorem scaledBlockMass_tendsto_nonzeroMass
    (A : OptimizerFiniteBlockApproximationResult k γ W) :
    Tendsto (fun m ↦ ((k - 1 : ℕ) : ℝ) * A.blockMass m) atTop
      (𝓝 (graphonNonzeroMass A.extremalApproximation.target)) := by
  apply A.nonzeroMass_tendsto.congr'
  filter_upwards [] with m
  rw [A.graphonNonzeroMass_blockGraphon m]

/-- The target nonzero region is exactly the disjoint union of its random and
one-valued regions. -/
theorem target_nonzeroMass_eq_oneMass_add_randomMass
    (A : OptimizerFiniteBlockApproximationResult k γ W) :
    graphonNonzeroMass A.extremalApproximation.target =
      graphonOneMass A.extremalApproximation.target +
        graphonRandomMass A.extremalApproximation.target :=
  graphonNonzeroMass_eq_oneMass_add_randomMass _

/-- Equivalently, the scaled finite block mass converges to the sum of the
target's one-valued and random-valued masses. -/
theorem scaledBlockMass_tendsto_oneMass_add_randomMass
    (A : OptimizerFiniteBlockApproximationResult k γ W) :
    Tendsto (fun m ↦ ((k - 1 : ℕ) : ℝ) * A.blockMass m) atTop
      (𝓝 (graphonOneMass A.extremalApproximation.target +
        graphonRandomMass A.extremalApproximation.target)) := by
  simpa only [A.target_nonzeroMass_eq_oneMass_add_randomMass] using
    A.scaledBlockMass_tendsto_nonzeroMass

/-! ### Subcritical finite stages -/

/-- The distinguished optimizer profile value is `pK` below the phase
transition. -/
theorem randomMean_eq_pK_of_lt_gammaK
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hsub : γ < gammaK k) :
    A.extremalApproximation.profile.randomMean = pK k :=
  A.extremalApproximation.profile.randomMean_eq_of_lt_gammaK
    A.three_le_k hγ hsub

/-- Every subcritical finite stage is literally an existing `WLambda`
graphon, with no limiting candidate asserted. -/
theorem blockGraphon_eq_WLambda_of_lt_gammaK
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hsub : γ < gammaK k) (m : ℕ) :
    A.blockGraphon m = WLambda A.three_le_k (A.blockSequence m) := by
  have hmean := A.randomMean_eq_pK_of_lt_gammaK hγ hsub
  rw [A.blockGraphon_eq]
  simpa only [hmean] using
    profileWLambda_pK A.three_le_k (A.blockSequence m)

/-- Density naturally carried by the `m`th subcritical finite candidate. -/
def subcriticalStageDensity
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) : ℝ :=
  (1 + ((k - 2 : ℕ) : ℝ) * pK k) * A.blockMass m

theorem graphonEdgeDensity_blockGraphon_eq_subcriticalStageDensity
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hsub : γ < gammaK k) (m : ℕ) :
    graphonEdgeDensity (A.blockGraphon m) = A.subcriticalStageDensity m := by
  rw [A.blockGraphon_eq_WLambda_of_lt_gammaK hγ hsub m,
    WLambda_edgeDensity]
  rfl

theorem subcriticalStageDensity_tendsto
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hsub : γ < gammaK k) :
    Tendsto A.subcriticalStageDensity atTop (𝓝 γ) := by
  apply A.edgeDensity_tendsto.congr'
  filter_upwards [] with m
  exact A.graphonEdgeDensity_blockGraphon_eq_subcriticalStageDensity
    hγ hsub m

theorem subcriticalBlockMass_tendsto
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hsub : γ < gammaK k) :
    Tendsto A.blockMass atTop
      (𝓝 (γ / (1 + ((k - 2 : ℕ) : ℝ) * pK k))) := by
  change Tendsto (fun m ↦ (A.blockSequence m).mass) atTop _
  simpa only [
    A.extremalApproximation.profile.oneMass_eq_of_lt_gammaK hsub] using
      A.blockMass_tendsto

theorem eventually_subcriticalStageDensity_pos_lt_gammaK
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hsub : γ < gammaK k) :
    ∀ᶠ m in atTop,
      0 < A.subcriticalStageDensity m ∧
        A.subcriticalStageDensity m < gammaK k := by
  have h := A.subcriticalStageDensity_tendsto hγ hsub
  have hpos : ∀ᶠ m in atTop, 0 < A.subcriticalStageDensity m :=
    (tendsto_order.1 h).1 0 hγ.1
  have hlt : ∀ᶠ m in atTop, A.subcriticalStageDensity m < gammaK k :=
    (tendsto_order.1 h).2 (gammaK k) hsub
  exact hpos.and hlt

/-- Every sufficiently late subcritical stage belongs to the candidate family
at its own exact finite-stage density. -/
theorem eventually_WLambda_mem_candidateOptimizerFamily
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hsub : γ < gammaK k) :
    ∀ᶠ m in atTop,
      WLambda A.three_le_k (A.blockSequence m) ∈
        candidateOptimizerFamily k (A.subcriticalStageDensity m) := by
  filter_upwards [A.eventually_subcriticalStageDensity_pos_lt_gammaK
      hγ hsub] with m hm
  have hmIoo : A.subcriticalStageDensity m ∈ Ioo (0 : ℝ) 1 :=
    ⟨hm.1, hm.2.trans (gammaK_lt_one A.three_le_k)⟩
  rw [candidateOptimizerFamily_of_lt A.three_le_k hmIoo hm.2]
  refine ⟨A.blockSequence m, ?_, rfl⟩
  unfold IsSubcriticalCandidate
  change (A.blockSequence m).mass =
    A.subcriticalStageDensity m /
      (1 + ((k - 2 : ℕ) : ℝ) * pK k)
  unfold subcriticalStageDensity blockMass
  have hden :
      (1 + ((k - 2 : ℕ) : ℝ) * pK k) ≠ 0 := by
    have hp : 0 < pK k := pK_pos
      (le_trans (by norm_num : 2 ≤ 3) A.three_le_k)
    positivity
  field_simp [hden]

/-! ### Critical and supercritical concentration inputs -/

/-- Explicit profile mean on the critical/supercritical branch. -/
theorem randomMean_eq_of_gammaK_le
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hcrit : gammaK k ≤ γ) :
    A.extremalApproximation.profile.randomMean =
      ((((k - 1 : ℕ) : ℝ) * γ - 1) / ((k - 2 : ℕ) : ℝ)) :=
  A.extremalApproximation.profile.randomMean_eq_of_gammaK_le
    A.three_le_k hcrit

/-- The target nonzero mass is one on the critical/supercritical branch. -/
theorem target_oneMass_add_randomMass_eq_one_of_gammaK_le
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hcrit : gammaK k ≤ γ) :
    graphonOneMass A.extremalApproximation.target +
        graphonRandomMass A.extremalApproximation.target = 1 :=
  A.extremalApproximation.profile.mass_sum_eq_one_of_gammaK_le
    A.three_le_k hcrit

theorem target_nonzeroMass_eq_one_of_gammaK_le
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hcrit : gammaK k ≤ γ) :
    graphonNonzeroMass A.extremalApproximation.target = 1 := by
  rw [A.target_nonzeroMass_eq_oneMass_add_randomMass,
    A.target_oneMass_add_randomMass_eq_one_of_gammaK_le hcrit]

/-- At and above the transition, the scaled block mass tends to one. -/
theorem criticalScaledBlockMass_tendsto_one
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hcrit : gammaK k ≤ γ) :
    Tendsto (fun m ↦ ((k - 1 : ℕ) : ℝ) * A.blockMass m)
      atTop (𝓝 1) := by
  have h := (tendsto_const_nhds
    (x := ((k - 1 : ℕ) : ℝ))).mul A.blockMass_tendsto
  have hmass :=
    A.extremalApproximation.profile.oneMass_eq_of_gammaK_le
      A.three_le_k hcrit
  rw [hmass] at h
  have hkne : ((k - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (kSubOne_pos A.three_le_k).ne'
  simpa only [blockMass, mul_div_cancel₀ 1 hkne] using h

/-- The sum of squared component lengths tends to one in the critical and
supercritical regimes. -/
theorem criticalBlockLengthSquareSum_tendsto_one
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hcrit : gammaK k ≤ γ) :
    Tendsto A.blockLengthSquareSum atTop (𝓝 1) := by
  apply Filter.Tendsto.squeeze
    (A.criticalScaledBlockMass_tendsto_one hcrit) tendsto_const_nhds
  · intro m
    simpa only [blockLengthSquareSum, blockMass_eq_model_blockMass] using
      (A.model m).k_sub_one_mul_blockMass_le_blockLengthSquareSum
  · intro m
    exact (A.model m).blockLengthSquareSum_le_sum_sq.trans
      (A.model m).blockLengthSum_sq_le_one

/-- The largest ordered component length tends to one. -/
theorem criticalLargestBlockLength_tendsto_one
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hcrit : gammaK k ≤ γ) :
    Tendsto A.largestBlockLength atTop (𝓝 1) := by
  apply Filter.Tendsto.squeeze
    (A.criticalBlockLengthSquareSum_tendsto_one hcrit)
    tendsto_const_nhds
  · intro m
    exact (A.model m).blockLengthSquareSum_le_largest_mul_sum.trans
      (A.model m).largest_mul_sum_le_largest
  · intro m
    exact (A.model m).largestBlockLength_le_one

/-- The total normalized length outside the largest component tends to zero. -/
theorem criticalTailBlockLength_tendsto_zero
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hcrit : gammaK k ≤ γ) :
    Tendsto A.tailBlockLength atTop (𝓝 0) := by
  have hupper : Tendsto (fun m ↦ 1 - A.largestBlockLength m)
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    simpa using hconst.sub
      (A.criticalLargestBlockLength_tendsto_one hcrit)
  apply squeeze_zero
  · intro m
    exact (A.model m).tailBlockLength_nonneg
  · intro m
    exact (A.model m).tailBlockLength_le_one_sub_largest
  · exact hupper

end OptimizerFiniteBlockApproximationResult

/-! ## Assembly from the two coordinate-sensitive convergence inputs -/

/-- Once cut convergence and block-mass convergence have been established by
finite equalization, every remaining functional limit follows from the exact
profile formulas.  In particular the random-mass limit is derived from the
optimizer profile's saturation equality rather than supplied independently. -/
noncomputable def optimizerFiniteBlockApproximation_of_tendsto
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (R : OptimizerExtremalApproximationResult k γ W) (hk : 3 ≤ k)
    (hcut : Tendsto
      (fun m ↦ cutDist (R.blockProfileGraphon hk m) R.target)
      atTop (𝓝 0))
    (hmass : Tendsto (fun m ↦ R.blockMass hk m) atTop
      (𝓝 (graphonOneMass R.target))) :
    OptimizerFiniteBlockApproximationResult k γ W := by
  let p := R.profile.randomMean
  let d : ℝ := ((k - 2 : ℕ) : ℝ)
  let model := fun m ↦ R.finiteBlockModel hk m
  let blocks := fun m ↦ R.blockSequence hk m
  let graphs := fun m ↦ R.blockProfileGraphon hk m
  have hmassSeq : Tendsto (fun m ↦ (blocks m).mass) atTop
      (𝓝 (graphonOneMass R.target)) := by
    apply hmass.congr'
    filter_upwards [] with m
    rfl
  have hrandom : Tendsto (fun m ↦ d * (blocks m).mass) atTop
      (𝓝 (graphonRandomMass R.target)) := by
    have hmul := (tendsto_const_nhds (x := d)).mul hmassSeq
    simpa only [d,
      R.profile.randomMass_eq_delta_mul_oneMass] using hmul
  have hedgeLimit :
      (1 + d * p) * graphonOneMass R.target = γ := by
    calc
      (1 + d * p) * graphonOneMass R.target =
          graphonOneMass R.target +
            p * graphonRandomMass R.target := by
        rw [R.profile.randomMass_eq_delta_mul_oneMass]
        ring
      _ = γ := R.profile.edgeDensity_decomposition.symm
  have hedge : Tendsto
      (fun m ↦ graphonEdgeDensity (graphs m)) atTop (𝓝 γ) := by
    have hmul :=
      (tendsto_const_nhds (x := (1 + d * p))).mul hmassSeq
    rw [hedgeLimit] at hmul
    apply hmul.congr'
    filter_upwards [] with m
    simpa only [graphs, blocks, p, d,
      OptimizerExtremalApproximationResult.blockSequence,
      OptimizerExtremalApproximationResult.blockMass,
      FiniteExtremalBlockModel.blockMass] using
      (R.graphonEdgeDensity_blockProfileGraphon hk m).symm
  have hp : p ∈ Ioo (0 : ℝ) 1 :=
    ⟨R.profile.randomMean_pos, R.profile.randomMean_lt_one⟩
  have hentropyLimit :
      (d * binaryEntropy p) * graphonOneMass R.target =
        entropyDensity k γ := by
    calc
      (d * binaryEntropy p) * graphonOneMass R.target =
          binaryEntropy p * (d * graphonOneMass R.target) := by ring
      _ = binaryEntropy p * graphonRandomMass R.target := by
        rw [R.profile.randomMass_eq_delta_mul_oneMass]
      _ = graphonEntropy R.target :=
        (graphonEntropy_eq_binaryEntropy_mul_randomMass_of_threeValued
          hp R.profile.ae_threeValued).symm
      _ = entropyDensity k γ := R.profile.entropy_eq
  have hentropy : Tendsto
      (fun m ↦ graphonEntropy (graphs m)) atTop
      (𝓝 (entropyDensity k γ)) := by
    have hmul :=
      (tendsto_const_nhds (x := (d * binaryEntropy p))).mul hmassSeq
    rw [hentropyLimit] at hmul
    apply hmul.congr'
    filter_upwards [] with m
    simpa only [graphs, blocks, p, d,
      OptimizerExtremalApproximationResult.blockSequence,
      OptimizerExtremalApproximationResult.blockMass,
      FiniteExtremalBlockModel.blockMass] using
      (R.graphonEntropy_blockProfileGraphon hk m).symm
  have hnonzeroLimit :
      (((k - 1 : ℕ) : ℝ) * graphonOneMass R.target) =
        graphonNonzeroMass R.target := by
    rw [graphonNonzeroMass_eq_oneMass_add_randomMass,
      R.profile.randomMass_eq_delta_mul_oneMass]
    norm_num [Nat.cast_sub (show 1 ≤ k by omega),
      Nat.cast_sub (show 2 ≤ k by omega)]
    ring
  have hnonzero : Tendsto
      (fun m ↦ graphonNonzeroMass (graphs m)) atTop
      (𝓝 (graphonNonzeroMass R.target)) := by
    have hmul :=
      (tendsto_const_nhds (x := ((k - 1 : ℕ) : ℝ))).mul hmassSeq
    rw [hnonzeroLimit] at hmul
    apply hmul.congr'
    filter_upwards [] with m
    simpa only [graphs, blocks,
      OptimizerExtremalApproximationResult.blockSequence,
      OptimizerExtremalApproximationResult.blockMass,
      FiniteExtremalBlockModel.blockMass] using
      (R.graphonNonzeroMass_blockProfileGraphon hk m).symm
  exact {
    three_le_k := hk
    extremalApproximation := R
    model := model
    model_eq := fun _ ↦ rfl
    blockSequence := blocks
    blockSequence_eq := fun _ ↦ rfl
    blockGraphon := graphs
    blockGraphon_eq := fun _ ↦ rfl
    cut_tendsto := hcut
    blockMass_tendsto := hmassSeq
    randomMass_tendsto := hrandom
    edgeDensity_tendsto := hedge
    entropy_tendsto := hentropy
    nonzeroMass_tendsto := hnonzero
    componentCount_pos := fun m ↦ R.extremal_coreCount_pos m }

/-- Component decomposition and coordinate-safe block equalization for a
fixed-density optimizer, corresponding to the finite-block portion of the
proof of paper Proposition `prop:graphon-char-fixed-gamma`.

The result stops before extracting a limiting component sequence or proving
the reverse optimizer classification. -/
theorem existsOptimizerFiniteBlockApproximation
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (W : Graphon) (hW : W ∈ fixedDensityOptimizers k γ) :
    Nonempty (OptimizerFiniteBlockApproximationResult k γ W) := by
  obtain ⟨R⟩ := existsOptimizerExtremalApproximation k hk γ hγ W hW
  let p := R.profile.randomMean
  have hp : p ∈ Ioo (0 : ℝ) 1 :=
    ⟨R.profile.randomMean_pos, R.profile.randomMean_lt_one⟩
  have hcutError : Tendsto
      (fun m ↦ blockEqualizationError k (R.selectedClusterCount m))
      atTop (𝓝 0) :=
    blockEqualizationError_tendsto_zero k R.selectedClusterCount_tendsto
  have hcutUpper : Tendsto
      (fun m ↦ blockEqualizationError k (R.selectedClusterCount m) +
        graphonL1Dist (R.extremalProfileGraphon m) R.target)
      atTop (𝓝 0) := by
    simpa using hcutError.add R.extremalProfile_l1_tendsto
  have hcut : Tendsto
      (fun m ↦ cutDist (R.blockProfileGraphon hk m) R.target)
      atTop (𝓝 0) := by
    apply squeeze_zero
    · intro m
      exact cutDist_nonneg _ _
    · intro m
      calc
        cutDist (R.blockProfileGraphon hk m) R.target ≤
            cutDist (R.blockProfileGraphon hk m)
                (R.extremalProfileGraphon m) +
              cutDist (R.extremalProfileGraphon m) R.target :=
          cutDist_triangle _ _ _
        _ = cutDist (R.extremalProfileGraphon m)
              (R.blockProfileGraphon hk m) +
            cutDist (R.extremalProfileGraphon m) R.target := by
          rw [cutDist_comm (R.blockProfileGraphon hk m)]
        _ ≤ blockEqualizationError k (R.selectedClusterCount m) +
            graphonL1Dist (R.extremalProfileGraphon m) R.target :=
          add_le_add
            (R.cutDist_extremalProfile_blockProfileGraphon_le hk m)
            (cutDist_le_graphonL1Dist _ _)
    · exact hcutUpper
  have hmassError : Tendsto
      (fun m ↦ blockEqualizationMassError k
        (R.selectedClusterCount m) p) atTop (𝓝 0) :=
    blockEqualizationMassError_tendsto_zero k hp
      R.selectedClusterCount_tendsto
  have hmassLower : Tendsto
      (fun m ↦ (R.extremalColoring m).normalizedBlueDiagonalArea -
        blockEqualizationMassError k (R.selectedClusterCount m) p)
      atTop (𝓝 (graphonOneMass R.target)) := by
    simpa using R.extremalBlueArea_tendsto.sub hmassError
  have hmassUpper : Tendsto
      (fun m ↦ (R.extremalColoring m).normalizedBlueDiagonalArea +
        blockEqualizationMassError k (R.selectedClusterCount m) p)
      atTop (𝓝 (graphonOneMass R.target)) := by
    simpa using R.extremalBlueArea_tendsto.add hmassError
  have hmass : Tendsto (fun m ↦ R.blockMass hk m) atTop
      (𝓝 (graphonOneMass R.target)) := by
    apply Filter.Tendsto.squeeze hmassLower hmassUpper
    · intro m
      have hm := (abs_le.mp
        (R.blockMass_sub_normalizedBlueDiagonalArea_abs_le hk m)).1
      change _ ≤ R.blockMass hk m
      dsimp only [p] at hm ⊢
      linarith
    · intro m
      have hm := (abs_le.mp
        (R.blockMass_sub_normalizedBlueDiagonalArea_abs_le hk m)).2
      change R.blockMass hk m ≤ _
      dsimp only [p] at hm ⊢
      linarith
  exact ⟨optimizerFiniteBlockApproximation_of_tendsto R hk hcut hmass⟩

end InducedStars
