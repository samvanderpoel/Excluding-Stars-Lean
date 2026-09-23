import InducedStars.Graphon.OptimizerProfile
import InducedStars.Graphon.GraphonMantel
import InducedStars.Graphon.ColorProfile
import Mathlib.Tactic

/-!
# Type-profile approximation

This file formalizes the fixed threshold and pointwise rounding operation used
in the preparation for `prop:graphon-char-fixed-gamma`.  It then compares the
rounded profile graphon of a regularity Type with a discrete-valued target.
-/

noncomputable section

open Filter Finset MeasureTheory Set
open scoped ENNReal Topology unitInterval
open scoped symmDiff

namespace InducedStars

open ColoredGraph Regularity

/-! ## A fixed threshold attached to an optimizer profile -/

/-- The fixed Type threshold used for an optimizer profile.  It is chosen once
from the profile's random value, rather than varying along an approximating
sequence. -/
def optimizerTypeThreshold {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W) : ℝ :=
  min (P.randomMean / 4) ((1 - P.randomMean) / 4)

theorem optimizerTypeThreshold_pos {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W) :
    0 < optimizerTypeThreshold P := by
  rw [optimizerTypeThreshold, lt_min_iff]
  constructor <;> nlinarith [P.randomMean_pos, P.randomMean_lt_one]

theorem optimizerTypeThreshold_le_randomMean_div_four
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W) :
    optimizerTypeThreshold P ≤ P.randomMean / 4 := by
  exact min_le_left _ _

theorem optimizerTypeThreshold_le_one_sub_randomMean_div_four
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W) :
    optimizerTypeThreshold P ≤ (1 - P.randomMean) / 4 := by
  exact min_le_right _ _

theorem optimizerTypeThreshold_lt_quarter {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W) :
    optimizerTypeThreshold P < 1 / 4 := by
  calc
    optimizerTypeThreshold P ≤ P.randomMean / 4 :=
      optimizerTypeThreshold_le_randomMean_div_four P
    _ < 1 / 4 := by nlinarith [P.randomMean_lt_one]

theorem optimizerTypeThreshold_lt_half {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W) :
    optimizerTypeThreshold P < 1 / 2 := by
  nlinarith [optimizerTypeThreshold_lt_quarter P]

theorem two_mul_optimizerTypeThreshold_lt_randomMean
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W) :
    2 * optimizerTypeThreshold P < P.randomMean := by
  have h := optimizerTypeThreshold_le_randomMean_div_four P
  nlinarith [P.randomMean_pos]

theorem two_mul_optimizerTypeThreshold_lt_one_sub_randomMean
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W) :
    2 * optimizerTypeThreshold P < 1 - P.randomMean := by
  have h := optimizerTypeThreshold_le_one_sub_randomMean_div_four P
  nlinarith [P.randomMean_lt_one]

theorem optimizerTypeThreshold_lt_randomMean
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W) :
    optimizerTypeThreshold P < P.randomMean := by
  nlinarith [optimizerTypeThreshold_pos P,
    two_mul_optimizerTypeThreshold_lt_randomMean P]

theorem randomMean_lt_one_sub_optimizerTypeThreshold
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W) :
    P.randomMean < 1 - optimizerTypeThreshold P := by
  nlinarith [optimizerTypeThreshold_pos P,
    two_mul_optimizerTypeThreshold_lt_one_sub_randomMean P]

/-! ## The paper's rounding map -/

/-- Round a density to the discrete profile palette `{0,p,1}`, with the same
strict/weak threshold convention as `Regularity.densityEdgeColor`. -/
def profileRound (p θ t : ℝ) : ℝ :=
  if t < θ then 0 else if t ≤ 1 - θ then p else 1

@[simp] theorem profileRound_of_lt {p θ t : ℝ} (h : t < θ) :
    profileRound p θ t = 0 := by
  simp [profileRound, h]

@[simp] theorem profileRound_of_mem {p θ t : ℝ}
    (h₁ : θ ≤ t) (h₂ : t ≤ 1 - θ) :
    profileRound p θ t = p := by
  simp [profileRound, not_lt_of_ge h₁, h₂]

@[simp] theorem profileRound_of_one_sub_lt {p θ t : ℝ}
    (hθ : θ ≤ 1 / 2) (h : 1 - θ < t) :
    profileRound p θ t = 1 := by
  have hnot : ¬t < θ := by linarith
  simp [profileRound, hnot, not_le_of_gt h]

@[measurability] theorem measurable_profileRound (p θ : ℝ) :
    Measurable (profileRound p θ) := by
  unfold profileRound
  refine Measurable.ite measurableSet_Iio measurable_const ?_
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

theorem profileRound_mem_Icc {p θ t : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    profileRound p θ t ∈ Icc (0 : ℝ) 1 := by
  by_cases h₁ : t < θ
  · simp [profileRound, h₁]
  · by_cases h₂ : t ≤ 1 - θ
    · simpa [profileRound, h₁, h₂] using hp
    · simp [profileRound, h₁, h₂]

/-- Quantitative form of the paper's discrete-target rounding estimate.  The
constant `2 / θ` works uniformly for all three target values. -/
theorem profileRound_discreteTarget_le {p θ t s : ℝ}
    (hp : 0 < p) (hp_one : p < 1) (hθ : 0 < θ)
    (hsep₀ : 2 * θ < p) (hsep₁ : 2 * θ < 1 - p)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hs : s = 0 ∨ s = p ∨ s = 1) :
    |profileRound p θ t - s| ≤ (2 / θ) * |t - s| := by
  have hθhalf : θ ≤ 1 / 2 := by nlinarith
  have hθone : θ < 1 := by nlinarith
  rcases hs with hs | hs | hs <;> subst s
  · by_cases hlow : t < θ
    · rw [profileRound_of_lt hlow]
      simp only [sub_zero, abs_zero]
      positivity
    · by_cases hupp : t ≤ 1 - θ
      · rw [profileRound_of_mem (le_of_not_gt hlow) hupp]
        rw [sub_zero, abs_of_pos hp, sub_zero, abs_of_nonneg ht.1,
          div_mul_eq_mul_div, le_div_iff₀ hθ]
        nlinarith
      · have hupp' : 1 - θ < t := lt_of_not_ge hupp
        rw [profileRound_of_one_sub_lt hθhalf hupp']
        rw [sub_zero, abs_one, sub_zero, abs_of_nonneg ht.1,
          div_mul_eq_mul_div, le_div_iff₀ hθ]
        nlinarith
  · by_cases hlow : t < θ
    · rw [profileRound_of_lt hlow, zero_sub, abs_neg, abs_of_pos hp]
      rw [abs_of_nonpos (by nlinarith : t - p ≤ 0),
        div_mul_eq_mul_div, le_div_iff₀ hθ]
      nlinarith
    · by_cases hupp : t ≤ 1 - θ
      · rw [profileRound_of_mem (le_of_not_gt hlow) hupp]
        simp only [sub_self, abs_zero]
        positivity
      · have hupp' : 1 - θ < t := lt_of_not_ge hupp
        rw [profileRound_of_one_sub_lt hθhalf hupp']
        rw [abs_of_nonneg (by nlinarith : 0 ≤ 1 - p),
          abs_of_nonneg (by nlinarith : 0 ≤ t - p),
          div_mul_eq_mul_div, le_div_iff₀ hθ]
        nlinarith
  · by_cases hlow : t < θ
    · rw [profileRound_of_lt hlow, zero_sub, abs_neg, abs_one]
      rw [abs_of_nonpos (by linarith [ht.2] : t - 1 ≤ 0),
        div_mul_eq_mul_div, le_div_iff₀ hθ]
      nlinarith
    · by_cases hupp : t ≤ 1 - θ
      · rw [profileRound_of_mem (le_of_not_gt hlow) hupp]
        rw [abs_of_nonpos (by linarith : p - 1 ≤ 0),
          abs_of_nonpos (by linarith : t - 1 ≤ 0),
          div_mul_eq_mul_div, le_div_iff₀ hθ]
        nlinarith
      · have hupp' : 1 - θ < t := lt_of_not_ge hupp
        rw [profileRound_of_one_sub_lt hθhalf hupp']
        simp only [sub_self, abs_zero]
        positivity

/-! ## An `L¹` comparison outside a measurable error set -/

/-- A pointwise Lipschitz comparison off a measurable exceptional set gives
an explicit graphon `L¹` estimate.  On the exceptional set we use only that
graphon values lie in `[0,1]`. -/
theorem graphonL1Dist_le_mul_add_measure_of_ae_off
    (A T U : Graphon) {c : ℝ} (hc : 0 ≤ c)
    {s : Set UnitSquare} (hs : MeasurableSet s)
    (hpoint : ∀ᵐ z ∂unitSquareMeasure, z ∉ s →
      |A.value z - U.value z| ≤ c * |T.value z - U.value z|) :
    graphonL1Dist A U ≤
      c * graphonL1Dist T U + unitSquareMeasure.real s := by
  let f : UnitSquare → ℝ := fun z ↦ |A.value z - U.value z|
  let g : UnitSquare → ℝ := fun z ↦ |T.value z - U.value z|
  have hf : Integrable f unitSquareMeasure :=
    (A.integrable_value.sub U.integrable_value).abs
  have hg : Integrable g unitSquareMeasure :=
    (T.integrable_value.sub U.integrable_value).abs
  have hbad : (∫ z in s, f z ∂unitSquareMeasure) ≤
      unitSquareMeasure.real s := by
    calc
      (∫ z in s, f z ∂unitSquareMeasure) ≤
          ∫ _z in s, (1 : ℝ) ∂unitSquareMeasure := by
        apply setIntegral_mono_on hf.integrableOn
          (integrable_const (1 : ℝ)).integrableOn hs
        intro z _hz
        dsimp [f]
        rw [abs_le]
        constructor <;> nlinarith [A.value_nonneg z, A.value_le_one z,
          U.value_nonneg z, U.value_le_one z]
      _ = unitSquareMeasure.real s := by simp [hs]
  have hgood : (∫ z in sᶜ, f z ∂unitSquareMeasure) ≤
      ∫ z in sᶜ, c * g z ∂unitSquareMeasure := by
    apply setIntegral_mono_on_ae hf.integrableOn
      (hg.const_mul c).integrableOn hs.compl
    filter_upwards [hpoint] with z hz
    intro hzs
    exact hz hzs
  have hg_compl : (∫ z in sᶜ, g z ∂unitSquareMeasure) ≤
      ∫ z, g z ∂unitSquareMeasure :=
    setIntegral_le_integral hg (Eventually.of_forall fun z ↦ abs_nonneg _)
  have hvalue_AU : graphonL1Dist A U =
      ∫ z, f z ∂unitSquareMeasure := by
    rw [graphonL1Dist_eq_integral]
    apply integral_congr_ae
    filter_upwards [A.value_ae_eq, U.value_ae_eq] with z hA hU
    simp only [f]
    rw [hA, hU]
  have hvalue_TU : graphonL1Dist T U =
      ∫ z, g z ∂unitSquareMeasure := by
    rw [graphonL1Dist_eq_integral]
    apply integral_congr_ae
    filter_upwards [T.value_ae_eq, U.value_ae_eq] with z hT hU
    simp only [g]
    rw [hT, hU]
  rw [hvalue_AU, hvalue_TU]
  calc
    (∫ z, f z ∂unitSquareMeasure) =
        (∫ z in s, f z ∂unitSquareMeasure) +
          ∫ z in sᶜ, f z ∂unitSquareMeasure :=
      (integral_add_compl hs hf).symm
    _ ≤ unitSquareMeasure.real s +
          ∫ z in sᶜ, c * g z ∂unitSquareMeasure :=
      add_le_add hbad hgood
    _ = unitSquareMeasure.real s +
          c * ∫ z in sᶜ, g z ∂unitSquareMeasure := by
      rw [integral_const_mul]
    _ ≤ unitSquareMeasure.real s + c * ∫ z, g z ∂unitSquareMeasure := by
      gcongr
    _ = c * (∫ z, g z ∂unitSquareMeasure) +
          unitSquareMeasure.real s := by ring

/-! ## Rounding the cells of a regularity Type -/

/-- On a regular off-diagonal cluster pair, the profile value of the
completed Type coloring is exactly the paper's rounding of the pair density.
Reduced nonedges and diagonal cells are deliberately excluded. -/
theorem profileColorMatrix_typeCompleteColoring_eq_profileRound
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {η θ : ℝ} {ℓ : ℕ} (p : ℝ) (T : RegularityType G η θ ℓ)
    {i j : Fin T.partition.clusterCount}
    (hregular : i ≠ j ∧
      IsRegularPair G η (T.partition.clusters i) (T.partition.clusters j)) :
    profileColorMatrix p (typeCompleteColoring T) i j =
      profileRound p θ
        (graphDensity G (T.partition.clusters i) (T.partition.clusters j)) := by
  let d := graphDensity G (T.partition.clusters i) (T.partition.clusters j)
  have hadj : T.coloredGraph.graph.Adj i j := by
    exact (T.partition.regularPairGraph_adj i j).2 hregular
  cases hcolor : (typeCompleteColoring T).color i j with
  | red =>
      obtain ⟨h, hred⟩ :=
        (typeCompleteColoring_color_eq_red_iff T i j).1 hcolor
      have hd : θ ≤ d ∧ d ≤ 1 - θ :=
        (edgeColor_eq_red_iff T.partition T.delta_lt_half.le
          T.vertexColor h).1 hred
      simp only [profileColorMatrix_apply, hcolor, profileColorValue_red]
      exact (profileRound_of_mem hd.1 hd.2).symm
  | green =>
      obtain ⟨h, hgreen⟩ :=
        (typeCompleteColoring_color_eq_green_iff T i j).1 hcolor
      have hd : d < θ :=
        (edgeColor_eq_green_iff T.partition T.delta_lt_half.le
          T.vertexColor h).1 hgreen
      simp only [profileColorMatrix_apply, hcolor, profileColorValue_green]
      exact (profileRound_of_lt hd).symm
  | blue =>
      rcases (typeCompleteColoring_color_eq_blue_iff T i j).1 hcolor with
        hnonedge | ⟨h, hblue⟩
      · exact (hnonedge hadj).elim
      · have hd : 1 - θ < d :=
          (edgeColor_eq_blue_iff T.partition T.delta_lt_half.le
            T.vertexColor h).1 hblue
        simp only [profileColorMatrix_apply, hcolor, profileColorValue_blue]
        exact (profileRound_of_one_sub_lt T.delta_lt_half.le hd).symm

/-- Simultaneous cell formula for the canonical values of a finite profile
graphon. -/
theorem profileColoringGraphon_value_ae_eq_on_all_cells
    {q : ℕ} (p : ℝ) (C : ColoredGraph (Fin q))
    (hp : p ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂unitSquareMeasure,
      ∀ i j : Fin q, z ∈ equalCell i ×ˢ equalCell j →
        (profileColoringGraphon p C hp).value z =
          profileColorMatrix p C i j := by
  apply Filter.eventually_all.2
  intro i
  apply Filter.eventually_all.2
  intro j
  simpa only [profileColorMatrix_apply] using
    profileColoringGraphon_ae_eq_on_cell p C hp i j

/-- Explicit Type-profile approximation estimate.  Regular off-diagonal
cells obey the rounding estimate; the only finite structural errors are the
irregular cells and diagonal cells recorded by `badClusterPairs`. -/
theorem graphonL1Dist_typeProfileGraphon_le
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {η θ : ℝ} {ℓ : ℕ} (T : RegularityType G η θ ℓ)
    (hq : 0 < T.partition.clusterCount)
    {p : ℝ} (hp : 0 < p) (hp_one : p < 1)
    (hsep₀ : 2 * θ < p) (hsep₁ : 2 * θ < 1 - p)
    (U : Graphon)
    (hU : ∀ᵐ z ∂unitSquareMeasure,
      U.value z = 0 ∨ U.value z = p ∨ U.value z = 1) :
    graphonL1Dist
        (profileColoringGraphon p (typeCompleteColoring T)
          ⟨hp.le, hp_one.le⟩) U ≤
      (2 / θ) * graphonL1Dist (typeGraphon T) U +
        2 * η + 1 / (T.partition.clusterCount : ℝ) := by
  let C := typeCompleteColoring T
  let A := profileColoringGraphon p C ⟨hp.le, hp_one.le⟩
  let s := equalCellPairRegion (badClusterPairs η T.partition)
  have hpoint : ∀ᵐ z ∂unitSquareMeasure, z ∉ s →
      |A.value z - U.value z| ≤
        (2 / θ) * |(typeGraphon T).value z - U.value z| := by
    filter_upwards
      [profileColoringGraphon_value_ae_eq_on_all_cells
        p C ⟨hp.le, hp_one.le⟩,
       typeGraphon_value_ae_eq_on_all_cells T,
       ae_mem_iUnion_equalCell_prod hq,
       hU] with z hA hT hcover hzU
    intro hzGood
    obtain ⟨ij, hzij⟩ := Set.mem_iUnion.mp hcover
    let i := ij.1
    let j := ij.2
    have hzCell : z ∈ equalCell i ×ˢ equalCell j := hzij
    have hijGood : (i, j) ∉ badClusterPairs η T.partition := by
      intro hijBad
      apply hzGood
      simp only [s, equalCellPairRegion, Set.mem_iUnion]
      exact ⟨(i, j), hijBad, hzCell⟩
    have hregular : i ≠ j ∧
        IsRegularPair G η (T.partition.clusters i) (T.partition.clusters j) := by
      simpa only [badClusterPairs, Finset.mem_filter, Finset.mem_univ,
        true_and, not_or, not_not] using hijGood
    have hmatrix : profileColorMatrix p C i j =
        profileRound p θ
          (graphDensity G (T.partition.clusters i) (T.partition.clusters j)) := by
      exact profileColorMatrix_typeCompleteColoring_eq_profileRound p T hregular
    have hAcell : A.value z = profileColorMatrix p C i j := hA i j hzCell
    have hTcell : (typeGraphon T).value z =
        graphDensity G (T.partition.clusters i) (T.partition.clusters j) :=
      hT i j hzCell
    rw [hAcell, hTcell, hmatrix]
    exact profileRound_discreteTarget_le hp hp_one T.delta_pos
      hsep₀ hsep₁
      ⟨graphDensity_nonneg G _ _, graphDensity_le_one G _ _⟩ hzU
  have hraw := graphonL1Dist_le_mul_add_measure_of_ae_off
    A (typeGraphon T) U (div_nonneg (by norm_num) T.delta_pos.le)
      (measurableSet_equalCellPairRegion (badClusterPairs η T.partition)) hpoint
  have harea : unitSquareMeasure.real s ≤
      1 / (T.partition.clusterCount : ℝ) + 2 * η := by
    rw [show unitSquareMeasure.real s =
        ((badClusterPairs η T.partition).card : ℝ) *
          (1 / (T.partition.clusterCount : ℝ)) ^ 2 by
      exact measureReal_equalCellPairRegion hq _]
    exact badClusterPairs_area_le T.partition hq T.epsilon_pos.le
  change graphonL1Dist A U ≤ _
  calc
    graphonL1Dist A U ≤
        (2 / θ) * graphonL1Dist (typeGraphon T) U +
          unitSquareMeasure.real s := hraw
    _ ≤ (2 / θ) * graphonL1Dist (typeGraphon T) U +
          (1 / (T.partition.clusterCount : ℝ) + 2 * η) := by
      gcongr
    _ = (2 / θ) * graphonL1Dist (typeGraphon T) U +
          2 * η + 1 / (T.partition.clusterCount : ℝ) := by ring

/-! ## Stability of value-region masses for a separated palette -/

/-- For graphons that are almost everywhere `{0,p,1}`-valued, the random
region masses are Lipschitz in `L¹`, with the exact palette separation in the
denominator.  No continuity statement for arbitrary graphons is used. -/
theorem graphonRandomMass_sub_abs_le_graphonL1Dist_div_min
    (U V : Graphon) {p : ℝ} (hp : 0 < p) (hp_one : p < 1)
    (hU : ∀ᵐ z ∂unitSquareMeasure,
      U.value z = 0 ∨ U.value z = p ∨ U.value z = 1)
    (hV : ∀ᵐ z ∂unitSquareMeasure,
      V.value z = 0 ∨ V.value z = p ∨ V.value z = 1) :
    |graphonRandomMass U - graphonRandomMass V| ≤
      graphonL1Dist U V / min p (1 - p) := by
  have hsep : 0 < min p (1 - p) := by
    rw [lt_min_iff]
    exact ⟨hp, sub_pos.mpr hp_one⟩
  have hsubset :
      graphonRandomRegion U ∆ graphonRandomRegion V ≤ᵐ[unitSquareMeasure]
        graphonL1BadSet U V (min p (1 - p)) := by
    filter_upwards [hU, hV] with z hzU hzV
    have hURandom : z ∈ graphonRandomRegion U ↔ U.value z = p := by
      constructor
      · rintro ⟨hzpos, hzlt⟩
        rcases hzU with hz0 | hzp | hz1
        · nlinarith
        · exact hzp
        · nlinarith
      · intro hzp
        change 0 < U.value z ∧ U.value z < 1
        rw [hzp]
        exact ⟨hp, hp_one⟩
    have hVRandom : z ∈ graphonRandomRegion V ↔ V.value z = p := by
      constructor
      · rintro ⟨hzpos, hzlt⟩
        rcases hzV with hz0 | hzp | hz1
        · nlinarith
        · exact hzp
        · nlinarith
      · intro hzp
        change 0 < V.value z ∧ V.value z < 1
        rw [hzp]
        exact ⟨hp, hp_one⟩
    intro hz
    change z ∈ graphonRandomRegion U ∆ graphonRandomRegion V at hz
    rw [Set.mem_symmDiff, hURandom, hVRandom] at hz
    change min p (1 - p) ≤ |U.value z - V.value z|
    rcases hz with ⟨hUp, hVnp⟩ | ⟨hVp, hUnp⟩
    · rcases hzV with hV0 | hVp' | hV1
      · rw [hUp, hV0, sub_zero, abs_of_pos hp]
        exact min_le_left _ _
      · exact (hVnp hVp').elim
      · rw [hUp, hV1, abs_of_nonpos (by linarith)]
        simpa using min_le_right p (1 - p)
    · rcases hzU with hU0 | hUp' | hU1
      · rw [hU0, hVp, zero_sub, abs_neg, abs_of_pos hp]
        exact min_le_left _ _
      · exact (hUnp hUp').elim
      · rw [hU1, hVp, abs_of_nonneg (by linarith)]
        simpa using min_le_right p (1 - p)
  calc
    |graphonRandomMass U - graphonRandomMass V| ≤
        unitSquareMeasure.real
          (graphonRandomRegion U ∆ graphonRandomRegion V) := by
      exact abs_measureReal_sub_le_measureReal_symmDiff
        (measurableSet_graphonRandomRegion U).nullMeasurableSet
        (measurableSet_graphonRandomRegion V).nullMeasurableSet
    _ ≤ unitSquareMeasure.real
        (graphonL1BadSet U V (min p (1 - p))) :=
      measureReal_mono_ae hsubset
    _ ≤ graphonL1Dist U V / min p (1 - p) :=
      graphonL1BadSet_measure_le U V hsep

/-- The one-valued regions of two `{0,p,1}`-valued graphons have the sharper
separation denominator `1-p`. -/
theorem graphonOneMass_sub_abs_le_graphonL1Dist_div_one_sub
    (U V : Graphon) {p : ℝ} (hp : 0 < p) (hp_one : p < 1)
    (hU : ∀ᵐ z ∂unitSquareMeasure,
      U.value z = 0 ∨ U.value z = p ∨ U.value z = 1)
    (hV : ∀ᵐ z ∂unitSquareMeasure,
      V.value z = 0 ∨ V.value z = p ∨ V.value z = 1) :
    |graphonOneMass U - graphonOneMass V| ≤
      graphonL1Dist U V / (1 - p) := by
  have hsep : 0 < 1 - p := sub_pos.mpr hp_one
  have hsubset :
      graphonOneRegion U ∆ graphonOneRegion V ≤ᵐ[unitSquareMeasure]
        graphonL1BadSet U V (1 - p) := by
    filter_upwards [hU, hV] with z hzU hzV
    intro hz
    change z ∈ graphonOneRegion U ∆ graphonOneRegion V at hz
    rw [Set.mem_symmDiff] at hz
    change 1 - p ≤ |U.value z - V.value z|
    rcases hz with ⟨hU1, hVn1⟩ | ⟨hV1, hUn1⟩
    · change U.value z = 1 at hU1
      change V.value z ≠ 1 at hVn1
      rcases hzV with hV0 | hVp | hV1
      · rw [hU1, hV0, sub_zero, abs_one]
        linarith
      · rw [hU1, hVp, abs_of_nonneg (by linarith)]
      · exact (hVn1 hV1).elim
    · change V.value z = 1 at hV1
      change U.value z ≠ 1 at hUn1
      rcases hzU with hU0 | hUp | hU1
      · rw [hU0, hV1, zero_sub, abs_neg, abs_one]
        linarith
      · rw [hUp, hV1, abs_of_nonpos (by linarith)]
        nlinarith
      · exact (hUn1 hU1).elim
  calc
    |graphonOneMass U - graphonOneMass V| ≤
        unitSquareMeasure.real (graphonOneRegion U ∆ graphonOneRegion V) := by
      exact abs_measureReal_sub_le_measureReal_symmDiff
        (measurableSet_graphonOneRegion U).nullMeasurableSet
        (measurableSet_graphonOneRegion V).nullMeasurableSet
    _ ≤ unitSquareMeasure.real (graphonL1BadSet U V (1 - p)) :=
      measureReal_mono_ae hsubset
    _ ≤ graphonL1Dist U V / (1 - p) :=
      graphonL1BadSet_measure_le U V hsep

/-- Common-denominator version of one-region mass stability. -/
theorem graphonOneMass_sub_abs_le_graphonL1Dist_div_min
    (U V : Graphon) {p : ℝ} (hp : 0 < p) (hp_one : p < 1)
    (hU : ∀ᵐ z ∂unitSquareMeasure,
      U.value z = 0 ∨ U.value z = p ∨ U.value z = 1)
    (hV : ∀ᵐ z ∂unitSquareMeasure,
      V.value z = 0 ∨ V.value z = p ∨ V.value z = 1) :
    |graphonOneMass U - graphonOneMass V| ≤
      graphonL1Dist U V / min p (1 - p) := by
  have hL1 : 0 ≤ graphonL1Dist U V := graphonL1Dist_nonneg U V
  have hmin : 0 < min p (1 - p) := by
    rw [lt_min_iff]
    exact ⟨hp, sub_pos.mpr hp_one⟩
  calc
    |graphonOneMass U - graphonOneMass V| ≤
        graphonL1Dist U V / (1 - p) :=
      graphonOneMass_sub_abs_le_graphonL1Dist_div_one_sub
        U V hp hp_one hU hV
    _ ≤ graphonL1Dist U V / min p (1 - p) := by
      rw [div_le_div_iff₀ (sub_pos.mpr hp_one) hmin]
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) hL1

end InducedStars
