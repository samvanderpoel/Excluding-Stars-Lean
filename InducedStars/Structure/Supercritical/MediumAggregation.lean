import InducedStars.Structure.Supercritical.MediumRefinement
import InducedStars.Structure.Supercritical.MediumOverhead
import InducedStars.Structure.Supercritical.ProfileRealization
import Mathlib.Tactic

/-!
# Aggregating the supercritical medium-degree refinement

This file contains the deterministic summation and exponential bookkeeping
which turns a uniform estimate for each refinement fiber into an estimate for
the whole medium-degree family.  The probabilistic estimate itself is an
explicit hypothesis: no Janson input is used or hidden here.
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

/-! ## Restricting the occurring keys to an actual profile window -/

/-- The product of defect, witness, part, incident-pattern and *windowed*
profile data.  This is the precise auxiliary space needed after close
structure has placed every occurring cross profile in one common window. -/
def supercriticalMediumProfileWindowTupleFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n))
    (profileCenter : ℕ) (rho delta : ℝ) (budget : ℕ) :=
  ((((supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D).product
      (Finset.univ : Finset (Fin n))).product
      (Finset.univ : Finset (Fin (k - 1)))).product
      (Finset.powerset (Finset.univ : Finset (Fin n)))).product
      (supercriticalProfileWindowFinset
        D profileCenter rho delta budget)

/-- An occurring key whose profile is in the designated window belongs to
the corresponding finite windowed auxiliary product. -/
theorem supercriticalMediumRefinementTuple_mem_profileWindowAuxiliary
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {halpha : 0 < alpha}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profileCenter budget : ℕ} {rho delta : ℝ}
    {key : SupercriticalMediumRefinementKey D}
    (hkey : key ∈ supercriticalMediumRefinementKeyFinset
      k hk gamma hgamma alpha halpha m n tau hn D)
    (hprofile : SupercriticalProfileWindow
      D profileCenter rho delta budget key.profile) :
    supercriticalMediumRefinementTuple key ∈
      supercriticalMediumProfileWindowTupleFinset
        k hk gamma hgamma m n tau hn D profileCenter rho delta budget := by
  classical
  have haux := supercriticalMediumRefinementTuple_mem_auxiliary hkey
  rw [supercriticalMediumAuxiliaryTupleFinset] at haux
  rw [supercriticalMediumProfileWindowTupleFinset]
  exact Finset.mem_product.mpr
    ⟨(Finset.mem_product.mp haux).1,
      count_mem_supercriticalProfileWindowFinset hprofile⟩

/-- Close structure supplies the common window hypothesis for every key
which actually occurs.  This bridge keeps the later aggregation theorem free
to work with an abstract common window while recording how its hypothesis is
discharged in the canonical supercritical family. -/
theorem supercriticalMediumRefinementKey_profile_mem_window_of_closeStructureResult
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {structureAlpha delta epsilon : ℝ}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (hresult : ∀ G ∈ supercriticalMediumDegreeGraphFinset
      k hk gamma hgamma alpha m n tau hn D,
      Nonempty (SupercriticalCloseStructureResult
        k hk gamma structureAlpha delta epsilon hgamma G hn))
    {key : SupercriticalMediumRefinementKey D}
    (hkey : key ∈ supercriticalMediumRefinementKeyFinset
      k hk gamma hgamma alpha halpha m n tau hn D) :
    SupercriticalProfileWindow D m
      (supercriticalOffDiagonal k gamma) delta
      ⌊epsilon * (n : ℝ) ^ 2⌋₊ key.profile := by
  obtain ⟨H, hH⟩ := mem_supercriticalMediumRefinementKeyFinset.mp hkey
  have hdefect := (mem_supercriticalMediumDegreeGraphFinset.mp H.2).1
  have hdivision :=
    (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).2.1
  have hclose :=
    (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).1
  have hedges : (finiteGraphEdges H.1).card = m := by
    simpa [finiteGraphEdges] using
      (mem_supercriticalCloseGraphFinset.mp hclose).2.1
  obtain ⟨R⟩ := hresult H.1 H.2
  have hwindow :=
    canonicalCrossEdgeProfile_mem_window_of_closeStructureResult
      hk hgamma H.1 hn R m hedges
  rw [← hH]
  let G : SimpleGraph (Fin n) := H.1
  have hdivision' :
      canonicalSupercriticalDivision G (by simpa using hn) = D := by
    simpa [G] using hdivision
  have hwindow' :
      SupercriticalProfileWindow
        (canonicalSupercriticalDivision G (by simpa using hn)) m
        (supercriticalOffDiagonal k gamma) delta
        ⌊epsilon * (n : ℝ) ^ 2⌋₊
        (crossEdgeProfile G
          (canonicalSupercriticalDivision G (by simpa using hn))) := by
    simpa [G] using hwindow
  change SupercriticalProfileWindow D m
    (supercriticalOffDiagonal k gamma) delta
    ⌊epsilon * (n : ℝ) ^ 2⌋₊ (crossEdgeProfile G D)
  rw [← hdivision']
  simpa using hwindow'

/-- Once every occurring profile lies in one common window, the number of
refinement keys is bounded by the exact defect/vertex/part/incident/window
product. -/
theorem card_supercriticalMediumRefinementKeyFinset_le_profileWindow
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n))
    (profileCenter : ℕ) (rho delta : ℝ) (budget : ℕ)
    (hprofile : ∀ key ∈ supercriticalMediumRefinementKeyFinset
      k hk gamma hgamma alpha halpha m n tau hn D,
      SupercriticalProfileWindow
        D profileCenter rho delta budget key.profile) :
    (supercriticalMediumRefinementKeyFinset
      k hk gamma hgamma alpha halpha m n tau hn D).card ≤
      (supercriticalCombinedDefectPatternFinset
          k hk gamma hgamma m n tau hn D).card *
        n * (k - 1) * 2 ^ n *
          (supercriticalProfileWindowFinset
            D profileCenter rho delta budget).card := by
  classical
  let keys := supercriticalMediumRefinementKeyFinset
    k hk gamma hgamma alpha halpha m n tau hn D
  let tupleImage := keys.image
    (supercriticalMediumRefinementTuple (D := D))
  have hcardImage : tupleImage.card = keys.card := by
    apply Finset.card_image_iff.mpr
    intro a _ha b _hb hab
    exact supercriticalMediumRefinementTuple_injective hab
  have hsubset : tupleImage ⊆
      supercriticalMediumProfileWindowTupleFinset
        k hk gamma hgamma m n tau hn D profileCenter rho delta budget := by
    intro x hx
    obtain ⟨key, hkey, rfl⟩ := Finset.mem_image.mp hx
    exact supercriticalMediumRefinementTuple_mem_profileWindowAuxiliary
      hkey (hprofile key hkey)
  rw [← hcardImage]
  calc
    tupleImage.card ≤
        (supercriticalMediumProfileWindowTupleFinset
          k hk gamma hgamma m n tau hn D
            profileCenter rho delta budget).card :=
      Finset.card_le_card hsubset
    _ = (supercriticalCombinedDefectPatternFinset
          k hk gamma hgamma m n tau hn D).card *
        n * (k - 1) * 2 ^ n *
          (supercriticalProfileWindowFinset
            D profileCenter rho delta budget).card := by
      simp [supercriticalMediumProfileWindowTupleFinset, Nat.mul_assoc]

/-! ## Exact aggregation of refinement fibers -/

/-- A uniform real-valued bound on every occurring refinement fiber sums to
the key-cardinality multiple of that bound. -/
theorem card_supercriticalMediumDegreeGraphFinset_le_keyCard_mul_of_fiber_bound
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) (B : ℝ)
    (hfiber : ∀ key ∈ supercriticalMediumRefinementKeyFinset
      k hk gamma hgamma alpha halpha m n tau hn D,
      ((supercriticalMediumRefinedGraphFinset
        k hk gamma hgamma alpha halpha m n tau hn key).card : ℝ) ≤ B) :
    ((supercriticalMediumDegreeGraphFinset
      k hk gamma hgamma alpha m n tau hn D).card : ℝ) ≤
      ((supercriticalMediumRefinementKeyFinset
        k hk gamma hgamma alpha halpha m n tau hn D).card : ℝ) * B := by
  classical
  let keys := supercriticalMediumRefinementKeyFinset
    k hk gamma hgamma alpha halpha m n tau hn D
  have hcover := card_supercriticalMediumDegreeGraphFinset_le_sum_refined
    (k := k) (hk := hk) (gamma := gamma) (hgamma := hgamma)
    (alpha := alpha) (m := m) (n := n) (tau := tau) (hn := hn)
    halpha D
  have hcoverReal :
      ((supercriticalMediumDegreeGraphFinset
        k hk gamma hgamma alpha m n tau hn D).card : ℝ) ≤
        ∑ key ∈ keys,
          ((supercriticalMediumRefinedGraphFinset
            k hk gamma hgamma alpha halpha m n tau hn key).card : ℝ) := by
    exact_mod_cast hcover
  calc
    ((supercriticalMediumDegreeGraphFinset
      k hk gamma hgamma alpha m n tau hn D).card : ℝ) ≤
        ∑ key ∈ keys,
          ((supercriticalMediumRefinedGraphFinset
            k hk gamma hgamma alpha halpha m n tau hn key).card : ℝ) :=
      hcoverReal
    _ ≤ ∑ _key ∈ keys, B := by
      exact Finset.sum_le_sum fun key hkey ↦ hfiber key hkey
    _ = (keys.card : ℝ) * B := by simp

/-- The explicit coefficient paid when two window profiles are compared. -/
def supercriticalMediumProfileComparisonRate
    (k : ℕ) (rho delta : ℝ) : ℝ :=
  (DenseGraph.binomialDensityBandConstant rho *
    Fintype.card (SupercriticalPartPair k)) * delta

/-- A per-fiber penalty relative to the fiber's own cross-profile can be
uniformized relative to any fixed base profile in the same window. -/
theorem card_supercriticalMediumDegreeGraphFinset_le_keyCard_mul_profileMultiplicity_mul_exp
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n))
    (profileCenter budget : ℕ) (rho delta penalty : ℝ)
    (base : SupercriticalEdgeProfile D)
    (hdelta : 0 ≤ delta) (hlower : 0 < rho - 2 * delta)
    (hupper : rho + 2 * delta < 1)
    (hbase : SupercriticalProfileWindow
      D profileCenter rho delta budget base)
    (hprofile : ∀ key ∈ supercriticalMediumRefinementKeyFinset
      k hk gamma hgamma alpha halpha m n tau hn D,
      SupercriticalProfileWindow
        D profileCenter rho delta budget key.profile)
    (hfiber : ∀ key ∈ supercriticalMediumRefinementKeyFinset
      k hk gamma hgamma alpha halpha m n tau hn D,
      ((supercriticalMediumRefinedGraphFinset
        k hk gamma hgamma alpha halpha m n tau hn key).card : ℝ) ≤
        (supercriticalProfileMultiplicity key.profile : ℝ) *
          Real.exp (-penalty * (n : ℝ) ^ 2)) :
    ((supercriticalMediumDegreeGraphFinset
      k hk gamma hgamma alpha m n tau hn D).card : ℝ) ≤
      ((supercriticalMediumRefinementKeyFinset
        k hk gamma hgamma alpha halpha m n tau hn D).card : ℝ) *
        (supercriticalProfileMultiplicity base : ℝ) *
          Real.exp ((supercriticalMediumProfileComparisonRate
            k rho delta - penalty) * (n : ℝ) ^ 2) := by
  have huniform : ∀ key ∈ supercriticalMediumRefinementKeyFinset
      k hk gamma hgamma alpha halpha m n tau hn D,
      ((supercriticalMediumRefinedGraphFinset
        k hk gamma hgamma alpha halpha m n tau hn key).card : ℝ) ≤
        (supercriticalProfileMultiplicity base : ℝ) *
          Real.exp ((supercriticalMediumProfileComparisonRate
            k rho delta - penalty) * (n : ℝ) ^ 2) := by
    intro key hkey
    have hcompare :=
      supercriticalProfileMultiplicity_le_mul_exp_card_sq_of_mem_window
        key.profile base hdelta hlower hupper (hprofile key hkey) hbase
    have hcompare' :
        (supercriticalProfileMultiplicity key.profile : ℝ) ≤
          (supercriticalProfileMultiplicity base : ℝ) *
            Real.exp (supercriticalMediumProfileComparisonRate k rho delta *
              (n : ℝ) ^ 2) := by
      simpa [supercriticalMediumProfileComparisonRate] using hcompare
    calc
      ((supercriticalMediumRefinedGraphFinset
        k hk gamma hgamma alpha halpha m n tau hn key).card : ℝ) ≤
          (supercriticalProfileMultiplicity key.profile : ℝ) *
            Real.exp (-penalty * (n : ℝ) ^ 2) := hfiber key hkey
      _ ≤ ((supercriticalProfileMultiplicity base : ℝ) *
          Real.exp (supercriticalMediumProfileComparisonRate k rho delta *
            (n : ℝ) ^ 2)) *
          Real.exp (-penalty * (n : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_right hcompare' (Real.exp_nonneg _)
      _ = (supercriticalProfileMultiplicity base : ℝ) *
          Real.exp ((supercriticalMediumProfileComparisonRate
            k rho delta - penalty) * (n : ℝ) ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  simpa [mul_assoc] using
    card_supercriticalMediumDegreeGraphFinset_le_keyCard_mul_of_fiber_bound
      halpha D
        ((supercriticalProfileMultiplicity base : ℝ) *
          Real.exp ((supercriticalMediumProfileComparisonRate
            k rho delta - penalty) * (n : ℝ) ^ 2)) huniform

/-- Fully explicit finite aggregation: replace the number of occurring keys
by the defect-pattern and windowed auxiliary-data product. -/
theorem card_supercriticalMediumDegreeGraphFinset_le_windowedAuxiliary_mul_profileMultiplicity_mul_exp
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n))
    (profileCenter budget : ℕ) (rho delta penalty : ℝ)
    (base : SupercriticalEdgeProfile D)
    (hdelta : 0 ≤ delta) (hlower : 0 < rho - 2 * delta)
    (hupper : rho + 2 * delta < 1)
    (hbase : SupercriticalProfileWindow
      D profileCenter rho delta budget base)
    (hprofile : ∀ key ∈ supercriticalMediumRefinementKeyFinset
      k hk gamma hgamma alpha halpha m n tau hn D,
      SupercriticalProfileWindow
        D profileCenter rho delta budget key.profile)
    (hfiber : ∀ key ∈ supercriticalMediumRefinementKeyFinset
      k hk gamma hgamma alpha halpha m n tau hn D,
      ((supercriticalMediumRefinedGraphFinset
        k hk gamma hgamma alpha halpha m n tau hn key).card : ℝ) ≤
        (supercriticalProfileMultiplicity key.profile : ℝ) *
          Real.exp (-penalty * (n : ℝ) ^ 2)) :
    ((supercriticalMediumDegreeGraphFinset
      k hk gamma hgamma alpha m n tau hn D).card : ℝ) ≤
      (((supercriticalCombinedDefectPatternFinset
          k hk gamma hgamma m n tau hn D).card *
        (n * (k - 1) * 2 ^ n *
          (supercriticalProfileWindowFinset
            D profileCenter rho delta budget).card) : ℕ) : ℝ) *
        (supercriticalProfileMultiplicity base : ℝ) *
          Real.exp ((supercriticalMediumProfileComparisonRate
            k rho delta - penalty) * (n : ℝ) ^ 2) := by
  have haggregate :=
    card_supercriticalMediumDegreeGraphFinset_le_keyCard_mul_profileMultiplicity_mul_exp
      halpha D profileCenter budget rho delta penalty base
        hdelta hlower hupper hbase hprofile hfiber
  have hkeysNat := card_supercriticalMediumRefinementKeyFinset_le_profileWindow
    halpha D profileCenter rho delta budget hprofile
  have hkeys :
      ((supercriticalMediumRefinementKeyFinset
        k hk gamma hgamma alpha halpha m n tau hn D).card : ℝ) ≤
      (((supercriticalCombinedDefectPatternFinset
          k hk gamma hgamma m n tau hn D).card *
        (n * (k - 1) * 2 ^ n *
          (supercriticalProfileWindowFinset
            D profileCenter rho delta budget).card) : ℕ) : ℝ) := by
    exact_mod_cast (by simpa [Nat.mul_assoc] using hkeysNat)
  exact haggregate.trans <| by
    gcongr

/-! ## Eventual absorption of all deterministic overhead -/

/-- The residual quadratic penalty after paying for defect patterns,
auxiliary refinement data, and profile comparison. -/
def supercriticalMediumAggregatedPenalty
    (k : ℕ) (epsilon auxiliaryRate rho delta penalty : ℝ) : ℝ :=
  penalty - (supercriticalDefectPatternRate epsilon + auxiliaryRate +
    supercriticalMediumProfileComparisonRate k rho delta)

/-- If every refinement fiber has quadratic penalty `penalty`, then the full
medium family has the residual penalty obtained by subtracting the explicit
defect, auxiliary-data and profile-comparison rates.  The conclusion is
uniform in all finite parameters shown after `n`; the only asymptotic choice
is the positive auxiliary slack `auxiliaryRate`.

This theorem is deliberately independent of Janson: a later module supplies
`hfiber` from its probabilistic estimate. -/
theorem eventually_card_supercriticalMediumDegreeGraphFinset_le_profileMultiplicity_mul_exp_neg_aggregatedPenalty
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    {epsilon auxiliaryRate rho delta penalty : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : 3 * epsilon < 1 / 2)
    (hauxiliary : 0 < auxiliaryRate) (_hpenalty : 0 < penalty)
    (hdelta : 0 ≤ delta) (hlower : 0 < rho - 2 * delta)
    (hupper : rho + 2 * delta < 1)
    (_hnet : 0 < supercriticalMediumAggregatedPenalty
      k epsilon auxiliaryRate rho delta penalty) :
    ∀ᶠ n : ℕ in atTop, ∀ (alpha : ℝ) (halpha : 0 < alpha)
      (m : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
      (D : SupercriticalDivision k (Fin n))
      (profileCenter budget : ℕ) (base : SupercriticalEdgeProfile D),
      SupercriticalProfileWindow D profileCenter rho delta budget base →
      (∀ key ∈ supercriticalMediumRefinementKeyFinset
        k hk gamma hgamma alpha halpha m n tau hn D,
        SupercriticalProfileWindow
          D profileCenter rho delta budget key.profile) →
      (∀ G ∈ supercriticalDivisionDefectGraphFinset
          k hk gamma hgamma m n tau hn D,
        supercriticalDefectCost G D ≤
          ⌊epsilon * (n : ℝ) ^ 2⌋₊) →
      (∀ key ∈ supercriticalMediumRefinementKeyFinset
        k hk gamma hgamma alpha halpha m n tau hn D,
        ((supercriticalMediumRefinedGraphFinset
          k hk gamma hgamma alpha halpha m n tau hn key).card : ℝ) ≤
          (supercriticalProfileMultiplicity key.profile : ℝ) *
            Real.exp (-penalty * (n : ℝ) ^ 2)) →
      ((supercriticalMediumDegreeGraphFinset
        k hk gamma hgamma alpha m n tau hn D).card : ℝ) ≤
        (supercriticalProfileMultiplicity base : ℝ) *
          Real.exp (-supercriticalMediumAggregatedPenalty
            k epsilon auxiliaryRate rho delta penalty * (n : ℝ) ^ 2) := by
  filter_upwards
      [eventually_card_supercriticalCombinedDefectPatternFinset_le_exp
        hk hgamma hepsilon hsmall,
       eventually_supercriticalMediumProfileWindowOverhead_le_exp
        k hauxiliary]
      with n hdefect haux alpha halpha m tau hn D
        profileCenter budget base hbase hprofile hcost hfiber
  have hfinite :=
    card_supercriticalMediumDegreeGraphFinset_le_windowedAuxiliary_mul_profileMultiplicity_mul_exp
      halpha D profileCenter budget rho delta penalty base
        hdelta hlower hupper hbase hprofile hfiber
  have hdefect' := hdefect m tau hn D hcost
  have haux' := haux D profileCenter budget rho delta
  let patternCount :=
    (supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D).card
  let auxiliaryCount := n * (k - 1) * 2 ^ n *
    (supercriticalProfileWindowFinset
      D profileCenter rho delta budget).card
  have hoverhead :
      ((patternCount * auxiliaryCount : ℕ) : ℝ) ≤
        Real.exp ((supercriticalDefectPatternRate epsilon + auxiliaryRate) *
          (n : ℝ) ^ 2) := by
    rw [Nat.cast_mul]
    calc
      (patternCount : ℝ) * (auxiliaryCount : ℝ) ≤
          Real.exp (supercriticalDefectPatternRate epsilon * (n : ℝ) ^ 2) *
            Real.exp (auxiliaryRate * (n : ℝ) ^ 2) := by
        exact mul_le_mul hdefect' haux' (by positivity) (Real.exp_nonneg _)
      _ = Real.exp ((supercriticalDefectPatternRate epsilon + auxiliaryRate) *
          (n : ℝ) ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    ((supercriticalMediumDegreeGraphFinset
      k hk gamma hgamma alpha m n tau hn D).card : ℝ) ≤
        ((patternCount * auxiliaryCount : ℕ) : ℝ) *
          (supercriticalProfileMultiplicity base : ℝ) *
            Real.exp ((supercriticalMediumProfileComparisonRate
              k rho delta - penalty) * (n : ℝ) ^ 2) := by
      simpa [patternCount, auxiliaryCount] using hfinite
    _ ≤ Real.exp ((supercriticalDefectPatternRate epsilon + auxiliaryRate) *
          (n : ℝ) ^ 2) *
        (supercriticalProfileMultiplicity base : ℝ) *
          Real.exp ((supercriticalMediumProfileComparisonRate
            k rho delta - penalty) * (n : ℝ) ^ 2) := by
      gcongr
    _ = (supercriticalProfileMultiplicity base : ℝ) *
        (Real.exp ((supercriticalDefectPatternRate epsilon + auxiliaryRate) *
          (n : ℝ) ^ 2) *
        Real.exp ((supercriticalMediumProfileComparisonRate
          k rho delta - penalty) * (n : ℝ) ^ 2)) := by ring
    _ = (supercriticalProfileMultiplicity base : ℝ) *
        Real.exp (((supercriticalDefectPatternRate epsilon + auxiliaryRate) *
          (n : ℝ) ^ 2) +
          ((supercriticalMediumProfileComparisonRate
            k rho delta - penalty) * (n : ℝ) ^ 2)) := by
      rw [Real.exp_add]
    _ = (supercriticalProfileMultiplicity base : ℝ) *
        Real.exp (-supercriticalMediumAggregatedPenalty
          k epsilon auxiliaryRate rho delta penalty * (n : ℝ) ^ 2) := by
      congr 2
      simp only [supercriticalMediumAggregatedPenalty]
      ring

end InducedStars
