import InducedStars.Structure.Critical.Basic
import InducedStars.Structure.Critical.Scalars

/-!
# The natural-log critical-window infrastructure

These auxiliary definitions use `Real.log`, the natural logarithm, at density
`gammaK k + a * Real.log n / n`.  The paper-facing base-two interface is
provided by `WindowBase2`.  The finite event below records the size of the
same exceptional set that witnesses the literal disjoint union.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The transition parameter for the natural-log window parameterization. -/
def criticalWindowThreshold (k : ℕ) : ℝ :=
  ((k - 2 : ℕ) : ℝ) * pK k * (1 - pK k) /
    (((k - 1 : ℕ) : ℝ) * gammaK k)

theorem criticalWindowThreshold_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalWindowThreshold k := by
  unfold criticalWindowThreshold
  exact div_pos
    (mul_pos (mul_pos (by exact_mod_cast (show 0 < k - 2 by omega))
      (pK_pos (by omega))) (sub_pos.mpr (pK_lt_one (by omega))))
    (mul_pos (by exact_mod_cast (show 0 < k - 1 by omega)) (gammaK_pos hk))

/-- The quadratic coefficient retained from the earlier critical upper
bound is exactly `gamma_k / a_*` in the natural-log parameterization. -/
theorem criticalQuadraticCoefficient_eq_gamma_div_threshold
    {k : ℕ} (hk : 3 ≤ k) :
    criticalQuadraticCoefficient k = gammaK k / criticalWindowThreshold k := by
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hd : (0 : ℝ) < (k - 2 : ℕ) := by exact_mod_cast (show 0 < k - 2 by omega)
  have hp := pK_pos (show 2 ≤ k by omega)
  have hq : 0 < 1 - pK k := sub_pos.mpr (pK_lt_one (show 2 ≤ k by omega))
  have hrel : ((k - 1 : ℕ) : ℝ) = ((k - 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show k - 1 = (k - 2) + 1 by omega)
  unfold criticalQuadraticCoefficient criticalWindowThreshold gammaK
  rw [hrel]
  field_simp
  ring

/-- The exact, order-dependent density in the natural-log parameterization. -/
def criticalWindowDensity (k : ℕ) (a : ℝ) (n : ℕ) : ℝ :=
  gammaK k + a * Real.log (n : ℝ) / n

/-- The exact floor edge count, including every fixed signed value of `a`.
Small orders at which the density is negative are totalized by `Nat.floor`;
the density is eventually strictly between zero and one. -/
def criticalWindowEdgeCount (k : ℕ) (a : ℝ) (n : ℕ) : ℕ :=
  floorEdgeCountSequence (criticalWindowDensity k a n) n

@[simp] theorem criticalWindowDensity_zero (k n : ℕ) :
    criticalWindowDensity k 0 n = gammaK k := by
  simp [criticalWindowDensity]

@[simp] theorem criticalWindowEdgeCount_zero (k n : ℕ) :
    criticalWindowEdgeCount k 0 n = criticalEdgeCount k n := by
  simp [criticalWindowEdgeCount, criticalEdgeCount]

theorem criticalWindowDensity_tendsto (k : ℕ) (a : ℝ) :
    Tendsto (criticalWindowDensity k a) atTop (𝓝 (gammaK k)) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  change Tendsto (fun n : ℕ ↦ gammaK k + a * Real.log (n : ℝ) / n) atTop (𝓝 (gammaK k))
  simpa only [mul_div_assoc, mul_zero, add_zero] using
    ((tendsto_const_nhds (x := gammaK k)).add ((tendsto_const_nhds (x := a)).mul hlog))

theorem eventually_criticalWindowDensity_mem_Ioo
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, criticalWindowDensity k a n ∈ Ioo (0 : ℝ) 1 :=
  (criticalWindowDensity_tendsto k a).eventually
    (Ioo_mem_nhds (gammaK_pos hk) (gammaK_lt_one hk))

theorem eventually_criticalWindowEdgeCount_le_completeEdgeCount
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, criticalWindowEdgeCount k a n ≤ completeEdgeCount n := by
  filter_upwards [eventually_criticalWindowDensity_mem_Ioo hk a] with n hn
  exact floorEdgeCountSequence_le_completeEdgeCount ⟨hn.1.le, hn.2.le⟩ n

/-- Flooring a varying eventually nonnegative density preserves its limit. -/
theorem varyingFloorEdgeCount_hasAsymptoticEdgeDensity
    {g : ℕ → ℝ} {gamma : ℝ} (hgamma : 0 < gamma)
    (hg : Tendsto g atTop (𝓝 gamma)) :
    HasAsymptoticEdgeDensity (fun n ↦ floorEdgeCountSequence (g n) n) gamma := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < g n :=
    hg.eventually (Ioi_mem_nhds hgamma)
  have hcap : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < completeEdgeCount n :=
    tendsto_completeEdgeCount_cast_atTop.eventually (eventually_gt_atTop 0)
  have herror : Tendsto (fun n ↦ g n -
      (floorEdgeCountSequence (g n) n : ℝ) / completeEdgeCount n) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_completeEdgeCount_cast_atTop)
    · filter_upwards [hpos, hcap] with n hn hc
      have hf := Nat.floor_le (mul_nonneg hn.le (Nat.cast_nonneg (completeEdgeCount n)))
      change 0 ≤ g n - (⌊g n * (completeEdgeCount n : ℝ)⌋₊ : ℝ) / completeEdgeCount n
      apply sub_nonneg.mpr
      exact (div_le_iff₀ hc).2 hf
    · filter_upwards [hpos, hcap] with n hn hc
      have hf := Nat.lt_floor_add_one (g n * (completeEdgeCount n : ℝ))
      change g n - (⌊g n * (completeEdgeCount n : ℝ)⌋₊ : ℝ) / completeEdgeCount n ≤
        1 / completeEdgeCount n
      apply (le_div_iff₀ hc).2
      have hcancel :
          (g n - (⌊g n * (completeEdgeCount n : ℝ)⌋₊ : ℝ) / completeEdgeCount n) *
            completeEdgeCount n =
          g n * completeEdgeCount n - (⌊g n * (completeEdgeCount n : ℝ)⌋₊ : ℝ) := by
        field_simp
      rw [hcancel]
      linarith
  have h := hg.sub herror
  simpa only [HasAsymptoticEdgeDensity, sub_zero, sub_sub_cancel] using h

/-- Every fixed critical-window parameter has limiting density `gammaK k`,
while retaining its exact floor sequence. -/
theorem criticalWindowEdgeCount_hasAsymptoticEdgeDensity
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    HasAsymptoticEdgeDensity (criticalWindowEdgeCount k a) (gammaK k) :=
  varyingFloorEdgeCount_hasAsymptoticEdgeDensity (gammaK_pos hk)
    (criticalWindowDensity_tendsto k a)

/-- The predicted remainder coefficient, used when `a ≤ criticalWindowThreshold k`. -/
def criticalWindowRemainderCoefficient (k : ℕ) (a : ℝ) : ℝ :=
  (criticalWindowThreshold k - a) / (2 * gammaK k)

/-- An exact disjoint-union witness whose exceptional set has the asserted
logarithmic order to tolerance `epsilon`. -/
def HasCriticalWindowStructure (k : ℕ) (a epsilon : ℝ)
    {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ W : CriticalStructureWitness k n G,
    |(W.exceptionalVertices.card : ℝ) / Real.log (n : ℝ) -
      criticalWindowRemainderCoefficient k a| ≤ epsilon

/-- Labeled induced-star-free sample space at the exact critical-window edge count. -/
def criticalWindowInducedStarFreeGraphFinset (k n : ℕ) (a : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  inducedStarFreeGraphFinsetWithEdges k n (criticalWindowEdgeCount k a n)

/-- Uniform probability of the joint decomposition and remainder-size event. -/
def criticalWindowStructuredProbability (k : ℕ) (a epsilon : ℝ) (n : ℕ) : ℝ := by
  classical
  exact uniformSubfamilyProbability (criticalWindowInducedStarFreeGraphFinset k n a)
    ((criticalWindowInducedStarFreeGraphFinset k n a).filter
      (HasCriticalWindowStructure k a epsilon))

end InducedStars
