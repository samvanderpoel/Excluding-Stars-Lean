import InducedStars.Structure.Critical.WindowAlmostAll

/-!
# The paper's base-two critical window

The natural-log theorem is applied at parameter `a / Real.log 2`.
Exact edge counts and joint witness events are identified before passing to
probabilities, so the conversion includes the transition and every signed
window parameter without changing the finite sample space or witness.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The paper's transition parameter, with the base-two normalization. -/
def criticalWindowBase2Threshold (k : ℕ) : ℝ :=
  ((k - 2 : ℕ) : ℝ) * pK k * (1 - pK k) * Real.log 2 /
    (((k - 1 : ℕ) : ℝ) * gammaK k)

/-- The density uses the paper's base-two logarithm. -/
def criticalWindowBase2Density (k : ℕ) (a : ℝ) (n : ℕ) : ℝ :=
  gammaK k + a * log2 (n : ℝ) / n

/-- The exact floor edge count in the paper's critical window. -/
def criticalWindowBase2EdgeCount (k : ℕ) (a : ℝ) (n : ℕ) : ℕ :=
  floorEdgeCountSequence (criticalWindowBase2Density k a n) n

/-- The coefficient of `log2 n` in the exceptional-set size. -/
def criticalWindowBase2RemainderCoefficient (k : ℕ) (a : ℝ) : ℝ :=
  (criticalWindowBase2Threshold k - a) / (2 * gammaK k)

/-- One literal disjoint-union witness carries the base-two size estimate. -/
def HasCriticalWindowBase2Structure (k : ℕ) (a epsilon : ℝ)
    {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ W : CriticalStructureWitness k n G,
    |(W.exceptionalVertices.card : ℝ) / log2 (n : ℝ) -
      criticalWindowBase2RemainderCoefficient k a| ≤ epsilon

/-- The induced-star-free sample space at the exact base-two window edge count. -/
def criticalWindowBase2InducedStarFreeGraphFinset (k n : ℕ) (a : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  inducedStarFreeGraphFinsetWithEdges k n (criticalWindowBase2EdgeCount k a n)

/-- Uniform probability of the joint decomposition and base-two size event. -/
def criticalWindowBase2StructuredProbability (k : ℕ) (a epsilon : ℝ) (n : ℕ) : ℝ := by
  classical
  exact uniformSubfamilyProbability (criticalWindowBase2InducedStarFreeGraphFinset k n a)
    ((criticalWindowBase2InducedStarFreeGraphFinset k n a).filter
      (HasCriticalWindowBase2Structure k a epsilon))

theorem criticalWindowBase2Threshold_eq (k : ℕ) :
    criticalWindowBase2Threshold k = criticalWindowThreshold k * Real.log 2 := by
  unfold criticalWindowBase2Threshold criticalWindowThreshold
  ring

theorem criticalWindowBase2Threshold_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalWindowBase2Threshold k := by
  rw [criticalWindowBase2Threshold_eq]
  exact mul_pos (criticalWindowThreshold_pos hk) realLogTwo_pos

/-- The densities agree exactly after rescaling the parameter. -/
theorem criticalWindowBase2Density_eq (k : ℕ) (a : ℝ) (n : ℕ) :
    criticalWindowBase2Density k a n = criticalWindowDensity k (a / Real.log 2) n := by
  unfold criticalWindowBase2Density criticalWindowDensity log2
  ring

/-- In particular the natural floors agree at every order. -/
theorem criticalWindowBase2EdgeCount_eq (k : ℕ) (a : ℝ) (n : ℕ) :
    criticalWindowBase2EdgeCount k a n = criticalWindowEdgeCount k (a / Real.log 2) n := by
  simp only [criticalWindowBase2EdgeCount, criticalWindowEdgeCount, criticalWindowBase2Density_eq]

@[simp] theorem criticalWindowBase2EdgeCount_zero (k n : ℕ) :
    criticalWindowBase2EdgeCount k 0 n = criticalEdgeCount k n := by
  simp [criticalWindowBase2EdgeCount_eq]

theorem criticalWindowBase2EdgeCount_hasAsymptoticEdgeDensity
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    HasAsymptoticEdgeDensity (criticalWindowBase2EdgeCount k a) (gammaK k) := by
  have h : criticalWindowBase2EdgeCount k a = criticalWindowEdgeCount k (a / Real.log 2) :=
    funext (criticalWindowBase2EdgeCount_eq k a)
  rw [h]
  exact criticalWindowEdgeCount_hasAsymptoticEdgeDensity hk (a / Real.log 2)

theorem criticalWindowBase2RemainderCoefficient_eq (k : ℕ) (a : ℝ) :
    criticalWindowBase2RemainderCoefficient k a =
      Real.log 2 * criticalWindowRemainderCoefficient k (a / Real.log 2) := by
  unfold criticalWindowBase2RemainderCoefficient criticalWindowRemainderCoefficient
  rw [criticalWindowBase2Threshold_eq, ← mul_div_assoc]
  congr 1
  field_simp

/-- The error scales for each individual witness, including small orders. -/
theorem criticalWindowBase2_normalized_error (k : ℕ) (a : ℝ) (n s : ℕ) :
    |(s : ℝ) / log2 (n : ℝ) - criticalWindowBase2RemainderCoefficient k a| =
      Real.log 2 * |(s : ℝ) / Real.log (n : ℝ) -
        criticalWindowRemainderCoefficient k (a / Real.log 2)| := by
  rw [criticalWindowBase2RemainderCoefficient_eq]
  have h : (s : ℝ) / log2 (n : ℝ) = Real.log 2 * ((s : ℝ) / Real.log (n : ℝ)) := by
    rw [log2, div_div_eq_mul_div]
    ring
  rw [h, ← mul_sub, abs_mul, abs_of_pos realLogTwo_pos]

/-- Exact equality of the joint events, with the same structure witness. -/
theorem hasCriticalWindowBase2Structure_iff (k : ℕ) (a epsilon : ℝ)
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    HasCriticalWindowBase2Structure k a epsilon G ↔
      HasCriticalWindowStructure k (a / Real.log 2) (epsilon / Real.log 2) G := by
  unfold HasCriticalWindowBase2Structure HasCriticalWindowStructure
  apply exists_congr
  intro W
  rw [criticalWindowBase2_normalized_error]
  rw [le_div_iff₀ realLogTwo_pos, mul_comm]

/-- The base-two probability is exactly the already-proved natural-log probability. -/
theorem criticalWindowBase2StructuredProbability_eq (k : ℕ) (a epsilon : ℝ) :
    criticalWindowBase2StructuredProbability k a epsilon =
      criticalWindowStructuredProbability k (a / Real.log 2) (epsilon / Real.log 2) := by
  classical
  funext n
  simp only [criticalWindowBase2StructuredProbability, criticalWindowStructuredProbability,
    criticalWindowBase2InducedStarFreeGraphFinset, criticalWindowInducedStarFreeGraphFinset,
    criticalWindowBase2EdgeCount_eq]
  congr 1
  apply Finset.filter_congr
  intro G _
  exact hasCriticalWindowBase2Structure_iff k a epsilon G

/-- Sharp exceptional-set concentration in the paper's base-two convention. -/
theorem inducedStarCriticalWindowBase2AlmostAll_structured
    (k : ℕ) (hk : 3 ≤ k) (a : ℝ) (ha : a ≤ criticalWindowBase2Threshold k)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Tendsto (criticalWindowBase2StructuredProbability k a epsilon) atTop (𝓝 1) := by
  rw [criticalWindowBase2StructuredProbability_eq]
  apply inducedStarCriticalWindowAlmostAll_structured k hk (a / Real.log 2)
  · apply (div_le_iff₀ realLogTwo_pos).2
    simpa only [criticalWindowBase2Threshold_eq] using ha
  · exact div_pos hepsilon realLogTwo_pos

/-- Co-partite concentration above the paper's base-two transition. -/
theorem inducedStarCriticalWindowBase2AlmostAll_coMultipartite
    (k : ℕ) (hk : 3 ≤ k) (a : ℝ) (ha : criticalWindowBase2Threshold k < a) :
    Tendsto (fun n ↦ supercriticalCoMultipartiteProbability k n (criticalWindowBase2EdgeCount k a n))
      atTop (𝓝 1) := by
  have ha' : criticalWindowThreshold k < a / Real.log 2 := by
    apply (lt_div_iff₀ realLogTwo_pos).2
    simpa only [criticalWindowBase2Threshold_eq] using ha
  simpa only [criticalWindowBase2EdgeCount_eq] using
    inducedStarCriticalWindowAlmostAll_coMultipartite k hk (a / Real.log 2) ha'

/-- Paper: the full critical clause of `thm:main-almostall`, with base-two
logarithms, every fixed signed parameter, and the exact floor edge count. -/
theorem inducedStarCriticalWindowBase2AlmostAll (k : ℕ) (hk : 3 ≤ k) :
    ∀ a : ℝ,
      (a ≤ criticalWindowBase2Threshold k → ∀ epsilon : ℝ, 0 < epsilon →
        Tendsto (criticalWindowBase2StructuredProbability k a epsilon) atTop (𝓝 1)) ∧
      (criticalWindowBase2Threshold k < a →
        Tendsto (fun n ↦ supercriticalCoMultipartiteProbability k n (criticalWindowBase2EdgeCount k a n))
          atTop (𝓝 1)) := by
  intro a
  exact ⟨fun ha epsilon hepsilon ↦ inducedStarCriticalWindowBase2AlmostAll_structured k hk a ha epsilon hepsilon,
    fun ha ↦ inducedStarCriticalWindowBase2AlmostAll_coMultipartite k hk a ha⟩

end InducedStars
