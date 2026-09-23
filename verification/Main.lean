import DenseGraph
import InducedStars

/-!
Main declarations advertised in docs/RESULTS.md. Run from the repository root:

    lake env lean verification/Main.lean

Each #check displays the actual statement; each #print axioms displays its
transitive assumption boundary. The examples check the complete typical-structure
statement and the critical window definitions and joint event explicitly.
The exhaustive allowlist check is Audit.lean.
-/

-- Colored extremal and stability results
#check InducedStars.ColoredGraph.kthOrderMantel
#print axioms InducedStars.ColoredGraph.kthOrderMantel
#check InducedStars.ColoredGraph.kthOrderStability
#print axioms InducedStars.ColoredGraph.kthOrderStability

-- Graphon optimization and classification
#check InducedStars.graphonCharacterizationFixedDensity
#print axioms InducedStars.graphonCharacterizationFixedDensity
#check InducedStars.graphonCharacterizationFixedDensity_upToEquivalence
#print axioms InducedStars.graphonCharacterizationFixedDensity_upToEquivalence
#check InducedStars.fixedDensityEntropyValue_eq
#print axioms InducedStars.fixedDensityEntropyValue_eq
#check InducedStars.gnpGraphonVariationalValue_eq_rateFunction
#print axioms InducedStars.gnpGraphonVariationalValue_eq_rateFunction
#check InducedStars.gnpGraphonOptimizerSet_eq
#print axioms InducedStars.gnpGraphonOptimizerSet_eq
#check InducedStars.fixedDensityOptimizerMultiplicity
#print axioms InducedStars.fixedDensityOptimizerMultiplicity
#check InducedStars.gnpGraphonOptimizerMultiplicity
#print axioms InducedStars.gnpGraphonOptimizerMultiplicity

-- Entropy, rates, and typical structure
#check InducedStars.inducedStarFixedDensityEntropyAsymptotic
#print axioms InducedStars.inducedStarFixedDensityEntropyAsymptotic
#check InducedStars.inducedStarGnpLargeDeviationRate
#print axioms InducedStars.inducedStarGnpLargeDeviationRate
#check InducedStars.inducedStarAlmostAll
#print axioms InducedStars.inducedStarAlmostAll
#check InducedStars.inducedStarCriticalWindowBase2AlmostAll
#print axioms InducedStars.inducedStarCriticalWindowBase2AlmostAll
#check InducedStars.inducedStarGnpTypicalStructure
#print axioms InducedStars.inducedStarGnpTypicalStructure

-- Induced C4 results
#check InducedStars.inducedC4AlmostAllSplit
#print axioms InducedStars.inducedC4AlmostAllSplit
#check InducedStars.inducedC4Entropy_eq_scalarMax
#print axioms InducedStars.inducedC4Entropy_eq_scalarMax
#check InducedStars.inducedC4CountComparison
#print axioms InducedStars.inducedC4CountComparison

noncomputable section
open Filter Set Topology InducedStars
open scoped Classical

-- The complete three-regime theorem has the exact
-- signed base-two window, and the subcritical cLower remains outside xi and m.
example (k : ℕ) (hk : 3 ≤ k) :
    (∀ gamma : ℝ, gamma ∈ Ioo (gammaK k) 1 →
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
        Tendsto (fun n ↦ supercriticalCoMultipartiteProbability k n (m n)) atTop (𝓝 1)) ∧
    (∀ a : ℝ,
      (a ≤ criticalWindowBase2Threshold k → ∀ epsilon : ℝ, 0 < epsilon →
        Tendsto (criticalWindowBase2StructuredProbability k a epsilon) atTop (𝓝 1)) ∧
      (criticalWindowBase2Threshold k < a →
        Tendsto (fun n ↦ supercriticalCoMultipartiteProbability k n
          (criticalWindowBase2EdgeCount k a n)) atTop (𝓝 1))) ∧
    (∀ gamma : ℝ, gamma ∈ Ioo (0 : ℝ) (gammaK k) →
      ∃ cLower : ℝ, 0 < cLower ∧ ∀ xi : ℝ, 0 < xi →
        ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
          Tendsto (fun n ↦ subcriticalStructuredProbability k gamma cLower xi n (m n))
            atTop (𝓝 1)) :=
  inducedStarAlmostAll k hk

-- The natural-log auxiliary includes equality at the transition,
-- every positive accuracy, and the strictly-above-threshold empty remainder.
example (k : ℕ) (hk : 3 ≤ k) :
    ∀ a : ℝ,
      (a ≤ criticalWindowThreshold k → ∀ epsilon : ℝ, 0 < epsilon →
        Tendsto (criticalWindowStructuredProbability k a epsilon) atTop (𝓝 1)) ∧
      (criticalWindowThreshold k < a →
        Tendsto (fun n ↦ supercriticalCoMultipartiteProbability k n
          (criticalWindowEdgeCount k a n)) atTop (𝓝 1)) :=
  inducedStarCriticalWindowAlmostAll k hk

-- The paper-facing critical clause uses base-two logarithms.
example (k : ℕ) (hk : 3 ≤ k) :
    ∀ a : ℝ,
      (a ≤ criticalWindowBase2Threshold k → ∀ epsilon : ℝ, 0 < epsilon →
        Tendsto (criticalWindowBase2StructuredProbability k a epsilon) atTop (𝓝 1)) ∧
      (criticalWindowBase2Threshold k < a →
        Tendsto (fun n ↦ supercriticalCoMultipartiteProbability k n
          (criticalWindowBase2EdgeCount k a n)) atTop (𝓝 1)) :=
  inducedStarCriticalWindowBase2AlmostAll k hk

-- The base is explicit, including the factor converting natural logarithms.
example (x : ℝ) : InducedStars.log2 x = Real.log x / Real.log 2 := rfl

example (k n : ℕ) (a : ℝ) :
    criticalWindowBase2EdgeCount k a n =
      ⌊(gammaK k + a * InducedStars.log2 (n : ℝ) / n) *
        (Nat.choose n 2 : ℝ)⌋₊ := rfl

example (k : ℕ) :
    criticalWindowBase2Threshold k =
      ((k - 2 : ℕ) : ℝ) * pK k * (1 - pK k) * Real.log 2 /
        (((k - 1 : ℕ) : ℝ) * gammaK k) := rfl

example (k : ℕ) (a : ℝ) :
    criticalWindowBase2RemainderCoefficient k a =
      (criticalWindowBase2Threshold k - a) / (2 * gammaK k) := rfl

-- One base-two witness carries the literal decomposition and remainder size.
example {k n : ℕ} (a epsilon : ℝ) (G : SimpleGraph (Fin n)) :
    HasCriticalWindowBase2Structure k a epsilon G ↔
      ∃ W : CriticalStructureWitness k n G,
        G = W.core.spanningCoe ⊔ W.remainder.spanningCoe ∧
        DenseGraph.IsCoMultipartite W.core (k - 1) ∧
        (∀ x ∈ W.exceptionalVertices, ∀ y ∉ W.exceptionalVertices, ¬G.Adj x y) ∧
        |(W.exceptionalVertices.card : ℝ) / InducedStars.log2 (n : ℝ) -
          (criticalWindowBase2Threshold k - a) / (2 * gammaK k)| ≤ epsilon := by
  constructor
  · rintro ⟨W, hW⟩
    exact ⟨W, W.decomposition, W.coreCoMultipartite,
      fun _ hx _ hy ↦ W.not_adj_of_mem_exceptional_of_not_mem hx hy, hW⟩
  · rintro ⟨W, _, _, _, hW⟩
    exact ⟨W, hW⟩

example (k n : ℕ) (a epsilon : ℝ) :
    criticalWindowBase2StructuredProbability k a epsilon n =
      uniformSubfamilyProbability
        (inducedStarFreeGraphFinsetWithEdges k n
          ⌊(gammaK k + a * InducedStars.log2 (n : ℝ) / n) *
            (Nat.choose n 2 : ℝ)⌋₊)
        ((inducedStarFreeGraphFinsetWithEdges k n
          ⌊(gammaK k + a * InducedStars.log2 (n : ℝ) / n) *
            (Nat.choose n 2 : ℝ)⌋₊).filter
          fun G ↦ ∃ W : CriticalStructureWitness k n G,
            |(W.exceptionalVertices.card : ℝ) / InducedStars.log2 (n : ℝ) -
              (criticalWindowBase2Threshold k - a) / (2 * gammaK k)| ≤ epsilon) := rfl
