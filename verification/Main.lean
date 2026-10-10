import DenseGraph
import InducedStars

/-!
Main declarations advertised in docs/RESULTS.md. Run from the repository root:

    lake env lean verification/Main.lean

Each #check displays the actual statement; each #print axioms displays its
transitive assumption boundary. The examples check the complete typical-structure
statement and the exact critical edge count and joint decomposition event explicitly.
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
#check InducedStars.inducedStarCriticalAlmostAll
#print axioms InducedStars.inducedStarCriticalAlmostAll
#check InducedStars.criticalLargeRemainders
#print axioms InducedStars.criticalLargeRemainders
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

-- The critical coefficient depends only on k. The subcritical cLower
-- remains outside both the accuracy xi and the edge-count sequence m.
example (k : ℕ) (hk : 3 ≤ k) :
    (∀ gamma : ℝ, gamma ∈ Ioo (gammaK k) 1 →
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
        Tendsto (fun n ↦ supercriticalCoMultipartiteProbability k n (m n)) atTop (𝓝 1)) ∧
    (∃ L : ℝ, 0 < L ∧
      Tendsto (fun n ↦ criticalStructuredProbability k n
        (Nat.ceil (L * Real.logb 2 (n : ℝ)))) atTop (𝓝 1)) ∧
    (∀ gamma : ℝ, gamma ∈ Ioo (0 : ℝ) (gammaK k) →
      ∃ cLower : ℝ, 0 < cLower ∧ ∀ xi : ℝ, 0 < xi →
        ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
          Tendsto (fun n ↦ subcriticalStructuredProbability k gamma cLower xi n (m n))
            atTop (𝓝 1)) :=
  inducedStarAlmostAll k hk

-- The exact critical event uses the paper's base-two logarithm.
example (k : ℕ) (hk : 3 ≤ k) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun n ↦ criticalStructuredProbability k n
        (Nat.ceil (L * Real.logb 2 (n : ℝ)))) atTop (𝓝 1) :=
  inducedStarCriticalAlmostAll k hk

-- Both current Q_s conclusions use the actual co-partite denominator.
-- The three positive constants depend only on k and are chosen before n.
example (k : ℕ) (hk : 3 ≤ k) :
    ∃ xi L C : ℝ, 0 < xi ∧ 0 < L ∧ 0 < C ∧
      Tendsto (fun n ↦ criticalRemainderCompletionTail k xi L n /
        (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ))
          atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        criticalRemainderCompletionSum k xi n ≤
          (2 : ℝ)^(C * (Real.logb 2 (n : ℝ))^2) *
            (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) :=
  criticalLargeRemainders k hk

example (k n : ℕ) :
    criticalEdgeCount k n = ⌊gammaK k * (Nat.choose n 2 : ℝ)⌋₊ := rfl

-- One witness carries the literal disjoint union and the remainder bound.
example {k n bound : ℕ} (G : SimpleGraph (Fin n)) :
    HasCriticalStructure k bound G ↔
      ∃ W : CriticalStructureWitness k n G,
        G = W.core.spanningCoe ⊔ W.remainder.spanningCoe ∧
        DenseGraph.IsCoMultipartite W.core (k - 1) ∧
        (∀ x ∈ W.exceptionalVertices, ∀ y ∉ W.exceptionalVertices, ¬G.Adj x y) ∧
        W.exceptionalVertices.card ≤ bound := by
  constructor
  · rintro ⟨W, hW⟩
    exact ⟨W, W.decomposition, W.coreCoMultipartite,
      fun _ hx _ hy ↦ W.not_adj_of_mem_exceptional_of_not_mem hx hy, hW⟩
  · rintro ⟨W, _, _, _, hW⟩
    exact ⟨W, hW⟩

example (k n bound : ℕ) :
    criticalStructuredProbability k n bound =
      uniformSubfamilyProbability
        (inducedStarFreeGraphFinsetWithEdges k n
          ⌊gammaK k * (Nat.choose n 2 : ℝ)⌋₊)
        ((inducedStarFreeGraphFinsetWithEdges k n
          ⌊gammaK k * (Nat.choose n 2 : ℝ)⌋₊).filter
            fun G ↦ ∃ W : CriticalStructureWitness k n G,
              W.exceptionalVertices.card ≤ bound) := rfl

-- The strictly supercritical theorem permits every edge sequence
-- with the stated limiting density.
example (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Ioo (gammaK k) 1)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    Tendsto (fun n ↦ supercriticalCoMultipartiteProbability k n (m n))
      atTop (𝓝 1) :=
  inducedStarSupercriticalAlmostAllCoMultipartite k hk gamma hgamma m hm

-- The linear lower coefficient is chosen before both accuracy and edge sequence.
example (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) :
    ∃ cLower : ℝ, 0 < cLower ∧ ∀ xi : ℝ, 0 < xi →
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
        Tendsto (fun n ↦ subcriticalStructuredProbability k gamma cLower xi n (m n))
          atTop (𝓝 1) :=
  inducedStarSubcriticalAlmostAll k hk hgamma

-- The subcritical event has one core and one complementary remainder;
-- core size, the linear lower bound, and the subquadratic upper bound are joint.
example {k n : ℕ} (gamma cLower xi : ℝ) (G : SimpleGraph (Fin n)) :
    HasSubcriticalStructure k gamma cLower xi G ↔
      ∃ U : Finset (Fin n),
        G = (G.induce (U : Set (Fin n))).spanningCoe ⊔
          (G.induce (U : Set (Fin n))ᶜ).spanningCoe ∧
        (∀ x ∈ U, ∀ y ∉ U, ¬G.Adj x y) ∧
        DenseGraph.IsCoMultipartite (G.induce (U : Set (Fin n))) (k - 1) ∧
        |(U.card : ℝ) / n - subcriticalOneBlockLength k gamma| ≤ xi ∧
        cLower * n ≤ (finiteGraphEdges (G.induce (U : Set (Fin n))ᶜ)).card ∧
        (finiteGraphEdges (G.induce (U : Set (Fin n))ᶜ)).card ≤ xi * (n : ℝ)^2 :=
  hasSubcriticalStructure_iff_disjointUnion G

example (k n m : ℕ) (gamma cLower xi : ℝ) :
    subcriticalStructuredProbability k gamma cLower xi n m =
      uniformSubfamilyProbability (inducedStarFreeGraphFinsetWithEdges k n m)
        ((inducedStarFreeGraphFinsetWithEdges k n m).filter
          fun G ↦ ∃ W : SubcriticalStructureWitness k n G,
            |(W.coreVertices.card : ℝ) / n - subcriticalOneBlockLength k gamma| ≤ xi ∧
              cLower * n ≤ W.remainderEdgeCount ∧
              W.remainderEdgeCount ≤ xi * (n : ℝ)^2) := rfl

-- The fixed-H endpoint is uniform in every finite edge count m, with the
-- same prescribed H in the graph family and completion reference.
example (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∀ᶠ n : ℕ in atTop, ∀ (m : ℕ) (hn : k - 1 ≤ n)
      (D : SupercriticalDivision k (Fin n)) (H : Finset (Sym2 (Fin n))),
      ((supercriticalFixedRemainderDefectGraphFinset
        k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
          m n P.tau hn D H).card : ℝ) ≤
        (Nat.choose (supercriticalTotalCrossCapacity D)
          (m - (divisionInternalCliqueCapacity D + H.card)) : ℝ) *
            Real.exp (-(P.cMat / 4) * n) :=
  eventually_criticalFixedRemainderDefect_le_reference k hk P

-- The actual downstream local-compensation API treats every profile root.
example {k n R₀ : ℕ} {D : SubcriticalDivision k (Fin n)}
    {eta theta omega alpha delta epsilon : ℝ} {G : SimpleGraph (Fin n)}
    {L : AdmissibleBlockSequence k} (hk : 3 ≤ k)
    (P : SubcriticalLocalPenaltyParameters k R₀ eta theta alpha delta epsilon n)
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (homega : omega ≤ 1) (hfree : ¬Regularity.InducedEmbeds (inducedStar k) G)
    (hminimal : ∀ E : SubcriticalDivision k (Fin n),
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    {p : SubcriticalProfile D eta R₀ theta} (hp : RealizesSubcriticalProfile G alpha p)
    (hB : (p.roots.card : ℝ) ≤ subcriticalProfileRootFraction alpha theta epsilon * n)
    (m : ℕ) (C : ℝ) (v : Fin n) (hv : v ∈ p.roots) :
    subcriticalProfileLocalExponent p m C alpha delta epsilon v ≤
      -(subcriticalLocalPenaltyUnit k * eta * n / (R₀ : ℝ)) :=
  subcriticalLocalCompensation_of_geometry hk P R homega hfree hminimal hp hB m C v hv

#print axioms inducedStarCriticalAlmostAll
#print axioms inducedStarAlmostAll
#print axioms inducedStarSubcriticalAlmostAll
#print axioms subcriticalLocalCompensation_of_geometry
#print axioms subcriticalRetainedRootUnifiedPenalty
#print axioms eventually_criticalFixedRemainderDefect_le_reference

-- Current fixed-H profile penalty with its explicit polynomial reserve.
#check subcriticalProfileBound_fixedRemainder
#print axioms subcriticalProfileBound_fixedRemainder

-- Complete current-paper residual sum over every admissible graph.
open scoped BigOperators
example
    {k R₀ : ℕ} {eta : ℝ}
    (hk : 3 ≤ k)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hR₀ : 1 ≤ R₀) (w : ℝ) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ subcriticalResidualDegreeCap k eta R₀ ∧ d0 ≤ 1 / 2 ∧
      ∀ᶠ n : ℕ in atTop, ∀ d ∈ Icc (0 : ℝ) d0,
        ∀ (D : SubcriticalDivision k (Fin n)) (B : Finset (Fin n))
          (H : SubcriticalRemainderGraph D eta R₀) (m ell : ℕ) (Cwin delta epsilon : ℝ),
        1 ≤ ell → delta ≤ subcriticalPaletteGap k / 2 →
        (∀ a ∈ D.retainedPartIndices eta R₀,
          eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ)) →
        (B.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 2 →
        (∑ R ∈ subcriticalAdmissibleResidualFinset D eta R₀ B d ell,
          (2 : ℝ) ^ (w * (finiteGraphEdges R).card) *
            subcriticalAdmissibleResidualSafeMaximum B H R m Cwin delta epsilon) ≤
          (2 : ℝ) ^ (-(subcriticalAdmissibleResidualBinaryMatchingConstant k eta R₀ /
            (2 * (subcriticalResidualMatchingKappa eta R₀ : ℝ))) * ell * n) :=
  subcriticalResidualMatchingAllAdmissible hk heta hetaOne hR₀ w

#print axioms subcriticalResidualMatchingAllAdmissible


-- Exact binary weighted sum in the zero-matching case.
example {k n R₀ : ℕ} {D : SubcriticalDivision k (Fin n)} {eta : ℝ}
    (B : Finset (Fin n)) (H : SubcriticalRemainderGraph D eta R₀)
    (m : ℕ) (Cwin delta epsilon d w : ℝ) (hd : 0 ≤ d)
    (hne : (retainedNarrowEdgeCountWindow D eta R₀ m Cwin delta epsilon).Nonempty) :
    (∑ R ∈ subcriticalAdmissibleResidualFinset D eta R₀ B d 0,
      (2 : ℝ) ^ (w * (finiteGraphEdges R).card) *
        subcriticalAdmissibleResidualSafeMaximum B H R m Cwin delta epsilon) = 1 :=
  subcriticalAdmissibleResidualSafetySum_zero_baseTwo B H m Cwin delta epsilon d w hd hne

#print axioms subcriticalAdmissibleResidualSafetySum_zero_baseTwo
