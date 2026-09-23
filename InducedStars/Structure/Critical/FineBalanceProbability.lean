import InducedStars.Structure.Critical.FineBalance
import InducedStars.Structure.Critical.FixedSparseCoverMultiplicity

/-!
# Literal fixed-sparse fine-balance events

The conditioning family here consists of the paper's canonical clean close
graphs with one prescribed sparse set.  The good and bad events form an
exact partition.  Probability statements require a nonempty conditioning
family; the definitions are assigned zero before a canonical division can
exist, and no probabilistic conclusion is drawn from that convention.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The literal fine-balanced event inside the canonical fixed-sparse clean
family. -/
noncomputable def criticalFixedSparseFineBalancedCleanGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (τ : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n)) : Finset (SimpleGraph (Fin n)) :=
  (criticalCanonicalCleanFixedSparseGraphFinset k hk n τ hn S).filter fun G ↦
    IsCriticalFineBalanced hk (canonicalSupercriticalDivision G (by simpa using hn))

/-- Membership in the bad event is precisely failure of fine balance for
the canonical division, within the same conditioning family. -/
theorem mem_criticalFixedSparseUnbalancedCleanGraphFinset
    {k n : ℕ} {hk : 3 ≤ k} {τ : ℝ} {hn : k - 1 ≤ n}
    {S : Finset (Fin n)} {G : SimpleGraph (Fin n)} :
    G ∈ criticalFixedSparseUnbalancedCleanGraphFinset k hk n τ hn S ↔
      G ∈ criticalCanonicalCleanFixedSparseGraphFinset k hk n τ hn S ∧
        ¬ IsCriticalFineBalanced hk
          (canonicalSupercriticalDivision G (by simpa using hn)) := by
  classical
  constructor
  · intro hG
    obtain ⟨D, hD, hG⟩ := Finset.mem_biUnion.mp hG
    obtain ⟨hDsparse, hDnot⟩ := Finset.mem_filter.mp hD
    have hDs := mem_criticalDivisionsWithSparseSet.mp hDsparse
    obtain ⟨hclose, hcanonical, hzero⟩ :=
      mem_supercriticalCleanDivisionGraphFinset.mp hG
    refine ⟨mem_criticalCanonicalCleanFixedSparseGraphFinset.mpr
      ⟨hclose, hcanonical ▸ hDs, hzero⟩, ?_⟩
    simpa only [hcanonical] using hDnot
  · rintro ⟨hG, hnot⟩
    obtain ⟨hclose, hsparse, hzero⟩ :=
      mem_criticalCanonicalCleanFixedSparseGraphFinset.mp hG
    let D := canonicalSupercriticalDivision G (by simpa using hn)
    apply Finset.mem_biUnion.mpr
    refine ⟨D, Finset.mem_filter.mpr
      ⟨mem_criticalDivisionsWithSparseSet.mpr hsparse, hnot⟩, ?_⟩
    exact mem_supercriticalCleanDivisionGraphFinset.mpr ⟨hclose, rfl, hzero⟩

theorem criticalFixedSparseUnbalancedCleanGraphFinset_eq_filter
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (τ : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n)) :
    criticalFixedSparseUnbalancedCleanGraphFinset k hk n τ hn S =
      (criticalCanonicalCleanFixedSparseGraphFinset k hk n τ hn S).filter
        (fun G ↦ ¬ IsCriticalFineBalanced hk
          (canonicalSupercriticalDivision G (by simpa using hn))) := by
  classical
  ext G
  simp only [mem_criticalFixedSparseUnbalancedCleanGraphFinset, Finset.mem_filter]

/-- The good and bad fine-balance events are disjoint. -/
theorem criticalFixedSparseFineBalance_disjoint
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (τ : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n)) :
    Disjoint (criticalFixedSparseFineBalancedCleanGraphFinset k hk n τ hn S)
      (criticalFixedSparseUnbalancedCleanGraphFinset k hk n τ hn S) := by
  classical
  rw [criticalFixedSparseUnbalancedCleanGraphFinset_eq_filter,
    criticalFixedSparseFineBalancedCleanGraphFinset]
  exact Finset.disjoint_filter_filter_not _ _ _

open scoped Classical in
/-- The good and bad events exhaust the exact conditioning family. -/
theorem criticalFixedSparseFineBalance_union
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (τ : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n)) :
    criticalFixedSparseFineBalancedCleanGraphFinset k hk n τ hn S ∪
      criticalFixedSparseUnbalancedCleanGraphFinset k hk n τ hn S =
        criticalCanonicalCleanFixedSparseGraphFinset k hk n τ hn S := by
  classical
  rw [criticalFixedSparseUnbalancedCleanGraphFinset_eq_filter,
    criticalFixedSparseFineBalancedCleanGraphFinset]
  exact Finset.filter_union_filter_not_eq _ _

/-- Exact good/bad decomposition, with no asymptotic or nonemptiness
hypothesis. -/
theorem criticalFixedSparseFineBalance_card_partition
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (τ : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n)) :
    (criticalFixedSparseFineBalancedCleanGraphFinset k hk n τ hn S).card +
      (criticalFixedSparseUnbalancedCleanGraphFinset k hk n τ hn S).card =
        (criticalCanonicalCleanFixedSparseGraphFinset k hk n τ hn S).card := by
  classical
  rw [criticalFixedSparseUnbalancedCleanGraphFinset_eq_filter,
    criticalFixedSparseFineBalancedCleanGraphFinset]
  exact Finset.card_filter_add_card_filter_not _

/-- Conditional failure probability for the paper's exact fine-balance
event.  Its denominator is the canonical clean close family, not raw ordered
cover mass. -/
noncomputable def criticalFixedSparseFineBalanceFailureProbability
    (k : ℕ) (hk : 3 ≤ k) (τ : ℝ) (n : ℕ) (S : Finset (Fin n)) : ℝ :=
  if hn : k - 1 ≤ n then
    uniformSubfamilyProbability
      (criticalCanonicalCleanFixedSparseGraphFinset k hk n τ hn S)
      (criticalFixedSparseUnbalancedCleanGraphFinset k hk n τ hn S)
  else 0

/-- Conditional fine-balance probability in the same fixed-sparse family. -/
noncomputable def criticalFixedSparseFineBalanceProbability
    (k : ℕ) (hk : 3 ≤ k) (τ : ℝ) (n : ℕ) (S : Finset (Fin n)) : ℝ :=
  if hn : k - 1 ≤ n then
    uniformSubfamilyProbability
      (criticalCanonicalCleanFixedSparseGraphFinset k hk n τ hn S)
      (criticalFixedSparseFineBalancedCleanGraphFinset k hk n τ hn S)
  else 0

/-- The two genuine conditional probabilities add to one whenever their
conditioning family is nonempty. -/
theorem criticalFixedSparseFineBalanceProbability_add_failure
    (k : ℕ) (hk : 3 ≤ k) (τ : ℝ) (n : ℕ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n))
    (hne : (criticalCanonicalCleanFixedSparseGraphFinset k hk n τ hn S).Nonempty) :
    criticalFixedSparseFineBalanceProbability k hk τ n S +
      criticalFixedSparseFineBalanceFailureProbability k hk τ n S = 1 := by
  rw [criticalFixedSparseFineBalanceProbability, dif_pos hn,
    criticalFixedSparseFineBalanceFailureProbability, dif_pos hn]
  unfold uniformSubfamilyProbability
  rw [← add_div, ← Nat.cast_add, criticalFixedSparseFineBalance_card_partition]
  exact div_self (by exact_mod_cast (Finset.card_pos.mpr hne).ne')

/-- Convert an actual canonical-family cardinality estimate into the
corresponding conditional probability bound.  Nonemptiness is explicit. -/
theorem criticalFixedSparseFineBalanceFailureProbability_le_of_card_le
    (k : ℕ) (hk : 3 ≤ k) (τ : ℝ) (n : ℕ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n)) {ε : ℝ}
    (hne : (criticalCanonicalCleanFixedSparseGraphFinset k hk n τ hn S).Nonempty)
    (hcard : ((criticalFixedSparseUnbalancedCleanGraphFinset k hk n τ hn S).card : ℝ) ≤
      ε * ((criticalCanonicalCleanFixedSparseGraphFinset k hk n τ hn S).card : ℝ)) :
    criticalFixedSparseFineBalanceFailureProbability k hk τ n S ≤ ε := by
  rw [criticalFixedSparseFineBalanceFailureProbability, dif_pos hn]
  unfold uniformSubfamilyProbability
  exact (div_le_iff₀ (by exact_mod_cast Finset.card_pos.mpr hne)).mpr hcard

end InducedStars
