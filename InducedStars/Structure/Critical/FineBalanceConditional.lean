import InducedStars.Structure.Critical.FineBalanceCanonical
import InducedStars.Structure.Critical.FineBalanceInducedFree
import InducedStars.Structure.Critical.FineBalanceProbability
import Mathlib.Tactic

/-!
# Conditional fixed-sparse fine balance

This file sums the fixed-remainder Gaussian estimate over the graph induced
on the prescribed sparse set.  The fibers are disjoint because that induced
graph is a function of the ambient graph.  Remainders containing an induced
`K₁,ₖ` contribute nothing: every graph in the canonical clean conditioning
family is induced-`K₁,ₖ`-free.  Thus a denominator comparison is needed only
for induced-star-free remainders.
-/

noncomputable section

open Finset Filter Set Topology
open scoped BigOperators

namespace InducedStars

noncomputable local instance criticalFineBalanceConditionalGraphDecidableEq
    (n : ℕ) : DecidableEq (SimpleGraph (Fin n)) :=
  Classical.decEq _

noncomputable local instance criticalFineBalanceConditionalRemainderDecidableEq
    (n : ℕ) (S : Finset (Fin n)) :
    DecidableEq (SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))) :=
  Classical.decEq _

attribute [local instance] criticalFineBalanceCanonicalEdgeSetFintype

private theorem card_eq_sum_card_eq_fibers
    {alpha beta : Type*} [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta]
    (family : Finset alpha) (fiber : alpha → beta) :
    family.card = ∑ b : beta, (family.filter fun a ↦ fiber a = b).card := by
  simpa using
    (Finset.card_eq_sum_card_fiberwise
      (s := family) (t := (Finset.univ : Finset beta)) (f := fiber)
      (by intro a ha; simp))

/-- A prescribed sparse remainder containing an induced star has empty
canonical clean conditioning fiber. -/
theorem
    criticalFixedRemainderCanonicalCleanGraphFinset_eq_empty_of_inducedEmbeds
    {k n : ℕ} (hk : 3 ≤ k) (tau : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n))
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    (hR : Regularity.InducedEmbeds (inducedStar k) R) :
    criticalFixedRemainderCanonicalCleanGraphFinset
        k hk n tau hn S R = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro G hG
  have hfixed :=
    mem_criticalFixedRemainderCanonicalCleanGraphFinset.mp hG
  obtain ⟨hclose, hsparse, hzero⟩ :=
    mem_criticalCanonicalCleanFixedSparseGraphFinset.mp hfixed.1
  have hfree := (mem_supercriticalCloseGraphFinset.mp hclose).1
  let D := canonicalSupercriticalDivision G (by simpa using hn)
  have hclean : supercriticalDefectGraph G D = ⊥ := by
    apply simpleGraph_eq_bot_of_finiteGraphEdges_card_eq_zero
    simpa [D, canonicalSupercriticalDefectGraph] using hzero
  have hsparseEmbed : Regularity.InducedEmbeds (inducedStar k)
      (G.induce (D.sparse : Set (Fin n))) := by
    rw [show D.sparse = S by simpa [D] using hsparse]
    change Regularity.InducedEmbeds (inducedStar k)
      (fixedSparseRemainderGraph S G)
    rw [hfixed.2]
    exact hR
  exact hfree
    ((inducedEmbeds_inducedStar_iff_sparse_of_clean
      (by omega : 1 ≤ k) G D hclean).mpr hsparseEmbed)

/-- The full canonical fixed-sparse family is the disjoint union of its
fixed-remainder fibers. -/
theorem card_criticalCanonicalCleanFixedSparseGraphFinset_eq_sum_remainders
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n)) :
    (criticalCanonicalCleanFixedSparseGraphFinset
        k hk n tau hn S).card =
      ∑ R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)),
        (criticalFixedRemainderCanonicalCleanGraphFinset
          k hk n tau hn S R).card := by
  classical
  let family := criticalCanonicalCleanFixedSparseGraphFinset
    k hk n tau hn S
  let remainder (G : SimpleGraph (Fin n)) := fixedSparseRemainderGraph S G
  rw [card_eq_sum_card_eq_fibers family remainder]
  apply Finset.sum_congr rfl
  intro R _hR
  apply congrArg Finset.card
  ext G
  simp [family, remainder]

/-- The fixed-sparse fine-unbalanced family is likewise the disjoint union
of its fixed-remainder fibers. -/
theorem card_criticalFixedSparseUnbalancedCleanGraphFinset_eq_sum_remainders
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n)) :
    (criticalFixedSparseUnbalancedCleanGraphFinset
        k hk n tau hn S).card =
      ∑ R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)),
        (criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset
          k hk n tau hn S R).card := by
  classical
  let family := criticalFixedSparseUnbalancedCleanGraphFinset
    k hk n tau hn S
  let remainder (G : SimpleGraph (Fin n)) := fixedSparseRemainderGraph S G
  rw [card_eq_sum_card_eq_fibers family remainder]
  apply Finset.sum_congr rfl
  intro R _hR
  apply congrArg Finset.card
  ext G
  simp [family, remainder,
    mem_criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset]

/-- Summing the exact fixed-remainder Gaussian estimates gives the desired
finite conditional comparison.  The hypothesis compares the balanced raw
reference slice with the actual fixed-remainder conditioning fiber only for
induced-star-free `R`; all other fibers are empty. -/
theorem criticalFixedSparseUnbalancedCleanGraphFinset_card_le_of_remainders
    {k n : ℕ} (hk : 3 ≤ k) (tau : ℝ) (hn : k - 1 ≤ n)
    (hnTwo : 2 ≤ n) (S : Finset (Fin n))
    (hsSmall : (S.card : ℝ) ≤
      criticalFineBalanceSparseFraction k * (n : ℝ))
    (A : ℝ)
    (hreference :
      ∀ R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)),
        ¬ Regularity.InducedEmbeds (inducedStar k) R →
        criticalFixedSparseBalancedCrossSliceMass
            k n S.card R.edgeFinset.card ≤
          A * ((criticalFixedRemainderCanonicalCleanGraphFinset
            k hk n tau hn S R).card : ℝ)) :
    ((criticalFixedSparseUnbalancedCleanGraphFinset
        k hk n tau hn S).card : ℝ) ≤
      (A * criticalFineBalanceRawError k n) *
        ((criticalCanonicalCleanFixedSparseGraphFinset
          k hk n tau hn S).card : ℝ) := by
  classical
  let remainderType :=
    SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))
  have hpointwise (R : remainderType) :
      ((criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset
          k hk n tau hn S R).card : ℝ) ≤
        (A * criticalFineBalanceRawError k n) *
          ((criticalFixedRemainderCanonicalCleanGraphFinset
            k hk n tau hn S R).card : ℝ) := by
    by_cases hRfree : ¬ Regularity.InducedEmbeds (inducedStar k) R
    · calc
        ((criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset
            k hk n tau hn S R).card : ℝ) ≤
            criticalFixedSparseBalancedCrossSliceMass
                k n S.card R.edgeFinset.card *
              criticalFineBalanceRawError k n :=
          card_criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset_le_reference_mul_error
            hk tau hn hnTwo S R hsSmall
        _ ≤ (A *
              ((criticalFixedRemainderCanonicalCleanGraphFinset
                k hk n tau hn S R).card : ℝ)) *
              criticalFineBalanceRawError k n :=
          mul_le_mul_of_nonneg_right (hreference R hRfree)
            (criticalFineBalanceRawError_nonneg k n)
        _ = (A * criticalFineBalanceRawError k n) *
              ((criticalFixedRemainderCanonicalCleanGraphFinset
                k hk n tau hn S R).card : ℝ) := by ring
    · have hRembed : Regularity.InducedEmbeds (inducedStar k) R :=
        Classical.not_not.mp hRfree
      have hfullEmpty :=
        criticalFixedRemainderCanonicalCleanGraphFinset_eq_empty_of_inducedEmbeds
          hk tau hn S R hRembed
      have hbadEmpty :
          criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset
              k hk n tau hn S R = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro G hG
        have hbad :=
          mem_criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset.mp hG
        have hbadData :=
          mem_criticalFixedSparseUnbalancedCleanGraphFinset.mp hbad.1
        have hfull : G ∈
            criticalFixedRemainderCanonicalCleanGraphFinset
              k hk n tau hn S R :=
          mem_criticalFixedRemainderCanonicalCleanGraphFinset.mpr
            ⟨hbadData.1, hbad.2⟩
        rw [hfullEmpty] at hfull
        simpa using hfull
      rw [hbadEmpty, hfullEmpty]
      simp
  rw [card_criticalFixedSparseUnbalancedCleanGraphFinset_eq_sum_remainders,
    Nat.cast_sum]
  calc
    ∑ R : remainderType,
        ((criticalFixedRemainderUnbalancedCanonicalCleanGraphFinset
          k hk n tau hn S R).card : ℝ) ≤
        ∑ R : remainderType,
          (A * criticalFineBalanceRawError k n) *
            ((criticalFixedRemainderCanonicalCleanGraphFinset
              k hk n tau hn S R).card : ℝ) :=
      Finset.sum_le_sum fun R _hR ↦ hpointwise R
    _ = (A * criticalFineBalanceRawError k n) *
        ∑ R : remainderType,
          ((criticalFixedRemainderCanonicalCleanGraphFinset
            k hk n tau hn S R).card : ℝ) := by
      rw [Finset.mul_sum]
    _ = (A * criticalFineBalanceRawError k n) *
        ((criticalCanonicalCleanFixedSparseGraphFinset
          k hk n tau hn S).card : ℝ) := by
      rw [← Nat.cast_sum,
        ← card_criticalCanonicalCleanFixedSparseGraphFinset_eq_sum_remainders]

/-- Finite conditional-probability form of the remainder transfer.  The only
nonemptiness assumption is the one required to interpret the conditioning
family as a genuine uniform probability. -/
theorem criticalFixedSparseFineBalanceFailureProbability_le_of_remainders
    {k n : ℕ} (hk : 3 ≤ k) (tau : ℝ) (hn : k - 1 ≤ n)
    (hnTwo : 2 ≤ n) (S : Finset (Fin n))
    (hsSmall : (S.card : ℝ) ≤
      criticalFineBalanceSparseFraction k * (n : ℝ))
    (A : ℝ)
    (hreference :
      ∀ R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)),
        ¬ Regularity.InducedEmbeds (inducedStar k) R →
        criticalFixedSparseBalancedCrossSliceMass
            k n S.card R.edgeFinset.card ≤
          A * ((criticalFixedRemainderCanonicalCleanGraphFinset
            k hk n tau hn S R).card : ℝ))
    (hne : (criticalCanonicalCleanFixedSparseGraphFinset
      k hk n tau hn S).Nonempty) :
    criticalFixedSparseFineBalanceFailureProbability k hk tau n S ≤
      A * criticalFineBalanceRawError k n := by
  apply criticalFixedSparseFineBalanceFailureProbability_le_of_card_le
    k hk tau n hn S hne
  exact criticalFixedSparseUnbalancedCleanGraphFinset_card_le_of_remainders
    hk tau hn hnTwo S hsSmall A hreference

/-- Sequence form: whenever the balanced-reference comparison is uniform
along a sequence of sparse sets, its prefactor times the raw Gaussian error
tends to zero, and the conditioning families are eventually nonempty, the
literal conditional fine-balance failure probability tends to zero. -/
theorem
    criticalFixedSparseFineBalanceFailureProbability_tendsto_zero_of_remainders
    (k : ℕ) (hk : 3 ≤ k) (tau : ℝ)
    (A : ℕ → ℝ) (S : ∀ n : ℕ, Finset (Fin n))
    (hsSmall : ∀ᶠ n : ℕ in atTop,
      ((S n).card : ℝ) ≤
        criticalFineBalanceSparseFraction k * (n : ℝ))
    (hne : ∀ᶠ n : ℕ in atTop, ∀ hn : k - 1 ≤ n,
      (criticalCanonicalCleanFixedSparseGraphFinset
        k hk n tau hn (S n)).Nonempty)
    (hreference : ∀ᶠ n : ℕ in atTop, ∀ hn : k - 1 ≤ n,
      ∀ R : SimpleGraph ({v : Fin n | v ∈ S n} : Set (Fin n)),
        ¬ Regularity.InducedEmbeds (inducedStar k) R →
        criticalFixedSparseBalancedCrossSliceMass
            k n (S n).card R.edgeFinset.card ≤
          A n * ((criticalFixedRemainderCanonicalCleanGraphFinset
            k hk n tau hn (S n) R).card : ℝ))
    (herror : Tendsto
      (fun n ↦ A n * criticalFineBalanceRawError k n)
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦ criticalFixedSparseFineBalanceFailureProbability
        k hk tau n (S n)) atTop (nhds 0) := by
  have hlarge : ∀ᶠ n : ℕ in atTop, k - 1 ≤ n ∧ 2 ≤ n :=
    Filter.eventually_atTop.2 ⟨max (k - 1) 2, fun n hn ↦
      ⟨(le_max_left _ _).trans hn, (le_max_right _ _).trans hn⟩⟩
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ criticalFixedSparseFineBalanceFailureProbability
        k hk tau n (S n) := by
    filter_upwards [hlarge, hne] with n hnLarge hnNonempty
    rw [criticalFixedSparseFineBalanceFailureProbability,
      dif_pos hnLarge.1]
    apply uniformSubfamilyProbability_nonneg (hnNonempty hnLarge.1)
    intro G hG
    exact (mem_criticalFixedSparseUnbalancedCleanGraphFinset.mp hG).1
  have hupper : ∀ᶠ n : ℕ in atTop,
      criticalFixedSparseFineBalanceFailureProbability
          k hk tau n (S n) ≤
        A n * criticalFineBalanceRawError k n := by
    filter_upwards [hlarge, hsSmall, hne, hreference] with
      n hnLarge hnSmall hnNonempty hnReference
    exact criticalFixedSparseFineBalanceFailureProbability_le_of_remainders
      hk tau hnLarge.1 hnLarge.2 (S n) hnSmall (A n)
        (hnReference hnLarge.1) (hnNonempty hnLarge.1)
  exact squeeze_zero' hnonneg hupper herror

end InducedStars
