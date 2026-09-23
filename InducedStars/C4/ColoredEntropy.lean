import DenseGraph.Combinatorics.FeasibleEntropySlice
import InducedStars.C4.ColoredBasic

/-!
# Feasible colored entropy and the complete-template benchmark

The benchmark in `eqn:coloring-entropy-0` uses complete templates. Partial templates remain inputs to entropy and stability. Zero red
capacity is feasible only when the target equals the blue count.
-/

noncomputable section
open Finset InducedStars.Regularity
open scoped Classical
namespace InducedStars

def c4ColorEdgeCount {V : Type*} [Fintype V]
    (J : RegularityColoredGraph V) (c : EdgeColor) : ℕ :=
  Nat.card (J.edgeColor.labelGraph c).edgeSet

theorem c4ColorEdgeCount_le_complete {n : ℕ}
    (J : RegularityColoredGraph (Fin n)) (c : EdgeColor) :
    c4ColorEdgeCount J c ≤ completeEdgeCount n := by
  letI : Fintype (J.edgeColor.labelGraph c).edgeSet := Fintype.ofFinite _
  rw [c4ColorEdgeCount, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  simpa [completeEdgeCount] using
    (J.edgeColor.labelGraph c).card_edgeFinset_le_card_choose_two

/-- Feasibility is required for partial as well as complete inputs. -/
def C4ColoredEntropyFeasible {n : ℕ}
    (J : RegularityColoredGraph (Fin n)) (gamma : ℝ) : Prop :=
  DenseGraph.EntropySliceFeasible (c4ColorEdgeCount J .red)
    (c4ColorEdgeCount J .blue) (gamma * completeEdgeCount n)

def c4ColoredEntropy {n : ℕ} (J : RegularityColoredGraph (Fin n))
    (gamma : ℝ) (h : C4ColoredEntropyFeasible J gamma) : ℝ := h.value

theorem c4ColoredEntropy_eq {n : ℕ} (J : RegularityColoredGraph (Fin n))
    (gamma : ℝ) (h : C4ColoredEntropyFeasible J gamma) :
    c4ColoredEntropy J gamma h = (c4ColorEdgeCount J .red : ℝ) *
      binaryEntropy ((gamma * completeEdgeCount n - c4ColorEdgeCount J .blue) /
        c4ColorEdgeCount J .red) := h.value_eq

theorem c4ColoredEntropy_zero_red {n : ℕ} (J : RegularityColoredGraph (Fin n))
    (gamma : ℝ) (h : C4ColoredEntropyFeasible J gamma)
    (hred : c4ColorEdgeCount J .red = 0) :
    gamma * completeEdgeCount n = c4ColorEdgeCount J .blue ∧
      c4ColoredEntropy J gamma h = 0 := by
  have hr : (c4ColorEdgeCount J .red : ℝ) = 0 := by exact_mod_cast hred
  exact ⟨h.target_eq_of_capacity_zero hr, by rw [c4ColoredEntropy_eq, hr, zero_mul]⟩

/-- Only complete C4-excluding templates index the benchmark.
Their red/blue count pairs give a finite optimization domain. -/
def c4CompleteBenchmarkPairs (n : ℕ) (gamma : ℝ) : Finset (ℕ × ℕ) :=
  ((range (completeEdgeCount n + 1)).product (range (completeEdgeCount n + 1))).filter
    fun rb ↦ ∃ J : RegularityColoredGraph (Fin n), J.graph = ⊤ ∧
      ¬RegularityColoredGraph.ColoredHomExists inducedC4 J ∧
      c4ColorEdgeCount J .red = rb.1 ∧ c4ColorEdgeCount J .blue = rb.2 ∧
      DenseGraph.EntropySliceFeasible rb.1 rb.2 (gamma * completeEdgeCount n)

def c4CountPairEntropy (n : ℕ) (gamma : ℝ) (rb : ℕ × ℕ) : ℝ :=
  (rb.1 : ℝ) * binaryEntropy ((gamma * completeEdgeCount n - rb.2) / rb.1)

/-- Complete-template maximum. Empty feasible classes have value
zero by convention; every attainment theorem assumes nonemptiness. -/
def c4CompleteEntropyBenchmark (n : ℕ) (gamma : ℝ) : ℝ :=
  if h : (c4CompleteBenchmarkPairs n gamma).Nonempty then
    (c4CompleteBenchmarkPairs n gamma).sup' h (c4CountPairEntropy n gamma)
  else 0

theorem c4CountPairEntropy_feasible {n : ℕ} {gamma : ℝ} {rb : ℕ × ℕ}
    (h : rb ∈ c4CompleteBenchmarkPairs n gamma) :
    ∃ hf : DenseGraph.EntropySliceFeasible rb.1 rb.2 (gamma * completeEdgeCount n),
      c4CountPairEntropy n gamma rb = hf.value := by
  obtain ⟨J, _, _, _, _, hf⟩ := (mem_filter.mp h).2
  exact ⟨hf, hf.value_eq.symm⟩

theorem c4CompleteBenchmarkPairs_mem {n : ℕ} {gamma : ℝ}
    (J : RegularityColoredGraph (Fin n)) (hc : J.graph = ⊤)
    (hfree : ¬RegularityColoredGraph.ColoredHomExists inducedC4 J)
    (h : C4ColoredEntropyFeasible J gamma) :
    (c4ColorEdgeCount J .red, c4ColorEdgeCount J .blue) ∈
      c4CompleteBenchmarkPairs n gamma := by
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_range.mpr ?_, mem_range.mpr ?_⟩,
    J, hc, hfree, rfl, rfl, h⟩
  · exact Nat.lt_succ_of_le (c4ColorEdgeCount_le_complete J .red)
  · exact Nat.lt_succ_of_le (c4ColorEdgeCount_le_complete J .blue)

theorem c4ColoredEntropy_le_completeBenchmark {n : ℕ} {gamma : ℝ}
    (J : RegularityColoredGraph (Fin n)) (hc : J.graph = ⊤)
    (hfree : ¬RegularityColoredGraph.ColoredHomExists inducedC4 J)
    (h : C4ColoredEntropyFeasible J gamma) :
    c4ColoredEntropy J gamma h ≤ c4CompleteEntropyBenchmark n gamma := by
  have hm := c4CompleteBenchmarkPairs_mem J hc hfree h
  rw [c4CompleteEntropyBenchmark, dif_pos ⟨_, hm⟩, c4ColoredEntropy_eq]
  exact Finset.le_sup' (c4CountPairEntropy n gamma) hm

/-- Attainment retains an actual complete template and feasibility. -/
theorem exists_completeTemplate_at_c4Benchmark {n : ℕ} {gamma : ℝ}
    (hS : (c4CompleteBenchmarkPairs n gamma).Nonempty) :
    ∃ J : RegularityColoredGraph (Fin n), J.graph = ⊤ ∧
      ¬RegularityColoredGraph.ColoredHomExists inducedC4 J ∧
      ∃ h : C4ColoredEntropyFeasible J gamma,
        c4ColoredEntropy J gamma h = c4CompleteEntropyBenchmark n gamma := by
  obtain ⟨rb, hrb, hmax⟩ := Finset.exists_mem_eq_sup' hS (c4CountPairEntropy n gamma)
  obtain ⟨J, hc, hfree, hR, hB, hf⟩ := (mem_filter.mp hrb).2
  have h : C4ColoredEntropyFeasible J gamma := by
    unfold C4ColoredEntropyFeasible
    simpa only [hR, hB] using hf
  refine ⟨J, hc, hfree, h, ?_⟩
  rw [c4ColoredEntropy_eq, c4CompleteEntropyBenchmark, dif_pos hS, hmax]
  simp only [c4CountPairEntropy, hR, hB]

theorem c4CompleteEntropyBenchmark_nonneg (n : ℕ) (gamma : ℝ) :
    0 ≤ c4CompleteEntropyBenchmark n gamma := by
  by_cases hS : (c4CompleteBenchmarkPairs n gamma).Nonempty
  · obtain ⟨J, _, _, h, heq⟩ := exists_completeTemplate_at_c4Benchmark hS
    rw [← heq]
    exact h.value_nonneg
  · simp [c4CompleteEntropyBenchmark, hS]

theorem c4CompleteEntropyBenchmark_le_complete (n : ℕ) (gamma : ℝ) :
    c4CompleteEntropyBenchmark n gamma ≤ completeEdgeCount n := by
  by_cases hS : (c4CompleteBenchmarkPairs n gamma).Nonempty
  · obtain ⟨J, _, _, h, heq⟩ := exists_completeTemplate_at_c4Benchmark hS
    rw [← heq]
    exact h.value_le_capacity.trans (by exact_mod_cast c4ColorEdgeCount_le_complete J .red)
  · simp [c4CompleteEntropyBenchmark, hS]

end InducedStars
