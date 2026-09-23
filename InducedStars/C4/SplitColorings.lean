import InducedStars.C4.ColoredEntropy
import InducedStars.C4.SplitFibers

/-!
# Complete split colorings

Paper: the split templates preceding Lemma `lemma:c4-stability`.
These are complete templates, so they are admissible for the entropy
benchmark in `eqn:coloring-entropy-0`. The exclusion proof retains the noninjective colored-map semantics.
-/

noncomputable section
open Finset InducedStars.Regularity InducedStars.Regularity.RegularityColoredGraph
open scoped Classical
namespace InducedStars

variable {V : Type*} [Fintype V] [DecidableEq V]

def c4SplitColoring (D : C4Division V) : RegularityColoredGraph V where
  graph := ⊤
  vertexColor v := if v ∈ D.independentPart then .green else .blue
  edgeColor := SimpleGraph.EdgeLabeling.mk
    (fun x y _ ↦ if x ∈ D.independentPart ∧ y ∈ D.independentPart then .green
      else if x ∉ D.independentPart ∧ y ∉ D.independentPart then .blue else .red)
    (by intros; simp only [and_comm])

@[simp] theorem c4SplitColoring_complete (D : C4Division V) :
    (c4SplitColoring D).graph = ⊤ := rfl

@[simp] theorem c4SplitColoring_vertexColor (D : C4Division V) (v : V) :
    (c4SplitColoring D).vertexColor v =
      if v ∈ D.independentPart then .green else .blue := rfl

@[simp] theorem c4SplitColoring_edgeColor (D : C4Division V) (x y : V)
    (h : (c4SplitColoring D).graph.Adj x y) :
    (c4SplitColoring D).getEdgeColor x y h =
      if x ∈ D.independentPart ∧ y ∈ D.independentPart then .green
      else if x ∉ D.independentPart ∧ y ∉ D.independentPart then .blue else .red := rfl

/-- Pulling back a split coloring along a colored homomorphism gives an
actual independent/clique partition of its source, even if the map collapses
vertices. -/
theorem c4SplitColoring_source_isSplit {W : Type*} [Fintype W] [DecidableEq W]
    (D : C4Division V) {H : SimpleGraph W} {f : W → V}
    (hf : IsColoredHom H (c4SplitColoring D) f) : DenseGraph.IsSplitGraph H := by
  let A : Finset W := univ.filter fun w ↦ f w ∈ D.independentPart
  refine ⟨⟨A, univ \ A, disjoint_sdiff_self_right, ?_, ?_, ?_⟩⟩
  · exact union_sdiff_of_subset (subset_univ A)
  · intro x hx y hy hne hxy
    have hx' : f x ∈ D.independentPart := (mem_filter.mp hx).2
    have hy' : f y ∈ D.independentPart := (mem_filter.mp hy).2
    rcases hf.map_edge hxy with ⟨_, hc⟩ | ⟨he, hc⟩
    · simpa [hx'] using hc
    · simpa [hx', hy'] using hc
  · intro x hx y hy hne
    have hx' : f x ∉ D.independentPart := by simpa [A] using (mem_sdiff.mp hx).2
    have hy' : f y ∉ D.independentPart := by simpa [A] using (mem_sdiff.mp hy).2
    by_contra hxy
    rcases hf.map_nonedge hne hxy with ⟨_, hc⟩ | ⟨he, hc⟩
    · simpa [hx'] using hc
    · simpa [hx', hy'] using hc

theorem c4SplitColoring_no_coloredHom (D : C4Division V) :
    ¬ColoredHomExists inducedC4 (c4SplitColoring D) := by
  rintro ⟨f, hf⟩
  exact (c4SplitColoring_source_isSplit D hf).no_induced_cycleFour
    ⟨RelEmbedding.refl _⟩

theorem c4ColorEdgeCount_eq_card (J : RegularityColoredGraph V) (c : EdgeColor) :
    c4ColorEdgeCount J c = (finiteGraphEdges (J.edgeColor.labelGraph c)).card := by
  letI : Fintype (J.edgeColor.labelGraph c).edgeSet := Fintype.ofFinite _
  rw [c4ColorEdgeCount, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  rfl

@[simp] theorem c4SplitColoring_labelGraph_adj (D : C4Division V)
    (c : EdgeColor) (x y : V) :
    ((c4SplitColoring D).edgeColor.labelGraph c).Adj x y ↔
      x ≠ y ∧ (if x ∈ D.independentPart ∧ y ∈ D.independentPart then .green
        else if x ∉ D.independentPart ∧ y ∉ D.independentPart then .blue else .red) = c := by
  rw [SimpleGraph.EdgeLabeling.labelGraph_adj]
  constructor
  · rintro ⟨h, hc⟩
    exact ⟨h.ne, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨h, hc⟩

theorem c4SplitColoring_blue_edges (D : C4Division V) :
    finiteGraphEdges ((c4SplitColoring D).edgeColor.labelGraph .blue) = c4CliqueEdges D := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    simp only [mk_mem_finiteGraphEdges, c4SplitColoring_labelGraph_adj,
      mk_mem_c4CliqueEdges, C4Division.mem_cliquePart]
    by_cases hx : x ∈ D.independentPart <;> by_cases hy : y ∈ D.independentPart <;>
      simp [hx, hy]

theorem c4SplitColoring_red_edges (D : C4Division V) :
    finiteGraphEdges ((c4SplitColoring D).edgeColor.labelGraph .red) =
      c4CrossPotentialEdges D := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    simp only [mk_mem_finiteGraphEdges, c4SplitColoring_labelGraph_adj,
      mk_mem_c4CrossPotentialEdges, C4Division.mem_cliquePart]
    by_cases heq : x = y
    · subst y; simp
    · by_cases hx : x ∈ D.independentPart <;> by_cases hy : y ∈ D.independentPart <;>
        simp [hx, hy, heq]

@[simp] theorem c4SplitColoring_blue_count (D : C4Division V) :
    c4ColorEdgeCount (c4SplitColoring D) .blue = Nat.choose D.cliquePart.card 2 := by
  rw [c4ColorEdgeCount_eq_card, c4SplitColoring_blue_edges, card_c4CliqueEdges]

@[simp] theorem c4SplitColoring_red_count (D : C4Division V) :
    c4ColorEdgeCount (c4SplitColoring D) .red =
      D.independentPart.card * D.cliquePart.card := by
  rw [c4ColorEdgeCount_eq_card, c4SplitColoring_red_edges, card_c4CrossPotentialEdges]

/-- Every feasible split template supplies a genuine complete-benchmark
competitor, not a completion of a partial template. -/
theorem c4SplitColoring_entropy_le_benchmark {n : ℕ} (D : C4Division (Fin n))
    (gamma : ℝ) (h : C4ColoredEntropyFeasible (c4SplitColoring D) gamma) :
    ((D.independentPart.card * D.cliquePart.card : ℕ) : ℝ) *
      binaryEntropy ((gamma * completeEdgeCount n - Nat.choose D.cliquePart.card 2) /
        (D.independentPart.card * D.cliquePart.card)) ≤ c4CompleteEntropyBenchmark n gamma := by
  simpa [c4ColoredEntropy_eq] using c4ColoredEntropy_le_completeBenchmark
    (c4SplitColoring D) rfl (c4SplitColoring_no_coloredHom D) h

/-- The canonical split division with the first `b` labels in the clique.
Values above `n` are harmlessly truncated; all size theorems state `b ≤ n`. -/
def c4DivisionOfCliqueSize (n b : ℕ) : C4Division (Fin n) :=
  univ \ (univ.filter fun v : Fin n ↦ v.val < b)

@[simp] theorem c4DivisionOfCliqueSize_clique (n b : ℕ) :
    (c4DivisionOfCliqueSize n b).cliquePart = univ.filter fun v : Fin n ↦ v.val < b := by
  ext v
  simp [c4DivisionOfCliqueSize, C4Division.cliquePart]

@[simp] theorem c4DivisionOfCliqueSize_clique_card {n b : ℕ} (hb : b ≤ n) :
    (c4DivisionOfCliqueSize n b).cliquePart.card = b := by
  rw [c4DivisionOfCliqueSize_clique, Fin.card_filter_val_lt, min_eq_right hb]

@[simp] theorem c4DivisionOfCliqueSize_independent_card {n b : ℕ} (hb : b ≤ n) :
    (c4DivisionOfCliqueSize n b).independentPart.card = n - b := by
  have h := (c4DivisionOfCliqueSize n b).card_add
  rw [c4DivisionOfCliqueSize_clique_card hb, Fintype.card_fin] at h
  omega

end InducedStars
