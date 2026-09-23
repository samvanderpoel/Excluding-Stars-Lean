import InducedStars.FinitePartition
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Real.Basic

/-!
# Three-colored complete graphs

This file provides the finite red--green--blue edge-coloring API used by the
paper. A coloring is a Mathlib `SimpleGraph.TopEdgeLabeling`, so its labels
live on unordered, loop-free edges of the complete graph. The total accessor
`ColoredGraph.color` assigns blue to the diagonal; this convention is only a
convenience for formulas on pairs of vertices and does not add loops.
-/

open Finset

namespace InducedStars

/-- The three edge colors used throughout the paper. -/
inductive EdgeColor where
  | red
  | green
  | blue
  deriving DecidableEq, Repr

instance : Inhabited EdgeColor := ⟨.red⟩

instance : Fintype EdgeColor where
  elems := {.red, .green, .blue}
  complete c := by cases c <;> simp

/-- A red--green--blue labeling of every unordered edge of the complete graph on `V`. -/
abbrev ColoredGraph (V : Type*) := SimpleGraph.TopEdgeLabeling V EdgeColor

namespace ColoredGraph

variable {V W : Type*}
variable [DecidableEq V]

/-- The color of a pair of vertices. Diagonal pairs are assigned blue by convention. -/
def color (C : ColoredGraph V) (x y : V) : EdgeColor :=
  if h : x = y then .blue else C.get x y (by simpa using h)

@[simp]
theorem color_self (C : ColoredGraph V) (x : V) : C.color x x = .blue := by
  simp [color]

/-- Away from the diagonal, `color` is the underlying edge label. -/
@[simp]
theorem color_eq_get (C : ColoredGraph V) {x y : V} (h : x ≠ y) :
    C.color x y = C.get x y (by simpa using h) := by
  simp [color, h]

/-- The total color accessor is symmetric. -/
theorem color_comm (C : ColoredGraph V) (x y : V) : C.color x y = C.color y x := by
  by_cases h : x = y
  · subst y
    rfl
  · have h' : y ≠ x := Ne.symm h
    rw [C.color_eq_get h, C.color_eq_get h']
    exact SimpleGraph.EdgeLabeling.get_comm y x _

/-- Two complete-graph colorings are equal when their total color accessors agree. -/
@[ext]
theorem ext {C C' : ColoredGraph V} (h : ∀ x y, C.color x y = C'.color x y) : C = C' := by
  apply SimpleGraph.EdgeLabeling.ext_get
  intro x y hxy
  have hne : x ≠ y := by simpa using hxy
  simpa only [color_eq_get C hne, color_eq_get C' hne] using h x y

/-- The simple graph formed by the edges of color `c`. -/
abbrev colorGraph (C : ColoredGraph V) (c : EdgeColor) : SimpleGraph V :=
  C.labelGraph c

/-- Adjacency in a color graph is exactly having that color off the diagonal. -/
@[simp]
theorem colorGraph_adj (C : ColoredGraph V) (c : EdgeColor) (x y : V) :
    (C.colorGraph c).Adj x y ↔ x ≠ y ∧ C.color x y = c := by
  rw [SimpleGraph.TopEdgeLabeling.labelGraph_adj]
  constructor
  · rintro ⟨hne, hcolor⟩
    exact ⟨hne, by simpa only [C.color_eq_get hne] using hcolor⟩
  · rintro ⟨hne, hcolor⟩
    exact ⟨hne, by simpa only [C.color_eq_get hne] using hcolor⟩

/-- The graph of red edges. -/
abbrev redGraph (C : ColoredGraph V) : SimpleGraph V := C.colorGraph .red

/-- The graph of green edges. -/
abbrev greenGraph (C : ColoredGraph V) : SimpleGraph V := C.colorGraph .green

/-- The graph of blue edges. -/
abbrev blueGraph (C : ColoredGraph V) : SimpleGraph V := C.colorGraph .blue

section Finite

variable [Fintype V]

/-- The vertices joined to `v` by an edge of color `c`. -/
def neighborFinset (C : ColoredGraph V) (c : EdgeColor) (v : V) : Finset V :=
  (C.colorGraph c).neighborFinset v

@[simp]
theorem mem_neighborFinset (C : ColoredGraph V) (c : EdgeColor) (v w : V) :
    w ∈ C.neighborFinset c v ↔ v ≠ w ∧ C.color v w = c := by
  rw [neighborFinset, SimpleGraph.mem_neighborFinset]
  exact C.colorGraph_adj c v w

/-- The color-`c` neighbors of `v` that lie in `U`. -/
def neighborFinsetIn (C : ColoredGraph V) (c : EdgeColor) (v : V) (U : Finset V) : Finset V :=
  C.neighborFinset c v ∩ U

@[simp]
theorem mem_neighborFinsetIn (C : ColoredGraph V) (c : EdgeColor) (v w : V)
    (U : Finset V) :
    w ∈ C.neighborFinsetIn c v U ↔
      v ≠ w ∧ C.color v w = c ∧ w ∈ U := by
  simp [neighborFinsetIn, and_assoc]

/-- The number of color-`c` neighbors of `v`. -/
def degree (C : ColoredGraph V) (c : EdgeColor) (v : V) : ℕ :=
  #(C.neighborFinset c v)

/-- The number of color-`c` neighbors of `v` lying in `U`. -/
def degreeIn (C : ColoredGraph V) (c : EdgeColor) (v : V) (U : Finset V) : ℕ :=
  #(C.neighborFinsetIn c v U)

/-- The unordered edges of color `c`. -/
def edgeFinset (C : ColoredGraph V) (c : EdgeColor) : Finset (Sym2 V) :=
  (C.colorGraph c).edgeFinset

@[simp]
theorem pair_mem_edgeFinset (C : ColoredGraph V) (c : EdgeColor) (x y : V) :
    s(x, y) ∈ C.edgeFinset c ↔ x ≠ y ∧ C.color x y = c := by
  simpa only [edgeFinset, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
    C.colorGraph_adj c x y

/-- The unordered edges of color `c` whose two endpoints lie in `U`. -/
def edgeFinsetIn (C : ColoredGraph V) (c : EdgeColor) (U : Finset V) : Finset (Sym2 V) :=
  C.edgeFinset c ∩ U.sym2

@[simp]
theorem pair_mem_edgeFinsetIn (C : ColoredGraph V) (c : EdgeColor) (U : Finset V) (x y : V) :
    s(x, y) ∈ C.edgeFinsetIn c U ↔
      x ≠ y ∧ C.color x y = c ∧ x ∈ U ∧ y ∈ U := by
  simp [edgeFinsetIn, and_assoc]

/-- The number of unordered edges of color `c`. -/
def edgeCount (C : ColoredGraph V) (c : EdgeColor) : ℕ :=
  #(C.edgeFinset c)

/-- The number of unordered edges of color `c` with both endpoints in `U`. -/
def edgeCountIn (C : ColoredGraph V) (c : EdgeColor) (U : Finset V) : ℕ :=
  #(C.edgeFinsetIn c U)

/-! Counts and densities between two vertex sets. -/

/-- Number of color-`c` edges from `S` to `T`, with one orientation fixed.
For disjoint sets this is the paper's between-set edge count. -/
def colorEdgeCountBetween (C : ColoredGraph V) (c : EdgeColor)
    (S T : Finset V) : ℕ :=
  #((C.colorGraph c).interedges S T)

/-- Real-valued color density between two vertex sets. -/
noncomputable def colorDensity (C : ColoredGraph V) (c : EdgeColor)
    (S T : Finset V) : ℝ :=
  (C.colorEdgeCountBetween c S T : ℝ) /
    ((S.card : ℝ) * (T.card : ℝ))

/-- The proportion of a set joined to `v` in color `c`. -/
noncomputable def colorDegreeRatio (C : ColoredGraph V) (c : EdgeColor)
    (v : V) (S : Finset V) : ℝ :=
  (C.degreeIn c v S : ℝ) / (S.card : ℝ)

/-- Double counting color incidences between two finite sets. -/
theorem sum_degreeIn_eq_colorEdgeCountBetween (C : ColoredGraph V)
    (c : EdgeColor) (S T : Finset V) :
    ∑ v ∈ S, C.degreeIn c v T = C.colorEdgeCountBetween c S T := by
  classical
  rw [colorEdgeCountBetween, SimpleGraph.interedges_def,
    Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro v hv
  unfold degreeIn neighborFinsetIn neighborFinset
  rw [SimpleGraph.neighborFinset_eq_filter]
  have hinter :
      {w ∈ (Finset.univ : Finset V) | (C.colorGraph c).Adj v w} ∩ T =
        {w ∈ T | (C.colorGraph c).Adj v w} := by
    ext w
    simp [and_comm]
  rw [hinter, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Color counts between two sets are symmetric. -/
theorem colorEdgeCountBetween_comm (C : ColoredGraph V) (c : EdgeColor)
    (S T : Finset V) :
    C.colorEdgeCountBetween c S T = C.colorEdgeCountBetween c T S := by
  have := (C.colorGraph c).symm
  exact Rel.card_interedges_comm (r := (C.colorGraph c).Adj) S T

/-- Between-set color counts are monotone in both vertex sets. -/
theorem colorEdgeCountBetween_mono (C : ColoredGraph V) (c : EdgeColor)
    {S S' T T' : Finset V} (hS : S ⊆ S') (hT : T ⊆ T') :
    C.colorEdgeCountBetween c S T ≤ C.colorEdgeCountBetween c S' T' := by
  unfold colorEdgeCountBetween
  exact Finset.card_le_card ((C.colorGraph c).interedges_mono hS hT)

/-- Color densities between two sets are symmetric. -/
theorem colorDensity_comm (C : ColoredGraph V) (c : EdgeColor)
    (S T : Finset V) :
    C.colorDensity c S T = C.colorDensity c T S := by
  unfold colorDensity
  rw [C.colorEdgeCountBetween_comm c S T, mul_comm]

/-- Restricted degree splits over a subset and its relative complement. -/
theorem degreeIn_add_degreeIn_sdiff (C : ColoredGraph V) (c : EdgeColor)
    (v : V) {S T : Finset V} (hST : S ⊆ T) :
    C.degreeIn c v S + C.degreeIn c v (T \ S) = C.degreeIn c v T := by
  unfold degreeIn neighborFinsetIn
  let N := C.neighborFinset c v
  have hdisj : Disjoint (N ∩ S) (N ∩ (T \ S)) :=
    Finset.disjoint_sdiff.mono Finset.inter_subset_right Finset.inter_subset_right
  rw [← Finset.card_union_of_disjoint hdisj,
    ← Finset.inter_union_distrib_left, Finset.union_sdiff_of_subset hST]

/-- Restricted degree is additive over two disjoint vertex sets. -/
theorem degreeIn_union_of_disjoint (C : ColoredGraph V) (c : EdgeColor)
    (v : V) {S T : Finset V} (hST : Disjoint S T) :
    C.degreeIn c v (S ∪ T) = C.degreeIn c v S + C.degreeIn c v T := by
  unfold degreeIn neighborFinsetIn
  rw [Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint
      (hST.mono Finset.inter_subset_right Finset.inter_subset_right)]

/-- Restricted degree is additive over a pairwise-disjoint finite union. -/
theorem degreeIn_biUnion {I : Type*} (C : ColoredGraph V) (c : EdgeColor) (v : V)
    (indices : Finset I) (sets : I → Finset V)
    (hsets : (indices : Set I).PairwiseDisjoint sets) :
    C.degreeIn c v (indices.biUnion sets) =
      ∑ i ∈ indices, C.degreeIn c v (sets i) := by
  unfold degreeIn neighborFinsetIn
  rw [Finset.inter_biUnion, Finset.card_biUnion]
  exact hsets.mono_on fun _ hi ↦ Finset.inter_subset_right

/-- Away from the diagonal, every vertex in a set has exactly one of the
three colors from `v`. -/
theorem redDegreeIn_add_greenDegreeIn_add_blueDegreeIn_of_not_mem
    (C : ColoredGraph V) (v : V) (T : Finset V) (hv : v ∉ T) :
    C.degreeIn .red v T + C.degreeIn .green v T + C.degreeIn .blue v T = T.card := by
  have hfilter (c : EdgeColor) :
      C.neighborFinsetIn c v T = {w ∈ T | C.color v w = c} := by
    ext w
    rw [C.mem_neighborFinsetIn, Finset.mem_filter]
    constructor
    · rintro ⟨_, hc, hw⟩
      exact ⟨hw, hc⟩
    · rintro ⟨hw, hc⟩
      exact ⟨fun hvw ↦ hv (hvw ▸ hw), hc, hw⟩
  unfold degreeIn
  rw [hfilter .red, hfilter .green, hfilter .blue]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  cases C.color v w <;> simp

/-- Between disjoint sets, the three color counts partition all pairs. -/
theorem red_add_green_add_blue_colorEdgeCountBetween (C : ColoredGraph V)
    {S T : Finset V} (hST : Disjoint S T) :
    C.colorEdgeCountBetween .red S T +
        C.colorEdgeCountBetween .green S T +
        C.colorEdgeCountBetween .blue S T = S.card * T.card := by
  rw [← C.sum_degreeIn_eq_colorEdgeCountBetween .red S T,
    ← C.sum_degreeIn_eq_colorEdgeCountBetween .green S T,
    ← C.sum_degreeIn_eq_colorEdgeCountBetween .blue S T,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    ∑ v ∈ S,
        (C.degreeIn .red v T + C.degreeIn .green v T + C.degreeIn .blue v T) =
        ∑ _v ∈ S, T.card := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [C.redDegreeIn_add_greenDegreeIn_add_blueDegreeIn_of_not_mem]
          exact fun hvT ↦ Finset.disjoint_left.mp hST hv hvT
    _ = S.card * T.card := by simp

/-- Between nonempty disjoint sets, the three real color densities sum to one. -/
theorem red_add_green_add_blue_colorDensity (C : ColoredGraph V)
    {S T : Finset V} (hS : S.Nonempty) (hT : T.Nonempty)
    (hST : Disjoint S T) :
    C.colorDensity .red S T + C.colorDensity .green S T +
        C.colorDensity .blue S T = 1 := by
  have hcount := C.red_add_green_add_blue_colorEdgeCountBetween hST
  have hcountR :
      (C.colorEdgeCountBetween .red S T : ℝ) +
          (C.colorEdgeCountBetween .green S T : ℝ) +
          (C.colorEdgeCountBetween .blue S T : ℝ) =
        (S.card : ℝ) * (T.card : ℝ) := by
    exact_mod_cast hcount
  have hden : (S.card : ℝ) * (T.card : ℝ) ≠ 0 := by
    positivity
  unfold colorDensity
  calc
    (C.colorEdgeCountBetween .red S T : ℝ) /
          ((S.card : ℝ) * (T.card : ℝ)) +
        (C.colorEdgeCountBetween .green S T : ℝ) /
          ((S.card : ℝ) * (T.card : ℝ)) +
        (C.colorEdgeCountBetween .blue S T : ℝ) /
          ((S.card : ℝ) * (T.card : ℝ)) =
        ((C.colorEdgeCountBetween .red S T : ℝ) +
            (C.colorEdgeCountBetween .green S T : ℝ) +
            (C.colorEdgeCountBetween .blue S T : ℝ)) /
          ((S.card : ℝ) * (T.card : ℝ)) := by ring
    _ = 1 := by rw [hcountR, div_self hden]

/-- The degree sum for one color counts every unordered edge twice. -/
theorem sum_degree_eq_two_mul_edgeCount (C : ColoredGraph V) (c : EdgeColor) :
    ∑ v, C.degree c v = 2 * C.edgeCount c := by
  simpa only [degree, neighborFinset, edgeCount, edgeFinset,
    SimpleGraph.card_neighborFinset_eq_degree] using
      (C.colorGraph c).sum_degrees_eq_twice_card_edges

/-- The restricted degree sum counts every color-`c` edge internal to `S`
twice. -/
theorem sum_degreeIn_eq_two_mul_edgeCountIn (C : ColoredGraph V)
    (c : EdgeColor) (S : Finset V) :
    ∑ v ∈ S, C.degreeIn c v S = 2 * C.edgeCountIn c S := by
  classical
  let H : SimpleGraph V := {
    Adj x y := (C.colorGraph c).Adj x y ∧ x ∈ S ∧ y ∈ S
    symm.symm x y h := ⟨h.1.symm, h.2.2, h.2.1⟩
    loopless.irrefl _ h := (C.colorGraph c).irrefl h.1 }
  have hedge : H.edgeFinset = C.edgeFinset c ∩ S.sym2 := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y => simp [H, edgeFinset, edgeFinsetIn]
  have hinter :
      (Finset.univ.filter fun xy : V × V ↦ H.Adj xy.1 xy.2) =
        (C.colorGraph c).interedges S S := by
    ext xy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.mem_interedges_iff]
    change ((C.colorGraph c).Adj xy.1 xy.2 ∧ xy.1 ∈ S ∧ xy.2 ∈ S) ↔
      (xy.1 ∈ S ∧ xy.2 ∈ S ∧ (C.colorGraph c).Adj xy.1 xy.2)
    tauto
  rw [C.sum_degreeIn_eq_colorEdgeCountBetween c S S]
  unfold colorEdgeCountBetween edgeCountIn edgeFinsetIn
  rw [← hinter]
  calc
    #(Finset.univ.filter fun xy : V × V ↦ H.Adj xy.1 xy.2) =
        2 * #H.edgeFinset := by
      simpa using H.two_mul_card_edgeFinset.symm
    _ = 2 * #(C.edgeFinset c ∩ S.sym2) := by rw [hedge]

/-- Internal edges of a disjoint union split into the internal edges of the
two sets and the edges crossing between them. -/
theorem edgeCountIn_union_of_disjoint (C : ColoredGraph V) (c : EdgeColor)
    {S T : Finset V} (hST : Disjoint S T) :
    C.edgeCountIn c (S ∪ T) =
      C.edgeCountIn c S + C.colorEdgeCountBetween c S T +
        C.edgeCountIn c T := by
  classical
  have hsum :
      ∑ v ∈ S ∪ T, C.degreeIn c v (S ∪ T) =
        ((∑ v ∈ S, C.degreeIn c v S) +
          ∑ v ∈ S, C.degreeIn c v T) +
        ((∑ v ∈ T, C.degreeIn c v S) +
          ∑ v ∈ T, C.degreeIn c v T) := by
    rw [Finset.sum_union hST]
    simp_rw [C.degreeIn_union_of_disjoint c _ hST]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hU := C.sum_degreeIn_eq_two_mul_edgeCountIn c (S ∪ T)
  have hS := C.sum_degreeIn_eq_two_mul_edgeCountIn c S
  have hT := C.sum_degreeIn_eq_two_mul_edgeCountIn c T
  have hSTcount := C.sum_degreeIn_eq_colorEdgeCountBetween c S T
  have hTScount := C.sum_degreeIn_eq_colorEdgeCountBetween c T S
  rw [hsum, hS, hT, hSTcount, hTScount,
    C.colorEdgeCountBetween_comm c T S] at hU
  omega

/-! Color-specific conveniences matching the paper. -/

abbrev redNeighborFinset (C : ColoredGraph V) (v : V) : Finset V := C.neighborFinset .red v
abbrev greenNeighborFinset (C : ColoredGraph V) (v : V) : Finset V := C.neighborFinset .green v
abbrev blueNeighborFinset (C : ColoredGraph V) (v : V) : Finset V := C.neighborFinset .blue v

abbrev redNeighborFinsetIn (C : ColoredGraph V) (v : V) (U : Finset V) : Finset V :=
  C.neighborFinsetIn .red v U
abbrev greenNeighborFinsetIn (C : ColoredGraph V) (v : V) (U : Finset V) : Finset V :=
  C.neighborFinsetIn .green v U
abbrev blueNeighborFinsetIn (C : ColoredGraph V) (v : V) (U : Finset V) : Finset V :=
  C.neighborFinsetIn .blue v U

abbrev redDegree (C : ColoredGraph V) (v : V) : ℕ := C.degree .red v
abbrev greenDegree (C : ColoredGraph V) (v : V) : ℕ := C.degree .green v
abbrev blueDegree (C : ColoredGraph V) (v : V) : ℕ := C.degree .blue v

abbrev redDegreeIn (C : ColoredGraph V) (v : V) (U : Finset V) : ℕ := C.degreeIn .red v U
abbrev greenDegreeIn (C : ColoredGraph V) (v : V) (U : Finset V) : ℕ :=
  C.degreeIn .green v U
abbrev blueDegreeIn (C : ColoredGraph V) (v : V) (U : Finset V) : ℕ := C.degreeIn .blue v U

abbrev redEdgeFinset (C : ColoredGraph V) : Finset (Sym2 V) := C.edgeFinset .red
abbrev greenEdgeFinset (C : ColoredGraph V) : Finset (Sym2 V) := C.edgeFinset .green
abbrev blueEdgeFinset (C : ColoredGraph V) : Finset (Sym2 V) := C.edgeFinset .blue

abbrev redEdgeFinsetIn (C : ColoredGraph V) (U : Finset V) : Finset (Sym2 V) :=
  C.edgeFinsetIn .red U
abbrev greenEdgeFinsetIn (C : ColoredGraph V) (U : Finset V) : Finset (Sym2 V) :=
  C.edgeFinsetIn .green U
abbrev blueEdgeFinsetIn (C : ColoredGraph V) (U : Finset V) : Finset (Sym2 V) :=
  C.edgeFinsetIn .blue U

abbrev redEdgeCount (C : ColoredGraph V) : ℕ := C.edgeCount .red
abbrev greenEdgeCount (C : ColoredGraph V) : ℕ := C.edgeCount .green
abbrev blueEdgeCount (C : ColoredGraph V) : ℕ := C.edgeCount .blue

abbrev redEdgeCountIn (C : ColoredGraph V) (U : Finset V) : ℕ := C.edgeCountIn .red U
abbrev greenEdgeCountIn (C : ColoredGraph V) (U : Finset V) : ℕ := C.edgeCountIn .green U
abbrev blueEdgeCountIn (C : ColoredGraph V) (U : Finset V) : ℕ := C.edgeCountIn .blue U

/-- Restricting both endpoints to a vertex set cannot increase an edge
count. -/
theorem edgeCountIn_le_edgeCount (C : ColoredGraph V) (c : EdgeColor)
    (S : Finset V) : C.edgeCountIn c S ≤ C.edgeCount c := by
  exact Finset.card_le_card Finset.inter_subset_left

/-- An edge not wholly contained in `S` can be charged to an endpoint in
`Sᶜ`.  Consequently, the number of color-`c` edges lost by restricting to
`S` is at most `|Sᶜ| |V|`.  The deliberately coarse product form is useful
for cleaning arguments. -/
theorem edgeCount_le_edgeCountIn_add_compl_mul_card
    (C : ColoredGraph V) (c : EdgeColor) (S : Finset V) :
    C.edgeCount c ≤
      C.edgeCountIn c S + (Finset.univ \ S).card * Fintype.card V := by
  classical
  let T : Finset V := Finset.univ \ S
  let outsidePairs : Finset (Sym2 V) :=
    (T ×ˢ (Finset.univ : Finset V)).image (fun xy ↦ s(xy.1, xy.2))
  have hsubset :
      C.edgeFinset c ⊆ C.edgeFinsetIn c S ∪ outsidePairs := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [pair_mem_edgeFinset] at he
        by_cases hx : x ∈ S
        · by_cases hy : y ∈ S
          · apply Finset.mem_union_left
            exact (C.pair_mem_edgeFinsetIn c S x y).2
              ⟨he.1, he.2, hx, hy⟩
          · apply Finset.mem_union_right
            apply Finset.mem_image.mpr
            refine ⟨(y, x), ?_, ?_⟩
            · simp [T, hy]
            · exact Sym2.eq_swap
        · apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          refine ⟨(x, y), ?_, rfl⟩
          simp [T, hx]
  calc
    C.edgeCount c = #(C.edgeFinset c) := rfl
    _ ≤ #(C.edgeFinsetIn c S ∪ outsidePairs) :=
      Finset.card_le_card hsubset
    _ ≤ #(C.edgeFinsetIn c S) + #outsidePairs :=
      Finset.card_union_le _ _
    _ ≤ #(C.edgeFinsetIn c S) + #(T ×ˢ (Finset.univ : Finset V)) := by
      exact Nat.add_le_add_left (Finset.card_image_le) _
    _ = C.edgeCountIn c S + (Finset.univ \ S).card * Fintype.card V := by
      simp [edgeCountIn, T]

end Finite

/-- The constant edge labeling with color `c`. -/
def monochromatic (c : EdgeColor) : ColoredGraph V := fun _ ↦ c

omit [DecidableEq V] in
@[simp]
theorem monochromatic_apply (c : EdgeColor) (e) : (monochromatic (V := V) c) e = c := rfl

omit [DecidableEq V] in
@[simp]
theorem monochromatic_get (c : EdgeColor) (x y : V) (h : (⊤ : SimpleGraph V).Adj x y) :
    (monochromatic c).get x y h = c := rfl

/-- The all-red coloring. -/
abbrev allRed : ColoredGraph V := monochromatic .red

/-- The all-green coloring. -/
abbrev allGreen : ColoredGraph V := monochromatic .green

/-- The all-blue coloring. -/
abbrev allBlue : ColoredGraph V := monochromatic .blue

@[simp]
theorem color_allRed (x y : V) :
    (allRed : ColoredGraph V).color x y =
      if x = y then EdgeColor.blue else EdgeColor.red := by
  simp [color, allRed]

@[simp]
theorem color_allGreen (x y : V) :
    (allGreen : ColoredGraph V).color x y =
      if x = y then EdgeColor.blue else EdgeColor.green := by
  simp [color, allGreen]

@[simp]
theorem color_allBlue (x y : V) : (allBlue : ColoredGraph V).color x y = .blue := by
  simp [color, allBlue]

/-! Recoloring outside a retained vertex set. -/

/-- Keep every color on pairs contained in `S` and recolor every other
off-diagonal pair green.  This is the cleaning operation used in the finite
core-extraction argument. -/
def greenOutside (C : ColoredGraph V) (S : Finset V) : ColoredGraph V :=
  SimpleGraph.EdgeLabeling.mk
    (fun x y _ ↦ if x ∈ S ∧ y ∈ S then C.color x y else .green)
    (by
      intro x y _
      by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
        simp [hx, hy, C.color_comm])

/-- The off-diagonal color formula for `greenOutside`. -/
@[simp]
theorem greenOutside_color_of_ne (C : ColoredGraph V) (S : Finset V)
    {x y : V} (hxy : x ≠ y) :
    (C.greenOutside S).color x y =
      if x ∈ S ∧ y ∈ S then C.color x y else .green := by
  rw [(C.greenOutside S).color_eq_get hxy]
  rfl

/-- Cleaning does not change colors between retained vertices. -/
@[simp]
theorem greenOutside_color_of_mem (C : ColoredGraph V) (S : Finset V)
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    (C.greenOutside S).color x y = C.color x y := by
  by_cases hxy : x = y
  · subst y
    simp
  · simp [C.greenOutside_color_of_ne S hxy, hx, hy]

/-- Every off-diagonal pair not contained in the retained set becomes green. -/
theorem greenOutside_color_of_not_both (C : ColoredGraph V) (S : Finset V)
    {x y : V} (hxy : x ≠ y) (hS : ¬(x ∈ S ∧ y ∈ S)) :
    (C.greenOutside S).color x y = .green := by
  simp [C.greenOutside_color_of_ne S hxy, hS]

section GreenOutsideFinite

variable [Fintype V]

/-- On a subset of the retained set, cleaning preserves the restricted
neighbor finset in every color.  Both the vertex and every possible neighbor
must be retained; unlike the full-degree lemmas below, this also applies to
green. -/
theorem greenOutside_neighborFinsetIn_of_mem_of_subset
    (C : ColoredGraph V) (retained : Finset V) (c : EdgeColor)
    {v : V} {T : Finset V} (hv : v ∈ retained) (hT : T ⊆ retained) :
    (C.greenOutside retained).neighborFinsetIn c v T =
      C.neighborFinsetIn c v T := by
  ext w
  simp only [mem_neighborFinsetIn]
  constructor
  · rintro ⟨hvw, hcolor, hw⟩
    have hwRetained : w ∈ retained := hT hw
    rw [C.greenOutside_color_of_mem retained hv hwRetained] at hcolor
    exact ⟨hvw, hcolor, hw⟩
  · rintro ⟨hvw, hcolor, hw⟩
    have hwRetained : w ∈ retained := hT hw
    rw [C.greenOutside_color_of_mem retained hv hwRetained]
    exact ⟨hvw, hcolor, hw⟩

/-- On a subset of the retained set, cleaning preserves every restricted
color degree. -/
theorem greenOutside_degreeIn_of_mem_of_subset
    (C : ColoredGraph V) (retained : Finset V) (c : EdgeColor)
    {v : V} {T : Finset V} (hv : v ∈ retained) (hT : T ⊆ retained) :
    (C.greenOutside retained).degreeIn c v T = C.degreeIn c v T := by
  unfold degreeIn
  rw [C.greenOutside_neighborFinsetIn_of_mem_of_subset retained c hv hT]

/-- Cleaning preserves the color-`c` edge finset induced by every subset of
the retained set. -/
theorem greenOutside_edgeFinsetIn_of_subset
    (C : ColoredGraph V) (retained : Finset V) (c : EdgeColor)
    {S : Finset V} (hS : S ⊆ retained) :
    (C.greenOutside retained).edgeFinsetIn c S = C.edgeFinsetIn c S := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [pair_mem_edgeFinsetIn]
      constructor
      · rintro ⟨hxy, hcolor, hx, hy⟩
        rw [C.greenOutside_color_of_mem retained (hS hx) (hS hy)] at hcolor
        exact ⟨hxy, hcolor, hx, hy⟩
      · rintro ⟨hxy, hcolor, hx, hy⟩
        rw [C.greenOutside_color_of_mem retained (hS hx) (hS hy)]
        exact ⟨hxy, hcolor, hx, hy⟩

/-- Cleaning preserves the number of color-`c` edges induced by every
subset of the retained set. -/
theorem greenOutside_edgeCountIn_of_subset
    (C : ColoredGraph V) (retained : Finset V) (c : EdgeColor)
    {S : Finset V} (hS : S ⊆ retained) :
    (C.greenOutside retained).edgeCountIn c S = C.edgeCountIn c S := by
  unfold edgeCountIn
  rw [C.greenOutside_edgeFinsetIn_of_subset retained c hS]

/-- Cleaning preserves color counts between two subsets of the retained
set.  No disjointness hypothesis is needed. -/
theorem greenOutside_colorEdgeCountBetween_of_subsets
    (C : ColoredGraph V) (retained : Finset V) (c : EdgeColor)
    {S T : Finset V} (hS : S ⊆ retained) (hT : T ⊆ retained) :
    (C.greenOutside retained).colorEdgeCountBetween c S T =
      C.colorEdgeCountBetween c S T := by
  rw [← (C.greenOutside retained).sum_degreeIn_eq_colorEdgeCountBetween c S T,
    ← C.sum_degreeIn_eq_colorEdgeCountBetween c S T]
  apply Finset.sum_congr rfl
  intro v hv
  exact C.greenOutside_degreeIn_of_mem_of_subset retained c (hS hv) hT

/-- Cleaning preserves color densities between two subsets of the retained
set. -/
theorem greenOutside_colorDensity_of_subsets
    (C : ColoredGraph V) (retained : Finset V) (c : EdgeColor)
    {S T : Finset V} (hS : S ⊆ retained) (hT : T ⊆ retained) :
    (C.greenOutside retained).colorDensity c S T =
      C.colorDensity c S T := by
  unfold colorDensity
  rw [C.greenOutside_colorEdgeCountBetween_of_subsets retained c hS hT]

/-- On the retained set, cleaning preserves the entire restricted edge
finset, in every color. -/
@[simp]
theorem greenOutside_edgeFinsetIn (C : ColoredGraph V) (S : Finset V)
    (c : EdgeColor) :
    (C.greenOutside S).edgeFinsetIn c S = C.edgeFinsetIn c S := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [pair_mem_edgeFinsetIn]
      constructor
      · rintro ⟨hxy, hcolor, hx, hy⟩
        rw [C.greenOutside_color_of_mem S hx hy] at hcolor
        exact ⟨hxy, hcolor, hx, hy⟩
      · rintro ⟨hxy, hcolor, hx, hy⟩
        rw [C.greenOutside_color_of_mem S hx hy]
        exact ⟨hxy, hcolor, hx, hy⟩

/-- On the retained set, cleaning preserves the number of edges in every
color. -/
@[simp]
theorem greenOutside_edgeCountIn (C : ColoredGraph V) (S : Finset V)
    (c : EdgeColor) :
    (C.greenOutside S).edgeCountIn c S = C.edgeCountIn c S := by
  unfold edgeCountIn
  rw [C.greenOutside_edgeFinsetIn S c]

/-- Cleaning creates no non-green edge outside the retained set.  Thus the
full non-green edge finset after cleaning is exactly the original restricted
edge finset. -/
theorem greenOutside_edgeFinset_of_ne_green (C : ColoredGraph V) (S : Finset V)
    {c : EdgeColor} (hc : c ≠ .green) :
    (C.greenOutside S).edgeFinset c = C.edgeFinsetIn c S := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [pair_mem_edgeFinset, pair_mem_edgeFinsetIn]
      constructor
      · rintro ⟨hxy, hcolor⟩
        rw [C.greenOutside_color_of_ne S hxy] at hcolor
        by_cases hmem : x ∈ S ∧ y ∈ S
        · rw [if_pos hmem] at hcolor
          exact ⟨hxy, hcolor, hmem.1, hmem.2⟩
        · rw [if_neg hmem] at hcolor
          exact (hc hcolor.symm).elim
      · rintro ⟨hxy, hcolor, hx, hy⟩
        refine ⟨hxy, ?_⟩
        rw [C.greenOutside_color_of_mem S hx hy]
        exact hcolor

/-- Cleaning creates no non-green edges outside the retained set, at the
level of edge counts. -/
theorem greenOutside_edgeCount_of_ne_green (C : ColoredGraph V) (S : Finset V)
    {c : EdgeColor} (hc : c ≠ .green) :
    (C.greenOutside S).edgeCount c = C.edgeCountIn c S := by
  unfold edgeCount edgeCountIn
  rw [C.greenOutside_edgeFinset_of_ne_green S hc]

/-- At a retained vertex, all non-green neighbors after cleaning are exactly
the original non-green neighbors inside the retained set. -/
theorem greenOutside_neighborFinset_of_mem_of_ne_green
    (C : ColoredGraph V) (S : Finset V) {c : EdgeColor} (hc : c ≠ .green)
    {v : V} (hv : v ∈ S) :
    (C.greenOutside S).neighborFinset c v = C.neighborFinsetIn c v S := by
  ext w
  rw [mem_neighborFinset, mem_neighborFinsetIn]
  constructor
  · rintro ⟨hvw, hcolor⟩
    rw [C.greenOutside_color_of_ne S hvw] at hcolor
    by_cases hw : w ∈ S
    · exact ⟨hvw, by simpa [hv, hw] using hcolor, hw⟩
    · simp [hv, hw] at hcolor
      exact (hc hcolor.symm).elim
  · rintro ⟨hvw, hcolor, hw⟩
    refine ⟨hvw, ?_⟩
    rw [C.greenOutside_color_of_mem S hv hw]
    exact hcolor

/-- At a retained vertex, cleaning turns full red degree into the original
red degree restricted to the retained set. -/
@[simp]
theorem greenOutside_redDegree_of_mem (C : ColoredGraph V) (S : Finset V)
    {v : V} (hv : v ∈ S) :
    (C.greenOutside S).redDegree v = C.redDegreeIn v S := by
  change #((C.greenOutside S).neighborFinset .red v) =
    #(C.neighborFinsetIn .red v S)
  rw [C.greenOutside_neighborFinset_of_mem_of_ne_green S
    (c := .red) (by decide) hv]

/-- At a retained vertex, cleaning turns full blue degree into the original
blue degree restricted to the retained set. -/
@[simp]
theorem greenOutside_blueDegree_of_mem (C : ColoredGraph V) (S : Finset V)
    {v : V} (hv : v ∈ S) :
    (C.greenOutside S).blueDegree v = C.blueDegreeIn v S := by
  change #((C.greenOutside S).neighborFinset .blue v) =
    #(C.neighborFinsetIn .blue v S)
  rw [C.greenOutside_neighborFinset_of_mem_of_ne_green S
    (c := .blue) (by decide) hv]

end GreenOutsideFinite

/-- Pull a complete-graph coloring back along an injective map of vertices. -/
abbrev pullback (C : ColoredGraph V) (f : W ↪ V) : ColoredGraph W :=
  SimpleGraph.TopEdgeLabeling.pullback C f

/-- Pullback commutes with the total color accessor. -/
@[simp]
theorem pullback_color [DecidableEq W] (C : ColoredGraph V) (f : W ↪ V) (x y : W) :
    (C.pullback f).color x y = C.color (f x) (f y) := by
  by_cases h : x = y
  · subst y
    simp
  · have hf : f x ≠ f y := f.injective.ne h
    simp only [color_eq_get _ h, color_eq_get _ hf]
    rfl

end ColoredGraph

end InducedStars
