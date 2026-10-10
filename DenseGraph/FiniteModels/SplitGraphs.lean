import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Tactic

/-!
# Transparent finite split-graph witnesses

Both sides may be empty. The exclusion of an induced four-cycle is proved
directly from the independent/clique partition, without a forbidden-graph
characterization of split graphs.
-/

namespace DenseGraph

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A finite split graph has a covering independent/clique partition. -/
structure SplitGraphWitness (G : SimpleGraph V) where
  independentPart : Finset V
  cliquePart : Finset V
  disjoint : Disjoint independentPart cliquePart
  cover : independentPart ∪ cliquePart = Finset.univ
  independent : G.IsIndepSet (independentPart : Set V)
  clique : G.IsClique (cliquePart : Set V)

/-- Existence of an actual split partition, permitting empty parts. -/
def IsSplitGraph (G : SimpleGraph V) : Prop := Nonempty (SplitGraphWitness G)

namespace SplitGraphWitness

variable {G : SimpleGraph V}

theorem mem_or_mem (P : SplitGraphWitness G) (v : V) :
    v ∈ P.independentPart ∨ v ∈ P.cliquePart := by
  have : v ∈ P.independentPart ∪ P.cliquePart := by rw [P.cover]; simp
  exact Finset.mem_union.mp this

theorem cliquePart_eq_compl (P : SplitGraphWitness G) :
    P.cliquePart = Finset.univ \ P.independentPart := by
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro hB hA
    exact Finset.disjoint_left.mp P.disjoint hA hB
  · intro hA
    exact (P.mem_or_mem v).resolve_left hA

/-- A neighbor of a vertex in the independent part must be in the clique. -/
theorem neighbor_mem_clique (P : SplitGraphWitness G) {x y : V}
    (hx : x ∈ P.independentPart) (hxy : G.Adj x y) : y ∈ P.cliquePart := by
  rcases P.mem_or_mem y with hy | hy
  · exact False.elim (P.independent hx hy hxy.ne hxy)
  · exact hy

/-- Direct induced-four-cycle exclusion. Two neighbors of a vertex in the
independent part would be nonadjacent vertices in the clique part. -/
theorem no_induced_cycleFour (P : SplitGraphWitness G) :
    ¬Nonempty ((SimpleGraph.cycleGraph 4) ↪g G) := by
  rintro ⟨f⟩
  have h01 : G.Adj (f 0) (f 1) := f.map_rel_iff.mpr (by decide)
  have h03 : G.Adj (f 0) (f 3) := f.map_rel_iff.mpr (by decide)
  have h21 : G.Adj (f 2) (f 1) := f.map_rel_iff.mpr (by decide)
  have h23 : G.Adj (f 2) (f 3) := f.map_rel_iff.mpr (by decide)
  have h13 : ¬G.Adj (f 1) (f 3) := fun h ↦ (by decide :
    ¬(SimpleGraph.cycleGraph 4).Adj 1 3) (f.map_rel_iff.mp h)
  have h02 : ¬G.Adj (f 0) (f 2) := fun h ↦ (by decide :
    ¬(SimpleGraph.cycleGraph 4).Adj 0 2) (f.map_rel_iff.mp h)
  have h0 : f 0 ∈ P.cliquePart := by
    rcases P.mem_or_mem (f 0) with h | h
    · exact False.elim (h13 (P.clique (P.neighbor_mem_clique h h01)
        (P.neighbor_mem_clique h h03) (f.injective.ne (by decide))))
    · exact h
  have h2 : f 2 ∈ P.cliquePart := by
    rcases P.mem_or_mem (f 2) with h | h
    · exact False.elim (h13 (P.clique (P.neighbor_mem_clique h h21)
        (P.neighbor_mem_clique h h23) (f.injective.ne (by decide))))
    · exact h
  exact h02 (P.clique h0 h2 (f.injective.ne (by decide)))

end SplitGraphWitness

theorem IsSplitGraph.no_induced_cycleFour {G : SimpleGraph V} (hG : IsSplitGraph G) :
    ¬Nonempty ((SimpleGraph.cycleGraph 4) ↪g G) := by
  obtain ⟨P⟩ := hG
  exact P.no_induced_cycleFour

end DenseGraph
