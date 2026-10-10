import InducedStars.Structure.Supercritical.ProfileRealization
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Card
import Mathlib.Tactic

/-!
# Clean supercritical profile fibers and sparse-edge encoding

This module formalizes the exact finite encoding used in the clean branch of
the supercritical argument.  Ordinary division defects vanish, but the graph
induced by the sparse set remains free.  A graph in one profile fiber is
therefore determined by its cross-part choices and its sparse induced edges.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance cleanSparseDecidableRel
    {V : Type*} (G : SimpleGraph V) : DecidableRel G.Adj :=
  Classical.decRel _

noncomputable local instance cleanSparseGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) :=
  Classical.decEq _

/-! ## The literal clean profile fiber -/

/-- The paper's clean fiber `ℱ*_{Π,m}`: clean close graphs whose exact
cross-part edge profile is `profile`. -/
def supercriticalCleanDivisionProfileGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n))
    (profile : SupercriticalEdgeProfile D) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (supercriticalCleanDivisionGraphFinset
    k hk gamma hgamma m n tau hn D).filter fun G ↦
      crossEdgeProfile G D = profile

@[simp] theorem mem_supercriticalCleanDivisionProfileGraphFinset
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profile : SupercriticalEdgeProfile D} {G : SimpleGraph (Fin n)} :
    G ∈ supercriticalCleanDivisionProfileGraphFinset
        k hk gamma hgamma m n tau hn D profile ↔
      G ∈ supercriticalCleanDivisionGraphFinset
          k hk gamma hgamma m n tau hn D ∧
        crossEdgeProfile G D = profile := by
  classical
  simp [supercriticalCleanDivisionProfileGraphFinset]

theorem canonicalSupercriticalDivision_eq_of_mem_cleanProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profile : SupercriticalEdgeProfile D} {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalCleanDivisionProfileGraphFinset
      k hk gamma hgamma m n tau hn D profile) :
    canonicalSupercriticalDivision G (by simpa using hn) = D := by
  exact (mem_supercriticalCleanDivisionGraphFinset.mp
    (mem_supercriticalCleanDivisionProfileGraphFinset.mp hG).1).2.1

theorem crossEdgeProfile_eq_of_mem_cleanProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profile : SupercriticalEdgeProfile D} {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalCleanDivisionProfileGraphFinset
      k hk gamma hgamma m n tau hn D profile) :
    crossEdgeProfile G D = profile :=
  (mem_supercriticalCleanDivisionProfileGraphFinset.mp hG).2

theorem finiteGraphEdges_card_eq_of_mem_cleanProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profile : SupercriticalEdgeProfile D} {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalCleanDivisionProfileGraphFinset
      k hk gamma hgamma m n tau hn D profile) :
    (finiteGraphEdges G).card = m := by
  have hclean := (mem_supercriticalCleanDivisionProfileGraphFinset.mp hG).1
  rw [finiteGraphEdges_card_eq_edgeFinset_card]
  exact (mem_supercriticalCloseGraphFinset.mp
    (mem_supercriticalCleanDivisionGraphFinset.mp hclean).1).2.1

/-! ## Exact clean geometry -/

theorem supercriticalDefectGraph_eq_bot_of_mem_cleanProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profile : SupercriticalEdgeProfile D} {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalCleanDivisionProfileGraphFinset
      k hk gamma hgamma m n tau hn D profile) :
    supercriticalDefectGraph G D = ⊥ := by
  have hclean := (mem_supercriticalCleanDivisionProfileGraphFinset.mp hG).1
  have hzero := (mem_supercriticalCleanDivisionGraphFinset.mp hclean).2.2
  have hD := canonicalSupercriticalDivision_eq_of_mem_cleanProfile hG
  have hzero' : (finiteGraphEdges (supercriticalDefectGraph G D)).card = 0 := by
    simpa [canonicalSupercriticalDefectGraph, hD] using hzero
  ext x y
  constructor
  · intro hxy
    have hmem : s(x, y) ∈ finiteGraphEdges (supercriticalDefectGraph G D) := by
      simpa using hxy
    have hempty : finiteGraphEdges (supercriticalDefectGraph G D) = ∅ :=
      Finset.card_eq_zero.mp hzero'
    simpa [hempty] using hmem
  · simp

theorem mainParts_clique_of_mem_cleanProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profile : SupercriticalEdgeProfile D} {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalCleanDivisionProfileGraphFinset
      k hk gamma hgamma m n tau hn D profile)
    (i : Fin (k - 1)) {x y : Fin n}
    (hx : x ∈ D.parts i) (hy : y ∈ D.parts i) (hxy : x ≠ y) :
    G.Adj x y := by
  by_contra hnot
  have hdef : (supercriticalDefectGraph G D).Adj x y :=
    (supercriticalDefectGraph_adj_of_mem_same_part G D i hx hy).2
      ⟨hxy, hnot⟩
  rw [supercriticalDefectGraph_eq_bot_of_mem_cleanProfile hG] at hdef
  exact hdef

theorem not_adj_support_sparse_of_mem_cleanProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profile : SupercriticalEdgeProfile D} {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalCleanDivisionProfileGraphFinset
      k hk gamma hgamma m n tau hn D profile)
    {x y : Fin n} (hx : x ∈ D.support) (hy : y ∈ D.sparse) :
    ¬ G.Adj x y := by
  intro hxy
  have hdef : (supercriticalDefectGraph G D).Adj x y :=
    (supercriticalDefectGraph_adj_support_sparse G D hx hy).2 hxy
  rw [supercriticalDefectGraph_eq_bot_of_mem_cleanProfile hG] at hdef
  exact hdef

theorem combinedSupercriticalDefectGraph_eq_sparseInduced_of_mem_cleanProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profile : SupercriticalEdgeProfile D} {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalCleanDivisionProfileGraphFinset
      k hk gamma hgamma m n tau hn D profile) :
    combinedSupercriticalDefectGraph G D = sparseInducedGraph G D := by
  rw [combinedSupercriticalDefectGraph,
    supercriticalDefectGraph_eq_bot_of_mem_cleanProfile hG, bot_sup_eq]

/-! ## Sparse potential edges -/

/-- All unordered non-loop pairs whose endpoints lie in the sparse set. -/
def supercriticalSparsePotentialEdges
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) : Finset (Sym2 V) :=
  D.sparse.offDiag.image Sym2.mk.uncurry

@[simp] theorem card_supercriticalSparsePotentialEdges
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) :
    (supercriticalSparsePotentialEdges D).card =
      Nat.choose D.sparse.card 2 := by
  exact Sym2.card_image_offDiag D.sparse

/-- The actual graph edges induced by the sparse set, retained as ambient
unordered edges. -/
def supercriticalSparseInducedEdges
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    Finset (Sym2 V) :=
  (@SimpleGraph.edgeFinset V G G.fintypeEdgeSet).filter fun e ↦
    e.toFinset ⊆ D.sparse

theorem supercriticalSparseInducedEdges_subset_potential
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    supercriticalSparseInducedEdges G D ⊆
      supercriticalSparsePotentialEdges D := by
  classical
  intro e he
  rw [supercriticalSparseInducedEdges, Finset.mem_filter] at he
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : x ≠ y := by
        exact G.ne_of_adj (by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
            using he.1)
      have hx : x ∈ D.sparse := he.2 (by simp)
      have hy : y ∈ D.sparse := he.2 (by simp)
      rw [supercriticalSparsePotentialEdges, Finset.mem_image]
      exact ⟨(x, y), by simp [hx, hy, hxy], rfl⟩

@[simp] theorem card_supercriticalSparseInducedEdges
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    (supercriticalSparseInducedEdges G D).card =
      inducedEdgeCount G D.sparse := by
  classical
  rw [supercriticalSparseInducedEdges, inducedEdgeCount]
  exact SimpleGraph.card_filter_edgeFinset_toFinset_subset
    (G := G) D.sparse

/-! ## The clean shift is exactly the sparse induced-edge count -/

private theorem cleanSparse_inducedEdgeCount_eq_of_induce_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (S : Finset V)
    (h : G.induce (S : Set V) = H.induce (S : Set V)) :
    inducedEdgeCount G S = inducedEdgeCount H S := by
  unfold inducedEdgeCount
  apply congrArg Finset.card
  ext e
  simp only [SimpleGraph.mem_edgeFinset]
  rw [h]

@[simp] theorem inducedEdgeCount_sparseInducedGraph_sparse
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    inducedEdgeCount (sparseInducedGraph G D) D.sparse =
      inducedEdgeCount G D.sparse := by
  apply cleanSparse_inducedEdgeCount_eq_of_induce_eq
  ext x y
  simp

@[simp] theorem inducedEdgeCount_sparseInducedGraph_support
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    inducedEdgeCount (sparseInducedGraph G D) D.support = 0 := by
  have hinter :
      (sparseInducedGraph G D).interedges D.support D.support = ∅ := by
    ext xy
    simp only [SimpleGraph.mem_interedges_iff, sparseInducedGraph_adj]
    constructor
    · rintro ⟨hxSupport, _, hxSparse, _, _⟩
      exact False.elim
        ((SupercriticalDivision.mem_sparse.mp hxSparse) hxSupport)
    · intro h
      simp at h
  have hcard := card_interedges_self_eq_two_mul_inducedEdgeCount
    (sparseInducedGraph G D) D.support
  rw [hinter] at hcard
  simp only [Finset.card_empty] at hcard
  omega

@[simp] theorem interedges_sparseInducedGraph_support_sparse
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    (sparseInducedGraph G D).interedges D.support D.sparse = ∅ := by
  ext xy
  simp only [SimpleGraph.mem_interedges_iff, sparseInducedGraph_adj]
  constructor
  · rintro ⟨hxSupport, _, hxSparse, _, _⟩
    exact False.elim ((SupercriticalDivision.mem_sparse.mp hxSparse) hxSupport)
  · intro h
    simp at h

/-- For a clean graph the paper's integer defect shift has positive sign and
is exactly the number of graph edges induced by the sparse set. -/
theorem supercriticalDefectShift_clean_eq_inducedEdgeCount
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profile : SupercriticalEdgeProfile D} {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalCleanDivisionProfileGraphFinset
      k hk gamma hgamma m n tau hn D profile) :
    supercriticalDefectShift (combinedSupercriticalDefectGraph G D) D =
      (inducedEdgeCount G D.sparse : ℤ) := by
  rw [combinedSupercriticalDefectGraph_eq_sparseInduced_of_mem_cleanProfile hG]
  simp [supercriticalDefectShift]

/-- In a clean fiber at shift `t`, the arbitrary sparse induced graph has
exactly `t` edges.  This is derived from the edge equation rather than added
as an extra defining condition on the fiber. -/
theorem inducedEdgeCount_eq_shift_of_mem_cleanProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n t : ℕ} {tau rho delta : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profile : SupercriticalEdgeProfile D} {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalCleanDivisionProfileGraphFinset
      k hk gamma hgamma m n tau hn D profile)
    (hprofile : SupercriticalProfileAtShift D m rho delta (t : ℤ) profile) :
    inducedEdgeCount G D.sparse = t := by
  have hedge := supercriticalDefectShift_edgeCount_identity G D
  have hprofileEquation := hprofile.1
  rw [finiteGraphEdges_card_eq_of_mem_cleanProfile hG,
    crossEdgeProfile_eq_of_mem_cleanProfile hG,
    supercriticalDefectShift_clean_eq_inducedEdgeCount hG] at hedge
  exact_mod_cast (show (inducedEdgeCount G D.sparse : ℤ) = (t : ℤ) by
    omega)

theorem card_supercriticalSparseInducedEdges_eq_shift_of_mem_cleanProfile
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n t : ℕ} {tau rho delta : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profile : SupercriticalEdgeProfile D} {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalCleanDivisionProfileGraphFinset
      k hk gamma hgamma m n tau hn D profile)
    (hprofile : SupercriticalProfileAtShift D m rho delta (t : ℤ) profile) :
    (supercriticalSparseInducedEdges G D).card = t := by
  rw [card_supercriticalSparseInducedEdges,
    inducedEdgeCount_eq_shift_of_mem_cleanProfile hG hprofile]

@[simp] theorem sym2_mk_mem_supercriticalSparseInducedEdges
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : SupercriticalDivision k V) (x y : V) :
    s(x, y) ∈ supercriticalSparseInducedEdges G D ↔
      x ∈ D.sparse ∧ y ∈ D.sparse ∧ G.Adj x y := by
  classical
  rw [supercriticalSparseInducedEdges, Finset.mem_filter,
    SimpleGraph.mem_edgeFinset]
  constructor
  · rintro ⟨hadj, hsubset⟩
    exact ⟨hsubset (by simp), hsubset (by simp), hadj⟩
  · rintro ⟨hx, hy, hadj⟩
    refine ⟨hadj, ?_⟩
    intro z hz
    rw [Sym2.mem_toFinset, Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy

/-! ## Exact clean encoding -/

/-- The oriented cross-cell choice made by a graph. -/
def supercriticalCleanCrossChoiceOfGraph
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) (G : SimpleGraph V) :
    SupercriticalPartPair k → Finset (V × V) :=
  fun e ↦ G.interedges (D.parts e.left) (D.parts e.right)

theorem supercriticalCleanCrossChoiceOfGraph_mem
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profile : SupercriticalEdgeProfile D} {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalCleanDivisionProfileGraphFinset
      k hk gamma hgamma m n tau hn D profile) :
    supercriticalCleanCrossChoiceOfGraph D G ∈
      supercriticalProfileChoiceFinset D profile := by
  rw [mem_supercriticalProfileChoiceFinset]
  intro e
  constructor
  · intro xy hxy
    rw [supercriticalCleanCrossChoiceOfGraph,
      SimpleGraph.mem_interedges_iff] at hxy
    exact Finset.mem_product.mpr ⟨hxy.1, hxy.2.1⟩
  · change (G.interedges (D.parts e.left) (D.parts e.right)).card =
      profile.count e
    have h := congrArg
      (fun p : SupercriticalEdgeProfile D ↦ p.count e)
      (crossEdgeProfile_eq_of_mem_cleanProfile hG)
    simpa only [crossEdgeProfile_count] using h

/-- The finite target for the exact clean graph encoding: one prescribed
cross-cell outcome and one `t`-edge sparse graph. -/
def supercriticalCleanGraphEncodingTarget
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V)
    (profile : SupercriticalEdgeProfile D) (t : ℕ) : Type _ :=
  ↑((supercriticalProfileChoiceFinset D profile).product
    ((supercriticalSparsePotentialEdges D).powersetCard t))

/-- Encode a graph in a clean profile fiber by precisely its cross-edge
choices and its sparse induced edge set. -/
def supercriticalCleanGraphEncoding
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n t : ℕ} {tau rho delta : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profile : SupercriticalEdgeProfile D}
    (hprofile : SupercriticalProfileAtShift D m rho delta (t : ℤ) profile) :
    ↑(supercriticalCleanDivisionProfileGraphFinset
      k hk gamma hgamma m n tau hn D profile) →
      supercriticalCleanGraphEncodingTarget D profile t :=
  fun G ↦
    ⟨(supercriticalCleanCrossChoiceOfGraph D G.1,
        supercriticalSparseInducedEdges G.1 D),
      Finset.mem_product.mpr
        ⟨supercriticalCleanCrossChoiceOfGraph_mem G.2,
          Finset.mem_powersetCard.mpr
            ⟨supercriticalSparseInducedEdges_subset_potential G.1 D,
              card_supercriticalSparseInducedEdges_eq_shift_of_mem_cleanProfile
                G.2 hprofile⟩⟩⟩

/-- The clean encoding is injective.  Its proof recovers adjacency in the
four geometric cases: one main part, two main parts, support--sparse, and
sparse--sparse. -/
theorem supercriticalCleanGraphEncoding_injective
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n t : ℕ} {tau rho delta : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profile : SupercriticalEdgeProfile D}
    (hprofile : SupercriticalProfileAtShift D m rho delta (t : ℤ) profile) :
    Function.Injective (supercriticalCleanGraphEncoding
      (hk := hk) (hgamma := hgamma) (tau := tau) (hn := hn) hprofile) := by
  classical
  intro G H henc
  apply Subtype.ext
  ext x y
  by_cases hxy : x = y
  · subst y
    simp
  have hcross : supercriticalCleanCrossChoiceOfGraph D G.1 =
      supercriticalCleanCrossChoiceOfGraph D H.1 :=
    congrArg (fun z ↦ z.1.1) henc
  have hsparse : supercriticalSparseInducedEdges G.1 D =
      supercriticalSparseInducedEdges H.1 D :=
    congrArg (fun z ↦ z.1.2) henc
  rcases D.sparse_or_existsUnique_part x with hxSparse | ⟨i, hxi, _⟩
  · rcases D.sparse_or_existsUnique_part y with hySparse | ⟨j, hyj, _⟩
    · have hmem := congrArg (fun E ↦ s(x, y) ∈ E) hsparse
      simpa [hxSparse, hySparse] using hmem
    · have hySupport : y ∈ D.support :=
        D.part_subset_support j hyj
      constructor
      · intro hGxy
        exact False.elim
          ((not_adj_support_sparse_of_mem_cleanProfile G.2
            hySupport hxSparse) ((G.1.adj_comm y x).mpr hGxy))
      · intro hHxy
        exact False.elim
          ((not_adj_support_sparse_of_mem_cleanProfile H.2
            hySupport hxSparse) ((H.1.adj_comm y x).mpr hHxy))
  · rcases D.sparse_or_existsUnique_part y with hySparse | ⟨j, hyj, _⟩
    · have hxSupport : x ∈ D.support := D.part_subset_support i hxi
      constructor
      · intro hGxy
        exact False.elim
          ((not_adj_support_sparse_of_mem_cleanProfile G.2
            hxSupport hySparse) hGxy)
      · intro hHxy
        exact False.elim
          ((not_adj_support_sparse_of_mem_cleanProfile H.2
            hxSupport hySparse) hHxy)
    · by_cases hij : i = j
      · subst j
        constructor
        · intro _
          exact mainParts_clique_of_mem_cleanProfile H.2 i hxi hyj hxy
        · intro _
          exact mainParts_clique_of_mem_cleanProfile G.2 i hxi hyj hxy
      · by_cases hlt : i < j
        · let e : SupercriticalPartPair k := ⟨i, j, hlt⟩
          have heq := congrFun hcross e
          have hmem := congrArg (fun E ↦ (x, y) ∈ E) heq
          simpa [supercriticalCleanCrossChoiceOfGraph,
            SimpleGraph.mem_interedges_iff, e, hxi, hyj] using hmem
        · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
          let e : SupercriticalPartPair k := ⟨j, i, hji⟩
          have heq := congrFun hcross e
          have hmem := congrArg (fun E ↦ (y, x) ∈ E) heq
          simpa [supercriticalCleanCrossChoiceOfGraph,
            SimpleGraph.mem_interedges_iff, e, hxi, hyj,
            G.1.adj_comm, H.1.adj_comm] using hmem

/-! ## Exact and coarse clean-fiber bounds -/

/-- Exact finite clean-fiber count: cross-part choices times the number of
`t`-edge graphs on the sparse vertex set. -/
theorem card_supercriticalCleanDivisionProfileGraphFinset_le
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n t : ℕ} {tau rho delta : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profile : SupercriticalEdgeProfile D}
    (hprofile : SupercriticalProfileAtShift D m rho delta (t : ℤ) profile) :
    (supercriticalCleanDivisionProfileGraphFinset
      k hk gamma hgamma m n tau hn D profile).card ≤
      supercriticalProfileMultiplicity profile *
        Nat.choose (Nat.choose D.sparse.card 2) t := by
  classical
  have hcard := Finset.card_le_card_of_injective
    (supercriticalCleanGraphEncoding_injective
      (hk := hk) (hgamma := hgamma) (tau := tau) (hn := hn) hprofile)
  calc
    (supercriticalCleanDivisionProfileGraphFinset
        k hk gamma hgamma m n tau hn D profile).card ≤
        ((supercriticalProfileChoiceFinset D profile).product
          ((supercriticalSparsePotentialEdges D).powersetCard t)).card := hcard
    _ = (supercriticalProfileChoiceFinset D profile).card *
          ((supercriticalSparsePotentialEdges D).powersetCard t).card :=
      Finset.card_product _ _
    _ = supercriticalProfileMultiplicity profile *
          Nat.choose (Nat.choose D.sparse.card 2) t := by
      rw [card_supercriticalProfileChoiceFinset,
        Finset.card_powersetCard, card_supercriticalSparsePotentialEdges]

/-- Coarse form of the clean-fiber count, retaining only the binary entropy
of an arbitrary graph on the sparse set. -/
theorem card_supercriticalCleanDivisionProfileGraphFinset_le_mul_two_pow
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n t : ℕ} {tau rho delta : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {profile : SupercriticalEdgeProfile D}
    (hprofile : SupercriticalProfileAtShift D m rho delta (t : ℤ) profile) :
    (supercriticalCleanDivisionProfileGraphFinset
      k hk gamma hgamma m n tau hn D profile).card ≤
      supercriticalProfileMultiplicity profile *
        2 ^ Nat.choose D.sparse.card 2 := by
  exact (card_supercriticalCleanDivisionProfileGraphFinset_le hprofile).trans
    (Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _))

end InducedStars
