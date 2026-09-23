import InducedStars.Structure.Supercritical.MatchingFamilies
import InducedStars.Structure.Supercritical.MatchingSetup
import InducedStars.FiniteModels.EntropyAsymptotics
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-!
# Counting support-incident supercritical defect patterns

The combined defect pattern splits into its support-incident part and its
sparse-induced part.  A maximum matching supplies a canonical vertex cover
of the former; recording the cover and its oriented neighborhoods gives an
injective low-entropy encoding.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

noncomputable local instance supportPatternEdgeSetFintype
    (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

noncomputable local instance supportPatternNeighborSetFintype
    (G : SimpleGraph V) (v : V) : Fintype (G.neighborSet v) :=
  Fintype.ofFinite (G.neighborSet v)

noncomputable local instance supportPatternDecidableRel
    (G : SimpleGraph V) : DecidableRel G.Adj :=
  Classical.decRel G.Adj

/-! ## Exact support/sparse decomposition -/

/-- The sparse-induced part of a displayed combined defect pattern. -/
abbrev supercriticalSparseInducedPattern
    (D : SupercriticalDivision k V) (T : SimpleGraph V) : SimpleGraph V :=
  sparseInducedGraph T D

/-- Every edge is either incident with the main support or has both endpoints
in the sparse set. -/
theorem supercriticalSupportIncident_sup_sparseInduced
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    supercriticalSupportIncidentGraph D T ⊔
        supercriticalSparseInducedPattern D T = T := by
  ext x y
  simp only [SimpleGraph.sup_adj, supercriticalSupportIncidentGraph_adj,
    sparseInducedGraph_adj]
  constructor
  · rintro (⟨hT, -⟩ | ⟨-, -, hT⟩) <;> exact hT
  · intro hT
    by_cases hx : x ∈ D.support
    · exact Or.inl ⟨hT, Or.inl hx⟩
    · have hxs : x ∈ D.sparse := by
        simpa [SupercriticalDivision.sparse] using hx
      by_cases hy : y ∈ D.support
      · exact Or.inl ⟨hT, Or.inr hy⟩
      · have hys : y ∈ D.sparse := by
          simpa [SupercriticalDivision.sparse] using hy
        exact Or.inr ⟨hxs, hys, hT⟩

/-- The two pieces of the support/sparse decomposition have disjoint edge
sets. -/
theorem supercriticalSupportIncident_disjoint_sparseInduced
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    Disjoint (supercriticalSupportIncidentGraph D T)
      (supercriticalSparseInducedPattern D T) := by
  rw [SimpleGraph.disjoint_left]
  intro x y hT hJ
  have hsupport :=
    (supercriticalSupportIncidentGraph_adj D T x y).mp hT |>.2
  have hsparse := (sparseInducedGraph_adj T D x y).mp hJ
  rcases hsupport with hx | hy
  · exact (SupercriticalDivision.mem_sparse.mp hsparse.1) hx
  · exact (SupercriticalDivision.mem_sparse.mp hsparse.2.1) hy

theorem supercriticalSupportIncident_edgeFinset_disjoint_sparseInduced
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    Disjoint (supercriticalSupportIncidentGraph D T).edgeFinset
      (supercriticalSparseInducedPattern D T).edgeFinset := by
  exact SimpleGraph.disjoint_edgeFinset.mpr
    (supercriticalSupportIncident_disjoint_sparseInduced D T)

/-- Applying the support-incident restriction twice changes nothing. -/
@[simp] theorem supercriticalSupportIncidentGraph_idem
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    supercriticalSupportIncidentGraph D
        (supercriticalSupportIncidentGraph D T) =
      supercriticalSupportIncidentGraph D T := by
  ext x y
  simp [supercriticalSupportIncidentGraph_adj]

/-- Removing the sparse-induced part does not change the paper's matching
number. -/
@[simp] theorem supercriticalMatchingNumber_supportIncident
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    supercriticalMatchingNumber D
        (supercriticalSupportIncidentGraph D T) =
      supercriticalMatchingNumber D T := by
  simp [supercriticalMatchingNumber]

/-! ## The signed support shift -/

/-- Net edge-count shift contributed by the support-incident pattern. -/
def supercriticalSupportDefectShift
    (D : SupercriticalDivision k V) (T₀ : SimpleGraph V) : ℤ :=
  by
    classical
    exact ((T₀.interedges D.support D.sparse).card : ℤ) -
      (inducedEdgeCount T₀ D.support : ℤ)

@[simp] theorem supercriticalSupportDefectShift_eq
    (D : SupercriticalDivision k V) (T₀ : SimpleGraph V) :
    supercriticalSupportDefectShift D T₀ =
      ((T₀.interedges D.support D.sparse).card : ℤ) -
        (inducedEdgeCount T₀ D.support : ℤ) :=
  rfl

private theorem interedges_support_sparse_supportIncident
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    (supercriticalSupportIncidentGraph D T).interedges
        D.support D.sparse = T.interedges D.support D.sparse := by
  ext p
  simp only [SimpleGraph.mem_interedges_iff,
    supercriticalSupportIncidentGraph_adj]
  tauto

private theorem inducedEdgeCount_support_supportIncident
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    inducedEdgeCount (supercriticalSupportIncidentGraph D T) D.support =
      inducedEdgeCount T D.support := by
  have hgraph :
      (supercriticalSupportIncidentGraph D T).induce (D.support : Set V) =
        T.induce (D.support : Set V) := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    simp [SimpleGraph.induce_adj, supercriticalSupportIncidentGraph_adj]
  unfold inducedEdgeCount
  apply congrArg Finset.card
  ext e
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  rw [hgraph]

private theorem inducedEdgeCount_sparse_sparseInduced
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    inducedEdgeCount (supercriticalSparseInducedPattern D T) D.sparse =
      inducedEdgeCount T D.sparse := by
  have hgraph :
      (supercriticalSparseInducedPattern D T).induce (D.sparse : Set V) =
        T.induce (D.sparse : Set V) := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    simp [SimpleGraph.induce_adj, sparseInducedGraph_adj]
  unfold inducedEdgeCount
  apply congrArg Finset.card
  ext e
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  rw [hgraph]

/-- The total defect shift is the support shift plus the number of
sparse-induced edges. -/
theorem supercriticalDefectShift_eq_support_add_sparse
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    supercriticalDefectShift T D =
      supercriticalSupportDefectShift D
          (supercriticalSupportIncidentGraph D T) +
        (inducedEdgeCount (supercriticalSparseInducedPattern D T)
          D.sparse : ℤ) := by
  rw [supercriticalDefectShift_eq, supercriticalSupportDefectShift_eq,
    interedges_support_sparse_supportIncident,
    inducedEdgeCount_support_supportIncident,
    inducedEdgeCount_sparse_sparseInduced]
  ring

private theorem supportIncident_edgeCount_eq_cross_add_internal
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    (finiteGraphEdges (supercriticalSupportIncidentGraph D T)).card =
      ((supercriticalSupportIncidentGraph D T).interedges
          D.support D.sparse).card +
        inducedEdgeCount (supercriticalSupportIncidentGraph D T) D.support := by
  let T₀ := supercriticalSupportIncidentGraph D T
  have hdecomp :=
    two_mul_card_finiteGraphEdges_eq_support_sparse_cells T₀ D
  have hsupport :=
    card_interedges_self_eq_two_mul_inducedEdgeCount T₀ D.support
  have hsparse : (T₀.interedges D.sparse D.sparse).card = 0 := by
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    rw [SimpleGraph.mem_interedges_iff] at hp
    exact supercriticalSupportIncidentGraph_not_adj_of_mem_sparse
      D T hp.1 hp.2.1 hp.2.2
  dsimp [T₀] at hdecomp hsupport hsparse ⊢
  rw [hsupport, hsparse, Nat.add_zero] at hdecomp
  omega

/-- The absolute support shift is at most the number of support-incident
edges. -/
theorem supercriticalSupportDefectShift_natAbs_le_edgeCount
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    (supercriticalSupportDefectShift D
      (supercriticalSupportIncidentGraph D T)).natAbs ≤
        (finiteGraphEdges
          (supercriticalSupportIncidentGraph D T)).card := by
  let a := ((supercriticalSupportIncidentGraph D T).interedges
    D.support D.sparse).card
  let b := inducedEdgeCount (supercriticalSupportIncidentGraph D T) D.support
  have habs : (((a : ℤ) - (b : ℤ))).natAbs ≤ a + b := by
    exact (Int.natAbs_sub_le (a : ℤ) (b : ℤ)).trans_eq (by simp)
  rw [supportIncident_edgeCount_eq_cross_add_internal D T]
  simpa [supercriticalSupportDefectShift, a, b] using habs

/-! ## Canonical endpoint cover and edge bound -/

/-- The endpoints of the canonical maximum matching, as a finset. -/
def supercriticalCanonicalMatchingEndpoints
    (D : SupercriticalDivision k V) (T : SimpleGraph V) : Finset V :=
  (supercriticalCanonicalMatching D T).verts.toFinite.toFinset

@[simp] theorem card_supercriticalCanonicalMatchingEndpoints
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    (supercriticalCanonicalMatchingEndpoints D T).card =
      2 * supercriticalMatchingNumber D T := by
  rw [supercriticalCanonicalMatchingEndpoints,
    ← Set.ncard_eq_toFinset_card]
  exact DenseGraph.canonicalMaximumMatching_endpoint_ncard
    (supercriticalSupportIncidentGraph D T)

theorem supercriticalCanonicalMatchingEndpoints_vertexCover
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    (supercriticalSupportIncidentGraph D T).IsVertexCover
      (supercriticalCanonicalMatchingEndpoints D T : Set V) := by
  have hcoe : (supercriticalCanonicalMatchingEndpoints D T : Set V) =
      (supercriticalCanonicalMatching D T).verts := by
    ext v
    simp [supercriticalCanonicalMatchingEndpoints]
  rw [hcoe]
  change (supercriticalSupportIncidentGraph D T).IsVertexCover
    (DenseGraph.canonicalMaximumMatching
      (supercriticalSupportIncidentGraph D T)).verts
  exact DenseGraph.canonicalMaximumMatching_endpoints_vertexCover
    (supercriticalSupportIncidentGraph D T)

private theorem degreeInFinset_univ_eq_degree
    (G : SimpleGraph V) (v : V) :
    degreeInFinset G v Finset.univ = G.degree v := by
  rw [← G.card_neighborFinset_eq_degree]
  unfold degreeInFinset
  congr 1
  ext w
  simp [SimpleGraph.neighborFinset]

private theorem degreeInFinset_graph_mono
    {G H : SimpleGraph V} (hGH : G ≤ H) (v : V) (S : Finset V) :
    degreeInFinset G v S ≤ degreeInFinset H v S := by
  classical
  unfold degreeInFinset
  apply Finset.card_le_card
  intro w hw
  rw [Finset.mem_filter] at hw ⊢
  exact ⟨hw.1, hGH hw.2⟩

/-- A vertex cover charges every edge to at least one degree in the cover. -/
theorem card_edgeFinset_le_sum_degreeInFinset_of_vertexCover
    (G : SimpleGraph V) (C : Finset V)
    (hC : G.IsVertexCover (C : Set V)) :
    G.edgeFinset.card ≤
      ∑ v ∈ C, degreeInFinset G v Finset.univ := by
  classical
  have hsubset : G.edgeFinset ⊆
      C.biUnion (fun v ↦ G.incidenceFinset v) := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxy : G.Adj x y := by
          simpa only [SimpleGraph.mem_edgeFinset,
            SimpleGraph.mem_edgeSet] using he
        rcases hC hxy with hx | hy
        · exact Finset.mem_biUnion.mpr ⟨x, hx,
            by rw [SimpleGraph.mem_incidenceFinset];
               exact G.mk'_mem_incidenceSet_left_iff.mpr hxy⟩
        · exact Finset.mem_biUnion.mpr ⟨y, hy,
            by rw [SimpleGraph.mem_incidenceFinset];
               exact G.mk'_mem_incidenceSet_right_iff.mpr hxy⟩
  calc
    G.edgeFinset.card ≤
        (C.biUnion (fun v ↦ G.incidenceFinset v)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ v ∈ C, (G.incidenceFinset v).card :=
      Finset.card_biUnion_le
    _ = ∑ v ∈ C, degreeInFinset G v Finset.univ := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [G.card_incidenceFinset_eq_degree,
        degreeInFinset_univ_eq_degree]

/-- A support pattern with matching number `h` and maximum degree `b` has at
most `2*h*b` edges. -/
theorem supercriticalSupportPattern_edgeCount_le_of_degree
    (D : SupercriticalDivision k V) (T : SimpleGraph V) (h b : ℕ)
    (hfixed : supercriticalSupportIncidentGraph D T = T)
    (hmatching : supercriticalMatchingNumber D T = h)
    (hdegree : ∀ v : V, degreeInFinset T v Finset.univ ≤ b) :
    (finiteGraphEdges T).card ≤ 2 * h * b := by
  let C := supercriticalCanonicalMatchingEndpoints D T
  have hcover : T.IsVertexCover (C : Set V) := by
    rw [← hfixed]
    exact supercriticalCanonicalMatchingEndpoints_vertexCover D T
  have hedge := card_edgeFinset_le_sum_degreeInFinset_of_vertexCover T C hcover
  have hsum : (∑ v ∈ C, degreeInFinset T v Finset.univ) ≤ C.card * b := by
    calc
      ∑ v ∈ C, degreeInFinset T v Finset.univ ≤ ∑ _v ∈ C, b := by
        exact Finset.sum_le_sum fun v _hv ↦ hdegree v
      _ = C.card * b := by simp
  have hcard : C.card = 2 * h := by
    simpa [C, hmatching] using
      card_supercriticalCanonicalMatchingEndpoints D T
  have hedgeEq : finiteGraphEdges T = T.edgeFinset := by
    ext e
    simp [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  rw [hedgeEq]
  exact hedge.trans (by simpa [hcard] using hsum)

/-- Low degree into every main part, together with the sparse-size bound,
controls the whole degree of a support-incident pattern.  Summing the main
parts costs only their total support size, not a factor of `k - 1`. -/
theorem supercriticalSupportPattern_degree_real_le
    {n : ℕ} (D : SupercriticalDivision k (Fin n))
    (T : SimpleGraph (Fin n)) {alpha delta : ℝ}
    (halpha : 0 ≤ alpha) (hdelta : 0 ≤ delta)
    (hlow : ∀ v : Fin n, ∀ i : Fin (k - 1),
      HasLowDegreeInPart T alpha D v i)
    (hsparse : (D.sparse.card : ℝ) ≤ delta * (n : ℝ) / 2)
    (v : Fin n) :
    (degreeInFinset T v Finset.univ : ℝ) ≤
      (alpha + delta) * (n : ℝ) := by
  have hsupportNat := degreeInFinset_support_eq_sum T D v
  have hsplitNat := degreeInFinset_support_add_sparse T D v
  have hmain :
      (∑ i : Fin (k - 1),
          (degreeInFinset T v (D.parts i) : ℝ)) ≤
        ∑ i : Fin (k - 1), alpha * ((D.parts i).card : ℝ) := by
    exact Finset.sum_le_sum fun i _hi ↦ (hlow v i).le
  have hsupportCard : ((D.support.card : ℕ) : ℝ) ≤ (n : ℝ) := by
    have h : D.support.card ≤ n := by
      simpa using Finset.card_le_univ (s := D.support)
    exact_mod_cast h
  have hsupportDegree :
      (degreeInFinset T v D.support : ℝ) ≤ alpha * (n : ℝ) := by
    calc
      (degreeInFinset T v D.support : ℝ) =
          ∑ i : Fin (k - 1),
            (degreeInFinset T v (D.parts i) : ℝ) := by
        exact_mod_cast hsupportNat
      _ ≤ ∑ i : Fin (k - 1),
          alpha * ((D.parts i).card : ℝ) := hmain
      _ = alpha * ∑ i : Fin (k - 1), ((D.parts i).card : ℝ) := by
        rw [Finset.mul_sum]
      _ = alpha * (D.support.card : ℝ) := by
        congr 1
        exact_mod_cast D.card_support.symm
      _ ≤ alpha * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hsupportCard halpha
  have hsparseDegreeNat :
      degreeInFinset T v D.sparse ≤ D.sparse.card := by
    unfold degreeInFinset
    exact Finset.card_filter_le _ _
  have hsparseDegree :
      (degreeInFinset T v D.sparse : ℝ) ≤
        delta * (n : ℝ) / 2 := by
    exact (by exact_mod_cast hsparseDegreeNat :
      (degreeInFinset T v D.sparse : ℝ) ≤ D.sparse.card) |>.trans hsparse
  calc
    (degreeInFinset T v Finset.univ : ℝ) =
        (degreeInFinset T v D.support : ℝ) +
          (degreeInFinset T v D.sparse : ℝ) := by
      exact_mod_cast hsplitNat.symm
    _ ≤ alpha * (n : ℝ) + delta * (n : ℝ) / 2 :=
      add_le_add hsupportDegree hsparseDegree
    _ ≤ (alpha + delta) * (n : ℝ) := by
      have hn : (0 : ℝ) ≤ n := by positivity
      nlinarith [mul_nonneg hdelta hn]

/-! ## The finite low-support family -/

/-- Support-incident graphs of matching number `h`, with the geometric edge
locations of a combined defect pattern and low degree into every main part. -/
def supercriticalLowSupportPatternFinset
    {n : ℕ} (D : SupercriticalDivision k (Fin n))
    (alpha : ℝ) (h : ℕ) : Finset (SimpleGraph (Fin n)) := by
  classical
  exact Finset.univ.filter fun T ↦
    supercriticalSupportIncidentGraph D T = T ∧
      supercriticalMatchingNumber D T = h ∧
      (∀ i j : Fin (k - 1), i ≠ j →
        ∀ x ∈ D.parts i, ∀ y ∈ D.parts j, ¬ T.Adj x y) ∧
      ∀ v : Fin n, ∀ i : Fin (k - 1),
        HasLowDegreeInPart T alpha D v i

@[simp] theorem mem_supercriticalLowSupportPatternFinset
    {n : ℕ} {D : SupercriticalDivision k (Fin n)}
    {alpha : ℝ} {h : ℕ} {T : SimpleGraph (Fin n)} :
    T ∈ supercriticalLowSupportPatternFinset D alpha h ↔
      supercriticalSupportIncidentGraph D T = T ∧
      supercriticalMatchingNumber D T = h ∧
      (∀ i j : Fin (k - 1), i ≠ j →
        ∀ x ∈ D.parts i, ∀ y ∈ D.parts j, ¬ T.Adj x y) ∧
      ∀ v : Fin n, ∀ i : Fin (k - 1),
        HasLowDegreeInPart T alpha D v i := by
  classical
  simp [supercriticalLowSupportPatternFinset]

/-- The support-incident part of a combined defect graph belongs to the
abstract low-support family as soon as its low-degree conclusion is known. -/
theorem supercriticalSupportIncidentGraph_mem_lowSupportPattern
    {n : ℕ} (G : SimpleGraph (Fin n))
    (D : SupercriticalDivision k (Fin n)) (alpha : ℝ)
    (hlow : ∀ v : Fin n, ∀ i : Fin (k - 1),
      HasLowDegreeInPart (combinedSupercriticalDefectGraph G D) alpha D v i) :
    supercriticalSupportIncidentGraph D
        (combinedSupercriticalDefectGraph G D) ∈
      supercriticalLowSupportPatternFinset D alpha
        (supercriticalMatchingNumber D
          (combinedSupercriticalDefectGraph G D)) := by
  rw [mem_supercriticalLowSupportPatternFinset]
  refine ⟨supercriticalSupportIncidentGraph_idem D _,
    supercriticalMatchingNumber_supportIncident D _, ?_, ?_⟩
  · intro i j hij x hx y hy
    exact supercriticalSupportIncidentGraph_not_adj_of_mem_distinct_parts_combined
      G D hij hx hy
  · intro v i
    unfold HasLowDegreeInPart at hlow ⊢
    have hmono := degreeInFinset_graph_mono
      (supercriticalSupportIncidentGraph_le D
        (combinedSupercriticalDefectGraph G D)) v (D.parts i)
    exact lt_of_le_of_lt (by exact_mod_cast hmono) (hlow v i)

/-- Robust geometric edge bound for the low support-pattern family.  The
constant is independent of `n`, the division, and the pattern (and is in fact
the absolute constant `2`). -/
theorem supercriticalSupportPattern_edgeCount_le
    {n : ℕ} (D : SupercriticalDivision k (Fin n))
    {alpha delta : ℝ} {h : ℕ} {T : SimpleGraph (Fin n)}
    (halpha : 0 ≤ alpha) (hdelta : 0 ≤ delta)
    (hsparse : (D.sparse.card : ℝ) ≤ delta * (n : ℝ) / 2)
    (hT : T ∈ supercriticalLowSupportPatternFinset D alpha h) :
    ((finiteGraphEdges T).card : ℝ) ≤
      2 * (h : ℝ) * (alpha + delta) * (n : ℝ) := by
  let C := supercriticalCanonicalMatchingEndpoints D T
  have hmem := mem_supercriticalLowSupportPatternFinset.mp hT
  have hcover : T.IsVertexCover (C : Set (Fin n)) := by
    rw [← hmem.1]
    exact supercriticalCanonicalMatchingEndpoints_vertexCover D T
  have hedgeNat :=
    card_edgeFinset_le_sum_degreeInFinset_of_vertexCover T C hcover
  have hedgeEq : finiteGraphEdges T = T.edgeFinset := by
    ext e
    simp [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  have hdegree (v : Fin n) :
      (degreeInFinset T v Finset.univ : ℝ) ≤
        (alpha + delta) * (n : ℝ) :=
    supercriticalSupportPattern_degree_real_le D T halpha hdelta
      hmem.2.2.2 hsparse v
  have hcard : C.card = 2 * h := by
    simpa [C, hmem.2.1] using
      card_supercriticalCanonicalMatchingEndpoints D T
  calc
    ((finiteGraphEdges T).card : ℝ) = (T.edgeFinset.card : ℝ) := by
      rw [hedgeEq]
    _ ≤ (∑ v ∈ C, degreeInFinset T v Finset.univ : ℕ) := by
      exact_mod_cast hedgeNat
    _ = ∑ v ∈ C, (degreeInFinset T v Finset.univ : ℝ) := by
      simp
    _ ≤ ∑ _v ∈ C, (alpha + delta) * (n : ℝ) := by
      exact Finset.sum_le_sum fun v _hv ↦ hdegree v
    _ = 2 * (h : ℝ) * (alpha + delta) * (n : ℝ) := by
      simp [hcard]
      <;> ring

/-! ## A finite cover-and-neighborhood encoding -/

/-- Subsets of `U` having cardinality at most `b`. -/
def finsetSubsetsAtMost {X : Type*} [DecidableEq X]
    (U : Finset X) (b : ℕ) : Finset (Finset X) :=
  (Finset.range (b + 1)).biUnion fun j ↦ U.powersetCard j

@[simp] theorem mem_finsetSubsetsAtMost
    {X : Type*} [DecidableEq X] {U A : Finset X} {b : ℕ} :
    A ∈ finsetSubsetsAtMost U b ↔ A ⊆ U ∧ A.card ≤ b := by
  constructor
  · rw [finsetSubsetsAtMost, Finset.mem_biUnion]
    rintro ⟨j, hj, hA⟩
    have hAj := Finset.mem_powersetCard.mp hA
    exact ⟨hAj.1, by simpa [hAj.2] using (Finset.mem_range.mp hj)⟩
  · rintro ⟨hAU, hAb⟩
    rw [finsetSubsetsAtMost, Finset.mem_biUnion]
    exact ⟨A.card, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hAb),
      Finset.mem_powersetCard.mpr ⟨hAU, rfl⟩⟩

@[simp] theorem card_finsetSubsetsAtMost
    {X : Type*} [DecidableEq X] (U : Finset X) (b : ℕ) :
    (finsetSubsetsAtMost U b).card = hammingBallVolume U.card b := by
  classical
  rw [finsetSubsetsAtMost, Finset.card_biUnion]
  · simp [hammingBallVolume]
  · intro i hi j hj hij
    change Disjoint (U.powersetCard i) (U.powersetCard j)
    rw [Finset.disjoint_left]
    intro A hAi hAj
    have hiCard := (Finset.mem_powersetCard.mp hAi).2
    have hjCard := (Finset.mem_powersetCard.mp hAj).2
    exact hij (hiCard.symm.trans hjCard)

/-- Oriented neighborhoods of the canonical endpoint cover. -/
def supercriticalSupportNeighborhoodCode
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    Finset (V × V) := by
  classical
  exact (supercriticalCanonicalMatchingEndpoints D T).biUnion fun v ↦
    ((Finset.univ.filter fun w ↦ T.Adj v w).image fun w ↦ (v, w))

theorem supercriticalSupportNeighborhoodCode_subset
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    supercriticalSupportNeighborhoodCode D T ⊆
      supercriticalCanonicalMatchingEndpoints D T ×ˢ
        (Finset.univ : Finset V) := by
  intro p hp
  rw [supercriticalSupportNeighborhoodCode, Finset.mem_biUnion] at hp
  obtain ⟨v, hv, hp⟩ := hp
  rw [Finset.mem_image] at hp
  obtain ⟨w, hw, rfl⟩ := hp
  simp [hv]

@[simp] theorem mem_supercriticalSupportNeighborhoodCode
    (D : SupercriticalDivision k V) (T : SimpleGraph V) (x y : V) :
    (x, y) ∈ supercriticalSupportNeighborhoodCode D T ↔
      x ∈ supercriticalCanonicalMatchingEndpoints D T ∧ T.Adj x y := by
  classical
  simp [supercriticalSupportNeighborhoodCode]

theorem card_supercriticalSupportNeighborhoodCode
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    (supercriticalSupportNeighborhoodCode D T).card =
      ∑ v ∈ supercriticalCanonicalMatchingEndpoints D T,
        degreeInFinset T v Finset.univ := by
  classical
  rw [supercriticalSupportNeighborhoodCode, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro v _hv
    rw [Finset.card_image_of_injective]
    · rfl
    · exact fun _ _ h ↦ congrArg Prod.snd h
  · intro v _hv w _hw hvw
    change Disjoint
      ((Finset.univ.filter fun x ↦ T.Adj v x).image fun x ↦ (v, x))
      ((Finset.univ.filter fun x ↦ T.Adj w x).image fun x ↦ (w, x))
    rw [Finset.disjoint_left]
    intro p hpv hpw
    rw [Finset.mem_image] at hpv hpw
    obtain ⟨a, _ha, rfl⟩ := hpv
    obtain ⟨b, _hb, hab⟩ := hpw
    exact hvw (congrArg Prod.fst hab).symm

/-- The cover together with all its oriented neighborhoods. -/
def supercriticalSupportPatternEncoding
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    Σ _C : Finset V, Finset (V × V) :=
  ⟨supercriticalCanonicalMatchingEndpoints D T,
    supercriticalSupportNeighborhoodCode D T⟩

/-- On support-fixed graphs, the canonical cover and its neighborhoods
determine every edge. -/
theorem supercriticalSupportPatternEncoding_injectiveOn
    (D : SupercriticalDivision k V) :
    Set.InjOn (supercriticalSupportPatternEncoding D)
      {T : SimpleGraph V | supercriticalSupportIncidentGraph D T = T} := by
  intro T hT U hU hcode
  have hcoverEq : supercriticalCanonicalMatchingEndpoints D T =
      supercriticalCanonicalMatchingEndpoints D U :=
    congrArg Sigma.fst hcode
  have hneighborhoodEq : supercriticalSupportNeighborhoodCode D T =
      supercriticalSupportNeighborhoodCode D U :=
    congrArg (fun z : Σ _C : Finset V, Finset (V × V) ↦ z.2) hcode
  have hcoverT : T.IsVertexCover
      (supercriticalCanonicalMatchingEndpoints D T : Set V) := by
    change supercriticalSupportIncidentGraph D T = T at hT
    have hcover := supercriticalCanonicalMatchingEndpoints_vertexCover D T
    rw [hT] at hcover
    exact hcover
  apply SimpleGraph.ext
  funext x y
  apply propext
  constructor
  · intro hxy
    rcases hcoverT hxy with hx | hy
    · have hmem : (x, y) ∈ supercriticalSupportNeighborhoodCode D T :=
        (mem_supercriticalSupportNeighborhoodCode D T x y).mpr ⟨hx, hxy⟩
      have hmem' : (x, y) ∈ supercriticalSupportNeighborhoodCode D U := by
        rw [← hneighborhoodEq]
        exact hmem
      exact (mem_supercriticalSupportNeighborhoodCode D U x y).mp hmem' |>.2
    · have hmem : (y, x) ∈ supercriticalSupportNeighborhoodCode D T :=
        (mem_supercriticalSupportNeighborhoodCode D T y x).mpr
          ⟨hy, T.adj_comm y x |>.mpr hxy⟩
      have hmem' : (y, x) ∈ supercriticalSupportNeighborhoodCode D U := by
        rw [← hneighborhoodEq]
        exact hmem
      exact U.adj_comm y x |>.mp
        ((mem_supercriticalSupportNeighborhoodCode D U y x).mp hmem' |>.2)
  · intro hxy
    have hcoverU : U.IsVertexCover
        (supercriticalCanonicalMatchingEndpoints D U : Set V) := by
      change supercriticalSupportIncidentGraph D U = U at hU
      have hcover := supercriticalCanonicalMatchingEndpoints_vertexCover D U
      rw [hU] at hcover
      exact hcover
    rcases hcoverU hxy with hx | hy
    · have hmem : (x, y) ∈ supercriticalSupportNeighborhoodCode D U :=
        (mem_supercriticalSupportNeighborhoodCode D U x y).mpr ⟨hx, hxy⟩
      have hmem' : (x, y) ∈ supercriticalSupportNeighborhoodCode D T := by
        rw [hneighborhoodEq]
        exact hmem
      exact (mem_supercriticalSupportNeighborhoodCode D T x y).mp hmem' |>.2
    · have hmem : (y, x) ∈ supercriticalSupportNeighborhoodCode D U :=
        (mem_supercriticalSupportNeighborhoodCode D U y x).mpr
          ⟨hy, U.adj_comm y x |>.mpr hxy⟩
      have hmem' : (y, x) ∈ supercriticalSupportNeighborhoodCode D T := by
        rw [hneighborhoodEq]
        exact hmem
      exact T.adj_comm y x |>.mp
        ((mem_supercriticalSupportNeighborhoodCode D T y x).mp hmem' |>.2)

/-- The finite target code space with cover size `2h` and total oriented
neighborhood size at most `2hb`. -/
def supercriticalSupportPatternCodeFinset
    {n : ℕ} (h b : ℕ) :
    Finset (Σ _C : Finset (Fin n), Finset (Fin n × Fin n)) :=
  (Finset.univ.powersetCard (2 * h)).sigma fun C ↦
    finsetSubsetsAtMost
      (C ×ˢ (Finset.univ : Finset (Fin n))) (2 * h * b)

@[simp] theorem card_supercriticalSupportPatternCodeFinset
    {n : ℕ} (h b : ℕ) :
    (supercriticalSupportPatternCodeFinset (n := n) h b).card =
      n.choose (2 * h) * hammingBallVolume (2 * h * n) (2 * h * b) := by
  classical
  rw [supercriticalSupportPatternCodeFinset, Finset.card_sigma]
  have hconst : ∀ C ∈
      (Finset.univ : Finset (Fin n)).powersetCard (2 * h),
      (finsetSubsetsAtMost
        (C ×ˢ (Finset.univ : Finset (Fin n))) (2 * h * b)).card =
          hammingBallVolume (2 * h * n) (2 * h * b) := by
    intro C hC
    rw [card_finsetSubsetsAtMost, Finset.card_product]
    have hCcard := (Finset.mem_powersetCard.mp hC).2
    simp [hCcard, Nat.mul_assoc]
  rw [Finset.sum_const_nat hconst, Finset.card_powersetCard]
  simp

theorem supercriticalSupportPatternEncoding_mem_codeFinset
    {n : ℕ} {D : SupercriticalDivision k (Fin n)}
    {T : SimpleGraph (Fin n)} {h b : ℕ}
    (hmatching : supercriticalMatchingNumber D T = h)
    (hdegree : ∀ v : Fin n, degreeInFinset T v Finset.univ ≤ b) :
    supercriticalSupportPatternEncoding D T ∈
      supercriticalSupportPatternCodeFinset (n := n) h b := by
  classical
  change ⟨supercriticalCanonicalMatchingEndpoints D T,
      supercriticalSupportNeighborhoodCode D T⟩ ∈
    supercriticalSupportPatternCodeFinset (n := n) h b
  rw [supercriticalSupportPatternCodeFinset, Finset.mem_sigma]
  constructor
  · rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [card_supercriticalCanonicalMatchingEndpoints, hmatching]
  · rw [mem_finsetSubsetsAtMost]
    constructor
    · exact supercriticalSupportNeighborhoodCode_subset D T
    · rw [card_supercriticalSupportNeighborhoodCode]
      calc
        ∑ v ∈ supercriticalCanonicalMatchingEndpoints D T,
            degreeInFinset T v Finset.univ ≤
            ∑ _v ∈ supercriticalCanonicalMatchingEndpoints D T, b := by
          exact Finset.sum_le_sum fun v _hv ↦ hdegree v
        _ = 2 * h * b := by simp [hmatching]

/-- Combinatorial support-pattern count from a uniform degree bound. -/
theorem card_supercriticalLowSupportPatternFinset_le
    {n : ℕ} (D : SupercriticalDivision k (Fin n))
    (alpha : ℝ) (h b : ℕ)
    (hdegree : ∀ T ∈ supercriticalLowSupportPatternFinset D alpha h,
      ∀ v : Fin n, degreeInFinset T v Finset.univ ≤ b) :
    (supercriticalLowSupportPatternFinset D alpha h).card ≤
      n.choose (2 * h) * hammingBallVolume (2 * h * n) (2 * h * b) := by
  classical
  let F := supercriticalLowSupportPatternFinset D alpha h
  let encode := supercriticalSupportPatternEncoding D
  have hinj : Set.InjOn encode (F : Set (SimpleGraph (Fin n))) := by
    apply (supercriticalSupportPatternEncoding_injectiveOn D).mono
    intro T hT
    exact (mem_supercriticalLowSupportPatternFinset.mp hT).1
  have hsubset : F.image encode ⊆
      supercriticalSupportPatternCodeFinset (n := n) h b := by
    intro code hcode
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hcode
    exact supercriticalSupportPatternEncoding_mem_codeFinset
      (mem_supercriticalLowSupportPatternFinset.mp hT).2.1
      (hdegree T hT)
  rw [← Finset.card_image_iff.mpr hinj,
    ← card_supercriticalSupportPatternCodeFinset h b]
  exact Finset.card_le_card hsubset

/-- Explicit entropy form of the support-pattern count.  The integer `b` is
a uniform whole-degree budget.  The final hypothesis is deliberately scalar:
it isolates the only application-specific comparison between that discrete
budget and the chosen small parameters.  All constants in the conclusion are
uniform in `n`, `D`, and the support pattern. -/
theorem card_supercriticalLowSupportPatternFinset_real_le_exp
    {n : ℕ} (D : SupercriticalDivision k (Fin n))
    (alpha delta : ℝ) (h b : ℕ)
    (hn : 0 < n) (hh : 0 < h) (hb : 0 < b) (hhalf : 2 * b ≤ n)
    (hdegree : ∀ T ∈ supercriticalLowSupportPatternFinset D alpha h,
      ∀ v : Fin n, degreeInFinset T v Finset.univ ≤ b)
    (hentropy : binaryEntropy ((b : ℝ) / (n : ℝ)) ≤
      binaryEntropy (3 * alpha) + delta) :
    ((supercriticalLowSupportPatternFinset D alpha h).card : ℝ) ≤
      Real.exp
        (2 * (h : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) +
          (2 * (h : ℝ) * (n : ℝ)) *
            (binaryEntropy (3 * alpha) + delta) * Real.log 2) := by
  let N := 2 * h * n
  let r := 2 * h * b
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hhalfN : 2 * r ≤ N := by
    dsimp [r, N]
    calc
      2 * (2 * h * b) = (2 * h) * (2 * b) := by ac_rfl
      _ ≤ (2 * h) * n := Nat.mul_le_mul_left (2 * h) hhalf
      _ = 2 * h * n := by omega
  have hratio : (r : ℝ) / (N : ℝ) = (b : ℝ) / (n : ℝ) := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    dsimp [r, N]
    push_cast
    field_simp
  have hlog2 := log2_hammingBallVolume_le N r hr hhalfN
  have hlogVolume :
      Real.log (hammingBallVolume N r : ℝ) ≤
        (N : ℝ) * (binaryEntropy (3 * alpha) + delta) * Real.log 2 := by
    rw [log2] at hlog2
    have hnatural := (div_le_iff₀ realLogTwo_pos).mp hlog2
    rw [hratio] at hnatural
    calc
      Real.log (hammingBallVolume N r : ℝ) ≤
          ((N : ℝ) * binaryEntropy ((b : ℝ) / (n : ℝ))) *
            Real.log 2 := hnatural
      _ ≤ ((N : ℝ) * (binaryEntropy (3 * alpha) + delta)) *
          Real.log 2 := by
        gcongr
      _ = (N : ℝ) * (binaryEntropy (3 * alpha) + delta) *
          Real.log 2 := rfl
  have hvolumePos : 0 < (hammingBallVolume N r : ℝ) := by
    exact_mod_cast hammingBallVolume_pos N r
  have hvolume : (hammingBallVolume N r : ℝ) ≤
      Real.exp ((2 * (h : ℝ) * (n : ℝ)) *
        (binaryEntropy (3 * alpha) + delta) * Real.log 2) := by
    calc
      (hammingBallVolume N r : ℝ) =
          Real.exp (Real.log (hammingBallVolume N r : ℝ)) :=
        (Real.exp_log hvolumePos).symm
      _ ≤ Real.exp ((N : ℝ) *
          (binaryEntropy (3 * alpha) + delta) * Real.log 2) :=
        Real.exp_le_exp.mpr hlogVolume
      _ = Real.exp ((2 * (h : ℝ) * (n : ℝ)) *
          (binaryEntropy (3 * alpha) + delta) * Real.log 2) := by
        congr 1
        dsimp [N]
        push_cast
        ring
  have hchooseNat : n.choose (2 * h) ≤ (n + 1) ^ (2 * h) :=
    (Nat.choose_le_pow n (2 * h)).trans
      (Nat.pow_le_pow_left n.le_succ (2 * h))
  have hbasePos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hchoose : (n.choose (2 * h) : ℝ) ≤
      Real.exp (2 * (h : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) := by
    calc
      (n.choose (2 * h) : ℝ) ≤ (((n + 1) ^ (2 * h) : ℕ) : ℝ) := by
        exact_mod_cast hchooseNat
      _ = (((n + 1 : ℕ) : ℝ)) ^ (2 * h) := by norm_num
      _ = (Real.exp (Real.log ((n + 1 : ℕ) : ℝ))) ^ (2 * h) := by
        rw [Real.exp_log hbasePos]
      _ = Real.exp ((2 * h : ℕ) * Real.log ((n + 1 : ℕ) : ℝ)) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp
          (2 * (h : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) := by
        congr 1
        push_cast
        rfl
  have hcardNat := card_supercriticalLowSupportPatternFinset_le
    D alpha h b hdegree
  calc
    ((supercriticalLowSupportPatternFinset D alpha h).card : ℝ) ≤
        ((n.choose (2 * h) * hammingBallVolume (2 * h * n)
          (2 * h * b) : ℕ) : ℝ) := by
      exact_mod_cast hcardNat
    _ = (n.choose (2 * h) : ℝ) * (hammingBallVolume N r : ℝ) := by
      simp [N, r]
    _ ≤ Real.exp (2 * (h : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) *
        Real.exp ((2 * (h : ℝ) * (n : ℝ)) *
          (binaryEntropy (3 * alpha) + delta) * Real.log 2) := by
      exact mul_le_mul hchoose hvolume (by positivity) (by positivity)
    _ = Real.exp
        (2 * (h : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) +
          (2 * (h : ℝ) * (n : ℝ)) *
            (binaryEntropy (3 * alpha) + delta) * Real.log 2) := by
      rw [Real.exp_add]

end InducedStars
