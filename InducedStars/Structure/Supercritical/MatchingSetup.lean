import DenseGraph.Combinatorics.Matching
import InducedStars.Structure.Supercritical.Closeness
import InducedStars.Structure.Supercritical.CountingSetup
import Mathlib.Tactic

/-!
# Deterministic setup for the supercritical matching penalty

This module isolates the support-incident part of a combined defect pattern,
selects and thins a canonical maximum matching, and records its unique
homogeneous location.  It also defines the exact fixed-defect/profile fiber
used by the subsequent probability argument.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

noncomputable local instance matchingSetupEdgeSetFintype
    (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

/-! ## The support-incident defect graph -/

/-- The part of `T` consisting of edges with at least one endpoint in the
main support of `D`.  This is the paper's graph `T[V(Π),V]`. -/
def supercriticalSupportIncidentGraph
    (D : SupercriticalDivision k V) (T : SimpleGraph V) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y ↦
    T.Adj x y ∧ (x ∈ D.support ∨ y ∈ D.support)

@[simp] theorem supercriticalSupportIncidentGraph_adj
    (D : SupercriticalDivision k V) (T : SimpleGraph V) (x y : V) :
    (supercriticalSupportIncidentGraph D T).Adj x y ↔
      T.Adj x y ∧ (x ∈ D.support ∨ y ∈ D.support) := by
  rw [supercriticalSupportIncidentGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact ⟨(T.adj_comm y x).mp h.1, h.2.symm⟩
  · intro h
    exact ⟨T.ne_of_adj h.1, Or.inl h⟩

theorem supercriticalSupportIncidentGraph_le
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    supercriticalSupportIncidentGraph D T ≤ T := by
  intro x y hxy
  exact (supercriticalSupportIncidentGraph_adj D T x y).mp hxy |>.1

theorem supercriticalSupportIncidentGraph_edgeFinset_subset
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    (supercriticalSupportIncidentGraph D T).edgeFinset ⊆ T.edgeFinset := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
        supercriticalSupportIncidentGraph_le D T
          (by simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he)

theorem supercriticalSupportIncidentGraph_not_adj_of_mem_sparse
    (D : SupercriticalDivision k V) (T : SimpleGraph V)
    {x y : V} (hx : x ∈ D.sparse) (hy : y ∈ D.sparse) :
    ¬(supercriticalSupportIncidentGraph D T).Adj x y := by
  rw [supercriticalSupportIncidentGraph_adj]
  have hx' := SupercriticalDivision.mem_sparse.mp hx
  have hy' := SupercriticalDivision.mem_sparse.mp hy
  tauto

theorem supercriticalSupportIncidentGraph_adj_of_mem_same_part_combined
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (i : Fin (k - 1)) {x y : V}
    (hx : x ∈ D.parts i) (hy : y ∈ D.parts i) :
    (supercriticalSupportIncidentGraph D
      (combinedSupercriticalDefectGraph G D)).Adj x y ↔
        x ≠ y ∧ ¬G.Adj x y := by
  rw [supercriticalSupportIncidentGraph_adj,
    combinedSupercriticalDefectGraph_adj_of_mem_same_part G D i hx hy]
  simp [D.part_subset_support i hx]

theorem supercriticalSupportIncidentGraph_adj_support_sparse_combined
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    {x y : V} (hx : x ∈ D.support) (hy : y ∈ D.sparse) :
    (supercriticalSupportIncidentGraph D
      (combinedSupercriticalDefectGraph G D)).Adj x y ↔ G.Adj x y := by
  rw [supercriticalSupportIncidentGraph_adj,
    combinedSupercriticalDefectGraph_adj_support_sparse G D hx hy]
  simp [hx]

theorem supercriticalSupportIncidentGraph_not_adj_of_mem_distinct_parts_combined
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    {i j : Fin (k - 1)} (hij : i ≠ j) {x y : V}
    (hx : x ∈ D.parts i) (hy : y ∈ D.parts j) :
    ¬(supercriticalSupportIncidentGraph D
      (combinedSupercriticalDefectGraph G D)).Adj x y := by
  intro h
  exact combinedSupercriticalDefectGraph_not_adj_of_mem_distinct_parts
    G D hij hx hy
    ((supercriticalSupportIncidentGraph_adj D _ x y).mp h).1

/-! ## Canonical maximum matching -/

/-- The canonical maximum matching in the support-incident defect graph. -/
def supercriticalCanonicalMatching
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    (supercriticalSupportIncidentGraph D T).Subgraph :=
  DenseGraph.canonicalMaximumMatching (supercriticalSupportIncidentGraph D T)

/-- The paper's matching number `h_D(T)`. -/
def supercriticalMatchingNumber
    (D : SupercriticalDivision k V) (T : SimpleGraph V) : ℕ :=
  DenseGraph.matchingNumber (supercriticalSupportIncidentGraph D T)

/-- The finite edge family of the canonical support-incident matching. -/
def supercriticalCanonicalMatchingEdges
    (D : SupercriticalDivision k V) (T : SimpleGraph V) : Finset (Sym2 V) :=
  DenseGraph.matchingEdgeFinset (supercriticalCanonicalMatching D T)

theorem supercriticalCanonicalMatching_isMatching
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    (supercriticalCanonicalMatching D T).IsMatching :=
  DenseGraph.canonicalMaximumMatching_isMatching _

@[simp] theorem supercriticalCanonicalMatching_card
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    (supercriticalCanonicalMatchingEdges D T).card =
      supercriticalMatchingNumber D T := by
  rw [supercriticalCanonicalMatchingEdges,
    DenseGraph.card_matchingEdgeFinset]
  rfl

theorem supercriticalCanonicalMatchingEdges_subset
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    supercriticalCanonicalMatchingEdges D T ⊆
      (supercriticalSupportIncidentGraph D T).edgeFinset := by
  intro e he
  rw [supercriticalCanonicalMatchingEdges,
    DenseGraph.mem_matchingEdgeFinset] at he
  rw [SimpleGraph.mem_edgeFinset]
  exact (supercriticalCanonicalMatching D T).edgeSet_subset he

theorem supercriticalCanonicalMatchingEdges_subset_pattern
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    supercriticalCanonicalMatchingEdges D T ⊆ T.edgeFinset :=
  (supercriticalCanonicalMatchingEdges_subset D T).trans
    (supercriticalSupportIncidentGraph_edgeFinset_subset D T)

/-- Every ordinary defect edge belongs to the support-incident part of the
combined defect graph. -/
theorem finiteGraphEdges_supercriticalDefectGraph_subset_supportIncident
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    finiteGraphEdges (supercriticalDefectGraph G D) ⊆
      (supercriticalSupportIncidentGraph D
        (combinedSupercriticalDefectGraph G D)).edgeFinset := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hdefect : (supercriticalDefectGraph G D).Adj x y := by
        simpa only [mem_finiteGraphEdges, SimpleGraph.mem_edgeSet] using he
      have hcombined : (combinedSupercriticalDefectGraph G D).Adj x y :=
        (combinedSupercriticalDefectGraph_adj G D x y).mpr (Or.inl hdefect)
      have hsupport : x ∈ D.support ∨ y ∈ D.support := by
        by_cases hx : x ∈ D.support
        · exact Or.inl hx
        · by_cases hy : y ∈ D.support
          · exact Or.inr hy
          · have hxs : x ∈ D.sparse := by simpa using hx
            have hys : y ∈ D.sparse := by simpa using hy
            exact False.elim
              (supercriticalDefectGraph_not_adj_of_mem_sparse
                G D hxs hys hdefect)
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        supercriticalSupportIncidentGraph_adj] using ⟨hcombined, hsupport⟩

theorem supercriticalMatchingNumber_pos_of_adj
    (D : SupercriticalDivision k V) (T : SimpleGraph V) {x y : V}
    (hxy : (supercriticalSupportIncidentGraph D T).Adj x y) :
    0 < supercriticalMatchingNumber D T := by
  have hle := DenseGraph.canonicalMaximumMatching_maximal_card
    (supercriticalSupportIncidentGraph D T)
    ((supercriticalSupportIncidentGraph D T).subgraphOfAdj hxy)
    (SimpleGraph.Subgraph.IsMatching.subgraphOfAdj hxy)
  rw [SimpleGraph.edgeSet_subgraphOfAdj, Set.ncard_singleton] at hle
  change 0 < (DenseGraph.canonicalMaximumMatching
    (supercriticalSupportIncidentGraph D T)).edgeSet.ncard
  exact Order.one_le_iff_pos.mp hle

/-- A displayed defective pattern has positive support-incident matching
number; sparse-induced edges alone never supply the required witness. -/
theorem supercriticalMatchingNumber_pos_of_mem_pattern
    {k n : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D) :
    0 < supercriticalMatchingNumber D T := by
  obtain ⟨G, hG, hGT⟩ :=
    mem_supercriticalCombinedDefectPatternFinset.mp hT
  have hmem := mem_supercriticalDivisionDefectGraphFinset.mp hG
  have hdivision := hmem.2.1
  obtain ⟨e, he⟩ := hmem.2.2
  have heDefect : e ∈ finiteGraphEdges (supercriticalDefectGraph G D) := by
    simpa [canonicalSupercriticalDefectGraph, hdivision] using he
  have heSupport :=
    finiteGraphEdges_supercriticalDefectGraph_subset_supportIncident G D heDefect
  have hcombined : combinedSupercriticalDefectGraph G D = T := by
    simpa [canonicalCombinedDefectGraph, hdivision] using hGT
  rw [hcombined] at heSupport
  induction e using Sym2.inductionOn with
  | _ x y =>
      apply supercriticalMatchingNumber_pos_of_adj D T
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
        heSupport

/-! ## The `2(k - 1)` matching locations -/

/-- An edge incident with the main support is either internal to one main
part or joins that main part to the sparse set. -/
inductive SupercriticalMatchingLocation (k : ℕ) where
  | internal (part : Fin (k - 1))
  | supportSparse (part : Fin (k - 1))
  deriving DecidableEq, Fintype

namespace SupercriticalMatchingLocation

/-- The symmetric predicate saying that an unordered edge has a prescribed
supercritical matching location. -/
def Contains (D : SupercriticalDivision k V) :
    SupercriticalMatchingLocation k → Sym2 V → Prop
  | .internal i =>
      Sym2.lift ⟨fun x y ↦ x ∈ D.parts i ∧ y ∈ D.parts i, by
        intro x y
        apply propext
        tauto⟩
  | .supportSparse i =>
      Sym2.lift ⟨fun x y ↦
        (x ∈ D.parts i ∧ y ∈ D.sparse) ∨
          (y ∈ D.parts i ∧ x ∈ D.sparse), by
        intro x y
        apply propext
        tauto⟩

instance (D : SupercriticalDivision k V)
    (loc : SupercriticalMatchingLocation k) (e : Sym2 V) :
    Decidable (loc.Contains D e) :=
  Classical.propDecidable _

@[simp] theorem contains_pair_internal
    (D : SupercriticalDivision k V) (i : Fin (k - 1)) (x y : V) :
    (internal i).Contains D s(x, y) ↔
      x ∈ D.parts i ∧ y ∈ D.parts i := by
  rfl

@[simp] theorem contains_pair_supportSparse
    (D : SupercriticalDivision k V) (i : Fin (k - 1)) (x y : V) :
    (supportSparse i).Contains D s(x, y) ↔
      (x ∈ D.parts i ∧ y ∈ D.sparse) ∨
        (y ∈ D.parts i ∧ x ∈ D.sparse) := by
  rfl

theorem contains_unique (D : SupercriticalDivision k V) {e : Sym2 V}
    {a b : SupercriticalMatchingLocation k}
    (ha : a.Contains D e) (hb : b.Contains D e) : a = b := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      cases a with
      | internal i =>
          cases b with
          | internal j =>
              simp only [contains_pair_internal] at ha hb
              have hij : i = j := D.mem_part_unique ha.1 hb.1
              simp [hij]
          | supportSparse j =>
              simp only [contains_pair_internal] at ha
              simp only [contains_pair_supportSparse] at hb
              rcases hb with hb | hb
              · exact False.elim
                  ((Finset.disjoint_left.mp (D.part_disjoint_sparse i))
                    ha.2 hb.2)
              · exact False.elim
                  ((Finset.disjoint_left.mp (D.part_disjoint_sparse i))
                    ha.1 hb.2)
      | supportSparse i =>
          cases b with
          | internal j =>
              simp only [contains_pair_supportSparse] at ha
              simp only [contains_pair_internal] at hb
              rcases ha with ha | ha
              · exact False.elim
                  ((Finset.disjoint_left.mp (D.part_disjoint_sparse j))
                    hb.2 ha.2)
              · exact False.elim
                  ((Finset.disjoint_left.mp (D.part_disjoint_sparse j))
                    hb.1 ha.2)
          | supportSparse j =>
              simp only [contains_pair_supportSparse] at ha hb
              rcases ha with ha | ha <;> rcases hb with hb | hb
              · have hij : i = j := D.mem_part_unique ha.1 hb.1
                simp [hij]
              · exact False.elim
                  ((Finset.disjoint_left.mp (D.part_disjoint_sparse i))
                    ha.1 hb.2)
              · exact False.elim
                  ((Finset.disjoint_left.mp (D.part_disjoint_sparse j))
                    hb.1 ha.2)
              · have hij : i = j := D.mem_part_unique ha.1 hb.1
                simp [hij]

end SupercriticalMatchingLocation

@[simp] theorem card_supercriticalMatchingLocation (k : ℕ) :
    Fintype.card (SupercriticalMatchingLocation k) = 2 * (k - 1) := by
  let e : SupercriticalMatchingLocation k ≃
      Fin (k - 1) ⊕ Fin (k - 1) :=
    { toFun := fun loc ↦ match loc with
        | .internal i => Sum.inl i
        | .supportSparse i => Sum.inr i
      invFun := fun loc ↦ match loc with
        | .inl i => .internal i
        | .inr i => .supportSparse i
      left_inv := by intro loc; cases loc <;> rfl
      right_inv := by intro loc; cases loc <;> rfl }
  calc
    Fintype.card (SupercriticalMatchingLocation k) =
        Fintype.card (Fin (k - 1) ⊕ Fin (k - 1)) :=
      Fintype.card_congr e
    _ = (k - 1) + (k - 1) := by simp
    _ = 2 * (k - 1) := by omega

/-- Every edge of the support-incident part of an actual combined defect
graph belongs to exactly one of the `2(k-1)` locations. -/
theorem existsUnique_supercriticalMatchingLocation_of_mem_combined
    (G : SimpleGraph V) (D : SupercriticalDivision k V) {e : Sym2 V}
    (he : e ∈ (supercriticalSupportIncidentGraph D
      (combinedSupercriticalDefectGraph G D)).edgeFinset) :
    ∃! loc : SupercriticalMatchingLocation k, loc.Contains D e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : (supercriticalSupportIncidentGraph D
          (combinedSupercriticalDefectGraph G D)).Adj x y := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      have hcombined :=
        (supercriticalSupportIncidentGraph_adj D _ x y).mp hxy |>.1
      rcases D.sparse_or_existsUnique_part x with hxs | ⟨i, hxi, _⟩
      · rcases D.sparse_or_existsUnique_part y with hys | ⟨j, hyj, _⟩
        · exact False.elim
            (supercriticalSupportIncidentGraph_not_adj_of_mem_sparse
              D _ hxs hys hxy)
        · refine ⟨.supportSparse j, ?_, ?_⟩
          · simp [hxs, hyj]
          · intro loc hloc
            exact SupercriticalMatchingLocation.contains_unique D hloc
              (by simp [hxs, hyj])
      · rcases D.sparse_or_existsUnique_part y with hys | ⟨j, hyj, _⟩
        · refine ⟨.supportSparse i, ?_, ?_⟩
          · simp [hxi, hys]
          · intro loc hloc
            exact SupercriticalMatchingLocation.contains_unique D hloc
              (by simp [hxi, hys])
        · have hij : i = j := by
            by_contra hij
            exact combinedSupercriticalDefectGraph_not_adj_of_mem_distinct_parts
              G D hij hxi hyj hcombined
          subst j
          refine ⟨.internal i, ?_, ?_⟩
          · simp [hxi, hyj]
          · intro loc hloc
            exact SupercriticalMatchingLocation.contains_unique D hloc
              (by simp [hxi, hyj])

/-- The previous geometry specialized to every displayed combined-defect
pattern. -/
theorem existsUnique_supercriticalMatchingLocation_of_mem_pattern
    {k n : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D) {e : Sym2 (Fin n)}
    (he : e ∈ (supercriticalSupportIncidentGraph D T).edgeFinset) :
    ∃! loc : SupercriticalMatchingLocation k, loc.Contains D e := by
  obtain ⟨G, hG, hGT⟩ :=
    mem_supercriticalCombinedDefectPatternFinset.mp hT
  have hdivision :=
    (mem_supercriticalDivisionDefectGraphFinset.mp hG).2.1
  have hcombined : combinedSupercriticalDefectGraph G D = T := by
    simpa [canonicalCombinedDefectGraph, hdivision] using hGT
  rw [← hcombined] at he
  exact existsUnique_supercriticalMatchingLocation_of_mem_combined G D he

/-! ## Canonical location assignment and its largest fiber -/

/-- A total, canonical location assignment.  On the relevant combined-defect
edges the existence branch is forced by the unique-location theorem; the
fallback only makes the definition total on arbitrary unordered pairs. -/
def supercriticalMatchingLocationOfEdge (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (e : Sym2 V) :
    SupercriticalMatchingLocation k :=
  if h : ∃ loc : SupercriticalMatchingLocation k, loc.Contains D e then
    Classical.choose h
  else
    .internal ⟨0, by omega⟩

theorem supercriticalMatchingLocationOfEdge_contains (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) {e : Sym2 V}
    (h : ∃ loc : SupercriticalMatchingLocation k, loc.Contains D e) :
    (supercriticalMatchingLocationOfEdge hk D e).Contains D e := by
  rw [supercriticalMatchingLocationOfEdge, dif_pos h]
  exact Classical.choose_spec h

theorem supercriticalMatchingLocationOfEdge_eq (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) {e : Sym2 V}
    {loc : SupercriticalMatchingLocation k} (hloc : loc.Contains D e) :
    supercriticalMatchingLocationOfEdge hk D e = loc := by
  exact SupercriticalMatchingLocation.contains_unique D
    (supercriticalMatchingLocationOfEdge_contains hk D ⟨loc, hloc⟩) hloc

/-- The fiber of the canonical maximum matching at one internal or
support--sparse location. -/
def matchingInLocation (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (T : SimpleGraph V) (loc : SupercriticalMatchingLocation k) :
    Finset (Sym2 V) :=
  (supercriticalCanonicalMatchingEdges D T).filter fun e ↦
    supercriticalMatchingLocationOfEdge hk D e = loc

@[simp] theorem mem_matchingInLocation (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (T : SimpleGraph V)
    (loc : SupercriticalMatchingLocation k) (e : Sym2 V) :
    e ∈ matchingInLocation hk D T loc ↔
      e ∈ supercriticalCanonicalMatchingEdges D T ∧
        supercriticalMatchingLocationOfEdge hk D e = loc := by
  simp [matchingInLocation]

theorem matchingInLocation_subset (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (T : SimpleGraph V)
    (loc : SupercriticalMatchingLocation k) :
    matchingInLocation hk D T loc ⊆
      supercriticalCanonicalMatchingEdges D T :=
  Finset.filter_subset _ _

/-- Each location fiber remains a finite edge matching in the
support-incident defect graph. -/
theorem matchingInLocation_isEdgeMatching (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (T : SimpleGraph V)
    (loc : SupercriticalMatchingLocation k) :
    DenseGraph.IsEdgeMatching (supercriticalSupportIncidentGraph D T)
      (matchingInLocation hk D T loc) := by
  have hmatching : DenseGraph.IsEdgeMatching
      (supercriticalSupportIncidentGraph D T)
      (supercriticalCanonicalMatchingEdges D T) := by
    simpa [supercriticalCanonicalMatchingEdges] using
      (DenseGraph.matchingEdgeFinset_isEdgeMatching
        (supercriticalCanonicalMatching_isMatching D T))
  exact hmatching.mono (matchingInLocation_subset hk D T loc)

theorem matchingInLocation_disjoint (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (T : SimpleGraph V)
    {a b : SupercriticalMatchingLocation k} (hab : a ≠ b) :
    Disjoint (matchingInLocation hk D T a)
      (matchingInLocation hk D T b) := by
  rw [Finset.disjoint_left]
  intro e hea heb
  exact hab ((mem_matchingInLocation hk D T a e).mp hea |>.2.symm.trans
    ((mem_matchingInLocation hk D T b e).mp heb |>.2))

/-- The union of all location fibers is literally the canonical maximum
matching edge family. -/
theorem biUnion_matchingInLocation_eq_canonicalMatchingEdges
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    Finset.univ.biUnion (matchingInLocation hk D T) =
      supercriticalCanonicalMatchingEdges D T := by
  ext e
  simp [matchingInLocation]

/-- The location fibers partition the canonical matching exactly. -/
theorem card_supercriticalCanonicalMatchingEdges_eq_sum_matchingInLocation
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    (supercriticalCanonicalMatchingEdges D T).card =
      ∑ loc : SupercriticalMatchingLocation k,
        (matchingInLocation hk D T loc).card := by
  simpa [matchingInLocation] using
    (Finset.card_eq_sum_card_fiberwise
      (s := supercriticalCanonicalMatchingEdges D T)
      (t := Finset.univ)
      (f := supercriticalMatchingLocationOfEdge hk D)
      (by intro e he; simp))

/-- A location whose fiber has maximum cardinality. -/
def dominantMatchingLocation (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    SupercriticalMatchingLocation k := by
  letI : Nonempty (SupercriticalMatchingLocation k) :=
    ⟨.internal ⟨0, by omega⟩⟩
  exact Classical.choose
    (Finset.exists_max_image Finset.univ
      (fun loc : SupercriticalMatchingLocation k ↦
        (matchingInLocation hk D T loc).card)
      Finset.univ_nonempty)

/-- The largest homogeneous fiber of the canonical maximum matching. -/
def dominantLocationMatching (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    Finset (Sym2 V) :=
  matchingInLocation hk D T (dominantMatchingLocation hk D T)

theorem matchingInLocation_card_le_dominant (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (T : SimpleGraph V)
    (loc : SupercriticalMatchingLocation k) :
    (matchingInLocation hk D T loc).card ≤
      (dominantLocationMatching hk D T).card := by
  letI : Nonempty (SupercriticalMatchingLocation k) :=
    ⟨.internal ⟨0, by omega⟩⟩
  have hmax := Classical.choose_spec
    (Finset.exists_max_image Finset.univ
      (fun a : SupercriticalMatchingLocation k ↦
        (matchingInLocation hk D T a).card)
      Finset.univ_nonempty)
  exact hmax.2 loc (by simp)

theorem dominantLocationMatching_subset (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    dominantLocationMatching hk D T ⊆
      supercriticalCanonicalMatchingEdges D T :=
  matchingInLocation_subset hk D T _

/-- The largest one of the `2(k-1)` fibers controls the whole matching. -/
theorem supercriticalMatchingNumber_le_two_mul_sub_one_mul_dominant
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    supercriticalMatchingNumber D T ≤
      2 * (k - 1) * (dominantLocationMatching hk D T).card := by
  rw [← supercriticalCanonicalMatching_card,
    card_supercriticalCanonicalMatchingEdges_eq_sum_matchingInLocation hk D T]
  calc
    (∑ loc : SupercriticalMatchingLocation k,
        (matchingInLocation hk D T loc).card) ≤
        ∑ _loc : SupercriticalMatchingLocation k,
          (dominantLocationMatching hk D T).card := by
      exact Finset.sum_le_sum fun loc _ ↦
        matchingInLocation_card_le_dominant hk D T loc
    _ = 2 * (k - 1) * (dominantLocationMatching hk D T).card := by
      simp

/-! ## A canonical half-sized homogeneous matching -/

/-- A fixed subset containing the ceiling of half of the dominant location
fiber.  This thinning leaves room for the later global orientation choice. -/
def selectedHomogeneousMatching (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    Finset (Sym2 V) :=
  Classical.choose
    (Finset.exists_subset_card_eq
      (s := dominantLocationMatching hk D T)
      (n := ((dominantLocationMatching hk D T).card + 1) / 2)
      (by omega))

theorem selectedHomogeneousMatching_subset_dominant (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    selectedHomogeneousMatching hk D T ⊆
      dominantLocationMatching hk D T :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := dominantLocationMatching hk D T)
      (n := ((dominantLocationMatching hk D T).card + 1) / 2)
      (by omega))).1

@[simp] theorem selectedHomogeneousMatching_card (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    (selectedHomogeneousMatching hk D T).card =
      ((dominantLocationMatching hk D T).card + 1) / 2 :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := dominantLocationMatching hk D T)
      (n := ((dominantLocationMatching hk D T).card + 1) / 2)
      (by omega))).2

theorem selectedHomogeneousMatching_subset (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    selectedHomogeneousMatching hk D T ⊆
      supercriticalCanonicalMatchingEdges D T :=
  (selectedHomogeneousMatching_subset_dominant hk D T).trans
    (dominantLocationMatching_subset hk D T)

theorem dominantLocationMatching_card_le_twice_selected (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    (dominantLocationMatching hk D T).card ≤
      2 * (selectedHomogeneousMatching hk D T).card := by
  rw [selectedHomogeneousMatching_card]
  omega

/-- The paper's deterministic loss `h ≤ 4(k-1)|M'|`. -/
theorem supercriticalMatchingNumber_le_four_mul_sub_one_mul_selected
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    supercriticalMatchingNumber D T ≤
      4 * (k - 1) * (selectedHomogeneousMatching hk D T).card := by
  calc
    supercriticalMatchingNumber D T ≤
        2 * (k - 1) * (dominantLocationMatching hk D T).card :=
      supercriticalMatchingNumber_le_two_mul_sub_one_mul_dominant hk D T
    _ ≤ 2 * (k - 1) *
        (2 * (selectedHomogeneousMatching hk D T).card) :=
      Nat.mul_le_mul_left _
        (dominantLocationMatching_card_le_twice_selected hk D T)
    _ = 4 * (k - 1) *
        (selectedHomogeneousMatching hk D T).card := by ring

theorem selectedHomogeneousMatching_edges_endpoint_disjoint
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) (T : SimpleGraph V)
    {e f : Sym2 V} (he : e ∈ selectedHomogeneousMatching hk D T)
    (hf : f ∈ selectedHomogeneousMatching hk D T) (hef : e ≠ f) :
    Disjoint (e : Set V) (f : Set V) := by
  have he' := selectedHomogeneousMatching_subset hk D T he
  have hf' := selectedHomogeneousMatching_subset hk D T hf
  rw [supercriticalCanonicalMatchingEdges,
    DenseGraph.mem_matchingEdgeFinset] at he' hf'
  exact DenseGraph.matching_edges_endpoint_disjoint
    (supercriticalCanonicalMatching_isMatching D T) he' hf' hef

/-- Every selected edge has the single dominant location whenever `T` is an
actual displayed combined-defect pattern. -/
theorem selectedHomogeneousMatching_contains_dominant
    {k n : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D) {e : Sym2 (Fin n)}
    (he : e ∈ selectedHomogeneousMatching hk D T) :
    (dominantMatchingLocation hk D T).Contains D e := by
  have heDominant := selectedHomogeneousMatching_subset_dominant hk D T he
  have heCanonical := dominantLocationMatching_subset hk D T heDominant
  have heSupport := supercriticalCanonicalMatchingEdges_subset D T heCanonical
  have hexists :=
    (existsUnique_supercriticalMatchingLocation_of_mem_pattern hT heSupport).exists
  have hcontains :=
    supercriticalMatchingLocationOfEdge_contains hk D hexists
  have hlocation :=
    (mem_matchingInLocation hk D T (dominantMatchingLocation hk D T) e).mp
      heDominant |>.2
  rw [hlocation] at hcontains
  exact hcontains

theorem selectedHomogeneousMatching_nonempty_of_mem_pattern
    {k n : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D) :
    (selectedHomogeneousMatching hk D T).Nonempty := by
  have hpos := supercriticalMatchingNumber_pos_of_mem_pattern hT
  have hbound :=
    supercriticalMatchingNumber_le_four_mul_sub_one_mul_selected hk D T
  apply Finset.card_pos.mp
  by_contra hcard
  have hzero : (selectedHomogeneousMatching hk D T).card = 0 :=
    Nat.eq_zero_of_not_pos hcard
  simp [hzero] at hbound
  omega

/-- Transparent data used by the candidate construction: a homogeneous
matching, its common location, disjointness, and the exact deterministic
cardinality loss. -/
structure SupercriticalHomogeneousMatching (k : ℕ) (V : Type*)
    [Fintype V] [DecidableEq V] (D : SupercriticalDivision k V)
    (T : SimpleGraph V) where
  location : SupercriticalMatchingLocation k
  edges : Finset (Sym2 V)
  edges_subset : edges ⊆ supercriticalCanonicalMatchingEdges D T
  same_location : ∀ e ∈ edges, location.Contains D e
  endpoint_disjoint : ∀ {e f}, e ∈ edges → f ∈ edges → e ≠ f →
    Disjoint (e : Set V) (f : Set V)
  matchingNumber_le : supercriticalMatchingNumber D T ≤
    4 * (k - 1) * edges.card

/-- The canonical homogeneous matching attached to a displayed pattern. -/
def selectedSupercriticalHomogeneousMatching
    {k n : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D) :
    SupercriticalHomogeneousMatching k (Fin n) D T where
  location := dominantMatchingLocation hk D T
  edges := selectedHomogeneousMatching hk D T
  edges_subset := selectedHomogeneousMatching_subset hk D T
  same_location := fun _ he ↦
    selectedHomogeneousMatching_contains_dominant hT he
  endpoint_disjoint := fun he hf hef ↦
    selectedHomogeneousMatching_edges_endpoint_disjoint hk D T he hf hef
  matchingNumber_le :=
    supercriticalMatchingNumber_le_four_mul_sub_one_mul_selected hk D T

namespace SupercriticalHomogeneousMatching

/-- All endpoints of the selected unordered edges. -/
def endpointFinset {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T) : Finset V :=
  M.edges.biUnion Sym2.toFinset

@[simp] theorem mem_endpointFinset
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T) (v : V) :
    v ∈ M.endpointFinset ↔ ∃ e ∈ M.edges, v ∈ e := by
  simp [endpointFinset, Sym2.mem_toFinset]

/-- The first endpoint of the fixed representative of an unordered edge. -/
def firstEndpoint {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    (e : {e // e ∈ M.edges}) : V :=
  e.1.out.1

/-- The second endpoint of the fixed representative of an unordered edge. -/
def secondEndpoint {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    (e : {e // e ∈ M.edges}) : V :=
  e.1.out.2

theorem edge_eq_endpoints {D : SupercriticalDivision k V}
    {T : SimpleGraph V} (M : SupercriticalHomogeneousMatching k V D T)
    (e : {e // e ∈ M.edges}) :
    e.1 = s(M.firstEndpoint e, M.secondEndpoint e) := by
  exact e.1.out_eq.symm

/-- Globally orient an internal edge by its fixed representative, and a
support--sparse edge from its main-part endpoint toward its sparse endpoint. -/
def orientedFirstEndpoint {D : SupercriticalDivision k V}
    {T : SimpleGraph V} (M : SupercriticalHomogeneousMatching k V D T)
    (e : {e // e ∈ M.edges}) : V :=
  match M.location with
  | .internal _ => M.firstEndpoint e
  | .supportSparse i =>
      if M.firstEndpoint e ∈ D.parts i then
        M.firstEndpoint e
      else
        M.secondEndpoint e

/-- The endpoint opposite `orientedFirstEndpoint`. -/
def orientedSecondEndpoint {D : SupercriticalDivision k V}
    {T : SimpleGraph V} (M : SupercriticalHomogeneousMatching k V D T)
    (e : {e // e ∈ M.edges}) : V :=
  match M.location with
  | .internal _ => M.secondEndpoint e
  | .supportSparse i =>
      if M.firstEndpoint e ∈ D.parts i then
        M.secondEndpoint e
      else
        M.firstEndpoint e

theorem edge_eq_orientedEndpoints {D : SupercriticalDivision k V}
    {T : SimpleGraph V} (M : SupercriticalHomogeneousMatching k V D T)
    (e : {e // e ∈ M.edges}) :
    e.1 = s(M.orientedFirstEndpoint e, M.orientedSecondEndpoint e) := by
  have hedge := M.edge_eq_endpoints e
  cases hloc : M.location with
  | internal i => simpa [orientedFirstEndpoint, orientedSecondEndpoint, hloc]
      using hedge
  | supportSparse i =>
      by_cases hfirst : M.firstEndpoint e ∈ D.parts i
      · simpa [orientedFirstEndpoint, orientedSecondEndpoint, hloc, hfirst]
          using hedge
      · simpa [orientedFirstEndpoint, orientedSecondEndpoint, hloc, hfirst]
          using hedge.trans
            (Sym2.eq_swap (a := M.firstEndpoint e)
              (b := M.secondEndpoint e))

theorem endpoints_mem_internalPart {D : SupercriticalDivision k V}
    {T : SimpleGraph V} (M : SupercriticalHomogeneousMatching k V D T)
    {i : Fin (k - 1)} (hloc : M.location = .internal i)
    (e : {e // e ∈ M.edges}) :
    M.orientedFirstEndpoint e ∈ D.parts i ∧
      M.orientedSecondEndpoint e ∈ D.parts i := by
  have h := M.same_location e.1 e.2
  rw [hloc, M.edge_eq_endpoints e] at h
  simpa [orientedFirstEndpoint, orientedSecondEndpoint, hloc] using h

theorem orientedFirstEndpoint_mem_supportPart
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    {i : Fin (k - 1)} (hloc : M.location = .supportSparse i)
    (e : {e // e ∈ M.edges}) :
    M.orientedFirstEndpoint e ∈ D.parts i := by
  have h := M.same_location e.1 e.2
  rw [hloc, M.edge_eq_endpoints e] at h
  rcases h with h | h
  · simp [orientedFirstEndpoint, hloc, h.1]
  · have hn : M.firstEndpoint e ∉ D.parts i := by
      intro hpart
      exact (Finset.disjoint_left.mp (D.part_disjoint_sparse i)) hpart h.2
    simp [orientedFirstEndpoint, hloc, hn, h.1]

theorem orientedSecondEndpoint_mem_sparse
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    {i : Fin (k - 1)} (hloc : M.location = .supportSparse i)
    (e : {e // e ∈ M.edges}) :
    M.orientedSecondEndpoint e ∈ D.sparse := by
  have h := M.same_location e.1 e.2
  rw [hloc, M.edge_eq_endpoints e] at h
  rcases h with h | h
  · simp [orientedSecondEndpoint, hloc, h.1, h.2]
  · have hn : M.firstEndpoint e ∉ D.parts i := by
      intro hpart
      exact (Finset.disjoint_left.mp (D.part_disjoint_sparse i)) hpart h.2
    simp [orientedSecondEndpoint, hloc, hn, h.2]

/-- Distinct matching edges have distinct oriented first endpoints. -/
theorem orientedFirstEndpoint_injective
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T) :
    Function.Injective M.orientedFirstEndpoint := by
  intro e f hef
  apply Subtype.ext
  by_contra hne
  have hdisjoint := M.endpoint_disjoint e.2 f.2 hne
  have he : M.orientedFirstEndpoint e ∈ (e.1 : Set V) := by
    rw [M.edge_eq_orientedEndpoints e]
    simp
  have hf : M.orientedFirstEndpoint f ∈ (f.1 : Set V) := by
    rw [M.edge_eq_orientedEndpoints f]
    simp
  exact Set.disjoint_left.mp hdisjoint he (by simpa [hef] using hf)

/-- Distinct matching edges have distinct oriented second endpoints. -/
theorem orientedSecondEndpoint_injective
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T) :
    Function.Injective M.orientedSecondEndpoint := by
  intro e f hef
  apply Subtype.ext
  by_contra hne
  have hdisjoint := M.endpoint_disjoint e.2 f.2 hne
  have he : M.orientedSecondEndpoint e ∈ (e.1 : Set V) := by
    rw [M.edge_eq_orientedEndpoints e]
    simp
  have hf : M.orientedSecondEndpoint f ∈ (f.1 : Set V) := by
    rw [M.edge_eq_orientedEndpoints f]
    simp
  exact Set.disjoint_left.mp hdisjoint he (by simpa [hef] using hf)

/-- The oriented first endpoints, one per selected matching edge. -/
def orientedFirstEndpointFinset
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T) : Finset V :=
  M.edges.attach.image M.orientedFirstEndpoint

/-- The oriented second endpoints, one per selected matching edge. -/
def orientedSecondEndpointFinset
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T) : Finset V :=
  M.edges.attach.image M.orientedSecondEndpoint

@[simp] theorem card_orientedFirstEndpointFinset
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T) :
    M.orientedFirstEndpointFinset.card = M.edges.card := by
  rw [orientedFirstEndpointFinset,
    Finset.card_image_of_injective _ M.orientedFirstEndpoint_injective]
  simp

@[simp] theorem card_orientedSecondEndpointFinset
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T) :
    M.orientedSecondEndpointFinset.card = M.edges.card := by
  rw [orientedSecondEndpointFinset,
    Finset.card_image_of_injective _ M.orientedSecondEndpoint_injective]
  simp

/-- In the support--sparse geometry the first-endpoint finset is the exact
main-endpoint set. -/
theorem orientedFirstEndpointFinset_subset_supportPart
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    {i : Fin (k - 1)} (hloc : M.location = .supportSparse i) :
    M.orientedFirstEndpointFinset ⊆ D.parts i := by
  intro v hv
  rw [orientedFirstEndpointFinset, Finset.mem_image] at hv
  obtain ⟨e, _he, rfl⟩ := hv
  exact M.orientedFirstEndpoint_mem_supportPart hloc e

/-- In the support--sparse geometry the second-endpoint finset lies in the
sparse set. -/
theorem orientedSecondEndpointFinset_subset_sparse
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    {i : Fin (k - 1)} (hloc : M.location = .supportSparse i) :
    M.orientedSecondEndpointFinset ⊆ D.sparse := by
  intro v hv
  rw [orientedSecondEndpointFinset, Finset.mem_image] at hv
  obtain ⟨e, _he, rfl⟩ := hv
  exact M.orientedSecondEndpoint_mem_sparse hloc e

/-- A matching really has two distinct endpoints per selected edge. -/
@[simp] theorem card_endpointFinset {D : SupercriticalDivision k V}
    {T : SimpleGraph V} (M : SupercriticalHomogeneousMatching k V D T) :
    M.endpointFinset.card = 2 * M.edges.card := by
  have hpairwise : (M.edges : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
    intro e he f hf hef
    change Disjoint e.toFinset f.toFinset
    rw [Finset.disjoint_left]
    intro v hve hvf
    exact Set.disjoint_left.mp (M.endpoint_disjoint he hf hef)
      (by simpa [Sym2.mem_toFinset] using hve)
      (by simpa [Sym2.mem_toFinset] using hvf)
  rw [endpointFinset, Finset.card_biUnion hpairwise]
  calc
    (∑ e ∈ M.edges, e.toFinset.card) = ∑ _e ∈ M.edges, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      have he' := M.edges_subset he
      rw [supercriticalCanonicalMatchingEdges,
        DenseGraph.mem_matchingEdgeFinset] at he'
      exact Sym2.card_toFinset_of_not_isDiag e
        ((supercriticalSupportIncidentGraph D T).not_isDiag_of_mem_edgeSet
          ((supercriticalCanonicalMatching D T).edgeSet_subset he'))
    _ = 2 * M.edges.card := by simp [Nat.mul_comm]

end SupercriticalHomogeneousMatching

end InducedStars
