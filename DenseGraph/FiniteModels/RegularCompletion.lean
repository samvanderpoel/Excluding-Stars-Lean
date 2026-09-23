import DenseGraph.FiniteModels.GraphEdit
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Bounded-edit completion of an almost regular finite graph

Two degree deficits can be filled by replacing one far-away edge with two
edges. This elementary switch also permits both deficits at the same vertex.
-/

noncomputable section

open Finset SimpleGraph
open scoped BigOperators Classical

namespace DenseGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable local instance (priority := 2000) (G : SimpleGraph V) : DecidableRel G.Adj :=
  Classical.decRel _

theorem degree_sup_of_disjoint_finite (G H : SimpleGraph V)
    (h : Disjoint G H) (v : V) :
    (G ⊔ H).degree v = G.degree v + H.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
    Finset.card_union_of_disjoint (SimpleGraph.disjoint_neighborFinset_of_disjoint G H v h)]
  simp

theorem degree_singleEdge (a b v : V) (hab : a ≠ b) :
    (SimpleGraph.edge a b).degree v = if v = a ∨ v = b then 1 else 0 := by
  have hset : (SimpleGraph.edge a b).neighborFinset v =
      if v = a then {b} else if v = b then {a} else ∅ := by
    ext w
    by_cases hva : v = a
    · subst v
      simp [SimpleGraph.edge_adj, hab, Ne.symm hab]
      rintro rfl
      exact hab
    by_cases hvb : v = b
    · subst v
      simp [SimpleGraph.edge_adj, hab, Ne.symm hab]
      rintro rfl
      exact hab.symm
    · simp [SimpleGraph.edge_adj, hva, hvb]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hset]
  by_cases hva : v = a <;> by_cases hvb : v = b <;> simp_all

theorem degree_add_fresh_edge (G : SimpleGraph V) {a b : V}
    (hab : a ≠ b) (hn : ¬ G.Adj a b) (v : V) :
    (G ⊔ SimpleGraph.edge a b).degree v =
      G.degree v + if v = a ∨ v = b then 1 else 0 := by
  rw [degree_sup_of_disjoint_finite G _ ((SimpleGraph.disjoint_edge G).mpr hn),
    degree_singleEdge a b v hab]

theorem degree_remove_edge (G : SimpleGraph V) {x y : V}
    (hxy : G.Adj x y) (v : V) :
    (G \ SimpleGraph.edge x y).degree v +
        (if v = x ∨ v = y then 1 else 0) = G.degree v := by
  have he : SimpleGraph.edge x y ≤ G := (SimpleGraph.edge_le_iff G).mpr (Or.inr hxy)
  have hnone : ¬ (G \ SimpleGraph.edge x y).Adj x y := by
    simp [SimpleGraph.edge_adj, hxy.ne]
  have h := degree_add_fresh_edge (G \ SimpleGraph.edge x y) hxy.ne hnone v
  rw [sdiff_sup_cancel he] at h
  exact h.symm

/-- Fill one degree deficit at each of `a,b`, permitting `a=b`, by taking
an edge `xy` far from the two deficit vertices. -/
def degreeDeficitSwitch (G : SimpleGraph V) (a b x y : V) : SimpleGraph V :=
  (G \ SimpleGraph.edge x y) ⊔ SimpleGraph.edge a x ⊔ SimpleGraph.edge b y

theorem degreeDeficitSwitch_degree (G : SimpleGraph V) (a b x y : V)
    (hxy : G.Adj x y)
    (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y)
    (hnax : ¬ G.Adj a x) (hnby : ¬ G.Adj b y) (v : V) :
    (degreeDeficitSwitch G a b x y).degree v =
      G.degree v + (if v = a then 1 else 0) + (if v = b then 1 else 0) := by
  let T := G \ SimpleGraph.edge x y
  have hT : ¬ T.Adj a x := fun h ↦ hnax h.1
  have hU : ¬ (T ⊔ SimpleGraph.edge a x).Adj b y := by
    intro h
    rcases h with h | h
    · exact hnby h.1
    · have h' := (SimpleGraph.edge_adj a x b y).mp h
      rcases h'.1 with ⟨_, hyx⟩ | ⟨hbx', _⟩
      · exact hxy.ne hyx.symm
      · exact hbx hbx'
  have hrem := degree_remove_edge G hxy v
  have hadd := degree_add_fresh_edge T hax hT v
  have hadd' := degree_add_fresh_edge (T ⊔ SimpleGraph.edge a x) hby hU v
  change (T ⊔ SimpleGraph.edge a x ⊔ SimpleGraph.edge b y).degree v = _
  rw [hadd', hadd]
  change T.degree v + (if v = x ∨ v = y then 1 else 0) = G.degree v at hrem
  by_cases hva : v = a <;> by_cases hvb : v = b <;>
    by_cases hvx : v = x <;> by_cases hvy : v = y <;>
      simp_all <;> omega

theorem degreeDeficitSwitch_edge_count (G : SimpleGraph V) (a b x y : V)
    (hxy : G.Adj x y)
    (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y)
    (hnax : ¬ G.Adj a x) (hnby : ¬ G.Adj b y) :
    (degreeDeficitSwitch G a b x y).edgeFinset.card = G.edgeFinset.card + 1 := by
  have hsum : ∑ v, (degreeDeficitSwitch G a b x y).degree v =
      (∑ v, G.degree v) + 2 := by
    simp_rw [degreeDeficitSwitch_degree G a b x y hxy hax hay hbx hby hnax hnby]
    simp [Finset.sum_add_distrib]
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges,
    SimpleGraph.sum_degrees_eq_twice_card_edges] at hsum
  omega

theorem degreeDeficitSwitch_edit_distance (G : SimpleGraph V) (a b x y : V) :
    simpleGraphEditDistance G (degreeDeficitSwitch G a b x y) ≤ 3 := by
  have hsub : simpleGraphEditFinset G (degreeDeficitSwitch G a b x y) ⊆
      {s(x, y), s(a, x), s(b, y)} := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      simp only [mem_simpleGraphEditFinset, SimpleGraph.mem_edgeSet] at he
      have hedge (p q : V) : (SimpleGraph.edge p q).Adj u v → s(u, v) = s(p, q) := by
        intro h
        exact ((SimpleGraph.adj_edge p q).mp h).1.symm
      change (G.Adj u v ∧ ¬ (((G.Adj u v ∧ ¬(SimpleGraph.edge x y).Adj u v) ∨
          (SimpleGraph.edge a x).Adj u v) ∨ (SimpleGraph.edge b y).Adj u v)) ∨
        ((((G.Adj u v ∧ ¬(SimpleGraph.edge x y).Adj u v) ∨
          (SimpleGraph.edge a x).Adj u v) ∨ (SimpleGraph.edge b y).Adj u v) ∧ ¬ G.Adj u v) at he
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases he with ⟨hG, hnew⟩ | ⟨hnew, hG⟩
      · have hdel : (SimpleGraph.edge x y).Adj u v := by tauto
        exact Or.inl (hedge x y hdel)
      · rcases hnew with (hold | hax) | hby
        · exact (hG hold.1).elim
        · exact Or.inr (Or.inl (hedge a x hax))
        · exact Or.inr (Or.inr (hedge b y hby))
  apply (Finset.card_le_card hsub).trans
  calc
    ({s(x, y), s(a, x), s(b, y)} : Finset (Sym2 V)).card ≤
        ({s(a, x), s(b, y)} : Finset (Sym2 V)).card + 1 := Finset.card_insert_le _ _
    _ ≤ (({s(b, y)} : Finset (Sym2 V)).card + 1) + 1 := by gcongr; exact Finset.card_insert_le _ _
    _ = 3 := by simp

/-- If every edge touches `S`, its cardinality is at most the sum of the
degrees on `S`; edges with both endpoints in `S` may be counted twice. -/
theorem card_edges_le_sum_degrees_of_vertex_cover (G : SimpleGraph V)
    (S : Finset V) (hcover : ∀ x y, G.Adj x y → x ∈ S ∨ y ∈ S) :
    G.edgeFinset.card ≤ ∑ v ∈ S, G.degree v := by
  have hsub : G.edgeFinset ⊆ S.biUnion (fun v ↦ G.incidenceFinset v) := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hxy : G.Adj x y := by simpa using he
      rcases hcover x y hxy with hx | hy
      · exact Finset.mem_biUnion.mpr ⟨x, hx, by simp [SimpleGraph.incidenceSet, hxy]⟩
      · exact Finset.mem_biUnion.mpr ⟨y, hy, by simp [SimpleGraph.incidenceSet, hxy]⟩
  calc
    G.edgeFinset.card ≤ (S.biUnion (fun v ↦ G.incidenceFinset v)).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ S, (G.incidenceFinset v).card := Finset.card_biUnion_le
    _ = _ := by simp

/-- A graph of maximum degree `d` with more than `2(d+1)d` edges has an
edge outside the closed neighborhoods of any two prescribed vertices. -/
theorem exists_edge_far_from_two (G : SimpleGraph V) (d : ℕ)
    (hdeg : ∀ v, G.degree v ≤ d)
    (hlarge : 2 * (d + 1) * d < G.edgeFinset.card) (a b : V) :
    ∃ x y, G.Adj x y ∧ a ≠ x ∧ a ≠ y ∧ b ≠ x ∧ b ≠ y ∧
      ¬ G.Adj a x ∧ ¬ G.Adj b y := by
  let S := insert a (insert b (G.neighborFinset a ∪ G.neighborFinset b))
  have hScard : S.card ≤ 2 * (d + 1) := by
    have h₁ := Finset.card_insert_le a (insert b (G.neighborFinset a ∪ G.neighborFinset b))
    have h₂ := Finset.card_insert_le b (G.neighborFinset a ∪ G.neighborFinset b)
    have h₃ := Finset.card_union_le (G.neighborFinset a) (G.neighborFinset b)
    rw [SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.card_neighborFinset_eq_degree] at h₃
    have ha := hdeg a
    have hb := hdeg b
    dsimp [S]
    omega
  have hex : ∃ x y, G.Adj x y ∧ x ∉ S ∧ y ∉ S := by
    by_contra hnone
    push_neg at hnone
    have hcover : ∀ x y, G.Adj x y → x ∈ S ∨ y ∈ S := by
      intro x y hxy
      by_cases hx : x ∈ S
      · exact Or.inl hx
      · exact Or.inr (hnone x y hxy hx)
    have hc := card_edges_le_sum_degrees_of_vertex_cover G S hcover
    have hs : (∑ v ∈ S, G.degree v) ≤ S.card * d := by
      calc
        _ ≤ ∑ _v ∈ S, d := Finset.sum_le_sum fun v _ ↦ hdeg v
        _ = _ := by simp
    exact (not_lt_of_ge (hc.trans (hs.trans (Nat.mul_le_mul_right d hScard)))) hlarge
  obtain ⟨x, y, hxy, hx, hy⟩ := hex
  have hx' : x ≠ a ∧ x ≠ b ∧ ¬ G.Adj a x ∧ ¬ G.Adj b x := by
    simpa [S] using hx
  have hy' : y ≠ a ∧ y ≠ b ∧ ¬ G.Adj a y ∧ ¬ G.Adj b y := by
    simpa [S] using hy
  exact ⟨x, y, hxy, hx'.1.symm, hy'.1.symm, hx'.2.1.symm,
    hy'.2.1.symm, hx'.2.2.1, hy'.2.2.2⟩

theorem card_edges_le_half_regular_target (G : SimpleGraph V) (d m : ℕ)
    (hdeg : ∀ v, G.degree v ≤ d) (htarget : Fintype.card V * d = 2 * m) :
    G.edgeFinset.card ≤ m := by
  have hs : (∑ v, G.degree v) ≤ Fintype.card V * d := by
    calc
      _ ≤ ∑ _v : V, d := Finset.sum_le_sum fun v _ ↦ hdeg v
      _ = _ := by simp
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges, htarget] at hs
  omega

/-- Unless a bounded-degree graph is already regular, an even total target
degree supplies two deficit units, possibly at the same vertex. -/
theorem exists_two_degree_deficits (G : SimpleGraph V) (d m : ℕ)
    (hdeg : ∀ v, G.degree v ≤ d) (htarget : Fintype.card V * d = 2 * m)
    (hnot : ¬ G.IsRegularOfDegree d) :
    ∃ a b, ∀ v, G.degree v + (if v = a then 1 else 0) +
      (if v = b then 1 else 0) ≤ d := by
  have hex : ∃ a, G.degree a < d := by
    by_contra h
    push_neg at h
    apply hnot
    intro v
    exact (hdeg v).antisymm (h v)
  obtain ⟨a, ha⟩ := hex
  by_cases haa : G.degree a + 2 ≤ d
  · refine ⟨a, a, ?_⟩
    intro v
    by_cases hv : v = a
    · subst v; simp; omega
    · simpa [hv] using hdeg v
  have hb : ∃ b, b ≠ a ∧ G.degree b < d := by
    by_contra h
    push_neg at h
    have hdef : ∀ v, d - G.degree v = if v = a then 1 else 0 := by
      intro v
      by_cases hv : v = a
      · subst v; simp; omega
      · have hvd := h v hv
        simp [hv]
        omega
    have hsum : (∑ v, (d - G.degree v)) + (∑ v, G.degree v) =
        Fintype.card V * d := by
      rw [← Finset.sum_add_distrib]
      simp [Nat.sub_add_cancel (hdeg _)]
    simp_rw [hdef] at hsum
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true,
      SimpleGraph.sum_degrees_eq_twice_card_edges, htarget] at hsum
    omega
  obtain ⟨b, hba, hb⟩ := hb
  refine ⟨a, b, ?_⟩
  intro v
  by_cases hva : v = a
  · subst v; simp [Ne.symm hba]; omega
  by_cases hvb : v = b
  · subst v; simp [hba]; omega
  · simpa [hva, hvb] using hdeg v

/-- A dense-enough almost regular graph admits a regular completion at
three edge edits per missing edge of the regular target. All assumptions
are finite, and the target parity is stated exactly. -/
theorem exists_regular_completion_bounded_edit (G : SimpleGraph V) (d m : ℕ)
    (hdeg : ∀ v, G.degree v ≤ d) (htarget : Fintype.card V * d = 2 * m)
    (hlarge : 2 * (d + 1) * d < G.edgeFinset.card) :
    ∃ H : SimpleGraph V, H.IsRegularOfDegree d ∧
      simpleGraphEditDistance G H ≤ 3 * (m - G.edgeFinset.card) := by
  generalize hdef : m - G.edgeFinset.card = t
  induction t using Nat.strong_induction_on generalizing G with
  | h t ih =>
    by_cases hreg : G.IsRegularOfDegree d
    · exact ⟨G, hreg, by simp⟩
    obtain ⟨a, b, hab⟩ := exists_two_degree_deficits G d m hdeg htarget hreg
    obtain ⟨x, y, hxy, hax, hay, hbx, hby, hnax, hnby⟩ :=
      exists_edge_far_from_two G d hdeg hlarge a b
    let U := degreeDeficitSwitch G a b x y
    have hUdeg : ∀ v, U.degree v ≤ d := by
      intro v
      rw [degreeDeficitSwitch_degree G a b x y hxy hax hay hbx hby hnax hnby]
      exact hab v
    have hUcard : U.edgeFinset.card = G.edgeFinset.card + 1 :=
      degreeDeficitSwitch_edge_count G a b x y hxy hax hay hbx hby hnax hnby
    have hUle := card_edges_le_half_regular_target U d m hUdeg htarget
    have hsmaller : m - U.edgeFinset.card < t := by omega
    have hUlarge : 2 * (d + 1) * d < U.edgeFinset.card := by omega
    obtain ⟨H, hH, hdist⟩ := ih (m - U.edgeFinset.card) hsmaller U hUdeg hUlarge rfl
    refine ⟨H, hH, ?_⟩
    have hstep : simpleGraphEditDistance G U ≤ 3 :=
      degreeDeficitSwitch_edit_distance G a b x y
    have htriangle := simpleGraphEditDistance_triangle G U H
    omega

/-- Deleting a set of vertices loses no more edges than the sum of their
old degrees. The induced graph lives on the actual remaining subtype. -/
theorem card_induced_edges_add_removed_degrees_ge (G : SimpleGraph V)
    (S : Finset V) :
    G.edgeFinset.card ≤ (G.induce (S : Set V)).edgeFinset.card +
      ∑ v ∈ Finset.univ \ S, G.degree v := by
  let E := (G.induce (S : Set V)).edgeFinset.map
    (Function.Embedding.subtype (· ∈ (S : Set V))).sym2Map
  let I := (Finset.univ \ S).biUnion (fun v ↦ G.incidenceFinset v)
  have hsub : G.edgeFinset ⊆ E ∪ I := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hxy : G.Adj x y := by simpa using he
      by_cases hx : x ∈ S
      · by_cases hy : y ∈ S
        · apply Finset.mem_union_left
          dsimp [E]
          exact Finset.mem_map.mpr ⟨s((⟨x, hx⟩ : (S : Set V)), ⟨y, hy⟩),
            by simpa using hxy, rfl⟩
        · apply Finset.mem_union_right
          exact Finset.mem_biUnion.mpr ⟨y, by simpa using hy,
            by simp [SimpleGraph.incidenceSet, hxy]⟩
      · apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨x, by simpa using hx,
          by simp [SimpleGraph.incidenceSet, hxy]⟩
  have hi : I.card ≤ ∑ v ∈ Finset.univ \ S, G.degree v := by
    calc
      I.card ≤ ∑ v ∈ Finset.univ \ S, (G.incidenceFinset v).card := Finset.card_biUnion_le
      _ = _ := by simp
  have he : E.card = (G.induce (S : Set V)).edgeFinset.card := Finset.card_map _
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le E I)
  omega

theorem degree_induce_le_finite (G : SimpleGraph V) (S : Finset V)
    (v : (S : Set V)) : (G.induce (S : Set V)).degree v ≤ G.degree v.val := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective
    (fun z : (G.induce (S : Set V)).neighborSet v ↦
      (⟨z.val.val, z.property⟩ : G.neighborSet v.val))
    (by
      intro z z' h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : G.neighborSet v.val ↦ t.val) h)

/-- Removing any two vertices of a sufficiently large regular graph leaves
a graph within `3*d` edits of a regular graph on exactly the remaining
vertices. Connectedness is not required of the replacement. -/
theorem exists_regular_after_deleting_two (G : SimpleGraph V) (d : ℕ)
    (hreg : G.IsRegularOfDegree d) (hd : 0 < d)
    (hlarge : 4 * d + 8 < Fintype.card V)
    (v w : V) (hvw : v ≠ w) :
    ∃ H : SimpleGraph {x : V // x ∈ (Finset.univ \ {v, w} : Finset V)},
      H.IsRegularOfDegree d ∧
        simpleGraphEditDistance
          (G.induce ((Finset.univ \ {v, w} : Finset V) : Set V)) H ≤ 3 * d := by
  let S : Finset V := Finset.univ \ {v, w}
  let U := G.induce (S : Set V)
  have hS : S.card = Fintype.card V - 2 := by
    dsimp [S]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hvw]
  have hvertices : Fintype.card (S : Set V) = Fintype.card V - 2 := by
    simpa using hS
  have hregularDegrees : ∀ x, G.degree x = d := hreg.degree_eq
  have hhand : 2 * G.edgeFinset.card = Fintype.card V * d := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
    simp [hregularDegrees]
  have hege : d ≤ G.edgeFinset.card := by
    have hn : 2 ≤ Fintype.card V := by omega
    have h := Nat.mul_le_mul_right d hn
    omega
  let m := G.edgeFinset.card - d
  have htarget : Fintype.card (S : Set V) * d = 2 * m := by
    rw [hvertices]
    dsimp [m]
    rw [Nat.sub_mul]
    omega
  have hdeg : ∀ x, U.degree x ≤ d := by
    intro x
    exact (degree_induce_le_finite G S x).trans_eq (hregularDegrees x.val)
  have hsurvive : G.edgeFinset.card ≤ U.edgeFinset.card + 2 * d := by
    have h := card_induced_edges_add_removed_degrees_ge G S
    have hremoved : Finset.univ \ S = {v, w} := by
      ext x
      simp [S]
    rw [hremoved] at h
    simpa [hregularDegrees, hvw, two_mul] using h
  have hUlarge : 2 * (d + 1) * d < U.edgeFinset.card := by
    have hprod := Nat.mul_lt_mul_of_pos_right hlarge hd
    nlinarith
  obtain ⟨H, hH, hdist⟩ := exists_regular_completion_bounded_edit U d m hdeg htarget hUlarge
  refine ⟨H, hH, hdist.trans ?_⟩
  have hdiff : m - U.edgeFinset.card ≤ d := by dsimp [m]; omega
  exact Nat.mul_le_mul_left 3 hdiff

/-- Localizing all disagreements at a finite set of vertices bounds the
edit distance by the corresponding degrees in the two graphs. -/
theorem edit_distance_le_local_degree_sum (G H : SimpleGraph V)
    (S : Finset V)
    (haway : ∀ x y, x ∉ S → y ∉ S → (G.Adj x y ↔ H.Adj x y)) :
    simpleGraphEditDistance G H ≤
      (∑ v ∈ S, G.degree v) + ∑ v ∈ S, H.degree v := by
  have hsub : simpleGraphEditFinset G H ⊆
      S.biUnion (fun v ↦ G.incidenceFinset v ∪ H.incidenceFinset v) := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf x y =>
      have he' := he
      simp only [mem_simpleGraphEditFinset, SimpleGraph.mem_edgeSet] at he'
      have hv : x ∈ S ∨ y ∈ S := by
        by_contra h
        have hx : x ∉ S := fun hx ↦ h (Or.inl hx)
        have hy : y ∉ S := fun hy ↦ h (Or.inr hy)
        have hh := haway x y hx hy
        tauto
      rcases hv with hx | hy
      · refine Finset.mem_biUnion.mpr ⟨x, hx, ?_⟩
        rcases he' with ⟨hG, _⟩ | ⟨hH, _⟩
        · exact Finset.mem_union_left _ (by simp [SimpleGraph.incidenceSet, hG])
        · exact Finset.mem_union_right _ (by simp [SimpleGraph.incidenceSet, hH])
      · refine Finset.mem_biUnion.mpr ⟨y, hy, ?_⟩
        rcases he' with ⟨hG, _⟩ | ⟨hH, _⟩
        · exact Finset.mem_union_left _ (by simp [SimpleGraph.incidenceSet, hG])
        · exact Finset.mem_union_right _ (by simp [SimpleGraph.incidenceSet, hH])
  calc
    simpleGraphEditDistance G H ≤
        (S.biUnion (fun v ↦ G.incidenceFinset v ∪ H.incidenceFinset v)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ v ∈ S, (G.incidenceFinset v ∪ H.incidenceFinset v).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ v ∈ S, ((G.incidenceFinset v).card + (H.incidenceFinset v).card) :=
      Finset.sum_le_sum fun v _ ↦ Finset.card_union_le _ _
    _ = _ := by simp [Finset.sum_add_distrib]

open scoped symmDiff in
theorem simpleGraphEditFinset_eq_edgeFinset_symmDiff (G H : SimpleGraph V) :
    simpleGraphEditFinset G H = G.edgeFinset ∆ H.edgeFinset := by
  ext e
  simp [mem_simpleGraphEditFinset, Finset.mem_symmDiff]

/-- A genuine vertex embedding preserves unordered edge edit distance,
including the isolated vertices added outside its image. -/
theorem simpleGraphEditDistance_map_embedding
    {W : Type*} [Fintype W] [DecidableEq W]
    (G H : SimpleGraph V) (f : V ↪ W) :
    simpleGraphEditDistance (G.map f) (H.map f) = simpleGraphEditDistance G H := by
  unfold simpleGraphEditDistance simpleGraphEditFinset
  rw [← Set.ncard_eq_toFinset_card, ← Set.ncard_eq_toFinset_card]
  rw [SimpleGraph.edgeSet_map, SimpleGraph.edgeSet_map,
    ← Set.image_symmDiff f.sym2Map.injective]
  exact Set.ncard_image_of_injective _ f.sym2Map.injective

theorem edit_distance_add_edges_of_le (G H : SimpleGraph V) (hHG : H ≤ G) :
    simpleGraphEditDistance G H + H.edgeFinset.card = G.edgeFinset.card := by
  have hsub := SimpleGraph.edgeFinset_mono hHG
  rw [simpleGraphEditDistance, simpleGraphEditFinset_eq_edgeFinset_symmDiff,
    Finset.symmDiff_def, Finset.sdiff_eq_empty_iff_subset.mpr hsub,
    Finset.union_empty, Finset.card_sdiff_of_subset hsub,
    Nat.sub_add_cancel (Finset.card_le_card hsub)]

theorem induced_spanningCoe_le (G : SimpleGraph V) (S : Finset V) :
    (G.induce (S : Set V)).map (Function.Embedding.subtype (· ∈ (S : Set V))) ≤ G := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  obtain ⟨u, v, huv, rfl, rfl⟩ := hxy
  exact huv

theorem edit_distance_induced_spanningCoe_le_removed_degrees
    (G : SimpleGraph V) (S : Finset V) :
    simpleGraphEditDistance G
      ((G.induce (S : Set V)).map (Function.Embedding.subtype (· ∈ (S : Set V)))) ≤
        ∑ v ∈ Finset.univ \ S, G.degree v := by
  have h := edit_distance_add_edges_of_le G _ (induced_spanningCoe_le G S)
  have hcard := SimpleGraph.card_edgeFinset_map
    (Function.Embedding.subtype (· ∈ (S : Set V))) (G.induce (S : Set V))
  have hsurvive := card_induced_edges_add_removed_degrees_ge G S
  simp only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard]
    at h hcard hsurvive
  rw [hcard] at h
  omega

/-- The two-vertex regular repair, with the removed vertices added back as
isolates, differs from the original regular graph in at most `5*d` edges. -/
theorem exists_regular_after_deleting_two_spanning_edit (G : SimpleGraph V) (d : ℕ)
    (hreg : G.IsRegularOfDegree d) (hd : 0 < d)
    (hlarge : 4 * d + 8 < Fintype.card V)
    (v w : V) (hvw : v ≠ w) :
    ∃ H : SimpleGraph {x : V // x ∈ (Finset.univ \ {v, w} : Finset V)},
      H.IsRegularOfDegree d ∧
        simpleGraphEditDistance G
          (H.map (Function.Embedding.subtype
            (· ∈ ((Finset.univ \ {v, w} : Finset V) : Set V)))) ≤ 5 * d := by
  let S : Finset V := Finset.univ \ {v, w}
  let f := Function.Embedding.subtype (· ∈ (S : Set V))
  obtain ⟨H, hH, hdist⟩ := exists_regular_after_deleting_two G d hreg hd hlarge v w hvw
  refine ⟨H, hH, ?_⟩
  have hremove := edit_distance_induced_spanningCoe_le_removed_degrees G S
  have hremoved : Finset.univ \ S = {v, w} := by ext x; simp [S]
  rw [hremoved] at hremove
  have hdegrees : ∀ x, G.degree x = d := hreg.degree_eq
  simp [hdegrees, hvw, ← two_mul] at hremove
  have hmap := simpleGraphEditDistance_map_embedding (G.induce (S : Set V)) H f
  have htri := simpleGraphEditDistance_triangle G ((G.induce (S : Set V)).map f) (H.map f)
  change simpleGraphEditDistance G (H.map f) ≤ _
  dsimp [f, S] at hmap htri hremove ⊢
  omega

end DenseGraph
