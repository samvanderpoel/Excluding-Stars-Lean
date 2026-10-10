import InducedStars.C4.Divisions
import Mathlib.Data.Sym.Card

/-!
# Exact split fibers and their free cross-edge coordinates

The clique edges are forced, independent-side edges are forbidden, and each
unordered cross pair is one free coordinate. The fixed-edge fiber is exactly
one binomial slice, with a zero guard below the forced clique edge count.
-/

noncomputable section

open Finset Set

namespace InducedStars

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- All forced unordered clique pairs of the division. -/
def c4CliqueEdges (D : C4Division V) : Finset (Sym2 V) :=
  D.cliquePart.offDiag.image Sym2.mk.uncurry

@[simp] theorem mk_mem_c4CliqueEdges (D : C4Division V) (x y : V) :
    s(x, y) ∈ c4CliqueEdges D ↔ x ∈ D.cliquePart ∧ y ∈ D.cliquePart ∧ x ≠ y := by
  constructor
  · rintro h
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp h
    have hab' := Finset.mem_offDiag.mp hab
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab'
    · exact ⟨hab'.2.1, hab'.1, hab'.2.2.symm⟩
  · rintro ⟨hx, hy, hne⟩
    exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hne⟩, rfl⟩

@[simp] theorem card_c4CliqueEdges (D : C4Division V) :
    (c4CliqueEdges D).card = Nat.choose D.cliquePart.card 2 :=
  Sym2.card_image_offDiag D.cliquePart

/-- All optional cross pairs, with their unique orientation from the
independent part to the clique part forgotten after taking the image. -/
def c4CrossPotentialEdges (D : C4Division V) : Finset (Sym2 V) :=
  (D.independentPart ×ˢ D.cliquePart).image Sym2.mk.uncurry

@[simp] theorem mk_mem_c4CrossPotentialEdges (D : C4Division V) (x y : V) :
    s(x, y) ∈ c4CrossPotentialEdges D ↔
      (x ∈ D.independentPart ∧ y ∈ D.cliquePart) ∨
      (y ∈ D.independentPart ∧ x ∈ D.cliquePart) := by
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp h
    have hab' := Finset.mem_product.mp hab
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hab'
    · exact Or.inr hab'
  · rintro (⟨hx, hy⟩ | ⟨hy, hx⟩)
    · exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨(y, x), Finset.mem_product.mpr ⟨hy, hx⟩,
        Sym2.eq_swap⟩

@[simp] theorem card_c4CrossPotentialEdges (D : C4Division V) :
    (c4CrossPotentialEdges D).card = D.independentPart.card * D.cliquePart.card := by
  rw [c4CrossPotentialEdges, Finset.card_image_iff.mpr, Finset.card_product]
  intro a ha b hb heq
  obtain ⟨haA, haB⟩ := Finset.mem_product.mp ha
  obtain ⟨hbA, hbB⟩ := Finset.mem_product.mp hb
  rcases Sym2.eq_iff.mp heq with h | h
  · exact Prod.ext h.1 h.2
  · exact False.elim (Finset.disjoint_left.mp D.disjoint haA (h.1 ▸ hbB))

theorem c4CliqueEdges_disjoint_cross (D : C4Division V) :
    Disjoint (c4CliqueEdges D) (c4CrossPotentialEdges D) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  induction e using Sym2.inductionOn with
  | _ x y =>
      obtain ⟨hx, hy, _hne⟩ := (mk_mem_c4CliqueEdges D x y).mp he
      rcases (mk_mem_c4CrossPotentialEdges D x y).mp hf with h | h
      · exact Finset.disjoint_left.mp D.disjoint h.1 hx
      · exact Finset.disjoint_left.mp D.disjoint h.1 hy

theorem ne_of_mem_c4CrossPotentialEdges (D : C4Division V) {x y : V}
    (h : s(x, y) ∈ c4CrossPotentialEdges D) : x ≠ y := by
  rcases (mk_mem_c4CrossPotentialEdges D x y).mp h with h | h
  · intro heq
    exact Finset.disjoint_left.mp D.disjoint h.1 (heq ▸ h.2)
  · intro heq
    exact Finset.disjoint_left.mp D.disjoint h.1 (heq ▸ h.2)

/-- The actual selected cross coordinates of a graph. -/
def c4CrossEdges (G : SimpleGraph V) (D : C4Division V) : Finset (Sym2 V) :=
  finiteGraphEdges G ∩ c4CrossPotentialEdges D

theorem c4CrossEdges_subset (G : SimpleGraph V) (D : C4Division V) :
    c4CrossEdges G D ⊆ c4CrossPotentialEdges D := Finset.inter_subset_right

/-- The split graph determined by a set of free cross coordinates. -/
def c4SplitGraphOfCrossChoice (D : C4Division V) (C : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (↑(c4CliqueEdges D ∪ C) : Set (Sym2 V))

theorem finiteGraphEdges_c4SplitGraphOfCrossChoice (D : C4Division V)
    {C : Finset (Sym2 V)} (hC : C ⊆ c4CrossPotentialEdges D) :
    finiteGraphEdges (c4SplitGraphOfCrossChoice D C) = c4CliqueEdges D ∪ C := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [mk_mem_finiteGraphEdges, c4SplitGraphOfCrossChoice, SimpleGraph.fromEdgeSet_adj]
      change (s(x, y) ∈ c4CliqueEdges D ∪ C ∧ x ≠ y) ↔ s(x, y) ∈ c4CliqueEdges D ∪ C
      constructor
      · exact And.left
      · intro h
        refine ⟨h, ?_⟩
        rcases Finset.mem_union.mp h with h | h
        · exact ((mk_mem_c4CliqueEdges D x y).mp h).2.2
        · exact ne_of_mem_c4CrossPotentialEdges D (hC h)

theorem c4CrossEdges_graphOfCrossChoice (D : C4Division V)
    {C : Finset (Sym2 V)} (hC : C ⊆ c4CrossPotentialEdges D) :
    c4CrossEdges (c4SplitGraphOfCrossChoice D C) D = C := by
  rw [c4CrossEdges, finiteGraphEdges_c4SplitGraphOfCrossChoice D hC]
  ext e
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨h | h, he⟩
    · exact False.elim (Finset.disjoint_left.mp (c4CliqueEdges_disjoint_cross D) h he)
    · exact h
  · intro he
    exact ⟨Or.inr he, hC he⟩

/-- Cross choices are recovered from the resulting graph, hence the
constructor is injective on its coordinate universe. -/
theorem c4SplitGraphOfCrossChoice_injectiveOn (D : C4Division V) :
    Set.InjOn (c4SplitGraphOfCrossChoice D)
      {C : Finset (Sym2 V) | C ⊆ c4CrossPotentialEdges D} := by
  intro C hC E hE heq
  have h := congrArg (fun G ↦ c4CrossEdges G D) heq
  simpa only [c4CrossEdges_graphOfCrossChoice D hC, c4CrossEdges_graphOfCrossChoice D hE] using h

theorem card_edges_c4SplitGraphOfCrossChoice (D : C4Division V)
    {C : Finset (Sym2 V)} (hC : C ⊆ c4CrossPotentialEdges D) :
    (finiteGraphEdges (c4SplitGraphOfCrossChoice D C)).card =
      Nat.choose D.cliquePart.card 2 + C.card := by
  rw [finiteGraphEdges_c4SplitGraphOfCrossChoice D hC,
    Finset.card_union_of_disjoint ((c4CliqueEdges_disjoint_cross D).mono_right hC),
    card_c4CliqueEdges]

/-- Every coordinate choice has exactly the independent/clique geometry. -/
theorem c4SplitGraphOfCrossChoice_geometry (D : C4Division V)
    {C : Finset (Sym2 V)} (hC : C ⊆ c4CrossPotentialEdges D) :
    (c4SplitGraphOfCrossChoice D C).IsIndepSet (D.independentPart : Set V) ∧
      (c4SplitGraphOfCrossChoice D C).IsClique (D.cliquePart : Set V) := by
  constructor
  · intro x hx y hy _hne hxy
    have he := (mk_mem_finiteGraphEdges _ x y).mpr hxy
    rw [finiteGraphEdges_c4SplitGraphOfCrossChoice D hC] at he
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.disjoint_left.mp D.disjoint hx ((mk_mem_c4CliqueEdges D x y).mp he).1
    · rcases (mk_mem_c4CrossPotentialEdges D x y).mp (hC he) with hc | hc
      · exact Finset.disjoint_left.mp D.disjoint hy hc.2
      · exact Finset.disjoint_left.mp D.disjoint hx hc.2
  · intro x hx y hy hne
    rw [← mk_mem_finiteGraphEdges, finiteGraphEdges_c4SplitGraphOfCrossChoice D hC]
    exact Finset.mem_union_left _ ((mk_mem_c4CliqueEdges D x y).mpr ⟨hx, hy, hne⟩)

/-- Any graph with this split geometry has precisely its forced clique
edges and its selected cross coordinates, with no other edges. -/
theorem finiteGraphEdges_eq_clique_union_cross_of_split (G : SimpleGraph V) (D : C4Division V)
    (hA : G.IsIndepSet (D.independentPart : Set V))
    (hB : G.IsClique (D.cliquePart : Set V)) :
    finiteGraphEdges G = c4CliqueEdges D ∪ c4CrossEdges G D := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [mk_mem_finiteGraphEdges, Finset.mem_union, mk_mem_c4CliqueEdges,
        c4CrossEdges, Finset.mem_inter, mk_mem_c4CrossPotentialEdges,
        C4Division.mem_cliquePart]
      by_cases hx : x ∈ D.independentPart <;> by_cases hy : y ∈ D.independentPart
      · have hn : ¬G.Adj x y := fun h ↦ hA hx hy h.ne h
        simp [hx, hy, hn]
      · simp [hx, hy]
      · simp [hx, hy]
      · simp only [hx, hy, not_false_eq_true, true_and, false_and, and_false,
          or_false, false_or]
        exact ⟨fun h ↦ h.ne, fun h ↦ hB ((D.mem_cliquePart x).mpr hx)
          ((D.mem_cliquePart y).mpr hy) h⟩

/-- Recovery of any graph in the prescribed split fiber. -/
theorem c4SplitGraphOfCrossChoice_crossEdges (G : SimpleGraph V) (D : C4Division V)
    (hA : G.IsIndepSet (D.independentPart : Set V))
    (hB : G.IsClique (D.cliquePart : Set V)) :
    c4SplitGraphOfCrossChoice D (c4CrossEdges G D) = G := by
  ext x y
  rw [← mk_mem_finiteGraphEdges, finiteGraphEdges_c4SplitGraphOfCrossChoice D
      (c4CrossEdges_subset G D), ← finiteGraphEdges_eq_clique_union_cross_of_split G D hA hB,
    mk_mem_finiteGraphEdges]

/-- Delete the independent-side defects and add the missing clique-side
edges, leaving every cross edge unchanged. -/
def c4SplitCompletion (G : SimpleGraph V) (D : C4Division V) : SimpleGraph V :=
  c4SplitGraphOfCrossChoice D (c4CrossEdges G D)

theorem c4SplitCompletion_geometry (G : SimpleGraph V) (D : C4Division V) :
    (c4SplitCompletion G D).IsIndepSet (D.independentPart : Set V) ∧
      (c4SplitCompletion G D).IsClique (D.cliquePart : Set V) :=
  c4SplitGraphOfCrossChoice_geometry D (c4CrossEdges_subset G D)

theorem c4SplitCompletion_isSplit (G : SimpleGraph V) (D : C4Division V) :
    DenseGraph.IsSplitGraph (c4SplitCompletion G D) :=
  ⟨⟨D.independentPart, D.cliquePart, D.disjoint, D.cover,
    (c4SplitCompletion_geometry G D).1, (c4SplitCompletion_geometry G D).2⟩⟩

@[simp] theorem c4SplitCompletion_adj (G : SimpleGraph V) (D : C4Division V) (x y : V) :
    (c4SplitCompletion G D).Adj x y ↔
      (x ∈ D.cliquePart ∧ y ∈ D.cliquePart ∧ x ≠ y) ∨
        (G.Adj x y ∧ ((x ∈ D.independentPart ∧ y ∈ D.cliquePart) ∨
          (y ∈ D.independentPart ∧ x ∈ D.cliquePart))) := by
  rw [← mk_mem_finiteGraphEdges (c4SplitCompletion G D) x y]
  change s(x, y) ∈ finiteGraphEdges (c4SplitGraphOfCrossChoice D (c4CrossEdges G D)) ↔ _
  rw [finiteGraphEdges_c4SplitGraphOfCrossChoice D (c4CrossEdges_subset G D)]
  simp only [Finset.mem_union, mk_mem_c4CliqueEdges,
    c4CrossEdges, Finset.mem_inter, mk_mem_finiteGraphEdges,
    mk_mem_c4CrossPotentialEdges]

/-- The source defect graph is exactly the unordered edit set of the
canonical split completion, not merely an upper bound on its edit cost. -/
theorem c4DefectGraph_edges_eq_splitCompletion_edits (G : SimpleGraph V)
    (D : C4Division V) :
    finiteGraphEdges (c4DefectGraph G D) =
      DenseGraph.simpleGraphEditFinset G (c4SplitCompletion G D) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    simp only [mk_mem_finiteGraphEdges, c4DefectGraph_adj,
      DenseGraph.mem_simpleGraphEditFinset, SimpleGraph.mem_edgeSet,
      c4SplitCompletion_adj, C4Division.mem_cliquePart]
    by_cases heq : x = y
    · subst y
      simp
    · tauto

theorem c4DefectCost_eq_splitCompletion_editDistance (G : SimpleGraph V)
    (D : C4Division V) :
    c4DefectCost G D = DenseGraph.simpleGraphEditDistance G (c4SplitCompletion G D) := by
  rw [c4DefectCost, DenseGraph.simpleGraphEditDistance,
    c4DefectGraph_edges_eq_splitCompletion_edits]

/-- Moving the missing clique edges to the left and the independent-side
edges to the right gives an equality without truncated subtraction. -/
theorem c4EdgeCount_add_cliqueDefects (G : SimpleGraph V) (D : C4Division V) :
    (finiteGraphEdges G).card +
        (finiteGraphEdges (Gᶜ.induce (D.cliquePart : Set V))).card =
      Nat.choose D.cliquePart.card 2 + (c4CrossEdges G D).card +
        (finiteGraphEdges (G.induce (D.independentPart : Set V))).card := by
  classical
  have heq : finiteGraphEdges G ∪ finiteGraphEdges (c4WithinGraph Gᶜ D.cliquePart) =
      finiteGraphEdges (c4SplitCompletion G D) ∪
        finiteGraphEdges (c4WithinGraph G D.independentPart) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
      simp only [Finset.mem_union, mk_mem_finiteGraphEdges, c4WithinGraph_adj,
        SimpleGraph.compl_adj, c4SplitCompletion_adj, C4Division.mem_cliquePart]
      by_cases heq : x = y
      · subst y
        simp
      · tauto
  have hleft : Disjoint (finiteGraphEdges G)
      (finiteGraphEdges (c4WithinGraph Gᶜ D.cliquePart)) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.inductionOn with
    | _ x y =>
      have he' := (mk_mem_finiteGraphEdges _ _ _).mp he
      have hf' := (mk_mem_finiteGraphEdges _ _ _).mp hf
      exact hf'.2.2.2 he'
  have hright : Disjoint (finiteGraphEdges (c4SplitCompletion G D))
      (finiteGraphEdges (c4WithinGraph G D.independentPart)) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.inductionOn with
    | _ x y =>
      have he' := (mk_mem_finiteGraphEdges _ _ _).mp he
      have hf' := (mk_mem_finiteGraphEdges _ _ _).mp hf
      exact (c4SplitCompletion_geometry G D).1 hf'.1 hf'.2.1 he'.ne he'
  have hcard := congrArg Finset.card heq
  rw [Finset.card_union_of_disjoint hleft, Finset.card_union_of_disjoint hright,
    card_finiteGraphEdges_c4WithinGraph, card_finiteGraphEdges_c4WithinGraph,
    show (finiteGraphEdges (c4SplitCompletion G D)).card =
      Nat.choose D.cliquePart.card 2 + (c4CrossEdges G D).card from
      card_edges_c4SplitGraphOfCrossChoice D (c4CrossEdges_subset G D)] at hcard
  exact hcard

/-- The signed defect convention in the source: independent-side edges
increase the edge count, whereas missing clique edges decrease it. -/
theorem c4EdgeCount_eq_clique_add_cross_add_signedDefects (G : SimpleGraph V)
    (D : C4Division V) :
    ((finiteGraphEdges G).card : ℤ) =
      (Nat.choose D.cliquePart.card 2 : ℤ) + (c4CrossEdges G D).card +
        (finiteGraphEdges (G.induce (D.independentPart : Set V))).card -
        (finiteGraphEdges (Gᶜ.induce (D.cliquePart : Set V))).card := by
  have h := c4EdgeCount_add_cliqueDefects G D
  omega

/-- The exact labeled split fiber with one prescribed ordered partition
and one prescribed unordered edge count. -/
def c4SplitFiber {n : ℕ} (D : C4Division (Fin n)) (m : ℕ) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact Finset.univ.filter fun G ↦
    G.IsIndepSet (D.independentPart : Set (Fin n)) ∧
      G.IsClique (D.cliquePart : Set (Fin n)) ∧ (finiteGraphEdges G).card = m

@[simp] theorem mem_c4SplitFiber {n m : ℕ} {D : C4Division (Fin n)}
    {G : SimpleGraph (Fin n)} :
    G ∈ c4SplitFiber D m ↔
      G.IsIndepSet (D.independentPart : Set (Fin n)) ∧
        G.IsClique (D.cliquePart : Set (Fin n)) ∧ (finiteGraphEdges G).card = m := by
  classical
  simp [c4SplitFiber]

local instance {n : ℕ} : DecidableEq (SimpleGraph (Fin n)) := Classical.decEq _

/-- Exact enumeration by a fixed-size subset of the cross-coordinate
universe. Below the forced clique edge count there are no graphs. -/
theorem c4SplitFiber_eq_crossChoice_image {n : ℕ} (D : C4Division (Fin n)) (m : ℕ) :
    c4SplitFiber D m =
      if Nat.choose D.cliquePart.card 2 ≤ m then
        ((c4CrossPotentialEdges D).powersetCard (m - Nat.choose D.cliquePart.card 2)).image
          (c4SplitGraphOfCrossChoice D)
      else ∅ := by
  classical
  by_cases hm : Nat.choose D.cliquePart.card 2 ≤ m
  · rw [if_pos hm]
    ext G
    constructor
    · intro hG
      obtain ⟨hA, hB, he⟩ := mem_c4SplitFiber.mp hG
      have hcard := card_edges_c4SplitGraphOfCrossChoice D (c4CrossEdges_subset G D)
      rw [c4SplitGraphOfCrossChoice_crossEdges G D hA hB, he] at hcard
      exact Finset.mem_image.mpr ⟨c4CrossEdges G D,
        Finset.mem_powersetCard.mpr ⟨c4CrossEdges_subset G D, by omega⟩,
        c4SplitGraphOfCrossChoice_crossEdges G D hA hB⟩
    · intro hG
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hG
      obtain ⟨hC, hcard⟩ := Finset.mem_powersetCard.mp hC
      obtain ⟨hA, hB⟩ := c4SplitGraphOfCrossChoice_geometry D hC
      refine mem_c4SplitFiber.mpr ⟨hA, hB, ?_⟩
      rw [card_edges_c4SplitGraphOfCrossChoice D hC, hcard]
      omega
  · rw [if_neg hm]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro G hG
    obtain ⟨hA, hB, he⟩ := mem_c4SplitFiber.mp hG
    have hcard := card_edges_c4SplitGraphOfCrossChoice D (c4CrossEdges_subset G D)
    rw [c4SplitGraphOfCrossChoice_crossEdges G D hA hB, he] at hcard
    omega

/-- The exact binomial cardinality of the split fiber, including all empty
sides and infeasible counts. The upper feasibility guard is provided by
`Nat.choose = 0` when the selected count exceeds capacity. -/
theorem card_c4SplitFiber {n : ℕ} (D : C4Division (Fin n)) (m : ℕ) :
    (c4SplitFiber D m).card =
      if Nat.choose D.cliquePart.card 2 ≤ m then
        Nat.choose (D.independentPart.card * D.cliquePart.card)
          (m - Nat.choose D.cliquePart.card 2)
      else 0 := by
  classical
  rw [c4SplitFiber_eq_crossChoice_image]
  by_cases hm : Nat.choose D.cliquePart.card 2 ≤ m
  · rw [if_pos hm, if_pos hm, Finset.card_image_iff.mpr]
    · rw [Finset.card_powersetCard, card_c4CrossPotentialEdges]
    · intro C hC E hE heq
      exact c4SplitGraphOfCrossChoice_injectiveOn D
        (Finset.mem_powersetCard.mp hC).1 (Finset.mem_powersetCard.mp hE).1 heq
  · simp [hm]

theorem c4SplitFiber_subset_splitGraphFinsetWithEdges {n m : ℕ} (D : C4Division (Fin n)) :
    c4SplitFiber D m ⊆ splitGraphFinsetWithEdges n m := by
  intro G hG
  obtain ⟨hA, hB, hm⟩ := mem_c4SplitFiber.mp hG
  refine mem_splitGraphFinsetWithEdges.mpr ⟨?_, hm⟩
  exact ⟨⟨D.independentPart, D.cliquePart, D.disjoint, D.cover, hA, hB⟩⟩

end InducedStars
