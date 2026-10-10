import DenseGraph.FiniteModels.Multipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Identification of an isolated connected support

Two connected vertex sets with no edges to their complements are either
equal or disjoint. A lower bound on the edges in one set, exceeding the
other set's remainder edge count, rules out disjointness. All graphs are
literal induced graphs on the original subtype vertex sets.
-/

noncomputable section
open Finset Set
open InducedStars
namespace DenseGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem mem_of_reachable_of_noCross {S : Set V} {x y : V}
    (hcross : ∀ a ∈ S, ∀ b ∉ S, ¬G.Adj a b) (hxy : G.Reachable x y) (hx : x ∈ S) : y ∈ S := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact hx
  | @cons a b c hab p ih =>
    apply ih
    by_contra hb
    exact hcross a hx b hb hab

theorem isolated_preconnected_subset_of_inter
    {S T : Set V} (hS : (G.induce S).Preconnected)
    (hcrossT : ∀ x ∈ T, ∀ y ∉ T, ¬G.Adj x y)
    (hinter : (S ∩ T).Nonempty) : S ⊆ T := by
  obtain ⟨x, hxS, hxT⟩ := hinter
  intro y hy
  have hreach : G.Reachable x y :=
    (hS ⟨x, hxS⟩ ⟨y, hy⟩).map (SimpleGraph.Embedding.induce S).toHom
  exact mem_of_reachable_of_noCross hcrossT hreach hxT

theorem isolated_preconnected_eq_or_disjoint
    {S T : Set V} (hS : (G.induce S).Preconnected) (hT : (G.induce T).Preconnected)
    (hcrossS : ∀ x ∈ S, ∀ y ∉ S, ¬G.Adj x y)
    (hcrossT : ∀ x ∈ T, ∀ y ∉ T, ¬G.Adj x y) : S = T ∨ Disjoint S T := by
  by_cases h : (S ∩ T).Nonempty
  · exact Or.inl (Subset.antisymm
      (isolated_preconnected_subset_of_inter hS hcrossT h)
      (isolated_preconnected_subset_of_inter hT hcrossS (by simpa [inter_comm] using h)))
  · exact Or.inr (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h))

/-- Monotonicity of the actual induced unordered-edge count under vertex
set inclusion. -/
theorem finiteGraphEdges_induce_card_mono {S T : Set V} (hST : S ⊆ T) :
    (finiteGraphEdges (G.induce S)).card ≤ (finiteGraphEdges (G.induce T)).card := by
  classical
  let f : S ↪ T := ⟨fun x ↦ ⟨x.val, hST x.property⟩,
    fun _ _ h ↦ Subtype.ext (congrArg (fun z : T ↦ z.val) h)⟩
  have hsub : (finiteGraphEdges (G.induce S)).map f.sym2Map ⊆ finiteGraphEdges (G.induce T) := by
    intro e he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp he
    induction z using Sym2.inductionOn with
    | _ x y =>
      have hxy := (mk_mem_finiteGraphEdges (G.induce S) x y).mp hz
      exact (mk_mem_finiteGraphEdges (G.induce T) (f x) (f y)).mpr hxy
  simpa only [Finset.card_map] using Finset.card_le_card hsub

/-- A connected isolated support with more edges than the competing
remainder is uniquely identified. No unmarked construction is asserted
injective; cover-label multiplicities are counted separately. -/
theorem isolated_preconnected_support_eq_of_edgeCount_gt
    {S T : Set V} (hS : (G.induce S).Preconnected) (hT : (G.induce T).Preconnected)
    (hcrossS : ∀ x ∈ S, ∀ y ∉ S, ¬G.Adj x y)
    (hcrossT : ∀ x ∈ T, ∀ y ∉ T, ¬G.Adj x y)
    (hedge : (finiteGraphEdges (G.induce Tᶜ)).card < (finiteGraphEdges (G.induce S)).card) : S = T := by
  rcases isolated_preconnected_eq_or_disjoint hS hT hcrossS hcrossT with h | h
  · exact h
  · have hST : S ⊆ Tᶜ := fun x hx ↦ fun hxT ↦ Set.disjoint_left.mp h hx hxT
    exact (not_lt_of_ge (finiteGraphEdges_induce_card_mono hST)) hedge |>.elim

/-- An actual clique contributes every unordered pair to the induced
support edge count. -/
theorem choose_card_le_inducedEdgeCount_of_clique
    {S : Set V} (P : Finset V) (hP : (P : Set V) ⊆ S) (hclique : G.IsClique (P : Set V)) :
    P.card.choose 2 ≤ (finiteGraphEdges (G.induce S)).card := by
  classical
  have htop : G.induce (P : Set V) = ⊤ := by
    ext x y
    simp only [SimpleGraph.induce_adj, SimpleGraph.top_adj]
    exact ⟨fun h ↦ fun heq ↦ h.ne (congrArg Subtype.val heq),
      fun h ↦ hclique x.property y.property (fun heq ↦ h (Subtype.ext heq))⟩
  have hcard : (finiteGraphEdges (G.induce (P : Set V))).card = P.card.choose 2 := by
    rw [htop]
    have heq : finiteGraphEdges (⊤ : SimpleGraph (P : Set V)) = (⊤ : SimpleGraph (P : Set V)).edgeFinset := by
      ext z
      rw [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
    rw [heq, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    simp
  rw [← hcard]
  exact finiteGraphEdges_induce_card_mono hP

/-- A linear-size clique has a quadratic number of edges, with the finite
large-order reserve stated explicitly. -/
theorem quarter_linear_square_le_choose {a : ℝ} {n t : ℕ}
    (ha : 0 ≤ a) (ht : a * n ≤ t) (hlarge : 2 ≤ a * n) :
    a ^ 2 * (n : ℝ) ^ 2 / 4 ≤ (t.choose 2 : ℝ) := by
  rw [Nat.cast_choose_two]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have ht2 : (2 : ℝ) ≤ t := hlarge.trans ht
  have hsq : a ^ 2 * (n : ℝ) ^ 2 ≤ (t : ℝ) ^ 2 := by
    nlinarith [mul_nonneg ha hn]
  nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht2)]

/-- A single linear-size clique identifies a connected isolated support
against any other connected isolated support with a sufficiently low-edge
remainder. No independence-number assertion is required for this route. -/
theorem isolated_support_eq_of_clique_and_sparse_remainder
    {S T : Set V} {a B : ℝ}
    (hS : (G.induce S).Preconnected) (hT : (G.induce T).Preconnected)
    (hcrossS : ∀ x ∈ S, ∀ y ∉ S, ¬G.Adj x y)
    (hcrossT : ∀ x ∈ T, ∀ y ∉ T, ¬G.Adj x y)
    (P : Finset V) (hP : (P : Set V) ⊆ S) (hclique : G.IsClique (P : Set V))
    (ha : 0 ≤ a) (hsize : a * Fintype.card V ≤ P.card)
    (hlarge : 2 ≤ a * Fintype.card V) (hB : B < a ^ 2 / 4)
    (hrem : (finiteGraphEdges (G.induce Tᶜ)).card ≤ B * (Fintype.card V : ℝ) ^ 2) : S = T := by
  apply isolated_preconnected_support_eq_of_edgeCount_gt hS hT hcrossS hcrossT
  have hchoose := quarter_linear_square_le_choose ha hsize hlarge
  have hcliqueEdges := choose_card_le_inducedEdgeCount_of_clique P hP hclique
  have hn : (0 : ℝ) < Fintype.card V := by
    have hn0 := Nat.cast_nonneg (α := ℝ) (Fintype.card V)
    by_contra hn
    have hz : (Fintype.card V : ℝ) = 0 := le_antisymm (le_of_not_gt hn) hn0
    rw [hz, mul_zero] at hlarge
    norm_num at hlarge
  have hstrict := mul_lt_mul_of_pos_right hB (sq_pos_of_pos hn)
  have hcliqueEdgesR : (P.card.choose 2 : ℝ) ≤ (finiteGraphEdges (G.induce S)).card := by
    exact_mod_cast hcliqueEdges
  have hedge : ((finiteGraphEdges (G.induce Tᶜ)).card : ℝ) <
      (finiteGraphEdges (G.induce S)).card := by nlinarith
  exact_mod_cast hedge

end DenseGraph
