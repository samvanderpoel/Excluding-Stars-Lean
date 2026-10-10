import InducedStars.Structure.Subcritical.ComponentReplacement
import InducedStars.Structure.Subcritical.DivisionMoveBounds

/-!
# Singleton-safe source comparisons

Comparison divisions are constructed from genuine regular cores and
nonempty parts. No singleton source part is removed in an unchanged core.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

def subcriticalSubsetEmbedding (S A : Finset V) (hSA : S ⊆ A) : S ↪ A where
  toFun x := ⟨x.val, hSA x.property⟩
  inj' := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : A ↦ z.val) h)

theorem subcriticalSubsetEmbedding_map_adj (S A : Finset V) (hSA : S ⊆ A)
    (H : SimpleGraph S) (x y : A) :
    (H.map (subcriticalSubsetEmbedding S A hSA)).Adj x y ↔
      H.spanningCoe.Adj x.val y.val := by
  simp only [SimpleGraph.spanningCoe, SimpleGraph.map_adj]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨u, v, huv, congrArg Subtype.val hu, congrArg Subtype.val hv⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨u, v, huv, Subtype.ext hu, Subtype.ext hv⟩

theorem subcriticalSingletonComponent_not_samePart
    (D : SubcriticalDivision k V) (i : Fin D.componentCount)
    (hsingle : ∀ j, (D.parts i j).card = 1)
    {x y : V} (hx : x ∈ D.componentSupport i) (hxy : x ≠ y) :
    ¬ D.SamePart x y := by
  obtain ⟨j, hj⟩ := D.mem_componentSupport.mp hx
  rintro ⟨a, hxa, hya⟩
  have ha := D.mem_part_unique (a := ⟨i, j⟩) hj hxa
  subst a
  exact hxy (((D.mem_singletonComponentPart_iff i hsingle j x).mp hj).trans
    ((D.mem_singletonComponentPart_iff i hsingle j y).mp hya).symm)

theorem subcriticalReplacement_model_away_source
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (i : Fin D.componentCount)
    (S : Finset V) (hS : S ⊆ D.componentSupport i)
    (H : SimpleGraph S) (hr : H.IsRegularOfDegree (k - 2))
    (hother : ∃ j : Fin D.componentCount, j ≠ i)
    {x y : V} (hx : x ∉ D.componentSupport i) :
    (subcriticalDivisionModelGraph G (D.replaceComponent i S hS H hr hother)).Adj x y ↔
      (subcriticalDivisionModelGraph G D).Adj x y := by
  have hxS : x ∉ S := fun h ↦ hx (hS h)
  have hH : ¬ H.spanningCoe.Adj x y := by
    intro h
    rw [SimpleGraph.spanningCoe, SimpleGraph.map_adj] at h
    obtain ⟨u, v, _, hu, _⟩ := h
    exact hxS (hu ▸ u.property)
  simp only [subcriticalDivisionModelGraph_adj, D.replaceComponent_samePart,
    D.replaceComponent_activePair, hx, hxS, hH, not_false_eq_true,
    and_true, and_false, or_false]

/-- Replacing an all-singleton component costs at most the actual number of
core-edge edits, after adding removed source vertices back as isolates. -/
theorem subcriticalReplaceSingletonComponent_cost_le
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (i : Fin D.componentCount)
    (hsingle : ∀ j, (D.parts i j).card = 1)
    (S : Finset V) (hS : S ⊆ D.componentSupport i)
    (H : SimpleGraph S) (hr : H.IsRegularOfDegree (k - 2))
    (hother : ∃ j : Fin D.componentCount, j ≠ i) :
    subcriticalDefectCost G (D.replaceComponent i S hS H hr hother) ≤
      subcriticalDefectCost G D + DenseGraph.simpleGraphEditDistance
        (D.singletonComponentCoreGraph i hsingle)
        (H.map (subcriticalSubsetEmbedding S (D.componentSupport i) hS)) := by
  let E := D.replaceComponent i S hS H hr hother
  let M := subcriticalDivisionModelGraph G D
  let N := subcriticalDivisionModelGraph G E
  let Q := D.singletonComponentCoreGraph i hsingle
  let J := H.map (subcriticalSubsetEmbedding S (D.componentSupport i) hS)
  let f := Function.Embedding.subtype (· ∈ (D.componentSupport i : Set V))
  have hsub : DenseGraph.simpleGraphEditFinset M N ⊆
      (DenseGraph.simpleGraphEditFinset Q J).map f.sym2Map := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hdiff := he
      simp only [DenseGraph.mem_simpleGraphEditFinset, SimpleGraph.mem_edgeSet] at hdiff
      have hxy : x ≠ y := by
        rcases hdiff with ⟨hm, _⟩ | ⟨hn, _⟩ <;> exact SimpleGraph.Adj.ne (by assumption)
      have hx : x ∈ D.componentSupport i := by
        by_contra hx
        have ha := subcriticalReplacement_model_away_source G D i S hS H hr hother (y := y) hx
        change N.Adj x y ↔ M.Adj x y at ha
        tauto
      have hy : y ∈ D.componentSupport i := by
        by_contra hy
        have ha := subcriticalReplacement_model_away_source G D i S hS H hr hother (y := x) hy
        change N.Adj y x ↔ M.Adj y x at ha
        rw [N.adj_comm y x, M.adj_comm y x] at ha
        tauto
      let x' : (D.componentSupport i : Set V) := ⟨x, hx⟩
      let y' : (D.componentSupport i : Set V) := ⟨y, hy⟩
      have hsame := subcriticalSingletonComponent_not_samePart D i hsingle hx hxy
      have hM : M.Adj x y ↔ Q.Adj x' y' ∧ G.Adj x y := by
        rw [D.singletonComponentCoreGraph_adj]
        simp [M, subcriticalDivisionModelGraph_adj, hxy, hsame, x', y']
      have hN : N.Adj x y ↔ J.Adj x' y' ∧ G.Adj x y := by
        rw [subcriticalSubsetEmbedding_map_adj]
        simp [N, E, subcriticalDivisionModelGraph_adj, D.replaceComponent_samePart,
          D.replaceComponent_activePair, hx, hxy, x', y']
      refine Finset.mem_map.mpr ⟨s(x', y'), ?_, rfl⟩
      simp only [DenseGraph.mem_simpleGraphEditFinset, SimpleGraph.mem_edgeSet]
      rw [hM, hN] at hdiff
      tauto
  have hedit : DenseGraph.simpleGraphEditDistance M N ≤ DenseGraph.simpleGraphEditDistance Q J := by
    exact (Finset.card_le_card hsub).trans_eq (Finset.card_map _)
  exact (subcriticalDefectCost_le_add_modelEdit G D E).trans (Nat.add_le_add_left hedit _)

/-- Flatten the surviving vertices after deleting two vertices inside an
actual component subtype. The map preserves the underlying ambient vertex. -/
def subcriticalEraseTwoFlattenEquiv (A : Finset V) (v w : A) :
    {x : A // x ∈ (Finset.univ \ {v, w} : Finset A)} ≃
      {x : V // x ∈ (A \ {v.val, w.val} : Finset V)} where
  toFun x := ⟨x.val.val, by
    have hx : x.val ≠ v ∧ x.val ≠ w := by simpa using x.property
    apply Finset.mem_sdiff.mpr
    refine ⟨x.val.property, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h ↦ hx.1 (Subtype.ext h), fun h ↦ hx.2 (Subtype.ext h)⟩⟩
  invFun x := ⟨⟨x.val, (Finset.mem_sdiff.mp x.property).1⟩, by
    have hx : x.val ≠ v.val ∧ x.val ≠ w.val := by
      simpa using (Finset.mem_sdiff.mp x.property).2
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h ↦ hx.1 (congrArg Subtype.val h), fun h ↦ hx.2 (congrArg Subtype.val h)⟩⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

set_option maxHeartbeats 1600000 in
/-- A large all-singleton source component permits a genuine comparison
division that frees the prescribed vertex at at most `5*(k-2)` edit cost.
Every other part survives verbatim. The replacement core may split into
several connected regular components. -/
theorem subcriticalSingleton_large_core_sparse_comparison
    (hk : 3 ≤ k) (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (hsingle : ∀ j, (D.parts i j).card = 1)
    (hlarge : 4 * (k - 2) + 8 < (D.core i).order)
    (v : V) (hv : v ∈ D.componentSupport i)
    (hother : ∃ j : Fin D.componentCount, j ≠ i) :
    ∃ E : SubcriticalDivision k V, v ∈ E.sparse ∧
      (∀ a : D.PartIndex, a.1 ≠ i → ∃ b : E.PartIndex, E.part b = D.part a) ∧
      subcriticalDefectCost G E ≤ subcriticalDefectCost G D + 5 * (k - 2) := by
  let A := D.componentSupport i
  let Q := D.singletonComponentCoreGraph i hsingle
  let vA : A := ⟨v, hv⟩
  have hcard : Fintype.card A = (D.core i).order := by
    rw [Fintype.card_coe]
    exact D.singletonComponent_card i hsingle
  have hlargeA : 4 * (k - 2) + 8 < Fintype.card A := by omega
  letI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨wA, hwv⟩ := exists_ne vA
  have hvw : vA ≠ wA := hwv.symm
  have hQ : Q.IsRegularOfDegree (k - 2) := D.singletonComponentCoreGraph_regular i hsingle
  obtain ⟨H₀, hH₀, hdist⟩ := DenseGraph.exists_regular_after_deleting_two_spanning_edit
    Q (k - 2) hQ (by omega) hlargeA vA wA hvw
  let S : Finset V := A \ {v, wA.val}
  have hS : S ⊆ D.componentSupport i := Finset.sdiff_subset
  let e := subcriticalEraseTwoFlattenEquiv A vA wA
  let H : SimpleGraph S := H₀.map e.toEmbedding
  letI : DecidableRel H.Adj := Classical.decRel _
  have hr : H.IsRegularOfDegree (k - 2) := by
    intro x
    exact ((SimpleGraph.Iso.map e H₀).symm.degree_eq x).symm.trans (hH₀.degree_eq (e.symm x))
  let E := D.replaceComponent i S hS H hr hother
  refine ⟨E, ?_, ?_, ?_⟩
  · rw [D.replaceComponent_sparse]
    apply Finset.mem_union_right
    exact Finset.mem_sdiff.mpr ⟨hv, by simp [S]⟩
  · intro a ha
    exact D.replaceComponent_exists_untouched_part i S hS H hr hother a ha
  · have hmap : H.map (subcriticalSubsetEmbedding S A hS) =
        H₀.map (Function.Embedding.subtype
          (· ∈ ((Finset.univ \ {vA, wA} : Finset A) : Set A))) := by
      ext x y
      simp only [H, SimpleGraph.map_adj]
      constructor
      · rintro ⟨u, z, ⟨s, t, hst, hsu, htz⟩, hux, hzy⟩
        refine ⟨s, t, hst, ?_, ?_⟩
        · rw [← hsu] at hux
          exact Subtype.ext (congrArg (fun p : A ↦ p.val) hux)
        · rw [← htz] at hzy
          exact Subtype.ext (congrArg (fun p : A ↦ p.val) hzy)
      · rintro ⟨s, t, hst, hsx, hty⟩
        refine ⟨e s, e t, ⟨s, t, hst, rfl, rfl⟩, ?_, ?_⟩
        · exact Subtype.ext (congrArg (fun p : A ↦ p.val) hsx)
        · exact Subtype.ext (congrArg (fun p : A ↦ p.val) hty)
    have hcost := subcriticalReplaceSingletonComponent_cost_le G D i hsingle S hS H hr hother
    change subcriticalDefectCost G E ≤ subcriticalDefectCost G D +
      DenseGraph.simpleGraphEditDistance Q (H.map (subcriticalSubsetEmbedding S A hS)) at hcost
    rw [hmap] at hcost
    exact hcost.trans (Nat.add_le_add_left hdist _)

end InducedStars
