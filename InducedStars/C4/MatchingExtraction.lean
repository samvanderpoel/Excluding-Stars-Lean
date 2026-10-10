import InducedStars.C4.MatchingPenalty
import DenseGraph.Combinatorics.BoundedDegreeCounting

/-!
# Actual oriented matchings for the C4 penalty

Paper: Lemma `lemma:c4-matching`. This module passes from graph matchings
to the injectively indexed endpoints used by the random-coordinate model.
-/

noncomputable section
open Finset
open scoped Classical

namespace InducedStars

variable {V : Type*} [Fintype V] [DecidableEq V]

private def c4MatchingEndpoint {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (_hE : DenseGraph.IsEdgeMatching G E) (p : ↥E × Fin 2) : V :=
  if p.2 = 0 then p.1.val.out.1 else p.1.val.out.2

private theorem c4MatchingEndpoint_mem {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (hE : DenseGraph.IsEdgeMatching G E) (p : ↥E × Fin 2) :
    c4MatchingEndpoint hE p ∈ (p.1.val : Set V) := by
  have heq : s(p.1.val.out.1, p.1.val.out.2) = p.1.val := p.1.val.out_eq
  have h1 : p.1.val.out.1 ∈ (p.1.val : Set V) := by
    have h : p.1.val.out.1 ∈ (s(p.1.val.out.1, p.1.val.out.2) : Set V) := by simp
    rwa [heq] at h
  have h2 : p.1.val.out.2 ∈ (p.1.val : Set V) := by
    have h : p.1.val.out.2 ∈ (s(p.1.val.out.1, p.1.val.out.2) : Set V) := by simp
    rwa [heq] at h
  simp only [c4MatchingEndpoint]
  split_ifs <;> assumption

private theorem c4MatchingEndpoint_injective {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (hE : DenseGraph.IsEdgeMatching G E) : Function.Injective (c4MatchingEndpoint hE) := by
  rintro ⟨e, a⟩ ⟨f, b⟩ hab
  have hef : e = f := by
    by_contra h
    have hne : e.val ≠ f.val := fun h' ↦ h (Subtype.ext h')
    have hd := hE.2 e.prop f.prop hne
    exact Set.disjoint_left.mp hd (c4MatchingEndpoint_mem hE (e, a))
      (hab ▸ c4MatchingEndpoint_mem hE (f, b))
  subst f
  have hadj : G.Adj e.val.out.1 e.val.out.2 := by
    have he := hE.1 e.val e.prop
    rw [← e.val.out_eq] at he
    exact he
  have ha : a = b := by
    fin_cases a <;> fin_cases b <;> simp_all [c4MatchingEndpoint, hadj.ne, hadj.ne']
  exact Prod.ext rfl ha

/-- Every actual edge matching has an injective orientation indexed by its
cardinality. No ordering of the ambient vertex type is required. -/
theorem c4_exists_orientedMatching {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (hE : DenseGraph.IsEdgeMatching G E) :
    ∃ f : (Fin E.card × Fin 2) ↪ V, ∀ i, G.Adj (f (i, 0)) (f (i, 1)) := by
  let e : Fin E.card ≃ ↥E := (Fintype.equivFinOfCardEq (by simp)).symm
  let f : (Fin E.card × Fin 2) ↪ V :=
    (Equiv.prodCongr e (Equiv.refl (Fin 2))).toEmbedding.trans
      ⟨c4MatchingEndpoint hE, c4MatchingEndpoint_injective hE⟩
  refine ⟨f, ?_⟩
  intro i
  change G.Adj (c4MatchingEndpoint hE (e i, 0)) (c4MatchingEndpoint hE (e i, 1))
  simp only [c4MatchingEndpoint, ↓reduceIte, Fin.zero_ne_one, show (1 : Fin 2) ≠ 0 by decide]
  have he := hE.1 (e i).val (e i).prop
  rw [← (e i).val.out_eq] at he
  exact he

/-- A maximum matching in an induced side, oriented on the ambient type. -/
theorem c4_exists_orientedMaximumWithinMatching (G : SimpleGraph V) (S : Finset V) :
    ∃ f : (Fin (DenseGraph.matchingNumber (c4WithinGraph G S)) × Fin 2) ↪ V,
      (∀ i a, f (i, a) ∈ S) ∧ ∀ i, G.Adj (f (i, 0)) (f (i, 1)) := by
  let H := c4WithinGraph G S
  let E := DenseGraph.matchingEdgeFinset (DenseGraph.canonicalMaximumMatching H)
  have hE : DenseGraph.IsEdgeMatching H E :=
    DenseGraph.matchingEdgeFinset_isEdgeMatching (DenseGraph.canonicalMaximumMatching_isMatching H)
  have hcard : E.card = DenseGraph.matchingNumber H := by
    simp only [E, DenseGraph.card_matchingEdgeFinset, DenseGraph.matchingNumber]
  have hex := c4_exists_orientedMatching hE
  rw [hcard] at hex
  obtain ⟨f, hf⟩ := hex
  refine ⟨f, ?_, fun i ↦ (hf i).2.2⟩
  intro i a
  fin_cases a
  · exact (hf i).1
  · exact (hf i).2.1

theorem c4_exists_orientedWithinMatching (G : SimpleGraph V) (S : Finset V) (q : ℕ)
    (hq : q ≤ DenseGraph.matchingNumber (c4WithinGraph G S)) :
    ∃ f : (Fin q × Fin 2) ↪ V,
      (∀ i a, f (i, a) ∈ S) ∧ ∀ i, G.Adj (f (i, 0)) (f (i, 1)) := by
  obtain ⟨f, hmem, hadj⟩ := c4_exists_orientedMaximumWithinMatching G S
  let j : (Fin q × Fin 2) ↪
      (Fin (DenseGraph.matchingNumber (c4WithinGraph G S)) × Fin 2) :=
    Function.Embedding.prodMap (Fin.castLEEmb hq) (Function.Embedding.refl _)
  exact ⟨j.trans f, fun i a ↦ hmem _ a, fun i ↦ hadj _⟩

end InducedStars
