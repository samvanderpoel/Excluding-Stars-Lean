import DenseGraph.Combinatorics.Matching
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Labeled matching counts

Pairing the images of an injective list gives a matching.  A fixed matching
has at most `q! * 2^q` such descriptions: an ordering and an orientation of
its edges.  This gives the factorial lower bound needed in labeled switching
arguments without making an unmarked switching injectivity assumption.
-/

noncomputable section

namespace DenseGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges obtained by pairing an injective list of `2*q` vertices. -/
def pairedEmbeddingEdges {q : ℕ} (f : (Fin q × Fin 2) ↪ V) : Finset (Sym2 V) :=
  Finset.univ.image (fun i ↦ s(f (i, 0), f (i, 1)))

theorem pairedEmbedding_edge_injective {q : ℕ} (f : (Fin q × Fin 2) ↪ V) :
    Function.Injective (fun i ↦ s(f (i, 0), f (i, 1))) := by
  intro i j h
  rcases Sym2.eq_iff.mp h with h | h
  · exact congrArg Prod.fst (f.injective h.1)
  · have := congrArg Prod.snd (f.injective h.1)
    norm_num at this

@[simp] theorem pairedEmbeddingEdges_card {q : ℕ} (f : (Fin q × Fin 2) ↪ V) :
    (pairedEmbeddingEdges f).card = q := by
  rw [pairedEmbeddingEdges, Finset.card_image_of_injective _ (pairedEmbedding_edge_injective f)]
  simp

theorem pairedEmbeddingEdges_isEdgeMatching {q : ℕ} (f : (Fin q × Fin 2) ↪ V) :
    IsEdgeMatching ⊤ (pairedEmbeddingEdges f) := by
  constructor
  · intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    change f (i, 0) ≠ f (i, 1)
    intro h
    have := congrArg Prod.snd (f.injective h)
    norm_num at this
  · intro e he e' he' hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he'
    have hij : i ≠ j := by intro h; subst j; exact hne rfl
    apply Set.disjoint_left.mpr
    intro v hv hw
    change v ∈ s(f (i, 0), f (i, 1)) at hv
    change v ∈ s(f (j, 0), f (j, 1)) at hw
    simp only [Sym2.mem_iff] at hv hw
    rcases hv with hv | hv <;> rcases hw with hw | hw
    all_goals exact hij (congrArg Prod.fst (f.injective (hv.symm.trans hw)))

/-- All `q`-edge matchings on a fixed finite labeled vertex set. -/
def edgeMatchingFinset (V : Type*) [Fintype V] [DecidableEq V] (q : ℕ) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact Finset.univ.filter (fun E ↦ IsEdgeMatching ⊤ E ∧ E.card = q)

@[simp] theorem mem_edgeMatchingFinset {q : ℕ} {E : Finset (Sym2 V)} :
    E ∈ edgeMatchingFinset V q ↔ IsEdgeMatching ⊤ E ∧ E.card = q := by
  classical
  simp [edgeMatchingFinset]

private def pairedEdgeOrder {q : ℕ} (E : Finset (Sym2 V))
    (f : {f : (Fin q × Fin 2) ↪ V // pairedEmbeddingEdges f = E}) : Fin q ↪ E where
  toFun i := ⟨s(f.1 (i, 0), f.1 (i, 1)), by
    have hh : s(f.1 (i, 0), f.1 (i, 1)) ∈ pairedEmbeddingEdges f.1 :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    simpa only [f.2] using hh⟩
  inj' i j h := pairedEmbedding_edge_injective f.1 (congrArg Subtype.val h)

private def pairedDescription [LinearOrder V] {q : ℕ} (E : Finset (Sym2 V))
    (f : {f : (Fin q × Fin 2) ↪ V // pairedEmbeddingEdges f = E}) :
    (Fin q ↪ E) × (Fin q → Bool) :=
  (pairedEdgeOrder E f, fun i ↦ decide (f.1 (i, 0) < f.1 (i, 1)))

private theorem pairedDescription_injective [LinearOrder V] {q : ℕ}
    (E : Finset (Sym2 V)) : Function.Injective (pairedDescription (q := q) E) := by
  intro f g h
  apply Subtype.ext
  apply Function.Embedding.ext
  rintro ⟨i, j⟩
  have he : s(f.1 (i, 0), f.1 (i, 1)) = s(g.1 (i, 0), g.1 (i, 1)) :=
    congrArg (fun z ↦ ((z.1 : Fin q ↪ E) i).val) h
  have ho : (f.1 (i, 0) < f.1 (i, 1)) ↔ (g.1 (i, 0) < g.1 (i, 1)) := by
    exact decide_eq_decide.mp (congrArg (fun z ↦ (z.2 : Fin q → Bool) i) h)
  rcases Sym2.eq_iff.mp he with he | he
  · fin_cases j <;> simp_all
  · have hne : f.1 (i, 0) ≠ f.1 (i, 1) := by
      intro hh
      have := congrArg Prod.snd (f.1.injective hh)
      norm_num at this
    exfalso
    rw [← he.1, ← he.2] at ho
    rcases lt_or_gt_of_ne hne with hh | hh
    · exact (not_lt_of_gt hh) (ho.mp hh)
    · exact (not_lt_of_gt hh) (ho.mpr hh)

/-- A matching has at most an ordering and an orientation for each edge. -/
theorem pairedEmbedding_fiber_card_le [LinearOrder V] {q : ℕ}
    (E : Finset (Sym2 V)) (hE : E.card = q) :
    Fintype.card {f : (Fin q × Fin 2) ↪ V // pairedEmbeddingEdges f = E} ≤
      q.factorial * 2 ^ q := by
  calc
    _ ≤ Fintype.card ((Fin q ↪ E) × (Fin q → Bool)) :=
      Fintype.card_le_of_injective _ (pairedDescription_injective E)
    _ = q.factorial * 2 ^ q := by
      simp [Fintype.card_embedding_eq, hE, Nat.descFactorial_self]

theorem descFactorial_le_edgeMatchingFinset_card_mul [LinearOrder V] (q : ℕ) :
    (Fintype.card V).descFactorial (2 * q) ≤
      (edgeMatchingFinset V q).card * (q.factorial * 2 ^ q) := by
  classical
  have hmaps : (↑(Finset.univ : Finset ((Fin q × Fin 2) ↪ V)) : Set _).MapsTo
      (pairedEmbeddingEdges (V := V) (q := q))
      ((edgeMatchingFinset V q) : Set (Finset (Sym2 V))) := by
    intro f _
    exact mem_edgeMatchingFinset.mpr
      ⟨pairedEmbeddingEdges_isEdgeMatching f, pairedEmbeddingEdges_card f⟩
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : ∀ E ∈ edgeMatchingFinset V q,
      ((Finset.univ : Finset ((Fin q × Fin 2) ↪ V)).filter
        (fun f ↦ pairedEmbeddingEdges f = E)).card ≤ q.factorial * 2 ^ q := by
    intro E hE
    have hh := pairedEmbedding_fiber_card_le E (mem_edgeMatchingFinset.mp hE).2
    rw [Fintype.card_of_subtype (Finset.univ.filter
      (fun f : (Fin q × Fin 2) ↪ V ↦ pairedEmbeddingEdges f = E)) (by simp)] at hh
    exact hh
  calc
    _ = (Finset.univ : Finset ((Fin q × Fin 2) ↪ V)).card := by
      simp [Fintype.card_embedding_eq, mul_comm]
    _ = _ := hsum
    _ ≤ ∑ _E ∈ edgeMatchingFinset V q, q.factorial * 2 ^ q :=
      Finset.sum_le_sum hbound
    _ = _ := by simp

/-- The classical labeled matching coefficient, including unused vertices. -/
def labeledMatchingCoefficient (t q : ℕ) : ℕ :=
  t.factorial / (2 ^ q * q.factorial * (t - 2 * q).factorial)

/-- The factorial expression is a lower bound for the actual matching family.
This proof uses bounded fibers of paired embeddings, not unmarked injection. -/
theorem labeledMatchingCoefficient_le_card [LinearOrder V] (q : ℕ)
    (hq : 2 * q ≤ Fintype.card V) :
    labeledMatchingCoefficient (Fintype.card V) q ≤ (edgeMatchingFinset V q).card := by
  have hf := Nat.factorial_mul_descFactorial hq
  have hd := Nat.div_mul_le_self (Fintype.card V).factorial
    (2 ^ q * q.factorial * (Fintype.card V - 2 * q).factorial)
  have hdiv : labeledMatchingCoefficient (Fintype.card V) q *
      (q.factorial * 2 ^ q) ≤ (Fintype.card V).descFactorial (2 * q) := by
    apply Nat.le_of_mul_le_mul_left (c := (Fintype.card V - 2 * q).factorial) _
      (Nat.factorial_pos (Fintype.card V - 2 * q))
    rw [hf]
    simpa [labeledMatchingCoefficient, mul_assoc, mul_comm, mul_left_comm] using hd
  have h := hdiv.trans (descFactorial_le_edgeMatchingFinset_card_mul (V := V) q)
  exact Nat.le_of_mul_le_mul_right h (by positivity)

end DenseGraph
