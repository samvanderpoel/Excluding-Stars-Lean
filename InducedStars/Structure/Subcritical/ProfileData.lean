import InducedStars.Structure.Subcritical.ProfileDefects
import InducedStars.Structure.Supercritical.CountingSetup
import DenseGraph.Combinatorics.Matching

/-!
# Finite subcritical profile data and exact realization

Paper: Definitions `def:profile-datum-K1k` and `def:profile-class-K1k`.
Rows store counts, with `some 0` recording a row even when its trimmed
target has no remaining neighbors. Auxiliary coordinates are normalized
outside their root domains. No graph or neighbor subset is stored.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The two full-part active-neighbor deviation labels. -/
inductive SubcriticalTailDirection
  | upper
  | lower
  deriving DecidableEq

instance : Fintype SubcriticalTailDirection :=
  ⟨{.upper, .lower}, by intro t; cases t <;> simp⟩

/-- A natural degree packaged in the common finite coordinate range. -/
def subcriticalBoundedDegree (G : SimpleGraph V) (v : V) (A : Finset V) :
    Fin (Fintype.card V + 1) :=
  ⟨degreeInFinset G v A, Nat.lt_succ_of_le
    ((Finset.card_filter_le _ _).trans (Finset.card_le_univ A))⟩

/-- A loopless complementary degree in the same finite coordinate range. -/
def subcriticalBoundedComplementDegree (G : SimpleGraph V) (v : V) (A : Finset V) :
    Fin (Fintype.card V + 1) :=
  ⟨complementDegreeInFinset G v A, Nat.lt_succ_of_le
    ((Finset.card_filter_le _ _).trans (Finset.card_le_univ A))⟩

@[simp] theorem subcriticalBoundedDegree_val (G : SimpleGraph V) (v : V)
    (A : Finset V) :
    (subcriticalBoundedDegree G v A).val = degreeInFinset G v A := rfl

@[simp] theorem subcriticalBoundedComplementDegree_val (G : SimpleGraph V) (v : V)
    (A : Finset V) :
    (subcriticalBoundedComplementDegree G v A).val =
      complementDegreeInFinset G v A := rfl

/-- Paper: Definition `def:profile-datum-K1k`. Counts and optional labels
on finite coordinate types, with exactly the source's domain and capacity
restrictions. The later realized-root bound is deliberately not a field. -/
structure SubcriticalProfile (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta : ℝ) where
  b : ℕ
  b_le : b ≤ (D.nonretainedVertices eta R₀).card.choose 2
  ell : ℕ
  two_mul_ell_le : 2 * ell ≤ Fintype.card V
  retainedRoots : Finset V
  outsideRoots : Finset V
  retainedRoots_subset : retainedRoots ⊆ D.retainedVertices eta R₀
  outsideRoots_subset : outsideRoots ⊆ D.nonretainedVertices eta R₀
  rows : V → D.PartIndex → Option (Fin (Fintype.card V + 1))
  rows_valid : ∀ v a r, rows v a = some r →
    ((v ∈ retainedRoots ∧ D.EligibleProfileTarget eta R₀ theta v a) ∨
      (v ∈ outsideRoots ∧ a ∈ D.retainedPartIndices eta R₀)) ∧
        r.val ≤ (D.part a \ (retainedRoots ∪ outsideRoots)).card
  ownCount : V → Fin (Fintype.card V + 1)
  ownCount_zero : ∀ v, v ∉ retainedRoots → ownCount v = 0
  ownCount_capacity : ∀ v (hv : v ∈ retainedRoots),
    (ownCount v).val ≤
      (D.part (D.retainedVertexPart eta R₀ v (retainedRoots_subset hv)) \
        (retainedRoots ∪ outsideRoots)).card
  tails : V → D.PartIndex → Option SubcriticalTailDirection
  tails_valid : ∀ v a t, tails v a = some t →
    ∃ hv : v ∈ retainedRoots,
      D.ActivePart (D.retainedVertexPart eta R₀ v (retainedRoots_subset hv)) a

namespace SubcriticalProfile

variable {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}

/-- The profile's retained and outside roots together. -/
def roots (p : SubcriticalProfile D eta R₀ theta) : Finset V :=
  p.retainedRoots ∪ p.outsideRoots

@[simp] theorem mem_roots (p : SubcriticalProfile D eta R₀ theta) (v : V) :
    v ∈ p.roots ↔ v ∈ p.retainedRoots ∨ v ∈ p.outsideRoots :=
  Finset.mem_union

theorem roots_disjoint (p : SubcriticalProfile D eta R₀ theta) :
    Disjoint p.retainedRoots p.outsideRoots :=
  (D.retainedVertices_disjoint_nonretainedVertices eta R₀).mono
    p.retainedRoots_subset p.outsideRoots_subset

theorem rows_eq_none_of_not_mem_roots (p : SubcriticalProfile D eta R₀ theta)
    {v : V} (hv : v ∉ p.roots) (a : D.PartIndex) : p.rows v a = none := by
  cases h : p.rows v a with
  | none => rfl
  | some r =>
    rcases (p.rows_valid v a r h).1 with hret | hout
    · exact (hv (Finset.mem_union_left _ hret.1)).elim
    · exact (hv (Finset.mem_union_right _ hout.1)).elim

theorem tails_eq_none_of_not_mem_retainedRoots
    (p : SubcriticalProfile D eta R₀ theta) {v : V}
    (hv : v ∉ p.retainedRoots) (a : D.PartIndex) : p.tails v a = none := by
  cases h : p.tails v a with
  | none => rfl
  | some t => exact (hv (p.tails_valid v a t h).choose).elim

private def finiteEncoding (p : SubcriticalProfile D eta R₀ theta) :
    Fin ((D.nonretainedVertices eta R₀).card.choose 2 + 1) ×
    Fin (Fintype.card V + 1) × Finset V × Finset V ×
    (V → D.PartIndex → Option (Fin (Fintype.card V + 1))) ×
    (V → Fin (Fintype.card V + 1)) ×
    (V → D.PartIndex → Option SubcriticalTailDirection) :=
  (⟨p.b, Nat.lt_succ_of_le p.b_le⟩,
    ⟨p.ell, Nat.lt_succ_of_le (by have := p.two_mul_ell_le; omega)⟩,
    p.retainedRoots, p.outsideRoots, p.rows, p.ownCount, p.tails)

private theorem finiteEncoding_injective :
    Function.Injective (finiteEncoding (D := D) (eta := eta) (R₀ := R₀)
      (theta := theta)) := by
  intro p q h
  cases p
  cases q
  simp only [finiteEncoding, Prod.mk.injEq, Fin.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rfl

/-- Finiteness follows from bounded integers and finite root, row, and tail
coordinates, without requiring syntactically valid profiles to be realized. -/
instance : Finite (SubcriticalProfile D eta R₀ theta) :=
  Finite.of_injective finiteEncoding finiteEncoding_injective

instance : Fintype (SubcriticalProfile D eta R₀ theta) := Fintype.ofFinite _

end SubcriticalProfile

/-- Equality with the existing matching number is precisely the paper's
existence of a maximum matching of the specified size. -/
theorem subcritical_matchingNumber_eq_iff (H : SimpleGraph V) (ell : ℕ) :
    DenseGraph.matchingNumber H = ell ↔
      ∃ M : H.Subgraph, DenseGraph.IsMaximumMatching M ∧ M.edgeSet.ncard = ell := by
  constructor
  · intro h
    exact ⟨DenseGraph.canonicalMaximumMatching H,
      DenseGraph.canonicalMaximumMatching_isMaximum H, h⟩
  · rintro ⟨M, hM, hcard⟩
    apply Nat.le_antisymm
    · rw [← hcard]
      exact hM.maximal_card (DenseGraph.canonicalMaximumMatching_isMatching H)
    · rw [← hcard]
      exact DenseGraph.matching_card_le_matchingNumber hM.isMatching

/-- Paper: Definition `def:profile-class-K1k`, its seven exact graph-data
conditions. Family membership is supplied separately by the profile class. -/
structure RealizesSubcriticalProfile (G : SimpleGraph V)
    {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}
    (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta) : Prop where
  edge_count : inducedEdgeCount G (D.nonretainedVertices eta R₀) = p.b
  retained_roots : p.retainedRoots = subcriticalBadRetainedRoots G D eta R₀ theta alpha
  outside_roots : p.outsideRoots = subcriticalBadOutsideRoots G D eta R₀ theta alpha
  retained_rows : ∀ v, v ∈ p.retainedRoots → ∀ a,
    p.rows v a = if D.EligibleProfileTarget eta R₀ theta v a ∧
        4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)
      then some (subcriticalBoundedDegree G v (D.part a \ p.roots)) else none
  own_counts : ∀ v (hv : v ∈ p.retainedRoots),
    (p.ownCount v).val = complementDegreeInFinset G v
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots)
  outside_rows : ∀ v, v ∈ p.outsideRoots → ∀ a,
    p.rows v a = if a ∈ D.retainedPartIndices eta R₀ ∧
        4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)
      then some (subcriticalBoundedDegree G v (D.part a \ p.roots)) else none
  tail_labels : ∀ v (hv : v ∈ p.retainedRoots) a,
    D.ActivePart (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) a →
      (p.tails v a = some .upper ↔
        (1 - alpha) * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)) ∧
      (p.tails v a = some .lower ↔
        (degreeInFinset G v (D.part a) : ℝ) ≤ alpha * (D.part a).card)
  matching : DenseGraph.matchingNumber
    (subcriticalResidualDefectGraph G D eta R₀ theta alpha) = p.ell

/-- The seven source clauses, grouping the two root identities as item two
and the two tail directions as item six. -/
theorem realizesSubcriticalProfile_iff (G : SimpleGraph V)
    {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}
    (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta) :
    RealizesSubcriticalProfile G alpha p ↔
      inducedEdgeCount G (D.nonretainedVertices eta R₀) = p.b ∧
      (p.retainedRoots = subcriticalBadRetainedRoots G D eta R₀ theta alpha ∧
        p.outsideRoots = subcriticalBadOutsideRoots G D eta R₀ theta alpha) ∧
      (∀ v, v ∈ p.retainedRoots → ∀ a,
        p.rows v a = if D.EligibleProfileTarget eta R₀ theta v a ∧
            4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)
          then some (subcriticalBoundedDegree G v (D.part a \ p.roots)) else none) ∧
      (∀ v (hv : v ∈ p.retainedRoots),
        (p.ownCount v).val = complementDegreeInFinset G v
          (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots)) ∧
      (∀ v, v ∈ p.outsideRoots → ∀ a,
        p.rows v a = if a ∈ D.retainedPartIndices eta R₀ ∧
            4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)
          then some (subcriticalBoundedDegree G v (D.part a \ p.roots)) else none) ∧
      (∀ v (hv : v ∈ p.retainedRoots) a,
        D.ActivePart (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) a →
          (p.tails v a = some .upper ↔
            (1 - alpha) * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)) ∧
          (p.tails v a = some .lower ↔
            (degreeInFinset G v (D.part a) : ℝ) ≤ alpha * (D.part a).card)) ∧
      (∃ M : (subcriticalResidualDefectGraph G D eta R₀ theta alpha).Subgraph,
        DenseGraph.IsMaximumMatching M ∧ M.edgeSet.ncard = p.ell) := by
  rw [← subcritical_matchingNumber_eq_iff]
  constructor
  · intro h
    exact ⟨h.edge_count, ⟨h.retained_roots, h.outside_roots⟩,
      h.retained_rows, h.own_counts, h.outside_rows, h.tail_labels, h.matching⟩
  · rintro ⟨he, ⟨hr, ho⟩, hrr, hi, hor, ht, hm⟩
    exact ⟨he, hr, ho, hrr, hi, hor, ht, hm⟩

namespace RealizesSubcriticalProfile

theorem roots_eq {G : SimpleGraph V} {D : SubcriticalDivision k V}
    {eta theta alpha : ℝ} {R₀ : ℕ} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) :
    p.roots = subcriticalBadRoots G D eta R₀ theta alpha := by
  simp only [SubcriticalProfile.roots, subcriticalBadRoots, h.retained_roots, h.outside_roots]

end RealizesSubcriticalProfile

end InducedStars
