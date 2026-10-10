import DenseGraph.FiniteModels.RestrictedCounting
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Witnesses from restricted finite pattern counts

This module complements `RestrictedCounting` with the two algebraic facts
needed when a positive finite count is used combinatorially.  First, every
summand is nonnegative, and for a simple-graph adjacency kernel a positive
count supplies an actual injective transversal when the role sets are
pairwise disjoint.  Second, a kernel which is constant between role sets has
the expected exact product formula, including the role-volume factor.
-/

noncomputable section

open Finset
open scoped BigOperators Classical SimpleGraph

namespace DenseGraph

namespace FiniteWeightedGraph

universe u

variable {q : ℕ} {V : Type u} [Fintype V] [DecidableEq V]

/-- Every restricted induced-map summand is nonnegative. -/
theorem restrictedInducedMapWeight_nonneg
    (F : SimpleGraph (Fin q)) (A : FiniteWeightedGraph V)
    (S : Fin q → Finset V) (x : Fin q → V) :
    0 ≤ restrictedInducedMapWeight F A S x := by
  exact mul_nonneg (restrictedRoleIndicator_nonneg S x)
    (Finset.prod_nonneg fun e _ ↦ restrictedInducedPairFactor_nonneg F A e x)

/-- Restricted finite induced-pattern counts are nonnegative. -/
theorem restrictedInducedPatternCount_nonneg
    (F : SimpleGraph (Fin q)) (A : FiniteWeightedGraph V)
    (S : Fin q → Finset V) :
    0 ≤ restrictedInducedPatternCount F A S := by
  unfold restrictedInducedPatternCount
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun x _ ↦ restrictedInducedMapWeight_nonneg F A S x)

private theorem restrictedInducedPairFactor_ofSimpleGraph_pos_iff
    (F : SimpleGraph (Fin q)) (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : FinitePatternPair q) (x : Fin q → V) :
    0 < restrictedInducedPairFactor F (ofSimpleGraph G) e x ↔
      (F.Adj e.val.1 e.val.2 ↔ G.Adj (x e.val.1) (x e.val.2)) := by
  classical
  by_cases hF : F.Adj e.val.1 e.val.2 <;>
    by_cases hG : G.Adj (x e.val.1) (x e.val.2) <;>
      simp [restrictedInducedPairFactor, hF, hG]

/-- For an adjacency kernel, a summand is positive exactly when its map lies
in every prescribed role set and preserves and reflects all adjacencies. -/
theorem restrictedInducedMapWeight_ofSimpleGraph_pos_iff
    (F : SimpleGraph (Fin q)) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Fin q → Finset V) (x : Fin q → V) :
    0 < restrictedInducedMapWeight F (ofSimpleGraph G) S x ↔
      (∀ i, x i ∈ S i) ∧
        ∀ i j, F.Adj i j ↔ G.Adj (x i) (x j) := by
  classical
  constructor
  · intro hx
    have hrole : ∀ i, x i ∈ S i := by
      intro i
      by_contra hi
      have hz := restrictedRoleIndicator_eq_zero_of_not_mem S x hi
      rw [restrictedInducedMapWeight, hz, zero_mul] at hx
      exact (lt_irrefl 0) hx
    have hpairPos : ∀ e : FinitePatternPair q,
        0 < restrictedInducedPairFactor F (ofSimpleGraph G) e x := by
      intro e
      have hfactorNonneg (e' : FinitePatternPair q) :
          0 ≤ restrictedInducedPairFactor F (ofSimpleGraph G) e' x :=
        restrictedInducedPairFactor_nonneg F (ofSimpleGraph G) e' x
      have hprodPos : 0 < ∏ e' : FinitePatternPair q,
          restrictedInducedPairFactor F (ofSimpleGraph G) e' x := by
        by_contra hnot
        have hprodNonpos :
            (∏ e' : FinitePatternPair q,
              restrictedInducedPairFactor F (ofSimpleGraph G) e' x) ≤ 0 :=
          le_of_not_gt hnot
        have hroleNonneg := restrictedRoleIndicator_nonneg S x
        have := mul_nonpos_of_nonneg_of_nonpos hroleNonneg hprodNonpos
        exact (not_lt_of_ge this) hx
      have hne : restrictedInducedPairFactor F (ofSimpleGraph G) e x ≠ 0 := by
        intro he
        have hzero : (∏ e' : FinitePatternPair q,
            restrictedInducedPairFactor F (ofSimpleGraph G) e' x) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ e) he
        rw [hzero] at hprodPos
        exact (lt_irrefl 0) hprodPos
      exact lt_of_le_of_ne (hfactorNonneg e) hne.symm
    refine ⟨hrole, ?_⟩
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · let e : FinitePatternPair q := ⟨(i, j), hijlt⟩
        have he := (restrictedInducedPairFactor_ofSimpleGraph_pos_iff
          F G e x).mp (hpairPos e)
        change (F.Adj i j ↔ G.Adj (x i) (x j)) at he
        exact he
      · let e : FinitePatternPair q := ⟨(j, i), hjilt⟩
        have he := (restrictedInducedPairFactor_ofSimpleGraph_pos_iff
          F G e x).mp (hpairPos e)
        change (F.Adj j i ↔ G.Adj (x j) (x i)) at he
        simpa only [F.adj_comm, G.adj_comm] using he
  · rintro ⟨hrole, hadj⟩
    rw [restrictedInducedMapWeight,
      (restrictedRoleIndicator_eq_one_iff S x).2 hrole, one_mul]
    apply Finset.prod_pos
    intro e _
    exact (restrictedInducedPairFactor_ofSimpleGraph_pos_iff F G e x).2
      (hadj e.val.1 e.val.2)

/-- A positive restricted adjacency-kernel count produces an actual role
choice preserving and reflecting adjacency.  Pairwise disjoint role sets
make that choice injective, even when several roles lie in one larger parent
cluster. -/
theorem exists_injective_restricted_induced_pattern_map_of_pos
    (F : SimpleGraph (Fin q)) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Fin q → Finset V)
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin q)) S)
    (hpos : 0 < restrictedInducedPatternCount F (ofSimpleGraph G) S) :
    ∃ x : Fin q → V,
      (∀ i, x i ∈ S i) ∧ Function.Injective x ∧
        ∀ i j, F.Adj i j ↔ G.Adj (x i) (x j) := by
  classical
  have hsumPos : 0 < ∑ x : Fin q → V,
      restrictedInducedMapWeight F (ofSimpleGraph G) S x := by
    by_contra hnot
    have hsumNonpos :
        (∑ x : Fin q → V,
          restrictedInducedMapWeight F (ofSimpleGraph G) S x) ≤ 0 :=
      le_of_not_gt hnot
    have hnormNonneg : 0 ≤ (1 / (Fintype.card V : ℝ)) ^ q := by positivity
    have hcountNonpos := mul_nonpos_of_nonneg_of_nonpos hnormNonneg hsumNonpos
    exact (not_lt_of_ge hcountNonpos) hpos
  have hxPos : ∃ x : Fin q → V,
      0 < restrictedInducedMapWeight F (ofSimpleGraph G) S x := by
    by_contra hnot
    push_neg at hnot
    have hsumNonpos :
        (∑ x : Fin q → V,
          restrictedInducedMapWeight F (ofSimpleGraph G) S x) ≤ 0 :=
      Finset.sum_nonpos fun x _ ↦ hnot x
    exact (not_lt_of_ge hsumNonpos) hsumPos
  obtain ⟨x, hx⟩ := hxPos
  obtain ⟨hmem, hadj⟩ :=
    (restrictedInducedMapWeight_ofSimpleGraph_pos_iff F G S x).mp hx
  have hinjective : Function.Injective x := by
    intro i j hij
    by_contra hne
    have hd : Disjoint (S i) (S j) :=
      hdisjoint (Set.mem_univ i) (Set.mem_univ j) hne
    exact (Finset.disjoint_left.mp hd (hmem i)) (by simpa [hij] using hmem j)
  exact ⟨x, hmem, hinjective, hadj⟩

/-- Bundled strong-embedding version of
`exists_injective_restricted_induced_pattern_map_of_pos`. -/
theorem exists_restricted_induced_pattern_embedding_of_pos
    (F : SimpleGraph (Fin q)) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Fin q → Finset V)
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin q)) S)
    (hpos : 0 < restrictedInducedPatternCount F (ofSimpleGraph G) S) :
    ∃ φ : F ↪g G, ∀ i, φ i ∈ S i := by
  obtain ⟨x, hmem, hinjective, hadj⟩ :=
    exists_injective_restricted_induced_pattern_map_of_pos
      F G S hdisjoint hpos
  exact ⟨{
    toFun := x
    inj' := hinjective
    map_rel_iff' := by
      intro i j
      change G.Adj (x i) (x j) ↔ F.Adj i j
      exact (hadj i j).symm }, hmem⟩

private theorem restrictedInducedMapWeight_eq_ite_of_pairFactors
    (F : SimpleGraph (Fin q)) (A : FiniteWeightedGraph V)
    (S : Fin q → Finset V) (c : FinitePatternPair q → ℝ)
    (hconstant : ∀ (x : Fin q → V), (∀ i, x i ∈ S i) →
      ∀ e, restrictedInducedPairFactor F A e x = c e)
    (x : Fin q → V) :
    restrictedInducedMapWeight F A S x =
      if ∀ i, x i ∈ S i then ∏ e, c e else 0 := by
  classical
  by_cases hmem : ∀ i, x i ∈ S i
  · rw [if_pos hmem, restrictedInducedMapWeight,
      (restrictedRoleIndicator_eq_one_iff S x).2 hmem, one_mul]
    exact Finset.prod_congr rfl fun e _ ↦ hconstant x hmem e
  · rw [if_neg hmem]
    push_neg at hmem
    obtain ⟨i, hi⟩ := hmem
    rw [restrictedInducedMapWeight,
      restrictedRoleIndicator_eq_zero_of_not_mem S x hi, zero_mul]

/-- Exact role-volume formula when every prescribed edge/nonedge factor is
constant on the corresponding pair of role sets. -/
theorem restrictedInducedPatternCount_eq_role_product_mul_pair_product
    (F : SimpleGraph (Fin q)) (A : FiniteWeightedGraph V)
    (S : Fin q → Finset V) (c : FinitePatternPair q → ℝ)
    (hconstant : ∀ (x : Fin q → V), (∀ i, x i ∈ S i) →
      ∀ e, restrictedInducedPairFactor F A e x = c e) :
    restrictedInducedPatternCount F A S =
      (1 / (Fintype.card V : ℝ)) ^ q *
        (∏ i, ((S i).card : ℝ)) * ∏ e, c e := by
  classical
  rw [restrictedInducedPatternCount]
  have hsum :
      (∑ x : Fin q → V, restrictedInducedMapWeight F A S x) =
        (∏ i, ((S i).card : ℝ)) * ∏ e, c e := by
    calc
      (∑ x : Fin q → V, restrictedInducedMapWeight F A S x) =
          ∑ x : Fin q → V,
            if ∀ i, x i ∈ S i then ∏ e, c e else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        exact restrictedInducedMapWeight_eq_ite_of_pairFactors
          F A S c hconstant x
      _ = Finset.sum
          (Finset.univ.filter fun x : Fin q → V ↦ ∀ i, x i ∈ S i)
          (fun _ ↦ ∏ e, c e) := by
        rw [Finset.sum_filter]
      _ = ∑ x ∈ Fintype.piFinset S, ∏ e, c e := by
        congr 1
        ext x
        simp [Fintype.mem_piFinset]
      _ = (∏ i, ((S i).card : ℝ)) * ∏ e, c e := by simp
  rw [hsum]
  ring

/-- Equal positive role sizes give the mandatory `q⁻q` role-volume factor.
The stated bound is valid for arbitrary pair constants bounded below by `a`.
-/
theorem one_div_pow_mul_pair_lower_le_restrictedInducedPatternCount
    (F : SimpleGraph (Fin q)) (A : FiniteWeightedGraph V)
    (S : Fin q → Finset V) (c : FinitePatternPair q → ℝ)
    {s : ℕ} {a : ℝ}
    (hq : 0 < q) (hs : 0 < s) (ha : 0 ≤ a)
    (hcardV : Fintype.card V = q * s)
    (hcardS : ∀ i, (S i).card = s)
    (hconstant : ∀ (x : Fin q → V), (∀ i, x i ∈ S i) →
      ∀ e, restrictedInducedPairFactor F A e x = c e)
    (hfactor : ∀ e, a ≤ c e) :
    (1 / (q : ℝ)) ^ q * a ^ Nat.choose q 2 ≤
      restrictedInducedPatternCount F A S := by
  rw [restrictedInducedPatternCount_eq_role_product_mul_pair_product
    F A S c hconstant]
  have hqne : (q : ℝ) ≠ 0 := by positivity
  have hsne : (s : ℝ) ≠ 0 := by positivity
  have hroles : (∏ i, ((S i).card : ℝ)) = (s : ℝ) ^ q := by
    simp_rw [hcardS]
    simp
  have hnormalize :
      (1 / (Fintype.card V : ℝ)) ^ q * (∏ i, ((S i).card : ℝ)) =
        (1 / (q : ℝ)) ^ q := by
    rw [hcardV, Nat.cast_mul, hroles]
    rw [one_div_pow, one_div_pow]
    field_simp
    rw [mul_pow]
    ring
  rw [hnormalize]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← card_finitePatternPair q]
  have hp : (∏ _e : FinitePatternPair q, a) ≤ ∏ e, c e :=
    Finset.prod_le_prod (fun _e _ ↦ ha) (fun e _ ↦ hfactor e)
  simpa using hp

end FiniteWeightedGraph

end DenseGraph
