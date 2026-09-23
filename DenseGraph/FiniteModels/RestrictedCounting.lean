import DenseGraph.FiniteModels.WeightedGraph

/-!
# Restricted finite induced-pattern counting

This module gives the finite, same-label counting estimate used to transfer a
positive transversal count across labeled cut distance.  Role restrictions
are kept as explicit `0/1` factors, so different roles may use arbitrary
finite subsets of one common host.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace DenseGraph

namespace FiniteWeightedGraph

variable {q : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Unordered pattern pairs, represented by their unique increasing ordered
representatives. -/
abbrev FinitePatternPair (q : ℕ) :=
  {e : Fin q × Fin q // e.1 < e.2}

@[simp] theorem card_finitePatternPair (q : ℕ) :
    Fintype.card (FinitePatternPair q) = Nat.choose q 2 := by
  rw [Fintype.card_subtype]
  simpa only [Fintype.card_fin] using
    (Fintype.card_product_filter_lt (α := Fin q))

/-- The edge or nonedge factor prescribed by `F` at one increasing pair. -/
def restrictedInducedPairFactor
    (F : SimpleGraph (Fin q)) (A : FiniteWeightedGraph V)
    (e : FinitePatternPair q) (x : Fin q → V) : ℝ :=
  if F.Adj e.val.1 e.val.2 then A.weight (x e.val.1) (x e.val.2)
  else 1 - A.weight (x e.val.1) (x e.val.2)

/-- The product of the `0/1` membership factors for all roles. -/
def restrictedRoleIndicator
    (S : Fin q → Finset V) (x : Fin q → V) : ℝ :=
  ∏ i, if x i ∈ S i then 1 else 0

/-- The unnormalized contribution of one role assignment. -/
def restrictedInducedMapWeight
    (F : SimpleGraph (Fin q)) (A : FiniteWeightedGraph V)
    (S : Fin q → Finset V) (x : Fin q → V) : ℝ :=
  restrictedRoleIndicator S x *
    ∏ e : FinitePatternPair q, restrictedInducedPairFactor F A e x

/-- The normalized induced-pattern count with role `i` restricted to `S i`.
The normalization is by the full host order to the number of roles. -/
def restrictedInducedPatternCount
    (F : SimpleGraph (Fin q)) (A : FiniteWeightedGraph V)
    (S : Fin q → Finset V) : ℝ :=
  (1 / (Fintype.card V : ℝ)) ^ q *
    ∑ x : Fin q → V, restrictedInducedMapWeight F A S x

theorem restrictedInducedPairFactor_nonneg
    (F : SimpleGraph (Fin q)) (A : FiniteWeightedGraph V)
    (e : FinitePatternPair q) (x : Fin q → V) :
    0 ≤ restrictedInducedPairFactor F A e x := by
  unfold restrictedInducedPairFactor
  split_ifs
  · exact A.nonneg _ _
  · linarith [A.le_one (x e.val.1) (x e.val.2)]

theorem restrictedInducedPairFactor_le_one
    (F : SimpleGraph (Fin q)) (A : FiniteWeightedGraph V)
    (e : FinitePatternPair q) (x : Fin q → V) :
    restrictedInducedPairFactor F A e x ≤ 1 := by
  unfold restrictedInducedPairFactor
  split_ifs
  · exact A.le_one _ _
  · linarith [A.nonneg (x e.val.1) (x e.val.2)]

@[simp] theorem restrictedRoleIndicator_eq_one_iff
    (S : Fin q → Finset V) (x : Fin q → V) :
    restrictedRoleIndicator S x = 1 ↔ ∀ i, x i ∈ S i := by
  constructor
  · intro h i
    by_contra hi
    have hz : restrictedRoleIndicator S x = 0 := by
      rw [restrictedRoleIndicator,
        Finset.prod_eq_zero (Finset.mem_univ i)]
      simp [hi]
    linarith
  · intro h
    simp [restrictedRoleIndicator, h]

@[simp] theorem restrictedRoleIndicator_eq_zero_of_not_mem
    (S : Fin q → Finset V) (x : Fin q → V)
    {i : Fin q} (hi : x i ∉ S i) :
    restrictedRoleIndicator S x = 0 := by
  classical
  rw [restrictedRoleIndicator, Finset.prod_eq_zero (Finset.mem_univ i)]
  simp [hi]

theorem restrictedRoleIndicator_nonneg
    (S : Fin q → Finset V) (x : Fin q → V) :
    0 ≤ restrictedRoleIndicator S x := by
  classical
  exact Finset.prod_nonneg fun i _ ↦ by
    split_ifs <;> norm_num

theorem restrictedRoleIndicator_le_one
    (S : Fin q → Finset V) (x : Fin q → V) :
    restrictedRoleIndicator S x ≤ 1 := by
  classical
  apply Finset.prod_le_one
  · intro i _
    split_ifs <;> norm_num
  · intro i _
    split_ifs <;> norm_num

/-! ## Splitting two coordinates from the finite assignment cube -/

private def restrictedPairCoordinatePredicate
    (i j r : Fin q) : Prop := r = i ∨ r = j

private def restrictedPairRestAssignment
    (i j : Fin q) (z : V × V)
    (y : {r : Fin q // ¬restrictedPairCoordinatePredicate i j r} → V) :
    Fin q → V := fun r ↦
  if hri : r = i then z.1
  else if hrj : r = j then z.2
  else y ⟨r, by simp [restrictedPairCoordinatePredicate, hri, hrj]⟩

@[simp] private theorem restrictedPairRestAssignment_left
    (i j : Fin q) (z : V × V)
    (y : {r : Fin q // ¬restrictedPairCoordinatePredicate i j r} → V) :
    restrictedPairRestAssignment i j z y i = z.1 := by
  simp [restrictedPairRestAssignment]

@[simp] private theorem restrictedPairRestAssignment_right
    (i j : Fin q) (hij : i ≠ j) (z : V × V)
    (y : {r : Fin q // ¬restrictedPairCoordinatePredicate i j r} → V) :
    restrictedPairRestAssignment i j z y j = z.2 := by
  simp [restrictedPairRestAssignment, hij.symm]

@[simp] private theorem restrictedPairRestAssignment_rest
    (i j : Fin q) (z : V × V)
    (y : {r : Fin q // ¬restrictedPairCoordinatePredicate i j r} → V)
    (r : {r : Fin q // ¬restrictedPairCoordinatePredicate i j r}) :
    restrictedPairRestAssignment i j z y r.val = y r := by
  have hri : r.val ≠ i := by
    intro h
    exact r.property (Or.inl h)
  have hrj : r.val ≠ j := by
    intro h
    exact r.property (Or.inr h)
  simp [restrictedPairRestAssignment, hri, hrj]

/-- Reindex all role assignments by two selected coordinates and the
remaining coordinate cube. -/
private def restrictedAssignmentPairRestEquiv
    (i j : Fin q) (hij : i ≠ j) :
    (Fin q → V) ≃
      (V × V) ×
        ({r : Fin q // ¬restrictedPairCoordinatePredicate i j r} → V) where
  toFun x := ((x i, x j), fun r ↦ x r.val)
  invFun p := restrictedPairRestAssignment i j p.1 p.2
  left_inv x := by
    funext r
    by_cases hri : r = i
    · subst r
      simp
    by_cases hrj : r = j
    · subst r
      simp [hij]
    · simp [restrictedPairRestAssignment, hri, hrj]
  right_inv p := by
    rcases p with ⟨⟨u, v⟩, y⟩
    apply Prod.ext
    · ext <;> simp [hij]
    · funext r
      exact restrictedPairRestAssignment_rest i j (u, v) y r

/-- The same reindexing with the remaining-coordinate cube outermost, which
is the useful order for the finite Fubini estimate below. -/
private def restrictedAssignmentRestPairEquiv
    (i j : Fin q) (hij : i ≠ j) :
    (Fin q → V) ≃
      ({r : Fin q // ¬restrictedPairCoordinatePredicate i j r} → V) ×
        (V × V) :=
  (restrictedAssignmentPairRestEquiv i j hij (V := V)).trans
    (Equiv.prodComm _ _)

/-! ## Products with pair-dependent kernels -/

private def restrictedMixedPairProduct
    (F : SimpleGraph (Fin q))
    (K : FinitePatternPair q → FiniteWeightedGraph V)
    (T : Finset (FinitePatternPair q)) (x : Fin q → V) : ℝ :=
  ∏ e ∈ T, restrictedInducedPairFactor F (K e) e x

private theorem restrictedMixedPairProduct_nonneg
    (F : SimpleGraph (Fin q))
    (K : FinitePatternPair q → FiniteWeightedGraph V)
    (T : Finset (FinitePatternPair q)) (x : Fin q → V) :
    0 ≤ restrictedMixedPairProduct F K T x := by
  classical
  exact Finset.prod_nonneg fun e _ ↦
    restrictedInducedPairFactor_nonneg F (K e) e x

private theorem restrictedMixedPairProduct_le_one
    (F : SimpleGraph (Fin q))
    (K : FinitePatternPair q → FiniteWeightedGraph V)
    (T : Finset (FinitePatternPair q)) (x : Fin q → V) :
    restrictedMixedPairProduct F K T x ≤ 1 := by
  classical
  apply Finset.prod_le_one
  · intro e _
    exact restrictedInducedPairFactor_nonneg F (K e) e x
  · intro e _
    exact restrictedInducedPairFactor_le_one F (K e) e x

private theorem restrictedInducedPairFactor_congr_assignments
    (F : SimpleGraph (Fin q)) (A : FiniteWeightedGraph V)
    (e : FinitePatternPair q) {x y : Fin q → V}
    (hleft : x e.val.1 = y e.val.1)
    (hright : x e.val.2 = y e.val.2) :
    restrictedInducedPairFactor F A e x =
      restrictedInducedPairFactor F A e y := by
  simp only [restrictedInducedPairFactor, hleft, hright]

private def finitePatternPairContains (i : Fin q)
    (e : FinitePatternPair q) : Prop :=
  e.val.1 = i ∨ e.val.2 = i

private theorem finitePatternPair_eq_of_contains_both
    (e p : FinitePatternPair q)
    (hi : finitePatternPairContains e.val.1 p)
    (hj : finitePatternPairContains e.val.2 p) : p = e := by
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exfalso
    exact (ne_of_lt e.property) (hi.symm.trans hj)
  · apply Subtype.ext
    apply Prod.ext
    · exact hi
    · exact hj
  · exfalso
    have hji : e.val.2 < e.val.1 := by simpa [hj, hi] using p.property
    exact (not_lt_of_ge e.property.le) hji
  · exfalso
    exact (ne_of_lt e.property) (hi.symm.trans hj)

private theorem restrictedPairRestAssignment_change_right
    (i j : Fin q) (u v v₀ : V)
    (y : {r : Fin q // ¬restrictedPairCoordinatePredicate i j r} → V)
    {r : Fin q} (hrj : r ≠ j) :
    restrictedPairRestAssignment i j (u, v) y r =
      restrictedPairRestAssignment i j (u, v₀) y r := by
  by_cases hri : r = i
  · subst r
    simp
  · simp [restrictedPairRestAssignment, hri, hrj]

private theorem restrictedPairRestAssignment_change_left
    (i j : Fin q) (u u₀ v : V)
    (y : {r : Fin q // ¬restrictedPairCoordinatePredicate i j r} → V)
    {r : Fin q} (hri : r ≠ i) :
    restrictedPairRestAssignment i j (u, v) y r =
      restrictedPairRestAssignment i j (u₀, v) y r := by
  simp [restrictedPairRestAssignment, hri]

private theorem restrictedPairFactor_change_right_of_contains_left
    (F : SimpleGraph (Fin q))
    (K : FinitePatternPair q → FiniteWeightedGraph V)
    (e p : FinitePatternPair q) (hpne : p ≠ e)
    (hpi : finitePatternPairContains e.val.1 p)
    (u v v₀ : V)
    (y : {r : Fin q //
      ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r} → V) :
    restrictedInducedPairFactor F (K p) p
        (restrictedPairRestAssignment e.val.1 e.val.2 (u, v) y) =
      restrictedInducedPairFactor F (K p) p
        (restrictedPairRestAssignment e.val.1 e.val.2 (u, v₀) y) := by
  have hpj : ¬finitePatternPairContains e.val.2 p := fun hpj ↦
    hpne (finitePatternPair_eq_of_contains_both e p hpi hpj)
  apply restrictedInducedPairFactor_congr_assignments
  · apply restrictedPairRestAssignment_change_right
    intro h
    exact hpj (Or.inl h)
  · apply restrictedPairRestAssignment_change_right
    intro h
    exact hpj (Or.inr h)

private theorem restrictedPairFactor_change_left_of_not_contains_left
    (F : SimpleGraph (Fin q))
    (K : FinitePatternPair q → FiniteWeightedGraph V)
    (e p : FinitePatternPair q)
    (hpi : ¬finitePatternPairContains e.val.1 p)
    (u u₀ v : V)
    (y : {r : Fin q //
      ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r} → V) :
    restrictedInducedPairFactor F (K p) p
        (restrictedPairRestAssignment e.val.1 e.val.2 (u, v) y) =
      restrictedInducedPairFactor F (K p) p
        (restrictedPairRestAssignment e.val.1 e.val.2 (u₀, v) y) := by
  apply restrictedInducedPairFactor_congr_assignments
  · apply restrictedPairRestAssignment_change_left
    intro h
    exact hpi (Or.inl h)
  · apply restrictedPairRestAssignment_change_left
    intro h
    exact hpi (Or.inr h)

private def restrictedMixedLeftWeight
    (F : SimpleGraph (Fin q)) (S : Fin q → Finset V)
    (K : FinitePatternPair q → FiniteWeightedGraph V)
    (e : FinitePatternPair q) (T : Finset (FinitePatternPair q))
    (base : V)
    (y : {r : Fin q //
      ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r} → V)
    (u : V) : ℝ :=
  (if u ∈ S e.val.1 then 1 else 0) *
    restrictedMixedPairProduct F K
      (T.filter (finitePatternPairContains e.val.1))
      (restrictedPairRestAssignment e.val.1 e.val.2 (u, base) y)

private def restrictedMixedRightWeight
    (F : SimpleGraph (Fin q)) (S : Fin q → Finset V)
    (K : FinitePatternPair q → FiniteWeightedGraph V)
    (e : FinitePatternPair q) (T : Finset (FinitePatternPair q))
    (base : V)
    (y : {r : Fin q //
      ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r} → V)
    (v : V) : ℝ :=
  (∏ r : {r : Fin q // r ≠ e.val.1},
      if restrictedPairRestAssignment e.val.1 e.val.2 (base, v) y r.val ∈ S r.val
      then 1 else 0) *
    restrictedMixedPairProduct F K
      (T.filter fun p ↦ ¬finitePatternPairContains e.val.1 p)
      (restrictedPairRestAssignment e.val.1 e.val.2 (base, v) y)

private theorem restrictedMixedLeftWeight_nonneg
    (F : SimpleGraph (Fin q)) (S : Fin q → Finset V)
    (K : FinitePatternPair q → FiniteWeightedGraph V)
    (e : FinitePatternPair q) (T : Finset (FinitePatternPair q))
    (base : V)
    (y : {r : Fin q //
      ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r} → V)
    (u : V) : 0 ≤ restrictedMixedLeftWeight F S K e T base y u := by
  unfold restrictedMixedLeftWeight
  exact mul_nonneg (by split_ifs <;> norm_num)
    (restrictedMixedPairProduct_nonneg _ _ _ _)

private theorem restrictedMixedLeftWeight_le_one
    (F : SimpleGraph (Fin q)) (S : Fin q → Finset V)
    (K : FinitePatternPair q → FiniteWeightedGraph V)
    (e : FinitePatternPair q) (T : Finset (FinitePatternPair q))
    (base : V)
    (y : {r : Fin q //
      ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r} → V)
    (u : V) : restrictedMixedLeftWeight F S K e T base y u ≤ 1 := by
  unfold restrictedMixedLeftWeight
  have hp := restrictedMixedPairProduct_nonneg F K
    (T.filter (finitePatternPairContains e.val.1))
    (restrictedPairRestAssignment e.val.1 e.val.2 (u, base) y)
  have hp1 := restrictedMixedPairProduct_le_one F K
    (T.filter (finitePatternPairContains e.val.1))
    (restrictedPairRestAssignment e.val.1 e.val.2 (u, base) y)
  by_cases hu : u ∈ S e.val.1
  · simp only [hu, if_pos, one_mul]
    exact hp1
  · simp only [hu, if_neg, zero_mul]
    norm_num

private theorem restrictedMixedRightWeight_nonneg
    (F : SimpleGraph (Fin q)) (S : Fin q → Finset V)
    (K : FinitePatternPair q → FiniteWeightedGraph V)
    (e : FinitePatternPair q) (T : Finset (FinitePatternPair q))
    (base : V)
    (y : {r : Fin q //
      ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r} → V)
    (v : V) : 0 ≤ restrictedMixedRightWeight F S K e T base y v := by
  unfold restrictedMixedRightWeight
  apply mul_nonneg
  · exact Finset.prod_nonneg fun r _ ↦ by split_ifs <;> norm_num
  · exact restrictedMixedPairProduct_nonneg _ _ _ _

private theorem restrictedMixedRightWeight_le_one
    (F : SimpleGraph (Fin q)) (S : Fin q → Finset V)
    (K : FinitePatternPair q → FiniteWeightedGraph V)
    (e : FinitePatternPair q) (T : Finset (FinitePatternPair q))
    (base : V)
    (y : {r : Fin q //
      ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r} → V)
    (v : V) : restrictedMixedRightWeight F S K e T base y v ≤ 1 := by
  unfold restrictedMixedRightWeight
  have hrole0 : 0 ≤ (∏ r : {r : Fin q // r ≠ e.val.1},
      if restrictedPairRestAssignment e.val.1 e.val.2 (base, v) y r.val ∈ S r.val
      then (1 : ℝ) else 0) :=
    Finset.prod_nonneg fun r _ ↦ by split_ifs <;> norm_num
  have hrole1 : (∏ r : {r : Fin q // r ≠ e.val.1},
      if restrictedPairRestAssignment e.val.1 e.val.2 (base, v) y r.val ∈ S r.val
      then (1 : ℝ) else 0) ≤ 1 := by
    apply Finset.prod_le_one
    · intro r _
      split_ifs <;> norm_num
    · intro r _
      split_ifs <;> norm_num
  have hp0 := restrictedMixedPairProduct_nonneg F K
    (T.filter fun p ↦ ¬finitePatternPairContains e.val.1 p)
    (restrictedPairRestAssignment e.val.1 e.val.2 (base, v) y)
  have hp1 := restrictedMixedPairProduct_le_one F K
    (T.filter fun p ↦ ¬finitePatternPairContains e.val.1 p)
    (restrictedPairRestAssignment e.val.1 e.val.2 (base, v) y)
  exact mul_le_one₀ hrole1 hp0 hp1

private theorem restrictedRoleIndicator_pairRest_factor
    (S : Fin q → Finset V) (e : FinitePatternPair q) (base : V)
    (z : V × V)
    (y : {r : Fin q //
      ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r} → V) :
    restrictedRoleIndicator S
        (restrictedPairRestAssignment e.val.1 e.val.2 z y) =
      (if z.1 ∈ S e.val.1 then 1 else 0) *
        ∏ r : {r : Fin q // r ≠ e.val.1},
          if restrictedPairRestAssignment e.val.1 e.val.2 (base, z.2) y r.val ∈
              S r.val then 1 else 0 := by
  classical
  rw [restrictedRoleIndicator,
    Fintype.prod_eq_mul_prod_subtype_ne
      (fun r : Fin q ↦
        if restrictedPairRestAssignment e.val.1 e.val.2 z y r ∈ S r
        then (1 : ℝ) else 0) e.val.1]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro r _hr
    have hr := restrictedPairRestAssignment_change_left
      e.val.1 e.val.2 z.1 base z.2 y r.property
    simp only [hr]

private theorem restrictedMixedPairProduct_pairRest_factor
    (F : SimpleGraph (Fin q))
    (K : FinitePatternPair q → FiniteWeightedGraph V)
    (e : FinitePatternPair q) (T : Finset (FinitePatternPair q))
    (heT : e ∉ T) (base : V) (z : V × V)
    (y : {r : Fin q //
      ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r} → V) :
    restrictedMixedPairProduct F K T
        (restrictedPairRestAssignment e.val.1 e.val.2 z y) =
      restrictedMixedPairProduct F K
          (T.filter (finitePatternPairContains e.val.1))
          (restrictedPairRestAssignment e.val.1 e.val.2 (z.1, base) y) *
        restrictedMixedPairProduct F K
          (T.filter fun p ↦ ¬finitePatternPairContains e.val.1 p)
          (restrictedPairRestAssignment e.val.1 e.val.2 (base, z.2) y) := by
  classical
  unfold restrictedMixedPairProduct
  calc
    (∏ p ∈ T,
        restrictedInducedPairFactor F (K p) p
          (restrictedPairRestAssignment e.val.1 e.val.2 z y)) =
        (∏ p ∈ T.filter (finitePatternPairContains e.val.1),
          restrictedInducedPairFactor F (K p) p
            (restrictedPairRestAssignment e.val.1 e.val.2 z y)) *
        ∏ p ∈ T.filter (fun p ↦ ¬finitePatternPairContains e.val.1 p),
          restrictedInducedPairFactor F (K p) p
            (restrictedPairRestAssignment e.val.1 e.val.2 z y) :=
      (Finset.prod_filter_mul_prod_filter_not T
        (finitePatternPairContains e.val.1)
        (fun p ↦ restrictedInducedPairFactor F (K p) p
          (restrictedPairRestAssignment e.val.1 e.val.2 z y))).symm
    _ = _ := by
      congr 1
      · apply Finset.prod_congr rfl
        intro p hp
        exact restrictedPairFactor_change_right_of_contains_left F K e p
          (fun hpe ↦ heT (hpe ▸ (Finset.mem_filter.mp hp).1))
          (Finset.mem_filter.mp hp).2 z.1 z.2 base y
      · apply Finset.prod_congr rfl
        intro p hp
        exact restrictedPairFactor_change_left_of_not_contains_left F K e p
          (Finset.mem_filter.mp hp).2 z.1 base z.2 y

private theorem restrictedRole_mul_mixedPairProduct_pairRest_factor
    (F : SimpleGraph (Fin q)) (S : Fin q → Finset V)
    (K : FinitePatternPair q → FiniteWeightedGraph V)
    (e : FinitePatternPair q) (T : Finset (FinitePatternPair q))
    (heT : e ∉ T) (base : V) (z : V × V)
    (y : {r : Fin q //
      ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r} → V) :
    restrictedRoleIndicator S
          (restrictedPairRestAssignment e.val.1 e.val.2 z y) *
        restrictedMixedPairProduct F K T
          (restrictedPairRestAssignment e.val.1 e.val.2 z y) =
      restrictedMixedLeftWeight F S K e T base y z.1 *
        restrictedMixedRightWeight F S K e T base y z.2 := by
  rw [restrictedRoleIndicator_pairRest_factor S e base z y,
    restrictedMixedPairProduct_pairRest_factor F K e T heT base z y]
  unfold restrictedMixedLeftWeight restrictedMixedRightWeight
  ring

private theorem restrictedInducedPairFactor_sub_eq
    (F : SimpleGraph (Fin q)) (A B : FiniteWeightedGraph V)
    (e : FinitePatternPair q) (x : Fin q → V) :
    restrictedInducedPairFactor F A e x -
        restrictedInducedPairFactor F B e x =
      if F.Adj e.val.1 e.val.2 then
        A.weight (x e.val.1) (x e.val.2) -
          B.weight (x e.val.1) (x e.val.2)
      else
        -(A.weight (x e.val.1) (x e.val.2) -
          B.weight (x e.val.1) (x e.val.2)) := by
  unfold restrictedInducedPairFactor
  split_ifs <;> ring

private theorem abs_sum_role_mul_mixed_mul_pairFactor_sub_le
    (hV : 0 < Fintype.card V)
    (F : SimpleGraph (Fin q)) (S : Fin q → Finset V)
    (K : FinitePatternPair q → FiniteWeightedGraph V)
    (e : FinitePatternPair q) (T : Finset (FinitePatternPair q))
    (heT : e ∉ T) (A B : FiniteWeightedGraph V) :
    |∑ x : Fin q → V,
        restrictedRoleIndicator S x * restrictedMixedPairProduct F K T x *
          (restrictedInducedPairFactor F A e x -
            restrictedInducedPairFactor F B e x)| ≤
      (Fintype.card
        ({r : Fin q //
          ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r} → V) : ℝ) *
        finiteLabeledCutRaw A B := by
  classical
  let base : V := Classical.choice (Fintype.card_pos_iff.mp hV)
  let E := restrictedAssignmentRestPairEquiv
    e.val.1 e.val.2 (ne_of_lt e.property) (V := V)
  let f : (Fin q → V) → ℝ := fun x ↦
    restrictedRoleIndicator S x * restrictedMixedPairProduct F K T x *
      (restrictedInducedPairFactor F A e x -
        restrictedInducedPairFactor F B e x)
  have hreindex :
      (∑ x : Fin q → V, f x) =
        ∑ z : ({r : Fin q //
              ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r} → V) ×
            (V × V),
          f (E.symm z) := by
    exact (E.symm.sum_comp f).symm
  rw [show (∑ x : Fin q → V,
      restrictedRoleIndicator S x * restrictedMixedPairProduct F K T x *
        (restrictedInducedPairFactor F A e x -
          restrictedInducedPairFactor F B e x)) = ∑ x, f x from rfl,
    hreindex]
  simp only [E, restrictedAssignmentRestPairEquiv,
    restrictedAssignmentPairRestEquiv, Equiv.coe_fn_mk,
    Fintype.sum_prod_type]
  calc
    |∑ y : {r : Fin q //
          ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r} → V,
        ∑ u : V, ∑ v : V,
          f (restrictedPairRestAssignment e.val.1 e.val.2 (u, v) y)| ≤
        ∑ _y : {r : Fin q //
            ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r} → V,
          finiteLabeledCutRaw A B := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro y _hy
      let a : V → ℝ := restrictedMixedLeftWeight F S K e T base y
      let b : V → ℝ := restrictedMixedRightWeight F S K e T base y
      have hrect : ∀ X Y : Finset V,
          |∑ u ∈ X, ∑ v ∈ Y,
            (A.weight u v - B.weight u v)| ≤
            finiteLabeledCutRaw A B := by
        intro X Y
        simpa only [rectangleDiscrepancy] using
          abs_rectangleDiscrepancy_le_raw A B X Y
      have hplus :
          |∑ u, ∑ v, a u * b v *
            (A.weight u v - B.weight u v)| ≤
              finiteLabeledCutRaw A B :=
        DenseGraph.abs_sum_mul_mul_le_of_abs_rect_sum_le
          (D := fun u v ↦ A.weight u v - B.weight u v) a b
          (restrictedMixedLeftWeight_nonneg F S K e T base y)
          (restrictedMixedLeftWeight_le_one F S K e T base y)
          (restrictedMixedRightWeight_nonneg F S K e T base y)
          (restrictedMixedRightWeight_le_one F S K e T base y) hrect
      have hminus :
          |∑ u, ∑ v, a u * b v *
            (-(A.weight u v - B.weight u v))| ≤
              finiteLabeledCutRaw A B := by
        convert hplus using 1 <;> push_cast
        simp only [mul_neg, Finset.sum_neg_distrib, abs_neg]
      by_cases hedge : F.Adj e.val.1 e.val.2
      · have heq :
            (∑ u, ∑ v,
              f (restrictedPairRestAssignment e.val.1 e.val.2 (u, v) y)) =
              ∑ u, ∑ v, a u * b v *
                (A.weight u v - B.weight u v) := by
          apply Finset.sum_congr rfl
          intro u _hu
          apply Finset.sum_congr rfl
          intro v _hv
          simp only [f, restrictedInducedPairFactor_sub_eq, hedge, if_pos]
          rw [restrictedRole_mul_mixedPairProduct_pairRest_factor
            F S K e T heT base (u, v) y]
          simp [a, b, ne_of_lt e.property]
        rw [heq]
        exact hplus
      · have heq :
            (∑ u, ∑ v,
              f (restrictedPairRestAssignment e.val.1 e.val.2 (u, v) y)) =
              ∑ u, ∑ v, a u * b v *
                (-(A.weight u v - B.weight u v)) := by
          apply Finset.sum_congr rfl
          intro u _hu
          apply Finset.sum_congr rfl
          intro v _hv
          simp only [f, restrictedInducedPairFactor_sub_eq, hedge, if_neg]
          rw [restrictedRole_mul_mixedPairProduct_pairRest_factor
            F S K e T heT base (u, v) y]
          simp [a, b, ne_of_lt e.property]
        rw [heq]
        exact hminus
    _ = _ := by simp

private theorem restricted_rest_card_mul_card_sq
    (e : FinitePatternPair q) :
    Fintype.card
          ({r : Fin q //
            ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r} → V) *
        Fintype.card V ^ 2 =
      Fintype.card V ^ q := by
  classical
  have hcard := Fintype.card_congr
    (restrictedAssignmentRestPairEquiv
      e.val.1 e.val.2 (ne_of_lt e.property) (V := V))
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod,
    pow_two, mul_assoc] using hcard.symm

private theorem abs_normalized_sum_role_mul_mixed_mul_pairFactor_sub_le
    (hV : 0 < Fintype.card V)
    (F : SimpleGraph (Fin q)) (S : Fin q → Finset V)
    (K : FinitePatternPair q → FiniteWeightedGraph V)
    (e : FinitePatternPair q) (T : Finset (FinitePatternPair q))
    (heT : e ∉ T) (A B : FiniteWeightedGraph V) :
    |(1 / (Fintype.card V : ℝ)) ^ q *
        ∑ x : Fin q → V,
          restrictedRoleIndicator S x * restrictedMixedPairProduct F K T x *
            (restrictedInducedPairFactor F A e x -
              restrictedInducedPairFactor F B e x)| ≤
      finiteLabeledCutDist A B := by
  let R := {r : Fin q //
    ¬restrictedPairCoordinatePredicate e.val.1 e.val.2 r}
  have hraw := abs_sum_role_mul_mixed_mul_pairFactor_sub_le
    hV F S K e T heT A B
  rw [abs_mul, abs_of_nonneg (by positivity :
    0 ≤ (1 / (Fintype.card V : ℝ)) ^ q)]
  calc
    (1 / (Fintype.card V : ℝ)) ^ q *
        |∑ x : Fin q → V,
          restrictedRoleIndicator S x * restrictedMixedPairProduct F K T x *
            (restrictedInducedPairFactor F A e x -
              restrictedInducedPairFactor F B e x)| ≤
        (1 / (Fintype.card V : ℝ)) ^ q *
          ((Fintype.card (R → V) : ℝ) * finiteLabeledCutRaw A B) := by
      gcongr
    _ = finiteLabeledCutDist A B := by
      unfold finiteLabeledCutDist R
      have hN : (Fintype.card V : ℝ) ≠ 0 := by positivity
      have hcard := restricted_rest_card_mul_card_sq (V := V) e
      have hcardReal :
          (Fintype.card (R → V) : ℝ) * (Fintype.card V : ℝ) ^ 2 =
            (Fintype.card V : ℝ) ^ q := by
        exact_mod_cast hcard
      rw [one_div, inv_pow]
      field_simp
      calc
        (Fintype.card (R → V) : ℝ) * finiteLabeledCutRaw A B *
            (Fintype.card V : ℝ) ^ 2 =
            ((Fintype.card (R → V) : ℝ) *
              (Fintype.card V : ℝ) ^ 2) * finiteLabeledCutRaw A B := by ring
        _ = (Fintype.card V : ℝ) ^ q * finiteLabeledCutRaw A B := by
          rw [hcardReal]

private theorem abs_normalized_sum_common_mixedPairProduct_sub_le
    (hV : 0 < Fintype.card V)
    (F : SimpleGraph (Fin q)) (S : Fin q → Finset V)
    (C T : Finset (FinitePatternPair q)) (hCT : Disjoint C T)
    (K : FinitePatternPair q → FiniteWeightedGraph V)
    (A B : FiniteWeightedGraph V) :
    |(1 / (Fintype.card V : ℝ)) ^ q *
        ∑ x : Fin q → V,
          restrictedRoleIndicator S x * restrictedMixedPairProduct F K C x *
            (restrictedMixedPairProduct F (fun _ ↦ A) T x -
              restrictedMixedPairProduct F (fun _ ↦ B) T x)| ≤
      (T.card : ℝ) * finiteLabeledCutDist A B := by
  classical
  induction T using Finset.induction_on generalizing C K with
  | empty => simp [restrictedMixedPairProduct]
  | @insert e T he ih =>
      have heC : e ∉ C := by
        intro heC
        exact Finset.disjoint_left.mp hCT heC (by simp)
      have hCTrest : Disjoint C T :=
        hCT.mono_right (Finset.subset_insert _ _)
      let D : Finset (FinitePatternPair q) := C ∪ T
      let KD : FinitePatternPair q → FiniteWeightedGraph V :=
        fun p ↦ if p ∈ C then K p else A
      have heD : e ∉ D := by simp [D, heC, he]
      have hDfactor (x : Fin q → V) :
          restrictedMixedPairProduct F KD D x =
            restrictedMixedPairProduct F K C x *
              restrictedMixedPairProduct F (fun _ ↦ A) T x := by
        simp only [restrictedMixedPairProduct, D]
        rw [Finset.prod_union hCTrest]
        congr 1
        · apply Finset.prod_congr rfl
          intro p hp
          simp [KD, hp]
        · apply Finset.prod_congr rfl
          intro p hp
          have hpC : p ∉ C := fun hpC ↦
            Finset.disjoint_left.mp hCTrest hpC hp
          simp [KD, hpC]
      let C' : Finset (FinitePatternPair q) := insert e C
      let K' : FinitePatternPair q → FiniteWeightedGraph V :=
        fun p ↦ if p = e then B else K p
      have hC'T : Disjoint C' T := by
        simp only [C', Finset.disjoint_insert_left]
        exact ⟨he, hCTrest⟩
      have hC'factor (x : Fin q → V) :
          restrictedMixedPairProduct F K' C' x =
            restrictedInducedPairFactor F B e x *
              restrictedMixedPairProduct F K C x := by
        simp only [restrictedMixedPairProduct, C']
        rw [Finset.prod_insert heC]
        congr 1
        · simp [K']
        · apply Finset.prod_congr rfl
          intro p hp
          have hpne : p ≠ e := fun hpe ↦ heC (hpe ▸ hp)
          simp [K', hpne]
      have hAinsert (x : Fin q → V) :
          restrictedMixedPairProduct F (fun _ ↦ A) (insert e T) x =
            restrictedInducedPairFactor F A e x *
              restrictedMixedPairProduct F (fun _ ↦ A) T x := by
        simp [restrictedMixedPairProduct, he]
      have hBinsert (x : Fin q → V) :
          restrictedMixedPairProduct F (fun _ ↦ B) (insert e T) x =
            restrictedInducedPairFactor F B e x *
              restrictedMixedPairProduct F (fun _ ↦ B) T x := by
        simp [restrictedMixedPairProduct, he]
      let first : (Fin q → V) → ℝ := fun x ↦
        restrictedRoleIndicator S x * restrictedMixedPairProduct F KD D x *
          (restrictedInducedPairFactor F A e x -
            restrictedInducedPairFactor F B e x)
      let second : (Fin q → V) → ℝ := fun x ↦
        restrictedRoleIndicator S x * restrictedMixedPairProduct F K' C' x *
          (restrictedMixedPairProduct F (fun _ ↦ A) T x -
            restrictedMixedPairProduct F (fun _ ↦ B) T x)
      have hpoint (x : Fin q → V) :
          restrictedRoleIndicator S x * restrictedMixedPairProduct F K C x *
              (restrictedMixedPairProduct F (fun _ ↦ A) (insert e T) x -
                restrictedMixedPairProduct F (fun _ ↦ B) (insert e T) x) =
            first x + second x := by
        rw [hAinsert x, hBinsert x]
        simp only [first, second, hDfactor x, hC'factor x]
        ring
      have hfirst :
          |(1 / (Fintype.card V : ℝ)) ^ q * ∑ x, first x| ≤
            finiteLabeledCutDist A B := by
        exact abs_normalized_sum_role_mul_mixed_mul_pairFactor_sub_le
          hV F S KD e D heD A B
      have hsecond :
          |(1 / (Fintype.card V : ℝ)) ^ q * ∑ x, second x| ≤
            (T.card : ℝ) * finiteLabeledCutDist A B := by
        exact ih C' hC'T K'
      rw [show (∑ x : Fin q → V,
          restrictedRoleIndicator S x * restrictedMixedPairProduct F K C x *
            (restrictedMixedPairProduct F (fun _ ↦ A) (insert e T) x -
              restrictedMixedPairProduct F (fun _ ↦ B) (insert e T) x)) =
            ∑ x, (first x + second x) by
              apply Finset.sum_congr rfl
              intro x _hx
              exact hpoint x,
        Finset.sum_add_distrib, mul_add]
      calc
        |(1 / (Fintype.card V : ℝ)) ^ q * ∑ x, first x +
            (1 / (Fintype.card V : ℝ)) ^ q * ∑ x, second x| ≤
            |(1 / (Fintype.card V : ℝ)) ^ q * ∑ x, first x| +
              |(1 / (Fintype.card V : ℝ)) ^ q * ∑ x, second x| :=
          abs_add_le _ _
        _ ≤ finiteLabeledCutDist A B +
              (T.card : ℝ) * finiteLabeledCutDist A B :=
          add_le_add hfirst hsecond
        _ = ((insert e T).card : ℝ) * finiteLabeledCutDist A B := by
          rw [Finset.card_insert_of_notMem he]
          push_cast
          ring

/-- Restricted normalized induced-pattern counts are Lipschitz in the
same-label finite cut distance, with one unit of loss per unordered pattern
pair.  The role sets need not be disjoint. -/
theorem abs_restrictedInducedPatternCount_sub_le_choose_mul_finiteLabeledCutDist
    (hV : 0 < Fintype.card V)
    (F : SimpleGraph (Fin q)) (A B : FiniteWeightedGraph V)
    (S : Fin q → Finset V) :
    |restrictedInducedPatternCount F A S -
        restrictedInducedPatternCount F B S| ≤
      (Nat.choose q 2 : ℝ) * finiteLabeledCutDist A B := by
  classical
  have h := abs_normalized_sum_common_mixedPairProduct_sub_le
    hV F S ∅ (Finset.univ : Finset (FinitePatternPair q))
      (by simp) (fun _ ↦ A) A B
  simpa [restrictedInducedPatternCount, restrictedInducedMapWeight,
    restrictedMixedPairProduct, Finset.sum_sub_distrib, Finset.mul_sum,
    mul_sub] using h

end FiniteWeightedGraph

end DenseGraph
