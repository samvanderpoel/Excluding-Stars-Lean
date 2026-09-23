import InducedStars.Structure.Subcritical.RetainedKeyCounts
import InducedStars.Graphon.EntropyUpperBound

/-!
# Weighted graphons of exact retained edge vectors

Paper: the weighted step graphon in `lemma:clean-retained-comparison-K1k`.
The division in this module is the division stored in a retained
key, so every one of its components is used. The sparse remainder has zero
weight. Clique squares include their diagonal cells; the resulting finite
diagonal correction is kept exactly in the density formula.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

variable {k n : ℕ}

/-- The regular-core obstruction applies to weighted matrices, including
noninjective label maps. No positivity of the active densities is needed. -/
theorem subcriticalWeightedMatrix_inducedStar_weight_zero
    (hk : 3 ≤ k) (D : SubcriticalDivision k (Fin n))
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (hcomplete : ∀ x y, D.SamePart x y → M x y = 1)
    (hallowed : ∀ x y, M x y ≠ 0 → D.SamePart x y ∨ D.ActivePair x y)
    (φ : Fin (k + 1) → Fin n) :
    matrixInducedMapWeight (inducedStar k) M hM φ = 0 := by
  by_cases hbad : ∃ a : Fin k, M (φ 0) (φ a.succ) = 0
  · obtain ⟨a, ha⟩ := hbad
    have he : s(0, a.succ) ∈ finiteGraphEdges (inducedStar k) := by
      simpa using inducedStar_center_adj_leaf a
    have hz : (∏ e ∈ finiteGraphEdges (inducedStar k),
        matrixMapPairValue M hM φ e) = 0 :=
      Finset.prod_eq_zero he (by simpa using ha)
    simp only [matrixInducedMapWeight, hz, zero_mul]
  have hcenter (a : Fin k) : M (φ 0) (φ a.succ) ≠ 0 := fun h ↦ hbad ⟨a, h⟩
  let a₀ : Fin k := ⟨0, by omega⟩
  have hsupport : φ 0 ∈ D.support := by
    rcases hallowed _ _ (hcenter a₀) with h | h
    · exact (SubcriticalDivision.samePart_imp_support h).1
    · exact (SubcriticalDivision.activePair_imp_support h).1
  obtain ⟨c, hc⟩ := D.mem_support.mp hsupport
  have hleaf (a : Fin k) : φ a.succ ∈ D.support := by
    rcases hallowed _ _ (hcenter a) with h | h
    · exact (SubcriticalDivision.samePart_imp_support h).2
    · exact (SubcriticalDivision.activePair_imp_support h).2
  let part : Fin k → D.PartIndex := fun a ↦ (D.mem_support.mp (hleaf a)).choose
  have hpart (a : Fin k) : φ a.succ ∈ D.part (part a) :=
    (D.mem_support.mp (hleaf a)).choose_spec
  have hclosed (a : Fin k) : part a ∈ D.closedPartIndices c := by
    rcases hallowed _ _ (hcenter a) with h | h
    · have he := (D.samePart_iff_of_mem_parts hc (hpart a)).mp h
      rw [← he]
      exact D.self_mem_closedPartIndices c
    · exact D.mem_closedPartIndices_of_activePart
        ((D.activePair_iff_of_mem_parts hc (hpart a)).mp h)
  let f : Fin k → {a // a ∈ D.closedPartIndices c} := fun a ↦ ⟨part a, hclosed a⟩
  have hnot : ¬ Function.Injective f := by
    intro hinj
    have hcard := Fintype.card_le_of_injective f hinj
    have : k ≤ k - 1 := by
      simpa only [Fintype.card_fin, Fintype.card_coe, D.card_closedPartIndices hk c]
        using hcard
    omega
  simp only [Function.Injective] at hnot
  push_neg at hnot
  obtain ⟨a, b, hab, hne⟩ := hnot
  have heq : part a = part b := congrArg Subtype.val hab
  have hsame : D.SamePart (φ a.succ) (φ b.succ) :=
    ⟨part a, hpart a, by simpa only [heq] using hpart b⟩
  have hnon : s(a.succ, b.succ) ∈ finiteGraphEdges (inducedStar k)ᶜ := by
    have hs : a.succ ≠ b.succ := by simpa using hne
    simp [hs]
  have hz : (∏ e ∈ finiteGraphEdges (inducedStar k)ᶜ,
      (1 - matrixMapPairValue M hM φ e)) = 0 :=
    Finset.prod_eq_zero hnon (by simp [hcomplete _ _ hsame])
  simp only [matrixInducedMapWeight, hz, mul_zero]

section Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (D : SubcriticalDivision k V)

/-- Matrix attached to an exact edge vector on all components of a retained
key. There is a single active density on each unordered bipartite block. -/
def retainedProfileMatrix
    (v : RetainedEdgeCountVector D 0 (Fintype.card V)) : Matrix V V ℝ :=
  fun x y ↦ if D.SamePart x y then 1 else
    ∑ e : RetainedActivePair D 0 (Fintype.card V),
      if s(x, y) ∈ retainedActivePotentialEdges D 0 (Fintype.card V) e
      then retainedEdgeCountDensity v e else 0

theorem retainedActivePotentialEdges_mem_activePair
    (e : RetainedActivePair D 0 (Fintype.card V)) {x y : V}
    (h : s(x, y) ∈ retainedActivePotentialEdges D 0 (Fintype.card V) e) :
    D.ActivePair x y := by
  obtain ⟨a, ha, b, hb, hab⟩ := (mem_retainedActivePotentialEdges _ _ _ _ _).mp h
  rcases (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (a, b))).mp hab with hh | hh
  · have hx : x = a := congrArg Prod.fst hh
    have hy : y = b := congrArg Prod.snd hh
    subst x; subst y
    exact (D.activePair_iff_of_mem_parts ha hb).mpr e.activePart
  · have hx : x = b := congrArg Prod.fst hh
    have hy : y = a := congrArg Prod.snd hh
    subst x; subst y
    exact (D.activePair_comm _ _).mp
      ((D.activePair_iff_of_mem_parts ha hb).mpr e.activePart)

theorem retainedProfileMatrix_isSymm
    (v : RetainedEdgeCountVector D 0 (Fintype.card V)) :
    (retainedProfileMatrix D v).IsSymm := by
  ext x y
  simp only [Matrix.transpose_apply, retainedProfileMatrix, Sym2.eq_swap]
  have hs : D.SamePart y x ↔ D.SamePart x y := D.samePart_comm y x
  rw [hs]

theorem retainedProfileMatrix_samePart
    (v : RetainedEdgeCountVector D 0 (Fintype.card V)) {x y : V}
    (h : D.SamePart x y) : retainedProfileMatrix D v x y = 1 := by
  simp [retainedProfileMatrix, h]

theorem retainedProfileMatrix_active
    (v : RetainedEdgeCountVector D 0 (Fintype.card V))
    (e : RetainedActivePair D 0 (Fintype.card V)) {x y : V}
    (h : s(x, y) ∈ retainedActivePotentialEdges D 0 (Fintype.card V) e) :
    retainedProfileMatrix D v x y = retainedEdgeCountDensity v e := by
  have ha := retainedActivePotentialEdges_mem_activePair D e h
  have hs : ¬ D.SamePart x y := fun h ↦ SubcriticalDivision.not_activePair_of_samePart h ha
  simp only [retainedProfileMatrix, if_neg hs]
  rw [Finset.sum_eq_single e]
  · simp [h]
  · intro f hf hfe
    have hn : s(x, y) ∉ retainedActivePotentialEdges D 0 (Fintype.card V) f := by
      intro hh
      exact Finset.disjoint_left.mp
        (retainedActivePotentialEdges_disjoint D 0 (Fintype.card V) hfe) hh h
    simp [hn]
  · simp

theorem retainedProfileMatrix_allowed
    (v : RetainedEdgeCountVector D 0 (Fintype.card V)) {x y : V}
    (h : retainedProfileMatrix D v x y ≠ 0) :
    D.SamePart x y ∨ D.ActivePair x y := by
  by_cases hs : D.SamePart x y
  · exact Or.inl hs
  right
  by_contra ha
  apply h
  simp only [retainedProfileMatrix, if_neg hs]
  apply Finset.sum_eq_zero
  intro e he
  have hn : s(x, y) ∉ retainedActivePotentialEdges D 0 (Fintype.card V) e :=
    fun hh ↦ ha (retainedActivePotentialEdges_mem_activePair D e hh)
  simp [hn]

theorem retainedProfileMatrix_bounds
    (v : RetainedEdgeCountVector D 0 (Fintype.card V)) (x y : V) :
    retainedProfileMatrix D v x y ∈ Icc (0 : ℝ) 1 := by
  by_cases hs : D.SamePart x y
  · simp [retainedProfileMatrix_samePart D v hs]
  by_cases ha : ∃ e : RetainedActivePair D 0 (Fintype.card V),
      s(x, y) ∈ retainedActivePotentialEdges D 0 (Fintype.card V) e
  · obtain ⟨e, he⟩ := ha
    rw [retainedProfileMatrix_active D v e he]
    constructor
    · exact div_nonneg (by positivity) (by positivity)
    · apply (div_le_one (by exact_mod_cast retainedActiveCapacity_pos D 0 _ e)).mpr
      exact_mod_cast v.count_le_capacity e
  · have hz : retainedProfileMatrix D v x y = 0 := by
      simp only [retainedProfileMatrix, if_neg hs]
      apply Finset.sum_eq_zero
      intro e he
      simp [show s(x, y) ∉ retainedActivePotentialEdges D 0 (Fintype.card V) e
        from fun h ↦ ha ⟨e, h⟩]
    simp [hz]

theorem retainedProfileMatrix_function_eq
    (v : RetainedEdgeCountVector D 0 (Fintype.card V)) (f : ℝ → ℝ)
    (hf : f 0 = 0) (x y : V) :
    f (retainedProfileMatrix D v x y) =
      (if D.SamePart x y then f 1 else 0) +
        ∑ e : RetainedActivePair D 0 (Fintype.card V),
          if s(x, y) ∈ retainedActivePotentialEdges D 0 (Fintype.card V) e
          then f (retainedEdgeCountDensity v e) else 0 := by
  by_cases hs : D.SamePart x y
  · rw [retainedProfileMatrix_samePart D v hs, if_pos hs]
    have hz : (∑ e : RetainedActivePair D 0 (Fintype.card V),
        if s(x, y) ∈ retainedActivePotentialEdges D 0 (Fintype.card V) e
        then f (retainedEdgeCountDensity v e) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      have hn : s(x, y) ∉ retainedActivePotentialEdges D 0 (Fintype.card V) e :=
        fun h ↦ SubcriticalDivision.not_activePair_of_samePart hs
          (retainedActivePotentialEdges_mem_activePair D e h)
      simp [hn]
    rw [hz, add_zero]
  rw [if_neg hs, zero_add]
  by_cases ha : ∃ e : RetainedActivePair D 0 (Fintype.card V),
      s(x, y) ∈ retainedActivePotentialEdges D 0 (Fintype.card V) e
  · obtain ⟨e, he⟩ := ha
    rw [retainedProfileMatrix_active D v e he, Finset.sum_eq_single e]
    · simp [he]
    · intro g hg hge
      have hn : s(x, y) ∉ retainedActivePotentialEdges D 0 (Fintype.card V) g :=
        fun h ↦ Finset.disjoint_left.mp
          (retainedActivePotentialEdges_disjoint D 0 (Fintype.card V) hge) h he
      simp [hn]
    · simp
  · have hn (e : RetainedActivePair D 0 (Fintype.card V)) :
        s(x, y) ∉ retainedActivePotentialEdges D 0 (Fintype.card V) e :=
      fun h ↦ ha ⟨e, h⟩
    simp [retainedProfileMatrix, hs, hn, hf]

theorem sum_sum_samePart_indicator (c : ℝ) :
    (∑ x : V, ∑ y : V, if D.SamePart x y then c else 0) =
      ∑ a : D.PartIndex, ((D.part a).card : ℝ)^2 * c := by
  have hpoint (x y : V) :
      (if D.SamePart x y then c else 0) =
        ∑ a : D.PartIndex, if x ∈ D.part a then if y ∈ D.part a then c else 0 else 0 := by
    by_cases hs : D.SamePart x y
    · obtain ⟨a, hx, hy⟩ := hs
      rw [if_pos ⟨a, hx, hy⟩, Finset.sum_eq_single a]
      · simp [hx, hy]
      · intro b hb hba
        have hn : x ∉ D.part b := fun h ↦ hba (D.mem_part_unique h hx)
        simp [hn]
      · simp
    · rw [if_neg hs]
      symm
      apply Finset.sum_eq_zero
      intro a ha
      by_cases hx : x ∈ D.part a
      · have hy : y ∉ D.part a := fun h ↦ hs ⟨a, hx, h⟩
        simp [hx, hy]
      · simp [hx]
  simp_rw [hpoint]
  calc
    _ = ∑ x : V, ∑ a : D.PartIndex, ∑ y : V,
        if x ∈ D.part a then if y ∈ D.part a then c else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ a : D.PartIndex, ∑ x : V, ∑ y : V,
        if x ∈ D.part a then if y ∈ D.part a then c else 0 else 0 := Finset.sum_comm
    _ = _ := ?_
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp [pow_two, mul_assoc]

theorem sum_sum_active_indicator
    (e : RetainedActivePair D 0 (Fintype.card V)) (c : ℝ) :
    (∑ x : V, ∑ y : V,
      if s(x, y) ∈ retainedActivePotentialEdges D 0 (Fintype.card V) e then c else 0) =
      2 * (retainedActiveCapacity D 0 (Fintype.card V) e : ℝ) * c := by
  have hmem (x y : V) :
      s(x, y) ∈ retainedActivePotentialEdges D 0 (Fintype.card V) e ↔
        (x ∈ D.part e.leftPart ∧ y ∈ D.part e.rightPart) ∨
          (x ∈ D.part e.rightPart ∧ y ∈ D.part e.leftPart) := by
    rw [mem_retainedActivePotentialEdges]
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      rcases (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (a, b))).mp hab with h | h
      · cases h
        exact Or.inl ⟨ha, hb⟩
      · have hx : x = b := congrArg Prod.fst h
        have hy : y = a := congrArg Prod.snd h
        exact Or.inr ⟨hx.symm ▸ hb, hy.symm ▸ ha⟩
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
      · exact ⟨x, hx, y, hy, rfl⟩
      · exact ⟨y, hy, x, hx, Sym2.eq_swap⟩
  have hpoint (x y : V) :
      (if s(x, y) ∈ retainedActivePotentialEdges D 0 (Fintype.card V) e then c else 0) =
        (if x ∈ D.part e.leftPart then if y ∈ D.part e.rightPart then c else 0 else 0) +
        (if x ∈ D.part e.rightPart then if y ∈ D.part e.leftPart then c else 0 else 0) := by
    have hdis : ¬ (x ∈ D.part e.leftPart ∧ x ∈ D.part e.rightPart) :=
      fun h ↦ e.leftPart_ne_rightPart (D.mem_part_unique h.1 h.2)
    simp only [hmem]
    split_ifs <;> simp_all
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_ite_irrel]
  simp [retainedActiveCapacity, mul_comm, mul_left_comm, mul_assoc, two_mul]
  <;> ring

/-- Exact functional sum over all equal vertex cells. -/
theorem retainedProfileMatrix_sum_function
    (v : RetainedEdgeCountVector D 0 (Fintype.card V)) (f : ℝ → ℝ)
    (hf : f 0 = 0) :
    (∑ x : V, ∑ y : V, f (retainedProfileMatrix D v x y)) =
      (∑ a : D.PartIndex, ((D.part a).card : ℝ)^2) * f 1 +
        2 * ∑ e : RetainedActivePair D 0 (Fintype.card V),
          (retainedActiveCapacity D 0 (Fintype.card V) e : ℝ) *
            f (retainedEdgeCountDensity v e) := by
  simp_rw [retainedProfileMatrix_function_eq D v f hf, Finset.sum_add_distrib]
  rw [sum_sum_samePart_indicator, ← Finset.sum_mul]
  congr 1
  calc
    _ = ∑ x : V, ∑ e : RetainedActivePair D 0 (Fintype.card V), ∑ y : V,
        if s(x, y) ∈ retainedActivePotentialEdges D 0 (Fintype.card V) e
        then f (retainedEdgeCountDensity v e) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ e : RetainedActivePair D 0 (Fintype.card V), ∑ x : V, ∑ y : V,
        if s(x, y) ∈ retainedActivePotentialEdges D 0 (Fintype.card V) e
        then f (retainedEdgeCountDensity v e) else 0 := Finset.sum_comm
    _ = ∑ e : RetainedActivePair D 0 (Fintype.card V),
        2 * (retainedActiveCapacity D 0 (Fintype.card V) e : ℝ) *
          f (retainedEdgeCountDensity v e) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [sum_sum_active_indicator]
    _ = _ := by rw [Finset.mul_sum]; congr 1; funext e; ring

end Matrix

/-- Equal-vertex-cell weighted graphon of a retained vector. -/
def retainedProfileGraphon (D : SubcriticalDivision k (Fin n))
    (v : RetainedEdgeCountVector D 0 (Fintype.card (Fin n))) : Graphon :=
  matrixGraphon (retainedProfileMatrix D v) (retainedProfileMatrix_isSymm D v)
    (fun x y ↦ (retainedProfileMatrix_bounds D v x y).1)
    (fun x y ↦ (retainedProfileMatrix_bounds D v x y).2)

theorem retainedProfileGraphon_inducedStar_free
    (hk : 3 ≤ k) (hn : 0 < n) (D : SubcriticalDivision k (Fin n))
    (v : RetainedEdgeCountVector D 0 (Fintype.card (Fin n))) :
    graphonInducedDensity (inducedStar k) (retainedProfileGraphon D v) = 0 := by
  apply graphonInducedDensity_matrixGraphon_eq_zero_of_weights hn
  exact subcriticalWeightedMatrix_inducedStar_weight_zero hk D _ _
    (fun x y h ↦ retainedProfileMatrix_samePart D v h)
    (fun x y h ↦ retainedProfileMatrix_allowed D v h)

end InducedStars
