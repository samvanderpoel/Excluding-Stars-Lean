import InducedStars.Structure.Subcritical.ClosenessResult
import Mathlib.Data.Fin.Tuple.Embedding

/-!
# Finite row witnesses for the deterministic subcritical constraints

Paper: the definitions of `N_{i,j}` and `\mathcal N_{\Pi,G}(v)` and the
selection steps of the three deterministic adjacency lemmas.  Complement
degrees are loopless.  Every selected free-vertex class excludes its fixed
root, including a nonneighbor class in the root's own part.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

variable {k n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The union of the parts adjacent to one core vertex. -/
def subcriticalCoreNeighborUnion (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (j : Fin (D.core i).order) : Finset V :=
  ((D.core i).graph.neighborFinset j).biUnion (D.parts i)

@[simp] theorem mem_subcriticalCoreNeighborUnion
    (D : SubcriticalDivision k V) (i : Fin D.componentCount)
    (j : Fin (D.core i).order) (x : V) :
    x ∈ subcriticalCoreNeighborUnion D i j ↔
      ∃ u, (D.core i).graph.Adj j u ∧ x ∈ D.parts i u := by
  simp [subcriticalCoreNeighborUnion]

theorem part_subset_subcriticalCoreNeighborUnion
    (D : SubcriticalDivision k V) (i : Fin D.componentCount)
    {j u : Fin (D.core i).order} (hju : (D.core i).graph.Adj j u) :
    D.parts i u ⊆ subcriticalCoreNeighborUnion D i j :=
  fun x hx ↦ (mem_subcriticalCoreNeighborUnion D i j x).mpr ⟨u, hju, hx⟩

/-- Visible parts on which the fixed vertex has a non-low ordinary row. -/
def subcriticalNonlowVisibleParts (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (alpha theta : ℝ) (v : V) :
    Finset D.PartIndex :=
  (D.visiblePartIndices theta).filter fun a ↦
    alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)

@[simp] theorem mem_subcriticalNonlowVisibleParts
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (alpha theta : ℝ) (v : V) (a : D.PartIndex) :
    a ∈ subcriticalNonlowVisibleParts G D alpha theta v ↔
      a ∈ D.visiblePartIndices theta ∧
        alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ) := by
  simp [subcriticalNonlowVisibleParts]

/-- The ordinary row-neighbor set, whose cardinality is the existing
`degreeInFinset`. -/
def subcriticalRowNeighborSet (G : SimpleGraph V) (v : V) (P : Finset V) :
    Finset V := P.filter (G.Adj v)

/-- The loopless complementary row; in particular it never contains `v`. -/
def subcriticalRowNonneighborSet (G : SimpleGraph V) (v : V) (P : Finset V) :
    Finset V := P.filter fun w ↦ w ≠ v ∧ ¬ G.Adj v w

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_subcriticalRowNeighborSet (G : SimpleGraph V) (v w : V)
    (P : Finset V) : w ∈ subcriticalRowNeighborSet G v P ↔ w ∈ P ∧ G.Adj v w := by
  simp [subcriticalRowNeighborSet]

omit [Fintype V] in
@[simp] theorem mem_subcriticalRowNonneighborSet (G : SimpleGraph V) (v w : V)
    (P : Finset V) :
    w ∈ subcriticalRowNonneighborSet G v P ↔ w ∈ P ∧ w ≠ v ∧ ¬ G.Adj v w := by
  simp [subcriticalRowNonneighborSet]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem card_subcriticalRowNeighborSet (G : SimpleGraph V) (v : V)
    (P : Finset V) : (subcriticalRowNeighborSet G v P).card = degreeInFinset G v P := rfl

omit [Fintype V] in
@[simp] theorem card_subcriticalRowNonneighborSet (G : SimpleGraph V) (v : V)
    (P : Finset V) :
    (subcriticalRowNonneighborSet G v P).card = complementDegreeInFinset G v P := rfl

@[simp] theorem root_not_mem_subcriticalRowNeighborSet (G : SimpleGraph V)
    (v : V) (P : Finset V) : v ∉ subcriticalRowNeighborSet G v P := by simp

@[simp] theorem root_not_mem_subcriticalRowNonneighborSet (G : SimpleGraph V)
    (v : V) (P : Finset V) : v ∉ subcriticalRowNonneighborSet G v P := by simp

theorem degreeInFinset_add_complementDegreeInFinset_of_mem
    (G : SimpleGraph V) (v : V) (P : Finset V) (hv : v ∈ P) :
    degreeInFinset G v P + complementDegreeInFinset G v P = P.card - 1 := by
  rw [degreeInFinset_add_complementDegreeInFinset, Finset.card_erase_of_mem hv]

theorem degreeInFinset_add_complementDegreeInFinset_of_notMem
    (G : SimpleGraph V) (v : V) (P : Finset V) (hv : v ∉ P) :
    degreeInFinset G v P + complementDegreeInFinset G v P = P.card := by
  rw [degreeInFinset_add_complementDegreeInFinset, Finset.erase_eq_of_notMem hv]

/-- A real-valued lower bound that keeps the possible deletion of the root. -/
theorem complementDegreeInFinset_ge_card_sub_degree_sub_one
    (G : SimpleGraph V) (v : V) (P : Finset V) :
    (P.card : ℝ) - degreeInFinset G v P - 1 ≤ complementDegreeInFinset G v P := by
  have hsum := degreeInFinset_add_complementDegreeInFinset G v P
  have hcard : P.card ≤ (P.erase v).card + 1 := by
    by_cases hv : v ∈ P
    · exact (Finset.card_erase_add_one hv).ge
    · simp [Finset.erase_eq_of_notMem hv]
  have hreal : (P.card : ℝ) ≤ degreeInFinset G v P +
      (complementDegreeInFinset G v P : ℝ) + 1 := by
    exact_mod_cast (by omega : P.card ≤ degreeInFinset G v P + complementDegreeInFinset G v P + 1)
  linarith

namespace SubcriticalCloseStructureResult

variable {R₀ : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
  {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
  {omega eta theta alpha delta epsilon : ℝ}

/-- The exact lower size bound for every part of a visible component. -/
theorem visible_part_card_ge
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (homega : 0 ≤ omega) (a : D.PartIndex) (ha : a ∈ D.visiblePartIndices theta) :
    theta * n / (1 + omega) ≤ (D.part a).card := by
  have hi := (D.mem_visiblePartIndices theta a).mp ha
  obtain ⟨u, hu⟩ := (D.mem_visibleComponentIndices theta a.1).mp hi
  have hratio := R.visible_component_ratio a.1 hi u a.2
  apply (div_le_iff₀ (by linarith : 0 < 1 + omega)).mpr
  simpa only [Fintype.card_fin, SubcriticalDivision.part, mul_comm] using hu.trans hratio

/-- For `omega ≤ 1`, each visible part has at least `theta*n/2` vertices. -/
theorem visible_part_card_ge_half
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (homega : omega ≤ 1) (a : D.PartIndex) (ha : a ∈ D.visiblePartIndices theta) :
    theta * n / 2 ≤ (D.part a).card := by
  have hi := (D.mem_visiblePartIndices theta a).mp ha
  obtain ⟨u, hu⟩ := (D.mem_visibleComponentIndices theta a.1).mp hi
  have hratio := R.visible_component_ratio a.1 hi u a.2
  have hmul := mul_le_mul_of_nonneg_right homega (Nat.cast_nonneg (D.parts a.1 a.2).card)
  simp only [Fintype.card_fin] at hu
  change theta * n / 2 ≤ ((D.parts a.1 a.2).card : ℝ)
  nlinarith

end SubcriticalCloseStructureResult

/-- The common size of every free role class in all three row arguments. -/
def subcriticalRoleSize (alpha theta : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (alpha * theta * n / 4)

theorem le_subcriticalRoleSize (alpha theta : ℝ) (n : ℕ) :
    alpha * theta * n / 4 ≤ (subcriticalRoleSize alpha theta n : ℝ) :=
  Nat.le_ceil _

theorem subcriticalRoleSize_pos {alpha theta : ℝ} (hscale : 8 ≤ alpha * theta * n) :
    0 < subcriticalRoleSize alpha theta n := by
  exact Nat.one_le_ceil_iff.mpr (by linarith)

omit [Fintype V] [DecidableEq V] in
/-- One ceiling calculation covers ordinary neighbors, loopless
nonneighbors, and ordinary nonneighbors after the possible loss of a root. -/
theorem subcriticalRoleSize_le_of_row_lower
    (P : Finset V) {alpha theta : ℝ} (halpha : 0 < alpha)
    (hpart : theta * n / 2 ≤ (P.card : ℝ))
    (hscale : 8 ≤ alpha * theta * n) (d : ℕ)
    (hd : alpha * P.card - 1 ≤ (d : ℝ)) :
    subcriticalRoleSize alpha theta n ≤ d := by
  apply Nat.ceil_le.mpr
  have hmul := mul_le_mul_of_nonneg_left hpart halpha.le
  nlinarith

omit [Fintype V] [DecidableEq V] in
/-- Select an exact-size role from a root-free finite eligibility set. -/
theorem subcritical_exists_roleSet_of_card_le
    (S : Finset V) (root : V) {alpha theta : ℝ}
    (hroot : root ∉ S) (hcard : subcriticalRoleSize alpha theta n ≤ S.card) :
    ∃ T, T ⊆ S ∧ T.card = subcriticalRoleSize alpha theta n ∧ root ∉ T := by
  obtain ⟨T, hT, hcardT⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨T, hT, hcardT, fun hrootT ↦ hroot (hT hrootT)⟩

/-- A non-low ordinary row contains an exact-size free neighbor role. -/
theorem subcritical_exists_neighbor_roleSet
    (G : SimpleGraph V) (root : V) (P : Finset V) {alpha theta : ℝ}
    (halpha : 0 < alpha) (hpart : theta * n / 2 ≤ (P.card : ℝ))
    (hscale : 8 ≤ alpha * theta * n)
    (hdegree : alpha * P.card ≤ (degreeInFinset G root P : ℝ)) :
    ∃ S, S ⊆ P ∧ S.card = subcriticalRoleSize alpha theta n ∧ root ∉ S ∧
      ∀ x ∈ S, G.Adj root x := by
  have hd := subcriticalRoleSize_le_of_row_lower P halpha hpart hscale
    (degreeInFinset G root P) (by linarith)
  obtain ⟨S, hS, hc, hr⟩ := subcritical_exists_roleSet_of_card_le
    (subcriticalRowNeighborSet G root P) root (by simp) (by simpa using hd)
  exact ⟨S, fun x hx ↦ ((mem_subcriticalRowNeighborSet G root x P).mp (hS hx)).1,
    hc, hr, fun x hx ↦ ((mem_subcriticalRowNeighborSet G root x P).mp (hS hx)).2⟩

/-- A lower bound on loopless complementary degree supplies a root-free
nonneighbor role. -/
theorem subcritical_exists_nonneighbor_roleSet_of_complement_lower
    (G : SimpleGraph V) (root : V) (P : Finset V) {alpha theta : ℝ}
    (halpha : 0 < alpha) (hpart : theta * n / 2 ≤ (P.card : ℝ))
    (hscale : 8 ≤ alpha * theta * n)
    (hdegree : alpha * P.card - 1 ≤ (complementDegreeInFinset G root P : ℝ)) :
    ∃ S, S ⊆ P ∧ S.card = subcriticalRoleSize alpha theta n ∧ root ∉ S ∧
      ∀ x ∈ S, ¬ G.Adj root x := by
  have hd := subcriticalRoleSize_le_of_row_lower P halpha hpart hscale
    (complementDegreeInFinset G root P) hdegree
  obtain ⟨S, hS, hc, hr⟩ := subcritical_exists_roleSet_of_card_le
    (subcriticalRowNonneighborSet G root P) root (by simp) (by simpa using hd)
  exact ⟨S, fun x hx ↦ ((mem_subcriticalRowNonneighborSet G root x P).mp (hS hx)).1,
    hc, hr, fun x hx ↦ ((mem_subcriticalRowNonneighborSet G root x P).mp (hS hx)).2.2⟩

/-- An ordinary row below the high threshold supplies enough loopless
nonneighbors even when the root belongs to the same parent part. -/
theorem subcritical_exists_nonneighbor_roleSet_of_degree_upper
    (G : SimpleGraph V) (root : V) (P : Finset V) {alpha theta : ℝ}
    (halpha : 0 < alpha) (hpart : theta * n / 2 ≤ (P.card : ℝ))
    (hscale : 8 ≤ alpha * theta * n)
    (hdegree : (degreeInFinset G root P : ℝ) ≤ (1 - alpha) * P.card) :
    ∃ S, S ⊆ P ∧ S.card = subcriticalRoleSize alpha theta n ∧ root ∉ S ∧
      ∀ x ∈ S, ¬ G.Adj root x := by
  apply subcritical_exists_nonneighbor_roleSet_of_complement_lower G root P
    halpha hpart hscale
  have hcomp := complementDegreeInFinset_ge_card_sub_degree_sub_one G root P
  nlinarith

omit [Fintype V] [DecidableEq V] in
/-- Free independent neighbors, with the root fixed as center, give the
canonical induced star on exactly `k+1` distinct vertices. -/
theorem inducedEmbeds_inducedStar_of_fixed_center
    (G : SimpleGraph V) (root : V) (f : Fin k ↪ V)
    (hadj : ∀ i, G.Adj root (f i))
    (hind : ∀ i j, ¬ G.Adj (f i) (f j)) :
    Regularity.InducedEmbeds (inducedStar k) G := by
  have hout : root ∉ Set.range f := by
    rintro ⟨i, hi⟩
    have h := hadj i
    rw [hi] at h
    exact G.irrefl h
  let e := Fin.Embedding.cons f hout
  refine ⟨{ toFun := e, inj' := e.injective, map_rel_iff' := ?_ }⟩
  intro a b
  change G.Adj (e a) (e b) ↔ (inducedStar k).Adj a b
  refine Fin.cases ?_ (fun i ↦ ?_) a
  · refine Fin.cases ?_ (fun j ↦ ?_) b
    · simp [e, Fin.Embedding.cons]
    · simpa [e, Fin.Embedding.cons, (Fin.succ_ne_zero j).symm] using hadj j
  · refine Fin.cases ?_ (fun j ↦ ?_) b
    · simpa [e, Fin.Embedding.cons] using (hadj i).symm
    · simp [e, Fin.Embedding.cons, hind]

omit [Fintype V] [DecidableEq V] in
/-- A transversal free star together with a fixed external vertex adjacent
exactly to its center extends to the canonical induced `K_{1,k}`.  Only
the free vertices are counted; the prescribed root is adjoined afterwards. -/
theorem inducedEmbeds_inducedStar_of_fixed_leaf
    (G : SimpleGraph V) (root : V) (f : Fin k ↪ V) (c : Fin k)
    (hout : ∀ i, f i ≠ root)
    (hpattern : ∀ i j, G.Adj (f i) (f j) ↔ (SimpleGraph.starGraph c).Adj i j)
    (hroot : ∀ i, G.Adj root (f i) ↔ i = c) :
    Regularity.InducedEmbeds (inducedStar k) G := by
  have hnot : root ∉ Set.range f := by rintro ⟨i, hi⟩; exact hout i hi
  let e := Fin.Embedding.snoc f hnot
  have hlast (i : Fin k) : Fin.last k ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
  have he (a b : Fin (k + 1)) :
      G.Adj (e a) (e b) ↔ (SimpleGraph.starGraph c.castSucc).Adj a b := by
    refine Fin.lastCases ?_ (fun i ↦ ?_) a
    · refine Fin.lastCases ?_ (fun j ↦ ?_) b
      · simp [e, Fin.Embedding.snoc]
      · simpa [e, Fin.Embedding.snoc, SimpleGraph.starGraph_adj, hlast] using hroot j
    · refine Fin.lastCases ?_ (fun j ↦ ?_) b
      · rw [G.adj_comm]
        simpa [e, Fin.Embedding.snoc, SimpleGraph.starGraph_adj, hlast] using hroot i
      · simpa [e, Fin.Embedding.snoc, SimpleGraph.starGraph_adj] using hpattern i j
  let p : Equiv.Perm (Fin (k + 1)) := Equiv.swap 0 c.castSucc
  have hp : p 0 = c.castSucc := by simp [p]
  refine ⟨{
    toFun := fun a ↦ e (p a)
    inj' := e.injective.comp p.injective
    map_rel_iff' := ?_ }⟩
  intro a b
  change G.Adj (e (p a)) (e (p b)) ↔ (inducedStar k).Adj a b
  rw [he, SimpleGraph.starGraph_adj, inducedStar_adj, ← hp]
  simp only [p.injective.eq_iff, ne_eq]

/-- A hypothetical `k` non-low visible parts supply disjoint equal-sized
neighbor roles, all avoiding the prescribed center. This is only finite
selection; the independent transversal is proved by the local counting
argument, not by an unproved density-to-independence implication. -/
theorem subcritical_exists_nonlow_neighbor_roles
    {R₀ : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
    {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
    {omega eta theta alpha delta epsilon : ℝ}
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (homega : omega ≤ 1) (halpha : 0 < alpha)
    (hscale : 8 ≤ alpha * theta * n) (root : Fin n)
    (hcard : k ≤ (subcriticalNonlowVisibleParts G D alpha theta root).card) :
    ∃ (parent : Fin k ↪ D.PartIndex) (S : Fin k → Finset (Fin n)),
      (∀ a, parent a ∈ D.visiblePartIndices theta) ∧
      (∀ a, S a ⊆ D.part (parent a)) ∧
      (∀ a, (S a).card = subcriticalRoleSize alpha theta n) ∧
      (Pairwise fun a b ↦ Disjoint (S a) (S b)) ∧
      (∀ a, root ∉ S a) ∧
      (∀ a x, x ∈ S a → G.Adj root x) := by
  classical
  obtain ⟨parent, hparent⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin k) (by simpa only [Fintype.card_fin] using hcard)
  have hnonlow (a : Fin k) : parent a ∈
      subcriticalNonlowVisibleParts G D alpha theta root :=
    hparent ⟨a, rfl⟩
  have hvisible (a : Fin k) : parent a ∈ D.visiblePartIndices theta :=
    ((mem_subcriticalNonlowVisibleParts G D alpha theta root (parent a)).mp (hnonlow a)).1
  have hdegree (a : Fin k) : alpha * (D.part (parent a)).card ≤
      (degreeInFinset G root (D.part (parent a)) : ℝ) :=
    ((mem_subcriticalNonlowVisibleParts G D alpha theta root (parent a)).mp (hnonlow a)).2
  choose S hS hsize hroot hadj using fun a ↦
    subcritical_exists_neighbor_roleSet G root (D.part (parent a)) halpha
      (R.visible_part_card_ge_half homega (parent a) (hvisible a)) hscale (hdegree a)
  refine ⟨parent, S, hvisible, hS, hsize, ?_, hroot, hadj⟩
  intro a b hab
  exact (D.part_disjoint (parent.injective.ne hab)).mono (hS a) (hS b)

end InducedStars
