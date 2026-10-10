import InducedStars.ColoredGraph
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic

open Finset

/-!
# Finite colored extremal theory

This file starts the finite colored extremal theory with the forbidden
patterns and the cloning operation. The weighted objective, twins, and the
`k`-th order Mantel inequality are developed later in this file.
-/

namespace InducedStars

/-- The paper's parameter `Δ = k - 2`. -/
def delta (k : ℕ) : ℕ := k - 2

namespace EdgeColor

/-- The colors allowed between the leaves of a forbidden pattern. -/
def IsLeafColor (c : EdgeColor) : Prop := c = .red ∨ c = .green

@[simp]
theorem isLeafColor_iff_ne_blue (c : EdgeColor) : c.IsLeafColor ↔ c ≠ .blue := by
  cases c <;> simp [IsLeafColor]

end EdgeColor

namespace ColoredGraph

variable {V W : Type*}
variable [DecidableEq V]

/-! ## Forbidden patterns -/

/--
The predicate defining a forbidden red--green--blue pattern on its entire
vertex type: there is a center whose incident edges are red, while every edge
between distinct noncenter vertices is red or green.

Paper: Definition `dfn:Fk-free-cols` (the predicate defining `ℑ_k`).
-/
def IsForbiddenPattern (C : ColoredGraph V) : Prop :=
  ∃ center : V,
    (∀ x : V, x ≠ center → C.color center x = .red) ∧
      ∀ x y : V, x ≠ center → y ≠ center → x ≠ y →
        (C.color x y).IsLeafColor

/-- Every edge of a forbidden pattern between distinct vertices is nonblue. -/
theorem IsForbiddenPattern.color_ne_blue {C : ColoredGraph V}
    (hC : C.IsForbiddenPattern) {x y : V} (hxy : x ≠ y) : C.color x y ≠ .blue := by
  rcases hC with ⟨center, hred, hleaf⟩
  by_cases hx : x = center
  · subst x
    rw [hred y hxy.symm]
    decide
  · by_cases hy : y = center
    · subst y
      rw [C.color_comm x center, hred x hx]
      decide
    · exact (EdgeColor.isLeafColor_iff_ne_blue _).mp (hleaf x y hx hy hxy)

/-- The paper's family `ℑ_k` of forbidden colorings of `K_k`. -/
def Fk (k : ℕ) : Set (ColoredGraph (Fin k)) :=
  {C | C.IsForbiddenPattern}

@[simp]
theorem mem_Fk_iff {k : ℕ} {C : ColoredGraph (Fin k)} : C ∈ Fk k ↔ C.IsForbiddenPattern :=
  Iff.rfl

/-- A coloring contains a forbidden `k`-vertex pattern via an injective vertex map. -/
def ContainsFk (k : ℕ) (C : ColoredGraph V) : Prop :=
  ∃ f : Fin k ↪ V, C.pullback f ∈ Fk k

/-- A coloring is `ℑ_k`-free when no injective `k`-vertex pullback belongs to `ℑ_k`. -/
def FkFree (k : ℕ) (C : ColoredGraph V) : Prop :=
  ¬ C.ContainsFk k

/-- The paper's family `ℂ_k(n)` of `ℑ_k`-free colorings of `K_n`.

Paper: Definition `dfn:Fk-free-cols`.
-/
def Ck (k n : ℕ) : Set (ColoredGraph (Fin n)) :=
  {C | C.FkFree k}

@[simp]
theorem mem_Ck_iff {k n : ℕ} {C : ColoredGraph (Fin n)} : C ∈ Ck k n ↔ C.FkFree k :=
  Iff.rfl

/-- Forbidden-pattern-freeness is hereditary under injective pullback. -/
theorem pullback_preserves_fkFree [DecidableEq W] {k : ℕ}
    {C : ColoredGraph V} (hC : C.FkFree k) (f : W ↪ V) :
    (C.pullback f).FkFree k := by
  intro hcontains
  rcases hcontains with ⟨g, hg⟩
  apply hC
  refine ⟨g.trans f, ?_⟩
  change ((C.pullback f).pullback g).IsForbiddenPattern at hg
  rcases hg with ⟨center, hred, hleaf⟩
  refine ⟨center, ?_, ?_⟩
  · intro x hx
    rw [pullback_color]
    change C.color (f (g center)) (f (g x)) = .red
    simpa only [pullback_color] using hred x hx
  · intro x y hx hy hxy
    rw [pullback_color]
    change (C.color (f (g x)) (f (g y))).IsLeafColor
    simpa only [pullback_color] using hleaf x y hx hy hxy

/-- The canonical injection which enumerates the vertices of a finite set.
Its domain has exactly the cardinality of the set, which makes it suitable
for applying results stated on `Fin m` to an induced coloring. -/
noncomputable def restrictionEmbedding (S : Finset V) : Fin S.card ↪ V where
  toFun i := ((Finset.equivFinOfCardEq (s := S) rfl).symm i : V)
  inj' := by
    intro i j hij
    apply (Finset.equivFinOfCardEq (s := S) rfl).symm.injective
    exact Subtype.ext hij

@[simp]
theorem restrictionEmbedding_mem (S : Finset V) (i : Fin S.card) :
    restrictionEmbedding S i ∈ S :=
  ((Finset.equivFinOfCardEq (s := S) rfl).symm i).property

/-- Every member of `S` occurs in its canonical enumeration. -/
theorem restrictionEmbedding_surjectiveOn (S : Finset V) {x : V} (hx : x ∈ S) :
    ∃ i : Fin S.card, restrictionEmbedding S i = x := by
  let xS : S := ⟨x, hx⟩
  refine ⟨Finset.equivFinOfCardEq (s := S) rfl xS, ?_⟩
  change (((Finset.equivFinOfCardEq (s := S) rfl).symm
    (Finset.equivFinOfCardEq (s := S) rfl xS) : S) : V) = x
  simp [xS]

/-- The coloring induced by `C` on `S`, relabeled on `Fin S.card`. -/
noncomputable def restrictToFin (C : ColoredGraph V) (S : Finset V) :
    ColoredGraph (Fin S.card) :=
  C.pullback (restrictionEmbedding S)

@[simp]
theorem restrictToFin_color (C : ColoredGraph V) (S : Finset V)
    (i j : Fin S.card) :
    (C.restrictToFin S).color i j =
      C.color (restrictionEmbedding S i) (restrictionEmbedding S j) := by
  simp [restrictToFin]

/-- Restricting a coloring to a finite vertex set preserves the number of
edges of each color. -/
theorem edgeCount_restrictToFin [Fintype V] (C : ColoredGraph V)
    (S : Finset V) (c : EdgeColor) :
    (C.restrictToFin S).edgeCount c = C.edgeCountIn c S := by
  classical
  unfold edgeCount edgeCountIn
  apply Finset.card_bij
      (fun e _ ↦ Sym2.map (restrictionEmbedding S) e)
  · intro e he
    induction e using Sym2.inductionOn with
    | _ i j =>
        rw [Sym2.map_mk, C.pair_mem_edgeFinsetIn]
        rw [(C.restrictToFin S).pair_mem_edgeFinset] at he
        exact ⟨(restrictionEmbedding S).injective.ne he.1,
          by simpa using he.2, restrictionEmbedding_mem S i,
          restrictionEmbedding_mem S j⟩
  · intro e₁ _ e₂ _ heq
    exact Sym2.map.injective (restrictionEmbedding S).injective heq
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [C.pair_mem_edgeFinsetIn] at he
        obtain ⟨i, hi⟩ := restrictionEmbedding_surjectiveOn S he.2.2.1
        obtain ⟨j, hj⟩ := restrictionEmbedding_surjectiveOn S he.2.2.2
        refine ⟨s(i, j), ?_, ?_⟩
        · rw [(C.restrictToFin S).pair_mem_edgeFinset]
          refine ⟨?_, ?_⟩
          · intro hij
            apply he.1
            simpa [hi, hj] using congrArg (restrictionEmbedding S) hij
          · simpa [hi, hj] using he.2.1
        · simp [hi, hj]

/-- Restricting an `ℑ_k`-free coloring to a finite set and relabeling it on
`Fin S.card` again gives a member of `ℂ_k(S.card)`. -/
theorem restrictToFin_mem_Ck {k n : ℕ} {C : ColoredGraph (Fin n)}
    (hC : C ∈ Ck k n) (S : Finset (Fin n)) :
    C.restrictToFin S ∈ Ck k S.card :=
  pullback_preserves_fkFree hC (restrictionEmbedding S)

/--
An ambient center together with exactly `k - 1` leaves satisfying the paper's
red-center and nonblue-leaf conditions.
-/
def IsForbiddenConfig (k : ℕ) (C : ColoredGraph V) (center : V) (leaves : Finset V) : Prop :=
  center ∉ leaves ∧
    leaves.card = k - 1 ∧
    (∀ x ∈ leaves, C.color center x = .red) ∧
    ∀ x ∈ leaves, ∀ y ∈ leaves, x ≠ y → (C.color x y).IsLeafColor

/-- A center-plus-leaf configuration produces an injectively embedded forbidden pattern. -/
theorem containsFk_of_forbiddenConfig {k : ℕ} (hk : 1 ≤ k)
    {C : ColoredGraph V} {center : V} {leaves : Finset V}
    (hconfig : IsForbiddenConfig k C center leaves) : C.ContainsFk k := by
  classical
  rcases hconfig with ⟨hcenter, hcard, hred, hleaf⟩
  let S : Finset V := insert center leaves
  have hS : S.card = k := by
    dsimp [S]
    rw [Finset.card_insert_of_notMem hcenter, hcard, Nat.sub_add_cancel hk]
  let e : Fin k ≃ S := (Finset.equivFinOfCardEq hS).symm
  let f : Fin k ↪ V :=
    ⟨fun i ↦ (e i : V), fun _ _ hij ↦ e.injective (Subtype.ext hij)⟩
  let centerIndex : Fin k := e.symm ⟨center, Finset.mem_insert_self center leaves⟩
  have he_center : (e centerIndex : V) = center := by
    simp [centerIndex]
  have hleaf_mem {i : Fin k} (hi : i ≠ centerIndex) : (e i : V) ∈ leaves := by
    have hne : (e i : V) ≠ center := by
      intro hei
      apply hi
      apply e.injective
      apply Subtype.ext
      simpa [he_center] using hei
    have hiS : (e i : V) ∈ insert center leaves := by
      simpa only [S] using (e i).property
    exact (Finset.mem_insert.mp hiS).resolve_left hne
  refine ⟨f, ?_⟩
  change (C.pullback f).IsForbiddenPattern
  refine ⟨centerIndex, ?_, ?_⟩
  · intro i hi
    rw [pullback_color]
    change C.color (e centerIndex : V) (e i : V) = .red
    rw [he_center]
    exact hred _ (hleaf_mem hi)
  · intro i j hi hj hij
    rw [pullback_color]
    change (C.color (e i : V) (e j : V)).IsLeafColor
    apply hleaf _ (hleaf_mem hi) _ (hleaf_mem hj)
    intro heij
    exact hij (e.injective (Subtype.ext heij))

/-- A center-plus-leaf configuration contradicts `ℑ_k`-freeness. -/
theorem not_fkFree_of_forbiddenConfig {k : ℕ} (hk : 1 ≤ k)
    {C : ColoredGraph V} {center : V} {leaves : Finset V}
    (hconfig : IsForbiddenConfig k C center leaves) : ¬ C.FkFree k := by
  intro hfree
  exact hfree (containsFk_of_forbiddenConfig hk hconfig)

/-! ## Green cleaning -/

/-- Recoloring every edge not wholly contained in a retained set green
preserves forbidden-pattern-freeness.  A forbidden pattern in the cleaned
coloring has red center edges, so its center and every leaf lie in the
retained set; all colors of the pattern therefore already occurred in the
original coloring. -/
theorem greenOutside_preserves_fkFree {k : ℕ} (hk : 2 ≤ k)
    {C : ColoredGraph V} (hC : C.FkFree k) (S : Finset V) :
    (C.greenOutside S).FkFree k := by
  intro hcontains
  rcases hcontains with ⟨f, hf⟩
  apply hC
  refine ⟨f, ?_⟩
  change (C.pullback f).IsForbiddenPattern
  change ((C.greenOutside S).pullback f).IsForbiddenPattern at hf
  rcases hf with ⟨center, hred, hleaf⟩
  have hredOriginal (x : Fin k) (hx : x ≠ center) :
      f x ∈ S ∧ C.color (f center) (f x) = .red := by
    have hclean : (C.greenOutside S).color (f center) (f x) = .red := by
      simpa using hred x hx
    rw [C.greenOutside_color_of_ne S (f.injective.ne hx.symm)] at hclean
    by_cases hmem : f center ∈ S ∧ f x ∈ S
    · simp only [hmem, if_true] at hclean
      exact ⟨hmem.2, hclean⟩
    · simp [hmem] at hclean
  refine ⟨center, ?_, ?_⟩
  · intro x hx
    rw [pullback_color]
    exact (hredOriginal x hx).2
  · intro x y hx hy hxy
    rw [pullback_color]
    have hclean := hleaf x y hx hy hxy
    rw [pullback_color,
      C.greenOutside_color_of_mem S (hredOriginal x hx).1
        (hredOriginal y hy).1] at hclean
    exact hclean

/-- The cleaning operation specialized to membership in `ℂ_k(n)`. -/
theorem greenOutside_mem_Ck {k n : ℕ} (hk : 2 ≤ k)
    {C : ColoredGraph (Fin n)} (hC : C ∈ Ck k n) (S : Finset (Fin n)) :
    C.greenOutside S ∈ Ck k n :=
  greenOutside_preserves_fkFree hk hC S

/-! ## Cloning -/

/-- The representative of a vertex after cloning every vertex of `U` from `v`. -/
def cloneRep (v : V) (U : Finset V) (x : V) : V :=
  if x ∈ U then v else x

@[simp]
theorem cloneRep_source (v : V) (U : Finset V) : cloneRep v U v = v := by
  simp [cloneRep]

@[simp]
theorem cloneRep_of_mem {v x : V} {U : Finset V} (hx : x ∈ U) : cloneRep v U x = v := by
  simp [cloneRep, hx]

@[simp]
theorem cloneRep_of_not_mem {v x : V} {U : Finset V} (hx : x ∉ U) : cloneRep v U x = x := by
  simp [cloneRep, hx]

theorem cloneRep_eq_source_of_mem_insert {v x : V} {U : Finset V}
    (hx : x ∈ insert v U) : cloneRep v U x = v := by
  rcases Finset.mem_insert.mp hx with hxv | hxU
  · subst x
    simp
  · exact cloneRep_of_mem hxU

theorem cloneRep_eq_self_of_not_mem_insert {v x : V} {U : Finset V}
    (hx : x ∉ insert v U) : cloneRep v U x = x := by
  exact cloneRep_of_not_mem (fun hxU ↦ hx (Finset.mem_insert_of_mem hxU))

/--
Clone every vertex of `U` from the source `v`: make `insert v U` a blue
clique, copy the colors from `v` to edges leaving `U`, and leave all other
edges unchanged. The paper uses this only under the hypothesis `v ∉ U`.

Paper: Definition `dfn:cloning`.
-/
def clone (C : ColoredGraph V) (v : V) (U : Finset V) : ColoredGraph V :=
  SimpleGraph.EdgeLabeling.mk
    (fun x y _ ↦
      if x ∈ insert v U ∧ y ∈ insert v U then .blue
      else C.color (cloneRep v U x) (cloneRep v U y))
    (by
      intro x y _
      by_cases hxy : x ∈ insert v U ∧ y ∈ insert v U
      · simp [hxy]
      · have hyx : ¬ (y ∈ insert v U ∧ x ∈ insert v U) := by
          simpa [and_comm] using hxy
        simp only [hxy, hyx, ite_false]
        exact C.color_comm _ _)

/-- The total color formula for cloning. -/
theorem clone_color (C : ColoredGraph V) (v : V) (U : Finset V) (x y : V) :
    (C.clone v U).color x y =
      if x ∈ insert v U ∧ y ∈ insert v U then .blue
      else C.color (cloneRep v U x) (cloneRep v U y) := by
  by_cases hxy : x = y
  · subst y
    simp
  · rw [color_eq_get _ hxy]
    rfl

/-- Cloning is equivalently the pullback of the total color function along
`cloneRep`; the diagonal-blue convention supplies the colors inside the cloned
class. -/
theorem clone_color_eq_color_cloneRep (C : ColoredGraph V) (v : V) (U : Finset V)
    (x y : V) :
    (C.clone v U).color x y = C.color (cloneRep v U x) (cloneRep v U y) := by
  rw [clone_color]
  split_ifs with h
  · rw [cloneRep_eq_source_of_mem_insert h.1,
      cloneRep_eq_source_of_mem_insert h.2]
    simp
  · rfl

/-- Every edge within the cloned class is blue. -/
@[simp]
theorem clone_color_of_mem_insert {C : ColoredGraph V} {v x y : V} {U : Finset V}
    (hx : x ∈ insert v U) (hy : y ∈ insert v U) :
    (C.clone v U).color x y = .blue := by
  rw [clone_color]
  simp [hx, hy]

/-- A cloned vertex copies the source color on every edge leaving the cloned class. -/
@[simp]
theorem clone_color_of_mem_of_not_mem_insert {C : ColoredGraph V} {v x y : V} {U : Finset V}
    (hx : x ∈ U) (hy : y ∉ insert v U) :
    (C.clone v U).color x y = C.color v y := by
  have hyU : y ∉ U := fun hyU ↦ hy (Finset.mem_insert_of_mem hyU)
  rw [clone_color]
  simp [hx, hy, hyU, cloneRep]

/-- Source edges leaving the cloned class retain their old colors. -/
@[simp]
theorem clone_color_source_of_not_mem_insert {C : ColoredGraph V} {v y : V} {U : Finset V}
    (hy : y ∉ insert v U) :
    (C.clone v U).color v y = C.color v y := by
  have hyU : y ∉ U := fun hyU ↦ hy (Finset.mem_insert_of_mem hyU)
  rw [clone_color]
  simp [hy, hyU]

/-- Edges with both endpoints outside the cloned class are unchanged. -/
@[simp]
theorem clone_color_of_not_mem_insert {C : ColoredGraph V} {v x y : V} {U : Finset V}
    (hx : x ∉ insert v U) (hy : y ∉ insert v U) :
    (C.clone v U).color x y = C.color x y := by
  have hxU : x ∉ U := fun hxU ↦ hx (Finset.mem_insert_of_mem hxU)
  have hyU : y ∉ U := fun hyU ↦ hy (Finset.mem_insert_of_mem hyU)
  rw [clone_color]
  simp [hx, hy, hxU, hyU, cloneRep]

/-- Clone the single target vertex `x` from the source vertex `v`. -/
abbrev cloneVertex (C : ColoredGraph V) (x v : V) : ColoredGraph V :=
  C.clone v {x}

@[simp]
theorem cloneVertex_color_target_source (C : ColoredGraph V) (x v : V) :
    (C.cloneVertex x v).color x v = .blue := by
  apply clone_color_of_mem_insert
  · simp
  · simp

@[simp]
theorem cloneVertex_color_target {C : ColoredGraph V} {x v y : V}
    (hyx : y ≠ x) (hyv : y ≠ v) :
    (C.cloneVertex x v).color x y = C.color v y := by
  apply clone_color_of_mem_of_not_mem_insert
  · simp
  · simp [hyx, hyv]

@[simp]
theorem cloneVertex_color_of_ne_target {C : ColoredGraph V} {x v a b : V}
    (ha : a ≠ x) (hb : b ≠ x) :
    (C.cloneVertex x v).color a b = C.color a b := by
  rw [clone_color]
  simp only [Finset.mem_insert, Finset.mem_singleton, ha, hb, or_false, cloneRep]
  split <;> simp_all

/-! ## Preservation of forbidden-pattern-freeness -/

/--
Cloning preserves `ℑ_k`-freeness.

Paper: Fact `fact:cloning-keeps-ckn`.
-/
theorem clone_preserves_fkFree {k : ℕ} {C : ColoredGraph V} (hC : C.FkFree k)
    {v : V} {U : Finset V} (_hv : v ∉ U) : (C.clone v U).FkFree k := by
  intro hcontains
  rcases hcontains with ⟨f, hf⟩
  have hforbidden : ((C.clone v U).pullback f).IsForbiddenPattern := by
    simpa only [mem_Fk_iff] using hf
  have hnonblue (i j : Fin k) (hij : i ≠ j) :
      (C.clone v U).color (f i) (f j) ≠ .blue := by
    simpa using hforbidden.color_ne_blue hij
  have hclass_unique {i j : Fin k} (hi : f i ∈ insert v U) (hj : f j ∈ insert v U) :
      i = j := by
    by_contra hij
    exact hnonblue i j hij (clone_color_of_mem_insert hi hj)
  let g : Fin k → V := fun i ↦ cloneRep v U (f i)
  have hg : Function.Injective g := by
    intro i j hij
    by_cases hi : f i ∈ insert v U
    · by_cases hj : f j ∈ insert v U
      · exact hclass_unique hi hj
      · have hgi : g i = v := cloneRep_eq_source_of_mem_insert hi
        have hgj : g j = f j := cloneRep_eq_self_of_not_mem_insert hj
        have hvfj : v = f j := by simpa only [hgi, hgj] using hij
        exact (hj (by simp [← hvfj])).elim
    · by_cases hj : f j ∈ insert v U
      · have hgi : g i = f i := cloneRep_eq_self_of_not_mem_insert hi
        have hgj : g j = v := cloneRep_eq_source_of_mem_insert hj
        have hfiv : f i = v := by simpa only [hgi, hgj] using hij
        exact (hi (by simp [hfiv])).elim
      · apply f.injective
        have hgi : g i = f i := cloneRep_eq_self_of_not_mem_insert hi
        have hgj : g j = f j := cloneRep_eq_self_of_not_mem_insert hj
        simpa only [hgi, hgj] using hij
  let gEmbedding : Fin k ↪ V := ⟨g, hg⟩
  have hcolor (i j : Fin k) (hij : i ≠ j) :
      C.color (g i) (g j) = (C.clone v U).color (f i) (f j) := by
    have hnotboth : ¬ (f i ∈ insert v U ∧ f j ∈ insert v U) := by
      rintro ⟨hi, hj⟩
      exact hij (hclass_unique hi hj)
    rw [clone_color]
    split
    · rename_i hboth
      exact (hnotboth hboth).elim
    · rfl
  apply hC
  refine ⟨gEmbedding, ?_⟩
  change (C.pullback gEmbedding).IsForbiddenPattern
  rcases hforbidden with ⟨center, hred, hleaf⟩
  refine ⟨center, ?_, ?_⟩
  · intro x hx
    rw [pullback_color]
    change C.color (g center) (g x) = .red
    rw [hcolor center x hx.symm]
    simpa using hred x hx
  · intro x y hx hy hxy
    rw [pullback_color]
    change (C.color (g x) (g y)).IsLeafColor
    rw [hcolor x y hxy]
    simpa using hleaf x y hx hy hxy

/-- The paper's cloning fact specialized to membership in `ℂ_k(n)`. -/
theorem clone_mem_Ck {k n : ℕ} {C : ColoredGraph (Fin n)} (hC : C ∈ Ck k n)
    {v : Fin n} {U : Finset (Fin n)} (hv : v ∉ U) : C.clone v U ∈ Ck k n :=
  clone_preserves_fkFree hC hv

/-! ## The weighted objective -/

section WeightedObjective

variable [Fintype V]

/-- The paper's integer-valued objective
`Phi(C) = e_red(C) - (k - 2) e_blue(C)`.

Paper: notation preceding Lemma `lemma:kthOrderMantel`.
-/
def objective (k : ℕ) (C : ColoredGraph V) : ℤ :=
  (C.redEdgeCount : ℤ) - (delta k : ℤ) * (C.blueEdgeCount : ℤ)

/-- The weighted objective restricted to pairs with both endpoints in `S`.
This is the exact objective of the coloring obtained by recoloring every
other edge green. -/
def objectiveIn (k : ℕ) (C : ColoredGraph V) (S : Finset V) : ℤ :=
  (C.redEdgeCountIn S : ℤ) -
    (delta k : ℤ) * (C.blueEdgeCountIn S : ℤ)

/-- Cleaning preserves the restricted objective on every subset of the
retained set. -/
theorem objectiveIn_greenOutside_of_subset (k : ℕ) (C : ColoredGraph V)
    (retained : Finset V) {S : Finset V} (hS : S ⊆ retained) :
    objectiveIn k (C.greenOutside retained) S = objectiveIn k C S := by
  unfold objectiveIn
  change
    ((C.greenOutside retained).edgeCountIn .red S : ℤ) -
        (delta k : ℤ) *
          ((C.greenOutside retained).edgeCountIn .blue S : ℤ) =
      (C.edgeCountIn .red S : ℤ) -
        (delta k : ℤ) * (C.edgeCountIn .blue S : ℤ)
  rw [C.greenOutside_edgeCountIn_of_subset retained .red hS,
    C.greenOutside_edgeCountIn_of_subset retained .blue hS]

/-- The weighted contribution of edges crossing from `S` to `T`.  For
disjoint sets each unordered crossing edge is counted once. -/
def objectiveBetween (k : ℕ) (C : ColoredGraph V)
    (S T : Finset V) : ℤ :=
  (C.colorEdgeCountBetween .red S T : ℤ) -
    (delta k : ℤ) * (C.colorEdgeCountBetween .blue S T : ℤ)

/-- The restricted objective of a disjoint union is the sum of its two
internal objectives and its crossing contribution. -/
theorem objectiveIn_union_of_disjoint (k : ℕ) (C : ColoredGraph V)
    {S T : Finset V} (hST : Disjoint S T) :
    objectiveIn k C (S ∪ T) =
      objectiveIn k C S + objectiveBetween k C S T + objectiveIn k C T := by
  have hr := congrArg (fun n : ℕ ↦ (n : ℤ))
    (C.edgeCountIn_union_of_disjoint .red hST)
  have hb := congrArg (fun n : ℕ ↦ (n : ℤ))
    (C.edgeCountIn_union_of_disjoint .blue hST)
  push_cast at hr hb
  unfold objectiveIn objectiveBetween
  rw [hr, hb]
  ring

/-- The paper's weighted degree
`D(v) = d_red(v) - (k - 2) d_blue(v)`.

Paper: notation preceding Lemma `lemma:kthOrderMantel`.
-/
def weightedDegree (k : ℕ) (C : ColoredGraph V) (v : V) : ℤ :=
  (C.redDegree v : ℤ) - (delta k : ℤ) * (C.blueDegree v : ℤ)

/-- The weighted degree restricted to a vertex set,
`D(v, U) = d_red(v, U) - (k - 2) d_blue(v, U)`.

Paper: notation preceding Lemma `lemma:kthOrderMantel`.
-/
def weightedDegreeIn (k : ℕ) (C : ColoredGraph V) (v : V) (U : Finset V) : ℤ :=
  (C.redDegreeIn v U : ℤ) - (delta k : ℤ) * (C.blueDegreeIn v U : ℤ)

/-- At a retained vertex, weighted degree in the cleaned coloring is exactly
the original weighted degree restricted to the retained set. -/
@[simp]
theorem weightedDegree_greenOutside_of_mem (k : ℕ) (C : ColoredGraph V)
    (S : Finset V) {v : V} (hv : v ∈ S) :
    weightedDegree k (C.greenOutside S) v = weightedDegreeIn k C v S := by
  simp only [weightedDegree, weightedDegreeIn,
    C.greenOutside_redDegree_of_mem S hv,
    C.greenOutside_blueDegree_of_mem S hv]

/-- Cleaning is exactly restriction of the weighted objective to the
retained set. -/
@[simp]
theorem objective_greenOutside (k : ℕ) (C : ColoredGraph V) (S : Finset V) :
    objective k (C.greenOutside S) = objectiveIn k C S := by
  simp only [objective, objectiveIn,
    C.greenOutside_edgeCount_of_ne_green S (c := .red) (by decide),
    C.greenOutside_edgeCount_of_ne_green S (c := .blue) (by decide)]

/-- Recoloring outside `S` green loses at most one unit of objective per red
edge that is removed.  Charging such an edge to an endpoint in `Sᶜ` gives
the coarse loss bound `|Sᶜ| |V|`. -/
theorem objective_sub_compl_mul_card_le_objective_greenOutside
    (k : ℕ) (C : ColoredGraph V) (S : Finset V) :
    objective k C -
        (((Finset.univ \ S).card * Fintype.card V : ℕ) : ℤ) ≤
      objective k (C.greenOutside S) := by
  have hrNat := C.edgeCount_le_edgeCountIn_add_compl_mul_card .red S
  have hbNat := C.edgeCountIn_le_edgeCount .blue S
  have hr : (C.redEdgeCount : ℤ) ≤
      (C.redEdgeCountIn S : ℤ) +
        (((Finset.univ \ S).card * Fintype.card V : ℕ) : ℤ) := by
    exact_mod_cast hrNat
  have hb : (C.blueEdgeCountIn S : ℤ) ≤ (C.blueEdgeCount : ℤ) := by
    exact_mod_cast hbNat
  have hdelta : (0 : ℤ) ≤ (delta k : ℤ) := by positivity
  have hblue := mul_le_mul_of_nonneg_left hb hdelta
  rw [objective_greenOutside]
  unfold objective objectiveIn
  omega

/-- The weighted handshake identity `sum_v D(v) = 2 Phi(C)`.

Paper: the displayed identity preceding Definition `dfn:cloning`.
-/
theorem sum_weightedDegree_eq_two_mul_objective (k : ℕ) (C : ColoredGraph V) :
    ∑ v, weightedDegree k C v = 2 * objective k C := by
  have hr := congrArg (fun n : ℕ ↦ (n : ℤ))
    (C.sum_degree_eq_two_mul_edgeCount .red)
  have hb := congrArg (fun n : ℕ ↦ (n : ℤ))
    (C.sum_degree_eq_two_mul_edgeCount .blue)
  push_cast at hr hb
  simp only [weightedDegree, objective, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, hr, hb]
  ring

end WeightedObjective

/-! ## Singleton cloning and color graphs -/

/-- Cloning `x` from `y` replaces `x` by `y` in every nonblue color graph.

This is the graph-level bookkeeping behind the singleton-cloning identities in
the proof of Lemma `lemma:kthOrderMantel`.
-/
theorem colorGraph_cloneVertex_of_ne_blue (C : ColoredGraph V) {x y : V}
    (hxy : x ≠ y) {c : EdgeColor} (hc : c ≠ .blue) :
    (C.cloneVertex x y).colorGraph c = (C.colorGraph c).replaceVertex y x := by
  ext a b
  by_cases ha : a = x
  · subst a
    by_cases hb : b = x
    · subst b
      simp
    · rw [colorGraph_adj,
        (C.colorGraph c).adj_replaceVertex_iff_of_ne_right y hb,
        colorGraph_adj]
      by_cases hby : b = y
      · subst b
        have hcolor : (C.cloneVertex x y).color x y = .blue :=
          C.cloneVertex_color_target_source x y
        rw [hcolor]
        simp [hc, hxy, ne_comm]
      · have hcolor := C.cloneVertex_color_target (x := x) (v := y)
          (y := b) hb hby
        rw [hcolor]
        have hxb : x ≠ b := Ne.symm hb
        have hyb : y ≠ b := Ne.symm hby
        simp [hxb, hyb]
  · by_cases hb : b = x
    · subst b
      rw [colorGraph_adj]
      have hreplace :
          ((C.colorGraph c).replaceVertex y x).Adj a x ↔
            (C.colorGraph c).Adj a y := by
        rw [SimpleGraph.adj_comm,
          (C.colorGraph c).adj_replaceVertex_iff_of_ne_right y ha,
          SimpleGraph.adj_comm]
      rw [hreplace, colorGraph_adj]
      by_cases hay : a = y
      · subst a
        have hcolor : (C.cloneVertex x y).color y x = .blue := by
          rw [(C.cloneVertex x y).color_comm]
          exact C.cloneVertex_color_target_source x y
        rw [hcolor]
        simp [hc, hxy, ne_comm]
      · have hcolor : (C.cloneVertex x y).color a x = C.color a y := by
          calc
            (C.cloneVertex x y).color a x = (C.cloneVertex x y).color x a :=
              (C.cloneVertex x y).color_comm a x
            _ = C.color y a := C.cloneVertex_color_target ha hay
            _ = C.color a y := C.color_comm y a
        rw [hcolor]
        simp [ha, hay]
    · rw [colorGraph_adj,
        (C.colorGraph c).adj_replaceVertex_iff_of_ne y ha hb,
        colorGraph_adj]
      have hcolor := C.cloneVertex_color_of_ne_target (x := x) (v := y) ha hb
      rw [hcolor]

/-- Cloning `x` from `y` replaces `x` by `y` in the blue graph and then adds
the blue edge joining source and target.

This is the blue graph counterpart of `colorGraph_cloneVertex_of_ne_blue`.
-/
theorem blueGraph_cloneVertex (C : ColoredGraph V) {x y : V} (hxy : x ≠ y) :
    (C.cloneVertex x y).blueGraph =
      C.blueGraph.replaceVertex y x ⊔ SimpleGraph.edge y x := by
  ext a b
  by_cases ha : a = x
  · subst a
    by_cases hb : b = x
    · subst b
      simp
    · rw [colorGraph_adj, SimpleGraph.sup_adj,
        C.blueGraph.adj_replaceVertex_iff_of_ne_right y hb,
        colorGraph_adj, SimpleGraph.edge_adj]
      by_cases hby : b = y
      · subst b
        have hcolor : (C.cloneVertex x y).color x y = .blue :=
          C.cloneVertex_color_target_source x y
        rw [hcolor]
        simp [hxy]
      · have hcolor := C.cloneVertex_color_target (x := x) (v := y)
          (y := b) hb hby
        rw [hcolor]
        have hxb : x ≠ b := Ne.symm hb
        have hyb : y ≠ b := Ne.symm hby
        simp [hxb, hyb, hxy, hb, hby]
  · by_cases hb : b = x
    · subst b
      rw [colorGraph_adj, SimpleGraph.sup_adj]
      have hreplace :
          (C.blueGraph.replaceVertex y x).Adj a x ↔ C.blueGraph.Adj a y := by
        rw [SimpleGraph.adj_comm,
          C.blueGraph.adj_replaceVertex_iff_of_ne_right y ha,
          SimpleGraph.adj_comm]
      rw [hreplace, colorGraph_adj, SimpleGraph.edge_adj]
      by_cases hay : a = y
      · subst a
        have hcolor : (C.cloneVertex x y).color y x = .blue := by
          rw [(C.cloneVertex x y).color_comm]
          exact C.cloneVertex_color_target_source x y
        rw [hcolor]
        simp [hxy, ne_comm]
      · have hcolor : (C.cloneVertex x y).color a x = C.color a y := by
          calc
            (C.cloneVertex x y).color a x = (C.cloneVertex x y).color x a :=
              (C.cloneVertex x y).color_comm a x
            _ = C.color y a := C.cloneVertex_color_target ha hay
            _ = C.color a y := C.color_comm y a
        rw [hcolor]
        simp [ha, hay]
    · rw [colorGraph_adj, SimpleGraph.sup_adj,
        C.blueGraph.adj_replaceVertex_iff_of_ne y ha hb,
        colorGraph_adj, SimpleGraph.edge_adj]
      have hcolor := C.cloneVertex_color_of_ne_target (x := x) (v := y) ha hb
      rw [hcolor]
      simp [ha, hb]

private theorem card_edgeFinset_eq_of_graph_eq {X : Type*}
    (G H : SimpleGraph X) [Fintype G.edgeSet] [Fintype H.edgeSet] (h : G = H) :
    #G.edgeFinset = #H.edgeFinset := by
  apply congrArg Finset.card
  ext e
  simp [h]

section FiniteCloneCounts

variable [Fintype V]

private theorem card_replaceVertex_of_not_adj_add_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : V} (hn : ¬ G.Adj s t) :
    #(G.replaceVertex s t).edgeFinset + G.degree t =
      #G.edgeFinset + G.degree s := by
  have hcard := G.card_edgeFinset_replaceVertex_of_not_adj hn
  have hle := G.degree_le_card_edgeFinset t
  omega

private theorem card_replaceVertex_sup_edge_of_not_adj_add_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : V} (hn : ¬ G.Adj s t)
    (hst : s ≠ t) :
    #((G.replaceVertex s t) ⊔ SimpleGraph.edge s t).edgeFinset + G.degree t =
      #G.edgeFinset + G.degree s + 1 := by
  have hreplace := G.card_edgeFinset_replaceVertex_of_not_adj hn
  have hadd := (G.replaceVertex s t).card_edgeFinset_sup_edge
    (G.not_adj_replaceVertex_same s t) hst
  have hle := G.degree_le_card_edgeFinset t
  omega

private theorem card_replaceVertex_sup_edge_of_adj_add_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : V} (ha : G.Adj s t) :
    #((G.replaceVertex s t) ⊔ SimpleGraph.edge s t).edgeFinset + G.degree t =
      #G.edgeFinset + G.degree s := by
  have hst : s ≠ t := ha.ne
  have hreplace := G.card_edgeFinset_replaceVertex_of_adj ha
  have hadd := (G.replaceVertex s t).card_edgeFinset_sup_edge
    (G.not_adj_replaceVertex_same s t) hst
  have hle := G.degree_le_card_edgeFinset t
  have hspos : 0 < G.degree s := ha.degree_pos_left
  omega

/-- Red edge-count bookkeeping for cloning the target `x` from the source `y`
along a blue edge. -/
theorem redEdgeCount_cloneVertex_add_degree (C : ColoredGraph V) {x y : V}
    (hxy : x ≠ y) (hblue : C.color x y = .blue) :
    (C.cloneVertex x y).redEdgeCount + C.redDegree x =
      C.redEdgeCount + C.redDegree y := by
  have hn : ¬ C.redGraph.Adj y x := by
    rw [colorGraph_adj]
    simp [show C.color y x = .blue by rw [C.color_comm]; exact hblue]
  have h := card_replaceVertex_of_not_adj_add_degree C.redGraph hn
  change #((C.cloneVertex x y).redGraph).edgeFinset + C.redGraph.degree x =
    #C.redGraph.edgeFinset + C.redGraph.degree y
  have hg : (C.cloneVertex x y).redGraph = C.redGraph.replaceVertex y x :=
    colorGraph_cloneVertex_of_ne_blue C hxy (by decide : EdgeColor.red ≠ .blue)
  have hcard := card_edgeFinset_eq_of_graph_eq _ _ hg
  rw [hcard]
  exact h

/-- Blue edge-count bookkeeping for cloning the target `x` from the source `y`
along a blue edge. -/
theorem blueEdgeCount_cloneVertex_add_degree (C : ColoredGraph V) {x y : V}
    (hxy : x ≠ y) (hblue : C.color x y = .blue) :
    (C.cloneVertex x y).blueEdgeCount + C.blueDegree x =
      C.blueEdgeCount + C.blueDegree y := by
  have ha : C.blueGraph.Adj y x := by
    rw [colorGraph_adj]
    exact ⟨hxy.symm, by rw [C.color_comm]; exact hblue⟩
  have h := card_replaceVertex_sup_edge_of_adj_add_degree C.blueGraph ha
  change #((C.cloneVertex x y).blueGraph).edgeFinset + C.blueGraph.degree x =
    #C.blueGraph.edgeFinset + C.blueGraph.degree y
  have hg : (C.cloneVertex x y).blueGraph =
      C.blueGraph.replaceVertex y x ⊔ SimpleGraph.edge y x :=
    blueGraph_cloneVertex C hxy
  have hcard := card_edgeFinset_eq_of_graph_eq _ _ hg
  rw [hcard]
  exact h

/-- Exact objective change under singleton cloning along a blue edge:
`Phi(C^{x <- y}) - Phi(C) = D_C(y) - D_C(x)`.

Paper: the first display in the proof of Lemma `lemma:kthOrderMantel`.
-/
theorem objective_cloneVertex_sub (k : ℕ) (C : ColoredGraph V) {x y : V}
    (hxy : x ≠ y) (hblue : C.color x y = .blue) :
    objective k (C.cloneVertex x y) - objective k C =
      weightedDegree k C y - weightedDegree k C x := by
  have hr := redEdgeCount_cloneVertex_add_degree C hxy hblue
  have hb := blueEdgeCount_cloneVertex_add_degree C hxy hblue
  have hrz := congrArg (fun n : ℕ ↦ (n : ℤ)) hr
  have hbz := congrArg (fun n : ℕ ↦ (n : ℤ)) hb
  push_cast at hrz hbz
  unfold objective weightedDegree
  linear_combination hrz - (delta k : ℤ) * hbz

/-- A color-independent lower bound for the objective change under singleton
cloning.  The loss `delta k + 1` is the largest possible loss on the edge
joining source and target. -/
theorem objective_cloneVertex_sub_lower_bound (k : ℕ) (C : ColoredGraph V)
    {x y : V} (hxy : x ≠ y) :
    weightedDegree k C y - weightedDegree k C x - ((delta k : ℤ) + 1) ≤
      objective k (C.cloneVertex x y) - objective k C := by
  cases hcolor : C.color x y with
  | blue =>
      have h := objective_cloneVertex_sub k C hxy hcolor
      omega
  | red =>
      have hred : C.redGraph.Adj y x := by
        rw [colorGraph_adj]
        exact ⟨hxy.symm, by rw [C.color_comm]; exact hcolor⟩
      have hnblue : ¬ C.blueGraph.Adj y x := by
        intro h
        have hc := (colorGraph_adj C .blue y x).mp h |>.2
        rw [C.color_comm y x, hcolor] at hc
        contradiction
      have hrreplace := C.redGraph.card_edgeFinset_replaceVertex_of_adj hred
      have hrle := C.redGraph.degree_le_card_edgeFinset x
      have hrpos := hred.degree_pos_left
      have hrbound : C.redGraph.degree x + 1 ≤
          #C.redGraph.edgeFinset + C.redGraph.degree y := by omega
      have hrbound0 : C.redGraph.degree x ≤
          #C.redGraph.edgeFinset + C.redGraph.degree y := by omega
      have hrsub := Nat.sub_add_cancel hrbound0
      have hrinner : 1 ≤ #C.redGraph.edgeFinset + C.redGraph.degree y -
          C.redGraph.degree x := by omega
      have hrsub1 := Nat.sub_add_cancel hrinner
      have hrEq :
          (C.cloneVertex x y).redEdgeCount + C.redDegree x + 1 =
            C.redEdgeCount + C.redDegree y := by
        change #((C.cloneVertex x y).redGraph).edgeFinset + C.redGraph.degree x + 1 =
          #C.redGraph.edgeFinset + C.redGraph.degree y
        have hg := colorGraph_cloneVertex_of_ne_blue C hxy
          (by decide : EdgeColor.red ≠ .blue)
        have hcard := card_edgeFinset_eq_of_graph_eq _ _ hg
        rw [hcard, hrreplace]
        omega
      have hbreplace := C.blueGraph.card_edgeFinset_replaceVertex_of_not_adj hnblue
      have hbadd := (C.blueGraph.replaceVertex y x).card_edgeFinset_sup_edge
        (C.blueGraph.not_adj_replaceVertex_same y x) hxy.symm
      have hble := C.blueGraph.degree_le_card_edgeFinset x
      have hbEq :
          (C.cloneVertex x y).blueEdgeCount + C.blueDegree x =
            C.blueEdgeCount + C.blueDegree y + 1 := by
        change #((C.cloneVertex x y).blueGraph).edgeFinset + C.blueGraph.degree x =
          #C.blueGraph.edgeFinset + C.blueGraph.degree y + 1
        have hg := blueGraph_cloneVertex C hxy
        have hcard := card_edgeFinset_eq_of_graph_eq _ _ hg
        rw [hcard]
        omega
      have hrz := congrArg (fun m : ℕ ↦ (m : ℤ)) hrEq
      have hbz := congrArg (fun m : ℕ ↦ (m : ℤ)) hbEq
      push_cast at hrz hbz
      have heq :
          objective k (C.cloneVertex x y) - objective k C =
            weightedDegree k C y - weightedDegree k C x - ((delta k : ℤ) + 1) := by
        unfold objective weightedDegree
        linear_combination hrz - (delta k : ℤ) * hbz
      exact heq.ge
  | green =>
      have hnred : ¬ C.redGraph.Adj y x := by
        intro h
        have hc := (colorGraph_adj C .red y x).mp h |>.2
        rw [C.color_comm y x, hcolor] at hc
        contradiction
      have hnblue : ¬ C.blueGraph.Adj y x := by
        intro h
        have hc := (colorGraph_adj C .blue y x).mp h |>.2
        rw [C.color_comm y x, hcolor] at hc
        contradiction
      have hrreplace := C.redGraph.card_edgeFinset_replaceVertex_of_not_adj hnred
      have hrle := C.redGraph.degree_le_card_edgeFinset x
      have hrbound : C.redGraph.degree x ≤
          #C.redGraph.edgeFinset + C.redGraph.degree y := by omega
      have hrsub := Nat.sub_add_cancel hrbound
      have hrEq :
          (C.cloneVertex x y).redEdgeCount + C.redDegree x =
            C.redEdgeCount + C.redDegree y := by
        change #((C.cloneVertex x y).redGraph).edgeFinset + C.redGraph.degree x =
          #C.redGraph.edgeFinset + C.redGraph.degree y
        have hg := colorGraph_cloneVertex_of_ne_blue C hxy
          (by decide : EdgeColor.red ≠ .blue)
        have hcard := card_edgeFinset_eq_of_graph_eq _ _ hg
        rw [hcard, hrreplace]
        omega
      have hbreplace := C.blueGraph.card_edgeFinset_replaceVertex_of_not_adj hnblue
      have hbadd := (C.blueGraph.replaceVertex y x).card_edgeFinset_sup_edge
        (C.blueGraph.not_adj_replaceVertex_same y x) hxy.symm
      have hble := C.blueGraph.degree_le_card_edgeFinset x
      have hbEq :
          (C.cloneVertex x y).blueEdgeCount + C.blueDegree x =
            C.blueEdgeCount + C.blueDegree y + 1 := by
        change #((C.cloneVertex x y).blueGraph).edgeFinset + C.blueGraph.degree x =
          #C.blueGraph.edgeFinset + C.blueGraph.degree y + 1
        have hg := blueGraph_cloneVertex C hxy
        have hcard := card_edgeFinset_eq_of_graph_eq _ _ hg
        rw [hcard]
        omega
      have hrz := congrArg (fun m : ℕ ↦ (m : ℤ)) hrEq
      have hbz := congrArg (fun m : ℕ ↦ (m : ℤ)) hbEq
      push_cast at hrz hbz
      have heq :
          objective k (C.cloneVertex x y) - objective k C =
            weightedDegree k C y - weightedDegree k C x - (delta k : ℤ) := by
        unfold objective weightedDegree
        linear_combination hrz - (delta k : ℤ) * hbz
      rw [heq]
      omega

omit [Fintype V] in
/-- Adding one target to a clone set is the same as singleton-cloning that
target after cloning the old set. -/
theorem clone_insert (C : ColoredGraph V) (v x : V) (U : Finset V)
    (hv : v ∉ U) :
    C.clone v (insert x U) = (C.clone v U).cloneVertex x v := by
  have hrep : ∀ a : V,
      cloneRep v U (cloneRep v {x} a) = cloneRep v (insert x U) a := by
    intro a
    by_cases hax : a = x
    · subst a
      simp [cloneRep, hv]
    · by_cases haU : a ∈ U
      · simp [cloneRep, hax, haU]
      · simp [cloneRep, hax, haU]
  ext a b
  rw [clone_color_eq_color_cloneRep C v (insert x U) a b,
    clone_color_eq_color_cloneRep (C.clone v U) v {x} a b,
    clone_color_eq_color_cloneRep C v U (cloneRep v {x} a) (cloneRep v {x} b),
    hrep a, hrep b]

omit [Fintype V] in
/-- Cloning leaves an edge unchanged when neither endpoint is a clone target.
The endpoints may include the source itself. -/
theorem clone_color_of_not_mem_targets (C : ColoredGraph V) (v : V)
    (U : Finset V) {z y : V} (hz : z ∉ U) (hy : y ∉ U) :
    (C.clone v U).color z y = C.color z y := by
  by_cases hzv : z = v
  · subst z
    by_cases hyv : y = v
    · subst y
      simp
    · apply clone_color_source_of_not_mem_insert
      simp [Finset.mem_insert, hyv, hy]
  · by_cases hyv : y = v
    · subst y
      rw [(C.clone v U).color_comm, C.color_comm]
      apply clone_color_source_of_not_mem_insert
      simp [Finset.mem_insert, hzv, hz]
    · apply clone_color_of_not_mem_insert
      · simp [Finset.mem_insert, hzv, hz]
      · simp [Finset.mem_insert, hyv, hy]

/-- A color degree can increase by at most the number of clone targets. -/
theorem degree_clone_le_add_card (C : ColoredGraph V) (v : V)
    (U : Finset V) (c : EdgeColor) {z : V} (hz : z ∉ U) :
    (C.clone v U).degree c z ≤ C.degree c z + U.card := by
  have hsub : (C.clone v U).neighborFinset c z \ U ⊆ C.neighborFinset c z := by
    intro y hy
    have hyn := (Finset.mem_sdiff.mp hy).1
    have hyU := (Finset.mem_sdiff.mp hy).2
    rw [C.mem_neighborFinset]
    have hn := ((C.clone v U).mem_neighborFinset c z y).mp hyn
    exact ⟨hn.1, by simpa [clone_color_of_not_mem_targets C v U hz hyU] using hn.2⟩
  have hdiff := Finset.card_le_card hsub
  have hsplit := Finset.card_le_card_sdiff_add_card
    (s := (C.clone v U).neighborFinset c z) (t := U)
  unfold ColoredGraph.degree
  omega

/-- A color degree can decrease by at most the number of clone targets. -/
theorem degree_le_clone_add_card (C : ColoredGraph V) (v : V)
    (U : Finset V) (c : EdgeColor) {z : V} (hz : z ∉ U) :
    C.degree c z ≤ (C.clone v U).degree c z + U.card := by
  have hsub : C.neighborFinset c z \ U ⊆ (C.clone v U).neighborFinset c z := by
    intro y hy
    have hyn := (Finset.mem_sdiff.mp hy).1
    have hyU := (Finset.mem_sdiff.mp hy).2
    rw [(C.clone v U).mem_neighborFinset]
    have hn := (C.mem_neighborFinset c z y).mp hyn
    exact ⟨hn.1, by simpa [clone_color_of_not_mem_targets C v U hz hyU] using hn.2⟩
  have hdiff := Finset.card_le_card hsub
  have hsplit := Finset.card_le_card_sdiff_add_card
    (s := C.neighborFinset c z) (t := U)
  unfold ColoredGraph.degree
  omega

/-- Weighted degree decreases by at most `(delta k + 1) * |U|` at a
non-target vertex when cloning `U`. -/
theorem weightedDegree_clone_lower (k : ℕ) (C : ColoredGraph V)
    (v : V) (U : Finset V) {z : V} (hz : z ∉ U) :
    weightedDegree k C z - ((delta k : ℤ) + 1) * (U.card : ℤ) ≤
      weightedDegree k (C.clone v U) z := by
  have hr := degree_le_clone_add_card C v U .red hz
  have hb := degree_clone_le_add_card C v U .blue hz
  have hrz : (C.redDegree z : ℤ) ≤
      ((C.clone v U).redDegree z : ℤ) + (U.card : ℤ) := by exact_mod_cast hr
  have hbz : ((C.clone v U).blueDegree z : ℤ) ≤
      (C.blueDegree z : ℤ) + (U.card : ℤ) := by exact_mod_cast hb
  unfold weightedDegree
  linear_combination hrz + (delta k : ℤ) * hbz

/-- Weighted degree increases by at most `(delta k + 1) * |U|` at a
non-target vertex when cloning `U`. -/
theorem weightedDegree_clone_upper (k : ℕ) (C : ColoredGraph V)
    (v : V) (U : Finset V) {z : V} (hz : z ∉ U) :
    weightedDegree k (C.clone v U) z ≤
      weightedDegree k C z + ((delta k : ℤ) + 1) * (U.card : ℤ) := by
  have hr := degree_clone_le_add_card C v U .red hz
  have hb := degree_le_clone_add_card C v U .blue hz
  have hrz : ((C.clone v U).redDegree z : ℤ) ≤
      (C.redDegree z : ℤ) + (U.card : ℤ) := by exact_mod_cast hr
  have hbz : (C.blueDegree z : ℤ) ≤
      ((C.clone v U).blueDegree z : ℤ) + (U.card : ℤ) := by exact_mod_cast hb
  unfold weightedDegree
  linear_combination hrz + (delta k : ℤ) * hbz

/-- Objective gain from cloning a finite set, in the form used throughout the
stability argument:
`Phi(C^{U <- v}) - Phi(C) ≥ |U| D_C(v) - sum_{u in U} D_C(u)
  - (delta k + 1) |U|^2`.

Paper: inequality `eqn:phi-clone-ineq`.
-/
theorem objective_clone_sub_lower_bound (k : ℕ) (C : ColoredGraph V)
    {v : V} (U : Finset V) (hv : v ∉ U) :
    (U.card : ℤ) * weightedDegree k C v -
        ∑ u ∈ U, weightedDegree k C u -
          ((delta k : ℤ) + 1) * (U.card : ℤ) ^ 2 ≤
      objective k (C.clone v U) - objective k C := by
  classical
  induction U using Finset.induction_on with
  | empty =>
      have hclone : C.clone v ∅ = C := by
        ext a b
        rw [clone_color_eq_color_cloneRep]
        simp [cloneRep]
      simp [hclone]
  | @insert x U hx ih =>
      have hvU : v ∉ U := fun h ↦ hv (Finset.mem_insert_of_mem h)
      have hxv : x ≠ v := by
        intro h
        subst x
        exact hv (Finset.mem_insert_self v U)
      have hset := ih hvU
      let C' := C.clone v U
      have hident : C.clone v (insert x U) = C'.cloneVertex x v := by
        dsimp only [C']
        exact clone_insert C v x U hvU
      have hsingle :
          weightedDegree k C' v - weightedDegree k C' x - ((delta k : ℤ) + 1) ≤
            objective k (C'.cloneVertex x v) - objective k C' := by
        exact objective_cloneVertex_sub_lower_bound k C' hxv
      have hvdrift :
          weightedDegree k C v - ((delta k : ℤ) + 1) * (U.card : ℤ) ≤
            weightedDegree k C' v := by
        dsimp only [C']
        exact weightedDegree_clone_lower k C v U hvU
      have hxdrift :
          weightedDegree k C' x ≤
            weightedDegree k C x + ((delta k : ℤ) + 1) * (U.card : ℤ) := by
        dsimp only [C']
        exact weightedDegree_clone_upper k C v U hx
      have hstep :
          weightedDegree k C v - weightedDegree k C x -
              ((delta k : ℤ) + 1) * (2 * (U.card : ℤ) + 1) ≤
            objective k (C'.cloneVertex x v) - objective k C' := by
        calc
          _ ≤ weightedDegree k C' v - weightedDegree k C' x -
                ((delta k : ℤ) + 1) := by linarith
          _ ≤ _ := hsingle
      rw [Finset.card_insert_of_notMem hx, Finset.sum_insert hx, hident]
      calc
        ((U.card + 1 : ℕ) : ℤ) * weightedDegree k C v -
              (weightedDegree k C x + ∑ u ∈ U, weightedDegree k C u) -
              ((delta k : ℤ) + 1) * ((U.card + 1 : ℕ) : ℤ) ^ 2 =
            ((U.card : ℤ) * weightedDegree k C v -
              ∑ u ∈ U, weightedDegree k C u -
              ((delta k : ℤ) + 1) * (U.card : ℤ) ^ 2) +
            (weightedDegree k C v - weightedDegree k C x -
              ((delta k : ℤ) + 1) * (2 * (U.card : ℤ) + 1)) := by
                push_cast
                ring
        _ ≤ (objective k C' - objective k C) +
              (objective k (C'.cloneVertex x v) - objective k C') :=
          add_le_add hset hstep
        _ = objective k (C'.cloneVertex x v) - objective k C := by ring

end FiniteCloneCounts

/-! ## Twins and the secondary objective -/

/-- The complete color profile of a vertex, including the blue diagonal
convention. -/
def profile (C : ColoredGraph V) (x : V) : V → EdgeColor :=
  fun z ↦ C.color x z

/-- Two distinct vertices are twins when their complete color profiles agree.

This is equivalent to the paper's definition: their mutual edge is blue and
their colors to every other vertex agree.

Paper: proof of Lemma `lemma:kthOrderMantel`.
-/
def Twin (C : ColoredGraph V) (x y : V) : Prop :=
  x ≠ y ∧ profile C x = profile C y

/-- The full-profile definition of twins agrees with the paper's formulation:
the mutual edge is blue and all colors to outside vertices agree. -/
theorem twin_iff_paper (C : ColoredGraph V) (x y : V) :
    Twin C x y ↔
      x ≠ y ∧ C.color x y = .blue ∧
        ∀ z, z ≠ x → z ≠ y → C.color x z = C.color y z := by
  constructor
  · rintro ⟨hxy, hprofile⟩
    refine ⟨hxy, ?_, fun z _ _ ↦ congrFun hprofile z⟩
    have h := congrFun hprofile x
    calc
      C.color x y = C.color y x := C.color_comm x y
      _ = .blue := by simpa [profile] using h.symm
  · rintro ⟨hxy, hblue, houtside⟩
    refine ⟨hxy, funext fun z ↦ ?_⟩
    by_cases hzx : z = x
    · subst z
      simpa [profile, C.color_comm] using hblue.symm
    · by_cases hzy : z = y
      · subst z
        simpa [profile] using hblue
      · exact houtside z hzx hzy

/-- The simple graph whose edges are unordered pairs of twin vertices. -/
def twinGraph (C : ColoredGraph V) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y ↦ profile C x = profile C y

@[simp]
theorem twinGraph_adj (C : ColoredGraph V) (x y : V) :
    (twinGraph C).Adj x y ↔ Twin C x y := by
  simp [twinGraph, Twin, eq_comm]

/-- Twin endpoints necessarily have a blue mutual edge. -/
theorem color_eq_blue_of_twin (C : ColoredGraph V) {x y : V} (h : Twin C x y) :
    C.color x y = .blue := by
  have hp := congrFun h.2 x
  calc
    C.color x y = C.color y x := C.color_comm x y
    _ = .blue := by simpa [profile] using hp.symm

private theorem profile_clone_eq_of_rep_profile_eq (C : ColoredGraph V) (v : V)
    (U : Finset V) {a b : V}
    (h : profile C (cloneRep v U a) = profile C (cloneRep v U b)) :
    profile (C.clone v U) a = profile (C.clone v U) b := by
  funext z
  simpa [profile, clone_color_eq_color_cloneRep] using
    congrFun h (cloneRep v U z)

/-- Every old twin pair survives singleton cloning after replacing the target
by the source, and the source-target pair becomes a new twin pair. -/
theorem twinGraph_replaceVertex_sup_edge_le (C : ColoredGraph V) {x y : V}
    (hxy : x ≠ y) :
    (twinGraph C).replaceVertex y x ⊔ SimpleGraph.edge y x ≤
      twinGraph (C.cloneVertex x y) := by
  intro a b hab
  rw [twinGraph_adj]
  refine ⟨hab.ne, ?_⟩
  apply profile_clone_eq_of_rep_profile_eq
  rcases hab with hab | hab
  · by_cases ha : a = x
    · subst a
      by_cases hb : b = x
      · subst b
        simp at hab
      · have hold : (twinGraph C).Adj y b := by
          simpa [SimpleGraph.replaceVertex, hb] using hab
        simpa [cloneRep, hb] using (twinGraph_adj C y b).mp hold |>.2
    · by_cases hb : b = x
      · subst b
        have hold : (twinGraph C).Adj a y := by
          simpa [SimpleGraph.replaceVertex, ha] using hab
        simpa [cloneRep, ha] using (twinGraph_adj C a y).mp hold |>.2
      · have hold : (twinGraph C).Adj a b := by
          simpa [SimpleGraph.replaceVertex, ha, hb] using hab
        simpa [cloneRep, ha, hb] using (twinGraph_adj C a b).mp hold |>.2
  · rw [SimpleGraph.edge_adj] at hab
    rcases hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [cloneRep]

section FiniteTwinCounts

variable [Fintype V]

noncomputable instance twinGraphDecidableAdj (C : ColoredGraph V) :
    DecidableRel (twinGraph C).Adj := Classical.decRel _

/-- The paper's secondary objective `tau(C)`, the number of unordered twin
pairs.

Paper: proof of Lemma `lemma:kthOrderMantel`.
-/
noncomputable def twinPairCount (C : ColoredGraph V) : ℕ :=
  #(twinGraph C).edgeFinset

/-- Singleton cloning from `y` to a nontwin target `x` gains the source's twin
neighbors, adds the pair `xy`, and can lose only the target's old twin
neighbors. This is the subtraction-free form of the paper's lower bound for
the change in `tau`. -/
theorem twinPairCount_cloneVertex_lower_bound (C : ColoredGraph V) {x y : V}
    (hxy : x ≠ y) (hnt : ¬ Twin C x y) :
    twinPairCount C + (twinGraph C).degree y + 1 ≤
      twinPairCount (C.cloneVertex x y) + (twinGraph C).degree x := by
  let G := twinGraph C
  have hn : ¬ G.Adj y x := by
    simpa [G, twinGraph_adj, Twin, hxy, eq_comm] using hnt
  have hexact := card_replaceVertex_sup_edge_of_not_adj_add_degree G hn hxy.symm
  have hle := twinGraph_replaceVertex_sup_edge_le C hxy
  have hcard : #((G.replaceVertex y x) ⊔ SimpleGraph.edge y x).edgeFinset ≤
      #(twinGraph (C.cloneVertex x y)).edgeFinset :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hle)
  change #G.edgeFinset + G.degree y + 1 ≤
    #(twinGraph (C.cloneVertex x y)).edgeFinset + G.degree x
  calc
    #G.edgeFinset + G.degree y + 1 =
        #((G.replaceVertex y x) ⊔ SimpleGraph.edge y x).edgeFinset + G.degree x :=
      hexact.symm
    _ ≤ #(twinGraph (C.cloneVertex x y)).edgeFinset + G.degree x :=
      Nat.add_le_add_right hcard _

/-- If two vertices are not twins, cloning one from the other strictly
increases the twin-pair count in at least one direction.

This packages the two `tau` inequalities used in the symmetrization step of
the proof of Lemma `lemma:kthOrderMantel`.
-/
theorem twinPairCount_increases_in_one_clone (C : ColoredGraph V) {x y : V}
    (hxy : x ≠ y) (hnt : ¬ Twin C x y) :
    twinPairCount C < twinPairCount (C.cloneVertex x y) ∨
      twinPairCount C < twinPairCount (C.cloneVertex y x) := by
  have h₁ := twinPairCount_cloneVertex_lower_bound C hxy hnt
  have hnt' : ¬ Twin C y x := by
    simpa [Twin, eq_comm] using hnt
  have h₂ := twinPairCount_cloneVertex_lower_bound C hxy.symm hnt'
  omega

end FiniteTwinCounts

/-! ## Lexicographic symmetrization -/

private theorem exists_lexicographic_maximum {α : Type*} [Finite α]
    (p : α → Prop) (primary : α → ℤ) (secondary : α → ℕ)
    {x : α} (hx : p x) :
    ∃ y, p y ∧ ∀ z, p z →
      primary z ≤ primary y ∧
        (primary z = primary y → secondary z ≤ secondary y) := by
  classical
  let _ := Fintype.ofFinite α
  let candidates := Finset.univ.filter p
  have hne : candidates.Nonempty := ⟨x, by simp [candidates, hx]⟩
  obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image candidates
    (fun z ↦ toLex (primary z, secondary z)) hne
  refine ⟨y, (Finset.mem_filter.mp hy).2, ?_⟩
  intro z hz
  exact Prod.Lex.toLex_le_toLex'.mp (hmax z (by simp [candidates, hz]))

/-- There is an objective-maximizing free coloring (with the twin-pair count
maximized secondarily) in which every blue edge has twin endpoints.

This is the cloning symmetrization step in the proof of the paper's
`lemma:kthOrderMantel`.
-/
theorem exists_extremal_with_blue_twins {k n : ℕ} (C : ColoredGraph (Fin n))
    (hC : C.FkFree k) :
    ∃ psi : ColoredGraph (Fin n),
      psi.FkFree k ∧
      objective k C ≤ objective k psi ∧
      ∀ {x y : Fin n}, x ≠ y → psi.color x y = .blue → Twin psi x y := by
  classical
  obtain ⟨psi, hpsi, hmax⟩ :=
    exists_lexicographic_maximum
      (fun chi : ColoredGraph (Fin n) ↦ chi.FkFree k)
      (objective k) twinPairCount hC
  refine ⟨psi, hpsi, (hmax C hC).1, ?_⟩
  intro x y hxy hblue
  have hfree_xy : (psi.cloneVertex x y).FkFree k :=
    clone_preserves_fkFree hpsi (by simpa using hxy.symm)
  have hfree_yx : (psi.cloneVertex y x).FkFree k :=
    clone_preserves_fkFree hpsi (by simpa using hxy)
  have hmax_xy := hmax (psi.cloneVertex x y) hfree_xy
  have hmax_yx := hmax (psi.cloneVertex y x) hfree_yx
  have hchange_xy := objective_cloneVertex_sub k psi hxy hblue
  have hblue_yx : psi.color y x = .blue := by
    rw [psi.color_comm]
    exact hblue
  have hchange_yx := objective_cloneVertex_sub k psi hxy.symm hblue_yx
  have hdegree : weightedDegree k psi x = weightedDegree k psi y := by omega
  have hobj_xy : objective k (psi.cloneVertex x y) = objective k psi := by omega
  have hobj_yx : objective k (psi.cloneVertex y x) = objective k psi := by omega
  by_contra hnot
  rcases twinPairCount_increases_in_one_clone psi hxy hnot with htau | htau
  · exact not_lt_of_ge (hmax_xy.2 hobj_xy) htau
  · exact not_lt_of_ge (hmax_yx.2 hobj_yx) htau

/-! ## Profile classes and the reduced red graph -/

/-- Two vertices have the same complete color profile.

This reflexive version of `Twin` is the equivalence relation used to form the
profile classes in the post-symmetrization argument.

Paper: proof of Lemma `lemma:kthOrderMantel`.
-/
def ProfileEq (C : ColoredGraph V) (x y : V) : Prop :=
  profile C x = profile C y

@[simp]
theorem profileEq_iff_profile_eq (C : ColoredGraph V) (x y : V) :
    ProfileEq C x y ↔ profile C x = profile C y :=
  Iff.rfl

theorem profileEq_refl (C : ColoredGraph V) (x : V) : ProfileEq C x x :=
  rfl

theorem profileEq_symm {C : ColoredGraph V} {x y : V} (h : ProfileEq C x y) :
    ProfileEq C y x :=
  h.symm

theorem profileEq_trans {C : ColoredGraph V} {x y z : V}
    (hxy : ProfileEq C x y) (hyz : ProfileEq C y z) : ProfileEq C x z :=
  hxy.trans hyz

/-- `ProfileEq` is exactly `Twin` after adding distinctness. -/
@[simp]
theorem twin_iff_ne_and_profileEq (C : ColoredGraph V) (x y : V) :
    Twin C x y ↔ x ≠ y ∧ ProfileEq C x y :=
  Iff.rfl

/-- The setoid of equal complete color profiles. -/
def profileSetoid (C : ColoredGraph V) : Setoid V where
  r := ProfileEq C
  iseqv.refl x := profileEq_refl C x
  iseqv.symm h := profileEq_symm h
  iseqv.trans hxy hyz := profileEq_trans hxy hyz

/-- Equal complete profiles force the joining pair to be blue, including on
the diagonal under the total diagonal-blue convention. -/
theorem color_blue_of_profileEq {C : ColoredGraph V} {x y : V} (h : ProfileEq C x y) :
    C.color x y = .blue := by
  by_cases hxy : x = y
  · subst y
    simp
  · exact color_eq_blue_of_twin C ⟨hxy, h⟩

/-- The structural hypothesis supplied by cloning symmetrization: every blue
edge has equal-profile endpoints.

Paper: the conclusion of the symmetrization step in the proof of Lemma
`lemma:kthOrderMantel`.
-/
def BlueEdgesAreProfileEq (C : ColoredGraph V) : Prop :=
  ∀ {x y}, x ≠ y → C.color x y = .blue → ProfileEq C x y

/-- Under the symmetrized hypothesis, distinct vertices are joined in blue
exactly when they have the same profile. -/
theorem blue_iff_profileEq {C : ColoredGraph V} (hblue : BlueEdgesAreProfileEq C)
    {x y : V} (hxy : x ≠ y) : C.color x y = .blue ↔ ProfileEq C x y :=
  ⟨hblue hxy, color_blue_of_profileEq⟩

/-- Weighted AM--GM on a finite graph of maximum degree at most `d`.

This is the abstract inequality used on the reduced red graph in the proof
of Lemma `lemma:kthOrderMantel`.
-/
theorem weighted_adj_sum_le {I : Type*} [Fintype I]
    (R : SimpleGraph I) [DecidableRel R.Adj] (a : I → ℤ) (d : ℕ)
    (hdeg : ∀ i, R.degree i ≤ d) :
    (∑ i, a i * ∑ j ∈ R.neighborFinset i, a j) ≤
      (d : ℤ) * ∑ i, (a i) ^ 2 := by
  classical
  have hamgm (i j : I) : 2 * (a i * a j) ≤ a i ^ 2 + a j ^ 2 := by
    nlinarith [sq_nonneg (a i - a j)]
  have hfirst :
      2 * (∑ i, a i * ∑ j ∈ R.neighborFinset i, a j) ≤
        ∑ i, ∑ j ∈ R.neighborFinset i, (a i ^ 2 + a j ^ 2) := by
    calc
      2 * (∑ i, a i * ∑ j ∈ R.neighborFinset i, a j) =
          ∑ i, ∑ j ∈ R.neighborFinset i, 2 * (a i * a j) := by
            simp [mul_sum]
      _ ≤ ∑ i, ∑ j ∈ R.neighborFinset i, (a i ^ 2 + a j ^ 2) := by
        exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hamgm i j
  have hswap :
      (∑ i, ∑ j ∈ R.neighborFinset i, a j ^ 2) =
        ∑ i, (R.degree i : ℤ) * a i ^ 2 := by
    simp_rw [R.neighborFinset_eq_filter, Finset.sum_filter]
    rw [Finset.sum_comm]
    congr 1
    funext i
    rw [← R.card_neighborFinset_eq_degree]
    calc
      (∑ x, if R.Adj x i then a i ^ 2 else 0) =
          (∑ x, if R.Adj x i then (1 : ℤ) else 0) * a i ^ 2 := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x _hx
            split <;> simp_all
      _ = a i ^ 2 * (#{x ∈ Finset.univ | R.Adj i x} : ℤ) := by
        rw [Finset.sum_boole]
        simp only [R.adj_comm]
        ring
      _ = (#{x ∈ R.neighborFinset i | True} : ℤ) * a i ^ 2 := by
        simp [R.neighborFinset_eq_filter]
        ring
      _ = (#(R.neighborFinset i) : ℤ) * a i ^ 2 := by simp
  have hstay :
      (∑ i, ∑ _j ∈ R.neighborFinset i, a i ^ 2) =
        ∑ i, (R.degree i : ℤ) * a i ^ 2 := by
    congr 1
    funext i
    rw [← R.card_neighborFinset_eq_degree]
    simp
  have hrewrite :
      (∑ i, ∑ j ∈ R.neighborFinset i, (a i ^ 2 + a j ^ 2)) =
        2 * ∑ i, (R.degree i : ℤ) * a i ^ 2 := by
    simp_rw [Finset.sum_add_distrib]
    rw [hstay, hswap]
    ring
  rw [hrewrite] at hfirst
  have hdegree :
      (∑ i, (R.degree i : ℤ) * a i ^ 2) ≤
        (d : ℤ) * ∑ i, a i ^ 2 := by
    calc
      (∑ i, (R.degree i : ℤ) * a i ^ 2) ≤
          ∑ i, (d : ℤ) * a i ^ 2 := by
            exact Finset.sum_le_sum fun i _ ↦ by
              gcongr
              exact_mod_cast hdeg i
      _ = (d : ℤ) * ∑ i, a i ^ 2 := by rw [Finset.mul_sum]
  omega

/-- Natural-number specialization of `weighted_adj_sum_le`. -/
theorem weighted_adj_sum_le_nat {I : Type*} [Fintype I]
    (R : SimpleGraph I) [DecidableRel R.Adj] (a : I → ℕ) (d : ℕ)
    (hdeg : ∀ i, R.degree i ≤ d) :
    (∑ i, a i * ∑ j ∈ R.neighborFinset i, a j) ≤
      d * ∑ i, (a i) ^ 2 := by
  classical
  have h := weighted_adj_sum_le R (fun i ↦ (a i : ℤ)) d hdeg
  exact_mod_cast h

section FiniteProfileQuotient

variable [Fintype V]

noncomputable instance profileEqDecidable (C : ColoredGraph V) :
    DecidableRel (ProfileEq C) :=
  Classical.decRel _

noncomputable instance profileSetoidDecidable (C : ColoredGraph V) :
    DecidableRel (profileSetoid C) := by
  change DecidableRel (ProfileEq C)
  exact profileEqDecidable C

/-- The finite partition of the vertex set into complete-profile classes. -/
noncomputable def twinPartition (C : ColoredGraph V) :
    Finpartition (Finset.univ : Finset V) :=
  Finpartition.ofSetoid (profileSetoid C)

/-- A class of the complete-profile partition. -/
abbrev Part (C : ColoredGraph V) := {A // A ∈ (twinPartition C).parts}

/-- The profile class containing a vertex. -/
noncomputable def partOf (C : ColoredGraph V) (x : V) : Part C :=
  ⟨(twinPartition C).part x, (twinPartition C).part_mem.2 (Finset.mem_univ x)⟩

@[simp]
theorem mem_partOf (C : ColoredGraph V) (x : V) : x ∈ (partOf C x).1 :=
  (twinPartition C).mem_part (Finset.mem_univ x)

@[simp]
theorem partOf_eq_of_mem (C : ColoredGraph V) {A : Part C} {x : V} (hx : x ∈ A.1) :
    partOf C x = A := by
  apply Subtype.ext
  exact (twinPartition C).part_eq_of_mem A.property hx

theorem part_card_pos (C : ColoredGraph V) (A : Part C) : 0 < #A.1 :=
  Finset.card_pos.mpr ((twinPartition C).nonempty_of_mem_parts A.property)

/-- Choose one representative from each nonempty profile class. -/
noncomputable def rep (C : ColoredGraph V) (A : Part C) : V :=
  ((twinPartition C).nonempty_of_mem_parts A.property).choose

theorem rep_mem (C : ColoredGraph V) (A : Part C) : rep C A ∈ A.1 :=
  ((twinPartition C).nonempty_of_mem_parts A.property).choose_spec

@[simp]
theorem mem_part_iff_profileEq (C : ColoredGraph V) (x y : V) :
    y ∈ (twinPartition C).part x ↔ ProfileEq C x y := by
  change y ∈ (Finpartition.ofSetoid (profileSetoid C)).part x ↔ (profileSetoid C) x y
  exact Finpartition.mem_part_ofSetoid_iff_rel

theorem profileEq_of_mem_part {C : ColoredGraph V} {A : Part C} {x y : V}
    (hx : x ∈ A.1) (hy : y ∈ A.1) : ProfileEq C x y := by
  have hpartx : (twinPartition C).part x = A.1 :=
    (twinPartition C).part_eq_of_mem A.property hx
  rw [← mem_part_iff_profileEq C, hpartx]
  exact hy

theorem profileEq_iff_partOf_eq (C : ColoredGraph V) (x y : V) :
    ProfileEq C x y ↔ partOf C x = partOf C y := by
  rw [← mem_part_iff_profileEq C]
  constructor
  · intro hy
    apply Subtype.ext
    exact ((twinPartition C).part_eq_of_mem (partOf C x).property hy).symm
  · intro h
    have hp : (twinPartition C).part x = (twinPartition C).part y :=
      congrArg Subtype.val h
    rw [hp]
    exact (twinPartition C).mem_part (Finset.mem_univ y)

/-- Regroup a finite vertex sum by profile classes. -/
theorem sum_by_parts {M : Type*} [AddCommMonoid M] (C : ColoredGraph V) (f : V → M) :
    ∑ x, f x = ∑ A : Part C, ∑ x : A.1, f x := by
  classical
  let e : V ≃ Σ A : Part C, A.1 :=
    (Equiv.subtypeUnivEquiv (fun x : V ↦ Finset.mem_univ x)).symm.trans
      (twinPartition C).equivSigmaParts
  calc
    ∑ x, f x = ∑ q : Σ A : Part C, A.1, f q.2 := by
      apply Fintype.sum_equiv e
      intro x
      rfl
    _ = ∑ A : Part C, ∑ x : A.1, f x := by
      simpa only using
        (Fintype.sum_sigma' (fun (A : Part C) (x : A.1) ↦ f (x : V)))

theorem color_eq_rep_rep {C : ColoredGraph V} {A B : Part C} {x y : V}
    (hx : x ∈ A.1) (hy : y ∈ B.1) :
    C.color x y = C.color (rep C A) (rep C B) := by
  have hxrep : ProfileEq C x (rep C A) := profileEq_of_mem_part hx (rep_mem C A)
  have hyrep : ProfileEq C y (rep C B) := profileEq_of_mem_part hy (rep_mem C B)
  calc
    C.color x y = C.color (rep C A) y := congrFun hxrep y
    _ = C.color y (rep C A) := C.color_comm _ _
    _ = C.color (rep C B) (rep C A) := congrFun hyrep (rep C A)
    _ = C.color (rep C A) (rep C B) := C.color_comm _ _

theorem rep_injective (C : ColoredGraph V) : Function.Injective (rep C) := by
  intro A B hrep
  apply Subtype.ext
  apply (twinPartition C).eq_of_mem_parts A.property B.property
  · exact rep_mem C A
  · simpa [hrep] using rep_mem C B

@[simp]
theorem partOf_rep (C : ColoredGraph V) (A : Part C) : partOf C (rep C A) = A := by
  apply Subtype.ext
  exact (twinPartition C).part_eq_of_mem A.property (rep_mem C A)

@[simp]
theorem profileEq_rep_iff_eq (C : ColoredGraph V) (A B : Part C) :
    ProfileEq C (rep C A) (rep C B) ↔ A = B := by
  rw [profileEq_iff_partOf_eq, partOf_rep, partOf_rep]

/-- The reduced red graph on profile classes: two distinct classes are
adjacent exactly when their constant cross-color is red.

Paper: reduced-graph step in the proof of Lemma `lemma:kthOrderMantel`.
-/
noncomputable def reducedRed (C : ColoredGraph V) : SimpleGraph (Part C) where
  Adj A B := A ≠ B ∧ C.color (rep C A) (rep C B) = .red
  symm.symm A B h := by
    exact ⟨h.1.symm, by rw [C.color_comm]; exact h.2⟩
  loopless.irrefl A h := h.1 rfl

noncomputable instance reducedRedDecidableAdj (C : ColoredGraph V) :
    DecidableRel (reducedRed C).Adj :=
  Classical.decRel _

theorem reducedRed_adj {C : ColoredGraph V} {A B : Part C} :
    (reducedRed C).Adj A B ↔ A ≠ B ∧ C.color (rep C A) (rep C B) = .red :=
  Iff.rfl

/-- Cross-edges between two profile classes are red exactly when their
classes are adjacent in the reduced graph. -/
theorem cross_red_iff_adj {C : ColoredGraph V} {A B : Part C} {x y : V}
    (hx : x ∈ A.1) (hy : y ∈ B.1) :
    C.color x y = .red ↔ (reducedRed C).Adj A B := by
  rw [reducedRed_adj, color_eq_rep_rep hx hy]
  constructor
  · intro hred
    refine ⟨?_, hred⟩
    intro hAB
    subst B
    simp at hred
  · exact And.right

/-! ### Exact cluster counts -/

/-- Under the blue-profile hypothesis, the blue neighbors of a vertex are
exactly the other vertices in its profile class. -/
theorem blueNeighborFinset_eq_erase_part (C : ColoredGraph V)
    (hblue : BlueEdgesAreProfileEq C) (x : V) :
    C.blueNeighborFinset x = ((twinPartition C).part x).erase x := by
  ext y
  rw [C.mem_neighborFinset, Finset.mem_erase, mem_part_iff_profileEq]
  constructor
  · rintro ⟨hxy, hcolor⟩
    exact ⟨hxy.symm, hblue hxy hcolor⟩
  · rintro ⟨hyx, hprofile⟩
    exact ⟨hyx.symm, color_blue_of_profileEq hprofile⟩

/-- Exact size formula for a blue degree. -/
theorem blueDegree_eq_part_card_sub_one (C : ColoredGraph V)
    (hblue : BlueEdgesAreProfileEq C) (x : V) :
    C.blueDegree x = #(partOf C x).1 - 1 := by
  change #(C.blueNeighborFinset x) = _
  rw [blueNeighborFinset_eq_erase_part C hblue]
  exact Finset.card_erase_of_mem (mem_partOf C x)

/-- The red neighbors of a vertex are the disjoint union of the profile
classes adjacent to its class in the reduced red graph. -/
theorem redNeighborFinset_eq_biUnion (C : ColoredGraph V) (x : V) :
    C.redNeighborFinset x =
      ((reducedRed C).neighborFinset (partOf C x)).biUnion (fun B ↦ B.1) := by
  ext y
  rw [C.mem_neighborFinset, Finset.mem_biUnion]
  constructor
  · rintro ⟨_hxy, hred⟩
    let B := partOf C y
    have hadj : (reducedRed C).Adj (partOf C x) B :=
      (cross_red_iff_adj (mem_partOf C x) (mem_partOf C y)).mp hred
    exact ⟨B, by simpa only [SimpleGraph.mem_neighborFinset] using hadj, mem_partOf C y⟩
  · rintro ⟨B, hB, hyB⟩
    have hadj : (reducedRed C).Adj (partOf C x) B := by
      simpa only [SimpleGraph.mem_neighborFinset] using hB
    have hred : C.color x y = .red :=
      (cross_red_iff_adj (mem_partOf C x) hyB).mpr hadj
    refine ⟨?_, hred⟩
    intro hxy
    subst y
    rw [C.color_self] at hred
    contradiction

/-- Exact weighted-neighborhood formula for a red degree. -/
theorem redDegree_eq_sum_neighbor_cards (C : ColoredGraph V) (x : V) :
    C.redDegree x =
      ∑ B ∈ (reducedRed C).neighborFinset (partOf C x), #B.1 := by
  change #(C.redNeighborFinset x) = _
  rw [redNeighborFinset_eq_biUnion C x]
  apply Finset.card_biUnion
  intro A _ B _ hAB
  exact (twinPartition C).disjoint A.property B.property
    (fun h ↦ hAB (Subtype.ext h))

/-- The profile-class sizes sum to the total number of vertices. -/
theorem sum_part_cards (C : ColoredGraph V) :
    ∑ A : Part C, #A.1 = Fintype.card V := by
  simpa using (sum_by_parts C (fun _ : V ↦ (1 : ℕ))).symm

/-- Exact blue-edge count as a sum of within-class contributions.

Paper: blue-edge identity in the reduced-graph step of the proof of Lemma
`lemma:kthOrderMantel`.
-/
theorem two_mul_blueEdgeCount_eq_cluster_sum (C : ColoredGraph V)
    (hblue : BlueEdgesAreProfileEq C) :
    2 * C.blueEdgeCount = ∑ A : Part C, #A.1 * (#A.1 - 1) := by
  calc
    2 * C.blueEdgeCount = ∑ x, C.blueDegree x :=
      (C.sum_degree_eq_two_mul_edgeCount .blue).symm
    _ = ∑ A : Part C, ∑ x : A.1, C.blueDegree x :=
      sum_by_parts C C.blueDegree
    _ = ∑ A : Part C, #A.1 * (#A.1 - 1) := by
      apply Fintype.sum_congr
      intro A
      calc
        ∑ x : A.1, C.blueDegree x = ∑ _x : A.1, (#A.1 - 1) := by
          apply Fintype.sum_congr
          intro x
          rw [blueDegree_eq_part_card_sub_one C hblue, partOf_eq_of_mem C x.property]
        _ = #A.1 * (#A.1 - 1) := by simp

/-- Exact doubled red-edge count as the oriented weighted adjacency sum of
the reduced red graph.

Paper: red-edge identity in the reduced-graph step of the proof of Lemma
`lemma:kthOrderMantel`.
-/
theorem two_mul_redEdgeCount_eq_cluster_sum (C : ColoredGraph V) :
    2 * C.redEdgeCount =
      ∑ A : Part C, #A.1 *
        ∑ B ∈ (reducedRed C).neighborFinset A, #B.1 := by
  calc
    2 * C.redEdgeCount = ∑ x, C.redDegree x :=
      (C.sum_degree_eq_two_mul_edgeCount .red).symm
    _ = ∑ A : Part C, ∑ x : A.1, C.redDegree x :=
      sum_by_parts C C.redDegree
    _ = ∑ A : Part C, #A.1 *
        ∑ B ∈ (reducedRed C).neighborFinset A, #B.1 := by
      apply Fintype.sum_congr
      intro A
      calc
        ∑ x : A.1, C.redDegree x =
            ∑ _x : A.1, ∑ B ∈ (reducedRed C).neighborFinset A, #B.1 := by
          apply Fintype.sum_congr
          intro x
          rw [redDegree_eq_sum_neighbor_cards C x, partOf_eq_of_mem C x.property]
        _ = #A.1 * ∑ B ∈ (reducedRed C).neighborFinset A, #B.1 := by simp

/-! ### Reduced degree and the post-symmetrization inequality -/

/-- In an `ℑ_k`-free symmetrized coloring, every vertex of the reduced red
graph has degree at most `delta k = k - 2`.

Paper: forbidden-star argument in the proof of Lemma
`lemma:kthOrderMantel`.
-/
theorem reducedRed_degree_le_delta {k : ℕ} (hk : 3 ≤ k) {C : ColoredGraph V}
    (hfree : C.FkFree k) (hblue : BlueEdgesAreProfileEq C) (A : Part C) :
    (reducedRed C).degree A ≤ delta k := by
  classical
  by_contra hdegree
  have hlarge : delta k + 1 ≤ #((reducedRed C).neighborFinset A) := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hlarge
  let leaves : Finset V := T.image (rep C)
  have hconfig : C.IsForbiddenConfig k (rep C A) leaves := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hcenter
      rw [Finset.mem_image] at hcenter
      obtain ⟨B, hBT, hrep⟩ := hcenter
      have hBA : B ≠ A := by
        have hadj : (reducedRed C).Adj A B := by
          simpa only [SimpleGraph.mem_neighborFinset] using hTsub hBT
        exact hadj.ne.symm
      exact hBA (rep_injective C hrep)
    · dsimp [leaves]
      rw [Finset.card_image_of_injective _ (rep_injective C), hTcard]
      unfold delta
      omega
    · intro x hx
      dsimp [leaves] at hx
      rw [Finset.mem_image] at hx
      obtain ⟨B, hBT, rfl⟩ := hx
      have hadj : (reducedRed C).Adj A B := by
        simpa only [SimpleGraph.mem_neighborFinset] using hTsub hBT
      exact (reducedRed_adj.mp hadj).2
    · intro x hx y hy hxy
      dsimp [leaves] at hx hy
      rw [Finset.mem_image] at hx hy
      obtain ⟨B, _hBT, rfl⟩ := hx
      obtain ⟨D, _hDT, rfl⟩ := hy
      rw [EdgeColor.isLeafColor_iff_ne_blue]
      intro hBDblue
      have hp : ProfileEq C (rep C B) (rep C D) := hblue hxy hBDblue
      have hBD : B = D := (profileEq_rep_iff_eq C B D).mp hp
      exact hxy (congrArg (rep C) hBD)
  exact (C.not_fkFree_of_forbiddenConfig (by omega) hconfig) hfree

/-- The sum of squared class sizes is the doubled blue-edge count plus the
number of vertices. -/
theorem sum_sq_part_cards_eq_two_mul_blueEdgeCount_add_card (C : ColoredGraph V)
    (hblue : BlueEdgesAreProfileEq C) :
    ∑ A : Part C, (#A.1) ^ 2 = 2 * C.blueEdgeCount + Fintype.card V := by
  calc
    ∑ A : Part C, (#A.1) ^ 2 =
        ∑ A : Part C, (#A.1 * (#A.1 - 1) + #A.1) := by
      apply Fintype.sum_congr
      intro A
      calc
        (#A.1) ^ 2 = #A.1 * #A.1 := pow_two _
        _ = #A.1 * ((#A.1 - 1) + 1) := by
          rw [Nat.sub_add_cancel (part_card_pos C A)]
        _ = #A.1 * (#A.1 - 1) + #A.1 := by rw [Nat.mul_add, Nat.mul_one]
    _ = (∑ A : Part C, #A.1 * (#A.1 - 1)) + ∑ A : Part C, #A.1 := by
      rw [Finset.sum_add_distrib]
    _ = 2 * C.blueEdgeCount + Fintype.card V := by
      rw [← two_mul_blueEdgeCount_eq_cluster_sum C hblue, sum_part_cards C]

/-- Natural-number form of the weighted reduced-graph estimate. -/
theorem two_mul_redEdgeCount_le_delta_mul_blue_card {k : ℕ} (hk : 3 ≤ k)
    {C : ColoredGraph V} (hfree : C.FkFree k) (hblue : BlueEdgesAreProfileEq C) :
    2 * C.redEdgeCount ≤
      delta k * (2 * C.blueEdgeCount + Fintype.card V) := by
  have h := weighted_adj_sum_le_nat (reducedRed C) (fun A : Part C ↦ #A.1)
    (delta k) (reducedRed_degree_le_delta hk hfree hblue)
  rw [← two_mul_redEdgeCount_eq_cluster_sum C,
    sum_sq_part_cards_eq_two_mul_blueEdgeCount_add_card C hblue] at h
  exact h

/-- The post-symmetrization objective bound
`2 * Phi(C) ≤ (k - 2) * |V|`.

This is the second half of the proof of Lemma `lemma:kthOrderMantel`; the
preceding lexicographic symmetrization supplies its blue-profile hypothesis.
-/
theorem two_mul_objective_le_delta_mul_card {k : ℕ} (hk : 3 ≤ k)
    {C : ColoredGraph V} (hfree : C.FkFree k) (hblue : BlueEdgesAreProfileEq C) :
    2 * objective k C ≤ (delta k : ℤ) * (Fintype.card V : ℤ) := by
  have hnat := two_mul_redEdgeCount_le_delta_mul_blue_card hk hfree hblue
  have hz : ((2 * C.redEdgeCount : ℕ) : ℤ) ≤
      (delta k * (2 * C.blueEdgeCount + Fintype.card V) : ℕ) := by
    exact_mod_cast hnat
  unfold objective
  push_cast at hz ⊢
  nlinarith

end FiniteProfileQuotient

/-! ## The kth-order Mantel inequality -/

/-- The two halves of the paper's symmetrization argument packaged together:
an extremal free coloring has equal profiles across every blue edge, and its
reduced red graph has maximum degree at most `k - 2`.

Paper: the symmetrization step in the proof of Lemma
`lemma:kthOrderMantel`.
-/
theorem twinClassSymmetrization {k n : ℕ} (hk : 3 ≤ k)
    (C : ColoredGraph (Fin n)) (hC : C.FkFree k) :
    ∃ psi : ColoredGraph (Fin n),
      psi.FkFree k ∧
        objective k C ≤ objective k psi ∧
          BlueEdgesAreProfileEq psi ∧
            ∀ A : Part psi, (reducedRed psi).degree A ≤ delta k := by
  obtain ⟨psi, hpsi, hobj, htwins⟩ := exists_extremal_with_blue_twins C hC
  have hprofiles : BlueEdgesAreProfileEq psi := by
    intro x y hxy hblue
    exact (htwins hxy hblue).2
  exact ⟨psi, hpsi, hobj, hprofiles,
    reducedRed_degree_le_delta hk hpsi hprofiles⟩

/-- The paper's kth-order Mantel inequality, with unordered edge counts and
the exact integer floor:
`Phi(C) ≤ floor ((k - 2) n / 2)`.

No hypothesis `k ≤ n` is needed; when `k > n`, forbidden-pattern-freeness is
vacuous and the same inequality remains valid.

Paper: Lemma `lemma:kthOrderMantel`.
-/
theorem kthOrderMantel {k n : ℕ} (hk : 3 ≤ k)
    {C : ColoredGraph (Fin n)} (hC : C ∈ Ck k n) :
    objective k C ≤ ((delta k * n / 2 : ℕ) : ℤ) := by
  obtain ⟨psi, hpsi, hobj, hprofiles, _hdegree⟩ :=
    twinClassSymmetrization hk C hC
  have htwo := two_mul_objective_le_delta_mul_card hk hpsi hprofiles
  have htwo' : 2 * objective k psi ≤ ((delta k * n : ℕ) : ℤ) := by
    simpa using htwo
  have hhalf : objective k psi ≤ ((delta k * n / 2 : ℕ) : ℤ) := by
    omega
  exact hobj.trans hhalf

/-! ## The Mantel bound on an induced vertex set -/

@[simp]
theorem redEdgeCount_restrictToFin {n : ℕ} (C : ColoredGraph (Fin n))
    (S : Finset (Fin n)) :
    (C.restrictToFin S).redEdgeCount = C.redEdgeCountIn S :=
  edgeCount_restrictToFin C S .red

@[simp]
theorem blueEdgeCount_restrictToFin {n : ℕ} (C : ColoredGraph (Fin n))
    (S : Finset (Fin n)) :
    (C.restrictToFin S).blueEdgeCount = C.blueEdgeCountIn S :=
  edgeCount_restrictToFin C S .blue

/-- Relabeling the coloring induced on `S` does not change its weighted
objective. -/
@[simp]
theorem objective_restrictToFin {k n : ℕ} (C : ColoredGraph (Fin n))
    (S : Finset (Fin n)) :
    objective k (C.restrictToFin S) = objectiveIn k C S := by
  unfold objective objectiveIn
  rw [redEdgeCount_restrictToFin, blueEdgeCount_restrictToFin]

/-- The exact integer `k`-th-order Mantel bound applied to the coloring
induced on an arbitrary finite vertex set.  This is the hereditary estimate
used for the remainder in the core-extraction argument. -/
theorem objectiveIn_le_kthOrderMantel {k n : ℕ} (hk : 3 ≤ k)
    {C : ColoredGraph (Fin n)} (hC : C ∈ Ck k n)
    (S : Finset (Fin n)) :
    objectiveIn k C S ≤ ((delta k * S.card / 2 : ℕ) : ℤ) := by
  rw [← objective_restrictToFin]
  exact kthOrderMantel hk (restrictToFin_mem_Ck hC S)

/-! ## Objective decomposition across an induced remainder -/

/-- The full objective is the restricted objective on `S`, the contribution
of the cut from `S` to its complement, and the restricted objective on the
complement.  This is the exact integer decomposition used in Stage F11 of
core extraction. -/
theorem objective_eq_objectiveIn_add_between_add_compl {k n : ℕ}
    (C : ColoredGraph (Fin n)) (S : Finset (Fin n)) :
    objective k C =
      objectiveIn k C S +
        objectiveBetween k C S (Finset.univ \ S) +
          objectiveIn k C (Finset.univ \ S) := by
  have hdisj : Disjoint S (Finset.univ \ S) := Finset.disjoint_sdiff
  have hunion : S ∪ (Finset.univ \ S) = Finset.univ := by
    ext v
    simp
  have hsplit := objectiveIn_union_of_disjoint k C hdisj
  rw [hunion] at hsplit
  have huniv (c : EdgeColor) :
      C.edgeCountIn c Finset.univ = C.edgeCount c := by
    unfold edgeCountIn edgeFinsetIn edgeCount
    simp only [Finset.sym2_univ, Finset.inter_univ]
  have hobjectiveUniv : objectiveIn k C Finset.univ = objective k C := by
    unfold objectiveIn objective
    change (C.edgeCountIn .red Finset.univ : ℤ) -
        (delta k : ℤ) * (C.edgeCountIn .blue Finset.univ : ℤ) =
      (C.edgeCount .red : ℤ) -
        (delta k : ℤ) * (C.edgeCount .blue : ℤ)
    rw [huniv, huniv]
  rw [hobjectiveUniv] at hsplit
  exact hsplit

/-- A quantitative remainder form of the objective decomposition.  If the
whole coloring is `a n²`-near-extremal, the red part of the cut is at most
`b n²`, and the Mantel contribution of the removed set is at most `g n²`,
then its complement is `(a+b+g)n²`-near-extremal.

The blue contribution of the cut has the favorable sign and is discarded.
The Mantel hypothesis is kept as an explicit real inequality so that the
caller can absorb the linear integer bound into its chosen large-`n`
threshold. -/
theorem objectiveIn_compl_lower_bound {k n : ℕ} (hk : 3 ≤ k)
    {C : ColoredGraph (Fin n)} (hC : C ∈ Ck k n)
    (S : Finset (Fin n)) {a b g : ℝ}
    (hnear : -(a * (n : ℝ) ^ 2) ≤ (objective k C : ℝ))
    (hcut : (C.colorEdgeCountBetween .red S (Finset.univ \ S) : ℝ) ≤
      b * (n : ℝ) ^ 2)
    (hcore : ((delta k * S.card / 2 : ℕ) : ℝ) ≤ g * (n : ℝ) ^ 2) :
    -((a + b + g) * (n : ℝ) ^ 2) ≤
      (objectiveIn k C (Finset.univ \ S) : ℝ) := by
  have hsplitZ := objective_eq_objectiveIn_add_between_add_compl
    (k := k) C S
  have hsplit : (objective k C : ℝ) =
      (objectiveIn k C S : ℝ) +
        (objectiveBetween k C S (Finset.univ \ S) : ℝ) +
          (objectiveIn k C (Finset.univ \ S) : ℝ) := by
    exact_mod_cast hsplitZ
  have hmantelZ := objectiveIn_le_kthOrderMantel hk hC S
  have hmantel : (objectiveIn k C S : ℝ) ≤
      ((delta k * S.card / 2 : ℕ) : ℝ) := by
    calc
      (objectiveIn k C S : ℝ) ≤
          ((((delta k * S.card / 2 : ℕ) : ℤ)) : ℝ) :=
        (Int.cast_le).2 hmantelZ
      _ = ((delta k * S.card / 2 : ℕ) : ℝ) := by
        rw [Int.cast_natCast]
  have hbetween :
      (objectiveBetween k C S (Finset.univ \ S) : ℝ) ≤
        (C.colorEdgeCountBetween .red S (Finset.univ \ S) : ℝ) := by
    unfold objectiveBetween
    push_cast
    have hnonneg : 0 ≤
        (delta k : ℝ) *
          (C.colorEdgeCountBetween .blue S (Finset.univ \ S) : ℝ) := by
      positivity
    linarith
  have hN : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  rw [hsplit] at hnear
  nlinarith

end ColoredGraph

end InducedStars
