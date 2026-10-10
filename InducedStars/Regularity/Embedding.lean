import InducedStars.Regularity.Basic
import Mathlib.Tactic

/-!
# The finite induced embedding lemma

This file proves the finite induced embedding input used by the local BTW
adapter.  The proof is a greedy transversal argument: regularity bounds the
number of atypical vertices at every step, and a geometric candidate-size
invariant leaves a vertex outside the union of all atypical sets.
-/

open Finset
open scoped SimpleGraph

namespace InducedStars.Regularity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

lemma card_interedges_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    (G.interedges A B).card = ∑ x ∈ A, (B.filter (G.Adj x)).card := by
  classical
  rw [SimpleGraph.interedges, Rel.interedges_eq_biUnion]
  rw [Finset.card_biUnion]
  · simp
  · intro x hx y hy hxy
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [Finset.mem_map, Finset.mem_filter] at hz hz'
    obtain ⟨zx, _, rfl⟩ := hz
    obtain ⟨zy, _, hpair⟩ := hz'
    exact hxy (congrArg Prod.fst hpair).symm

lemma graphDensity_lt_of_pointwise_lt
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {c : ℝ}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hpoint : ∀ x ∈ A, ((B.filter (G.Adj x)).card : ℝ) < c * B.card) :
    graphDensity G A B < c := by
  rw [graphDensity_eq]
  have hsum : ((G.interedges A B).card : ℝ) <
      (A.card : ℝ) * (c * (B.card : ℝ)) := by
    rw [card_interedges_eq_sum]
    push_cast
    calc
      ∑ x ∈ A, ((B.filter (G.Adj x)).card : ℝ) <
          ∑ _x ∈ A, c * (B.card : ℝ) := by
            exact Finset.sum_lt_sum (fun x hx ↦ (hpoint x hx).le)
              ⟨hA.choose, hA.choose_spec, hpoint hA.choose hA.choose_spec⟩
      _ = (A.card : ℝ) * (c * (B.card : ℝ)) := by simp
  have hden : 0 < (A.card : ℝ) * (B.card : ℝ) := by positivity
  apply (div_lt_iff₀ hden).2
  calc
    ((G.interedges A B).card : ℝ) <
        (A.card : ℝ) * (c * (B.card : ℝ)) := hsum
    _ = c * ((A.card : ℝ) * (B.card : ℝ)) := by ring

noncomputable def edgeBad (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (c : ℝ) : Finset V :=
  A.filter fun x ↦ ((B.filter (G.Adj x)).card : ℝ) < c * B.card

lemma edgeBad_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (c : ℝ) : edgeBad G A B c ⊆ A := by
  exact Finset.filter_subset _ _

lemma edgeBad_card_lt
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B A₀ B₀ : Finset V} {ε d : ℝ}
    (hε : 0 < ε)
    (hreg : IsRegularPair G ε A₀ B₀)
    (hA₀ne : A₀.Nonempty) (hB₀ne : B₀.Nonempty)
    (hA : A ⊆ A₀) (hB : B ⊆ B₀)
    (hBlarge : ε * (B₀.card : ℝ) ≤ B.card)
    (hdensity : d ≤ graphDensity G A₀ B₀) :
    ((edgeBad G A B (d - ε)).card : ℝ) < ε * A₀.card := by
  classical
  by_contra hnot
  have hlarge : ε * (A₀.card : ℝ) ≤ (edgeBad G A B (d - ε)).card :=
    le_of_not_gt hnot
  have hBne : B.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.card_empty, Nat.cast_zero] at hBlarge
    have : 0 < ε * (B₀.card : ℝ) := mul_pos hε (by exact_mod_cast hB₀ne.card_pos)
    linarith
  have hbadne : (edgeBad G A B (d - ε)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.card_empty, Nat.cast_zero] at hlarge
    have hA₀pos : 0 < (A₀.card : ℝ) := by exact_mod_cast hA₀ne.card_pos
    nlinarith
  have hbadDensity : graphDensity G (edgeBad G A B (d - ε)) B < d - ε := by
    apply graphDensity_lt_of_pointwise_lt G hbadne hBne
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hregular := hreg ((edgeBad_subset G A B (d - ε)).trans hA) hB hlarge hBlarge
  have habs : graphDensity G A₀ B₀ -
      graphDensity G (edgeBad G A B (d - ε)) B ≤ ε := by
    calc
      graphDensity G A₀ B₀ - graphDensity G (edgeBad G A B (d - ε)) B ≤
          |graphDensity G (edgeBad G A B (d - ε)) B - graphDensity G A₀ B₀| := by
            rw [abs_sub_comm]
            exact le_abs_self _
      _ ≤ ε := hregular
  linarith

lemma graphDensity_add_compl
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty)
    (hdisj : Disjoint A B) :
    graphDensity G A B + graphDensity Gᶜ A B = 1 := by
  unfold graphDensity
  norm_cast
  exact G.edgeDensity_add_edgeDensity_compl hA hB hdisj

lemma isRegularPair_compl
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {ε : ℝ} (hε : 0 < ε)
    (hA : A.Nonempty) (hB : B.Nonempty) (hdisj : Disjoint A B)
    (hreg : IsRegularPair G ε A B) :
    IsRegularPair Gᶜ ε A B := by
  intro A' hA' B' hB' hAlarge hBlarge
  have hA'ne : A'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.card_empty, Nat.cast_zero] at hAlarge
    have hApos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
    nlinarith
  have hB'ne : B'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.card_empty, Nat.cast_zero] at hBlarge
    have hBpos : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
    nlinarith
  have hdisj' : Disjoint A' B' := hdisj.mono hA' hB'
  have hparent := graphDensity_add_compl G hA hB hdisj
  have hchild := graphDensity_add_compl G hA'ne hB'ne hdisj'
  have h := hreg hA' hB' hAlarge hBlarge
  rw [show graphDensity Gᶜ A' B' - graphDensity Gᶜ A B =
      -(graphDensity G A' B' - graphDensity G A B) by linarith]
  simpa only [abs_neg] using h

noncomputable def desiredGraph (G : SimpleGraph V) (p : Prop) : SimpleGraph V := by
  classical
  exact if p then G else Gᶜ

noncomputable def desiredBad {f : ℕ} (G : SimpleGraph V)
    (H : SimpleGraph (Fin f)) (i j : Fin f) (A B : Finset V) (c : ℝ) : Finset V := by
  classical
  exact A.filter fun x ↦
    ((B.filter fun y ↦ (desiredGraph G (H.Adj i j)).Adj x y).card : ℝ) <
      c * B.card

lemma desiredGraph_adj_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : Prop) {x y : V} (hxy : x ≠ y) :
    (desiredGraph G p).Adj x y ↔ (p ↔ G.Adj x y) := by
  classical
  by_cases hp : p
  · simp [desiredGraph, hp]
  · simp [desiredGraph, hp, hxy]

lemma desiredBad_card_lt
    {f : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin f)) [DecidableRel H.Adj] {ε d : ℝ}
    (C : InducedEmbeddingConfiguration G H ε d)
    (hε : 0 < ε) {i j : Fin f} (hij : i ≠ j)
    {A B : Finset V} (hA : A ⊆ C.parts i) (hB : B ⊆ C.parts j)
    (hBlarge : ε * ((C.parts j).card : ℝ) ≤ B.card) :
    ((desiredBad G H i j A B (d - ε)).card : ℝ) <
      ε * (C.parts i).card := by
  classical
  by_cases hadj : H.Adj i j
  · simpa [desiredBad, desiredGraph, hadj, edgeBad] using
      edgeBad_card_lt G hε (C.regular hij) (C.parts_nonempty i)
        (C.parts_nonempty j) hA hB hBlarge (C.edge_density hadj)
  · have hdisj := C.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij
    have hregc : IsRegularPair Gᶜ ε (C.parts i) (C.parts j) :=
      isRegularPair_compl G hε (C.parts_nonempty i) (C.parts_nonempty j)
        hdisj (C.regular hij)
    have hsum := graphDensity_add_compl G (C.parts_nonempty i)
      (C.parts_nonempty j) hdisj
    have hdensc : d ≤ graphDensity Gᶜ (C.parts i) (C.parts j) := by
      have := C.nonedge_density hij hadj
      linarith
    simpa [desiredBad, desiredGraph, hadj, edgeBad] using
      edgeBad_card_lt Gᶜ hε hregc (C.parts_nonempty i)
        (C.parts_nonempty j) hA hB hBlarge hdensc

abbrev Prefix (f n : ℕ) := {i : Fin f // i.val < n}

noncomputable def candidates {f n : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] (H : SimpleGraph (Fin f)) {ε d : ℝ}
    (C : InducedEmbeddingConfiguration G H ε d)
    (map : Prefix f n → V) (j : Fin f) : Finset V := by
  classical
  exact (C.parts j).filter fun y ↦
    ∀ i : Prefix f n, (desiredGraph G (H.Adj i.1 j)).Adj (map i) y

def IsPartialEmbedding {f n : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] (H : SimpleGraph (Fin f)) {ε d α : ℝ}
    (C : InducedEmbeddingConfiguration G H ε d)
    (map : Prefix f n → V) : Prop :=
  (∀ i, map i ∈ C.parts i.1) ∧
  (∀ i j, i.1.val < j.1.val →
    (desiredGraph G (H.Adj i.1 j.1)).Adj (map i) (map j)) ∧
  (∀ j : Fin f, n ≤ j.val →
    α ^ n * ((C.parts j).card : ℝ) ≤ (candidates G H C map j).card)

noncomputable def extendMap {f n : ℕ} (map : Prefix f n → V) (x : V) :
    Prefix f (n + 1) → V := by
  classical
  intro i
  exact if h : i.1.val < n then map ⟨i.1, h⟩ else x

@[simp]
lemma extendMap_old {f n : ℕ} (map : Prefix f n → V) (x : V)
    (i : Prefix f n) :
    extendMap map x ⟨i.1, Nat.lt_succ_of_lt i.2⟩ = map i := by
  simp [extendMap, i.2]

@[simp]
lemma extendMap_last {f n : ℕ} (hn : n < f) (map : Prefix f n → V) (x : V) :
    extendMap map x ⟨⟨n, hn⟩, Nat.lt_succ_self n⟩ = x := by
  simp [extendMap]

noncomputable def restrictCandidate {f : ℕ} (G : SimpleGraph V)
    (H : SimpleGraph (Fin f)) (i j : Fin f) (x : V) (B : Finset V) : Finset V := by
  classical
  exact B.filter fun y ↦ (desiredGraph G (H.Adj i j)).Adj x y

lemma candidates_succ {f n : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] (H : SimpleGraph (Fin f)) {ε d : ℝ}
    (C : InducedEmbeddingConfiguration G H ε d)
    (hn : n < f) (map : Prefix f n → V) (x : V) (j : Fin f) :
    candidates G H C (extendMap map x) j =
      restrictCandidate G H ⟨n, hn⟩ j x (candidates G H C map j) := by
  classical
  ext y
  simp only [candidates, restrictCandidate, Finset.mem_filter]
  constructor
  · rintro ⟨hy, hall⟩
    refine ⟨⟨hy, ?_⟩, ?_⟩
    · intro i
      have hi := hall ⟨i.1, Nat.lt_succ_of_lt i.2⟩
      simpa using hi
    · have hi := hall ⟨⟨n, hn⟩, Nat.lt_succ_self n⟩
      simpa using hi
  · rintro ⟨⟨hy, hold⟩, hnew⟩
    refine ⟨hy, ?_⟩
    intro i
    by_cases hi : i.1.val < n
    · have := hold ⟨i.1, hi⟩
      simpa [extendMap, hi] using this
    · have hin : i.1.val = n := by omega
      have hiEq : i = ⟨⟨n, hn⟩, Nat.lt_succ_self n⟩ := by
        apply Subtype.ext
        exact Fin.ext hin
      subst i
      simpa using hnew

theorem exists_partialEmbedding
    {f k n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin f)) [DecidableRel H.Adj]
    {ε d α : ℝ} (C : InducedEmbeddingConfiguration G H ε d)
    (hε : 0 < ε) (hα : 0 < α) (hα1 : α ≤ 1)
    (hαd : α + ε ≤ d) (hbudget : (k : ℝ) * ε < α ^ k)
    (hfk : f ≤ k) (hnf : n ≤ f) :
    ∃ map : Prefix f n → V, IsPartialEmbedding G H C map (α := α) := by
  classical
  induction n with
  | zero =>
      let map : Prefix f 0 → V := fun i ↦ (Nat.not_lt_zero _ i.2).elim
      refine ⟨map, ?_, ?_, ?_⟩
      · intro i
        exact (Nat.not_lt_zero _ i.2).elim
      · intro i
        exact (Nat.not_lt_zero _ i.2).elim
      · intro j _
        simp [candidates, map]
  | succ n ih =>
      have hnlt : n < f := Nat.lt_of_succ_le hnf
      obtain ⟨map, hmem, hrel, hlarge⟩ := ih (Nat.le_of_succ_le hnf)
      let idx : Fin f := ⟨n, hnlt⟩
      let current : Finset V := candidates G H C map idx
      let future : Finset (Fin f) := Finset.univ.filter fun j ↦ n < j.val
      let bad : Fin f → Finset V := fun j ↦
        desiredBad G H idx j current (candidates G H C map j) (d - ε)
      let allBad : Finset V := future.biUnion bad
      have hkpos : 0 < k := lt_of_lt_of_le (Nat.zero_lt_of_lt hnlt) hfk
      have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
      have hεk : ε < α ^ k := by
        calc
          ε ≤ (k : ℝ) * ε := by nlinarith
          _ < α ^ k := hbudget
      have hnk : n ≤ k := (Nat.le_of_lt hnlt).trans hfk
      have hpownk : α ^ k ≤ α ^ n :=
        pow_le_pow_of_le_one hα.le hα1 hnk
      have hεn : ε ≤ α ^ n := (hεk.trans_le hpownk).le
      have hcurrent_subset : current ⊆ C.parts idx := by
        exact Finset.filter_subset _ _
      have hbad (j : Fin f) (hj : j ∈ future) :
          ((bad j).card : ℝ) < ε * (C.parts idx).card := by
        have hnj : n < j.val := (Finset.mem_filter.mp hj).2
        have hidxj : idx ≠ j := by
          intro heq
          have := congrArg Fin.val heq
          dsimp [idx] at this
          omega
        have hBj : ε * ((C.parts j).card : ℝ) ≤
            (candidates G H C map j).card := by
          calc
            ε * ((C.parts j).card : ℝ) ≤
                α ^ n * ((C.parts j).card : ℝ) := by gcongr
            _ ≤ (candidates G H C map j).card := hlarge j (Nat.le_of_lt hnj)
        exact desiredBad_card_lt G H C hε hidxj hcurrent_subset
          (Finset.filter_subset _ _) hBj
      have hfuture_card : future.card ≤ k := by
        calc
          future.card ≤ Fintype.card (Fin f) := Finset.card_le_univ _
          _ = f := Fintype.card_fin f
          _ ≤ k := hfk
      have hpartpos : 0 < ((C.parts idx).card : ℝ) := by
        exact_mod_cast (C.parts_nonempty idx).card_pos
      have hallBad_lt : (allBad.card : ℝ) < (current.card : ℝ) := by
        calc
          (allBad.card : ℝ) ≤
              ((∑ j ∈ future, (bad j).card : ℕ) : ℝ) := by
                exact_mod_cast Finset.card_biUnion_le
          _ = ∑ j ∈ future, ((bad j).card : ℝ) := by push_cast; rfl
          _ ≤ ∑ _j ∈ future, ε * ((C.parts idx).card : ℝ) := by
            exact Finset.sum_le_sum fun j hj ↦ (hbad j hj).le
          _ = (future.card : ℝ) * (ε * ((C.parts idx).card : ℝ)) := by simp
          _ ≤ (k : ℝ) * (ε * ((C.parts idx).card : ℝ)) := by
            gcongr
          _ = ((k : ℝ) * ε) * ((C.parts idx).card : ℝ) := by ring
          _ < α ^ k * ((C.parts idx).card : ℝ) := by gcongr
          _ ≤ α ^ n * ((C.parts idx).card : ℝ) := by gcongr
          _ ≤ (current.card : ℝ) := hlarge idx (by simp [idx])
      have hallBad_nat : allBad.card < current.card := by exact_mod_cast hallBad_lt
      obtain ⟨x, hxcurrent, hxnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hallBad_nat
      refine ⟨extendMap map x, ?_, ?_, ?_⟩
      · intro i
        by_cases hi : i.1.val < n
        · have := hmem ⟨i.1, hi⟩
          simpa [extendMap, hi] using this
        · have hin : i.1.val = n := by omega
          have hiEq : i = ⟨idx, Nat.lt_succ_self n⟩ := by
            apply Subtype.ext
            exact Fin.ext hin
          subst i
          have := (Finset.mem_filter.mp hxcurrent).1
          simpa [idx] using this
      · intro i j hij
        by_cases hj : j.1.val < n
        · have hi : i.1.val < n := hij.trans hj
          have := hrel ⟨i.1, hi⟩ ⟨j.1, hj⟩ hij
          simpa [extendMap, hi, hj] using this
        · have hjn : j.1.val = n := by omega
          have hi : i.1.val < n := by omega
          have hjEq : j = ⟨idx, Nat.lt_succ_self n⟩ := by
            apply Subtype.ext
            exact Fin.ext hjn
          subst j
          have hxall := (Finset.mem_filter.mp hxcurrent).2 ⟨i.1, hi⟩
          simpa [extendMap, hi, idx] using hxall
      · intro j hj
        have hnj : n < j.val := by omega
        have hjfuture : j ∈ future := by simp [future, hnj]
        have hxnotbad : x ∉ bad j := by
          intro hxbad
          exact hxnot (Finset.mem_biUnion.mpr ⟨j, hjfuture, hxbad⟩)
        have hdegree : (d - ε) * ((candidates G H C map j).card : ℝ) ≤
            (restrictCandidate G H idx j x (candidates G H C map j)).card := by
          have hxnotlt : ¬(((restrictCandidate G H idx j x
              (candidates G H C map j)).card : ℝ) <
                (d - ε) * (candidates G H C map j).card) := by
            simpa [bad, desiredBad, restrictCandidate, hxcurrent] using hxnotbad
          exact le_of_not_gt hxnotlt
        rw [candidates_succ G H C hnlt map x j]
        have hαle : α ≤ d - ε := by linarith
        calc
          α ^ (n + 1) * ((C.parts j).card : ℝ) =
              α * (α ^ n * ((C.parts j).card : ℝ)) := by rw [pow_succ]; ring
          _ ≤ α * ((candidates G H C map j).card : ℝ) := by
            gcongr
            exact hlarge j (Nat.le_of_lt hnj)
          _ ≤ (d - ε) * ((candidates G H C map j).card : ℝ) := by gcongr
          _ ≤ (restrictCandidate G H idx j x
              (candidates G H C map j)).card := hdegree

theorem inducedEmbedding_of_tolerance
    {f k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin f)) [DecidableRel H.Adj]
    {ε d α : ℝ} (C : InducedEmbeddingConfiguration G H ε d)
    (hε : 0 < ε) (hα : 0 < α) (hα1 : α ≤ 1)
    (hαd : α + ε ≤ d) (hbudget : (k : ℝ) * ε < α ^ k)
    (hfk : f ≤ k) : InducedEmbeds H G := by
  classical
  obtain ⟨map, hmem, hrel, _⟩ :=
    exists_partialEmbedding G H C hε hα hα1 hαd hbudget hfk (le_refl f)
  let φ : Fin f → V := fun i ↦ map ⟨i, i.isLt⟩
  have hφmem (i : Fin f) : φ i ∈ C.parts i := hmem ⟨i, i.isLt⟩
  have hφinj : Function.Injective φ := by
    intro i j hij
    by_contra hne
    have hdisj := C.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hne
    exact (Finset.disjoint_left.mp hdisj (hφmem i)) (by simpa [hij] using hφmem j)
  refine ⟨{
    toFun := φ
    inj' := hφinj
    map_rel_iff' := ?_ }⟩
  intro i j
  change G.Adj (φ i) (φ j) ↔ H.Adj i j
  by_cases hij : i = j
  · subst j
    simp
  · rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hdes := hrel ⟨i, i.isLt⟩ ⟨j, j.isLt⟩ hijlt
      exact ((desiredGraph_adj_iff G (H.Adj i j) (hφinj.ne hij)).mp hdes).symm
    · have hdes := (hrel ⟨j, j.isLt⟩ ⟨i, i.isLt⟩ hjilt).symm
      have hiff := (desiredGraph_adj_iff G (H.Adj j i) (hφinj.ne hij)).mp hdes
      simpa only [H.adj_comm] using hiff.symm

/-- A uniform candidate-family induced-embedding tolerance.

The tolerance depends only on the density reserve `d` and the source-order
bound `k`, never on the number or size of unused ambient clusters.  This is
the locally proved embedding step used in paper Lemma `lemma:type-lemma`;
it introduces no external assumption. -/
theorem exists_inducedEmbedding_tolerance (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1)
    (k : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (f : ℕ), f ≤ k →
        ∀ {W : Type*} [Fintype W] [DecidableEq W]
          (G : SimpleGraph W) [DecidableRel G.Adj]
          (H : SimpleGraph (Fin f)) [DecidableRel H.Adj],
          InducedEmbeddingConfiguration G H ε d → InducedEmbeds H G := by
  let α : ℝ := d / 2
  let bound : ℝ := min α (α ^ k / ((k : ℝ) + 1))
  let ε : ℝ := bound / 2
  have hα : 0 < α := by dsimp [α]; linarith
  have hα1 : α ≤ 1 := by dsimp [α]; linarith
  have hkden : 0 < (k : ℝ) + 1 := by positivity
  have hfrac : 0 < α ^ k / ((k : ℝ) + 1) := div_pos (pow_pos hα _) hkden
  have hbound : 0 < bound := by
    simpa only [bound, lt_min_iff] using And.intro hα hfrac
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεltBound : ε < bound := by dsimp [ε]; linarith
  have hεltα : ε < α := hεltBound.trans_le (min_le_left _ _)
  have hεltFrac : ε < α ^ k / ((k : ℝ) + 1) :=
    hεltBound.trans_le (min_le_right _ _)
  have hαd : α + ε ≤ d := by
    dsimp [α] at hεltα ⊢
    linarith
  have hbudget : (k : ℝ) * ε < α ^ k := by
    have hscaled := mul_lt_mul_of_pos_left hεltFrac hkden
    have hcancel : ((k : ℝ) + 1) * (α ^ k / ((k : ℝ) + 1)) = α ^ k := by
      field_simp
    have hupper : ((k : ℝ) + 1) * ε < α ^ k := by
      rw [hcancel] at hscaled
      exact hscaled
    calc
      (k : ℝ) * ε < ((k : ℝ) + 1) * ε := by nlinarith
      _ < α ^ k := hupper
  refine ⟨ε, hε, ?_⟩
  intro f hfk W _ _ G _ H _ C
  exact inducedEmbedding_of_tolerance G H C hε hα hα1 hαd hbudget hfk

end InducedStars.Regularity
