import InducedStars.Structure.Subcritical.CoreEmbedding
import InducedStars.Structure.Subcritical.CellAlignment
import Mathlib.Data.Finset.SymmDiff

/-!
# Matching one reference component to one whole division component

Paper: the component-matching argument in `lemma:WtoWtildeMetricsK1k`.
Large cell overlaps determine an injective edge-preserving map, and degree
saturation retains an actual core isomorphism.  The unmatched vertices
outside its entire component are controlled by one signed rectangle, not
by summing an unbounded family of small intersections.
-/

noncomputable section

open Finset
open scoped BigOperators Classical symmDiff

namespace InducedStars

open DenseGraph FiniteWeightedGraph

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

local instance componentAlignmentAdjDecidable (G : SimpleGraph V) : DecidableRel G.Adj :=
  Classical.decRel _

/-- Every neighbor of a vertex in a division part stays in that part's
component.  Active pairs need not carry any edges for this implication. -/
theorem subcritical_neighbor_mem_componentSupport_of_mem_part
    (D : SubcriticalDivision k V) (H : SimpleGraph V)
    (hH : IsSubcriticalRegularBlowupFor D H) (a : D.PartIndex)
    {x y : V} (hx : x ∈ D.part a) (hxy : H.Adj x y) :
    y ∈ D.componentSupport a.1 := by
  rcases hH.edge_allowed hxy with hs | ha
  · obtain ⟨b, hxb, hyb⟩ := hs
    have hab : a = b := D.mem_part_unique hx hxb
    subst b
    exact SubcriticalDivision.mem_componentSupport.mpr ⟨a.2, hyb⟩
  · obtain ⟨i, u, v, _, hxu, hyv⟩ := ha
    have hau : a = ⟨i, u⟩ := D.mem_part_unique hx hxu
    rw [hau]
    exact SubcriticalDivision.mem_componentSupport.mpr ⟨v, hyv⟩

/-- Disjoint cells cannot share an associated part if each has a large
overlap and every associated part has small spill. -/
theorem subcritical_cell_part_map_injective
    {ι : Type*} (D : SubcriticalDivision k V) (C : ι → Finset V)
    (f : ι → D.PartIndex) {m : ℝ}
    (hdisj : ∀ {u v}, u ≠ v → Disjoint (C u) (C v))
    (hoverlap : ∀ v, m ≤ ((C v ∩ D.part (f v)).card : ℝ))
    (hspill : ∀ v, ((D.part (f v) \ C v).card : ℝ) < m) :
    Function.Injective f := by
  intro u v huv
  by_contra hne
  have hsub : C u ∩ D.part (f u) ⊆ D.part (f v) \ C v := by
    intro x hx
    obtain ⟨hxC, hxP⟩ := Finset.mem_inter.mp hx
    refine Finset.mem_sdiff.mpr ⟨huv ▸ hxP, ?_⟩
    exact fun hxv ↦ Finset.disjoint_left.mp (hdisj hne) hxC hxv
  have hc : ((C u ∩ D.part (f u)).card : ℝ) ≤
      (D.part (f v) \ C v).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact (not_lt_of_ge ((hoverlap u).trans hc)) (hspill v)

/-- A positive reference rectangle between two matched cells forces the
corresponding distinct division parts to be an active pair. -/
theorem subcritical_activePart_of_matched_cell_edge
    (D : SubcriticalDivision k V) (H : SimpleGraph V)
    (hH : IsSubcriticalRegularBlowupFor D H) (R : FiniteWeightedGraph V)
    (S T : Finset V) (a b : D.PartIndex) {g m : ℝ}
    (hg : 0 < g) (hm : 0 < m) (hab : a ≠ b)
    (hS : m ≤ ((S ∩ D.part a).card : ℝ))
    (hT : m ≤ ((T ∩ D.part b).card : ℝ))
    (hR : ∀ x ∈ S, ∀ y ∈ T, g ≤ R.weight x y)
    (hcut : finiteLabeledCutDist (ofSimpleGraph H) R *
      (Fintype.card V : ℝ) ^ 2 < g * m ^ 2) : D.ActivePart a b := by
  by_contra hactive
  have hcut' : finiteLabeledCutDist R (ofSimpleGraph H) *
      (Fintype.card V : ℝ) ^ 2 < g * m ^ 2 := by
    simpa only [finiteLabeledCutDist_comm R (ofSimpleGraph H)] using hcut
  have hsmall := subcritical_card_lt_of_signed_rectangle R (ofSimpleGraph H)
    (S ∩ D.part a) (T ∩ D.part b) hg hm hS hcut' (by
      intro x hx y hy
      obtain ⟨hxS, hxP⟩ := Finset.mem_inter.mp hx
      obtain ⟨hyT, hyP⟩ := Finset.mem_inter.mp hy
      have hzero : ¬ H.Adj x y := by
        intro hxy
        rcases hH.edge_allowed hxy with hs | ha
        · exact hab ((D.samePart_iff_of_mem_parts hxP hyP).mp hs)
        · exact hactive ((D.activePair_iff_of_mem_parts hxP hyP).mp ha)
      simpa only [ofSimpleGraph_weight, ite_eq_right hzero, sub_zero] using hR x hxS y hyT)
  exact (not_lt_of_ge hT) hsmall

/-- The total part of a reference-one cell outside a matched division
component is small.  All those vertices are controlled simultaneously by
the same zero-versus-one rectangle. -/
theorem subcritical_cell_outside_component_lt
    (D : SubcriticalDivision k V) (H : SimpleGraph V)
    (hH : IsSubcriticalRegularBlowupFor D H) (R : FiniteWeightedGraph V)
    (C : Finset V) (a : D.PartIndex) {g m : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) (hm : 0 < m)
    (hoverlap : m ≤ ((C ∩ D.part a).card : ℝ))
    (hone : ∀ x ∈ C, ∀ y ∈ C, R.weight x y = 1)
    (hcut : finiteLabeledCutDist (ofSimpleGraph H) R *
      (Fintype.card V : ℝ) ^ 2 < g * m ^ 2) :
    ((C \ D.componentSupport a.1).card : ℝ) < m := by
  apply subcritical_card_lt_of_signed_rectangle R (ofSimpleGraph H)
    (C ∩ D.part a) (C \ D.componentSupport a.1) hg hm hoverlap
  · simpa only [finiteLabeledCutDist_comm R (ofSimpleGraph H)] using hcut
  · intro x hx y hy
    obtain ⟨hxC, hxP⟩ := Finset.mem_inter.mp hx
    obtain ⟨hyC, hyout⟩ := Finset.mem_sdiff.mp hy
    have hzero : ¬ H.Adj x y := fun hxy ↦ hyout
      (subcritical_neighbor_mem_componentSupport_of_mem_part D H hH a hxP hxy)
    simpa only [hone x hxC y hyC, ofSimpleGraph_weight, ite_eq_right hzero, sub_zero]
      using hg1

/-- Once the component isomorphism is known, the full cell remainder is
bounded by the aggregate outside-component error and one spill term for
each of its finitely many matched parts. -/
theorem subcritical_matched_component_cell_remainder_le
    (D : SubcriticalDivision k V) (Q : RegularBlockCore k)
    (C : Fin Q.order → Finset V) (i : Fin D.componentCount)
    (e : Q.graph ≃g (D.core i).graph) {m : ℝ}
    (hdisj : ∀ {u v}, u ≠ v → Disjoint (C u) (C v))
    (hspill : ∀ v, ((D.parts i (e v) \ C v).card : ℝ) < m)
    (hout : ∀ v, ((C v \ D.componentSupport i).card : ℝ) < m)
    (v : Fin Q.order) :
    ((C v \ D.parts i (e v)).card : ℝ) ≤ ((Q.order : ℝ) + 1) * m := by
  let U := Finset.univ.biUnion fun w : Fin Q.order ↦ D.parts i (e w) \ C w
  have hsub : C v \ D.parts i (e v) ⊆ (C v \ D.componentSupport i) ∪ U := by
    intro x hx
    obtain ⟨hxC, hxP⟩ := Finset.mem_sdiff.mp hx
    by_cases hxin : x ∈ D.componentSupport i
    · apply Finset.mem_union_right
      obtain ⟨j, hxj⟩ := SubcriticalDivision.mem_componentSupport.mp hxin
      have hne : v ≠ e.symm j := by
        intro hv
        apply hxP
        simpa only [hv, RelIso.apply_symm_apply] using hxj
      apply Finset.mem_biUnion.mpr
      refine ⟨e.symm j, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
      · simpa using hxj
      · exact fun hxw ↦ Finset.disjoint_left.mp (hdisj hne) hxC hxw
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxC, hxin⟩)
  have hsum : (U.card : ℝ) ≤ (Q.order : ℝ) * m := by
    calc
      _ ≤ ∑ w : Fin Q.order, ((D.parts i (e w) \ C w).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le :
          U.card ≤ ∑ w : Fin Q.order, (D.parts i (e w) \ C w).card)
      _ ≤ ∑ _w : Fin Q.order, m := Finset.sum_le_sum fun w _ ↦ (hspill w).le
      _ = _ := by simp
  have hcard : ((C v \ D.parts i (e v)).card : ℝ) ≤
      (C v \ D.componentSupport i).card + (U.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  nlinarith [hout v]

/-- Paper: one-reference-component alignment in
`lemma:WtoWtildeMetricsK1k`.  The output keeps a single actual core
isomorphism and two-sided errors for every matched cell. -/
theorem subcritical_exists_component_cell_alignment
    (hk : 3 ≤ k) (D : SubcriticalDivision k V)
    (H : SimpleGraph V) (hH : IsSubcriticalRegularBlowupFor D H)
    (R : FiniteWeightedGraph V) (Q : RegularBlockCore k)
    (C : Fin Q.order → Finset V)
    (hdisj : ∀ {u v}, u ≠ v → Disjoint (C u) (C v))
    {g m : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (hm : 0 < m)
    (hsize : ∀ v, 2 * (k - 1 : ℕ) * m ≤ (C v).card)
    (hone : ∀ v, ∀ x ∈ C v, ∀ y ∈ C v, R.weight x y = 1)
    (hout : ∀ v, ∀ x ∈ C v, ∀ y ∉ C v, R.weight x y ≤ 1 - g)
    (hadj : ∀ {u v}, Q.graph.Adj u v → ∀ x ∈ C u, ∀ y ∈ C v,
      g ≤ R.weight x y)
    (hcut : finiteLabeledCutDist (ofSimpleGraph H) R *
      (Fintype.card V : ℝ) ^ 2 < g * m ^ 2) :
    ∃ (i : Fin D.componentCount) (e : Q.graph ≃g (D.core i).graph),
      ∀ v,
        m ≤ ((C v ∩ D.parts i (e v)).card : ℝ) ∧
        ((D.parts i (e v) \ C v).card : ℝ) < m ∧
        ((C v \ D.parts i (e v)).card : ℝ) ≤ ((Q.order : ℝ) + 1) * m ∧
        ((D.parts i (e v) ∆ C v).card : ℝ) ≤ ((Q.order : ℝ) + 2) * m := by
  have hcut1 : finiteLabeledCutDist (ofSimpleGraph H) R *
      (Fintype.card V : ℝ) ^ 2 < m ^ 2 := by
    exact hcut.trans_le (mul_le_of_le_one_left (sq_nonneg m) hg1)
  choose f hf using fun v ↦ subcritical_exists_part_large_cell_overlap
    hk D H hH R (C v) hm (hsize v) (hone v) hcut1
  have hspill (v : Fin Q.order) : ((D.part (f v) \ C v).card : ℝ) < m :=
    subcritical_part_spill_lt_of_cell_overlap D H hH R (C v) (f v)
      hg hm (hf v) (hout v) hcut
  have hfinj : Function.Injective f :=
    subcritical_cell_part_map_injective D C f hdisj hf hspill
  have hactive {u v : Fin Q.order} (huv : Q.graph.Adj u v) :
      D.ActivePart (f u) (f v) :=
    subcritical_activePart_of_matched_cell_edge D H hH R (C u) (C v) (f u) (f v)
      hg hm (fun h ↦ huv.ne (hfinj h)) (hf u) (hf v) (hadj huv) hcut
  obtain ⟨i, e, he⟩ := D.exists_coreIso_of_injective_activePart_map Q f hfinj hactive
  have hf' (v : Fin Q.order) : m ≤ ((C v ∩ D.parts i (e v)).card : ℝ) := by
    change m ≤ ((C v ∩ D.part ⟨i, e v⟩).card : ℝ)
    rw [← he v]
    exact hf v
  have hspill' (v : Fin Q.order) : ((D.parts i (e v) \ C v).card : ℝ) < m := by
    change ((D.part ⟨i, e v⟩ \ C v).card : ℝ) < m
    rw [← he v]
    exact hspill v
  have hout' (v : Fin Q.order) :
      ((C v \ D.componentSupport i).card : ℝ) < m :=
    subcritical_cell_outside_component_lt D H hH R (C v) ⟨i, e v⟩
      hg hg1 hm (hf' v) (hone v) hcut
  refine ⟨i, e, fun v ↦ ⟨hf' v, hspill' v, ?_, ?_⟩⟩
  · exact subcritical_matched_component_cell_remainder_le D Q C i e hdisj hspill' hout' v
  · have hrem :=
      subcritical_matched_component_cell_remainder_le D Q C i e hdisj hspill' hout' v
    have hcard : ((D.parts i (e v) ∆ C v).card : ℝ) ≤
        (D.parts i (e v) \ C v).card + ((C v \ D.parts i (e v)).card : ℝ) := by
      rw [Finset.symmDiff_def]
      exact_mod_cast Finset.card_union_le (D.parts i (e v) \ C v) (C v \ D.parts i (e v))
    nlinarith [hspill' v]

end InducedStars
