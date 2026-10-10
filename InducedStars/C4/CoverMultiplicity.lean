import InducedStars.C4.SplitFibers
import Mathlib.Data.Finset.Option

/-!
# Polynomial multiplicity of ordered split covers

Relative to one split partition, each other clique part removes at most one
vertex and adds at most one vertex. Thus there are at most `(n + 1)^2`
ordered split partitions, including empty sides. This elementary finite
bound is the sufficient substitute explicitly requested in Final Goal §26;
it does not assert the source's sharper asymptotic uniqueness estimate.
-/

noncomputable section

open Finset Set

namespace InducedStars

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Every ordered division which displays this graph as split. -/
def c4SplitDivisions (G : SimpleGraph V) : Finset (C4Division V) := by
  classical
  exact Finset.univ.filter fun D ↦
    G.IsIndepSet (D.independentPart : Set V) ∧ G.IsClique (D.cliquePart : Set V)

@[simp] theorem mem_c4SplitDivisions {G : SimpleGraph V} {D : C4Division V} :
    D ∈ c4SplitDivisions G ↔
      G.IsIndepSet (D.independentPart : Set V) ∧ G.IsClique (D.cliquePart : Set V) := by
  classical
  simp [c4SplitDivisions]

/-- A difference of two clique parts is simultaneously a clique and an
independent set, so contains at most one vertex. -/
theorem c4SplitDivision_clique_sdiff_card_le_one {G : SimpleGraph V}
    {D E : C4Division V} (hD : D ∈ c4SplitDivisions G) (hE : E ∈ c4SplitDivisions G) :
    (D.cliquePart \ E.cliquePart).card ≤ 1 := by
  obtain ⟨hDA, hDB⟩ := mem_c4SplitDivisions.mp hD
  obtain ⟨hEA, hEB⟩ := mem_c4SplitDivisions.mp hE
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxD, hxE⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hyD, hyE⟩ := Finset.mem_sdiff.mp hy
  have hxA : x ∈ E.independentPart := by simpa using hxE
  have hyA : y ∈ E.independentPart := by simpa using hyE
  by_contra hne
  exact hEA hxA hyA hne (hDB hxD hyD hne)

private theorem exists_option_toFinset_of_card_le_one (S : Finset V) (hS : S.card ≤ 1) :
    ∃ o : Option V, o.toFinset = S := by
  rcases S.eq_empty_or_nonempty with hzero | ⟨v, hv⟩
  · exact ⟨none, by simpa using hzero.symm⟩
  · refine ⟨some v, ?_⟩
    ext w
    simp only [Option.toFinset_some, Finset.mem_singleton]
    exact ⟨fun h ↦ h ▸ hv, fun hw ↦ Finset.card_le_one.mp hS w hw v hv⟩

/-- Polynomial split-cover multiplicity with no density, nondegeneracy, or
asymptotic hypothesis. The encoding uses one optional removed clique vertex
and one optional added clique vertex. -/
theorem card_c4SplitDivisions_le (G : SimpleGraph V) :
    (c4SplitDivisions G).card ≤ (Fintype.card V + 1) ^ 2 := by
  classical
  rcases (c4SplitDivisions G).eq_empty_or_nonempty with hzero | ⟨D, hD⟩
  · simp [hzero]
  let decode : Option V × Option V → C4Division V := fun o ↦
    Finset.univ \ ((D.cliquePart \ o.1.toFinset) ∪ o.2.toFinset)
  have hsub : c4SplitDivisions G ⊆ Finset.univ.image decode := by
    intro E hE
    obtain ⟨removed, hremoved⟩ := exists_option_toFinset_of_card_le_one
      (D.cliquePart \ E.cliquePart) (c4SplitDivision_clique_sdiff_card_le_one hD hE)
    obtain ⟨added, hadded⟩ := exists_option_toFinset_of_card_le_one
      (E.cliquePart \ D.cliquePart) (c4SplitDivision_clique_sdiff_card_le_one hE hD)
    refine Finset.mem_image.mpr ⟨(removed, added), Finset.mem_univ _, ?_⟩
    dsimp [decode]
    rw [hremoved, hadded]
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
      C4Division.mem_cliquePart]
    change _ ↔ v ∈ E.independentPart
    tauto
  calc
    (c4SplitDivisions G).card ≤ (Finset.univ.image decode).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Option V × Option V)).card := Finset.card_image_le
    _ = (Fintype.card V + 1) ^ 2 := by simp [Fintype.card_prod, pow_two]

/-- Exact double counting of ordered partition/graph pairs. The global
split family itself is not equated with a sum which counts covers. -/
theorem sum_card_c4SplitFiber_eq_sum_splitDivisions (n m : ℕ) :
    (∑ D : C4Division (Fin n), (c4SplitFiber D m).card) =
      ∑ G ∈ splitGraphFinsetWithEdges n m, (c4SplitDivisions G).card := by
  classical
  have hsum : (∑ D : C4Division (Fin n), (c4SplitFiber D m).card) =
      ∑ G : SimpleGraph (Fin n),
        if (finiteGraphEdges G).card = m then (c4SplitDivisions G).card else 0 := by
    simp only [c4SplitFiber, c4SplitDivisions, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro G hG
    by_cases hm : (finiteGraphEdges G).card = m <;> simp [hm]
  rw [hsum]
  rw [show splitGraphFinsetWithEdges n m =
    Finset.univ.filter (fun G : SimpleGraph (Fin n) ↦
      DenseGraph.IsSplitGraph G ∧ (finiteGraphEdges G).card = m) by rfl,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro G hG
  by_cases hm : (finiteGraphEdges G).card = m
  · by_cases hs : DenseGraph.IsSplitGraph G
    · simp [hm, hs]
    · have hempty : c4SplitDivisions G = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro D hD
        obtain ⟨hA, hB⟩ := mem_c4SplitDivisions.mp hD
        exact hs ⟨⟨D.independentPart, D.cliquePart, D.disjoint, D.cover, hA, hB⟩⟩
      simp [hm, hs, hempty]
  · simp [hm]

/-- The exact split-fiber sum is at most the polynomial cover multiplicity
times the number of labeled split graphs with the same edge count. -/
theorem sum_card_c4SplitFiber_le (n m : ℕ) :
    (∑ D : C4Division (Fin n), (c4SplitFiber D m).card) ≤
      (n + 1) ^ 2 * splitGraphCountWithEdges n m := by
  rw [sum_card_c4SplitFiber_eq_sum_splitDivisions]
  calc
    ∑ G ∈ splitGraphFinsetWithEdges n m, (c4SplitDivisions G).card ≤
        ∑ _G ∈ splitGraphFinsetWithEdges n m, (n + 1) ^ 2 :=
      Finset.sum_le_sum fun G _ ↦ by simpa using card_c4SplitDivisions_le G
    _ = (n + 1) ^ 2 * splitGraphCountWithEdges n m := by
      simp [splitGraphCountWithEdges, Nat.mul_comm]

end InducedStars
