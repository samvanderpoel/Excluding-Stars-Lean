import InducedStars.Structure.Subcritical.RetainedKeyGeometry
import InducedStars.Structure.Subcritical.RetainedRepairCost

/-!
# One globally minimizing completion for a fixed retained key and remainder

The auxiliary completion depends on K and the entire induced graph
H on its complement, not on retained edges or on a root/row profile. The old
canonical selector is unchanged. Global minimality follows from the exact
cost split, not from an assumed tie-breaking property of that selector.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- All ordered completions of the specified retained data. Compatibility
is not imposed here: it follows from the minimizing geometry when needed. -/
def subcriticalRetainedKeyCompletions (K : SubcriticalRetainedKey k V)
    (eta : ℝ) (R₀ : ℕ) : Set (SubcriticalDivision k V) :=
  {D | D.IsOrderedByCutoff R₀ ∧ retainedKey D eta R₀ = K}

/-- Minimize only the remainder term on the fixed-key completion family.
No ambient graph or profile is an argument of this definition. -/
def subcriticalFixedRemainderCompletion (K : SubcriticalRetainedKey k V)
    (eta : ℝ) (R₀ : ℕ) (H : SimpleGraph {v : V // v ∈ K.remainder})
    (hK : (subcriticalRetainedKeyCompletions K eta R₀).Nonempty) :
    SubcriticalDivision k V :=
  Function.argminOn (subcriticalRemainderRepairCost K.remainder H)
    (subcriticalRetainedKeyCompletions K eta R₀) hK

theorem subcriticalFixedRemainderCompletion_mem
    (K : SubcriticalRetainedKey k V) (eta : ℝ) (R₀ : ℕ)
    (H : SimpleGraph {v : V // v ∈ K.remainder})
    (hK : (subcriticalRetainedKeyCompletions K eta R₀).Nonempty) :
    subcriticalFixedRemainderCompletion K eta R₀ H hK ∈
      subcriticalRetainedKeyCompletions K eta R₀ :=
  Function.argminOn_mem _ _ _

theorem subcriticalFixedRemainderCompletion_remainder_minimal
    (K : SubcriticalRetainedKey k V) (eta : ℝ) (R₀ : ℕ)
    (H : SimpleGraph {v : V // v ∈ K.remainder})
    (hK : (subcriticalRetainedKeyCompletions K eta R₀).Nonempty)
    (D : SubcriticalDivision k V)
    (hD : D ∈ subcriticalRetainedKeyCompletions K eta R₀) :
    subcriticalRemainderRepairCost K.remainder H
        (subcriticalFixedRemainderCompletion K eta R₀ H hK) ≤
      subcriticalRemainderRepairCost K.remainder H D :=
  Function.argminOn_le _ _ hD

/-- Full cost comparison with every completion of the same key. This is
valid for every ambient G inducing H, regardless of its retained edges. -/
theorem subcriticalFixedRemainderCompletion_cost_le
    (K : SubcriticalRetainedKey k V) (eta : ℝ) (R₀ : ℕ)
    (H : SimpleGraph {v : V // v ∈ K.remainder})
    (hK : (subcriticalRetainedKeyCompletions K eta R₀).Nonempty)
    (G : SimpleGraph V) (hH : G.induce (K.remainder : Set V) = H)
    (D : SubcriticalDivision k V)
    (hD : D ∈ subcriticalRetainedKeyCompletions K eta R₀) :
    subcriticalDefectCost G (subcriticalFixedRemainderCompletion K eta R₀ H hK) ≤
      subcriticalDefectCost G D := by
  let E := subcriticalFixedRemainderCompletion K eta R₀ H hK
  have hE := subcriticalFixedRemainderCompletion_mem K eta R₀ H hK
  have heKey : retainedKey E eta R₀ = K := hE.2
  have hdKey : retainedKey D eta R₀ = K := hD.2
  have heS : K.remainder = E.nonretainedVertices eta R₀ := by
    rw [← heKey, retainedKey_remainder]
  have hdS : K.remainder = D.nonretainedVertices eta R₀ := by
    rw [← hdKey, retainedKey_remainder]
  have hcostE := subcriticalDefectCost_eq_retained_add_fixedRemainder
    G E eta R₀ K.remainder heS H hH
  have hcostD := subcriticalDefectCost_eq_retained_add_fixedRemainder
    G D eta R₀ K.remainder hdS H hH
  have hincident : subcriticalRetainedIncidentCost G E eta R₀ =
      subcriticalRetainedIncidentCost G D eta R₀ := by
    unfold subcriticalRetainedIncidentCost
    rw [subcriticalRetainedIncidentDefectGraph_eq_of_retainedKey_eq G
      (heKey.trans hdKey.symm)]
  rw [hcostE, hcostD, hincident]
  exact Nat.add_le_add_left
    (subcriticalFixedRemainderCompletion_remainder_minimal K eta R₀ H hK D hD) _

/-- If any completion with this retained key is a global minimum for G,
the fixed-(K,H) completion is a global minimum as well. -/
theorem subcriticalFixedRemainderCompletion_global_minimal
    (K : SubcriticalRetainedKey k V) (eta : ℝ) (R₀ : ℕ)
    (H : SimpleGraph {v : V // v ∈ K.remainder})
    (hK : (subcriticalRetainedKeyCompletions K eta R₀).Nonempty)
    (G : SimpleGraph V) (hH : G.induce (K.remainder : Set V) = H)
    (D : SubcriticalDivision k V)
    (hD : D ∈ subcriticalRetainedKeyCompletions K eta R₀)
    (hmin : ∀ E : SubcriticalDivision k V,
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E) :
    ∀ E : SubcriticalDivision k V,
      subcriticalDefectCost G (subcriticalFixedRemainderCompletion K eta R₀ H hK) ≤
        subcriticalDefectCost G E :=
  fun E ↦ (subcriticalFixedRemainderCompletion_cost_le K eta R₀ H hK G hH D hD).trans
    (hmin E)

/-- The fixed completion and the original global minimum have exactly the
same cost. This theorem does not identify the divisions themselves. -/
theorem subcriticalFixedRemainderCompletion_cost_eq
    (K : SubcriticalRetainedKey k V) (eta : ℝ) (R₀ : ℕ)
    (H : SimpleGraph {v : V // v ∈ K.remainder})
    (hK : (subcriticalRetainedKeyCompletions K eta R₀).Nonempty)
    (G : SimpleGraph V) (hH : G.induce (K.remainder : Set V) = H)
    (D : SubcriticalDivision k V)
    (hD : D ∈ subcriticalRetainedKeyCompletions K eta R₀)
    (hmin : ∀ E : SubcriticalDivision k V,
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E) :
    subcriticalDefectCost G (subcriticalFixedRemainderCompletion K eta R₀ H hK) =
      subcriticalDefectCost G D :=
  Nat.le_antisymm
    (subcriticalFixedRemainderCompletion_cost_le K eta R₀ H hK G hH D hD) (hmin _)

/-- Group by the original selector's retained key, not by a replacement
selector. This family contains each original graph exactly once. -/
def subcriticalCanonicalRetainedKeyGraphFinset
    (F : Finset (SimpleGraph V)) (K : SubcriticalRetainedKey k V)
    (eta : ℝ) (R₀ : ℕ) (hk : 3 ≤ k) (hn : k - 1 ≤ Fintype.card V) :
    Finset (SimpleGraph V) :=
  F.filter fun G ↦ retainedKey (canonicalSubcriticalDivision G R₀ hk hn) eta R₀ = K

/-- Fix the entire induced graph on the key's complementary vertex set
before the profile argument is run. -/
def subcriticalFixedKeyRemainderGraphFinset
    (F : Finset (SimpleGraph V)) (K : SubcriticalRetainedKey k V)
    (eta : ℝ) (R₀ : ℕ) (hk : 3 ≤ k) (hn : k - 1 ≤ Fintype.card V)
    (H : SimpleGraph {v : V // v ∈ K.remainder}) : Finset (SimpleGraph V) :=
  (subcriticalCanonicalRetainedKeyGraphFinset F K eta R₀ hk hn).filter fun G ↦
    G.induce (K.remainder : Set V) = H

@[simp] theorem mem_subcriticalCanonicalRetainedKeyGraphFinset
    (F : Finset (SimpleGraph V)) (K : SubcriticalRetainedKey k V)
    (eta : ℝ) (R₀ : ℕ) (hk : 3 ≤ k) (hn : k - 1 ≤ Fintype.card V)
    (G : SimpleGraph V) :
    G ∈ subcriticalCanonicalRetainedKeyGraphFinset F K eta R₀ hk hn ↔
      G ∈ F ∧ retainedKey (canonicalSubcriticalDivision G R₀ hk hn) eta R₀ = K := by
  simp [subcriticalCanonicalRetainedKeyGraphFinset]

@[simp] theorem mem_subcriticalFixedKeyRemainderGraphFinset
    (F : Finset (SimpleGraph V)) (K : SubcriticalRetainedKey k V)
    (eta : ℝ) (R₀ : ℕ) (hk : 3 ≤ k) (hn : k - 1 ≤ Fintype.card V)
    (H : SimpleGraph {v : V // v ∈ K.remainder}) (G : SimpleGraph V) :
    G ∈ subcriticalFixedKeyRemainderGraphFinset F K eta R₀ hk hn H ↔
      G ∈ F ∧ retainedKey (canonicalSubcriticalDivision G R₀ hk hn) eta R₀ = K ∧
        G.induce (K.remainder : Set V) = H := by
  simp [subcriticalFixedKeyRemainderGraphFinset, and_assoc]

theorem subcriticalFixedKeyRemainder_completion_global_minimal
    (F : Finset (SimpleGraph V)) (K : SubcriticalRetainedKey k V)
    (eta : ℝ) (R₀ : ℕ) (hk : 3 ≤ k) (hn : k - 1 ≤ Fintype.card V)
    (H : SimpleGraph {v : V // v ∈ K.remainder})
    (hK : (subcriticalRetainedKeyCompletions K eta R₀).Nonempty)
    {G : SimpleGraph V}
    (hG : G ∈ subcriticalFixedKeyRemainderGraphFinset F K eta R₀ hk hn H) :
    ∀ E : SubcriticalDivision k V,
      subcriticalDefectCost G (subcriticalFixedRemainderCompletion K eta R₀ H hK) ≤
        subcriticalDefectCost G E := by
  obtain ⟨_, hkey, hH⟩ := (mem_subcriticalFixedKeyRemainderGraphFinset
    F K eta R₀ hk hn H G).mp hG
  exact subcriticalFixedRemainderCompletion_global_minimal K eta R₀ H hK G hH
    (canonicalSubcriticalDivision G R₀ hk hn)
    ⟨canonicalSubcriticalDivision_isOrdered G R₀ hk hn, hkey⟩
    (canonicalSubcriticalDivision_minimal G R₀ hk hn)

/-- The complement is transported by the identity on ambient vertices. -/
def retainedKeyRemainderEquiv (K : SubcriticalRetainedKey k V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (hD : retainedKey D eta R₀ = K) :
    {v : V // v ∈ D.nonretainedVertices eta R₀} ≃ {v : V // v ∈ K.remainder} :=
  Equiv.setCongr (by rw [← hD, retainedKey_remainder])

/-- The same fixed remainder, with the subtype expected by the old profile
APIs. This relabeling adds no choices or multiplicity. -/
def retainedKeyRemainderTransport (K : SubcriticalRetainedKey k V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (hD : retainedKey D eta R₀ = K)
    (H : SimpleGraph {v : V // v ∈ K.remainder}) : SubcriticalRemainderGraph D eta R₀ :=
  H.comap (retainedKeyRemainderEquiv K D eta R₀ hD)

theorem retainedKeyRemainderTransport_card (K : SubcriticalRetainedKey k V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (hD : retainedKey D eta R₀ = K)
    (H : SimpleGraph {v : V // v ∈ K.remainder}) :
    (finiteGraphEdges (retainedKeyRemainderTransport K D eta R₀ hD H)).card =
      (finiteGraphEdges H).card := by
  have hleft : finiteGraphEdges (retainedKeyRemainderTransport K D eta R₀ hD H) =
      (retainedKeyRemainderTransport K D eta R₀ hD H).edgeFinset := by
    ext z
    simp
  have hright : finiteGraphEdges H = H.edgeFinset := by
    ext z
    simp
  rw [hleft, hright]
  exact (SimpleGraph.Iso.comap (retainedKeyRemainderEquiv K D eta R₀ hD) H).card_edgeFinset_eq

theorem subcriticalRemainderGraph_eq_transport (K : SubcriticalRetainedKey k V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (hD : retainedKey D eta R₀ = K)
    (H : SimpleGraph {v : V // v ∈ K.remainder})
    (G : SimpleGraph V) (hH : G.induce (K.remainder : Set V) = H) :
    subcriticalRemainderGraph G D eta R₀ =
      retainedKeyRemainderTransport K D eta R₀ hD H := by
  subst H
  ext x y
  rfl

theorem subcriticalRetainedKeyCompletions_nonempty_of_mem
    (F : Finset (SimpleGraph V)) (K : SubcriticalRetainedKey k V)
    (eta : ℝ) (R₀ : ℕ) (hk : 3 ≤ k) (hn : k - 1 ≤ Fintype.card V)
    {G : SimpleGraph V}
    (hG : G ∈ subcriticalCanonicalRetainedKeyGraphFinset F K eta R₀ hk hn) :
    (subcriticalRetainedKeyCompletions K eta R₀).Nonempty := by
  exact ⟨canonicalSubcriticalDivision G R₀ hk hn,
    canonicalSubcriticalDivision_isOrdered G R₀ hk hn,
    ((mem_subcriticalCanonicalRetainedKeyGraphFinset F K eta R₀ hk hn G).mp hG).2⟩

theorem subcriticalCanonicalRetainedKeyGraphFinset_eq_biUnion_remainders
    (F : Finset (SimpleGraph V)) (K : SubcriticalRetainedKey k V)
    (eta : ℝ) (R₀ : ℕ) (hk : 3 ≤ k) (hn : k - 1 ≤ Fintype.card V) :
    subcriticalCanonicalRetainedKeyGraphFinset F K eta R₀ hk hn =
      Finset.univ.biUnion (subcriticalFixedKeyRemainderGraphFinset F K eta R₀ hk hn) := by
  ext G
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    mem_subcriticalCanonicalRetainedKeyGraphFinset, mem_subcriticalFixedKeyRemainderGraphFinset]
  exact ⟨fun h ↦ ⟨_, h.1, h.2, rfl⟩, fun ⟨_, h, hkey, _⟩ ↦ ⟨h, hkey⟩⟩

theorem subcriticalFixedKeyRemainderGraphFinset_disjoint
    (F : Finset (SimpleGraph V)) (K : SubcriticalRetainedKey k V)
    (eta : ℝ) (R₀ : ℕ) (hk : 3 ≤ k) (hn : k - 1 ≤ Fintype.card V)
    {H H' : SimpleGraph {v : V // v ∈ K.remainder}} (h : H ≠ H') :
    Disjoint (subcriticalFixedKeyRemainderGraphFinset F K eta R₀ hk hn H)
      (subcriticalFixedKeyRemainderGraphFinset F K eta R₀ hk hn H') := by
  apply Finset.disjoint_left.mpr
  intro G hG hG'
  exact h (((mem_subcriticalFixedKeyRemainderGraphFinset F K eta R₀ hk hn H G).mp hG).2.2.symm.trans
    ((mem_subcriticalFixedKeyRemainderGraphFinset F K eta R₀ hk hn H' G).mp hG').2.2)

/-- This is an exact disjoint partition, before any estimate is applied:
the graph H, rather than just its edge count, is summed exactly once. -/
theorem card_subcriticalCanonicalRetainedKeyGraphFinset_eq_sum_remainders
    (F : Finset (SimpleGraph V)) (K : SubcriticalRetainedKey k V)
    (eta : ℝ) (R₀ : ℕ) (hk : 3 ≤ k) (hn : k - 1 ≤ Fintype.card V) :
    (subcriticalCanonicalRetainedKeyGraphFinset F K eta R₀ hk hn).card =
      ∑ H : SimpleGraph {v : V // v ∈ K.remainder},
        (subcriticalFixedKeyRemainderGraphFinset F K eta R₀ hk hn H).card := by
  rw [subcriticalCanonicalRetainedKeyGraphFinset_eq_biUnion_remainders]
  exact Finset.card_biUnion (fun H _ H' _ h ↦
    subcriticalFixedKeyRemainderGraphFinset_disjoint F K eta R₀ hk hn h)

end InducedStars
