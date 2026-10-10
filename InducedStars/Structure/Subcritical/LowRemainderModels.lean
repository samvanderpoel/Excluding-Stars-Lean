import InducedStars.Structure.Subcritical.RetainedKeyModels
import InducedStars.Structure.Subcritical.RetainedKeyFamilies
import InducedStars.Structure.Subcritical.RetainedKeyNormalization

/-!
# Actual low-remainder clean model families

Paper: `lemma:sub-Wstar-sparse-lower-tail-K1k`. Each exact remainder
level is counted once per retained key. The upper family need not consist
of canonical graphs or lie in any chosen cut ball.
-/

noncomputable section
open Finset Set
open scoped Classical BigOperators
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta delta : ℝ} {R₀ m b : ℕ}

abbrev SubcriticalCleanLevelData (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) (b : ℕ) :=
  ↥(subcriticalCleanRemainderGraphFinset D eta R₀ b) ×
    (Σ v : ↥(retainedEdgeCountLevel D eta R₀ m delta (b : ℤ)), RetainedEdgeChoices v.val)

def SubcriticalCleanLevelData.graph (d : SubcriticalCleanLevelData D eta R₀ m delta b) :
    SimpleGraph V := subcriticalCleanGraph d.1.val d.2.2

theorem SubcriticalCleanLevelData.graph_injective :
    Function.Injective (SubcriticalCleanLevelData.graph
      (D := D) (eta := eta) (R₀ := R₀) (m := m) (delta := delta) (b := b)) := by
  rintro ⟨⟨H,hH⟩,⟨v,hv⟩,S⟩ ⟨⟨H',hH'⟩,⟨v',hv'⟩,S'⟩ h
  change subcriticalCleanGraph H S = subcriticalCleanGraph H' S' at h
  have hh := congrArg (fun G ↦ subcriticalRemainderGraph G D eta R₀) h
  simp only [subcriticalCleanGraph_remainder] at hh
  subst H'
  have hvv := congrArg (fun G ↦ actualRetainedEdgeCountVector G D eta R₀) h
  simp only [subcriticalCleanGraph_active_vector] at hvv
  subst v'
  have hs := subcriticalActiveGraphFromOutcome_injective H ⊥
    (isSubcriticalRetainedDefectPattern_bot D eta R₀) v h
  subst S'
  rfl

def subcriticalCleanLevelGraphFinset (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) (b : ℕ) : Finset (SimpleGraph V) :=
  Finset.univ.image (SubcriticalCleanLevelData.graph
    (D := D) (eta := eta) (R₀ := R₀) (m := m) (delta := delta) (b := b))

theorem card_subcriticalCleanLevelGraphFinset (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) (b : ℕ) :
    (subcriticalCleanLevelGraphFinset D eta R₀ m delta b).card =
      inducedStarFreeGraphCountWithEdges k (D.nonretainedVertices eta R₀).card b *
        retainedPartitionFunction D eta R₀ m delta (b : ℤ) := by
  rw [subcriticalCleanLevelGraphFinset, Finset.card_image_of_injective _
    SubcriticalCleanLevelData.graph_injective, Finset.card_univ]
  simp only [SubcriticalCleanLevelData, Fintype.card_prod, Fintype.card_coe,
    card_subcriticalCleanRemainderGraphFinset, Fintype.card_sigma,
    retainedEdgeChoices_card, retainedPartitionFunction, Finset.sum_coe_sort]

theorem mem_subcriticalCleanLevelGraphFinset_free_edges (hk : 3 ≤ k)
    {G : SimpleGraph V} (hG : G ∈ subcriticalCleanLevelGraphFinset D eta R₀ m delta b) :
    ¬Regularity.InducedEmbeds (inducedStar k) G ∧ (finiteGraphEdges G).card = m := by
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hG
  have hH := (mem_subcriticalCleanRemainderGraphFinset d.1.val b).mp d.1.property
  refine ⟨subcriticalCleanModelGraph_inducedFree hk d.1.val hH.1 d.2.2, ?_⟩
  apply subcriticalCleanGraph_card_of_mem_level
  simpa only [hH.2] using d.2.1.property

theorem mem_subcriticalCleanLevelGraphFinset_of_model (G : SimpleGraph V)
    (hG : G ∈ subcriticalCleanModelGraphFinset D eta R₀ m delta) :
    G ∈ subcriticalCleanLevelGraphFinset D eta R₀ m delta
      (finiteGraphEdges (subcriticalRemainderGraph G D eta R₀)).card := by
  obtain ⟨hc, hf, _, hv⟩ := (mem_subcriticalCleanModelGraphFinset_iff G D eta R₀ m delta).mp hG
  let d : SubcriticalCleanLevelData D eta R₀ m delta
      (finiteGraphEdges (subcriticalRemainderGraph G D eta R₀)).card :=
    ⟨⟨subcriticalRemainderGraph G D eta R₀,
      (mem_subcriticalCleanRemainderGraphFinset _ _).mpr ⟨hf,rfl⟩⟩,
      ⟨actualRetainedEdgeCountVector G D eta R₀,hv⟩,
      subcriticalActualActiveSample G D eta R₀⟩
  apply Finset.mem_image.mpr
  refine ⟨d, Finset.mem_univ _, ?_⟩
  change subcriticalActiveGraphFromOutcome (subcriticalRemainderGraph G D eta R₀) ⊥
    (subcriticalActualActiveSample G D eta R₀) = G
  rw [← hc]
  exact subcriticalActiveGraphFromOutcome_actual G D eta R₀

def retainedKeyLowRemainderGraphFinset (K : SubcriticalRetainedKey k V)
    (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) (B : ℕ) : Finset (SimpleGraph V) :=
  K.elim ∅ (fun E ↦ (Finset.range (B+1)).biUnion
    (subcriticalCleanLevelGraphFinset E eta R₀ m delta))

def subcriticalLowRemainderGraphFinset (k n m : ℕ) (L : AdmissibleBlockSequence k)
    (eta delta : ℝ) (R₀ B : ℕ) : Finset (SimpleGraph (Fin n)) :=
  (compatibleRetainedKeys k n L eta delta R₀).biUnion
    (fun K ↦ retainedKeyLowRemainderGraphFinset K eta R₀ m delta B)

theorem subcriticalLowRemainderGraphFinset_subset {k n m : ℕ} (hk : 3 ≤ k)
    (L : AdmissibleBlockSequence k) (eta delta : ℝ) (R₀ B : ℕ) :
    subcriticalLowRemainderGraphFinset k n m L eta delta R₀ B ⊆
      inducedStarFreeGraphFinsetWithEdges k n m := by
  intro G hG
  obtain ⟨K, _, hG⟩ := Finset.mem_biUnion.mp hG
  cases K with
  | none => exact False.elim (Finset.notMem_empty _ hG)
  | some E =>
    obtain ⟨b, _, hG⟩ := Finset.mem_biUnion.mp hG
    exact mem_inducedFreeGraphFinsetWithEdges_iff_finiteGraphEdges.mpr
      (mem_subcriticalCleanLevelGraphFinset_free_edges hk hG)

theorem card_retainedKeyLowRemainderGraphFinset_le
    (K : SubcriticalRetainedKey k V) (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) (B : ℕ)
    (hK : ∀ E, K = some E → retainedKey E eta R₀ = some E) :
    (retainedKeyLowRemainderGraphFinset K eta R₀ m delta B).card ≤
      ∑ b ∈ Finset.range (B+1), inducedStarFreeGraphCountWithEdges k K.remainder.card b *
        retainedKeyPartitionFunction K m delta (b : ℤ) := by
  cases K with
  | none => simp only [retainedKeyLowRemainderGraphFinset, Option.elim_none, Finset.card_empty]; omega
  | some E =>
    have hh := hK E rfl
    have hr := retainedKey_remainder E eta R₀
    rw [hh] at hr
    change ((Finset.range (B+1)).biUnion _).card ≤ _
    refine Finset.card_biUnion_le.trans (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro b _
    rw [card_subcriticalCleanLevelGraphFinset, ← retainedKeyPartitionFunction_retainedKey, hh, hr]

theorem card_subcriticalLowRemainderGraphFinset_le (k n m : ℕ)
    (L : AdmissibleBlockSequence k) (eta delta : ℝ) (R₀ B : ℕ) :
    (subcriticalLowRemainderGraphFinset k n m L eta delta R₀ B).card ≤
      ∑ K ∈ compatibleRetainedKeys k n L eta delta R₀,
        ∑ b ∈ Finset.range (B+1), inducedStarFreeGraphCountWithEdges k K.remainder.card b *
          retainedKeyPartitionFunction K m delta (b : ℤ) := by
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro K hK
  apply card_retainedKeyLowRemainderGraphFinset_le
  intro E hE
  obtain ⟨D, _, hD⟩ := mem_compatibleRetainedKeys.mp hK
  exact retainedKey_some_idempotent (hD.trans hE)

set_option maxHeartbeats 600000 in
theorem mem_subcriticalLowRemainderGraphFinset_of_model
    {n B : ℕ} {L : AdmissibleBlockSequence k} {G : SimpleGraph (Fin n)}
    {D E : SubcriticalDivision k (Fin n)}
    (hD : D ∈ subcriticalCompatibleDivisions k n L eta delta R₀)
    (hkey : retainedKey D eta R₀ = some E)
    (hG : G ∈ subcriticalCleanModelGraphFinset D eta R₀ m delta)
    (hb : (finiteGraphEdges (subcriticalRemainderGraph G D eta R₀)).card ≤ B) :
    G ∈ subcriticalLowRemainderGraphFinset k n m L eta delta R₀ B := by
  have hnorm := retainedKey_some_idempotent hkey
  have heq : retainedKey D eta R₀ = retainedKey E eta R₀ := hkey.trans hnorm.symm
  have hG' : G ∈ subcriticalCleanModelGraphFinset E eta R₀ m delta := by
    rwa [← subcriticalCleanModelGraphFinset_eq_of_retainedKey_eq heq]
  have hs := nonretainedVertices_eq_of_retainedKey_eq heq
  have hb' : (finiteGraphEdges (subcriticalRemainderGraph G E eta R₀)).card ≤ B := by
    have he := congrArg (fun S : Finset (Fin n) ↦ (finiteGraphEdges (G.induce (S : Set _))).card) hs
    exact he ▸ hb
  apply Finset.mem_biUnion.mpr
  refine ⟨some E, ?_, ?_⟩
  · rw [← hkey]
    exact retainedKey_mem_compatibleRetainedKeys hD
  · apply Finset.mem_biUnion.mpr
    exact ⟨_, Finset.mem_range.mpr (Nat.lt_succ_of_le hb'),
      mem_subcriticalCleanLevelGraphFinset_of_model G hG'⟩

end InducedStars
