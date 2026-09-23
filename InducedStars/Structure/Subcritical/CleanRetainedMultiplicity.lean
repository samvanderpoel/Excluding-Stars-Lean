import InducedStars.Structure.Subcritical.OneCoreGoodModels
import InducedStars.Structure.Subcritical.OneCoreSupport
import InducedStars.Structure.Subcritical.RetainedCleanStructure
import InducedStars.Structure.Subcritical.RetainedKeyNormalization
import InducedStars.Structure.Subcritical.RetainedKeyModels
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Identifying the support and counting retained keys, not full divisions

Good model graphs have a connected, uniquely covered retained
support. A linear-size clique and a low-edge complementary graph identify
that support. Only the clique-label permutation factor remains.
-/

noncomputable section
open Finset Set
open scoped Classical BigOperators
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

def retainedKeyCleanModelGraphFinset (K : SubcriticalRetainedKey k V)
    (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) : Finset (SimpleGraph V) :=
  K.elim ∅ (fun E ↦ subcriticalCleanModelGraphFinset E eta R₀ m delta)

def retainedKeyGoodCleanGraphFinset (K : SubcriticalRetainedKey k V)
    (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) : Finset (SimpleGraph V) :=
  (retainedKeyCleanModelGraphFinset K eta R₀ m delta).filter
    (fun G ↦ SubcriticalGoodCleanSupport k G K.support)

/-- The source clean graph itself supplies exact separation, literal clique
parts, and the sparse-edge bound on the complement of the retained support. -/
theorem oneCore_cleanModel_geometry (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    {eta delta : ℝ} {R₀ m : ℕ}
    (hret : (SubcriticalDivision.ofSupercritical hk D).retainedComponentIndices eta R₀ = Finset.univ)
    {G : SimpleGraph V}
    (hG : G ∈ subcriticalCleanModelGraphFinset (SubcriticalDivision.ofSupercritical hk D)
      eta R₀ m delta) (heta : 0 ≤ eta) :
    (∀ x ∈ D.support, ∀ y ∉ D.support, ¬G.Adj x y) ∧
    (∀ i, G.IsClique (D.parts i : Set V)) ∧
    ((finiteGraphEdges (G.induce (D.support : Set V)ᶜ)).card : ℝ) ≤
      subcriticalSparseSideConstant k * eta * (Fintype.card V : ℝ)^2 := by
  let E := SubcriticalDivision.ofSupercritical hk D
  let i₀ : Fin E.componentCount := ⟨0, E.componentCount_pos⟩
  obtain ⟨hclean, _, hb, _⟩ := (mem_subcriticalCleanModelGraphFinset_iff G E eta R₀ m delta).mp hG
  have hzero : i₀ ∈ E.retainedComponentIndices eta R₀ := by
    rw [hret]; exact Finset.mem_univ _
  have hsupport : E.componentSupport i₀ = D.support := rfl
  have hvertices : E.retainedVertices eta R₀ = D.support := by
    rw [← retainedKey_support E eta R₀,
      retainedKey_eq_some_of_retainedComponentIndices_eq_univ E hret]
    exact SubcriticalDivision.ofSupercritical_support hk D
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hsupport] using subcriticalIncidentClean_component_noCross hclean i₀ hzero
  · intro i x hx y hy hne
    have hxret : x ∈ E.retainedVertices eta R₀ := hvertices.symm ▸ D.part_subset_support i hx
    apply (subcriticalIncidentClean_model_adj_iff hclean hxret).mpr
    apply (subcriticalDivisionModelGraph_adj G E x y).mpr
    exact ⟨hne, Or.inl ⟨⟨i₀,i⟩,hx,hy⟩⟩
  · have hset : (D.support : Set V)ᶜ = (E.nonretainedVertices eta R₀ : Set V) := by
      ext x
      simp only [Set.mem_compl_iff, Finset.mem_coe, E.mem_nonretainedVertices, hvertices]
    have he := congrArg (fun S : Set V ↦ (finiteGraphEdges (G.induce S)).card) hset
    rw [he]
    exact (show ((finiteGraphEdges (subcriticalRemainderGraph G E eta R₀)).card : ℝ) ≤
      Nat.floor (subcriticalSparseSideConstant k * eta * (Fintype.card V : ℝ)^2) by
        exact_mod_cast hb).trans (Nat.floor_le (by
          have : 0 ≤ subcriticalSparseSideConstant k := by
            unfold subcriticalSparseSideConstant; positivity
          positivity))

/-- Exact bounded-fiber comparison. Its hypotheses are finite geometric
properties of the actual good graphs, not a uniqueness assumption for full
canonical divisions. -/
theorem sum_retainedKeyGoodClean_card_le_factorial
    (hk : 3 ≤ k) (F : Finset (SubcriticalRetainedKey k V))
    {eta delta a : ℝ} {R₀ m : ℕ} (heta : 0 ≤ eta) (ha : 0 ≤ a)
    (hlarge : 2 ≤ a * Fintype.card V)
    (hsparse : subcriticalSparseSideConstant k * eta < a^2/4)
    (hkeys : ∀ K ∈ F,
      (retainedKeyGoodCleanGraphFinset K eta R₀ m delta).Nonempty →
      ∃ D : SupercriticalDivision k V,
        K = some (SubcriticalDivision.ofSupercritical hk D) ∧
        (SubcriticalDivision.ofSupercritical hk D).retainedComponentIndices eta R₀ = Finset.univ ∧
        ∀ i, a * Fintype.card V ≤ ((D.parts i).card : ℝ)) :
    ∑ K ∈ F, (retainedKeyGoodCleanGraphFinset K eta R₀ m delta).card ≤
      (k-1).factorial * (F.biUnion (fun K ↦ retainedKeyGoodCleanGraphFinset K eta R₀ m delta)).card := by
  letI : Fintype (SubcriticalRetainedKey k V) := Fintype.ofFinite _
  let family := fun K : SubcriticalRetainedKey k V ↦ retainedKeyGoodCleanGraphFinset K eta R₀ m delta
  rw [Finset.sum_card_eq_sum_biUnion_card family F]
  have hfiber : ∀ G ∈ F.biUnion family,
      (Finset.univ.filter fun K ↦ K ∈ F ∧ G ∈ family K).card ≤ (k-1).factorial := by
    intro G hG
    obtain ⟨K₀, hK₀, hG₀⟩ := Finset.mem_biUnion.mp hG
    have hgood₀ := (Finset.mem_filter.mp hG₀).2
    obtain ⟨D₀, heq₀, hret₀, hpart₀⟩ := hkeys K₀ hK₀ ⟨G,hG₀⟩
    have hmodel₀ := (Finset.mem_filter.mp hG₀).1
    rw [heq₀] at hmodel₀
    have hgeom₀ := oneCore_cleanModel_geometry hk D₀ hret₀ hmodel₀ heta
    have hsupport₀ : D₀.support = K₀.support := by
      rw [heq₀]; exact (SubcriticalDivision.ofSupercritical_support hk D₀).symm
    apply card_oneCoreRetainedKeys_le_factorial_of_unique hk G K₀.support _ hgood₀.2
    intro K hK
    obtain ⟨hKF,hGK⟩ := (Finset.mem_filter.mp hK).2
    obtain ⟨D, heq, hret, hpart⟩ := hkeys K hKF ⟨G,hGK⟩
    have hmodel := (Finset.mem_filter.mp hGK).1
    have hgood := (Finset.mem_filter.mp hGK).2
    rw [heq] at hmodel
    have hgeom := oneCore_cleanModel_geometry hk D hret hmodel heta
    have hsupport : D.support = K.support := by
      rw [heq]; exact (SubcriticalDivision.ofSupercritical_support hk D).symm
    have hs : (D.support : Set V) = (D₀.support : Set V) := by
      have hcon : (G.induce (D.support : Set V)).Preconnected := by
        rw [hsupport]
        exact hgood.1.preconnected
      have hcon₀ : (G.induce (D₀.support : Set V)).Preconnected := by
        rw [hsupport₀]
        exact hgood₀.1.preconnected
      apply DenseGraph.isolated_support_eq_of_clique_and_sparse_remainder
        hcon hcon₀ hgeom.1 hgeom₀.1
        (D.parts ⟨0,by omega⟩) (D.part_subset_support _) (hgeom.2.1 _) ha
        (hpart _) hlarge hsparse hgeom₀.2.2
    refine ⟨D,heq,?_,hgeom.2.1⟩
    exact (Finset.coe_injective hs).trans hsupport₀
  calc
    _ ≤ ∑ _G ∈ F.biUnion family, (k-1).factorial := Finset.sum_le_sum hfiber
    _ = _ := by simp [family, mul_comm]

end InducedStars
