import InducedStars.Structure.Subcritical.OneCoreKey
import DenseGraph.FiniteModels.IsolatedSupport

/-!
# Full clique-cover coordinates on the actual retained support

The restricted division uses the original labelled support subtype and
preserves every part and its cardinality. It supplies the finite fixed-cell
models with a genuinely full cover, without discarding ambient labels.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars
namespace SupercriticalDivision

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

def onSupportSet (D : SupercriticalDivision k V) (S : Finset V) (hS : D.support = S) :
    SupercriticalDivision k (S : Set V) where
  parts i := Finset.univ.filter fun v ↦ v.val ∈ D.parts i
  parts_nonempty i := by
    obtain ⟨v, hv⟩ := D.parts_nonempty i
    have hvs : v ∈ S := hS ▸ D.part_subset_support i hv
    exact ⟨⟨v, hvs⟩, by simp [hv]⟩
  parts_pairwiseDisjoint := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    exact hij (D.mem_part_unique (Finset.mem_filter.mp hvi).2 (Finset.mem_filter.mp hvj).2)

@[simp] theorem mem_onSupportSet_part (D : SupercriticalDivision k V)
    (S : Finset V) (hS : D.support = S) (i : Fin (k - 1)) (v : (S : Set V)) :
    v ∈ (D.onSupportSet S hS).parts i ↔ v.val ∈ D.parts i := by
  simp [onSupportSet]

theorem onSupportSet_isFull (D : SupercriticalDivision k V) (S : Finset V) (hS : D.support = S) :
    (D.onSupportSet S hS).IsFull := by
  rw [isFull_iff_support_eq_univ]
  ext v
  simp only [mem_support, mem_onSupportSet_part, Finset.mem_univ, iff_true]
  exact mem_support.mp (hS.symm ▸ v.property)

theorem onSupportSet_parts_image (D : SupercriticalDivision k V)
    (S : Finset V) (hS : D.support = S) (i : Fin (k - 1)) :
    ((D.onSupportSet S hS).parts i).image (fun v ↦ v.val) = D.parts i := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (mem_onSupportSet_part D S hS i w).mp hw
  · intro hv
    have hvs : v ∈ S := hS ▸ D.part_subset_support i hv
    exact Finset.mem_image.mpr ⟨⟨v, hvs⟩, (mem_onSupportSet_part D S hS i _).mpr hv, rfl⟩

theorem onSupportSet_part_card (D : SupercriticalDivision k V)
    (S : Finset V) (hS : D.support = S) (i : Fin (k - 1)) :
    ((D.onSupportSet S hS).parts i).card = (D.parts i).card := by
  rw [← onSupportSet_parts_image D S hS i,
    Finset.card_image_of_injective _ Subtype.val_injective]

theorem onSupportSet_injective {S : Finset V} {D E : SupercriticalDivision k V}
    {hD : D.support = S} {hE : E.support = S}
    (h : D.onSupportSet S hD = E.onSupportSet S hE) : D = E := by
  apply SupercriticalDivision.ext_parts
  funext i
  rw [← onSupportSet_parts_image D S hD i, ← onSupportSet_parts_image E S hE i, h]

theorem fullDivisionsEquivalent_of_onSupportSet
    {S : Finset V} {D E : SupercriticalDivision k V}
    {hD : D.support = S} {hE : E.support = S}
    (h : FullDivisionsEquivalent (D.onSupportSet S hD) (E.onSupportSet S hE)) :
    FullDivisionsEquivalent D E := by
  obtain ⟨sigma, heq⟩ := h
  refine ⟨sigma, SupercriticalDivision.ext_parts ?_⟩
  funext i
  have hp := congrArg (fun P : SupercriticalDivision k (S : Set V) ↦
    (P.parts i).image (fun v ↦ v.val)) heq
  simpa only [onSupportSet_parts_image, reindexParts_parts] using hp

theorem onSupportSet_parts_isClique (D : SupercriticalDivision k V)
    (S : Finset V) (hS : D.support = S) (G : SimpleGraph V)
    (hclique : ∀ i, G.IsClique (D.parts i : Set V)) (i : Fin (k - 1)) :
    (G.induce (S : Set V)).IsClique ((D.onSupportSet S hS).parts i : Set (S : Set V)) := by
  intro x hx y hy hne
  exact hclique i ((mem_onSupportSet_part D S hS i x).mp hx)
    ((mem_onSupportSet_part D S hS i y).mp hy) (fun h ↦ hne (Subtype.ext h))

end SupercriticalDivision

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Uniform factorial multiplicity for a finite family of literal one-core
keys with a fixed, uniquely covered induced support. The support equality
is supplied separately by the isolated-support theorem. -/
theorem card_oneCoreRetainedKeys_le_factorial_of_unique
    (hk : 3 ≤ k) (G : SimpleGraph V) (S : Finset V)
    (F : Finset (SubcriticalRetainedKey k V))
    (hunique : HasUniqueCoMultipartiteCover k (G.induce (S : Set V)))
    (hF : ∀ K ∈ F, ∃ D : SupercriticalDivision k V,
      K = some (SubcriticalDivision.ofSupercritical hk D) ∧
      D.support = S ∧ ∀ i, G.IsClique (D.parts i : Set V)) :
    F.card ≤ (k - 1).factorial := by
  by_cases hempty : F = ∅
  · simp [hempty]
  obtain ⟨K₀, hK₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨D₀, hKD₀, hD₀, hclique₀⟩ := hF K₀ hK₀
  obtain ⟨C, hCfull, hCclique, hCunique⟩ := hunique
  have hC₀ := hCunique (D₀.onSupportSet S hD₀) (D₀.onSupportSet_isFull S hD₀)
    (D₀.onSupportSet_parts_isClique S hD₀ G hclique₀)
  apply card_retainedKeys_le_factorial_of_reindexing hk D₀ F
  intro K hK
  obtain ⟨D, hKD, hD, hclique⟩ := hF K hK
  have hCD := hCunique (D.onSupportSet S hD) (D.onSupportSet_isFull S hD)
    (D.onSupportSet_parts_isClique S hD G hclique)
  have heq := SupercriticalDivision.fullDivisionsEquivalent_of_onSupportSet
    (fullDivisionsEquivalent_trans (fullDivisionsEquivalent_symm hC₀) hCD)
  obtain ⟨sigma, hsigma⟩ := heq
  exact ⟨sigma, by rw [hKD, hsigma]⟩

end InducedStars
