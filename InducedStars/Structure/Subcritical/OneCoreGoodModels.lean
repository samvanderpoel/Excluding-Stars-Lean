import InducedStars.Structure.Subcritical.OneCoreCleanGraphGeometry
import InducedStars.Structure.Subcritical.CleanCoverLimits
import InducedStars.Structure.Subcritical.CleanModelGoodCounting

/-!
# A uniform positive fraction of identifiable clean one-core models

The retained support is connected and has a unique clique cover, up to
permutation. These are properties of the generated graph and its literal
support, not assumptions on a canonical full division.
-/

noncomputable section
open Finset Set Filter Topology
open scoped Classical BigOperators
namespace InducedStars
variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

def SubcriticalGoodCleanSupport (k : ℕ) (G : SimpleGraph V) (S : Finset V) : Prop :=
  (G.induce (S : Set V)).Connected ∧ HasUniqueCoMultipartiteCover k (G.induce (S : Set V))

theorem oneCore_goodSample_half (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    {eta : ℝ} {R₀ : ℕ}
    (hret : (SubcriticalDivision.ofSupercritical hk D).retainedComponentIndices eta R₀ = Finset.univ)
    (v : RetainedEdgeCountVector (SubcriticalDivision.ofSupercritical hk D) eta R₀)
    (H : SubcriticalRemainderGraph (SubcriticalDivision.ofSupercritical hk D) eta R₀)
    (hquota : ∀ e, 0 < (oneCoreProfile hk D hret v).count e)
    (hhalf : supercriticalProfileMultiplicity (oneCoreProfile hk D hret v) ≤
      2 * (fixedProfileUniqueCoverEvent D.onSupportFin (oneCoreProfile hk D hret v)).card) :
    retainedEdgeCountMultiplicity v ≤ 2 *
      (Finset.univ.filter fun T : RetainedEdgeChoices v ↦
        SubcriticalGoodCleanSupport k (subcriticalCleanGraph H T) D.support).card := by
  let p := oneCoreProfile hk D hret v
  let e := oneCoreProfileSampleEquiv hk D hret v
  have hsub : (fixedProfileUniqueCoverEvent D.onSupportFin p).image e ⊆
      Finset.univ.filter (fun T : RetainedEdgeChoices v ↦
        SubcriticalGoodCleanSupport k (subcriticalCleanGraph H T) D.support) := by
    rintro T hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact (oneCoreCleanSupportIso hk D hret v H S).connected_iff.mp
        (fixedProfileCleanGraph_connected D.onSupportFin (by omega) p
          D.onSupportFin_isFull hquota S)
    · exact ((mem_fixedProfileUniqueCoverEvent D.onSupportFin p S).mp hS).of_iso
        (oneCoreCleanSupportIso hk D hret v H S)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ e.injective] at hc
  rw [oneCoreProfile_multiplicity] at hhalf
  exact hhalf.trans (Nat.mul_le_mul_left 2 hc)

theorem exists_oneCore_goodSample_threshold_uniform (hk : 3 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, ∀ (W : Type*) [Fintype W] [DecidableEq W]
      (D : SupercriticalDivision k W), N ≤ D.support.card →
      ∀ {eta : ℝ} {R₀ : ℕ}
      (hret : (SubcriticalDivision.ofSupercritical hk D).retainedComponentIndices eta R₀ = Finset.univ)
      (v : RetainedEdgeCountVector (SubcriticalDivision.ofSupercritical hk D) eta R₀)
      (H : SubcriticalRemainderGraph (SubcriticalDivision.ofSupercritical hk D) eta R₀),
      (∀ i, D.support.card ≤ 2 * (k - 1) * (D.parts i).card) →
      (∀ e, 0 < retainedEdgeCountDensity v e ∧ retainedEdgeCountDensity v e ≤ Real.exp (-c)) →
      retainedEdgeCountMultiplicity v ≤ 2 *
        (Finset.univ.filter fun T : RetainedEdgeChoices v ↦
          SubcriticalGoodCleanSupport k (subcriticalCleanGraph H T) D.support).card := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_fixedProfile_uniqueCover_half hk hc)
  refine ⟨N, ?_⟩
  intro W _ _ D hn eta R₀ hret v H hpart hdensity
  have hnon : (Finset.univ : Finset (Fin (k - 1))).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin (k - 1) ↦ (D.parts i).card) hnon
  have hhalf := hN D.support.card hn D.onSupportFin (oneCoreProfile hk D hret v)
    (D.parts i).card D.onSupportFin_isFull
    (fun j ↦ by rw [D.onSupportFin_part_card]; exact hmin j (Finset.mem_univ _))
    (hpart i) (fun e ↦ by rw [oneCoreProfile_density]; exact (hdensity _).2)
  apply oneCore_goodSample_half hk D hret v H _ hhalf
  intro e
  have hd : 0 < profileDensity (oneCoreProfile hk D hret v) e := by
    rw [oneCoreProfile_density]
    exact (hdensity _).1
  have : 0 < ((oneCoreProfile hk D hret v).count e : ℝ) :=
    (div_pos_iff.mp hd).elim (fun h ↦ h.1)
      (fun h ↦ (not_lt_of_ge (Nat.cast_nonneg _) h.1).elim)
  exact_mod_cast this

theorem exists_oneCore_goodSample_threshold (hk : 3 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∃ N : ℕ, ∀ (D : SupercriticalDivision k V), N ≤ D.support.card →
      ∀ {eta : ℝ} {R₀ : ℕ}
      (hret : (SubcriticalDivision.ofSupercritical hk D).retainedComponentIndices eta R₀ = Finset.univ)
      (v : RetainedEdgeCountVector (SubcriticalDivision.ofSupercritical hk D) eta R₀)
      (H : SubcriticalRemainderGraph (SubcriticalDivision.ofSupercritical hk D) eta R₀),
      (∀ i, D.support.card ≤ 2 * (k - 1) * (D.parts i).card) →
      (∀ e, 0 < retainedEdgeCountDensity v e ∧ retainedEdgeCountDensity v e ≤ Real.exp (-c)) →
      retainedEdgeCountMultiplicity v ≤ 2 *
        (Finset.univ.filter fun T : RetainedEdgeChoices v ↦
          SubcriticalGoodCleanSupport k (subcriticalCleanGraph H T) D.support).card := by
  obtain ⟨N, hN⟩ := exists_oneCore_goodSample_threshold_uniform hk hc
  exact ⟨N, hN V⟩

end InducedStars
