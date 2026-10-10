import InducedStars.Structure.Subcritical.RetainedKeyCounts
import InducedStars.Structure.Subcritical.CandidateGeometry

/-!
# The finite image of compatible retained keys

This is the image of the actual compatible division family under
the minimal retained-key map. Full divisions are not used as duplicate
indices for the grouped clean partition function.
-/

noncomputable section
open Finset
open scoped Classical
namespace InducedStars

def compatibleRetainedKeys (k n : ℕ) (L : AdmissibleBlockSequence k)
    (eta delta : ℝ) (R₀ : ℕ) : Finset (SubcriticalRetainedKey k (Fin n)) :=
  (subcriticalCompatibleDivisions k n L eta delta R₀).image
    (fun D ↦ retainedKey D eta R₀)

@[simp] theorem mem_compatibleRetainedKeys
    {k n R₀ : ℕ} {L : AdmissibleBlockSequence k} {eta delta : ℝ}
    {K : SubcriticalRetainedKey k (Fin n)} :
    K ∈ compatibleRetainedKeys k n L eta delta R₀ ↔
      ∃ D ∈ subcriticalCompatibleDivisions k n L eta delta R₀,
        retainedKey D eta R₀ = K := by
  simp only [compatibleRetainedKeys, Finset.mem_image]

theorem retainedKey_mem_compatibleRetainedKeys
    {k n R₀ : ℕ} {L : AdmissibleBlockSequence k} {eta delta : ℝ}
    {D : SubcriticalDivision k (Fin n)}
    (hD : D ∈ subcriticalCompatibleDivisions k n L eta delta R₀) :
    retainedKey D eta R₀ ∈ compatibleRetainedKeys k n L eta delta R₀ :=
  Finset.mem_image.mpr ⟨D, hD, rfl⟩

theorem card_compatibleRetainedKeys_le
    (k n : ℕ) (L : AdmissibleBlockSequence k) (eta delta : ℝ) (R₀ : ℕ) :
    (compatibleRetainedKeys k n L eta delta R₀).card ≤
      (subcriticalCompatibleDivisions k n L eta delta R₀).card :=
  Finset.card_image_le

end InducedStars
