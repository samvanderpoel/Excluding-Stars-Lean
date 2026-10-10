import InducedStars.Structure.Subcritical.ProfilePenalty
import InducedStars.Structure.Subcritical.CleanFamilies
import InducedStars.Structure.Subcritical.ProfileEnumeration
import DenseGraph.Combinatorics.ProfileSums

/-!
# Summing the nonclean subcritical profile classes

Paper: Lemma `lemma:NtaunmWUpperBdK1k`, exceptional-family estimate.
The fixed polynomial prefactor is retained during summation and is
paid from the common positive-complexity penalty. This includes root-free
profiles of positive matching complexity. Every profile estimate uses the
same ambient family, and no positivity of the clean partition function is
required.
-/

noncomputable section
open Finset
open scoped BigOperators Classical

namespace InducedStars

/-- Deterministic covering by positive-complexity classes in the original
ambient family. No disjointness of profile classes is assumed. -/
theorem subcriticalNonclean_card_le_sum_profiles
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (SimpleGraph V)) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ) (ha : 0 < alpha) (haHalf : alpha < 1 / 2) :
    (subcriticalNoncleanDivisionGraphFinset F D eta R₀).card ≤
      ∑ r ∈ Finset.Icc 1 (2 * Fintype.card V),
        ∑ p ∈ subcriticalProfilesOfComplexity D eta R₀ theta r,
          (subcriticalProfileClassGraphFinset F alpha p).card := by
  have hcover : subcriticalNoncleanDivisionGraphFinset F D eta R₀ ⊆
      (Finset.Icc 1 (2 * Fintype.card V)).biUnion (fun r ↦
        (subcriticalProfilesOfComplexity D eta R₀ theta r).biUnion fun p ↦
          subcriticalProfileClassGraphFinset F alpha p) := by
    intro G hG
    obtain ⟨hGF, hnon⟩ := (mem_subcriticalNoncleanDivisionGraphFinset F G).mp hG
    obtain ⟨p, hp⟩ := subcriticalProfileCovering F D eta R₀ theta alpha ha haHalf G hGF
    have hrealizes := (mem_subcriticalProfileClassGraphFinset.mp hp).2
    apply Finset.mem_biUnion.mpr
    refine ⟨subcriticalProfileComplexity p,
      Finset.mem_Icc.mpr ⟨hrealizes.complexity_pos_of_nonclean ha hnon,
        subcriticalProfileComplexity_le p⟩, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨p, by simp, hp⟩
  calc
    _ ≤ _ := Finset.card_le_card hcover
    _ ≤ ∑ r ∈ Finset.Icc 1 (2 * Fintype.card V),
        ((subcriticalProfilesOfComplexity D eta R₀ theta r).biUnion fun p ↦
          subcriticalProfileClassGraphFinset F alpha p).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun _ _ ↦ Finset.card_biUnion_le

end InducedStars
