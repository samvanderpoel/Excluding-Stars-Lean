import DenseGraph.Graphon.ZeroDistance
import InducedStars.Structure.Subcritical.RetainedMassCompatibility
import InducedStars.Structure.Subcritical.RetainedKeyFamilies

/-!
# Positive retained mass for critical optimizers away from zero

The omitted quantity is quadratic mass, as in `lemma:critical-gnp-comparison-K1k`. The estimates work for
every admissible representation, including one full complete core, without
a strict-subcritical density assumption.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

theorem gnpRetainedBlockLength_lower {k : ℕ}
    (L : AdmissibleBlockSequence k) {eta : ℝ} (heta : 0 < eta) (R₀ : ℕ) :
    L.mass - (2 * eta + 1 / ((R₀ + 1 : ℕ) : ℝ)) ≤
      subcriticalRetainedBlockLength L eta R₀ := by
  have hsplit := subcriticalMass_eq_retained_add_omitted L eta R₀
  have htail := subcriticalOmittedBlockMass_le L heta R₀
  have hhead : (∑ i ∈ subcriticalMassRetainedBlockIndices L eta R₀, L.massTerm i) ≤
      subcriticalRetainedBlockLength L eta R₀ :=
    Finset.sum_le_sum (fun i _ ↦ L.massTerm_le_alpha i)
  linarith

/-- Uniform positive retained length follows from a cut separation and
explicit small-length/large-core tail reserves. -/
theorem gnpRetainedBlockLength_lower_of_separated
    {k : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    {eta separation : ℝ} (heta : 0 < eta) (R₀ : ℕ)
    (hseparation : separation ≤ cutDist (WLambda hk L) zeroGraphon)
    (htail : 2 * eta + 1 / ((R₀ + 1 : ℕ) : ℝ) ≤
      separation / (2 * (1 + ((k - 2 : ℕ) : ℝ) * pK k))) :
    separation / (2 * (1 + ((k - 2 : ℕ) : ℝ) * pK k)) ≤
      subcriticalRetainedBlockLength L eta R₀ := by
  have hc : 0 < 1 + ((k - 2 : ℕ) : ℝ) * pK k := by
    have hp := (pK_mem_Ioo (show 2 ≤ k by omega)).1
    positivity
  rw [DenseGraph.cutDist_zeroGraphon, graphonEdgeDensity_WLambda] at hseparation
  change separation ≤ (1 + ((k - 2 : ℕ) : ℝ) * pK k) * L.mass at hseparation
  have hmass : separation / (1 + ((k - 2 : ℕ) : ℝ) * pK k) ≤ L.mass :=
    (div_le_iff₀ hc).mpr (by simpa [mul_comm] using hseparation)
  have hhalf : separation / (1 + ((k - 2 : ℕ) : ℝ) * pK k) =
      2 * (separation / (2 * (1 + ((k - 2 : ℕ) : ℝ) * pK k))) := by
    field_simp
  rw [hhalf] at hmass
  linarith [gnpRetainedBlockLength_lower L heta R₀]

/-- The actual retained key contains a positive linear number of vertices.
No part-balance assertion and no count of remainder decorations is used. -/
theorem gnpCompatibleRetainedKey_support_lower
    {k n R₀ : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    {eta delta separation : ℝ} (heta : 0 < eta) (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ eta)
    (hseparation : separation ≤ cutDist (WLambda hk L) zeroGraphon)
    (htail : 2 * eta + 1 / ((R₀ + 1 : ℕ) : ℝ) ≤
      separation / (2 * (1 + ((k - 2 : ℕ) : ℝ) * pK k)))
    (hreserve : delta ≤ eta *
      (separation / (2 * (1 + ((k - 2 : ℕ) : ℝ) * pK k))))
    {K : SubcriticalRetainedKey k (Fin n)}
    (hK : K ∈ compatibleRetainedKeys k n L eta delta R₀) :
    (separation / (4 * (1 + ((k - 2 : ℕ) : ℝ) * pK k))) * n ≤ K.support.card := by
  obtain ⟨D, hD, rfl⟩ := mem_compatibleRetainedKeys.mp hK
  obtain ⟨C⟩ := (mem_subcriticalCompatibleDivisions D).mp hD |>.2
  have hlength := gnpRetainedBlockLength_lower_of_separated hk L heta R₀ hseparation htail
  have h := C.retained_mass_gap (mu := 0) heta hdelta0 hdelta hreserve (by simpa using hlength)
  rw [retainedKey_support]
  simp only [zero_add, Fintype.card_fin] at h
  convert h using 1 <;> simp only [div_div, mul_assoc] <;> ring

end InducedStars
