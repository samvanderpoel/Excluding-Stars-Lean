import InducedStars.FiniteModels.GnpCore
import InducedStars.FiniteModels.GraphFamilies

/-!
# Induced-star binomial random-graph compatibility

The exact labeled `G(n,p)` law and arbitrary induced-`H`-free events live
in `FiniteModels.GnpCore`.  This historical import path retains only the
induced-star aliases and their elementary positivity witnesses while
re-exporting the complete general API.
-/

noncomputable section

open Finset Set

namespace InducedStars

/-- Probability that a labeled `G(n,p)` graph is induced-`K₁,ₖ`-free. -/
noncomputable abbrev gnpInducedStarFreeProbability
    (k n : ℕ) (p : ℝ) : ℝ :=
  gnpInducedFreeProbability (inducedStar k) n p

private theorem inducedStar_not_inducedEmbeds_bot {k n : ℕ}
    (hk : 1 ≤ k) :
    ¬Regularity.InducedEmbeds (inducedStar k)
      (⊥ : SimpleGraph (Fin n)) := by
  rintro ⟨φ⟩
  let i : Fin k := ⟨0, hk⟩
  have hadj := inducedStar_center_adj_leaf i
  have himage : (⊥ : SimpleGraph (Fin n)).Adj (φ 0) (φ i.succ) :=
    φ.map_adj_iff.mpr hadj
  simpa using himage

/-- The empty labeled graph is induced-star-free as soon as the star has an
edge. -/
theorem bot_mem_inducedStarFreeGraphFinset {k n : ℕ} (hk : 1 ≤ k) :
    (⊥ : SimpleGraph (Fin n)) ∈ inducedFreeGraphFinset (inducedStar k) n :=
  mem_inducedFreeGraphFinset.mpr (inducedStar_not_inducedEmbeds_bot hk)

/-- Induced-star-freeness has strictly positive `G(n,p)` probability on the
open random domain. -/
theorem gnpInducedStarFreeProbability_pos {k n : ℕ} (hk : 1 ≤ k)
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    0 < gnpInducedStarFreeProbability k n p := by
  have hsingle : ({(⊥ : SimpleGraph (Fin n))} :
      Finset (SimpleGraph (Fin n))) ⊆
        inducedFreeGraphFinset (inducedStar k) n := by
    simpa only [Finset.singleton_subset_iff] using
      bot_mem_inducedStarFreeGraphFinset (n := n) hk
  have hmono := gnpGraphEventProbability_mono
    ⟨hp.1.le, hp.2.le⟩ hsingle
  rw [gnpGraphEventProbability_singleton] at hmono
  exact (gnpGraphWeight_pos hp (⊥ : SimpleGraph (Fin n))).trans_le hmono

/-- The requested positive-probability and at-most-one bounds for induced
stars. -/
theorem gnpInducedStarFreeProbability_pos_le_one {k n : ℕ}
    (hk : 1 ≤ k) {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    0 < gnpInducedStarFreeProbability k n p ∧
      gnpInducedStarFreeProbability k n p ≤ 1 :=
  ⟨gnpInducedStarFreeProbability_pos hk hp,
    gnpInducedFreeProbability_le_one (inducedStar k)
      ⟨hp.1.le, hp.2.le⟩⟩

/-- Normalized logarithm of the induced-star-free `G(n,p)` probability. -/
noncomputable abbrev normalizedLogGnpInducedStarFreeProbability
    (k n : ℕ) (p : ℝ) : ℝ :=
  normalizedLogGnpInducedFreeProbability (inducedStar k) n p

end InducedStars
