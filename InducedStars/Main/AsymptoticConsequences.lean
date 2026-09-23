import InducedStars.Asymptotics.FixedDensityEnumeration
import InducedStars.Asymptotics.GnpTransfer
import InducedStars.Graphon.EntropyUpperBound
import InducedStars.Graphon.GnpDomains
import InducedStars.Main.VariationalConsequences

/-!
# Fixed-density asymptotic consequences

This module specializes the general fixed-density transfer to induced stars
and identifies its restricted graphon variational value with the explicit
entropy profile from the optimization layer.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The positive-random fixed-density induced-star domain is nonempty at
every interior density. -/
theorem positiveRandomFixedDensityGraphons_inducedStar_nonempty
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    (positiveRandomFixedDensityGraphons (inducedStar k) γ).Nonempty := by
  obtain ⟨W, hW⟩ := candidateOptimizerFamily_nonempty k hk γ hγ
  have hproperties := VgammaOpt k hk γ hγ hW
  have hEntropy : 0 < graphonEntropy W := by
    rw [hproperties.2.2]
    exact entropyDensity_pos k hk γ hγ
  exact ⟨W, hproperties.2.1, hproperties.1,
    (graphonEntropy_pos_iff_graphonRandomMass_pos W).mp hEntropy⟩

/-- The unrestricted positive-random induced-star domain is nonempty.  A
witness is obtained from any interior fixed-density candidate. -/
theorem positiveRandomInducedFreeGraphons_inducedStar_nonempty
    (k : ℕ) (hk : 3 ≤ k) :
    (positiveRandomInducedFreeGraphons (inducedStar k)).Nonempty := by
  obtain ⟨W, hedge, hfree, hrandom⟩ :=
    positiveRandomFixedDensityGraphons_inducedStar_nonempty
      k hk (1 / 2 : ℝ) (by constructor <;> norm_num)
  exact ⟨W, hfree, hrandom⟩

/-- The positive-random restriction has the same value as the full
fixed-density induced-star variational problem.  This theorem is entirely
local and has no dependency on the HJS, BCLSV, or Janson sampling inputs. -/
theorem positiveRandomFixedDensityEntropyValue_inducedStar_eq
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    positiveRandomFixedDensityEntropyValue (inducedStar k) γ =
      entropyDensity k γ := by
  have hdomain := positiveRandomFixedDensityGraphons_inducedStar_nonempty
    k hk γ hγ
  have hvalues :
      (graphonEntropy ''
        positiveRandomFixedDensityGraphons (inducedStar k) γ).Nonempty := by
    obtain ⟨W, hW⟩ := hdomain
    exact ⟨graphonEntropy W, W, hW, rfl⟩
  have hupper : ∀ z ∈
      (graphonEntropy ''
        positiveRandomFixedDensityGraphons (inducedStar k) γ),
      z ≤ entropyDensity k γ := by
    rintro _ ⟨W, hW, rfl⟩
    exact graphonEntropy_le_entropyDensity k hk γ hγ W
      (positiveRandomFixedDensityGraphons_inducedStar_subset k γ hW)
  have hbounded : BddAbove
      (graphonEntropy ''
        positiveRandomFixedDensityGraphons (inducedStar k) γ) := by
    exact ⟨entropyDensity k γ, hupper⟩
  apply le_antisymm
  · unfold positiveRandomFixedDensityEntropyValue
    exact csSup_le hvalues hupper
  · obtain ⟨W, hW⟩ := candidateOptimizerFamily_nonempty k hk γ hγ
    have hproperties := VgammaOpt k hk γ hγ hW
    have hEntropy : 0 < graphonEntropy W := by
      rw [hproperties.2.2]
      exact entropyDensity_pos k hk γ hγ
    rw [← hproperties.2.2]
    unfold positiveRandomFixedDensityEntropyValue
    exact le_csSup hbounded ⟨W,
      ⟨hproperties.2.1, hproperties.1,
        (graphonEntropy_pos_iff_graphonRandomMass_pos W).mp hEntropy⟩,
      rfl⟩

/-- Paper: Theorem `thm:main-entropy`.

For every interior fixed edge density, the labeled induced-star-free graph
count has the entropy-density exponent. -/
theorem inducedStarFixedDensityEntropyAsymptotic
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m γ) :
    Tendsto
      (fun n ↦ normalizedLogGraphCount n
        (inducedStarFreeGraphCountWithEdges k n (m n)))
      atTop (nhds (entropyDensity k γ)) := by
  have hdomain :
      (positiveRandomFixedDensityGraphons (inducedStar k) γ).Nonempty :=
    positiveRandomFixedDensityGraphons_inducedStar_nonempty k hk γ hγ
  have htransfer := inducedFreeFixedDensityEnumeration
    (inducedStar k) γ hγ m hm hdomain
  rw [positiveRandomFixedDensityEntropyValue_inducedStar_eq k hk γ hγ]
    at htransfer
  exact htransfer

/-! ## Unconditioned induced-star probability -/

/-- The positive-random induced-star rate agrees with the explicit scalar
rate function.  The first equality is the local direct-sum/join approximation;
the remaining two are the full-domain graphon optimization. -/
theorem positiveRandomInducedStarFreeRateValue_eq
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    positiveRandomInducedFreeRateValue (inducedStar k) p =
      rateFunction k p := by
  calc
    positiveRandomInducedFreeRateValue (inducedStar k) p =
        inducedFreeGraphonRateValue (inducedStar k) p :=
      positiveRandomInducedFreeRateValue_eq_full
        (inducedStar k) p hp
        (positiveRandomInducedFreeGraphons_inducedStar_nonempty k hk)
    _ = gnpGraphonVariationalValue k p :=
      inducedFreeGraphonRateValue_inducedStar_eq k p
    _ = rateFunction k p :=
      gnpGraphonVariationalValue_eq_rateFunction k hk p hp

/-- Paper: Theorem `thm:main-rate`. The positive-random and full feasible
variational domains have the same rate value. -/
theorem inducedStarGnpLargeDeviationRate
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    Tendsto
      (fun n ↦ normalizedLogProbability n
        (gnpInducedStarFreeProbability k n p))
      atTop (nhds (-rateFunction k p)) := by
  have htransfer := inducedFreeGnpLargeDeviation
    (inducedStar k) p hp
    (positiveRandomInducedFreeGraphons_inducedStar_nonempty k hk)
  simpa only [positiveRandomInducedStarFreeRateValue_eq k hk p hp] using
    htransfer

end InducedStars
