import InducedStars.Asymptotics.ExponentialRatio
import InducedStars.Asymptotics.RoughStructureUpper
import InducedStars.Main.AsymptoticConsequences

/-!
# Exponential rough structure around graphon optimizers

This file combines the strict optimizer gaps and bad-family upper bounds
with the already-proved total fixed-density and `G(n,p)` asymptotics.  The
resulting probability ratios decay as `exp (-C n²)`, with the fixed-density
constant chosen before—and independently of—the exact-edge sequence.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-! ## Lower bounds for the two conditioning families -/

/-- The fixed-density main entropy asymptotic gives every prescribed
positive lower tolerance eventually. -/
theorem eventually_fixedDensityTotal_count_lower
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m γ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      entropyDensity k γ - δ ≤
        normalizedLogGraphCount n
          (inducedStarFreeGraphCountWithEdges k n (m n)) := by
  have hlimit := inducedStarFixedDensityEntropyAsymptotic
    k hk γ hγ m hm
  exact ((tendsto_order.mp hlimit).1
    (entropyDensity k γ - δ) (sub_lt_self _ hδ)).mono
      (fun _ hn ↦ hn.le)

/-- Exact-edge induced-star-free conditioning families are eventually
nonempty for every interior limiting density. -/
theorem eventually_inducedStarFreeGraphFinsetWithEdges_nonempty
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m γ) :
    ∀ᶠ n in atTop,
      (inducedStarFreeGraphFinsetWithEdges k n (m n)).Nonempty := by
  exact eventually_inducedFreeGraphFinsetWithEdges_nonempty
    (inducedStar k) γ m hm
    (positiveRandomFixedDensityGraphons_inducedStar_nonempty k hk γ hγ)

/-- The induced-star-free `G(n,p)` main-rate asymptotic gives every
prescribed lower tolerance eventually. -/
theorem eventually_gnpInducedStarFreeProbability_lower
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      -rateFunction k p - δ ≤
        normalizedLogProbability n
          (gnpInducedStarFreeProbability k n p) := by
  have hlimit := inducedStarGnpLargeDeviationRate k hk p hp
  have hlower : -rateFunction k p - δ < -rateFunction k p := by
    linarith
  exact ((tendsto_order.mp hlimit).1 _ hlower).mono
    (fun _ hn ↦ hn.le)

/-! ## Paper-facing rough-structure theorems -/

/-- Paper: Lemma `lemma:rough-struc-fixed-g`.

For each positive cut-distance tolerance there is an exponential constant
`C > 0`, depending only on `k`, `γ`, and the tolerance, such that for every
exact-edge sequence of limiting density `γ`, a uniformly chosen labeled
induced-star-free graph is optimizer-far with probability at most
`exp (-C n²)` eventually. -/
theorem inducedStarFixedDensityRoughStructure
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m γ →
        ∀ᶠ n in atTop,
          fixedDensityOptimizerFarProbability k γ ε m n ≤
            Real.exp (-C * (n : ℝ) ^ 2) := by
  obtain ⟨c, hc, _hremainder, hbad⟩ :=
    eventually_fixedDensityOptimizerFar_count_upper k hk γ hγ ε hε
  let C : ℝ := (c / 2) * Real.log 2 / 4
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro m hm
  have hbadUpper := hbad m hm
  have htotalLower := eventually_fixedDensityTotal_count_lower
    k hk γ hγ m hm (c / 4) (by positivity)
  have hnonempty :=
    eventually_inducedStarFreeGraphFinsetWithEdges_nonempty
      k hk γ hγ m hm
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    eventually_atTop.2 ⟨2, fun _ hn ↦ hn⟩
  filter_upwards [hbadUpper, htotalLower, hnonempty, hlarge] with
    n hnBad hnTotal hnNonempty hnLarge
  have hden :
      0 < ((inducedStarFreeGraphFinsetWithEdges k n (m n)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hnNonempty
  have hgapCounts :
      normalizedLogGraphCount n
          (fixedDensityOptimizerFarGraphFinset k γ ε m n).card ≤
        normalizedLogGraphCount n
            (inducedStarFreeGraphFinsetWithEdges k n (m n)).card - c / 2 := by
    change normalizedLogGraphCount n
          (fixedDensityOptimizerFarGraphFinset k γ ε m n).card ≤
        normalizedLogGraphCount n
            (inducedStarFreeGraphCountWithEdges k n (m n)) - c / 2
    linarith
  have hgapProbability :
      normalizedLogProbability n
          ((fixedDensityOptimizerFarGraphFinset k γ ε m n).card : ℝ) ≤
        normalizedLogProbability n
            ((inducedStarFreeGraphFinsetWithEdges k n (m n)).card : ℝ) -
          c / 2 := by
    simpa only [normalizedLogProbability, normalizedLogGraphCount] using
      hgapCounts
  have hratio := ratio_le_exp_neg_square_of_normalizedLog_gap
    hnLarge (Nat.cast_nonneg _ :
      0 ≤ ((fixedDensityOptimizerFarGraphFinset k γ ε m n).card : ℝ))
    hden (half_pos hc) hgapProbability
  rw [fixedDensityOptimizerFarProbability_eq_card_ratio]
  simpa only [C] using hratio

/-- Paper: Lemma `lemma:rough-struc-gnp`.

Conditioned on induced-star-freeness, a labeled `G(n,p)` graph is at fixed
positive cut distance from the complete conditioned optimizer set with
probability at most `exp (-C n²)` eventually.  The local proof uses positive
KL throughout and incorporates the manuscript repair `CFD-009`. -/
theorem inducedStarGnpConditionedRoughStructure
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n in atTop,
        gnpConditionedOptimizerFarProbability k n p ε ≤
          Real.exp (-C * (n : ℝ) ^ 2) := by
  obtain ⟨c, hc, hbad⟩ :=
    eventually_gnpOptimizerFarProbability_upper k hk p hp ε hε
  let C : ℝ := (c / 2) * Real.log 2 / 4
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  have htotalLower := eventually_gnpInducedStarFreeProbability_lower
    k hk p hp (c / 4) (by positivity)
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    eventually_atTop.2 ⟨2, fun _ hn ↦ hn⟩
  filter_upwards [hbad, htotalLower, hlarge] with
    n hnBad hnTotal hnLarge
  have hden : 0 < gnpInducedStarFreeProbability k n p :=
    gnpConditionedOptimizerFarProbability_denominator_pos hk hp
  rcases hnBad with hzero | hnBad
  · rw [gnpConditionedOptimizerFarProbability, hzero, zero_div]
    exact (Real.exp_pos _).le
  · have hgap :
        normalizedLogProbability n
            (gnpOptimizerFarInducedStarProbability k n p ε) ≤
          normalizedLogProbability n
              (gnpInducedStarFreeProbability k n p) - c / 2 := by
      linarith
    have hratio := ratio_le_exp_neg_square_of_normalizedLog_gap
      hnLarge
      (gnpGraphEventProbability_nonneg ⟨hp.1.le, hp.2.le⟩
        (gnpOptimizerFarInducedStarFinset k p ε n))
      hden (half_pos hc) hgap
    simpa only [gnpConditionedOptimizerFarProbability,
      gnpOptimizerFarInducedStarProbability, C] using hratio

end InducedStars
