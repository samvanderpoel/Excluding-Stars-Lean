import InducedStars.Graphon.SetDistance
import InducedStars.Graphon.Semicontinuity
import InducedStars.Main.VariationalConsequences

/-!
# Strict gaps away from graphon optimizer sets

This file characterizes both optimizer sets by equality in their universal
variational bounds.  Sequential cut compactness and semicontinuity then give
strict objective gaps on every fixed positive cut-distance complement.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- Within the fixed-density feasible set, attaining the explicit entropy
value is equivalent to being an entropy optimizer. -/
theorem mem_fixedDensityOptimizers_iff_entropy_eq
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    {W : Graphon} (hW : W ∈ fixedDensityFeasible k γ) :
    W ∈ fixedDensityOptimizers k γ ↔
      graphonEntropy W = entropyDensity k γ := by
  constructor
  · intro hopt
    exact hopt.entropy_eq_entropyDensity hk hγ
  · intro heq
    refine ⟨hW, ?_⟩
    intro U hU
    calc
      graphonEntropy U ≤ entropyDensity k γ :=
        graphonEntropy_le_entropyDensity k hk γ hγ U hU
      _ = graphonEntropy W := heq.symm

/-- Within the induced-star-free set, attaining the explicit conditioned
rate is equivalent to being a relative-entropy optimizer. -/
theorem mem_gnpGraphonOptimizers_iff_relativeEntropy_eq
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    {W : Graphon} (hW : W ∈ inducedStarFreeGraphons k) :
    W ∈ gnpGraphonOptimizers k p ↔
      graphonRelativeEntropy p W = rateFunction k p := by
  constructor
  · intro hopt
    exact gnpOptimizer_relativeEntropy_eq_rateFunction k hk p hp hopt
  · intro heq
    refine ⟨hW, ?_⟩
    intro U hU
    have hvalue :
        gnpGraphonVariationalValue k p ≤ graphonRelativeEntropy p U := by
      unfold gnpGraphonVariationalValue
      exact csInf_le (gnpGraphonRelativeEntropyValues_bddBelow k p hp)
        ⟨U, hU, rfl⟩
    rw [gnpGraphonVariationalValue_eq_rateFunction k hk p hp] at hvalue
    rw [heq]
    exact hvalue

/-- At fixed density, graphons a fixed positive cut distance from the
optimizer set lose a uniform positive amount of entropy. -/
private theorem exists_fixedDensityEntropyGap_raw
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ W : Graphon,
        W ∈ fixedDensityFeasible k γ →
        ε ≤ cutDistToSet W (fixedDensityOptimizers k γ) →
        graphonEntropy W ≤ entropyDensity k γ - c := by
  by_contra hgap
  push_neg at hgap
  let δ : ℕ → ℝ := fun n ↦ 1 / ((n + 1 : ℕ) : ℝ)
  have hδpos (n : ℕ) : 0 < δ n := by
    dsimp [δ]
    positivity
  let Wseq : ℕ → Graphon := fun n ↦
    Classical.choose (hgap (δ n) (hδpos n))
  have hWseq (n : ℕ) :
      Wseq n ∈ fixedDensityFeasible k γ ∧
      ε ≤ cutDistToSet (Wseq n) (fixedDensityOptimizers k γ) ∧
      entropyDensity k γ - δ n < graphonEntropy (Wseq n) :=
    Classical.choose_spec (hgap (δ n) (hδpos n))
  obtain ⟨σ, hσ, W, hcut⟩ :=
    PriorLiterature.bclsvGraphonSequentialCompactness Wseq
  have hWfeasible : W ∈ fixedDensityFeasible k γ :=
    mem_fixedDensityFeasible_of_cutDist_tendsto_zero
      (fun n ↦ Wseq (σ n)) W (fun n ↦ (hWseq (σ n)).1) hcut
  have hWfar :
      ε ≤ cutDistToSet W (fixedDensityOptimizers k γ) :=
    le_cutDistToSet_of_tendsto
      (fun n ↦ Wseq (σ n)) W
      (fixedDensityOptimizers_nonempty k hk γ hγ) hcut
      (fun n ↦ (hWseq (σ n)).2.1)
  have hδtendsto : Tendsto δ atTop (nhds 0) := by
    simpa only [δ, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hδsub : Tendsto (fun n ↦ δ (σ n)) atTop (nhds 0) :=
    hδtendsto.comp hσ.tendsto_atTop
  have hlower : entropyDensity k γ ≤ graphonEntropy W := by
    apply le_of_forall_pos_le_add
    intro η hη
    have hentropy :=
      graphonEntropy_eventually_le_of_cutDist_tendsto_zero
        (fun n ↦ Wseq (σ n)) W hcut (half_pos hη)
    have hsmall : ∀ᶠ n in atTop, δ (σ n) < η / 2 :=
      (tendsto_order.mp hδsub).2 _ (half_pos hη)
    obtain ⟨n, hnEntropy, hnSmall⟩ := (hentropy.and hsmall).exists
    linarith [(hWseq (σ n)).2.2]
  have hupper : graphonEntropy W ≤ entropyDensity k γ :=
    graphonEntropy_le_entropyDensity k hk γ hγ W hWfeasible
  have hopt : W ∈ fixedDensityOptimizers k γ :=
    (mem_fixedDensityOptimizers_iff_entropy_eq
      k hk γ hγ hWfeasible).2 (le_antisymm hupper hlower)
  have hzero := cutDistToSet_self_eq_zero hopt
  rw [hzero] at hWfar
  linarith

/-- At fixed density, the entropy gap can be chosen smaller than the
positive optimum value.  This is the form needed by the possibly-empty HJS
counting wrapper, whose comparison bound must remain strictly positive. -/
theorem exists_fixedDensityEntropyGapWithPositiveRemainder
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ 0 < entropyDensity k γ - c ∧
      ∀ W : Graphon,
        W ∈ fixedDensityFeasible k γ →
        ε ≤ cutDistToSet W (fixedDensityOptimizers k γ) →
        graphonEntropy W ≤ entropyDensity k γ - c := by
  obtain ⟨d, hd, hgap⟩ :=
    exists_fixedDensityEntropyGap_raw k hk γ hγ ε hε
  let c := min d (entropyDensity k γ / 2)
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min hd (half_pos (entropyDensity_pos k hk γ hγ))
  refine ⟨c, hc, ?_, ?_⟩
  · have hcle : c ≤ entropyDensity k γ / 2 := min_le_right _ _
    linarith [entropyDensity_pos k hk γ hγ]
  · intro W hW hfar
    have hdBound := hgap W hW hfar
    have hcd : c ≤ d := min_le_left _ _
    linarith

/-- At fixed density, graphons a fixed positive cut distance from the
optimizer set lose a uniform positive amount of entropy. -/
theorem exists_fixedDensityEntropyGap
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ W : Graphon,
        W ∈ fixedDensityFeasible k γ →
        ε ≤ cutDistToSet W (fixedDensityOptimizers k γ) →
        graphonEntropy W ≤ entropyDensity k γ - c := by
  obtain ⟨c, hc, _hremainder, hgap⟩ :=
    exists_fixedDensityEntropyGapWithPositiveRemainder k hk γ hγ ε hε
  exact ⟨c, hc, hgap⟩

/-- In the conditioned graphon problem, graphons a fixed positive cut
distance from the optimizer set pay a uniform positive relative-entropy
penalty. -/
theorem exists_gnpRelativeEntropyGap
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ W : Graphon,
        W ∈ inducedStarFreeGraphons k →
        ε ≤ cutDistToSet W (gnpGraphonOptimizers k p) →
        rateFunction k p + c ≤ graphonRelativeEntropy p W := by
  by_contra hgap
  push_neg at hgap
  let δ : ℕ → ℝ := fun n ↦ 1 / ((n + 1 : ℕ) : ℝ)
  have hδpos (n : ℕ) : 0 < δ n := by
    dsimp [δ]
    positivity
  let Wseq : ℕ → Graphon := fun n ↦
    Classical.choose (hgap (δ n) (hδpos n))
  have hWseq (n : ℕ) :
      Wseq n ∈ inducedStarFreeGraphons k ∧
      ε ≤ cutDistToSet (Wseq n) (gnpGraphonOptimizers k p) ∧
      graphonRelativeEntropy p (Wseq n) < rateFunction k p + δ n :=
    Classical.choose_spec (hgap (δ n) (hδpos n))
  obtain ⟨σ, hσ, W, hcut⟩ :=
    PriorLiterature.bclsvGraphonSequentialCompactness Wseq
  have hWfree : W ∈ inducedStarFreeGraphons k :=
    mem_inducedStarFreeGraphons_of_cutDist_tendsto_zero
      (fun n ↦ Wseq (σ n)) W (fun n ↦ (hWseq (σ n)).1) hcut
  have hWfar :
      ε ≤ cutDistToSet W (gnpGraphonOptimizers k p) :=
    le_cutDistToSet_of_tendsto
      (fun n ↦ Wseq (σ n)) W
      (gnpGraphonOptimizers_nonempty k hk p hp) hcut
      (fun n ↦ (hWseq (σ n)).2.1)
  have hδtendsto : Tendsto δ atTop (nhds 0) := by
    simpa only [δ, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hδsub : Tendsto (fun n ↦ δ (σ n)) atTop (nhds 0) :=
    hδtendsto.comp hσ.tendsto_atTop
  have hupper : graphonRelativeEntropy p W ≤ rateFunction k p := by
    apply le_of_forall_pos_le_add
    intro η hη
    have hlsc :=
      graphonRelativeEntropy_eventually_ge_of_cutDist_tendsto_zero
        hp (fun n ↦ Wseq (σ n)) W hcut (half_pos hη)
    have hsmall : ∀ᶠ n in atTop, δ (σ n) < η / 2 :=
      (tendsto_order.mp hδsub).2 _ (half_pos hη)
    obtain ⟨n, hnLsc, hnSmall⟩ := (hlsc.and hsmall).exists
    linarith [(hWseq (σ n)).2.2]
  have hlower : rateFunction k p ≤ graphonRelativeEntropy p W := by
    calc
      rateFunction k p ≤ rateAtDensity k p (graphonEdgeDensity W) :=
        (rateScalarMinimization k hk p hp).1 _
          (graphonEdgeDensity_mem_Icc W)
      _ ≤ graphonRelativeEntropy p W :=
        graphonRelativeEntropy_ge_rateAt_edgeDensity k hk p hp W hWfree
  have hopt : W ∈ gnpGraphonOptimizers k p :=
    (mem_gnpGraphonOptimizers_iff_relativeEntropy_eq
      k hk p hp hWfree).2 (le_antisymm hupper hlower)
  have hzero := cutDistToSet_self_eq_zero hopt
  rw [hzero] at hWfar
  linarith

end InducedStars
