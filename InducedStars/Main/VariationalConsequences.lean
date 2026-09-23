import InducedStars.Graphon.Optimization
import InducedStars.Graphon.RelativeEntropy
import InducedStars.Graphon.SubcriticalMultiplicity
import InducedStars.PriorLiterature

/-!
# Variational consequences

This file proves the paper's fixed-density entropy value and optimizer
multiplicity, then completes the conditioned graphon variational value,
cut-saturated optimizer classification, and three-regime multiplicity theorem.
-/

noncomputable section

open Set

namespace InducedStars

/-! ## Fixed-density variational value -/

/-- The literal supremum in the paper's fixed-density graphon variational
problem `eqn:var-prob-intro-gamma`. -/
noncomputable def fixedDensityEntropyValue (k : ℕ) (γ : ℝ) : ℝ :=
  sSup (graphonEntropy '' fixedDensityFeasible k γ)

/-- The entropy-value set in the fixed-density problem is nonempty throughout
the paper's interior parameter range. -/
theorem fixedDensityEntropyValues_nonempty
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    (graphonEntropy '' fixedDensityFeasible k γ).Nonempty := by
  obtain ⟨W, hW⟩ := candidateOptimizerFamily_nonempty k hk γ hγ
  exact ⟨graphonEntropy W,
    W, candidate_mem_fixedDensityFeasible k hk γ hγ hW, rfl⟩

/-- The entropy-value set in the fixed-density problem is bounded above by
the explicit entropy profile. -/
theorem fixedDensityEntropyValues_bddAbove
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    BddAbove (graphonEntropy '' fixedDensityFeasible k γ) := by
  refine ⟨entropyDensity k γ, ?_⟩
  rintro _ ⟨W, hW, rfl⟩
  exact graphonEntropy_le_entropyDensity k hk γ hγ W hW

/-- Exact value of the fixed-density graphon variational problem. -/
theorem fixedDensityEntropyValue_eq
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    fixedDensityEntropyValue k γ = entropyDensity k γ := by
  unfold fixedDensityEntropyValue
  apply le_antisymm
  · refine csSup_le (fixedDensityEntropyValues_nonempty k hk γ hγ) ?_
    rintro _ ⟨W, hW, rfl⟩
    exact graphonEntropy_le_entropyDensity k hk γ hγ W hW
  · obtain ⟨W, hW⟩ := candidateOptimizerFamily_nonempty k hk γ hγ
    have hproperties := VgammaOpt k hk γ hγ hW
    rw [← hproperties.2.2]
    exact le_csSup (fixedDensityEntropyValues_bddAbove k hk γ hγ)
      ⟨W, candidate_mem_fixedDensityFeasible k hk γ hγ hW, rfl⟩

/-! ## Uniqueness at and above the critical density -/

/-- The optimizer set is nonempty and any two of its elements are equivalent
in the paper's common-measure-preserving-pullback sense. -/
def UniqueOptimizerUpToEquivalence (k : ℕ) (γ : ℝ) : Prop :=
  (fixedDensityOptimizers k γ).Nonempty ∧
    ∀ U ∈ fixedDensityOptimizers k γ,
      ∀ W ∈ fixedDensityOptimizers k γ,
        GraphonEquivalent U W

/-- At and above the critical density, the fixed-density optimizer is unique
up to the exact graphon equivalence relation used in the paper. -/
theorem fixedDensityOptimizer_uniqueUpToEquivalence_of_gammaK_le
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ico (gammaK k) 1) :
    UniqueOptimizerUpToEquivalence k γ := by
  have hγIoo : γ ∈ Ioo (0 : ℝ) 1 :=
    ⟨(gammaK_pos hk).trans_le hγ.1, hγ.2⟩
  refine ⟨fixedDensityOptimizers_nonempty k hk γ hγIoo, ?_⟩
  intro U hU W hW
  obtain ⟨VU, hVU, hcutU⟩ :=
    exists_candidate_cutEquivalent_of_optimizer k hk γ hγIoo U hU
  obtain ⟨VW, hVW, hcutW⟩ :=
    exists_candidate_cutEquivalent_of_optimizer k hk γ hγIoo W hW
  have hVUeq : VU = Wstar k hk γ ⟨hγ.1, hγ.2⟩ := by
    rw [candidateOptimizerFamily_of_ge hk hγIoo hγ.1] at hVU
    simpa only [mem_singleton_iff] using hVU
  have hVWeq : VW = Wstar k hk γ ⟨hγ.1, hγ.2⟩ := by
    rw [candidateOptimizerFamily_of_ge hk hγIoo hγ.1] at hVW
    simpa only [mem_singleton_iff] using hVW
  subst VU
  subst VW
  apply graphonEquivalent_of_cutDist_eq_zero
  apply le_antisymm
  · calc
      cutDist U W ≤
          cutDist U (Wstar k hk γ ⟨hγ.1, hγ.2⟩) +
            cutDist (Wstar k hk γ ⟨hγ.1, hγ.2⟩) W :=
        cutDist_triangle U (Wstar k hk γ ⟨hγ.1, hγ.2⟩) W
      _ = 0 := by
        rw [hcutU, cutDist_comm
          (Wstar k hk γ ⟨hγ.1, hγ.2⟩) W, hcutW, zero_add]
  · exact cutDist_nonneg U W

/-! ## Optimizer multiplicity -/

/-- Paper: Theorem `thm:ent-graphons`.

At and above the transition density the fixed-density optimizer is unique up
to the paper's common-pullback equivalence.  Below the transition there is an
explicit sequence of pairwise non-equivalent optimizers. -/
theorem fixedDensityOptimizerMultiplicity
    (k : ℕ) (hk : 3 ≤ k) :
    (∀ γ : ℝ,
      γ ∈ Ico (gammaK k) 1 →
        UniqueOptimizerUpToEquivalence k γ) ∧
    (∀ γ : ℝ,
      γ ∈ Ioo (0 : ℝ) (gammaK k) →
        ∃ Wseq : ℕ → Graphon,
          (∀ n, Wseq n ∈ fixedDensityOptimizers k γ) ∧
          ∀ ⦃m n : ℕ⦄, m ≠ n →
            ¬ GraphonEquivalent (Wseq m) (Wseq n)) := by
  constructor
  · intro γ hγ
    exact fixedDensityOptimizer_uniqueUpToEquivalence_of_gammaK_le k hk γ hγ
  · intro γ hγ
    exact exists_pairwiseNonEquivalent_subcriticalOptimizers k hk γ hγ

/-! ## Conditioned graphon candidates -/

/-- The canonical, unsaturated conditioned optimizer family from the paper's
display `eqn:CpStarFormalDef`.  At the critical probability it explicitly
contains the zero graphon and all positive-density fixed-density candidates
through density `gammaK k`. -/
noncomputable def gnpCandidateFamily (k : ℕ) (p : ℝ) : Set Graphon :=
  if _hpLow : p < pK k then
    {zeroGraphon}
  else if _hpCrit : p = pK k then
    {zeroGraphon} ∪
      {W | ∃ γ ∈ Ioc (0 : ℝ) (gammaK k),
        W ∈ candidateOptimizerFamily k γ}
  else
    candidateOptimizerFamily k (gammaFromProbability k p)

theorem gnpCandidateFamily_of_lt_pK {k : ℕ} {p : ℝ}
    (hp : p < pK k) :
    gnpCandidateFamily k p = {zeroGraphon} := by
  simp [gnpCandidateFamily, hp]

@[simp] theorem gnpCandidateFamily_at_pK (k : ℕ) :
    gnpCandidateFamily k (pK k) =
      {zeroGraphon} ∪
        {W | ∃ γ ∈ Ioc (0 : ℝ) (gammaK k),
          W ∈ candidateOptimizerFamily k γ} := by
  simp [gnpCandidateFamily]

theorem gnpCandidateFamily_of_pK_lt {k : ℕ} {p : ℝ}
    (hp : pK k < p) :
    gnpCandidateFamily k p =
      candidateOptimizerFamily k (gammaFromProbability k p) := by
  simp [gnpCandidateFamily, hp.not_gt, hp.ne']

/-- The zero graphon is induced-star-free as soon as the star has an edge. -/
theorem zeroGraphon_mem_inducedStarFreeGraphons
    (k : ℕ) (hk : 1 ≤ k) :
    zeroGraphon ∈ inducedStarFreeGraphons k := by
  exact graphonInducedDensity_inducedStar_zeroGraphon k hk

/-- The canonical conditioned candidate family is nonempty throughout the
paper's probability range. -/
theorem gnpCandidateFamily_nonempty
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    (gnpCandidateFamily k p).Nonempty := by
  by_cases hsub : p < pK k
  · rw [gnpCandidateFamily_of_lt_pK hsub]
    exact singleton_nonempty zeroGraphon
  · by_cases hcrit : p = pK k
    · subst p
      rw [gnpCandidateFamily_at_pK]
      exact (singleton_nonempty zeroGraphon).mono subset_union_left
    · have hsuper : pK k < p :=
        lt_of_le_of_ne (le_of_not_gt hsub) (Ne.symm hcrit)
      rw [gnpCandidateFamily_of_pK_lt hsuper]
      have hγp := gammaFromProbability_mem_Ioo hk hsuper hp.2
      exact candidateOptimizerFamily_nonempty k hk _
        ⟨(gammaK_pos hk).trans hγp.1, hγp.2⟩

/-- Every canonical conditioned candidate is induced-star-free and attains
the scalar rate. -/
theorem gnpCandidate_properties
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    {W : Graphon} (hW : W ∈ gnpCandidateFamily k p) :
    W ∈ inducedStarFreeGraphons k ∧
      graphonRelativeEntropy p W = rateFunction k p := by
  by_cases hsub : p < pK k
  · rw [gnpCandidateFamily_of_lt_pK hsub] at hW
    have hWzero : W = zeroGraphon := by simpa using hW
    subst W
    refine ⟨zeroGraphon_mem_inducedStarFreeGraphons k (by omega), ?_⟩
    rw [graphonRelativeEntropy_zeroGraphon hp, rateFunction_of_le hsub.le]
  · by_cases hcrit : p = pK k
    · subst p
      have hpK : pK k ∈ Ioo (0 : ℝ) 1 :=
        pK_mem_Ioo (show 2 ≤ k by omega)
      rw [gnpCandidateFamily_at_pK] at hW
      rcases hW with hzero | ⟨γ, hγ, hcandidate⟩
      · have hWzero : W = zeroGraphon := by simpa using hzero
        subst W
        refine ⟨zeroGraphon_mem_inducedStarFreeGraphons k (by omega), ?_⟩
        rw [graphonRelativeEntropy_zeroGraphon hpK, rateFunction_of_le le_rfl]
      · have hγIoo : γ ∈ Ioo (0 : ℝ) 1 :=
          ⟨hγ.1, hγ.2.trans_lt (gammaK_lt_one hk)⟩
        have hopt := candidate_mem_fixedDensityOptimizers
          k hk γ hγIoo hcandidate
        refine ⟨hopt.1.1, ?_⟩
        calc
          graphonRelativeEntropy (pK k) W =
              rateAtDensity k (pK k) γ :=
            (graphonRelativeEntropy_eq_rateAtDensity_iff_optimizer
              k hk (pK k) hpK γ hγIoo W hopt.1).2 hopt
          _ = rateFunction k (pK k) :=
            (rateAtDensity_critical_minimization hk
              ⟨hγIoo.1.le, hγIoo.2.le⟩).2.2 ⟨hγ.1.le, hγ.2⟩
    · have hsuper : pK k < p :=
        lt_of_le_of_ne (le_of_not_gt hsub) (Ne.symm hcrit)
      rw [gnpCandidateFamily_of_pK_lt hsuper] at hW
      have hγp := gammaFromProbability_mem_Ioo hk hsuper hp.2
      have hγpIoo : gammaFromProbability k p ∈ Ioo (0 : ℝ) 1 :=
        ⟨(gammaK_pos hk).trans hγp.1, hγp.2⟩
      have hopt := candidate_mem_fixedDensityOptimizers
        k hk _ hγpIoo hW
      refine ⟨hopt.1.1, ?_⟩
      calc
        graphonRelativeEntropy p W =
            rateAtDensity k p (gammaFromProbability k p) :=
          (graphonRelativeEntropy_eq_rateAtDensity_iff_optimizer
            k hk p hp _ hγpIoo W hopt.1).2 hopt
        _ = rateFunction k p :=
          rateAtDensity_gammaFromProbability_eq_rateFunction hk hp hsuper

/-! ## Exact conditioned variational value -/

/-- The feasible relative-entropy value set is nonempty. -/
theorem gnpGraphonRelativeEntropyValues_nonempty
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) :
    (graphonRelativeEntropy p '' inducedStarFreeGraphons k).Nonempty := by
  exact ⟨graphonRelativeEntropy p zeroGraphon, zeroGraphon,
    zeroGraphon_mem_inducedStarFreeGraphons k (by omega), rfl⟩

/-- The feasible relative-entropy value set is bounded below. -/
theorem gnpGraphonRelativeEntropyValues_bddBelow
    (k : ℕ) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    BddBelow (graphonRelativeEntropy p '' inducedStarFreeGraphons k) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨W, _, rfl⟩
  exact graphonRelativeEntropy_nonneg hp W

/-- Exact value of the conditioned graphon variational problem. -/
theorem gnpGraphonVariationalValue_eq_rateFunction
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    gnpGraphonVariationalValue k p = rateFunction k p := by
  unfold gnpGraphonVariationalValue
  apply le_antisymm
  · obtain ⟨W, hW⟩ := gnpCandidateFamily_nonempty k hk p hp
    have hproperties := gnpCandidate_properties k hk p hp hW
    rw [← hproperties.2]
    exact csInf_le (gnpGraphonRelativeEntropyValues_bddBelow k p hp)
      ⟨W, hproperties.1, rfl⟩
  · refine le_csInf (gnpGraphonRelativeEntropyValues_nonempty k hk p) ?_
    rintro _ ⟨W, hfree, rfl⟩
    calc
      rateFunction k p ≤ rateAtDensity k p (graphonEdgeDensity W) :=
        (rateScalarMinimization k hk p hp).1 _
          (graphonEdgeDensity_mem_Icc W)
      _ ≤ graphonRelativeEntropy p W :=
        graphonRelativeEntropy_ge_rateAt_edgeDensity k hk p hp W hfree

/-- Every canonical conditioned candidate is a global conditioned optimizer. -/
theorem gnpCandidate_mem_optimizer
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    {W : Graphon} (hW : W ∈ gnpCandidateFamily k p) :
    W ∈ gnpGraphonOptimizers k p := by
  have hproperties := gnpCandidate_properties k hk p hp hW
  refine ⟨hproperties.1, ?_⟩
  intro U hU
  rw [hproperties.2]
  exact (rateScalarMinimization k hk p hp).1 _
    (graphonEdgeDensity_mem_Icc U) |>.trans
      (graphonRelativeEntropy_ge_rateAt_edgeDensity k hk p hp U hU)

/-- The conditioned optimizer set is nonempty. -/
theorem gnpGraphonOptimizers_nonempty
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    (gnpGraphonOptimizers k p).Nonempty := by
  obtain ⟨W, hW⟩ := gnpCandidateFamily_nonempty k hk p hp
  exact ⟨W, gnpCandidate_mem_optimizer k hk p hp hW⟩

/-! ## Conditioned optimizer classification -/

/-- A conditioned optimizer attains the explicit global rate. -/
theorem gnpOptimizer_relativeEntropy_eq_rateFunction
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    {W : Graphon} (hW : W ∈ gnpGraphonOptimizers k p) :
    graphonRelativeEntropy p W = rateFunction k p := by
  obtain ⟨V, hV⟩ := gnpCandidateFamily_nonempty k hk p hp
  have hVproperties := gnpCandidate_properties k hk p hp hV
  apply le_antisymm
  · exact (hW.relativeEntropy_le hVproperties.1).trans_eq hVproperties.2
  · calc
      rateFunction k p ≤ rateAtDensity k p (graphonEdgeDensity W) :=
        (rateScalarMinimization k hk p hp).1 _
          (graphonEdgeDensity_mem_Icc W)
      _ ≤ graphonRelativeEntropy p W :=
        graphonRelativeEntropy_ge_rateAt_edgeDensity k hk p hp W hW.feasible

/-- The edge density of a conditioned optimizer attains equality in the
one-dimensional scalar minimization. -/
theorem gnpOptimizer_rateAt_edgeDensity_eq_rateFunction
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    {W : Graphon} (hW : W ∈ gnpGraphonOptimizers k p) :
    rateAtDensity k p (graphonEdgeDensity W) = rateFunction k p := by
  have hgraph := graphonRelativeEntropy_ge_rateAt_edgeDensity
    k hk p hp W hW.feasible
  have hvalue := gnpOptimizer_relativeEntropy_eq_rateFunction k hk p hp hW
  exact le_antisymm (hgraph.trans_eq hvalue)
    ((rateScalarMinimization k hk p hp).1 _ (graphonEdgeDensity_mem_Icc W))

/-- Exact piecewise scalar classification of a conditioned optimizer's edge
density. -/
theorem gnpOptimizer_edgeDensity_classification
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    {W : Graphon} (hW : W ∈ gnpGraphonOptimizers k p) :
    if p < pK k then
      graphonEdgeDensity W = 0
    else if p = pK k then
      graphonEdgeDensity W ∈ Icc (0 : ℝ) (gammaK k)
    else
      graphonEdgeDensity W = gammaFromProbability k p := by
  exact ((rateScalarMinimization k hk p hp).2 _
    (graphonEdgeDensity_mem_Icc W)).1
      (gnpOptimizer_rateAt_edgeDensity_eq_rateFunction k hk p hp hW)

/-- A conditioned optimizer also attains equality in the graphon-to-scalar
reduction at its own edge density. -/
theorem gnpOptimizer_relativeEntropy_eq_rateAt_edgeDensity
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    {W : Graphon} (hW : W ∈ gnpGraphonOptimizers k p) :
    graphonRelativeEntropy p W =
      rateAtDensity k p (graphonEdgeDensity W) := by
  exact (gnpOptimizer_relativeEntropy_eq_rateFunction k hk p hp hW).trans
    (gnpOptimizer_rateAt_edgeDensity_eq_rateFunction k hk p hp hW).symm

/-- Elementwise conditioned optimizer classification: an optimizer is
exactly a cut-distance-zero representative of a canonical conditioned
candidate. -/
theorem mem_gnpGraphonOptimizers_iff_exists_candidate_cutDist_zero
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (W : Graphon) :
    W ∈ gnpGraphonOptimizers k p ↔
      ∃ V ∈ gnpCandidateFamily k p, cutDist W V = 0 := by
  constructor
  · intro hW
    have hrate := gnpOptimizer_rateAt_edgeDensity_eq_rateFunction
      k hk p hp hW
    have hgraph := gnpOptimizer_relativeEntropy_eq_rateAt_edgeDensity
      k hk p hp hW
    by_cases hsub : p < pK k
    · have hedgeZero :=
        (rateAtDensity_subcritical_minimization hk hp hsub
          (graphonEdgeDensity_mem_Icc W)).2.1 hrate
      have hWzero := (graphonEdgeDensity_eq_zero_iff W).1 hedgeZero
      subst W
      refine ⟨zeroGraphon, ?_, cutDist_self zeroGraphon⟩
      rw [gnpCandidateFamily_of_lt_pK hsub]
      exact mem_singleton zeroGraphon
    · by_cases hcrit : p = pK k
      · subst p
        have hγrange :=
          (rateAtDensity_critical_minimization hk
            (graphonEdgeDensity_mem_Icc W)).2.1 hrate
        by_cases hzero : graphonEdgeDensity W = 0
        · have hWzero := (graphonEdgeDensity_eq_zero_iff W).1 hzero
          subst W
          refine ⟨zeroGraphon, ?_, cutDist_self zeroGraphon⟩
          rw [gnpCandidateFamily_at_pK]
          exact Or.inl (mem_singleton zeroGraphon)
        · have hedgeIoo : graphonEdgeDensity W ∈ Ioo (0 : ℝ) 1 :=
            ⟨lt_of_le_of_ne hγrange.1 (Ne.symm hzero),
              hγrange.2.trans_lt (gammaK_lt_one hk)⟩
          have hfixed :=
            (graphonRelativeEntropy_eq_rateAt_edgeDensity_iff_optimizer
              k hk (pK k) (pK_mem_Ioo (show 2 ≤ k by omega)) W hW.feasible
                hedgeIoo).1 hgraph
          obtain ⟨V, hV, hcut⟩ :=
            exists_candidate_cutEquivalent_of_optimizer
              k hk (graphonEdgeDensity W) hedgeIoo W hfixed
          refine ⟨V, ?_, hcut⟩
          rw [gnpCandidateFamily_at_pK]
          exact Or.inr ⟨graphonEdgeDensity W,
            ⟨hedgeIoo.1, hγrange.2⟩, hV⟩
      · have hsuper : pK k < p :=
          lt_of_le_of_ne (le_of_not_gt hsub) (Ne.symm hcrit)
        have hedgeEq :=
          (rateAtDensity_supercritical_minimization hk hp hsuper
            (graphonEdgeDensity_mem_Icc W)).2.1 hrate
        have hγp := gammaFromProbability_mem_Ioo hk hsuper hp.2
        have hedgeIoo : graphonEdgeDensity W ∈ Ioo (0 : ℝ) 1 := by
          rw [hedgeEq]
          exact ⟨(gammaK_pos hk).trans hγp.1, hγp.2⟩
        have hfixedOwn :=
          (graphonRelativeEntropy_eq_rateAt_edgeDensity_iff_optimizer
            k hk p hp W hW.feasible hedgeIoo).1 hgraph
        have hfixed :
            W ∈ fixedDensityOptimizers k (gammaFromProbability k p) := by
          simpa only [hedgeEq] using hfixedOwn
        obtain ⟨V, hV, hcut⟩ :=
          exists_candidate_cutEquivalent_of_optimizer k hk _
            ⟨(gammaK_pos hk).trans hγp.1, hγp.2⟩ W hfixed
        refine ⟨V, ?_, hcut⟩
        rw [gnpCandidateFamily_of_pK_lt hsuper]
        exact hV
  · rintro ⟨V, hV, hcut⟩
    have hVopt := gnpCandidate_mem_optimizer k hk p hp hV
    exact hVopt.of_cutDist_eq_zero hp (by
      rw [cutDist_comm]
      exact hcut)

/-- Exact set-level conditioned optimizer classification under cut-distance
zero saturation. -/
theorem gnpGraphonOptimizers_eq_cutSaturation
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    gnpGraphonOptimizers k p = cutSaturation (gnpCandidateFamily k p) := by
  ext W
  exact mem_gnpGraphonOptimizers_iff_exists_candidate_cutDist_zero
    k hk p hp W

theorem gnpGraphonOptimizers_eq_of_lt_pK
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) (hsub : p < pK k) :
    gnpGraphonOptimizers k p = cutSaturation {zeroGraphon} := by
  rw [gnpGraphonOptimizers_eq_cutSaturation k hk p hp,
    gnpCandidateFamily_of_lt_pK hsub]

@[simp] theorem gnpGraphonOptimizers_at_pK
    (k : ℕ) (hk : 3 ≤ k) :
    gnpGraphonOptimizers k (pK k) =
      cutSaturation
        ({zeroGraphon} ∪
          {W | ∃ γ ∈ Ioc (0 : ℝ) (gammaK k),
            W ∈ candidateOptimizerFamily k γ}) := by
  rw [gnpGraphonOptimizers_eq_cutSaturation k hk (pK k)
    (pK_mem_Ioo (show 2 ≤ k by omega)), gnpCandidateFamily_at_pK]

theorem gnpGraphonOptimizers_eq_of_pK_lt
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) (hsuper : pK k < p) :
    gnpGraphonOptimizers k p =
      cutSaturation
        (candidateOptimizerFamily k (gammaFromProbability k p)) := by
  rw [gnpGraphonOptimizers_eq_cutSaturation k hk p hp,
    gnpCandidateFamily_of_pK_lt hsuper]

/-- Paper display `eqn:CpStarFormalDef`: the conditioned optimizer set in
its three explicit probability regimes, with cut saturation implementing
the paper's phrase "up to equivalence". -/
theorem gnpGraphonOptimizerSet_eq
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    gnpGraphonOptimizers k p =
      if p < pK k then
        cutSaturation {zeroGraphon}
      else if p = pK k then
        cutSaturation
          ({zeroGraphon} ∪
            {W | ∃ γ ∈ Ioc (0 : ℝ) (gammaK k),
              W ∈ candidateOptimizerFamily k γ})
      else
        cutSaturation
          (candidateOptimizerFamily k (gammaFromProbability k p)) := by
  rw [gnpGraphonOptimizers_eq_cutSaturation k hk p hp]
  by_cases hsub : p < pK k
  · simp [hsub, gnpCandidateFamily_of_lt_pK hsub]
  · by_cases hcrit : p = pK k
    · subst p
      simp [gnpCandidateFamily_at_pK]
    · have hsuper : pK k < p :=
        lt_of_le_of_ne (le_of_not_gt hsub) (Ne.symm hcrit)
      simp [hsub, hcrit, gnpCandidateFamily_of_pK_lt hsuper]

/-! ## Conditioned optimizer multiplicity -/

/-- The conditioned optimizer set is nonempty and any two optimizers are
equivalent in the paper's common-measure-preserving-pullback sense. -/
def UniqueGnpOptimizerUpToEquivalence (k : ℕ) (p : ℝ) : Prop :=
  (gnpGraphonOptimizers k p).Nonempty ∧
    ∀ U ∈ gnpGraphonOptimizers k p,
      ∀ W ∈ gnpGraphonOptimizers k p,
        GraphonEquivalent U W

/-- Below the critical probability, every conditioned optimizer is
equivalent to the zero graphon. -/
theorem gnpOptimizer_uniqueUpToEquivalence_of_lt_pK
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) (hsub : p < pK k) :
    UniqueGnpOptimizerUpToEquivalence k p := by
  refine ⟨gnpGraphonOptimizers_nonempty k hk p hp, ?_⟩
  intro U hU W hW
  have hUzero : graphonEdgeDensity U = 0 :=
    (rateAtDensity_subcritical_minimization hk hp hsub
      (graphonEdgeDensity_mem_Icc U)).2.1
        (gnpOptimizer_rateAt_edgeDensity_eq_rateFunction k hk p hp hU)
  have hWzero : graphonEdgeDensity W = 0 :=
    (rateAtDensity_subcritical_minimization hk hp hsub
      (graphonEdgeDensity_mem_Icc W)).2.1
        (gnpOptimizer_rateAt_edgeDensity_eq_rateFunction k hk p hp hW)
  have hUeq := (graphonEdgeDensity_eq_zero_iff U).1 hUzero
  have hWeq := (graphonEdgeDensity_eq_zero_iff W).1 hWzero
  subst U
  subst W
  exact graphonEquivalent_of_cutDist_eq_zero zeroGraphon zeroGraphon
    (cutDist_self zeroGraphon)

/-- Above the critical probability, every conditioned optimizer lies in the
fixed-density optimizer class at the unique minimizing density. -/
theorem gnpOptimizer_mem_fixedDensityOptimizers_of_pK_lt
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) (hsuper : pK k < p)
    {W : Graphon} (hW : W ∈ gnpGraphonOptimizers k p) :
    W ∈ fixedDensityOptimizers k (gammaFromProbability k p) := by
  have hrate := gnpOptimizer_rateAt_edgeDensity_eq_rateFunction
    k hk p hp hW
  have hedgeEq :=
    (rateAtDensity_supercritical_minimization hk hp hsuper
      (graphonEdgeDensity_mem_Icc W)).2.1 hrate
  have hγp := gammaFromProbability_mem_Ioo hk hsuper hp.2
  have hedgeIoo : graphonEdgeDensity W ∈ Ioo (0 : ℝ) 1 := by
    rw [hedgeEq]
    exact ⟨(gammaK_pos hk).trans hγp.1, hγp.2⟩
  have hfixedOwn :=
    (graphonRelativeEntropy_eq_rateAt_edgeDensity_iff_optimizer
      k hk p hp W hW.feasible hedgeIoo).1
        (gnpOptimizer_relativeEntropy_eq_rateAt_edgeDensity k hk p hp hW)
  simpa only [hedgeEq] using hfixedOwn

/-- Above the critical probability, the conditioned optimizer is unique up
to graphon equivalence. -/
theorem gnpOptimizer_uniqueUpToEquivalence_of_pK_lt
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) (hsuper : pK k < p) :
    UniqueGnpOptimizerUpToEquivalence k p := by
  have hγp := gammaFromProbability_mem_Ioo hk hsuper hp.2
  have hunique := fixedDensityOptimizer_uniqueUpToEquivalence_of_gammaK_le
    k hk (gammaFromProbability k p) ⟨hγp.1.le, hγp.2⟩
  refine ⟨gnpGraphonOptimizers_nonempty k hk p hp, ?_⟩
  intro U hU W hW
  exact hunique.2 U
    (gnpOptimizer_mem_fixedDensityOptimizers_of_pK_lt
      k hk p hp hsuper hU) W
    (gnpOptimizer_mem_fixedDensityOptimizers_of_pK_lt
      k hk p hp hsuper hW)

/-- At the critical probability there is an explicit sequence of pairwise
non-equivalent conditioned optimizers, obtained from the fixed-density
subcritical family at density `gammaK k / 2`. -/
theorem exists_pairwiseNonEquivalent_criticalGnpOptimizers
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ Wseq : ℕ → Graphon,
      (∀ n, Wseq n ∈ gnpGraphonOptimizers k (pK k)) ∧
      ∀ ⦃m n : ℕ⦄, m ≠ n →
        ¬ GraphonEquivalent (Wseq m) (Wseq n) := by
  let γ0 : ℝ := gammaK k / 2
  have hγ0sub : γ0 ∈ Ioo (0 : ℝ) (gammaK k) := by
    dsimp [γ0]
    constructor <;> nlinarith [gammaK_pos hk]
  have hγ0full : γ0 ∈ Ioo (0 : ℝ) 1 :=
    ⟨hγ0sub.1, hγ0sub.2.trans (gammaK_lt_one hk)⟩
  obtain ⟨Wseq, hfixed, hpairwise⟩ :=
    exists_pairwiseNonEquivalent_subcriticalOptimizers k hk γ0 hγ0sub
  refine ⟨Wseq, ?_, hpairwise⟩
  intro n
  obtain ⟨V, hV, hcut⟩ :=
    exists_candidate_cutEquivalent_of_optimizer
      k hk γ0 hγ0full (Wseq n) (hfixed n)
  apply (mem_gnpGraphonOptimizers_iff_exists_candidate_cutDist_zero
    k hk (pK k) (pK_mem_Ioo (show 2 ≤ k by omega)) (Wseq n)).2
  refine ⟨V, ?_, hcut⟩
  rw [gnpCandidateFamily_at_pK]
  exact Or.inr ⟨γ0, ⟨hγ0sub.1, hγ0sub.2.le⟩, hV⟩

/-- Paper: Theorem `thm:gnp-graphons`.

The conditioned optimizer is unique up to graphon equivalence away from the
critical probability, while at the critical probability there are infinitely
many pairwise non-equivalent optimizers. -/
theorem gnpGraphonOptimizerMultiplicity
    (k : ℕ) (hk : 3 ≤ k) :
    (∀ p : ℝ,
      p ∈ Ioo (0 : ℝ) (pK k) →
        UniqueGnpOptimizerUpToEquivalence k p) ∧
    (∃ Wseq : ℕ → Graphon,
      (∀ n, Wseq n ∈ gnpGraphonOptimizers k (pK k)) ∧
      ∀ ⦃m n : ℕ⦄, m ≠ n →
        ¬ GraphonEquivalent (Wseq m) (Wseq n)) ∧
    (∀ p : ℝ,
      p ∈ Ioo (pK k) 1 →
        UniqueGnpOptimizerUpToEquivalence k p) := by
  constructor
  · intro p hp
    exact gnpOptimizer_uniqueUpToEquivalence_of_lt_pK k hk p
      ⟨hp.1, hp.2.trans (pK_lt_one (by omega))⟩ hp.2
  · constructor
    · exact exists_pairwiseNonEquivalent_criticalGnpOptimizers k hk
    · intro p hp
      exact gnpOptimizer_uniqueUpToEquivalence_of_pK_lt k hk p
        ⟨(pK_pos (by omega)).trans hp.1, hp.2⟩ hp.1

end InducedStars
