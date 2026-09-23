import InducedStars.Asymptotics.WeightedEntropyUpper
import InducedStars.FiniteModels.GnpFamilySlices
import InducedStars.FiniteModels.Uniform
import InducedStars.Graphon.OptimizerGap

/-!
# Upper bounds for graphon rough structure

This module contains the compactness and entropy-counting layer shared by
the fixed-density and conditioned `G(n,p)` rough-structure theorems.  In
particular, the HJS wrapper below is valid for families that are empty at
arbitrarily many orders; it never treats the totalized value `log2 0` as the
logarithm of a positive count.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

attribute [local instance] Classical.propDecidable

/-! ## An empty-graph padding for arbitrary labeled families -/

/-- Add the empty labeled graph at every order.  This makes a graph family
pointwise nonempty while adding only the zero graphon to its possible limit
points. -/
noncomputable def emptyGraphPaddedFamily
    (Q : (n : ℕ) → Finset (SimpleGraph (Fin n)))
    (n : ℕ) : Finset (SimpleGraph (Fin n)) :=
  insert ⊥ (Q n)

theorem emptyGraphPaddedFamily_nonempty
    (Q : (n : ℕ) → Finset (SimpleGraph (Fin n))) (n : ℕ) :
    (emptyGraphPaddedFamily Q n).Nonempty := by
  exact ⟨⊥, by simp [emptyGraphPaddedFamily]⟩

theorem subset_emptyGraphPaddedFamily
    (Q : (n : ℕ) → Finset (SimpleGraph (Fin n))) (n : ℕ) :
    Q n ⊆ emptyGraphPaddedFamily Q n := by
  exact Finset.subset_insert ⊥ (Q n)

private theorem emptyGraph_edgeDensity_tendsto_zero
    (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    Tendsto
      (fun j ↦ graphonEdgeDensity
        (graphGraphon (⊥ : SimpleGraph (Fin (σ j)))))
      atTop (nhds 0) := by
  have hzero (j : ℕ) :
      (finiteGraphEdges (⊥ : SimpleGraph (Fin (σ j)))).card = 0 := by
    rw [Finset.card_eq_zero]
    ext e
    simp [mem_finiteGraphEdges]
  apply graphonEdgeDensity_graphGraphon_tendsto_of_normalizedEdgeCount
    hσ.tendsto_atTop
  convert (tendsto_const_nhds :
    Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0)) using 1
  funext j
  rw [hzero]
  simp

/-- Every limit of the empty-graph padding is either a limit of the original
family or has zero entropy.  The proof passes to a frequent original member
when one exists; otherwise the chosen graphs are eventually empty. -/
theorem entropy_le_of_mem_emptyGraphPaddedFamily_limitSet
    (Q : (n : ℕ) → Finset (SimpleGraph (Fin n)))
    (B : ℝ)
    (hlimit : ∀ W ∈ labeledGraphFamilyLimitSet Q,
      graphonEntropy W ≤ B)
    {W : Graphon}
    (hW : W ∈ labeledGraphFamilyLimitSet
      (emptyGraphPaddedFamily Q)) :
    graphonEntropy W ≤ B ∨ graphonEntropy W = 0 := by
  obtain ⟨σ, hσ, G, hG, hcut⟩ := hW
  by_cases hfrequent : ∃ᶠ j in atTop, G j ∈ Q (σ j)
  · obtain ⟨τ, hτ, hτmem⟩ :=
      exists_strictMono_forall_of_frequently_atTop hfrequent
    have hQlimit : W ∈ labeledGraphFamilyLimitSet Q := by
      refine ⟨σ ∘ τ, hσ.comp hτ, fun j ↦ G (τ j), hτmem, ?_⟩
      change Tendsto
        ((fun j ↦ cutDist (graphGraphon (G j)) W) ∘ τ)
        atTop (nhds 0)
      exact hcut.comp hτ.tendsto_atTop
    exact Or.inl (hlimit W hQlimit)
  · have hempty : ∀ᶠ j in atTop,
        G j = (⊥ : SimpleGraph (Fin (σ j))) := by
      have hnot : ∀ᶠ j in atTop, G j ∉ Q (σ j) :=
        not_frequently.mp hfrequent
      filter_upwards [hnot] with j hj
      have hjmem := hG j
      simp only [emptyGraphPaddedFamily, Finset.mem_insert] at hjmem
      exact hjmem.resolve_right hj
    have hedgeFinite : Tendsto
        (fun j ↦ graphonEdgeDensity (graphGraphon (G j)))
        atTop (nhds 0) := by
      apply (emptyGraph_edgeDensity_tendsto_zero σ hσ).congr'
      filter_upwards [hempty] with j hj
      rw [hj]
    have hedgeLimit :=
      graphonEdgeDensity_tendsto_of_cutDist_tendsto_zero
        (fun j ↦ graphGraphon (G j)) W hcut
    have hWedge : graphonEdgeDensity W = 0 :=
      tendsto_nhds_unique hedgeLimit hedgeFinite
    have hWzero : W = zeroGraphon :=
      (graphonEdgeDensity_eq_zero_iff W).mp hWedge
    exact Or.inr (by rw [hWzero, graphonEntropy_zero])

/-- The padded family has a graphon limit, by graphon sequential
compactness. -/
theorem emptyGraphPaddedFamily_limitSet_nonempty
    (Q : (n : ℕ) → Finset (SimpleGraph (Fin n))) :
    (labeledGraphFamilyLimitSet (emptyGraphPaddedFamily Q)).Nonempty := by
  let G : (n : ℕ) → SimpleGraph (Fin n) := fun n ↦
    Classical.choose (emptyGraphPaddedFamily_nonempty Q n)
  have hG (n : ℕ) : G n ∈ emptyGraphPaddedFamily Q n :=
    Classical.choose_spec (emptyGraphPaddedFamily_nonempty Q n)
  obtain ⟨σ, hσ, W, hcut⟩ :=
    PriorLiterature.bclsvGraphonSequentialCompactness
      (fun n ↦ graphGraphon (G n))
  exact ⟨W, σ, hσ, fun j ↦ G (σ j), fun j ↦ hG (σ j), hcut⟩

/-- HJS entropy counting for a family that may be empty at infinitely many
orders.  Empty orders are handled directly; logarithm monotonicity is used
only after proving that the original count is positive. -/
theorem eventually_normalizedLogGraphCount_le_of_limitEntropyBound
    (Q : (n : ℕ) → Finset (SimpleGraph (Fin n)))
    (B : ℝ) (hB : 0 < B)
    (hlimit : ∀ W ∈ labeledGraphFamilyLimitSet Q,
      graphonEntropy W ≤ B) :
    ∀ δ > 0,
      ∀ᶠ n in atTop,
        normalizedLogGraphCount n (Q n).card ≤ B + δ := by
  intro δ hδ
  let P : (n : ℕ) → Finset (SimpleGraph (Fin n)) :=
    emptyGraphPaddedFamily Q
  have hPne : ∀ᶠ n in atTop, (P n).Nonempty :=
    Eventually.of_forall (emptyGraphPaddedFamily_nonempty Q)
  have hPlimit : ∀ W ∈ labeledGraphFamilyLimitSet P,
      graphonEntropy W ≤ B := by
    intro W hW
    rcases entropy_le_of_mem_emptyGraphPaddedFamily_limitSet
        Q B hlimit hW with h | h
    · exact h
    · rw [h]
      exact hB.le
  have hlimitNonempty :
      (labeledGraphFamilyLimitSet P).Nonempty :=
    emptyGraphPaddedFamily_limitSet_nonempty Q
  have hsup :
      sSup (graphonEntropy '' labeledGraphFamilyLimitSet P) ≤ B := by
    apply csSup_le (hlimitNonempty.image graphonEntropy)
    rintro z ⟨W, hW, rfl⟩
    exact hPlimit W hW
  have hHJS :=
    PriorLiterature.hatamiJansonSzegedyLabeledEntropyUpperBound
      P hPne δ hδ
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    eventually_atTop.2 ⟨2, fun _ hn ↦ hn⟩
  filter_upwards [hHJS, hlarge] with n hnHJS hn
  by_cases hQne : (Q n).Nonempty
  · have hcard : (Q n).card ≤ (P n).card :=
      Finset.card_le_card (subset_emptyGraphPaddedFamily Q n)
    have hcountPos : 0 < ((Q n).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hQne
    have hlog : log2 ((Q n).card : ℝ) ≤
        log2 ((P n).card : ℝ) := by
      unfold log2
      apply div_le_div_of_nonneg_right _ realLogTwo_pos.le
      exact Real.log_le_log hcountPos (by exact_mod_cast hcard)
    have hden : 0 ≤ (completeEdgeCount n : ℝ) := by positivity
    have hmono : normalizedLogGraphCount n (Q n).card ≤
        normalizedLogGraphCount n (P n).card := by
      exact div_le_div_of_nonneg_right hlog hden
    exact hmono.trans (hnHJS.trans (by linarith))
  · have hQempty : Q n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQne
    rw [hQempty]
    simp only [Finset.card_empty, normalizedLogGraphCount,
      normalizedLogAtGraphOrder, Nat.cast_zero, log2_zero, zero_div]
    linarith

/-! ## Exact slices supported on a selected sequence of orders -/

/-- At orders in the range of `σ`, take the prescribed exact-edge slice of
`Q`; at every other order take the empty family. -/
noncomputable def selectedGraphFamilyEdgeSlices
    (Q : (n : ℕ) → Finset (SimpleGraph (Fin n)))
    (m : ℕ → ℕ) (σ : ℕ → ℕ)
    (n : ℕ) : Finset (SimpleGraph (Fin n)) :=
  if n ∈ Set.range σ then graphFamilyEdgeSlice (Q n) (m n) else ∅

@[simp] theorem selectedGraphFamilyEdgeSlices_apply
    (Q : (n : ℕ) → Finset (SimpleGraph (Fin n)))
    (m : ℕ → ℕ) (σ : ℕ → ℕ) (j : ℕ) :
    selectedGraphFamilyEdgeSlices Q m σ (σ j) =
      graphFamilyEdgeSlice (Q (σ j)) (m (σ j)) := by
  simp [selectedGraphFamilyEdgeSlices]

@[simp] theorem mem_selectedGraphFamilyEdgeSlices
    {Q : (n : ℕ) → Finset (SimpleGraph (Fin n))}
    {m : ℕ → ℕ} {σ : ℕ → ℕ} {n : ℕ}
    {G : SimpleGraph (Fin n)} :
    G ∈ selectedGraphFamilyEdgeSlices Q m σ n ↔
      n ∈ Set.range σ ∧ G ∈ Q n ∧
        (finiteGraphEdges G).card = m n := by
  classical
  by_cases hn : n ∈ Set.range σ
  · rw [selectedGraphFamilyEdgeSlices, if_pos hn,
      mem_graphFamilyEdgeSlice_iff_finiteGraphEdges]
    constructor
    · exact fun h ↦ ⟨hn, h⟩
    · exact fun h ↦ h.2
  · simp [selectedGraphFamilyEdgeSlices, hn]

/-- A limit of selected slices is a limit of the original family. -/
theorem selectedGraphFamilyEdgeSlices_limitSet_subset
    (Q : (n : ℕ) → Finset (SimpleGraph (Fin n)))
    (m : ℕ → ℕ) (σ : ℕ → ℕ) :
    labeledGraphFamilyLimitSet (selectedGraphFamilyEdgeSlices Q m σ) ⊆
      labeledGraphFamilyLimitSet Q := by
  rintro W ⟨τ, hτ, G, hG, hcut⟩
  exact ⟨τ, hτ, G, fun j ↦
    (mem_selectedGraphFamilyEdgeSlices.mp (hG j)).2.1, hcut⟩

/-- Every graphon limit of selected exact slices has the selected limiting
edge density. -/
theorem selectedGraphFamilyEdgeSlices_limitSet_edgeDensity
    (Q : (n : ℕ) → Finset (SimpleGraph (Fin n)))
    (m : ℕ → ℕ) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    {γ : ℝ}
    (hm : Tendsto
      (fun j ↦ (m (σ j) : ℝ) /
        (completeEdgeCount (σ j) : ℝ)) atTop (nhds γ))
    {W : Graphon}
    (hW : W ∈ labeledGraphFamilyLimitSet
      (selectedGraphFamilyEdgeSlices Q m σ)) :
    graphonEdgeDensity W = γ := by
  obtain ⟨τ, hτ, G, hG, hcut⟩ := hW
  have hrange (j : ℕ) : τ j ∈ Set.range σ :=
    (mem_selectedGraphFamilyEdgeSlices.mp (hG j)).1
  let r : ℕ → ℕ := fun j ↦ Classical.choose (hrange j)
  have heq (j : ℕ) : σ (r j) = τ j :=
    Classical.choose_spec (hrange j)
  have hr : StrictMono r := by
    intro i j hij
    apply (hσ.lt_iff_lt).mp
    rw [heq i, heq j]
    exact hτ hij
  have hmτ : Tendsto
      (fun j ↦ (m (τ j) : ℝ) /
        (completeEdgeCount (τ j) : ℝ)) atTop (nhds γ) := by
    convert hm.comp hr.tendsto_atTop using 1
    funext j
    rw [← heq j]
    rfl
  have hcount : Tendsto
      (fun j ↦ ((finiteGraphEdges (G j)).card : ℝ) /
        (completeEdgeCount (τ j) : ℝ)) atTop (nhds γ) := by
    apply hmτ.congr'
    filter_upwards [] with j
    have hedge : (finiteGraphEdges (G j)).card = m (τ j) := by
      exact (mem_selectedGraphFamilyEdgeSlices.mp (hG j)).2.2
    rw [hedge]
  have hfinite :=
    graphonEdgeDensity_graphGraphon_tendsto_of_normalizedEdgeCount
      hτ.tendsto_atTop G hcount
  have hlimit :=
    graphonEdgeDensity_tendsto_of_cutDist_tendsto_zero
      (fun j ↦ graphGraphon (G j)) W hcut
  exact tendsto_nhds_unique hlimit hfinite

/-- Nonempty selected slices have a graphon limit after passing to a
subsequence. -/
theorem selectedGraphFamilyEdgeSlices_limitSet_nonempty
    (Q : (n : ℕ) → Finset (SimpleGraph (Fin n)))
    (m : ℕ → ℕ) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hne : ∀ j, (graphFamilyEdgeSlice (Q (σ j)) (m (σ j))).Nonempty) :
    (labeledGraphFamilyLimitSet
      (selectedGraphFamilyEdgeSlices Q m σ)).Nonempty := by
  let G : (j : ℕ) → SimpleGraph (Fin (σ j)) := fun j ↦
    Classical.choose (hne j)
  have hG (j : ℕ) :
      G j ∈ graphFamilyEdgeSlice (Q (σ j)) (m (σ j)) :=
    Classical.choose_spec (hne j)
  obtain ⟨τ, hτ, W, hcut⟩ :=
    PriorLiterature.bclsvGraphonSequentialCompactness
      (fun j ↦ graphGraphon (G j))
  refine ⟨W, σ ∘ τ, hσ.comp hτ, fun j ↦ G (τ j), ?_, ?_⟩
  · intro j
    simpa only [Function.comp_apply,
      selectedGraphFamilyEdgeSlices_apply] using hG (τ j)
  · simpa only [Function.comp_apply] using hcut

/-! ## A weighted HJS upper bound for arbitrary graph families -/

/-- Generic weighted graph-family entropy upper bound.  Because the project
totalizes `log2 0` as zero, the mathematically correct conclusion keeps a
zero-probability alternative.  On positive orders it is exactly the usual
limsup bound by the negative infimum of graphon relative entropy over the
family's limit set.

The proof factors the Goal 6d argument through the generic exact-slice API:
it selects a maximum-weight edge slice, compactifies the slice densities,
applies the possibly-empty HJS wrapper to the selected slices, and then uses
the exact entropy/KL decomposition. -/
theorem eventually_normalizedLogGnpGraphFamilyProbability_le
    (Q : (n : ℕ) → Finset (SimpleGraph (Fin n)))
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (a : ℝ)
    (hlimit : ∀ W ∈ labeledGraphFamilyLimitSet Q,
      a ≤ graphonRelativeEntropy p W) :
    ∀ δ > 0,
      ∀ᶠ n in atTop,
        gnpGraphEventProbability p (Q n) = 0 ∨
          normalizedLogProbability n
              (gnpGraphEventProbability p (Q n)) ≤
            -a + δ := by
  intro δ hδ
  by_contra hnot
  have hbad : ∃ᶠ n in atTop,
      ¬(gnpGraphEventProbability p (Q n) = 0 ∨
        normalizedLogProbability n
            (gnpGraphEventProbability p (Q n)) ≤ -a + δ) :=
    not_eventually.mp hnot
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    eventually_atTop.2 ⟨2, fun _ hn ↦ hn⟩
  have hfrequent : ∃ᶠ n in atTop,
      (-a + δ < normalizedLogProbability n
          (gnpGraphEventProbability p (Q n))) ∧
        0 < gnpGraphEventProbability p (Q n) ∧ 2 ≤ n := by
    exact (hbad.and_eventually hlarge).mono fun n hn ↦ by
      have hne : gnpGraphEventProbability p (Q n) ≠ 0 :=
        fun hz ↦ hn.1 (Or.inl hz)
      have hprob : 0 < gnpGraphEventProbability p (Q n) :=
        lt_of_le_of_ne
          (gnpGraphEventProbability_nonneg ⟨hp.1.le, hp.2.le⟩ (Q n))
          (Ne.symm hne)
      exact ⟨lt_of_not_ge (fun hle ↦ hn.1 (Or.inr hle)),
        hprob, hn.2⟩
  obtain ⟨σ, hσ, hσgood⟩ :=
    exists_strictMono_forall_of_frequently_atTop hfrequent
  let m : ℕ → ℕ := fun n ↦ maximizingGraphFamilyEdgeCount (Q n) p
  have hmle (n : ℕ) : m n ≤ completeEdgeCount n :=
    maximizingGraphFamilyEdgeCount_le_completeEdgeCount (Q n) p
  let density : ℕ → ℝ := fun j ↦
    (m (σ j) : ℝ) / (completeEdgeCount (σ j) : ℝ)
  have hdensity (j : ℕ) : density j ∈ Icc (0 : ℝ) 1 := by
    have hN : 0 < (completeEdgeCount (σ j) : ℝ) := by
      exact_mod_cast Nat.choose_pos (hσgood j).2.2
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hN.le
    · exact (div_le_one hN).2 (by exact_mod_cast hmle (σ j))
  obtain ⟨γ, _hγ, τ, hτ, hDensity⟩ :=
    isCompact_Icc.tendsto_subseq hdensity
  let ρ : ℕ → ℕ := σ ∘ τ
  have hρ : StrictMono ρ := hσ.comp hτ
  have hρgood (j : ℕ) :
      (-a + δ < normalizedLogProbability (ρ j)
          (gnpGraphEventProbability p (Q (ρ j)))) ∧
        0 < gnpGraphEventProbability p (Q (ρ j)) ∧ 2 ≤ ρ j := by
    exact hσgood (τ j)
  have hρdensity : Tendsto
      (fun j ↦ (m (ρ j) : ℝ) /
        (completeEdgeCount (ρ j) : ℝ)) atTop (nhds γ) := by
    simpa [density, ρ, Function.comp_def] using hDensity
  have hsliceNonempty (j : ℕ) :
      (graphFamilyEdgeSlice (Q (ρ j)) (m (ρ j))).Nonempty := by
    exact maximizingGraphFamilyEdgeSlice_nonempty_of_probability_pos
      (Q (ρ j)) hp (hρgood j).2.1
  let R : (n : ℕ) → Finset (SimpleGraph (Fin n)) :=
    selectedGraphFamilyEdgeSlices Q m ρ
  have hRnonempty : (labeledGraphFamilyLimitSet R).Nonempty :=
    selectedGraphFamilyEdgeSlices_limitSet_nonempty
      Q m ρ hρ hsliceNonempty
  have hRsubset : labeledGraphFamilyLimitSet R ⊆
      labeledGraphFamilyLimitSet Q :=
    selectedGraphFamilyEdgeSlices_limitSet_subset Q m ρ
  have hRedge : ∀ W ∈ labeledGraphFamilyLimitSet R,
      graphonEdgeDensity W = γ := by
    intro W hW
    exact selectedGraphFamilyEdgeSlices_limitSet_edgeDensity
      Q m ρ hρ hρdensity hW
  have hodds : log2 ((1 - p) / p) =
      -log2 (p / (1 - p)) := by
    rw [log2_div (sub_pos.mpr hp.2).ne' hp.1.ne',
      log2_div hp.1.ne' (sub_pos.mpr hp.2).ne']
    ring
  let fiberBound : ℝ :=
    -a - γ * log2 (p / (1 - p)) - log2 (1 - p)
  have hRentropy : ∀ W ∈ labeledGraphFamilyLimitSet R,
      graphonEntropy W ≤ fiberBound := by
    intro W hW
    have hKL := hlimit W (hRsubset hW)
    rw [graphonRelativeEntropy_eq_negEntropy_add_edge hp W,
      hRedge W hW, hodds] at hKL
    dsimp only [fiberBound]
    linarith
  have hfiberNonneg : 0 ≤ fiberBound := by
    obtain ⟨U, hU⟩ := hRnonempty
    exact (graphonEntropy_nonneg U).trans (hRentropy U hU)
  let η : ℝ := δ / 4
  have hη : 0 < η := by
    dsimp [η]
    linarith
  let B : ℝ := fiberBound + η
  have hB : 0 < B := by
    dsimp [B]
    linarith
  have hcountAll :=
    eventually_normalizedLogGraphCount_le_of_limitEntropyBound
      R B hB (fun W hW ↦ (hRentropy W hW).trans (by
        dsimp [B]
        linarith)) η hη
  have hcountSelected := hρ.tendsto_atTop.eventually hcountAll
  have hoddsLimit : Tendsto
      (fun j ↦ (m (ρ j) : ℝ) /
          (completeEdgeCount (ρ j) : ℝ) *
            log2 (p / (1 - p)))
      atTop (nhds (γ * log2 (p / (1 - p)))) :=
    hρdensity.mul_const _
  have hoddsUpper : ∀ᶠ j in atTop,
      (m (ρ j) : ℝ) / (completeEdgeCount (ρ j) : ℝ) *
          log2 (p / (1 - p)) <
        γ * log2 (p / (1 - p)) + η :=
    (tendsto_order.mp hoddsLimit).2 _ (lt_add_of_pos_right _ hη)
  have hfactorLimit :=
    normalizedLogPolynomialSliceFactor_tendsto_zero.comp hρ.tendsto_atTop
  have hfactorUpper : ∀ᶠ j in atTop,
      normalizedLogProbability (ρ j)
          ((completeEdgeCount (ρ j) : ℝ) + 1) < η :=
    (tendsto_order.mp hfactorLimit).2 _ hη
  have hfalse : ∀ᶠ _j : ℕ in atTop, False := by
    filter_upwards [hcountSelected, hoddsUpper, hfactorUpper] with
      j hcount hoddsJ hfactor
    have hj := hρgood j
    have hjprob := hj.2.1
    have hjlarge := hj.2.2
    have hsliceCount :
        0 < (graphFamilyEdgeSlice (Q (ρ j)) (m (ρ j))).card :=
      Finset.card_pos.mpr (hsliceNonempty j)
    have hmax : 0 < maximalGnpGraphFamilySliceWeight (Q (ρ j)) p :=
      maximalGnpGraphFamilySliceWeight_pos_of_probability_pos
        (Q (ρ j)) p hjprob
    have hfactorPos : 0 < (completeEdgeCount (ρ j) : ℝ) + 1 := by
      positivity
    have hprobUpper : normalizedLogProbability (ρ j)
          (gnpGraphEventProbability p (Q (ρ j))) ≤
        normalizedLogProbability (ρ j)
            ((completeEdgeCount (ρ j) : ℝ) + 1) +
          normalizedLogProbability (ρ j)
            (maximalGnpGraphFamilySliceWeight (Q (ρ j)) p) := by
      apply normalizedLogProbability_le_mul hjlarge
        hfactorPos hmax hjprob
      simpa only [Nat.cast_add, Nat.cast_one] using
        gnpGraphEventProbability_le_card_mul_maximalFamilySlice
          (Q (ρ j)) p
    have hsliceExponent :=
      normalizedLogGnpGraphFamilySliceWeight_eq_odds
        (Q (ρ j)) p hp (hmle (ρ j)) hsliceCount hjlarge
    have hmaxExponent :
        normalizedLogProbability (ρ j)
            (maximalGnpGraphFamilySliceWeight (Q (ρ j)) p) =
          normalizedLogGraphCount (ρ j)
              (graphFamilyEdgeSlice (Q (ρ j)) (m (ρ j))).card +
            (m (ρ j) : ℝ) /
                (completeEdgeCount (ρ j) : ℝ) *
              log2 (p / (1 - p)) + log2 (1 - p) := by
      simpa only [m, maximalGnpGraphFamilySliceWeight] using hsliceExponent
    rw [hmaxExponent] at hprobUpper
    have hcount' : normalizedLogGraphCount (ρ j)
          (graphFamilyEdgeSlice (Q (ρ j)) (m (ρ j))).card ≤
        fiberBound + 2 * η := by
      have hcountRaw : normalizedLogGraphCount (ρ j)
            (graphFamilyEdgeSlice (Q (ρ j)) (m (ρ j))).card ≤
          fiberBound + η + η := by
        simpa only [R, selectedGraphFamilyEdgeSlices_apply, B] using hcount
      linarith
    have hsliceUpper :
        normalizedLogGraphCount (ρ j)
              (graphFamilyEdgeSlice (Q (ρ j)) (m (ρ j))).card +
            (m (ρ j) : ℝ) /
                (completeEdgeCount (ρ j) : ℝ) *
              log2 (p / (1 - p)) + log2 (1 - p) <
          -a + 3 * η := by
      dsimp only [fiberBound] at hcount'
      linarith
    have hstrict : normalizedLogProbability (ρ j)
          (gnpGraphEventProbability p (Q (ρ j))) <
        -a + 4 * η := by
      linarith
    dsimp only [η] at hstrict
    linarith [hj.1]
  exact hfalse.exists.choose_spec

/-! ## Optimizer-far limit sets and their strict exponent gaps -/

/-- Every graphon limit of the fixed-density optimizer-far family is
feasible at the prescribed limiting density and remains optimizer-far. -/
theorem fixedDensityOptimizerFar_limitSet_subset
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (ε : ℝ) (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m γ)
    {W : Graphon}
    (hW : W ∈ labeledGraphFamilyLimitSet
      (fixedDensityOptimizerFarGraphFinset k γ ε m)) :
    W ∈ fixedDensityFeasible k γ ∧
      ε ≤ cutDistToSet W (fixedDensityOptimizers k γ) := by
  obtain ⟨σ, hσ, G, hG, hcut⟩ := hW
  have hExact :
      W ∈ exactEdgeInducedFreeLimitSet (inducedStar k) γ m := by
    exact ⟨σ, hσ, G,
      fun j ↦ fixedDensityOptimizerFarGraphFinset_subset
        k (σ j) γ ε m (hG j), hcut⟩
  refine ⟨⟨
    graphonInducedDensity_eq_zero_of_mem_exactEdgeInducedFreeLimitSet hExact,
    graphonEdgeDensity_eq_of_mem_exactEdgeInducedFreeLimitSet hm hExact⟩,
    ?_⟩
  exact le_cutDistToSet_of_tendsto
    (fun j ↦ graphGraphon (G j)) W
    (fixedDensityOptimizers_nonempty k hk γ hγ) hcut
    (fun j ↦ (mem_fixedDensityOptimizerFarGraphFinset.mp (hG j)).2.2)

/-- Every graphon limit of the conditioned optimizer-far family is
induced-star-free and remains optimizer-far. -/
theorem gnpOptimizerFar_limitSet_subset
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (ε : ℝ) {W : Graphon}
    (hW : W ∈ labeledGraphFamilyLimitSet
      (gnpOptimizerFarInducedStarFinset k p ε)) :
    W ∈ inducedStarFreeGraphons k ∧
      ε ≤ cutDistToSet W (gnpGraphonOptimizers k p) := by
  obtain ⟨σ, hσ, G, hG, hcut⟩ := hW
  have hfinite :=
    graphonInducedDensity_graphGraphon_tendsto_zero_of_inducedFree
      (inducedStar k) hσ.tendsto_atTop G
      (fun j ↦ (mem_gnpOptimizerFarInducedStarFinset.mp (hG j)).1)
  have hlimit :=
    graphonInducedDensity_tendsto_of_cutDist_tendsto_zero
      (inducedStar k) (fun j ↦ graphGraphon (G j)) W hcut
  refine ⟨tendsto_nhds_unique hlimit hfinite, ?_⟩
  exact le_cutDistToSet_of_tendsto
    (fun j ↦ graphGraphon (G j)) W
    (gnpGraphonOptimizers_nonempty k hk p hp) hcut
    (fun j ↦ (mem_gnpOptimizerFarInducedStarFinset.mp (hG j)).2)

/-- The fixed-density optimizer-far family has a strict entropy exponent
loss, uniformly over every exact-edge sequence with limiting density `γ`.
The gap is chosen below the positive optimum so the empty-safe HJS wrapper
can use the positive comparison value `entropyDensity k γ - c`. -/
theorem eventually_fixedDensityOptimizerFar_count_upper
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ 0 < entropyDensity k γ - c ∧
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m γ →
        ∀ᶠ n in atTop,
          normalizedLogGraphCount n
              (fixedDensityOptimizerFarGraphFinset k γ ε m n).card ≤
            entropyDensity k γ - 3 * c / 4 := by
  obtain ⟨c, hc, hremainder, hgap⟩ :=
    exists_fixedDensityEntropyGapWithPositiveRemainder
      k hk γ hγ ε hε
  refine ⟨c, hc, hremainder, ?_⟩
  intro m hm
  have hlimit : ∀ W ∈ labeledGraphFamilyLimitSet
      (fixedDensityOptimizerFarGraphFinset k γ ε m),
      graphonEntropy W ≤ entropyDensity k γ - c := by
    intro W hW
    have hproperties := fixedDensityOptimizerFar_limitSet_subset
      k hk γ hγ ε m hm hW
    exact hgap W hproperties.1 hproperties.2
  have hupper := eventually_normalizedLogGraphCount_le_of_limitEntropyBound
    (fixedDensityOptimizerFarGraphFinset k γ ε m)
    (entropyDensity k γ - c) hremainder hlimit
    (c / 4) (by positivity)
  filter_upwards [hupper] with n hn
  convert hn using 1 <;> ring

/-- The unconditioned `G(n,p)` mass of induced-star-free graphs that stay
optimizer-far has a strict relative-entropy exponent penalty.  This is the
locally repaired form of the conditioned manuscript step recorded as
`CFD-009`. -/
theorem eventually_gnpOptimizerFarProbability_upper
    (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n in atTop,
        gnpOptimizerFarInducedStarProbability k n p ε = 0 ∨
          normalizedLogProbability n
              (gnpOptimizerFarInducedStarProbability k n p ε) ≤
            -rateFunction k p - 3 * c / 4 := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_gnpRelativeEntropyGap k hk p hp ε hε
  refine ⟨c, hc, ?_⟩
  have hlimit : ∀ W ∈ labeledGraphFamilyLimitSet
      (gnpOptimizerFarInducedStarFinset k p ε),
      rateFunction k p + c ≤ graphonRelativeEntropy p W := by
    intro W hW
    have hproperties :=
      gnpOptimizerFar_limitSet_subset k hk p hp ε hW
    exact hgap W hproperties.1 hproperties.2
  have hupper := eventually_normalizedLogGnpGraphFamilyProbability_le
    (gnpOptimizerFarInducedStarFinset k p ε) p hp
    (rateFunction k p + c) hlimit (c / 4) (by positivity)
  filter_upwards [hupper] with n hn
  simpa only [gnpOptimizerFarInducedStarProbability] using
    hn.imp_right (by intro h; linarith)

end InducedStars
