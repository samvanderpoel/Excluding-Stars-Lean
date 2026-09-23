import InducedStars.FiniteModels.GraphonLimits
import InducedStars.FiniteModels.Shannon
import InducedStars.Graphon.FlexibleBand
import InducedStars.Graphon.Star
import InducedStars.PriorLiterature

/-!
# Fixed-density enumeration transfer

This module formalizes the local transfer from positive-random graphons to
exact-edge labeled graph families.  It is the Lean proof layer corresponding
to Proposition 2.11 of *The typical structure of dense claw-free graphs*;
that unpublished manuscript is used only as a proof blueprint, never as an
axiom.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal

namespace InducedStars

/-! ## The positive-random variational domain -/

/-- Fixed-density, induced-`H`-free graphons whose genuinely random region
has positive measure. -/
def positiveRandomFixedDensityGraphons {h : ℕ}
    (H : SimpleGraph (Fin h)) (γ : ℝ) : Set Graphon :=
  {W | graphonEdgeDensity W = γ ∧
    graphonInducedDensity H W = 0 ∧
    0 < graphonRandomMass W}

@[simp] theorem mem_positiveRandomFixedDensityGraphons {h : ℕ}
    {H : SimpleGraph (Fin h)} {γ : ℝ} {W : Graphon} :
    W ∈ positiveRandomFixedDensityGraphons H γ ↔
      graphonEdgeDensity W = γ ∧
        graphonInducedDensity H W = 0 ∧
          0 < graphonRandomMass W :=
  Iff.rfl

/-- Entropy supremum over the positive-random fixed-density domain. -/
noncomputable def positiveRandomFixedDensityEntropyValue {h : ℕ}
    (H : SimpleGraph (Fin h)) (γ : ℝ) : ℝ :=
  sSup (graphonEntropy '' positiveRandomFixedDensityGraphons H γ)

theorem positiveRandomFixedDensityGraphons_inducedStar_subset
    (k : ℕ) (γ : ℝ) :
    positiveRandomFixedDensityGraphons (inducedStar k) γ ⊆
      fixedDensityFeasible k γ := by
  rintro W ⟨hedge, hfree, _hrandom⟩
  exact ⟨hfree, hedge⟩

/-! ## Elementary entropy bounds and comparison of variational domains -/

/-- Every graphon has at most one bit of entropy per unordered pair. -/
theorem graphonEntropy_le_one (W : Graphon) : graphonEntropy W ≤ 1 := by
  unfold graphonEntropy graphonValueFunctional
  calc
    (∫ z : UnitSquare, binaryEntropy (W.value z) ∂unitSquareMeasure) ≤
        ∫ _z : UnitSquare, (1 : ℝ) ∂unitSquareMeasure :=
      integral_mono (integrable_binaryEntropy_value W) (integrable_const 1)
        (fun z ↦ binaryEntropy_le_one (W.value z))
    _ = 1 := by simp

/-- Graphon entropy values over any set of graphons are bounded above. -/
theorem bddAbove_graphonEntropy_image (A : Set Graphon) :
    BddAbove (graphonEntropy '' A) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨W, _hW, rfl⟩
  exact graphonEntropy_le_one W

/-- Abstract comparison behind the exact-edge entropy-supremum identity.
The first hypothesis supplies approximating exact-edge limits for every
positive-random graphon.  The second records the two closed constraints
satisfied by every exact-edge limit. -/
theorem graphonEntropy_sSup_limitSet_eq_positiveRandom
    {h : ℕ} (H : SimpleGraph (Fin h)) (γ : ℝ)
    (S : Set Graphon)
    (hne : (positiveRandomFixedDensityGraphons H γ).Nonempty)
    (hinclude : positiveRandomFixedDensityGraphons H γ ⊆ S)
    (hfeasible : ∀ U ∈ S,
      graphonEdgeDensity U = γ ∧ graphonInducedDensity H U = 0) :
    sSup (graphonEntropy '' S) =
      positiveRandomFixedDensityEntropyValue H γ := by
  let P : Set ℝ := graphonEntropy '' positiveRandomFixedDensityGraphons H γ
  let T : Set ℝ := graphonEntropy '' S
  have hPne : P.Nonempty := by
    obtain ⟨W, hW⟩ := hne
    exact ⟨graphonEntropy W, W, hW, rfl⟩
  have hTne : T.Nonempty := by
    obtain ⟨W, hW⟩ := hne
    exact ⟨graphonEntropy W, W, hinclude hW, rfl⟩
  have hPbdd : BddAbove P := bddAbove_graphonEntropy_image _
  have hTbdd : BddAbove T := bddAbove_graphonEntropy_image _
  have hPsupPos : 0 < sSup P := by
    obtain ⟨W, hW⟩ := hne
    have hEntropy : 0 < graphonEntropy W :=
      graphonEntropy_pos_of_graphonRandomMass_pos W hW.2.2
    exact hEntropy.trans_le (le_csSup hPbdd ⟨W, hW, rfl⟩)
  have hPT : sSup P ≤ sSup T := by
    apply csSup_le hPne
    rintro z ⟨W, hW, rfl⟩
    exact le_csSup hTbdd ⟨W, hinclude hW, rfl⟩
  have hTP : sSup T ≤ sSup P := by
    apply csSup_le hTne
    rintro z ⟨U, hU, rfl⟩
    obtain ⟨hDensity, hFree⟩ := hfeasible U hU
    by_cases hRandom : graphonRandomMass U = 0
    · rw [graphonEntropy_eq_zero_of_randomMass_eq_zero U hRandom]
      exact hPsupPos.le
    · have hRandomPos : 0 < graphonRandomMass U :=
        lt_of_le_of_ne (graphonRandomMass_nonneg U) (Ne.symm hRandom)
      exact le_csSup hPbdd ⟨U, ⟨hDensity, hFree, hRandomPos⟩, rfl⟩
  unfold positiveRandomFixedDensityEntropyValue
  change sSup T = sSup P
  exact le_antisymm hTP hPT

/-! ## Published entropy upper bound after the local limit-set comparison -/

/-- Hatami--Janson--Szegedy gives the fixed-density upper bound once the
local repair argument has supplied eventual nonemptiness and identified the
exact-edge limit-set entropy supremum. -/
theorem eventually_fixedDensityCount_le_positiveRandomEntropyValue
    {h : ℕ} (H : SimpleGraph (Fin h)) (γ : ℝ) (m : ℕ → ℕ)
    (hdomain : (positiveRandomFixedDensityGraphons H γ).Nonempty)
    (hfinite : ∀ᶠ n in atTop,
      (inducedFreeGraphFinsetWithEdges H n (m n)).Nonempty)
    (hinclude : positiveRandomFixedDensityGraphons H γ ⊆
      exactEdgeInducedFreeLimitSet H γ m)
    (hfeasible : ∀ U ∈ exactEdgeInducedFreeLimitSet H γ m,
      graphonEdgeDensity U = γ ∧ graphonInducedDensity H U = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      normalizedLogGraphCount n
          (inducedFreeGraphCountWithEdges H n (m n)) ≤
        positiveRandomFixedDensityEntropyValue H γ + ε := by
  let Q : (n : ℕ) → Finset (SimpleGraph (Fin n)) := fun n ↦
    inducedFreeGraphFinsetWithEdges H n (m n)
  have hHJS :=
    PriorLiterature.hatamiJansonSzegedyLabeledEntropyUpperBound Q hfinite ε hε
  have hSup :
      sSup (graphonEntropy '' labeledGraphFamilyLimitSet Q) =
        positiveRandomFixedDensityEntropyValue H γ := by
    exact graphonEntropy_sSup_limitSet_eq_positiveRandom H γ
      (exactEdgeInducedFreeLimitSet H γ m) hdomain hinclude hfeasible
  filter_upwards [hHJS] with n hn
  simpa only [Q, exactEdgeInducedFreeLimitSet,
    inducedFreeGraphCountWithEdges, hSup] using hn

/-- Order-theoretic final step of the fixed-density transfer: pointwise
lower bounds from every positive-random graphon and an upper bound at their
entropy supremum give a full limit. -/
theorem tendsto_fixedDensityCount_of_eventual_entropy_bounds
    {h : ℕ} (H : SimpleGraph (Fin h)) (γ : ℝ) (m : ℕ → ℕ)
    (hdomain : (positiveRandomFixedDensityGraphons H γ).Nonempty)
    (hlower : ∀ W ∈ positiveRandomFixedDensityGraphons H γ,
      ∀ ε > 0, ∀ᶠ n in atTop,
        graphonEntropy W - ε <
          normalizedLogGraphCount n
            (inducedFreeGraphCountWithEdges H n (m n)))
    (hupper : ∀ ε > 0, ∀ᶠ n in atTop,
      normalizedLogGraphCount n
          (inducedFreeGraphCountWithEdges H n (m n)) ≤
        positiveRandomFixedDensityEntropyValue H γ + ε) :
    Tendsto
      (fun n ↦ normalizedLogGraphCount n
        (inducedFreeGraphCountWithEdges H n (m n)))
      atTop (nhds (positiveRandomFixedDensityEntropyValue H γ)) := by
  let P : Set ℝ :=
    graphonEntropy '' positiveRandomFixedDensityGraphons H γ
  have hPne : P.Nonempty := by
    obtain ⟨W, hW⟩ := hdomain
    exact ⟨graphonEntropy W, W, hW, rfl⟩
  have hPbdd : BddAbove P := bddAbove_graphonEntropy_image _
  rw [tendsto_order]
  constructor
  · intro a ha
    change a < sSup P at ha
    obtain ⟨z, ⟨W, hW, rfl⟩, haz⟩ :=
      (lt_csSup_iff hPbdd hPne).mp ha
    have hgap : 0 < graphonEntropy W - a := sub_pos.mpr haz
    have hlow := hlower W hW (graphonEntropy W - a) hgap
    filter_upwards [hlow] with n hn
    simpa only [sub_sub_cancel] using hn
  · intro b hb
    let ε := (b - positiveRandomFixedDensityEntropyValue H γ) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hupp := hupper ε hε
    filter_upwards [hupp] with n hn
    have hn' : normalizedLogGraphCount n
          (inducedFreeGraphCountWithEdges H n (m n)) < b := by
      calc
        normalizedLogGraphCount n
            (inducedFreeGraphCountWithEdges H n (m n)) ≤
            positiveRandomFixedDensityEntropyValue H γ + ε := hn
        _ < b := by
          dsimp [ε]
          linarith
    exact hn'

end InducedStars
