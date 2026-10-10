import InducedStars.Graphon.CutLimit
import InducedStars.Graphon.FiniteBlockApproximation
import InducedStars.Graphon.FiniteBlockLayouts
import Mathlib.Tactic

/-!
# Supercritical fixed-density optimizer classification

This file carries out the concentration argument for the canonical finite
block approximations at and above `gammaK`.  The integer gap in the order of
a regular core forces the largest core to be the complete graph on `k - 1`
vertices; quantitative block estimates then identify the cut limit with the
distinguished graphon `Wstar`.
-/

noncomputable section

open Filter MeasureTheory Set SimpleGraph
open scoped BigOperators ENNReal Topology unitInterval symmDiff

namespace InducedStars

/-- Two `[0,1]`-valued graphons which agree off a measurable set have `L¹`
distance at most the real measure of that set. -/
theorem graphonL1Dist_le_measureReal_of_ae_eq_off
    (U V : Graphon) (S : Set UnitSquare) (hS : MeasurableSet S)
    (heq : ∀ᵐ z ∂unitSquareMeasure, z ∉ S → U z = V z) :
    graphonL1Dist U V ≤ unitSquareMeasure.real S := by
  rw [graphonL1Dist_eq_integral]
  let g : UnitSquare → ℝ := S.indicator (fun _ ↦ 1)
  have hf : Integrable (fun z ↦ |U z - V z|) unitSquareMeasure :=
    (U.integrable.sub V.integrable).abs
  have hg : Integrable g unitSquareMeasure := by
    exact (integrable_const (1 : ℝ)).indicator hS
  have hle : (fun z ↦ |U z - V z|) ≤ᵐ[unitSquareMeasure] g := by
    filter_upwards [heq, U.ae_mem_Icc, V.ae_mem_Icc] with z hz hzU hzV
    by_cases hmem : z ∈ S
    · rw [show g z = 1 by simp [g, hmem]]
      simpa [Real.dist_eq] using Real.dist_le_of_mem_Icc hzU hzV
    · rw [hz hmem]
      simp [g, hmem]
  calc
    (∫ z, |U z - V z| ∂unitSquareMeasure) ≤
        ∫ z, g z ∂unitSquareMeasure := integral_mono_ae hf hg hle
    _ = ∫ _ in S, (1 : ℝ) ∂unitSquareMeasure := by
      rw [MeasureTheory.integral_indicator hS]
    _ = unitSquareMeasure.real S := by
      rw [MeasureTheory.setIntegral_const]
      simp

/-- Moving both endpoints of a half-open interval monotonically controls the
measure of its symmetric difference by the two endpoint displacements. -/
theorem volumeReal_Ico_symmDiff_le {a b c d : UnitInterval}
    (hac : a ≤ c) (hbd : b ≤ d) :
    (volume : Measure UnitInterval).real (Ico a b ∆ Ico c d) ≤
      ((c : ℝ) - (a : ℝ)) + ((d : ℝ) - (b : ℝ)) := by
  have hsubset : Ico a b ∆ Ico c d ⊆ Ico a c ∪ Ico b d := by
    intro x hx
    rw [Set.symmDiff_def] at hx
    rcases hx with hx | hx
    · left
      refine ⟨hx.1.1, ?_⟩
      by_contra hxc
      apply hx.2
      exact ⟨le_of_not_gt hxc, hx.1.2.trans_le hbd⟩
    · right
      refine ⟨?_, hx.1.2⟩
      by_contra hxb
      apply hx.2
      exact ⟨hac.trans hx.1.1, lt_of_not_ge hxb⟩
  calc
    (volume : Measure UnitInterval).real (Ico a b ∆ Ico c d) ≤
        (volume : Measure UnitInterval).real (Ico a c ∪ Ico b d) :=
      measureReal_mono hsubset
    _ ≤ (volume : Measure UnitInterval).real (Ico a c) +
        (volume : Measure UnitInterval).real (Ico b d) :=
      measureReal_union_le _ _
    _ = ((c : ℝ) - (a : ℝ)) + ((d : ℝ) - (b : ℝ)) := by
      simp only [Measure.real, unitInterval.volume_Ico,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hac),
        ENNReal.toReal_ofReal (sub_nonneg.mpr hbd)]

namespace FiniteExtremalBlockModel

variable {k q : ℕ} {C : ColoredGraph (Fin q)}

/-- If the largest core has order at least `k`, its contribution leaves the
explicit integer gap `1 / k`; all remaining scaled mass is absorbed by the
total tail length. -/
theorem scaledBlockMass_le_k_sub_one_div_k_add_tail
    (M : FiniteExtremalBlockModel k q C)
    (hfirst : k ≤ M.orderedCoreOrder M.firstIndex) :
    ((k - 1 : ℕ) : ℝ) * M.blockMass ≤
      ((k - 1 : ℕ) : ℝ) / (k : ℝ) + M.tailBlockLength := by
  classical
  let s : ℝ := ((k - 1 : ℕ) : ℝ)
  let f : Fin M.componentCount → ℝ := fun a ↦
    s * (M.orderedLength a ^ 2 / (M.orderedCoreOrder a : ℝ))
  have hspos : 0 < s := by
    dsimp [s]
    exact_mod_cast kSubOne_pos M.three_le_k
  have hkpos : 0 < (k : ℝ) := by
    have hkposNat : 0 < k := lt_of_lt_of_le (by omega) M.three_le_k
    exact_mod_cast hkposNat
  have hfirstR :
      (k : ℝ) ≤ (M.orderedCoreOrder M.firstIndex : ℝ) := by
    exact_mod_cast hfirst
  have hfirstTerm : f M.firstIndex ≤ s / (k : ℝ) := by
    have ha2 : M.largestBlockLength ^ 2 ≤ 1 := by
      nlinarith [M.largestBlockLength_nonneg,
        M.largestBlockLength_le_one]
    change s * (M.largestBlockLength ^ 2 /
      (M.orderedCoreOrder M.firstIndex : ℝ)) ≤ s / (k : ℝ)
    calc
      s * (M.largestBlockLength ^ 2 /
          (M.orderedCoreOrder M.firstIndex : ℝ)) =
          (s * M.largestBlockLength ^ 2) /
            (M.orderedCoreOrder M.firstIndex : ℝ) := by ring
      _ ≤ s / (k : ℝ) :=
        div_le_div₀ hspos.le (mul_le_of_le_one_right hspos.le ha2)
          hkpos hfirstR
  have htailTerm : ∀ a ∈
      (Finset.univ : Finset (Fin M.componentCount)).erase M.firstIndex,
      f a ≤ M.orderedLength a := by
    intro a _ha
    have horder : s ≤ (M.orderedCoreOrder a : ℝ) := by
      dsimp [s]
      exact_mod_cast M.k_sub_one_le_orderedCoreOrder a
    have hdiv :
        (s * M.orderedLength a ^ 2) /
            (M.orderedCoreOrder a : ℝ) ≤ M.orderedLength a ^ 2 := by
      calc
        (s * M.orderedLength a ^ 2) /
              (M.orderedCoreOrder a : ℝ) ≤
            (s * M.orderedLength a ^ 2) / s :=
          div_le_div_of_nonneg_left
            (mul_nonneg hspos.le (sq_nonneg _)) hspos horder
        _ = M.orderedLength a ^ 2 := by field_simp
    change s * (M.orderedLength a ^ 2 /
      (M.orderedCoreOrder a : ℝ)) ≤ M.orderedLength a
    calc
      s * (M.orderedLength a ^ 2 /
          (M.orderedCoreOrder a : ℝ)) =
          (s * M.orderedLength a ^ 2) /
            (M.orderedCoreOrder a : ℝ) := by ring
      _ ≤ M.orderedLength a ^ 2 := hdiv
      _ ≤ M.orderedLength a := by
        nlinarith [M.orderedLength_nonneg a, M.orderedLength_le_one a]
  rw [M.blockMass_eq_sum, Finset.mul_sum]
  change ∑ a : Fin M.componentCount, f a ≤ _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ M.firstIndex)]
  calc
    (∑ a ∈ (Finset.univ : Finset (Fin M.componentCount)).erase M.firstIndex,
          f a) + f M.firstIndex ≤ M.tailBlockLength + s / (k : ℝ) :=
      add_le_add (Finset.sum_le_sum htailTerm) hfirstTerm
    _ = s / (k : ℝ) + M.tailBlockLength := add_comm _ _
    _ = ((k - 1 : ℕ) : ℝ) / (k : ℝ) + M.tailBlockLength := by rfl

end FiniteExtremalBlockModel

namespace OptimizerFiniteBlockApproximationResult

variable {k : ℕ} {γ : ℝ} {W : Graphon}

/-- The first position of the nonempty canonical ordered component list. -/
def firstComponentIndex
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) :
    Fin (A.model m).componentCount :=
  ⟨0, A.componentCount_pos m⟩

/-- The reduced regular core carried by the largest canonical component. -/
noncomputable def firstComponentCore
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) :
    RegularBlockCore k :=
  (A.model m).orderedCore (A.firstComponentIndex m)

/-- Order of the reduced core carried by the largest component. -/
def firstComponentCoreOrder
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) : ℕ :=
  (A.firstComponentCore m).order

@[simp] theorem firstComponentIndex_eq_firstIndex
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) :
    A.firstComponentIndex m = (A.model m).firstIndex :=
  rfl

theorem k_sub_one_le_firstComponentCoreOrder
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) :
    k - 1 ≤ A.firstComponentCoreOrder m := by
  exact RegularBlockCore.k_sub_one_le_order A.three_le_k
    (A.firstComponentCore m)

/-- Above the phase transition, the integer gap in the first core order is
eventually closed: the largest core has the minimum possible order `k - 1`.
The proof uses the explicit gap `1 / k`, not an abstract discreteness
argument. -/
theorem eventually_firstComponentCoreOrder_eq_k_sub_one
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hcrit : gammaK k ≤ γ) :
    ∀ᶠ m in atTop, A.firstComponentCoreOrder m = k - 1 := by
  let ε : ℝ := 1 / (4 * (k : ℝ))
  have hkpos : 0 < (k : ℝ) := by
    have hkposNat : 0 < k := lt_of_lt_of_le (by omega) A.three_le_k
    exact_mod_cast hkposNat
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hmass : ∀ᶠ m in atTop,
      1 - ε < ((k - 1 : ℕ) : ℝ) * A.blockMass m :=
    (tendsto_order.1 (A.criticalScaledBlockMass_tendsto_one hcrit)).1
      (1 - ε) (by linarith)
  have htail : ∀ᶠ m in atTop, A.tailBlockLength m < ε :=
    (tendsto_order.1 (A.criticalTailBlockLength_tendsto_zero hcrit)).2
      ε hεpos
  filter_upwards [hmass, htail] with m hm ht
  by_contra hne
  have hfirstNat : k ≤ A.firstComponentCoreOrder m := by
    have hmin := A.k_sub_one_le_firstComponentCoreOrder m
    omega
  have hfirstModel :
      k ≤ (A.model m).orderedCoreOrder (A.model m).firstIndex := by
    change k ≤ ((A.model m).orderedCore (A.model m).firstIndex).order
    rw [← A.firstComponentIndex_eq_firstIndex m]
    exact hfirstNat
  have hbound :=
    (A.model m).scaledBlockMass_le_k_sub_one_div_k_add_tail hfirstModel
  rw [← A.blockMass_eq_model_blockMass m] at hbound
  change ((k - 1 : ℕ) : ℝ) * A.blockMass m ≤
    ((k - 1 : ℕ) : ℝ) / (k : ℝ) + A.tailBlockLength m at hbound
  have hratio :
      ((k - 1 : ℕ) : ℝ) / (k : ℝ) = 1 - 1 / (k : ℝ) := by
    have hkOne : 1 ≤ k := le_trans (by omega) A.three_le_k
    rw [Nat.cast_sub hkOne, Nat.cast_one]
    field_simp
  have hgap : 2 * ε < 1 / (k : ℝ) := by
    have hklt : (k : ℝ) < 2 * (k : ℝ) := by nlinarith
    calc
      2 * ε = 1 / (2 * (k : ℝ)) := by
        dsimp [ε]
        field_simp
        ring
      _ < 1 / (k : ℝ) := one_div_lt_one_div_of_lt hkpos hklt
  rw [hratio] at hbound
  nlinarith

end OptimizerFiniteBlockApproximationResult

namespace RegularBlockCore

/-- A simple `(k-2)`-regular graph on exactly `k-1` vertices is complete. -/
theorem graph_eq_top_of_order_eq_k_sub_one {k : ℕ}
    (C : RegularBlockCore k) (hk : 3 ≤ k)
    (horder : C.order = k - 1) : C.graph = ⊤ := by
  classical
  rw [SimpleGraph.eq_top_iff_forall_isUniversal]
  intro v
  rw [← C.graph.degree_eq_card_sub_one v]
  simp only [C.degree_eq, Fintype.card_fin]
  omega

/-- Transport-safe strengthening of
`graph_eq_top_of_order_eq_k_sub_one`. -/
theorem eq_complete_of_order_eq_k_sub_one {k : ℕ}
    (C : RegularBlockCore k) (hk : 3 ≤ k)
    (horder : C.order = k - 1) : C = RegularBlockCore.complete k hk := by
  have hgraph := C.graph_eq_top_of_order_eq_k_sub_one hk horder
  cases C with
  | mk n hn G hconnected hregular =>
    dsimp at horder hgraph
    subst n
    subst G
    rfl

end RegularBlockCore

namespace OptimizerFiniteBlockApproximationResult

variable {k : ℕ} {γ : ℝ} {W : Graphon}

/-- Eventually the first core is literally the canonical complete core.
This form eliminates all dependent transports in the graphon comparison. -/
theorem eventually_firstComponentCore_eq_complete
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hcrit : gammaK k ≤ γ) :
    ∀ᶠ m in atTop,
      A.firstComponentCore m = RegularBlockCore.complete k A.three_le_k := by
  filter_upwards [A.eventually_firstComponentCoreOrder_eq_k_sub_one hcrit]
    with m hm
  exact (A.firstComponentCore m).eq_complete_of_order_eq_k_sub_one
    A.three_le_k hm

end OptimizerFiniteBlockApproximationResult

namespace OptimizerFiniteBlockApproximationResult

variable {k : ℕ} {γ : ℝ} {W : Graphon}

/-- On the critical/supercritical branch, the common profile mean is exactly
the off-diagonal value of `Wstar`. -/
theorem randomMean_eq_supercriticalOffDiagonal
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hcrit : gammaK k ≤ γ) :
    A.extremalApproximation.profile.randomMean =
      supercriticalOffDiagonal k γ := by
  rw [A.randomMean_eq_of_gammaK_le hcrit]
  unfold supercriticalOffDiagonal phaseLower
  ring

/-- The finite analytic layout underlying the canonical stage sequence. -/
noncomputable def stageLayout
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) :
    FiniteProfileBlockLayout k :=
  FiniteProfileBlockLayout.ofFiniteSequence (A.blockSequence m)
    (A.model m).componentCount (by
      rw [A.blockSequence_eq m]
      exact (A.model m).blockSequence_count)

@[simp] theorem stageLayout_count
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) :
    (A.stageLayout m).count = (A.model m).componentCount :=
  rfl

@[simp] theorem stageLayout_alpha
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ)
    (i : Fin (A.model m).componentCount) :
    (A.stageLayout m).alpha i = (A.model m).orderedLength i := by
  unfold stageLayout
  rw [FiniteProfileBlockLayout.ofFiniteSequence_alpha,
    A.blockSequence_eq m, (A.model m).blockSequence_alpha_of_lt i.isLt]

@[simp] theorem stageLayout_core
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ)
    (i : Fin (A.model m).componentCount) :
    (A.stageLayout m).core i = (A.model m).orderedCore i := by
  unfold stageLayout
  rw [FiniteProfileBlockLayout.ofFiniteSequence_core,
    A.blockSequence_eq m, (A.model m).blockSequence_core_of_lt i.isLt]

/-- The graphon carried by `stageLayout` is literally the retained stage
graphon. -/
theorem stageLayout_graphon_eq_blockGraphon
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) :
    (A.stageLayout m).graphon
      A.extremalApproximation.profile.randomMean
      ⟨A.extremalApproximation.profile.randomMean_pos.le,
        A.extremalApproximation.profile.randomMean_lt_one.le⟩ =
      A.blockGraphon m := by
  calc
    (A.stageLayout m).graphon
          A.extremalApproximation.profile.randomMean
          ⟨A.extremalApproximation.profile.randomMean_pos.le,
            A.extremalApproximation.profile.randomMean_lt_one.le⟩ =
        profileWLambda A.extremalApproximation.profile.randomMean
          (A.blockSequence m)
          ⟨A.extremalApproximation.profile.randomMean_pos.le,
            A.extremalApproximation.profile.randomMean_lt_one.le⟩ := by
      unfold stageLayout
      exact FiniteProfileBlockLayout.graphon_ofFiniteSequence_eq_profileWLambda
        A.three_le_k A.extremalApproximation.profile.randomMean
          ⟨A.extremalApproximation.profile.randomMean_pos.le,
            A.extremalApproximation.profile.randomMean_lt_one.le⟩
          (A.blockSequence m) (A.model m).componentCount _
    _ = A.blockGraphon m := (A.blockGraphon_eq m).symm

/-- The canonical graphon obtained by deleting every stage block except the
largest one, without changing coordinates inside that block. -/
noncomputable def firstBlockGraphon
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) : Graphon :=
  (A.stageLayout m).prefixGraphon
    A.extremalApproximation.profile.randomMean
    ⟨A.extremalApproximation.profile.randomMean_pos.le,
      A.extremalApproximation.profile.randomMean_lt_one.le⟩ 1

/-- The omitted-square expression in the prefix estimate is exactly the
finite model's squared tail. -/
theorem stageLayout_sum_omittedSquares_one_eq_tailBlockSquareSum
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) :
    (∑ i : Fin (A.stageLayout m).count,
        if 1 ≤ (i : ℕ) then (A.stageLayout m).alpha i ^ 2 else 0) =
      (A.model m).tailBlockSquareSum := by
  classical
  let first : Fin (A.model m).componentCount := (A.model m).firstIndex
  have hfilter :
      (Finset.univ.filter fun i : Fin (A.model m).componentCount ↦ 1 ≤ (i : ℕ)) =
        (Finset.univ : Finset (Fin (A.model m).componentCount)).erase first := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · intro hi
      refine ⟨?_, trivial⟩
      intro hifirst
      have : (i : ℕ) = 0 := congrArg Fin.val hifirst
      omega
    · rintro ⟨hine, _⟩
      have hi0 : (i : ℕ) ≠ 0 := by
        intro hi0
        apply hine
        apply Fin.ext
        exact hi0
      omega
  rw [← Finset.sum_filter]
  change (∑ i ∈ Finset.univ.filter (fun i : Fin (A.model m).componentCount ↦
      1 ≤ (i : ℕ)), (A.stageLayout m).alpha i ^ 2) = _
  rw [hfilter]
  unfold FiniteExtremalBlockModel.tailBlockSquareSum
  apply Finset.sum_congr rfl
  intro i _hi
  rw [A.stageLayout_alpha m i]

/-- Deleting all blocks after the largest costs at most their total squared
length, hence at most the total tail length. -/
theorem graphonL1Dist_blockGraphon_firstBlockGraphon_le_tailBlockLength
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) :
    graphonL1Dist (A.blockGraphon m) (A.firstBlockGraphon m) ≤
      A.tailBlockLength m := by
  let p := A.extremalApproximation.profile.randomMean
  let hp : p ∈ Icc (0 : ℝ) 1 :=
    ⟨A.extremalApproximation.profile.randomMean_pos.le,
      A.extremalApproximation.profile.randomMean_lt_one.le⟩
  calc
    graphonL1Dist (A.blockGraphon m) (A.firstBlockGraphon m) =
        graphonL1Dist ((A.stageLayout m).graphon p hp)
          ((A.stageLayout m).prefixGraphon p hp 1) := by
      rw [A.stageLayout_graphon_eq_blockGraphon m]
      rfl
    _ ≤ ∑ i : Fin (A.stageLayout m).count,
          if 1 ≤ (i : ℕ) then (A.stageLayout m).alpha i ^ 2 else 0 :=
      (A.stageLayout m).graphonL1Dist_prefixGraphon_le_sum_omittedSquares
        A.three_le_k p hp 1
    _ = (A.model m).tailBlockSquareSum :=
      A.stageLayout_sum_omittedSquares_one_eq_tailBlockSquareSum m
    _ ≤ A.tailBlockLength m :=
      (A.model m).tailBlockSquareSum_le_second_mul_tail.trans
        (A.model m).second_mul_tail_le_tail

end OptimizerFiniteBlockApproximationResult

/-- The arbitrary-profile graphon of the minimum-order complete core is
exactly the distinguished supercritical matrix graphon. -/
theorem profileXiGraphon_complete_eq_Wstar {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hcrit : gammaK k ≤ γ) (hγlt : γ < 1) :
    profileXiGraphon (supercriticalOffDiagonal k γ)
      (RegularBlockCore.complete k hk)
      ⟨supercriticalOffDiagonal_nonneg hk hcrit,
        (supercriticalOffDiagonal_lt_one hk hγlt).le⟩ =
      Wstar k hk γ ⟨hcrit, hγlt⟩ := by
  classical
  unfold profileXiGraphon Wstar
  congr 1
  funext i j
  change (if i = j then 1 else
      if (⊤ : SimpleGraph (Fin (k - 1))).Adj i j then
        supercriticalOffDiagonal k γ else 0) =
    if i = j then 1 else supercriticalOffDiagonal k γ
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij]
  · rw [if_neg hij, if_neg hij]
    rw [if_pos]
    exact (SimpleGraph.top_adj i j).2 hij

/-! ### Quantitative growth of one complete block -/

/-- The profile graphon consisting of one complete core block of length
`α`, in the canonical left-justified coordinates. -/
def oneCompleteProfileBlockGraphon (k : ℕ) (hk : 3 ≤ k)
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) : Graphon :=
  profileWLambda p (oneBlockSequence k hk α hα0 hα1) hp

/-- Symmetric differences between the scaled vertex cells of a complete
block and the full equal partition. -/
def oneCompleteCellErrorSet (k : ℕ) (hk : 3 ≤ k) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) : Set UnitInterval :=
  ⋃ v : Fin (k - 1),
    (oneBlockSequence k hk α hα0 hα1).blockCell 0 v ∆ equalCell v

theorem measurableSet_oneCompleteCellErrorSet
    (k : ℕ) (hk : 3 ≤ k) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) :
    MeasurableSet (oneCompleteCellErrorSet k hk α hα0 hα1) := by
  unfold oneCompleteCellErrorSet
  exact MeasurableSet.iUnion fun v ↦
    ((oneBlockSequence k hk α hα0 hα1).measurableSet_blockCell 0 v)
      |>.symmDiff (measurableSet_equalCell v)

private theorem oneCompleteCell_left_le {k : ℕ} (hk : 3 ≤ k)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (v : Fin (k - 1)) :
    (oneBlockSequence k hk α hα0 hα1).cellLeftUI 0 v ≤
      equalCellLeft v := by
  change ((oneBlockSequence k hk α hα0 hα1).cellLeftUI 0 v).1 ≤
    (equalCellLeft v).1
  simp only [AdmissibleBlockSequence.cellLeftUI,
    AdmissibleBlockSequence.cellLeft,
    AdmissibleBlockSequence.blockStart_zero,
    oneBlockSequence_alpha_zero, equalCellLeft, zero_add]
  exact mul_le_of_le_one_left (by positivity) hα1

private theorem oneCompleteCell_right_le {k : ℕ} (hk : 3 ≤ k)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (v : Fin (k - 1)) :
    (oneBlockSequence k hk α hα0 hα1).cellRightUI 0 v ≤
      equalCellRight v := by
  change ((oneBlockSequence k hk α hα0 hα1).cellRightUI 0 v).1 ≤
    (equalCellRight v).1
  simp only [AdmissibleBlockSequence.cellRightUI,
    AdmissibleBlockSequence.cellRight,
    AdmissibleBlockSequence.blockStart_zero,
    oneBlockSequence_alpha_zero, equalCellRight, zero_add]
  exact mul_le_of_le_one_left (by positivity) hα1

/-- Each scaled vertex cell differs from its full-size counterpart on length
at most `2 * (1 - α)`. -/
theorem volumeReal_oneCompleteCell_symmDiff_le {k : ℕ} (hk : 3 ≤ k)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (v : Fin (k - 1)) :
    (volume : Measure UnitInterval).real
        ((oneBlockSequence k hk α hα0 hα1).blockCell 0 v ∆ equalCell v) ≤
      2 * (1 - α) := by
  let L := oneBlockSequence k hk α hα0 hα1
  have hkpos : 0 < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hrLeft0 : 0 ≤ (v : ℝ) / ((k - 1 : ℕ) : ℝ) := by positivity
  have hrLeft1 : (v : ℝ) / ((k - 1 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hkpos]
    exact_mod_cast v.isLt.le
  have hrRight0 : 0 ≤ (((v : ℕ) + 1 : ℝ) / ((k - 1 : ℕ) : ℝ)) := by
    positivity
  have hrRight1 :
      (((v : ℕ) + 1 : ℝ) / ((k - 1 : ℕ) : ℝ)) ≤ 1 := by
    rw [div_le_one hkpos]
    exact_mod_cast v.isLt
  have hleftDisp :
      ((equalCellLeft v : UnitInterval) : ℝ) -
          ((L.cellLeftUI 0 v : UnitInterval) : ℝ) ≤ 1 - α := by
    have hformula : (v : ℝ) / ((k - 1 : ℕ) : ℝ) -
        α * ((v : ℝ) / ((k - 1 : ℕ) : ℝ)) ≤ 1 - α := by
      calc
      (v : ℝ) / ((k - 1 : ℕ) : ℝ) -
          α * ((v : ℝ) / ((k - 1 : ℕ) : ℝ)) =
          (1 - α) * ((v : ℝ) / ((k - 1 : ℕ) : ℝ)) := by ring
      _ ≤ (1 - α) * 1 :=
        mul_le_mul_of_nonneg_left hrLeft1 (by linarith)
      _ = 1 - α := mul_one _
    simpa [L, oneBlockSequence, equalCellLeft,
      AdmissibleBlockSequence.cellLeftUI,
      AdmissibleBlockSequence.cellLeft,
      AdmissibleBlockSequence.blockStart_zero] using hformula
  have hrightDisp :
      ((equalCellRight v : UnitInterval) : ℝ) -
          ((L.cellRightUI 0 v : UnitInterval) : ℝ) ≤ 1 - α := by
    have hformula : (((v : ℕ) + 1 : ℝ) / ((k - 1 : ℕ) : ℝ)) -
        α * (((v : ℕ) + 1 : ℝ) / ((k - 1 : ℕ) : ℝ)) ≤ 1 - α := by
      calc
      (((v : ℕ) + 1 : ℝ) / ((k - 1 : ℕ) : ℝ)) -
          α * (((v : ℕ) + 1 : ℝ) / ((k - 1 : ℕ) : ℝ)) =
          (1 - α) *
            (((v : ℕ) + 1 : ℝ) / ((k - 1 : ℕ) : ℝ)) := by ring
      _ ≤ (1 - α) * 1 :=
        mul_le_mul_of_nonneg_left hrRight1 (by linarith)
      _ = 1 - α := mul_one _
    simpa [L, oneBlockSequence, equalCellRight,
      AdmissibleBlockSequence.cellRightUI,
      AdmissibleBlockSequence.cellRight,
      AdmissibleBlockSequence.blockStart_zero] using hformula
  calc
    (volume : Measure UnitInterval).real
        (L.blockCell 0 v ∆ equalCell v) ≤
        ((equalCellLeft v : UnitInterval) : ℝ) -
            ((L.cellLeftUI 0 v : UnitInterval) : ℝ) +
          (((equalCellRight v : UnitInterval) : ℝ) -
            ((L.cellRightUI 0 v : UnitInterval) : ℝ)) :=
      volumeReal_Ico_symmDiff_le
        (oneCompleteCell_left_le hk hα0 hα1 v)
        (oneCompleteCell_right_le hk hα0 hα1 v)
    _ ≤ 2 * (1 - α) := by linarith

/-- The full one-dimensional boundary-error set has explicit measure at most
`2 (k-1) (1-α)`. -/
theorem volumeReal_oneCompleteCellErrorSet_le
    (k : ℕ) (hk : 3 ≤ k) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (volume : Measure UnitInterval).real
        (oneCompleteCellErrorSet k hk α hα0 hα1) ≤
      2 * ((k - 1 : ℕ) : ℝ) * (1 - α) := by
  calc
    (volume : Measure UnitInterval).real
        (oneCompleteCellErrorSet k hk α hα0 hα1) ≤
        ∑ v : Fin (k - 1),
          (volume : Measure UnitInterval).real
            ((oneBlockSequence k hk α hα0 hα1).blockCell 0 v ∆
              equalCell v) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _v : Fin (k - 1), 2 * (1 - α) := by
      apply Finset.sum_le_sum
      intro v _hv
      exact volumeReal_oneCompleteCell_symmDiff_le hk hα0 hα1 v
    _ = 2 * ((k - 1 : ℕ) : ℝ) * (1 - α) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

/-- The two-dimensional disagreement set generated by the scaled cell
boundaries. -/
def oneCompleteGraphonErrorSet (k : ℕ) (hk : 3 ≤ k) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) : Set UnitSquare :=
  let B := oneCompleteCellErrorSet k hk α hα0 hα1
  (B ×ˢ (Set.univ : Set UnitInterval)) ∪
    ((Set.univ : Set UnitInterval) ×ˢ B)

theorem measurableSet_oneCompleteGraphonErrorSet
    (k : ℕ) (hk : 3 ≤ k) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) :
    MeasurableSet (oneCompleteGraphonErrorSet k hk α hα0 hα1) := by
  unfold oneCompleteGraphonErrorSet
  exact ((measurableSet_oneCompleteCellErrorSet k hk α hα0 hα1).prod
    MeasurableSet.univ).union
      (MeasurableSet.univ.prod
        (measurableSet_oneCompleteCellErrorSet k hk α hα0 hα1))

private theorem mem_oneCompleteCell_iff_mem_equalCell_of_not_mem_error
    {k : ℕ} (hk : 3 ≤ k) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) {x : UnitInterval}
    (hx : x ∉ oneCompleteCellErrorSet k hk α hα0 hα1)
    (v : Fin (k - 1)) :
    x ∈ (oneBlockSequence k hk α hα0 hα1).blockCell 0 v ↔
      x ∈ equalCell v := by
  have hnot : x ∉
      ((oneBlockSequence k hk α hα0 hα1).blockCell 0 v ∆ equalCell v) := by
    intro hmem
    apply hx
    exact Set.mem_iUnion.2 ⟨v, hmem⟩
  constructor
  · intro hscaled
    by_contra hfull
    apply hnot
    rw [Set.mem_symmDiff]
    exact Or.inl ⟨hscaled, hfull⟩
  · intro hfull
    by_contra hscaled
    apply hnot
    rw [Set.mem_symmDiff]
    exact Or.inr ⟨hfull, hscaled⟩

/-- A complete block of length `α` differs from its full-length core graphon
by at most `4 (k-1) (1-α)` in canonical-coordinate `L¹` distance. -/
theorem graphonL1Dist_oneCompleteProfileBlock_profileXiGraphon_le
    {k : ℕ} (hk : 3 ≤ k) {p α : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hα0 : 0 < α) (hα1 : α ≤ 1) :
    graphonL1Dist
        (oneCompleteProfileBlockGraphon k hk p hp α hα0 hα1)
        (profileXiGraphon p (RegularBlockCore.complete k hk) hp) ≤
      4 * ((k - 1 : ℕ) : ℝ) * (1 - α) := by
  let L := oneBlockSequence k hk α hα0 hα1
  let B := oneCompleteCellErrorSet k hk α hα0 hα1
  let S := oneCompleteGraphonErrorSet k hk α hα0 hα1
  have hEq : ∀ᵐ z ∂unitSquareMeasure, z ∉ S →
      oneCompleteProfileBlockGraphon k hk p hp α hα0 hα1 z =
        profileXiGraphon p (RegularBlockCore.complete k hk) hp z := by
    filter_upwards [profileWLambda_ae_eq_profileKernel p L hp,
      matrixGraphon_ae_eq_kernel
        (profileXiMatrix p (RegularBlockCore.complete k hk))
        (profileXiMatrix_isSymm p (RegularBlockCore.complete k hk))
        (profileXiMatrix_nonneg hp.1 (RegularBlockCore.complete k hk))
        (profileXiMatrix_le_one hp.2 (RegularBlockCore.complete k hk)),
      ae_mem_iUnion_equalCell_prod (show 0 < k - 1 by omega)]
        with z hzL hzXi hzCover
    intro hzS
    have hxB : z.1 ∉ B := by
      intro hx
      apply hzS
      exact Or.inl ⟨hx, Set.mem_univ _⟩
    have hyB : z.2 ∉ B := by
      intro hy
      apply hzS
      exact Or.inr ⟨Set.mem_univ _, hy⟩
    obtain ⟨ij, hij⟩ := Set.mem_iUnion.1 hzCover
    have hxScaled : z.1 ∈ L.blockCell 0 ij.1 :=
      (mem_oneCompleteCell_iff_mem_equalCell_of_not_mem_error
        hk hα0 hα1 hxB ij.1).2 hij.1
    have hyScaled : z.2 ∈ L.blockCell 0 ij.2 :=
      (mem_oneCompleteCell_iff_mem_equalCell_of_not_mem_error
        hk hα0 hα1 hyB ij.2).2 hij.2
    change profileWLambda p L hp z =
      profileXiGraphon p (RegularBlockCore.complete k hk) hp z
    rw [hzL]
    have hzXi' :
        profileXiGraphon p (RegularBlockCore.complete k hk) hp z =
          matrixKernel
            (profileXiMatrix p (RegularBlockCore.complete k hk)) z := by
      simpa only [profileXiGraphon] using hzXi
    rw [hzXi',
      L.profileKernel_of_mem hk p 0 ij.1 ij.2 z hxScaled hyScaled,
      matrixKernel_of_mem
        (profileXiMatrix p (RegularBlockCore.complete k hk))
        ij.1 ij.2 z hij.1 hij.2]
    rfl
  have hsupport := graphonL1Dist_le_measureReal_of_ae_eq_off
    (oneCompleteProfileBlockGraphon k hk p hp α hα0 hα1)
    (profileXiGraphon p (RegularBlockCore.complete k hk) hp) S
    (measurableSet_oneCompleteGraphonErrorSet k hk α hα0 hα1) hEq
  have hprodLeft :
      unitSquareMeasure.real
          (B ×ˢ (Set.univ : Set UnitInterval)) =
        (volume : Measure UnitInterval).real B := by
    simp only [Measure.real, Measure.prod_prod, volume_unitInterval_univ,
      mul_one, ENNReal.toReal_one]
  have hprodRight :
      unitSquareMeasure.real
          ((Set.univ : Set UnitInterval) ×ˢ B) =
        (volume : Measure UnitInterval).real B := by
    simp only [Measure.real, Measure.prod_prod, volume_unitInterval_univ,
      one_mul, ENNReal.toReal_one]
  have hSmeasure : unitSquareMeasure.real S ≤
      2 * (volume : Measure UnitInterval).real B := by
    calc
      unitSquareMeasure.real S ≤
          unitSquareMeasure.real
              (B ×ˢ (Set.univ : Set UnitInterval)) +
            unitSquareMeasure.real
              ((Set.univ : Set UnitInterval) ×ˢ B) :=
        measureReal_union_le _ _
      _ = 2 * (volume : Measure UnitInterval).real B := by
        rw [hprodLeft, hprodRight]
        ring
  have hBmeasure : (volume : Measure UnitInterval).real B ≤
      2 * ((k - 1 : ℕ) : ℝ) * (1 - α) :=
    volumeReal_oneCompleteCellErrorSet_le k hk hα0 hα1
  calc
    graphonL1Dist
        (oneCompleteProfileBlockGraphon k hk p hp α hα0 hα1)
        (profileXiGraphon p (RegularBlockCore.complete k hk) hp) ≤
        unitSquareMeasure.real S := hsupport
    _ ≤ 2 * (volume : Measure UnitInterval).real B := hSmeasure
    _ ≤ 4 * ((k - 1 : ℕ) : ℝ) * (1 - α) := by
      nlinarith

/-- Requested explicit complete-first-block estimate against `Wstar`. -/
theorem graphonL1Dist_oneCompleteProfileBlock_Wstar_le
    {k : ℕ} (hk : 3 ≤ k) {γ α : ℝ}
    (hcrit : gammaK k ≤ γ) (hγlt : γ < 1)
    (hα0 : 0 < α) (hα1 : α ≤ 1) :
    graphonL1Dist
        (oneCompleteProfileBlockGraphon k hk
          (supercriticalOffDiagonal k γ)
          ⟨supercriticalOffDiagonal_nonneg hk hcrit,
            (supercriticalOffDiagonal_lt_one hk hγlt).le⟩
          α hα0 hα1)
        (Wstar k hk γ ⟨hcrit, hγlt⟩) ≤
      4 * ((k - 1 : ℕ) : ℝ) * (1 - α) := by
  rw [← profileXiGraphon_complete_eq_Wstar hk hcrit hγlt]
  exact graphonL1Dist_oneCompleteProfileBlock_profileXiGraphon_le
    hk _ hα0 hα1

namespace OptimizerFiniteBlockApproximationResult

variable {k : ℕ} {γ : ℝ} {W : Graphon}

/-- The retained first stage block is explicitly close to the profile
graphon carried by its reduced core. -/
theorem graphonL1Dist_firstBlockGraphon_profileFirstComponentCore_le
    (A : OptimizerFiniteBlockApproximationResult k γ W) (m : ℕ) :
    graphonL1Dist (A.firstBlockGraphon m)
        (profileXiGraphon A.extremalApproximation.profile.randomMean
          (A.firstComponentCore m)
          ⟨A.extremalApproximation.profile.randomMean_pos.le,
            A.extremalApproximation.profile.randomMean_lt_one.le⟩) ≤
      4 * (A.firstComponentCoreOrder m : ℝ) *
        (1 - A.largestBlockLength m) := by
  let p := A.extremalApproximation.profile.randomMean
  let hp : p ∈ Icc (0 : ℝ) 1 :=
    ⟨A.extremalApproximation.profile.randomMean_pos.le,
      A.extremalApproximation.profile.randomMean_lt_one.le⟩
  have h :=
    (A.stageLayout m).graphonL1Dist_prefixGraphon_one_profileXiGraphon_le
      p hp (A.componentCount_pos m)
  have hindex :
      (⟨0, A.componentCount_pos m⟩ : Fin (A.model m).componentCount) =
        (A.model m).firstIndex := by
    apply Fin.ext
    rfl
  unfold largestBlockLength FiniteExtremalBlockModel.largestBlockLength
  rw [← hindex]
  simpa [firstBlockGraphon, firstComponentCore, firstComponentIndex,
    firstComponentCoreOrder, p, hp] using h

/-- Once the integer gap has closed, the explicit first-block estimate is
an estimate directly against `Wstar`. -/
theorem eventually_graphonL1Dist_firstBlockGraphon_Wstar_le
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hcrit : gammaK k ≤ γ) (hγlt : γ < 1) :
    ∀ᶠ m in atTop,
      graphonL1Dist (A.firstBlockGraphon m)
          (Wstar k A.three_le_k γ ⟨hcrit, hγlt⟩) ≤
        4 * ((k - 1 : ℕ) : ℝ) * (1 - A.largestBlockLength m) := by
  filter_upwards [A.eventually_firstComponentCore_eq_complete hcrit]
    with m hm
  have h :=
    A.graphonL1Dist_firstBlockGraphon_profileFirstComponentCore_le m
  rw [hm] at h
  have hprofile :
      profileXiGraphon A.extremalApproximation.profile.randomMean
          (RegularBlockCore.complete k A.three_le_k)
          ⟨A.extremalApproximation.profile.randomMean_pos.le,
            A.extremalApproximation.profile.randomMean_lt_one.le⟩ =
        Wstar k A.three_le_k γ ⟨hcrit, hγlt⟩ := by
    simpa only [A.randomMean_eq_supercriticalOffDiagonal hcrit] using
      profileXiGraphon_complete_eq_Wstar A.three_le_k hcrit hγlt
  have horder : A.firstComponentCoreOrder m = k - 1 := by
    simpa only [firstComponentCoreOrder, RegularBlockCore.complete_order] using
      congrArg RegularBlockCore.order hm
  rw [hprofile, horder] at h
  exact h

/-- The retained first block converges in canonical-coordinate `L¹` to
`Wstar`. -/
theorem graphonL1Dist_firstBlockGraphon_Wstar_tendsto
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hcrit : gammaK k ≤ γ) (hγlt : γ < 1) :
    Tendsto
      (fun m ↦ graphonL1Dist (A.firstBlockGraphon m)
        (Wstar k A.three_le_k γ ⟨hcrit, hγlt⟩))
      atTop (𝓝 0) := by
  let r : ℕ → ℝ := fun m ↦
    4 * ((k - 1 : ℕ) : ℝ) * (1 - A.largestBlockLength m)
  have hr : Tendsto r atTop (𝓝 0) := by
    have honeMinus : Tendsto
        (fun m ↦ 1 - A.largestBlockLength m) atTop (𝓝 0) := by
      simpa using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub
          (A.criticalLargestBlockLength_tendsto_one hcrit))
    simpa [r] using
      (tendsto_const_nhds (x := 4 * ((k - 1 : ℕ) : ℝ))).mul honeMinus
  have hbound : ∀ᶠ m in atTop,
      graphonL1Dist (A.firstBlockGraphon m)
          (Wstar k A.three_le_k γ ⟨hcrit, hγlt⟩) ≤ r m := by
    simpa [r] using
      A.eventually_graphonL1Dist_firstBlockGraphon_Wstar_le hcrit hγlt
  rw [tendsto_order]
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun m ↦
      ha.trans_le (graphonL1Dist_nonneg _ _)
  · intro b hb
    filter_upwards [hbound, (tendsto_order.1 hr).2 b hb] with m hm hrm
    exact hm.trans_lt hrm

/-- The entire canonical finite block graphon converges in `L¹` to `Wstar`:
the deleted tail and the first-block boundary error both vanish. -/
theorem graphonL1Dist_blockGraphon_Wstar_tendsto
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hcrit : gammaK k ≤ γ) (hγlt : γ < 1) :
    Tendsto
      (fun m ↦ graphonL1Dist (A.blockGraphon m)
        (Wstar k A.three_le_k γ ⟨hcrit, hγlt⟩))
      atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun m ↦ A.tailBlockLength m +
        graphonL1Dist (A.firstBlockGraphon m)
          (Wstar k A.three_le_k γ ⟨hcrit, hγlt⟩))
      atTop (𝓝 0) := by
    simpa using (A.criticalTailBlockLength_tendsto_zero hcrit).add
      (A.graphonL1Dist_firstBlockGraphon_Wstar_tendsto hcrit hγlt)
  exact squeeze_zero
    (fun m ↦ graphonL1Dist_nonneg _ _)
    (fun m ↦
      (graphonL1Dist_triangle (A.blockGraphon m) (A.firstBlockGraphon m)
        (Wstar k A.three_le_k γ ⟨hcrit, hγlt⟩)).trans
        (add_le_add
          (A.graphonL1Dist_blockGraphon_firstBlockGraphon_le_tailBlockLength m)
          le_rfl))
    hupper

/-- Hence the canonical finite block graphons converge to `Wstar` in cut
distance as well. -/
theorem cutDist_blockGraphon_Wstar_tendsto
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hcrit : gammaK k ≤ γ) (hγlt : γ < 1) :
    Tendsto
      (fun m ↦ cutDist (A.blockGraphon m)
        (Wstar k A.three_le_k γ ⟨hcrit, hγlt⟩))
      atTop (𝓝 0) := by
  exact squeeze_zero
    (fun m ↦ cutDist_nonneg _ _)
    (fun m ↦ cutDist_le_graphonL1Dist _ _)
    (A.graphonL1Dist_blockGraphon_Wstar_tendsto hcrit hγlt)

/-- The optimizer target and the supercritical candidate are the same cut
limit of the canonical finite block sequence. -/
theorem cutDist_target_Wstar_eq_zero
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hcrit : gammaK k ≤ γ) :
    cutDist A.extremalApproximation.target
      (Wstar k A.three_le_k γ ⟨hcrit, hγ.2⟩) = 0 := by
  exact cutDist_eq_zero_of_common_approximation A.cut_tendsto
    (A.cutDist_blockGraphon_Wstar_tendsto hcrit hγ.2)

/-- Every critical or supercritical optimizer target is cut-equivalent to
the unique member of the paper's candidate family. -/
theorem exists_supercritical_candidate_equivalent
    (A : OptimizerFiniteBlockApproximationResult k γ W)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hcrit : gammaK k ≤ γ) :
    ∃ V, V ∈ candidateOptimizerFamily k γ ∧
      cutDist A.extremalApproximation.target V = 0 := by
  refine ⟨Wstar k A.three_le_k γ ⟨hcrit, hγ.2⟩, ?_,
    A.cutDist_target_Wstar_eq_zero hγ hcrit⟩
  rw [candidateOptimizerFamily_of_ge A.three_le_k hγ hcrit]
  exact Set.mem_singleton _

end OptimizerFiniteBlockApproximationResult

end InducedStars
