import InducedStars.Structure.Subcritical.ProfileLeftoverRows
import InducedStars.Structure.Supercritical.SupportPatternCounting

/-!
# Finite counting tools for fixed-remainder leftovers

The small-side graph is fixed throughout the neighborhood encoding.
The error budget is expressed using binary entropy and binary logarithms;
all natural exponential conversions below are explicit.
-/

noncomputable section
open Finset Set
open scoped Classical BigOperators
namespace InducedStars

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A three-piece row code for a graph all of whose edges meet `B`.
The possible rows in the first two pieces are explicit finite families. -/
theorem subcritical_card_graphFamily_le_rowProduct
    (F : Finset (SimpleGraph V)) (U S B : Finset V)
    (AV AS : Finset (Finset V)) (hcover : U ∪ S ∪ B = Finset.univ)
    (hincident : ∀ L ∈ F, ∀ x y, L.Adj x y → x ∈ B ∨ y ∈ B)
    (hU : ∀ L ∈ F, ∀ v ∈ B, U.filter (L.Adj v) ∈ AV)
    (hS : ∀ L ∈ F, ∀ v ∈ B, S.filter (L.Adj v) ∈ AS) :
    F.card ≤ (AV.card * AS.card * 2 ^ B.card) ^ B.card := by
  let Code := {v // v ∈ B} →
    ({A // A ∈ AV} × {A // A ∈ AS} × {A // A ∈ B.powerset})
  let encode : {L // L ∈ F} → Code := fun L v ↦
    (⟨U.filter (L.val.Adj v.val), hU L.val L.property v.val v.property⟩,
      ⟨S.filter (L.val.Adj v.val), hS L.val L.property v.val v.property⟩,
      ⟨B.filter (L.val.Adj v.val), Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩)
  have hinj : Function.Injective encode := by
    intro L M heq
    apply Subtype.ext
    have hrow (v : V) (hv : v ∈ B) (y : V) : L.val.Adj v y ↔ M.val.Adj v y := by
      have hu : U.filter (L.val.Adj v) = U.filter (M.val.Adj v) :=
        congrArg (fun c : Code ↦ ((c ⟨v, hv⟩).1).val) heq
      have hs : S.filter (L.val.Adj v) = S.filter (M.val.Adj v) :=
        congrArg (fun c : Code ↦ ((c ⟨v, hv⟩).2.1).val) heq
      have hb : B.filter (L.val.Adj v) = B.filter (M.val.Adj v) :=
        congrArg (fun c : Code ↦ ((c ⟨v, hv⟩).2.2).val) heq
      have hy : y ∈ U ∪ S ∪ B := by rw [hcover]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp hy with hy | hy
      · rcases Finset.mem_union.mp hy with hy | hy
        · have hh := congrArg (fun A : Finset V ↦ y ∈ A) hu
          simpa [hy] using (iff_of_eq hh)
        · have hh := congrArg (fun A : Finset V ↦ y ∈ A) hs
          simpa [hy] using (iff_of_eq hh)
      · have hh := congrArg (fun A : Finset V ↦ y ∈ A) hb
        simpa [hy] using (iff_of_eq hh)
    ext x y
    by_cases hx : x ∈ B
    · exact hrow x hx y
    by_cases hy : y ∈ B
    · exact (L.val.symm.iff x y).trans ((hrow y hy x).trans (M.val.symm.iff y x))
    constructor
    · intro h
      exact ((hincident L.val L.property x y h).elim hx hy).elim
    · intro h
      exact ((hincident M.val M.property x y h).elim hx hy).elim
  have hc := Fintype.card_le_of_injective encode hinj
  have hpow : Fintype.card {A // A ∈ B.powerset} = 2 ^ B.card := by
    rw [Fintype.card_coe, Finset.card_powerset]
  simpa only [Code, Fintype.card_fun, Fintype.card_prod, hpow,
    Fintype.card_coe, mul_assoc] using hc

/-- The sharp Hamming-ball bound in natural-exponential form, including
zero capacity and zero floored radius. -/
theorem subcritical_smallSubsetCard_le_exp_entropy (U : Finset V)
    {t : ℝ} (ht : 0 ≤ t) (htHalf : t ≤ 1 / 2) :
    ((finsetSubsetsAtMost U ⌊t * U.card⌋₊).card : ℝ) ≤
      Real.exp (Real.log 2 * binaryEntropy t * U.card) := by
  rw [card_finsetSubsetsAtMost]
  let r : ℕ := ⌊t * U.card⌋₊
  have hEnt : 0 ≤ binaryEntropy t := binaryEntropy_nonneg ht (by linarith)
  have hr : (r : ℝ) ≤ t * U.card := Nat.floor_le (by positivity)
  by_cases hz : r = 0
  · change (hammingBallVolume U.card r : ℝ) ≤ _
    rw [hz]
    simp only [hammingBallVolume, Nat.zero_add, Finset.range_one, Finset.sum_singleton,
      Nat.choose_zero_right, Nat.cast_one]
    exact Real.one_le_exp (by positivity)
  have hrpos : 0 < r := Nat.pos_of_ne_zero hz
  have hrposR : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hN : (0 : ℝ) < U.card := by
    by_contra hN
    have hNz : (U.card : ℝ) = 0 := le_antisymm (le_of_not_gt hN) (Nat.cast_nonneg _)
    rw [hNz, mul_zero] at hr
    linarith
  have hhalf : 2 * r ≤ U.card := by
    have hh := mul_le_mul_of_nonneg_right htHalf (Nat.cast_nonneg U.card)
    exact_mod_cast (show 2 * (r : ℝ) ≤ U.card by linarith)
  have hratio : (r : ℝ) / U.card ≤ t := (div_le_iff₀ hN).mpr hr
  have hmono : binaryEntropy ((r : ℝ) / U.card) ≤ binaryEntropy t := by
    apply div_le_div_of_nonneg_right _ realLogTwo_pos.le
    exact Real.binEntropy_strictMonoOn.monotoneOn
      ⟨by positivity, by norm_num; linarith⟩ ⟨ht, by norm_num; linarith⟩ hratio
  have hlog := (log2_hammingBallVolume_le U.card r hrpos hhalf).trans
    (mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg U.card))
  have hvol : (0 : ℝ) < hammingBallVolume U.card r := by
    exact_mod_cast hammingBallVolume_pos U.card r
  have hlogR : Real.log (hammingBallVolume U.card r : ℝ) ≤
      Real.log 2 * binaryEntropy t * U.card := by
    have hh := (div_le_iff₀ realLogTwo_pos).mp hlog
    nlinarith
  change (hammingBallVolume U.card r : ℝ) ≤ _
  calc
    _ = Real.exp (Real.log (hammingBallVolume U.card r : ℝ)) := (Real.exp_log hvol).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlogR

variable {k : ℕ} {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}
  {p : SubcriticalProfile D eta R₀ theta}

/-- The three pieces used by the row code cover the vertex set, even when
roots lie in both the visible and small sides. -/
theorem subcriticalLeftover_row_cover
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta) :
    (D.visibleVertices theta \ p.roots) ∪
      (D.nonretainedSmallVertices eta R₀ theta \ p.roots) ∪ p.roots = Finset.univ := by
  have hc := D.visibleVertices_union_nonretainedSmall hret
  ext v
  have hv : v ∈ D.visibleVertices theta ∪ D.nonretainedSmallVertices eta R₀ theta := by
    rw [hc]; exact Finset.mem_univ _
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, iff_true] at *
  tauto

/-- A finite row encoding with the entire remainder graph fixed.
The small-side degree bound belongs to that fixed graph, not to an
unspecified graph varying with the leftover pattern. -/
theorem subcriticalProfileLeftover_card_le_rowProduct
    (F : Finset (SimpleGraph V)) (H : SubcriticalRemainderGraph D eta R₀)
    (TB R : SimpleGraph V) (d : ℕ)
    (halpha : 0 ≤ alpha) (halpha_fifth : alpha ≤ 1 / 5)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hB : ∀ a ∈ D.visiblePartIndices theta,
      (p.roots.card : ℝ) ≤ alpha * (D.part a).card)
    (hfree : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hdeg : ∀ v ∈ D.nonretainedSmallVertices eta R₀ theta,
      degreeInFinset (subcriticalRemainderGraphSpanningCoe H) v
        (D.nonretainedSmallVertices eta R₀ theta) ≤ d) :
    (subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R).card ≤
      ((finsetSubsetsAtMost (Finset.univ : Finset V)
          ⌊5 * alpha * Fintype.card V⌋₊).card *
        ((Fintype.card V + 1) ^ (k - 1) * 2 ^ ((k - 1) * (d + 1))) *
        2 ^ p.roots.card) ^ p.roots.card := by
  let U := D.visibleVertices theta \ p.roots
  let S := D.nonretainedSmallVertices eta R₀ theta \ p.roots
  let AV := finsetSubsetsAtMost (Finset.univ : Finset V)
    ⌊5 * alpha * Fintype.card V⌋₊
  let AS := DenseGraph.boundedIndependenceSubsetFinset
    (subcriticalRemainderGraphSpanningCoe H) S (k - 1)
  let FL := subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R
  have hc : FL.card ≤ (AV.card * AS.card * 2 ^ p.roots.card) ^ p.roots.card := by
    apply subcritical_card_graphFamily_le_rowProduct FL U S p.roots AV AS
      (subcriticalLeftover_row_cover hret)
    · intro L hL x y hxy
      have hLit := subcriticalLeftoverDefectPatternFinsetWithRemainder_subset
        F alpha p H TB R hL
      exact (mem_subcriticalLeftoverDefectPatternFinset F alpha p TB R L).mp hLit
        |>.leftover_incident_roots hxy
    · intro L hL v hv
      obtain ⟨G, hG, _, _, _, hGL⟩ :=
        (mem_subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R L).mp hL
      apply mem_finsetSubsetsAtMost.mpr
      refine ⟨Finset.subset_univ _, ?_⟩
      apply Nat.le_floor
      rw [← hGL]
      exact subcriticalActualLeftover_visible_degree_le
        (mem_subcriticalProfileClassGraphFinset.mp hG).2 hv halpha halpha_fifth hB
    · intro L hL v hv
      obtain ⟨G, hG, hH, _, _, hGL⟩ :=
        (mem_subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R L).mp hL
      apply (DenseGraph.mem_boundedIndependenceSubsetFinset _ _ _ _).mpr
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro I hI hInd
      rw [← hGL] at hI
      exact subcriticalActualLeftover_small_independence
        (mem_subcriticalProfileClassGraphFinset.mp hG).2 (hfree G hG) hH hv I hI hInd
  have hAS : AS.card ≤ (Fintype.card V + 1) ^ (k - 1) *
      2 ^ ((k - 1) * (d + 1)) := by
    apply (DenseGraph.card_boundedIndependenceSubsetFinset_le
      (subcriticalRemainderGraphSpanningCoe H) S (k - 1) d ?_).trans
    · exact Nat.mul_le_mul_right _
        (Nat.pow_le_pow_left (Nat.add_le_add_right (Finset.card_le_univ S) 1) _)
    · intro v hv
      apply (Finset.card_le_card (Finset.filter_subset_filter _
        (show S ⊆ D.nonretainedSmallVertices eta R₀ theta from Finset.sdiff_subset))).trans
      exact hdeg v (Finset.mem_sdiff.mp hv).1
  exact hc.trans (Nat.pow_le_pow_left
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hAS)) _)

end InducedStars
