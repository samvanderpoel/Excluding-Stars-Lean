import InducedStars.C4.HighDegreeAFromSets
import InducedStars.C4.FrozenCrossBounds
import InducedStars.C4.DefectEnumeration

/-!
# Actual-family summation for high independent-side defect degree

Paper: Lemma `lemma:FPi1`. The dense-neighborhood branch is bounded by
the matching fiber; the other branch uses the actual frozen-star fiber.
The complete finite overhead is retained before exponential absorption.
-/

noncomputable section
open Finset
open scoped Classical
namespace InducedStars

abbrev C4HighAIndex {n : ℕ} (D : C4Division (Fin n)) :=
  ↥D.independentPart × ↥D.cliquePart.powerset

namespace C4HighAIndex
variable {n : ℕ} {D : C4Division (Fin n)}

def neighbors (i : C4HighAIndex D) (T : SimpleGraph (Fin n)) : Finset (Fin n) :=
  D.independentPart.filter (T.Adj i.1.val)

def frozen (i : C4HighAIndex D) : C4FrozenCrossData D :=
  c4FrozenCrossStar D i.1.val i.2.val
    (c4HighA_star_cross i.1.prop (Finset.mem_powerset.mp i.2.prop)) false

def Dense (i : C4HighAIndex D) (T : SimpleGraph (Fin n)) : Prop :=
  ((i.neighbors T).card : ℝ) ^ 2 / 4 ≤
    (finiteGraphEdges (T.induce (i.neighbors T : Set (Fin n)))).card

def fiber (i : C4HighAIndex D) (T : SimpleGraph (Fin n)) (m : ℕ) :
    Finset (SimpleGraph (Fin n)) :=
  if i.Dense T then c4FixedDefectFreeFiber D T m else i.frozen.freeFiber T m

theorem neighbors_card (i : C4HighAIndex D) (T : SimpleGraph (Fin n))
    (hT : C4DefectSupported D T) : (i.neighbors T).card = T.degree i.1.val := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext x
  simp only [neighbors, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  constructor
  · exact And.right
  · intro hx
    refine ⟨?_, hx⟩
    rcases hT _ _ hx with h | h
    · exact h.2
    · exact False.elim (Finset.disjoint_left.mp D.disjoint i.1.prop h.1)

theorem matchingNumber_ge_of_dense (i : C4HighAIndex D) (T : SimpleGraph (Fin n))
    (hN : 0 < (i.neighbors T).card) (hdense : i.Dense T) :
    ((i.neighbors T).card : ℝ) / 8 ≤
      DenseGraph.matchingNumber (c4WithinGraph T D.independentPart) := by
  have h := c4Within_matchingNumber_ge_of_dense T (i.neighbors T) hN hdense
  exact h.trans (Nat.cast_le.mpr (c4MatchingNumber_mono (by
    intro x y hxy
    exact ⟨(Finset.mem_filter.mp hxy.1).1, (Finset.mem_filter.mp hxy.2.1).1, hxy.2.2⟩)))

end C4HighAIndex

def c4HighAIndices {n : ℕ} (D : C4Division (Fin n)) (T : SimpleGraph (Fin n)) (nu : ℝ) :
    Finset (C4HighAIndex D) :=
  univ.filter fun i ↦ nu * n ≤ ((i.neighbors T).card : ℝ) ∧ nu * n ≤ (i.2.val.card : ℝ)

theorem card_c4HighAIndices_le {n : ℕ} (D : C4Division (Fin n))
    (T : SimpleGraph (Fin n)) (nu : ℝ) : (c4HighAIndices D T nu).card ≤ n * 2 ^ n := by
  have hparts := D.card_add
  simp only [Fintype.card_fin] at hparts
  calc
    _ ≤ Fintype.card (C4HighAIndex D) := Finset.card_le_univ _
    _ = D.independentPart.card * 2 ^ D.cliquePart.card := by
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, Finset.card_powerset]
    _ ≤ n * 2 ^ n := by gcongr <;> omega

theorem c4HighIndependent_member_fiberUnion {n m : ℕ} {gamma epsilon zeta alpha beta : ℝ}
    {D : C4Division (Fin n)} (halpha : 0 ≤ alpha)
    (hA : beta * n ≤ (D.independentPart.card : ℝ)) {G : SimpleGraph (Fin n)}
    (hG : G ∈ c4HighIndependentGraphFinset n m gamma epsilon zeta alpha D) :
    ∃ T ∈ c4SmallDefectGraphFinset n epsilon,
      ∃ i ∈ c4HighAIndices D T (alpha * beta), G ∈ i.fiber T m := by
  obtain ⟨hclose, v, hv, hdegree⟩ := mem_c4HighIndependentGraphFinset.mp hG
  let T := c4DefectGraph G D
  let Z := D.cliquePart.filter fun z ↦ z ≠ v ∧ ¬G.Adj v z
  have hZ : Z ⊆ D.cliquePart := Finset.filter_subset _ _
  let i : C4HighAIndex D := ⟨⟨v, hv⟩, ⟨Z, Finset.mem_powerset.mpr hZ⟩⟩
  have hNcard : (i.neighbors T).card = T.degree v := i.neighbors_card T (c4DefectGraph_supported G D)
  have hlarge : alpha * beta * n ≤ (T.degree v : ℝ) := by
    have hfirst : alpha * beta * n ≤ alpha * D.independentPart.card := by
      nlinarith only [mul_le_mul_of_nonneg_left hA halpha]
    exact hfirst.trans hdegree
  have hZcard : T.degree v ≤ Z.card := by
    have h := c4Relocation_of_mem_independent G D (c4CloseDivision_minimal hclose) hv
    rw [← c4DefectGraph_degree_eq_independent G D hv] at h
    exact h
  have hi : i ∈ c4HighAIndices D T (alpha * beta) := by
    simp only [c4HighAIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · simpa only [hNcard] using hlarge
    · exact hlarge.trans (by exact_mod_cast hZcard)
  have hcost := (mem_c4CloseDivisionGraphFinset.mp hclose).2.2.1
  refine ⟨T, Finset.mem_filter.mpr ⟨mem_univ _, Nat.le_floor hcost⟩, i, hi, ?_⟩
  by_cases hdense : i.Dense T
  · rw [C4HighAIndex.fiber, if_pos hdense]
    exact c4CloseDivision_mem_fixedDefectFiber hclose
  · rw [C4HighAIndex.fiber, if_neg hdense]
    apply (i.frozen.mem_freeFiber T m G).mpr
    refine ⟨mem_c4FixedDefectFreeFiber.mp (c4CloseDivision_mem_fixedDefectFiber hclose), ?_⟩
    change c4CrossEdges G D ∩ c4CrossStar v Z = ∅
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hcross := (Finset.mem_inter.mp he).1
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp (Finset.mem_inter.mp he).2
    have hno : ¬G.Adj v z := (Finset.mem_filter.mp hz).2.2
    exact hno ((mk_mem_finiteGraphEdges G v z).mp (Finset.mem_inter.mp hcross).1)

/-- The finite union bound includes all defect choices and the exact
`n*2^n` vertex/subset overhead. -/
theorem c4HighIndependent_card_le_of_fiber_bound {n m : ℕ}
    {gamma epsilon zeta alpha beta E : ℝ} (D : C4Division (Fin n))
    (halpha : 0 ≤ alpha) (hA : beta * n ≤ (D.independentPart.card : ℝ)) (hE : 0 ≤ E)
    (hfiber : ∀ T ∈ c4SmallDefectGraphFinset n epsilon,
      ∀ i ∈ c4HighAIndices D T (alpha * beta), ((i.fiber T m).card : ℝ) ≤ E) :
    ((c4HighIndependentGraphFinset n m gamma epsilon zeta alpha D).card : ℝ) ≤
      (hammingBallVolume (completeEdgeCount n) ⌊epsilon * (n : ℝ) ^ 2⌋₊ : ℝ) *
        ((n : ℝ) * (2 : ℝ) ^ n) * E := by
  have hsub : c4HighIndependentGraphFinset n m gamma epsilon zeta alpha D ⊆
      (c4SmallDefectGraphFinset n epsilon).biUnion fun T ↦
        (c4HighAIndices D T (alpha * beta)).biUnion fun i ↦ i.fiber T m := by
    intro G hG
    obtain ⟨T, hT, i, hi, hGi⟩ := c4HighIndependent_member_fiberUnion halpha hA hG
    exact Finset.mem_biUnion.mpr ⟨T, hT, Finset.mem_biUnion.mpr ⟨i, hi, hGi⟩⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hsum : ((c4HighIndependentGraphFinset n m gamma epsilon zeta alpha D).card : ℝ) ≤
      ∑ T ∈ c4SmallDefectGraphFinset n epsilon,
        ∑ i ∈ c4HighAIndices D T (alpha * beta), ((i.fiber T m).card : ℝ) := by
    have hNat := hcard.trans (Finset.sum_le_sum fun T hT ↦ Finset.card_biUnion_le)
    exact_mod_cast hNat
  refine hsum.trans ?_
  calc
    _ ≤ ∑ T ∈ c4SmallDefectGraphFinset n epsilon,
        ∑ _i ∈ c4HighAIndices D T (alpha * beta), E :=
      Finset.sum_le_sum fun T hT ↦ Finset.sum_le_sum fun i hi ↦ hfiber T hT i hi
    _ ≤ ∑ _T ∈ c4SmallDefectGraphFinset n epsilon, ((n : ℝ) * (2 : ℝ) ^ n) * E := by
      apply Finset.sum_le_sum
      intro T hT
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_c4HighAIndices_le D T (alpha * beta)) hE
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (show ((c4SmallDefectGraphFinset n epsilon).card : ℝ) ≤
          (hammingBallVolume (completeEdgeCount n) ⌊epsilon * (n : ℝ) ^ 2⌋₊ : ℝ) by
            exact_mod_cast card_c4SmallDefectGraphFinset_le n epsilon)
        (show 0 ≤ (n : ℝ) * (2 : ℝ) ^ n * E by positivity)

/-- Both local cases with their binomial shift and conditioning costs.
The matching estimate is supplied at its already-proved finite interface. -/
theorem c4HighIndependent_card_le_explicit {n m : ℕ}
    {gamma epsilon zeta alpha beta cMat rate : ℝ} (D : C4Division (Fin n))
    (hepsilon : 0 ≤ epsilon) (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hbeta : 0 < beta) (hbetaHalf : beta < 1 / 2) (hcMat : 0 < cMat)
    (hrate : 0 < rate) (hrateMat : rate ≤ cMat * beta / 8)
    (hrateStar : rate ≤ beta ^ 6 / 64) (hn : 8 ≤ alpha * beta * n)
    (hA : beta * n ≤ (D.independentPart.card : ℝ))
    (hsampling : ∀ t : ℤ, |(t : ℝ)| ≤ epsilon * (n : ℝ) ^ 2 + n →
      ∀ z : ℕ, z ≤ n → C4NondegenerateSamplingBounds n m D.cliquePart.card z t beta)
    (hmat : ∀ T ∈ c4SmallDefectGraphFinset n epsilon,
      ∀ q : ℕ, 1 ≤ q → q ≤ DenseGraph.matchingNumber (c4WithinGraph T D.independentPart) →
        ((c4FixedDefectFreeFiber D T m).card : ℝ) ≤
          (Nat.choose (c4CrossPotentialEdges D).card (c4FixedDefectQuota D T m) : ℝ) *
            Real.exp (-cMat * q * n)) :
    let C := DenseGraph.binomialCompactBandShiftConstant beta
    ((c4HighIndependentGraphFinset n m gamma epsilon zeta alpha D).card : ℝ) ≤
      (hammingBallVolume (completeEdgeCount n) ⌊epsilon * (n : ℝ) ^ 2⌋₊ : ℝ) *
        ((n : ℝ) * (2 : ℝ) ^ n) *
        (((c4SplitFiber D m).card : ℝ) * ((n : ℝ) ^ 2 + 1) *
          Real.exp ((C * epsilon - rate * alpha ^ 2) * (n : ℝ) ^ 2)) := by
  let C := DenseGraph.binomialCompactBandShiftConstant beta
  have hC : 0 < C := DenseGraph.binomialCompactBandShiftConstant_pos hbeta hbetaHalf
  apply c4HighIndependent_card_le_of_fiber_bound D halpha.le hA (by positivity)
  intro T hT i hi
  have hsmall := c4SmallDefectGraphFinset_edgeCount_le hepsilon hT
  have hshift : |(c4MatchingSignedShift D T : ℝ)| ≤ epsilon * (n : ℝ) ^ 2 + n :=
    (c4MatchingSignedShift_abs_le D T).trans (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hbase := hsampling 0 (by simp; positivity) 0 (Nat.zero_le n)
  have hsize := (Finset.mem_filter.mp hi).2
  have hNpos : 0 < (i.neighbors T).card := by
    exact_mod_cast (show (0 : ℝ) < (i.neighbors T).card by linarith [hsize.1])
  have hcost : C * (finiteGraphEdges T).card ≤ C * epsilon * (n : ℝ) ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hsmall hC.le]
  by_cases hdense : i.Dense T
  · rw [C4HighAIndex.fiber, if_pos hdense]
    let q := DenseGraph.matchingNumber (c4WithinGraph T D.independentPart)
    have hqlo : alpha * beta * n / 8 ≤ (q : ℝ) :=
      (div_le_div_of_nonneg_right hsize.1 (by norm_num)).trans
        (i.matchingNumber_ge_of_dense T hNpos hdense)
    have hq : 1 ≤ q := by exact_mod_cast (show (1 : ℝ) ≤ q by linarith)
    have hprob := hmat T hT q hq le_rfl
    obtain ⟨hm, hquota, _, _⟩ := c4Matching_quotaBand_of_samplingBounds D T
      (hsampling (c4MatchingSignedShift D T) hshift 0 (Nat.zero_le n))
    let W0 : C4FrozenCrossData D := ⟨∅, ∅, Finset.empty_subset _, Finset.empty_subset _⟩
    have hchoose0 := c4Frozen_choose_le_splitFiber W0 T hbeta hbetaHalf
      (by simpa [W0] using hm)
      (by simpa [W0, C4FrozenCrossData.quota, C4FrozenCrossData.optional, c4FixedDefectQuota] using hquota) hbase
    have hchoose : (Nat.choose (c4CrossPotentialEdges D).card (c4FixedDefectQuota D T m) : ℝ) ≤
        ((c4SplitFiber D m).card : ℝ) * Real.exp (C * (finiteGraphEdges T).card) := by
      simpa [W0, C4FrozenCrossData.quota, C4FrozenCrossData.optional, c4FixedDefectQuota, C] using hchoose0
    have hrateAlpha : rate * alpha ^ 2 ≤ cMat * beta * alpha / 8 := by
      have ha2 : alpha ^ 2 ≤ alpha := by nlinarith
      calc
        _ ≤ (cMat * beta / 8) * alpha ^ 2 := by gcongr
        _ ≤ (cMat * beta / 8) * alpha := by gcongr
        _ = _ := by ring
    have hpenalty : rate * alpha ^ 2 * (n : ℝ) ^ 2 ≤ cMat * q * n := by
      have h1 := mul_le_mul_of_nonneg_right hrateAlpha (sq_nonneg (n : ℝ))
      have h2 := mul_le_mul_of_nonneg_left hqlo (show 0 ≤ cMat * (n : ℝ) by positivity)
      nlinarith only [h1, h2]
    calc
      _ ≤ _ := hprob
      _ ≤ (((c4SplitFiber D m).card : ℝ) * Real.exp (C * (finiteGraphEdges T).card)) *
          Real.exp (-cMat * q * n) := by gcongr
      _ = ((c4SplitFiber D m).card : ℝ) *
          Real.exp (C * (finiteGraphEdges T).card - cMat * q * n) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ ((c4SplitFiber D m).card : ℝ) *
          Real.exp ((C * epsilon - rate * alpha ^ 2) * (n : ℝ) ^ 2) := by
        gcongr
        nlinarith only [hcost, hpenalty]
      _ ≤ _ := by
        have hfac : ((c4SplitFiber D m).card : ℝ) ≤
            ((c4SplitFiber D m).card : ℝ) * ((n : ℝ) ^ 2 + 1) := by
          nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (c4SplitFiber D m).card) (sq_nonneg (n : ℝ))]
        exact mul_le_mul_of_nonneg_right hfac (Real.exp_nonneg _)
  · rw [C4HighAIndex.fiber, if_neg hdense]
    have hZ := Finset.mem_powerset.mp i.2.prop
    have hzn : i.2.val.card ≤ n := by simpa using Finset.card_le_univ i.2.val
    have hs := hsampling (c4MatchingSignedShift D T) hshift i.2.val.card hzn
    obtain ⟨hm, hquota, hband, _⟩ := c4Frozen_quotaBand_of_samplingBounds i.frozen T
      (by simp [C4HighAIndex.frozen]) (Or.inl (by simp [C4HighAIndex.frozen])) hs
    have hchoose := c4Frozen_choose_le_splitFiber i.frozen T hbeta hbetaHalf hm hquota hbase
    have hprob := c4HighA_starFiber_le D T i.1.val i.1.prop (i.neighbors T) i.2.val
      (Finset.filter_subset _ _) (fun x hx ↦ (Finset.mem_filter.mp hx).2) hZ m
      (mul_pos halpha hbeta) hbeta (by linarith) (by linarith) hsize.1 hsize.2
      (le_of_not_ge hdense) hquota hband
    change ((i.frozen.freeFiber T m).card : ℝ) ≤
      (i.frozen.optional.card.choose (i.frozen.quota T m) : ℝ) * (i.frozen.optional.card + 1) *
        Real.exp (-(beta ^ 4 * (alpha * beta) ^ 2 / 64) * (n : ℝ) ^ 2) at hprob
    have hcap : (i.frozen.optional.card : ℝ) + 1 ≤ (n : ℝ) ^ 2 + 1 := by
      have hnat := (Finset.card_le_card i.frozen.optional_subset).trans (c4CrossPotentialEdges_card_le_sq D)
      have hh : (i.frozen.optional.card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hnat
      linarith
    have hpresent : i.frozen.present.card = 0 := by simp [C4HighAIndex.frozen]
    rw [hpresent, Nat.cast_zero, add_zero] at hchoose
    have hpenalty : rate * alpha ^ 2 * (n : ℝ) ^ 2 ≤ beta ^ 4 * (alpha * beta) ^ 2 / 64 * (n : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hrateStar (show 0 ≤ alpha ^ 2 * (n : ℝ) ^ 2 by positivity)
      nlinarith only [h]
    calc
      _ ≤ _ := hprob
      _ ≤ (((c4SplitFiber D m).card : ℝ) * Real.exp (C * (finiteGraphEdges T).card)) *
          ((n : ℝ) ^ 2 + 1) * Real.exp (-(beta ^ 4 * (alpha * beta) ^ 2 / 64) * (n : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hchoose hcap (by positivity) (by positivity)) (Real.exp_nonneg _)
      _ = ((c4SplitFiber D m).card : ℝ) * ((n : ℝ) ^ 2 + 1) *
          Real.exp (C * (finiteGraphEdges T).card - beta ^ 4 * (alpha * beta) ^ 2 / 64 * (n : ℝ) ^ 2) := by
        rw [mul_right_comm _ (Real.exp _) _, mul_assoc, ← Real.exp_add]
        congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith only [hcost, hpenalty]))
        (by positivity)

end InducedStars
