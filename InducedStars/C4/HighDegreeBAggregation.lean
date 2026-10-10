import InducedStars.C4.HighDegreeB
import InducedStars.C4.FrozenCrossBounds
import InducedStars.C4.CountingFamilies
import InducedStars.C4.DefectEnumeration

/-!
# Aggregation of the high clique-side defect-degree penalty

Paper: Lemma `lemma:FPi2`. The union is over actual small defect graphs,
actual clique-side vertices, and actual independent-side frozen neighbor
sets. All reference factors are guarded cardinalities of split fibers.
-/

noncomputable section
open Finset Set Filter
open scoped Classical Topology
namespace InducedStars

abbrev C4HighBIndex {n : ℕ} (D : C4Division (Fin n)) :=
  ↥D.cliquePart × ↥D.independentPart.powerset

namespace C4HighBIndex
variable {n : ℕ} {D : C4Division (Fin n)}

def neighbors (i : C4HighBIndex D) (T : SimpleGraph (Fin n)) : Finset (Fin n) :=
  D.cliquePart.filter (T.Adj i.1.val)

def frozen (i : C4HighBIndex D) : C4FrozenCrossData D :=
  c4FrozenCrossStar D i.1.val i.2.val
    (c4HighB_star_cross i.1.prop (Finset.mem_powerset.mp i.2.prop)) true

theorem neighbors_card (i : C4HighBIndex D) (T : SimpleGraph (Fin n))
    (hT : C4DefectSupported D T) : (i.neighbors T).card = T.degree i.1.val := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext x
  simp only [neighbors, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  constructor
  · exact And.right
  · intro hx
    refine ⟨?_,hx⟩
    rcases hT _ _ hx with h | h
    · exact False.elim (Finset.disjoint_left.mp D.disjoint h.1 i.1.prop)
    · exact h.2

end C4HighBIndex

def c4HighBIndices {n : ℕ} (D : C4Division (Fin n)) (T : SimpleGraph (Fin n)) (nu : ℝ) :
    Finset (C4HighBIndex D) :=
  univ.filter fun i => nu*n ≤ ((i.neighbors T).card : ℝ) ∧ nu*n ≤ (i.2.val.card : ℝ)

theorem card_c4HighBIndices_le {n : ℕ} (D : C4Division (Fin n))
    (T : SimpleGraph (Fin n)) (nu : ℝ) : (c4HighBIndices D T nu).card ≤ n*2^n := by
  have hparts := D.card_add
  simp only [Fintype.card_fin] at hparts
  calc
    _ ≤ Fintype.card (C4HighBIndex D) := Finset.card_le_univ _
    _ = D.cliquePart.card*2^D.independentPart.card := by
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, Finset.card_powerset]
    _ ≤ n*2^n := by
      gcongr <;> omega

/-- Optimality provides an actual forced-neighbor set. Taking the entire
cross-neighborhood is harmless: its size is at most `n` and at least the
clique-side defect degree. -/
theorem c4HighClique_member_frozenUnion {n m : ℕ} {gamma epsilon zeta alpha beta : ℝ}
    {D : C4Division (Fin n)} (halpha : 0 ≤ alpha)
    (hB : beta*n ≤ (D.cliquePart.card : ℝ))
    {G : SimpleGraph (Fin n)}
    (hG : G ∈ c4HighCliqueGraphFinset n m gamma epsilon zeta alpha D) :
    ∃ T ∈ c4SmallDefectGraphFinset n epsilon,
      ∃ i ∈ c4HighBIndices D T (alpha*beta), G ∈ i.frozen.freeFiber T m := by
  obtain ⟨hclose,v,hv,hdegree⟩ := mem_c4HighCliqueGraphFinset.mp hG
  let T := c4DefectGraph G D
  let Z := D.independentPart.filter (G.Adj v)
  have hZ : Z ⊆ D.independentPart := Finset.filter_subset _ _
  let i : C4HighBIndex D := ⟨⟨v,hv⟩,⟨Z,Finset.mem_powerset.mpr hZ⟩⟩
  have hNcard : (i.neighbors T).card = T.degree v := i.neighbors_card T (c4DefectGraph_supported G D)
  have hmul : alpha*beta*n ≤ alpha*D.cliquePart.card := by
    nlinarith only [mul_le_mul_of_nonneg_left hB halpha]
  have hlarge : alpha*beta*n ≤ (T.degree v : ℝ) := hmul.trans hdegree
  have hZcard : T.degree v ≤ Z.card := by
    have hh := c4Relocation_of_mem_clique G D (c4CloseDivision_minimal hclose) hv
    rw [← c4DefectGraph_degree_eq_clique G D hv] at hh
    exact hh
  have hi : i ∈ c4HighBIndices D T (alpha*beta) := by
    simp only [c4HighBIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · simpa only [hNcard] using hlarge
    · exact hlarge.trans (by exact_mod_cast hZcard)
  have hcost := (mem_c4CloseDivisionGraphFinset.mp hclose).2.2.1
  have hTsmall : T ∈ c4SmallDefectGraphFinset n epsilon := by
    exact Finset.mem_filter.mpr ⟨mem_univ _,Nat.le_floor hcost⟩
  refine ⟨T,hTsmall,i,hi,?_⟩
  apply (i.frozen.mem_freeFiber T m G).mpr
  refine ⟨mem_c4FixedDefectFreeFiber.mp (c4CloseDivision_mem_fixedDefectFiber hclose),?_⟩
  change c4CrossEdges G D ∩ c4CrossStar v Z = c4CrossStar v Z
  apply Finset.inter_eq_right.mpr
  intro e he
  obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp he
  have hz' := Finset.mem_filter.mp hz
  rw [c4CrossEdges, Finset.mem_inter]
  exact ⟨(mk_mem_finiteGraphEdges G v z).mpr hz'.2,
    (mk_mem_c4CrossPotentialEdges D v z).mpr (Or.inr ⟨hz'.1,hv⟩)⟩

/-- Finite summation with every source counting overhead explicit. -/
theorem c4HighClique_card_le_of_frozen_bound {n m : ℕ} {gamma epsilon zeta alpha beta E : ℝ}
    (D : C4Division (Fin n)) (halpha : 0 ≤ alpha) (hB : beta*n ≤ (D.cliquePart.card : ℝ))
    (hE : 0 ≤ E)
    (hfiber : ∀ T ∈ c4SmallDefectGraphFinset n epsilon,
      ∀ i ∈ c4HighBIndices D T (alpha*beta), ((i.frozen.freeFiber T m).card : ℝ) ≤ E) :
    ((c4HighCliqueGraphFinset n m gamma epsilon zeta alpha D).card : ℝ) ≤
      (hammingBallVolume (completeEdgeCount n) ⌊epsilon*(n : ℝ)^2⌋₊ : ℝ)*
        ((n : ℝ)*(2 : ℝ)^n)*E := by
  have hsub : c4HighCliqueGraphFinset n m gamma epsilon zeta alpha D ⊆
      (c4SmallDefectGraphFinset n epsilon).biUnion fun T =>
        (c4HighBIndices D T (alpha*beta)).biUnion fun i => i.frozen.freeFiber T m := by
    intro G hG
    obtain ⟨T,hT,i,hi,hGi⟩ := c4HighClique_member_frozenUnion halpha hB hG
    exact Finset.mem_biUnion.mpr ⟨T,hT,Finset.mem_biUnion.mpr ⟨i,hi,hGi⟩⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hsum : ((c4HighCliqueGraphFinset n m gamma epsilon zeta alpha D).card : ℝ) ≤
      ∑ T ∈ c4SmallDefectGraphFinset n epsilon,
        ∑ i ∈ c4HighBIndices D T (alpha*beta), ((i.frozen.freeFiber T m).card : ℝ) := by
    have hNat := hcard.trans (Finset.sum_le_sum fun T hT => Finset.card_biUnion_le)
    exact_mod_cast hNat
  refine hsum.trans ?_
  calc
    _ ≤ ∑ T ∈ c4SmallDefectGraphFinset n epsilon,
        ∑ _i ∈ c4HighBIndices D T (alpha*beta), E :=
      Finset.sum_le_sum fun T hT => Finset.sum_le_sum fun i hi => hfiber T hT i hi
    _ ≤ ∑ _T ∈ c4SmallDefectGraphFinset n epsilon, ((n : ℝ)*(2 : ℝ)^n)*E := by
      apply Finset.sum_le_sum
      intro T hT
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_c4HighBIndices_le D T (alpha*beta)) hE
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (show ((c4SmallDefectGraphFinset n epsilon).card : ℝ) ≤
          (hammingBallVolume (completeEdgeCount n) ⌊epsilon*(n : ℝ)^2⌋₊ : ℝ) by
            exact_mod_cast card_c4SmallDefectGraphFinset_le n epsilon)
        (show 0 ≤ ((n : ℝ)*(2 : ℝ)^n)*E by positivity)

/-- A uniform finite high-B count before absorbing the defect, vertex-set,
and conditioning costs. All inputs are elementary sampling-band and size
bounds, not probability or count conclusions. -/
theorem c4HighClique_card_le_explicit {n m : ℕ} {gamma epsilon zeta alpha beta : ℝ}
    (D : C4Division (Fin n)) (hepsilon : 0 ≤ epsilon) (halpha : 0 < alpha)
    (hbeta : 0 < beta) (hbetaHalf : beta < 1/2) (hn : 4 ≤ alpha*beta*n)
    (hB : beta*n ≤ (D.cliquePart.card : ℝ)) (hsmall : epsilon ≤ (alpha*beta)^2/8)
    (hsampling : ∀ t : ℤ, |(t : ℝ)| ≤ epsilon*(n : ℝ)^2+n →
      ∀ z : ℕ, z ≤ n → C4NondegenerateSamplingBounds n m D.cliquePart.card z t beta) :
    let C := DenseGraph.binomialCompactBandShiftConstant beta
    ((c4HighCliqueGraphFinset n m gamma epsilon zeta alpha D).card : ℝ) ≤
      (hammingBallVolume (completeEdgeCount n) ⌊epsilon*(n : ℝ)^2⌋₊ : ℝ)*
        ((n : ℝ)*(2 : ℝ)^n)*
        (((c4SplitFiber D m).card : ℝ)*((n : ℝ)^2+1)*
          Real.exp (C*(epsilon*(n : ℝ)^2+n)-beta^5*alpha^3/16*(n : ℝ)^2)) := by
  let C := DenseGraph.binomialCompactBandShiftConstant beta
  have hC : 0 < C := DenseGraph.binomialCompactBandShiftConstant_pos hbeta hbetaHalf
  apply c4HighClique_card_le_of_frozen_bound D halpha.le hB (by positivity)
  intro T hT i hi
  have hTsmall : ((finiteGraphEdges T).card : ℝ) ≤ epsilon*(n : ℝ)^2 := by
    exact (Nat.cast_le.mpr (Finset.mem_filter.mp hT).2).trans (Nat.floor_le (by positivity))
  have hshift : |(c4MatchingSignedShift D T : ℝ)| ≤ epsilon*(n : ℝ)^2+n :=
    (c4MatchingSignedShift_abs_le D T).trans (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hZ : i.2.val ⊆ D.independentPart := Finset.mem_powerset.mp i.2.prop
  have hzn : i.2.val.card ≤ n := by simpa using Finset.card_le_univ i.2.val
  have hs := hsampling (c4MatchingSignedShift D T) hshift i.2.val.card hzn
  have hpresent : i.frozen.present.card = i.2.val.card := by simp [C4HighBIndex.frozen]
  obtain ⟨hm,hq,hband,hband'⟩ := c4Frozen_quotaBand_of_samplingBounds i.frozen T
    (by simp [C4HighBIndex.frozen]) (Or.inr hpresent) hs
  have hbase := hsampling 0 (by simp; positivity) 0 (Nat.zero_le n)
  have hchoose := c4Frozen_choose_le_splitFiber i.frozen T hbeta hbetaHalf hm hq hbase
  have hsize := (Finset.mem_filter.mp hi).2
  have hprob := c4HighB_starFiber_le D T i.1.val i.1.prop (i.neighbors T) i.2.val
    (Finset.filter_subset _ _) (fun x hx => (Finset.mem_filter.mp hx).2) hZ m
    (mul_pos halpha hbeta) hbeta.le hn hsize.1 hsize.2
    (hTsmall.trans (by nlinarith only [mul_le_mul_of_nonneg_right hsmall (sq_nonneg (n : ℝ))]))
    hq hband
  have hcap : (i.frozen.optional.card : ℝ)+1 ≤ (n : ℝ)^2+1 := by
    have hnat := (Finset.card_le_card i.frozen.optional_subset).trans (c4CrossPotentialEdges_card_le_sq D)
    have hh : (i.frozen.optional.card : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast hnat
    linarith only [hh]
  have hshiftBound : C*((finiteGraphEdges T).card+i.frozen.present.card) ≤
      C*(epsilon*(n : ℝ)^2+n) := by
    rw [hpresent]
    have hzR : (i.2.val.card : ℝ) ≤ n := by exact_mod_cast hzn
    apply mul_le_mul_of_nonneg_left _ hC.le
    linarith only [hTsmall,hzR]
  calc
    _ ≤ _ := hprob
    _ ≤ (((c4SplitFiber D m).card : ℝ)*
        Real.exp (C*((finiteGraphEdges T).card+i.frozen.present.card)))*
        ((n : ℝ)^2+1)*Real.exp (-(beta^2*(alpha*beta)^3/16)*(n : ℝ)^2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hchoose hcap (by positivity) (by positivity)) (Real.exp_pos _).le
    _ = ((c4SplitFiber D m).card : ℝ)*((n : ℝ)^2+1)*
        Real.exp (C*((finiteGraphEdges T).card+i.frozen.present.card)-
          beta^5*alpha^3/16*(n : ℝ)^2) := by
      rw [mul_right_comm _ (Real.exp _) _, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hshiftBound]))
      (by positivity)

/-- Paper: Lemma `lemma:FPi2`. The positive rate and nondegeneracy window
depend only on `gamma`. The defect tolerance is selected afterwards, for
the chosen positive high-degree threshold. The conclusion is uniform in
every smaller positive defect tolerance and nondegeneracy window. -/
theorem inducedC4HighCliquePenalty {gamma : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1) :
    ∃ zetaMax c : ℝ, 0 < zetaMax ∧ 0 < c ∧
      ∀ alpha : ℝ, 0 < alpha → ∃ epsilonMax : ℝ, 0 < epsilonMax ∧
        ∀ epsilon zeta : ℝ, 0 < epsilon → epsilon ≤ epsilonMax → zeta ≤ zetaMax →
          ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
            ∀ᶠ n in atTop, ∀ D : C4Division (Fin n),
              ((c4HighCliqueGraphFinset n (m n) gamma epsilon zeta alpha D).card : ℝ) ≤
                ((c4SplitFiber D (m n)).card : ℝ)*Real.exp (-c*alpha^3*(n : ℝ)^2) := by
  obtain ⟨zetaMax,hzetaMax,epsBand,hepsBand,beta,hbeta,hbetaHalf,hsampling⟩ :=
    exists_c4NondegenerateSamplingBand hgamma
  let C := DenseGraph.binomialCompactBandShiftConstant beta
  have hC : 0 < C := DenseGraph.binomialCompactBandShiftConstant_pos hbeta hbetaHalf
  refine ⟨zetaMax,beta^5/64,hzetaMax,by positivity,?_⟩
  intro alpha halpha
  let q : ℝ := beta^5*alpha^3/16
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨e0,he0,hecontrol⟩ := exists_epsilon0_supercriticalDefectPatternRate_lt (show 0 < q/4 by positivity)
  let epsilonMax := min epsBand (min ((alpha*beta)^2/8) (min (q/(4*(C+1))) (e0/2)))
  have hepsilonMax : 0 < epsilonMax := by dsimp [epsilonMax]; positivity
  refine ⟨epsilonMax,hepsilonMax,?_⟩
  intro epsilon zeta hepsilon hepsMax hzeta m hm
  have hepsBand' : epsilon ≤ epsBand := hepsMax.trans (min_le_left _ _)
  have hepsSmall : epsilon ≤ (alpha*beta)^2/8 := hepsMax.trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hepsCost : epsilon ≤ q/(4*(C+1)) := hepsMax.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hepsE0 : epsilon < e0 := (hepsMax.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))).trans_lt (by linarith)
  obtain ⟨hepsHalf,hepsRate⟩ := hecontrol hepsilon hepsE0
  have hCe : C*epsilon ≤ q/4 := by
    have hh := (le_div_iff₀ (show 0 < 4*(C+1) by positivity)).mp hepsCost
    nlinarith only [hh,hepsilon,hC]
  have hlarge : ∀ᶠ n : ℕ in atTop, 4/(alpha*beta) ≤ (n : ℝ) ∧
      (C+Real.log 2+3)/(q/4) ≤ (n : ℝ) := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (4/(alpha*beta)),
      tendsto_natCast_atTop_atTop.eventually_ge_atTop ((C+Real.log 2+3)/(q/4))] with n h1 h2
    exact ⟨h1,h2⟩
  filter_upwards [hsampling m hm, eventually_hammingBallVolume_floor_square_le_exp hepsilon hepsHalf,
    hlarge] with n hn hball hlarge
  intro D
  by_cases hnonempty : (c4HighCliqueGraphFinset n (m n) gamma epsilon zeta alpha D).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty, Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨G,hG⟩ := hnonempty
  have hclose := (mem_c4HighCliqueGraphFinset.mp hG).1
  have hnear := (mem_c4CloseDivisionGraphFinset.mp hclose).2.2.2
  have hnear' : |(D.cliquePart.card : ℝ)/n-c4Lambda gamma| ≤ zetaMax :=
    ((c4_nondegenerate_ratio_iff hn.1 D gamma zeta).mpr hnear).trans hzeta
  have hbn : D.cliquePart.card ≤ n := by simpa using Finset.card_le_univ D.cliquePart
  have hsample : ∀ t : ℤ, |(t : ℝ)| ≤ epsilon*(n : ℝ)^2+n →
      ∀ z : ℕ, z ≤ n → C4NondegenerateSamplingBounds n (m n) D.cliquePart.card z t beta := by
    intro t ht z hz
    apply hn.2 D.cliquePart.card hbn hnear' t _ z hz
    exact ht.trans (by nlinarith only [mul_le_mul_of_nonneg_right hepsBand' (sq_nonneg (n : ℝ))])
  have hbase := hsample 0 (by simp; positivity) 0 (Nat.zero_le n)
  have hdegree : 4 ≤ alpha*beta*n := by
    simpa only [mul_comm] using (div_le_iff₀ (mul_pos halpha hbeta)).mp hlarge.1
  have hfinite := c4HighClique_card_le_explicit (gamma := gamma) (zeta := zeta)
    D hepsilon.le halpha hbeta hbetaHalf hdegree
    hbase.clique_size.le hepsSmall hsample
  have hlinear : (C+Real.log 2+3)*n ≤ q/4*(n : ℝ)^2 := by
    have hh := (div_le_iff₀ (show 0 < q/4 by positivity)).mp hlarge.2
    have hh' := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) n)
    nlinarith only [hh']
  have hfinalExp : supercriticalDefectPatternRate epsilon*(n : ℝ)^2 +
      (C+Real.log 2+3)*n + C*epsilon*(n : ℝ)^2-q*(n : ℝ)^2 ≤
        -(beta^5/64)*alpha^3*(n : ℝ)^2 := by
    have h1 := mul_le_mul_of_nonneg_right hepsRate.le (sq_nonneg (n : ℝ))
    have h2 := mul_le_mul_of_nonneg_right hCe (sq_nonneg (n : ℝ))
    dsimp [q] at *
    nlinarith only [h1,h2,hlinear]
  calc
    _ ≤ _ := hfinite
    _ = ((c4SplitFiber D (m n)).card : ℝ)*
        (hammingBallVolume (completeEdgeCount n) ⌊epsilon*(n : ℝ)^2⌋₊ : ℝ)*
        (((n : ℝ)*(2 : ℝ)^n)*((n : ℝ)^2+1)*Real.exp (C*n))*
        Real.exp (C*epsilon*(n : ℝ)^2-q*(n : ℝ)^2) := by
      rw [← mul_assoc, ← mul_assoc]
      have hexp : C*(epsilon*(n : ℝ)^2+n)-beta^5*alpha^3/16*(n : ℝ)^2 =
          C*n+(C*epsilon*(n : ℝ)^2-q*(n : ℝ)^2) := by dsimp [q]; ring
      rw [hexp, Real.exp_add]
      ring
    _ ≤ ((c4SplitFiber D (m n)).card : ℝ)*
        Real.exp (supercriticalDefectPatternRate epsilon*(n : ℝ)^2)*
        Real.exp ((C+Real.log 2+3)*n)*
        Real.exp (C*epsilon*(n : ℝ)^2-q*(n : ℝ)^2) := by
      gcongr
      exact c4DefectEnumeration_linearOverhead_le n C
    _ = ((c4SplitFiber D (m n)).card : ℝ)*
        Real.exp (supercriticalDefectPatternRate epsilon*(n : ℝ)^2+
          (C+Real.log 2+3)*n+C*epsilon*(n : ℝ)^2-q*(n : ℝ)^2) := by
      rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hfinalExp) (by positivity)

theorem c4HighCliqueGraphFinset_mono {n m : ℕ} {gamma epsilon epsilon' zeta zeta' alpha : ℝ}
    (D : C4Division (Fin n)) (he : epsilon ≤ epsilon') (hz : zeta ≤ zeta') :
    c4HighCliqueGraphFinset n m gamma epsilon zeta alpha D ⊆
      c4HighCliqueGraphFinset n m gamma epsilon' zeta' alpha D := by
  intro G hG
  obtain ⟨hclose,hhigh⟩ := mem_c4HighCliqueGraphFinset.mp hG
  obtain ⟨hfree,hcanonical,hcost,hnear⟩ := mem_c4CloseDivisionGraphFinset.mp hclose
  exact mem_c4HighCliqueGraphFinset.mpr
    ⟨mem_c4CloseDivisionGraphFinset.mpr ⟨hfree,hcanonical,
      hcost.trans (mul_le_mul_of_nonneg_right he (sq_nonneg (n : ℝ))),
      hnear.trans (mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg n))⟩,hhigh⟩

/-- Paper: Lemma `lemma:FPi2`, uniformly over all smaller tolerances after
one threshold. This is the synchronization form for the final C4 theorem. -/
theorem inducedC4HighCliquePenalty_uniform {gamma : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1) :
    ∃ zetaMax c : ℝ, 0 < zetaMax ∧ 0 < c ∧
      ∀ alpha : ℝ, 0 < alpha → ∃ epsilonMax : ℝ, 0 < epsilonMax ∧
        ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
          ∀ᶠ n in atTop, ∀ D : C4Division (Fin n), ∀ epsilon zeta : ℝ,
            epsilon ≤ epsilonMax → zeta ≤ zetaMax →
              ((c4HighCliqueGraphFinset n (m n) gamma epsilon zeta alpha D).card : ℝ) ≤
                ((c4SplitFiber D (m n)).card : ℝ)*Real.exp (-c*alpha^3*(n : ℝ)^2) := by
  obtain ⟨zetaMax,c,hz,hc,hbound⟩ := inducedC4HighCliquePenalty hgamma
  refine ⟨zetaMax,c,hz,hc,?_⟩
  intro alpha ha
  obtain ⟨epsilonMax,he,hbound⟩ := hbound alpha ha
  refine ⟨epsilonMax,he,?_⟩
  intro m hm
  filter_upwards [hbound epsilonMax zetaMax he le_rfl le_rfl m hm] with n hn
  intro D epsilon zeta heps hzeta
  have hcard := Finset.card_le_card (c4HighCliqueGraphFinset_mono
    (m := m n) (gamma := gamma) (alpha := alpha) D heps hzeta)
  exact (show ((c4HighCliqueGraphFinset n (m n) gamma epsilon zeta alpha D).card : ℝ) ≤
    ((c4HighCliqueGraphFinset n (m n) gamma epsilonMax zetaMax alpha D).card : ℝ) by
      exact_mod_cast hcard).trans (hn D)

end InducedStars
