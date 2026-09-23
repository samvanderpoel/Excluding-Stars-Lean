import InducedStars.C4.NondegenerateEntropy
import InducedStars.Structure.Supercritical.MediumParameters

/-!
# Almost every close induced-C4-free graph has a nondegenerate division

Paper: Lemma `lemma:almost-all-nondeg`, using the feasible perturbed-density
comparison.
The closeness tolerance is selected after the prescribed nondegeneracy
tolerance, and before the asymptotic edge-count sequence.
-/

noncomputable section
namespace InducedStars
open Filter Set
open scoped Topology

private theorem c4CloseDegenerate_card_le_of_fiber_bound
    {n m : ℕ} {gamma epsilon zeta E : ℝ}
    (hF : ∀ D ∈ c4DegenerateDivisions n gamma zeta,
      ∀ j ∈ c4SplitRepairEdgeWindow n m ⌊epsilon*(n : ℝ)^2⌋₊,
        ((c4SplitFiber D j).card : ℝ) ≤ Real.exp (E*(n : ℝ)^2)) :
    ((c4CloseDegenerateGraphFinset n m gamma epsilon zeta).card : ℝ) ≤
      (2 : ℝ)^n * (completeEdgeCount n+1) * Real.exp (E*(n : ℝ)^2) *
        (hammingBallVolume (completeEdgeCount n) ⌊epsilon*(n : ℝ)^2⌋₊ : ℝ) := by
  classical
  have hD : ((c4DegenerateDivisions n gamma zeta).card : ℝ) ≤ (2 : ℝ)^n := by
    have h := Finset.card_filter_le (s := Finset.univ)
      (p := fun D : C4Division (Fin n) ↦
        zeta*n < |(D.cliquePart.card : ℝ)-c4Lambda gamma*n|)
    simpa [c4DegenerateDivisions, C4Division] using (show
      ((c4DegenerateDivisions n gamma zeta).card : ℝ) ≤
        (Fintype.card (C4Division (Fin n)) : ℝ) by exact_mod_cast h)
  have hJ : ((c4SplitRepairEdgeWindow n m ⌊epsilon*(n : ℝ)^2⌋₊).card : ℝ) ≤
      completeEdgeCount n+1 := by
    have h : (c4SplitRepairEdgeWindow n m ⌊epsilon*(n : ℝ)^2⌋₊).card ≤
        completeEdgeCount n+1 :=
      (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
    exact_mod_cast h
  have hsum : (∑ D ∈ c4DegenerateDivisions n gamma zeta,
      ∑ j ∈ c4SplitRepairEdgeWindow n m ⌊epsilon*(n : ℝ)^2⌋₊,
        ((c4SplitFiber D j).card : ℝ)) ≤
      (2 : ℝ)^n * (completeEdgeCount n+1) * Real.exp (E*(n : ℝ)^2) := by
    calc
      _ ≤ ∑ _D ∈ c4DegenerateDivisions n gamma zeta,
          ∑ _j ∈ c4SplitRepairEdgeWindow n m ⌊epsilon*(n : ℝ)^2⌋₊,
            Real.exp (E*(n : ℝ)^2) :=
        Finset.sum_le_sum fun D hD ↦ Finset.sum_le_sum fun j hj ↦ hF D hD j hj
      _ = ((c4DegenerateDivisions n gamma zeta).card : ℝ) *
          ((c4SplitRepairEdgeWindow n m ⌊epsilon*(n : ℝ)^2⌋₊).card : ℝ) *
            Real.exp (E*(n : ℝ)^2) := by simp [mul_assoc]
      _ ≤ _ := by gcongr
  calc
    _ ≤ ((∑ D ∈ c4DegenerateDivisions n gamma zeta,
        ∑ j ∈ c4SplitRepairEdgeWindow n m ⌊epsilon*(n : ℝ)^2⌋₊,
          (c4SplitFiber D j).card : ℕ) : ℝ) *
          (hammingBallVolume (completeEdgeCount n) ⌊epsilon*(n : ℝ)^2⌋₊ : ℝ) := by
      exact_mod_cast (c4CloseDegenerate_card_le_sum_splitFibers
        (n := n) (m := m) (gamma := gamma) (epsilon := epsilon) (zeta := zeta))
    _ ≤ _ := by push_cast; exact mul_le_mul_of_nonneg_right hsum (by positivity)

private theorem c4PartitionLevelOverhead_le (n : ℕ) :
    (2 : ℝ)^n * (completeEdgeCount n+1) ≤ Real.exp ((Real.log 2+2)*n) := by
  have hN : completeEdgeCount n ≤ n^2 := Nat.choose_le_pow n 2
  have hlog := c4_log_capacity_succ_le_linear hN
  have hfactor : (completeEdgeCount n : ℝ)+1 ≤ Real.exp (2*n) := by
    have h := Real.exp_le_exp.mpr hlog
    simpa only [Nat.cast_add, Nat.cast_one, Real.exp_log (by positivity :
      (0 : ℝ) < (completeEdgeCount n : ℝ)+1)] using h
  have htwo : (2 : ℝ)^n = Real.exp ((n : ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ)<2)]
  calc
    _ ≤ (2 : ℝ)^n * Real.exp (2*n) := mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = _ := by rw [htwo, ← Real.exp_add]; congr 1; ring

/-- Paper: Lemma `lemma:almost-all-nondeg`, with the sequential
parameter hierarchy. The exponential constants are independent of the
exact-edge sequence; its finite threshold may depend on that sequence. -/
theorem inducedC4AlmostAllNondegenerate {gamma : ℝ} (hgamma : gamma ∈ Ioo 0 1)
    (zeta : ℝ) (hzeta : 0 < zeta) :
    ∃ epsilon c : ℝ, 0 < epsilon ∧ 0 < c ∧
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
        ∀ᶠ n in atTop,
          ((c4CloseDegenerateGraphFinset n (m n) gamma epsilon zeta).card : ℝ) ≤
            Real.exp (-c*(n : ℝ)^2) * (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) := by
  obtain ⟨delta, gap, hdelta, hgap, hwindow⟩ :=
    exists_c4Split_degenerate_entropy_window hgamma hzeta
  obtain ⟨e0, he0, hecontrol⟩ :=
    exists_epsilon0_supercriticalDefectPatternRate_lt (show 0 < gap/4 by positivity)
  let epsilon := min (delta/8) (e0/2)
  have hepsilon : 0 < epsilon := lt_min (by positivity) (by positivity)
  have he0' : epsilon < e0 := (min_le_right _ _).trans_lt (by linarith)
  obtain ⟨hesmall, herate⟩ := hecontrol hepsilon he0'
  refine ⟨epsilon, gap/4, hepsilon, by positivity, ?_⟩
  intro m hm
  have hfib := eventually_c4DegenerateShiftedSplitFiber_le hdelta hepsilon.le
    (min_le_left _ _) hwindow hm
  have hball := eventually_hammingBallVolume_floor_square_le_exp hepsilon hesmall
  have hlin : ∀ᶠ n : ℕ in atTop, (Real.log 2+2)/(n : ℝ) ≤ gap/4 := by
    have hlim : Tendsto (fun n : ℕ ↦ (Real.log 2+2)/(n : ℝ)) atTop (𝓝 0) := by
      convert tendsto_one_div_atTop_nhds_zero_nat.const_mul (Real.log 2+2) using 1 <;>
        first | rfl | simp [div_eq_mul_inv]
    exact (hlim.eventually (gt_mem_nhds (by positivity))).mono fun _ h ↦ h.le
  let E := c4SplitEntropyNat gamma (c4Lambda gamma)
  have hlower : ∀ᶠ n in atTop,
      E-gap/4 < Real.log (splitGraphCountWithEdges n (m n) : ℝ)/(n : ℝ)^2 :=
    (splitGraphCount_log_div_sq_tendsto hgamma hm).eventually (lt_mem_nhds (by dsimp [E]; linarith))
  filter_upwards [hfib, hball, hlin, hlower,
    eventually_splitGraphCountWithEdges_pos hgamma hm, eventually_ge_atTop 1]
    with n hfib hball hlin hlower hpos hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnSq := sq_pos_of_pos hnR
  have hlinear : (Real.log 2+2)*n ≤ gap/4*(n : ℝ)^2 := by
    have h := (div_le_iff₀ hnR).mp hlin
    simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_right h hnR.le
  have hupper : ((c4CloseDegenerateGraphFinset n (m n) gamma epsilon zeta).card : ℝ) ≤
      Real.exp ((E-gap/2)*(n : ℝ)^2) := by
    calc
      _ ≤ (2 : ℝ)^n*(completeEdgeCount n+1)*Real.exp ((E-gap)*(n : ℝ)^2)*
          (hammingBallVolume (completeEdgeCount n) ⌊epsilon*(n : ℝ)^2⌋₊ : ℝ) :=
        c4CloseDegenerate_card_le_of_fiber_bound hfib
      _ ≤ Real.exp ((Real.log 2+2)*n)*Real.exp ((E-gap)*(n : ℝ)^2)*
          Real.exp (supercriticalDefectPatternRate epsilon*(n : ℝ)^2) := by
        gcongr
        exact c4PartitionLevelOverhead_le n
      _ = Real.exp ((Real.log 2+2)*n+(E-gap)*(n : ℝ)^2+
          supercriticalDefectPatternRate epsilon*(n : ℝ)^2) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hr := mul_le_mul_of_nonneg_right herate.le (sq_nonneg (n : ℝ))
        nlinarith only [hlinear, hr])
  have href : Real.exp ((E-gap/4)*(n : ℝ)^2) ≤
      (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) := by
    calc
      _ ≤ (splitGraphCountWithEdges n (m n) : ℝ) := by
        have h := Real.exp_le_exp.mpr ((lt_div_iff₀ hnSq).mp hlower).le
        simpa only [Real.exp_log (by exact_mod_cast hpos :
          (0 : ℝ) < (splitGraphCountWithEdges n (m n) : ℝ))] using h
      _ ≤ _ := by exact_mod_cast splitGraphCountWithEdges_le_inducedC4Free n (m n)
  apply hupper.trans
  calc
    _ = Real.exp (-(gap/4)*(n : ℝ)^2)*Real.exp ((E-gap/4)*(n : ℝ)^2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left href (Real.exp_pos _).le

end InducedStars
