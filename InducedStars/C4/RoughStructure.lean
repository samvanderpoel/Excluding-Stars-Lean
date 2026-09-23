import InducedStars.C4.RoughEntropyGap
import InducedStars.C4.TemplateEntropyCounting
import InducedStars.Structure.Supercritical.MediumParameters

/-!
# Exponentially strong rough split structure

Paper: Lemma `lemma:c4-rough-struc`. Complete templates supply the lower
benchmark. Actual repaired slices are counted through the feasible
entropy envelope, including infeasible ideal targets. All choices
of tolerances precede the edge-count sequence and the ambient graph.
-/

noncomputable section
open Filter Finset Set InducedStars.Regularity
open scoped Topology Classical
namespace InducedStars

private theorem eventually_c4RepairWindow_card_le_exp {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, ∀ m r : ℕ, r ≤ n^2 →
      ((Finset.Icc (m-r) (m+r)).card : ℝ) ≤ Real.exp (a*(n : ℝ)^2) := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (3/a)] with n hn
  intro m r hr
  have hcard : (Finset.Icc (m-r) (m+r)).card ≤ 2*r+1 := by
    rw [Nat.card_Icc]
    omega
  have hrR : (r : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast hr
  have hcardR : ((Finset.Icc (m-r) (m+r)).card : ℝ) ≤ ((n : ℝ)+1)^3 := by
    have hh := (Nat.cast_le (α := ℝ)).mpr hcard
    push_cast at hh
    nlinarith [Nat.cast_nonneg (α := ℝ) n, pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 3]
  have hlin := mul_le_mul_of_nonneg_right ((div_le_iff₀ ha).mp hn)
    (Nat.cast_nonneg (α := ℝ) n)
  calc
    _ ≤ ((n : ℝ)+1)^3 := hcardR
    _ ≤ (Real.exp (n : ℝ))^3 :=
      pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) 3
    _ = Real.exp (3*(n : ℝ)) := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hlin])

/-- Paper: Lemma `lemma:c4-rough-struc`, with its complete-template benchmark
and feasible quota envelope. The canonical defect cost
is exactly the minimum edit distance to a split graph, as exposed by
`mem_c4FarGraphFinset_iff_editDistance`. -/
theorem inducedC4RoughSplitStructure {gamma epsilon : ℝ}
    (hgamma : gamma ∈ Set.Ioo 0 1) (hepsilon : 0 < epsilon) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
      ∀ᶠ n : ℕ in atTop,
        ((c4FarGraphFinset n (m n) epsilon).card : ℝ) ≤
          Real.exp (-c*(n : ℝ)^2) * (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) := by
  obtain ⟨d, eta0, hd, heta0, hgap⟩ :=
    exists_c4FarTemplate_entropy_gap hgamma (half_pos hepsilon)
  obtain ⟨modulus, hmodulus, hupper⟩ :=
    c4TemplateNearSlice_entropy_upper (show 0 < d/8 by positivity)
  let a : ℝ := Real.log 2*d/8
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨e0, he0, hrate⟩ := exists_epsilon0_supercriticalDefectPatternRate_lt ha
  let tau : ℝ := min (1/4) (min (epsilon/24) (min (modulus/12) (e0/6)))
  have htau : 0 < tau := by dsimp [tau]; positivity
  have htauquarter : tau ≤ 1/4 := min_le_left _ _
  have htauE : tau ≤ epsilon/24 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have htauM : tau ≤ modulus/12 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have htauRate : tau ≤ e0/6 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let rho : ℝ := 3*tau
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrhoE : rho ≤ epsilon/2 := by dsimp [rho]; linarith
  have hrhoM : rho ≤ modulus/4 := by dsimp [rho]; linarith
  have hrhoOne : rho ≤ 1 := by dsimp [rho]; linarith
  obtain ⟨hrhoSmall, hballRate⟩ := hrate hrho (show rho < e0 by dsimp [rho]; linarith)
  let etaMax : ℝ := min (eta0/3) (min (modulus/12) (d/24))
  have hetaMax : 0 < etaMax := by dsimp [etaMax]; positivity
  obtain ⟨eta, heta, hetaMax', u, n0, _, hlift⟩ :=
    exists_c4BoundedLift_for_every_graph htau (by linarith) hetaMax
  have heta0' : 3*eta ≤ eta0 := by
    have := hetaMax'.trans (min_le_left _ _)
    linarith
  have hetaM : 3*eta ≤ modulus/4 := by
    have := hetaMax'.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hetaD : 3*eta ≤ d/8 := by
    have := hetaMax'.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  refine ⟨Real.log 2*d/4, by positivity, ?_⟩
  intro m hm
  filter_upwards [hgap, eventually_ge_atTop n0, eventually_ge_atTop 1,
    c4_edgeTarget_error_eventually hm (show 0 < modulus/4 by positivity),
    eventually_hammingBallVolume_floor_square_le_exp hrho hrhoSmall,
    eventually_c4RepairWindow_card_le_exp ha,
    eventually_card_c4BoundedLift_le_exp u ha,
    eventually_c4Free_count_entropy_lower hgamma (show 0 < d/8 by positivity) hm]
    with n hgap hn0 hnpos htarget hball hwindow hdata hlower
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnSq : 0 ≤ (n : ℝ)^2 := sq_nonneg _
  let r : ℕ := ⌊rho*(n : ℝ)^2⌋₊
  have hrR : (r : ℝ) ≤ rho*(n : ℝ)^2 := Nat.floor_le (by positivity)
  have hrn : r ≤ n^2 := by
    have hh := mul_le_mul_of_nonneg_right hrhoOne hnSq
    have hcast : (r : ℝ) ≤ (n : ℝ)^2 := by linarith
    exact_mod_cast hcast
  let F := c4FarLiftTemplateFamily n u (3*eta) (epsilon-rho)
  have hslice : ∀ J ∈ F,
      ((c4TemplateNearSlice J (m n) r).card : ℝ) ≤
        Real.exp (Real.log 2*(c4CompleteEntropyBenchmark n gamma-d/2*(n : ℝ)^2)) := by
    intro J hJ
    obtain ⟨_, hfree, hmissing, hfar⟩ := mem_filter.mp hJ
    have hmissingR : (c4MissingEdgeCount J : ℝ) ≤ 3*eta*(n : ℝ)^2 := hmissing
    have hmissingM := mul_le_mul_of_nonneg_right hetaM hnSq
    have hmissingD := mul_le_mul_of_nonneg_right hetaD hnSq
    have hmissing0 := mul_le_mul_of_nonneg_right heta0' hnSq
    have hperturb : |(m n : ℝ)-gamma*completeEdgeCount n|+r+c4MissingEdgeCount J ≤
        modulus*(n : ℝ)^2 := by
      have hh := mul_le_mul_of_nonneg_right hrhoM hnSq
      linarith
    have hfar' (D : C4Division (Fin n)) :
        epsilon/2*(n : ℝ)^2 ≤ DenseGraph.coloredEditDistance J (c4SplitColoring D) := by
      have hh := mul_le_mul_of_nonneg_right hrhoE hnSq
      have hh' := hfar D
      nlinarith only [hh, hh']
    have hentropy := hgap J hfree (hmissing.trans hmissing0) hfar'
    have hmissPow : (2 : ℝ)^c4MissingEdgeCount J ≤ Real.exp (a*(n : ℝ)^2) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ)<2), ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (hmissingR.trans hmissingD) realLogTwo_pos.le
      dsimp only [a]
      nlinarith only [hh]
    have hball' : (hammingBallVolume (completeEdgeCount n) r : ℝ) ≤
        Real.exp (a*(n : ℝ)^2) := hball.trans (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right hballRate.le hnSq))
    calc
      _ ≤ ((Finset.Icc (m n-r) (m n+r)).card : ℝ) *
          (2 : ℝ)^c4MissingEdgeCount J *
          (hammingBallVolume (completeEdgeCount n) r : ℝ) *
          Real.exp (Real.log 2*(DenseGraph.feasibleEntropyEnvelope
            (c4ColorEdgeCount J .red) (c4ColorEdgeCount J .blue)
            (gamma*completeEdgeCount n)+d/8*(n : ℝ)^2)) :=
        hupper n (m n) r J _ hn hperturb
      _ ≤ Real.exp (a*(n : ℝ)^2)*Real.exp (a*(n : ℝ)^2)*Real.exp (a*(n : ℝ)^2)*
          Real.exp (Real.log 2*(c4CompleteEntropyBenchmark n gamma-d*(n : ℝ)^2+
            d/8*(n : ℝ)^2)) := by
        gcongr
        · exact hwindow (m n) r hrn
      _ = _ := by
        simp only [← Real.exp_add]
        congr 1
        dsimp only [a]
        ring
  have hsum : ((c4FarGraphFinset n (m n) epsilon).card : ℝ) ≤
      Real.exp (Real.log 2*(c4CompleteEntropyBenchmark n gamma-3*d/8*(n : ℝ)^2)) := by
    have hfinite := c4FarGraph_card_le_template_sum
      (n := n) (m := m n) (u := u) (epsilon := epsilon) (rho := rho) (eta := 3*eta)
      (fun G hG ↦ hlift n hn0 G (mem_inducedC4FreeGraphFinsetWithEdges.mp
        (mem_c4FarGraphFinset.mp hG).1).1)
    have hcard : (F.card : ℝ) ≤ Real.exp (a*(n : ℝ)^2) := by
      apply le_trans _ hdata
      exact_mod_cast card_filter_le _ _
    calc
      _ ≤ ∑ J ∈ F, ((c4TemplateNearSlice J (m n) r).card : ℝ) := by
        have hh : (c4FarGraphFinset n (m n) epsilon).card ≤
            ∑ J ∈ F, (c4TemplateNearSlice J (m n) r).card := hfinite
        exact_mod_cast hh
      _ ≤ ∑ _J ∈ F,
          Real.exp (Real.log 2*(c4CompleteEntropyBenchmark n gamma-d/2*(n : ℝ)^2)) :=
        sum_le_sum hslice
      _ = (F.card : ℝ)*
          Real.exp (Real.log 2*(c4CompleteEntropyBenchmark n gamma-d/2*(n : ℝ)^2)) := by
        simp
      _ ≤ Real.exp (a*(n : ℝ)^2)*
          Real.exp (Real.log 2*(c4CompleteEntropyBenchmark n gamma-d/2*(n : ℝ)^2)) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [a]; ring
  apply hsum.trans
  calc
    _ = Real.exp (-(Real.log 2*d/4)*(n : ℝ)^2)*
        Real.exp (Real.log 2*(c4CompleteEntropyBenchmark n gamma-d/8*(n : ℝ)^2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (Real.exp_pos _).le

end InducedStars
