import InducedStars.C4.BenchmarkLower
import InducedStars.C4.CoverMultiplicity
import InducedStars.C4.ScalarAnalytic
import InducedStars.Asymptotics.SampledEdgeCount
import DenseGraph.Combinatorics.BinomialEntropy

/-!
# Exact-edge enumeration of labeled split graphs

The entropy sandwich for binomial coefficients replaces Stirling's formula.
The partition sum counts cover/graph pairs, not graphs; the inequalities
below retain this distinction explicitly.
-/

noncomputable section
namespace InducedStars
open Filter Set
open scoped Topology

theorem c4SplitFiber_card_le_splitGraphCount {n m : ℕ} (D : C4Division (Fin n)) :
    (c4SplitFiber D m).card ≤ splitGraphCountWithEdges n m :=
  Finset.card_le_card (c4SplitFiber_subset_splitGraphFinsetWithEdges D)

theorem splitGraphCount_le_sum_card_c4SplitFiber (n m : ℕ) :
    splitGraphCountWithEdges n m ≤ ∑ D : C4Division (Fin n), (c4SplitFiber D m).card := by
  classical
  rw [sum_card_c4SplitFiber_eq_sum_splitDivisions]
  change (splitGraphFinsetWithEdges n m).card ≤ _
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro G hG
  obtain ⟨⟨P⟩, _⟩ := mem_splitGraphFinsetWithEdges.mp hG
  apply Finset.one_le_card.mpr
  refine ⟨P.independentPart, mem_c4SplitDivisions.mpr ⟨P.independent, ?_⟩⟩
  simpa only [C4Division.cliquePart, ← P.cliquePart_eq_compl] using P.clique

lemma c4_log_capacity_succ_le_linear {n N : ℕ} (hN : N ≤ n ^ 2) :
    Real.log ((N + 1 : ℕ) : ℝ) ≤ 2 * n := by
  have hNR : (N : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hN
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ((N + 1 : ℕ) : ℝ))
    (show ((N + 1 : ℕ) : ℝ) ≤ ((n : ℝ) + 1) ^ 2 by
      push_cast
      nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
  rw [Real.log_pow] at hlog
  have hnlog := Real.log_le_sub_one_of_pos (show 0 < (n : ℝ) + 1 by positivity)
  norm_num at hlog
  push_cast
  linarith

/-- A quadratic-scale binomial entropy limit, including endpoint quotas.
The only error estimate used is `log(N+1) ≤ 2n` for `N ≤ n²`. -/
theorem c4_log_choose_normalized_tendsto {N M : ℕ → ℕ} {a q : ℝ}
    (hfeas : ∀ᶠ n in atTop, M n ≤ N n)
    (hbound : ∀ᶠ n in atTop, N n ≤ n ^ 2)
    (hN : Tendsto (fun n => (N n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 a))
    (hq : Tendsto (fun n => (M n : ℝ) / (N n : ℝ)) atTop (𝓝 q)) :
    Tendsto (fun n => Real.log (Nat.choose (N n) (M n) : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (a * Real.binEntropy q)) := by
  have hE := hN.mul (Real.binEntropy_continuous.continuousAt.tendsto.comp hq)
  have hErr : Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    convert ht.const_mul (2 : ℝ) using 1 <;> first | rfl | simp [div_eq_mul_inv]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hE.sub hErr) hE
  · filter_upwards [hfeas, hbound, eventually_ge_atTop 1] with n hm hn hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnSq := sq_pos_of_pos hnR
    have hlo := DenseGraph.log_choose_lower_binEntropy hm
    have herr := c4_log_capacity_succ_le_linear hn
    have hlin : (2 : ℝ) / n = (2 * n) / (n : ℝ) ^ 2 := by field_simp
    rw [hlin, div_mul_eq_mul_div, ← sub_div]
    apply (div_le_div_iff_of_pos_right hnSq).mpr
    dsimp [DenseGraph.binomialEntropyPerspective] at hlo
    linarith
  · filter_upwards [hfeas] with n hm
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (DenseGraph.log_choose_upper_binEntropy hm) (sq_nonneg _)

/-- The exact finite binomial entropy is the scalar split objective at a
density shifted by `b/n²`, which accounts for the clique diagonal. -/
theorem c4_split_binomialEntropy_normalized {n m b : ℕ} (hn : 0 < n) (hb : b ≤ n)
    (hbm : b.choose 2 ≤ m) :
    DenseGraph.binomialEntropyPerspective ((n - b) * b) (m - b.choose 2) / (n : ℝ) ^ 2 =
      c4SplitEntropyNat ((2 * (m : ℝ) + b) / (n : ℝ) ^ 2) ((b : ℝ) / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcap : (((n - b) * b : ℕ) : ℝ) / (n : ℝ) ^ 2 =
      (b : ℝ) / n * (1 - (b : ℝ) / n) := by
    rw [Nat.cast_mul, Nat.cast_sub hb]
    field_simp
  have hnum : ((m - b.choose 2 : ℕ) : ℝ) / (n : ℝ) ^ 2 =
      (((2 * (m : ℝ) + b) / (n : ℝ) ^ 2) - ((b : ℝ) / n) ^ 2) / 2 := by
    rw [Nat.cast_sub hbm, Nat.cast_choose_two]
    field_simp
    ring
  have hq : c4SplitCrossDensity ((2 * (m : ℝ) + b) / (n : ℝ) ^ 2) ((b : ℝ) / n) =
      ((m - b.choose 2 : ℕ) : ℝ) / (((n - b) * b : ℕ) : ℝ) := by
    calc
      _ = (((m - b.choose 2 : ℕ) : ℝ) / (n : ℝ) ^ 2) /
          ((((n - b) * b : ℕ) : ℝ) / (n : ℝ) ^ 2) := by
        rw [hnum, hcap]
        unfold c4SplitCrossDensity
        rw [div_div, mul_assoc]
      _ = _ := div_div_div_cancel_right₀ (pow_ne_zero 2 hn0) _ _
  unfold DenseGraph.binomialEntropyPerspective c4SplitEntropyNat
  rw [hq, ← div_mul_eq_mul_div, hcap]

lemma c4_finite_cliqueFraction_feasible {n m b : ℕ}
    (hn : 0 < n) (hb : b ≤ n) (hbm : b.choose 2 ≤ m)
    (hcross : m - b.choose 2 ≤ (n - b) * b)
    (hγ : (2 * (m : ℝ) + b) / (n : ℝ) ^ 2 ∈ Ioo 0 1) :
    (b : ℝ) / n ∈ Icc
      (1 - Real.sqrt (1 - (2 * (m : ℝ) + b) / (n : ℝ) ^ 2))
      (Real.sqrt ((2 * (m : ℝ) + b) / (n : ℝ) ^ 2)) := by
  let x := (b : ℝ) / n
  let d := (2 * (m : ℝ) + b) / (n : ℝ) ^ 2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnSq := sq_pos_of_pos hnR
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hb)
  have hbR : (b.choose 2 : ℝ) ≤ m := by exact_mod_cast hbm
  have hcR : (m : ℝ) - (b.choose 2 : ℝ) ≤ ((n : ℝ) - b) * b := by
    have hh : ((m - b.choose 2 : ℕ) : ℝ) ≤ (((n - b) * b : ℕ) : ℝ) := by
      exact_mod_cast hcross
    simpa only [Nat.cast_sub hbm, Nat.cast_mul, Nat.cast_sub hb] using hh
  rw [Nat.cast_choose_two] at hbR hcR
  have hlo : x ^ 2 ≤ d := by
    dsimp [x, d]
    apply (le_div_iff₀ hnSq).mpr
    field_simp
    nlinarith
  have hhi : d ≤ 2 * x - x ^ 2 := by
    dsimp [x, d]
    apply (div_le_iff₀ hnSq).mpr
    field_simp
    nlinarith
  have hd0 : 0 ≤ d := hγ.1.le
  have hd1 : 0 ≤ 1 - d := by linarith [hγ.2]
  have hs0 := Real.sqrt_nonneg d
  have hs1 := Real.sqrt_nonneg (1 - d)
  have hsq0 := Real.sq_sqrt hd0
  have hsq1 := Real.sq_sqrt hd1
  change x ∈ Icc (1 - Real.sqrt (1 - d)) (Real.sqrt d)
  constructor <;> nlinarith

/-- The reference split partition rounds the optimizing clique proportion down. -/
def c4OptimalCliqueSize (γ : ℝ) (n : ℕ) : ℕ := ⌊c4Lambda γ * n⌋₊

def c4OptimalSplitCapacity (γ : ℝ) (n : ℕ) : ℕ :=
  (n - c4OptimalCliqueSize γ n) * c4OptimalCliqueSize γ n

def c4OptimalSplitSelectedCount (γ : ℝ) (m : ℕ → ℕ) (n : ℕ) : ℕ :=
  m n - (c4OptimalCliqueSize γ n).choose 2

lemma c4OptimalCliqueSize_le {γ : ℝ} (hγ : γ ∈ Ioo 0 1) (n : ℕ) :
    c4OptimalCliqueSize γ n ≤ n :=
  c4_floor_clique_le ⟨(c4Lambda_mem_Ioo hγ).1.le, (c4Lambda_mem_Ioo hγ).2.le⟩ n

lemma c4OptimalSplitCapacity_tendsto {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    Tendsto (fun n => (c4OptimalSplitCapacity γ n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (c4Lambda γ * (1 - c4Lambda γ))) :=
  c4_floor_split_capacity_tendsto (c4Lambda_mem_Ioo hγ)

private lemma c4OptimalSplit_real_quota_tendsto {γ : ℝ} (hγ : γ ∈ Ioo 0 1)
    {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m γ) :
    Tendsto (fun n => ((m n : ℝ) - ((c4OptimalCliqueSize γ n).choose 2 : ℝ)) /
      (c4OptimalSplitCapacity γ n : ℝ)) atTop (𝓝 (c4OptimalCrossDensity γ)) := by
  have hx := c4Lambda_mem_Ioo hγ
  have hcap := c4OptimalSplitCapacity_tendsto hγ
  have hb : Tendsto (fun n => (c4OptimalCliqueSize γ n : ℝ) / n)
      atTop (𝓝 (c4Lambda γ)) :=
    (tendsto_nat_floor_mul_div_atTop hx.1.le).comp tendsto_natCast_atTop_atTop
  have hI := c4_choose_normalized_tendsto hb
  have hM : Tendsto (fun n => (m n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (γ / 2)) := by
    convert (hasAsymptoticEdgeDensity_orderedSquare hm).div_const 2 using 1 <;> try rfl
    funext n
    ring
  have h := (hM.sub hI).div hcap (mul_pos hx.1 (sub_pos.mpr hx.2)).ne'
  have hvalue : (γ / 2 - c4Lambda γ ^ 2 / 2) /
      (c4Lambda γ * (1 - c4Lambda γ)) = c4OptimalCrossDensity γ := by
    unfold c4OptimalCrossDensity c4SplitCrossDensity
    field_simp
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change ((m n : ℝ) / (n : ℝ) ^ 2 - ((c4OptimalCliqueSize γ n).choose 2 : ℝ) /
    (n : ℝ) ^ 2) / ((c4OptimalSplitCapacity γ n : ℝ) / (n : ℝ) ^ 2) = _
  rw [← sub_div, div_div_div_cancel_right₀ (pow_ne_zero 2 hn0)]

theorem c4OptimalSplit_eventually_feasible {γ : ℝ} (hγ : γ ∈ Ioo 0 1)
    {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m γ) :
    ∀ᶠ n in atTop, (c4OptimalCliqueSize γ n).choose 2 ≤ m n ∧
      c4OptimalSplitSelectedCount γ m n ≤ c4OptimalSplitCapacity γ n := by
  have hx := c4Lambda_mem_Ioo hγ
  have hp := mul_pos hx.1 (sub_pos.mpr hx.2)
  have hcap := (c4OptimalSplitCapacity_tendsto hγ).eventually (lt_mem_nhds hp)
  have hquota := (c4OptimalSplit_real_quota_tendsto hγ hm).eventually
    (isOpen_Ioo.mem_nhds (c4OptimalCrossDensity_mem_Ioo hγ))
  filter_upwards [hcap, hquota] with n hcap hquota
  have hcap0 : (0 : ℝ) < c4OptimalSplitCapacity γ n :=
    (div_pos_iff.mp hcap).resolve_right
      (by rintro ⟨_, h⟩; nlinarith [sq_nonneg (n : ℝ)]) |>.1
  have hlo := (div_pos_iff_of_pos_right hcap0).mp hquota.1
  have hhi := (div_lt_one hcap0).mp hquota.2
  have hforced : (c4OptimalCliqueSize γ n).choose 2 ≤ m n := by
    exact_mod_cast (show ((c4OptimalCliqueSize γ n).choose 2 : ℝ) ≤ m n by linarith)
  refine ⟨hforced, ?_⟩
  have hM : (c4OptimalSplitSelectedCount γ m n : ℝ) =
      (m n : ℝ) - ((c4OptimalCliqueSize γ n).choose 2 : ℝ) := Nat.cast_sub hforced
  exact_mod_cast (show (c4OptimalSplitSelectedCount γ m n : ℝ) ≤ c4OptimalSplitCapacity γ n by
    rw [hM]
    exact hhi.le)

theorem c4OptimalSplit_quota_tendsto {γ : ℝ} (hγ : γ ∈ Ioo 0 1)
    {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m γ) :
    Tendsto (fun n => (c4OptimalSplitSelectedCount γ m n : ℝ) /
      (c4OptimalSplitCapacity γ n : ℝ)) atTop (𝓝 (c4OptimalCrossDensity γ)) := by
  apply (c4OptimalSplit_real_quota_tendsto hγ hm).congr'
  filter_upwards [c4OptimalSplit_eventually_feasible hγ hm] with n hn
  simp only [c4OptimalSplitSelectedCount, Nat.cast_sub hn.1]

theorem c4OptimalSplit_log_choose_tendsto {γ : ℝ} (hγ : γ ∈ Ioo 0 1)
    {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m γ) :
    Tendsto (fun n => Real.log (Nat.choose (c4OptimalSplitCapacity γ n)
      (c4OptimalSplitSelectedCount γ m n) : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (c4SplitEntropyNat γ (c4Lambda γ))) := by
  apply c4_log_choose_normalized_tendsto
    ((c4OptimalSplit_eventually_feasible hγ hm).mono fun _ h => h.2)
    (Eventually.of_forall fun n => ?_) (c4OptimalSplitCapacity_tendsto hγ)
    (c4OptimalSplit_quota_tendsto hγ hm)
  exact (Nat.mul_le_mul (Nat.sub_le _ _) (c4OptimalCliqueSize_le hγ n)).trans_eq (pow_two n).symm

lemma c4OptimalSplit_choose_le_count {γ : ℝ} (hγ : γ ∈ Ioo 0 1)
    {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m γ) :
    ∀ᶠ n in atTop, Nat.choose (c4OptimalSplitCapacity γ n)
      (c4OptimalSplitSelectedCount γ m n) ≤ splitGraphCountWithEdges n (m n) := by
  filter_upwards [c4OptimalSplit_eventually_feasible hγ hm] with n hn
  have h := c4SplitFiber_card_le_splitGraphCount
    (m := m n) (c4DivisionOfCliqueSize n (c4OptimalCliqueSize γ n))
  rwa [card_c4SplitFiber, c4DivisionOfCliqueSize_clique_card (c4OptimalCliqueSize_le hγ n),
    c4DivisionOfCliqueSize_independent_card (c4OptimalCliqueSize_le hγ n), ite_eq_left hn.1] at h

/-- The floor-optimizer fiber proves positivity before any logarithmic
comparison or probability quotient is taken. -/
theorem eventually_splitGraphCountWithEdges_pos {γ : ℝ} (hγ : γ ∈ Ioo 0 1)
    {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m γ) :
    ∀ᶠ n in atTop, 0 < splitGraphCountWithEdges n (m n) := by
  filter_upwards [c4OptimalSplit_eventually_feasible hγ hm,
    c4OptimalSplit_choose_le_count hγ hm] with n hfeas hcount
  exact (Nat.choose_pos hfeas.2).trans_le hcount

private lemma eventually_c4SplitFiber_le_entropy_exp {γ : ℝ} (hγ : γ ∈ Ioo 0 1)
    {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m γ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ D : C4Division (Fin n),
      ((c4SplitFiber D (m n)).card : ℝ) ≤
        Real.exp ((n : ℝ) ^ 2 * (c4SplitEntropyNat γ (c4Lambda γ) + ε)) := by
  have hE := (analyticAt_c4SplitEntropyNat_optimizer hγ).continuousAt
  have hmem : ∀ᶠ d in 𝓝 γ, d ∈ Ioo 0 1 := isOpen_Ioo.mem_nhds hγ
  have hevent : ∀ᶠ d in 𝓝 γ, d ∈ Ioo 0 1 ∧
      c4SplitEntropyNat d (c4Lambda d) < c4SplitEntropyNat γ (c4Lambda γ) + ε :=
    hmem.and (hE.eventually (gt_mem_nhds (by linarith)))
  obtain ⟨δ, hδ, hwindow⟩ := Metric.eventually_nhds_iff.mp hevent
  have hmclose : ∀ᶠ n in atTop, |2 * (m n : ℝ) / (n : ℝ) ^ 2 - γ| < δ / 2 := by
    simpa only [Real.dist_eq] using (hasAsymptoticEdgeDensity_orderedSquare hm).eventually
      (Metric.ball_mem_nhds γ (by positivity))
  have hinv : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / n < δ / 2 :=
    tendsto_one_div_atTop_nhds_zero_nat.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hmclose, hinv, eventually_ge_atTop 1] with n hmclose hinv hn D
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnSq := sq_pos_of_pos hnR
  let b := D.cliquePart.card
  have hparts : D.independentPart.card + b = n := by simpa [b] using D.card_add
  have hb : b ≤ n := by omega
  have hA : D.independentPart.card = n - b := by omega
  have hbR : (b : ℝ) ≤ n := by exact_mod_cast hb
  have hbsmall : 0 ≤ (b : ℝ) / (n : ℝ) ^ 2 ∧ (b : ℝ) / (n : ℝ) ^ 2 ≤ 1 / n := by
    refine ⟨by positivity, ?_⟩
    apply (div_le_iff₀ hnSq).mpr
    field_simp
    nlinarith
  have hnear : dist ((2 * (m n : ℝ) + b) / (n : ℝ) ^ 2) γ < δ := by
    rw [Real.dist_eq, add_div]
    have habs := abs_add_le (2 * (m n : ℝ) / (n : ℝ) ^ 2 - γ)
      ((b : ℝ) / (n : ℝ) ^ 2)
    rw [abs_of_nonneg hbsmall.1] at habs
    have heq : 2 * (m n : ℝ) / (n : ℝ) ^ 2 + (b : ℝ) / (n : ℝ) ^ 2 - γ =
        (2 * (m n : ℝ) / (n : ℝ) ^ 2 - γ) + (b : ℝ) / (n : ℝ) ^ 2 := by ring
    rw [heq]
    linarith
  obtain ⟨hdensity, hopt⟩ := hwindow hnear
  rw [card_c4SplitFiber, hA]
  change ((if b.choose 2 ≤ m n then Nat.choose ((n - b) * b) (m n - b.choose 2) else 0 : ℕ) : ℝ) ≤ _
  split_ifs with hbm
  · by_cases hcap : m n - b.choose 2 ≤ (n - b) * b
    · apply (DenseGraph.choose_le_exp_binomialEntropyPerspective hcap).trans
      apply Real.exp_le_exp.mpr
      have hfeas := c4_finite_cliqueFraction_feasible hnpos hb hbm hcap hdensity
      have hscalar := (c4Lambda_isMaxOn hdensity) hfeas
      have hnorm : DenseGraph.binomialEntropyPerspective ((n - b) * b) (m n - b.choose 2) /
          (n : ℝ) ^ 2 ≤ c4SplitEntropyNat γ (c4Lambda γ) + ε := by
        rw [c4_split_binomialEntropy_normalized hnpos hb hbm]
        exact hscalar.trans hopt.le
      simpa only [mul_comm] using (div_le_iff₀ hnSq).mp hnorm
    · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hcap), Nat.cast_zero]
      exact (Real.exp_pos _).le
  · simp only [Nat.cast_zero]
    exact (Real.exp_pos _).le

private lemma eventually_log_splitGraphCount_normalized_upper {γ : ℝ} (hγ : γ ∈ Ioo 0 1)
    {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m γ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, Real.log (splitGraphCountWithEdges n (m n) : ℝ) / (n : ℝ) ^ 2 ≤
      c4SplitEntropyNat γ (c4Lambda γ) + ε + Real.log 2 / n := by
  classical
  filter_upwards [eventually_c4SplitFiber_le_entropy_exp hγ hm hε,
    eventually_splitGraphCountWithEdges_pos hγ hm, eventually_ge_atTop 1] with n hbound hpos hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htotal : (splitGraphCountWithEdges n (m n) : ℝ) ≤ (2 : ℝ) ^ n *
      Real.exp ((n : ℝ) ^ 2 * (c4SplitEntropyNat γ (c4Lambda γ) + ε)) := by
    calc
      _ ≤ ((∑ D : C4Division (Fin n), (c4SplitFiber D (m n)).card : ℕ) : ℝ) := by
        exact_mod_cast splitGraphCount_le_sum_card_c4SplitFiber n (m n)
      _ = ∑ D : C4Division (Fin n), ((c4SplitFiber D (m n)).card : ℝ) := by simp
      _ ≤ ∑ _D : C4Division (Fin n),
          Real.exp ((n : ℝ) ^ 2 * (c4SplitEntropyNat γ (c4Lambda γ) + ε)) :=
        Finset.sum_le_sum fun D _ => hbound D
      _ = _ := by simp [C4Division]
  have hlog := Real.log_le_log (by exact_mod_cast hpos) htotal
  rw [Real.log_mul (pow_ne_zero _ (by norm_num)) (Real.exp_ne_zero _),
    Real.log_pow, Real.log_exp] at hlog
  apply (div_le_iff₀ (sq_pos_of_pos hnR)).mpr
  have heq : (c4SplitEntropyNat γ (c4Lambda γ) + ε + Real.log 2 / n) * (n : ℝ) ^ 2 =
      (n : ℝ) * Real.log 2 + (n : ℝ) ^ 2 * (c4SplitEntropyNat γ (c4Lambda γ) + ε) := by
    field_simp
    ring
  rwa [heq]

/-- Natural-log split enumeration with quadratic normalization. -/
theorem splitGraphCount_log_div_sq_tendsto {γ : ℝ} (hγ : γ ∈ Ioo 0 1)
    {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m γ) :
    Tendsto (fun n => Real.log (splitGraphCountWithEdges n (m n) : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (c4SplitEntropyNat γ (c4Lambda γ))) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hlo := (c4OptimalSplit_log_choose_tendsto hγ hm).eventually (lt_mem_nhds ha)
    filter_upwards [hlo, c4OptimalSplit_choose_le_count hγ hm,
      c4OptimalSplit_eventually_feasible hγ hm] with n hlo hcount hfeas
    apply hlo.trans_le
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact Real.log_le_log (by exact_mod_cast Nat.choose_pos hfeas.2) (by exact_mod_cast hcount)
  · intro a ha
    let ε := (a - c4SplitEntropyNat γ (c4Lambda γ)) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have herr : Tendsto (fun n : ℕ => Real.log 2 / n) atTop (𝓝 0) := by
      have ht : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      convert ht.const_mul (Real.log 2) using 1 <;> first | rfl | simp [div_eq_mul_inv]
    filter_upwards [eventually_log_splitGraphCount_normalized_upper hγ hm hε,
      herr.eventually (gt_mem_nhds hε)] with n hn he
    dsimp [ε] at hn he
    linarith

/-- Exact split-graph entropy in the paper's base-two, complete-edge-count
normalization.  This theorem concerns split graphs themselves; the later
almost-all-split theorem is required to transfer it to induced-C4-free graphs. -/
theorem splitGraphCount_normalizedLog_tendsto {γ : ℝ} (hγ : γ ∈ Ioo 0 1)
    {m : ℕ → ℕ} (hm : HasAsymptoticEdgeDensity m γ) :
    Tendsto (fun n => log2 (splitGraphCountWithEdges n (m n) : ℝ) /
      (completeEdgeCount n : ℝ)) atTop (𝓝 (c4SplitOptimalEntropy γ)) := by
  have h := ((splitGraphCount_log_div_sq_tendsto hγ hm).div
    c4_complete_normalized_tendsto (by norm_num)).div_const (Real.log 2)
  have heq : c4SplitEntropyNat γ (c4Lambda γ) / (1 / 2) / Real.log 2 =
      c4SplitOptimalEntropy γ := by
    rw [c4SplitOptimalEntropy, c4SplitEntropy_eq_nat_div_log_two]
    ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change (Real.log (splitGraphCountWithEdges n (m n) : ℝ) / (n : ℝ) ^ 2 /
    ((completeEdgeCount n : ℝ) / (n : ℝ) ^ 2)) / Real.log 2 = _
  rw [div_div_div_cancel_right₀ (pow_ne_zero 2 hn0)]
  unfold log2
  ring

end InducedStars
