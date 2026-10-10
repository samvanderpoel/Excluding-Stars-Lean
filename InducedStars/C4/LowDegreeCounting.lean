import InducedStars.C4.LowDegreeGeometry
import DenseGraph.Combinatorics.ProfileSums
import DenseGraph.Combinatorics.BinomialJointShift

/-!
# Counting low-degree internal defects and summing their shifted slices

Paper: the final matching-defect sum in `eqn:c4-fmat-sum`. Both induced
side graphs are counted by their matching-cover neighborhood encodings.
The explicit natural entropy rate tends to zero with the degree parameter.
-/

noncomputable section
open Finset Filter
open scoped Classical Topology
namespace InducedStars

theorem card_c4LowDegreeDefectFinset_le {n : ℕ} (D : C4Division (Fin n))
    (k : ℕ) {alpha : ℝ} (halpha : 0 ≤ alpha) (hhalf : alpha ≤ 1/2) :
    ((c4LowDegreeDefectFinset D alpha k).card : ℝ) ≤
      Real.exp (4*(k : ℝ)*((n : ℝ)*Real.binEntropy alpha+Real.log (n+1))+2*k) := by
  let F := c4LowDegreeDefectFinset D alpha k
  let S : Finset (SimpleGraph (Fin n)) := univ.filter fun H ↦
    DenseGraph.matchingNumber H ≤ k ∧ ∀ v, (H.degree v : ℝ) ≤ alpha*n
  let code (T : SimpleGraph (Fin n)) :=
    (c4WithinGraph T D.independentPart,c4WithinGraph T D.cliquePart)
  have hmap : F.image code ⊆ S ×ˢ S := by
    intro p hp
    obtain ⟨T,hT,rfl⟩ := mem_image.mp hp
    obtain ⟨hsupport,hmatching,hdegree⟩ := mem_c4LowDegreeDefectFinset.mp hT
    have hdeg (A : Finset (Fin n)) (v : Fin n) :
        ((c4WithinGraph T A).degree v : ℝ) ≤ alpha*n :=
      (show ((c4WithinGraph T A).degree v : ℝ) ≤ T.degree v by
        exact_mod_cast SimpleGraph.degree_le_of_le (c4WithinGraph_le T A)).trans (hdegree v)
    obtain ⟨ha,hb⟩ := (c4SideMatchingNumber_le_iff D T k).mp hmatching
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,ha,hdeg _⟩,
      mem_filter.mpr ⟨mem_univ _,hb,hdeg _⟩⟩
  have hinj : Set.InjOn code (F : Set (SimpleGraph (Fin n))) := by
    intro T hT U hU hcode
    have ha := congrArg Prod.fst hcode
    have hb := congrArg Prod.snd hcode
    rw [← (mem_c4LowDegreeDefectFinset.mp hT).1.within_sup_eq,
      ← (mem_c4LowDegreeDefectFinset.mp hU).1.within_sup_eq]
    exact congrArg₂ (fun A B : SimpleGraph (Fin n) ↦ A ⊔ B) ha hb
  have hcard : F.card ≤ S.card*S.card := by
    rw [← card_image_iff.mpr hinj]
    exact (card_le_card hmap).trans_eq (card_product _ _)
  have hS := DenseGraph.card_graphFamily_le_exp_of_matching_le_degree S k halpha hhalf
    (fun H hH ↦ (mem_filter.mp hH).2.1)
    (fun H hH v ↦ by simpa only [Fintype.card_fin] using (mem_filter.mp hH).2.2 v)
  simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at hS
  calc
    _ ≤ (S.card : ℝ)*(S.card : ℝ) := by exact_mod_cast hcard
    _ ≤ Real.exp (2*(k : ℝ)*((n : ℝ)*Real.binEntropy alpha+Real.log (n+1))+k)*
        Real.exp (2*(k : ℝ)*((n : ℝ)*Real.binEntropy alpha+Real.log (n+1))+k) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem card_c4LowDegreeDefectPatternFinset_le {n : ℕ} (D : C4Division (Fin n))
    (k : ℕ) {alpha : ℝ} (halpha : 0 ≤ alpha) (hhalf : alpha ≤ 1/2) :
    ((c4LowDegreeDefectPatternFinset D alpha k).card : ℝ) ≤
      Real.exp (4*(k : ℝ)*((n : ℝ)*Real.binEntropy alpha+Real.log (n+1))+2*k) := by
  apply (show ((c4LowDegreeDefectPatternFinset D alpha k).card : ℝ) ≤
    (c4LowDegreeDefectFinset D alpha k).card by exact_mod_cast card_filter_le _ _).trans
  exact card_c4LowDegreeDefectFinset_le D k halpha hhalf

/-- Counting all actual patterns, with an exponential cost per defect edge. -/
theorem sum_c4LowDegreeDefectPattern_exp_edges_le {n : ℕ} (D : C4Division (Fin n))
    (k : ℕ) {alpha C : ℝ} (halpha : 0 ≤ alpha) (hhalf : alpha ≤ 1/2) (hC : 0 ≤ C) :
    (∑ T ∈ c4LowDegreeDefectPatternFinset D alpha k,
      Real.exp (C*(finiteGraphEdges T).card)) ≤
      Real.exp (4*(k : ℝ)*((n : ℝ)*(Real.binEntropy alpha+C*alpha)+
        Real.log (n+1))+2*k) := by
  have hpoint (T : SimpleGraph (Fin n)) (hT : T ∈ c4LowDegreeDefectPatternFinset D alpha k) :
      C*(finiteGraphEdges T).card ≤ C*(4*(k : ℝ)*alpha*n) := by
    obtain ⟨hs,hk,hd⟩ := mem_c4LowDegreeDefectPatternFinset.mp hT
    exact mul_le_mul_of_nonneg_left (c4LowDegreeDefect_edgeCount_le halpha hs hk.le hd) hC
  calc
    _ ≤ ∑ _T ∈ c4LowDegreeDefectPatternFinset D alpha k,
        Real.exp (C*(4*(k : ℝ)*alpha*n)) :=
      sum_le_sum fun T hT ↦ Real.exp_le_exp.mpr (hpoint T hT)
    _ = ((c4LowDegreeDefectPatternFinset D alpha k).card : ℝ)*
        Real.exp (C*(4*(k : ℝ)*alpha*n)) := by simp
    _ ≤ Real.exp (4*(k : ℝ)*((n : ℝ)*Real.binEntropy alpha+Real.log (n+1))+2*k)*
        Real.exp (C*(4*(k : ℝ)*alpha*n)) :=
      mul_le_mul_of_nonneg_right (card_c4LowDegreeDefectPatternFinset_le D k halpha hhalf)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Uniform `exp(o_alpha(1) k n)` control, including a fixed cost per
defect edge. The finite threshold is independent of the division and k. -/
theorem exists_alpha0_c4LowDegree_weighted_count {C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 < rho) :
    ∃ alpha0 : ℝ, 0 < alpha0 ∧ alpha0 ≤ 1/2 ∧
      ∀ᶠ n : ℕ in atTop, ∀ alpha ∈ Set.Icc (0 : ℝ) alpha0,
        ∀ D : C4Division (Fin n), ∀ k : ℕ,
          (∑ T ∈ c4LowDegreeDefectPatternFinset D alpha k,
            Real.exp (C*(finiteGraphEdges T).card)) ≤ Real.exp (rho*k*n) := by
  have hcontinuous : ContinuousAt (fun a : ℝ ↦ Real.binEntropy a+C*a) 0 := by fun_prop
  have hev : ∀ᶠ a : ℝ in 𝓝 0, Real.binEntropy a+C*a < rho/8 := by
    simpa using hcontinuous.eventually (gt_mem_nhds (by simpa using (show 0 < rho/8 by positivity)))
  obtain ⟨d,hd,hwindow⟩ := Metric.eventually_nhds_iff.mp hev
  let alpha0 := min (d/2) (1/4)
  have ha0 : 0 < alpha0 := lt_min (by positivity) (by norm_num)
  have hahalf : alpha0 ≤ 1/2 := (min_le_right _ _).trans (by norm_num)
  have hlog := DenseGraph.eventually_natCast_mul_log_add_one_le_mul 4
    (show 0 < rho/4 by positivity)
  have htwo : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ rho/4*n := by
    have h := tendsto_natCast_atTop_atTop.eventually_ge_atTop (8/rho)
    filter_upwards [h] with n hn
    have hmul := (div_le_iff₀ hrho).mp hn
    nlinarith
  refine ⟨alpha0,ha0,hahalf,?_⟩
  filter_upwards [hlog,htwo] with n hlog htwo alpha ha D k
  have hanear : dist alpha 0 < d := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ha.1]
    exact (ha.2.trans (min_le_left _ _)).trans_lt (by linarith)
  have hentropy := hwindow hanear
  apply (sum_c4LowDegreeDefectPattern_exp_edges_le D k ha.1 (ha.2.trans hahalf) hC).trans
  apply Real.exp_le_exp.mpr
  have he := mul_le_mul_of_nonneg_right hentropy.le (Nat.cast_nonneg n)
  have hbase : 4*((n : ℝ)*(Real.binEntropy alpha+C*alpha)+Real.log (n+1))+2 ≤ rho*n :=
    by nlinarith only [he,hlog,htwo]
  have hmul := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg k)
  nlinarith only [hmul]

/-- Pure pattern counting is the zero edge-cost specialization. -/
theorem exists_alpha0_c4LowDegree_pattern_count {rho : ℝ} (hrho : 0 < rho) :
    ∃ alpha0 : ℝ, 0 < alpha0 ∧ alpha0 ≤ 1/2 ∧
      ∀ᶠ n : ℕ in atTop, ∀ alpha ∈ Set.Icc (0 : ℝ) alpha0,
        ∀ D : C4Division (Fin n), ∀ k : ℕ,
          ((c4LowDegreeDefectPatternFinset D alpha k).card : ℝ) ≤ Real.exp (rho*k*n) := by
  simpa using exists_alpha0_c4LowDegree_weighted_count (C := 0) (by norm_num) hrho

end InducedStars
