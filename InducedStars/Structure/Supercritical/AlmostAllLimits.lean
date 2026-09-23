import InducedStars.Structure.Supercritical.ReferenceFiber
import InducedStars.Asymptotics.RoughStructure
import Mathlib.Tactic

/-!
# Limit algebra for the final supercritical aggregation

This module separates the analytic last step from the combinatorial global
bound.  Its hypothesis is precisely the two-scale exceptional-family
estimate produced by the aggregation layer.
-/

noncomputable section

set_option maxHeartbeats 800000

open Filter Set Topology

namespace InducedStars

/-- A positive linear exponential decays along the natural numbers. -/
theorem tendsto_exp_neg_mul_natCast_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ Real.exp (-c * (n : ℝ))) atTop (nhds 0) := by
  have hlinear : Tendsto (fun n : ℕ ↦ c * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear).congr' ?_
  exact Eventually.of_forall fun n ↦ by
    simp only [Function.comp_apply]
    congr 1
    ring

/-- A positive quadratic exponential decays along the natural numbers. -/
theorem tendsto_exp_neg_mul_natCast_sq_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ Real.exp (-c * (n : ℝ) ^ 2)) atTop (nhds 0) := by
  have hsquare : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      tendsto_natCast_atTop_atTop
  have hquadratic : Tendsto (fun n : ℕ ↦ c * (n : ℝ) ^ 2) atTop atTop :=
    hsquare.const_mul_atTop hc
  refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp hquadratic).congr' ?_
  exact Eventually.of_forall fun n ↦ by
    simp only [Function.comp_apply]
    congr 1
    ring

/-- Abstract final output of the finite aggregation: linear decay relative
to the good family plus quadratic decay relative to the entire family. -/
def SupercriticalExceptionalBound
    (k : ℕ) (m : ℕ → ℕ) (cLinear cQuadratic : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    ((supercriticalNonCoMultipartiteGraphFinset k n (m n)).card : ℝ) ≤
      (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) *
          Real.exp (-cLinear * (n : ℝ)) +
        (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) *
          Real.exp (-cQuadratic * (n : ℝ) ^ 2)

/-- The two-scale exceptional-family estimate forces the bad uniform
proportion to zero. -/
theorem supercriticalNonCoMultipartiteProbability_tendsto_zero_of_bound
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Ioo (gammaK k) 1)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma)
    {cLinear cQuadratic : ℝ} (hcLinear : 0 < cLinear)
    (hcQuadratic : 0 < cQuadratic)
    (hbound : SupercriticalExceptionalBound k m cLinear cQuadratic) :
    Tendsto
      (fun n ↦ supercriticalNonCoMultipartiteProbability k n (m n))
      atTop (nhds 0) := by
  have hgammaInterior : gamma ∈ Ioo (0 : ℝ) 1 :=
    ⟨(gammaK_pos hk).trans hgamma.1, hgamma.2⟩
  have hnonempty :=
    eventually_inducedStarFreeGraphFinsetWithEdges_nonempty
      k hk gamma hgammaInterior m hm
  have hupper : ∀ᶠ n in atTop,
      supercriticalNonCoMultipartiteProbability k n (m n) ≤
        Real.exp (-cLinear * (n : ℝ)) +
          Real.exp (-cQuadratic * (n : ℝ) ^ 2) := by
    filter_upwards [hbound, hnonempty] with n hn hne
    let total : ℝ := inducedStarFreeGraphCountWithEdges k n (m n)
    let good : ℝ := coMultipartiteGraphCountWithEdges (k - 1) n (m n)
    have htotal : 0 < total := by
      dsimp [total, inducedStarFreeGraphCountWithEdges]
      exact_mod_cast Finset.card_pos.mpr hne
    have hgood : good ≤ total := by
      have hdecomp :=
        inducedStarFreeGraphCountWithEdges_eq_coMultipartite_add_nonCoMultipartite
          (k := k) (n := n) (m := m n) (by omega)
      have hgoodNat : coMultipartiteGraphCountWithEdges (k - 1) n (m n) ≤
          inducedStarFreeGraphCountWithEdges k n (m n) := by omega
      dsimp [good, total]
      exact_mod_cast hgoodNat
    have hscaled :
        good * Real.exp (-cLinear * (n : ℝ)) +
            total * Real.exp (-cQuadratic * (n : ℝ) ^ 2) ≤
          total * (Real.exp (-cLinear * (n : ℝ)) +
            Real.exp (-cQuadratic * (n : ℝ) ^ 2)) := by
      have hmul :
          good * Real.exp (-cLinear * (n : ℝ)) ≤
            total * Real.exp (-cLinear * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hgood (Real.exp_pos _).le
      calc
        good * Real.exp (-cLinear * (n : ℝ)) +
            total * Real.exp (-cQuadratic * (n : ℝ) ^ 2) ≤
          total * Real.exp (-cLinear * (n : ℝ)) +
            total * Real.exp (-cQuadratic * (n : ℝ) ^ 2) :=
          add_le_add hmul le_rfl
        _ = total * (Real.exp (-cLinear * (n : ℝ)) +
            Real.exp (-cQuadratic * (n : ℝ) ^ 2)) := by ring
    unfold supercriticalNonCoMultipartiteProbability
      uniformSubfamilyProbability
    change ((supercriticalNonCoMultipartiteGraphFinset k n (m n)).card : ℝ) /
        total ≤ _
    apply (div_le_iff₀ htotal).2
    simpa [good, total, mul_comm] using hn.trans hscaled
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ by
      unfold supercriticalNonCoMultipartiteProbability
        uniformSubfamilyProbability
      positivity
  · exact hupper
  · simpa using (tendsto_exp_neg_mul_natCast_zero hcLinear).add
      (tendsto_exp_neg_mul_natCast_sq_zero hcQuadratic)

/-- The good and bad proportions are exact complements eventually, hence
vanishing of the bad side forces convergence of the good side to one. -/
theorem supercriticalCoMultipartiteProbability_tendsto_one_of_bad
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Ioo (gammaK k) 1)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma)
    (hbad : Tendsto
      (fun n ↦ supercriticalNonCoMultipartiteProbability k n (m n))
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦ supercriticalCoMultipartiteProbability k n (m n))
      atTop (nhds 1) := by
  have hgammaInterior : gamma ∈ Ioo (0 : ℝ) 1 :=
    ⟨(gammaK_pos hk).trans hgamma.1, hgamma.2⟩
  have hnonempty :=
    eventually_inducedStarFreeGraphFinsetWithEdges_nonempty
      k hk gamma hgammaInterior m hm
  have heq : ∀ᶠ n in atTop,
      supercriticalCoMultipartiteProbability k n (m n) =
        1 - supercriticalNonCoMultipartiteProbability k n (m n) := by
    filter_upwards [hnonempty] with n hne
    linarith [supercriticalCoMultipartiteProbability_add_nonCoMultipartiteProbability
      (k := k) (n := n) (m := m n) (by omega) hne]
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hsub : Tendsto
      (fun n ↦ 1 - supercriticalNonCoMultipartiteProbability k n (m n))
      atTop (nhds 1) := by simpa using hone.sub hbad
  exact hsub.congr'
    (heq.mono fun _ h ↦ h.symm)

/-- The good probability is the co-multipartite/induced-star-free count
ratio, so its convergence is also the reciprocal count comparison. -/
theorem coMultipartiteCount_div_inducedStarFreeCount_tendsto_one_of_good
    (k : ℕ) (m : ℕ → ℕ)
    (hgood : Tendsto
      (fun n ↦ supercriticalCoMultipartiteProbability k n (m n))
      atTop (nhds 1)) :
    Tendsto
      (fun n ↦
        (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) /
          (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ))
      atTop (nhds 1) := by
  simpa [supercriticalCoMultipartiteProbability,
    uniformSubfamilyProbability, supercriticalCoMultipartiteGraphFinset,
    coMultipartiteGraphCountWithEdges,
    inducedStarFreeGraphCountWithEdges] using hgood

/-- The reciprocal good/total ratio is exactly the total/good count ratio
once both exact-edge families are nonempty. -/
theorem inducedStarFreeCount_div_coMultipartiteCount_tendsto_one_of_good
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Ioo (gammaK k) 1)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma)
    (hgood : Tendsto
      (fun n ↦ supercriticalCoMultipartiteProbability k n (m n))
      atTop (nhds 1)) :
    Tendsto
      (fun n ↦
        (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) /
          (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ))
      atTop (nhds 1) := by
  have hinv : Tendsto
      (fun n ↦ (supercriticalCoMultipartiteProbability k n (m n))⁻¹)
      atTop (nhds (1 : ℝ)⁻¹) := hgood.inv₀ one_ne_zero
  have hcoPos := eventually_supercriticalCoMultipartiteGraphCountWithEdges_pos
    k hk gamma hgamma m hm
  have htotalPos :=
    eventually_inducedStarFreeGraphFinsetWithEdges_nonempty
      k hk gamma ⟨(gammaK_pos hk).trans hgamma.1, hgamma.2⟩ m hm
  have hinv' : Tendsto
      (fun n ↦ (supercriticalCoMultipartiteProbability k n (m n))⁻¹)
      atTop (nhds 1) := by simpa using hinv
  refine hinv'.congr' ?_
  filter_upwards [hcoPos, htotalPos] with n hco htotal
  unfold supercriticalCoMultipartiteProbability uniformSubfamilyProbability
  change
    (((coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) /
        (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ)))⁻¹ =
      (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) /
        (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ)
  have hcoReal : (coMultipartiteGraphCountWithEdges
      (k - 1) n (m n) : ℝ) ≠ 0 := by exact_mod_cast hco.ne'
  have htotalReal : (inducedStarFreeGraphCountWithEdges
      k n (m n) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr htotal).ne'
  field_simp

end InducedStars
