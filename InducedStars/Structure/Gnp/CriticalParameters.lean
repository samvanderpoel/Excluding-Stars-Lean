import InducedStars.Structure.Gnp.GroupedFinite
import InducedStars.Structure.Gnp.RetainedMass

/-!
# One hierarchy for the critical weighted comparison

The separation from zero supplies the positive lower edge-density parameter.
The tail reserve concerns omitted quadratic mass, and the finite
counting theorem sums retained keys. The radius is selected before
the candidate representation, including representations at the endpoint.
-/

noncomputable section
open Filter Set
namespace InducedStars

structure GnpCriticalComparisonParameters (k : ℕ) (hk : 3 ≤ k)
    (separation omega : ℝ) where
  eta : ℝ
  theta : ℝ
  alpha : ℝ
  delta : ℝ
  epsilon : ℝ
  tau : ℝ
  R₀ : ℕ
  eta_pos : 0 < eta
  eta_one : eta ≤ 1
  delta_pos : 0 < delta
  delta_eta : delta ≤ eta
  order_one : 1 ≤ R₀
  tail_reserve : 2 * eta + 1 / ((R₀ + 1 : ℕ) : ℝ) ≤
    separation / (2 * (1 + ((k - 2 : ℕ) : ℝ) * pK k))
  mass_reserve : delta ≤ eta *
    (separation / (2 * (1 + ((k - 2 : ℕ) : ℝ) * pK k)))
  sparse_reserve : subcriticalSparseSideConstant k * eta ≤ omega / 4
  tau_pos : 0 < tau
  tau_separation : tau ≤ separation / 2
  tau_omega : tau ≤ omega / 4
  aggregation : ∀ᶠ n : ℕ in atTop,
    SubcriticalAggregationParameters k separation eta R₀ theta alpha delta epsilon n
  grouped : ∀ L : AdmissibleBlockSequence k,
    ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0,
      ∀ {n : ℕ} (hn : n0 ≤ n) (m : ℕ), separation / 8 * (n : ℝ)^2 ≤ m →
        SubcriticalGroupedCandidateUpperBounds hk (hn0.trans hn) L R₀ m eta delta tau
          (subcriticalAggregationConstant k eta R₀)

/-- All critical weighted reserves are imposed while selecting the existing
nested hierarchy; separately chosen parameter tuples are never combined. -/
theorem exists_gnpCriticalComparisonParameters {k : ℕ} (hk : 3 ≤ k)
    {separation omega : ℝ} (hseparation : 0 < separation) (homega : 0 < omega) :
    Nonempty (GnpCriticalComparisonParameters k hk separation omega) := by
  let A := 1 + ((k - 2 : ℕ) : ℝ) * pK k
  let C := subcriticalSparseSideConstant k
  have hA : 0 < A := by
    have hp := (pK_mem_Ioo (show 2 ≤ k by omega)).1
    dsimp [A]
    positivity
  have hC : 0 < C := by dsimp [C, subcriticalSparseSideConstant]; positivity
  let etaMax := min (separation / (6 * A)) (omega / (4 * C))
  have heMax : 0 < etaMax := by dsimp [etaMax]; positivity
  obtain ⟨eta, heta, hecap, _, heone, heres, R₀, hR, _, hinv⟩ :=
    exists_subcriticalAggregationOuterParameters k hseparation
      (by norm_num : (0 : ℝ) < 1) heMax (k - 1)
  have heSep : eta ≤ separation / (6 * A) := hecap.trans (min_le_left _ _)
  have heSparse : C * eta ≤ omega / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp
      (hecap.trans (min_le_right _ _))
    nlinarith
  have hRpos : (0 : ℝ) < R₀ := by exact_mod_cast (show 0 < R₀ by omega)
  have hinv' : 1 / ((R₀ + 1 : ℕ) : ℝ) ≤ eta := by
    apply le_trans _ hinv
    apply one_div_le_one_div_of_le hRpos
    exact_mod_cast (Nat.le_succ R₀)
  have htail : 2 * eta + 1 / ((R₀ + 1 : ℕ) : ℝ) ≤ separation / (2 * A) := by
    have h := (le_div_iff₀ (by positivity : 0 < 6 * A)).mp heSep
    apply (le_div_iff₀ (by positivity : 0 < 2 * A)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hinv' hA.le]
  let deltaMax := min eta (eta * (separation / (2 * A)))
  have hdMax : 0 < deltaMax := by dsimp [deltaMax]; positivity
  obtain ⟨theta, _, _, ha⟩ := exists_subcriticalAggregationParameters
    hk hseparation heta hR hinv heres 1 (by norm_num)
  obtain ⟨alpha, _, _, hd⟩ := ha 1 (by norm_num)
  obtain ⟨delta, hdelta, hdcap, he⟩ := hd deltaMax hdMax
  obtain ⟨epsilon, _, _, hparameters⟩ := he 1 (by norm_num)
  obtain ⟨tau, htau, htcap, hgrouped⟩ := gnpGroupedUpperBound_of_eventual_parameters
    k hk separation R₀ 1 eta theta alpha delta epsilon
    (min (separation / 2) (omega / 4)) (by norm_num) le_rfl heone
    (by positivity) hparameters
  exact ⟨{
    eta := eta, theta := theta, alpha := alpha, delta := delta,
    epsilon := epsilon, tau := tau, R₀ := R₀,
    eta_pos := heta, eta_one := heone, delta_pos := hdelta,
    delta_eta := hdcap.trans (min_le_left _ _), order_one := hR,
    tail_reserve := htail, mass_reserve := hdcap.trans (min_le_right _ _),
    sparse_reserve := heSparse, tau_pos := htau,
    tau_separation := htcap.trans (min_le_left _ _),
    tau_omega := htcap.trans (min_le_right _ _),
    aggregation := hparameters, grouped := hgrouped }⟩

end InducedStars
