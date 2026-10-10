import InducedStars.Structure.Subcritical.AdmissibleResidualProbability
import InducedStars.Structure.Subcritical.AdmissibleResidualParameters
import InducedStars.PriorInstances

/-!
# The weighted residual estimate over all admissible graphs

Paper: `lemma:residual-matching-estimate-K1k` and
`eqn:sub-residual-weighted-sum-K1k`.
The remainder graph and roots are fixed before the sum. The residual family
contains every graph meeting the paper's stated conditions. The Janson
bound is proved uniformly over every vector in the narrow active window.
-/

noncomputable section
open Finset Filter Set
open scoped BigOperators Classical Topology
namespace InducedStars

variable {k n R₀ : ℕ} {D : SubcriticalDivision k (Fin n)}
  {eta d delta : ℝ} {B : Finset (Fin n)} {ell : ℕ}

/-- The full weighted residual estimate in natural-exponential units,
with an arbitrary nonnegative edge-weight coefficient. -/
theorem subcriticalAdmissibleResidualMatchingEstimate
    (hk : 3 ≤ k) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hR₀ : 1 ≤ R₀)
    (hell : 1 ≤ ell) (hn : 0 < n)
    (hscale : 16 ≤ subcriticalResidualMatchingLambda eta R₀ * n)
    (hdelta : delta ≤ subcriticalPaletteGap k / 2)
    (hd0 : 0 ≤ d) (hdHalf : d ≤ 1 / 2)
    (hd : d ≤ subcriticalResidualDegreeCap k eta R₀)
    (hpart : ∀ a ∈ D.retainedPartIndices eta R₀,
      eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ))
    (hroots : (B.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 2)
    (H : SubcriticalRemainderGraph D eta R₀) (m : ℕ) (Cwin epsilon w : ℝ)
    (hw : 0 ≤ w)
    (herror : subcriticalAdmissibleResidualEnumerationCoefficient d w n ≤
      subcriticalResidualMatchingConstant k eta R₀ /
        (2 * (subcriticalResidualMatchingKappa eta R₀ : ℝ))) :
    (∑ R ∈ subcriticalAdmissibleResidualFinset D eta R₀ B d ell,
      Real.exp (w * (finiteGraphEdges R).card) *
        subcriticalAdmissibleResidualSafeMaximum B H R m Cwin delta epsilon) ≤
      Real.exp (-(subcriticalResidualMatchingConstant k eta R₀ /
        (2 * (subcriticalResidualMatchingKappa eta R₀ : ℝ))) * ell * n) := by
  have hprob (R : SimpleGraph (Fin n))
      (hR : SubcriticalAdmissibleResidualGraph D eta R₀ B d ell R) :
      subcriticalAdmissibleResidualSafeMaximum B H R m Cwin delta epsilon ≤
        Real.exp (-(subcriticalResidualMatchingConstant k eta R₀ /
          subcriticalResidualMatchingKappa eta R₀) * ell * n) :=
    subcriticalAdmissibleResidualSafeMaximum_le hk J heta hetaOne hR₀ hell hscale
      hdelta hd0 hd hpart hroots H m Cwin epsilon R hR
  have hhalf :
      (subcriticalResidualMatchingConstant k eta R₀ /
        subcriticalResidualMatchingKappa eta R₀) / 2 =
      subcriticalResidualMatchingConstant k eta R₀ /
        (2 * (subcriticalResidualMatchingKappa eta R₀ : ℝ)) := by ring
  have herror' :
      subcriticalAdmissibleResidualEnumerationCoefficient d w (Fintype.card (Fin n)) ≤
        (subcriticalResidualMatchingConstant k eta R₀ /
          subcriticalResidualMatchingKappa eta R₀) / 2 := by
    simpa only [Fintype.card_fin, hhalf] using herror
  have h := subcriticalAdmissibleResidualWeightedSum_le_half D eta R₀ B ell d w
    (subcriticalResidualMatchingConstant k eta R₀ / subcriticalResidualMatchingKappa eta R₀)
    (fun R ↦ subcriticalAdmissibleResidualSafeMaximum B H R m Cwin delta epsilon)
    (by simpa only [Fintype.card_fin] using hn) hd0 hdHalf hw
    (by simpa only [Fintype.card_fin] using hprob) herror'
  simpa only [Fintype.card_fin, hhalf] using h

/-- The paper's binary-exponential matching constant. Its value depends
only on the fixed geometric parameters, independently of the edge weight. -/
def subcriticalAdmissibleResidualBinaryMatchingConstant (k : ℕ) (eta : ℝ) (R₀ : ℕ) : ℝ :=
  subcriticalResidualMatchingConstant k eta R₀ / Real.log 2

theorem subcriticalAdmissibleResidualBinaryMatchingConstant_pos
    (hk : 3 ≤ k) (heta : 0 < eta) (hR₀ : 1 ≤ R₀) :
    0 < subcriticalAdmissibleResidualBinaryMatchingConstant k eta R₀ :=
  div_pos (subcriticalResidualMatchingConstant_pos hk heta hR₀)
    (Real.log_pos (by norm_num))

/-- The literal base-two weighted estimate. Negative weights are bounded
by weight zero, so every fixed real coefficient is permitted. -/
theorem subcriticalAdmissibleResidualMatchingEstimate_baseTwo
    (hk : 3 ≤ k) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hR₀ : 1 ≤ R₀)
    (hell : 1 ≤ ell) (hn : 0 < n)
    (hscale : 16 ≤ subcriticalResidualMatchingLambda eta R₀ * n)
    (hdelta : delta ≤ subcriticalPaletteGap k / 2)
    (hd0 : 0 ≤ d) (hdHalf : d ≤ 1 / 2)
    (hd : d ≤ subcriticalResidualDegreeCap k eta R₀)
    (hpart : ∀ a ∈ D.retainedPartIndices eta R₀,
      eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ))
    (hroots : (B.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 2)
    (H : SubcriticalRemainderGraph D eta R₀) (m : ℕ) (Cwin epsilon w : ℝ)
    (herror : subcriticalAdmissibleResidualEnumerationCoefficient d
      (Real.log 2 * max w 0) n ≤ subcriticalResidualMatchingConstant k eta R₀ /
        (2 * (subcriticalResidualMatchingKappa eta R₀ : ℝ))) :
    (∑ R ∈ subcriticalAdmissibleResidualFinset D eta R₀ B d ell,
      (2 : ℝ) ^ (w * (finiteGraphEdges R).card) *
        subcriticalAdmissibleResidualSafeMaximum B H R m Cwin delta epsilon) ≤
      (2 : ℝ) ^ (-(subcriticalAdmissibleResidualBinaryMatchingConstant k eta R₀ /
        (2 * (subcriticalResidualMatchingKappa eta R₀ : ℝ))) * ell * n) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hweight (R : SimpleGraph (Fin n)) :
      (2 : ℝ) ^ (w * (finiteGraphEdges R).card) ≤
        Real.exp ((Real.log 2 * max w 0) * (finiteGraphEdges R).card) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (le_max_left w 0)
        (Nat.cast_nonneg (finiteGraphEdges R).card)) hlog.le
    simpa only [mul_assoc] using hh
  have hrate :
      Real.exp (-(subcriticalResidualMatchingConstant k eta R₀ /
        (2 * (subcriticalResidualMatchingKappa eta R₀ : ℝ))) * ell * n) =
      (2 : ℝ) ^ (-(subcriticalAdmissibleResidualBinaryMatchingConstant k eta R₀ /
        (2 * (subcriticalResidualMatchingKappa eta R₀ : ℝ))) * ell * n) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    unfold subcriticalAdmissibleResidualBinaryMatchingConstant
    have hkap : (0 : ℝ) < subcriticalResidualMatchingKappa eta R₀ := by
      exact_mod_cast (show 0 < subcriticalResidualMatchingKappa eta R₀ from
        lt_of_lt_of_le (by omega) (subcriticalResidualMatchingKappa_pos heta hR₀))
    field_simp [hlog.ne', hkap.ne']
    <;> ring
  calc
    _ ≤ ∑ R ∈ subcriticalAdmissibleResidualFinset D eta R₀ B d ell,
        Real.exp ((Real.log 2 * max w 0) * (finiteGraphEdges R).card) *
          subcriticalAdmissibleResidualSafeMaximum B H R m Cwin delta epsilon := by
      apply Finset.sum_le_sum
      intro R _
      exact mul_le_mul_of_nonneg_right (hweight R) (subcriticalFiniteMax_nonneg _ _)
    _ ≤ Real.exp (-(subcriticalResidualMatchingConstant k eta R₀ /
        (2 * (subcriticalResidualMatchingKappa eta R₀ : ℝ))) * ell * n) :=
      subcriticalAdmissibleResidualMatchingEstimate hk J heta hetaOne hR₀ hell hn hscale
        hdelta hd0 hdHalf hd hpart hroots H m Cwin epsilon (Real.log 2 * max w 0)
        (mul_nonneg hlog.le (le_max_right w 0)) herror
    _ = _ := hrate

/-- For any fixed real edge-weight coefficient, one sufficiently small
degree bound and one order threshold work for all divisions, root sets,
remainder graphs, matching sizes, and narrow windows satisfying the stated
finite geometric conditions. The matching rate is independent of the weight. -/
theorem exists_subcriticalAdmissibleResidualMatchingEstimate
    {k R₀ : ℕ} {eta : ℝ}
    (hk : 3 ≤ k) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hR₀ : 1 ≤ R₀) (w : ℝ) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ subcriticalResidualDegreeCap k eta R₀ ∧ d0 ≤ 1 / 2 ∧
      ∀ᶠ n : ℕ in atTop, ∀ d ∈ Icc (0 : ℝ) d0,
        ∀ (D : SubcriticalDivision k (Fin n)) (B : Finset (Fin n))
          (H : SubcriticalRemainderGraph D eta R₀) (m ell : ℕ) (Cwin delta epsilon : ℝ),
        1 ≤ ell → delta ≤ subcriticalPaletteGap k / 2 →
        (∀ a ∈ D.retainedPartIndices eta R₀,
          eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ)) →
        (B.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 2 →
        (∑ R ∈ subcriticalAdmissibleResidualFinset D eta R₀ B d ell,
          (2 : ℝ) ^ (w * (finiteGraphEdges R).card) *
            subcriticalAdmissibleResidualSafeMaximum B H R m Cwin delta epsilon) ≤
          (2 : ℝ) ^ (-(subcriticalAdmissibleResidualBinaryMatchingConstant k eta R₀ /
            (2 * (subcriticalResidualMatchingKappa eta R₀ : ℝ))) * ell * n) := by
  obtain ⟨d0, hd0, hdCap, hdHalf, hreserve⟩ :=
    exists_subcriticalAdmissibleResidualDegreeReserve hk heta hR₀ (Real.log 2 * max w 0)
  have hlambda := subcriticalResidualMatchingLambda_pos heta hR₀
  have hlarge (t : ℝ) : ∀ᶠ n : ℕ in atTop, t ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop t)
  refine ⟨d0, hd0, hdCap, hdHalf, ?_⟩
  filter_upwards [hreserve, hlarge (16 / subcriticalResidualMatchingLambda eta R₀),
    hlarge 1] with n hnReserve hnScale hnOne
  intro d hd D B H m ell Cwin delta epsilon hell hdelta hpart hroots
  have hn : 0 < n := by
    have hnReal : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnOne
    exact_mod_cast hnReal
  have hscale : 16 ≤ subcriticalResidualMatchingLambda eta R₀ * n := by
    simpa only [mul_comm] using (div_le_iff₀ hlambda).mp hnScale
  exact subcriticalAdmissibleResidualMatchingEstimate_baseTwo hk J heta hetaOne hR₀
    hell hn hscale hdelta hd.1 (hd.2.trans hdHalf) (hd.2.trans hdCap)
    hpart hroots H m Cwin epsilon w (hnReserve d hd)


/-- For any fixed real edge weight, the all-admissible residual sum has
the paper's exponential matching penalty. The rate is independent of the
weight, and the order threshold is uniform over the finite geometry. -/
theorem subcriticalResidualMatchingAllAdmissible
    {k R₀ : ℕ} {eta : ℝ}
    (hk : 3 ≤ k)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hR₀ : 1 ≤ R₀) (w : ℝ) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ subcriticalResidualDegreeCap k eta R₀ ∧ d0 ≤ 1 / 2 ∧
      ∀ᶠ n : ℕ in atTop, ∀ d ∈ Icc (0 : ℝ) d0,
        ∀ (D : SubcriticalDivision k (Fin n)) (B : Finset (Fin n))
          (H : SubcriticalRemainderGraph D eta R₀) (m ell : ℕ) (Cwin delta epsilon : ℝ),
        1 ≤ ell → delta ≤ subcriticalPaletteGap k / 2 →
        (∀ a ∈ D.retainedPartIndices eta R₀,
          eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ)) →
        (B.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 2 →
        (∑ R ∈ subcriticalAdmissibleResidualFinset D eta R₀ B d ell,
          (2 : ℝ) ^ (w * (finiteGraphEdges R).card) *
            subcriticalAdmissibleResidualSafeMaximum B H R m Cwin delta epsilon) ≤
          (2 : ℝ) ^ (-(subcriticalAdmissibleResidualBinaryMatchingConstant k eta R₀ /
            (2 * (subcriticalResidualMatchingKappa eta R₀ : ℝ))) * ell * n) :=
  exists_subcriticalAdmissibleResidualMatchingEstimate hk
    PriorInstances.principalJansonInput heta hetaOne hR₀ w

/-- The zero-matching case of the literal binary weighted sum. -/
theorem subcriticalAdmissibleResidualSafetySum_zero_baseTwo
    (B : Finset (Fin n)) (H : SubcriticalRemainderGraph D eta R₀)
    (m : ℕ) (Cwin delta epsilon d w : ℝ) (hd : 0 ≤ d)
    (hne : (retainedNarrowEdgeCountWindow D eta R₀ m Cwin delta epsilon).Nonempty) :
    (∑ R ∈ subcriticalAdmissibleResidualFinset D eta R₀ B d 0,
      (2 : ℝ) ^ (w * (finiteGraphEdges R).card) *
        subcriticalAdmissibleResidualSafeMaximum B H R m Cwin delta epsilon) = 1 := by
  rw [subcriticalAdmissibleResidualFinset_zero D eta R₀ B d hd]
  have hempty : finiteGraphEdges (⊥ : SimpleGraph (Fin n)) = ∅ := by
    ext e
    simp only [mem_finiteGraphEdges, Finset.notMem_empty, SimpleGraph.edgeSet_bot,
      Set.mem_empty_iff_false]
  simp [hempty, subcriticalAdmissibleResidualSafeMaximum_bot B H m Cwin delta epsilon hne]

end InducedStars
