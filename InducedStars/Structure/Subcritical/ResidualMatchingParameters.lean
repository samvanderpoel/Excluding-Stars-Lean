import InducedStars.Structure.Subcritical.ResidualMatchingScalars
import InducedStars.Structure.Subcritical.ResidualParameterFeasibility

/-!
# Finite numerical conditions for residual matching

The matching rate and the geometric degree cap are fixed by `k,eta,R₀`
before choosing the four small parameters. The existence theorem preserves
arbitrary earlier positive upper bounds at every stage of that hierarchy.
The entropy reserve is the locally proved residual enumeration cost;
all exponential units are natural.
-/

noncomputable section
open Filter
open scoped Topology

namespace InducedStars

/-- Explicit finite scalar reserves for the residual matching argument.
No candidate, probability, or graph-count assertion is a field. -/
structure SubcriticalResidualMatchingConditions
    (k : ℕ) (eta : ℝ) (R₀ : ℕ) (theta alpha delta epsilon : ℝ) (n : ℕ) : Prop where
  alpha_pos : 0 < alpha
  theta_pos : 0 < theta
  delta_pos : 0 < delta
  epsilon_pos : 0 < epsilon
  theta_cutoff : theta ≤ eta / (2 * (R₀ : ℝ))
  degree_half : subcriticalResidualDegreeCoefficient k alpha theta ≤ 1 / 2
  degree_cap : subcriticalResidualDegreeCoefficient k alpha theta ≤
    subcriticalResidualDegreeCap k eta R₀
  delta_palette : delta ≤ subcriticalPaletteGap k / 2
  epsilon_theta : epsilon ≤ theta ^ 2
  roots_room : subcriticalProfileRootFraction alpha theta epsilon ≤
    subcriticalResidualMatchingLambda eta R₀ / 2
  enumeration_error : subcriticalResidualEnumerationCoefficient k alpha theta n ≤
    subcriticalResidualMatchingConstant k eta R₀ /
      (2 * (subcriticalResidualMatchingKappa eta R₀ : ℝ))
  matching_room : 16 ≤ subcriticalResidualMatchingLambda eta R₀ * n
  sparse_scale : 1 ≤ theta * n
  fallback_order : subcriticalResidualMatchingConstant k eta R₀ /
    (subcriticalResidualMatchingKappa eta R₀ : ℝ) ≤ n + 1
  order_pos : 0 < n

/-- Genuine nested parameter feasibility. The positive matching rate,
degree cap, palette gap, and room scale depend only on `k,eta,R₀`.
Theta is selected before the arbitrary alpha cap, and each later parameter
likewise accepts its cap only at its own stage. The finite order is selected
last. The weighted residual count has this same parameter order. -/
theorem exists_subcriticalResidualMatchingConditions
    {k R₀ : ℕ} {eta : ℝ} (hk : 3 ≤ k) (heta : 0 < eta) (hR : 1 ≤ R₀)
    (thetaMax : ℝ) (hthetaMax : 0 < thetaMax) :
    ∃ theta : ℝ, 0 < theta ∧ theta ≤ thetaMax ∧
      ∀ alphaMax : ℝ, 0 < alphaMax →
      ∃ alpha : ℝ, 0 < alpha ∧ alpha ≤ alphaMax ∧
        ∀ deltaMax : ℝ, 0 < deltaMax →
        ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaMax ∧
          ∀ epsilonMax : ℝ, 0 < epsilonMax →
          ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ epsilonMax ∧
            ∀ᶠ n : ℕ in atTop,
              SubcriticalResidualMatchingConditions k eta R₀ theta alpha delta epsilon n := by
  have hRpos : (0 : ℝ) < R₀ := by exact_mod_cast (show 0 < R₀ by omega)
  have hkap : (0 : ℝ) < subcriticalResidualMatchingKappa eta R₀ := by
    have hh := subcriticalResidualMatchingKappa_pos heta hR
    exact_mod_cast (show 0 < subcriticalResidualMatchingKappa eta R₀ by omega)
  have hc : 0 < subcriticalResidualMatchingConstant k eta R₀ /
      (subcriticalResidualMatchingKappa eta R₀ : ℝ) :=
    div_pos (subcriticalResidualMatchingConstant_pos hk heta hR) hkap
  have htMax : 0 < min thetaMax (eta / (2 * (R₀ : ℝ))) := by positivity
  obtain ⟨theta, ht, htBound, hAlpha⟩ :=
    exists_subcriticalResidualParameterHierarchy k
      (subcriticalResidualMatchingConstant k eta R₀ /
        (subcriticalResidualMatchingKappa eta R₀ : ℝ))
      (subcriticalResidualDegreeCap k eta R₀)
      (subcriticalResidualMatchingLambda eta R₀)
      (subcriticalPaletteGap k) (min thetaMax (eta / (2 * (R₀ : ℝ))))
      hc (subcriticalResidualDegreeCap_pos k heta hR)
      (subcriticalResidualMatchingLambda_pos heta hR)
      (subcriticalPaletteGap_pos hk) htMax
  have htCap := (le_min_iff.mp htBound).1
  have htCutoff := (le_min_iff.mp htBound).2
  refine ⟨theta, ht, htCap, ?_⟩
  intro alphaMax haMax
  obtain ⟨alpha, ha, haCap, hDegree, _, hDelta⟩ := hAlpha alphaMax haMax
  refine ⟨alpha, ha, haCap, ?_⟩
  intro deltaMax hdMax
  obtain ⟨delta, hd, hdCap, hdPalette, hEpsilon⟩ := hDelta deltaMax hdMax
  refine ⟨delta, hd, hdCap, ?_⟩
  intro epsilonMax heMax
  obtain ⟨epsilon, he, heCap, heTheta, heRoots, hn⟩ := hEpsilon epsilonMax heMax
  refine ⟨epsilon, he, heCap, ?_⟩
  filter_upwards [hn] with n hn
  refine
    { alpha_pos := ha
      theta_pos := ht
      delta_pos := hd
      epsilon_pos := he
      theta_cutoff := htCutoff
      degree_half := (le_min_iff.mp hDegree).1
      degree_cap := (le_min_iff.mp hDegree).2
      delta_palette := hdPalette
      epsilon_theta := heTheta
      roots_room := heRoots
      enumeration_error := ?_
      matching_room := hn.2.1
      sparse_scale := hn.2.2.1
      fallback_order := hn.2.2.2.1
      order_pos := hn.2.2.2.2 }
  convert hn.1 using 1 <;> ring

end InducedStars
