import InducedStars.Structure.Supercritical.Conclusion
import InducedStars.Structure.Critical.AlmostAll
import InducedStars.Structure.Subcritical.AlmostAll
import InducedStars.Structure.Gnp.Main
import InducedStars.C4.AlmostAll

/-!
# Paper-facing typical-structure theorems

This conjunction preserves the individual quantifiers: arbitrary asymptotic
edge sequences off the transition, and the exact critical floor edge sequence
with an O(log n) remainder at the transition. The logarithmic cutoff uses
the paper's base-two convention.
The imports also expose the complete conditioned-binomial theorem and the
separate induced-C4 almost-all split theorem without changing this interface.
-/

noncomputable section
open Filter Set Topology
namespace InducedStars

/-- Paper: Theorem `thm:main-almostall`, all three clauses. -/
theorem inducedStarAlmostAll (k : ℕ) (hk : 3 ≤ k) :
    (∀ gamma : ℝ, gamma ∈ Ioo (gammaK k) 1 →
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
        Tendsto (fun n ↦ supercriticalCoMultipartiteProbability k n (m n)) atTop (𝓝 1)) ∧
    (∃ L : ℝ, 0 < L ∧
      Tendsto (fun n ↦ criticalStructuredProbability k n
        (Nat.ceil (L * Real.logb 2 (n : ℝ)))) atTop (𝓝 1)) ∧
    (∀ gamma : ℝ, gamma ∈ Ioo (0 : ℝ) (gammaK k) →
      ∃ cLower : ℝ, 0 < cLower ∧ ∀ xi : ℝ, 0 < xi →
        ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
          Tendsto (fun n ↦ subcriticalStructuredProbability k gamma cLower xi n (m n))
            atTop (𝓝 1)) :=
  ⟨fun gamma hgamma m hm ↦ inducedStarSupercriticalAlmostAllCoMultipartite k hk gamma hgamma m hm,
    inducedStarCriticalAlmostAll k hk, fun _ hgamma ↦ inducedStarSubcriticalAlmostAll k hk hgamma⟩

end InducedStars
