import DenseGraph.Asymptotics.SequentialUniformity
import InducedStars.Asymptotics.GnpDensity
import InducedStars.Structure.Supercritical.Conclusion

/-!
# Local uniformity of the supercritical fixed-density theorem

The completed exact-edge theorem applies to every sequence with prescribed
limiting density.  The diagonal extension lemma converts that assertion into
a fixed local density window for each error tolerance.  This is the uniformity
needed to mix exact-edge laws in the conditioned `G(n,p)` model.
-/

open Filter Set
open scoped Topology

namespace InducedStars

/-- Near any strictly supercritical density, the exact-edge probability of
failing to be co-`(k - 1)`-partite is uniformly small for all sufficiently
large graph orders.  The density window may depend on the requested error
tolerance; no uniform convergence on an arbitrary fixed interval is asserted. -/
theorem exists_supercriticalNonCoMultipartiteProbability_densityWindow
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ioo (gammaK k) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m : ℕ,
      m ≤ completeEdgeCount n →
      |(m : ℝ) / (completeEdgeCount n : ℝ) - γ| < δ →
      supercriticalNonCoMultipartiteProbability k n m < ε := by
  have hγunit : γ ∈ Icc (0 : ℝ) 1 :=
    ⟨(gammaK_pos hk).le.trans hγ.1.le, hγ.2.le⟩
  apply DenseGraph.exists_densityWindow_of_tendsto_along_feasible_sequences
    (fun n m : ℕ ↦ m ≤ completeEdgeCount n)
    (fun n m : ℕ ↦ (m : ℝ) / (completeEdgeCount n : ℝ))
    (supercriticalNonCoMultipartiteProbability k)
    (floorEdgeCountSequence γ)
    (floorEdgeCountSequence_le_completeEdgeCount hγunit)
    (floorEdgeCountSequence_hasAsymptoticEdgeDensity hγunit)
    (fun m _ hm ↦
      supercriticalNonCoMultipartiteProbability_tendsto_zero k hk γ hγ m hm) hε

end InducedStars
