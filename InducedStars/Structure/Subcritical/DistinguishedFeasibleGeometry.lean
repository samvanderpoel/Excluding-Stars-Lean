import InducedStars.Structure.Subcritical.DistinguishedPartBalance
import InducedStars.Structure.Subcritical.CleanMultiplicityGeometry
import InducedStars.Structure.Subcritical.RetainedEntropyComparison
import InducedStars.Structure.Subcritical.DistinguishedFiniteReference

/-!
# Uniform geometry of feasible distinguished keys

Compatibility identifies the retained component, while positive
partition function supplies an actual wide-level count vector. The latter
is essential to derive individual part-size control.
-/

noncomputable section
open Finset Set Filter Topology
open scoped Classical BigOperators
namespace InducedStars

theorem retainedKeySomeVector_mem_level {k n m : ℕ}
    (D : SubcriticalDivision k (Fin n)) {delta : ℝ} {u : ℤ}
    {v : RetainedKeyEdgeCountVector (some D)}
    (hv : v ∈ retainedKeyEdgeCountLevel (some D) m delta u) :
    retainedKeySomeVector D v ∈ retainedEdgeCountLevel D 0 (Fintype.card (Fin n)) m delta u := by
  have h := (Finset.mem_filter.mp hv).2
  apply mem_retainedEdgeCountLevel.mpr
  constructor
  · have hc : SubcriticalRetainedKey.cliqueCapacity (some D : SubcriticalRetainedKey k (Fin n)) =
        retainedCliqueCapacity D 0 (Fintype.card (Fin n)) := retainedCliquePotentialEdges_card D 0 _
    simpa only [hc, retainedKeySomeVector_total] using h.1
  · intro e
    simpa only [retainedEdgeCountDensity, retainedKeySomeVector,
      retainedKeyEdgeCountDensity, SubcriticalRetainedKey.activeCapacity,
      SubcriticalRetainedKey.activeEdges, retainedActivePotentialEdges_card] using h.2 e

/-- Every positive counting term has the support-relative part lower bound
used by the finite unique-cover argument, as well as a uniform linear bound. -/
theorem compatibleRetainedKeys_part_lower_of_positive_level {k n m b R₀ : ℕ}
    (hk : 3 ≤ k) (hn : 1 ≤ n) {mu eta delta : ℝ}
    (hmu : 0 < mu) (hmu1 : mu ≤ 1) (heta : 0 ≤ eta) (hd : 0 ≤ delta)
    (hsize : eta + delta ≤ mu) (horder : k - 1 ≤ R₀) (hdmu : delta ≤ mu / 2)
    (hm : 2 * (m : ℝ) ≤ gammaK k * mu^2 * (n : ℝ)^2 + delta * (n : ℝ)^2)
    (hlarge : 5 * delta * (n : ℝ)^2 + n ≤
      (1 - pK k) * (mu * n / (4 * (k - 1 : ℕ)))^2)
    {K : SubcriticalRetainedKey k (Fin n)}
    (hK : K ∈ compatibleRetainedKeys k n
      (oneBlockSequence k hk mu hmu hmu1) eta delta R₀)
    (hZ : 0 < retainedKeyPartitionFunction K m delta (b : ℤ)) :
    ∃ E : SubcriticalDivision k (Fin n), K = some E ∧ E.componentCount = 1 ∧
      (∀ i, E.core i = RegularBlockCore.complete k hk) ∧
      ∀ a : E.PartIndex,
        E.support.card ≤ 2 * (k - 1) * (E.part a).card ∧
        mu / (4 * (k - 1 : ℕ)) * n ≤ ((E.part a).card : ℝ) := by
  obtain ⟨E, rfl, hcount, hcore, hs⟩ := compatibleRetainedKeys_oneBlock_geometry
    hk hmu hmu1 heta hd hsize horder hK
  have hne : (retainedKeyEdgeCountLevel (some E) m delta (b : ℤ)).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [retainedKeyPartitionFunction, he, Finset.sum_empty] at hZ
    omega
  obtain ⟨v, hv⟩ := hne
  have hp := oneCompleteCore_part_lower_of_level hk hn E hcount hcore hmu hmu1 hd
    hdmu hs hm hlarge (retainedKeySomeVector E v) (retainedKeySomeVector_mem_level E hv)
  refine ⟨E, rfl, hcount, hcore, ?_⟩
  intro a
  refine ⟨?_, (hp a).2⟩
  have hr : (0 : ℝ) < 2 * (k - 1 : ℕ) := by
    have : 0 < k - 1 := by omega
    positivity
  have h := (div_le_iff₀ hr).mp (hp a).1
  have hn : E.support.card ≤ (E.part a).card * (2 * (k - 1)) := by exact_mod_cast h
  simpa only [mul_comm] using hn

/-- A displayed scalar reserve supplies the order threshold uniformly over
all divisions, vectors and edge counts. -/
theorem eventually_oneCompleteCore_part_balance_reserve {k : ℕ} (hk : 3 ≤ k)
    {mu delta : ℝ} (hmu : 0 < mu) (hd : 0 ≤ delta)
    (hsmall : delta ≤ (1 - pK k) * (mu / (4 * (k - 1 : ℕ)))^2 / 10) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 5 * delta * (n : ℝ)^2 + n ≤
      (1 - pK k) * (mu * n / (4 * (k - 1 : ℕ)))^2 := by
  let c := (1 - pK k) * (mu / (4 * (k - 1 : ℕ)))^2
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hp : 0 < 1 - pK k := sub_pos.mpr (pK_lt_one (by omega))
  have hc : 0 < c := by dsimp [c]; positivity
  filter_upwards [eventually_ge_atTop (max 1 (Nat.ceil (2 / c)))] with n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 2 / c ≤ (n : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right 1 (Nat.ceil (2 / c))).trans hn)
  have hNc := (div_le_iff₀ hc).mp hN
  have hmul := mul_le_mul_of_nonneg_right hNc hnR.le
  have hsm := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (n : ℝ))
  refine ⟨hn1, ?_⟩
  have heq : (1 - pK k) * (mu * n / (4 * (k - 1 : ℕ)))^2 = c * (n : ℝ)^2 := by
    dsimp [c]
    ring
  rw [heq]
  change delta ≤ c / 10 at hsmall
  change delta * (n : ℝ)^2 ≤ c / 10 * (n : ℝ)^2 at hsm
  nlinarith

theorem eventually_subcritical_edge_upper {gamma delta : ℝ}
    (hg : 0 ≤ gamma) (hd : 0 < delta)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n : ℕ in atTop,
      2 * (m n : ℝ) ≤ gamma * (n : ℝ)^2 + delta * (n : ℝ)^2 := by
  have hlim := hm.eventually (Iio_mem_nhds (show gamma < gamma + delta by linarith))
  filter_upwards [hlim, eventually_ge_atTop 2] with n hn hn2
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hN : (0 : ℝ) < (n.choose 2 : ℝ) := by exact_mod_cast Nat.choose_pos hn2
  have h := (div_lt_iff₀ hN).mp hn
  rw [Nat.cast_choose_two] at h
  nlinarith [mul_nonneg (show 0 ≤ gamma + delta by linarith) (show (0 : ℝ) ≤ n by positivity)]

/-- The part geometry follows eventually for every feasible compatible key,
uniformly in the key and the remainder edge count. -/
theorem eventually_compatibleRetainedKeys_part_lower {k R₀ : ℕ} (hk : 3 ≤ k)
    {mu eta delta : ℝ} (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (heta : 0 ≤ eta) (hd : 0 < delta) (hsize : eta + delta ≤ mu)
    (horder : k - 1 ≤ R₀) (hdmu : delta ≤ mu / 2)
    (hsmall : delta ≤ (1 - pK k) * (mu / (4 * (k - 1 : ℕ)))^2 / 10)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m (gammaK k * mu^2)) :
    ∀ᶠ n : ℕ in atTop, ∀ K : SubcriticalRetainedKey k (Fin n),
      K ∈ compatibleRetainedKeys k n (oneBlockSequence k hk mu hmu hmu1) eta delta R₀ →
      ∀ b : ℕ, 0 < retainedKeyPartitionFunction K (m n) delta (b : ℤ) →
      ∃ E : SubcriticalDivision k (Fin n), K = some E ∧ E.componentCount = 1 ∧
        (∀ i, E.core i = RegularBlockCore.complete k hk) ∧
        ∀ a : E.PartIndex,
          E.support.card ≤ 2 * (k - 1) * (E.part a).card ∧
          mu / (4 * (k - 1 : ℕ)) * n ≤ ((E.part a).card : ℝ) := by
  have hg : 0 ≤ gammaK k * mu^2 := mul_nonneg (gammaK_pos hk).le (sq_nonneg mu)
  filter_upwards [eventually_oneCompleteCore_part_balance_reserve hk hmu hd.le hsmall,
    eventually_subcritical_edge_upper hg hd m hm] with n hn hm'
  intro K hK b hZ
  exact compatibleRetainedKeys_part_lower_of_positive_level hk hn.1 hmu hmu1 heta
    hd.le hsize horder hdmu hm' hn.2 hK hZ

end InducedStars
