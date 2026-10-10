import InducedStars.Structure.Subcritical.CleanRetainedMultiplicity
import InducedStars.Structure.Subcritical.DistinguishedFeasibleGeometry
import InducedStars.Structure.Subcritical.DistinguishedDenominatorShift

/-!
# A uniform half of the clean choices have identifiable retained support

Exact feasible edge levels, not compatibility alone, give the part
balance used by the fixed-cell unique-cover estimate. The threshold is
uniform in all keys, remainders, profiles and graph orders.
-/

noncomputable section
open Filter Finset Set Topology
open scoped Classical BigOperators
namespace InducedStars

theorem eventually_retainedKeyClean_le_two_good {k R₀ : ℕ} (hk : 3 ≤ k)
    {mu eta delta : ℝ} (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (heta : 0 ≤ eta) (hd : 0 < delta) (hsize : eta + delta ≤ mu)
    (hR : k - 1 ≤ R₀) (hdmu : delta ≤ mu / 2)
    (hsmall : delta ≤ (1 - pK k) * (mu / (4 * (k - 1 : ℕ)))^2 / 10)
    (hdBand : delta ≤ subcriticalReferenceShiftBand k / 2)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m (gammaK k * mu^2)) :
    ∀ᶠ n : ℕ in atTop, ∀ K ∈ compatibleRetainedKeys k n
      (oneBlockSequence k hk mu hmu hmu1) eta delta R₀,
      retainedKeyCleanPartitionFunction K eta (m n) delta ≤
        2 * (retainedKeyGoodCleanGraphFinset K eta R₀ (m n) delta).card := by
  let u := (pK k + 1) / 2
  have hp := pK_mem_Ioo (by omega : 2 ≤ k)
  have hu : 0 < u := by dsimp [u]; linarith [hp.1]
  have hu1 : u < 1 := by dsimp [u]; linarith [hp.2]
  let c := -Real.log u
  have hc : 0 < c := neg_pos.mpr (Real.log_neg hu hu1)
  have hexc : Real.exp (-c) = u := by
    simp only [c, neg_neg, Real.exp_log hu]
  obtain ⟨N, hN⟩ := exists_oneCore_goodSample_threshold_uniform hk hc
  let a := mu / (4 * (k - 1 : ℕ))
  have ha : 0 < a := by
    have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
    dsimp [a]; positivity
  have hscale : ∀ᶠ n : ℕ in atTop, (N : ℝ) ≤ a * n :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop ha).eventually (eventually_ge_atTop (N : ℝ))
  filter_upwards [eventually_compatibleRetainedKeys_part_lower hk hmu hmu1 heta hd hsize
    hR hdmu hsmall m hm, hscale] with n hgeom hscale
  intro K hK
  by_cases hz : retainedKeyCleanPartitionFunction K eta (m n) delta = 0
  · rw [hz]; exact Nat.zero_le _
  have hzpos : 0 < retainedKeyCleanPartitionFunction K eta (m n) delta := Nat.pos_of_ne_zero hz
  obtain ⟨b, hb, hbpos⟩ := Finset.sum_pos_iff.mp hzpos
  have hZ : 0 < retainedKeyPartitionFunction K (m n) delta (b : ℤ) :=
    Nat.pos_of_mul_pos_left hbpos
  obtain ⟨E, heq, hcount, hcore, hpart⟩ := hgeom K hK b hZ
  obtain ⟨D, hD⟩ := E.exists_ofSupercritical_of_one_complete hk hcount hcore
  subst E
  have hnorm : retainedKey (SubcriticalDivision.ofSupercritical hk D) eta R₀ = K := by
    obtain ⟨A, _, hA⟩ := mem_compatibleRetainedKeys.mp hK
    exact (retainedKey_some_idempotent (hA.trans heq)).trans heq.symm
  have hret : (SubcriticalDivision.ofSupercritical hk D).retainedComponentIndices eta R₀ =
      Finset.univ := by
    obtain ⟨A, _, hA⟩ := mem_compatibleRetainedKeys.mp hK
    exact retainedKey_some_retains_all (hA.trans heq)
  have hpart' : ∀ i : Fin (k - 1),
      D.support.card ≤ 2 * (k - 1) * (D.parts i).card ∧
        a * n ≤ ((D.parts i).card : ℝ) := by
    intro i
    have hh := hpart ⟨⟨0, by change 0 < 1; omega⟩,i⟩
    rw [SubcriticalDivision.ofSupercritical_support] at hh
    exact hh
  have hNs : N ≤ D.support.card := by
    let i : Fin (k - 1) := ⟨0, by omega⟩
    have hh : (N : ℝ) ≤ D.support.card := hscale.trans
      ((hpart' i).2.trans (by exact_mod_cast Finset.card_le_card (D.part_subset_support i)))
    exact_mod_cast hh
  rw [← hnorm, retainedKeyCleanPartitionFunction_retainedKey]
  have hsupport : (retainedKey (SubcriticalDivision.ofSupercritical hk D) eta R₀).support =
      D.support := by rw [hnorm, heq]; exact SubcriticalDivision.ofSupercritical_support hk D
  change cleanRetainedPartitionFunction (SubcriticalDivision.ofSupercritical hk D)
      eta R₀ (m n) delta ≤ 2 * _
  have hgood := cleanRetainedPartitionFunction_le_mul_good
    (SubcriticalDivision.ofSupercritical hk D) eta R₀ (m n) delta
    (fun G ↦ SubcriticalGoodCleanSupport k G D.support) 2 ?_
  · simpa only [retainedKeyGoodCleanGraphFinset, retainedKeyCleanModelGraphFinset,
      hnorm, heq, Option.elim_some, SubcriticalRetainedKey.support,
      SubcriticalDivision.ofSupercritical_support] using hgood
  · intro b hb H hH v hv
    apply hN (Fin n) D hNs hret v H (fun i ↦ (hpart' i).1)
    intro e
    have hvd := (mem_retainedEdgeCountLevel.mp hv).2 e
    have hbnd := subcriticalReferenceShiftBand_bounds hk
    constructor
    · have hdl : 4 * delta ≤ pK k := by linarith [hbnd.2.2.1]
      linarith [hp.1]
    · rw [hexc]
      dsimp [u]
      have hdu : 4 * delta ≤ 1 - pK k := by linarith [hbnd.2.2.2]
      linarith

end InducedStars
