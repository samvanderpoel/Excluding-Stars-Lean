import InducedStars.Structure.Subcritical.CleanRetainedFraction

/-!
# The constant-factor clean retained-key comparison

Paper: lemma:canonical-clean-lower-K1k.
The multiplicity is at most twice (k-1)!, independent of n. The comparison
is to the total exact-edge family, so no cut-radius selection is circular.
-/

noncomputable section
open Filter Finset Set Topology
open scoped Classical BigOperators
namespace InducedStars

theorem retainedKeyGoodCleanGraphFinset_subset_total
    {k n m R₀ : ℕ} (hk : 3 ≤ k) (K : SubcriticalRetainedKey k (Fin n))
    (eta delta : ℝ) :
    retainedKeyGoodCleanGraphFinset K eta R₀ m delta ⊆
      inducedStarFreeGraphFinsetWithEdges k n m := by
  intro G hG
  have hmodel := (Finset.mem_filter.mp hG).1
  cases K with
  | none => exact False.elim (Finset.notMem_empty _ hmodel)
  | some E =>
    have hf := subcriticalCleanModelGraphFinset_inducedFree hk hmodel
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hmodel
    apply mem_inducedFreeGraphFinsetWithEdges_iff_finiteGraphEdges.mpr
    exact ⟨hf, hd ▸ d.graph_card⟩

/-- A nonempty model family supplies a positive exact wide level, and hence
the already proved feasible-key part geometry. -/
theorem compatibleRetainedGoodKey_geometry {k n m R₀ : ℕ} (hk : 3 ≤ k)
    {mu eta delta : ℝ} (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (hgeom : ∀ K : SubcriticalRetainedKey k (Fin n),
      K ∈ compatibleRetainedKeys k n (oneBlockSequence k hk mu hmu hmu1) eta delta R₀ →
      ∀ b : ℕ, 0 < retainedKeyPartitionFunction K m delta (b : ℤ) →
      ∃ E : SubcriticalDivision k (Fin n), K = some E ∧ E.componentCount = 1 ∧
        (∀ i, E.core i = RegularBlockCore.complete k hk) ∧
        ∀ a : E.PartIndex, E.support.card ≤ 2 * (k - 1) * (E.part a).card ∧
          mu / (4 * (k - 1 : ℕ)) * n ≤ ((E.part a).card : ℝ))
    (K : SubcriticalRetainedKey k (Fin n))
    (hK : K ∈ compatibleRetainedKeys k n (oneBlockSequence k hk mu hmu hmu1) eta delta R₀)
    (hne : (retainedKeyGoodCleanGraphFinset K eta R₀ m delta).Nonempty) :
    ∃ D : SupercriticalDivision k (Fin n),
      K = some (SubcriticalDivision.ofSupercritical hk D) ∧
      (SubcriticalDivision.ofSupercritical hk D).retainedComponentIndices eta R₀ = Finset.univ ∧
      ∀ i, mu / (4 * (k - 1 : ℕ)) * n ≤ ((D.parts i).card : ℝ) := by
  obtain ⟨G,hG⟩ := hne
  have hmodel := (Finset.mem_filter.mp hG).1
  cases K with
  | none => exact False.elim (Finset.notMem_empty _ hmodel)
  | some E =>
    obtain ⟨A,hA,hAE⟩ := mem_compatibleRetainedKeys.mp hK
    have hnorm := retainedKey_some_idempotent hAE
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hmodel
    have hpos : 0 < retainedEdgeCountMultiplicity d.2.2.1.val := by
      apply Finset.prod_pos
      intro e _
      exact Nat.choose_pos (d.2.2.1.val.count_le_capacity e)
    have hz := hpos.trans_le (retainedEdgeCountMultiplicity_le_partitionFunction d.2.2.1.property)
    rw [← retainedKeyPartitionFunction_retainedKey, hnorm] at hz
    obtain ⟨E', heq, hcount, hcore, hpart⟩ := hgeom (some E) hK d.1.val hz
    have he := Option.some.inj heq
    subst E'
    obtain ⟨D,hD⟩ := E.exists_ofSupercritical_of_one_complete hk hcount hcore
    subst E
    refine ⟨D,rfl,retainedKey_some_retains_all hAE,?_⟩
    intro i
    simpa only [SubcriticalDivision.part, SubcriticalDivision.ofSupercritical] using
      (hpart ⟨⟨0,by change 0 < 1; omega⟩,i⟩).2

/-- Uniform constant-factor lower comparison for the actual clean partition
functions indexed by minimal retained keys. All multiplicity and probability
bounds used here are locally proved. -/
theorem eventually_retainedKeyCleanSum_le_total {k R₀ : ℕ} (hk : 3 ≤ k)
    {mu eta delta : ℝ} (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (heta : 0 ≤ eta) (hd : 0 < delta) (hsize : eta + delta ≤ mu)
    (hR : k - 1 ≤ R₀) (hdmu : delta ≤ mu / 2)
    (hsmall : delta ≤ (1 - pK k) * (mu / (4 * (k - 1 : ℕ)))^2 / 10)
    (hdBand : delta ≤ subcriticalReferenceShiftBand k / 2)
    (hsparse : subcriticalSparseSideConstant k * eta < (mu / (4 * (k - 1 : ℕ)))^2 / 4)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m (gammaK k * mu^2)) :
    ∀ᶠ n : ℕ in atTop,
      (∑ K ∈ compatibleRetainedKeys k n (oneBlockSequence k hk mu hmu hmu1) eta delta R₀,
        retainedKeyCleanPartitionFunction K eta (m n) delta) ≤
      (2 * (k - 1).factorial) * inducedStarFreeGraphCountWithEdges k n (m n) := by
  let a := mu / (4 * (k - 1 : ℕ))
  have ha : 0 < a := by
    have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
    dsimp [a]; positivity
  have hscale : ∀ᶠ n : ℕ in atTop, 2 ≤ a * n :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop ha).eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [eventually_retainedKeyClean_le_two_good hk hmu hmu1 heta hd hsize hR hdmu
    hsmall hdBand m hm, eventually_compatibleRetainedKeys_part_lower hk hmu hmu1 heta hd
      hsize hR hdmu hsmall m hm, hscale] with n hhalf hgeom hscale
  let F := compatibleRetainedKeys k n (oneBlockSequence k hk mu hmu hmu1) eta delta R₀
  have hmult := sum_retainedKeyGoodClean_card_le_factorial hk F heta ha.le
    (by simpa only [Fintype.card_fin] using hscale) hsparse
    (fun K hK hne ↦ by
      simpa only [Fintype.card_fin] using compatibleRetainedGoodKey_geometry hk hmu hmu1 hgeom K hK hne)
  have hsub : F.biUnion (fun K ↦ retainedKeyGoodCleanGraphFinset K eta R₀ (m n) delta) ⊆
      inducedStarFreeGraphFinsetWithEdges k n (m n) := by
    intro G hG
    obtain ⟨K, _, hG⟩ := Finset.mem_biUnion.mp hG
    exact retainedKeyGoodCleanGraphFinset_subset_total hk K eta delta hG
  calc
    _ ≤ ∑ K ∈ F, 2 * (retainedKeyGoodCleanGraphFinset K eta R₀ (m n) delta).card :=
      Finset.sum_le_sum hhalf
    _ = 2 * ∑ K ∈ F, (retainedKeyGoodCleanGraphFinset K eta R₀ (m n) delta).card :=
      (Finset.mul_sum ..).symm
    _ ≤ 2 * ((k - 1).factorial *
        (F.biUnion (fun K ↦ retainedKeyGoodCleanGraphFinset K eta R₀ (m n) delta)).card) :=
      Nat.mul_le_mul_left 2 hmult
    _ ≤ (2 * (k - 1).factorial) * inducedStarFreeGraphCountWithEdges k n (m n) := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (Finset.card_le_card hsub)

end InducedStars
