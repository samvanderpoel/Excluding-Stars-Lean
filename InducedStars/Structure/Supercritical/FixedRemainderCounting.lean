import InducedStars.Structure.Supercritical.FixedDefectAggregation

/-!
# Cross-edge counts with a prescribed remainder

The remainder graph is fixed throughout these comparisons. Summing the
admissible cross profiles therefore contributes one binomial coefficient,
without a factor counting graphs on the remainder.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance fixedRemainderGraphDecidableEq (W : Type*) :
    DecidableEq (SimpleGraph W) := Classical.decEq _

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- A family of cross profiles with one prescribed total is bounded by the
corresponding layer of the cross-coordinate universe. -/
theorem sum_supercriticalProfileMultiplicity_le_choose
    (D : SupercriticalDivision k V)
    (S : Finset (SupercriticalEdgeProfile D)) (L : ℕ)
    (hL : ∀ p ∈ S, profileTotal p = L) :
    (∑ p ∈ S, supercriticalProfileMultiplicity p) ≤
      Nat.choose (supercriticalTotalCrossCapacity D) L := by
  classical
  let choices := S.sigma (supercriticalProfileChoiceFinset D)
  let encode : (Σ _p : SupercriticalEdgeProfile D,
      SupercriticalPartPair k → Finset (V × V)) →
        Finset (SupercriticalTaggedCrossChoice k V) :=
    fun z ↦ Finset.univ.sigma z.2
  have hmap : Set.MapsTo encode choices
      ((supercriticalTaggedCrossChoiceUniverse D).powersetCard L) := by
    rintro ⟨p, f⟩ hz
    obtain ⟨hp, hf⟩ := Finset.mem_sigma.mp hz
    have hf' := (mem_supercriticalProfileChoiceFinset D p f).mp hf
    change encode ⟨p, f⟩ ∈ (supercriticalTaggedCrossChoiceUniverse D).powersetCard L
    rw [Finset.mem_powersetCard]
    constructor
    · intro z hz'
      obtain ⟨_, hzf⟩ := Finset.mem_sigma.mp hz'
      rw [mem_supercriticalTaggedCrossChoiceUniverse]
      exact Finset.mem_product.mp ((hf' z.1).1 hzf)
    · change (Finset.univ.sigma f).card = L
      rw [Finset.card_sigma, ← hL p hp]
      exact Finset.sum_congr rfl (fun e _ ↦ (hf' e).2)
  have hinj : Set.InjOn encode choices := by
    rintro ⟨p, f⟩ hz ⟨q, g⟩ hw heq
    obtain ⟨_, hf⟩ := Finset.mem_sigma.mp hz
    obtain ⟨_, hg⟩ := Finset.mem_sigma.mp hw
    have hfg : f = g := by
      funext e
      ext xy
      have hmem := congrArg
        (fun A : Finset (SupercriticalTaggedCrossChoice k V) ↦
          (⟨e, xy⟩ : SupercriticalTaggedCrossChoice k V) ∈ A) heq
      simpa [encode] using hmem
    have hpq : p = q := by
      apply SupercriticalEdgeProfile.ext
      funext e
      rw [← ((mem_supercriticalProfileChoiceFinset D p f).mp hf e).2,
        ← ((mem_supercriticalProfileChoiceFinset D q g).mp hg e).2, hfg]
    cases hpq
    cases hfg
    rfl
  have hcard := Finset.card_le_card_of_injOn encode hmap hinj
  simpa [choices, Finset.card_sigma,
    card_supercriticalProfileChoiceFinset] using hcard

/-- At a fixed signed edge shift, profile aggregation counts only cross
edges. The equality hypothesis records the exact integer edge budget. -/
theorem supercriticalProfileMassAtShift_le_crossChoose
    (D : SupercriticalDivision k V) (m L : ℕ)
    (rho delta : ℝ) (u : ℤ)
    (hL : (L : ℤ) + (divisionInternalCliqueCapacity D : ℤ) + u = m) :
    supercriticalProfileMassAtShift D m rho delta u ≤
      Nat.choose (supercriticalTotalCrossCapacity D) L := by
  classical
  rw [supercriticalProfileMassAtShift, ← Finset.sum_filter]
  apply sum_supercriticalProfileMultiplicity_le_choose
  intro p hp
  have hcount := (Finset.mem_filter.mp hp).2.1
  omega

/-- A fixed defect pattern retains its matching penalty after summing over
all admissible cross profiles. The remainder is already fixed in the
combined pattern, so no sparse-graph multiplicity is introduced. -/
theorem card_supercriticalFixedDefect_le_crossChoose_mul_exp
    {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha rho delta : ℝ} {m n L : ℕ} {tau c : ℝ}
    {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (hL : (L : ℤ) + (divisionInternalCliqueCapacity D : ℤ) +
      supercriticalDefectShift T D = m)
    (hcount :
      ((supercriticalFixedDefectGraphFinset
        k hk gamma hgamma alpha m n tau hn D T).card : ℝ) ≤
        (supercriticalProfileMassAtShift D m rho delta
          (supercriticalDefectShift T D) : ℝ) * Real.exp c) :
    ((supercriticalFixedDefectGraphFinset
      k hk gamma hgamma alpha m n tau hn D T).card : ℝ) ≤
      (Nat.choose (supercriticalTotalCrossCapacity D) L : ℝ) *
        Real.exp c := by
  apply hcount.trans
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast (supercriticalProfileMassAtShift_le_crossChoose
      D m L rho delta (supercriticalDefectShift T D) hL))
    (Real.exp_nonneg _)


/-- Fixing the sparse graph makes the support-incident pattern an injective
encoding of the complete defect pattern. -/
theorem supercriticalSupportIncidentGraph_injectiveOn_fixedSparse
    (D : SupercriticalDivision k V)
    (H : Finset (Sym2 V)) :
    Set.InjOn (supercriticalSupportIncidentGraph D)
      {T : SimpleGraph V | supercriticalSparseInducedEdges T D = H} := by
  intro T hT U hU hsupp
  exact supercriticalSparseInducedEdges_injectiveOn_supportFiber
    D (supercriticalSupportIncidentGraph D T)
    (show supercriticalSupportIncidentGraph D T =
      supercriticalSupportIncidentGraph D T from rfl)
    hsupp.symm (hT.trans hU.symm)

/-- No multiplicity for the remainder is charged when a fixed-remainder
family is grouped by its support pattern. -/
theorem sum_fixedSparsePatterns_eq_sum_support
    (D : SupercriticalDivision k V)
    (S : Finset (SimpleGraph V)) (H : Finset (Sym2 V))
    (hH : ∀ T ∈ S, supercriticalSparseInducedEdges T D = H)
    (w : SimpleGraph V → ℝ) :
    (∑ T ∈ S, w (supercriticalSupportIncidentGraph D T)) =
      ∑ T₀ ∈ S.image (supercriticalSupportIncidentGraph D), w T₀ := by
  classical
  symm
  apply Finset.sum_image
  intro T hT U hU hTU
  exact supercriticalSupportIncidentGraph_injectiveOn_fixedSparse
    D H (hH T hT) (hH U hU) hTU

/-- The compact-band adjacent-ratio estimate pays for a signed defect shift
while retaining a single fixed-remainder reference binomial. -/
theorem card_supercriticalFixedDefect_le_referenceCrossChoose_mul_exp
    {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha rho delta lambda : ℝ} {m n L M : ℕ} {tau c : ℝ}
    {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (hL : (L : ℤ) + (divisionInternalCliqueCapacity D : ℤ) +
      supercriticalDefectShift T D = m)
    (hLC : L ≤ supercriticalTotalCrossCapacity D)
    (hMC : M ≤ supercriticalTotalCrossCapacity D)
    (hlambda : 0 < lambda) (hlambdaHalf : lambda < 1 / 2)
    (hMlo : lambda * (supercriticalTotalCrossCapacity D : ℝ) ≤ M)
    (hMhi : (M : ℝ) ≤ (1 - lambda) *
      (supercriticalTotalCrossCapacity D : ℝ))
    (hcount :
      ((supercriticalFixedDefectGraphFinset
        k hk gamma hgamma alpha m n tau hn D T).card : ℝ) ≤
        (supercriticalProfileMassAtShift D m rho delta
          (supercriticalDefectShift T D) : ℝ) * Real.exp c) :
    ((supercriticalFixedDefectGraphFinset
      k hk gamma hgamma alpha m n tau hn D T).card : ℝ) ≤
      (Nat.choose (supercriticalTotalCrossCapacity D) M : ℝ) *
        Real.exp (c + DenseGraph.binomialCompactBandShiftConstant lambda *
          (Nat.dist L M : ℝ)) := by
  have hp := card_supercriticalFixedDefect_le_crossChoose_mul_exp
    D T hL hcount
  have hs := DenseGraph.choose_le_choose_mul_exp_abs_shift_of_compact_band
    hLC hMC hlambda hlambdaHalf hMlo hMhi
  calc
    _ ≤ (Nat.choose (supercriticalTotalCrossCapacity D) L : ℝ) *
        Real.exp c := hp
    _ ≤ ((Nat.choose (supercriticalTotalCrossCapacity D) M : ℝ) *
        Real.exp (DenseGraph.binomialCompactBandShiftConstant lambda *
          (Nat.dist L M : ℝ))) * Real.exp c :=
      mul_le_mul_of_nonneg_right hs (Real.exp_nonneg _)
    _ = _ := by rw [mul_assoc, ← Real.exp_add, add_comm]


/-- The literal canonical nonclean family with a prescribed induced graph
on the sparse set, represented by its ambient unordered edge set. -/
noncomputable def supercriticalFixedRemainderDefectGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n))
    (H : Finset (Sym2 (Fin n))) : Finset (SimpleGraph (Fin n)) := by
  classical
  exact (supercriticalDivisionDefectGraphFinset
    k hk gamma hgamma m n tau hn D).filter
      fun G ↦ supercriticalSparseInducedEdges G D = H

@[simp] theorem mem_supercriticalFixedRemainderDefectGraphFinset
    {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {H : Finset (Sym2 (Fin n))} {G : SimpleGraph (Fin n)} :
    G ∈ supercriticalFixedRemainderDefectGraphFinset
        k hk gamma hgamma m n tau hn D H ↔
      G ∈ supercriticalDivisionDefectGraphFinset
        k hk gamma hgamma m n tau hn D ∧
        supercriticalSparseInducedEdges G D = H := by
  classical
  simp [supercriticalFixedRemainderDefectGraphFinset]

/-- A fixed remainder leaves one exact cross-edge binomial. The explicit
integer budget excludes any ambiguity from truncated natural subtraction. -/
theorem supercriticalProfileMassAtShift_le_referenceCrossChoose
    (D : SupercriticalDivision k V) (m M t : ℕ)
    (rho delta lambda : ℝ) (u : ℤ)
    (hbudget : M + divisionInternalCliqueCapacity D + t = m)
    (hMC : M ≤ supercriticalTotalCrossCapacity D)
    (hlambda : 0 < lambda) (hlambdaHalf : lambda < 1 / 2)
    (hMlo : lambda * (supercriticalTotalCrossCapacity D : ℝ) ≤ M)
    (hMhi : (M : ℝ) ≤ (1 - lambda) *
      (supercriticalTotalCrossCapacity D : ℝ)) :
    (supercriticalProfileMassAtShift D m rho delta (u + (t : ℤ)) : ℝ) ≤
      (Nat.choose (supercriticalTotalCrossCapacity D) M : ℝ) *
        Real.exp (DenseGraph.binomialCompactBandShiftConstant lambda *
          (u.natAbs : ℝ)) := by
  classical
  let S := (supercriticalAllEdgeProfilesFinset D).filter
    (SupercriticalProfileAtShift D m rho delta (u + (t : ℤ)))
  by_cases hS : S.Nonempty
  · obtain ⟨p, hp⟩ := hS
    have hprofile := (Finset.mem_filter.mp hp).2
    have hL : (profileTotal p : ℤ) +
        (divisionInternalCliqueCapacity D : ℤ) + (u + (t : ℤ)) = m :=
      hprofile.1
    have hLM : (profileTotal p : ℤ) = (M : ℤ) - u := by
      have hb : (M : ℤ) + (divisionInternalCliqueCapacity D : ℤ) + t = m := by
        exact_mod_cast hbudget
      omega
    have hdist : Nat.dist (profileTotal p) M = u.natAbs := by
      by_cases hu : 0 ≤ u
      · have habs : (u.natAbs : ℤ) = u := Int.natAbs_of_nonneg hu
        have hnat : profileTotal p + u.natAbs = M := by omega
        rw [Nat.dist_eq_sub_of_le (by omega)]
        omega
      · have habs : (u.natAbs : ℤ) = -u :=
          Int.ofNat_natAbs_of_nonpos (le_of_not_ge hu)
        have hnat : profileTotal p = M + u.natAbs := by omega
        rw [Nat.dist_eq_sub_of_le_right (by omega)]
        omega
    have hLC : profileTotal p ≤ supercriticalTotalCrossCapacity D := by
      unfold profileTotal supercriticalTotalCrossCapacity
      exact Finset.sum_le_sum fun e _ ↦ p.count_le_capacity e
    have hmass := supercriticalProfileMassAtShift_le_crossChoose
      D m (profileTotal p) rho delta (u + (t : ℤ)) hL
    have hshift := DenseGraph.choose_le_choose_mul_exp_abs_shift_of_compact_band
      hLC hMC hlambda hlambdaHalf hMlo hMhi
    rw [hdist] at hshift
    have hmassReal : (supercriticalProfileMassAtShift D m rho delta
        (u + (t : ℤ)) : ℝ) ≤
        (Nat.choose (supercriticalTotalCrossCapacity D) (profileTotal p) : ℝ) := by
      exact_mod_cast hmass
    exact hmassReal.trans hshift
  · have hzero : supercriticalProfileMassAtShift D m rho delta (u + (t : ℤ)) = 0 := by
      rw [supercriticalProfileMassAtShift, ← Finset.sum_filter]
      change (∑ p ∈ S, supercriticalProfileMultiplicity p) = 0
      rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simp
    simp only [hzero, Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)


/-- Two balanced nonempty main parts already provide a quadratic cross
capacity, uniformly over the sparse set. -/
theorem supercriticalTotalCrossCapacity_lower_of_balanced
    {k n : ℕ} (hk : 3 ≤ k) {delta : ℝ}
    (hdelta : delta ≤ 1 / (2 * ((k - 1 : ℕ) : ℝ)))
    (D : SupercriticalDivision k (Fin n))
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
        (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n) :
    (n : ℝ) ^ 2 / (4 * ((k - 1 : ℕ) : ℝ) ^ 2) ≤
      (supercriticalTotalCrossCapacity D : ℝ) := by
  let r : ℝ := ((k - 1 : ℕ) : ℝ)
  have hr : 0 < r := by dsimp [r]; exact_mod_cast (by omega : 0 < k - 1)
  have hpart (i : Fin (k - 1)) :
      (n : ℝ) / (2 * r) ≤ ((D.parts i).card : ℝ) := by
    have hdn := mul_le_mul_of_nonneg_right hdelta (Nat.cast_nonneg (α := ℝ) n)
    have hbal := (abs_le.mp (hbalanced i)).1
    change -(delta * n) ≤ ((D.parts i).card : ℝ) - (n : ℝ) / r at hbal
    have hid : (1 / (2 * r)) * (n : ℝ) = (n : ℝ) / (2 * r) := by ring
    rw [show ((k - 1 : ℕ) : ℝ) = r from rfl, hid] at hdn
    have htwo : (n : ℝ) / r = 2 * ((n : ℝ) / (2 * r)) := by ring
    linarith
  let i : Fin (k - 1) := ⟨0, by omega⟩
  let j : Fin (k - 1) := ⟨1, by omega⟩
  let e : SupercriticalPartPair k := ⟨i, j, by simp [i, j]⟩
  have hcap : (n : ℝ) ^ 2 / (4 * r ^ 2) ≤
      (crossEdgeCapacity D e : ℝ) := by
    calc
      _ = ((n : ℝ) / (2 * r)) * ((n : ℝ) / (2 * r)) := by ring
      _ ≤ ((D.parts i).card : ℝ) * ((D.parts j).card : ℝ) :=
        mul_le_mul (hpart i) (hpart j) (by positivity) (by positivity)
      _ = _ := by simp [crossEdgeCapacity, e]
  have hterm : crossEdgeCapacity D e ≤ supercriticalTotalCrossCapacity D := by
    unfold supercriticalTotalCrossCapacity
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ e)
  exact hcap.trans (by exact_mod_cast hterm)

/-- Componentwise density control gives the same bounds on the total
number of selected cross edges. -/
theorem supercriticalProfileTotal_bounds
    (D : SupercriticalDivision k V)
    (p : SupercriticalEdgeProfile D) {rho delta : ℝ}
    (hp : ∀ e, rho - delta ≤ profileDensity p e ∧
      profileDensity p e ≤ rho + delta) :
    (rho - delta) * (supercriticalTotalCrossCapacity D : ℝ) ≤
        (profileTotal p : ℝ) ∧
      (profileTotal p : ℝ) ≤
        (rho + delta) * (supercriticalTotalCrossCapacity D : ℝ) := by
  have hcap (e : SupercriticalPartPair k) :
      (0 : ℝ) < (crossEdgeCapacity D e : ℕ) := by
    exact_mod_cast crossEdgeCapacity_pos D e
  constructor
  · rw [supercriticalTotalCrossCapacity, Nat.cast_sum, Finset.mul_sum,
      profileTotal, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro e _
    have h := (le_div_iff₀ (hcap e)).mp (hp e).1
    simpa [profileDensity, crossEdgeCapacity, Nat.cast_mul] using h
  · rw [supercriticalTotalCrossCapacity, Nat.cast_sum, Finset.mul_sum,
      profileTotal, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro e _
    have h := (div_le_iff₀ (hcap e)).mp (hp e).2
    simpa [profileDensity, crossEdgeCapacity, Nat.cast_mul] using h

/-- A small signed discrepancy from a genuine profile puts the fixed
remainder reference count in a compact density band. In particular its
forced clique and remainder edges fit below the exact edge budget. -/
theorem supercriticalFixedRemainderReferenceBand_of_profile
    (D : SupercriticalDivision k V) (p : SupercriticalEdgeProfile D)
    (m t : ℕ) {rho delta lambda : ℝ} (u : ℤ)
    (hlambda : 0 ≤ lambda)
    (hrhoLo : 2 * lambda + delta ≤ rho)
    (hrhoHi : rho + delta ≤ 1 - 2 * lambda)
    (hp : SupercriticalProfileAtShift D m rho delta (u + (t : ℤ)) p)
    (hu : (u.natAbs : ℝ) ≤
      lambda * (supercriticalTotalCrossCapacity D : ℝ)) :
    divisionInternalCliqueCapacity D + t ≤ m ∧
      m - (divisionInternalCliqueCapacity D + t) ≤
        supercriticalTotalCrossCapacity D ∧
      lambda * (supercriticalTotalCrossCapacity D : ℝ) ≤
        (m - (divisionInternalCliqueCapacity D + t) : ℕ) ∧
      ((m - (divisionInternalCliqueCapacity D + t) : ℕ) : ℝ) ≤
        (1 - lambda) * (supercriticalTotalCrossCapacity D : ℝ) := by
  have hb := supercriticalProfileTotal_bounds D p hp.2
  have hcount : (profileTotal p : ℝ) +
      (divisionInternalCliqueCapacity D : ℝ) + ((u : ℝ) + (t : ℝ)) = m := by
    exact_mod_cast hp.1
  have huPos : (u : ℝ) ≤ (u.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact le_abs_self _
  have huNeg : -(u.natAbs : ℝ) ≤ (u : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact neg_abs_le _
  have hN : (0 : ℝ) ≤ supercriticalTotalCrossCapacity D := by positivity
  have hLo := mul_le_mul_of_nonneg_right hrhoLo hN
  have hHi := mul_le_mul_of_nonneg_right hrhoHi hN
  have hmargin := mul_nonneg hlambda hN
  have hforcedReal :
      (divisionInternalCliqueCapacity D : ℝ) + t ≤ m := by
    nlinarith only [hb.1, hcount, huNeg, hu, hLo, hmargin]
  have hforced : divisionInternalCliqueCapacity D + t ≤ m := by
    exact_mod_cast hforcedReal
  have hcast :
      ((m - (divisionInternalCliqueCapacity D + t) : ℕ) : ℝ) =
        (m : ℝ) - ((divisionInternalCliqueCapacity D : ℝ) + t) := by
    rw [Nat.cast_sub hforced, Nat.cast_add]
  have hlo : lambda * (supercriticalTotalCrossCapacity D : ℝ) ≤
      ((m - (divisionInternalCliqueCapacity D + t) : ℕ) : ℝ) := by
    rw [hcast]
    nlinarith only [hb.1, hcount, huNeg, hu, hLo]
  have hhi : ((m - (divisionInternalCliqueCapacity D + t) : ℕ) : ℝ) ≤
      (1 - lambda) * (supercriticalTotalCrossCapacity D : ℝ) := by
    rw [hcast]
    nlinarith only [hb.2, hcount, huPos, hu, hHi]
  refine ⟨hforced, ?_, hlo, hhi⟩
  have : ((m - (divisionInternalCliqueCapacity D + t) : ℕ) : ℝ) ≤
      supercriticalTotalCrossCapacity D := by nlinarith only [hhi, hmargin]
  exact_mod_cast this


@[simp] theorem finiteGraphEdges_sparseInducedGraph
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    finiteGraphEdges (sparseInducedGraph G D) =
      supercriticalSparseInducedEdges G D := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [supercriticalSparseInducedEdges, finiteGraphEdges,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_filter, sparseInducedGraph_adj,
        Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      tauto

/-- Sparse-induced edges are among the combined defects already controlled
by the close-structure theorem. -/
theorem card_supercriticalSparseInducedEdges_le_cost
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    (supercriticalSparseInducedEdges G D).card ≤
      supercriticalDefectCost G D := by
  unfold supercriticalDefectCost
  rw [finiteGraphEdges_sparseInducedGraph]
  omega

/-- The combined defect operation preserves the prescribed sparse graph. -/
@[simp] theorem supercriticalSparseInducedEdges_combined
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    supercriticalSparseInducedEdges (combinedSupercriticalDefectGraph G D) D =
      supercriticalSparseInducedEdges G D := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [supercriticalSparseInducedEdges, Finset.mem_filter,
        SimpleGraph.mem_edgeFinset, Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
        Finset.singleton_subset_iff]
      constructor
      · rintro ⟨hxy, hx, hy⟩
        exact ⟨(combinedSupercriticalDefectGraph_adj_of_mem_sparse G D hx hy).mp hxy,
          hx, hy⟩
      · rintro ⟨hxy, hx, hy⟩
        exact ⟨(combinedSupercriticalDefectGraph_adj_of_mem_sparse G D hx hy).mpr hxy,
          hx, hy⟩

/-- The sparse-edge set of a fixed combined pattern equals that of every
graph counted by its fiber. -/
theorem supercriticalSparseInducedEdges_eq_of_mem_fixedDefect
    {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalFixedDefectGraphFinset
      k hk gamma hgamma alpha m n tau hn D T) :
    supercriticalSparseInducedEdges T D =
      supercriticalSparseInducedEdges G D := by
  have hmem := mem_supercriticalFixedDefectGraphFinset.mp hG
  have hD := (mem_supercriticalDivisionDefectGraphFinset.mp hmem.1).2.1
  have hT : combinedSupercriticalDefectGraph G D = T := by
    simpa [canonicalCombinedDefectGraph, hD] using hmem.2.1
  rw [← hT, supercriticalSparseInducedEdges_combined]

/-- Splitting off the medium-degree class and recording the literal
combined pattern covers every fixed-remainder nonclean graph. -/
theorem supercriticalFixedRemainderDefect_subset_medium_union_fixed
    {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) (H : Finset (Sym2 (Fin n))) :
    supercriticalFixedRemainderDefectGraphFinset
        k hk gamma hgamma m n tau hn D H ⊆
      (supercriticalMediumDegreeGraphFinset
        k hk gamma hgamma alpha m n tau hn D).filter
          (fun G ↦ supercriticalSparseInducedEdges G D = H) ∪
      ((supercriticalCombinedDefectPatternFinset
        k hk gamma hgamma m n tau hn D).filter
          (fun T ↦ supercriticalSparseInducedEdges T D = H ∧
            (supercriticalFixedDefectGraphFinset
              k hk gamma hgamma alpha m n tau hn D T).Nonempty)).biUnion
        (supercriticalFixedDefectGraphFinset
          k hk gamma hgamma alpha m n tau hn D) := by
  classical
  intro G hG
  obtain ⟨hdef, hH⟩ := mem_supercriticalFixedRemainderDefectGraphFinset.mp hG
  by_cases hmed : ∃ v i, HasMediumDegreeInPart
      (canonicalCombinedDefectGraph G (by simpa using hn)) alpha D v i
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨mem_supercriticalMediumDegreeGraphFinset.mpr ⟨hdef, hmed⟩, hH⟩)
  · let T := canonicalCombinedDefectGraph G (by simpa using hn)
    have hfixed : G ∈ supercriticalFixedDefectGraphFinset
        k hk gamma hgamma alpha m n tau hn D T :=
      mem_supercriticalFixedDefectGraphFinset.mpr ⟨hdef, rfl, hmed⟩
    have hpattern : T ∈ supercriticalCombinedDefectPatternFinset
        k hk gamma hgamma m n tau hn D :=
      mem_supercriticalCombinedDefectPatternFinset.mpr ⟨G, hdef, rfl⟩
    have hTH : supercriticalSparseInducedEdges T D = H :=
      (supercriticalSparseInducedEdges_eq_of_mem_fixedDefect hfixed).trans hH
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨T, Finset.mem_filter.mpr ⟨hpattern, hTH, ⟨G, hfixed⟩⟩, hfixed⟩)


@[simp] theorem supercriticalSparseInducedEdges_sparseInduced
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    supercriticalSparseInducedEdges (sparseInducedGraph G D) D =
      supercriticalSparseInducedEdges G D := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [supercriticalSparseInducedEdges, Finset.mem_filter,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, sparseInducedGraph_adj,
        Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      tauto

/-- The signed defect shift separates the support defect from the fixed
ambient sparse-edge set. -/
theorem supercriticalDefectShift_eq_support_add_sparseEdges
    (D : SupercriticalDivision k V) (T : SimpleGraph V) :
    supercriticalDefectShift T D =
      supercriticalSupportDefectShift D (supercriticalSupportIncidentGraph D T) +
        ((supercriticalSparseInducedEdges T D).card : ℤ) := by
  rw [supercriticalDefectShift_eq_support_add_sparse]
  congr 1
  rw [← card_supercriticalSparseInducedEdges]
  simp only [supercriticalSparseInducedPattern, supercriticalSparseInducedEdges_sparseInduced]

end InducedStars
