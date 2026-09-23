import InducedStars.Asymptotics.GnpSlices
import InducedStars.Graphon.GnpDomains
import InducedStars.Graphon.Counting
import InducedStars.PriorLiterature

/-!
# Weighted entropy upper bound for induced-free `G(n,p)`

This file proves the compactness/HJS upper-bound layer in the local proof of
the induced-free `G(n,p)` transfer theorem.  The padding construction below
is the correction recorded in `CFD-006`: it lets a family selected only on a
subsequence of graph orders be passed to the published labeled-family
entropy upper bound without adding spurious graphon limits.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

attribute [local instance] Classical.propDecidable

noncomputable local instance weightedEntropyEdgeSetFintype {n : ℕ}
    (G : SimpleGraph (Fin n)) : Fintype G.edgeSet :=
  graphFamiliesEdgeSetFintype G

/-! ## A selected exact-edge family padded by an approximating sequence -/

/-- Reindex an approximation sequence on orders `n + 1` as a sequence on all
orders.  The value at order zero is irrelevant to every limiting argument. -/
def approximationGraphAtOrder
    (A : (n : ℕ) → SimpleGraph (Fin (n + 1))) :
    (n : ℕ) → SimpleGraph (Fin n)
  | 0 => ⊥
  | n + 1 => A n

@[simp] theorem approximationGraphAtOrder_succ
    (A : (n : ℕ) → SimpleGraph (Fin (n + 1))) (n : ℕ) :
    approximationGraphAtOrder A (n + 1) = A n :=
  rfl

/-- The exact-edge family at selected orders and a singleton approximation
at every other order.  The conditional definition gives literal agreement,
not merely inclusion, at selected orders. -/
def paddedSelectedSliceFamily {h : ℕ}
    (H : SimpleGraph (Fin h)) (m : ℕ → ℕ) (σ : ℕ → ℕ)
    (A : (n : ℕ) → SimpleGraph (Fin (n + 1))) :
    (n : ℕ) → Finset (SimpleGraph (Fin n)) := fun n ↦
  if n ∈ Set.range σ then
    inducedFreeGraphFinsetWithEdges H n (m n)
  else
    {approximationGraphAtOrder A n}

theorem paddedSelectedSliceFamily_eq_selected {h : ℕ}
    (H : SimpleGraph (Fin h)) (m : ℕ → ℕ) (σ : ℕ → ℕ)
    (A : (n : ℕ) → SimpleGraph (Fin (n + 1)))
    {n : ℕ} (hn : n ∈ Set.range σ) :
    paddedSelectedSliceFamily H m σ A n =
      inducedFreeGraphFinsetWithEdges H n (m n) := by
  simp [paddedSelectedSliceFamily, hn]

theorem paddedSelectedSliceFamily_eq_selected_apply {h : ℕ}
    (H : SimpleGraph (Fin h)) (m : ℕ → ℕ) (σ : ℕ → ℕ)
    (A : (n : ℕ) → SimpleGraph (Fin (n + 1))) (j : ℕ) :
    paddedSelectedSliceFamily H m σ A (σ j) =
      inducedFreeGraphFinsetWithEdges H (σ j) (m (σ j)) := by
  exact paddedSelectedSliceFamily_eq_selected H m σ A
    ⟨j, rfl⟩

theorem paddedSelectedSliceFamily_eq_padding {h : ℕ}
    (H : SimpleGraph (Fin h)) (m : ℕ → ℕ) (σ : ℕ → ℕ)
    (A : (n : ℕ) → SimpleGraph (Fin (n + 1)))
    {n : ℕ} (hn : n ∉ Set.range σ) :
    paddedSelectedSliceFamily H m σ A n =
      {approximationGraphAtOrder A n} := by
  simp [paddedSelectedSliceFamily, hn]

/-- Padding turns nonemptiness along the selected orders into nonemptiness
at every order. -/
theorem paddedSelectedSliceFamily_nonempty {h : ℕ}
    (H : SimpleGraph (Fin h)) (m : ℕ → ℕ) (σ : ℕ → ℕ)
    (A : (n : ℕ) → SimpleGraph (Fin (n + 1)))
    (hne : ∀ j,
      (inducedFreeGraphFinsetWithEdges H (σ j) (m (σ j))).Nonempty) :
    ∀ n, (paddedSelectedSliceFamily H m σ A n).Nonempty := by
  intro n
  by_cases hn : n ∈ Set.range σ
  · obtain ⟨j, rfl⟩ := hn
    simpa [paddedSelectedSliceFamily] using hne j
  · simp [paddedSelectedSliceFamily, hn]

/-- Every positive-order member of the padded family is induced-`H`-free,
provided the padding sequence is. -/
theorem paddedSelectedSliceFamily_member_inducedFree {h : ℕ}
    (H : SimpleGraph (Fin h)) (m : ℕ → ℕ) (σ : ℕ → ℕ)
    (A : (n : ℕ) → SimpleGraph (Fin (n + 1)))
    (hAfree : ∀ n, ¬ Regularity.InducedEmbeds H (A n))
    {n : ℕ} (hn : 0 < n) {G : SimpleGraph (Fin n)}
    (hG : G ∈ paddedSelectedSliceFamily H m σ A n) :
    ¬ Regularity.InducedEmbeds H G := by
  by_cases hselected : n ∈ Set.range σ
  · rw [paddedSelectedSliceFamily_eq_selected H m σ A hselected] at hG
    exact (mem_inducedFreeGraphFinsetWithEdges.mp hG).1
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [paddedSelectedSliceFamily_eq_padding H m σ A hselected] at hG
    have hGA : G = A k := by
      simpa only [Finset.mem_singleton, approximationGraphAtOrder_succ] using hG
    subst G
    exact hAfree k

/-- Every graphon limit of the padded family is induced-`H`-free.  Only the
zero-order padding value is exceptional, and a limit-set witness discards it
after a finite shift. -/
theorem paddedSelectedSliceFamily_limitSet_inducedFree {h : ℕ}
    (H : SimpleGraph (Fin h)) (m : ℕ → ℕ) (σ : ℕ → ℕ)
    (A : (n : ℕ) → SimpleGraph (Fin (n + 1)))
    (hAfree : ∀ n, ¬ Regularity.InducedEmbeds H (A n))
    {W : Graphon}
    (hW : W ∈ labeledGraphFamilyLimitSet
      (paddedSelectedSliceFamily H m σ A)) :
    graphonInducedDensity H W = 0 := by
  obtain ⟨τ, hτ, G, hG, hcut⟩ := hW
  have hpositive : ∀ᶠ j in atTop, 0 < τ j :=
    hτ.tendsto_atTop.eventually
      (eventually_atTop.2 ⟨1, fun _ hn ↦ hn⟩)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hpositive
  let τ' : ℕ → ℕ := fun j ↦ τ (j + N)
  let G' : (j : ℕ) → SimpleGraph (Fin (τ' j)) := fun j ↦ G (j + N)
  have hτ' : StrictMono τ' :=
    hτ.comp (strictMono_id.add_const N)
  have hGfree : ∀ j, ¬ Regularity.InducedEmbeds H (G' j) := by
    intro j
    exact paddedSelectedSliceFamily_member_inducedFree H m σ A hAfree
      (hN (j + N) (Nat.le_add_left N j)) (hG (j + N))
  have hfinite : Tendsto
      (fun j ↦ graphonInducedDensity H (graphGraphon (G' j)))
      atTop (nhds 0) :=
    graphonInducedDensity_graphGraphon_tendsto_zero_of_inducedFree
      H hτ'.tendsto_atTop G' hGfree
  have hcut' : Tendsto
      (fun j ↦ cutDist (graphGraphon (G' j)) W) atTop (nhds 0) := by
    exact (tendsto_add_atTop_iff_nat N).2 hcut
  have hlimit :=
    graphonInducedDensity_tendsto_of_cutDist_tendsto_zero
      H (fun j ↦ graphGraphon (G' j)) W hcut'
  exact tendsto_nhds_unique hlimit hfinite

/-- The padding construction preserves the selected limiting edge density.
The proof is uniform over all members of each padded family: selected
members have the common exact edge count, while unselected members are the
prescribed approximants.  Hence an arbitrary mixture of the two kinds has
the same density limit. -/
theorem paddedSelectedSliceFamily_limitSet_edgeDensity {h : ℕ}
    (H : SimpleGraph (Fin h)) (m : ℕ → ℕ) (σ : ℕ → ℕ)
    (A : (n : ℕ) → SimpleGraph (Fin (n + 1)))
    (hσ : StrictMono σ)
    (hne : ∀ j,
      (inducedFreeGraphFinsetWithEdges H (σ j) (m (σ j))).Nonempty)
    {γ : ℝ}
    (hm : Tendsto
      (fun j ↦ (m (σ j) : ℝ) /
        (completeEdgeCount (σ j) : ℝ)) atTop (nhds γ))
    {U : Graphon}
    (hAcut : Tendsto
      (fun n ↦ cutDist (graphGraphon (A n)) U) atTop (nhds 0))
    (hUedge : graphonEdgeDensity U = γ)
    {W : Graphon}
    (hW : W ∈ labeledGraphFamilyLimitSet
      (paddedSelectedSliceFamily H m σ A)) :
    graphonEdgeDensity W = γ := by
  let S : (j : ℕ) → SimpleGraph (Fin (σ j)) := fun j ↦
    Classical.choose (hne j)
  have hSmem (j : ℕ) :
      S j ∈ inducedFreeGraphFinsetWithEdges H (σ j) (m (σ j)) :=
    Classical.choose_spec (hne j)
  have hScount : Tendsto
      (fun j ↦ ((finiteGraphEdges (S j)).card : ℝ) /
        (completeEdgeCount (σ j) : ℝ)) atTop (nhds γ) := by
    apply hm.congr'
    filter_upwards [] with j
    rw [finiteGraphEdges_card_eq_edgeFinset_card,
      (mem_inducedFreeGraphFinsetWithEdges.mp (hSmem j)).2]
  have hselectedEdge : Tendsto
      (fun j ↦ graphonEdgeDensity (graphGraphon (S j)))
      atTop (nhds γ) :=
    graphonEdgeDensity_graphGraphon_tendsto_of_normalizedEdgeCount
      hσ.tendsto_atTop S hScount
  have hAedge : Tendsto
      (fun n ↦ graphonEdgeDensity (graphGraphon (A n)))
      atTop (nhds γ) := by
    rw [← hUedge]
    exact graphonEdgeDensity_tendsto_of_cutDist_tendsto_zero
      (fun n ↦ graphGraphon (A n)) U hAcut
  have hpaddingEdge : Tendsto
      (fun n ↦ graphonEdgeDensity
        (graphGraphon (approximationGraphAtOrder A n)))
      atTop (nhds γ) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [approximationGraphAtOrder_succ] using hAedge
  have huniform : ∀ s : Set ℝ, IsOpen s → γ ∈ s →
      ∀ᶠ n in atTop, ∀ G,
        G ∈ paddedSelectedSliceFamily H m σ A n →
          graphonEdgeDensity (graphGraphon G) ∈ s := by
    intro s hsopen hγs
    have hsselected := (tendsto_nhds.mp hselectedEdge) s hsopen hγs
    obtain ⟨K, hK⟩ := eventually_atTop.1 hsselected
    have hspadding := (tendsto_nhds.mp hpaddingEdge) s hsopen hγs
    filter_upwards [eventually_atTop.2
        ⟨max (σ K) 1, fun n hn ↦ hn⟩,
      hspadding] with n hnlarge hnpadding G hG
    have hnσ : σ K ≤ n := (le_max_left _ _).trans hnlarge
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one
      ((le_max_right (σ K) 1).trans hnlarge)
    by_cases hnselected : n ∈ Set.range σ
    · obtain ⟨j, rfl⟩ := hnselected
      have hKj : K ≤ j := (hσ.le_iff_le).mp hnσ
      have hGslice :
          G ∈ inducedFreeGraphFinsetWithEdges H (σ j) (m (σ j)) := by
        simpa [paddedSelectedSliceFamily] using hG
      have hedgeCount : G.edgeFinset.card = (S j).edgeFinset.card := by
        rw [(mem_inducedFreeGraphFinsetWithEdges.mp hGslice).2,
          (mem_inducedFreeGraphFinsetWithEdges.mp (hSmem j)).2]
      have hedge : graphonEdgeDensity (graphGraphon G) =
          graphonEdgeDensity (graphGraphon (S j)) := by
        rw [graphonEdgeDensity_graphGraphon hnpos,
          graphonEdgeDensity_graphGraphon hnpos,
          finiteGraphEdges_card_eq_edgeFinset_card,
          finiteGraphEdges_card_eq_edgeFinset_card, hedgeCount]
      rw [hedge]
      exact hK j hKj
    · have hGpadding : G = approximationGraphAtOrder A n := by
        have := hG
        rw [paddedSelectedSliceFamily_eq_padding H m σ A hnselected] at this
        simpa only [Finset.mem_singleton] using this
      rw [hGpadding]
      exact hnpadding
  obtain ⟨τ, hτ, G, hG, hcut⟩ := hW
  have hfinite : Tendsto
      (fun j ↦ graphonEdgeDensity (graphGraphon (G j)))
      atTop (nhds γ) := by
    apply tendsto_nhds.mpr
    intro s hsopen hγs
    have horders := hτ.tendsto_atTop.eventually
      (huniform s hsopen hγs)
    filter_upwards [horders] with j hj
    exact hj (G j) (hG j)
  have hlimit := graphonEdgeDensity_tendsto_of_cutDist_tendsto_zero
    (fun j ↦ graphGraphon (G j)) W hcut
  exact tendsto_nhds_unique hlimit hfinite

/-! ## HJS along the selected orders -/

/-- The published HJS upper bound applied to a selected exact-edge family.
The family is padded by induced-free approximants to the already-selected
cut limit `U`; the preceding two lemmas show that its entire limit set stays
inside the same full fixed-density domain. -/
theorem eventually_selectedSliceCount_le_fullEntropy {h : ℕ}
    (H : SimpleGraph (Fin h)) (m : ℕ → ℕ) (σ : ℕ → ℕ)
    (hσ : StrictMono σ)
    (G : (j : ℕ) → SimpleGraph (Fin (σ j)))
    (hG : ∀ j,
      G j ∈ inducedFreeGraphFinsetWithEdges H (σ j) (m (σ j)))
    {γ : ℝ} {U : Graphon}
    (hm : Tendsto
      (fun j ↦ (m (σ j) : ℝ) /
        (completeEdgeCount (σ j) : ℝ)) atTop (nhds γ))
    (hGcut : Tendsto
      (fun j ↦ cutDist (graphGraphon (G j)) U) atTop (nhds 0))
    (hUedge : graphonEdgeDensity U = γ)
    (hUfree : graphonInducedDensity H U = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop,
      normalizedLogGraphCount (σ j)
          (inducedFreeGraphCountWithEdges H (σ j) (m (σ j))) ≤
        inducedFreeFixedDensityEntropyValue H γ + ε := by
  obtain ⟨A, hAfree, _hAhom, hAcut⟩ :=
    PriorLiterature.existsInducedFreeApproximatingGraphSequence_cut
      H U hUfree
  let Q : (n : ℕ) → Finset (SimpleGraph (Fin n)) :=
    paddedSelectedSliceFamily H m σ A
  have hne (j : ℕ) :
      (inducedFreeGraphFinsetWithEdges H (σ j) (m (σ j))).Nonempty :=
    ⟨G j, hG j⟩
  have hQne : ∀ᶠ n in atTop, (Q n).Nonempty :=
    Eventually.of_forall
      (paddedSelectedSliceFamily_nonempty H m σ A hne)
  have hQlimitNonempty : (labeledGraphFamilyLimitSet Q).Nonempty := by
    refine ⟨U, σ, hσ, G, ?_, hGcut⟩
    intro j
    simpa only [Q, paddedSelectedSliceFamily_eq_selected_apply] using hG j
  have hQlimitSubset : labeledGraphFamilyLimitSet Q ⊆
      inducedFreeFixedDensityGraphons H γ := by
    intro W hW
    refine ⟨?_, ?_⟩
    · exact paddedSelectedSliceFamily_limitSet_edgeDensity
        H m σ A hσ hne hm hAcut hUedge hW
    · exact paddedSelectedSliceFamily_limitSet_inducedFree
        H m σ A hAfree hW
  have hsup : sSup (graphonEntropy '' labeledGraphFamilyLimitSet Q) ≤
      inducedFreeFixedDensityEntropyValue H γ :=
    graphonEntropy_sSup_le_inducedFreeFixedDensityEntropyValue
      H γ _ hQlimitNonempty hQlimitSubset
  have hHJS :=
    PriorLiterature.hatamiJansonSzegedyLabeledEntropyUpperBound
      Q hQne ε hε
  have hHJSselected := hσ.tendsto_atTop.eventually hHJS
  filter_upwards [hHJSselected] with j hj
  have hj' : normalizedLogGraphCount (σ j) (Q (σ j)).card ≤
      inducedFreeFixedDensityEntropyValue H γ + ε :=
    hj.trans (by linarith [hsup])
  simpa only [Q, paddedSelectedSliceFamily_eq_selected_apply,
    inducedFreeGraphCountWithEdges_eq_card] using hj'

/-! ## Generic subsequence and logarithm bridges -/

/-- A predicate that occurs frequently at natural infinity can be retained
along a strictly increasing sequence. -/
theorem exists_strictMono_forall_of_frequently_atTop
    {P : ℕ → Prop} (hP : ∃ᶠ n in atTop, P n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ j, P (σ j) := by
  have hcofinal : ∀ a : ℕ, ∃ b, a < b ∧ P b := by
    intro a
    obtain ⟨b, hab, hb⟩ := (frequently_atTop.mp hP) (a + 1)
    exact ⟨b, (Nat.lt_succ_self a).trans_le hab, hb⟩
  let next : ℕ → ℕ := fun a ↦ Classical.choose (hcofinal a)
  have hnext (a : ℕ) : a < next a ∧ P (next a) :=
    Classical.choose_spec (hcofinal a)
  let σ : ℕ → ℕ := fun j ↦ Nat.rec (next 0) (fun _ a ↦ next a) j
  have hstep (j : ℕ) : σ j < σ (j + 1) := by
    exact (hnext (σ j)).1
  have hmono : StrictMono σ := strictMono_nat_of_lt_succ hstep
  refine ⟨σ, hmono, ?_⟩
  intro j
  cases j with
  | zero => exact (hnext 0).2
  | succ j => exact (hnext (σ j)).2

/-- A nonempty induced-free graphon domain supplies induced-free finite
graphs, and hence positive `G(n,p)` event probability, at every positive
order.  This uses the already-approved induced-free approximation theorem. -/
theorem eventually_gnpInducedFreeProbability_pos_of_graphonDomain_nonempty
    {h : ℕ} (H : SimpleGraph (Fin h)) (p : ℝ)
    (hp : p ∈ Ioo (0 : ℝ) 1)
    (hdomain : (inducedFreeGraphons H).Nonempty) :
    ∀ᶠ n in atTop, 0 < gnpInducedFreeProbability H n p := by
  obtain ⟨W, hW⟩ := hdomain
  obtain ⟨A, hAfree, _hAhom, _hAcut⟩ :=
    PriorLiterature.existsInducedFreeApproximatingGraphSequence_cut H W hW
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn ↦ hn⟩] with n hn
  cases n with
  | zero => omega
  | succ j =>
      apply gnpInducedFreeProbability_pos_of_exactEdge_nonempty H hp
      refine ⟨A j, ?_⟩
      exact mem_inducedFreeGraphFinsetWithEdges.mpr ⟨hAfree j, rfl⟩

/-- Monotonicity and multiplicativity of the positive normalized logarithm. -/
theorem normalizedLogProbability_le_mul
    {n : ℕ} (hn : 2 ≤ n) {x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hle : z ≤ x * y) :
    normalizedLogProbability n z ≤
      normalizedLogProbability n x + normalizedLogProbability n y := by
  have hlog : log2 z ≤ log2 (x * y) := by
    unfold log2
    apply div_le_div_of_nonneg_right _ realLogTwo_pos.le
    exact Real.log_le_log hz hle
  rw [log2_mul hx.ne' hy.ne'] at hlog
  have hN : 0 < (completeEdgeCount n : ℝ) := by
    exact_mod_cast Nat.choose_pos hn
  unfold normalizedLogProbability normalizedLogAtGraphOrder
  calc
    log2 z / (completeEdgeCount n : ℝ) ≤
        (log2 x + log2 y) / (completeEdgeCount n : ℝ) :=
      (div_le_div_iff_of_pos_right hN).2 hlog
    _ = log2 x / (completeEdgeCount n : ℝ) +
        log2 y / (completeEdgeCount n : ℝ) := by ring

/-- At a nonempty fixed-density fiber, the entropy supremum plus the exact
binomial edge exponent is bounded by the negative full-domain KL infimum. -/
theorem inducedFreeFixedDensityEntropyValue_add_odds_le_neg_rate
    {h : ℕ} (H : SimpleGraph (Fin h)) (p : ℝ)
    (hp : p ∈ Ioo (0 : ℝ) 1) (γ : ℝ)
    (hne : (inducedFreeFixedDensityGraphons H γ).Nonempty) :
    inducedFreeFixedDensityEntropyValue H γ +
        γ * log2 (p / (1 - p)) + log2 (1 - p) ≤
      -inducedFreeGraphonRateValue H p := by
  have hodds : log2 ((1 - p) / p) = -log2 (p / (1 - p)) := by
    rw [log2_div (sub_pos.mpr hp.2).ne' hp.1.ne',
      log2_div hp.1.ne' (sub_pos.mpr hp.2).ne']
    ring
  have hsup : inducedFreeFixedDensityEntropyValue H γ ≤
      -inducedFreeGraphonRateValue H p -
        γ * log2 (p / (1 - p)) - log2 (1 - p) := by
    unfold inducedFreeFixedDensityEntropyValue
    apply csSup_le (hne.image graphonEntropy)
    rintro z ⟨W, hW, rfl⟩
    have hrate := inducedFreeGraphonRateValue_le H p hp hW.2
    rw [graphonRelativeEntropy_eq_negEntropy_add_edge hp W,
      hW.1, hodds] at hrate
    linarith
  linarith

/-! ## The full weighted upper bound -/

/-- Local weighted graph-family upper bound (the corrected form of the
upper-bound step in the unpublished Proposition 2.10; see `CFD-006`).

The epsilon-eventual conclusion is equivalent to the asserted limsup
inequality.  The proof selects a frequently violating sequence, maximizes an
exact-edge slice at every selected order, compactifies first its edge
densities and then its adjacency graphons, and applies HJS to the padded
family.  The polynomial number of edge levels contributes a vanishing term. -/
theorem inducedFreeGnp_limsup_le_fullRate
    {h : ℕ} (H : SimpleGraph (Fin h)) (p : ℝ)
    (hp : p ∈ Ioo (0 : ℝ) 1)
    (hdomain : (inducedFreeGraphons H).Nonempty) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      normalizedLogGnpInducedFreeProbability H n p ≤
        -inducedFreeGraphonRateValue H p + ε := by
  intro ε hε
  by_contra hnot
  have hbad : ∃ᶠ n in atTop,
      -inducedFreeGraphonRateValue H p + ε <
        normalizedLogGnpInducedFreeProbability H n p := by
    exact (not_eventually.mp hnot).mono fun n hn ↦ lt_of_not_ge hn
  have hpositive :=
    eventually_gnpInducedFreeProbability_pos_of_graphonDomain_nonempty
      H p hp hdomain
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    eventually_atTop.2 ⟨2, fun _ hn ↦ hn⟩
  have hfrequent : ∃ᶠ n in atTop,
      (-inducedFreeGraphonRateValue H p + ε <
          normalizedLogGnpInducedFreeProbability H n p) ∧
        0 < gnpInducedFreeProbability H n p ∧ 2 ≤ n :=
    (hbad.and_eventually (hpositive.and hlarge)).mono fun _ hn ↦
      ⟨hn.1, hn.2.1, hn.2.2⟩
  obtain ⟨σ, hσ, hσgood⟩ :=
    exists_strictMono_forall_of_frequently_atTop hfrequent
  let m : ℕ → ℕ := fun n ↦
    maximizingInducedFreeEdgeCount H n p
  have hmle (n : ℕ) : m n ≤ completeEdgeCount n := by
    exact maximizingInducedFreeEdgeCount_le_completeEdgeCount H n p
  let density : ℕ → ℝ := fun j ↦
    (m (σ j) : ℝ) / (completeEdgeCount (σ j) : ℝ)
  have hdensity (j : ℕ) : density j ∈ Set.Icc (0 : ℝ) 1 := by
    have hN : 0 < (completeEdgeCount (σ j) : ℝ) := by
      exact_mod_cast Nat.choose_pos (hσgood j).2.2
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hN.le
    · exact (div_le_one hN).2 (by exact_mod_cast hmle (σ j))
  obtain ⟨γ, hγ, τ, hτ, hDensity⟩ :=
    isCompact_Icc.tendsto_subseq hdensity
  let ρ : ℕ → ℕ := σ ∘ τ
  have hρ : StrictMono ρ := hσ.comp hτ
  have hρgood (j : ℕ) :
      (-inducedFreeGraphonRateValue H p + ε <
          normalizedLogGnpInducedFreeProbability H (ρ j) p) ∧
        0 < gnpInducedFreeProbability H (ρ j) p ∧ 2 ≤ ρ j := by
    exact hσgood (τ j)
  have hρdensity : Tendsto
      (fun j ↦ (m (ρ j) : ℝ) /
        (completeEdgeCount (ρ j) : ℝ)) atTop (nhds γ) := by
    simpa [density, ρ, Function.comp_def] using hDensity
  have hsliceNonempty (j : ℕ) :
      (inducedFreeGraphFinsetWithEdges H (ρ j) (m (ρ j))).Nonempty := by
    exact maximizingInducedFreeSlice_nonempty_of_probability_pos
      H (ρ j) hp (hρgood j).2.1
  let G : (j : ℕ) → SimpleGraph (Fin (ρ j)) := fun j ↦
    Classical.choose (hsliceNonempty j)
  have hG (j : ℕ) :
      G j ∈ inducedFreeGraphFinsetWithEdges H (ρ j) (m (ρ j)) :=
    Classical.choose_spec (hsliceNonempty j)
  obtain ⟨κ, hκ, U, hcut⟩ :=
    PriorLiterature.bclsvGraphonSequentialCompactness
      (fun j ↦ graphGraphon (G j))
  let ξ : ℕ → ℕ := ρ ∘ κ
  let G' : (j : ℕ) → SimpleGraph (Fin (ξ j)) := fun j ↦ G (κ j)
  have hξ : StrictMono ξ := hρ.comp hκ
  have hG' (j : ℕ) :
      G' j ∈ inducedFreeGraphFinsetWithEdges H (ξ j) (m (ξ j)) :=
    hG (κ j)
  have hξdensity : Tendsto
      (fun j ↦ (m (ξ j) : ℝ) /
        (completeEdgeCount (ξ j) : ℝ)) atTop (nhds γ) := by
    simpa [ξ, Function.comp_def] using
      hρdensity.comp hκ.tendsto_atTop
  have hG'cut : Tendsto
      (fun j ↦ cutDist (graphGraphon (G' j)) U) atTop (nhds 0) := by
    simpa only [G', Function.comp_apply] using hcut
  have hfiniteEdgeCount : Tendsto
      (fun j ↦ ((finiteGraphEdges (G' j)).card : ℝ) /
        (completeEdgeCount (ξ j) : ℝ)) atTop (nhds γ) := by
    apply hξdensity.congr'
    filter_upwards [] with j
    rw [finiteGraphEdges_card_eq_edgeFinset_card,
      (mem_inducedFreeGraphFinsetWithEdges.mp (hG' j)).2]
  have hfiniteEdgeDensity :=
    graphonEdgeDensity_graphGraphon_tendsto_of_normalizedEdgeCount
      hξ.tendsto_atTop G' hfiniteEdgeCount
  have hlimitEdgeDensity :=
    graphonEdgeDensity_tendsto_of_cutDist_tendsto_zero
      (fun j ↦ graphGraphon (G' j)) U hG'cut
  have hUedge : graphonEdgeDensity U = γ :=
    tendsto_nhds_unique hlimitEdgeDensity hfiniteEdgeDensity
  have hG'free (j : ℕ) :
      ¬ Regularity.InducedEmbeds H (G' j) :=
    (mem_inducedFreeGraphFinsetWithEdges.mp (hG' j)).1
  have hfiniteInducedDensity :=
    graphonInducedDensity_graphGraphon_tendsto_zero_of_inducedFree
      H hξ.tendsto_atTop G' hG'free
  have hlimitInducedDensity :=
    graphonInducedDensity_tendsto_of_cutDist_tendsto_zero
      H (fun j ↦ graphGraphon (G' j)) U hG'cut
  have hUfree : graphonInducedDensity H U = 0 :=
    tendsto_nhds_unique hlimitInducedDensity hfiniteInducedDensity
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hcountUpper := eventually_selectedSliceCount_le_fullEntropy
    H m ξ hξ G' hG' hξdensity hG'cut hUedge hUfree δ hδ
  have hoddsLimit : Tendsto
      (fun j ↦ (m (ξ j) : ℝ) /
          (completeEdgeCount (ξ j) : ℝ) * log2 (p / (1 - p)))
      atTop (nhds (γ * log2 (p / (1 - p)))) :=
    hξdensity.mul_const _
  have hoddsUpper : ∀ᶠ j in atTop,
      (m (ξ j) : ℝ) / (completeEdgeCount (ξ j) : ℝ) *
          log2 (p / (1 - p)) <
        γ * log2 (p / (1 - p)) + δ :=
    (tendsto_order.1 hoddsLimit).2 _ (lt_add_of_pos_right _ hδ)
  have hfactorLimit :=
    normalizedLogPolynomialSliceFactor_tendsto_zero.comp hξ.tendsto_atTop
  have hfactorUpper : ∀ᶠ j in atTop,
      normalizedLogProbability (ξ j)
          ((completeEdgeCount (ξ j) : ℝ) + 1) < δ :=
    (tendsto_order.1 hfactorLimit).2 _ hδ
  have hrateFiber :
      inducedFreeFixedDensityEntropyValue H γ +
          γ * log2 (p / (1 - p)) + log2 (1 - p) ≤
        -inducedFreeGraphonRateValue H p :=
    inducedFreeFixedDensityEntropyValue_add_odds_le_neg_rate
      H p hp γ ⟨U, hUedge, hUfree⟩
  have hcontradiction : ∀ᶠ _j : ℕ in atTop, False := by
    filter_upwards [hcountUpper, hoddsUpper, hfactorUpper] with
      j hcount hodds hfactor
    have hjgood :
        (-inducedFreeGraphonRateValue H p + ε <
            normalizedLogGnpInducedFreeProbability H (ξ j) p) ∧
          0 < gnpInducedFreeProbability H (ξ j) p ∧ 2 ≤ ξ j := by
      simpa [ξ, ρ, Function.comp_def] using hρgood (κ j)
    have hjbad := hjgood.1
    have hjprob := hjgood.2.1
    have hjlarge := hjgood.2.2
    have hjcount : 0 < inducedFreeGraphCountWithEdges H (ξ j) (m (ξ j)) := by
      exact maximizingInducedFreeSlice_count_pos_of_probability_pos
        H (ξ j) hp hjprob
    have hjmax : 0 < maximalInducedFreeSliceWeight H (ξ j) p :=
      maximalInducedFreeSliceWeight_pos_of_probability_pos
        H (ξ j) p hjprob
    have hjfactor : 0 < (completeEdgeCount (ξ j) : ℝ) + 1 := by
      positivity
    have hjprobUpper : normalizedLogGnpInducedFreeProbability H (ξ j) p ≤
        normalizedLogProbability (ξ j)
            ((completeEdgeCount (ξ j) : ℝ) + 1) +
          normalizedLogProbability (ξ j)
            (maximalInducedFreeSliceWeight H (ξ j) p) := by
      apply normalizedLogProbability_le_mul hjlarge hjfactor hjmax hjprob
      simpa only [Nat.cast_add, Nat.cast_one] using
        gnpInducedFreeProbability_le_card_mul_maximalSlice H (ξ j) p
    have hjExponent := normalizedLogGnpInducedFreeSliceWeight_eq_odds
      H (ξ j) (m (ξ j)) p hp (hmle (ξ j)) hjcount hjlarge
    have hjMaxExponent :
        normalizedLogProbability (ξ j)
            (maximalInducedFreeSliceWeight H (ξ j) p) =
          normalizedLogGraphCount (ξ j)
              (inducedFreeGraphCountWithEdges H (ξ j) (m (ξ j))) +
            (m (ξ j) : ℝ) / (completeEdgeCount (ξ j) : ℝ) *
              log2 (p / (1 - p)) + log2 (1 - p) := by
      rw [maximalInducedFreeSliceWeight_eq_selected]
      simpa only [m] using hjExponent
    rw [hjMaxExponent] at hjprobUpper
    dsimp [δ] at hcount hodds hfactor
    have hcount' :
        normalizedLogGraphCount (ξ j)
            (inducedFreeGraphCountWithEdges H (ξ j) (m (ξ j))) ≤
          inducedFreeFixedDensityEntropyValue H γ + ε / 4 := by
      simpa only [inducedFreeGraphCountWithEdges] using hcount
    have hsliceExponentUpper :
        normalizedLogGraphCount (ξ j)
              (inducedFreeGraphCountWithEdges H (ξ j) (m (ξ j))) +
            (m (ξ j) : ℝ) / (completeEdgeCount (ξ j) : ℝ) *
              log2 (p / (1 - p)) + log2 (1 - p) <
          -inducedFreeGraphonRateValue H p + ε / 2 := by
      linarith [hcount', hodds, hrateFiber]
    have hprobStrict :
        normalizedLogGnpInducedFreeProbability H (ξ j) p <
          -inducedFreeGraphonRateValue H p + 3 * ε / 4 := by
      linarith [hjprobUpper, hfactor, hsliceExponentUpper]
    linarith [hjbad, hprobStrict, hε]
  obtain ⟨j, hj⟩ := hcontradiction.exists
  exact hj

end InducedStars
