import InducedStars.Structure.Subcritical.ActiveLevelComparison
import InducedStars.Structure.Subcritical.RetainedMembership
import InducedStars.Structure.Subcritical.ProfileLeftover

/-!
# Finite capacity and signed headroom for the master profile bound

Paper: the active-level application in the proof of
`lemma:profile-bound-K1k`. The estimates below quantify its parameter reserve;
all exponential coefficients use natural logarithms in the natural-unit convention.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Every retained part meets an active core edge, including when the
retained family itself may be empty. -/
theorem retainedPart_exists_incident_activePair
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (hk : 3 ≤ k)
    {a : D.PartIndex} (ha : a ∈ D.retainedPartIndices eta R₀) :
    ∃ e : RetainedActivePair D eta R₀, a = e.leftPart ∨ a = e.rightPart := by
  have hpos : 0 < (D.core a.1).graph.degree a.2 := by
    rw [(D.core a.1).degree_eq]
    omega
  obtain ⟨b, hab⟩ := ((D.core a.1).graph.degree_pos_iff_exists_adj a.2).mp hpos
  have hi := (D.mem_retainedPartIndices eta R₀ a).mp ha
  rcases lt_or_gt_of_ne hab.ne with hlt | hgt
  · exact ⟨⟨a.1, hi, a.2, b, hlt, hab⟩, Or.inl (by cases a; rfl)⟩
  · exact ⟨⟨a.1, hi, b, a.2, hgt, hab.symm⟩, Or.inr (by cases a; rfl)⟩

private theorem choose_two_le_product_of_le_twice {a b : ℕ} (hab : a ≤ 2 * b) :
    a.choose 2 ≤ a * b := by
  have hd : a.choose 2 * 2 ≤ a * (a - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.div_mul_le_self _ _
  have hs := Nat.mul_le_mul_left a (Nat.sub_le a 1)
  have hh := Nat.mul_le_mul_left a hab
  nlinarith

/-- The clique capacity is at most twice the active capacity under a
factor-two balance condition on each retained component. This is a finite
geometric theorem and does not require any graph or density witness. -/
theorem retainedCliqueCapacity_le_two_mul_activeTotalCapacity
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (hk : 3 ≤ k)
    (hbalance : ∀ i ∈ D.retainedComponentIndices eta R₀,
      ∀ a b : Fin (D.core i).order, (D.parts i a).card ≤ 2 * (D.parts i b).card) :
    retainedCliqueCapacity D eta R₀ ≤ 2 * retainedActiveTotalCapacity D eta R₀ := by
  have hcover (a : D.PartIndex) (ha : a ∈ D.retainedPartIndices eta R₀) :
      (D.part a).card.choose 2 ≤
        ∑ e : RetainedActivePair D eta R₀,
          if a = e.leftPart ∨ a = e.rightPart then (D.part a).card.choose 2 else 0 := by
    obtain ⟨e, he⟩ := retainedPart_exists_incident_activePair D eta R₀ hk ha
    have h := Finset.single_le_sum (f := fun e : RetainedActivePair D eta R₀ ↦
      if a = e.leftPart ∨ a = e.rightPart then (D.part a).card.choose 2 else 0)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ e)
    simpa only [ite_eq_left he] using h
  calc
    retainedCliqueCapacity D eta R₀ ≤
        ∑ a ∈ D.retainedPartIndices eta R₀, ∑ e : RetainedActivePair D eta R₀,
          if a = e.leftPart ∨ a = e.rightPart then (D.part a).card.choose 2 else 0 :=
      Finset.sum_le_sum hcover
    _ = ∑ e : RetainedActivePair D eta R₀,
        ((D.part e.leftPart).card.choose 2 + (D.part e.rightPart).card.choose 2) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      have hsplit (a : D.PartIndex) :
          (if a = e.leftPart ∨ a = e.rightPart then (D.part a).card.choose 2 else 0) =
            (if a = e.leftPart then (D.part a).card.choose 2 else 0) +
            (if a = e.rightPart then (D.part a).card.choose 2 else 0) := by
        by_cases hl : a = e.leftPart
        · subst a
          simp [e.leftPart_ne_rightPart]
        · simp [hl]
      simp_rw [hsplit]
      simp [Finset.sum_add_distrib, e.leftPart_mem_retained, e.rightPart_mem_retained]
    _ ≤ ∑ e : RetainedActivePair D eta R₀, 2 * retainedActiveCapacity D eta R₀ e := by
      apply Finset.sum_le_sum
      intro e _
      have hl := choose_two_le_product_of_le_twice
        (hbalance e.component e.component_retained e.left e.right)
      have hr := choose_two_le_product_of_le_twice
        (hbalance e.component e.component_retained e.right e.left)
      change (D.parts e.component e.left).card.choose 2 +
        (D.parts e.component e.right).card.choose 2 ≤
          2 * ((D.parts e.component e.left).card * (D.parts e.component e.right).card)
      nlinarith
    _ = _ := by rw [← Finset.mul_sum]; rfl

/-- Every capacity-bounded vector has total count bounded by the total
active capacity; the empty active index set is included. -/
theorem retainedEdgeCountTotal_le_activeTotalCapacity
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (v : RetainedEdgeCountVector D eta R₀) :
    retainedEdgeCountTotal v ≤ retainedActiveTotalCapacity D eta R₀ :=
  Finset.sum_le_sum (fun e _ ↦ v.count_le_capacity e)

namespace SubcriticalCloseStructureResult

/-- The completed close-structure ratio supplies the factor-two comparison
on all retained components. No nonempty-retained hypothesis is required. -/
theorem retainedCliqueCapacity_le_two_mul_activeTotalCapacity
    {n R₀ : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
    {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
    {omega eta theta alpha delta epsilon : ℝ}
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (homega : omega ≤ 1)
    (hvisible : D.retainedComponentIndices eta R₀ ⊆ D.visibleComponentIndices theta) :
    retainedCliqueCapacity D eta R₀ ≤ 2 * retainedActiveTotalCapacity D eta R₀ := by
  apply InducedStars.retainedCliqueCapacity_le_two_mul_activeTotalCapacity D eta R₀ hk
  intro i hi a b
  have h := R.visible_component_ratio i (hvisible hi) a b
  have hb : (0 : ℝ) ≤ (D.parts i b).card := by positivity
  have htwo : ((D.parts i a).card : ℝ) ≤ 2 * (D.parts i b).card := by nlinarith
  exact_mod_cast htwo

end SubcriticalCloseStructureResult

/-- The actual exact-edge identity and the strong one-error sparse shift
bound force quadratic active capacity. The coefficient is exactly `γ/48`. -/
theorem retainedActiveTotalCapacity_lower_of_actual_bounds
    {n R₀ m : ℕ} (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n))
    {eta gamma C epsilon : ℝ}
    (hclique : retainedCliqueCapacity D eta R₀ ≤ 2 * retainedActiveTotalCapacity D eta R₀)
    (hedges : (finiteGraphEdges G).card = m)
    (hsparse : (inducedEdgeCount G (D.nonretainedVertices eta R₀) : ℝ) ≤
      C * eta * (n : ℝ) ^ 2)
    (hdefect : (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ) ^ 2)
    (hdensity : gamma / 8 * (n : ℝ) ^ 2 ≤ (m : ℝ))
    (hreserve : C * eta + epsilon ≤ gamma / 16) :
    gamma / 48 * (n : ℝ) ^ 2 ≤ retainedActiveTotalCapacity D eta R₀ := by
  have hshift := (retainedEdgeShift_mem_strongWindow_of_bounds G D hsparse hdefect).2
  have hcount := retainedEdgeCountTotal_le_activeTotalCapacity
    (actualRetainedEdgeCountVector G D eta R₀)
  have hcliqueR : (retainedCliqueCapacity D eta R₀ : ℝ) ≤
      2 * retainedActiveTotalCapacity D eta R₀ := by exact_mod_cast hclique
  have hcountR : (retainedEdgeCountTotal (actualRetainedEdgeCountVector G D eta R₀) : ℝ) ≤
      retainedActiveTotalCapacity D eta R₀ := by exact_mod_cast hcount
  have heq := retainedEdgeCountTotal_add_shift G D eta R₀
  rw [hedges] at heq
  have heqR : (retainedCliqueCapacity D eta R₀ : ℝ) +
      retainedEdgeCountTotal (actualRetainedEdgeCountVector G D eta R₀) +
      retainedEdgeShift G D eta R₀ = (m : ℝ) := by exact_mod_cast heq
  have hres := mul_le_mul_of_nonneg_right hreserve (sq_nonneg (n : ℝ))
  nlinarith

/-- Explicit numerical closure of the profile shift headroom. -/
theorem profileSignedShift_headroom_of_capacity_lower
    {n : ℕ} {A : ℕ} {gamma delta epsilon : ℝ}
    (hd : 0 ≤ delta) (hcapacity : gamma / 48 * (n : ℝ) ^ 2 ≤ A)
    (hepsilon : epsilon ≤ delta * gamma / 192) :
    epsilon * (n : ℝ) ^ 2 ≤ delta * A / 4 := by
  have hcap := mul_le_mul_of_nonneg_left hcapacity hd
  have heps := mul_le_mul_of_nonneg_right hepsilon (sq_nonneg (n : ℝ))
  nlinarith

/-- The actual graph closes both the active-capacity and shift reserves;
this is the finite headroom package for the master profile proof. -/
theorem profileActiveCapacity_and_shiftHeadroom
    {n R₀ m : ℕ} (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n))
    {eta gamma C delta epsilon : ℝ}
    (hclique : retainedCliqueCapacity D eta R₀ ≤ 2 * retainedActiveTotalCapacity D eta R₀)
    (hedges : (finiteGraphEdges G).card = m)
    (hsparse : (inducedEdgeCount G (D.nonretainedVertices eta R₀) : ℝ) ≤
      C * eta * (n : ℝ) ^ 2)
    (hdefect : (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ) ^ 2)
    (hdensity : gamma / 8 * (n : ℝ) ^ 2 ≤ (m : ℝ))
    (hreserve : C * eta + epsilon ≤ gamma / 16)
    (hd : 0 ≤ delta) (hepsilon : epsilon ≤ delta * gamma / 192) :
    gamma / 48 * (n : ℝ) ^ 2 ≤ retainedActiveTotalCapacity D eta R₀ ∧
      epsilon * (n : ℝ) ^ 2 ≤ delta * retainedActiveTotalCapacity D eta R₀ / 4 := by
  have hcap := retainedActiveTotalCapacity_lower_of_actual_bounds G D hclique hedges
    hsparse hdefect hdensity hreserve
  exact ⟨hcap, profileSignedShift_headroom_of_capacity_lower hd hcap hepsilon⟩

namespace SubcriticalCloseStructureResult

/-- Close structure and the already-proved strong sparse-side estimate
give the complete finite reserve needed by profile counting. -/
theorem profileActiveCapacityHeadroom
    {n R₀ m : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
    {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
    {omega eta theta alpha delta epsilon gamma C : ℝ}
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hR₀ : 1 ≤ R₀) (htheta : 0 ≤ theta) (homega : omega ≤ 1)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ)))
    (hedges : (finiteGraphEdges G).card = m)
    (hsparse : (inducedEdgeCount G (D.nonretainedVertices eta R₀) : ℝ) ≤
      C * eta * (n : ℝ) ^ 2)
    (hdensity : gamma / 8 * (n : ℝ) ^ 2 ≤ (m : ℝ))
    (hreserve : C * eta + epsilon ≤ gamma / 16)
    (hd : 0 ≤ delta) (hepsilon : epsilon ≤ delta * gamma / 192) :
    gamma / 48 * (n : ℝ) ^ 2 ≤ retainedActiveTotalCapacity D eta R₀ ∧
      epsilon * (n : ℝ) ^ 2 ≤ delta * retainedActiveTotalCapacity D eta R₀ / 4 := by
  have hc := R.retainedCliqueCapacity_le_two_mul_activeTotalCapacity homega
    (D.retainedComponentIndices_subset_visibleComponentIndices hR₀ htheta hcutoff)
  exact profileActiveCapacity_and_shiftHeadroom G D hc hedges hsparse R.defect_cost_le
    hdensity hreserve hd hepsilon

/-- Reuse the existing integer-rounding threshold at the retained-part
scale. This does not reprove or alter the discrete headroom allocator. -/
theorem profileActiveRoundingReserve
    {n R₀ : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
    {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
    {omega eta theta alpha delta epsilon : ℝ}
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hR₀ : 1 ≤ R₀) (heta : 0 ≤ eta) (htheta : 0 < theta) (hdelta : 0 < delta)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ)))
    (hn : subcriticalActiveRoundingThreshold delta theta ≤ n) :
    ∀ e, 2 ≤ delta * retainedActiveCapacity D eta R₀ e :=
  retainedActiveCapacity_rounding_reserve_of_order_ge D eta R₀ hdelta htheta hn
    (fun _ ha ↦ R.retainedPart_card_ge_theta hR₀ heta hcutoff ha)

end SubcriticalCloseStructureResult

/-- Signed size is additive on disjoint unordered edge sets, including
missing clique edges with their negative weights. -/
theorem subcriticalSignedDefectSize_sup_of_edge_disjoint
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (T U : SimpleGraph V)
    (hdis : Disjoint (finiteGraphEdges T) (finiteGraphEdges U)) :
    subcriticalSignedDefectSize D eta R₀ (T ⊔ U) =
      subcriticalSignedDefectSize D eta R₀ T + subcriticalSignedDefectSize D eta R₀ U := by
  have hedge : finiteGraphEdges (T ⊔ U) = finiteGraphEdges T ∪ finiteGraphEdges U := by
    ext z
    simp [mem_finiteGraphEdges, SimpleGraph.edgeSet_sup]
  have hdisI : Disjoint
      (finiteGraphEdges T ∩ retainedCliquePotentialEdges D eta R₀)
      (finiteGraphEdges U ∩ retainedCliquePotentialEdges D eta R₀) :=
    hdis.mono Finset.inter_subset_left Finset.inter_subset_left
  simp only [subcriticalSignedDefectSize, hedge, Finset.union_inter_distrib_right,
    Finset.card_union_of_disjoint hdis, Finset.card_union_of_disjoint hdisI, Nat.cast_add]
  ring

/-- The retained-incident pattern is an actual subgraph of the combined
defect graph whose cardinality is the canonical objective. -/
theorem card_subcriticalRetainedIncidentDefectGraph_le_defectCost
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    (finiteGraphEdges (subcriticalRetainedIncidentDefectGraph G D eta R₀)).card ≤
      subcriticalDefectCost G D := by
  apply Finset.card_le_card
  intro z hz
  induction z using Sym2.inductionOn with
  | hf x y =>
      rw [mem_finiteGraphEdges, SimpleGraph.mem_edgeSet] at hz ⊢
      exact ((subcriticalDefectGraph_adj G D x y).mp hz.1).1

/-- A compatible triple keeps its exact total signed size. This identity
uses its actual profile witness, not a formal sum with a guessed sign. -/
theorem SubcriticalCompatibleDefectTriple.signedSize_eq
    {F : Finset (SimpleGraph V)} {D : SubcriticalDivision k V}
    {eta theta alpha : ℝ} {R₀ : ℕ} {p : SubcriticalProfile D eta R₀ theta}
    {TB R L : SimpleGraph V} (h : SubcriticalCompatibleDefectTriple F alpha p TB R L) :
    subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L) =
      subcriticalSignedDefectSize D eta R₀ TB + subcriticalSignedDefectSize D eta R₀ R +
        subcriticalSignedDefectSize D eta R₀ L := by
  obtain ⟨_, hBR, hBL, hRL⟩ := h.decomposition
  have hdis : Disjoint (finiteGraphEdges (TB ⊔ R)) (finiteGraphEdges L) := by
    have hedge : finiteGraphEdges (TB ⊔ R) = finiteGraphEdges TB ∪ finiteGraphEdges R := by
      ext z
      simp [mem_finiteGraphEdges, SimpleGraph.edgeSet_sup]
    rw [hedge, Finset.disjoint_union_left]
    exact ⟨hBL, hRL⟩
  rw [subcriticalSignedDefectSize_sup_of_edge_disjoint D eta R₀ _ _ hdis,
    subcriticalSignedDefectSize_sup_of_edge_disjoint D eta R₀ _ _ hBR]

/-- Strong compatible-triple control: the absolute sum of signed sizes is
bounded by the actual retained defect count, which is bounded by the
objective of one graph in the realized profile class. -/
theorem SubcriticalCompatibleDefectTriple.exists_signedSize_bound
    {F : Finset (SimpleGraph V)} {D : SubcriticalDivision k V}
    {eta theta alpha : ℝ} {R₀ : ℕ} {p : SubcriticalProfile D eta R₀ theta}
    {TB R L : SimpleGraph V} (h : SubcriticalCompatibleDefectTriple F alpha p TB R L) :
    ∃ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      |subcriticalSignedDefectSize D eta R₀ TB + subcriticalSignedDefectSize D eta R₀ R +
          subcriticalSignedDefectSize D eta R₀ L| ≤ (finiteGraphEdges (TB ⊔ R ⊔ L)).card ∧
        (finiteGraphEdges (TB ⊔ R ⊔ L)).card ≤ subcriticalDefectCost G D := by
  obtain ⟨⟨G, hG, hgraph⟩, _⟩ := h.decomposition
  refine ⟨G, hG, ?_, ?_⟩
  · rw [← h.signedSize_eq]
    exact abs_subcriticalSignedDefectSize_le D eta R₀ _
  · rw [← hgraph]
    exact card_subcriticalRetainedIncidentDefectGraph_le_defectCost G D eta R₀

/-- The profile defect bound supplies the signed shift reserve with one
copy of the canonical error, not a separate error for each of three pieces. -/
theorem SubcriticalCompatibleDefectTriple.signedSize_le_of_defect_bound
    {n R₀ : ℕ} {F : Finset (SimpleGraph (Fin n))}
    {D : SubcriticalDivision k (Fin n)} {eta theta alpha epsilon : ℝ}
    {p : SubcriticalProfile D eta R₀ theta} {TB R L : SimpleGraph (Fin n)}
    (h : SubcriticalCompatibleDefectTriple F alpha p TB R L)
    (hdefect : ∀ G ∈ F, (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ) ^ 2) :
    (finiteGraphEdges (TB ⊔ R ⊔ L)).card ≤ epsilon * (n : ℝ) ^ 2 ∧
      |((subcriticalSignedDefectSize D eta R₀ TB + subcriticalSignedDefectSize D eta R₀ R +
        subcriticalSignedDefectSize D eta R₀ L : ℤ) : ℝ)| ≤ epsilon * (n : ℝ) ^ 2 := by
  obtain ⟨G, hG, hsigned, hcard⟩ := h.exists_signedSize_bound
  have hbound := hdefect G (mem_subcriticalProfileClassGraphFinset.mp hG).1
  have hcardR : (finiteGraphEdges (TB ⊔ R ⊔ L)).card ≤ (subcriticalDefectCost G D : ℝ) := by
    exact_mod_cast hcard
  have hsignedR :
      |((subcriticalSignedDefectSize D eta R₀ TB + subcriticalSignedDefectSize D eta R₀ R +
        subcriticalSignedDefectSize D eta R₀ L : ℤ) : ℝ)| ≤
          (finiteGraphEdges (TB ⊔ R ⊔ L)).card := by exact_mod_cast hsigned
  exact ⟨hcardR.trans hbound, hsignedR.trans (hcardR.trans hbound)⟩

/-- The compatible total signed size lies in the exact quarter-capacity
window once the explicit numerical reserve is imposed. -/
theorem SubcriticalCompatibleDefectTriple.activeLevelHeadroom
    {n R₀ : ℕ} {F : Finset (SimpleGraph (Fin n))}
    {D : SubcriticalDivision k (Fin n)} {eta theta alpha delta epsilon gamma : ℝ}
    {p : SubcriticalProfile D eta R₀ theta} {TB R L : SimpleGraph (Fin n)}
    (h : SubcriticalCompatibleDefectTriple F alpha p TB R L)
    (hdefect : ∀ G ∈ F, (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ) ^ 2)
    (hd : 0 ≤ delta)
    (hcapacity : gamma / 48 * (n : ℝ) ^ 2 ≤ retainedActiveTotalCapacity D eta R₀)
    (hepsilon : epsilon ≤ delta * gamma / 192) :
    |((subcriticalSignedDefectSize D eta R₀ TB + subcriticalSignedDefectSize D eta R₀ R +
      subcriticalSignedDefectSize D eta R₀ L : ℤ) : ℝ)| ≤
        delta * retainedActiveTotalCapacity D eta R₀ / 4 :=
  (h.signedSize_le_of_defect_bound hdefect).2.trans
    (profileSignedShift_headroom_of_capacity_lower hd hcapacity hepsilon)

/-- The signed level corollary used by profile counting: positive signed
defects lower the exponential weight. The two natural adjustments are the
positive and negative parts of the actual integer shift. -/
theorem subcriticalActiveLevelComparison_signed
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m : ℕ)
    (hk : 3 ≤ k) (hn : 2 ≤ Fintype.card V) {delta : ℝ} (hd : 0 ≤ delta)
    (hdp : 6 * delta ≤ pK k) (hdq : 6 * delta ≤ 1 - pK k)
    (hreserve : ∀ e, 2 ≤ delta * retainedActiveCapacity D eta R₀ e)
    (b s : ℤ)
    (hdist : |(s : ℝ)| ≤ delta * retainedActiveTotalCapacity D eta R₀ / 4) :
    (retainedNarrowPartitionFunction D eta R₀ m delta (b + s) : ℝ) ≤
      (Fintype.card V : ℝ) ^ (3 * Fintype.card (RetainedActivePair D eta R₀)) *
        (retainedPartitionFunction D eta R₀ m delta b : ℝ) *
        Real.exp (-subcriticalLogOddsNat k * s +
          subcriticalActiveLevelConstant k * delta * |(s : ℝ)|) := by
  have hsplit : (s.toNat : ℤ) - (-s).toNat = s := by omega
  have hsum : (s.toNat : ℤ) + (-s).toNat = |s| := by
    by_cases hs : 0 ≤ s
    · rw [abs_of_nonneg hs]
      omega
    · rw [abs_of_nonpos (by omega)]
      omega
  have hsplitR : (s.toNat : ℝ) - (-s).toNat = s := by exact_mod_cast hsplit
  have hsumR : (s.toNat : ℝ) + (-s).toNat = |(s : ℝ)| := by exact_mod_cast hsum
  have h := subcriticalActiveLevelComparison D eta R₀ m hk hn hd hdp hdq hreserve
    (u := b) (u' := b + s) s.toNat (-s).toNat (by omega) (by
      simpa only [add_sub_cancel_left, Int.cast_abs] using hdist)
  have hexp : -(subcriticalLogOddsNat k - subcriticalActiveLevelConstant k * delta) * s.toNat +
      (subcriticalLogOddsNat k + subcriticalActiveLevelConstant k * delta) * (-s).toNat =
        -subcriticalLogOddsNat k * s + subcriticalActiveLevelConstant k * delta * |(s : ℝ)| := by
    rw [← hsumR, ← hsplitR]
    ring
  rw [hexp] at h
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

end InducedStars
