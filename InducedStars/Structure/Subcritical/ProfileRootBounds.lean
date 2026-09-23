import InducedStars.Structure.Subcritical.ModelEdgeBounds
import InducedStars.Structure.Subcritical.ProfileGeometry

/-!
# Finite profile root bounds and target trimming

Paper: the incidence calculation in `lemma:profile-covering-K1k`, and the
elementary target restrictions used after the profile definitions. All
degrees selecting roots or tails are measured on the full target part.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical

namespace InducedStars

/-- The paper's root-fraction constant, with its stated factor two. -/
def subcriticalProfileRootFraction (alpha theta epsilon : ℝ) : ℝ :=
  2 * epsilon / (alpha * theta)

variable {k n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordinary defect count is bounded by the combined edit cost retained
by the close-structure bridge. Sparse--sparse defects can only increase that cost. -/
theorem subcriticalDefectGraph_card_le_defectCost
    (G : SimpleGraph V) (D : SubcriticalDivision k V) :
    (subcriticalDefectGraph G D).edgeFinset.card ≤ subcriticalDefectCost G D := by
  rw [subcriticalDefectCost_eq_card_edgeFinset]
  apply Finset.card_le_card
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
    exact ((subcriticalDefectGraph_adj G D x y).mp he).1

/-- The incidences at any selected roots count each unordered edge at
most twice. This uses the existing degree-sum formula with the full target. -/
theorem subcriticalRoot_degree_sum_le_twice_edges
    (T : SimpleGraph V) (B : Finset V) :
    (∑ v ∈ B, (degreeInFinset T v Finset.univ : ℝ)) ≤
      2 * (T.edgeFinset.card : ℝ) := by
  have hsum := sum_degreeInFinset_eq_two_mul_inducedEdgeCount T Finset.univ
  rw [inducedEdgeCount_eq_card_inter_sym2] at hsum
  simp only [Finset.sym2_univ, Finset.inter_univ] at hsum
  have hsumR : (∑ v : V, (degreeInFinset T v Finset.univ : ℝ)) =
      2 * (T.edgeFinset.card : ℝ) := by exact_mod_cast hsum
  rw [← hsumR]
  exact Finset.sum_le_univ_sum_of_nonneg fun _ ↦ Nat.cast_nonneg _

/-- Quantitative incidence counting for roots with the full-target defect
degree supplied by the profile thresholds. The actual calculation gives
`epsilon / (alpha * theta)`, stronger than the paper's stated constant. -/
theorem subcriticalRoot_card_le_of_incident_defects
    (T : SimpleGraph V) (B : Finset V) {alpha theta epsilon : ℝ}
    (halpha : 0 < alpha) (htheta : 0 < theta) (hn : 0 < Fintype.card V)
    (hdegree : ∀ v ∈ B,
      2 * alpha * theta * Fintype.card V ≤
        (degreeInFinset T v Finset.univ : ℝ))
    (hedges : (T.edgeFinset.card : ℝ) ≤ epsilon * (Fintype.card V : ℝ)^2) :
    (B.card : ℝ) ≤ epsilon / (alpha * theta) * Fintype.card V := by
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hsum : (B.card : ℝ) * (2 * alpha * theta * Fintype.card V) ≤
      ∑ v ∈ B, (degreeInFinset T v Finset.univ : ℝ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hdegree
  have hbound := hsum.trans (subcriticalRoot_degree_sum_le_twice_edges T B)
  have hmult : (B.card : ℝ) * (alpha * theta) ≤ epsilon * Fintype.card V := by
    have hprod : ((B.card : ℝ) * (alpha * theta)) * (Fintype.card V : ℝ) ≤
        (epsilon * Fintype.card V) * (Fintype.card V : ℝ) := by nlinarith [hedges]
    exact (mul_le_mul_iff_left₀ hnR).mp hprod
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (mul_pos halpha htheta)).mpr hmult

/-- The paper's stated factor two follows from the stronger incidence
calculation without changing the root threshold or rescaling `alpha`. -/
theorem subcriticalRoot_card_le_paper_of_incident_defects
    (T : SimpleGraph V) (B : Finset V) {alpha theta epsilon : ℝ}
    (halpha : 0 < alpha) (htheta : 0 < theta) (hn : 0 < Fintype.card V)
    (hdegree : ∀ v ∈ B,
      2 * alpha * theta * Fintype.card V ≤
        (degreeInFinset T v Finset.univ : ℝ))
    (hedges : (T.edgeFinset.card : ℝ) ≤ epsilon * (Fintype.card V : ℝ)^2) :
    (B.card : ℝ) ≤
      subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V := by
  have hstrong := subcriticalRoot_card_le_of_incident_defects
    T B halpha htheta hn hdegree hedges
  have hnonneg : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  unfold subcriticalProfileRootFraction
  calc
    (B.card : ℝ) ≤ 2 * (epsilon / (alpha * theta) * Fintype.card V) := by linarith
    _ = _ := by ring

/-- Every actual bad root has at least `2 * alpha * theta * |V|` ordinary
defect incidences, using its full high target or full own-part complement. -/
theorem subcriticalBadRoot_incident_defects_ge
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    {theta alpha : ℝ} (halpha : 0 < alpha)
    (hretained : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hvisible : ∀ a ∈ D.visiblePartIndices theta,
      theta * Fintype.card V / 2 ≤ ((D.part a).card : ℝ))
    (v : V) (hv : v ∈ subcriticalBadRoots G D eta R₀ theta alpha) :
    2 * alpha * theta * Fintype.card V ≤
      (degreeInFinset (subcriticalDefectGraph G D) v Finset.univ : ℝ) := by
  have hsize (a : D.PartIndex) (ha : a ∈ D.visiblePartIndices theta) :
      2 * alpha * theta * Fintype.card V ≤ 4 * alpha * (D.part a).card := by
    have h := mul_le_mul_of_nonneg_left (hvisible a ha)
      (show 0 ≤ 4 * alpha by positivity)
    nlinarith
  rcases (mem_subcriticalBadRoots G D eta R₀ theta alpha v).mp hv with hv | hv
  · obtain ⟨hvret, hrow | hown⟩ :=
      (mem_subcriticalBadRetainedRoots G D eta R₀ theta alpha v).mp hv
    · obtain ⟨a, ha, hhigh⟩ := hrow
      have hdegree : degreeInFinset G v (D.part a) ≤
          degreeInFinset (subcriticalDefectGraph G D) v Finset.univ := by
        unfold degreeInFinset
        apply Finset.card_le_card
        intro y hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          eligibleVisibleTarget_edge_is_defect G D eta R₀ theta v hvret ha
            (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2⟩
      have hdegreeR : (degreeInFinset G v (D.part a) : ℝ) ≤
          degreeInFinset (subcriticalDefectGraph G D) v Finset.univ := by
        exact_mod_cast hdegree
      exact (hsize a ((D.mem_eligibleVisibleTargets eta R₀ theta v hvret a).mp ha).1).trans
        (hhigh.trans hdegreeR)
    · have hdegree :
          complementDegreeInFinset G v (D.part (D.retainedVertexPart eta R₀ v hvret)) ≤
            degreeInFinset (subcriticalDefectGraph G D) v Finset.univ := by
        unfold complementDegreeInFinset degreeInFinset
        apply Finset.card_le_card
        intro y hy
        obtain ⟨hy, hne, hG⟩ := Finset.mem_filter.mp hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          retainedOwn_missing_edge_is_defect G D eta R₀ v hvret hy hne hG⟩
      have hdegreeR :
          (complementDegreeInFinset G v (D.part (D.retainedVertexPart eta R₀ v hvret)) : ℝ) ≤
            degreeInFinset (subcriticalDefectGraph G D) v Finset.univ := by
        exact_mod_cast hdegree
      exact (hsize _ (hretained (D.retainedVertexPart_mem_retained eta R₀ v hvret))).trans
        (hown.trans hdegreeR)
  · obtain ⟨hvout, a, ha, hhigh⟩ :=
      (mem_subcriticalBadOutsideRoots G D eta R₀ theta alpha v).mp hv
    have hdegree : degreeInFinset G v (D.part a) ≤
        degreeInFinset (subcriticalDefectGraph G D) v Finset.univ := by
      unfold degreeInFinset
      apply Finset.card_le_card
      intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        outside_retainedTarget_edge_is_defect G D eta R₀ hvout ha
          (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2⟩
    have hdegreeR : (degreeInFinset G v (D.part a) : ℝ) ≤
        degreeInFinset (subcriticalDefectGraph G D) v Finset.univ := by
      exact_mod_cast hdegree
    exact (hsize a (hretained ha)).trans (hhigh.trans hdegreeR)

/-- Finite root bound from explicit retained visibility, visible-part size,
and the ordinary defect edge count. Its constant is stronger than the paper's. -/
theorem subcriticalBadRoots_card_le_finite_strong
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    {theta alpha epsilon : ℝ} (halpha : 0 < alpha) (htheta : 0 < theta)
    (hn : 0 < Fintype.card V)
    (hretained : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hvisible : ∀ a ∈ D.visiblePartIndices theta,
      theta * Fintype.card V / 2 ≤ ((D.part a).card : ℝ))
    (hedges : ((subcriticalDefectGraph G D).edgeFinset.card : ℝ) ≤
      epsilon * (Fintype.card V : ℝ)^2) :
    ((subcriticalBadRoots G D eta R₀ theta alpha).card : ℝ) ≤
      epsilon / (alpha * theta) * Fintype.card V :=
  subcriticalRoot_card_le_of_incident_defects _ _ halpha htheta hn
    (subcriticalBadRoot_incident_defects_ge G D eta R₀ halpha hretained hvisible) hedges

/-- Paper: the root-cardinality conclusion of `lemma:profile-covering-K1k`,
at the paper's stated constant and with explicit finite geometric inputs. -/
theorem subcriticalBadRoots_card_le_finite
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    {theta alpha epsilon : ℝ} (halpha : 0 < alpha) (htheta : 0 < theta)
    (hn : 0 < Fintype.card V)
    (hretained : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hvisible : ∀ a ∈ D.visiblePartIndices theta,
      theta * Fintype.card V / 2 ≤ ((D.part a).card : ℝ))
    (hedges : ((subcriticalDefectGraph G D).edgeFinset.card : ℝ) ≤
      epsilon * (Fintype.card V : ℝ)^2) :
    ((subcriticalBadRoots G D eta R₀ theta alpha).card : ℝ) ≤
      subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V :=
  subcriticalRoot_card_le_paper_of_incident_defects _ _ halpha htheta hn
    (subcriticalBadRoot_incident_defects_ge G D eta R₀ halpha hretained hvisible) hedges

namespace SubcriticalCloseStructureResult

/-- The completed finite bridge supplies every geometric input to the profile
root bound. This wrapper does not repeat cell alignment or use star-freeness. -/
theorem badRoots_card_le
    {R₀ : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
    {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
    {omega eta theta alpha delta epsilon : ℝ}
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (halpha : 0 < alpha) (htheta : 0 < theta) (hn : 0 < n)
    (hR₀ : 1 ≤ R₀) (homega : omega ≤ 1)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ))) :
    ((subcriticalBadRoots G D eta R₀ theta alpha).card : ℝ) ≤
      subcriticalProfileRootFraction alpha theta epsilon * n := by
  have hvisible (a : D.PartIndex) (ha : a ∈ D.visiblePartIndices theta) :
      theta * Fintype.card (Fin n) / 2 ≤ ((D.part a).card : ℝ) := by
    simpa only [Fintype.card_fin] using R.visible_part_card_ge_half homega a ha
  have hedges : ((subcriticalDefectGraph G D).edgeFinset.card : ℝ) ≤
      epsilon * (Fintype.card (Fin n) : ℝ)^2 := by
    have hedge : ((subcriticalDefectGraph G D).edgeFinset.card : ℝ) ≤
        subcriticalDefectCost G D := by
      exact_mod_cast subcriticalDefectGraph_card_le_defectCost G D
    simpa only [Fintype.card_fin] using hedge.trans R.defect_cost_le
  simpa only [Fintype.card_fin] using
    subcriticalBadRoots_card_le_finite G D eta R₀ halpha htheta
      (by simpa using hn)
      (D.retainedPartIndices_subset_visiblePartIndices hR₀ htheta.le hcutoff)
      hvisible hedges

end SubcriticalCloseStructureResult

/-- Removing all roots loses at most their number, even when some roots
lie outside the target. The subtraction here is real subtraction. -/
theorem subcriticalTarget_card_sdiff_ge (Y B : Finset V) :
    (Y.card : ℝ) - B.card ≤ ((Y \ B).card : ℝ) := by
  have h : (Y.card : ℝ) ≤ ((Y \ B).card : ℝ) + B.card := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := Y) (t := B))
  linarith

/-- Uniform relative trimming from the visible-target lower bound. -/
theorem subcriticalTarget_card_sdiff_ge_mul
    (Y B : Finset V) {rho theta : ℝ} (hrho : 0 ≤ rho) (htheta : 0 < theta)
    (hB : (B.card : ℝ) ≤ rho * n)
    (hY : theta * n / 2 ≤ (Y.card : ℝ)) :
    (1 - 2 * rho / theta) * Y.card ≤ ((Y \ B).card : ℝ) := by
  have hbase := subcriticalTarget_card_sdiff_ge Y B
  have h1 := mul_le_mul_of_nonneg_left hB htheta.le
  have h2 := mul_le_mul_of_nonneg_left hY (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hrho)
  have hfrac : (B.card : ℝ) ≤ (2 * rho / theta) * Y.card := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ htheta).mpr
    nlinarith
  nlinarith

theorem subcriticalTarget_card_sdiff_ge_half
    (Y B : Finset V) {rho theta : ℝ} (hrho : 0 ≤ rho) (htheta : 0 < theta)
    (hB : (B.card : ℝ) ≤ rho * n)
    (hY : theta * n / 2 ≤ (Y.card : ℝ)) (hsmall : 4 * rho ≤ theta) :
    (Y.card : ℝ) / 2 ≤ ((Y \ B).card : ℝ) := by
  have hh := subcriticalTarget_card_sdiff_ge_mul Y B hrho htheta hB hY
  have hfrac : 2 * rho / theta ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ htheta).mpr
    linarith
  have hmul := mul_le_mul_of_nonneg_right hfrac
    (show (0 : ℝ) ≤ Y.card from Nat.cast_nonneg _)
  nlinarith

theorem subcriticalTarget_sdiff_nonempty
    (Y B : Finset V) {rho theta : ℝ} (hrho : 0 ≤ rho) (htheta : 0 < theta)
    (hn : 0 < n) (hB : (B.card : ℝ) ≤ rho * n)
    (hY : theta * n / 2 ≤ (Y.card : ℝ)) (hsmall : 4 * rho ≤ theta) :
    (Y \ B).Nonempty := by
  have hh := subcriticalTarget_card_sdiff_ge_half Y B hrho htheta hB hY hsmall
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (Y \ B).card := by
    have : 0 < theta * (n : ℝ) := mul_pos htheta hnR
    linarith
  exact Finset.card_pos.mp (by exact_mod_cast hpos)

/-- An ordinary row loses at most one neighbor per removed vertex. -/
theorem subcriticalDegree_le_sdiff_add_card (G : SimpleGraph V) (v : V)
    (Y B : Finset V) :
    degreeInFinset G v Y ≤ degreeInFinset G v (Y \ B) + B.card := by
  have h := Finset.card_le_card_sdiff_add_card (s := Y.filter (G.Adj v)) (t := B)
  have heq : (Y.filter (G.Adj v)) \ B = (Y \ B).filter (G.Adj v) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    tauto
  simpa only [heq, degreeInFinset] using h

/-- A full-target upper tail remains a relaxed upper tail after deleting
at most `alpha` times the original target size. -/
theorem subcriticalUpperTail_trimmed
    (G : SimpleGraph V) (v : V) (Y B : Finset V) {alpha : ℝ}
    (hB : (B.card : ℝ) ≤ alpha * Y.card)
    (hupper : (1 - alpha) * Y.card ≤ (degreeInFinset G v Y : ℝ)) :
    (1 - 2 * alpha) * Y.card ≤ (degreeInFinset G v (Y \ B) : ℝ) := by
  have h : (degreeInFinset G v Y : ℝ) ≤
      (degreeInFinset G v (Y \ B) : ℝ) + B.card := by
    exact_mod_cast subcriticalDegree_le_sdiff_add_card G v Y B
  nlinarith

/-- A lower tail only improves when the target is trimmed. -/
theorem subcriticalLowerTail_trimmed
    (G : SimpleGraph V) (v : V) (Y B : Finset V) {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hlower : (degreeInFinset G v Y : ℝ) ≤ alpha * Y.card) :
    (degreeInFinset G v (Y \ B) : ℝ) ≤ 2 * alpha * Y.card := by
  have h : (degreeInFinset G v (Y \ B) : ℝ) ≤ degreeInFinset G v Y := by
    exact_mod_cast degreeInFinset_mono G v (Finset.sdiff_subset : Y \ B ⊆ Y)
  have hnonneg : 0 ≤ alpha * (Y.card : ℝ) := mul_nonneg halpha (Nat.cast_nonneg _)
  linarith

end InducedStars
