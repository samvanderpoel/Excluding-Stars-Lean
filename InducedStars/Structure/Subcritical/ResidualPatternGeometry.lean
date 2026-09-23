import InducedStars.Structure.Subcritical.ResidualGraphCount
import InducedStars.Structure.Subcritical.ResidualMatchingSelection
import InducedStars.Structure.Subcritical.RowWitnesses

/-!
# Geometry extracted from an actual residual pattern

Residual-family membership supplies a generating graph and its realized
profile. The canonical maximum-matching selector and exact ceiling thinning
then produce the homogeneous matching used by the candidate construction.
The remaining adapters use only actual finite close-structure fields.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}
  {p : SubcriticalProfile D eta R₀ theta}
  {F : Finset (SimpleGraph V)} {TB R : SimpleGraph V}

/-- The unthinned homogeneous fiber comes from the canonical maximum
matching. Its selected submatching keeps the placement, is an actual
edge subfamily, and has exactly the paper's prescribed ceiling size. -/
theorem subcriticalResidualPattern_exists_exact_thinning
    (hR : R ∈ subcriticalResidualDefectPatternFinset F alpha p TB)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hR₀ : 1 ≤ R₀) (hell : 1 ≤ p.ell)
    (hscale : 16 ≤ subcriticalResidualMatchingLambda eta R₀ * Fintype.card V) :
    ∃ M₀ : SubcriticalHomogeneousResidualMatching D eta R₀ R p.roots,
      p.ell ≤ subcriticalResidualMatchingKappa eta R₀ * M₀.edges.card ∧
      ∃ M : SubcriticalHomogeneousResidualMatching D eta R₀ R p.roots,
        M.placement = M₀.placement ∧ M.edges ⊆ M₀.edges ∧
        M.edges.card = subcriticalResidualMatchingThinSize eta R₀ M₀.edges.card ∧
        subcriticalResidualMatchingLambda eta R₀ * p.ell /
          (8 * (subcriticalResidualMatchingKappa eta R₀ : ℝ)) ≤ (M.edges.card : ℝ) ∧
        (M.edges.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * Fintype.card V / 8 := by
  obtain ⟨G, hG, _, rfl⟩ := (mem_subcriticalResidualDefectPatternFinset F alpha p TB R).mp hR
  have hp := (mem_subcriticalProfileClassGraphFinset.mp hG).2
  obtain ⟨M₀, hM₀⟩ := hp.exists_homogeneousResidualMatching heta hetaOne hR₀ hell
  exact ⟨M₀, hM₀, M₀.exists_thin heta hetaOne hR₀ p.ell hM₀ hscale⟩

/-- Candidate-facing matching selection from actual residual membership.
Every selected endpoint avoids the profile roots by the matching structure. -/
theorem subcriticalResidualPattern_exists_matching
    (hR : R ∈ subcriticalResidualDefectPatternFinset F alpha p TB)
    (heta : 0 < eta) (hetaOne : eta ≤ 1) (hR₀ : 1 ≤ R₀) (hell : 1 ≤ p.ell)
    (hscale : 16 ≤ subcriticalResidualMatchingLambda eta R₀ * Fintype.card V) :
    ∃ M : SubcriticalHomogeneousResidualMatching D eta R₀ R p.roots,
      subcriticalResidualMatchingLambda eta R₀ * p.ell /
        (8 * (subcriticalResidualMatchingKappa eta R₀ : ℝ)) ≤ (M.edges.card : ℝ) ∧
      (M.edges.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * Fintype.card V / 8 := by
  obtain ⟨M₀, _, M, _, _, _, hlow, hhigh⟩ :=
    subcriticalResidualPattern_exists_exact_thinning hR heta hetaOne hR₀ hell hscale
  exact ⟨M, hlow, hhigh⟩

/-- Public standard-degree form of the proved residual-defect row bound. -/
theorem subcriticalResidualPattern_standardDegree_le
    (hR : R ∈ subcriticalResidualDefectPatternFinset F alpha p TB)
    (ha : 0 ≤ alpha)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hsmall : ∀ G ∈ F, ∀ v,
      (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
        subcriticalSparseSideConstant k * theta * Fintype.card V) (v : V) :
    (R.degree v : ℝ) ≤ subcriticalResidualDegreeCoefficient k alpha theta * Fintype.card V := by
  have heq : R.degree v = degreeInFinset R v Finset.univ := by
    simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, degreeInFinset]
  rw [heq]
  exact subcriticalResidualPattern_degree_le hR ha hret hsmall v

/-- Pattern membership witnesses profile realization, so the root bound
follows from the finite defect and visible-part inequalities. It does not
require any candidate-star or Janson assertion. -/
theorem subcriticalResidualPattern_roots_card_le_of_finite_geometry
    (hR : R ∈ subcriticalResidualDefectPatternFinset F alpha p TB)
    {epsilon : ℝ} (ha : 0 < alpha) (ht : 0 < theta) (hn : 0 < Fintype.card V)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hvisible : ∀ a ∈ D.visiblePartIndices theta,
      theta * Fintype.card V / 2 ≤ ((D.part a).card : ℝ))
    (hdefect : ∀ G ∈ F, (subcriticalDefectCost G D : ℝ) ≤
      epsilon * (Fintype.card V : ℝ) ^ 2) :
    (p.roots.card : ℝ) ≤ subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V := by
  obtain ⟨G, hG, _, _⟩ := (mem_subcriticalResidualDefectPatternFinset F alpha p TB R).mp hR
  obtain ⟨hGF, hp⟩ := mem_subcriticalProfileClassGraphFinset.mp hG
  apply hp.roots_card_le_of_geometry ha ht hn hret hvisible
  have he : ((subcriticalDefectGraph G D).edgeFinset.card : ℝ) ≤ subcriticalDefectCost G D := by
    exact_mod_cast subcriticalDefectGraph_card_le_defectCost G D
  exact he.trans (hdefect G hGF)

/-- Standard maximum-degree bound directly from star-free finite generating
graphs and their actual edit budgets. No alignment theorem is invoked. -/
theorem subcriticalResidualPattern_standardDegree_le_of_geometry
    {k n : ℕ} (hk : 3 ≤ k) {F : Finset (SimpleGraph (Fin n))}
    {D : SubcriticalDivision k (Fin n)} {eta theta alpha epsilon : ℝ} {R₀ : ℕ}
    {p : SubcriticalProfile D eta R₀ theta} {TB R : SimpleGraph (Fin n)}
    (hR : R ∈ subcriticalResidualDefectPatternFinset F alpha p TB)
    (ha : 0 ≤ alpha) (ht : 0 ≤ theta) (he : 0 ≤ epsilon)
    (heTheta : epsilon ≤ theta ^ 2) (hscale : 1 ≤ theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hfree : ∀ G ∈ F, ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hdefect : ∀ G ∈ F, (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ) ^ 2)
    (v : Fin n) :
    (R.degree v : ℝ) ≤ subcriticalResidualDegreeCoefficient k alpha theta * n := by
  have hsmall (G : SimpleGraph (Fin n)) (hG : G ∈ F) (x : Fin n) :
      (degreeInFinset G x (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
        subcriticalSparseSideConstant k * theta * Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using
      subcriticalResidual_smallSide_bound_of_geometry hk G D ht he heTheta hscale
        (hfree G hG) (hdefect G hG) x
  simpa only [Fintype.card_fin] using
    subcriticalResidualPattern_standardDegree_le hR ha hret hsmall v

/-- A supplied finite close-structure witness for each generating graph
gives both root and retained-part room bounds. This adapter uses only its
fields; obtaining that witness from graphon alignment is a separate step. -/
theorem subcriticalResidualPattern_root_part_bounds_of_closeStructure
    {k n R₀ : ℕ} {hk : 3 ≤ k} {F : Finset (SimpleGraph (Fin n))}
    {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
    {omega eta theta alpha delta epsilon : ℝ}
    {p : SubcriticalProfile D eta R₀ theta} {TB R : SimpleGraph (Fin n)}
    (hR : R ∈ subcriticalResidualDefectPatternFinset F alpha p TB)
    (hgeometry : ∀ G ∈ F, Nonempty
      (SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon))
    (hR₀ : 1 ≤ R₀) (heta : 0 ≤ eta) (homega : omega ≤ 1)
    (ha : 0 < alpha) (ht : 0 < theta)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ))) :
    (p.roots.card : ℝ) ≤ subcriticalProfileRootFraction alpha theta epsilon * n ∧
      ∀ a ∈ D.retainedPartIndices eta R₀,
        eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ) := by
  obtain ⟨G, hG, _, _⟩ := (mem_subcriticalResidualDefectPatternFinset F alpha p TB R).mp hR
  obtain ⟨hGF, hp⟩ := mem_subcriticalProfileClassGraphFinset.mp hG
  obtain ⟨S⟩ := hgeometry G hGF
  have hret := D.retainedPartIndices_subset_visiblePartIndices hR₀ ht.le hcutoff
  have hn : 0 < Fintype.card (Fin n) := D.componentCount_pos.trans_le D.componentCount_le_card
  have hroot := hp.roots_card_le_of_geometry (epsilon := epsilon) ha ht hn hret
    (fun a hmem ↦ by simpa only [Fintype.card_fin] using S.visible_part_card_ge_half homega a hmem)
  have he : ((subcriticalDefectGraph G D).edgeFinset.card : ℝ) ≤ subcriticalDefectCost G D := by
    exact_mod_cast subcriticalDefectGraph_card_le_defectCost G D
  refine ⟨?_, fun a hmem ↦ S.retainedPart_card_lower_bound hR₀ heta hmem⟩
  simp only [Fintype.card_fin] at hroot
  exact hroot (he.trans S.defect_cost_le)

end InducedStars
