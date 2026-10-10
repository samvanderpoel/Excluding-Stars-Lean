import DenseGraph.Combinatorics.BoundedDegreeCounting
import InducedStars.Structure.Subcritical.ResidualDegree
import InducedStars.Structure.Subcritical.ProfileExponents

/-!
# Weighted residual-pattern counting

The residual family is counted by direct bounded-degree
Hamming encoding. The remainder may vary throughout the pattern family.
Every degree and matching hypothesis is derived from a generating graph,
not assumed as a bound on the number of patterns.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}
  {p : SubcriticalProfile D eta R₀ theta}

theorem subcriticalResidualPattern_matching
    {F : Finset (SimpleGraph V)} {TB R : SimpleGraph V}
    (hR : R ∈ subcriticalResidualDefectPatternFinset F alpha p TB) :
    DenseGraph.matchingNumber R = p.ell := by
  obtain ⟨G, hG, _, rfl⟩ := (mem_subcriticalResidualDefectPatternFinset F alpha p TB R).mp hR
  exact (mem_subcriticalProfileClassGraphFinset.mp hG).2.matching

theorem subcriticalResidualPattern_roots_avoiding
    {F : Finset (SimpleGraph V)} {TB R : SimpleGraph V}
    (hR : R ∈ subcriticalResidualDefectPatternFinset F alpha p TB)
    {x y : V} (hxy : R.Adj x y) : x ∉ p.roots ∧ y ∉ p.roots := by
  obtain ⟨G, hG, _, rfl⟩ := (mem_subcriticalResidualDefectPatternFinset F alpha p TB R).mp hR
  have hp := (mem_subcriticalProfileClassGraphFinset.mp hG).2
  simpa only [hp.roots_eq] using hxy.2

/-- The exact canonical maximum-matching endpoint finset required for
residual placement and enumeration. -/
abbrev subcriticalResidualMatchingCover (R : SimpleGraph V) : Finset V :=
  DenseGraph.canonicalMatchingCover R

theorem subcriticalResidualMatchingCover_card
    {F : Finset (SimpleGraph V)} {TB R : SimpleGraph V}
    (hR : R ∈ subcriticalResidualDefectPatternFinset F alpha p TB) :
    (subcriticalResidualMatchingCover R).card = 2 * p.ell := by
  rw [subcriticalResidualMatchingCover, DenseGraph.card_canonicalMatchingCover,
    subcriticalResidualPattern_matching hR]

theorem subcriticalResidualMatchingCover_vertexCover (R : SimpleGraph V) :
    R.IsVertexCover (subcriticalResidualMatchingCover R : Set V) :=
  DenseGraph.canonicalMatchingCover_vertexCover R

theorem subcriticalResidualMatchingCover_disjoint_roots
    {F : Finset (SimpleGraph V)} {TB R : SimpleGraph V}
    (hR : R ∈ subcriticalResidualDefectPatternFinset F alpha p TB) :
    Disjoint (subcriticalResidualMatchingCover R) p.roots := by
  apply Finset.disjoint_left.mpr
  intro x hx hxB
  have hxM : x ∈ (DenseGraph.canonicalMaximumMatching R).verts := by
    simpa only [subcriticalResidualMatchingCover, DenseGraph.canonicalMatchingCover,
      Set.Finite.mem_toFinset] using hx
  obtain ⟨y, hxy, _⟩ := DenseGraph.canonicalMaximumMatching_isMatching R hxM
  exact (subcriticalResidualPattern_roots_avoiding hR
    ((DenseGraph.canonicalMaximumMatching R).adj_sub hxy)).1 hxB

theorem subcriticalResidualPattern_degree_le
    {F : Finset (SimpleGraph V)} {TB R : SimpleGraph V}
    (hR : R ∈ subcriticalResidualDefectPatternFinset F alpha p TB)
    (ha : 0 ≤ alpha)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hsmall : ∀ G ∈ F, ∀ v,
      (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
        subcriticalSparseSideConstant k * theta * Fintype.card V) (v : V) :
    (degreeInFinset R v Finset.univ : ℝ) ≤
      subcriticalResidualDegreeCoefficient k alpha theta * Fintype.card V := by
  obtain ⟨G, hG, _, rfl⟩ := (mem_subcriticalResidualDefectPatternFinset F alpha p TB R).mp hR
  obtain ⟨hGF, hp⟩ := mem_subcriticalProfileClassGraphFinset.mp hG
  exact subcriticalResidual_degree_le hp ha hret (hsmall G hGF) v

private theorem degree_eq_degreeInFinset_univ (R : SimpleGraph V) (v : V) :
    R.degree v = degreeInFinset R v Finset.univ := by
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, degreeInFinset]

private theorem finiteGraphEdges_eq_edgeFinset (R : SimpleGraph V) :
    finiteGraphEdges R = R.edgeFinset := by
  ext e
  simp only [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]

theorem subcriticalResidualPattern_edgeCount_le
    {F : Finset (SimpleGraph V)} {TB R : SimpleGraph V}
    (hR : R ∈ subcriticalResidualDefectPatternFinset F alpha p TB)
    (ha : 0 ≤ alpha)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hsmall : ∀ G ∈ F, ∀ v,
      (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
        subcriticalSparseSideConstant k * theta * Fintype.card V) :
    ((finiteGraphEdges R).card : ℝ) ≤ (2 * p.ell : ℕ) *
      (subcriticalResidualDegreeCoefficient k alpha theta * Fintype.card V) := by
  have hd (v : V) : (R.degree v : ℝ) ≤
      subcriticalResidualDegreeCoefficient k alpha theta * Fintype.card V := by
    rw [degree_eq_degreeInFinset_univ]
    exact subcriticalResidualPattern_degree_le hR ha hret hsmall v
  simpa only [finiteGraphEdges_eq_edgeFinset, subcriticalResidualPattern_matching hR] using
    DenseGraph.edgeFinset_card_le_matching_degree R hd

/-- Paper `eqn:residual-graph-count-K1k`:
the exact finite weighted Hamming bound is uniform over all remainder
graphs. Its logarithms and binary entropy are natural. -/
theorem subcriticalResidualWeightedGraphCount_le
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta) (TB : SimpleGraph V)
    (ha : 0 ≤ alpha) (ht : 0 ≤ theta)
    (hhalf : subcriticalResidualDegreeCoefficient k alpha theta ≤ 1/2)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hsmall : ∀ G ∈ F, ∀ v,
      (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
        subcriticalSparseSideConstant k * theta * Fintype.card V) :
    (∑ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
      Real.exp (subcriticalResidualWeightConstant k * (finiteGraphEdges R).card)) ≤
        Real.exp ((2 * p.ell : ℕ) * ((Fintype.card V : ℝ) *
          (Real.binEntropy (subcriticalResidualDegreeCoefficient k alpha theta) +
            subcriticalResidualWeightConstant k * subcriticalResidualDegreeCoefficient k alpha theta) +
          Real.log (Fintype.card V + 1))) := by
  simp_rw [finiteGraphEdges_eq_edgeFinset]
  apply DenseGraph.sum_exp_edges_le_of_matching_degree _ p.ell
    (subcriticalResidualDegreeCoefficient_nonneg k ha ht) hhalf
    (subcriticalResidualWeightConstant_pos k).le
  · intro R hR
    exact subcriticalResidualPattern_matching hR
  · intro R hR v
    rw [degree_eq_degreeInFinset_univ]
    exact subcriticalResidualPattern_degree_le hR ha hret hsmall v

/-- Actual finite-geometry specialization of the weighted count.
Star-freeness and the finite defect budget apply to every generating graph;
the remainder is not fixed and no abstract counting hypothesis is assumed. -/
theorem subcriticalResidualWeightedGraphCount_le_of_geometry
    {k n : ℕ} (hk : 3 ≤ k) (F : Finset (SimpleGraph (Fin n)))
    {D : SubcriticalDivision k (Fin n)} {eta theta alpha epsilon : ℝ} {R₀ : ℕ}
    (p : SubcriticalProfile D eta R₀ theta) (TB : SimpleGraph (Fin n))
    (ha : 0 ≤ alpha) (ht : 0 ≤ theta) (he : 0 ≤ epsilon)
    (heTheta : epsilon ≤ theta ^ 2) (hscale : 1 ≤ theta * n)
    (hhalf : subcriticalResidualDegreeCoefficient k alpha theta ≤ 1/2)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hfree : ∀ G ∈ F, ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hdefect : ∀ G ∈ F, (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ)^2) :
    (∑ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
      Real.exp (subcriticalResidualWeightConstant k * (finiteGraphEdges R).card)) ≤
        Real.exp ((2 * p.ell : ℕ) * ((n : ℝ) *
          (Real.binEntropy (subcriticalResidualDegreeCoefficient k alpha theta) +
            subcriticalResidualWeightConstant k * subcriticalResidualDegreeCoefficient k alpha theta) +
          Real.log (n + 1))) := by
  have hsmall (G : SimpleGraph (Fin n)) (hG : G ∈ F) (v : Fin n) :
      (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
        subcriticalSparseSideConstant k * theta * Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using
      subcriticalResidual_smallSide_bound_of_geometry hk G D ht he heTheta hscale
        (hfree G hG) (hdefect G hG) v
  simpa only [Fintype.card_fin] using
    subcriticalResidualWeightedGraphCount_le F p TB ha ht hhalf hret hsmall

end InducedStars
