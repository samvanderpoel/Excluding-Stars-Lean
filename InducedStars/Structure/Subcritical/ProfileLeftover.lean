import InducedStars.Structure.Subcritical.ProfileCovering
import InducedStars.Structure.Subcritical.ActiveModels

/-!
# Compatible leftover defect patterns

The literal finite compatibility relation preceding Paper Lemma
`lemma:profile-root-leftover-bound-K1k`. The leftover graph is necessary:
rooted and residual graphs intentionally omit some retained-incident defects.
-/

noncomputable section
open Finset
open scoped Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Remove exactly the rooted and residual edges from a retained pattern. -/
def subcriticalLeftoverDefectGraph (T₀ TB R : SimpleGraph V) : SimpleGraph V :=
  T₀ \ (TB ⊔ R)

/-- The actual leftover pattern extracted from one graph. -/
def subcriticalActualLeftoverDefectGraph (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ) : SimpleGraph V :=
  subcriticalLeftoverDefectGraph (subcriticalRetainedIncidentDefectGraph G D eta R₀)
    (subcriticalRootedDefectGraph G D eta R₀ theta alpha)
    (subcriticalResidualDefectGraph G D eta R₀ theta alpha)

@[simp] theorem subcriticalLeftoverDefectGraph_adj
    (T₀ TB R : SimpleGraph V) (x y : V) :
    (subcriticalLeftoverDefectGraph T₀ TB R).Adj x y ↔
      T₀.Adj x y ∧ ¬ TB.Adj x y ∧ ¬ R.Adj x y := by
  simp [subcriticalLeftoverDefectGraph, SimpleGraph.sdiff_adj]

/-- Compatibility retains an actual graph witness in the specified profile class. -/
def SubcriticalCompatibleDefectTriple (F : Finset (SimpleGraph V))
    {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}
    (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta)
    (TB R L : SimpleGraph V) : Prop :=
  ∃ G ∈ subcriticalProfileClassGraphFinset F alpha p,
    subcriticalRootedDefectGraph G D eta R₀ theta alpha = TB ∧
    subcriticalResidualDefectGraph G D eta R₀ theta alpha = R ∧
    subcriticalLeftoverDefectGraph
      (subcriticalRetainedIncidentDefectGraph G D eta R₀) TB R = L

/-- The paper's leftover family, with no additional restriction on the remainder graph. -/
def subcriticalLeftoverDefectPatternFinset (F : Finset (SimpleGraph V))
    {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}
    (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta) (TB R : SimpleGraph V) :
    Finset (SimpleGraph V) :=
  ((subcriticalProfileClassGraphFinset F alpha p).filter fun G ↦
    subcriticalRootedDefectGraph G D eta R₀ theta alpha = TB ∧
    subcriticalResidualDefectGraph G D eta R₀ theta alpha = R).image fun G ↦
      subcriticalLeftoverDefectGraph
        (subcriticalRetainedIncidentDefectGraph G D eta R₀) TB R

@[simp] theorem mem_subcriticalLeftoverDefectPatternFinset
    (F : Finset (SimpleGraph V)) {D : SubcriticalDivision k V}
    {eta theta : ℝ} {R₀ : ℕ} (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta)
    (TB R L : SimpleGraph V) :
    L ∈ subcriticalLeftoverDefectPatternFinset F alpha p TB R ↔
      SubcriticalCompatibleDefectTriple F alpha p TB R L := by
  simp only [subcriticalLeftoverDefectPatternFinset, SubcriticalCompatibleDefectTriple,
    Finset.mem_image, Finset.mem_filter]
  aesop

theorem subcriticalLeftoverDefectGraph_union
    (T₀ TB R : SimpleGraph V) (hB : TB ≤ T₀) (hR : R ≤ T₀) :
    TB ⊔ R ⊔ subcriticalLeftoverDefectGraph T₀ TB R = T₀ := by
  ext x y
  simp only [SimpleGraph.sup_adj, subcriticalLeftoverDefectGraph_adj]
  constructor
  · rintro ((h | h) | h)
    · exact hB h
    · exact hR h
    · exact h.1
  · intro h
    by_cases hb : TB.Adj x y
    · exact Or.inl (Or.inl hb)
    by_cases hr : R.Adj x y
    · exact Or.inl (Or.inr hr)
    exact Or.inr ⟨h, hb, hr⟩

theorem subcriticalLeftoverDefectGraph_edge_disjoint
    (T₀ TB R : SimpleGraph V) :
    Disjoint (finiteGraphEdges TB)
        (finiteGraphEdges (subcriticalLeftoverDefectGraph T₀ TB R)) ∧
      Disjoint (finiteGraphEdges R)
        (finiteGraphEdges (subcriticalLeftoverDefectGraph T₀ TB R)) := by
  constructor <;> apply Finset.disjoint_left.mpr <;> intro e he hl
  · induction e using Sym2.inductionOn with
    | _ x y =>
      rw [mk_mem_finiteGraphEdges] at he hl
      exact ((subcriticalLeftoverDefectGraph_adj T₀ TB R x y).mp hl).2.1 he
  · induction e using Sym2.inductionOn with
    | _ x y =>
      rw [mk_mem_finiteGraphEdges] at he hl
      exact ((subcriticalLeftoverDefectGraph_adj T₀ TB R x y).mp hl).2.2 he

/-- Every compatible triple gives the exact pairwise edge-disjoint decomposition. -/
theorem SubcriticalCompatibleDefectTriple.decomposition
    {F : Finset (SimpleGraph V)} {D : SubcriticalDivision k V}
    {eta theta alpha : ℝ} {R₀ : ℕ} {p : SubcriticalProfile D eta R₀ theta}
    {TB R L : SimpleGraph V} (h : SubcriticalCompatibleDefectTriple F alpha p TB R L) :
    (∃ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      subcriticalRetainedIncidentDefectGraph G D eta R₀ = TB ⊔ R ⊔ L) ∧
    Disjoint (finiteGraphEdges TB) (finiteGraphEdges R) ∧
    Disjoint (finiteGraphEdges TB) (finiteGraphEdges L) ∧
    Disjoint (finiteGraphEdges R) (finiteGraphEdges L) := by
  obtain ⟨G, hG, rfl, rfl, rfl⟩ := h
  refine ⟨⟨G, hG, ?_⟩,
    subcriticalRooted_residual_edge_disjoint G D eta R₀ theta alpha,
    subcriticalLeftoverDefectGraph_edge_disjoint _ _ _⟩
  exact (subcriticalLeftoverDefectGraph_union _ _ _
    (subcriticalRootedDefectGraph_le G D eta R₀ theta alpha)
    (subcriticalResidualDefectGraph_le G D eta R₀ theta alpha)).symm

/-- A leftover edge must meet the profile's roots. -/
theorem SubcriticalCompatibleDefectTriple.leftover_incident_roots
    {F : Finset (SimpleGraph V)} {D : SubcriticalDivision k V}
    {eta theta alpha : ℝ} {R₀ : ℕ} {p : SubcriticalProfile D eta R₀ theta}
    {TB R L : SimpleGraph V} (h : SubcriticalCompatibleDefectTriple F alpha p TB R L)
    {x y : V} (hxy : L.Adj x y) : x ∈ p.roots ∨ y ∈ p.roots := by
  obtain ⟨G, hG, rfl, rfl, rfl⟩ := h
  have hp := (mem_subcriticalProfileClassGraphFinset.mp hG).2
  rw [hp.roots_eq]
  obtain ⟨hT, _, hR⟩ := (subcriticalLeftoverDefectGraph_adj _ _ _ x y).mp hxy
  by_contra hnot
  exact hR ⟨hT, (not_or.mp hnot).1, (not_or.mp hnot).2⟩

/-- Fix the full nonretained graph before counting compatible leftovers. -/
def SubcriticalCompatibleDefectTripleWithRemainder (F : Finset (SimpleGraph V))
    {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}
    (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta)
    (H : SubcriticalRemainderGraph D eta R₀) (TB R L : SimpleGraph V) : Prop :=
  SubcriticalCompatibleDefectTriple
    (F.filter fun G ↦ subcriticalRemainderGraph G D eta R₀ = H) alpha p TB R L

/-- The fixed-remainder counting fiber. The unrestricted
family is kept separately; this definition does not silently redefine it. -/
def subcriticalLeftoverDefectPatternFinsetWithRemainder (F : Finset (SimpleGraph V))
    {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}
    (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta)
    (H : SubcriticalRemainderGraph D eta R₀) (TB R : SimpleGraph V) :
    Finset (SimpleGraph V) :=
  subcriticalLeftoverDefectPatternFinset
    (F.filter fun G ↦ subcriticalRemainderGraph G D eta R₀ = H) alpha p TB R

@[simp] theorem mem_subcriticalLeftoverDefectPatternFinsetWithRemainder
    (F : Finset (SimpleGraph V)) {D : SubcriticalDivision k V}
    {eta theta : ℝ} {R₀ : ℕ} (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta)
    (H : SubcriticalRemainderGraph D eta R₀) (TB R L : SimpleGraph V) :
    L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R ↔
      ∃ G ∈ subcriticalProfileClassGraphFinset F alpha p,
        subcriticalRemainderGraph G D eta R₀ = H ∧
        subcriticalRootedDefectGraph G D eta R₀ theta alpha = TB ∧
        subcriticalResidualDefectGraph G D eta R₀ theta alpha = R ∧
        subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha = L := by
  simp only [subcriticalLeftoverDefectPatternFinsetWithRemainder,
    mem_subcriticalLeftoverDefectPatternFinset, SubcriticalCompatibleDefectTriple,
    mem_subcriticalProfileClassGraphFinset, Finset.mem_filter,
    subcriticalActualLeftoverDefectGraph]
  aesop

theorem subcriticalLeftoverDefectPatternFinsetWithRemainder_subset
    (F : Finset (SimpleGraph V)) {D : SubcriticalDivision k V}
    {eta theta : ℝ} {R₀ : ℕ} (alpha : ℝ) (p : SubcriticalProfile D eta R₀ theta)
    (H : SubcriticalRemainderGraph D eta R₀) (TB R : SimpleGraph V) :
    subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R ⊆
      subcriticalLeftoverDefectPatternFinset F alpha p TB R := by
  intro L hL
  obtain ⟨G, hG, _, hB, hR, hL⟩ :=
    (mem_subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R L).mp hL
  apply (mem_subcriticalLeftoverDefectPatternFinset F alpha p TB R L).mpr
  refine ⟨G, hG, hB, hR, ?_⟩
  simpa [subcriticalActualLeftoverDefectGraph, hB, hR] using hL

/-- An explicit scale constant depending only on the permitted parameters. -/
def subcriticalProfileErrorConstant (k R₀ : ℕ) : ℝ :=
  1000 * (k + 1 : ℕ)^4 * (R₀ + 1 : ℕ)

/-- The profile error scale, in binary entropy/log units. Conversions to
natural exponential bounds must be supplied explicitly by the counting proof. -/
def subcriticalProfileErrorBudget {D : SubcriticalDivision k V}
    {eta theta : ℝ} {R₀ : ℕ} (alpha delta epsilon : ℝ)
    (p : SubcriticalProfile D eta R₀ theta) : ℝ :=
  subcriticalProfileErrorConstant k R₀ * p.roots.card *
    (binaryEntropy (5 * alpha) * Fintype.card V + theta * Fintype.card V +
      delta * Fintype.card V +
      subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V +
      log2 (Fintype.card V + 1))

end InducedStars
