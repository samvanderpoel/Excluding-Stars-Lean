import InducedStars.Structure.Subcritical.EditEstimate
import InducedStars.Structure.Subcritical.Defect
import InducedStars.Structure.Subcritical.RetainedMass
import DenseGraph.Graphon.Inputs
import InducedStars.Graphon.Candidates
import InducedStars.PriorInstances

/-!
# The small-edit part of the subcritical cut-to-division bridge

Only item (i) of paper Lemma `lemma:WtoWtildeMetricsK1k` is in scope here.
The finite alignment radius is chosen before the candidate representation;
the finite-reference threshold may depend on that representation.
-/

noncomputable section

open Filter Topology
open scoped BigOperators Classical

namespace InducedStars

open DenseGraph FiniteWeightedGraph

/-- The explicit finite cut-to-edit inequality. It is valid for every
division and every reference agreeing on the retained support, before any
candidate-specific bound on the residual mass is used. The denominator two
is precisely the conversion between ordered pairs and unordered edges. -/
theorem subcriticalDefectCost_le_of_reference
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D : SubcriticalDivision k V) (G : SimpleGraph V)
    (R : FiniteWeightedGraph V) {beta : ℝ}
    (hcut : finiteLabeledCutDist (ofSimpleGraph G) R ≤ beta)
    (hR : ∀ x ∈ D.support, ∀ y ∈ D.support,
      R.weight x y = (subcriticalDivisionWeightedGraph hk D).weight x y) :
    (subcriticalDefectCost G D : ℝ) ≤
      ((Fintype.card D.PartIndex : ℝ) ^ 2 + 2) / 2 * beta *
        (Fintype.card V : ℝ) ^ 2 +
          (∑ x ∈ D.sparse, ∑ y : V, R.weight x y) := by
  let Q := subcriticalCombinedDefectGraph G D
  have hedge : finiteGraphEdges Q = Q.edgeFinset := by
    ext e
    simp only [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  have hcount : subcriticalDefectCost G D = Q.edgeFinset.card := by
    unfold subcriticalDefectCost
    exact congrArg Finset.card hedge
  have h := subcritical_two_mul_defect_edges_le_cut_and_residual hk D Q G R hcut
    (fun _ _ ↦ subcriticalCombinedDefectGraph_adj_iff G D) hR
  rw [hcount]
  linarith

/-- Align a full finite reference before making any truncation choices.
The radius is uniform in both the limiting graphon and its reference
sequence; only the order threshold depends on the reference convergence. -/
theorem exists_subcritical_fullReference_alignment_radius
    (alignment : FiniteWeightedAlignmentInput) (beta : ℝ) (hbeta : 0 < beta) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ W : Graphon,
      ∀ R : (n : ℕ) → FiniteWeightedGraph (Fin n),
        Tendsto (fun n ↦ cutDist (R n).toGraphon W) atTop (𝓝 0) →
          ∃ n0 : ℕ, ∀ n ≥ n0, ∀ G : SimpleGraph (Fin n),
            cutDist (graphGraphon G) W < tau →
              ∃ pi : Equiv.Perm (Fin n),
                finiteLabeledCutDist (ofSimpleGraph G) ((R n).permute pi) < beta := by
  obtain ⟨tauAlign, htauAlign, halign⟩ := alignment.align beta hbeta
  refine ⟨tauAlign / 2, half_pos htauAlign, ?_⟩
  intro W R hR
  have hevent : ∀ᶠ n in atTop, cutDist (R n).toGraphon W < tauAlign / 2 :=
    (tendsto_order.1 hR).2 _ (half_pos htauAlign)
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hevent
  refine ⟨n0, ?_⟩
  intro n hn G hG
  apply halign (ofSimpleGraph G) (R n)
  rw [toGraphon_ofSimpleGraph]
  have ht := cutDist_triangle (graphGraphon G) W (R n).toGraphon
  rw [cutDist_comm W] at ht
  have hr := hn0 n hn
  linarith

/-- Finite aligned-reference construction, including the empty-retained
case. The same permutation transports the division and its residual rows
back to the original graph labels before canonical minimality is applied. -/
theorem canonicalSubcriticalDefectCost_le_of_aligned_reference
    {k n : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    (I : Finset ℕ) (M : ℕ)
    (hsize : (∑ i ∈ I, (L.core i).order) ≤ M)
    (hcells : ∀ i ∈ I, ∀ v, (subcriticalReferenceCellVertices L n i v).Nonempty)
    (G : SimpleGraph (Fin n)) (R₀ : ℕ) (hcard : k - 1 ≤ Fintype.card (Fin n))
    (pi : Equiv.Perm (Fin n)) {beta : ℝ}
    (hcut : finiteLabeledCutDist (ofSimpleGraph G)
      ((subcriticalReferenceWeightedGraph hk L n).permute pi) ≤ beta) :
    (canonicalSubcriticalDefectCost G R₀ hk hcard : ℝ) ≤
      ((M : ℝ) ^ 2 + 2) / 2 * beta * (n : ℝ) ^ 2 +
        subcriticalReferenceResidualOrderedWeight L hk n I := by
  have hbeta : 0 ≤ beta := (finiteLabeledCutDist_nonneg _ _).trans hcut
  let A := subcriticalReferenceWeightedGraph hk L n
  by_cases hI : I.Nonempty
  · let D := subcriticalRetainedDivision L I hI hcells
    let E := D.relabel pi.symm
    have hR : ∀ x ∈ E.support, ∀ y ∈ E.support,
        (A.permute pi).weight x y = (subcriticalDivisionWeightedGraph hk E).weight x y := by
      intro x hx y _
      have hxE : x ∈ (D.relabel pi.symm).support := by
        simpa only [E] using hx
      have hx' : pi x ∈ D.support := by
        simpa only [Equiv.symm_symm] using
          (SubcriticalDivision.mem_relabel_support D pi.symm x).mp hxE
      exact (subcriticalRetainedDivision_relabel_weight_eq_reference L I hI hcells hk pi
        (Or.inl hx')).symm
    have he := subcriticalDefectCost_le_of_reference hk E G (A.permute pi) hcut hR
    have hm : Fintype.card E.PartIndex ≤ M := by
      change Fintype.card D.PartIndex ≤ M
      rw [subcriticalRetainedDivision_card_partIndex L I hI hcells]
      exact hsize
    have hs : (∑ x ∈ E.sparse, ∑ y, (A.permute pi).weight x y) =
        subcriticalReferenceResidualOrderedWeight L hk n I := by
      rw [subcritical_sparse_weight_sum_relabel D A pi]
      simp only [D, subcriticalRetainedDivision_sparse,
        subcriticalReferenceResidualOrderedWeight, A]
    rw [hs, Fintype.card_fin] at he
    have hmR : (Fintype.card E.PartIndex : ℝ) ≤ M := by exact_mod_cast hm
    have hsquare : (Fintype.card E.PartIndex : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := by
      exact (sq_le_sq₀ (by positivity) (by positivity)).2 hmR
    have hcoef : ((Fintype.card E.PartIndex : ℝ) ^ 2 + 2) / 2 * beta * (n : ℝ) ^ 2 ≤
        ((M : ℝ) ^ 2 + 2) / 2 * beta * (n : ℝ) ^ 2 := by gcongr
    have hmin : (canonicalSubcriticalDefectCost G R₀ hk hcard : ℝ) ≤
        subcriticalDefectCost G E := by
      exact_mod_cast canonicalSubcriticalDivision_minimal G R₀ hk hcard E
    linarith
  · have hI0 : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    have htotal : (∑ x : Fin n, ∑ y : Fin n, (A.permute pi).weight x y) =
        subcriticalReferenceResidualOrderedWeight L hk n I := by
      subst I
      simp only [subcriticalReferenceResidualOrderedWeight, subcriticalRetainedCellSupport,
        Finset.biUnion_empty, Finset.sdiff_empty]
      calc
        (∑ x : Fin n, ∑ y : Fin n, (A.permute pi).weight x y) =
            ∑ x : Fin n, ∑ y : Fin n, A.weight (pi x) y := by
          apply Finset.sum_congr rfl
          intro x _
          exact Equiv.sum_comp pi (fun y ↦ A.weight (pi x) y)
        _ = _ := Equiv.sum_comp pi (fun x ↦ ∑ y, A.weight x y)
    have he := subcritical_card_interedges_le_weight_add_cut G (A.permute pi)
      Finset.univ Finset.univ
    rw [htotal, Fintype.card_fin] at he
    have hedge : finiteGraphEdges G = G.edgeFinset := by
      ext e
      simp only [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
    have htwice : 2 * (finiteGraphEdges G).card =
        (G.interedges Finset.univ Finset.univ).card := by
      rw [hedge]
      simpa [SimpleGraph.interedges, Rel.interedges] using G.two_mul_card_edgeFinset
    have htwiceR : 2 * ((finiteGraphEdges G).card : ℝ) =
        ((G.interedges Finset.univ Finset.univ).card : ℝ) := by exact_mod_cast htwice
    have hmin : (canonicalSubcriticalDefectCost G R₀ hk hcard : ℝ) ≤
        (finiteGraphEdges G).card := by
      exact_mod_cast canonicalSubcriticalDefectCost_le_card_edges G R₀ hk hcard
    have hc := mul_le_mul_of_nonneg_right hcut (sq_nonneg (n : ℝ))
    have hcoef : beta * (n : ℝ) ^ 2 ≤
        ((M : ℝ) ^ 2 + 2) / 2 * beta * (n : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (M : ℝ)) (mul_nonneg hbeta (sq_nonneg (n : ℝ)))]
    nlinarith [show (0 : ℝ) ≤ ((finiteGraphEdges G).card : ℝ) by positivity]

/-- Capability-parametric small-edit bridge. The positive cut radius
depends only on `k,epsilon`; the vertex threshold may depend on `L`. The
conclusion is uniform in the ordering cutoff, and needs neither induced-star
freeness nor a specified edge count. Paper: Lemma
`lemma:WtoWtildeMetricsK1k`, item `item:bgleqen2` only. The matrix normalization gives the
ordered/unordered normalization; no particular numerical alignment modulus
from the paper is asserted. -/
theorem subcriticalCanonicalDefectCost_le_of_cutCloseCore
    (alignment : FiniteWeightedAlignmentInput)
    (k : ℕ) (hk : 3 ≤ k) (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
        ∀ (G : SimpleGraph (Fin n)) (R₀ : ℕ),
          cutDist (graphGraphon G) (WLambda hk L) < tau →
            (canonicalSubcriticalDefectCost G R₀ hk
              (by simpa using hn0.trans hn) : ℝ) ≤ epsilon * (n : ℝ) ^ 2 := by
  let c : ℝ := 1 + ((k - 2 : ℕ) : ℝ) * pK k
  have hc : 0 < c := by
    have hp := (pK_mem_Icc k).1
    dsimp [c]
    positivity
  let eta : ℝ := epsilon / (32 * c)
  have heta : 0 < eta := div_pos hepsilon.1 (by positivity)
  let B : ℕ := Nat.ceil (1 / eta)
  let R : ℕ := B + 1
  have hR : 0 < R := by dsimp [R]; omega
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hinv : 1 / (R : ℝ) ≤ eta := by
    have hceil : (1 / eta : ℝ) ≤ R :=
      (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_succ B)
    have hh := (div_le_iff₀ heta).mp hceil
    apply (div_le_iff₀ hRr).mpr
    simpa [mul_comm] using hh
  have hetaEq : 32 * c * eta = epsilon := by
    dsimp [eta]
    field_simp
  have hresCoef : 2 * c * (eta + 1 / (R : ℝ)) ≤ epsilon / 8 := by
    nlinarith
  let M : ℕ := B * R
  let beta : ℝ := epsilon / (4 * ((M : ℝ) ^ 2 + 2))
  have hbeta : 0 < beta := div_pos hepsilon.1 (by positivity)
  have hbetaEq : ((M : ℝ) ^ 2 + 2) / 2 * beta = epsilon / 8 := by
    dsimp [beta]
    field_simp
    <;> ring
  obtain ⟨tau, htau, halign⟩ := exists_subcritical_fullReference_alignment_radius
    alignment beta hbeta
  refine ⟨tau, htau, ?_⟩
  intro L
  let I := subcriticalRetainedBlockIndices L eta R
  have hlarge : ∀ i ∈ I, eta ≤ L.alpha i :=
    fun i hi ↦ (mem_subcriticalRetainedBlockIndices.mp hi).2.1
  have horder : ∀ i ∈ I, (L.core i).order ≤ R :=
    fun i hi ↦ (mem_subcriticalRetainedBlockIndices.mp hi).2.2
  have hsize : (∑ i ∈ I, (L.core i).order) ≤ M := by
    calc
      _ ≤ ∑ _i ∈ I, R := Finset.sum_le_sum horder
      _ = I.card * R := by simp
      _ ≤ M := Nat.mul_le_mul_right R
        (subcriticalRetained_card_le_ceil_inv L I heta hlarge)
  have hcells : ∀ᶠ n in atTop,
      ∀ i ∈ I, ∀ v, (subcriticalReferenceCellVertices L n i v).Nonempty := by
    apply (Filter.eventually_all_finset I).2
    intro i hi
    apply Filter.eventually_all.2
    intro v
    exact eventually_subcriticalReferenceCellVertices_nonempty L (heta.trans_le (hlarge i hi)) v
  have hres : ∀ᶠ n in atTop,
      subcriticalReferenceResidualOrderedWeight L hk n I ≤ epsilon / 8 * (n : ℝ) ^ 2 := by
    filter_upwards [eventually_subcriticalReferenceRetainedResidual_le L hk heta hR] with n hn
    exact hn.trans (mul_le_mul_of_nonneg_right hresCoef (sq_nonneg (n : ℝ)))
  obtain ⟨nA, hnA⟩ := halign (WLambda hk L) (subcriticalReferenceWeightedGraph hk L)
    (subcriticalReferenceGraphon_tendsto_WLambda hk L)
  obtain ⟨nB, hnB⟩ := eventually_atTop.1 (hcells.and hres)
  let n0 := max (k - 1) (max nA nB)
  refine ⟨n0, le_max_left _ _, ?_⟩
  intro n hn G R₀ hG
  have hnA' : nA ≤ n := (le_max_of_le_right (le_max_left _ _)).trans hn
  have hnB' : nB ≤ n := (le_max_of_le_right (le_max_right _ _)).trans hn
  obtain ⟨pi, hpi⟩ := hnA n hnA' G hG
  obtain ⟨hcelln, hresn⟩ := hnB n hnB'
  have he := canonicalSubcriticalDefectCost_le_of_aligned_reference hk L I M hsize hcelln
    G R₀ (by simpa using (le_max_left (k - 1) (max nA nB)).trans hn) pi hpi.le
  rw [hbetaEq] at he
  have hnSq := sq_nonneg (n : ℝ)
  nlinarith [mul_nonneg hepsilon.1.le hnSq]

/-- Project-facing form of the small-edit bridge, using only the existing
published finite-weighted-alignment input. This proves item (i), not the
remaining four conclusions of `lemma:WtoWtildeMetricsK1k`. -/
theorem subcriticalCanonicalDefectCost_le_of_cutClose
    (k : ℕ) (hk : 3 ≤ k) (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
        ∀ (G : SimpleGraph (Fin n)) (R₀ : ℕ),
          cutDist (graphGraphon G) (WLambda hk L) < tau →
            (canonicalSubcriticalDefectCost G R₀ hk
              (by simpa using hn0.trans hn) : ℝ) ≤ epsilon * (n : ℝ) ^ 2 :=
  subcriticalCanonicalDefectCost_le_of_cutCloseCore
    PriorInstances.finiteWeightedAlignmentInput k hk epsilon hepsilon

/-- Paper-facing specialization of the small-edit conclusion to an arbitrary
member of the subcritical optimizer family.  The positive cut radius is
chosen before the optimizer `W`; the finite threshold may depend on its
explicit block-sequence representation.  This is only item (i) of paper
Lemma `lemma:WtoWtildeMetricsK1k`. -/
theorem subcriticalCanonicalDefectCost_le_of_mem_candidateOptimizerFamily
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) (gammaK k))
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ W : Graphon,
      W ∈ candidateOptimizerFamily k gamma →
        ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
          ∀ (G : SimpleGraph (Fin n)) (R₀ : ℕ),
            cutDist (graphGraphon G) W < tau →
              (canonicalSubcriticalDefectCost G R₀ hk
                (by simpa using hn0.trans hn) : ℝ) ≤
                  epsilon * (n : ℝ) ^ 2 := by
  have hgammaOne : gamma ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hgamma.1, hgamma.2.trans (gammaK_lt_one hk)⟩
  obtain ⟨tau, htau, hcore⟩ :=
    subcriticalCanonicalDefectCost_le_of_cutClose k hk epsilon hepsilon
  refine ⟨tau, htau, ?_⟩
  intro W hW
  rw [candidateOptimizerFamily_of_lt hk hgammaOne hgamma.2] at hW
  obtain ⟨L, _hL, hWL⟩ := mem_subcriticalCandidateFamily.mp hW
  subst W
  exact hcore L

/-- The preceding numerical cost bound is attained by an actual edited
simple graph: the canonical repair is a regular blow-up and differs from the
input in at most `epsilon * n²` unordered edges.  This exposes the literal
finite witness required by item (i), rather than only its minimum cost. -/
theorem subcriticalRegularBlowup_exists_of_mem_candidateOptimizerFamily
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) (gammaK k))
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ W : Graphon,
      W ∈ candidateOptimizerFamily k gamma →
        ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
          ∀ (G : SimpleGraph (Fin n)) (R₀ : ℕ),
            cutDist (graphGraphon G) W < tau →
              ∃ H : SimpleGraph (Fin n),
                IsSubcriticalRegularBlowup k H ∧
                  (DenseGraph.simpleGraphEditDistance G H : ℝ) ≤
                    epsilon * (n : ℝ) ^ 2 := by
  obtain ⟨tau, htau, hcost⟩ :=
    subcriticalCanonicalDefectCost_le_of_mem_candidateOptimizerFamily
      k hk hgamma epsilon hepsilon
  refine ⟨tau, htau, ?_⟩
  intro W hW
  obtain ⟨n0, hn0, hmain⟩ := hcost W hW
  refine ⟨n0, hn0, ?_⟩
  intro n hn G R₀ hclose
  have hcard : k - 1 ≤ Fintype.card (Fin n) := by
    simpa using hn0.trans hn
  let D := canonicalSubcriticalDivision G R₀ hk hcard
  let H := subcriticalDivisionModelGraph G D
  refine ⟨H, subcriticalDivisionModelGraph_isRegularBlowup G D, ?_⟩
  have hattain := canonicalSubcriticalRepair_attains G R₀ hk hcard
  change (DenseGraph.simpleGraphEditDistance G
    (subcriticalDivisionModelGraph G D) : ℝ) ≤ epsilon * (n : ℝ) ^ 2
  rw [hattain]
  exact hmain hn G R₀ hclose

end InducedStars
