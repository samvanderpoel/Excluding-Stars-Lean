import InducedStars.Structure.Subcritical.AlignedComponents
import InducedStars.Structure.Subcritical.ClosenessParameters
import InducedStars.Structure.Subcritical.SmallEdit

/-!
# Uniform construction of the canonical subcritical alignment

The cut radius is chosen before the candidate sequence. The canonical
division stays in the labels of the original graph, and only the full
reference is permuted. The repaired-graph comparison retains the exact
factor two for unordered edits; cell comparisons use the signed
rectangle comparison.
-/

noncomputable section

open Filter
open scoped Topology

namespace InducedStars

open DenseGraph FiniteWeightedGraph

/-- Quantitative repaired-reference comparison in the original labels. -/
theorem subcritical_repaired_reference_cut_le
    {k n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (D : SubcriticalDivision k (Fin n)) (R : FiniteWeightedGraph (Fin n))
    {e beta : ℝ} (hedit : (subcriticalDefectCost G D : ℝ) ≤ e * (n : ℝ) ^ 2)
    (hcut : finiteLabeledCutDist (ofSimpleGraph G) R ≤ beta) :
    finiteLabeledCutDist (ofSimpleGraph (subcriticalDivisionModelGraph G D)) R ≤
      2 * e + beta := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he := finiteLabeledCutDist_subcriticalDivisionModelGraph_le G D
  simp only [Fintype.card_fin] at he
  have he' : finiteLabeledCutDist (ofSimpleGraph G)
      (ofSimpleGraph (subcriticalDivisionModelGraph G D)) ≤ 2 * e := by
    apply he.trans
    apply (div_le_iff₀ (sq_pos_of_pos hnR)).mpr
    nlinarith
  have htri := finiteLabeledCutDist_triangle
    (ofSimpleGraph (subcriticalDivisionModelGraph G D)) (ofSimpleGraph G) R
  rw [finiteLabeledCutDist_comm (ofSimpleGraph (subcriticalDivisionModelGraph G D))
    (ofSimpleGraph G)] at htri
  linarith

/-- The full finite alignment follows from the numerical package and cut
closeness alone. No induced-freeness, exact edge count, or pre-existing
compatibility certificate is required. -/
theorem subcriticalCanonicalAlignmentCore
    (alignment : FiniteWeightedAlignmentInput)
    (k : ℕ) (hk : 3 ≤ k) (R₀ : ℕ)
    {omega eta theta alpha delta epsilon : ℝ}
    (P : SubcriticalClosenessParameters k R₀ omega eta theta alpha delta epsilon) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
        ∀ G : SimpleGraph (Fin n),
          cutDist (graphGraphon G) (WLambda hk L) < tau →
            ∃ pi : Equiv.Perm (Fin n),
              (canonicalSubcriticalDefectCost G R₀ hk (by simpa using hn0.trans hn) : ℝ) ≤
                P.epsilonWork * (n : ℝ) ^ 2 ∧
              finiteLabeledCutDist (ofSimpleGraph G)
                ((subcriticalReferenceWeightedGraph hk L n).permute pi) ≤ P.beta ∧
              4 ≤ P.t * n / 4 ∧
              2 ≤ subcriticalPaletteGap k * (P.zeta * n) ∧
              Nonempty (SubcriticalComponentAlignment
                (canonicalSubcriticalDivision G R₀ hk (by simpa using hn0.trans hn))
                L pi P.t (P.zeta * n) P.B) := by
  obtain ⟨tauE, htauE, hE⟩ := subcriticalCanonicalDefectCost_le_of_cutCloseCore
    alignment k hk P.epsilonWork P.epsilonWork_mem
  obtain ⟨tauA, htauA, hA⟩ := exists_subcritical_fullReference_alignment_radius
    alignment P.beta P.beta_pos
  refine ⟨min tauE tauA, lt_min htauE htauA, ?_⟩
  intro L
  obtain ⟨nE, hnE, hE⟩ := hE L
  obtain ⟨nA, hnA⟩ := hA (WLambda hk L) (subcriticalReferenceWeightedGraph hk L)
    (subcriticalReferenceGraphon_tendsto_WLambda hk L)
  let nR : ℕ := Nat.ceil (max (16 / P.t) (2 / (subcriticalPaletteGap k * P.zeta)))
  let n0 := max nE (max nA nR)
  have hn0 : k - 1 ≤ n0 := hnE.trans (le_max_left _ _)
  refine ⟨n0, hn0, ?_⟩
  intro n hn G hG
  have hEn : nE ≤ n := (le_max_left _ _).trans hn
  have hAn : nA ≤ n := (le_max_of_le_right (le_max_left _ _)).trans hn
  have hRn : nR ≤ n := (le_max_of_le_right (le_max_right _ _)).trans hn
  have hnpos : 0 < n := by have := hn0.trans hn; omega
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hRn' : max (16 / P.t) (2 / (subcriticalPaletteGap k * P.zeta)) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hRn)
  have hround : 4 ≤ P.t * n / 4 := by
    have h := (div_le_iff₀ P.t_pos).mp ((le_max_left _ _).trans hRn')
    nlinarith
  have hdiag : 2 ≤ subcriticalPaletteGap k * (P.zeta * n) := by
    have h := (div_le_iff₀ (mul_pos (subcriticalPaletteGap_pos hk) P.zeta_pos)).mp
      ((le_max_right _ _).trans hRn')
    nlinarith
  have hedit := hE hEn G R₀ (hG.trans_le (min_le_left _ _))
  obtain ⟨pi, hpi⟩ := hnA n hAn G (hG.trans_le (min_le_right _ _))
  refine ⟨pi, hedit, hpi.le, hround, hdiag, ?_⟩
  let D := canonicalSubcriticalDivision G R₀ hk (by simpa using hn0.trans hn)
  let H := subcriticalDivisionModelGraph G D
  have hedit' : (subcriticalDefectCost G D : ℝ) ≤ P.epsilonWork * (n : ℝ) ^ 2 := hedit
  have hcut := subcritical_repaired_reference_cut_le hnpos G D
    ((subcriticalReferenceWeightedGraph hk L n).permute pi) hedit' hpi.le
  have hfinite : finiteLabeledCutDist (ofSimpleGraph H)
      ((subcriticalReferenceWeightedGraph hk L n).permute pi) * (n : ℝ) ^ 2 <
        subcriticalPaletteGap k * (P.zeta * n) ^ 2 := by
    have hh := mul_lt_mul_of_pos_right (hcut.trans_lt P.contradiction_reserve)
      (sq_pos_of_pos hnRpos)
    nlinarith only [hh]
  apply subcritical_exists_component_alignment hk hnpos D H
    (subcriticalDivisionModelGraph_isRegularBlowupFor G D) L pi P.t_pos
    (mul_pos P.zeta_pos hnRpos) P.B P.four_div_t_le_B
  · have h := mul_le_mul_of_nonneg_right P.degree_reserve hnRpos.le
    nlinarith only [h]
  · exact hround
  · exact hdiag
  · have h := mul_le_mul_of_nonneg_right P.cell_error_reserve hnRpos.le
    push_cast at h
    have hz := mul_pos P.zeta_pos hnRpos
    nlinarith
  · exact hfinite

end InducedStars
