import InducedStars.Structure.Subcritical.Retained
import InducedStars.Structure.Subcritical.ModelEdgeBounds

/-!
# Sparse-side controls

Paper: Lemma `lemma:SubCompareSparseSideEdgesK1k`. The finite argument counts
the repaired regular blow-up, transfers unordered induced-edge counts with
edit coefficient one, and applies Turán to an original-graph neighborhood.
In particular no individual row is transferred across a global edit bound.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical

namespace InducedStars

/-- A single generous constant for all three sparse-side estimates. -/
def subcriticalSparseSideConstant (k : ℕ) : ℝ := 100 * (k : ℝ)^2

theorem subcriticalSparseSideConstant_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < subcriticalSparseSideConstant k := by
  have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold subcriticalSparseSideConstant
  positivity

variable {k n : ℕ}

/-- Pairwise size ratio at most two bounds every visible part by twice its
component's average size, without divisibility or equal-part assumptions. -/
theorem subcritical_visible_part_card_le_average
    (D : SubcriticalDivision k (Fin n)) (i : Fin D.componentCount)
    {omega : ℝ} (homega : omega ≤ 1)
    (hratio : ∀ u v : Fin (D.core i).order,
      ((D.parts i u).card : ℝ) ≤ (1 + omega) * (D.parts i v).card)
    (u : Fin (D.core i).order) :
    ((D.parts i u).card : ℝ) ≤ 2 * (D.componentSupport i).card / (D.core i).order := by
  have hs : (∑ _v : Fin (D.core i).order, ((D.parts i u).card : ℝ)) ≤
      ∑ v : Fin (D.core i).order, 2 * ((D.parts i v).card : ℝ) := by
    apply Finset.sum_le_sum
    intro v _
    have hh := hratio u v
    have hm := mul_le_mul_of_nonneg_right homega
      (show (0 : ℝ) ≤ (D.parts i v).card from Nat.cast_nonneg _)
    linarith
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, ← Nat.cast_sum, ← D.card_componentSupport i] at hs
  apply (le_div_iff₀ (by exact_mod_cast (D.core i).order_pos)).mpr
  simpa only [mul_comm] using hs

/-- The visible-component quadratic estimate used in the source counting
argument follows by multiplying the part-to-average bound and summing. -/
theorem subcritical_visible_sum_part_sq_le
    (D : SubcriticalDivision k (Fin n)) (i : Fin D.componentCount)
    {omega : ℝ} (homega : omega ≤ 1)
    (hratio : ∀ u v : Fin (D.core i).order,
      ((D.parts i u).card : ℝ) ≤ (1 + omega) * (D.parts i v).card) :
    (∑ u, ((D.parts i u).card : ℝ)^2) ≤
      2 * ((D.componentSupport i).card : ℝ)^2 / (D.core i).order := by
  have hs : (∑ u, ((D.parts i u).card : ℝ)^2) ≤
      ∑ u, (2 * (D.componentSupport i).card / (D.core i).order) *
        ((D.parts i u).card : ℝ) := by
    apply Finset.sum_le_sum
    intro u _
    have hh := mul_le_mul_of_nonneg_right
      (subcritical_visible_part_card_le_average D i homega hratio u)
      (show (0 : ℝ) ≤ (D.parts i u).card from Nat.cast_nonneg _)
    simpa only [pow_two] using hh
  rw [← Finset.mul_sum, ← Nat.cast_sum, ← D.card_componentSupport i] at hs
  convert hs using 1 <;> ring

/-- A nonvisible component needs no balancing hypothesis. -/
theorem subcritical_nonvisible_sum_part_sq_le
    (D : SubcriticalDivision k (Fin n)) (i : Fin D.componentCount)
    {theta : ℝ} (hvis : i ∉ D.visibleComponentIndices theta) :
    (∑ u, ((D.parts i u).card : ℝ)^2) ≤
      theta * n * (D.componentSupport i).card := by
  have hs : (∑ u, ((D.parts i u).card : ℝ)^2) ≤
      ∑ u, (theta * n) * ((D.parts i u).card : ℝ) := by
    apply Finset.sum_le_sum
    intro u _
    have hp : ((D.parts i u).card : ℝ) ≤ theta * n := by
      by_contra h
      exact hvis ((D.mem_visibleComponentIndices theta i).mpr
        ⟨u, by simpa only [Fintype.card_fin] using (lt_of_not_ge h).le⟩)
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hp
      (show (0 : ℝ) ≤ (D.parts i u).card from Nat.cast_nonneg _)
  simpa only [← Finset.mul_sum, ← Nat.cast_sum, ← D.card_componentSupport i] using hs

/-- Every part of a nonretained component is small under the explicit
cutoff hierarchy. This includes small supports, nonvisible components,
and visible components with large core order. -/
theorem subcritical_nonretained_part_card_le
    (D : SubcriticalDivision k (Fin n)) {eta theta omega : ℝ} {R₀ : ℕ}
    (heta : 0 ≤ eta) (hR : 1 ≤ R₀) (hinv : 1 / (R₀ : ℝ) ≤ eta)
    (htheta : theta ≤ eta) (homega : omega ≤ 1)
    (hratio : ∀ i, i ∈ D.visibleComponentIndices theta →
      ∀ u v : Fin (D.core i).order,
        ((D.parts i u).card : ℝ) ≤ (1 + omega) * (D.parts i v).card)
    (a : D.PartIndex) (ha : a.1 ∉ D.retainedComponentIndices eta R₀) :
    ((D.part a).card : ℝ) ≤ 2 * eta * n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hp : (D.part a).card ≤ (D.componentSupport a.1).card :=
    Finset.card_le_card (fun _ hx ↦ D.mem_componentSupport.mpr ⟨a.2, hx⟩)
  by_cases hs : ((D.componentSupport a.1).card : ℝ) < eta * n
  · have hpR : ((D.part a).card : ℝ) ≤ (D.componentSupport a.1).card := by exact_mod_cast hp
    nlinarith
  have horder : R₀ < (D.core a.1).order := by
    by_contra h
    exact ha ((D.mem_retainedComponentIndices eta R₀ a.1).mpr
      ⟨by simpa only [Fintype.card_fin] using le_of_not_gt hs, by omega⟩)
  by_cases hv : a.1 ∈ D.visibleComponentIndices theta
  · have hpAvg := subcritical_visible_part_card_le_average D a.1 homega (hratio a.1 hv) a.2
    have hq : (0 : ℝ) < (D.core a.1).order := by exact_mod_cast (D.core a.1).order_pos
    have hRR : (0 : ℝ) < R₀ := by exact_mod_cast (show 0 < R₀ by omega)
    have hcap : ((D.componentSupport a.1).card : ℝ) ≤ n := by
      exact_mod_cast (show (D.componentSupport a.1).card ≤ n by
        simpa using (Finset.card_le_univ (D.componentSupport a.1)))
    have hi : 1 ≤ eta * (R₀ : ℝ) := (div_le_iff₀ hRR).mp hinv
    have hqR : (R₀ : ℝ) ≤ (D.core a.1).order := by exact_mod_cast horder.le
    have hiq : 1 ≤ eta * ((D.core a.1).order : ℝ) :=
      hi.trans (mul_le_mul_of_nonneg_left hqR heta)
    have hdiv : 2 * (D.componentSupport a.1).card / (D.core a.1).order ≤
        2 * eta * n := by
      apply (div_le_iff₀ hq).mpr
      have hh := mul_le_mul_of_nonneg_right hiq hn
      nlinarith
    exact hpAvg.trans hdiv
  · have hpSmall : ((D.part a).card : ℝ) < theta * n := by
      by_contra hh
      exact hv ((D.mem_visibleComponentIndices theta a.1).mpr
        ⟨a.2, by simpa only [Fintype.card_fin, SubcriticalDivision.part] using le_of_not_gt hh⟩)
    have hh := mul_le_mul_of_nonneg_right htheta hn
    nlinarith

theorem subcriticalModel_nonretained_degree_le
    (hk : 3 ≤ k) (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n))
    {eta theta omega : ℝ} {R₀ : ℕ}
    (heta : 0 ≤ eta) (hR : 1 ≤ R₀) (hinv : 1 / (R₀ : ℝ) ≤ eta)
    (htheta : theta ≤ eta) (homega : omega ≤ 1)
    (hratio : ∀ i, i ∈ D.visibleComponentIndices theta →
      ∀ u v : Fin (D.core i).order,
        ((D.parts i u).card : ℝ) ≤ (1 + omega) * (D.parts i v).card)
    (x : Fin n) (hx : x ∈ D.nonretainedVertices eta R₀) (A : Finset (Fin n)) :
    (degreeInFinset (subcriticalDivisionModelGraph G D) x A : ℝ) ≤
      2 * (k : ℝ) * eta * n := by
  rcases D.sparse_or_existsUnique_part x with hs | ⟨a, ha, _⟩
  · rw [subcriticalModel_degree_eq_zero_of_sparse G D hs]
    norm_num only [Nat.cast_zero]
    positivity
  · have hnret : a.1 ∉ D.retainedComponentIndices eta R₀ := by
      intro hh
      exact (D.mem_nonretainedVertices eta R₀ x).mp hx
        ((D.mem_retainedVertices eta R₀ x).mpr
          ⟨a.1, hh, D.mem_componentSupport.mpr ⟨a.2, ha⟩⟩)
    have hparts (j : Fin (D.core a.1).order) : ((D.parts a.1 j).card : ℝ) ≤ 2 * eta * n :=
      subcritical_nonretained_part_card_le D heta hR hinv htheta homega hratio ⟨a.1, j⟩ hnret
    have hh := subcriticalModel_degree_le_of_part_bound hk G D a ha A (2 * eta * n) hparts
    have hkle : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast (Nat.sub_le k 1)
    have hmul := mul_le_mul_of_nonneg_right hkle (show 0 ≤ 2 * eta * (n : ℝ) by positivity)
    nlinarith

/-- Raw repaired sparse-side estimate before absorbing the cutoff scales
into `eta`. Components of every order, including nonvisible unbalanced
components, are counted. -/
theorem subcriticalModel_nonretained_edges_le_raw
    (hk : 3 ≤ k) (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n))
    {eta theta omega : ℝ} {R₀ : ℕ}
    (heta : 0 ≤ eta) (htheta : 0 ≤ theta) (hR : 1 ≤ R₀) (homega : omega ≤ 1)
    (hratio : ∀ i, i ∈ D.visibleComponentIndices theta →
      ∀ u v : Fin (D.core i).order,
        ((D.parts i u).card : ℝ) ≤ (1 + omega) * (D.parts i v).card) :
    (inducedEdgeCount (subcriticalDivisionModelGraph G D)
      (D.nonretainedVertices eta R₀) : ℝ) ≤
        2 * (k : ℝ) * (eta + theta + 1 / (R₀ : ℝ)) * (n : ℝ)^2 := by
  let z : ℝ := eta + theta + 1 / (R₀ : ℝ)
  have hinv : (0 : ℝ) ≤ 1 / (R₀ : ℝ) := by positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hetaZ : eta ≤ z := by dsimp [z]; linarith
  have hthetaZ : theta ≤ z := by dsimp [z]; linarith
  have hinvZ : 1 / (R₀ : ℝ) ≤ z := by dsimp [z]; linarith
  have hsubset : D.nonretainedVertices eta R₀ ⊆ D.nonretainedVertices z R₀ := by
    intro x hx
    apply (D.mem_nonretainedVertices z R₀ x).mpr
    intro hh
    obtain ⟨i, hi, hxi⟩ := (D.mem_retainedVertices z R₀ x).mp hh
    obtain ⟨his, hiq⟩ := (D.mem_retainedComponentIndices z R₀ i).mp hi
    have hie : eta * Fintype.card (Fin n) ≤ (D.componentSupport i).card :=
      (mul_le_mul_of_nonneg_right hetaZ (Nat.cast_nonneg _)).trans his
    exact (D.mem_nonretainedVertices eta R₀ x).mp hx
      ((D.mem_retainedVertices eta R₀ x).mpr
        ⟨i, (D.mem_retainedComponentIndices eta R₀ i).mpr ⟨hie, hiq⟩, hxi⟩)
  have hbound := inducedEdgeCount_le_mul_of_degreeInFinset_le
    (subcriticalDivisionModelGraph G D) (D.nonretainedVertices eta R₀)
    (2 * (k : ℝ) * z * n) (fun x hx ↦
      subcriticalModel_nonretained_degree_le hk G D hz hR hinvZ hthetaZ homega
        hratio x (hsubset hx) _)
  have hcard : ((D.nonretainedVertices eta R₀).card : ℝ) ≤ n := by
    exact_mod_cast (show (D.nonretainedVertices eta R₀).card ≤ n by
      simpa using (Finset.card_le_univ (D.nonretainedVertices eta R₀)))
  have hmul := mul_le_mul_of_nonneg_left hcard
    (show 0 ≤ 2 * (k : ℝ) * z * n by positivity)
  dsimp [z] at hbound hmul
  nlinarith

theorem subcriticalModel_nonretainedSmall_degree_le
    (hk : 3 ≤ k) (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n))
    {eta theta : ℝ} {R₀ : ℕ} (htheta : 0 ≤ theta)
    (x : Fin n) (hx : x ∈ D.nonretainedSmallVertices eta R₀ theta) (A : Finset (Fin n)) :
    (degreeInFinset (subcriticalDivisionModelGraph G D) x A : ℝ) ≤
      (k : ℝ) * theta * n := by
  rcases D.sparse_or_existsUnique_part x with hs | ⟨a, ha, _⟩
  · rw [subcriticalModel_degree_eq_zero_of_sparse G D hs]
    norm_num only [Nat.cast_zero]
    positivity
  · obtain ⟨hnret, hnlg⟩ := (D.mem_nonretainedSmallVertices eta R₀ theta x).mp hx
    have hcomp : x ∈ D.componentSupport a.1 := D.mem_componentSupport.mpr ⟨a.2, ha⟩
    have hnret' : a.1 ∉ D.retainedComponentIndices eta R₀ := fun hh ↦
      (D.mem_nonretainedVertices eta R₀ x).mp hnret
        ((D.mem_retainedVertices_iff_of_mem_componentSupport hcomp).mpr hh)
    have hvis : a.1 ∉ D.visibleComponentIndices theta := fun hh ↦ hnlg
      ((D.mem_nonretainedVisibleVertices eta R₀ theta x).mpr ⟨a.1, hh, hnret', hcomp⟩)
    have hparts (j : Fin (D.core a.1).order) : ((D.parts a.1 j).card : ℝ) ≤ theta * n := by
      by_contra hh
      exact hvis ((D.mem_visibleComponentIndices theta a.1).mpr
        ⟨j, by simpa only [Fintype.card_fin] using (lt_of_not_ge hh).le⟩)
    have hh := subcriticalModel_degree_le_of_part_bound hk G D a ha A (theta * n) hparts
    have hkle : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast (Nat.sub_le k 1)
    have hmul := mul_le_mul_of_nonneg_right hkle (show 0 ≤ theta * (n : ℝ) by positivity)
    nlinarith

/-- Uniform subset estimate with exactly one copy of the unordered edit error. -/
theorem subcritical_smallSide_subset_edges_le
    (hk : 3 ≤ k) (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n))
    {eta theta epsilon : ℝ} {R₀ : ℕ} (htheta : 0 ≤ theta)
    (hdefect : (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ)^2)
    (A : Finset (Fin n)) (hA : A ⊆ D.nonretainedSmallVertices eta R₀ theta) :
    (inducedEdgeCount G A : ℝ) ≤ (k : ℝ) * theta * n * A.card + epsilon * (n : ℝ)^2 := by
  have hmodel := inducedEdgeCount_le_mul_of_degreeInFinset_le
    (subcriticalDivisionModelGraph G D) A ((k : ℝ) * theta * n)
    (fun x hx ↦ subcriticalModel_nonretainedSmall_degree_le hk G D htheta x (hA hx) A)
  have htransfer := inducedEdgeCount_le_add_simpleGraphEditDistance G
    (subcriticalDivisionModelGraph G D) A
  rw [simpleGraphEditDistance_subcriticalDivisionModelGraph] at htransfer
  have ht : (inducedEdgeCount G A : ℝ) ≤
      inducedEdgeCount (subcriticalDivisionModelGraph G D) A + (subcriticalDefectCost G D : ℝ) :=
    by exact_mod_cast htransfer
  linarith

end InducedStars

namespace InducedStars

/-- The neighborhood quadratic gives a linear row bound once its two
lower-order errors are absorbed by the explicit scale condition. -/
theorem subcriticalSparseSide_row_bound_of_quadratic
    {k : ℕ} (hk : 3 ≤ k) {a t : ℝ} (ha : 0 ≤ a) (ht : 1 ≤ t)
    (hquad : a^2 / (2 * (k - 1 : ℕ)) - a / 2 ≤
      (k : ℝ) * t * a + t^2) :
    a ≤ 4 * (k : ℝ)^2 * t := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (by omega : 0 < k - 1)
  have heq : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hq : a^2 ≤
      2 * ((k - 1 : ℕ) : ℝ) * ((k : ℝ) * t * a + t^2 + a / 2) := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * ((k - 1 : ℕ) : ℝ))).mp
      (show a^2 / (2 * (k - 1 : ℕ)) ≤ (k : ℝ) * t * a + t^2 + a / 2 by linarith)
    nlinarith
  rw [heq] at hq
  by_cases hat : a ≤ t
  · have hc : (1 : ℝ) ≤ 4 * (k : ℝ)^2 := by nlinarith
    exact hat.trans (by nlinarith)
  have hat' : t ≤ a := (lt_of_not_ge hat).le
  have hta : t^2 ≤ t * a := by nlinarith
  have hlinear : a ≤ t * a := by nlinarith
  have hterm : 2 * ((k : ℝ) - 1) * t^2 ≤
      2 * ((k : ℝ) - 1) * (t * a) :=
    mul_le_mul_of_nonneg_left hta (by linarith)
  have hlin : ((k : ℝ) - 1) * a ≤ ((k : ℝ) - 1) * (t * a) :=
    mul_le_mul_of_nonneg_left hlinear (by linarith)
  have hcoeff : 2 * ((k : ℝ) - 1) * (k : ℝ) + 3 * ((k : ℝ) - 1) ≤
      4 * (k : ℝ)^2 := by nlinarith
  have hcoeffMul := mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ t * a by positivity)
  have hsquare : a^2 ≤ (4 * (k : ℝ)^2 * t) * a := by nlinarith
  by_contra h
  have hap : 0 < a := by linarith
  have hmul := mul_lt_mul_of_pos_right (lt_of_not_ge h) hap
  nlinarith

/-- The unabsorbed row estimate, displaying both the square-root edit
error and the finite constant term explicitly. -/
theorem subcriticalSparseSide_row_bound_raw
    {k : ℕ} (hk : 3 ≤ k) {a n theta epsilon : ℝ}
    (ha : 0 ≤ a) (hn : 0 ≤ n) (htheta : 0 ≤ theta) (heps : 0 ≤ epsilon)
    (hquad : a^2 / (2 * (k - 1 : ℕ)) - a / 2 ≤
      (k : ℝ) * theta * n * a + epsilon * n^2) :
    a ≤ 4 * (k : ℝ)^2 * (theta * n + Real.sqrt epsilon * n + 1) := by
  let t := theta * n + Real.sqrt epsilon * n + 1
  have hsqrt : 0 ≤ Real.sqrt epsilon * n := mul_nonneg (Real.sqrt_nonneg epsilon) hn
  have ht : 1 ≤ t := by dsimp [t]; linarith [mul_nonneg htheta hn]
  have httheta : theta * n ≤ t := by dsimp [t]; linarith
  have htsqrt : Real.sqrt epsilon * n ≤ t := by
    dsimp [t]
    linarith [mul_nonneg htheta hn]
  have hsquare : (Real.sqrt epsilon * n)^2 = epsilon * n^2 := by
    rw [mul_pow, Real.sq_sqrt heps]
  have herror : epsilon * n^2 ≤ t^2 := by nlinarith
  have hlinear := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left httheta (Nat.cast_nonneg k)) ha
  exact subcriticalSparseSide_row_bound_of_quadratic hk ha ht (by nlinarith)

/-- The raw original-graph row bound before the hierarchy absorbs its
square-root and constant errors. -/
theorem subcritical_smallSide_degree_le_raw
    {k n : ℕ} (hk : 3 ≤ k) (G : SimpleGraph (Fin n))
    (D : SubcriticalDivision k (Fin n)) {eta theta epsilon : ℝ} {R₀ : ℕ}
    (htheta : 0 ≤ theta) (heps : 0 ≤ epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hdefect : (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ)^2)
    (x : Fin n) :
    (degreeInFinset G x (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
      4 * (k : ℝ)^2 * (theta * n + Real.sqrt epsilon * n + 1) := by
  let A := (D.nonretainedSmallVertices eta R₀ theta).filter (G.Adj x)
  have hA : A ⊆ D.nonretainedSmallVertices eta R₀ theta := Finset.filter_subset _ _
  have hadj : ∀ y ∈ A, G.Adj x y := fun y hy ↦ (Finset.mem_filter.mp hy).2
  have hlower := inducedEdgeCount_neighborhood_lower hk G hfree x A hadj
  have hupper := subcritical_smallSide_subset_edges_le hk G D htheta hdefect A hA
  change (A.card : ℝ) ≤ _
  exact subcriticalSparseSide_row_bound_raw hk (Nat.cast_nonneg A.card)
    (Nat.cast_nonneg n) htheta heps (hlower.trans hupper)

/-- The finite three-part form of Paper Lemma
`lemma:SubCompareSparseSideEdgesK1k`. Only the actual defect bound and
visible-component ratio bound are consumed. The row estimate is proved
in the original graph using its star-free neighborhood, not by edit
transfer of an individual row. -/
theorem subcriticalSparseSideControls_of_geometry
    {k n : ℕ} (hk : 3 ≤ k) (G : SimpleGraph (Fin n))
    (D : SubcriticalDivision k (Fin n))
    {eta theta epsilon omega : ℝ} {R₀ : ℕ}
    (heta : 0 ≤ eta) (hR : 1 ≤ R₀) (hinv : 1 / (R₀ : ℝ) ≤ eta)
    (homega : omega ≤ 1) (htheta : theta ≤ eta)
    (hepsEta : epsilon ≤ eta) (hepsTheta : epsilon ≤ theta^2)
    (hscale : 1 ≤ theta * n)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hdefect : (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ)^2)
    (hratio : ∀ i, i ∈ D.visibleComponentIndices theta →
      ∀ u v : Fin (D.core i).order,
        ((D.parts i u).card : ℝ) ≤ (1 + omega) * (D.parts i v).card) :
    (inducedEdgeCount G (D.nonretainedVertices eta R₀) : ℝ) ≤
        subcriticalSparseSideConstant k * eta * (n : ℝ)^2 ∧
      (∀ A ⊆ D.nonretainedSmallVertices eta R₀ theta,
        (inducedEdgeCount G A : ℝ) ≤
          subcriticalSparseSideConstant k * theta * n * A.card + epsilon * (n : ℝ)^2) ∧
      (∀ x : Fin n,
        (degreeInFinset G x (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
          subcriticalSparseSideConstant k * theta * n) := by
  have hn : (0 : ℝ) < n := by
    exact_mod_cast D.componentCount_pos.trans_le
      (by simpa only [Fintype.card_fin] using D.componentCount_le_card)
  have htheta0 : 0 ≤ theta := by nlinarith
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hCk : (k : ℝ) ≤ subcriticalSparseSideConstant k := by
    unfold subcriticalSparseSideConstant
    nlinarith
  have hCtotal : 2 * (k : ℝ) + 1 ≤ subcriticalSparseSideConstant k := by
    unfold subcriticalSparseSideConstant
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · let S := D.nonretainedVertices eta R₀
    have hmodel := inducedEdgeCount_le_mul_of_degreeInFinset_le
      (subcriticalDivisionModelGraph G D) S (2 * (k : ℝ) * eta * n)
      (fun x hx ↦ subcriticalModel_nonretained_degree_le hk G D heta hR hinv
        htheta homega hratio x hx S)
    have hScard : (S.card : ℝ) ≤ n := by
      exact_mod_cast (show S.card ≤ n by simpa using Finset.card_le_univ S)
    have hcap := mul_le_mul_of_nonneg_left hScard
      (show 0 ≤ 2 * (k : ℝ) * eta * n by positivity)
    have htransfer := inducedEdgeCount_le_add_simpleGraphEditDistance G
      (subcriticalDivisionModelGraph G D) S
    rw [simpleGraphEditDistance_subcriticalDivisionModelGraph] at htransfer
    have ht : (inducedEdgeCount G S : ℝ) ≤
        inducedEdgeCount (subcriticalDivisionModelGraph G D) S +
          (subcriticalDefectCost G D : ℝ) := by exact_mod_cast htransfer
    have heps := mul_le_mul_of_nonneg_right hepsEta (sq_nonneg (n : ℝ))
    have hconst := mul_le_mul_of_nonneg_right hCtotal
      (show 0 ≤ eta * (n : ℝ)^2 by positivity)
    change (inducedEdgeCount G S : ℝ) ≤ _
    nlinarith
  · intro A hA
    have hsubset := subcritical_smallSide_subset_edges_le hk G D htheta0 hdefect A hA
    have hconst := mul_le_mul_of_nonneg_right hCk
      (show 0 ≤ theta * n * (A.card : ℝ) by positivity)
    nlinarith
  · intro x
    let A := (D.nonretainedSmallVertices eta R₀ theta).filter (G.Adj x)
    have hA : A ⊆ D.nonretainedSmallVertices eta R₀ theta := Finset.filter_subset _ _
    have hadj : ∀ y ∈ A, G.Adj x y := fun y hy ↦ (Finset.mem_filter.mp hy).2
    have hlower := inducedEdgeCount_neighborhood_lower hk G hfree x A hadj
    have hupper := subcritical_smallSide_subset_edges_le hk G D htheta0 hdefect A hA
    have heps := mul_le_mul_of_nonneg_right hepsTheta (sq_nonneg (n : ℝ))
    have hquad : (A.card : ℝ)^2 / (2 * (k - 1 : ℕ)) - (A.card : ℝ) / 2 ≤
        (k : ℝ) * (theta * n) * A.card + (theta * n)^2 := by nlinarith
    have hrow := subcriticalSparseSide_row_bound_of_quadratic hk
      (Nat.cast_nonneg A.card) hscale hquad
    have hC : 4 * (k : ℝ)^2 ≤ subcriticalSparseSideConstant k := by
      unfold subcriticalSparseSideConstant
      nlinarith [sq_nonneg (k : ℝ)]
    have hconst := mul_le_mul_of_nonneg_right hC
      (show 0 ≤ theta * n by positivity)
    change (A.card : ℝ) ≤ _
    nlinarith

namespace SubcriticalCloseStructureResult

/-- Sparse-side controls for the one common close-structure witness. -/
theorem sparseSideControls
    {k n R₀ : ℕ} {hk : 3 ≤ k}
    {G : SimpleGraph (Fin n)} {D : SubcriticalDivision k (Fin n)}
    {L : AdmissibleBlockSequence k} {omega eta theta alpha delta epsilon : ℝ}
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (heta : 0 ≤ eta) (hR : 1 ≤ R₀) (hinv : 1 / (R₀ : ℝ) ≤ eta)
    (homega : omega ≤ 1) (htheta : theta ≤ eta)
    (hepsEta : epsilon ≤ eta) (hepsTheta : epsilon ≤ theta^2)
    (hscale : 1 ≤ theta * n)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G) :
    (inducedEdgeCount G (D.nonretainedVertices eta R₀) : ℝ) ≤
        subcriticalSparseSideConstant k * eta * (n : ℝ)^2 ∧
      (∀ A ⊆ D.nonretainedSmallVertices eta R₀ theta,
        (inducedEdgeCount G A : ℝ) ≤
          subcriticalSparseSideConstant k * theta * n * A.card + epsilon * (n : ℝ)^2) ∧
      (∀ x : Fin n,
        (degreeInFinset G x (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
          subcriticalSparseSideConstant k * theta * n) :=
  subcriticalSparseSideControls_of_geometry hk G D heta hR hinv homega htheta
    hepsEta hepsTheta hscale hfree R.defect_cost_le R.visible_component_ratio

end SubcriticalCloseStructureResult
end InducedStars
