import InducedStars.Structure.Subcritical.ResidualMatchingPlacement
import InducedStars.Structure.Subcritical.ResidualDegree

/-!
# Exact selection and thinning of a residual matching

The finite pigeonhole argument uses the canonical maximum matching,
then selects exactly the prescribed ceiling. Every deletion and every
large-order reserve is quantitative.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}

private theorem residualPlacement_exists_of_left_retained {x y : V}
    (hx : x ∈ D.retainedVertices eta R₀) (hno : ¬ D.ActivePair x y) :
    ∃ c : SubcriticalResidualMatchingPlacement D eta R₀, c.Contains s(x, y) := by
  let a : SubcriticalRetainedPartIndex D eta R₀ :=
    ⟨D.retainedVertexPart eta R₀ x hx, D.retainedVertexPart_mem_retained eta R₀ x hx⟩
  have hxa : x ∈ D.part a.val := D.mem_retainedVertexPart eta R₀ x hx
  by_cases hy : y ∈ D.retainedVertices eta R₀
  · let b : SubcriticalRetainedPartIndex D eta R₀ :=
      ⟨D.retainedVertexPart eta R₀ y hy, D.retainedVertexPart_mem_retained eta R₀ y hy⟩
    have hyb : y ∈ D.part b.val := D.mem_retainedVertexPart eta R₀ y hy
    have hnoab : ¬ D.ActivePart a.val b.val := fun h ↦
      hno ((D.activePair_iff_of_mem_parts hxa hyb).mpr h)
    by_cases hab : a = b
    · refine ⟨.internal a, ?_⟩
      exact ⟨x, hxa, y, hab ▸ hyb, rfl⟩
    have hrne : subcriticalRetainedPartRank a ≠ subcriticalRetainedPartRank b :=
      fun h ↦ hab (subcriticalRetainedPartRank_injective h)
    by_cases hr : subcriticalRetainedPartRank a < subcriticalRetainedPartRank b
    · by_cases hi : a.val.1 = b.val.1
      · exact ⟨.inactive a b hr hi hnoab, x, hxa, y, hyb, rfl⟩
      · exact ⟨.different a b hr hi, x, hxa, y, hyb, rfl⟩
    · have hr' : subcriticalRetainedPartRank b < subcriticalRetainedPartRank a :=
        lt_of_le_of_ne (le_of_not_gt hr) hrne.symm
      have hno' : ¬ D.ActivePart b.val a.val := by
        rintro ⟨i, u, v, hb, ha, huv⟩
        exact hnoab ⟨i, v, u, ha, hb, huv.symm⟩
      by_cases hi : b.val.1 = a.val.1
      · exact ⟨.inactive b a hr' hi hno', y, hyb, x, hxa, Sym2.eq_swap⟩
      · exact ⟨.different b a hr' hi, y, hyb, x, hxa, Sym2.eq_swap⟩
  · exact ⟨.sparse a, x, hxa, y, (D.mem_nonretainedVertices eta R₀ y).mpr hy, rfl⟩

/-- Every retained-incident nonactive pair occupies one of the four
geometric classes. This excludes active and wholly nonretained pairs. -/
theorem subcriticalResidualMatchingPlacement_exists {x y : V}
    (hret : x ∈ D.retainedVertices eta R₀ ∨ y ∈ D.retainedVertices eta R₀)
    (hno : ¬ D.ActivePair x y) :
    ∃ c : SubcriticalResidualMatchingPlacement D eta R₀, c.Contains s(x, y) := by
  rcases hret with hx | hy
  · exact residualPlacement_exists_of_left_retained hx hno
  · obtain ⟨c, hc⟩ := residualPlacement_exists_of_left_retained (x := y) (y := x) hy
      (fun h ↦ hno ((D.activePair_comm x y).mpr h))
    refine ⟨c, ?_⟩
    rw [Sym2.eq_swap (a := x) (b := y)]
    exact hc

/-- A matching's assigned placement fibers are disjoint. Each fiber
retains its actual geometric target, including the designated orientation. -/
theorem residualPlacement_fibers_disjoint {E : Finset (Sym2 V)}
    (f : {e // e ∈ E} → SubcriticalResidualMatchingPlacement D eta R₀)
    {a b : SubcriticalResidualMatchingPlacement D eta R₀} (hab : a ≠ b) :
    Disjoint (Finset.univ.filter fun e ↦ f e = a)
      (Finset.univ.filter fun e ↦ f e = b) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact hab ((Finset.mem_filter.mp he).2.symm.trans (Finset.mem_filter.mp hf).2)

theorem residualPlacement_fibers_cover {E : Finset (Sym2 V)}
    (f : {e // e ∈ E} → SubcriticalResidualMatchingPlacement D eta R₀) :
    Finset.univ.biUnion (fun c ↦ Finset.univ.filter fun e ↦ f e = c) =
      (Finset.univ : Finset {e // e ∈ E}) := by
  ext e
  simp

/-- Pigeonhole on the canonical maximum matching, in exact integer form. -/
theorem exists_subcriticalHomogeneousResidualMatching
    (T : SimpleGraph V) (B : Finset V)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hR : 1 ≤ R₀)
    (hallowed : ∀ x y, T.Adj x y →
      (x ∈ D.retainedVertices eta R₀ ∨ y ∈ D.retainedVertices eta R₀) ∧ ¬ D.ActivePair x y)
    (havoid : ∀ x y, T.Adj x y → x ∉ B ∧ y ∉ B)
    (hell : 1 ≤ DenseGraph.matchingNumber T) :
    ∃ M : SubcriticalHomogeneousResidualMatching D eta R₀ T B,
      DenseGraph.matchingNumber T ≤ subcriticalResidualMatchingKappa eta R₀ * M.edges.card := by
  let E := DenseGraph.matchingEdgeFinset (DenseGraph.canonicalMaximumMatching T)
  have hmatch : DenseGraph.IsEdgeMatching T E :=
    DenseGraph.matchingEdgeFinset_isEdgeMatching (DenseGraph.canonicalMaximumMatching_isMatching T)
  have hcard : E.card = DenseGraph.matchingNumber T := by simp [E]
  have hne : E.Nonempty := Finset.card_pos.mp (by omega)
  have hplace (e : {e // e ∈ E}) :
      ∃ c : SubcriticalResidualMatchingPlacement D eta R₀, c.Contains e.val := by
    have ht := hmatch.1 e.val e.property
    induction heq : e.val using Sym2.ind with
    | _ x y =>
      rw [heq, SimpleGraph.mem_edgeSet] at ht
      exact subcriticalResidualMatchingPlacement_exists (hallowed x y ht).1 (hallowed x y ht).2
  let f : {e // e ∈ E} → SubcriticalResidualMatchingPlacement D eta R₀ :=
    fun e ↦ Classical.choose (hplace e)
  obtain ⟨e0, he0⟩ := hne
  letI : Nonempty (SubcriticalResidualMatchingPlacement D eta R₀) := ⟨f ⟨e0, he0⟩⟩
  let fiber (c : SubcriticalResidualMatchingPlacement D eta R₀) :=
    Finset.univ.filter fun e ↦ f e = c
  obtain ⟨c, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun c ↦ (fiber c).card)
    Finset.univ_nonempty
  have hsum : E.card = ∑ c : SubcriticalResidualMatchingPlacement D eta R₀, (fiber c).card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using
      (Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
        (fun e _ ↦ Finset.mem_univ (f e)))
  have hc : E.card ≤ subcriticalResidualMatchingKappa eta R₀ * (fiber c).card := by
    calc
      E.card = ∑ b : SubcriticalResidualMatchingPlacement D eta R₀, (fiber b).card := hsum
      _ ≤ ∑ _b : SubcriticalResidualMatchingPlacement D eta R₀, (fiber c).card :=
        Finset.sum_le_sum (fun b hb ↦ hmax b hb)
      _ = Fintype.card (SubcriticalResidualMatchingPlacement D eta R₀) * (fiber c).card := by simp
      _ ≤ _ := Nat.mul_le_mul_right _
        (SubcriticalResidualMatchingPlacement.card_le_kappa heta heta1 hR)
  let F := (fiber c).image Subtype.val
  have hFE : F ⊆ E := by
    intro e he
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp he
    exact f.property
  have hFc : F.card = (fiber c).card := Finset.card_image_of_injective _ Subtype.val_injective
  refine ⟨⟨c, F, hmatch.mono hFE, ?_, ?_⟩, ?_⟩
  · intro e he
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp he
    have hfc : f f' = c := (Finset.mem_filter.mp hf').2
    exact hfc ▸ Classical.choose_spec (hplace f')
  · intro e he x hx
    have ht := hmatch.1 e (hFE he)
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at ht
      have ha := (havoid a b ht).1
      have hb := (havoid a b ht).2
      rcases Sym2.mem_iff.mp hx with hxa | hxb
      · simpa only [hxa] using ha
      · simpa only [hxb] using hb
  · change DenseGraph.matchingNumber T ≤ subcriticalResidualMatchingKappa eta R₀ * F.card
    rwa [hFc, ← hcard]

/-- The realized residual graph supplies the geometric and root-avoidance
hypotheses of the finite maximum-matching selector. -/
theorem RealizesSubcriticalProfile.exists_homogeneousResidualMatching
    {G : SimpleGraph V} {theta alpha : ℝ} {p : SubcriticalProfile D eta R₀ theta}
    (hp : RealizesSubcriticalProfile G alpha p)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hR : 1 ≤ R₀) (hell : 1 ≤ p.ell) :
    ∃ M : SubcriticalHomogeneousResidualMatching D eta R₀
        (subcriticalResidualDefectGraph G D eta R₀ theta alpha) p.roots,
      p.ell ≤ subcriticalResidualMatchingKappa eta R₀ * M.edges.card := by
  obtain ⟨M, hM⟩ := exists_subcriticalHomogeneousResidualMatching
    (subcriticalResidualDefectGraph G D eta R₀ theta alpha) p.roots heta heta1 hR
    (fun x y h ↦ ⟨h.1.2, subcriticalResidual_no_active h⟩)
    (fun x y h ↦ by simpa only [hp.roots_eq] using h.2)
    (by simpa only [hp.matching] using hell)
  exact ⟨M, by simpa only [hp.matching] using hM⟩

/-- The exact paper thinning size, with its ceiling left visible. -/
def subcriticalResidualMatchingThinSize (eta : ℝ) (R₀ q : ℕ) : ℕ :=
  Nat.ceil (subcriticalResidualMatchingLambda eta R₀ * q / 8)

theorem subcriticalResidualMatchingThinSize_le {eta : ℝ} {R₀ : ℕ}
    (heta1 : eta ≤ 1) (hR : 1 ≤ R₀) (q : ℕ) :
    subcriticalResidualMatchingThinSize eta R₀ q ≤ q := by
  apply Nat.ceil_le.mpr
  have h := mul_le_mul_of_nonneg_right
    (subcriticalResidualMatchingLambda_le_quarter heta1 hR) (Nat.cast_nonneg q)
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  linarith

/-- A ceiling is absorbed by the explicit reserve `16 ≤ lambda*n`.
The factor two is the exact endpoint count of a matching. -/
theorem subcriticalResidualMatchingThinSize_le_scale {eta : ℝ} {R₀ n q : ℕ}
    (heta : 0 < eta) (hR : 1 ≤ R₀) (hqn : 2 * q ≤ n)
    (hn : 16 ≤ subcriticalResidualMatchingLambda eta R₀ * n) :
    (subcriticalResidualMatchingThinSize eta R₀ q : ℝ) ≤
      subcriticalResidualMatchingLambda eta R₀ * n / 8 := by
  have hl := subcriticalResidualMatchingLambda_pos heta hR
  have hc := Nat.ceil_lt_add_one (show 0 ≤ subcriticalResidualMatchingLambda eta R₀ * q / 8 by
    positivity)
  have hqR : 2 * (q : ℝ) ≤ n := by exact_mod_cast hqn
  have hm := mul_le_mul_of_nonneg_left hqR hl.le
  change (subcriticalResidualMatchingThinSize eta R₀ q : ℝ) < _ at hc
  linarith

/-- The selected submatching has exactly the prescribed ceiling,
retains its placement and avoids the same roots. Both final size bounds
are quantitative, including the ceiling's order threshold. -/
theorem SubcriticalHomogeneousResidualMatching.exists_thin
    {T : SimpleGraph V} {B : Finset V}
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hR : 1 ≤ R₀)
    (ell : ℕ) (hell : ell ≤ subcriticalResidualMatchingKappa eta R₀ * M.edges.card)
    (hn : 16 ≤ subcriticalResidualMatchingLambda eta R₀ * Fintype.card V) :
    ∃ M' : SubcriticalHomogeneousResidualMatching D eta R₀ T B,
      M'.placement = M.placement ∧ M'.edges ⊆ M.edges ∧
      M'.edges.card = subcriticalResidualMatchingThinSize eta R₀ M.edges.card ∧
      subcriticalResidualMatchingLambda eta R₀ * ell /
        (8 * (subcriticalResidualMatchingKappa eta R₀ : ℝ)) ≤ (M'.edges.card : ℝ) ∧
      (M'.edges.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * Fintype.card V / 8 := by
  obtain ⟨E, hE, hc⟩ := Finset.exists_subset_card_eq
    (subcriticalResidualMatchingThinSize_le heta1 hR M.edges.card)
  let M' : SubcriticalHomogeneousResidualMatching D eta R₀ T B :=
    ⟨M.placement, E, M.isMatching.mono hE,
      fun e he ↦ M.samePlacement e (hE he), fun e he ↦ M.avoids e (hE he)⟩
  refine ⟨M', rfl, hE, hc, ?_, ?_⟩
  · change subcriticalResidualMatchingLambda eta R₀ * ell /
      (8 * (subcriticalResidualMatchingKappa eta R₀ : ℝ)) ≤ (E.card : ℝ)
    rw [hc]
    have hl := subcriticalResidualMatchingLambda_pos heta hR
    have hk : (0 : ℝ) < subcriticalResidualMatchingKappa eta R₀ := by
      exact_mod_cast (show 0 < subcriticalResidualMatchingKappa eta R₀ from
        lt_of_lt_of_le (by omega) (subcriticalResidualMatchingKappa_pos heta hR))
    have hbound : (ell : ℝ) ≤ (subcriticalResidualMatchingKappa eta R₀ : ℝ) * M.edges.card :=
      by exact_mod_cast hell
    have hmul := mul_le_mul_of_nonneg_left hbound hl.le
    have hratio : subcriticalResidualMatchingLambda eta R₀ * ell /
        (8 * (subcriticalResidualMatchingKappa eta R₀ : ℝ)) ≤
      subcriticalResidualMatchingLambda eta R₀ * M.edges.card / 8 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [hmul]
    exact hratio.trans (Nat.le_ceil _)
  · change (E.card : ℝ) ≤ _
    rw [hc]
    exact subcriticalResidualMatchingThinSize_le_scale heta hR M.two_mul_card_le hn

/-- Uniform retained-part room after deleting both roots and all matching
endpoints. The factor-two retained lower bound pays for both deletions. -/
theorem subcriticalResidualMatching_part_room
    {n : ℕ} {D : SubcriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)} {B : Finset (Fin n)}
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ T B)
    (heta : 0 < eta) (hR : 1 ≤ R₀)
    (hpart : ∀ a ∈ D.retainedPartIndices eta R₀,
      eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ))
    (hB : (B.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 2)
    (hsmall : (M.edges.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 8)
    (a : D.PartIndex) (ha : a ∈ D.retainedPartIndices eta R₀) :
    subcriticalResidualMatchingLambda eta R₀ * n ≤
      ((D.part a \ (B ∪ DenseGraph.matchingEndpoints M.edges)).card : ℝ) := by
  have hl := subcriticalResidualMatchingLambda_pos heta hR
  have hcount : ((D.part a).card : ℝ) ≤
      (D.part a \ (B ∪ DenseGraph.matchingEndpoints M.edges)).card +
        (B ∪ DenseGraph.matchingEndpoints M.edges).card := by
    exact_mod_cast Finset.card_le_card_sdiff_add_card
      (s := D.part a) (t := B ∪ DenseGraph.matchingEndpoints M.edges)
  have hu : ((B ∪ DenseGraph.matchingEndpoints M.edges).card : ℝ) ≤
      B.card + 2 * M.edges.card := by
    exact_mod_cast (Finset.card_union_le B (DenseGraph.matchingEndpoints M.edges)).trans
      (by rw [M.endpoints_card])
  have hs := hpart a ha
  have he : eta * n / (2 * (R₀ : ℝ)) = 2 * subcriticalResidualMatchingLambda eta R₀ * n := by
    unfold subcriticalResidualMatchingLambda
    ring
  rw [he] at hs
  have hn : 0 ≤ subcriticalResidualMatchingLambda eta R₀ * n := by positivity
  linarith

end InducedStars
