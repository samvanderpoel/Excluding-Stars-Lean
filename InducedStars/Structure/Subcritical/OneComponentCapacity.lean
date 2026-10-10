import InducedStars.Structure.Subcritical.RetainedProfileFunctionals
import InducedStars.Structure.Subcritical.ActiveLevelComparison

/-!
# Exact capacities of a single complete retained core

Finite prerequisites for the feasible-level part-balance argument in
`lemma:sub-combined`. This concerns the actual retained key and
does not impose conditions on a discarded remainder decomposition.
-/

noncomputable section
open Finset Set
open scoped Classical BigOperators
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem oneCompleteCore_same_or_active (hk : 3 ≤ k)
    (D : SubcriticalDivision k V) (hcount : D.componentCount = 1)
    (hcore : ∀ i, D.core i = RegularBlockCore.complete k hk)
    {x y : V} (hx : x ∈ D.support) (hy : y ∈ D.support) :
    D.SamePart x y ∨ D.ActivePair x y := by
  obtain ⟨⟨i, a⟩, hxa⟩ := D.mem_support.mp hx
  obtain ⟨⟨j, b⟩, hyb⟩ := D.mem_support.mp hy
  have hij : i = j := Fin.ext (by have hi := i.isLt; have hj := j.isLt; omega)
  subst j
  by_cases hab : a = b
  · subst b
    exact Or.inl ⟨⟨i, a⟩, hxa, hyb⟩
  · have hgraph : ∀ u v : Fin (D.core i).order, (D.core i).graph.Adj u v ↔ u ≠ v := by
      rw [hcore i]
      intro u v
      rfl
    exact Or.inr ⟨i, a, b, (hgraph a b).2 hab, hxa, hyb⟩

theorem oneCompleteCore_card_partIndex (hk : 3 ≤ k)
    (D : SubcriticalDivision k V) (hcount : D.componentCount = 1)
    (hcore : ∀ i, D.core i = RegularBlockCore.complete k hk) :
    Fintype.card D.PartIndex = k - 1 := by
  change Fintype.card (Σ i : Fin D.componentCount, Fin (D.core i).order) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  simp_rw [hcore, RegularBlockCore.complete_order]
  simp [hcount]

theorem oneCompleteCore_capacity_add (hk : 3 ≤ k)
    (D : SubcriticalDivision k V) (hcount : D.componentCount = 1)
    (hcore : ∀ i, D.core i = RegularBlockCore.complete k hk) :
    retainedCliqueCapacity D 0 (Fintype.card V) +
      retainedActiveTotalCapacity D 0 (Fintype.card V) = D.support.card.choose 2 := by
  have heq : retainedCliquePotentialEdges D 0 (Fintype.card V) ∪
      retainedActiveEdgeUniverse D 0 (Fintype.card V) =
      D.support.offDiag.image Sym2.mk.uncurry := by
    ext z
    induction z using Sym2.inductionOn with
    | _ x y =>
      rw [Finset.mem_union, mk_mem_retainedCliquePotentialEdges_iff,
        mk_mem_retainedActiveEdgeUniverse_iff, D.retainedVertices_all]
      constructor
      · intro h
        have hs : x ∈ D.support ∧ y ∈ D.support ∧ x ≠ y := by
          rcases h with h | h
          · exact ⟨h.2.2, (SubcriticalDivision.samePart_imp_support h.2.1).2, h.1⟩
          · refine ⟨h.2, (SubcriticalDivision.activePair_imp_support h.1).2, ?_⟩
            intro he
            subst y
            exact D.not_activePair_self x h.1
        exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr hs, rfl⟩
      · intro h
        obtain ⟨⟨u, v⟩, huv, he⟩ := Finset.mem_image.mp h
        have hs := Finset.mem_offDiag.mp huv
        have hsxy : x ∈ D.support ∧ y ∈ D.support ∧ x ≠ y := by
          change s(u, v) = s(x, y) at he
          rcases (Sym2.mk_eq_mk_iff (p := (u, v)) (q := (x, y))).mp he with he | he
          · have hux : u = x := congrArg Prod.fst he
            have hvy : v = y := congrArg Prod.snd he
            simpa [hux, hvy] using hs
          · have huy : u = y := congrArg Prod.fst he
            have hvx : v = x := congrArg Prod.snd he
            exact ⟨hvx ▸ hs.2.1, huy ▸ hs.1, fun hxy ↦ hs.2.2 (by simpa [huy, hvx] using hxy.symm)⟩
        rcases oneCompleteCore_same_or_active hk D hcount hcore hsxy.1 hsxy.2.1 with h | h
        · exact Or.inl ⟨hsxy.2.2, h, hsxy.1⟩
        · exact Or.inr ⟨h, hsxy.1⟩
  have hc := congrArg Finset.card heq
  rw [Finset.card_union_of_disjoint (retainedCliquePotentialEdges_disjoint_active D _ _),
    retainedCliquePotentialEdges_card, ← retainedActiveTotalCapacity_eq_card,
    Sym2.card_image_offDiag] at hc
  exact hc

/-- The exact variance is the excess internal capacity, including the
finite diagonal term. No divisibility or equal-part assumption is used. -/
theorem oneCompleteCore_variance_identity (hk : 3 ≤ k)
    (D : SubcriticalDivision k V) (hcount : D.componentCount = 1)
    (hcore : ∀ i, D.core i = RegularBlockCore.complete k hk) :
    (1 - pK k) * (∑ a : D.PartIndex,
      (((D.part a).card : ℝ) - D.support.card / (k - 1 : ℕ)) ^ 2) =
      2 * ((retainedCliqueCapacity D 0 (Fintype.card V) : ℝ) +
        pK k * retainedActiveTotalCapacity D 0 (Fintype.card V)) +
        D.support.card - gammaK k * (D.support.card : ℝ) ^ 2 := by
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hsum : (∑ a : D.PartIndex, ((D.part a).card : ℝ)) = D.support.card := by
    rw [D.card_support, Nat.cast_sum]
  have hsq := retainedCliqueCapacity_all_square_identity D
  have hnum : (Fintype.card D.PartIndex : ℝ) = (k - 1 : ℕ) := by
    exact_mod_cast oneCompleteCore_card_partIndex hk D hcount hcore
  have hvar : (∑ a : D.PartIndex,
      (((D.part a).card : ℝ) - D.support.card / (k - 1 : ℕ)) ^ 2) =
      2 * (retainedCliqueCapacity D 0 (Fintype.card V) : ℝ) + D.support.card -
        (D.support.card : ℝ)^2 / (k - 1 : ℕ) := by
    calc
      _ = (∑ a : D.PartIndex, ((D.part a).card : ℝ)^2) -
          2 * (D.support.card / (k - 1 : ℕ) : ℝ) * (∑ a : D.PartIndex, ((D.part a).card : ℝ)) +
          (Fintype.card D.PartIndex : ℝ) * (D.support.card / (k - 1 : ℕ) : ℝ)^2 := by
        calc
          _ = ∑ a : D.PartIndex, (((D.part a).card : ℝ)^2 -
              2 * (D.support.card / (k - 1 : ℕ) : ℝ) * (D.part a).card +
              (D.support.card / (k - 1 : ℕ) : ℝ)^2) := by
            apply Finset.sum_congr rfl
            intro a _
            ring
          _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
            simp
      _ = _ := by rw [hnum, hsum, hsq]; field_simp; ring
  have hcap : (retainedCliqueCapacity D 0 (Fintype.card V) : ℝ) +
      retainedActiveTotalCapacity D 0 (Fintype.card V) =
      (D.support.card : ℝ) * (D.support.card - 1) / 2 := by
    have h := congrArg (Nat.cast (R := ℝ)) (oneCompleteCore_capacity_add hk D hcount hcore)
    simpa only [Nat.cast_add, Nat.cast_choose_two] using h
  have hg := gammaK_mul_denominator k hk
  have hrsub : ((k - 2 : ℕ) : ℝ) = (k - 1 : ℕ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : 2 ≤ k)]
    ring
  rw [hrsub] at hg
  have hgmul := congrArg (fun x : ℝ ↦ x * (D.support.card : ℝ)^2) hg
  have hcmul := congrArg (fun x : ℝ ↦ x * 2 * (k - 1 : ℕ) * pK k) hcap
  rw [hvar]
  field_simp
  nlinarith [hgmul, hcmul]

end InducedStars
