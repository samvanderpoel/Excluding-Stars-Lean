import InducedStars.Regularity.Basic
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma

/-!
# Uniform refinements of finite partitions

This file records the refinement bookkeeping needed to run Mathlib's
Szemerédi-regularity energy increment from a prescribed initial
equipartition.  A uniform refinement has the same number of children below
each parent part.
-/

open Finset Fintype Function

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- `Q.UniformRefines P r` means that `Q` refines `P` and that every part of
`P` contains exactly `r` parts of `Q`. -/
structure UniformRefines (Q P : _root_.Finpartition s) (r : ℕ) : Prop where
  le : Q ≤ P
  card_parts_subset :
    ∀ U ∈ P.parts, #{A ∈ Q.parts | A ⊆ U} = r

/-- Every finite partition uniformly refines itself with factor one. -/
theorem uniformRefines_refl (P : _root_.Finpartition s) : P.UniformRefines P 1 := by
  refine ⟨le_rfl, fun U hU => ?_⟩
  have hfilter : {A ∈ P.parts | A ⊆ U} = {U} := by
    ext A
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hA, hAU⟩
      exact P.disjoint.eq_of_le hA hU (P.ne_bot hA) hAU
    · rintro rfl
      exact ⟨hU, Subset.rfl⟩
  rw [hfilter, card_singleton]

/-- Binding equally large subpartitions below the parts of `P` gives a
uniform refinement of `P`. -/
theorem uniformRefines_bind (P : _root_.Finpartition s)
    (R : ∀ U ∈ P.parts, _root_.Finpartition U) (r : ℕ)
    (hR : ∀ U hU, #(R U hU).parts = r) :
    (P.bind R).UniformRefines P r := by
  refine ⟨?_, fun U hU => ?_⟩
  · intro A hA
    obtain ⟨V, hV, hA⟩ := _root_.Finpartition.mem_bind.mp hA
    exact ⟨V, hV, (R V hV).le hA⟩
  · have hfilter : {A ∈ (P.bind R).parts | A ⊆ U} = (R U hU).parts := by
      ext A
      simp only [mem_filter]
      constructor
      · rintro ⟨hAbind, hAU⟩
        obtain ⟨V, hV, hAV⟩ := _root_.Finpartition.mem_bind.mp hAbind
        obtain ⟨x, hxA⟩ := (R V hV).nonempty_of_mem_parts hAV
        have hVU : V = U := P.eq_of_mem_parts hV hU ((R V hV).le hAV hxA) (hAU hxA)
        subst V
        simpa using hAV
      · intro hA
        exact ⟨_root_.Finpartition.mem_bind.mpr ⟨U, hU, hA⟩, (R U hU).le hA⟩
    rw [hfilter, hR U hU]

/-- Uniform refinements compose, and their factors multiply. -/
theorem UniformRefines.trans {Q P R : _root_.Finpartition s} {r q : ℕ}
    (hQP : Q.UniformRefines P r) (hPR : P.UniformRefines R q) :
    Q.UniformRefines R (r * q) := by
  refine ⟨hQP.le.trans hPR.le, fun U hU => ?_⟩
  let parents := {V ∈ P.parts | V ⊆ U}
  let children := fun V : Finset α => {A ∈ Q.parts | A ⊆ V}
  have hunion : {A ∈ Q.parts | A ⊆ U} = parents.biUnion children := by
    ext A
    rw [mem_filter, mem_biUnion]
    constructor
    · rintro ⟨hAQ, hAU⟩
      obtain ⟨V, hVP, hAV⟩ := hQP.le hAQ
      obtain ⟨W, hWR, hVW⟩ := hPR.le hVP
      obtain ⟨x, hxA⟩ := Q.nonempty_of_mem_parts hAQ
      have hWU : W = U := R.eq_of_mem_parts hWR hU (hVW (hAV hxA)) (hAU hxA)
      subst W
      exact ⟨V, mem_filter.mpr ⟨hVP, hVW⟩, mem_filter.mpr ⟨hAQ, hAV⟩⟩
    · rintro ⟨V, hVP, hAV⟩
      obtain ⟨hVP, hVU⟩ := mem_filter.mp hVP
      obtain ⟨hAQ, hAV⟩ := mem_filter.mp hAV
      exact ⟨hAQ, hAV.trans hVU⟩
  rw [hunion, card_biUnion]
  · calc
      ∑ V ∈ parents, #(children V) = ∑ _V ∈ parents, r := by
        apply Finset.sum_congr rfl
        intro V hV
        dsimp only [children]
        exact hQP.card_parts_subset V (mem_filter.mp hV).1
      _ = #parents * r := by simp
      _ = q * r := by rw [show #parents = q by simpa [parents] using hPR.card_parts_subset U hU]
      _ = r * q := Nat.mul_comm q r
  · intro V hV W hW hVW
    rw [Function.onFun, Finset.disjoint_left]
    intro A hAV hAW
    simp only [children, mem_filter] at hAV hAW
    obtain ⟨x, hxA⟩ := Q.nonempty_of_mem_parts hAV.1
    exact hVW (P.eq_of_mem_parts (mem_filter.mp hV).1 (mem_filter.mp hW).1
      (hAV.2 hxA) (hAW.2 hxA))

end Finpartition

/-! ### The Mathlib increment as a uniform refinement -/

namespace InducedStars.Regularity

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Each part of a Mathlib regularity increment has exactly
`4 ^ #P.parts` children. -/
theorem increment_uniformRefines
    {P : _root_.Finpartition (univ : Finset α)}
    (hP : P.IsEquipartition) (G : SimpleGraph α) [DecidableRel G.Adj]
    (ε : ℝ) (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPG : ¬P.IsUniform G ε) :
    (SzemerediRegularity.increment hP G ε).UniformRefines P (4 ^ #P.parts) := by
  obtain ⟨U, hU⟩ := P.nonempty_of_not_uniform hPG
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hU
  let : Nonempty α := ⟨x⟩
  simpa only [SzemerediRegularity.increment] using
    Finpartition.uniformRefines_bind P
      (fun U hU => SzemerediRegularity.chunk hP G ε hU) (4 ^ #P.parts)
      (fun U hU => SzemerediRegularity.card_chunk
        (SzemerediRegularity.m_pos hPα).ne')

/-! ### Regularity from a prescribed equipartition -/

/-- An ambient-cardinality and final-part-count bound for the regularity
energy iteration started from at most `K` parts. -/
noncomputable def uniformRefinementBound (ε : ℝ) (K : ℕ) : ℕ :=
  let S := SzemerediRegularity.stepBound^[⌊4 / ε ^ 5⌋₊] K
  S * 16 ^ S

theorem le_uniformRefinementBound (ε : ℝ) (K : ℕ) :
    K ≤ uniformRefinementBound ε K :=
  (id_le_iterate_of_id_le SzemerediRegularity.le_stepBound _ _).trans <|
    Nat.le_mul_of_pos_right _ (by positivity)

theorem uniformRefinementBound_pos (ε : ℝ) {K : ℕ} (hK : 0 < K) :
    0 < uniformRefinementBound ε K :=
  hK.trans_le (le_uniformRefinementBound ε K)

/-- Szemerédi regularity, starting from a prescribed equipartition.

The final partition uniformly refines the prescribed partition.  The ambient
cardinality and the final number of parts are both controlled by
`uniformRefinementBound ε K`, where `K` is any upper bound for the number of
initial parts. -/
theorem exists_uniform_equipartition_uniformRefines
    (G : SimpleGraph α) [DecidableRel G.Adj] (ε : ℝ) (K : ℕ)
    (P₀ : _root_.Finpartition (univ : Finset α))
    (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hP₀ : P₀.IsEquipartition)
    (hP₀seven : 7 ≤ #P₀.parts)
    (hP₀ε : 100 ≤ (4 : ℝ) ^ #P₀.parts * ε ^ 5)
    (hP₀K : #P₀.parts ≤ K)
    (hα : uniformRefinementBound ε K ≤ card α) :
    ∃ (Q : _root_.Finpartition (univ : Finset α)) (r : ℕ),
      Q.IsEquipartition ∧ 0 < r ∧ Q.UniformRefines P₀ r ∧
        #Q.parts ≤ uniformRefinementBound ε K ∧ Q.IsUniform G ε := by
  have hparts : P₀.parts.Nonempty := card_pos.mp (by omega : 0 < #P₀.parts)
  obtain ⟨U, hU⟩ := hparts
  obtain ⟨x, hx⟩ := P₀.nonempty_of_mem_parts hU
  let : Nonempty α := ⟨x⟩
  suffices h : ∀ i, ∃ (Q : _root_.Finpartition (univ : Finset α)) (r : ℕ),
      Q.IsEquipartition ∧ 0 < r ∧ Q.UniformRefines P₀ r ∧
        #Q.parts ≤ SzemerediRegularity.stepBound^[i] K ∧
          (Q.IsUniform G ε ∨ ε ^ 5 / 4 * i ≤ Q.energy G) by
    obtain ⟨Q, r, hQequip, hr, hQref, hQcard, hQstate⟩ :=
      h (⌊4 / ε ^ 5⌋₊ + 1)
    refine ⟨Q, r, hQequip, hr, hQref, hQcard.trans ?_,
      hQstate.resolve_right fun hQenergy => lt_irrefl (1 : ℝ) ?_⟩
    · rw [iterate_succ_apply', SzemerediRegularity.stepBound, uniformRefinementBound]
      gcongr
      simp
    calc
      (1 : ℝ) = ε ^ 5 / ↑4 * (↑4 / ε ^ 5) := by
        rw [mul_comm, div_mul_div_cancel₀ (pow_pos hε 5).ne']
        simp
      _ < ε ^ 5 / 4 * (⌊4 / ε ^ 5⌋₊ + 1) := by
        gcongr
        exact Nat.lt_floor_add_one _
      _ ≤ (Q.energy G : ℝ) := by rwa [← Nat.cast_add_one]
      _ ≤ 1 := mod_cast Q.energy_le_one G
  intro i
  induction i with
  | zero =>
      refine ⟨P₀, 1, hP₀, Nat.zero_lt_succ 0,
        Finpartition.uniformRefines_refl P₀, ?_, Or.inr ?_⟩
      · simpa using hP₀K
      · rw [Nat.cast_zero, mul_zero]
        exact_mod_cast P₀.energy_nonneg G
  | succ i ih =>
      obtain ⟨Q, r, hQequip, hr, hQref, hQcard, hQstate⟩ := ih
      by_cases huniform : Q.IsUniform G ε
      · refine ⟨Q, r, hQequip, hr, hQref, ?_, Or.inl huniform⟩
        rw [iterate_succ_apply']
        exact hQcard.trans (SzemerediRegularity.le_stepBound _)
      replace hQstate := hQstate.resolve_left huniform
      have hP₀Q : #P₀.parts ≤ #Q.parts := _root_.Finpartition.card_mono hQref.le
      have hQε : 100 ≤ (4 : ℝ) ^ #Q.parts * ε ^ 5 :=
        hP₀ε.trans <| mul_le_mul_of_nonneg_right
          (pow_right_mono₀ (by simp) hP₀Q) (by positivity)
      have hi : (i : ℝ) ≤ 4 / ε ^ 5 := by
        have hi : ε ^ 5 / 4 * (i : ℝ) ≤ 1 :=
          hQstate.trans (mod_cast Q.energy_le_one G)
        rw [div_mul_eq_mul_div, div_le_iff₀ (show (0 : ℝ) < 4 by simp)] at hi
        norm_num at hi
        rwa [le_div_iff₀' (pow_pos hε _)]
      have hsize : #Q.parts ≤
          SzemerediRegularity.stepBound^[⌊4 / ε ^ 5⌋₊] K :=
        hQcard.trans <| monotone_iterate_of_id_le SzemerediRegularity.le_stepBound
          (Nat.le_floor hi) _
      have hQα : #Q.parts * 16 ^ #Q.parts ≤ card α :=
        (Nat.mul_le_mul hsize (Nat.pow_le_pow_right (by simp) hsize)).trans <| by
          simpa only [uniformRefinementBound] using hα
      have hIncRef := increment_uniformRefines hQequip G ε hQα huniform
      refine ⟨SzemerediRegularity.increment hQequip G ε,
        4 ^ #Q.parts * r,
        SzemerediRegularity.increment_isEquipartition hQequip G ε,
        Nat.mul_pos (by positivity) hr,
        hIncRef.trans hQref, ?_, Or.inr <| le_trans ?_ <|
          SzemerediRegularity.energy_increment hQequip
            (hP₀seven.trans hP₀Q) hQε hQα huniform hε.le hε₁⟩
      · rw [SzemerediRegularity.card_increment hQα huniform, iterate_succ_apply']
        exact SzemerediRegularity.stepBound_mono hQcard
      · rw [Nat.cast_succ, mul_add, mul_one]
        gcongr

end InducedStars.Regularity
