import InducedStars.Structure.Subcritical.RetainedMassScalars
import InducedStars.Structure.Subcritical.Retained

/-!
# Transport of retained candidate lengths to actual division supports

The compatibility injection and its actual size errors suffice for this
finite inequality. No balance of the individual parts is inferred.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Every candidate block above the stronger 2 eta threshold is assigned
to an actually retained component, when delta is at most eta. -/
theorem SubcriticalDivision.CandidateCompatibility.retained_block_matched
    {D : SubcriticalDivision k V} {L : AdmissibleBlockSequence k}
    {eta delta : ℝ} {R₀ : ℕ}
    (C : D.CandidateCompatibility L eta delta R₀)
    (heta : 0 < eta) (hdelta : delta ≤ eta)
    (j : ↥(subcriticalMassRetainedBlockIndices L eta R₀)) :
    ∃ i : {i // i ∈ D.compatibilityComponentIndices eta R₀},
      (C.assignment i).val = j.val ∧ i.val ∈ D.retainedComponentIndices eta R₀ ∧
        L.alpha j.val * Fintype.card V ≤
          (D.componentSupport i.val).card + delta * Fintype.card V := by
  have hj := (mem_subcriticalMassRetainedBlockIndices L heta R₀ j.val).mp j.property
  let a : {j : ℕ // blockIndexActive L.count j} :=
    ⟨j.val, subcriticalMassRetainedBlockIndices_active L heta j.property⟩
  obtain ⟨i, hi⟩ := C.large_smallOrder_block_matched a (by dsimp [a]; linarith) hj.2
  have hij : (C.assignment i).val = j.val := congrArg Subtype.val hi
  have hsize := C.size_error i
  rw [hij] at hsize
  have hlower := (abs_le.mp hsize).1
  have hcore : (D.core i.val).order = (L.core j.val).order := by
    have h := Fintype.card_congr (C.coreIso i).toEquiv
    simpa only [Fintype.card_fin, hij] using h
  refine ⟨i, hij, (D.mem_retainedComponentIndices eta R₀ i.val).mpr ⟨?_, ?_⟩, ?_⟩
  · have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hj.1 hn
    have hd := mul_le_mul_of_nonneg_right hdelta hn
    linarith
  · rw [hcore]
    exact hj.2
  · linarith

/-- Actual compatibility gives the retained-support lower bound with the
entire finite injection error shown explicitly. -/
theorem SubcriticalDivision.CandidateCompatibility.retained_length_mul_card_le
    {D : SubcriticalDivision k V} {L : AdmissibleBlockSequence k}
    {eta delta : ℝ} {R₀ : ℕ}
    (C : D.CandidateCompatibility L eta delta R₀)
    (heta : 0 < eta) (hdelta : delta ≤ eta) :
    subcriticalRetainedBlockLength L eta R₀ * Fintype.card V ≤
      (D.retainedVertices eta R₀).card +
        (subcriticalMassRetainedBlockIndices L eta R₀).card * delta * Fintype.card V := by
  let I := subcriticalMassRetainedBlockIndices L eta R₀
  choose f hf hret hsize using C.retained_block_matched heta hdelta
  have hinj : Function.Injective (fun j : ↥I ↦ (f j).val) := by
    intro i j h
    have hfij : f i = f j := Subtype.ext h
    apply Subtype.ext
    exact (hf i).symm.trans ((congrArg (fun a ↦ (C.assignment a).val) hfij).trans (hf j))
  have hsum : (∑ j : ↥I, ((D.componentSupport (f j).val).card : ℝ)) ≤
      ((D.retainedVertices eta R₀).card : ℝ) := by
    rw [D.card_retainedVertices, Nat.cast_sum]
    apply Finset.sum_le_sum_of_injOn (fun j : ↥I ↦ (f j).val) hinj.injOn
    · intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact hret j
    · intro j _
      exact le_rfl
    · intro i _ _
      positivity
  have hbound := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ↥I)) ↦ hsize j)
  have hsource : (∑ j : ↥I, L.alpha j.val * Fintype.card V) =
      subcriticalRetainedBlockLength L eta R₀ * Fintype.card V := by
    rw [← Finset.sum_mul]
    congr 1
    exact Finset.sum_coe_sort I L.alpha
  rw [hsource, Finset.sum_add_distrib] at hbound
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] at hbound
  dsimp [I] at hsum hbound
  nlinarith

/-- A positive candidate retained-mass gap remains positive after the
compatibility errors, under the explicit delta ≤ eta*gap reserve. -/
theorem SubcriticalDivision.CandidateCompatibility.retained_mass_gap
    {D : SubcriticalDivision k V} {L : AdmissibleBlockSequence k}
    {eta delta mu gap : ℝ} {R₀ : ℕ}
    (C : D.CandidateCompatibility L eta delta R₀)
    (heta : 0 < eta) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ eta)
    (hreserve : delta ≤ eta * gap)
    (hlength : mu + gap ≤ subcriticalRetainedBlockLength L eta R₀) :
    (mu + gap / 2) * Fintype.card V ≤ (D.retainedVertices eta R₀).card := by
  have hmain := C.retained_length_mul_card_le heta hdelta
  have hcard := subcriticalMassRetainedBlockIndices_card_le L heta R₀
  have hcount0 : (0 : ℝ) ≤ (subcriticalMassRetainedBlockIndices L eta R₀).card := Nat.cast_nonneg _
  have herror : (subcriticalMassRetainedBlockIndices L eta R₀).card * delta ≤ gap / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hreserve hcount0
    have hgap0 : 0 ≤ gap := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right hcard hgap0
    nlinarith
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have h3 := mul_le_mul_of_nonneg_right herror hn
  have h4 := mul_le_mul_of_nonneg_right hlength hn
  nlinarith

end InducedStars
