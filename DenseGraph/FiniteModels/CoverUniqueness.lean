import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

/-!
# Finite covering and fixed-cardinality containment

This file contains project-independent finite counting facts used to prove
uniqueness of multipartite clique covers.  In particular, containment in a
uniform fixed-cardinality subset is counted exactly and bounded without any
probabilistic axiom.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DenseGraph

variable {Omega : Type*} [Fintype Omega] [DecidableEq Omega]

/-- The `L`-subsets of `U` which contain every coordinate in `F`. -/
def fixedCardinalityContainingFinset
    (U F : Finset Omega) (L : Nat) : Finset (Finset Omega) :=
  (U.powersetCard L).filter (F ⊆ ·)

@[simp] theorem mem_fixedCardinalityContainingFinset
    {U F S : Finset Omega} {L : Nat} :
    S ∈ fixedCardinalityContainingFinset U F L ↔
      S ⊆ U ∧ S.card = L ∧ F ⊆ S := by
  simp [fixedCardinalityContainingFinset, and_assoc]

/-- Exact hypergeometric containment count. -/
theorem card_fixedCardinalityContainingFinset
    {U F : Finset Omega} {L : Nat} (hFU : F ⊆ U) (hFL : F.card ≤ L) :
    (fixedCardinalityContainingFinset U F L).card =
      Nat.choose (U.card - F.card) (L - F.card) := by
  exact Finset.card_filter_powersetCard_subset F U L hFU hFL

/-- The containment family is empty if more forced coordinates are requested
than the sample cardinality. -/
theorem fixedCardinalityContainingFinset_eq_empty_of_lt
    {U F : Finset Omega} {L : Nat} (hLF : L < F.card) :
    fixedCardinalityContainingFinset U F L = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨_, hSL, hFS⟩ := mem_fixedCardinalityContainingFinset.mp hS
  exact (not_le_of_gt hLF) ((Finset.card_le_card hFS).trans_eq hSL)

/-- The uniform fixed-cardinality probability that the selected subset
contains `F`.  Division is totalized, as usual in Lean; later theorems supply
the hypotheses which make the denominator positive. -/
def fixedCardinalityContainmentProbability
    (U F : Finset Omega) (L : Nat) : Real :=
  ((fixedCardinalityContainingFinset U F L).card : Real) /
    (Nat.choose U.card L : Real)

/-- Exact fixed-cardinality containment probability in the feasible range. -/
theorem fixedCardinalityContainmentProbability_eq
    {U F : Finset Omega} {L : Nat}
    (hFU : F ⊆ U) (hFL : F.card ≤ L) :
    fixedCardinalityContainmentProbability U F L =
      (Nat.choose (U.card - F.card) (L - F.card) : Real) /
        (Nat.choose U.card L : Real) := by
  simp only [fixedCardinalityContainmentProbability,
    card_fixedCardinalityContainingFinset hFU hFL]

theorem fixedCardinalityContainmentProbability_eq_zero_of_lt
    {U F : Finset Omega} {L : Nat} (hLF : L < F.card) :
    fixedCardinalityContainmentProbability U F L = 0 := by
  simp [fixedCardinalityContainmentProbability,
    fixedCardinalityContainingFinset_eq_empty_of_lt hLF]

/-! The next two elementary lemmas prove the density-power estimate.  Writing
binomial ratios as descending-factorial ratios avoids importing any
probabilistic inequality. -/

private theorem descFactorial_ratio_le_density_pow
    {N L q : Nat} (hLN : L ≤ N) (hqL : q ≤ L) (hN : 0 < N) :
    (L.descFactorial q : Real) / (N.descFactorial q : Real) ≤
      ((L : Real) / (N : Real)) ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hqL' : q ≤ L := Nat.le_trans (Nat.le_succ q) hqL
      have hqN' : q ≤ N := hqL'.trans hLN
      have hqLtN : q < N := lt_of_lt_of_le (Nat.lt_succ_self q) hqL |>.trans_le hLN
      have hNq : 0 < (N - q : Real) := by
        exact_mod_cast Nat.sub_pos_of_lt hqLtN
      have hNr : 0 < (N : Real) := by exact_mod_cast hN
      have hfactor :
          ((L - q : Nat) : Real) / ((N - q : Nat) : Real) ≤
            (L : Real) / (N : Real) := by
        rw [Nat.cast_sub hqL', Nat.cast_sub hqN']
        rw [div_le_div_iff₀ hNq hNr]
        have hLNreal : (L : Real) ≤ N := by exact_mod_cast hLN
        nlinarith
      have hden : (N.descFactorial q : Real) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hqN'))
      calc
        (L.descFactorial (q + 1) : Real) /
              (N.descFactorial (q + 1) : Real) =
            (((L - q : Nat) : Real) / ((N - q : Nat) : Real)) *
              ((L.descFactorial q : Real) / (N.descFactorial q : Real)) := by
                simp only [Nat.descFactorial_succ, Nat.cast_mul]
                field_simp
                <;> ring
        _ ≤ ((L : Real) / (N : Real)) *
              (((L : Real) / (N : Real)) ^ q) := by
                exact mul_le_mul hfactor (ih hqL')
                  (by positivity) (by positivity)
        _ = ((L : Real) / (N : Real)) ^ (q + 1) := by
              rw [pow_succ]
              ring

private theorem choose_ratio_le_density_pow
    {N L q : Nat} (hLN : L ≤ N) (hqL : q ≤ L) (hN : 0 < N) :
    (Nat.choose L q : Real) / (Nat.choose N q : Real) ≤
      ((L : Real) / (N : Real)) ^ q := by
  have hfac : (q.factorial : Real) ≠ 0 := by positivity
  have hdescN : (N.descFactorial q : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr (hqL.trans hLN)))
  calc
    (Nat.choose L q : Real) / (Nat.choose N q : Real) =
        (L.descFactorial q : Real) / (N.descFactorial q : Real) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose,
        Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      field_simp
    _ ≤ ((L : Real) / (N : Real)) ^ q :=
      descFactorial_ratio_le_density_pow hLN hqL hN

/-- A uniform `L`-subset of a nonempty `N`-coordinate universe contains a
fixed `q`-set with probability at most `(L/N)^q`. -/
theorem fixedCardinality_probability_contains_le_density_pow
    {U F : Finset Omega} {L : Nat}
    (hFU : F ⊆ U) (hLN : L ≤ U.card) (hN : 0 < U.card) :
    fixedCardinalityContainmentProbability U F L ≤
      ((L : Real) / (U.card : Real)) ^ F.card := by
  by_cases hFL : F.card ≤ L
  · rw [fixedCardinalityContainmentProbability_eq hFU hFL]
    have hchooseN : (Nat.choose U.card L : Real) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero hLN
    have hchooseQ : (Nat.choose U.card F.card : Real) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero (Finset.card_le_card hFU)
    have hidentity := Nat.choose_mul (n := U.card) (k := L)
      (s := F.card) hFL
    have hratio :
        (Nat.choose (U.card - F.card) (L - F.card) : Real) /
            (Nat.choose U.card L : Real) =
          (Nat.choose L F.card : Real) /
            (Nat.choose U.card F.card : Real) := by
      rw [div_eq_div_iff hchooseN hchooseQ]
      exact_mod_cast (by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hidentity.symm)
    rw [hratio]
    exact choose_ratio_le_density_pow hLN hFL hN
  · rw [fixedCardinalityContainmentProbability_eq_zero_of_lt
      (Nat.lt_of_not_ge hFL)]
    positivity

/-! ## Generic ordered partition assignments -/

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

/-- Number of vertices on which two assignments disagree after relabeling the
first assignment by `sigma`. -/
def assignmentMoveCount (p q : V → I) (sigma : Equiv.Perm I) : Nat :=
  (Finset.univ.filter fun v ↦ q v ≠ sigma (p v)).card

/-- Best assignment disagreement over all label permutations. -/
def assignmentMoveDistance (p q : V → I) : Nat :=
  (Finset.univ.image (assignmentMoveCount p q)).min' (by simp)

theorem assignmentMoveDistance_eq_zero_iff (p q : V → I) :
    assignmentMoveDistance p q = 0 ↔
      ∃ sigma : Equiv.Perm I, q = sigma ∘ p := by
  classical
  constructor
  · intro hzero
    obtain ⟨sigma, hsigma⟩ : ∃ sigma : Equiv.Perm I,
        assignmentMoveCount p q sigma = assignmentMoveDistance p q := by
      simpa [assignmentMoveDistance] using
        Finset.min'_mem (Finset.univ.image (assignmentMoveCount p q)) (by simp)
    refine ⟨sigma, funext fun v ↦ ?_⟩
    have hempty : Finset.univ.filter (fun w ↦ q w ≠ sigma (p w)) = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa [assignmentMoveCount, hzero] using hsigma
    by_contra hv
    change q v ≠ sigma (p v) at hv
    have : v ∈ Finset.univ.filter (fun w ↦ q w ≠ sigma (p w)) := by simp [hv]
    simpa [hempty] using this
  · rintro ⟨sigma, rfl⟩
    have hmem : 0 ∈ Finset.univ.image
        (assignmentMoveCount p (sigma ∘ p)) := by
      refine Finset.mem_image.mpr ⟨sigma, Finset.mem_univ _, ?_⟩
      simp [assignmentMoveCount, Function.comp_apply]
    apply Nat.eq_zero_of_le_zero
    rw [assignmentMoveDistance]
    exact Finset.min'_le _ _ hmem

/-! ## Hamming-sphere counting -/

/-- Functions differing from `p` in exactly `t` coordinates. -/
def assignmentHammingSphere (p : V → I) (t : Nat) : Finset (V → I) :=
  Finset.univ.filter fun q ↦
    (Finset.univ.filter fun v ↦ q v ≠ p v).card = t

@[simp] theorem mem_assignmentHammingSphere
    {p q : V → I} {t : Nat} :
    q ∈ assignmentHammingSphere p t ↔
      (Finset.univ.filter fun v ↦ q v ≠ p v).card = t := by
  simp [assignmentHammingSphere]

/-- A changed-coordinate set together with the new labels on that set. -/
abbrev AssignmentHammingCode (V I : Type*) [Fintype V] [DecidableEq V]
    [Fintype I] (t : Nat) : Type _ :=
  Σ S : {S : Finset V // S ∈ (Finset.univ : Finset V).powersetCard t},
    ({v // v ∈ S.1} → I)

private def assignmentHammingEncode (p : V → I) (t : Nat) :
    {q // q ∈ assignmentHammingSphere p t} →
      AssignmentHammingCode V I t := fun q ↦
  ⟨⟨Finset.univ.filter fun v ↦ q.1 v ≠ p v,
      Finset.mem_powersetCard.mpr
        ⟨Finset.filter_subset _ _, mem_assignmentHammingSphere.mp q.2⟩⟩,
    fun v ↦ q.1 v.1⟩

private def assignmentHammingDecode (p : V → I) (t : Nat) :
    AssignmentHammingCode V I t → (V → I) := fun c v ↦
  if hv : v ∈ c.1.1 then c.2 ⟨v, hv⟩ else p v

private theorem assignmentHammingDecode_encode
    (p : V → I) (t : Nat)
    (q : {q // q ∈ assignmentHammingSphere p t}) :
    assignmentHammingDecode p t (assignmentHammingEncode p t q) = q.1 := by
  funext v
  by_cases hv : q.1 v ≠ p v
  · simp [assignmentHammingDecode, assignmentHammingEncode, hv]
  · simp [assignmentHammingDecode, assignmentHammingEncode, hv]
    exact (not_ne_iff.mp hv).symm

private theorem assignmentHammingEncode_injective
    (p : V → I) (t : Nat) :
    Function.Injective (assignmentHammingEncode p t) := by
  intro q r h
  apply Subtype.ext
  rw [← assignmentHammingDecode_encode p t q,
    ← assignmentHammingDecode_encode p t r, h]

private theorem card_assignmentHammingCode (t : Nat) :
    Fintype.card (AssignmentHammingCode V I t) =
      Nat.choose (Fintype.card V) t * (Fintype.card I) ^ t := by
  classical
  rw [Fintype.card_sigma]
  have hcard : ∀ S :
      {S : Finset V // S ∈ (Finset.univ : Finset V).powersetCard t},
      S.1.card = t := fun S ↦ (Finset.mem_powersetCard.mp S.2).2
  simp_rw [Fintype.card_fun, Fintype.card_coe, hcard]
  simp [Finset.card_powersetCard]

/-- The elementary Hamming-sphere bound used to enumerate nearby ordered
partitions.  (The exact cardinality is smaller by replacing `|I|^t` with
`(|I|-1)^t`; the displayed upper bound is the form needed downstream.) -/
theorem card_assignmentHammingSphere_le
    (p : V → I) (t : Nat) :
    (assignmentHammingSphere p t).card ≤
      Nat.choose (Fintype.card V) t * (Fintype.card I) ^ t := by
  classical
  calc
    (assignmentHammingSphere p t).card =
        Fintype.card {q // q ∈ assignmentHammingSphere p t} := by
          exact (Fintype.card_coe _).symm
    _ ≤ Fintype.card (AssignmentHammingCode V I t) :=
      Fintype.card_le_of_injective (assignmentHammingEncode p t)
        (assignmentHammingEncode_injective p t)
    _ = Nat.choose (Fintype.card V) t * (Fintype.card I) ^ t :=
      card_assignmentHammingCode t

end DenseGraph
