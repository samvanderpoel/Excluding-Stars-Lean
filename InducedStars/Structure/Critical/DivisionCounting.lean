import InducedStars.Structure.Critical.CapacityBookkeeping
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
# Counting supercritical divisions with prescribed sparse size

A division with `s` sparse vertices is encoded by choosing that sparse set
and assigning one of the `k-1` main-part labels to every remaining vertex.
Dropping the requirement that every label occur gives the sharp elementary
upper bound `choose n s * (k-1)^(n-s)`.
-/

noncomputable section

open Filter Finset Set

namespace InducedStars

/-! ## The fixed-sparse-size family -/

/-- Supercritical divisions on `Fin n` whose sparse set has cardinality
exactly `s`. -/
noncomputable def supercriticalDivisionsWithSparseCard
    (k n s : ℕ) : Finset (SupercriticalDivision k (Fin n)) :=
  (allSupercriticalDivisions k n).filter fun D ↦ D.sparse.card = s

@[simp] theorem mem_supercriticalDivisionsWithSparseCard
    {k n s : ℕ} {D : SupercriticalDivision k (Fin n)} :
    D ∈ supercriticalDivisionsWithSparseCard k n s ↔
      D.sparse.card = s := by
  classical
  simp [supercriticalDivisionsWithSparseCard]

/-! ## Sparse assignments and their compressed codes -/

/-- Assignments with exactly `s` vertices carrying the sparse label `none`. -/
abbrev SupercriticalSparseAssignment (r n s : ℕ) :=
  {a : Fin n → Option (Fin r) //
    ((Finset.univ : Finset (Fin n)).filter fun v ↦ a v = none).card = s}

/-- A compressed assignment consists of its sparse set and labels only on
the complementary subtype. -/
abbrev SupercriticalSparseLabelingCode (r n s : ℕ) :=
  Σ S : {S : Finset (Fin n) // S.card = s},
    ({v : Fin n // v ∉ S.1} → Fin r)

/-- Compress an exact-sparse assignment by deleting its `none` entries. -/
noncomputable def supercriticalSparseAssignmentCode
    {r n s : ℕ} (a : SupercriticalSparseAssignment r n s) :
    SupercriticalSparseLabelingCode r n s := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun v ↦ a.1 v = none
  refine ⟨⟨S, a.2⟩, fun v ↦ ?_⟩
  have ha : a.1 v.1 ≠ none := by
    intro hnone
    exact v.2 (by simp [S, hnone])
  exact (a.1 v.1).get (Option.isSome_iff_ne_none.mpr ha)

/-- Expand a sparse-set/label code to an option-valued assignment. -/
def supercriticalSparseAssignmentDecode
    {r n s : ℕ} (c : SupercriticalSparseLabelingCode r n s) :
    Fin n → Option (Fin r) := fun v ↦
  if hv : v ∈ c.1.1 then none else some (c.2 ⟨v, hv⟩)

/-- Expanding a compressed exact-sparse assignment recovers the original
assignment pointwise. -/
theorem supercriticalSparseAssignmentDecode_code
    {r n s : ℕ} (a : SupercriticalSparseAssignment r n s) :
    supercriticalSparseAssignmentDecode
      (supercriticalSparseAssignmentCode a) = a.1 := by
  classical
  funext v
  cases hav : a.1 v with
  | none =>
      simp [supercriticalSparseAssignmentDecode,
        supercriticalSparseAssignmentCode, hav]
  | some i =>
      simp [supercriticalSparseAssignmentDecode,
        supercriticalSparseAssignmentCode, hav]

/-- Compression is injective. -/
theorem supercriticalSparseAssignmentCode_injective
    {r n s : ℕ} :
    Function.Injective
      (@supercriticalSparseAssignmentCode r n s) := by
  intro a b hab
  apply Subtype.ext
  have hdecode := congrArg supercriticalSparseAssignmentDecode hab
  simpa [supercriticalSparseAssignmentDecode_code] using hdecode

/-- The compressed code space has the expected elementary cardinality. -/
theorem card_supercriticalSparseLabelingCode
    (r n s : ℕ) :
    Fintype.card (SupercriticalSparseLabelingCode r n s) =
      Nat.choose n s * r ^ (n - s) := by
  classical
  unfold SupercriticalSparseLabelingCode
  rw [Fintype.card_sigma]
  have hterm (S : {S : Finset (Fin n) // S.card = s}) :
      Fintype.card ({v : Fin n // v ∉ S.1} → Fin r) =
        r ^ (n - s) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    congr 1
    rw [Fintype.card_subtype_compl (fun v : Fin n ↦ v ∈ S.1)]
    simp [Fintype.card_subtype, S.2]
  simp_rw [hterm]
  rw [Finset.sum_const]
  change Fintype.card {S : Finset (Fin n) // S.card = s} *
      r ^ (n - s) = _
  rw [Fintype.card_finset_len, Fintype.card_fin]

/-- Exact-sparse option assignments inject into the compressed code space. -/
theorem card_supercriticalSparseAssignment_le
    (r n s : ℕ) :
    Fintype.card (SupercriticalSparseAssignment r n s) ≤
      Nat.choose n s * r ^ (n - s) := by
  rw [← card_supercriticalSparseLabelingCode]
  exact Fintype.card_le_of_injective
    (@supercriticalSparseAssignmentCode r n s)
    supercriticalSparseAssignmentCode_injective

/-! ## Division count -/

/-- The assignment of a division in the fixed-sparse-size family, with its
exact `none`-fiber cardinality attached. -/
noncomputable def supercriticalDivisionSparseAssignment
    {k n s : ℕ}
    (D : ↑(supercriticalDivisionsWithSparseCard k n s)) :
    SupercriticalSparseAssignment (k - 1) n s := by
  classical
  refine ⟨D.1.assignment, ?_⟩
  have hsparse := mem_supercriticalDivisionsWithSparseCard.mp D.2
  have heq :
      (Finset.univ.filter fun v : Fin n ↦ D.1.assignment v = none) =
        D.1.sparse := by
    ext v
    simp
  rw [heq, hsparse]

/-- Distinct divisions have distinct exact-sparse assignments. -/
theorem supercriticalDivisionSparseAssignment_injective
    {k n s : ℕ} :
    Function.Injective
      (@supercriticalDivisionSparseAssignment k n s) := by
  intro D E hDE
  apply Subtype.ext
  apply SupercriticalDivision.assignment_injective
  exact congrArg Subtype.val hDE

/-- There are at most `choose n s * (k-1)^(n-s)` ordered divisions with
exactly `s` sparse vertices. -/
theorem card_supercriticalDivisionsWithSparseCard_le
    (k n s : ℕ) :
    (supercriticalDivisionsWithSparseCard k n s).card ≤
      Nat.choose n s * (k - 1) ^ (n - s) := by
  calc
    (supercriticalDivisionsWithSparseCard k n s).card =
        Fintype.card ↑(supercriticalDivisionsWithSparseCard k n s) := by
      simp
    _ ≤ Fintype.card (SupercriticalSparseAssignment (k - 1) n s) :=
      Fintype.card_le_of_injective
        (@supercriticalDivisionSparseAssignment k n s)
        supercriticalDivisionSparseAssignment_injective
    _ ≤ Nat.choose n s * (k - 1) ^ (n - s) :=
      card_supercriticalSparseAssignment_le (k - 1) n s

/-- Uniform eventual comparison of all divisions at sparse size `s` with the
balanced reference fiber.  This bound drops the additional factor `(k-1)^{-s}`, while retaining the
explicit polynomial and ordered-cover losses. -/
theorem
    eventually_card_supercriticalDivisionsWithSparseCard_mul_reference_le
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ∀ s ≤ n,
      ((supercriticalDivisionsWithSparseCard k n s).card : ℝ) *
          (criticalReferenceFiberCard k n : ℝ) ≤
        ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
          (2 * (k - 1).factorial : ℕ) *
            (Nat.choose n s : ℝ) *
              (coMultipartiteGraphCountWithEdges (k - 1) n
                (criticalEdgeCount k n) : ℝ) := by
  filter_upwards [
    eventually_criticalReferenceFiberCard_mul_pow_le_coMultipartiteCount_mul_poly
      k hk] with n href
  intro s hs
  have hr : 0 < k - 1 := by omega
  have hpow : (k - 1) ^ (n - s) ≤ (k - 1) ^ n :=
    Nat.pow_le_pow_right hr (Nat.sub_le n s)
  have hdiv :
      (supercriticalDivisionsWithSparseCard k n s).card ≤
        Nat.choose n s * (k - 1) ^ n :=
    (card_supercriticalDivisionsWithSparseCard_le k n s).trans
      (Nat.mul_le_mul_left (Nat.choose n s) hpow)
  have hdivReal :
      ((supercriticalDivisionsWithSparseCard k n s).card : ℝ) ≤
        (Nat.choose n s : ℝ) * ((k - 1 : ℕ) : ℝ) ^ n := by
    exact_mod_cast hdiv
  calc
    ((supercriticalDivisionsWithSparseCard k n s).card : ℝ) *
          (criticalReferenceFiberCard k n : ℝ) ≤
        ((Nat.choose n s : ℝ) * ((k - 1 : ℕ) : ℝ) ^ n) *
          (criticalReferenceFiberCard k n : ℝ) :=
      mul_le_mul_of_nonneg_right hdivReal (by positivity)
    _ = (Nat.choose n s : ℝ) *
        (((k - 1 : ℕ) : ℝ) ^ n *
          (criticalReferenceFiberCard k n : ℝ)) := by ring
    _ ≤ (Nat.choose n s : ℝ) *
        (((n + 1 : ℕ) : ℝ) ^ (k - 1) *
          (2 * (k - 1).factorial : ℕ) *
            (coMultipartiteGraphCountWithEdges (k - 1) n
              (criticalEdgeCount k n) : ℝ)) :=
      mul_le_mul_of_nonneg_left href (by positivity)
    _ = ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
          (2 * (k - 1).factorial : ℕ) *
            (Nat.choose n s : ℝ) *
              (coMultipartiteGraphCountWithEdges (k - 1) n
                (criticalEdgeCount k n) : ℝ) := by ring

end InducedStars
