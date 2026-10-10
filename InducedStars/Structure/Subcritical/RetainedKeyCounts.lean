import InducedStars.Structure.Subcritical.RetainedKeyCoordinates

/-!
# Partition functions depend only on the retained key

All coordinates are transported literally. In particular, the clean
partition function retains the original `eta` in its sparse-edge cutoff;
forgetting nonretained decorations does not alter any graph multiplicity.
-/

noncomputable section
open Finset
open scoped Classical BigOperators
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

abbrev RetainedKeyEdgeCountVector (K : SubcriticalRetainedKey k V) :=
  (e : K.ActiveIndex) → Fin (K.activeCapacity e + 1)

def retainedKeyEdgeCountTotal {K : SubcriticalRetainedKey k V}
    (v : RetainedKeyEdgeCountVector K) : ℕ := ∑ e, (v e).val

def retainedKeyEdgeCountMultiplicity {K : SubcriticalRetainedKey k V}
    (v : RetainedKeyEdgeCountVector K) : ℕ :=
  ∏ e, Nat.choose (K.activeCapacity e) (v e).val

def retainedKeyEdgeCountDensity {K : SubcriticalRetainedKey k V}
    (v : RetainedKeyEdgeCountVector K) (e : K.ActiveIndex) : ℝ :=
  ((v e).val : ℝ) / K.activeCapacity e

def retainedKeyEdgeCountLevel (K : SubcriticalRetainedKey k V) (m : ℕ)
    (delta : ℝ) (u : ℤ) : Finset (RetainedKeyEdgeCountVector K) :=
  Finset.univ.filter fun v ↦
    (K.cliqueCapacity : ℤ) + (retainedKeyEdgeCountTotal v : ℤ) + u = (m : ℤ) ∧
      ∀ e, pK k - 2 * delta ≤ retainedKeyEdgeCountDensity v e ∧
        retainedKeyEdgeCountDensity v e ≤ pK k + 2 * delta

def retainedKeyNarrowEdgeCountLevel (K : SubcriticalRetainedKey k V) (m : ℕ)
    (delta : ℝ) (u : ℤ) : Finset (RetainedKeyEdgeCountVector K) :=
  Finset.univ.filter fun v ↦
    (K.cliqueCapacity : ℤ) + (retainedKeyEdgeCountTotal v : ℤ) + u = (m : ℤ) ∧
      ∀ e, pK k - delta ≤ retainedKeyEdgeCountDensity v e ∧
        retainedKeyEdgeCountDensity v e ≤ pK k + delta

def retainedKeyPartitionFunction (K : SubcriticalRetainedKey k V) (m : ℕ)
    (delta : ℝ) (u : ℤ) : ℕ :=
  ∑ v ∈ retainedKeyEdgeCountLevel K m delta u, retainedKeyEdgeCountMultiplicity v

def retainedKeyNarrowPartitionFunction (K : SubcriticalRetainedKey k V) (m : ℕ)
    (delta : ℝ) (u : ℤ) : ℕ :=
  ∑ v ∈ retainedKeyNarrowEdgeCountLevel K m delta u, retainedKeyEdgeCountMultiplicity v

def retainedKeyCleanPartitionFunction (K : SubcriticalRetainedKey k V)
    (eta : ℝ) (m : ℕ) (delta : ℝ) : ℕ :=
  ∑ b ∈ Finset.range (Nat.floor
      (subcriticalSparseSideConstant k * eta * (Fintype.card V : ℝ)^2) + 1),
    inducedStarFreeGraphCountWithEdges k K.remainder.card b *
      retainedKeyPartitionFunction K m delta (b : ℤ)

/-- The exact capacity-preserving coordinate transport, including empty keys. -/
def retainedKeyVectorEquiv (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    RetainedEdgeCountVector D eta R₀ ≃
      RetainedKeyEdgeCountVector (retainedKey D eta R₀) where
  toFun v e := ⟨v.count (retainedKeyActiveEquiv D eta R₀ e), by
    rw [retainedKeyActiveEquiv_capacity]
    exact Nat.lt_succ_iff.mpr (v.count_le_capacity _)⟩
  invFun w := {
    count e := (w ((retainedKeyActiveEquiv D eta R₀).symm e)).val
    count_le_capacity e := by
      have h := Nat.lt_succ_iff.mp
        (w ((retainedKeyActiveEquiv D eta R₀).symm e)).isLt
      exact h.trans (by simpa only [Equiv.apply_symm_apply] using
        (retainedKeyActiveEquiv_capacity D eta R₀
          ((retainedKeyActiveEquiv D eta R₀).symm e)).le) }
  left_inv v := by
    apply RetainedEdgeCountVector.ext
    funext e
    simp
  right_inv w := by
    funext e
    apply Fin.ext
    exact congrArg (fun a ↦ (w a).val)
      ((retainedKeyActiveEquiv D eta R₀).symm_apply_apply e)

@[simp] theorem retainedKeyVectorEquiv_count (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (v : RetainedEdgeCountVector D eta R₀)
    (e : (retainedKey D eta R₀).ActiveIndex) :
    (retainedKeyVectorEquiv D eta R₀ v e).val =
      v.count (retainedKeyActiveEquiv D eta R₀ e) := rfl

@[simp] theorem retainedKeyVectorEquiv_total (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (v : RetainedEdgeCountVector D eta R₀) :
    retainedKeyEdgeCountTotal (retainedKeyVectorEquiv D eta R₀ v) =
      retainedEdgeCountTotal v := by
  exact (retainedKeyActiveEquiv D eta R₀).sum_comp v.count

@[simp] theorem retainedKeyVectorEquiv_multiplicity (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (v : RetainedEdgeCountVector D eta R₀) :
    retainedKeyEdgeCountMultiplicity (retainedKeyVectorEquiv D eta R₀ v) =
      retainedEdgeCountMultiplicity v := by
  simp only [retainedKeyEdgeCountMultiplicity, retainedKeyVectorEquiv_count,
    retainedKeyActiveEquiv_capacity]
  exact (retainedKeyActiveEquiv D eta R₀).prod_comp
    (fun e ↦ Nat.choose (retainedActiveCapacity D eta R₀ e) (v.count e))

@[simp] theorem retainedKeyVectorEquiv_density (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (v : RetainedEdgeCountVector D eta R₀)
    (e : (retainedKey D eta R₀).ActiveIndex) :
    retainedKeyEdgeCountDensity (retainedKeyVectorEquiv D eta R₀ v) e =
      retainedEdgeCountDensity v (retainedKeyActiveEquiv D eta R₀ e) := by
  simp only [retainedKeyEdgeCountDensity, retainedKeyVectorEquiv_count,
    retainedKeyActiveEquiv_capacity, retainedEdgeCountDensity]

@[simp] theorem retainedKeyVectorEquiv_mem_level (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) (u : ℤ)
    (v : RetainedEdgeCountVector D eta R₀) :
    retainedKeyVectorEquiv D eta R₀ v ∈
      retainedKeyEdgeCountLevel (retainedKey D eta R₀) m delta u ↔
      v ∈ retainedEdgeCountLevel D eta R₀ m delta u := by
  simp only [retainedKeyEdgeCountLevel, Finset.mem_filter, Finset.mem_univ, true_and,
    retainedKey_cliqueCapacity, retainedKeyVectorEquiv_total,
    retainedKeyVectorEquiv_density, mem_retainedEdgeCountLevel]
  rw [(retainedKeyActiveEquiv D eta R₀).surjective.forall]

@[simp] theorem retainedKeyVectorEquiv_mem_narrowLevel (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) (u : ℤ)
    (v : RetainedEdgeCountVector D eta R₀) :
    retainedKeyVectorEquiv D eta R₀ v ∈
      retainedKeyNarrowEdgeCountLevel (retainedKey D eta R₀) m delta u ↔
      v ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta u := by
  simp only [retainedKeyNarrowEdgeCountLevel, Finset.mem_filter, Finset.mem_univ, true_and,
    retainedKey_cliqueCapacity, retainedKeyVectorEquiv_total,
    retainedKeyVectorEquiv_density, mem_retainedNarrowEdgeCountLevel]
  rw [(retainedKeyActiveEquiv D eta R₀).surjective.forall]

@[simp] theorem retainedKeyPartitionFunction_retainedKey (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) (u : ℤ) :
    retainedKeyPartitionFunction (retainedKey D eta R₀) m delta u =
      retainedPartitionFunction D eta R₀ m delta u := by
  symm
  apply Finset.sum_equiv (retainedKeyVectorEquiv D eta R₀)
  · intro v; exact (retainedKeyVectorEquiv_mem_level D eta R₀ m delta u v).symm
  · intro v _; exact (retainedKeyVectorEquiv_multiplicity D eta R₀ v).symm

@[simp] theorem retainedKeyNarrowPartitionFunction_retainedKey
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) (u : ℤ) :
    retainedKeyNarrowPartitionFunction (retainedKey D eta R₀) m delta u =
      retainedNarrowPartitionFunction D eta R₀ m delta u := by
  symm
  apply Finset.sum_equiv (retainedKeyVectorEquiv D eta R₀)
  · intro v; exact (retainedKeyVectorEquiv_mem_narrowLevel D eta R₀ m delta u v).symm
  · intro v _; exact (retainedKeyVectorEquiv_multiplicity D eta R₀ v).symm

@[simp] theorem retainedKeyCleanPartitionFunction_retainedKey
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) :
    retainedKeyCleanPartitionFunction (retainedKey D eta R₀) eta m delta =
      cleanRetainedPartitionFunction D eta R₀ m delta := by
  simp only [retainedKeyCleanPartitionFunction, cleanRetainedPartitionFunction,
    retainedKey_remainder, retainedKeyPartitionFunction_retainedKey]

theorem retainedPartitionFunction_eq_of_retainedKey_eq
    {D E : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (h : retainedKey D eta R₀ = retainedKey E eta R₀) (m : ℕ) (delta : ℝ) (u : ℤ) :
    retainedPartitionFunction D eta R₀ m delta u =
      retainedPartitionFunction E eta R₀ m delta u := by
  rw [← retainedKeyPartitionFunction_retainedKey, h, retainedKeyPartitionFunction_retainedKey]

theorem retainedNarrowPartitionFunction_eq_of_retainedKey_eq
    {D E : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (h : retainedKey D eta R₀ = retainedKey E eta R₀) (m : ℕ) (delta : ℝ) (u : ℤ) :
    retainedNarrowPartitionFunction D eta R₀ m delta u =
      retainedNarrowPartitionFunction E eta R₀ m delta u := by
  rw [← retainedKeyNarrowPartitionFunction_retainedKey, h,
    retainedKeyNarrowPartitionFunction_retainedKey]

theorem cleanRetainedPartitionFunction_eq_of_retainedKey_eq
    {D E : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (h : retainedKey D eta R₀ = retainedKey E eta R₀) (m : ℕ) (delta : ℝ) :
    cleanRetainedPartitionFunction D eta R₀ m delta =
      cleanRetainedPartitionFunction E eta R₀ m delta := by
  rw [← retainedKeyCleanPartitionFunction_retainedKey, h,
    retainedKeyCleanPartitionFunction_retainedKey]

end InducedStars
