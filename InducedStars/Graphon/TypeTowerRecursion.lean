import InducedStars.Graphon.TypeTowerSystem

/-!
# Generic recursion for clean Type towers

This module packages a base clean Type-sequence level and an abstract
successor operation into an infinite `CleanTypeTowerSystem`.  It deliberately
does not depend on any concrete construction of one-row extensions.
-/

noncomputable section

namespace InducedStars

/-- The data supplied by one abstract successor step in the generic clean
Type-tower recursion.  This structure is needed because an exact extension is
data (a `Type`), whereas cluster-count growth is a proposition. -/
structure CleanTypeTowerSuccessor
    {f : ℕ} {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
    {parentEta delta : ℝ} (childEta : ℝ)
    (parent : CleanTypeSequenceLevel (f := f) G parentEta delta) where
  child : CleanTypeSequenceLevel (f := f) G childEta delta
  extension : CleanTypeSequenceExtension parent child
  clusterCount_growth : 2 * parent.clusterCount ≤ child.clusterCount

/-- Dependent choice of an infinite clean Type tower from a base level and an
abstract successor operation.  The successor package supplies both the exact
extension data and the required doubling of cluster counts. -/
theorem exists_cleanTypeTowerSystem_of_base_step
    {f : ℕ} {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
    {eta : ℕ → ℝ} {delta : ℝ}
    (hbase : Nonempty (CleanTypeSequenceLevel (f := f) G (eta 0) delta))
    (hstep : ∀ (m : ℕ)
        (parent : CleanTypeSequenceLevel (f := f) G (eta m) delta),
      Nonempty (CleanTypeTowerSuccessor (eta (m + 1)) parent)) :
    Nonempty (CleanTypeTowerSystem (f := f) G eta delta) := by
  let base : CleanTypeSequenceLevel (f := f) G (eta 0) delta :=
    Classical.choice hbase
  let level : (m : ℕ) →
      CleanTypeSequenceLevel (f := f) G (eta m) delta :=
    fun m ↦ Nat.rec (motive := fun r ↦
        CleanTypeSequenceLevel (f := f) G (eta r) delta)
      base
      (fun r parent ↦ (Classical.choice (hstep r parent)).child)
      m
  have level_succ (m : ℕ) :
      level (m + 1) = (Classical.choice (hstep m (level m))).child := by
    rfl
  let extension (m : ℕ) :
      CleanTypeSequenceExtension (level m) (level (m + 1)) := by
    rw [level_succ m]
    exact (Classical.choice (hstep m (level m))).extension
  have growth (m : ℕ) :
      2 * (level m).clusterCount ≤ (level (m + 1)).clusterCount := by
    rw [level_succ m]
    exact (Classical.choice (hstep m (level m))).clusterCount_growth
  exact ⟨{
    level := level
    factor := fun m ↦ (extension m).factor
    factor_strictMono := fun m ↦ (extension m).factor_strictMono
    extraction_succ := fun m ↦ (extension m).row_extraction
    clusterCount_dvd_succ := fun m ↦ (extension m).clusterCount_dvd
    clusterCount_growth := growth
    limit_blockAverage_succ := fun m ↦
      (extension m).limitMatrix_blockAverage
  }⟩

end InducedStars
