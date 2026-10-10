import InducedStars.Graphon.TypeTower
import InducedStars.Regularity.TypeLemma
import Mathlib.Tactic

/-!
# Construction of the Type-partition tower

This module builds the nested finite Type data used by the Type Graphon
Sequence Lemma.  The first section isolates the repeated extraction from the
enhanced Type Lemma: discard a prefix, choose a Type on every remaining host,
and make the number of children constant along a subsequence.
-/

noncomputable section

open Finset Filter Set
open scoped BigOperators Topology

namespace InducedStars

open Regularity

attribute [local instance] Classical.propDecidable

/-- A sequence of prescribed equitable partitions carried by a subsequence
of the original sampling graphs. -/
structure EquitablePartitionRow (s : ℕ) where
  extraction : ℕ → ℕ
  extraction_strictMono : StrictMono extraction
  partition : (n : ℕ) →
    EquitableInitialPartition (Fin (extraction n + 1)) s

namespace EquitablePartitionRow

/-- The one-class prescribed partition on every graph in the original
sampling sequence. -/
def trivial : EquitablePartitionRow 1 where
  extraction := id
  extraction_strictMono := strictMono_id
  partition n := EquitableInitialPartition.ofParts
    (fun _ : Fin 1 => (Finset.univ : Finset (Fin (n + 1))))
    (fun _ => Finset.univ_nonempty)
    (by
      intro i _ j _ hij
      exact (hij (Subsingleton.elim i j)).elim)
    (by simp)
    (by simp [Nat.dist_self])

@[simp] theorem trivial_extraction (n : ℕ) : trivial.extraction n = n :=
  rfl

@[simp] theorem trivial_partition_parts (n : ℕ) (i : Fin 1) :
    (trivial.partition n).parts i = (Finset.univ : Finset (Fin (n + 1))) := by
  change (Finset.univ : Finset (Fin (n + 1))) = Finset.univ
  rfl

/-- Selecting the `index m`-th member of an arbitrary level-indexed family
of strictly increasing rows is cofinal as soon as `m ≤ index m`.  This is the
adapter used by the final, level-dependent diagonal selection. -/
theorem tendsto_selected_extraction
    {clusterCount : ℕ → ℕ}
    (row : (m : ℕ) → EquitablePartitionRow (clusterCount m))
    (index : ℕ → ℕ) (hindex : ∀ m, m ≤ index m) :
    Tendsto (fun m ↦ (row m).extraction (index m)) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop N] with m hm
  exact hm.trans <| (hindex m).trans <|
    (row m).extraction_strictMono.id_le (index m)

end EquitablePartitionRow

/-- The result of applying the enhanced Type Lemma along a partition row and
then extracting a subsequence with a constant number of children. -/
structure TypeLemmaRowResult
    {f s : ℕ} (G : (n : ℕ) → SimpleGraph (Fin (n + 1)))
    (parent : EquitablePartitionRow s)
    (eta delta : ℝ) (L : ℕ) where
  upperBound : ℕ
  factor : ℕ → ℕ
  factor_strictMono : StrictMono factor
  childCount : ℕ
  childCount_pos : 0 < childCount
  result : (n : ℕ) →
    @TypeLemmaResult (Fin (parent.extraction (factor n) + 1))
      inferInstance inferInstance
      (G (parent.extraction (factor n))) (Classical.decRel _)
      eta delta f s (parent.partition (factor n)) L upperBound
  result_childCount : ∀ n,
    letI : DecidableRel (G (parent.extraction (factor n))).Adj := Classical.decRel _
    (result n).childCount = childCount

namespace TypeLemmaRowResult

variable {f s : ℕ} {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
  {parent : EquitablePartitionRow s} {eta delta : ℝ} {L : ℕ}

/-- The extracted row of original sampling indices. -/
def extraction (R : TypeLemmaRowResult (f := f) G parent eta delta L) (n : ℕ) : ℕ :=
  parent.extraction (R.factor n)

theorem extraction_strictMono
    (R : TypeLemmaRowResult (f := f) G parent eta delta L) :
    StrictMono R.extraction :=
  parent.extraction_strictMono.comp R.factor_strictMono

/-- The number of final clusters is the fixed parent count times the fixed
child count. -/
theorem clusterCount_eq
    (R : TypeLemmaRowResult (f := f) G parent eta delta L) (n : ℕ) :
    (R.result n).regularityType.partition.clusterCount = s * R.childCount := by
  letI : DecidableRel (G (parent.extraction (R.factor n))).Adj := Classical.decRel _
  rw [(R.result n).clusterCount_eq, R.result_childCount]

/-- Restrict a constant-child Type row along a further subsequence. -/
def subsequence (R : TypeLemmaRowResult (f := f) G parent eta delta L)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    TypeLemmaRowResult (f := f) G parent eta delta L where
  upperBound := R.upperBound
  factor := R.factor ∘ phi
  factor_strictMono := R.factor_strictMono.comp hphi
  childCount := R.childCount
  childCount_pos := R.childCount_pos
  result n := R.result (phi n)
  result_childCount n := R.result_childCount (phi n)

@[simp] theorem subsequence_factor
    (R : TypeLemmaRowResult (f := f) G parent eta delta L)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (n : ℕ) :
    (R.subsequence phi hphi).factor n = R.factor (phi n) :=
  rfl

@[simp] theorem subsequence_result
    (R : TypeLemmaRowResult (f := f) G parent eta delta L)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (n : ℕ) :
    (R.subsequence phi hphi).result n = R.result (phi n) :=
  rfl

end TypeLemmaRowResult

/-- Apply the enhanced Type Lemma uniformly along a prescribed partition
row, discard its finite size threshold, and make the positive child count
constant along a further subsequence. -/
theorem exists_typeLemmaRowResult
    {f s : ℕ} (hf : 0 < f)
    (G : (n : ℕ) → SimpleGraph (Fin (n + 1)))
    (parent : EquitablePartitionRow s) (hs : 0 < s)
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    {epsilonStar eta : ℝ} (hStar :
      ∀ L t : ℕ, 0 < L → 0 < t →
        ∀ eta : ℝ, 0 < eta → eta < epsilonStar →
          ∃ U n0 : ℕ,
            ∀ {V : Type} [Fintype V] [DecidableEq V]
              (H : SimpleGraph V) [DecidableRel H.Adj]
              {q : ℕ} (_hq : 0 < q) (_hqt : q ≤ t)
              (initial : EquitableInitialPartition V q),
                n0 ≤ Fintype.card V →
                  Nonempty (TypeLemmaResult H eta delta f initial L U))
    (heta : 0 < eta) (hetaStar : eta < epsilonStar)
    (L t : ℕ) (hL : 0 < L) (ht : 0 < t) (hst : s ≤ t) :
    Nonempty (TypeLemmaRowResult (f := f) G parent eta delta L) := by
  classical
  obtain ⟨U, n0, happly⟩ := hStar L t hL ht eta heta hetaStar
  let shift : ℕ → ℕ := fun n => n + n0
  have hshift : StrictMono shift := by
    intro a b hab
    simp only [shift]
    omega
  let ResultAt (n : ℕ) :=
    @TypeLemmaResult (Fin (parent.extraction (shift n) + 1))
      inferInstance inferInstance
      (G (parent.extraction (shift n))) (Classical.decRel _)
      eta delta f s (parent.partition (shift n)) L U
  have hresult : ∀ n, Nonempty (ResultAt n) := by
    intro n
    apply happly (G (parent.extraction (shift n))) hs hst
      (parent.partition (shift n))
    simp only [Fintype.card_fin]
    have hmono : shift n ≤ parent.extraction (shift n) :=
      parent.extraction_strictMono.id_le _
    simp only [shift] at hmono ⊢
    omega
  let chosen : (n : ℕ) → ResultAt n := fun n => Classical.choice (hresult n)
  have hchildPos : ∀ n, 1 ≤ (chosen n).childCount := by
    intro n
    letI : DecidableRel (G (parent.extraction (shift n))).Adj := Classical.decRel _
    exact (chosen n).childCount_pos
  have hchildBound : ∀ n, (chosen n).childCount ≤ U := by
    intro n
    letI : DecidableRel (G (parent.extraction (shift n))).Adj := Classical.decRel _
    have hcount := (chosen n).clusterCount_eq
    have hlower : (chosen n).childCount ≤ s * (chosen n).childCount := by
      calc
        (chosen n).childCount = 1 * (chosen n).childCount := by omega
        _ ≤ s * (chosen n).childCount :=
          Nat.mul_le_mul_right (chosen n).childCount (Nat.succ_le_iff.mpr hs)
    exact hlower.trans (hcount ▸ (chosen n).upper_clusterCount)
  obtain ⟨r, hr, _hrU, phi, hphi, hconstant⟩ :=
    Graphon.boundedNat_constant_subsequence U
      (fun n => (chosen n).childCount) hchildPos hchildBound
  let factor : ℕ → ℕ := shift ∘ phi
  have hfactor : StrictMono factor := hshift.comp hphi
  let selected (n : ℕ) :
      @TypeLemmaResult (Fin (parent.extraction (factor n) + 1))
        inferInstance inferInstance
        (G (parent.extraction (factor n))) (Classical.decRel _)
        eta delta f s (parent.partition (factor n)) L U :=
    chosen (phi n)
  exact ⟨{
    upperBound := U
    factor := factor
    factor_strictMono := hfactor
    childCount := r
    childCount_pos := hr
    result := selected
    result_childCount := by
      intro n
      letI : DecidableRel (G (parent.extraction (factor n))).Adj := Classical.decRel _
      exact hconstant n }⟩

end InducedStars
