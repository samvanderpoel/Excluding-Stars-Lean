import InducedStars.Structure.Subcritical.LocalRowData
import InducedStars.Structure.Subcritical.ProfileRootEnergy
import InducedStars.Structure.Subcritical.DivisionMoveBounds
import InducedStars.Structure.Subcritical.RetainedMembership

/-!
# Finite retained-root geometry

The own count excludes every profile root, including the vertex itself.
The full complementary degree excludes the loop separately. The explicit
identities below retain that distinction in every local degree conversion.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Removing a set changes the loopless missing degree by at most its
cardinality. This also holds if the removed set contains the root. -/
theorem subcriticalComplement_trim_bounds (G : SimpleGraph V) (v : V)
    (P B : Finset V) :
    complementDegreeInFinset G v (P \ B) ≤ complementDegreeInFinset G v P ∧
      complementDegreeInFinset G v P ≤ complementDegreeInFinset G v (P \ B) + B.card := by
  constructor
  · exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
  · apply (Finset.card_le_card (show
        P.filter (fun y ↦ y ≠ v ∧ ¬ G.Adj v y) ⊆
          ((P \ B).filter fun y ↦ y ≠ v ∧ ¬ G.Adj v y) ∪ B from ?_)).trans
        (Finset.card_union_le _ _)
    intro y hy
    obtain ⟨hyP, hy⟩ := Finset.mem_filter.mp hy
    by_cases hyB : y ∈ B
    · exact Finset.mem_union_right _ hyB
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hyP, hyB⟩, hy⟩)

/-- Exact loop accounting for an own part. -/
theorem subcriticalOwn_degree_complement_add_one (G : SimpleGraph V) (v : V)
    (P : Finset V) (hv : v ∈ P) :
    degreeInFinset G v P + complementDegreeInFinset G v P + 1 = P.card := by
  have h := degreeInFinset_add_complementDegreeInFinset G v P
  rw [Finset.card_erase_of_mem hv] at h
  have hp := Finset.card_pos.mpr ⟨v, hv⟩
  omega

/-- In the trimmed own part there is no loop term because the root was
itself removed. -/
theorem subcriticalOwn_trimmed_degree_add_count (G : SimpleGraph V) (v : V)
    (P B : Finset V) (hvB : v ∈ B) :
    degreeInFinset G v (P \ B) + complementDegreeInFinset G v (P \ B) = (P \ B).card := by
  rw [degreeInFinset_add_complementDegreeInFinset,
    Finset.erase_eq_of_notMem (fun h ↦ (Finset.mem_sdiff.mp h).2 hvB)]

/-- The medium own-missing range gives both full-degree bounds and the
loopless complementary lower bound. A half-size trimming reserve suffices. -/
theorem subcriticalOwn_medium_degree_bounds
    (G : SimpleGraph V) (v : V) (P B : Finset V) {alpha : ℝ}
    (ha : 0 ≤ alpha) (hvP : v ∈ P) (hvB : v ∈ B)
    (hB : (B.card : ℝ) ≤ P.card / 2)
    (hlo : 2 * alpha * (P \ B).card ≤
      (complementDegreeInFinset G v (P \ B) : ℝ))
    (hhi : (complementDegreeInFinset G v (P \ B) : ℝ) ≤
      (1 - 2 * alpha) * (P \ B).card) :
    alpha * P.card ≤ (degreeInFinset G v P : ℝ) ∧
      (degreeInFinset G v P : ℝ) ≤ (1 - alpha) * P.card ∧
      alpha * P.card ≤ (complementDegreeInFinset G v P : ℝ) := by
  have hsize : (P.card : ℝ) ≤ (P \ B).card + B.card := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card : P.card ≤ (P \ B).card + B.card)
  have htrim : (degreeInFinset G v (P \ B) : ℝ) +
      complementDegreeInFinset G v (P \ B) = (P \ B).card := by
    exact_mod_cast subcriticalOwn_trimmed_degree_add_count G v P B hvB
  have hfull : (degreeInFinset G v P : ℝ) + complementDegreeInFinset G v P + 1 = P.card := by
    exact_mod_cast subcriticalOwn_degree_complement_add_one G v P hvP
  have hdegree : (degreeInFinset G v (P \ B) : ℝ) ≤ degreeInFinset G v P := by
    exact_mod_cast degreeInFinset_mono G v (Finset.sdiff_subset : P \ B ⊆ P)
  have hcomp : (complementDegreeInFinset G v (P \ B) : ℝ) ≤
      complementDegreeInFinset G v P := by
    exact_mod_cast (subcriticalComplement_trim_bounds G v P B).1
  have hscale : alpha * P.card ≤ 2 * alpha * (P \ B).card := by nlinarith
  exact ⟨by nlinarith, by nlinarith, hscale.trans (hlo.trans hcomp)⟩

/-- High missing count implies a nontrivial full complementary row and a
small full present row. All trimming loss is explicit. -/
theorem subcriticalOwn_highNegative_degree_bounds
    (G : SimpleGraph V) (v : V) (P B : Finset V) {alpha : ℝ}
    (ha : 0 ≤ alpha) (ha4 : alpha ≤ 1 / 4) (hvP : v ∈ P)
    (hB : (B.card : ℝ) ≤ P.card / 2)
    (hI : (1 - 2 * alpha) * (P \ B).card ≤
      (complementDegreeInFinset G v (P \ B) : ℝ)) :
    alpha * P.card ≤ (complementDegreeInFinset G v P : ℝ) ∧
      (degreeInFinset G v P : ℝ) ≤ 2 * alpha * P.card + B.card := by
  have hsize : (P.card : ℝ) ≤ (P \ B).card + B.card := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card : P.card ≤ (P \ B).card + B.card)
  have hsub : ((P \ B).card : ℝ) ≤ P.card := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : P \ B ⊆ P)
  have hcomp : (complementDegreeInFinset G v (P \ B) : ℝ) ≤
      complementDegreeInFinset G v P := by
    exact_mod_cast (subcriticalComplement_trim_bounds G v P B).1
  have hfull : (degreeInFinset G v P : ℝ) + complementDegreeInFinset G v P + 1 = P.card := by
    exact_mod_cast subcriticalOwn_degree_complement_add_one G v P hvP
  have ht : (0 : ℝ) ≤ (P \ B).card := Nat.cast_nonneg _
  constructor <;> nlinarith

/-- A high trimmed missing row keeps its order-one reserve when the roots
occupy at most an `alpha` fraction of the whole part. -/
theorem subcriticalOwn_highNegative_strong_complement
    (G : SimpleGraph V) (v : V) (P B : Finset V) {alpha : ℝ}
    (ha : 0 ≤ alpha)
    (hB : (B.card : ℝ) ≤ alpha * P.card)
    (hI : (1 - 2 * alpha) * (P \ B).card ≤
      (complementDegreeInFinset G v (P \ B) : ℝ)) :
    (1 - 3 * alpha) * P.card ≤ (complementDegreeInFinset G v P : ℝ) := by
  have hsize : (P.card : ℝ) ≤ (P \ B).card + B.card := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card : P.card ≤ (P \ B).card + B.card)
  have hcomp : (complementDegreeInFinset G v (P \ B) : ℝ) ≤
      complementDegreeInFinset G v P := by
    exact_mod_cast (subcriticalComplement_trim_bounds G v P B).1
  have hsub : ((P \ B).card : ℝ) ≤ P.card := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : P \ B ⊆ P)
  nlinarith

/-- The corresponding full present-row conversion for a high recorded
target. It has no own-part loop loss. -/
theorem subcriticalTrim_high_degree_lower
    (G : SimpleGraph V) (v : V) (P B : Finset V) {alpha : ℝ}
    (ha : 0 ≤ alpha)
    (hB : (B.card : ℝ) ≤ alpha * P.card)
    (hI : (1 - 2 * alpha) * (P \ B).card ≤ (degreeInFinset G v (P \ B) : ℝ)) :
    (1 - 3 * alpha) * P.card ≤ (degreeInFinset G v P : ℝ) := by
  have hsize : (P.card : ℝ) ≤ (P \ B).card + B.card := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card : P.card ≤ (P \ B).card + B.card)
  have hdeg : (degreeInFinset G v (P \ B) : ℝ) ≤ degreeInFinset G v P := by
    exact_mod_cast degreeInFinset_mono G v (Finset.sdiff_subset : P \ B ⊆ P)
  have hsub : ((P \ B).card : ℝ) ≤ P.card := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : P \ B ⊆ P)
  nlinarith

/-- High present degree after trimming, with the single loop accounted for
in the explicit reserve `|B|+1 ≤ alpha |P|`. -/
theorem subcriticalOwn_highDegree_lower
    (G : SimpleGraph V) (v : V) (P B : Finset V) {alpha : ℝ}
    (ha : 0 ≤ alpha) (hvP : v ∈ P)
    (hB : (B.card : ℝ) + 1 ≤ alpha * P.card)
    (hI : (complementDegreeInFinset G v (P \ B) : ℝ) <
      2 * alpha * (P \ B).card) :
    (1 - 3 * alpha) * P.card ≤ (degreeInFinset G v P : ℝ) := by
  have hsub : ((P \ B).card : ℝ) ≤ P.card := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : P \ B ⊆ P)
  have hcomp : (complementDegreeInFinset G v P : ℝ) ≤
      complementDegreeInFinset G v (P \ B) + B.card := by
    exact_mod_cast (subcriticalComplement_trim_bounds G v P B).2
  have hfull : (degreeInFinset G v P : ℝ) + complementDegreeInFinset G v P + 1 = P.card := by
    exact_mod_cast subcriticalOwn_degree_complement_add_one G v P hvP
  nlinarith

namespace RealizesSubcriticalProfile

variable {G : SimpleGraph V} {D : SubcriticalDivision k V}
  {eta theta alpha : ℝ} {R₀ : ℕ} {p : SubcriticalProfile D eta R₀ theta}

/-- Small stored own missing count rules out the complementary-degree
cause of retained badness, leaving an actual recorded eligible row. -/
theorem highDegree_rows_nonempty (h : RealizesSubcriticalProfile G alpha p)
    (v : V) (hv : v ∈ p.retainedRoots) (ha : 0 ≤ alpha)
    (hB : (p.roots.card : ℝ) ≤ alpha *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hI : ((p.ownCount v).val : ℝ) < 2 * alpha *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots).card) :
    (subcriticalProfileRowIndices p v).Nonempty := by
  let a := D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)
  have hbad := (mem_subcriticalBadRetainedRoots G D eta R₀ theta alpha v).mp
    (h.retained_roots ▸ hv)
  have hc : (complementDegreeInFinset G v (D.part a) : ℝ) ≤
      (p.ownCount v).val + p.roots.card := by
    rw [h.own_counts v hv]
    exact_mod_cast (subcriticalComplement_trim_bounds G v (D.part a) p.roots).2
  have ht : ((D.part a \ p.roots).card : ℝ) ≤ (D.part a).card := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : D.part a \ p.roots ⊆ D.part a)
  have hnot : (complementDegreeInFinset G v (D.part a) : ℝ) <
      4 * alpha * (D.part a).card := by
    dsimp [a] at hc ht ⊢
    nlinarith
  rcases hbad.2 with ⟨b, hb, hdegree⟩ | hcomp
  · refine ⟨b, (mem_subcriticalProfileRowIndices p v b).mpr ?_⟩
    rw [h.retained_rows v hv b]
    have helig' : D.EligibleProfileTarget eta R₀ theta v b := ⟨p.retainedRoots_subset hv, hb⟩
    simp [helig', hdegree]
  · exact (not_lt_of_ge hcomp hnot).elim

end RealizesSubcriticalProfile

/-- The explicit retained-part order reserve makes the existing ordinary
vertex-move interface valid; no singleton surgery is involved. -/
theorem SubcriticalCloseStructureResult.retainedPart_card_two_le
    {n R₀ : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
    {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
    {omega eta theta alpha delta epsilon : ℝ}
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hR : 1 ≤ R₀) (heta : 0 ≤ eta)
    {a : D.PartIndex} (ha : a ∈ D.retainedPartIndices eta R₀)
    (hn : 4 * (R₀ : ℝ) ≤ eta * n) :
    2 ≤ (D.part a).card := by
  have hr0 : (0 : ℝ) < R₀ := by exact_mod_cast (show 0 < R₀ by omega)
  have hr : (0 : ℝ) < 2 * (R₀ : ℝ) := by positivity
  have htwo : (2 : ℝ) ≤ eta * n / (2 * (R₀ : ℝ)) :=
    (le_div_iff₀ hr).mpr (by linarith)
  exact_mod_cast htwo.trans (R.retainedPart_card_lower_bound hR heta ha)

end InducedStars
