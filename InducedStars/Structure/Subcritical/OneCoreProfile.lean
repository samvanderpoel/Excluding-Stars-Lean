import InducedStars.Structure.Subcritical.OneCoreSupport
import InducedStars.Structure.Subcritical.CleanCoverConnectivity
import InducedStars.Structure.Subcritical.RetainedCounts
import DenseGraph.FiniteModels.FixedCardinalityTransport

/-!
# Literal one-core profile coordinates on the retained support

Only the support is relabeled to its fixed `Fin` type. Its vertex labels,
part labels, fixed quotas and individual edge coordinates are all retained
by explicit equivalences.
-/

noncomputable section
open Finset Set
open scoped Classical BigOperators
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

namespace SupercriticalDivision

def supportLabelEquiv (D : SupercriticalDivision k V) :
    (D.support : Set V) ≃ Fin D.support.card :=
  Fintype.equivFinOfCardEq (Fintype.card_coe _)

def onSupportFin (D : SupercriticalDivision k V) :
    SupercriticalDivision k (Fin D.support.card) :=
  (D.onSupportSet D.support rfl).relabel D.supportLabelEquiv

def supportVertex (D : SupercriticalDivision k V) (x : Fin D.support.card) : V :=
  (D.supportLabelEquiv.symm x).val

theorem supportVertex_injective (D : SupercriticalDivision k V) :
    Function.Injective D.supportVertex :=
  Subtype.val_injective.comp D.supportLabelEquiv.symm.injective

@[simp] theorem mem_onSupportFin_part (D : SupercriticalDivision k V)
    (i : Fin (k - 1)) (x : Fin D.support.card) :
    x ∈ D.onSupportFin.parts i ↔ D.supportVertex x ∈ D.parts i := by
  simp only [onSupportFin, mem_relabel_part]
  exact D.mem_onSupportSet_part D.support rfl i (D.supportLabelEquiv.symm x)

theorem onSupportFin_part_card (D : SupercriticalDivision k V) (i : Fin (k - 1)) :
    (D.onSupportFin.parts i).card = (D.parts i).card := by
  simp only [onSupportFin, relabel, Finset.card_map, onSupportSet_part_card]

theorem onSupportFin_isFull (D : SupercriticalDivision k V) : D.onSupportFin.IsFull := by
  rw [isFull_iff_support_eq_univ]
  ext v
  simp only [onSupportFin, mem_relabel_support,
    (D.onSupportSet D.support rfl).support_eq_univ (D.onSupportSet_isFull D.support rfl),
    Finset.mem_univ]

end SupercriticalDivision

theorem SubcriticalDivision.ofSupercritical_componentSupport (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (i : Fin 1) :
    (SubcriticalDivision.ofSupercritical hk D).componentSupport i = D.support := by
  ext v
  simp only [SubcriticalDivision.mem_componentSupport, SupercriticalDivision.mem_support,
    SubcriticalDivision.ofSupercritical]
  rfl

theorem SubcriticalDivision.ofSupercritical_retained_all (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) {eta : ℝ} {R₀ : ℕ}
    (hsize : eta * Fintype.card V ≤ (D.support.card : ℝ)) (horder : k - 1 ≤ R₀) :
    (SubcriticalDivision.ofSupercritical hk D).retainedComponentIndices eta R₀ = Finset.univ := by
  ext i
  simp only [SubcriticalDivision.mem_retainedComponentIndices,
    SubcriticalDivision.ofSupercritical_componentSupport, Finset.mem_univ, iff_true]
  exact ⟨hsize, horder⟩

def oneCoreRetainedPairEquiv (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ)
    (hret : (SubcriticalDivision.ofSupercritical hk D).retainedComponentIndices eta R₀ = Finset.univ) :
    SupercriticalPartPair k ≃ RetainedActivePair (SubcriticalDivision.ofSupercritical hk D) eta R₀ where
  toFun e := {
    component := ⟨0, by change 0 < 1; omega⟩
    component_retained := by rw [hret]; exact Finset.mem_univ _
    left := e.left
    right := e.right
    left_lt_right := e.left_lt_right
    active := e.left_ne_right }
  invFun e := ⟨e.left, e.right, e.left_lt_right⟩
  left_inv e := rfl
  right_inv e := by
    rcases e with ⟨i, hi, a, b, hab, hadj⟩
    have hi0 : i = (⟨0, by change 0 < 1; omega⟩ :
        Fin (SubcriticalDivision.ofSupercritical hk D).componentCount) := by
      apply Fin.ext
      change i.val = 0
      have hi1 : i.val < 1 := i.isLt
      omega
    apply RetainedActivePair.eq_of_parts
    · exact Sigma.ext hi0.symm (heq_of_eq rfl)
    · exact Sigma.ext hi0.symm (heq_of_eq rfl)

@[simp] theorem oneCoreRetainedPairEquiv_capacity (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (hret) (e : SupercriticalPartPair k) :
    retainedActiveCapacity (SubcriticalDivision.ofSupercritical hk D) eta R₀
      (oneCoreRetainedPairEquiv hk D eta R₀ hret e) = crossEdgeCapacity D.onSupportFin e := by
  simp only [crossEdgeCapacity, D.onSupportFin_part_card]
  rfl

def oneCoreProfile (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    {eta : ℝ} {R₀ : ℕ}
    (hret : (SubcriticalDivision.ofSupercritical hk D).retainedComponentIndices eta R₀ = Finset.univ)
    (v : RetainedEdgeCountVector (SubcriticalDivision.ofSupercritical hk D) eta R₀) :
    SupercriticalEdgeProfile D.onSupportFin where
  count e := v.count (oneCoreRetainedPairEquiv hk D eta R₀ hret e)
  count_le_capacity e := by
    rw [← oneCoreRetainedPairEquiv_capacity hk D eta R₀ hret e]
    exact v.count_le_capacity _

theorem oneCoreProfile_multiplicity (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    {eta : ℝ} {R₀ : ℕ} (hret)
    (v : RetainedEdgeCountVector (SubcriticalDivision.ofSupercritical hk D) eta R₀) :
    supercriticalProfileMultiplicity (oneCoreProfile hk D hret v) =
      retainedEdgeCountMultiplicity v := by
  unfold supercriticalProfileMultiplicity retainedEdgeCountMultiplicity
  have h := Equiv.prod_comp (oneCoreRetainedPairEquiv hk D eta R₀ hret)
    (fun e ↦ (retainedActiveCapacity _ eta R₀ e).choose (v.count e))
  simpa only [oneCoreRetainedPairEquiv_capacity, oneCoreProfile] using h

theorem oneCoreProfile_density (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    {eta : ℝ} {R₀ : ℕ} (hret)
    (v : RetainedEdgeCountVector (SubcriticalDivision.ofSupercritical hk D) eta R₀)
    (e : SupercriticalPartPair k) :
    profileDensity (oneCoreProfile hk D hret v) e =
      retainedEdgeCountDensity v (oneCoreRetainedPairEquiv hk D eta R₀ hret e) := by
  unfold profileDensity retainedEdgeCountDensity
  rw [oneCoreRetainedPairEquiv_capacity]
  rfl

end InducedStars
