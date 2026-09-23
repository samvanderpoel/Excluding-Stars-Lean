import InducedStars.Structure.Subcritical.DivisionMoveBounds

/-!
# Valid donor comparisons at a singleton source

Swap the source vertex with a donor in a non-singleton part of its
own component, then move it to the target. Both divisions remain valid.
This costs at most five closed-neighborhood row budgets, independently of
the source part's size.
-/

noncomputable section
open scoped Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- A donor makes the target comparison admissible even at a singleton
source. The conclusion is uniform in the source component's core order. -/
theorem subcriticalMinimal_donor_target_gain_le
    (hk : 3 ≤ k) (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (hminimal : ∀ E : SubcriticalDivision k V,
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (i : Fin D.componentCount) (j l : Fin (D.core i).order) (v : V)
    (hv : v ∈ D.parts i j) (hdonor : 2 ≤ (D.parts i l).card)
    (target : D.PartIndex) (htarget : target.1 ≠ i)
    (B : ℝ) (hparts : ∀ t, ((D.parts i t).card : ℝ) ≤ B) :
    2 * (degreeInFinset G v (D.part target) : ℝ) ≤
      (D.part target).card + 5 * ((k - 1 : ℕ) : ℝ) * B := by
  classical
  have he : ((D.parts i l).erase v).Nonempty := by
    apply Finset.card_pos.mp
    have hlower := Finset.pred_card_le_card_erase (s := D.parts i l) (a := v)
    omega
  obtain ⟨w, hw⟩ := he
  obtain ⟨hwv, hw⟩ := Finset.mem_erase.mp hw
  have hvw : v ≠ w := Ne.symm hwv
  let E := D.relabel (Equiv.swap v w)
  have hvE : v ∈ E.parts i l := by simpa [E] using hw
  have hdonorE : 2 ≤ (E.parts i l).card := by
    simpa [E, SubcriticalDivision.relabel] using hdonor
  have hpartsE : ∀ t, ((E.parts i t).card : ℝ) ≤ B := by
    intro t
    simpa [E, SubcriticalDivision.relabel] using hparts t
  have hvt : v ∉ D.part target := by
    intro ht
    have ha := D.mem_part_unique (b := ⟨i, j⟩) ht hv
    exact htarget (congrArg Sigma.fst ha)
  have hwt : w ∉ D.part target := by
    intro ht
    have ha := D.mem_part_unique (b := ⟨i, l⟩) ht hw
    exact htarget (congrArg Sigma.fst ha)
  have htargetE : E.part target = D.part target := by
    ext x
    change x ∈ (D.relabel (Equiv.swap v w)).parts target.1 target.2 ↔ _
    rw [SubcriticalDivision.mem_relabel_part]
    change Equiv.swap v w x ∈ D.part target ↔ x ∈ D.part target
    by_cases hxv : x = v
    · subst x
      simp [hwt, hvt]
    by_cases hxw : x = w
    · subst x
      simp [hwt, hvt]
    simp [Equiv.swap_apply_of_ne_of_ne hxv hxw]
  have hvalid : ∀ a, some target ≠ some a → ((E.part a).erase v).Nonempty :=
    fun a _ ↦ E.erase_nonempty_of_source (source := ⟨i, l⟩) hvE hdonorE a
  have hcost := subcriticalMove_target_cost_bound G E v target hvalid
  have hmin := hminimal (E.moveVertex v (some target) hvalid)
  have hswap := subcriticalSwap_cost_le hk G D i j l v w hv hw hvw B hparts
  have hdegree := subcriticalModel_degree_le_of_part_bound hk G E ⟨i, l⟩
    hvE Finset.univ B hpartsE
  rw [degreeInFinset_univ_eq_degree] at hdegree
  rw [htargetE] at hcost
  have hcostR : (subcriticalDefectCost G (E.moveVertex v (some target) hvalid) : ℝ) +
      2 * degreeInFinset G v (D.part target) ≤ subcriticalDefectCost G E +
        (D.part target).card + (subcriticalDivisionModelGraph G E).degree v := by
    exact_mod_cast hcost
  have hminR : (subcriticalDefectCost G D : ℝ) ≤
      subcriticalDefectCost G (E.moveVertex v (some target) hvalid) := by
    exact_mod_cast hmin
  change (subcriticalDefectCost G E : ℝ) ≤ _ at hswap
  linarith

end InducedStars
