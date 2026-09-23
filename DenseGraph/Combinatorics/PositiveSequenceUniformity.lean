import DenseGraph.Combinatorics.CompactSequenceUniformity

/-!
# Uniformity when the second normalization depends on a positive size
-/

noncomputable section

open Filter Set Topology

namespace DenseGraph

theorem eventually_uniform_of_positiveNormalizedSequences_tendsto_zero
    {D : ℕ → ℝ} (hD : Tendsto D atTop atTop)
    {F : ℕ → ℕ → ℕ → ℝ}
    (hseq : ∀ (s t : ℕ → ℕ) (x z : ℝ), 0 ≤ x → 0 ≤ z →
      (∀ᶠ n : ℕ in atTop, 1 ≤ s n) →
      Tendsto (fun n ↦ (s n : ℝ) / D n) atTop (𝓝 x) →
      Tendsto (fun n ↦ (t n : ℝ) / ((s n : ℝ) * D n)) atTop (𝓝 z) →
      Tendsto (fun n ↦ F n (s n) (t n)) atTop (𝓝 0))
    (L T : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ s t : ℕ, 1 ≤ s →
      (s : ℝ) / D n ≤ L → (t : ℝ) / ((s : ℝ) * D n) ≤ T → |F n s t| ≤ epsilon := by
  classical
  by_contra h
  have hf := (not_eventually.mp h).and_eventually
    (hD.eventually (eventually_gt_atTop (0 : ℝ)))
  have hf' : ∃ᶠ n : ℕ in atTop, ∃ s t : ℕ,
      1 ≤ s ∧ (s : ℝ) / D n ≤ L ∧ (t : ℝ) / ((s : ℝ) * D n) ≤ T ∧
        epsilon < |F n s t| ∧ 0 < D n := by
    apply hf.mono
    intro n hn
    push Not at hn
    rcases hn with ⟨⟨s, t, hspos, hs, ht, hbad⟩, hD'⟩
    exact ⟨s, t, hspos, hs, ht, hbad, hD'⟩
  rcases extraction_of_frequently_atTop hf' with ⟨g, hg, hbad⟩
  choose s t hspos hs ht hbad hDpos using hbad
  let z : ℕ → ℝ × ℝ := fun j ↦ ((s j : ℝ) / D (g j), (t j : ℝ) / ((s j : ℝ) * D (g j)))
  have hz : ∀ j, z j ∈ Icc (0 : ℝ) L ×ˢ Icc (0 : ℝ) T := by
    intro j
    exact ⟨⟨div_nonneg (Nat.cast_nonneg _) (hDpos j).le, hs j⟩,
      ⟨div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hDpos j).le), ht j⟩⟩
  rcases (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hz with
    ⟨w, hw, phi, hphi, hwlim⟩
  have hx : Tendsto (fun j ↦ (s (phi j) : ℝ) / D (g (phi j))) atTop (𝓝 w.1) := by
    convert (continuous_fst.tendsto w).comp hwlim using 1
    ext j
    rfl
  have hz' : Tendsto (fun j ↦ (t (phi j) : ℝ) / ((s (phi j) : ℝ) * D (g (phi j))))
      atTop (𝓝 w.2) := by
    convert (continuous_snd.tendsto w).comp hwlim using 1
    ext j
    rfl
  rcases exists_positive_natSequence_extension_of_div_tendsto hD (hg.comp hphi) hw.1.1
      (fun j ↦ hspos (phi j)) hx with ⟨v, hv, hvpos, hvlim⟩
  have hE : Tendsto (fun n ↦ (v n : ℝ) * D n) atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ hD
    filter_upwards [hD.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    have hp : (1 : ℝ) ≤ v n := by exact_mod_cast hvpos n
    nlinarith
  have hz'' : Tendsto (fun j ↦ (t (phi j) : ℝ) / ((v ((g ∘ phi) j) : ℝ) * D ((g ∘ phi) j)))
      atTop (𝓝 w.2) := by
    convert hz' using 1
    ext j
    rw [hv j]
    rfl
  rcases exists_natSequence_extension_of_div_tendsto hE (hg.comp hphi) hw.2.1 hz'' with
    ⟨u, hu, hulim⟩
  have hlim := (hseq v u w.1 w.2 hw.1.1 hw.2.1 (Eventually.of_forall hvpos) hvlim hulim).comp
    (hg.comp hphi).tendsto_atTop
  have hlim' : Tendsto (fun j ↦ F (g (phi j)) (s (phi j)) (t (phi j))) atTop (𝓝 0) := by
    convert hlim using 1
    ext j
    have hv' := hv j
    have hu' := hu j
    change v (g (phi j)) = s (phi j) at hv'
    change u (g (phi j)) = t (phi j) at hu'
    simp only [Function.comp_apply, hv', hu']
  have habs := hlim'.abs
  simp only [abs_zero] at habs
  rcases (habs.eventually (Iio_mem_nhds hepsilon)).exists with ⟨j, hj⟩
  exact (not_lt_of_ge (hbad (phi j)).le) hj

end DenseGraph
