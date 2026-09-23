import DenseGraph.Combinatorics.SequenceExtension

/-!
# Uniformity of sequential finite-model estimates
-/

noncomputable section

open Filter Set Topology

namespace DenseGraph

/-- A sequential estimate for every pair of normalized natural-valued
sequences is uniform on each compact rectangle of normalized parameters.
The extension lemma preserves the natural values on every extracted
subsequence, so no stronger reindexing hypothesis is hidden here. -/
theorem eventually_uniform_of_normalizedSequences_tendsto_zero
    {D E : ℕ → ℝ} (hD : Tendsto D atTop atTop) (hE : Tendsto E atTop atTop)
    {F : ℕ → ℕ → ℕ → ℝ}
    (hseq : ∀ (s t : ℕ → ℕ) (x y : ℝ), 0 ≤ x → 0 ≤ y →
      Tendsto (fun n ↦ (s n : ℝ) / D n) atTop (𝓝 x) →
      Tendsto (fun n ↦ (t n : ℝ) / E n) atTop (𝓝 y) →
      Tendsto (fun n ↦ F n (s n) (t n)) atTop (𝓝 0))
    (L T : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ s t : ℕ,
      (s : ℝ) / D n ≤ L → (t : ℝ) / E n ≤ T → |F n s t| ≤ epsilon := by
  classical
  by_contra h
  have hf := (not_eventually.mp h).and_eventually
    ((hD.eventually (eventually_gt_atTop (0 : ℝ))).and
      (hE.eventually (eventually_gt_atTop (0 : ℝ))))
  have hf' : ∃ᶠ n : ℕ in atTop, ∃ s t : ℕ,
      (s : ℝ) / D n ≤ L ∧ (t : ℝ) / E n ≤ T ∧ epsilon < |F n s t| ∧
        0 < D n ∧ 0 < E n := by
    apply hf.mono
    intro n hn
    push Not at hn
    rcases hn with ⟨⟨s, t, hs, ht, hbad⟩, hD', hE'⟩
    exact ⟨s, t, hs, ht, hbad, hD', hE'⟩
  rcases extraction_of_frequently_atTop hf' with ⟨g, hg, hbad⟩
  choose s t hs ht hbad hDpos hEpos using hbad
  let z : ℕ → ℝ × ℝ := fun j ↦ ((s j : ℝ) / D (g j), (t j : ℝ) / E (g j))
  have hz : ∀ j, z j ∈ Icc (0 : ℝ) L ×ˢ Icc (0 : ℝ) T := by
    intro j
    exact ⟨⟨div_nonneg (Nat.cast_nonneg _) (hDpos j).le, hs j⟩,
      ⟨div_nonneg (Nat.cast_nonneg _) (hEpos j).le, ht j⟩⟩
  rcases (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hz with
    ⟨w, hw, phi, hphi, hwlim⟩
  have hx : Tendsto (fun j ↦ (s (phi j) : ℝ) / D (g (phi j))) atTop (𝓝 w.1) :=
    by
      convert (continuous_fst.tendsto w).comp hwlim using 1
      ext j
      rfl
  have hy : Tendsto (fun j ↦ (t (phi j) : ℝ) / E (g (phi j))) atTop (𝓝 w.2) :=
    by
      convert (continuous_snd.tendsto w).comp hwlim using 1
      ext j
      rfl
  rcases exists_natSequence_extension_of_div_tendsto hD (hg.comp hphi) hw.1.1 hx with
    ⟨v, hv, hvlim⟩
  rcases exists_natSequence_extension_of_div_tendsto hE (hg.comp hphi) hw.2.1 hy with
    ⟨u, hu, hulim⟩
  have hlim := (hseq v u w.1 w.2 hw.1.1 hw.2.1 hvlim hulim).comp
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

/-- An eventual finite property along every normalized sequence is
uniform on every compact rectangle of normalized parameters. -/
theorem eventually_uniform_of_normalizedSequences_eventually
    {D E : ℕ → ℝ} (hD : Tendsto D atTop atTop) (hE : Tendsto E atTop atTop)
    {P : ℕ → ℕ → ℕ → Prop}
    (hseq : ∀ (s t : ℕ → ℕ) (x y : ℝ), 0 ≤ x → 0 ≤ y →
      Tendsto (fun n ↦ (s n : ℝ) / D n) atTop (𝓝 x) →
      Tendsto (fun n ↦ (t n : ℝ) / E n) atTop (𝓝 y) →
      ∀ᶠ n : ℕ in atTop, P n (s n) (t n)) (L T : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ s t : ℕ,
      (s : ℝ) / D n ≤ L → (t : ℝ) / E n ≤ T → P n s t := by
  classical
  have h := eventually_uniform_of_normalizedSequences_tendsto_zero hD hE
    (F := fun n s t ↦ if P n s t then 0 else 1)
    (fun s t x y hx hy hs ht ↦ by
      apply (tendsto_const_nhds (x := (0 : ℝ))).congr'
      filter_upwards [hseq s t x y hx hy hs ht] with n hn
      simp only [hn, ↓reduceIte]) L T (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [h] with n hn
  intro s t hs ht
  by_contra hp
  have hh := hn s t hs ht
  norm_num [hp] at hh

end DenseGraph
