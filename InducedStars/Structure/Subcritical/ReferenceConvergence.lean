import InducedStars.Structure.Subcritical.Reference

/-!
# Convergence of the full sampled candidate reference

The approximation concerns the explicit block kernel, not an arbitrary
representative of a graphon. A fixed finite prefix is stable away from its
finitely many cell endpoints; the full reference is recovered by a separate
uniform bound on sampled tail squares.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal unitInterval Classical

namespace InducedStars

/-- Project a point to the midpoint of its equal cell. At a point outside
all equal cells (including the `n=0` case), leave it unchanged. -/
def subcriticalMidpointProjection (n : ℕ) (x : UnitInterval) : UnitInterval :=
  if h : ∃ i : Fin n, x ∈ equalCell i then
    subcriticalReferenceSamplePoint h.choose else x

theorem subcriticalMidpointProjection_eq_of_mem {n : ℕ} {x : UnitInterval}
    (i : Fin n) (hi : x ∈ equalCell i) :
    subcriticalMidpointProjection n x = subcriticalReferenceSamplePoint i := by
  have h : ∃ j : Fin n, x ∈ equalCell j := ⟨i, hi⟩
  have he : h.choose = i := equalCell_eq_of_mem h.choose_spec hi
  simp only [subcriticalMidpointProjection, dif_pos h, he]

theorem dist_subcriticalMidpointProjection_le (n : ℕ) (x : UnitInterval) :
    dist (subcriticalMidpointProjection n x) x ≤ 1 / (n : ℝ) := by
  by_cases h : ∃ i : Fin n, x ∈ equalCell i
  · obtain ⟨i, hi⟩ := h
    rw [subcriticalMidpointProjection_eq_of_mem i hi]
    have hs := subcriticalReferenceSamplePoint_mem_equalCell i
    change (i : ℝ) / n ≤ (x : ℝ) ∧ (x : ℝ) < ((i : ℝ) + 1) / n at hi
    change (i : ℝ) / n ≤ (subcriticalReferenceSamplePoint i : ℝ) ∧
      (subcriticalReferenceSamplePoint i : ℝ) < ((i : ℝ) + 1) / n at hs
    change |(subcriticalReferenceSamplePoint i : ℝ) - (x : ℝ)| ≤ 1 / (n : ℝ)
    have he : ((i : ℝ) + 1) / n = (i : ℝ) / n + 1 / n := add_div _ _ _
    rw [abs_le]
    constructor <;> linarith
  · simp only [subcriticalMidpointProjection, dif_neg h, dist_self]
    positivity

theorem subcriticalMidpointProjection_tendsto (x : UnitInterval) :
    Tendsto (fun n ↦ subcriticalMidpointProjection n x) atTop (𝓝 x) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ ↦ dist_nonneg)
    (fun n ↦ dist_subcriticalMidpointProjection_le n x)
    tendsto_one_div_atTop_nhds_zero_nat

private theorem eventually_mem_Ico_iff_of_tendsto
    {f : ℕ → UnitInterval} {x a b : UnitInterval}
    (hf : Tendsto f atTop (𝓝 x)) (ha : x ≠ a) (hb : x ≠ b) :
    ∀ᶠ n in atTop, f n ∈ Ico a b ↔ x ∈ Ico a b := by
  by_cases hax : a ≤ x
  · have hax' : a < x := lt_of_le_of_ne hax ha.symm
    have heA := (tendsto_order.1 hf).1 a hax'
    by_cases hxb : x < b
    · filter_upwards [heA, (tendsto_order.1 hf).2 b hxb] with n hnA hnB
      simp only [mem_Ico]
      exact iff_of_true ⟨hnA.le, hnB⟩ ⟨hax, hxb⟩
    · have hbx : b < x := lt_of_le_of_ne (le_of_not_gt hxb) hb.symm
      filter_upwards [(tendsto_order.1 hf).1 b hbx] with n hn
      simp only [mem_Ico]
      constructor
      · intro h
        exact (not_lt_of_ge hn.le h.2).elim
      · intro h
        exact (hxb h.2).elim
  · have hxa : x < a := lt_of_not_ge hax
    filter_upwards [(tendsto_order.1 hf).2 a hxa] with n hn
    simp only [mem_Ico]
    constructor
    · intro h
      exact (not_lt_of_ge h.1 hn).elim
    · intro h
      exact (hax h.1).elim

namespace FiniteProfileBlockLayout

variable {k : ℕ} (A : FiniteProfileBlockLayout k)

/-- Sample a fixed finite layout on the same midpoint grid as the full
candidate reference. This is used only for its approximation proof. -/
def sampledWeightedGraph (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    DenseGraph.FiniteWeightedGraph (Fin n) where
  weight x y := A.kernel p (subcriticalReferenceSamplePoint x, subcriticalReferenceSamplePoint y)
  symmetric x y := (A.kernel_symm p _).symm
  nonneg x y := A.kernel_nonneg hp.1 _
  le_one x y := A.kernel_le_one hp.2 _

theorem sampledWeightedGraph_kernel_eq_projection
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) {n : ℕ} (hn : 0 < n)
    (z : UnitSquare) (hx : (z.1 : ℝ) < 1) (hy : (z.2 : ℝ) < 1) :
    matrixKernel (A.sampledWeightedGraph p hp n).weight z =
      A.kernel p (subcriticalMidpointProjection n z.1, subcriticalMidpointProjection n z.2) := by
  obtain ⟨i, hi⟩ := exists_mem_equalCell_lt_one hn z.1 hx
  obtain ⟨j, hj⟩ := exists_mem_equalCell_lt_one hn z.2 hy
  rw [matrixKernel_of_mem _ i j z hi hj,
    subcriticalMidpointProjection_eq_of_mem i hi,
    subcriticalMidpointProjection_eq_of_mem j hj]
  rfl

theorem kernel_projection_eventually_eq (p : ℝ) (z : UnitSquare)
    (hx : ∀ (i : Fin A.count) (v : Fin (A.core i).order),
      z.1 ≠ A.cellLeftUI i v ∧ z.1 ≠ A.cellRightUI i v)
    (hy : ∀ (i : Fin A.count) (v : Fin (A.core i).order),
      z.2 ≠ A.cellLeftUI i v ∧ z.2 ≠ A.cellRightUI i v) :
    ∀ᶠ n in atTop,
      A.kernel p (subcriticalMidpointProjection n z.1, subcriticalMidpointProjection n z.2) =
        A.kernel p z := by
  have hleft : ∀ᶠ n in atTop, ∀ (i : Fin A.count) (v : Fin (A.core i).order),
      subcriticalMidpointProjection n z.1 ∈ A.blockCell i v ↔ z.1 ∈ A.blockCell i v := by
    apply Filter.eventually_all.2
    intro i
    apply Filter.eventually_all.2
    intro v
    exact eventually_mem_Ico_iff_of_tendsto (subcriticalMidpointProjection_tendsto z.1)
      (hx i v).1 (hx i v).2
  have hright : ∀ᶠ n in atTop, ∀ (i : Fin A.count) (v : Fin (A.core i).order),
      subcriticalMidpointProjection n z.2 ∈ A.blockCell i v ↔ z.2 ∈ A.blockCell i v := by
    apply Filter.eventually_all.2
    intro i
    apply Filter.eventually_all.2
    intro v
    exact eventually_mem_Ico_iff_of_tendsto (subcriticalMidpointProjection_tendsto z.2)
      (hy i v).1 (hy i v).2
  filter_upwards [hleft, hright] with n hnL hnR
  unfold kernel
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  simp only [Set.indicator_apply, Set.mem_prod, hnL i v, hnR i w]

theorem sampledWeightedGraph_graphonL1Dist_tendsto_zero
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n ↦ graphonL1Dist (A.sampledWeightedGraph p hp n).toGraphon
      (A.graphon p hp)) atTop (𝓝 0) := by
  have havoid : ∀ᵐ x : UnitInterval ∂volume,
      x ≠ 1 ∧ ∀ (i : Fin A.count) (v : Fin (A.core i).order),
        x ≠ A.cellLeftUI i v ∧ x ≠ A.cellRightUI i v := by
    apply (Measure.ae_ne _ _).and
    apply ae_all_iff.2
    intro i
    apply ae_all_iff.2
    intro v
    exact (Measure.ae_ne _ _).and (Measure.ae_ne _ _)
  have hleft := (measurePreserving_fst (μ := (volume : Measure UnitInterval))
    (ν := (volume : Measure UnitInterval))).quasiMeasurePreserving.ae havoid
  have hright := (measurePreserving_snd (μ := (volume : Measure UnitInterval))
    (ν := (volume : Measure UnitInterval))).quasiMeasurePreserving.ae havoid
  have hkernel : ∀ᵐ z ∂unitSquareMeasure, ∀ n : ℕ,
      (A.sampledWeightedGraph p hp n).toGraphon z =
        matrixKernel (A.sampledWeightedGraph p hp n).weight z := by
    apply ae_all_iff.2
    intro n
    exact matrixGraphon_ae_eq_kernel _ _ _ _
  apply graphonL1Dist_tendsto_zero_of_ae
  filter_upwards [hleft, hright, hkernel, A.graphon_ae_eq_kernel p hp]
    with z hzL hzR hzK hzA
  have hx : (z.1 : ℝ) < 1 := lt_of_le_of_ne z.1.property.2
    (fun h ↦ hzL.1 (Subtype.ext h))
  have hy : (z.2 : ℝ) < 1 := lt_of_le_of_ne z.2.property.2
    (fun h ↦ hzR.1 (Subtype.ext h))
  apply tendsto_const_nhds.congr'
  filter_upwards [A.kernel_projection_eventually_eq p z hzL.2 hzR.2,
    eventually_gt_atTop 0] with n hn hnpos
  rw [hzK n, A.sampledWeightedGraph_kernel_eq_projection p hp hnpos z hx hy, hn]
  exact hzA

end FiniteProfileBlockLayout

/-- Sampling the full candidate and sampling a fixed prefix differ only on
sampled tail-block squares. Their total area is controlled row by row,
without accumulating one rounding error per omitted component. -/
theorem graphonL1Dist_subcriticalReference_sampledPrefix_le
    {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n)
    (L : AdmissibleBlockSequence k) (N : ℕ) :
    graphonL1Dist (subcriticalReferenceGraphon hk L n)
      ((FiniteProfileBlockLayout.ofPrefix L N).sampledWeightedGraph
        (pK k) (pK_mem_Icc k) n).toGraphon ≤ L.alpha N + 1 / (n : ℝ) := by
  let A := subcriticalReferenceWeightedGraph hk L n
  let B := (FiniteProfileBlockLayout.ofPrefix L N).sampledWeightedGraph
    (pK k) (pK_mem_Icc k) n
  let C : DenseGraph.FiniteWeightedGraph (Fin n) := {
    weight := fun x y ↦ if (x, y) ∈ subcriticalReferenceTailPairFinset L n N then 1 else 0
    symmetric := by
      intro x y
      have he : (x, y) ∈ subcriticalReferenceTailPairFinset L n N ↔
          (y, x) ∈ subcriticalReferenceTailPairFinset L n N := by
        simp only [mem_subcriticalReferenceTailPairFinset_iff]
        constructor <;> rintro ⟨i, hi, hx, hy⟩ <;> exact ⟨i, hi, hy, hx⟩
      simp only [he]
    nonneg := by intro x y; split_ifs <;> norm_num
    le_one := by intro x y; split_ifs <;> norm_num }
  have hpair (x y : Fin n) : |A.weight x y - B.weight x y| ≤ C.weight x y := by
    by_cases h : (x, y) ∈ subcriticalReferenceTailPairFinset L n N
    · change |A.weight x y - B.weight x y| ≤ if _ then 1 else 0
      rw [if_pos h, abs_le]
      constructor <;> linarith [A.nonneg x y, A.le_one x y, B.nonneg x y, B.le_one x y]
    · change |A.weight x y - B.weight x y| ≤ if _ then 1 else 0
      rw [if_neg h]
      have ht : (subcriticalReferenceSamplePoint x, subcriticalReferenceSamplePoint y) ∉
          FiniteProfileBlockLayout.tailBlockSquares L N := by simpa using h
      have he := FiniteProfileBlockLayout.kernel_ofPrefix_eq_profileKernel_of_not_mem_tailBlockSquares
        hk (pK k) L N _ ht
      change |L.profileKernel (pK k) _ - (FiniteProfileBlockLayout.ofPrefix L N).kernel (pK k) _| ≤ 0
      rw [he, sub_self, abs_zero]
  have hdist : graphonL1Dist A.toGraphon B.toGraphon ≤ graphonEdgeDensity C.toGraphon := by
    rw [graphonL1Dist_eq_integral, graphonEdgeDensity_eq_integral]
    apply integral_mono_ae (A.toGraphon.integrable.sub B.toGraphon.integrable).abs
      C.toGraphon.integrable
    filter_upwards [matrixGraphon_ae_eq_kernel A.weight A.weight_isSymm A.nonneg A.le_one,
      matrixGraphon_ae_eq_kernel B.weight B.weight_isSymm B.nonneg B.le_one,
      matrixGraphon_ae_eq_kernel C.weight C.weight_isSymm C.nonneg C.le_one,
      ae_mem_iUnion_equalCell_prod hn] with z hzA hzB hzC hz
    obtain ⟨⟨i, j⟩, hi, hj⟩ := Set.mem_iUnion.mp hz
    change |A.toGraphon z - B.toGraphon z| ≤ C.toGraphon z
    unfold DenseGraph.FiniteWeightedGraph.toGraphon
    rw [hzA, hzB, hzC, matrixKernel_of_mem A.weight i j z hi hj,
      matrixKernel_of_mem B.weight i j z hi hj, matrixKernel_of_mem C.weight i j z hi hj]
    exact hpair i j
  have hmass : graphonEdgeDensity C.toGraphon =
      (1 / (n : ℝ)) ^ 2 * (subcriticalReferenceTailPairFinset L n N).card := by
    rw [DenseGraph.FiniteWeightedGraph.toGraphon, graphonEdgeDensity_matrixGraphon hn]
    congr 1
    change (∑ x : Fin n, ∑ y : Fin n,
      if (x, y) ∈ subcriticalReferenceTailPairFinset L n N then (1 : ℝ) else 0) = _
    calc
      _ = ∑ z : Fin n × Fin n,
          if z ∈ subcriticalReferenceTailPairFinset L n N then (1 : ℝ) else 0 :=
        (Fintype.sum_prod_type _).symm
      _ = _ := by simp [subcriticalReferenceTailPairFinset]
  exact hdist.trans (hmass.le.trans (subcriticalReferenceTailPairProportion_le hn L))

/-- The full finite reference converges in `L¹` to the explicit candidate,
for both finite and infinite admissible sequences. The fixed-prefix and
sampled-tail estimates account separately for all rounding and endpoints. -/
theorem graphonL1Dist_subcriticalReferenceGraphon_WLambda_tendsto_zero
    {k : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k) :
    Tendsto (fun n ↦ graphonL1Dist (subcriticalReferenceGraphon hk L n)
      (WLambda hk L)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n ↦ ha.trans_le (graphonL1Dist_nonneg _ _)
  · intro epsilon hepsilon
    have hsmall : ∀ᶠ N : ℕ in atTop,
        1 / ((N + 1 : ℕ) : ℝ) < epsilon / 4 := by
      have ht : Tendsto (fun N : ℕ ↦ 1 / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact (tendsto_order.1 ht).2 _ (by positivity)
    obtain ⟨N, hN⟩ := hsmall.exists
    let P := FiniteProfileBlockLayout.ofPrefix L N
    have hpref : ∀ᶠ n in atTop,
        graphonL1Dist (P.sampledWeightedGraph (pK k) (pK_mem_Icc k) n).toGraphon
          (P.graphon (pK k) (pK_mem_Icc k)) < epsilon / 4 :=
      (tendsto_order.1 (P.sampledWeightedGraph_graphonL1Dist_tendsto_zero
        (pK k) (pK_mem_Icc k))).2 _ (by positivity)
    have hinv : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < epsilon / 4 :=
      (tendsto_order.1 (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).2 _ (by positivity)
    have htail : graphonL1Dist (P.graphon (pK k) (pK_mem_Icc k)) (WLambda hk L) ≤
        L.alphaSquareTail N := by
      rw [graphonL1Dist_comm, ← profileWLambda_pK hk L]
      exact FiniteProfileBlockLayout.graphonL1Dist_profileWLambda_graphon_ofPrefix_le_alphaSquareTail
        hk (pK k) (pK_mem_Icc k) L N
    filter_upwards [hpref, hinv, eventually_gt_atTop 0] with n hnP hnInv hn
    have hs := graphonL1Dist_subcriticalReference_sampledPrefix_le hk hn L N
    have ht₁ := graphonL1Dist_triangle (subcriticalReferenceGraphon hk L n)
      (P.sampledWeightedGraph (pK k) (pK_mem_Icc k) n).toGraphon (WLambda hk L)
    have ht₂ := graphonL1Dist_triangle
      (P.sampledWeightedGraph (pK k) (pK_mem_Icc k) n).toGraphon
      (P.graphon (pK k) (pK_mem_Icc k)) (WLambda hk L)
    have ha := L.alpha_le_inv_succ N
    have htail' := L.alphaSquareTail_le_inv_succ N
    change graphonL1Dist (subcriticalReferenceGraphon hk L n)
      (P.sampledWeightedGraph (pK k) (pK_mem_Icc k) n).toGraphon ≤ _ at hs
    linarith

/-- Cut convergence is inherited from the stronger `L¹` convergence. -/
theorem subcriticalReferenceGraphon_tendsto_WLambda
    {k : ℕ} (hk : 3 ≤ k) (L : AdmissibleBlockSequence k) :
    Tendsto (fun n ↦ cutDist (subcriticalReferenceGraphon hk L n)
      (WLambda hk L)) atTop (𝓝 0) :=
  squeeze_zero (fun _ ↦ cutDist_nonneg _ _)
    (fun _ ↦ cutDist_le_graphonL1Dist _ _)
    (graphonL1Dist_subcriticalReferenceGraphon_WLambda_tendsto_zero hk L)

end InducedStars
