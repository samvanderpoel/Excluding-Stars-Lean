import InducedStars.C4.DefectModels
import InducedStars.PriorInstances

/-!
# Two-coordinate Janson calculation for the high-degree independent side

Paper: Lemma `lemma:FPi1`, Case 2. A candidate consists of an edge of a
graph on the defect neighborhood (representing a nonedge of the defect)
and one vertex of the frozen nonneighbor set. Each event requires just
two remaining cross coordinates. The dependency sum is unordered.
-/

noncomputable section
open Finset
open scoped Classical

namespace InducedStars

universe u z w
variable {U : Type u} {Z : Type z} {Ω : Type w} [Fintype U] [DecidableEq U]
  [Fintype Z] [DecidableEq Z] [Fintype Ω] [DecidableEq Ω]

abbrev C4StarCandidate (H : SimpleGraph U) (Z : Type*) := ↥(finiteGraphEdges H) × Z

namespace C4StarCandidate

variable (H : SimpleGraph U) (f : (U × Z) ↪ Ω)

def coordinateEmbedding (z : Z) : U ↪ Ω :=
  ⟨fun x ↦ f (x, z), fun x y h ↦ (Prod.mk.inj (f.injective h)).1⟩

def required (i : C4StarCandidate H Z) : Finset Ω :=
  i.1.val.toFinset.map (coordinateEmbedding f i.2)

theorem mem_required (i : C4StarCandidate H Z) (c : Ω) :
    c ∈ required H f i ↔ ∃ x ∈ i.1.val, f (x, i.2) = c := by
  simp only [required, Finset.mem_map, Sym2.mem_toFinset, coordinateEmbedding,
    Function.Embedding.coeFn_mk]
  rfl

@[simp] theorem card_required (i : C4StarCandidate H Z) : (required H f i).card = 2 := by
  rw [required, Finset.card_map]
  exact Sym2.card_toFinset_of_not_isDiag _
    (H.not_isDiag_of_mem_edgeSet ((mem_finiteGraphEdges _ _).mp i.1.prop))

def incidenceFiber (x : U) (z : Z) : Finset (C4StarCandidate H Z) :=
  univ.filter fun i ↦ x ∈ i.1.val ∧ i.2 = z

theorem card_incidenceFiber_le (x : U) (z : Z) :
    (incidenceFiber H x z).card ≤ Fintype.card U := by
  have hcard : (incidenceFiber H x z).card ≤ (H.incidenceFinset x).card := by
    apply Finset.card_le_card_of_injOn (fun i : C4StarCandidate H Z ↦ i.1.val)
    · intro i hi
      have hx := (Finset.mem_filter.mp hi).2.1
      change i.1.val ∈ H.incidenceFinset x
      rw [SimpleGraph.mem_incidenceFinset]
      exact ⟨(mem_finiteGraphEdges _ _).mp i.1.prop, hx⟩
    · intro i hi j hj hij
      exact Prod.ext (Subtype.ext hij)
        ((Finset.mem_filter.mp hi).2.2.trans (Finset.mem_filter.mp hj).2.2.symm)
  rw [SimpleGraph.card_incidenceFinset_eq_degree] at hcard
  by_cases hU : Nonempty U
  · exact hcard.trans (H.degree_lt_card_verts x).le
  · exact False.elim (hU ⟨x⟩)

def overlaps (i : C4StarCandidate H Z) : Finset (C4StarCandidate H Z) :=
  univ.filter fun j ↦ ¬Disjoint (required H f i) (required H f j)

theorem overlaps_subset_incidence (i : C4StarCandidate H Z) :
    overlaps H f i ⊆ i.1.val.toFinset.biUnion (fun x ↦ incidenceFiber H x i.2) := by
  intro j hj
  obtain ⟨c, hci, hcj⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hj).2
  obtain ⟨x, hx, hxi⟩ := (mem_required H f i c).mp hci
  obtain ⟨y, hy, hyj⟩ := (mem_required H f j c).mp hcj
  have hpair := f.injective (hxi.trans hyj.symm)
  have hxy : x = y := (Prod.mk.inj hpair).1
  have hz : j.2 = i.2 := (Prod.mk.inj hpair).2.symm
  refine Finset.mem_biUnion.mpr ⟨x, by simpa using hx, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy ▸ hy, hz⟩

theorem card_overlaps_le (i : C4StarCandidate H Z) :
    (overlaps H f i).card ≤ 2 * Fintype.card U := by
  have htwo : i.1.val.toFinset.card = 2 := by
    simpa only [required, Finset.card_map] using card_required H f i
  calc
    _ ≤ (i.1.val.toFinset.biUnion (fun x ↦ incidenceFiber H x i.2)).card :=
      Finset.card_le_card (overlaps_subset_incidence H f i)
    _ ≤ ∑ x ∈ i.1.val.toFinset, (incidenceFiber H x i.2).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ i.1.val.toFinset, Fintype.card U :=
      Finset.sum_le_sum (fun x _ ↦ card_incidenceFiber_le H x i.2)
    _ = _ := by simp [htwo, Nat.mul_comm]

theorem card_unorderedOverlappingPairs_le [LinearOrder (C4StarCandidate H Z)] :
    (DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs (required H f)).card ≤
      2 * Fintype.card U * (finiteGraphEdges H).card * Fintype.card Z := by
  let E : Finset (C4StarCandidate H Z × C4StarCandidate H Z) :=
    univ.biUnion fun i ↦ (overlaps H f i).map
      ⟨fun j ↦ (i, j), fun _ _ heq ↦ (Prod.mk.inj heq).2⟩
  have hsub : DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs (required H f) ⊆ E := by
    intro ij hij
    have ho := (DenseGraph.FiniteBernoulliProduct.mem_unorderedOverlappingPairs
      (required H f) ij.1 ij.2).mp hij
    exact Finset.mem_biUnion.mpr ⟨ij.1, Finset.mem_univ _,
      Finset.mem_map.mpr ⟨ij.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho.2⟩, rfl⟩⟩
  calc
    _ ≤ E.card := Finset.card_le_card hsub
    _ ≤ ∑ i : C4StarCandidate H Z, (overlaps H f i).card := by
      simpa [E] using (Finset.card_biUnion_le (s := (univ : Finset (C4StarCandidate H Z)))
        (t := fun i ↦ (overlaps H f i).map
          ⟨fun j ↦ (i, j), fun _ _ heq ↦ (Prod.mk.inj heq).2⟩))
    _ ≤ ∑ _i : C4StarCandidate H Z, 2 * Fintype.card U :=
      Finset.sum_le_sum (fun i _ ↦ card_overlaps_le H f i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_coe,
        nsmul_eq_mul, Nat.cast_id]
      ring

theorem principal_probability_ge (P : DenseGraph.FiniteBernoulliProduct Ω)
    {beta : ℝ} (hbeta : 0 ≤ beta) (hband : ∀ c, beta ≤ P.probability c)
    (i : C4StarCandidate H Z) :
    beta ^ 2 ≤ P.eventProbability (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent
      (required H f i)) := by
  rw [P.eventProbability_principalSuccessEvent]
  calc
    beta ^ 2 = ∏ _c ∈ required H f i, beta := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ ↦ hbeta) (fun c _ ↦ hband c)

theorem mu_lower [LinearOrder (C4StarCandidate H Z)]
    (P : DenseGraph.FiniteBernoulliProduct Ω) {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : ∀ c, beta ≤ P.probability c) :
    beta ^ 2 * (finiteGraphEdges H).card * Fintype.card Z ≤
      P.principalJansonMu (required H f) := by
  calc
    _ = ∑ _i : C4StarCandidate H Z, beta ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_coe,
        nsmul_eq_mul, Nat.cast_mul]
      ring
    _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ principal_probability_ge H f P hbeta hband i)

/-- The unordered dependency sum is bounded by its actual overlap count.
This compact-band version does not need the optional extra factor `p³`. -/
theorem delta_upper [LinearOrder (C4StarCandidate H Z)]
    (P : DenseGraph.FiniteBernoulliProduct Ω) :
    P.principalJansonDelta (required H f) ≤
      2 * Fintype.card U * (finiteGraphEdges H).card * Fintype.card Z := by
  calc
    _ ≤ ∑ _ij ∈ DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs (required H f), (1 : ℝ) :=
      Finset.sum_le_sum (fun ij _ ↦ P.eventProbability_le_one _)
    _ = ((DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs (required H f)).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast card_unorderedOverlappingPairs_le H f

private theorem janson_scalar_reserves {beta s e z mu delta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hs : 1 ≤ s) (hz : 0 < z)
    (he : s ^ 2 / 8 ≤ e) (hmu : beta ^ 2 * e * z ≤ mu)
    (hdelta : delta ≤ 2 * s * e * z) :
    beta ^ 4 / 64 * s * z ≤ mu / 2 ∧
      (0 < delta → beta ^ 4 / 64 * s * z ≤ mu ^ 2 / (4 * delta)) := by
  have hs0 : 0 < s := by linarith
  have he0 : 0 < e := by nlinarith
  have hmu0 : 0 < mu := (mul_pos (mul_pos (sq_pos_of_pos hbeta) he0) hz).trans_le hmu
  have hbeta2 : beta ^ 2 ≤ 1 := by nlinarith
  have hbeta4 : beta ^ 4 ≤ beta ^ 2 := by nlinarith [sq_nonneg (beta ^ 2 - 1)]
  have hs2 : s ≤ s ^ 2 := by nlinarith
  have hlinear : beta ^ 4 / 64 * s * z ≤ beta ^ 2 * e * z / 8 := by
    calc
      _ ≤ beta ^ 2 / 64 * s ^ 2 * z := by gcongr
      _ ≤ beta ^ 2 / 64 * (8 * e) * z := by gcongr; linarith
      _ = _ := by ring
  constructor
  · linarith
  · intro hd
    apply (le_div_iff₀ (mul_pos (by norm_num) hd)).mpr
    calc
      _ ≤ (beta ^ 4 / 64 * s * z) * (4 * (2 * s * e * z)) := by gcongr
      _ = beta ^ 4 * (s ^ 2) * e * z ^ 2 / 8 := by ring
      _ ≤ beta ^ 4 * (8 * e) * e * z ^ 2 / 8 := by gcongr; linarith
      _ = (beta ^ 2 * e * z) ^ 2 := by ring
      _ ≤ mu ^ 2 := (sq_le_sq₀ (by positivity) hmu0.le).mpr hmu

set_option maxHeartbeats 1000000 in
/-- The exact two-edge principal-event calculation, including an explicit
zero-dependency branch. Its exponent is proportional to neighborhood size
times frozen-set size, as required for `alpha²*n²`. -/
theorem avoidance_le [LinearOrder (C4StarCandidate H Z)]
    (J : DenseGraph.PrincipalJansonInput.{w, max u z})
    (P : DenseGraph.FiniteBernoulliProduct Ω) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1)
    (hband : ∀ c, beta ≤ P.probability c)
    (hU : 1 ≤ Fintype.card U) (hZ : 0 < Fintype.card Z)
    (hdense : (Fintype.card U : ℝ) ^ 2 / 8 ≤ (finiteGraphEdges H).card) :
    P.eventProbability (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent (required H f)) ≤
      Real.exp (-(beta ^ 4 / 64) * Fintype.card U * Fintype.card Z) := by
  have hmean := mu_lower H f P hbeta.le hband
  have hdep := delta_upper H f P
  have hUR : (1 : ℝ) ≤ Fintype.card U := by exact_mod_cast hU
  have hZR : (0 : ℝ) < Fintype.card Z := by exact_mod_cast hZ
  have hepos : (0 : ℝ) < (finiteGraphEdges H).card := by nlinarith
  have hmpos : 0 < P.principalJansonMu (required H f) :=
    (mul_pos (mul_pos (sq_pos_of_pos hbeta) hepos) hZR).trans_le hmean
  obtain ⟨hmreserve, hdreserve⟩ := janson_scalar_reserves hbeta hbeta1 hUR hZR hdense hmean hdep
  by_cases hd : P.principalJansonDelta (required H f) = 0
  · have h := J.principalJanson_avoidance_le_exp_neg_of_delta_eq_zero P (required H f) hmpos hd
    refine h.trans (Real.exp_le_exp.mpr ?_)
    nlinarith
  · have hdpos := lt_of_le_of_ne (P.principalJansonDelta_nonneg (required H f)) (Ne.symm hd)
    have h := J.principalJanson_avoidance_le_exp_neg_min P (required H f) hmpos hdpos
    refine h.trans (Real.exp_le_exp.mpr ?_)
    have hmin := le_min hmreserve (hdreserve hdpos)
    nlinarith

end C4StarCandidate
end InducedStars
