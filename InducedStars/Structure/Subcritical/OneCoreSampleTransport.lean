import InducedStars.Structure.Subcritical.OneCoreProfile
import InducedStars.Structure.Subcritical.CleanModelGeometry

/-!
# Fixed-cell sampling on a literal one-core retained support

The equivalence below transports individual unordered ambient edges to
oriented support coordinates. In particular, it preserves every cell quota,
not merely the total number of active edges.
-/

noncomputable section
open Finset Set
open scoped Classical BigOperators
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

def oneCoreBlockCoordinate (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    {eta : ℝ} {R₀ : ℕ}
    (hret : (SubcriticalDivision.ofSupercritical hk D).retainedComponentIndices eta R₀ = Finset.univ)
    (v : RetainedEdgeCountVector (SubcriticalDivision.ofSupercritical hk D) eta R₀)
    (e : SupercriticalPartPair k)
    (z : ↥((supercriticalFixedProfileBlockModel D.onSupportFin
      (oneCoreProfile hk D hret v)).block e)) :
    ↥((retainedEdgeChoiceModel v).block (oneCoreRetainedPairEquiv hk D eta R₀ hret e)) := by
  refine ⟨s(D.supportVertex z.val.1, D.supportVertex z.val.2), ?_⟩
  apply (mem_retainedActivePotentialEdges _ eta R₀ _ _).mpr
  have hz := Finset.mem_product.mp z.property
  exact ⟨_, (D.mem_onSupportFin_part _ _).mp hz.1,
    _, (D.mem_onSupportFin_part _ _).mp hz.2, rfl⟩

theorem oneCoreBlockCoordinate_injective (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    {eta : ℝ} {R₀ : ℕ} (hret)
    (v : RetainedEdgeCountVector (SubcriticalDivision.ofSupercritical hk D) eta R₀)
    (e : SupercriticalPartPair k) :
    Function.Injective (oneCoreBlockCoordinate hk D hret v e) := by
  intro x y h
  have heq := congrArg Subtype.val h
  change s(D.supportVertex x.val.1, D.supportVertex x.val.2) =
    s(D.supportVertex y.val.1, D.supportVertex y.val.2) at heq
  rw [Sym2.eq_iff] at heq
  rcases heq with heq | heq
  · apply Subtype.ext
    exact Prod.ext (D.supportVertex_injective heq.1)
      (D.supportVertex_injective heq.2)
  · have hx := (Finset.mem_product.mp x.property).1
    have hy := (Finset.mem_product.mp y.property).2
    have hxy : x.val.1 = y.val.2 :=
      D.supportVertex_injective heq.1
    exact (e.left_ne_right
      (D.onSupportFin.mem_part_unique hx (hxy ▸ hy))).elim

theorem oneCoreBlockCoordinate_surjective (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    {eta : ℝ} {R₀ : ℕ} (hret)
    (v : RetainedEdgeCountVector (SubcriticalDivision.ofSupercritical hk D) eta R₀)
    (e : SupercriticalPartPair k) :
    Function.Surjective (oneCoreBlockCoordinate hk D hret v e) := by
  intro z
  obtain ⟨x, hx, y, hy, hz⟩ :=
    (mem_retainedActivePotentialEdges _ eta R₀ _ z.val).mp z.property
  have hx' : x ∈ D.parts e.left := hx
  have hy' : y ∈ D.parts e.right := hy
  let x' : Fin D.support.card :=
    D.supportLabelEquiv ⟨x, D.part_subset_support e.left hx'⟩
  let y' : Fin D.support.card :=
    D.supportLabelEquiv ⟨y, D.part_subset_support e.right hy'⟩
  have hxx : D.supportVertex x' = x := by simp [x', SupercriticalDivision.supportVertex]
  have hyy : D.supportVertex y' = y := by simp [y', SupercriticalDivision.supportVertex]
  have hxy : (x', y') ∈ (supercriticalFixedProfileBlockModel D.onSupportFin
      (oneCoreProfile hk D hret v)).block e := by
    apply Finset.mem_product.mpr
    constructor
    · exact (D.mem_onSupportFin_part _ _).mpr (hxx ▸ hx')
    · exact (D.mem_onSupportFin_part _ _).mpr (hyy ▸ hy')
  refine ⟨⟨(x', y'), hxy⟩, Subtype.ext ?_⟩
  change s(D.supportVertex x', D.supportVertex y') = z.val
  rw [hxx, hyy, hz]

def oneCoreBlockEquiv (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    {eta : ℝ} {R₀ : ℕ} (hret)
    (v : RetainedEdgeCountVector (SubcriticalDivision.ofSupercritical hk D) eta R₀)
    (e : SupercriticalPartPair k) :
    ↥((supercriticalFixedProfileBlockModel D.onSupportFin
      (oneCoreProfile hk D hret v)).block e) ≃
    ↥((retainedEdgeChoiceModel v).block (oneCoreRetainedPairEquiv hk D eta R₀ hret e)) :=
  Equiv.ofBijective (oneCoreBlockCoordinate hk D hret v e)
    ⟨oneCoreBlockCoordinate_injective hk D hret v e,
      oneCoreBlockCoordinate_surjective hk D hret v e⟩

def oneCoreProfileSampleEquiv (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    {eta : ℝ} {R₀ : ℕ} (hret)
    (v : RetainedEdgeCountVector (SubcriticalDivision.ofSupercritical hk D) eta R₀) :
    (supercriticalFixedProfileBlockModel D.onSupportFin (oneCoreProfile hk D hret v)).Sample ≃
      RetainedEdgeChoices v :=
  (supercriticalFixedProfileBlockModel D.onSupportFin (oneCoreProfile hk D hret v)).sampleEquiv
    (retainedEdgeChoiceModel v) (oneCoreRetainedPairEquiv hk D eta R₀ hret)
    (oneCoreBlockEquiv hk D hret v) (fun _ ↦ rfl)

theorem oneCoreProfileSampleEquiv_selected (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    {eta : ℝ} {R₀ : ℕ} (hret)
    (v : RetainedEdgeCountVector (SubcriticalDivision.ofSupercritical hk D) eta R₀)
    (S : (supercriticalFixedProfileBlockModel D.onSupportFin (oneCoreProfile hk D hret v)).Sample)
    (e : SupercriticalPartPair k)
    (z : ↥((supercriticalFixedProfileBlockModel D.onSupportFin
      (oneCoreProfile hk D hret v)).block e)) :
    s(D.supportVertex z.val.1, D.supportVertex z.val.2) ∈
      (retainedEdgeChoiceModel v).selectedInBlock (oneCoreProfileSampleEquiv hk D hret v S)
        (oneCoreRetainedPairEquiv hk D eta R₀ hret e) ↔
    z.val ∈ (supercriticalFixedProfileBlockModel D.onSupportFin
      (oneCoreProfile hk D hret v)).selectedInBlock S e := by
  have h := (supercriticalFixedProfileBlockModel D.onSupportFin
    (oneCoreProfile hk D hret v)).sampleEquiv_mem (retainedEdgeChoiceModel v)
      (oneCoreRetainedPairEquiv hk D eta R₀ hret) (oneCoreBlockEquiv hk D hret v)
      (fun _ ↦ rfl) S e z
  change (oneCoreBlockEquiv hk D hret v e z).val ∈ _ ↔ _
  rw [DenseGraph.FixedCardinalityBlockModel.mem_selectedInBlock_subtype,
    DenseGraph.FixedCardinalityBlockModel.mem_selectedInBlock_subtype]
  exact h

end InducedStars
