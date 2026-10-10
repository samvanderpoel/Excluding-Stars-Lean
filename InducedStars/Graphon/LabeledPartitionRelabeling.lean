import InducedStars.FinitePartition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# Relabeling equal finite labeled partitions

This file builds an explicit ambient permutation between two finite labeled
partitions with matching part sizes.  The construction passes through the
sigma types of the labeled part subtypes and uses `Finset.equivOfCardEq`
inside each label.
-/

noncomputable section

open Set

namespace InducedStars

/-! ## The sigma type of a labeled partition -/

/-- Forget the label and subtype proof of a point in the sigma type of a
labeled family of finsets. -/
def labeledPartitionSigmaCoe {V I : Type*} (A : I → Finset V) :
    (Σ i, A i) → V :=
  fun z ↦ z.2

theorem labeledPartitionSigmaCoe_injective
    {V I : Type*}
    (A : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) A) :
    Function.Injective (labeledPartitionSigmaCoe A) := by
  classical
  rintro ⟨i, x⟩ ⟨j, y⟩ hxy
  change (x : V) = (y : V) at hxy
  have hij : i = j := by
    by_contra hne
    have hd : Disjoint (A i) (A j) :=
      hdisj (Set.mem_univ i) (Set.mem_univ j) hne
    have hxj : (x : V) ∈ A j := by
      rw [hxy]
      exact y.property
    exact Finset.disjoint_left.mp hd x.property hxj
  subst j
  have hsub : x = y := Subtype.ext hxy
  subst y
  rfl

theorem labeledPartitionSigmaCoe_surjective
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]
    (A : I → Finset V)
    (hcover : ColoredGraph.clusterUnion A = (Finset.univ : Finset V)) :
    Function.Surjective (labeledPartitionSigmaCoe A) := by
  intro x
  have hxUnion : x ∈ ColoredGraph.clusterUnion A := by
    rw [hcover]
    exact Finset.mem_univ x
  rw [ColoredGraph.clusterUnion, Finset.mem_biUnion] at hxUnion
  obtain ⟨i, _hi, hxi⟩ := hxUnion
  exact ⟨⟨i, ⟨x, hxi⟩⟩, rfl⟩

/-- A labeled partition identifies its sigma type of part subtypes with the
ambient finite type. -/
noncomputable def labeledPartitionSigmaEquiv
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]
    (A : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) A)
    (hcover : ColoredGraph.clusterUnion A = (Finset.univ : Finset V)) :
    (Σ i, A i) ≃ V :=
  Equiv.ofBijective (labeledPartitionSigmaCoe A)
    ⟨labeledPartitionSigmaCoe_injective A hdisj,
      labeledPartitionSigmaCoe_surjective A hcover⟩

@[simp] theorem labeledPartitionSigmaEquiv_apply
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]
    (A : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) A)
    (hcover : ColoredGraph.clusterUnion A = (Finset.univ : Finset V))
    (z : Σ i, A i) :
    labeledPartitionSigmaEquiv A hdisj hcover z = z.2 :=
  rfl

/-- The inverse sigma representation of a vertex lies in the part named by
its sigma label. -/
theorem mem_labeledPart_sigmaEquiv_symm
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]
    (A : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) A)
    (hcover : ColoredGraph.clusterUnion A = (Finset.univ : Finset V))
    (x : V) :
    x ∈ A ((labeledPartitionSigmaEquiv A hdisj hcover).symm x).1 := by
  let z := (labeledPartitionSigmaEquiv A hdisj hcover).symm x
  have hz : labeledPartitionSigmaEquiv A hdisj hcover z = x :=
    (labeledPartitionSigmaEquiv A hdisj hcover).apply_symm_apply x
  have hzval : (z.2 : V) = x := by
    simpa only [labeledPartitionSigmaEquiv_apply] using hz
  change x ∈ A z.1
  rw [← hzval]
  exact z.2.property

/-- Membership determines the label of the inverse sigma representation. -/
theorem labeledPartitionSigmaEquiv_symm_fst_eq_of_mem
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]
    (A : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) A)
    (hcover : ColoredGraph.clusterUnion A = (Finset.univ : Finset V))
    {i : I} {x : V} (hx : x ∈ A i) :
    ((labeledPartitionSigmaEquiv A hdisj hcover).symm x).1 = i := by
  let j := ((labeledPartitionSigmaEquiv A hdisj hcover).symm x).1
  have hxj : x ∈ A j := mem_labeledPart_sigmaEquiv_symm A hdisj hcover x
  by_contra hji
  exact Finset.disjoint_left.mp
    (hdisj (Set.mem_univ j) (Set.mem_univ i) hji) hxj hx

/-! ## Labelwise equivalences and the ambient permutation -/

/-- Equivalence of two same-cardinality parts with the same label. -/
noncomputable def labeledPartEquiv
    {V I : Type*} (A B : I → Finset V)
    (hcard : ∀ i, (A i).card = (B i).card) (i : I) :
    A i ≃ B i :=
  Finset.equivOfCardEq (hcard i)

/-- The label-preserving equivalence between the sigma types of two labeled
families. -/
noncomputable def labeledPartitionSigmaCongr
    {V I : Type*} (A B : I → Finset V)
    (hcard : ∀ i, (A i).card = (B i).card) :
    (Σ i, A i) ≃ (Σ i, B i) :=
  Equiv.sigmaCongrRight (fun i ↦ labeledPartEquiv A B hcard i)

/-- Ambient permutation carrying each source part to the target part with
the same label. -/
noncomputable def labeledPartitionPerm
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]
    (A B : I → Finset V)
    (hAdisj : Set.PairwiseDisjoint (Set.univ : Set I) A)
    (hAcover : ColoredGraph.clusterUnion A = (Finset.univ : Finset V))
    (hBdisj : Set.PairwiseDisjoint (Set.univ : Set I) B)
    (hBcover : ColoredGraph.clusterUnion B = (Finset.univ : Finset V))
    (hcard : ∀ i, (A i).card = (B i).card) : Equiv.Perm V :=
  (labeledPartitionSigmaEquiv A hAdisj hAcover).symm |>.trans
    ((labeledPartitionSigmaCongr A B hcard).trans
      (labeledPartitionSigmaEquiv B hBdisj hBcover))

/-- Every vertex is sent into the target part having its source sigma
label. -/
theorem labeledPartitionPerm_mem_target
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]
    (A B : I → Finset V)
    (hAdisj : Set.PairwiseDisjoint (Set.univ : Set I) A)
    (hAcover : ColoredGraph.clusterUnion A = (Finset.univ : Finset V))
    (hBdisj : Set.PairwiseDisjoint (Set.univ : Set I) B)
    (hBcover : ColoredGraph.clusterUnion B = (Finset.univ : Finset V))
    (hcard : ∀ i, (A i).card = (B i).card) (x : V) :
    labeledPartitionPerm A B hAdisj hAcover hBdisj hBcover hcard x ∈
      B ((labeledPartitionSigmaEquiv A hAdisj hAcover).symm x).1 := by
  let z := (labeledPartitionSigmaEquiv A hAdisj hAcover).symm x
  change labeledPartitionSigmaEquiv B hBdisj hBcover
      (labeledPartitionSigmaCongr A B hcard z) ∈ B z.1
  rw [labeledPartitionSigmaEquiv_apply]
  exact (labeledPartitionSigmaCongr A B hcard z).2.property

/-- Exact labelwise membership identity for the ambient permutation. -/
theorem labeledPartitionPerm_mem_iff
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]
    (A B : I → Finset V)
    (hAdisj : Set.PairwiseDisjoint (Set.univ : Set I) A)
    (hAcover : ColoredGraph.clusterUnion A = (Finset.univ : Finset V))
    (hBdisj : Set.PairwiseDisjoint (Set.univ : Set I) B)
    (hBcover : ColoredGraph.clusterUnion B = (Finset.univ : Finset V))
    (hcard : ∀ i, (A i).card = (B i).card) (i : I) (x : V) :
    labeledPartitionPerm A B hAdisj hAcover hBdisj hBcover hcard x ∈ B i ↔
      x ∈ A i := by
  let j := ((labeledPartitionSigmaEquiv A hAdisj hAcover).symm x).1
  have hxA : x ∈ A j :=
    mem_labeledPart_sigmaEquiv_symm A hAdisj hAcover x
  have hpermB :
      labeledPartitionPerm A B hAdisj hAcover hBdisj hBcover hcard x ∈ B j :=
    labeledPartitionPerm_mem_target A B hAdisj hAcover hBdisj hBcover hcard x
  constructor
  · intro hxBi
    have hji : j = i := by
      by_contra hne
      exact Finset.disjoint_left.mp
        (hBdisj (Set.mem_univ j) (Set.mem_univ i) hne) hpermB hxBi
    simpa [hji] using hxA
  · intro hxAi
    have hji : j = i :=
      labeledPartitionSigmaEquiv_symm_fst_eq_of_mem
        A hAdisj hAcover hxAi
    simpa [hji] using hpermB

/-- The ambient permutation maps every source part into the equally labeled
target part. -/
theorem labeledPartitionPerm_mapsTo
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]
    (A B : I → Finset V)
    (hAdisj : Set.PairwiseDisjoint (Set.univ : Set I) A)
    (hAcover : ColoredGraph.clusterUnion A = (Finset.univ : Finset V))
    (hBdisj : Set.PairwiseDisjoint (Set.univ : Set I) B)
    (hBcover : ColoredGraph.clusterUnion B = (Finset.univ : Finset V))
    (hcard : ∀ i, (A i).card = (B i).card) (i : I) :
    Set.MapsTo
      (labeledPartitionPerm A B hAdisj hAcover hBdisj hBcover hcard)
      (↑(A i) : Set V) (↑(B i) : Set V) := by
  intro x hx
  exact (labeledPartitionPerm_mem_iff
    A B hAdisj hAcover hBdisj hBcover hcard i x).2 hx

end InducedStars
