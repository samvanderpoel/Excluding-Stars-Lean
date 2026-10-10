import InducedStars.Regularity.InitialPartition
import InducedStars.Regularity.FinpartitionRefinement

/-!
# Equal cores inside a prescribed equitable partition

Given an equitable partition into `s` parent parts and a positive integer
`q`, this file retains the same multiple of `q` vertices in every parent.
The retained subtype then has an exactly equitable parent partition, which is
split uniformly into `q` equal children per parent.
-/

open Finset Fintype

namespace InducedStars.Regularity

universe u

namespace PrescribedCore

variable {V : Type u} [Fintype V] [DecidableEq V] {s : ℕ}

/-- The cardinality of each child after first taking equal `q`-divisible
cores from all prescribed parent parts. -/
def coreSize (_I : EquitableInitialPartition V s) (q : ℕ) : ℕ :=
  (Fintype.card V / s) / q

theorem targetCard_le_part (I : EquitableInitialPartition V s) (q : ℕ) (i : Fin s) :
    q * coreSize I q ≤ (I.parts i).card := by
  calc
    q * coreSize I q = (Fintype.card V / s / q) * q := by
      simp only [coreSize, Nat.mul_comm]
    _ ≤ Fintype.card V / s := Nat.div_mul_le_self _ _
    _ ≤ (I.parts i).card := I.average_le_card_part i

/-- A chosen equal, `q`-divisible core inside parent part `i`. -/
noncomputable def core (I : EquitableInitialPartition V s) (q : ℕ) (i : Fin s) : Finset V :=
  chosenSubsetOfCard (I.parts i) (q * coreSize I q) (targetCard_le_part I q i)

theorem core_subset_part (I : EquitableInitialPartition V s) (q : ℕ) (i : Fin s) :
    core I q i ⊆ I.parts i :=
  chosenSubsetOfCard_subset _ _ _

@[simp]
theorem card_core (I : EquitableInitialPartition V s) (q : ℕ) (i : Fin s) :
    (core I q i).card = q * coreSize I q :=
  card_chosenSubsetOfCard _ _ _

theorem core_disjoint (I : EquitableInitialPartition V s) (q : ℕ)
    {i j : Fin s} (hij : i ≠ j) : Disjoint (core I q i) (core I q j) :=
  (I.parts_disjoint hij).mono (core_subset_part I q i) (core_subset_part I q j)

theorem core_pairwiseDisjoint (I : EquitableInitialPartition V s) (q : ℕ) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin s)) (core I q) := by
  intro i _ j _ hij
  exact core_disjoint I q hij

/-- All vertices retained in the equal cores. -/
noncomputable def retained (I : EquitableInitialPartition V s) (q : ℕ) : Finset V :=
  Finset.univ.biUnion (core I q)

theorem core_subset_retained (I : EquitableInitialPartition V s) (q : ℕ) (i : Fin s) :
    core I q i ⊆ retained I q := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩

theorem retained_subset_univ (I : EquitableInitialPartition V s) (q : ℕ) :
    retained I q ⊆ (Finset.univ : Finset V) :=
  Finset.subset_univ _

@[simp]
theorem card_retained (I : EquitableInitialPartition V s) (q : ℕ) :
    (retained I q).card = s * (q * coreSize I q) := by
  have hdisjoint :
      ((Finset.univ : Finset (Fin s)) : Set (Fin s)).PairwiseDisjoint (core I q) := by
    simpa only [Finset.coe_univ] using core_pairwiseDisjoint I q
  rw [retained, Finset.card_biUnion hdisjoint]
  simp only [card_core, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  norm_num

/-- At most `s*q` vertices are discarded when taking the equal divisible
cores.  The two possible losses are the remainder modulo `s` and, inside
each parent, the remainder modulo `q`. -/
theorem card_compl_retained_le (I : EquitableInitialPartition V s) (q : ℕ)
    (hs : 0 < s) (hq : 0 < q) :
    ((Finset.univ : Finset V) \ retained I q).card ≤ s * q := by
  rw [Finset.card_sdiff_of_subset (retained_subset_univ I q), Finset.card_univ,
    card_retained]
  let n := Fintype.card V
  let a := n / s
  let c := a / q
  have hsmod : n % s < s := Nat.mod_lt n hs
  have hqmod : a % q < q := Nat.mod_lt a hq
  have hdecomp : n - s * (q * c) = n % s + s * (a % q) := by
    calc
      n - s * (q * c) = (n % s + s * a) - s * (q * c) := by
        rw [Nat.mod_add_div n s]
      _ = (n % s + s * (a % q + q * c)) - s * (q * c) := by
        rw [Nat.mod_add_div a q]
      _ = n % s + s * (a % q) := by
        simp only [Nat.mul_add]
        omega
  change n - s * (q * c) ≤ s * q
  rw [hdecomp]
  calc
    n % s + s * (a % q) ≤ s + s * (a % q) := Nat.add_le_add_right hsmod.le _
    _ = s * (a % q + 1) := by simp [Nat.mul_add, Nat.add_comm]
    _ ≤ s * q := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hqmod)

/-- The retained vertices, regarded as their own finite vertex type. -/
abbrev Vertex (I : EquitableInitialPartition V s) (q : ℕ) :=
  {v : V // v ∈ retained I q}

@[simp]
theorem card_vertex (I : EquitableInitialPartition V s) (q : ℕ) :
    Fintype.card (Vertex I q) = s * (q * coreSize I q) := by
  rw [Fintype.card_coe, card_retained]

/-- Inclusion of the `i`th core into the retained-vertex subtype. -/
def coreEmbedding (I : EquitableInitialPartition V s) (q : ℕ) (i : Fin s) :
    (core I q i : Type u) ↪ Vertex I q where
  toFun v := ⟨v.1, core_subset_retained I q i v.2⟩
  inj' v w h := by
    apply Subtype.ext
    simpa using congrArg Subtype.val h

/-- The `i`th core as a finset of retained vertices. -/
noncomputable def corePart (I : EquitableInitialPartition V s) (q : ℕ) (i : Fin s) :
    Finset (Vertex I q) :=
  (core I q i).attach.map (coreEmbedding I q i)

@[simp]
theorem mem_corePart (I : EquitableInitialPartition V s) (q : ℕ) (i : Fin s)
    (x : Vertex I q) :
    x ∈ corePart I q i ↔ x.1 ∈ core I q i := by
  rw [corePart, Finset.mem_map]
  constructor
  · rintro ⟨a, _, rfl⟩
    exact a.2
  · intro hx
    refine ⟨⟨x.1, hx⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

@[simp]
theorem card_corePart (I : EquitableInitialPartition V s) (q : ℕ) (i : Fin s) :
    (corePart I q i).card = q * coreSize I q := by
  simp [corePart]

theorem corePart_pairwiseDisjoint (I : EquitableInitialPartition V s) (q : ℕ) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin s)) (corePart I q) := by
  intro i _ j _ hij
  change Disjoint (corePart I q i) (corePart I q j)
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rw [mem_corePart] at hxi hxj
  exact Finset.disjoint_left.mp (core_disjoint I q hij) hxi hxj

@[simp]
theorem corePart_cover (I : EquitableInitialPartition V s) (q : ℕ) :
    Finset.univ.biUnion (corePart I q) = (Finset.univ : Finset (Vertex I q)) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_corePart]
  constructor
  · exact fun _ ↦ trivial
  · intro _
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp x.2
    exact ⟨i, hi⟩

theorem corePart_nonempty (I : EquitableInitialPartition V s) (q : ℕ)
    (hq : 0 < q) (hc : 0 < coreSize I q) (i : Fin s) :
    (corePart I q i).Nonempty := by
  rw [← Finset.card_pos, card_corePart]
  exact Nat.mul_pos hq hc

theorem corePart_balanced (I : EquitableInitialPartition V s) (q : ℕ) (i j : Fin s) :
    Nat.dist (corePart I q i).card (corePart I q j).card ≤ 1 := by
  simp only [card_corePart, Nat.dist_self]
  omega

/-- The exactly equitable partition of the retained subtype by its `s`
parent cores. -/
noncomputable def parentPartition (I : EquitableInitialPartition V s) (q : ℕ)
    (hq : 0 < q) (hc : 0 < coreSize I q) :
    EquitableInitialPartition (Vertex I q) s :=
  EquitableInitialPartition.ofParts (corePart I q)
    (corePart_nonempty I q hq hc) (corePart_pairwiseDisjoint I q)
    (corePart_cover I q) (corePart_balanced I q)

@[simp]
theorem parentPartition_parts (I : EquitableInitialPartition V s) (q : ℕ)
    (hq : 0 < q) (hc : 0 < coreSize I q) (i : Fin s) :
    (parentPartition I q hq hc).parts i = corePart I q i := by
  exact EquitableInitialPartition.parts_ofParts _ _ _ _ _ i

theorem parent_part_card (I : EquitableInitialPartition V s) (q : ℕ)
    (hq : 0 < q) (hc : 0 < coreSize I q)
    (U : Finset (Vertex I q))
    (hU : U ∈ (parentPartition I q hq hc).partition.parts) :
    U.card = q * coreSize I q := by
  obtain ⟨i, hi⟩ := (parentPartition I q hq hc).mem_partition_iff U |>.mp hU
  rw [← hi, parentPartition_parts, card_corePart]

theorem q_le_parent_part_card (I : EquitableInitialPartition V s) (q : ℕ)
    (hq : 0 < q) (hc : 0 < coreSize I q)
    (U : Finset (Vertex I q))
    (hU : U ∈ (parentPartition I q hq hc).partition.parts) :
    q ≤ U.card := by
  rw [parent_part_card I q hq hc U hU]
  exact Nat.le_mul_of_pos_right q hc

/-- A chosen equipartition of a retained parent core into exactly `q`
children. -/
noncomputable def childPartition (I : EquitableInitialPartition V s) (q : ℕ)
    (hq : 0 < q) (hc : 0 < coreSize I q)
    (U : Finset (Vertex I q))
    (hU : U ∈ (parentPartition I q hq hc).partition.parts) : Finpartition U :=
  (Finpartition.exists_equipartition_card_eq U hq.ne'
    (q_le_parent_part_card I q hq hc U hU)).choose

theorem childPartition_isEquipartition (I : EquitableInitialPartition V s) (q : ℕ)
    (hq : 0 < q) (hc : 0 < coreSize I q)
    (U : Finset (Vertex I q))
    (hU : U ∈ (parentPartition I q hq hc).partition.parts) :
    (childPartition I q hq hc U hU).IsEquipartition :=
  (Finpartition.exists_equipartition_card_eq U hq.ne'
    (q_le_parent_part_card I q hq hc U hU)).choose_spec.1

@[simp]
theorem card_childPartition_parts (I : EquitableInitialPartition V s) (q : ℕ)
    (hq : 0 < q) (hc : 0 < coreSize I q)
    (U : Finset (Vertex I q))
    (hU : U ∈ (parentPartition I q hq hc).partition.parts) :
    (childPartition I q hq hc U hU).parts.card = q :=
  (Finpartition.exists_equipartition_card_eq U hq.ne'
    (q_le_parent_part_card I q hq hc U hU)).choose_spec.2

theorem child_card (I : EquitableInitialPartition V s) (q : ℕ)
    (hq : 0 < q) (hc : 0 < coreSize I q)
    (U : Finset (Vertex I q))
    (hU : U ∈ (parentPartition I q hq hc).partition.parts)
    (A : Finset (Vertex I q)) (hA : A ∈ (childPartition I q hq hc U hU).parts) :
    A.card = coreSize I q := by
  let R := childPartition I q hq hc U hU
  have hequip : R.IsEquipartition := childPartition_isEquipartition I q hq hc U hU
  have hRcard : R.parts.card = q := card_childPartition_parts I q hq hc U hU
  have hUcard : U.card = q * coreSize I q := parent_part_card I q hq hc U hU
  have havg : U.card / R.parts.card = coreSize I q := by
    rw [hRcard, hUcard]
    simpa only [Nat.mul_comm] using Nat.mul_div_left (coreSize I q) hq
  rcases hequip.card_parts_eq_average hA with hsmall | hlarge
  · exact hsmall.trans havg
  · have hlargeCount := hequip.card_large_parts_eq_mod
    have hzero :
        #{B ∈ R.parts | B.card = U.card / R.parts.card + 1} = 0 := by
      rw [hlargeCount, hRcard, hUcard]
      simp
    have hpos : 0 < #{B ∈ R.parts | B.card = U.card / R.parts.card + 1} :=
      Finset.card_pos.mpr ⟨A, Finset.mem_filter.mpr ⟨hA, hlarge⟩⟩
    omega

/-- The starting partition for the seeded regularity iteration: bind the
equal `q`-way splits below all retained parent cores. -/
noncomputable def startingPartition (I : EquitableInitialPartition V s) (q : ℕ)
    (hq : 0 < q) (hc : 0 < coreSize I q) :
    Finpartition (Finset.univ : Finset (Vertex I q)) :=
  (parentPartition I q hq hc).partition.bind fun U hU ↦
    childPartition I q hq hc U hU

theorem startingPartition_isEquipartition (I : EquitableInitialPartition V s) (q : ℕ)
    (hq : 0 < q) (hc : 0 < coreSize I q) :
    (startingPartition I q hq hc).IsEquipartition := by
  intro A B hA hB
  obtain ⟨U, hU, hAU⟩ := Finpartition.mem_bind.mp hA
  obtain ⟨W, hW, hBW⟩ := Finpartition.mem_bind.mp hB
  have hAcard := child_card I q hq hc U hU A hAU
  have hBcard := child_card I q hq hc W hW B hBW
  omega

@[simp]
theorem card_startingPartition_parts (I : EquitableInitialPartition V s) (q : ℕ)
    (hq : 0 < q) (hc : 0 < coreSize I q) :
    (startingPartition I q hq hc).parts.card = s * q := by
  rw [startingPartition, Finpartition.card_bind]
  calc
    ∑ A ∈ (parentPartition I q hq hc).partition.parts.attach,
        (childPartition I q hq hc A A.2).parts.card =
        ∑ _A ∈ (parentPartition I q hq hc).partition.parts.attach, q := by
          apply Finset.sum_congr rfl
          intro A _
          exact card_childPartition_parts I q hq hc A A.2
    _ = (parentPartition I q hq hc).partition.parts.attach.card * q := by simp
    _ = s * q := by
      rw [Finset.card_attach, (parentPartition I q hq hc).card_partition_parts]

theorem startingPartition_uniformRefines (I : EquitableInitialPartition V s) (q : ℕ)
    (hq : 0 < q) (hc : 0 < coreSize I q) :
    (startingPartition I q hq hc).UniformRefines
      (parentPartition I q hq hc).partition q := by
  exact Finpartition.uniformRefines_bind (parentPartition I q hq hc).partition
    (fun U hU ↦ childPartition I q hq hc U hU) q
    (fun U hU ↦ card_childPartition_parts I q hq hc U hU)

end PrescribedCore

end InducedStars.Regularity
