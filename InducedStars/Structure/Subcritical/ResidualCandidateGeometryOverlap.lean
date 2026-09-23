import InducedStars.Structure.Subcritical.ResidualCandidateCounting
import InducedStars.Structure.Subcritical.ResidualCandidateOverlap
import InducedStars.Structure.Subcritical.ResidualCandidateEvents
import InducedStars.Structure.Subcritical.ResidualStarWitnesses

/-!
# Actual role-adapted vectors for residual candidate overlaps

Every random pair contains a free role.  Compressing the two fixed endpoint
roles into one slot therefore preserves that pair.  The slot stores the
second matching endpoint precisely when the random pair uses it; either
endpoint identifies its matching edge injectively.
-/

noncomputable section
open Finset
open scoped Classical

namespace InducedStars.SubcriticalHomogeneousResidualMatching

variable {k n R₀ : ℕ} {D : SubcriticalDivision k (Fin n)} {eta : ℝ}
  {R : SimpleGraph (Fin n)} {B : Finset (Fin n)}
  (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)

/-- An ordered pair of distinct roles with at least one free vertex.
The designated fixed-fixed pair is never a random coordinate. -/
abbrev RandomRole := {q : M.Role × M.Role // q.1 ≠ q.2 ∧
  ∃ t : M.FreeRole, q.1 = Sum.inr t ∨ q.2 = Sum.inr t}

theorem randomRole_card_le (hk : 3 ≤ k) : Fintype.card M.RandomRole ≤ (k + 1) ^ 2 := by
  have h := Fintype.card_le_of_injective
    (Subtype.val : M.RandomRole → M.Role × M.Role) Subtype.val_injective
  simpa [Role, Fintype.card_prod, card_subcriticalResidualStarRole hk, pow_two] using h

/-- Both designated endpoint roles compress to the one matching-anchor slot. -/
def compressedRole : M.Role → Option M.FreeRole := Sum.elim (fun _ ↦ none) some

def compressedRoleEquiv (hk : 3 ≤ k) : Option M.FreeRole ≃ Fin k :=
  Fintype.equivFinOfCardEq (by
    simp only [Fintype.card_option, FreeRole, card_subcriticalResidualFreeRole hk]
    omega)

def randomRoleUsesSecond (r : M.RandomRole) : Prop :=
  r.val.1 = Sum.inl 1 ∨ r.val.2 = Sum.inl 1

def candidateVectorValue (r : M.RandomRole) (c : M.Candidate) : Option M.FreeRole → Fin n
  | none => if M.randomRoleUsesSecond r then M.secondEndpoint c.1 else M.firstEndpoint c.1
  | some t => c.2.val t

def candidateVector (hk : 3 ≤ k) (r : M.RandomRole) (c : M.Candidate) : Fin k → Fin n :=
  fun i ↦ M.candidateVectorValue r c ((M.compressedRoleEquiv hk).symm i)

theorem candidateVector_injective (hk : 3 ≤ k) (r : M.RandomRole) :
    Function.Injective (M.candidateVector hk r) := by
  rintro ⟨e, f⟩ ⟨d, g⟩ hfg
  have he : e = d := by
    have h := congrFun hfg (M.compressedRoleEquiv hk none)
    by_cases hr : M.randomRoleUsesSecond r
    · apply M.secondEndpoint_injective
      simpa [candidateVector, candidateVectorValue, hr] using h
    · apply M.firstEndpoint_injective
      simpa [candidateVector, candidateVectorValue, hr] using h
  subst d
  have hs : f = g := by
    apply Subtype.ext
    funext t
    have h := congrFun hfg (M.compressedRoleEquiv hk (some t))
    simpa [candidateVector, candidateVectorValue] using h
  subst g
  rfl

def randomRolePositions (hk : 3 ≤ k) (r : M.RandomRole) : Fin k × Fin k :=
  (M.compressedRoleEquiv hk (M.compressedRole r.val.1),
    M.compressedRoleEquiv hk (M.compressedRole r.val.2))

theorem randomRolePositions_ne (hk : 3 ≤ k) (r : M.RandomRole) :
    (M.randomRolePositions hk r).1 ≠ (M.randomRolePositions hk r).2 := by
  intro h
  have he : M.compressedRole r.val.1 = M.compressedRole r.val.2 :=
    (M.compressedRoleEquiv hk).injective h
  clear h
  obtain ⟨⟨s, t⟩, hst, hfree⟩ := r
  change M.compressedRole s = M.compressedRole t at he
  cases s with
  | inl s =>
      cases t with
      | inl t => obtain ⟨u, hu | hu⟩ := hfree <;> cases hu
      | inr t => simp [compressedRole] at he
  | inr s =>
      cases t with
      | inl t => simp [compressedRole] at he
      | inr t => exact hst (by simpa [compressedRole] using he)

/-- At either endpoint of the random role, compression recovers the actual
candidate vertex. -/
theorem candidateVector_at_role (hk : 3 ≤ k) (r : M.RandomRole) (c : M.Candidate)
    (t : M.Role) (ht : t = r.val.1 ∨ t = r.val.2) :
    M.candidateVector hk r c (M.compressedRoleEquiv hk (M.compressedRole t)) =
      M.selectionVertex c.1 c.2 t := by
  simp only [candidateVector, Equiv.symm_apply_apply]
  cases t with
  | inr t => rfl
  | inl t =>
      fin_cases t
      · have hno : ¬M.randomRoleUsesSecond r := by
          obtain ⟨u, hu⟩ := r.property.2
          intro hs
          rcases ht with ht | ht <;> rcases hu with hu | hu <;>
            rcases hs with hs | hs <;> simp_all [randomRoleUsesSecond]
        simp [compressedRole, candidateVectorValue, selectionVertex, hno]
      · have hyes : M.randomRoleUsesSecond r := by
          exact ht.elim (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm)
        simp [compressedRole, candidateVectorValue, selectionVertex, hyes]

/-- Look up the actual retained active coordinate for a pair of selected
vertices. Inactive pairs impose no random requirement. -/
def randomRoleCoordinate (c : M.Candidate) (r : M.RandomRole) :
    Option (SubcriticalActiveCoordinate D eta R₀) :=
  if h : ∃ e : SubcriticalActiveCoordinate D eta R₀,
      e.2.1 = s(M.selectionVertex c.1 c.2 r.val.1, M.selectionVertex c.1 c.2 r.val.2)
  then some (Classical.choose h) else none

theorem randomRoleCoordinate_eq_some_iff
    (mvec : RetainedEdgeCountVector D eta R₀)
    (c : M.Candidate) (r : M.RandomRole) (e : SubcriticalActiveCoordinate D eta R₀) :
    M.randomRoleCoordinate c r = some e ↔
      e.2.1 = s(M.selectionVertex c.1 c.2 r.val.1, M.selectionVertex c.1 c.2 r.val.2) := by
  have hinj : Function.Injective (fun e : SubcriticalActiveCoordinate D eta R₀ ↦ e.2.1) :=
    subcriticalActiveCoordinate_val_injective mvec
  unfold randomRoleCoordinate
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · intro he
      exact (congrArg (fun z : SubcriticalActiveCoordinate D eta R₀ ↦ z.2.1) he).symm.trans
        (Classical.choose_spec h)
    · intro he
      exact hinj ((Classical.choose_spec h).trans he.symm)
  · simp only [Option.noConfusion, false_iff]
    exact fun he ↦ h ⟨e, he⟩

end InducedStars.SubcriticalHomogeneousResidualMatching

namespace InducedStars.SubcriticalHomogeneousResidualMatching

variable {k n R₀ : ℕ} {D : SubcriticalDivision k (Fin n)} {eta theta : ℝ}
  {R : SimpleGraph (Fin n)} {p : SubcriticalProfile D eta R₀ theta}
  (M : SubcriticalHomogeneousResidualMatching D eta R₀ R p.roots)

/-- Exactly the full coordinate support of the actual signed star event. -/
def candidateRequiredCoordinates (c : M.Candidate) : Finset (SubcriticalActiveCoordinate D eta R₀) :=
  (M.selectionWitness c.1 c.2).present ∪ (M.selectionWitness c.1 c.2).absent

/-- Every required coordinate has an actual role pair containing a free
vertex: the two fixed matching endpoints form a nonactive pair. -/
theorem candidateRequiredCoordinates_has_role
    (mvec : RetainedEdgeCountVector D eta R₀)
    (c : M.Candidate) (e : SubcriticalActiveCoordinate D eta R₀)
    (he : e ∈ M.candidateRequiredCoordinates c) :
    ∃ r : M.RandomRole, M.randomRoleCoordinate c r = some e := by
  have hw : ∃ i j : M.Role,
      e.2.1 = s(M.selectionVertex c.1 c.2 i, M.selectionVertex c.1 c.2 j) ∧ i ≠ j := by
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨i, j, heq, hstar⟩ := ((M.selectionWitness c.1 c.2).mem_present e).mp he
      exact ⟨i, j, heq, hstar.ne⟩
    · obtain ⟨i, j, heq, hne, _⟩ := ((M.selectionWitness c.1 c.2).mem_absent e).mp he
      exact ⟨i, j, heq, hne⟩
  obtain ⟨i, j, heq, hne⟩ := hw
  have hu : e.2.1 ∈ retainedActiveEdgeUniverse D eta R₀ :=
    (mem_retainedActiveEdgeUniverse D eta R₀ _).mpr ⟨e.1, e.2.2⟩
  rw [heq] at hu
  have ha : D.ActivePair (M.selectionVertex c.1 c.2 i) (M.selectionVertex c.1 c.2 j) :=
    ((mk_mem_retainedActiveEdgeUniverse_iff D eta R₀ _ _).mp hu).1
  have hfree : ∃ t : M.FreeRole, i = Sum.inr t ∨ j = Sum.inr t := by
    cases i with
    | inr i => exact ⟨i, Or.inl rfl⟩
    | inl i =>
        cases j with
        | inr j => exact ⟨j, Or.inr rfl⟩
        | inl j =>
            fin_cases i <;> fin_cases j
            · exact (hne rfl).elim
            · exact (M.endpoints_nonactive c.1 (by simpa [selectionVertex] using ha)).elim
            · apply False.elim
              apply M.endpoints_nonactive c.1
              apply (D.activePair_comm _ _).mp
              simpa [selectionVertex] using ha
            · exact (hne rfl).elim
  let r : M.RandomRole := ⟨(i, j), hne, hfree⟩
  exact ⟨r, (M.randomRoleCoordinate_eq_some_iff mvec c r e).mpr heq⟩

/-- The actual candidate family satisfies the generic overlap encoding;
neither abundance nor an overlap bound is assumed. -/
def candidateCoordinateEncoding (hk : 3 ≤ k)
    (mvec : RetainedEdgeCountVector D eta R₀) :
    SubcriticalResidualCoordinateEncoding M.Candidate M.RandomRole
      (SubcriticalActiveCoordinate D eta R₀) k n where
  required := M.candidateRequiredCoordinates
  coordinate := M.randomRoleCoordinate
  vector := M.candidateVector hk
  vector_injective := M.candidateVector_injective hk
  positions := M.randomRolePositions hk
  positions_ne := M.randomRolePositions_ne hk
  value := fun e ↦ e.2.1
  coordinate_eq := by
    intro c r e he
    change e.2.1 = s(M.candidateVector hk r c
      (M.compressedRoleEquiv hk (M.compressedRole r.val.1)),
      M.candidateVector hk r c (M.compressedRoleEquiv hk (M.compressedRole r.val.2)))
    rw [M.candidateVector_at_role hk r c _ (Or.inl rfl),
      M.candidateVector_at_role hk r c _ (Or.inr rfl)]
    exact (M.randomRoleCoordinate_eq_some_iff mvec c r e).mp he
  required_has_role := M.candidateRequiredCoordinates_has_role mvec

/-- Actual unordered dependency-pair count for the signed residual star
events. The coefficient `2*(k+1)^4` depends only on `k`. -/
theorem candidate_unorderedOverlappingPairs_card_le
    (hk : 3 ≤ k) (mvec : RetainedEdgeCountVector D eta R₀)
    [LinearOrder M.Candidate] :
    (DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
      M.candidateRequiredCoordinates).card ≤
        2 * (k + 1) ^ 4 * M.edges.card * n ^ (2 * k - 3) := by
  have h := (M.candidateCoordinateEncoding hk mvec).unorderedOverlappingPairs_card_le_matchingScale
    hk (M.candidate_card_upper hk)
  change (DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
      M.candidateRequiredCoordinates).card ≤
    2 * Fintype.card M.RandomRole ^ 2 * M.edges.card * n ^ (2 * k - 3) at h
  calc
    _ ≤ _ := h
    _ ≤ 2 * ((k + 1) ^ 2) ^ 2 * M.edges.card * n ^ (2 * k - 3) := by
      gcongr
      exact M.randomRole_card_le hk
    _ = _ := by ring

/-- Real-cast form consumed by the Janson dependency-sum adapter. -/
theorem candidate_unorderedOverlappingPairs_card_cast_le
    (hk : 3 ≤ k) (mvec : RetainedEdgeCountVector D eta R₀)
    [LinearOrder M.Candidate] :
    ((DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
      M.candidateRequiredCoordinates).card : ℝ) ≤
        (2 * (k + 1) ^ 4 : ℝ) * (M.edges.card : ℝ) * (n : ℝ) ^ (2 * k - 3) := by
  exact_mod_cast M.candidate_unorderedOverlappingPairs_card_le hk mvec

/-- Direct actual-event interface for the residual Janson proof.  The zero
count vector is used only to access the existing coordinate-value injection;
it asserts no density feasibility and disappears from the statement. -/
theorem candidate_unorderedOverlap_card_le
    (hk : 3 ≤ k) [LinearOrder M.Candidate] :
    ((DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
      (fun c : M.Candidate ↦ (M.selectionWitness c.1 c.2).present ∪
        (M.selectionWitness c.1 c.2).absent)).card : ℝ) ≤
      (2 * (k + 1 : ℝ) ^ 4) * (M.edges.card : ℝ) * (n : ℝ) ^ (2 * k - 3) := by
  have h := M.candidate_unorderedOverlappingPairs_card_cast_le hk
    (zeroRetainedEdgeCountVector D eta R₀)
  have he : M.candidateRequiredCoordinates =
      (fun c : M.Candidate ↦ (M.selectionWitness c.1 c.2).present ∪
        (M.selectionWitness c.1 c.2).absent) := rfl
  rw [he] at h
  exact h

end InducedStars.SubcriticalHomogeneousResidualMatching
