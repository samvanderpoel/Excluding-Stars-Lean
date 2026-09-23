import InducedStars.Structure.Subcritical.ProfileAccounting
import InducedStars.Structure.Subcritical.ActiveLevelComparison
import InducedStars.Structure.Subcritical.FixedCountTransfer
import InducedStars.Structure.Subcritical.ProfileLeftover

/-!
# Natural-unit finite profile exponents

Paper: local exponents and `eqn:Psi-mat-definition-K1k`.
Entropy, log odds, and probability logarithms use natural units.
The residual weight retains the full remainder in each leftover fiber.
Residual safety forbids only induced stars avoiding all profile roots.
Zero probabilities use explicit finite cubic substitutes, not `Real.log 0`.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical

namespace InducedStars

/-- A finite substitute for the infinite negative log of probability zero.
For positive inputs this is exactly the natural negative logarithm. The
cubic fallback is a convention for finite exponents, not a source divergence. -/
def subcriticalNegLogProbability (n : ℕ) (p : ℝ) : ℝ :=
  if p = 0 then (n + 1 : ℝ)^3 else -Real.log p

/-- A finite substitute for the log of weight zero. Positive weights retain
their exact natural logarithm. -/
def subcriticalLogWeight (n : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then -((n + 1 : ℝ)^3) else Real.log x

theorem subcriticalNegLogProbability_nonneg (n : ℕ) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) : 0 ≤ subcriticalNegLogProbability n p := by
  unfold subcriticalNegLogProbability
  split_ifs with h
  · positivity
  · exact neg_nonneg.mpr (Real.log_nonpos hp.1 hp.2)

theorem subcriticalProbability_le_exp_negLog (n : ℕ) {p : ℝ}
    (hp : 0 ≤ p) : p ≤ Real.exp (-subcriticalNegLogProbability n p) := by
  unfold subcriticalNegLogProbability
  split_ifs with h
  · subst p
    exact (Real.exp_pos _).le
  · simp only [neg_neg, Real.exp_log (lt_of_le_of_ne hp (Ne.symm h))]
    exact le_rfl

theorem subcriticalProbability_eq_exp_negLog (n : ℕ) {p : ℝ}
    (hp : 0 < p) : p = Real.exp (-subcriticalNegLogProbability n p) := by
  simp [subcriticalNegLogProbability, hp.ne', Real.exp_log hp]

theorem subcriticalWeight_le_exp_logWeight (n : ℕ) {x : ℝ}
    (hx : 0 ≤ x) : x ≤ Real.exp (subcriticalLogWeight n x) := by
  unfold subcriticalLogWeight
  split_ifs with h
  · subst x
    exact (Real.exp_pos _).le
  · rw [Real.exp_log (lt_of_le_of_ne hx (Ne.symm h))]

theorem subcriticalWeight_eq_exp_logWeight (n : ℕ) {x : ℝ}
    (hx : 0 < x) : x = Real.exp (subcriticalLogWeight n x) := by
  simp [subcriticalLogWeight, hx.ne', Real.exp_log hx]

/-- Finite maximum with a zero default. All uses below have nonnegative
weights, so adjoining zero changes only the empty-family convention. -/
def subcriticalFiniteMax {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ℝ :=
  (insert 0 (s.image f)).sup' (Finset.insert_nonempty _ _) id

theorem subcriticalFiniteMax_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    0 ≤ subcriticalFiniteMax s f :=
  Finset.le_sup' id (Finset.mem_insert_self _ _)

theorem le_subcriticalFiniteMax {ι : Type*} {s : Finset ι} (f : ι → ℝ)
    {i : ι} (hi : i ∈ s) : f i ≤ subcriticalFiniteMax s f :=
  Finset.le_sup' id (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩))

theorem subcriticalFiniteMax_le {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    {b : ℝ} (hb : 0 ≤ b) (hf : ∀ i ∈ s, f i ≤ b) :
    subcriticalFiniteMax s f ≤ b := by
  apply Finset.sup'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hb
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hf i hi

@[simp] theorem subcriticalFiniteMax_empty {ι : Type*} (f : ι → ℝ) :
    subcriticalFiniteMax ∅ f = 0 := by simp [subcriticalFiniteMax]

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}

/-- One recorded present row in natural units. `none` is still distinct from
`some 0` in the profile datum, even though both have zero entropy cost. -/
def subcriticalProfilePresentRowEntropyNat
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (a : D.PartIndex) : ℝ :=
  match p.rows v a with
  | none => 0
  | some r =>
      (D.part a \ p.roots).card * Real.binEntropy
        ((r.val : ℝ) / (D.part a \ p.roots).card) - subcriticalLogOddsNat k * r.val

/-- The own-part missing-edge summand, present only at retained roots. -/
def subcriticalProfileOwnMissingEntropyNat
    (p : SubcriticalProfile D eta R₀ theta) (v : V) : ℝ :=
  if hv : v ∈ p.retainedRoots then
    let N := (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \
      p.roots).card
    (N : ℝ) * Real.binEntropy ((p.ownCount v).val / (N : ℝ)) +
      subcriticalLogOddsNat k * (p.ownCount v).val
  else 0

/-- Paper `Ent_v`, converted consistently to natural-exponential units.
It contains no tail probability or matching penalty. -/
def subcriticalProfileRootEntropyNat
    (p : SubcriticalProfile D eta R₀ theta) (v : V) : ℝ :=
  (∑ a : D.PartIndex, subcriticalProfilePresentRowEntropyNat p v a) +
    subcriticalProfileOwnMissingEntropyNat p v

theorem subcriticalProfilePresentRowEntropyNat_zero_of_empty
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (a : D.PartIndex)
    (he : D.part a \ p.roots = ∅) :
    subcriticalProfilePresentRowEntropyNat p v a = 0 := by
  unfold subcriticalProfilePresentRowEntropyNat
  split <;> rename_i h
  · rfl
  · have hc := (p.rows_valid _ _ _ h).2
    change _ ≤ (D.part a \ p.roots).card at hc
    rw [he, Finset.card_empty] at hc
    simp [he, Nat.eq_zero_of_le_zero hc]

@[simp] theorem subcriticalProfileOwnMissingEntropyNat_of_outside
    (p : SubcriticalProfile D eta R₀ theta) {v : V} (hv : v ∈ p.outsideRoots) :
    subcriticalProfileOwnMissingEntropyNat p v = 0 := by
  exact dif_neg (Finset.disjoint_right.mp p.roots_disjoint hv)

theorem subcriticalProfileRootEntropyNat_of_not_root
    (p : SubcriticalProfile D eta R₀ theta) {v : V} (hv : v ∉ p.roots) :
    subcriticalProfileRootEntropyNat p v = 0 := by
  have hret : v ∉ p.retainedRoots := fun h ↦ hv (Finset.mem_union_left _ h)
  simp [subcriticalProfileRootEntropyNat, subcriticalProfilePresentRowEntropyNat,
    p.rows_eq_none_of_not_mem_roots hv, subcriticalProfileOwnMissingEntropyNat, hret]

/-- Actual tagged Bernoulli coordinates, independent of the quota vector. -/
abbrev SubcriticalActiveCoordinate (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :=
  (e : RetainedActivePair D eta R₀) × ↥(retainedActivePotentialEdges D eta R₀ e)

/-- Random present degree into the trimmed target. Deterministic `H,T,L`
do not occur in the definition. -/
def subcriticalTailDegree (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (a : D.PartIndex) (S : Finset (SubcriticalActiveCoordinate D eta R₀)) : ℕ :=
  ((D.part a \ p.roots).filter fun y ↦ s(v, y) ∈ S.image (fun e ↦ e.2.1)).card

/-- One relaxed tail event. The threshold uses the full part, not its trim. -/
def subcriticalTailEvent (p : SubcriticalProfile D eta R₀ theta)
    (alpha : ℝ) (v : V) (a : D.PartIndex) (t : SubcriticalTailDirection) :
    Finset (Finset (SubcriticalActiveCoordinate D eta R₀)) :=
  Finset.univ.filter fun S ↦ match t with
    | .upper => (1 - 2 * alpha) * (D.part a).card ≤ (subcriticalTailDegree p v a S : ℝ)
    | .lower => (subcriticalTailDegree p v a S : ℝ) ≤ 2 * alpha * (D.part a).card

/-- Simultaneous tails at one root; no labels gives the whole outcome space. -/
def subcriticalRootTailEvent (p : SubcriticalProfile D eta R₀ theta)
    (alpha : ℝ) (v : V) : Finset (Finset (SubcriticalActiveCoordinate D eta R₀)) :=
  Finset.univ.filter fun S ↦ ∀ a t, p.tails v a = some t →
    S ∈ subcriticalTailEvent p alpha v a t

def subcriticalAllTailEvents (p : SubcriticalProfile D eta R₀ theta)
    (alpha : ℝ) : Finset (Finset (SubcriticalActiveCoordinate D eta R₀)) :=
  Finset.univ.filter fun S ↦ ∀ v ∈ p.retainedRoots,
    S ∈ subcriticalRootTailEvent p alpha v

/-- Root-tail probability depends only on the profile, alpha, and active quotas. -/
def subcriticalRootTailProbability (p : SubcriticalProfile D eta R₀ theta)
    (alpha : ℝ) (v : V) (mvec : RetainedEdgeCountVector D eta R₀) : ℝ :=
  (subcriticalActiveBernoulliModel mvec).eventProbability
    (subcriticalRootTailEvent p alpha v)

theorem subcriticalRootTailProbability_mem_Icc
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V)
    (mvec : RetainedEdgeCountVector D eta R₀) :
    subcriticalRootTailProbability p alpha v mvec ∈ Icc (0 : ℝ) 1 :=
  ⟨(subcriticalActiveBernoulliModel mvec).eventProbability_nonneg _,
    (subcriticalActiveBernoulliModel mvec).eventProbability_le_one _⟩

/-- Whether a root has any recorded tail label. -/
def SubcriticalProfile.HasTail (p : SubcriticalProfile D eta R₀ theta) (v : V) : Prop :=
  ∃ a t, p.tails v a = some t

theorem subcriticalRootTailEvent_eq_univ_of_no_tail
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V)
    (h : ¬ p.HasTail v) : subcriticalRootTailEvent p alpha v = Finset.univ := by
  ext S
  simp only [subcriticalRootTailEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    iff_true]
  intro a t ht
  exact (h ⟨a, t, ht⟩).elim

/-- `J_v`: the safe negative logarithm of the finite maximum over the full
narrow quota window. Empty windows use the zero-probability fallback.
An outside root or a root without tails has penalty zero. -/
def subcriticalProfileRootTailPenalty (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C alpha delta epsilon : ℝ) (v : V) : ℝ :=
  if v ∈ p.retainedRoots ∧ p.HasTail v then
    subcriticalNegLogProbability (Fintype.card V)
      (subcriticalFiniteMax (retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon)
        (subcriticalRootTailProbability p alpha v))
  else 0

theorem subcriticalProfileRootTailPenalty_nonneg
    (p : SubcriticalProfile D eta R₀ theta) (m : ℕ) (C alpha delta epsilon : ℝ)
    (v : V) : 0 ≤ subcriticalProfileRootTailPenalty p m C alpha delta epsilon v := by
  unfold subcriticalProfileRootTailPenalty
  split_ifs
  · exact subcriticalNegLogProbability_nonneg _
      ⟨subcriticalFiniteMax_nonneg _ _, subcriticalFiniteMax_le zero_le_one
        (fun v _ ↦ (subcriticalRootTailProbability_mem_Icc _ _ _ v).2)⟩
  · exact le_rfl

theorem subcriticalRootTailProbability_le_exp_penalty
    (p : SubcriticalProfile D eta R₀ theta) (m : ℕ) (C alpha delta epsilon : ℝ)
    (v : V) {mvec : RetainedEdgeCountVector D eta R₀}
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon) :
    subcriticalRootTailProbability p alpha v mvec ≤
      Real.exp (-subcriticalProfileRootTailPenalty p m C alpha delta epsilon v) := by
  unfold subcriticalProfileRootTailPenalty
  split_ifs
  · exact (le_subcriticalFiniteMax _ hm).trans
      (subcriticalProbability_le_exp_negLog _ (subcriticalFiniteMax_nonneg _ _))
  · simpa using (subcriticalRootTailProbability_mem_Icc p alpha v mvec).2

/-- Natural-unit local profile exponent: entropy minus the root-tail penalty. -/
def subcriticalProfileLocalExponent (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C alpha delta epsilon : ℝ) (v : V) : ℝ :=
  subcriticalProfileRootEntropyNat p v -
    subcriticalProfileRootTailPenalty p m C alpha delta epsilon v

/-- No residual pair is contained in an induced star whose whole
image avoids the roots. A pair is specified by its endpoints; it need not
be an edge of the star (residual missing defects must also be tested). -/
def subcriticalResidualSafeAwayFromRootsEvent
    (p : SubcriticalProfile D eta R₀ theta) (R : SimpleGraph V) : Set (SimpleGraph V) :=
  {G | ∀ f : inducedStar k ↪g G, (∀ i, f i ∉ p.roots) →
    ∀ i j, ¬ R.Adj (f i) (f j)}

theorem subcriticalResidualSafeAwayFromRoots_of_induced_free
    (p : SubcriticalProfile D eta R₀ theta) (R G : SimpleGraph V)
    (h : ¬ Regularity.InducedEmbeds (inducedStar k) G) :
    G ∈ subcriticalResidualSafeAwayFromRootsEvent p R := by
  intro f
  exact (h ⟨f⟩).elim

def subcriticalResidualSafeProbability (p : SubcriticalProfile D eta R₀ theta)
    (H : SubcriticalRemainderGraph D eta R₀) (TB R L : SimpleGraph V)
    (mvec : RetainedEdgeCountVector D eta R₀) : ℝ :=
  subcriticalActiveBernoulliProbability H (TB ⊔ R ⊔ L) mvec
    (subcriticalResidualSafeAwayFromRootsEvent p R)

theorem subcriticalResidualSafeProbability_mem_Icc
    (p : SubcriticalProfile D eta R₀ theta) (H : SubcriticalRemainderGraph D eta R₀)
    (TB R L : SimpleGraph V) (mvec : RetainedEdgeCountVector D eta R₀) :
    subcriticalResidualSafeProbability p H TB R L mvec ∈ Icc (0 : ℝ) 1 :=
  ⟨(subcriticalActiveBernoulliModel mvec).eventProbability_nonneg _,
    (subcriticalActiveBernoulliModel mvec).eventProbability_le_one _⟩

/-- Explicit residual weight coefficient, independent of profile and order. -/
def subcriticalResidualWeightConstant (k : ℕ) : ℝ :=
  |subcriticalLogOddsNat k| + subcriticalActiveLevelConstant k + 1

theorem subcriticalResidualWeightConstant_pos (k : ℕ) :
    0 < subcriticalResidualWeightConstant k := by
  have h : 3 ≤ subcriticalActiveLevelConstant k := le_max_left _ _
  unfold subcriticalResidualWeightConstant
  linarith [abs_nonneg (subcriticalLogOddsNat k)]

/-- The precise admissible inner family: an induced-free remainder, a
leftover compatible with that full remainder, and a narrow vector. -/
def subcriticalMatchingAdmissibleData (F : Finset (SimpleGraph V))
    (p : SubcriticalProfile D eta R₀ theta) (m : ℕ) (C alpha delta epsilon : ℝ)
    (TB R : SimpleGraph V) :
    Finset (SubcriticalRemainderGraph D eta R₀ × SimpleGraph V ×
      RetainedEdgeCountVector D eta R₀) :=
  Finset.univ.filter fun z ↦
    ¬ Regularity.InducedEmbeds (inducedStar k) z.1 ∧
      z.2.1 ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p z.1 TB R ∧
      z.2.2 ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon

/-- The admissible residual-probability maximum, still indexed by `TB,R`. -/
def subcriticalResidualSafeMaximum (F : Finset (SimpleGraph V))
    (p : SubcriticalProfile D eta R₀ theta) (m : ℕ) (C alpha delta epsilon : ℝ)
    (TB R : SimpleGraph V) : ℝ :=
  subcriticalFiniteMax (subcriticalMatchingAdmissibleData F p m C alpha delta epsilon TB R)
    (fun z ↦ subcriticalResidualSafeProbability p z.1 TB R z.2.1 z.2.2)

/-- The weighted sum is retained inside the outer maximum; it must not be
replaced by a separate pointwise bound before summing over residual graphs. -/
def subcriticalProfileMatchingWeight (F : Finset (SimpleGraph V))
    (p : SubcriticalProfile D eta R₀ theta) (m : ℕ) (C alpha delta epsilon : ℝ) : ℝ :=
  subcriticalFiniteMax (subcriticalRootedDefectPatternFinset F alpha p) fun TB ↦
    ∑ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
      Real.exp (subcriticalResidualWeightConstant k * (finiteGraphEdges R).card) *
        subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R

/-- Natural-log matching exponent, with a negative cubic value at weight zero.
The definition retains natural units, fixed-remainder compatibility, and root-avoiding residual safety. -/
def subcriticalProfileMatchingExponent (F : Finset (SimpleGraph V))
    (p : SubcriticalProfile D eta R₀ theta) (m : ℕ) (C alpha delta epsilon : ℝ) : ℝ :=
  subcriticalLogWeight (Fintype.card V)
    (subcriticalProfileMatchingWeight F p m C alpha delta epsilon)

/-- The level-comparison residual cost is absorbed by the explicit matching
weight. This uses only the signed-size bound, not any matching estimate. -/
theorem subcriticalResidualSignedCost_le (T : SimpleGraph V) {delta : ℝ}
    (hd : 0 ≤ delta) (hd1 : delta ≤ 1) :
    -subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ T : ℝ) +
        subcriticalActiveLevelConstant k * delta *
          |(subcriticalSignedDefectSize D eta R₀ T : ℝ)| ≤
      subcriticalResidualWeightConstant k * (finiteGraphEdges T).card := by
  have hc : 0 ≤ subcriticalActiveLevelConstant k :=
    (by norm_num : (0 : ℝ) ≤ 3).trans (le_max_left _ _)
  have hs : |(subcriticalSignedDefectSize D eta R₀ T : ℝ)| ≤
      (finiteGraphEdges T).card := by
    exact_mod_cast abs_subcriticalSignedDefectSize_le D eta R₀ T
  have hlead : -subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ T : ℝ) ≤
      |subcriticalLogOddsNat k| * |(subcriticalSignedDefectSize D eta R₀ T : ℝ)| := by
    simpa only [abs_mul, abs_neg] using
      le_abs_self (-subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ T : ℝ))
  have hdelta := mul_le_of_le_one_right hc hd1
  have hcost := mul_le_mul_of_nonneg_right hdelta
    (abs_nonneg (subcriticalSignedDefectSize D eta R₀ T : ℝ))
  have hsum := mul_le_mul_of_nonneg_left hs
    (add_nonneg (abs_nonneg (subcriticalLogOddsNat k)) hc)
  unfold subcriticalResidualWeightConstant
  nlinarith [show (0 : ℝ) ≤ (finiteGraphEdges T).card by positivity]

theorem subcriticalResidualSafeMaximum_nonneg (F : Finset (SimpleGraph V))
    (p : SubcriticalProfile D eta R₀ theta) (m : ℕ) (C alpha delta epsilon : ℝ)
    (TB R : SimpleGraph V) :
    0 ≤ subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R :=
  subcriticalFiniteMax_nonneg _ _

theorem subcriticalResidualSafeProbability_le_maximum
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C alpha delta epsilon : ℝ) (H : SubcriticalRemainderGraph D eta R₀)
    (TB R L : SimpleGraph V) (mvec : RetainedEdgeCountVector D eta R₀)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) H)
    (hL : L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon) :
    subcriticalResidualSafeProbability p H TB R L mvec ≤
      subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R := by
  unfold subcriticalResidualSafeMaximum
  apply le_subcriticalFiniteMax (i := (H, L, mvec))
    (fun z ↦ subcriticalResidualSafeProbability p z.1 TB R z.2.1 z.2.2)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfree, hL, hm⟩

/-- The sum form needed in the master bound. It avoids introducing an
unwanted factor equal to the number of residual patterns. -/
theorem subcriticalResidualWeightedSum_le_exp_matching
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C alpha delta epsilon : ℝ) {TB : SimpleGraph V}
    (hTB : TB ∈ subcriticalRootedDefectPatternFinset F alpha p) :
    (∑ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
      Real.exp (subcriticalResidualWeightConstant k * (finiteGraphEdges R).card) *
        subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R) ≤
      Real.exp (subcriticalProfileMatchingExponent F p m C alpha delta epsilon) := by
  unfold subcriticalProfileMatchingExponent subcriticalProfileMatchingWeight
  exact (le_subcriticalFiniteMax (fun TB ↦
    ∑ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
      Real.exp (subcriticalResidualWeightConstant k * (finiteGraphEdges R).card) *
        subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R) hTB).trans
    (subcriticalWeight_le_exp_logWeight _ (subcriticalFiniteMax_nonneg _ _))

/-- Weighted pointwise residual bound. The full weighted sum above is also
retained for summation in the master profile theorem. -/
theorem subcriticalResidualSafeProbability_le_exp_matching
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C alpha delta epsilon : ℝ) (H : SubcriticalRemainderGraph D eta R₀)
    (TB R L : SimpleGraph V) (mvec : RetainedEdgeCountVector D eta R₀)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) H)
    (hL : L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon) :
    subcriticalResidualSafeProbability p H TB R L mvec ≤
      Real.exp (subcriticalProfileMatchingExponent F p m C alpha delta epsilon -
        subcriticalResidualWeightConstant k * (finiteGraphEdges R).card) := by
  obtain ⟨G, hG, _, hGB, hGR, _⟩ :=
    (mem_subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R L).mp hL
  have hTB : TB ∈ subcriticalRootedDefectPatternFinset F alpha p :=
    Finset.mem_image.mpr ⟨G, hG, hGB⟩
  have hR : R ∈ subcriticalResidualDefectPatternFinset F alpha p TB :=
    Finset.mem_image.mpr ⟨G, Finset.mem_filter.mpr ⟨hG, hGB⟩, hGR⟩
  have hmax := subcriticalResidualSafeProbability_le_maximum F p m C alpha delta epsilon
    H TB R L mvec hfree hL hm
  have hsum := Finset.single_le_sum
    (fun R _ ↦ mul_nonneg
      (Real.exp_pos (subcriticalResidualWeightConstant k * (finiteGraphEdges R).card)).le
      (subcriticalResidualSafeMaximum_nonneg F p m C alpha delta epsilon TB R)) hR
  have hbound := (mul_le_mul_of_nonneg_left hmax (Real.exp_pos _).le).trans
    (hsum.trans (subcriticalResidualWeightedSum_le_exp_matching
      F p m C alpha delta epsilon hTB))
  rw [Real.exp_sub]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hbound)

theorem subcriticalResidualSafeProbability_le_exp_matching_weak
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C alpha delta epsilon : ℝ) (H : SubcriticalRemainderGraph D eta R₀)
    (TB R L : SimpleGraph V) (mvec : RetainedEdgeCountVector D eta R₀)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) H)
    (hL : L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon) :
    subcriticalResidualSafeProbability p H TB R L mvec ≤
      Real.exp (subcriticalProfileMatchingExponent F p m C alpha delta epsilon) := by
  apply (subcriticalResidualSafeProbability_le_exp_matching
    F p m C alpha delta epsilon H TB R L mvec hfree hL hm).trans
  apply Real.exp_le_exp.mpr
  exact sub_le_self _ (mul_nonneg (subcriticalResidualWeightConstant_pos k).le
    (Nat.cast_nonneg _))

end InducedStars
