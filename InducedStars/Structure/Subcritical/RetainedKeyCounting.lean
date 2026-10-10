import InducedStars.Structure.Subcritical.RetainedKeyFamilies

/-!
# An exponential bound for retained keys

Only retained cores and their actual parts are encoded.  At most
`ceil (1/eta)` components remain, each of order at most `R₀`.  Counting every
possible finset in these boundedly many slots gives `exp(C*n)`, uniformly
in the candidate representation.  No discarded completion is counted.
-/

noncomputable section
open Finset
open scoped Classical BigOperators

namespace InducedStars

private abbrev BoundedRetainedCore (k R : ℕ) :=
  {C : RegularBlockCore k // C.order ≤ R}

private instance (k R : ℕ) : Fintype (BoundedRetainedCore k R) := Fintype.ofFinite _

/-- A finite constant depending only on the regular-core parameter and the
fixed order cutoff.  It counts labeled cores, including their labels. -/
def retainedKeyBoundedCoreCount (k R : ℕ) : ℕ :=
  Nat.card {C : RegularBlockCore k // C.order ≤ R}

private abbrev BoundedRetainedDivision {V : Type*} [Fintype V] [DecidableEq V]
    (k B R : ℕ) :=
  {D : SubcriticalDivision k V // D.componentCount ≤ B ∧ ∀ i, (D.core i).order ≤ R}

private abbrev RetainedDivisionCode (k B R : ℕ) (V : Type*) [Fintype V] :=
  Σ l : Fin (B + 1), Σ C : Fin l.val → BoundedRetainedCore k R,
    (i : Fin l.val) → Fin (C i).val.order → Finset V

private def boundedRetainedDivisionCode {V : Type*} [Fintype V] [DecidableEq V]
    {k B R : ℕ} (D : BoundedRetainedDivision (V := V) k B R) :
    RetainedDivisionCode k B R V :=
  ⟨⟨D.val.componentCount, Nat.lt_succ_of_le D.prop.1⟩,
    (fun i ↦ ⟨D.val.core i, D.prop.2 i⟩), D.val.parts⟩

private theorem boundedRetainedDivisionCode_injective
    {V : Type*} [Fintype V] [DecidableEq V] {k B R : ℕ} :
    Function.Injective (boundedRetainedDivisionCode (V := V) (k := k) (B := B) (R := R)) := by
  rintro ⟨D, hD⟩ ⟨E, hE⟩ h
  apply Subtype.ext
  have hc : D.componentCount = E.componentCount := congrArg (fun z ↦ z.1.val) h
  rcases D with ⟨l, hl, C, P, hp, hd⟩
  rcases E with ⟨l', hl', C', P', hp', hd'⟩
  dsimp at hc
  subst l'
  have hrest := (Sigma.mk.inj h).2
  have hcodes : (fun i ↦ (⟨C i, hD.2 i⟩ : BoundedRetainedCore k R)) =
      (fun i ↦ (⟨C' i, hE.2 i⟩ : BoundedRetainedCore k R)) :=
    congrArg Sigma.fst (eq_of_heq hrest)
  have hC : C = C' := by
    funext i
    exact congrArg Subtype.val (congrFun hcodes i)
  subst C'
  have hP : P = P' := by simpa [boundedRetainedDivisionCode] using h
  subst P'
  rfl

private theorem card_retainedDivisionCode_le (k B R : ℕ)
    (V : Type*) [Fintype V] :
    Fintype.card (RetainedDivisionCode k B R V) ≤
      (B + 1) * (retainedKeyBoundedCoreCount k R + 1) ^ B *
        2 ^ (Fintype.card V * (R * B)) := by
  classical
  have hcore : Fintype.card (BoundedRetainedCore k R) = retainedKeyBoundedCoreCount k R :=
    Nat.card_eq_fintype_card.symm
  have hpart (l : Fin (B + 1)) (C : Fin l.val → BoundedRetainedCore k R) :
      Fintype.card ((i : Fin l.val) → Fin (C i).val.order → Finset V) ≤
        2 ^ (Fintype.card V * (R * B)) := by
    simp only [Fintype.card_pi, Fintype.card_finset, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum, ← pow_mul]
    apply Nat.pow_le_pow_right (by omega : 1 ≤ 2)
    apply Nat.mul_le_mul_left
    calc
      ∑ i : Fin l.val, (C i).val.order ≤ ∑ _i : Fin l.val, R :=
        Finset.sum_le_sum fun i _ ↦ (C i).prop
      _ = R * l.val := by simp [mul_comm]
      _ ≤ R * B := Nat.mul_le_mul_left R (Nat.lt_succ_iff.mp l.isLt)
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _l : Fin (B + 1),
        (retainedKeyBoundedCoreCount k R + 1) ^ B *
          2 ^ (Fintype.card V * (R * B)) := by
      apply Finset.sum_le_sum
      intro l _
      rw [Fintype.card_sigma]
      calc
        _ ≤ ∑ _C : Fin l.val → BoundedRetainedCore k R,
            2 ^ (Fintype.card V * (R * B)) :=
          Finset.sum_le_sum fun C _ ↦ hpart l C
        _ = (retainedKeyBoundedCoreCount k R) ^ l.val *
            2 ^ (Fintype.card V * (R * B)) := by simp [hcore]
        _ ≤ _ := Nat.mul_le_mul_right _
          ((Nat.pow_le_pow_left (Nat.le_succ _) _).trans
            (Nat.pow_le_pow_right (by omega) (Nat.lt_succ_iff.mp l.isLt)))
    _ = _ := by simp [mul_assoc]

/-- A finite family of retained-only keys with bounded component count and
bounded core order has at most exponentially many actual vertex-part arrays. -/
theorem card_retainedKey_family_le {V : Type*} [Fintype V] [DecidableEq V]
    (k B R : ℕ) (F : Finset (SubcriticalRetainedKey k V))
    (hF : ∀ D, some D ∈ F → D.componentCount ≤ B ∧ ∀ i, (D.core i).order ≤ R) :
    F.card ≤ 1 + (B + 1) * (retainedKeyBoundedCoreCount k R + 1) ^ B *
      2 ^ (Fintype.card V * (R * B)) := by
  classical
  let encode : F → Option (RetainedDivisionCode k B R V) := fun K ↦
    match h : K.val with
    | none => none
    | some D => some (boundedRetainedDivisionCode ⟨D, hF D (h ▸ K.prop)⟩)
  have hinj : Function.Injective encode := by
    intro K L h
    apply Subtype.ext
    rcases K with ⟨K, hK⟩
    rcases L with ⟨L, hL⟩
    cases K with
    | none => cases L <;> simpa [encode] using h
    | some D =>
      cases L with
      | none => simp [encode] at h
      | some E =>
        have hh := boundedRetainedDivisionCode_injective (Option.some.inj h)
        exact congrArg (fun z : BoundedRetainedDivision (V := V) k B R ↦ some z.val) hh
  have hc := Fintype.card_le_of_injective encode hinj
  have hb := card_retainedDivisionCode_le k B R V
  simp only [Fintype.card_coe, Fintype.card_option] at hc
  exact hc.trans (by simpa only [Nat.add_comm] using Nat.add_le_add_right hb 1)

/-- Retention itself, without compatibility or ordering assumptions, bounds
the number of recorded components and the order of every recorded core. -/
theorem retainedKey_some_bounds {V : Type*} [Fintype V] [DecidableEq V]
    {k R₀ : ℕ} (D E : SubcriticalDivision k V) {eta : ℝ} (heta : 0 < eta)
    (h : retainedKey D eta R₀ = some E) :
    E.componentCount ≤ Nat.ceil (1 / eta) ∧ ∀ i, (E.core i).order ≤ R₀ := by
  have hcount : D.retainedComponentCount eta R₀ ≤ Nat.ceil (1 / eta) := by
    have hh : (D.retainedComponentCount eta R₀ : ℝ) ≤ 1 / eta := by
      apply (le_div_iff₀ heta).mpr
      simpa [mul_comm] using D.eta_mul_retainedComponentCount_le_one eta R₀
    exact_mod_cast hh.trans (Nat.le_ceil _)
  unfold retainedKey at h
  split_ifs at h with hn
  · have he := Option.some.inj h
    subst E
    constructor
    · exact hcount
    · intro i
      exact ((D.mem_retainedComponentIndices eta R₀ _).mp
        ((D.retainedComponentIndices eta R₀).orderIsoOfFin rfl i).property).2

/-- The finite image count depends on `eta,R₀,k,n`, never on the candidate
sequence or its chosen compatible completion. -/
theorem card_compatibleRetainedKeys_le_encoding
    (k n : ℕ) (L : AdmissibleBlockSequence k) {eta : ℝ} (heta : 0 < eta)
    (delta : ℝ) (R₀ : ℕ) :
    (compatibleRetainedKeys k n L eta delta R₀).card ≤
      1 + (Nat.ceil (1 / eta) + 1) *
        (retainedKeyBoundedCoreCount k R₀ + 1) ^ Nat.ceil (1 / eta) *
        2 ^ (n * (R₀ * Nat.ceil (1 / eta))) := by
  simpa only [Fintype.card_fin] using
    (card_retainedKey_family_le k (Nat.ceil (1 / eta)) R₀
      (compatibleRetainedKeys k n L eta delta R₀) (by
        intro E hE
        obtain ⟨D, _, hD⟩ := mem_compatibleRetainedKeys.mp hE
        exact retainedKey_some_bounds D E heta hD))

/-- The fixed finite factor for the bounded list of labeled regular cores. -/
def retainedKeyEncodingFactor (k : ℕ) (eta : ℝ) (R₀ : ℕ) : ℕ :=
  (Nat.ceil (1 / eta) + 1) *
    (retainedKeyBoundedCoreCount k R₀ + 1) ^ Nat.ceil (1 / eta)

/-- A uniform exponential counting constant; no candidate sequence or vertex
count occurs in its definition. -/
def retainedKeyCountingConstant (k : ℕ) (eta : ℝ) (R₀ : ℕ) : ℝ :=
  2 * (retainedKeyEncodingFactor k eta R₀ : ℝ) +
    2 * (R₀ * Nat.ceil (1 / eta) : ℕ)

theorem retainedKeyCountingConstant_pos (k : ℕ) (eta : ℝ) (R₀ : ℕ) :
    0 < retainedKeyCountingConstant k eta R₀ := by
  unfold retainedKeyCountingConstant retainedKeyEncodingFactor
  positivity

/-- The actual deduplicated compatible key family has `exp(C*n)`
elements, uniformly in `L`, `delta`, and `n`.  The constant is fixed by
`k,eta,R₀` alone.  This also handles the empty ambient vertex set. -/
theorem card_compatibleRetainedKeys_le_exp
    (k n : ℕ) (L : AdmissibleBlockSequence k) {eta : ℝ} (heta : 0 < eta)
    (delta : ℝ) (R₀ : ℕ) :
    ((compatibleRetainedKeys k n L eta delta R₀).card : ℝ) ≤
      Real.exp (retainedKeyCountingConstant k eta R₀ * n) := by
  classical
  by_cases hn : n = 0
  · subst n
    have he : compatibleRetainedKeys k 0 L eta delta R₀ = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro K hK
      obtain ⟨D, _, _⟩ := mem_compatibleRetainedKeys.mp hK
      have hh := D.componentCount_le_card
      have hp := D.componentCount_pos
      simp only [Fintype.card_fin] at hh
      omega
    simp [he]
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  let A := retainedKeyEncodingFactor k eta R₀
  let Q := R₀ * Nat.ceil (1 / eta)
  have henc := card_compatibleRetainedKeys_le_encoding k n L heta delta R₀
  change (compatibleRetainedKeys k n L eta delta R₀).card ≤ 1 + A * 2 ^ (n * Q) at henc
  have hApos : 0 < A := by dsimp [A, retainedKeyEncodingFactor]; positivity
  have hnat : (compatibleRetainedKeys k n L eta delta R₀).card ≤
      (2 * A) * 2 ^ (n * Q) := by
    have hp : 0 < A * 2 ^ (n * Q) := by positivity
    nlinarith
  have hAe : (2 * A : ℝ) ≤ Real.exp (2 * A) := by
    linarith [Real.add_one_le_exp (2 * (A : ℝ))]
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hpow : (2 : ℝ) ^ (n * Q) ≤ Real.exp (2 * (n * Q : ℕ)) := by
    calc
      _ ≤ (Real.exp 2) ^ (n * Q) := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  calc
    _ ≤ (2 * A : ℝ) * 2 ^ (n * Q) := by exact_mod_cast hnat
    _ ≤ Real.exp (2 * A) * Real.exp (2 * (n * Q : ℕ)) :=
      mul_le_mul hAe hpow (by positivity) (by positivity)
    _ = Real.exp (2 * A + 2 * (n * Q : ℕ)) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      change 2 * (A : ℝ) + 2 * (n * Q : ℕ) ≤ (2 * A + 2 * Q) * n
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg A) (sub_nonneg.mpr hnreal)]

end InducedStars
