import InducedStars.Structure.Subcritical.UnifiedRootPenalty

/-!
# Derived retained-root interfaces

These interfaces specialize the unified target-deficit theorem to the three
stored-count ranges. They are not used by the local-compensation proof.
-/

noncomputable section
open Finset
open scoped Classical
namespace InducedStars
variable {k n R₀ : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
  {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
  {omega eta theta alpha delta epsilon rho : ℝ}

/-- The established three-range interface, derived from the uniform retained
root theorem without a case split in its proof. -/
theorem subcriticalRetainedRootPenalties_of_geometry
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (ha5 : 5 * alpha ≤ 1)
    (hsmall : (4 * (k : ℝ) + 8) * alpha ≤ 1)
    (htheta : 0 < theta) (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hdp : 2 * delta ≤ pK k) (hdq : 2 * delta ≤ 1 - pK k)
    (hn : 0 < n) (hscale : 8 ≤ alpha * theta * n)
    (hrho : 0 ≤ rho) (hR : 1 ≤ R₀) (heta : 0 < eta)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (hp : RealizesSubcriticalProfile G alpha p)
    (hB : (p.roots.card : ℝ) ≤ rho * n)
    (hBalpha : ∀ a ∈ D.visiblePartIndices theta,
      (p.roots.card : ℝ) + 1 ≤ alpha * (D.part a).card)
    (hxi1 : subcriticalTrimErrorNat rho theta < 1)
    (hownband : subcriticalSmallOwnConstant k * alpha /
      (1 - subcriticalTrimErrorNat rho theta) ≤ 1 / 2)
    (htailband : 2 * alpha / (1 - subcriticalTrimErrorNat rho theta) ≤ 1 / 2)
    (hsentinel : ((k - 2 : ℕ) : ℝ) * subcriticalLocalU_Nat k ≤ (n + 1 : ℝ) ^ 2)
    (herror : subcriticalTotalErrorNat k R₀ eta alpha delta
      (subcriticalTrimErrorNat rho theta) (subcriticalInsideScaleErrorNat alpha delta theta n) ≤
        subcriticalLocalA_Nat k / 4)
    (hminimal : ∀ E : SubcriticalDivision k (Fin n),
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : Fin n) (hv : v ∈ p.retainedRoots)
    (hsource : 2 ≤ (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hbalance : ∀ b : D.PartIndex,
      b.1 = (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1 →
      ((D.part b).card : ℝ) ≤ 2 *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (m : ℕ) (C : ℝ) :
    (2 * alpha *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots).card ≤
          ((p.ownCount v).val : ℝ) →
      ((p.ownCount v).val : ℝ) ≤ (1 - 2 * alpha) *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots).card →
      subcriticalProfileLocalExponent p m C alpha delta epsilon v ≤
        -(subcriticalLocalA_Nat k / 2) *
          (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card) ∧
    ((1 - 2 * alpha) *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots).card ≤
          ((p.ownCount v).val : ℝ) →
      subcriticalProfileLocalExponent p m C alpha delta epsilon v ≤
        -(subcriticalLocalA_Nat k / 2) *
          (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card) ∧
    (((p.ownCount v).val : ℝ) < 2 * alpha *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots).card →
      subcriticalProfileLocalExponent p m C alpha delta epsilon v ≤
        -(subcriticalLocalA_Nat k / 2) *
          (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card) := by
  have h := subcriticalRetainedRootUnifiedPenalty R hfree homega halpha ha5 hsmall
    htheta hdelta0 hdelta hdp hdq hn hscale hrho hR heta hret hp hB hBalpha
    hxi1 hownband htailband hsentinel herror hminimal v hv hsource hbalance m C
  exact ⟨fun _ _ ↦ h, fun _ ↦ h, fun _ ↦ h⟩

end InducedStars
