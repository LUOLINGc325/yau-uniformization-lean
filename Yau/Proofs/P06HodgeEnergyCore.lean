import Yau.Proofs.P06HodgeEnergyPairings

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

theorem realizeActualForm_congr (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : RealForm M k) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B)
    (he : A = B) : realizeActualForm g μ A hA = realizeActualForm g μ B hB := by
  subst B
  rfl

theorem compactlySupportedRealForm_smul (c : ℝ) (A : RealForm M k)
    (hcA : CompactlySupportedRealForm A) : CompactlySupportedRealForm (c • A) := by
  apply hcA.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro x hx
  change A x ≠ 0
  intro h
  exact hx (by simp only [Pi.smul_apply, h, smul_zero])

theorem realizeActualForm_smul (g : SmoothMetric M) (μ : Measure M.Carrier)
    (c : ℝ) (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    realizeActualForm g μ (c • A) (l2RealForm_smul g μ c A hA) =
      c • realizeActualForm g μ A hA := by
  let F : L2FormSpace g μ k →L[ℝ] L2FormHilbert g μ k := UniformSpace.Completion.toComplL
  exact F.map_smul c (L2FormSpace.ofSection A hA)

theorem hodgeEnergyCoreTuple_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    hodgeEnergyCoreTuple g μ hμ (A + B) (smoothRealForm_add A B hA hB)
      (compactlySupportedRealForm_add A B hcA hcB) =
        hodgeEnergyCoreTuple g μ hμ A hA hcA + hodgeEnergyCoreTuple g μ hμ B hB hcB := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact realizeActualForm_add g μ A B _ _
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change realizeActualForm g μ (exteriorRealForm (A + B)) _ = _
      exact (realizeActualForm_congr g μ _ _ _ _ (exteriorRealForm_add A B hA hB)).trans
        (realizeActualForm_add g μ _ _ (exteriorRealForm_l2 g μ hμ A hA hcA)
          (exteriorRealForm_l2 g μ hμ B hB hcB))
    · change realizeActualForm g μ (codifferentialRealForm g.form (A + B)) _ = _
      exact (realizeActualForm_congr g μ _ _ _ _ (codifferentialRealForm_add g μ hμ A B hA hB)).trans
        (realizeActualForm_add g μ _ _ (codifferentialRealForm_l2 g μ hμ A hA hcA)
          (codifferentialRealForm_l2 g μ hμ B hB hcB))

theorem hodgeEnergyCoreTuple_smul (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (c : ℝ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    hodgeEnergyCoreTuple g μ hμ (c • A) (smoothRealForm_smul c A hA)
      (compactlySupportedRealForm_smul c A hcA) =
        c • hodgeEnergyCoreTuple g μ hμ A hA hcA := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact realizeActualForm_smul g μ c A _
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change realizeActualForm g μ (exteriorRealForm (c • A)) _ = _
      exact (realizeActualForm_congr g μ _ _ _ _ (exteriorRealForm_smul c A hA)).trans
        (realizeActualForm_smul g μ c _ (exteriorRealForm_l2 g μ hμ A hA hcA))
    · change realizeActualForm g μ (codifferentialRealForm g.form (c • A)) _ = _
      exact (realizeActualForm_congr g μ _ _ _ _ (codifferentialRealForm_smul g μ hμ c A hA)).trans
        (realizeActualForm_smul g μ c _ (codifferentialRealForm_l2 g μ hμ A hA hcA))

def hodgeEnergyCoreSubmodule (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : Submodule ℝ (HodgeEnergyAmbient g μ) where
  carrier := hodgeEnergyCoreSet g μ hμ
  zero_mem' := by
    have hs : SmoothRealForm (0 : RealForm M 2) := smoothRealForm_zero
    have hc : CompactlySupportedRealForm (0 : RealForm M 2) := by
      simpa [CompactlySupportedRealForm] using (isCompact_empty : IsCompact (∅ : Set M.Carrier))
    refine ⟨0, hs, hc, ?_⟩
    have he := hodgeEnergyCoreTuple_smul g μ hμ 0 0 hs hc
    simpa only [zero_smul] using he.symm
  add_mem' := by
    rintro p q ⟨A, hA, hcA, rfl⟩ ⟨B, hB, hcB, rfl⟩
    exact ⟨A + B, smoothRealForm_add A B hA hB, compactlySupportedRealForm_add A B hcA hcB,
      (hodgeEnergyCoreTuple_add g μ hμ A B hA hcA hB hcB).symm⟩
  smul_mem' := by
    rintro c p ⟨A, hA, hcA, rfl⟩
    exact ⟨c • A, smoothRealForm_smul c A hA, compactlySupportedRealForm_smul c A hcA,
      (hodgeEnergyCoreTuple_smul g μ hμ c A hA hcA).symm⟩

theorem hodgeEnergySubmodule_eq_closure (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) :
    (hodgeEnergySubmodule g μ hμ : Set (HodgeEnergyAmbient g μ)) = closure (hodgeEnergyCoreSet g μ hμ) := by
  change ((Submodule.span ℝ (hodgeEnergyCoreSet g μ hμ)).topologicalClosure : Set (HodgeEnergyAmbient g μ)) = _
  have he : Submodule.span ℝ (hodgeEnergyCoreSet g μ hμ) = hodgeEnergyCoreSubmodule g μ hμ :=
    Submodule.span_eq (R := ℝ) (p := hodgeEnergyCoreSubmodule g μ hμ)
  rw [he, Submodule.topologicalClosure_coe]
  rfl

end Yau.NodeProofs.P06Aux
