import Yau.Proofs.C02FieldOrder
import Yau.Proofs.C02SmoothPaths

/-! Comparing the actual length distances. The near-minimizing path is chosen
smoothly, so its two genuine metric speeds are integrable independently. -/

noncomputable section
open MeasureTheory
open scoped Manifold ENNReal
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem inducedDistance_le_of_gMat_order (k₀ k₁ : HermitianField M)
    (hk₀ : MetricSmooth k₀) (hk₁ : MetricSmooth k₁)
    (hle : ∀ x, HermLE (gMat k₀ x) (gMat k₁ x)) (x y : M.Carrier) :
    inducedDistance k₀ x y ≤ inducedDistance k₁ x y := by
  let := L12Aux.manifold_realSmooth M
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨γ, hγ, hshort⟩ := exists_smooth_nearMinimizingCurve k₁ hk₁ x y ε hε
  have hIntegrable : IntegrableOn (curveSpeed k₀ γ.1) (Set.Icc (0 : ℝ) 1) := by
    have h := L23Aux.integrable_curveSpeed_of_contMDiff k₀ hk₀ hγ
    change IntegrableOn (curveSpeed k₀ γ.1) (Set.Icc (0 : ℝ) 1) at h
    exact h
  let γ₀ : IntegrableCurve k₀ x y := ⟨γ.1, hIntegrable⟩
  have hLength : curveLength k₀ γ.1 ≤ curveLength k₁ γ.1 := by
    exact setIntegral_mono_on hIntegrable γ.2 measurableSet_Icc
      (fun s _ => curveSpeed_le_of_gMat_order k₀ k₁ hle γ.1 s)
  exact (L12Aux.inducedDistance_le_curveLength k₀ γ₀).trans (hLength.trans hshort.le)

end Yau.Blueprint.C02Proof
