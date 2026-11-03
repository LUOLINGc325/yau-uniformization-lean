import Yau.Proofs.F01NormalizedBackgroundTensorJets
import Yau.Proofs.F01AffineParabolicHolder

/-! The actual normalized clamped background is spatially smooth at
every time, and its fixed log-determinant source has all-order numerical
Holder budgets before the center and scale. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def normalizedPotentialLogSource (A : BoundedChartFamily g) (a : M.Carrier) (ρ : ℝ)
    (z : Space n) : ℝ := -A.backgroundLogDet a (ρ • z)

theorem normalizedComplexBackground_smooth_spatial_slice (A : BoundedChartFamily g)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (a : M.Carrier) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun z => normalizedComplexBackground A a ρ (z, t)) (ball 0 1) := by
  have hd : ContDiffOn ℝ ∞ (fun z : Space n => ρ • z) (ball 0 1) := by fun_prop
  have hm := (background_matrix_frobenius_smooth A a).comp hd
    (fun z hz => spatialDilation_mem_ball hρ hρr hz)
  have hr := (backgroundRicci_frobenius_smooth A a).comp hd
    (fun z hz => spatialDilation_mem_ball hρ hρr hz)
  exact hm.add ((hr.const_smul (-(ρ ^ 2))).const_smul (max t 0))

theorem normalizedPotentialLogSource_smooth (A : BoundedChartFamily g)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (a : M.Carrier) :
    ContDiffOn ℝ ∞ (normalizedPotentialLogSource A a ρ) (ball 0 1) := by
  have hd : ContDiffOn ℝ ∞ (fun z : Space n => ρ • z) (ball 0 1) := by fun_prop
  exact ((A.backgroundLogDet_smooth a).comp hd
    (fun z hz => spatialDilation_mem_ball hρ hρr hz)).neg

theorem normalizedPotentialLogSource_spatial_holder_budgets
    (A : BoundedChartFamily g) {β : ℝ} (hβ : β ≤ 1) :
    ∃ K : ℕ → ℝ, (∀ k, 0 < K k) ∧ ∀ k (ρ : ℝ),
      0 < ρ → ρ ≤ A.radius → ρ ≤ 1 → ∀ a : M.Carrier,
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => iteratedFDeriv ℝ k (normalizedPotentialLogSource A a ρ) p.1) (K k) := by
  have each : ∀ k : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ (ρ : ℝ),
      0 < ρ → ρ ≤ A.radius → ρ ≤ 1 → ∀ a : M.Carrier,
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => iteratedFDeriv ℝ k (normalizedPotentialLogSource A a ρ) p.1) K := by
    intro k
    obtain ⟨K, hK, hk⟩ := dilated_affine_spatial_tensor_holder_budget k
      (A.backgroundLogDet_uniformJetBounds (k + 1))
      (A.backgroundLogDet_uniformJetBounds (k + 1))
      A.backgroundLogDet_smooth A.backgroundLogDet_smooth hβ
    refine ⟨K, hK, ?_⟩
    intro ρ hρ hρr hρ1 a
    have hRaw := hk ρ hρ hρr hρ1 0 (by norm_num) a
    have hPositive : HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => iteratedFDeriv ℝ k (fun z => A.backgroundLogDet a (ρ • z)) p.1) K := by
      simpa only [zero_smul, smul_zero, add_zero] using hRaw
    apply holderBound_congr_on_native (holderBound_neg hPositive)
    intro p hp
    exact (iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := k)
      (f := fun z => A.backgroundLogDet a (ρ • z)) (x := p.1)).symm
  choose K hK hk using each
  exact ⟨K, hK, hk⟩

end Yau.NodeProofs.F01Aux
