import Yau.LeafProofs.L05AutonomousPeanoEquationPolynomial

noncomputable section
open Filter Set Asymptotics
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

theorem auto_peano_residual_eq {n : ℕ} {Q : Set (Point n)}
    {F : Sym n → ℝ} {u V : Point n → ℝ}
    (hQ : IsOpen Q) (hF : Continuous F) (hu : ContinuousOn u Q) (hV : ContinuousOn V Q)
    (hTime : ∀ q∈Q, HasDerivAt (fun t => u (q.1,t)) (V q) q.2)
    (hsol : viscositySolution Q (fun H _ => F H) (fun _ => 0) u)
    {p : Point n} (hp : p∈Q) (l : Space n →L[ℝ] ℝ)
    (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) (hB : ∀ v w, B v w=B w v)
    (hRem : (fun y : Space n => u (y,p.2)-u p-l (y-p.1)-
      (1/2 : ℝ)*B (y-p.1) (y-p.1))=o[𝓝 p.1](fun y => ‖y-p.1‖^2)) :
    V p=F (sym (fun i j : Yau.RIdx n => B (Yau.realVec i) (Yau.realVec j))) := by
  have hUpper (eta : ℝ) (heta : 0<eta) : V p≤F (autoPeanoHessianPerturbation B eta) := by
    have hh := auto_spatial_slice_sub hQ hF hu hV hTime hsol.1 hp
      ((autoPeanoSpatialPolynomial_smooth (u p) p.1 l B eta).contDiffAt.of_le (by simp))
      (auto_peano_spatial_upper_test hRem heta)
    rwa [autoPeanoSpatialPolynomial_hessian (u p) p.1 l B hB eta p] at hh
  have hLower (eta : ℝ) (heta : 0<eta) : F (autoPeanoHessianPerturbation B (-eta))≤V p := by
    have hh := auto_spatial_slice_super hQ hF hu hV hTime hsol.2 hp
      ((autoPeanoSpatialPolynomial_smooth (u p) p.1 l B (-eta)).contDiffAt.of_le (by simp))
      (auto_peano_spatial_lower_test hRem heta)
    rwa [autoPeanoSpatialPolynomial_hessian (u p) p.1 l B hB (-eta) p] at hh
  have hplus : Tendsto (fun eta : ℝ => autoPeanoHessianPerturbation B eta) (𝓝[>] (0 : ℝ))
      (𝓝 (sym (fun i j : Yau.RIdx n => B (Yau.realVec i) (Yau.realVec j)))) := by
    simpa only [autoPeanoHessianPerturbation_zero] using
      ((autoPeanoHessianPerturbation_continuous B).tendsto 0).mono_left nhdsWithin_le_nhds
  have hminus : Tendsto (fun eta : ℝ => autoPeanoHessianPerturbation B (-eta)) (𝓝[>] (0 : ℝ))
      (𝓝 (sym (fun i j : Yau.RIdx n => B (Yau.realVec i) (Yau.realVec j)))) := by
    simpa only [Function.comp_def,neg_zero,autoPeanoHessianPerturbation_zero] using
      (((autoPeanoHessianPerturbation_continuous B).comp continuous_neg).tendsto 0).mono_left
        nhdsWithin_le_nhds
  have hPositive : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), 0<eta := self_mem_nhdsWithin
  exact le_antisymm
    (le_of_tendsto_of_tendsto tendsto_const_nhds (hF.continuousAt.tendsto.comp hplus)
      (hPositive.mono hUpper))
    (le_of_tendsto_of_tendsto (hF.continuousAt.tendsto.comp hminus) tendsto_const_nhds
      (hPositive.mono hLower))

end Yau.LeafProofs.L05AutonomousAux
