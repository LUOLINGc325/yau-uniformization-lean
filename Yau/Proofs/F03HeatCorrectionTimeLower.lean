import Yau.Proofs.F03HeatCorrectionEuler
import Yau.Proofs.F03RhoHeatMean

/-! The actual correction's ordinary time derivative has the lower bound required for the final weight. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem metricDefectHeatCorrection_time_lower_bound
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Ioc 0 T → ∀ L : ℝ,1 ≤ L →
      ∀ x,inducedDistance X.metric.form o x ≤ C₀*L →
      metricDefectHeatCorrection X h μ hμ O hO L x s/s-C*L ≤
        deriv (metricDefectHeatCorrection X h μ hμ O hO L x) s := by
  obtain ⟨C,hC,hMean⟩ := localizedFlow_rho_matching_heat_mean X o h U P ρ hf hT C₀ hC₀
  refine ⟨C,hC,fun μ hμ O hO s hs L hL x hx => ?_⟩
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let H := dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO
  have hEuler := metricDefectHeatCorrection_timeEuler_identity X o h U P ρ hf u hu μ hμ O hO hL0 x hs.1
  have hRho := hMean μ hμ O hO s ⟨hs.1.le,hs.2⟩ L hL x hx
  have hInt := dirichletMinimalKernel_potential_slab_integrable X o h U P ρ hf hT.le μ hμ O hO
    (sq_pos_of_pos hL0) x ⟨hs.1.le,hs.2⟩
  have hIntQ : Integrable (fun y => H (L^2) x y*(U y s-s*P y s)) μ := by
    apply (hInt.2.sub (hInt.1.const_mul s)).congr
    apply ae_of_all μ
    intro y
    change H (L^2) x y*U y s-s*(H (L^2) x y*P y s)=H (L^2) x y*(U y s-s*P y s)
    ring
  have hIntegral : (∫ y,H (L^2) x y*(U y s-s*P y s) ∂μ) ≤
      s*(∫ y,H (L^2) x y*ρ y s ∂μ) := by
    calc
      _ ≤ ∫ y,s*(H (L^2) x y*ρ y s) ∂μ := by
        apply integral_mono hIntQ (hRho.1.const_mul s)
        intro y
        convert mul_le_mul_of_nonneg_left
          (localizedFlow_potential_euler_bounds X o h U P ρ hf hs.1.le y).2
          (dirichletMinimalKernelCandidate_nonneg X.metric X.kahler_metric μ hμ O hO
            (sq_pos_of_pos hL0) x y) using 1 <;> ring
      _ = _ := integral_const_mul _ _
  have hEulerBound : metricDefectHeatCorrection X h μ hμ O hO L x s-
      s*deriv (metricDefectHeatCorrection X h μ hμ O hO L x) s ≤ s*(C*L) := by
    rw [hEuler]
    calc
      _ ≤ ∫ y,H (L^2) x y*(U y s-s*P y s) ∂μ :=
        sub_le_self _ (localizedFlow_potential_euler_bounds X o h U P ρ hf hs.1.le x).1
      _ ≤ s*(∫ y,H (L^2) x y*ρ y s ∂μ) := hIntegral
      _ ≤ _ := mul_le_mul_of_nonneg_left hRho.2 hs.1.le
  have hDiv : metricDefectHeatCorrection X h μ hμ O hO L x s/s ≤
      deriv (metricDefectHeatCorrection X h μ hμ O hO L x) s+C*L :=
    (div_le_iff₀ hs.1).mpr (by nlinarith)
  linarith

end Yau.Proofs.F03Aux
