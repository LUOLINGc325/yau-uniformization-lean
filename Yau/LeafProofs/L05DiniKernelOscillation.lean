import Yau.LeafProofs.L05DiniKernelCausal
import Yau.LeafProofs.L05ChuOscillation

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

local instance l05DiniKernelOscillationDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelOscillationDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelOscillationHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05DiniKernelOscillationHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

theorem constant_causal_dini_oscillation (n : ℕ) (hn : 0 < n) (ell L : ℝ)
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Mat n) (T eta G F W : ℝ) (g w : Point n → ℝ),
      0 < T → T ≤ 1 → 0 < eta → eta < 1 → 0 ≤ G → 0 ≤ F → 0 ≤ W →
      Elliptic (cylinder Set.univ 0 T) (fun _ => A) ell L →
      HolderBound eta (cylinder Set.univ 0 T) g F →
      (∀ p ∈ cylinder Set.univ 0 T, |g p| ≤ G) → (∀ x : Space n, g (x,0)=0) →
      C2 (cylinder Set.univ 0 T) w → (∀ p ∈ cylinder Set.univ 0 T, |w p| ≤ W) →
      (∀ x : Space n, w (x,0)=0) →
      (∀ p ∈ Set.univ ×ˢ Set.Ioc (0:ℝ) T,
        linearOp (cylinder Set.univ 0 T) (fun _ => A) (fun _ _ => 0) w p=g p) →
      ∀ r ∈ Set.Ioc (0:ℝ) 1, chuOscillation (cylinder Set.univ 0 T) (spatialDD w) r ≤
        C*(diniTransform (chuOscillation (cylinder Set.univ 0 T) g) r+r*G) := by
  obtain ⟨C,hC,hKernel⟩ := constant_causal_dini_hessian n hn ell L hell hL
  refine ⟨C,hC,?_⟩
  intro A T eta G F W g w hT hT1 he he1 hG0 hF hW hEll hg hG hg0 hw hwB hw0 hPDE r hr
  have hBound (p : Point n) (hp : p ∈ cylinder Set.univ 0 T) : ‖g p‖ ≤ G := by
    simpa only [Real.norm_eq_abs] using hG p hp
  have hm := chuOscillation_measurable hG0 hBound
  have hmono : MonotoneOn (chuOscillation (cylinder Set.univ 0 T) g) (Set.Ioc (0:ℝ) 1) :=
    (chuOscillation_monotone hG0 hBound).monotoneOn _
  have hp := chuOscillation_powerBound he.le hg
  have hK := hKernel A T eta G F (2*F) W g w (chuOscillation (cylinder Set.univ 0 T) g)
    hT hT1 he he1 hG0 hF (by positivity) hW hEll hg hG hg0 hm hmono hp
    (fun r hr p hpm q hqm hpq => by
      simpa only [Real.norm_eq_abs] using chuOscillation_pair_le hG0 hBound hpm hqm hpq)
    hw hwB hw0 hPDE r hr
  apply chuOscillation_le (mul_nonneg hC.le (add_nonneg
    (diniTransform_nonneg_of_powerBound he he1 (by positivity) hm hmono hp hr)
    (mul_nonneg hr.1.le hG0)))
  exact hK

end Yau.LeafProofs.L05Aux
