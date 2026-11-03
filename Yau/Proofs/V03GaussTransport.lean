import Yau.Proofs.V03GaussCharts

/-! The local Gauss Levi densities agree under the actual induced cotangent
coordinate changes; the logarithmic determinant correction is pluriharmonic. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem secondFDeriv_add_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y + g y)) z v w =
      fderiv ℝ (fderiv ℝ f) z v w + fderiv ℝ (fderiv ℝ g) z v w := by
  have h := congrArg (fun A => A ![v, w]) (iteratedFDeriv_add_apply hf hg)
  simpa only [Pi.add_def, iteratedFDeriv_two_apply, add_apply, Pi.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem mixedWirt_real_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) (v : E) :
    (wirt (fun y => wirtBar (fun y' => ((f y' + g y' : ℝ) : ℂ)) y v) z v).re =
      (wirt (fun y => wirtBar (fun y' => (f y' : ℂ)) y v) z v).re +
      (wirt (fun y => wirtBar (fun y' => (g y' : ℂ)) y v) z v).re := by
  rw [mixedWirt_real_diagonal (hf.add hg), mixedWirt_real_diagonal hf,
    mixedWirt_real_diagonal hg]
  simp only [secondFDeriv_add_real hf hg]
  ring

variable {n q : ℕ} {M : ComplexManifold n}

theorem gaussPotential_levi_chart_change {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) (x x' : M.Carrier) {z : CotangentCoord n}
    (hz : z ∈ cotangentTarget x)
    (hz' : chartInv x z.1 ∈ (extChartAt (ComplexModel n) x').source)
    (v : CotangentCoord n) :
    (wirt (fun w => wirtBar (fun w' => (gaussPotential G x w' : ℂ)) w v) z v).re =
      (wirt (fun w => wirtBar (fun w' => (gaussPotential G x' w' : ℂ)) w
        (fderiv ℂ (fun w' => cotangentChart x' (cotangentChartInv x w')) z v))
        (cotangentChart x' (cotangentChartInv x z))
        (fderiv ℂ (fun w' => cotangentChart x' (cotangentChartInv x w')) z v)).re := by
  let T : CotangentCoord n → CotangentCoord n := fun w => cotangentChart x' (cotangentChartInv x w)
  have hT : ContDiffAt ℂ 2 T z :=
    (cotangentChartTransition_contDiffAt x x' hz hz').of_le (by simp)
  have htarget' : T z ∈ cotangentTarget x' := cotangentChart_mapsTo x' hz'
  have hP : ContDiffAt ℝ 2 (gaussPotential G x') (T z) :=
    (gaussPotential_contDiffAt hG x' htarget').of_le (by simp)
  have hcomp : ContDiffAt ℝ 2 (fun w => gaussPotential G x' (T w)) z :=
    hP.comp z (hT.restrict_scalars ℝ)
  have hdet := cotangentTransitionDet_contDiffAt x x' hz hz'
  have hne := cotangentTransitionDet_ne_zero x x' hz hz'
  have hlog : ContDiffAt ℝ 2
      (fun w => Real.log (Complex.normSq (cotangentTransitionDet x x' w))) z := by
    simp_rw [Complex.normSq_eq_norm_sq]
    exact ((hdet.restrict_scalars ℝ).norm_sq (𝕜 := ℂ)).log
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
  have heq : (fun w => (gaussPotential G x w : ℂ)) =ᶠ[𝓝 z]
      (fun w => ((gaussPotential G x' (T w) +
        Real.log (Complex.normSq (cotangentTransitionDet x x' w)) : ℝ) : ℂ)) := by
    filter_upwards [(isOpen_cotangentChartOverlap x x').mem_nhds ⟨hz, hz'⟩] with w hw
    exact congrArg Complex.ofReal (gaussPotential_chart_change hG x x' hw.1 hw.2)
  rw [mixedWirt_congr heq, mixedWirt_real_add hcomp hlog,
    mixedWirt_log_normSq_holomorphic_zero hdet hne, add_zero]
  exact mixedWirt_holomorphic_comp_re hT hP v

end Yau.Blueprint.V03Proof
