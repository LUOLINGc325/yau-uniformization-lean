import Yau.Proofs.F01ScalarSymbolEllipticity
import Yau.Proofs.F01ClosedScalarHeat
import Yau.Proofs.F01LogDetRatioSmooth

/-! The same native logarithmic determinant ratio satisfies the original
real linear operator equation in every holomorphic chart, with its computed
source and the actual closed-face within-time derivative. -/
noncomputable section
open Set
open scoped ContDiff Manifold Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem linearOp_scalarSymbol_eq_complex_heat {H : Point n → Matrix (Fin n) (Fin n) ℂ}
    {u : Point n → ℝ} {Q : Set (Point n)} {p : Point n}
    (hu : ContDiffAt ℝ 2 (fun z => u (z, p.2)) p.1) :
    linearOp Q (fun q => scalarSymbol (H q)) (fun _ _ => 0) u p =
      timeD Q u p - traceWith (H p) (leviC (fun z => u (z, p.2)) p.1) := by
  rw [traceWith_levi_eq_scalarSymbol _ hu]
  simp only [linearOp, realHessianContraction, spatialDD, zero_mul, Finset.sum_const_zero, sub_zero]

theorem linearOp_scalarSymbol_holomorphic_chart
    (h : ℝ → HermitianField M) (F : ℝ → M.Carrier → ℝ) (I : Set ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {p : Point n} (hp : p ∈ e.source ×ˢ I) (hF : SmoothFn (F p.2)) :
    linearOp (e.source ×ˢ I) (fun q => scalarSymbol (pullbackMatrix (h q.2) e q.1))
      (fun _ _ => 0) (fun q => F q.2 (e q.1)) p = fieldHeatWithin h I F (e p.1) p.2 := by
  have hf : ContDiffAt ℝ 2 (inChart (e p.1) (F p.2)) (chartPt (e p.1) (e p.1)) :=
    ((hF (e p.1)).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) (e p.1)).mem_nhds
      (mem_extChartAt_target (e p.1)))).of_le (by simp)
  rw [linearOp_scalarSymbol_eq_complex_heat (backgroundChart_comp_contDiffAt e he (F p.2) hp.1 hf),
    traceWith_backgroundChart_eq_laplacian (h p.2) e he hei (F p.2) hp.1 hf]
  have hset : {s : ℝ | (p.1, s) ∈ e.source ×ˢ I} = I := by
    ext s
    exact and_iff_right hp.1
  simp only [timeD, fieldHeatWithin, hset]

theorem native_scalar_closed_linear_equation
    (g : HermitianField M) (hg : MetricSmooth g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {T : ℝ} (hT : 0 < T)
    (hh : MetricFamilySmooth h (Icc 0 T)) (hU : SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Icc 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
      (Real.log ((gMat (h s) x).det.re / (gMat g x).det.re)) (Icc 0 T) s)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {p : Point n} (hp : p ∈ e.source ×ˢ Icc 0 T) :
    linearOp (e.source ×ˢ Icc 0 T) (fun q => scalarSymbol (pullbackMatrix (h q.2) e q.1))
      (fun _ _ => 0) (fun q => flowLogDetRatio g h (e q.1) q.2) p =
      -traceWith (gMat (h p.2) (e p.1)) (ricci g (e p.1)) := by
  rw [linearOp_scalarSymbol_holomorphic_chart h (fun t x => flowLogDetRatio g h x t)
    (Icc 0 T) e he hei hp
    (smoothSpaceTime_slice (flowLogDetRatio_smoothSpaceTime g hg h hh) hp.2)]
  exact (closed_slab_logdet_evolution_and_heat g hg h U hT hh hU hpot hpde (e p.1) hp.2).2

end Yau.NodeProofs.F01Aux
