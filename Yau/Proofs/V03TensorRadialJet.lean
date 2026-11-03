import Yau.Proofs.V03ComplexWithinRealImag
import Yau.Proofs.V03CotangentCoefficientRegularity
import Yau.Proofs.V03HolomorphicRadialDerivative

/-! Each actual tensor coefficient's radial derivative is given by its
genuine intrinsic scalar differentials paired with the actual angular immersion derivative. -/

open scoped Manifold Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem tensor_coefficient_radial_jet {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    {B : CotangentPoint M → Matrix (Fin q) (Fin q) ℂ}
    (hB : ∀ x a b, ContDiffOn ℝ ∞ (fun z => B (cotangentChartInv x z) a b) (cotangentTarget x))
    (a b : Fin q) (θ : ℝ) :
    fderivWithin ℝ (fun ζ => B (f ζ) a b) (Metric.closedBall (0 : ℂ) 1) (circlePoint θ) (circlePoint θ) =
      ((2 * (ambientScalarCovector G (fun y => (B y a b).re) (f (circlePoint θ)) ⬝ᵥ
        (fun c => -Complex.I * holomorphicAngularTrace (fun ζ => G (f ζ) c) θ)).re : ℝ) : ℂ) +
      Complex.I * ((2 * (ambientScalarCovector G (fun y => (B y a b).im) (f (circlePoint θ)) ⬝ᵥ
        (fun c => -Complex.I * holomorphicAngularTrace (fun ζ => G (f ζ) c) θ)).re : ℝ) : ℂ) := by
  have hp := circlePoint_mem_closedBall θ
  have hc := cotangentHolomorphicOn_coefficient_contDiffOn (b := fun y => B y a b)
    (cotangentDisc_holomorphicOn hf)
    (fun x => hB x a b)
  have hopen : IsOpen (cotangentTarget (f (circlePoint θ)).1) :=
    (isOpen_extChartAt_target (I := ComplexModel n) (f (circlePoint θ)).1).prod isOpen_univ
  have ht := cotangentChart_mapsTo (f (circlePoint θ)).1 (mem_extChartAt_source _)
  have hRe : DifferentiableAt ℝ
      (fun z => (B (cotangentChartInv (f (circlePoint θ)).1 z) a b).re)
      (cotangentChart (f (circlePoint θ)).1 (f (circlePoint θ))) :=
    ((Complex.reCLM.contDiff.comp_contDiffOn (hB (f (circlePoint θ)).1 a b)).contDiffAt
      (hopen.mem_nhds ht)).differentiableAt (by simp)
  have hIm : DifferentiableAt ℝ
      (fun z => (B (cotangentChartInv (f (circlePoint θ)).1 z) a b).im)
      (cotangentChart (f (circlePoint θ)).1 (f (circlePoint θ))) :=
    ((Complex.imCLM.contDiff.comp_contDiffOn (hB (f (circlePoint θ)).1 a b)).contDiffAt
      (hopen.mem_nhds ht)).differentiableAt (by simp)
  have h0 := cotangentDisc_scalar_radial_ambient (b := fun y => (B y a b).re) hG hf θ hRe
  have h1 := cotangentDisc_scalar_radial_ambient (b := fun y => (B y a b).im) hG hf θ hIm
  rw [fderivWithin_complex_eq_re_im (uniqueDiffOn_real_closedDisc _ hp)
    ((hc.differentiableOn (by simp)) _ hp), h0, h1]

end Yau.Blueprint.V03Proof
