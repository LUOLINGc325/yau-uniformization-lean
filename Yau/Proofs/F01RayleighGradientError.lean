import Yau.Proofs.F01WeightedGradientError
import Yau.Proofs.F01FlowNegativeSquare
import Yau.Proofs.F01RayleighLogJet

/-! The actual negative matrix square cancels the diagonal logarithmic
gradient, leaving only the controlled conformal error and the Rayleigh gradient. -/
noncomputable section
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem flow_negative_square_gradient_error (g k : HermitianField M)
    (hg : MetricSmooth g) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (t : ℝ)
    (hpot : ∀ x, gMat k x = gMat (conformalField g f) x -
      (t : ℂ) • ricci (conformalField g f) x + levi u x)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs0 : (0 : ComplexVector n) ∈ e.source) (hvalue : pullbackMatrix g e 0 = 1)
    (hjet : ∀ i j, fderiv ℝ (fun w => pullbackMatrix g e w i j) 0 = 0)
    (values : Fin n → ℝ)
    (hdiag : pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ))) (a : Fin n)
    (hlarge : Real.exp (f (e 0)) ≤ (pullbackMatrix k e 0 a a).re) :
    let q := (pullbackMatrix k e 0 a a).re
    let η := fun i => wirt (fun w => (f (e w) : ℂ)) 0 (stdVec i)
    let ξ := fun i => wirt (fun w => (Real.log (matrixRayleigh
      (pullbackMatrix (conformalField g f) e w) (pullbackMatrix k e w)
        (Pi.single a 1)) : ℂ)) 0 (stdVec i)
    dualNormMat (pullbackMatrix k e 0) (WithLp.toLp 2 (fun i =>
      wirt (fun w => (Real.log (pullbackMatrix k e w a a).re : ℂ)) 0 (stdVec i))) -
        q⁻¹ * ∑ i, ∑ j, (values i)⁻¹ * (values j)⁻¹ *
          Complex.normSq (wirt (fun w => pullbackMatrix k e w j i) 0 (stdVec a)) ≤
      2 * (Real.exp (f (e 0)) / q) *
          Real.sqrt (dualNormMat (pullbackMatrix k e 0) (WithLp.toLp 2 ξ)) *
          Real.sqrt (dualNormMat (pullbackMatrix k e 0) (WithLp.toLp 2 η)) +
        2 * dualNormMat (pullbackMatrix k e 0) (WithLp.toLp 2 η) := by
  dsimp only
  let q := (pullbackMatrix k e 0 a a).re
  let η : Fin n → ℂ := fun i => wirt (fun w => (f (e w) : ℂ)) 0 (stdVec i)
  let ξ : Fin n → ℂ := fun i => wirt (fun w => (Real.log (matrixRayleigh
    (pullbackMatrix (conformalField g f) e w) (pullbackMatrix k e w)
      (Pi.single a 1)) : ℂ)) 0 (stdVec i)
  let β : Fin n → ℂ := fun i =>
    wirt (fun w => (Real.log (pullbackMatrix k e w a a).re : ℂ)) 0 (stdVec i)
  let s := Real.exp (f (e 0)) / q
  have hv (i : Fin n) : 0 < values i := by
    have hh := pullback_diagonal_pos k e he hei hs0 i
    simpa only [hdiag, Matrix.diagonal_apply_eq, Complex.ofReal_re] using hh
  have hq : 0 < q := pullback_diagonal_pos k e he hei hs0 a
  have hs : 0 ≤ s := (div_pos (Real.exp_pos _) hq).le
  have hs1 : s ≤ 1 := (div_le_one hq).mpr hlarge
  have hsum : (fun i => ξ i + η i) = β := by
    funext i
    have hh := conformal_rayleigh_log_wirt g k hg hk f hf e he hei hs0 hjet a (stdVec i)
    change ξ i = β i - η i at hh
    rw [hh]
    ring
  have hnorm (ν : Fin n → ℂ) :
      weightedCovectorSquare (fun i => (values i)⁻¹) ν =
        dualNormMat (pullbackMatrix k e 0) (WithLp.toLp 2 ν) := by
    rw [hdiag, dualNormMat_real_diagonal values (fun i => (hv i).ne')]
    rfl
  have herror := weighted_gradient_correction_le (fun i => (values i)⁻¹)
    (fun i => inv_nonneg.mpr (hv i).le) a ξ η s hs hs1
  have hcomponent (i : Fin n) : ξ i + η i = β i := congrFun hsum i
  simp only [hcomponent] at herror
  simp only [hnorm] at herror
  have hnegative := flow_negative_square_controls_corrected_gradient g k hg hk f hf u hu t
    hpot e he hei hs0 hvalue hjet values hdiag a
  dsimp only at hnegative
  have hcast : (s : ℂ) = (Real.exp (f (e 0)) : ℂ) / (q : ℂ) := by
    dsimp only [s]
    push_cast
    rfl
  rw [hcast] at herror
  change dualNormMat (pullbackMatrix k e 0) (WithLp.toLp 2 β) - _ ≤ _
  have hstep := sub_le_sub_left hnegative (dualNormMat (pullbackMatrix k e 0) (WithLp.toLp 2 β))
  exact hstep.trans herror

end Yau.NodeProofs.F01Aux
