import Yau.Proofs.F01RayleighDriftWithin
import Yau.Proofs.F01FamilyLogRayleigh
import Yau.Proofs.F01DiagonalHeat

/-! The actual drift inequality is written in the very same local
log-Rayleigh test and closed-time operator used at a maximum. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {N : ComplexManifold n}

def chartLogRayleigh (α : HermitianField N) (h : ℝ → HermitianField N)
    (e : OpenPartialHomeomorph (ComplexVector n) N.Carrier) (j : Fin n)
    (p : ComplexVector n × ℝ) : ℝ :=
  Real.log (matrixRayleigh (pullbackMatrix α e p.1) (pullbackMatrix (h p.2) e p.1) (Pi.single j 1))

variable (M : ComplexManifold n) (S : Opens M.Carrier) (hS : IsConnected (S : Set M.Carrier))

theorem normal_rayleigh_heat_bound_within
    (g : SmoothMetric M) (hcurv : NonnegBisectional g.form)
    (f u : (openConnectedManifold M S hS).Carrier → ℝ) (hf : SmoothFn f) (hu : SmoothFn u)
    (k : ℝ → HermitianField (openConnectedManifold M S hS)) (t : ℝ) (hk : MetricSmooth (k t))
    (hpot : ∀ x, gMat (k t) x = gMat (conformalField (openRestrictedField M S hS g.form) f) x -
      (t : ℂ) • ricci (conformalField (openRestrictedField M S hS g.form) f) x + levi u x)
    (e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs0 : (0 : ComplexVector n) ∈ e.source)
    (hvalue : pullbackMatrix (openRestrictedField M S hS g.form) e 0 = 1)
    (hjet : ∀ i j, fderiv ℝ (fun w =>
      pullbackMatrix (openRestrictedField M S hS g.form) e w i j) 0 = 0)
    (values : Fin n → ℝ)
    (hdiag : pullbackMatrix (k t) e 0 = Matrix.diagonal (fun i => (values i : ℂ)))
    (j : Fin n) (B G : ℝ) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hlarge : Real.exp (f (e 0)) ≤ (pullbackMatrix (k t) e 0 j j).re)
    (hgrad : gradNormSq (conformalField (openRestrictedField M S hS g.form) f) f (e 0) ≤ G)
    (hlo : (levi f (e 0) - ((-B : ℝ) : ℂ) •
      gMat (conformalField (openRestrictedField M S hS g.form) f) (e 0)).PosSemidef)
    (hhi : ((B : ℂ) • gMat (conformalField (openRestrictedField M S hS g.form) f) (e 0) -
      levi f (e 0)).PosSemidef)
    {I : Set ℝ} (hUnique : UniqueDiffWithinAt ℝ I t)
    (hevolution : HasDerivWithinAt (fun s => (pullbackMatrix (k s) e 0 j j).re)
      (leviC (fun w => Real.log (pullbackMatrix (k t) e w).det.re) 0 j j).re I t) :
    let α := conformalField (openRestrictedField M S hS g.form) f
    let U := chartLogRayleigh α k e j
    let τ := traceWith (pullbackMatrix (k t) e 0) (pullbackMatrix α e 0)
    diagonalHeatWithin values U I 0 t ≤ (3 * B + 3 * G) * τ +
      2 * (Real.exp (U (0, t)))⁻¹ * Real.sqrt (diagonalGradientNorm values (fun w => f (e w)) 0) *
        Real.sqrt (diagonalGradientNorm values (fun w => U (w, t)) 0) := by
  let g0 := openRestrictedField M S hS g.form
  let α := conformalField g0 f
  let U := chartLogRayleigh α k e j
  let q := (pullbackMatrix (k t) e 0 j j).re
  have hq : 0 < q := pullback_diagonal_pos (k t) e he hei hs0 j
  have htime := conformal_single_logRayleigh_time_eq g0 f k e hvalue j
  have htimeD : derivWithin (fun s => U (0, s)) I t =
      derivWithin (fun s => Real.log ((pullbackMatrix (k s) e 0 j j).re / Real.exp (f (e 0)))) I t :=
    congrArg (fun F : ℝ → ℝ => derivWithin F I t) htime
  have hratio : matrixRayleigh (pullbackMatrix α e 0) (pullbackMatrix (k t) e 0) (Pi.single j 1) =
      q / Real.exp (f (e 0)) := by
    rw [matrixRayleigh_single, conformalField_pullbackMatrix, hvalue]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Complex.ofReal_re]
    rfl
  have hexp : Real.exp (U (0, t)) = q / Real.exp (f (e 0)) := by
    change Real.exp (Real.log (matrixRayleigh _ _ _)) = _
    rw [hratio, Real.exp_log (div_pos hq (Real.exp_pos _))]
  have hinv : (Real.exp (U (0, t)))⁻¹ = Real.exp (f (e 0)) / q := by
    rw [hexp, inv_div]
  have hb := rayleigh_drift_bound_within M S hS g hcurv f u hf hu (k t) hk t hpot
    e he hei hs0 hvalue hjet values hdiag j B G hB hG hlarge hgrad hlo hhi
    (fun s => (pullbackMatrix (k s) e 0 j j).re) rfl hUnique hevolution
  rw [← htimeD, hdiag] at hb
  change diagonalHeatWithin values U I 0 t ≤
    (3 * B + 3 * G) * traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (pullbackMatrix α e 0) +
    2 * (Real.exp (f (e 0)) / (Matrix.diagonal (fun i => (values i : ℂ)) j j).re) *
      Real.sqrt (diagonalGradientNorm values (fun w => U (w, t)) 0) *
      Real.sqrt (diagonalGradientNorm values (fun w => f (e w)) 0) at hb
  have hqdiag : q = (Matrix.diagonal (fun i => (values i : ℂ)) j j).re :=
    congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => (A j j).re) hdiag
  have htrace : traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (pullbackMatrix α e 0) =
      traceWith (pullbackMatrix (k t) e 0) (pullbackMatrix α e 0) := by rw [← hdiag]
  rw [← hqdiag, htrace] at hb
  dsimp only
  change diagonalHeatWithin values U I 0 t ≤ _
  rw [hinv]
  calc
    _ ≤ (3 * B + 3 * G) * traceWith (pullbackMatrix (k t) e 0) (pullbackMatrix α e 0) +
        2 * (Real.exp (f (e 0)) / q) *
          Real.sqrt (diagonalGradientNorm values (fun w => U (w, t)) 0) *
          Real.sqrt (diagonalGradientNorm values (fun w => f (e w)) 0) := hb
    _ = _ := by ring

end Yau.NodeProofs.F01Aux
