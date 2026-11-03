import Yau.Proofs.F01FlowSecondExchange
import Yau.Proofs.F01ConformalSecondTraceError
import Yau.Proofs.F01NormalConformalBudgets
import Yau.Proofs.F01DiagonalGradientTrace
import Yau.Proofs.F01LogLaplacianDiagonal
import Yau.Proofs.F01MetricEntryLog

/-! The actual flow's second-derivative exchange has the controlled
conformal trace error, with the intrinsic budgets selected before the point. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem conformal_flow_second_trace_bound (g : SmoothMetric M)
    (f u : (openConnectedManifold M S hS).Carrier → ℝ) (hf : SmoothFn f) (hu : SmoothFn u)
    (k : HermitianField (openConnectedManifold M S hS)) (hk : MetricSmooth k) (t : ℝ)
    (hpot : ∀ x, gMat k x = gMat (conformalField (openRestrictedField M S hS g.form) f) x -
      (t : ℂ) • ricci (conformalField (openRestrictedField M S hS g.form) f) x + levi u x)
    (e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs0 : (0 : ComplexVector n) ∈ e.source)
    (hvalue : pullbackMatrix (openRestrictedField M S hS g.form) e 0 = 1)
    (hjet : ∀ i j, fderiv ℝ (fun w =>
      pullbackMatrix (openRestrictedField M S hS g.form) e w i j) 0 = 0)
    (values : Fin n → ℝ)
    (hdiag : pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ)))
    (a : Fin n) (B G : ℝ) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hlarge : Real.exp (f (e 0)) ≤ (pullbackMatrix k e 0 a a).re)
    (hgrad : gradNormSq (conformalField (openRestrictedField M S hS g.form) f) f (e 0) ≤ G)
    (hlo : (levi f (e 0) - ((-B : ℝ) : ℂ) •
      gMat (conformalField (openRestrictedField M S hS g.form) f) (e 0)).PosSemidef)
    (hhi : ((B : ℂ) • gMat (conformalField (openRestrictedField M S hS g.form) f) (e 0) -
      levi f (e 0)).PosSemidef) :
    (pullbackMatrix k e 0 a a).re⁻¹ * (∑ i, (values i)⁻¹ *
      ((wirt (fun w => wirtBar (fun y => pullbackMatrix k e y i i) w (stdVec a)) 0 (stdVec a)).re -
        (wirt (fun w => wirtBar (fun y => pullbackMatrix k e y a a) w (stdVec i)) 0 (stdVec i)).re)) +
      traceWith (pullbackMatrix k e 0) (leviC (fun w => f (e w)) 0) ≤
      (3 * B + G) * traceWith (pullbackMatrix k e 0)
        (pullbackMatrix (conformalField (openRestrictedField M S hS g.form) f) e 0) := by
  let g0 := openRestrictedField M S hS g.form
  have hv (i : Fin n) : 0 < values i := by
    have hh := pullback_diagonal_pos k e he hei hs0 i
    simpa only [hdiag, Matrix.diagonal_apply_eq, Complex.ofReal_re] using hh
  have hff : ContDiffAt ℝ 2 (fun w => f (e w)) 0 :=
    ((smoothFn_comp_holomorphic_chart f hf e he).contDiffAt
      (e.open_source.mem_nhds hs0)).of_le (by simp)
  have hF (i : Fin n) : |(leviC (fun w => f (e w)) 0 i i).re| ≤ B * Real.exp (f (e 0)) :=
    conformal_normal_coordinate_levi_bound g0 f hf e he hs0 hvalue B hlo hhi i
  have hD (i : Fin n) :
      Complex.normSq (wirt (fun w => (f (e w) : ℂ)) 0 (stdVec i)) ≤ G * Real.exp (f (e 0)) :=
    conformal_normal_coordinate_gradient_bound g0 f hf e he hei hs0 hvalue hgrad i
  have hh := conformal_second_exchange_trace_bound (fun i => (values i)⁻¹)
    (fun i => (leviC (fun w => f (e w)) 0 i i).re)
    (fun i => Complex.normSq (wirt (fun w => (f (e w) : ℂ)) 0 (stdVec i)))
    (fun i => inv_nonneg.mpr (hv i).le) (Real.exp_pos (f (e 0))) hlarge hB hG hF
    (fun i => Complex.normSq_nonneg _) hD a
  have hEx (i : Fin n) :
      (wirt (fun w => wirtBar (fun y => pullbackMatrix k e y i i) w (stdVec a)) 0 (stdVec a)).re -
        (wirt (fun w => wirtBar (fun y => pullbackMatrix k e y a a) w (stdVec i)) 0 (stdVec i)).re =
      Real.exp (f (e 0)) * ((leviC (fun w => f (e w)) 0 a a).re +
        Complex.normSq (wirt (fun w => (f (e w) : ℂ)) 0 (stdVec a))) -
      Real.exp (f (e 0)) * ((leviC (fun w => f (e w)) 0 i i).re +
        Complex.normSq (wirt (fun w => (f (e w) : ℂ)) 0 (stdVec i))) := by
    have hx := congrArg Complex.re (conformal_flow_diagonal_second_exchange M S hS g f u hf hu
      k hk t hpot e he hei hs0 hvalue hjet i a)
    rw [Complex.sub_re, Complex.sub_re, leviC_exp_diagonal hff a, leviC_exp_diagonal hff i] at hx
    exact hx
  simp only [hEx]
  rw [hdiag, traceWith_real_diagonal values (fun i => (hv i).ne'),
    conformalField_pullbackMatrix, hvalue,
    traceWith_real_diagonal_smul_one values (fun i => (hv i).ne')]
  rw [hdiag] at hh
  simpa only [mul_assoc] using hh

end Yau.NodeProofs.F01Aux
