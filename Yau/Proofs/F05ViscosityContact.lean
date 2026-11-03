import Yau.Proofs.F05SpatialConstants
import Yau.Proofs.F05Scalar
import Yau.Proofs.F05CompactContact
import Yau.Proofs.F05Penalty

/-! The local viscosity comparison at an actual smooth upper contact. -/

noncomputable section

open scoped ContDiff

namespace Yau.Proofs.F05Aux

theorem weighted_upper_contact {n : ℕ} {M : ComplexManifold n}
    (u v : M.Carrier → ℝ → ℝ) (C S ε : ℝ) (p : M.Carrier × ℝ)
    (hmax : IsLocalMax (fun z : M.Carrier × ℝ =>
      (Real.exp (C * z.2))⁻¹ * (v z.1 z.2 - u z.1 z.2) - ε / (S - z.2)) p) :
    let m := (Real.exp (C * p.2))⁻¹ * (v p.1 p.2 - u p.1 p.2) - ε / (S - p.2)
    TouchesAbove (fun y s => u y s + comparisonPenalty C S ε m s) v p.1 p.2 := by
  have h := weighted_max_touches u v (fun t => (Real.exp (C * t))⁻¹)
    (fun t => ε / (S - t)) p (fun t => inv_pos.mpr (Real.exp_pos _)) hmax
  simpa only [TouchesAbove, comparisonPenalty, div_inv_eq_mul, mul_comm,
    Prod.mk.eta] using h

theorem viscosity_contact_slope_bound {n : ℕ} {M : ComplexManifold n}
    (h : ℝ → HermitianField M) (T : ℝ) (u v : M.Carrier → ℝ → ℝ)
    (hv : NonlinearViscositySub h T v) (x : M.Carrier) (t : ℝ)
    (ht : 0 < t) (htT : t < T) (a : ℝ → ℝ)
    (hsmooth : SmoothNear (fun y s => u y s + a s) x t)
    (htouch : TouchesAbove (fun y s => u y s + a s) v x t)
    (hu : timeDeriv u x t = scalarNonlinearRHS (scalarCurvature (h t) x)
      (laplacian (h t) (fun y => u y t) x) (u x t))
    (hu0 : 0 ≤ u x t) (huv : u x t ≤ v x t) (A : ℝ)
    (hA : |scalarCurvature (h t) x - laplacian (h t) (fun y => u y t) x| ≤ A) :
    timeDeriv (fun y s => u y s + a s) x t - timeDeriv u x t ≤
      A * (v x t - u x t) := by
  have htest := hv x t ht htT _ hsmooth htouch
  rw [laplacian_add_const] at htest
  have hvalue := scalarNonlinearRHS_sub_le (scalarCurvature (h t) x)
    (laplacian (h t) (fun y => u y t) x) A hu0 huv hA
  change timeDeriv _ x t ≤ scalarNonlinearRHS _ _ _ at htest
  rw [hu]
  linarith

theorem no_strict_viscosity_contact {n : ℕ} {M : ComplexManifold n}
    (h : ℝ → HermitianField M) (T : ℝ) (u v : M.Carrier → ℝ → ℝ)
    (hv : NonlinearViscositySub h T v) (x : M.Carrier) (t : ℝ)
    (ht : 0 < t) (htT : t < T) (a : ℝ → ℝ)
    (hsmooth : SmoothNear (fun y s => u y s + a s) x t)
    (htouch : TouchesAbove (fun y s => u y s + a s) v x t)
    (hu : timeDeriv u x t = scalarNonlinearRHS (scalarCurvature (h t) x)
      (laplacian (h t) (fun y => u y t) x) (u x t))
    (hu0 : 0 ≤ u x t) (huv : u x t < v x t) (A C : ℝ) (hAC : A < C)
    (hA : |scalarCurvature (h t) x - laplacian (h t) (fun y => u y t) x| ≤ A)
    (hslope : C * (v x t - u x t) ≤
      timeDeriv (fun y s => u y s + a s) x t - timeDeriv u x t) : False := by
  have hbound := viscosity_contact_slope_bound h T u v hv x t ht htT a hsmooth htouch
    hu hu0 huv.le A hA
  have hstrict := mul_lt_mul_of_pos_right hAC (sub_pos.mpr huv)
  linarith

/-- At a nonnegative penalized maximum the explicit smooth test contradicts
the original nonlinear viscosity inequality. -/
theorem no_nonnegative_penalized_max {n : ℕ} {M : ComplexManifold n}
    (h : ℝ → HermitianField M) (T : ℝ) (u v : M.Carrier → ℝ → ℝ)
    (hv : NonlinearViscositySub h T v) (x : M.Carrier) (t C S ε : ℝ)
    (ht : 0 < t) (htT : t < T) (htS : t < S) (hε : 0 < ε)
    (hmax : IsLocalMax (fun z : M.Carrier × ℝ =>
      (Real.exp (C * z.2))⁻¹ * (v z.1 z.2 - u z.1 z.2) - ε / (S - z.2)) (x,t))
    (hm : 0 ≤ (Real.exp (C * t))⁻¹ * (v x t - u x t) - ε / (S - t))
    (husmooth : SmoothNear u x t) (hudiff : DifferentiableAt ℝ (u x) t)
    (hu : timeDeriv u x t = scalarNonlinearRHS (scalarCurvature (h t) x)
      (laplacian (h t) (fun y => u y t) x) (u x t))
    (hu0 : 0 ≤ u x t) (A : ℝ) (hAC : A < C)
    (hA : |scalarCurvature (h t) x - laplacian (h t) (fun y => u y t) x| ≤ A) :
    False := by
  let m := (Real.exp (C * t))⁻¹ * (v x t - u x t) - ε / (S - t)
  have htouch : TouchesAbove (fun y s => u y s + comparisonPenalty C S ε m s) v x t :=
    weighted_upper_contact u v C S ε (x,t) hmax
  have hpen := comparisonPenalty_pos C S ε m t hε hm htS
  have huv : u x t < v x t := by linarith [htouch.1]
  have hsmooth : SmoothNear (fun y s => u y s + comparisonPenalty C S ε m s) x t := by
    exact husmooth.add ((comparisonPenalty_contDiffAt C S ε m t htS.ne).comp
      (chartPt x x,t) contDiffAt_snd)
  apply no_strict_viscosity_contact h T u v hv x t ht htT
    (comparisonPenalty C S ε m) hsmooth htouch hu hu0 huv A C hAC hA
  have hderiv := (hudiff.hasDerivAt.add
    (comparisonPenalty_hasDerivAt C S ε m t htS.ne)).deriv
  change deriv (fun s => u x s + comparisonPenalty C S ε m s) t = _ at hderiv
  change C * (v x t - u x t) ≤ deriv (fun s => u x s + comparisonPenalty C S ε m s) t - deriv (u x) t
  have hgap : v x t - u x t = comparisonPenalty C S ε m t := by linarith [htouch.1]
  rw [hgap, hderiv]
  have hterm : 0 ≤ Real.exp (C * t) * ε / (S - t)^2 := by positivity
  linarith

end Yau.Proofs.F05Aux
