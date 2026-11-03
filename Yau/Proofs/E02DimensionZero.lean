import Yau.Proofs.E02Optimizer

open Set Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- The entire ORIGINAL ellipsoid comparison in dimension zero. A lower
 test of the actual locally constant zero optimizer value has a local
 maximum along the physical time line, so its actual derivative is zero. -/
theorem ellipsoidComparison_dimension_zero
    (X : KahlerManifold 0) (h : Flow X) (ρ : STF X)
    (hoc : OptimizerContacts X h ρ) : EllipsoidComparison X h := by
  intro T hT x z t hz ht φ _hφ hEq hTouch
  have hφ0 : φ (z,t) = 0 := hEq.trans (ellipsoidLogDet_dimension_zero X h ρ hoc hT x z t hz ht)
  have hMap : Continuous (fun s : ℝ => (z,s)) := continuous_const.prodMk continuous_id
  have hTime : ∀ᶠ s in 𝓝 t, φ (z,s) ≤ ellipsoidLogDet X h T x z s :=
    hMap.continuousAt.tendsto.eventually hTouch
  have hMax : IsLocalMax (fun s : ℝ => φ (z,s)) t := by
    change ∀ᶠ s in 𝓝 t, φ (z,s) ≤ φ (z,t)
    filter_upwards [hTime,isOpen_Ioo.mem_nhds ht] with s hs hsT
    have hs0 : φ (z,s) ≤ 0 := by
      simpa only [ellipsoidLogDet_dimension_zero X h ρ hoc hT x z s hz hsT] using hs
    rw [hφ0]
    exact hs0
  have hTrace : traceWith (hMat (h t) x z) (leviC (fun w => φ (w,t)) z) = 0 := by
    simp [traceWith,Matrix.trace]
  rw [hTrace,mul_zero,hMax.deriv_eq_zero]

end Yau.NodeProofs.E02Aux
