import Yau.Geometry.HolomorphicBundle

open scoped Manifold Topology
open Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

variable {n r : ℕ}

theorem wirt_eventually_congr {f g : ComplexVector n → ℂ} {z : ComplexVector n}
    (h : f =ᶠ[𝓝 z] g) (v : ComplexVector n) :
    (fun w => wirt f w v) =ᶠ[𝓝 z] (fun w => wirt g w v) := by
  have hd := h.fderiv (𝕜 := ℝ)
  filter_upwards [hd] with w hw
  simp only [wirt, hw]

theorem chernConnectionMatrix_eventually_congr
    {H H' : ComplexVector n → Matrix (Fin r) (Fin r) ℂ} {z : ComplexVector n}
    (h : H =ᶠ[𝓝 z] H') (i : Fin n) :
    (fun w => chernConnectionMatrix H w i) =ᶠ[𝓝 z]
      (fun w => chernConnectionMatrix H' w i) := by
  classical
  have hd (α β : Fin r) :
      (fun w => wirt (fun v => H v α β) w (stdVec i)) =ᶠ[𝓝 z]
        (fun w => wirt (fun v => H' v α β) w (stdVec i)) :=
    wirt_eventually_congr (h.mono fun w hw => congrFun (congrFun hw α) β) (stdVec i)
  have hall : ∀ᶠ w in 𝓝 z, ∀ α β : Fin r,
      wirt (fun v => H v α β) w (stdVec i) =
        wirt (fun v => H' v α β) w (stdVec i) :=
    Filter.eventually_all.mpr fun α => Filter.eventually_all.mpr fun β => hd α β
  filter_upwards [h, hall] with w hw hdw
  have hW : (Matrix.of fun α β => wirt (fun v => H v α β) w (stdVec i)) =
      Matrix.of (fun α β => wirt (fun v => H' v α β) w (stdVec i)) := by
    ext α β
    exact hdw α β
  simp only [chernConnectionMatrix, hw, hW]

/-- The computed Chern curvature depends only on the germ of its actual
metric matrix. No smoothness or invertibility certificate is assumed. -/
theorem curvatureMatrix_congr_germ
    {H H' : ComplexVector n → Matrix (Fin r) (Fin r) ℂ} {z : ComplexVector n}
    (h : H =ᶠ[𝓝 z] H') : curvatureMatrix H z = curvatureMatrix H' z := by
  have hz := h.eq_of_nhds
  funext i j
  have hc := chernConnectionMatrix_eventually_congr h i
  have hW : (Matrix.of fun α β => wirtBar
      (fun w => chernConnectionMatrix H w i α β) z (stdVec j)) =
      Matrix.of (fun α β => wirtBar
        (fun w => chernConnectionMatrix H' w i α β) z (stdVec j)) := by
    ext α β
    have he : (fun w => chernConnectionMatrix H w i α β) =ᶠ[𝓝 z]
        (fun w => chernConnectionMatrix H' w i α β) :=
      hc.mono fun w hw => congrFun (congrFun hw α) β
    simp only [Matrix.of_apply, wirtBar, he.fderiv_eq]
  simp only [curvatureMatrix, hz, hW]

end Yau.NodeProofs.P03Aux
