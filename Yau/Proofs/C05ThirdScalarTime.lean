import Yau.Proofs.C05ThirdScalarTimeDerivatives

/-! The actual third scalar time derivative, with the original physical clock. -/
noncomputable section
open scoped Manifold Topology ContDiff
namespace Yau.Proofs.C05ThirdScalarTimeAux
open Yau Blueprint Yau.Proofs.C05Aux Set Filter
variable {n : ℕ} {X : KahlerManifold n}

theorem scalar_third_hasDerivAt_polynomial (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => deriv (fun r => deriv (fun q => scalarCurvature (h q) x) r) s)
      (laplacian (h t) (fun y => deriv (fun s => deriv (fun q => scalarCurvature (h q) y) s) t) x +
        4 * ricciLeviPairing (h t) (fun y => deriv (fun s => scalarCurvature (h s) y) t) x +
        12 * ricciSquareLevi (h t) x + 3 * leviScalarSquare (h t) x + 6 * ricciQuartic (h t) x) t := by
  let u : STF X := fun y s => scalarCurvature (h s) y
  have hu := localizedFlow_scalar_smoothSpaceTime X o h U P ρ hf
  have htu := smoothSpaceTime_timeDeriv isOpen_Ioi hu
  have hl := laplacian_hasDerivAt o h U P ρ hf (timeDeriv u) htu x ht
  have hp := (ricciLeviPairing_hasDerivAt o h U P ρ hf x ht).const_mul 3
  have hc := (ricciCube_hasDerivAt o h U P ρ hf x ht).const_mul 2
  have he : (fun s => deriv (fun r => deriv (fun q => scalarCurvature (h q) x) r) s) =ᶠ[𝓝 t]
      (fun s => laplacian (h s) (fun y => deriv (fun q => scalarCurvature (h q) y) s) x +
        3 * ricciLeviPairing (h s) (scalarCurvature (h s)) x + 2 * ricciCube (h s) x) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (scalar_second_hasDerivAt o h U P ρ hf x hs).deriv
  have hd := ((hl.add hp).add hc).congr_of_eventuallyEq he
  convert hd using 1
  dsimp only [u, timeDeriv]
  ring

theorem scalar_third_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t) :
    let B := (gMat (h t) x)⁻¹ * ricci (h t) x
    let C := (gMat (h t) x)⁻¹ * levi (scalarCurvature (h t)) x
    HasDerivAt (fun s => deriv (fun r => deriv (fun q => scalarCurvature (h q) x) r) s)
      (laplacian (h t) (fun y => deriv (fun s => deriv (fun q => scalarCurvature (h q) y) s) t) x +
        4 * ricciLeviPairing (h t) (fun y => deriv (fun s => scalarCurvature (h s) y) t) x +
        12 * (B * B * C).trace.re + 3 * (C * C).trace.re + 6 * (B * B * B * B).trace.re) t := by
  exact scalar_third_hasDerivAt_polynomial o h U P ρ hf x ht

end Yau.Proofs.C05ThirdScalarTimeAux
