import Yau.Proofs.C05RicciSquareTimeEvolution
import Yau.Proofs.C05LeviLinearity
import Yau.Proofs.C05ScalarHarnack

/-! The exact scalar Harnack evolution, proved for the original flow and its
original physical clock. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux Set Filter
variable {n : ℕ} {X : KahlerManifold n}

def scalarHarnackHeatOp (h : Flow X) (x : Pt X) (t : ℝ) : ℝ :=
  deriv (fun s => scalarHarnackSum h x s) t -
    laplacian (h t) (fun y => scalarHarnackSum h y t) x

theorem scalar_second_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => deriv (fun r => scalarCurvature (h r) x) s)
      (laplacian (h t) (fun y => deriv (fun s => scalarCurvature (h s) y) t) x +
        3 * ricciLeviPairing (h t) (scalarCurvature (h t)) x + 2 * ricciCube (h t) x) t := by
  let u : STF X := fun y s => scalarCurvature (h s) y
  have hu : SmoothSpaceTime u (Ioi 0) := localizedFlow_scalar_smoothSpaceTime X o h U P ρ hf
  have hl := laplacian_hasDerivAt o h U P ρ hf u hu x ht
  have hr := ricciNormSq_hasDerivAt o h U P ρ hf x ht
  have he : (fun s => deriv (fun r => scalarCurvature (h r) x) s) =ᶠ[𝓝 t]
      (fun s => laplacian (h s) (scalarCurvature (h s)) x + ricciNormSq (h s) x) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact scalar_time_evolution o h U P ρ hf x hs
  have hd := (hl.add hr).congr_of_eventuallyEq he
  convert hd using 1
  dsimp only [u, timeDeriv]
  ring

theorem scalarHarnack_heat_evolution (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t) :
    scalarHarnackHeatOp h x t =
      3 * ricciLeviPairing (h t) (scalarCurvature (h t)) x + 2 * ricciCube (h t) x +
        t⁻¹ * ricciNormSq (h t) x - (t⁻¹) ^ 2 * scalarCurvature (h t) x := by
  let u : STF X := fun y s => scalarCurvature (h s) y
  have hu : SmoothSpaceTime u (Ioi 0) := localizedFlow_scalar_smoothSpaceTime X o h U P ρ hf
  have htu : SmoothSpaceTime (timeDeriv u) (Ioi 0) := smoothSpaceTime_timeDeriv isOpen_Ioi hu
  have hsu : SmoothFn (fun y => u y t) := spaceSlice_smoothFn hu ht
  have hstu : SmoothFn (fun y => timeDeriv u y t) := spaceSlice_smoothFn htu ht
  have hsmul : SmoothFn (fun y => t⁻¹ * u y t) := by
    intro y
    exact contDiffOn_const.mul (hsu y)
  have hlap : laplacian (h t) (fun y => scalarHarnackSum h y t) x =
      laplacian (h t) (fun y => timeDeriv u y t) x +
        t⁻¹ * laplacian (h t) (fun y => u y t) x := by
    rw [show (fun y => scalarHarnackSum h y t) =
      (fun y => timeDeriv u y t + t⁻¹ * u y t) by rfl,
      laplacian_add (h t) _ _ hstu hsmul, laplacian_const_mul (h t) _ hsu t⁻¹]
  have hfD := (scalar_contDiffAt X o h U P ρ hf x ht).differentiableAt (by simp)
  have hs := (scalar_second_hasDerivAt o h U P ρ hf x ht).add
    ((hasDerivAt_inv ht.ne').mul hfD.hasDerivAt)
  change HasDerivAt (fun s => scalarHarnackSum h x s) _ t at hs
  unfold scalarHarnackHeatOp
  rw [hs.deriv, hlap, scalar_time_evolution o h U P ρ hf x ht]
  change (laplacian (h t) (fun y => timeDeriv u y t) x +
      3 * ricciLeviPairing (h t) (scalarCurvature (h t)) x + 2 * ricciCube (h t) x +
        (-(t ^ 2)⁻¹ * scalarCurvature (h t) x + t⁻¹ *
          (laplacian (h t) (scalarCurvature (h t)) x + ricciNormSq (h t) x))) -
      (laplacian (h t) (fun y => timeDeriv u y t) x +
        t⁻¹ * laplacian (h t) (scalarCurvature (h t)) x) = _
  field_simp [ht.ne']
  ring

end Yau.Proofs.C05Aux
