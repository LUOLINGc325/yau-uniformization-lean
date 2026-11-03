import Yau.Proofs.C05ActualInverseEnergyLaplacian
import Yau.Proofs.C05ActualInverseEnergyTime
import Yau.Proofs.C05ScalarHarnackEvolution

/-! The heat operator of the actual minimized Harnack quantity.
Its only leading positive term is the same covariant Hessian square. -/

noncomputable section
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05Aux
open Yau Blueprint Set Yau.LeafProofs C04Aux
variable {n : ℕ} {M : ComplexManifold n} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem laplacian_sub (k : HermitianField M) (f g : M.Carrier → ℝ)
    (hf : SmoothFn f) (hg : SmoothFn g) (x : M.Carrier) :
    laplacian k (fun y => f y - g y) x = laplacian k f x - laplacian k g x := by
  have hn : SmoothFn (fun y => (-1 : ℝ) * g y) := fun c => contDiffOn_const.mul (hg c)
  have he : (fun y => f y - g y) = (fun y => f y + (-1 : ℝ) * g y) := by funext y; ring
  rw [he,laplacian_add k f _ hf hn,laplacian_const_mul k g hg]
  ring

theorem scalarHarnackSum_smoothFn (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {t : ℝ} (ht : 0 < t) :
    SmoothFn (fun y => scalarHarnackSum h y t) := by
  have hu := localizedFlow_scalar_smoothSpaceTime X o h U P ρ hf
  have htu := smoothSpaceTime_timeDeriv isOpen_Ioi hu
  have hs := spaceSlice_smoothFn hu ht
  have hts := spaceSlice_smoothFn htu ht
  intro c
  exact (hts c).add (contDiffOn_const.mul (hs c))

def minimizedScalarHarnackHeatOp (h : Flow X) (x : Pt X) (t : ℝ) : ℝ :=
  deriv (fun s => minimizedScalarHarnack h x s) t -
    laplacian (h t) (fun y => minimizedScalarHarnack h y t) x

def inverseEnergyHeatRemainder (h : Flow X) (x : Pt X) (t : ℝ) : ℝ :=
  ricciDifferentialEnergyTime h x t - (1 / 4 : ℝ) *
    inverseEnergySpatialRemainder (h t) x (ricciInverseTensor (h t) x)
      (scalarJet (h t) (scalarCurvature (h t)) x 1) (chartPt x x)

theorem minimizedScalarHarnack_heat_decomposition (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (x : Pt X) {t : ℝ} (ht : 0 < t) :
    minimizedScalarHarnackHeatOp h x t = scalarHarnackHeatOp h x t +
      (1 / 2 : ℝ) * inverseEnergyHessianSquare (h t) (scalarCurvature (h t)) x (chartPt x x) -
      inverseEnergyHeatRemainder h x t := by
  have ht0 : t ∈ Ici (0 : ℝ) := ht.le
  have hk := L23Aux.metricFamilySmooth_slice h hf.1.2.1 ht0
  have hK := hf.1.2.2.1 t ht.le
  have hA := hH.2.2.1 t ht.le
  have hu := localizedFlow_scalar_smoothSpaceTime X o h U P ρ hf
  have hs := spaceSlice_smoothFn hu ht
  have hqfun : (fun y => dualNormMat (ricci (h t) y) (scalarCovector (h t) y)) =
      realRicciDifferentialEnergy (h t) (scalarCurvature (h t)) := by
    funext y
    exact scalar_differential_ricci_dual_eq (h t) hk hK (scalarCurvature (h t)) hs y (hA y)
  have hqSmooth : SmoothFn (fun y => dualNormMat (ricci (h t) y) (scalarCovector (h t) y)) := by
    rw [hqfun]
    exact realRicciDifferentialEnergy_smoothFn (h t) hk hK hA (scalarCurvature (h t)) hs
  have hsum := scalarHarnackSum_smoothFn o h U P ρ hf ht
  have hlap := laplacian_sub (h t) (fun y => scalarHarnackSum h y t)
    (fun y => dualNormMat (ricci (h t) y) (scalarCovector (h t) y)) hsum hqSmooth x
  rw [hqfun,realRicciDifferentialEnergy_laplacian (h t) hk hK hA _ hs] at hlap
  have hsd := (scalar_second_hasDerivAt o h U P ρ hf x ht).add
    ((hasDerivAt_inv ht.ne').mul
      ((C04Aux.scalar_contDiffAt X o h U P ρ hf x ht).differentiableAt (by simp)).hasDerivAt)
  change HasDerivAt (fun s => scalarHarnackSum h x s) _ t at hsd
  have hqd := scalarHarnackQuadratic_hasDerivAt o h U P ρ hf hH x ht
  have hzd := (hsd.differentiableAt.hasDerivAt.sub hqd).deriv
  change deriv (fun s => minimizedScalarHarnack h x s) t =
    deriv (fun s => scalarHarnackSum h x s) t - ricciDifferentialEnergyTime h x t at hzd
  unfold minimizedScalarHarnackHeatOp scalarHarnackHeatOp inverseEnergyHeatRemainder
  rw [hzd]
  change _ - laplacian (h t) (fun y => scalarHarnackSum h y t -
    dualNormMat (ricci (h t) y) (scalarCovector (h t) y)) x = _
  rw [hlap]
  ring

theorem minimizedScalarHarnack_heat_evolution (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (x : Pt X) {t : ℝ} (ht : 0 < t) :
    minimizedScalarHarnackHeatOp h x t =
      3 * ricciLeviPairing (h t) (scalarCurvature (h t)) x + 2 * ricciCube (h t) x +
        t⁻¹ * ricciNormSq (h t) x - (t⁻¹) ^ 2 * scalarCurvature (h t) x +
        (1 / 2 : ℝ) * inverseEnergyHessianSquare (h t) (scalarCurvature (h t)) x (chartPt x x) -
        inverseEnergyHeatRemainder h x t := by
  rw [minimizedScalarHarnack_heat_decomposition o h U P ρ hf hH x ht,
    scalarHarnack_heat_evolution o h U P ρ hf x ht]

end Yau.Proofs.C05Aux
