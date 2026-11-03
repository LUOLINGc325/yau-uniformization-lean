import Yau.LeafProofs.L05PerturbationCoreABPGeometry
import Yau.LeafProofs.L05PerturbationCoreABPInterval
import Yau.LeafProofs.L05PerturbationCoreABPMeasure
import Yau.LeafProofs.L05PerronLattice

noncomputable section

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

open Filter MeasureTheory Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem perturb_core_abp (n : ℕ) (_hn : 0 < n) (ell L : ℝ) (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (tau G E : ℝ) (v : Point n → ℝ),
      0 < tau → tau ≤ 1/8 → 0 ≤ G → ContinuousOn v (perturbCore tau) →
      (∀ p ∈ perturbCoreBoundary tau, v p ≤ E) →
      viscositySub (perturbCoreOpen tau) (fun H _ => pucciPlus ell L H) (fun _ => G) v →
      ∀ p ∈ perturbCore tau, v p ≤ E+C*G := by
  let V : ℝ := perturbCoreABPUnitVolume n
  let exponent : ℝ := 1/((2*n+1 : ℕ):ℝ)
  have hV : 0 < V := perturb_core_abp_unit_volume_pos n
  have hRoot : 0 ≤ V^exponent := Real.rpow_nonneg hV.le _
  have hCabp := abpC_pos n hell
  refine ⟨1+abpC n ell*V^exponent,by positivity,?_⟩
  intro tau G E v ht ht1 hG hv hboundary hsub p hp
  let R : ℝ := perturbCoreABPRadius tau
  let T : ℝ := perturbCoreABPTime tau
  have hGeo := perturb_core_abp_geometry ht ht1
  have hR : 0 < R := hGeo.1
  have hT : 0 < T := hGeo.2.1
  have hT1 : T ≤ 1 := hGeo.2.2.1
  have hq1 : 1 ≤ T/R^2 := hGeo.2.2.2.1
  have hq2 : T/R^2 ≤ 2 := hGeo.2.2.2.2
  have hMap : MapsTo (harnackAffine (0 : Space n) R (-T) T) (unitClosed n) (perturbCore tau) := by
    intro z hz
    rw [perturb_core_abp_closed_eq]
    exact (harnack_affine_closed_mem_iff (a := -T) (0 : Space n) hR hT z).mpr hz
  have hMapOpen : MapsTo (harnackAffine (0 : Space n) R (-T) T) (unitOpen n) (perturbCoreOpen tau) := by
    intro z hz
    rw [perturb_core_abp_open_eq]
    exact (harnack_affine_open_mem_iff (a := -T) (0 : Space n) hR hT z).mpr hz
  have hWcont : ContinuousOn (fun z => v (harnackAffine (0 : Space n) R (-T) T z)-E) (unitClosed n) :=
    ((hv.sub continuousOn_const).comp (harnack_affine_contDiff (0 : Space n) R (-T) T).continuous.continuousOn hMap)
  have hBoundary (z : Point n) (hz : z ∈ parabolicBoundary n) :
      v (harnackAffine (0 : Space n) R (-T) T z)-E ≤ 0 := by
    apply sub_nonpos.mpr
    apply hboundary
    rw [perturb_core_abp_boundary_eq]
    exact harnack_affine_maps_boundary (0 : Space n) hR hT hz
  have hSubw : viscositySub (perturbCoreOpen tau) (fun H _ => pucciPlus ell L H) (fun _ => G)
      (fun z => v z-E) := by
    simpa only [sub_eq_add_neg] using viscositySub_add_const hsub (-E)
  have hPull := harnack_sub_affine_pullback hell.le hL hSubw (0 : Space n) (a := -T) hR hT
    (by norm_num : (0:ℝ) < 1) hMapOpen
  simp only [div_one] at hPull
  have hFixed := perturb_core_abp_viscosity_widen hell.le hL hq1 hq2 hPull
  have hInv : harnackAffineInv (0 : Space n) R (-T) T p ∈ unitClosed n := by
    apply (harnack_affine_closed_mem_iff (a := -T) (0 : Space n) hR hT _).mp
    rw [harnack_affine_apply_inv hR.ne' hT.ne']
    rwa [← perturb_core_abp_closed_eq tau]
  have hLfixed : ell ≤ 2*L := by linarith only [hell,hL]
  have hABP := viscosity_abp_closed hell hLfixed hWcont continuousOn_const hBoundary hFixed hInv
  rw [harnack_affine_apply_inv hR.ne' hT.ne',perturb_core_abp_constant_root n (mul_nonneg hT.le hG)] at hABP
  have hTG : T*G ≤ G := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hT1 hG
  have hScaled := mul_le_mul_of_nonneg_left hTG (mul_nonneg hCabp.le hRoot)
  change v p ≤ E+(1+abpC n ell*V^exponent)*G
  change v p-E ≤ abpC n ell*((T*G)*V^exponent) at hABP
  nlinarith only [hABP,hScaled,hG]

end Yau.LeafProofs.L05Aux
