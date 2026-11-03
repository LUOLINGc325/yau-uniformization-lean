import Yau.LeafProofs.L05PerturbationFrozenHalf
import Yau.LeafProofs.L05PerturbationWeights
import Yau.LeafProofs.L05PucciHarnackDomains

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_scale_half_affine {n : ℕ} (p : Point n) :
    harnackAffine (0 : Space n) (1/2) (-1/4) (1/4) p=perturbScale (1/2) p := by
  rw [harnack_affine_apply]
  apply Prod.ext
  · simp only [zero_add,perturbScale]
  · change -1/4+(1/4)*(p.2+1)=(1/2 : ℝ)^2*p.2
    ring

theorem perturb_half_scale_open {n : ℕ} {p : Point n} (hp : p∈unitOpen n) :
    perturbScale (1/2) p∈perturbOpen (0 : Space n) (1/2) 0 := by
  have hh := (harnack_affine_open_mem_iff (a := -1/4) (0 : Space n)
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (0 : ℝ) < 1/4) p).mpr hp
  rw [perturb_scale_half_affine] at hh
  norm_num only [harnackOpen,perturbOpen,neg_add_cancel,zero_sub,one_div] at hh ⊢
  convert hh using 1 <;> norm_num

theorem perturb_half_scale_boundary {n : ℕ} {p : Point n} (hp : p∈parabolicBoundary n) :
    perturbScale (1/2) p∈perturbBoundary (0 : Space n) (1/2) 0 := by
  have hh := harnack_affine_maps_boundary (0 : Space n) (a := -1/4)
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (0 : ℝ) < 1/4) hp
  rw [perturb_scale_half_affine] at hh
  convert hh using 1 <;> norm_num [harnackBoundary,perturbBoundary]

theorem perturb_half_twice {n : ℕ} (p : Point n) : perturbScale (1/2) (perturbScale 2 p)=p := by
  rw [perturbScale_comp]
  norm_num
  exact perturbScale_one p

theorem perturb_half_holder {n : ℕ} {kappa H0 : ℝ} (hk : 0 ≤ kappa) {u : Point n → ℝ}
    (hu : HolderBound kappa (perturbClosed (0 : Space n) (1/2) 0) u H0) :
    HolderBound kappa (unitClosed n) (fun p => u (perturbScale (1/2) p)) H0 := by
  refine ⟨hu.1,fun p hp => hu.2.1 _ (perturb_half_scale_mem hp),?_⟩
  intro p hp q hq
  have hh := hu.2.2 _ (perturb_half_scale_mem hp) _ (perturb_half_scale_mem hq)
  rw [perturb_scale_weight (by norm_num : (0 : ℝ) < 1/2)] at hh
  have hFactor : (1/2 : ℝ)^kappa ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) hk
  have hWeight : 0 ≤ holderWeight kappa p q :=
    add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hScaled : (1/2 : ℝ)^kappa*holderWeight kappa p q ≤ holderWeight kappa p q := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hFactor hWeight
  exact hh.trans (mul_le_mul_of_nonneg_left hScaled hu.1)

theorem perturb_half_solution_to_unit {n : ℕ} {F : Sym n → ℝ} {h : Point n → ℝ}
    (hSol : viscositySolution (perturbOpen (0 : Space n) (1/2) 0)
      (fun H _ => F H) (fun _ => 0) h) :
    viscositySolution (unitOpen n) (fun H _ => perturbFrozenScale F H) (fun _ => 0)
      (fun p => h (perturbScale (1/2) p)) := by
  have hMap : MapsTo (harnackAffine (0 : Space n) (1/2) (-1/4) (1/4))
      (unitOpen n) (perturbOpen (0 : Space n) (1/2) 0) := by
    intro p hp
    rw [perturb_scale_half_affine]
    exact perturb_half_scale_open hp
  have hSub := perturb_viscosity_sub_affine hSol.1 (0 : Space n) (R := 1/2) (a := -1/4)
    (T := 1/4) (N := 1) (by norm_num) (by norm_num) (by norm_num) hMap
  have hSuper := perturb_viscosity_super_affine hSol.2 (0 : Space n) (R := 1/2) (a := -1/4)
    (T := 1/4) (N := 1) (by norm_num) (by norm_num) (by norm_num) hMap
  have hOperator (H : Sym n) : (1/4 : ℝ)*F ((1*((1/2 : ℝ)⁻¹)^2) • H)=perturbFrozenScale F H := by
    norm_num [perturbFrozenScale]
  constructor
  · simpa only [div_one,mul_zero,hOperator,perturb_scale_half_affine] using hSub
  · simpa only [div_one,mul_zero,hOperator,perturb_scale_half_affine] using hSuper

end Yau.LeafProofs.L05Aux
