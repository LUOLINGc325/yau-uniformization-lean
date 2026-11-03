import Yau.LeafProofs.L05PerturbationUnitCollar
import Yau.LeafProofs.L05PerturbationHalfUnit

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_half_neg_rpow (a : ℝ) : (1/2 : ℝ)^(-a)=(2 : ℝ)^a := by
  rw [Real.rpow_neg_eq_inv_rpow]
  norm_num

theorem perturb_quantitative_collar (n : ℕ) (hn : 0 < n) (ell L kappa H0 : ℝ)
    (hell : 0 < ell) (hL : ell ≤ L) (hk0 : 0 < kappa) (hk1 : kappa < 1) (hH0 : 0 ≤ H0) :
    ∃ Cc : ℝ, 0 < Cc ∧
      ∀ (F : Sym n → ℝ) (u h : Point n → ℝ),
      Continuous F → globalElliptic F ell L → F 0=0 →
      HolderBound kappa (perturbClosed (0 : Space n) (1/2) 0) u H0 →
      ContinuousOn h (perturbClosed (0 : Space n) (1/2) 0) →
      EqOn h u (perturbBoundary (0 : Space n) (1/2) 0) →
      viscositySolution (perturbOpen (0 : Space n) (1/2) 0) (fun H _ => F H) (fun _ => 0) h →
      ∀ tau : ℝ, 0 < tau → tau ≤ 1/8 →
      ∀ p∈perturbCollar (n := n) tau, |u p-h p| ≤ Cc*tau^(kappa/4) := by
  let nu := kappa/4
  let B := perturbBoundaryBudget n ell L kappa H0
  let Cc := 1+(1/2 : ℝ)^(-nu)*B
  have hB : 0 ≤ B := perturb_boundary_budget_nonneg hn hell hL kappa hH0
  have hCc : 0 < Cc := by
    have hh : 0 ≤ (1/2 : ℝ)^(-nu)*B :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hB
    dsimp only [Cc]
    linarith
  refine ⟨Cc,hCc,?_⟩
  intro F u h hF hE h0 hU hC hEq hSol tau ht htb p hp
  let G := perturbFrozenScale F
  have hGC : Continuous G := by
    rw [show G=perturbOperatorScale F 0 4 from perturb_frozenScale_eq h0]
    exact perturb_operatorScale_continuous hF _ _
  have hGE : globalElliptic G ell L := by
    rw [show G=perturbOperatorScale F 0 4 from perturb_frozenScale_eq h0]
    exact perturb_operatorScale_elliptic hE (by norm_num) _
  have hG0 : G 0=0 := by simp [G,perturbFrozenScale,h0]
  have hData := perturb_half_holder hk0.le hU
  have hCont : ContinuousOn (fun q => h (perturbScale (1/2) q)) (unitClosed n) :=
    hC.comp (perturbScale_continuous (1/2)).continuousOn (fun _ hq => perturb_half_scale_mem hq)
  have hBoundary : EqOn (fun q => h (perturbScale (1/2) q))
      (fun q => u (perturbScale (1/2) q)) (parabolicBoundary n) := by
    intro q hq
    exact hEq (perturb_half_scale_boundary hq)
  have hSolution := perturb_half_solution_to_unit hSol
  let q := perturbScale 2 p
  have hq : q∈unitClosed n := perturb_twice_scale_closed hp.1
  have hNear : 1-2*tau ≤ ‖q.1‖ ∨ q.2 ≤ -1+(2*tau)^2 := by
    rcases hp.2 with hSpace | hTime
    · left
      change 1-2*tau ≤ ‖(2 : ℝ) • p.1‖
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith only [hSpace]
    · right
      change (2 : ℝ)^2*p.2 ≤ -1+(2*tau)^2
      have hh : p.2 ≤ -(1/2 : ℝ)^2+tau^2 := hTime
      nlinarith only [hh]
  have hUnit := perturb_unit_collar hn hell hL hk0 hk1 hGC hGE hG0 hData hCont hBoundary
    hSolution (xi := 2*tau) (by positivity) (by linarith only [htb]) hq hNear
  change |u (perturbScale (1/2) (perturbScale 2 p))-
    h (perturbScale (1/2) (perturbScale 2 p))| ≤ B*(2*tau)^nu at hUnit
  rw [perturb_half_twice,Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht.le] at hUnit
  have htPow : 0 ≤ tau^nu := Real.rpow_nonneg ht.le nu
  change |u p-h p| ≤ Cc*tau^nu
  calc
    _ ≤ B*((2 : ℝ)^nu*tau^nu) := hUnit
    _ ≤ Cc*tau^nu := by
      dsimp only [Cc]
      rw [perturb_half_neg_rpow]
      nlinarith only [htPow]

end Yau.LeafProofs.L05Aux
