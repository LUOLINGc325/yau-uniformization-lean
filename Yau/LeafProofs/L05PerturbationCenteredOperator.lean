import Yau.LeafProofs.L05PerturbationCoordinates
import Yau.LeafProofs.L05PerturbationRescaledOperator

open Filter Set Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbCenteredOperator {n : ℕ} (Phi : Sym n → Point n → ℝ) (z : Point n)
    (r N : ℝ) (H : Sym n) (p : Point n) : ℝ :=
  (r^2/N)*(Phi ((N/r^2) • H) (perturbCenter z r p)-Phi 0 z)

def perturbCenteredSource {n : ℕ} (f : Point n → ℝ) (z : Point n) (r N : ℝ) (p : Point n) : ℝ :=
  (r^2/N)*(f (perturbCenter z r p)-f z)

theorem perturb_centered_operator_eq_scale {n : ℕ} (Phi : Sym n → Point n → ℝ)
    (z : Point n) (r N : ℝ) (p : Point n) :
    (fun H => perturbCenteredOperator Phi z r N H p)=
      fun H => perturbOperatorScale (fun K => Phi K (perturbCenter z r p)) 0 (N/r^2) H+
        (r^2/N)*(Phi 0 (perturbCenter z r p)-Phi 0 z) := by
  funext H
  have hRatio (a : ℝ) : a/(N/r^2)=(r^2/N)*a := by
    rw [div_eq_mul_inv,inv_div]
    ring
  dsimp only [perturbCenteredOperator,perturbOperatorScale]
  simp only [zero_add]
  rw [hRatio]
  ring

theorem perturb_centered_operator_continuousOn {n : ℕ} {Phi : Sym n → Point n → ℝ}
    (hPhi : ContinuousOn (fun a : Sym n × Point n => Phi a.1 a.2) (univ ×ˢ backward 1))
    (z : Point n) {r N : ℝ} (hr : 0 < r)
    (hBuf : perturbClosed z.1 r z.2⊆backward 1) :
    ContinuousOn (fun a : Sym n × Point n => perturbCenteredOperator Phi z r N a.1 a.2)
      (univ ×ˢ backward 1) := by
  let M : Sym n × Point n → Sym n × Point n := fun a => ((N/r^2) • a.1,perturbCenter z r a.2)
  have hM : Continuous M := ((perturb_sym_smul_continuous (N/r^2)).comp continuous_fst).prodMk
    ((perturbCenter_continuous z r).comp continuous_snd)
  have hMap : MapsTo M (univ ×ˢ backward 1) (univ ×ˢ backward 1) :=
    fun a ha => ⟨mem_univ _,perturb_center_mem_original hr hBuf ha.2⟩
  have hConst : ContinuousOn (fun _ : Sym n × Point n => Phi 0 z) (univ ×ˢ backward 1) := continuousOn_const
  have hC := ((hPhi.comp hM.continuousOn hMap).sub hConst).const_mul (r^2/N)
  simpa only [M,Function.comp_def,Pi.sub_apply,perturbCenteredOperator] using hC

theorem perturb_centered_operator_elliptic {n : ℕ} {Phi : Sym n → Point n → ℝ} {ell L : ℝ}
    (hE : ∀ p∈backward 1, globalElliptic (fun H => Phi H p) ell L) (z : Point n) {r N : ℝ}
    (hr : 0 < r) (hN : 0 < N) (hBuf : perturbClosed z.1 r z.2⊆backward 1)
    {p : Point n} (hp : p∈backward 1) :
    globalElliptic (fun H => perturbCenteredOperator Phi z r N H p) ell L := by
  rw [perturb_centered_operator_eq_scale]
  exact perturb_globalElliptic_add_const
    (perturb_operatorScale_elliptic (hE _ (perturb_center_mem_original hr hBuf hp))
      (div_pos hN (sq_pos_of_pos hr)) 0) _

theorem perturb_centered_operator_concave {n : ℕ} {Phi : Sym n → Point n → ℝ}
    (hC : ∀ p∈backward 1, ConcaveOn ℝ univ (fun H => Phi H p)) (z : Point n) {r N : ℝ}
    (hr : 0 < r) (hN : 0 < N) (hBuf : perturbClosed z.1 r z.2⊆backward 1)
    {p : Point n} (hp : p∈backward 1) :
    ConcaveOn ℝ univ (fun H => perturbCenteredOperator Phi z r N H p) := by
  rw [perturb_centered_operator_eq_scale]
  exact (perturb_operatorScale_concave (hC _ (perturb_center_mem_original hr hBuf hp))
    (div_pos hN (sq_pos_of_pos hr)) 0).add_const _

theorem perturb_centered_operator_zero {n : ℕ} (Phi : Sym n → Point n → ℝ)
    (z : Point n) (r N : ℝ) : perturbCenteredOperator Phi z r N 0 (0,0)=0 := by
  simp [perturbCenteredOperator,perturbCenter_zero]

theorem perturb_centered_source_zero {n : ℕ} (f : Point n → ℝ) (z : Point n) (r N : ℝ) :
    perturbCenteredSource f z r N (0,0)=0 := by simp [perturbCenteredSource,perturbCenter_zero]

theorem perturb_centered_equation {n : ℕ} {Phi : Sym n → Point n → ℝ} {f u : Point n → ℝ}
    (hu : C2 (backward 1) u)
    (hPDE : ∀ p∈backward 1, timeD (backward 1) u p-Phi (hessian u p) p=f p)
    (z : Point n) {r N q0 : ℝ} (hr : 0 < r) (hN : 0 < N)
    (hBuf : perturbClosed z.1 r z.2⊆backward 1) (hq : q0=Phi 0 z+f z) :
    C2 (backward 1) (perturbNormalize u z r N q0) ∧
      ∀ p∈backward 1, timeD (backward 1) (perturbNormalize u z r N q0) p-
        perturbCenteredOperator Phi z r N (hessian (perturbNormalize u z r N q0) p) p=
          perturbCenteredSource f z r N p := by
  refine ⟨perturb_normalize_c2 hu z hr hBuf,?_⟩
  intro p hp
  rw [perturb_normalize_timeD hu z hr hBuf hp,perturb_normalize_hessian hu z hr hBuf hp]
  have hMatrix : (N/r^2) • ((r^2/N) • hessian u (perturbCenter z r p))=hessian u (perturbCenter z r p) := by
    rw [smul_smul]
    have hCoef : (N/r^2)*(r^2/N)=1 := by field_simp [hr.ne',hN.ne']
    rw [hCoef,one_smul]
  dsimp only [perturbCenteredOperator,perturbCenteredSource]
  rw [hMatrix]
  calc
    _ = (r^2/N)*((timeD (backward 1) u (perturbCenter z r p)-
        Phi (hessian u (perturbCenter z r p)) (perturbCenter z r p))-f z) := by rw [hq]; ring
    _ = _ := by rw [hPDE _ (perturb_center_mem_original hr hBuf hp)]

end Yau.LeafProofs.L05Aux
