import Yau.LeafProofs.L05PerturbationRescaling
import Yau.LeafProofs.L05PerturbationOperatorScaling

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_sym_smul_continuous {n : ℕ} (a : ℝ) :
    Continuous (fun H : Sym n => a • H) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun H : Sym n => a • (H : Mat n))
  exact (continuous_const : Continuous (fun _ : Sym n => a)).smul
    (continuous_subtype_val : Continuous (fun H : Sym n => (H : Mat n)))

theorem perturb_sym_smul_norm {n : ℕ} (a : ℝ) (A : Sym n) : ‖a • A‖=|a| *‖A‖ := by
  change ‖a • (A : Mat n)‖=|a| *‖(A : Mat n)‖
  rw [norm_smul,Real.norm_eq_abs]

theorem perturb_globalElliptic_add_const {n : ℕ} {F : Sym n → ℝ} {ell L : ℝ}
    (hF : globalElliptic F ell L) (c : ℝ) : globalElliptic (fun H => F H+c) ell L := by
  intro N P hP
  simpa only [add_sub_add_right_eq_sub] using hF N P hP

theorem perturb_iter_operator_eq_normalized {n : ℕ} (Phi : Sym n → Point n → ℝ)
    (A : Sym n) (r eta : ℝ) (p : Point n) :
    (fun H => perturbIterOperator Phi A r eta H p)=
      fun H => perturbOperatorScale (fun K => Phi K (perturbScale r p)) A (r^eta) H+
        (r^eta)⁻¹*(Phi A (perturbScale r p)-Phi A (0,0)) := by
  funext H
  dsimp only [perturbIterOperator,perturbOperatorScale]
  ring

theorem perturb_iter_operator_elliptic {n : ℕ} {Phi : Sym n → Point n → ℝ} {ell L r eta : ℝ}
    (hE : ∀ p∈backward 1, globalElliptic (fun H => Phi H p) ell L)
    (hr : 0 < r) (hr1 : r ≤ 1) (A : Sym n) {p : Point n} (hp : p∈backward 1) :
    globalElliptic (fun H => perturbIterOperator Phi A r eta H p) ell L := by
  rw [perturb_iter_operator_eq_normalized]
  exact perturb_globalElliptic_add_const
    (perturb_operatorScale_elliptic (hE _ (perturb_scale_back_mem hr hr1 hp))
      (Real.rpow_pos_of_pos hr eta) A) _

theorem perturb_iter_operator_concave {n : ℕ} {Phi : Sym n → Point n → ℝ} {r eta : ℝ}
    (hC : ∀ p∈backward 1, ConcaveOn ℝ univ (fun H => Phi H p))
    (hr : 0 < r) (hr1 : r ≤ 1) (A : Sym n) {p : Point n} (hp : p∈backward 1) :
    ConcaveOn ℝ univ (fun H => perturbIterOperator Phi A r eta H p) := by
  rw [perturb_iter_operator_eq_normalized]
  exact (perturb_operatorScale_concave (hC _ (perturb_scale_back_mem hr hr1 hp))
    (Real.rpow_pos_of_pos hr eta) A).add_const _

theorem perturb_iter_operator_continuousOn {n : ℕ} {Phi : Sym n → Point n → ℝ}
    (hC : ContinuousOn (fun z : Sym n × Point n => Phi z.1 z.2) (univ ×ˢ backward 1))
    {r eta : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (A : Sym n) :
    ContinuousOn (fun z : Sym n × Point n => perturbIterOperator Phi A r eta z.1 z.2)
      (univ ×ˢ backward 1) := by
  let M : Sym n × Point n → Sym n × Point n := fun z => (A+r^eta • z.1,perturbScale r z.2)
  have hFirst : Continuous (fun z : Sym n × Point n => A+r^eta • z.1) :=
    continuous_const.add ((perturb_sym_smul_continuous (r^eta)).comp continuous_fst)
  have hM : Continuous M := hFirst.prodMk ((perturbScale_continuous r).comp continuous_snd)
  have hMap : MapsTo M (univ ×ˢ backward 1) (univ ×ˢ backward 1) := by
    intro z hz
    exact ⟨mem_univ _,perturb_scale_back_mem hr hr1 hz.2⟩
  have hConst : ContinuousOn (fun _ : Sym n × Point n => Phi A (0,0)) (univ ×ˢ backward 1) := continuousOn_const
  have hh := ((hC.comp hM.continuousOn hMap).sub hConst).const_mul (r^eta)⁻¹
  simpa only [M,Function.comp_def,Pi.sub_apply,perturbIterOperator] using hh

theorem perturb_iter_operator_zero {n : ℕ} (Phi : Sym n → Point n → ℝ)
    (A : Sym n) (r eta : ℝ) : perturbIterOperator Phi A r eta 0 (0,0)=0 := by
  simp [perturbIterOperator,perturbScale]

theorem perturb_iter_source_zero {n : ℕ} (f : Point n → ℝ) (r eta : ℝ) :
    perturbIterSource f r eta (0,0)=0 := by simp [perturbIterSource,perturbScale]

end Yau.LeafProofs.L05Aux
