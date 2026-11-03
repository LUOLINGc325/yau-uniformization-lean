import Yau.LeafProofs.L05PerturbationPolynomialSubtraction
import Yau.LeafProofs.L05PerturbationData

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perturbIterOperator {n : ℕ} (Phi : Sym n → Point n → ℝ)
    (A : Sym n) (r eta : ℝ) (H : Sym n) (p : Point n) : ℝ :=
  (r^eta)⁻¹*(Phi (A+r^eta • H) (perturbScale r p)-Phi A (0,0))

def perturbIterSource {n : ℕ} (f : Point n → ℝ) (r eta : ℝ) (p : Point n) : ℝ :=
  (r^eta)⁻¹*(f (perturbScale r p)-f (0,0))

def perturbIterSolution {n : ℕ} (u : Point n → ℝ) (c : ℝ)
    (b : Space n →L[ℝ] ℝ) (A : Sym n) (q r eta : ℝ) (p : Point n) : ℝ :=
  (r^(2+eta))⁻¹*(u (perturbScale r p)-perturbPolynomial c b A q (perturbScale r p))

theorem perturb_iter_solution_eq_scaleValue {n : ℕ} (u : Point n → ℝ) (c : ℝ)
    (b : Space n →L[ℝ] ℝ) (A : Sym n) (q r eta : ℝ) :
    perturbIterSolution u c b A q r eta=
      perturbScaleValue (fun p => u p-perturbPolynomial c b A q p) r (r^(2+eta)) := by
  funext p
  dsimp only [perturbIterSolution,perturbScaleValue]
  ring

theorem perturb_iter_scale_ratio {r eta : ℝ} (hr : 0 < r) : r^2/r^(2+eta)=(r^eta)⁻¹ := by
  rw [Real.rpow_add hr,Real.rpow_two]
  have hR := (sq_pos_of_pos hr).ne'
  have hE := (Real.rpow_pos_of_pos hr eta).ne'
  field_simp [hR,hE]

theorem perturb_iter_c2 {n : ℕ} {u : Point n → ℝ} (hu : C2 (backward 1) u)
    {r eta : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (c : ℝ) (b : Space n →L[ℝ] ℝ)
    (A : Sym n) (q : ℝ) : C2 (backward 1) (perturbIterSolution u c b A q r eta) := by
  rw [perturb_iter_solution_eq_scaleValue]
  exact perturb_scaleValue_c2 (perturb_polynomial_sub_c2 hu c b A q) hr hr1

theorem perturb_iter_hessian {n : ℕ} {u : Point n → ℝ} (hu : C2 (backward 1) u)
    {r eta : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (c : ℝ) (b : Space n →L[ℝ] ℝ)
    (A : Sym n) (q : ℝ) {p : Point n} (hp : p∈backward 1) :
    hessian (perturbIterSolution u c b A q r eta) p=
      (r^eta)⁻¹ • (hessian u (perturbScale r p)-A) := by
  rw [perturb_iter_solution_eq_scaleValue,
    perturb_scaleValue_hessian (perturb_polynomial_sub_c2 hu c b A q) hr hr1 hp,
    perturb_polynomial_sub_hessian hu c b A q (perturb_scale_back_mem hr hr1 hp),
    perturb_iter_scale_ratio hr]

theorem perturb_iter_timeD {n : ℕ} {u : Point n → ℝ} (hu : C2 (backward 1) u)
    {r eta : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (c : ℝ) (b : Space n →L[ℝ] ℝ)
    (A : Sym n) (q : ℝ) {p : Point n} (hp : p∈backward 1) :
    timeD (backward 1) (perturbIterSolution u c b A q r eta) p=
      (r^eta)⁻¹*(timeD (backward 1) u (perturbScale r p)-q) := by
  rw [perturb_iter_solution_eq_scaleValue,
    perturb_scaleValue_timeD (perturb_polynomial_sub_c2 hu c b A q) hr hr1 hp,
    perturb_polynomial_sub_timeD hu c b A q (perturb_scale_back_mem hr hr1 hp),
    perturb_iter_scale_ratio hr]

theorem perturb_iter_equation {n : ℕ} {r eta q c : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (b : Space n →L[ℝ] ℝ) (A : Sym n)
    {Phi : Sym n → Point n → ℝ} {f u : Point n → ℝ} (hu : C2 (backward 1) u)
    (hpde : ∀ p∈backward 1, timeD (backward 1) u p-Phi (hessian u p) p=f p)
    (hq : q=Phi A (0,0)+f (0,0)) :
    let v := perturbIterSolution u c b A q r eta
    C2 (backward 1) v ∧ ∀ p∈backward 1,
      timeD (backward 1) v p-perturbIterOperator Phi A r eta (hessian v p) p=
        perturbIterSource f r eta p := by
  intro v
  refine ⟨perturb_iter_c2 hu hr hr1 c b A q,?_⟩
  intro p hp
  have hOrig := hpde _ (perturb_scale_back_mem hr hr1 hp)
  change timeD (backward 1) (perturbIterSolution u c b A q r eta) p-
    perturbIterOperator Phi A r eta (hessian (perturbIterSolution u c b A q r eta) p) p= _
  rw [perturb_iter_timeD hu hr hr1 c b A q hp,perturb_iter_hessian hu hr hr1 c b A q hp]
  have hMatrix : A+r^eta • ((r^eta)⁻¹ • (hessian u (perturbScale r p)-A))=hessian u (perturbScale r p) := by
    rw [smul_smul,mul_inv_cancel₀ (Real.rpow_pos_of_pos hr eta).ne',one_smul]
    abel
  dsimp only [perturbIterOperator,perturbIterSource]
  rw [hMatrix]
  calc
    _ = (r^eta)⁻¹*((timeD (backward 1) u (perturbScale r p)-
        Phi (hessian u (perturbScale r p)) (perturbScale r p))-f (0,0)) := by rw [hq]; ring
    _ = _ := by rw [hOrig]

end Yau.LeafProofs.L05Aux
