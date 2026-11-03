import Yau.LeafProofs.L05PerturbationScaleC2
import Yau.LeafProofs.L16

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_c2_hessian_sub {n : ℕ} {Q : Set (Point n)} {u v : Point n → ℝ}
    (hu : C2 Q u) (hv : C2 Q v) {p : Point n} (hp : p∈Q) :
    hessian (fun p => u p-v p) p=hessian u p-hessian v p := by
  have he : (fun i j => spatialDD (fun q => u q-v q) p (realVec i) (realVec j) : Mat n)=
      (fun i j => spatialDD u p (realVec i) (realVec j) : Mat n)-
      (fun i j => spatialDD v p (realVec i) (realVec j) : Mat n) := by
    ext i j
    rw [L16Aux.spatialDD_sub hu hv hp]
    rfl
  unfold hessian sym
  rw [he]
  exact (selfAdjointPart ℝ).map_sub _ _

theorem perturb_polynomial_sub_c2 {n : ℕ} {u : Point n → ℝ} (hu : C2 (backward 1) u)
    (c : ℝ) (b : Space n →L[ℝ] ℝ) (A : Sym n) (q : ℝ) :
    C2 (backward 1) (fun p => u p-perturbPolynomial c b A q p) :=
  L16Aux.c2_sub hu (perturb_polynomial_c2 c b A q 1)

theorem perturb_polynomial_sub_hessian {n : ℕ} {u : Point n → ℝ} (hu : C2 (backward 1) u)
    (c : ℝ) (b : Space n →L[ℝ] ℝ) (A : Sym n) (q : ℝ) {p : Point n} (hp : p∈backward 1) :
    hessian (fun p => u p-perturbPolynomial c b A q p) p=hessian u p-A := by
  rw [perturb_c2_hessian_sub hu (perturb_polynomial_c2 c b A q 1) hp,
    perturb_polynomial_hessian]

theorem perturb_polynomial_sub_timeD {n : ℕ} {u : Point n → ℝ} (hu : C2 (backward 1) u)
    (c : ℝ) (b : Space n →L[ℝ] ℝ) (A : Sym n) (q : ℝ) {p : Point n} (hp : p∈backward 1) :
    timeD (backward 1) (fun p => u p-perturbPolynomial c b A q p) p=timeD (backward 1) u p-q := by
  rw [L16Aux.timeD_sub hu (perturb_polynomial_c2 c b A q 1) hp,
    perturb_polynomial_timeD c b A q 1 hp]

end Yau.LeafProofs.L05Aux
