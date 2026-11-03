import Yau.Proofs.E01MatrixWirtProduct
import Yau.Proofs.V03LeviLocality

/-! Actual Wirtinger derivatives of metric entries lifted to the cotangent product chart. -/

noncomputable section
open scoped Matrix Topology
open Filter

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint
open Yau.Blueprint.V03Proof

variable {n : ℕ}

theorem wirt_prod_fst {f : ComplexVector n → ℂ}
    (p v : CotangentCoord n) (hf : DifferentiableAt ℝ f p.1) :
    wirt (fun q : CotangentCoord n => f q.1) p v = wirt f p.1 v.1 := by
  unfold wirt
  have hd := fderiv_comp p hf
    (differentiableAt_fst : DifferentiableAt ℝ
      (Prod.fst : CotangentCoord n → ComplexVector n) p)
  simp only [Function.comp_def] at hd
  rw [hd]
  simp only [fderiv_fst, ContinuousLinearMap.comp_apply]
  rfl

theorem wirtBar_prod_fst {f : ComplexVector n → ℂ}
    (p v : CotangentCoord n) (hf : DifferentiableAt ℝ f p.1) :
    wirtBar (fun q : CotangentCoord n => f q.1) p v = wirtBar f p.1 v.1 := by
  unfold wirtBar
  have hd := fderiv_comp p hf
    (differentiableAt_fst : DifferentiableAt ℝ
      (Prod.fst : CotangentCoord n → ComplexVector n) p)
  simp only [Function.comp_def] at hd
  rw [hd]
  simp only [fderiv_fst, ContinuousLinearMap.comp_apply]
  rfl

theorem mixedWirt_prod_fst {f : ComplexVector n → ℂ}
    (p v : CotangentCoord n) (hf : ContDiffAt ℝ 2 f p.1) :
    wirt (fun q => wirtBar (fun r : CotangentCoord n => f r.1) q v) p v =
      wirt (fun y => wirtBar f y v.1) p.1 v.1 := by
  have hnear : ∀ᶠ q : CotangentCoord n in 𝓝 p, ContDiffAt ℝ 2 f q.1 :=
    (continuous_fst.tendsto p).eventually (hf.eventually (by norm_num))
  have heq : (fun q => wirtBar (fun r : CotangentCoord n => f r.1) q v) =ᶠ[𝓝 p]
      (fun q : CotangentCoord n => wirtBar f q.1 v.1) := by
    filter_upwards [hnear] with q hq
    exact wirtBar_prod_fst q v (hq.differentiableAt (by norm_num))
  have hw : wirt (fun q => wirtBar (fun r : CotangentCoord n => f r.1) q v) p v =
      wirt (fun q : CotangentCoord n => wirtBar f q.1 v.1) p v := by
    unfold wirt
    rw [heq.fderiv_eq]
  rw [hw, wirt_prod_fst p v (wirtBar_differentiableAt hf v.1)]

theorem complexMatrixWirt_prod_fst (H : ComplexVector n → Herm n) (p v : CotangentCoord n)
    (hH : ∀ i j, DifferentiableAt ℝ (fun w => H w i j) p.1) :
    complexMatrixWirt (fun q : CotangentCoord n => H q.1) p v = complexMatrixWirt H p.1 v.1 := by
  ext i j
  exact wirt_prod_fst (f := fun w => H w i j) p v (hH i j)

theorem complexMatrixWirtBar_prod_fst (H : ComplexVector n → Herm n) (p v : CotangentCoord n)
    (hH : ∀ i j, DifferentiableAt ℝ (fun w => H w i j) p.1) :
    complexMatrixWirtBar (fun q : CotangentCoord n => H q.1) p v = complexMatrixWirtBar H p.1 v.1 := by
  ext i j
  exact wirtBar_prod_fst (f := fun w => H w i j) p v (hH i j)

theorem complexMatrixMixed_prod_fst (H : ComplexVector n → Herm n) (p v : CotangentCoord n)
    (hH : ∀ i j, ContDiffAt ℝ 2 (fun w => H w i j) p.1) :
    complexMatrixWirt (fun q => complexMatrixWirtBar (fun r : CotangentCoord n => H r.1) q v) p v =
      complexMatrixWirt (fun w => complexMatrixWirtBar H w v.1) p.1 v.1 := by
  ext i j
  exact mixedWirt_prod_fst (f := fun w => H w i j) p v (hH i j)

end Yau.NodeProofs.E01Aux
