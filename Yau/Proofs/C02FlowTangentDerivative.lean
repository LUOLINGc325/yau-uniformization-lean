import Yau.Proofs.C02FieldOrder
import Yau.Proofs.C02RicciQuadraticBound

noncomputable section
open Set
open scoped Matrix Manifold
namespace Yau.Blueprint.C02Proof
open Yau.NodeProofs.G01Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem centralMetricPairing_re (h : HermitianField M) (x : M.Carrier) (v : TangentVector M x) :
    (complexMatrixPairing (gMat h x) (tangentCoords x x v) (tangentCoords x x v)).re =
      hermitianNormSq (h x) v := by
  rw [← gMat_quadratic_tangent h x v]
  apply congrArg Complex.re
  simp only [complexMatrixPairing, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem kahlerRicciFlow_tangentNormSq_hasDerivWithinAt
    (g : HermitianField M) (h : ℝ → HermitianField M) (hflow : IsKahlerRicciFlow g h)
    (x : M.Carrier) (v : TangentVector M x) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => hermitianNormSq (h s x) v)
      (-centralRicciQuadratic (h t) x v) (Ici 0) t := by
  let c := tangentCoords x x v
  have hd : HasDerivWithinAt (fun s => complexMatrixPairing (gMat (h s) x) c c)
      (-complexMatrixPairing (ricci (h t) x) c c) (Ici 0) t := by
    have hh := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun a _ =>
      HasDerivWithinAt.fun_sum (u := Finset.univ) (fun b _ =>
        ((hflow.2.2.2 x t ht a b).mul_const (c b)).mul_const (star (c a))))
    simpa only [complexMatrixPairing, neg_mul, Finset.sum_neg_distrib] using hh
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
  have hfun : (fun s => (complexMatrixPairing (gMat (h s) x) c c).re) =
      (fun s => hermitianNormSq (h s x) v) := funext (fun s => centralMetricPairing_re (h s) x v)
  rw [← hfun]
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.neg_re,
    centralRicciQuadratic, c] using hr

end Yau.Blueprint.C02Proof
