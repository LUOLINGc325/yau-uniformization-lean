import Yau.LeafProofs.L05PerturbationPolynomials

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_extraction_time_identity {n : ℕ} (c q r T : ℝ)
    (b : Space n →L[ℝ] ℝ) (A : Sym n) (x : Space n) :
    perturbPolynomial c b A q (x,T)-perturbPolynomial c b A q (x,T-r^2)=q*r^2 := by
  dsimp only [perturbPolynomial]
  ring

theorem perturb_extraction_space_identity {n : ℕ} (c q r T : ℝ)
    (b : Space n →L[ℝ] ℝ) (A : Sym n) (x e : Space n) :
    perturbPolynomial c b A q (x+r • e,T)+perturbPolynomial c b A q (x-r • e,T)-
      2*perturbPolynomial c b A q (x,T)=r^2*perturbBilinear A e e := by
  simp only [perturbPolynomial,perturbQuad_eq_bilinear,map_add,map_sub,map_smul,
    add_apply,sub_apply,smul_apply,
    smul_eq_mul]
  ring

end Yau.LeafProofs.L05Aux
