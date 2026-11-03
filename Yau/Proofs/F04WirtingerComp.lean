import Yau.Proofs.F04LeviProduct

open Filter Set
open scoped Topology ContDiff Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

theorem wirt_real_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : V → ℝ} {F : ℝ → ℝ} {z : V} {a : ℝ}
    (hf : DifferentiableAt ℝ f z) (hF : HasDerivAt F a (f z)) (v : V) :
    wirt (fun y => (F (f y) : ℂ)) z v = (a : ℂ) * wirt (fun y => (f y : ℂ)) z v ∧
      wirtBar (fun y => (F (f y) : ℂ)) z v = (a : ℂ) * wirtBar (fun y => (f y : ℂ)) z v := by
  have hreal : HasFDerivAt (fun y => F (f y)) (a • fderiv ℝ f z) z :=
    hF.comp_hasFDerivAt z hf.hasFDerivAt
  have hcomp : HasFDerivAt (fun y => (F (f y) : ℂ))
      (Complex.ofRealCLM.comp (a • fderiv ℝ f z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hreal
  have hbase : HasFDerivAt (fun y => (f y : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ f z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hf.hasFDerivAt
  simp only [wirt, wirtBar, hcomp.fderiv, hbase.fderiv,
    ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul,
    Complex.ofRealCLM_apply, Complex.ofReal_mul]
  constructor <;> ring

end Yau.F04Proof
