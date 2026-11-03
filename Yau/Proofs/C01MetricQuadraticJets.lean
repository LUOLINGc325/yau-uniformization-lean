import Yau.Proofs.C01FlowTimeJets

/-! Actual constant-vector metric quadratic derivatives and one-sided
continuity for comparison of the original matrices h_t. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_metric_quadratic_contDiffOn
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) (v : Fin n → ℂ) :
    ContDiffOn ℝ ∞ (fun t => (star v ⬝ᵥ (gMat (h t) x *ᵥ v)).re) (Set.Ici 0) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  apply Complex.reCLM.contDiff.comp_contDiffOn
  exact ContDiffOn.sum fun i _ => contDiffOn_const.mul
    (ContDiffOn.sum fun j _ => (localizedFlow_gMat_time_contDiffOn hflow x i j).mul contDiffOn_const)

theorem localizedFlow_metric_quadratic_hasDerivAt
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t)
    (v : Fin n → ℂ) :
    HasDerivAt (fun s => (star v ⬝ᵥ (gMat (h s) x *ᵥ v)).re)
      (-(star v ⬝ᵥ (ricci (h t) x *ᵥ v)).re) t := by
  have hi (i : Fin n) := HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (localizedFlow_gMat_hasDerivAt hflow x ht i j).mul_const (v j))
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hi i).const_mul (star (v i)))
  have hcomplex : HasDerivAt (fun s => star v ⬝ᵥ (gMat (h s) x *ᵥ v))
      (-(star v ⬝ᵥ (ricci (h t) x *ᵥ v))) t := by
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, neg_mul, mul_neg,
      Finset.sum_neg_distrib] using! hsum
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, Complex.reCLM_apply,
    Complex.neg_re] using!
      (Complex.reCLM.hasFDerivAt.comp t hcomplex.hasFDerivAt).hasDerivAt

end Yau.NodeProofs.C01Aux
