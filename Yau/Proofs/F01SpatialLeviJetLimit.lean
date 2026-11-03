import Yau.Proofs.F01ClosedLeviLimit

/-! The actual spatial second Frechet jet controls the native nested
Wirtinger Levi matrix. This endpoint version needs no joint time jet. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem spatial_levi_entry_limit_of_second_jets
    (f : ℕ → ComplexVector n → ℝ) (u : ComplexVector n → ℝ) (x : ComplexVector n)
    (hf : ∀ m, ContDiffAt ℝ 2 (f m) x) (hu : ContDiffAt ℝ 2 u x)
    (hJet : Tendsto (fun m => iteratedFDeriv ℝ 2 (f m) x) atTop
      (𝓝 (iteratedFDeriv ℝ 2 u x))) (i j : Fin n) :
    Tendsto (fun m => leviC (f m) x i j) atTop (𝓝 (leviC u x i j)) := by
  have hsecond (v w : ComplexVector n) :
      Tendsto (fun m => fderiv ℝ (fderiv ℝ (f m)) x v w) atTop
        (𝓝 (fderiv ℝ (fderiv ℝ u) x v w)) := by
    have hEval : Continuous (fun D : ContinuousMultilinearMap ℝ
        (fun _ : Fin 2 => ComplexVector n) ℝ => D ![v, w]) := by fun_prop
    have hh := hEval.continuousAt.tendsto.comp hJet
    have heq (q : ComplexVector n → ℝ) :
        iteratedFDeriv ℝ 2 q x ![v, w] = fderiv ℝ (fderiv ℝ q) x v w := by
      rw [iteratedFDeriv_two_apply]
      rfl
    have hSeq : (fun m => fderiv ℝ (fderiv ℝ (f m)) x v w) =
        fun m => iteratedFDeriv ℝ 2 (f m) x ![v, w] := funext (fun m => (heq (f m)).symm)
    rw [hSeq, ← heq u]
    exact hh
  have hRF (m : ℕ) := (LeafProofs.L18Aux.leviMatrix_entry_re_im (hf m) stdVec i j).1
  have hIF (m : ℕ) := (LeafProofs.L18Aux.leviMatrix_entry_re_im (hf m) stdVec i j).2
  have hRU := (LeafProofs.L18Aux.leviMatrix_entry_re_im hu stdVec i j).1
  have hIU := (LeafProofs.L18Aux.leviMatrix_entry_re_im hu stdVec i j).2
  have hre : Tendsto (fun m => (leviC (f m) x i j).re) atTop (𝓝 ((leviC u x i j).re)) := by
    simpa only [leviC, hRF, hRU] using
      ((hsecond (stdVec j) (stdVec i)).add
        (hsecond (Complex.I • stdVec j) (Complex.I • stdVec i))).const_mul (1 / 4 : ℝ)
  have him : Tendsto (fun m => (leviC (f m) x i j).im) atTop (𝓝 ((leviC u x i j).im)) := by
    simpa only [leviC, hIF, hIU] using
      ((hsecond (stdVec j) (Complex.I • stdVec i)).sub
        (hsecond (Complex.I • stdVec j) (stdVec i))).const_mul (1 / 4 : ℝ)
  have hh := Complex.equivRealProdCLM.symm.continuous.continuousAt.tendsto.comp (hre.prodMk_nhds him)
  simpa only [Function.comp_def, Complex.equivRealProdCLM_symm_apply, Complex.re_add_im] using hh

end Yau.NodeProofs.F01Aux
