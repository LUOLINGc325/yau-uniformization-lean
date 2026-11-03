import Yau.Proofs.V03LeviLinear
import Yau.Proofs.V03Wirtinger

/-! Native real linearity of the actual nested mixed derivative. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

theorem mixedReal_const_mul {f : ℂ → ℝ} (hf : ContDiffAt ℝ 2 f 0) (c : ℝ) :
    mixedReal (fun z => c * f z) = c * mixedReal f := by
  unfold mixedReal
  simp only [Complex.ofReal_mul]
  have hfC : ContDiffAt ℝ 2 (fun z => (f z : ℂ)) 0 := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      hf.continuousLinearMap_comp Complex.ofRealCLM
  rw [mixedWirt_const_mul (f := fun z => (f z : ℂ)) hfC (c : ℂ) 1 1,
    Complex.re_ofReal_mul]

theorem mixedReal_finsetSum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℝ}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) 0) :
    mixedReal (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, mixedReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mixedReal, wirt, wirtBar]
  | @insert i s hi ih =>
      have hfs : ∀ j ∈ s, ContDiffAt ℝ 2 (f j) 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hfC (j : ι) (hj : j ∈ insert i s) : ContDiffAt ℝ 2 (fun z => (f j z : ℂ)) 0 := by
        simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
          (hf j hj).continuousLinearMap_comp Complex.ofRealCLM
      have hs : ContDiffAt ℝ 2 (fun z => ((∑ j ∈ s, f j z : ℝ) : ℂ)) 0 := by
        simpa only [Complex.ofReal_sum] using ContDiffAt.sum
          (fun j hj => hfC j (Finset.mem_insert_of_mem hj))
      simp only [Finset.sum_insert hi]
      rw [mixedReal_add (f := f i) (g := fun z => ∑ j ∈ s, f j z)
        (hfC i (Finset.mem_insert_self i s)) hs,
        ih hfs]

end Yau.Blueprint.V03Proof
