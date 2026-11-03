import Yau.Proofs.F01KahlerMixedExchange

/-! Actual scalar complex Hessians have closed holomorphic first jets.
All derivatives are the native nested real Wirtinger derivatives. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem wirt_wirt_comm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (z : E) (hf : ContDiffAt ℝ 2 f z) (v w : E) :
    wirt (fun y => wirt f y v) z w = wirt (fun y => wirt f y w) z v := by
  have hstar : ContDiffAt ℝ 2 (fun y => star (f y)) z :=
    Complex.conjCLE.contDiff.contDiffAt.comp z hf
  have hh := congrArg star (L14Aux.wirtBar_wirtBar_comm (fun y => star (f y)) z hstar v w)
  simp_rw [L14Aux.wirtBar_star, star_star] at hh
  exact hh

theorem leviC_wirt_closed (f : ComplexVector n → ℝ) {S : Set (ComplexVector n)}
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S) {z : ComplexVector n} (hz : z ∈ S)
    (i j k : Fin n) :
    wirt (fun w => leviC f w i j) z (stdVec k) =
      wirt (fun w => leviC f w i k) z (stdVec j) := by
  have hfc : ContDiffOn ℝ ∞ (fun w => (f w : ℂ)) S :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hf
  have hd : ContDiffAt ℝ 2 (fun w => wirtBar (fun y => (f y : ℂ)) w (stdVec i)) z :=
    ((L14Aux.wirtBar_contDiffOn hS _ hfc (stdVec i)).contDiffAt (hS.mem_nhds hz)).of_le
      (by simp)
  exact wirt_wirt_comm _ z hd (stdVec j) (stdVec k)

end Yau.NodeProofs.F01Aux
