import Yau.Proofs.F05BootstrapRelativeLinear

/-! Exact linearity of the original relative operator, through its actual
computed spatial Hessian and one-sided time derivative. -/

open Set
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_const_mul_jets {X : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) {f : Point n → ℝ} (hf : F05RelC2 X I f) (c : ℝ)
    {z : Point n} (hz : z ∈ X ×ˢ I) :
    F05RelD X (fun z => c*f z) z = c • F05RelD X f z ∧
      F05RelDD X (fun z => c*f z) z = c • F05RelDD X f z ∧
      F05RelT I (fun z => c*f z) z = c*F05RelT I f z := by
  have hD (p : Point n) (hp : p ∈ X ×ˢ I) :
      F05RelD X (fun z => c*f z) p = c • F05RelD X f p :=
    fderivWithin_fun_const_smul (hX p.1 hp.1)
      ((hf.2.2.2.2.1 p.2 hp.2 p.1 hp.1).differentiableWithinAt (by norm_num)) c
  refine ⟨hD z hz,?_,derivWithin_fun_const_smul c (hf.2.2.2.2.2 z hz)⟩
  rw [F05RelDD,fderivWithin_congr (fun x hx => hD (x,z.2) ⟨hx,hz.2⟩) (hD z hz)]
  exact fderivWithin_fun_const_smul (hX z.1 hz.1)
    (((hf.2.2.2.2.1 z.2 hz.2).fderivWithin hX (m := 1) (by norm_num)).differentiableOn (by norm_num) z.1 hz.1) c

theorem F05_relative_operator_add {X : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) {f g : Point n → ℝ}
    (hf : F05RelC2 X I f) (hg : F05RelC2 X I g)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) {z : Point n} (hz : z ∈ X ×ˢ I) :
    F05RelOp X I a b (fun z => f z+g z) z = F05RelOp X I a b f z+F05RelOp X I a b g z := by
  have hJets := F05_relative_add_jets hX hf hg hz
  simp only [F05RelOp,hJets.1,hJets.2.1,hJets.2.2,ContinuousLinearMap.add_apply,
    mul_add,Finset.sum_add_distrib]
  ring

theorem F05_relative_operator_const_mul {X : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) {f : Point n → ℝ} (hf : F05RelC2 X I f) (c : ℝ)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) {z : Point n} (hz : z ∈ X ×ˢ I) :
    F05RelOp X I a b (fun z => c*f z) z = c*F05RelOp X I a b f z := by
  have hJets := F05_relative_const_mul_jets hX hf c hz
  have hSecond : (∑ j,∑ k,a z j k*(c*F05RelDD X f z (realVec j) (realVec k))) =
      c*(∑ j,∑ k,a z j k*F05RelDD X f z (realVec j) (realVec k)) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hFirst : (∑ j,b z j*(c*F05RelD X f z (realVec j))) =
      c*(∑ j,b z j*F05RelD X f z (realVec j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [F05RelOp,hJets.1,hJets.2.1,hJets.2.2,ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [hSecond,hFirst]
  ring

theorem F05_relative_operator_sub {X : Set (Space n)} {I : Set ℝ}
    (hX : UniqueDiffOn ℝ X) {f g : Point n → ℝ}
    (hf : F05RelC2 X I f) (hg : F05RelC2 X I g)
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) {z : Point n} (hz : z ∈ X ×ˢ I) :
    F05RelOp X I a b (fun z => f z-g z) z = F05RelOp X I a b f z-F05RelOp X I a b g z := by
  have hOp := F05_relative_operator_add hX hf (F05_relative_c2_const_mul hX hg (-1)) a b hz
  rw [F05_relative_operator_const_mul hX hg (-1) a b hz] at hOp
  simpa only [neg_one_mul,sub_eq_add_neg] using hOp

end Yau.Proofs.F05Aux
