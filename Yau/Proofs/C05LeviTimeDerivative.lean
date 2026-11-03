import Yau.Proofs.C05SpaceTimeDirections
import Yau.LeafProofs.L18

/-! Time differentiation commutes with the actual Levi matrix in a fixed
holomorphic coordinate domain. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C05Aux
open Yau
variable {n : ℕ}

theorem leviC_eq_real_hessian {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (i j : Fin n) :
    leviC f z i j =
      (((fderiv ℝ (fderiv ℝ f) z (stdVec j) (stdVec i) +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • stdVec j) (Complex.I • stdVec i)) / 4 : ℝ) : ℂ) +
      Complex.I * (((fderiv ℝ (fderiv ℝ f) z (stdVec j) (Complex.I • stdVec i) -
        fderiv ℝ (fderiv ℝ f) z (Complex.I • stdVec j) (stdVec i)) / 4 : ℝ) : ℂ) := by
  obtain ⟨hr, hi⟩ := Yau.LeafProofs.L18Aux.leviMatrix_entry_re_im hf stdVec i j
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, mul_zero, sub_zero, zero_add, add_zero]
  · change (leviMatrix f z stdVec i j).re = _
    linarith
  · change (leviMatrix f z stdVec i j).im = _
    linarith

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_leviC_spaceTime {F : ComplexVector n × ℝ → ℝ}
    {z : ComplexVector n} {t : ℝ} (hf : ContDiffAt ℝ 3 F (z, t)) (i j : Fin n) :
    HasDerivAt (fun s => leviC (fun y => F (y, s)) z i j)
      (leviC (fun y => directionalDerivative (0, 1) F (y, t)) z i j) t := by
  let H (s : ℝ) (v w : ComplexVector n) :=
    fderiv ℝ (fderiv ℝ (fun y => F (y, s))) z v w
  let D (v w : ComplexVector n) :=
    fderiv ℝ (fderiv ℝ (fun y => directionalDerivative (0, 1) F (y, t))) z v w
  have hdt : ContDiffAt ℝ 2 (directionalDerivative (0, 1) F) (z, t) :=
    contDiffAt_directionalDerivative hf (by norm_num) (0, 1)
  have hD (v w : ComplexVector n) : HasDerivAt (fun s => H s v w) (D v w) t := by
    have hd := hasDerivAt_second_spatial_derivative hf v w
    rw [← second_left_directionalDerivative hdt v w] at hd
    exact hd
  have hr := ((hD (stdVec j) (stdVec i)).add
    (hD (Complex.I • stdVec j) (Complex.I • stdVec i))).div_const 4
  have hi := ((hD (stdVec j) (Complex.I • stdVec i)).sub
    (hD (Complex.I • stdVec j) (stdVec i))).div_const 4
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hr).add
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hi).const_mul Complex.I)
  have htarget := leviC_eq_real_hessian
    (hdt.comp z (contDiffAt_id.prodMk contDiffAt_const)) i j
  simp only [Function.comp_def, id_eq] at htarget
  rw [htarget]
  apply hd.congr_of_eventuallyEq
  have hh : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 3 F (z, s) :=
    (show ContinuousAt (fun s : ℝ => (z, s)) t from
      continuousAt_const.prodMk continuousAt_id).eventually (hf.eventually (by norm_num))
  filter_upwards [hh] with s hs
  exact leviC_eq_real_hessian
    ((hs.of_le (by norm_num)).comp z (contDiffAt_id.prodMk contDiffAt_const)) i j

end Yau.Proofs.C05Aux
