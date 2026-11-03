import Yau.LeafProofs.L05PucciHarnackCylinder
import Yau.LeafProofs.L05PerturbationGeometry

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_affine_residual {T N t F : ℝ} (hT : T≠0) (hN : N≠0) :
    (T/N)*((N*T⁻¹)*t-F)=t-(T/N)*F := by
  field_simp [hT,hN]
  <;> ring

theorem perturb_viscosity_super_affine {n : ℕ}
    {D Q : Set (Point n)} {Phi : Sym n → Point n → ℝ} {u f : Point n → ℝ}
    (hv : viscositySuper Q Phi f u) (c : Space n) {R a T N : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hN : 0 < N)
    (hMap : MapsTo (harnackAffine c R a T) D Q) :
    viscositySuper D
      (fun H z => (T/N)*Phi ((N*(R⁻¹)^2) • H) (harnackAffine c R a T z))
      (fun z => (T/N)*f (harnackAffine c R a T z))
      (fun z => u (harnackAffine c R a T z)/N) := by
  intro z hz psi hpsi ht
  let phi := fun y => N*psi (harnackAffineInv c R a T y)
  have hJets := harnack_inverse_test_jets (c := c) (a := a) (h := N) hR.ne' hT.ne' hpsi
  have hTouch := harnack_touch_below_inverse hR.ne' hT.ne' hN ht
  have hRes := hv _ (hMap hz) phi hJets.1 hTouch
  change f (harnackAffine c R a T z) ≤ timeD univ phi (harnackAffine c R a T z)-
    Phi (hessian phi (harnackAffine c R a T z)) (harnackAffine c R a T z) at hRes
  rw [hJets.2.1,hJets.2.2] at hRes
  have hMul := mul_le_mul_of_nonneg_left hRes (div_nonneg hT.le hN.le)
  rw [perturb_affine_residual hT.ne' hN.ne'] at hMul
  exact hMul

theorem perturb_viscosity_sub_affine {n : ℕ}
    {D Q : Set (Point n)} {Phi : Sym n → Point n → ℝ} {u f : Point n → ℝ}
    (hv : viscositySub Q Phi f u) (c : Space n) {R a T N : ℝ}
    (hR : 0 < R) (hT : 0 < T) (hN : 0 < N)
    (hMap : MapsTo (harnackAffine c R a T) D Q) :
    viscositySub D
      (fun H z => (T/N)*Phi ((N*(R⁻¹)^2) • H) (harnackAffine c R a T z))
      (fun z => (T/N)*f (harnackAffine c R a T z))
      (fun z => u (harnackAffine c R a T z)/N) := by
  intro z hz psi hpsi ht
  let phi := fun y => N*psi (harnackAffineInv c R a T y)
  have hJets := harnack_inverse_test_jets (c := c) (a := a) (h := N) hR.ne' hT.ne' hpsi
  have hTouch := harnack_touch_above_inverse hR.ne' hT.ne' hN ht
  have hRes := hv _ (hMap hz) phi hJets.1 hTouch
  change timeD univ phi (harnackAffine c R a T z)-
    Phi (hessian phi (harnackAffine c R a T z)) (harnackAffine c R a T z) ≤
    f (harnackAffine c R a T z) at hRes
  rw [hJets.2.1,hJets.2.2] at hRes
  have hMul := mul_le_mul_of_nonneg_left hRes (div_nonneg hT.le hN.le)
  rw [perturb_affine_residual hT.ne' hN.ne'] at hMul
  exact hMul

theorem perturb_harnack_center {n : ℕ} (z : Point n) (r : ℝ) (p : Point n) :
    harnackAffine z.1 r (z.2-r^2) (r^2) p=perturbCenter z r p := by
  rw [harnack_affine_apply]
  apply Prod.ext
  · rfl
  · change z.2-r^2+r^2*(p.2+1)=z.2+r^2*p.2
    ring

end Yau.LeafProofs.L05Aux
