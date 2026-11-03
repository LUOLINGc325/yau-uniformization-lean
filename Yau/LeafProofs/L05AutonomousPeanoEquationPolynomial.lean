import Yau.LeafProofs.L05AutonomousSliceTests
import Yau.LeafProofs.L05ABPPeano

noncomputable section
open Filter Set Asymptotics
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

def autoPeanoSpatialPolynomial {n : ℕ} (c : ℝ) (x : Space n)
    (l : Space n →L[ℝ] ℝ) (B : Space n →L[ℝ] Space n →L[ℝ] ℝ)
    (eta : ℝ) (y : Space n) : ℝ :=
  c+l (y-x)+(1/2 : ℝ)*B (y-x) (y-x)+eta*‖y-x‖^2

theorem autoPeanoSpatialPolynomial_eq_restriction {n : ℕ} (c : ℝ) (x : Space n)
    (l : Space n →L[ℝ] ℝ) (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) (eta : ℝ) :
    autoPeanoSpatialPolynomial c x l B eta = fun y : Space n =>
      peanoPolynomial c (x,0) (l.comp (ContinuousLinearMap.fst ℝ (Space n) ℝ))
        (B.bilinearComp (ContinuousLinearMap.fst ℝ (Space n) ℝ)
          (ContinuousLinearMap.fst ℝ (Space n) ℝ)) eta (y,0) := by
  funext y
  simp [autoPeanoSpatialPolynomial,peanoPolynomial,qnorm2,ContinuousLinearMap.bilinearComp_apply]

theorem autoPeanoSpatialPolynomial_smooth {n : ℕ} (c : ℝ) (x : Space n)
    (l : Space n →L[ℝ] ℝ) (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) (eta : ℝ) :
    ContDiff ℝ ∞ (autoPeanoSpatialPolynomial c x l B eta) := by
  rw [autoPeanoSpatialPolynomial_eq_restriction]
  exact (peanoPolynomial_smooth c (x,0) _ _ eta).comp
    (contDiff_id.prodMk contDiff_const)

def autoPeanoHessianPerturbation {n : ℕ}
    (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) (eta : ℝ) : Sym n :=
  sym (fun i j => B (Yau.realVec i) (Yau.realVec j)+
    (2*eta)*inner ℝ (Yau.realVec i) (Yau.realVec j))

theorem autoPeanoHessianPerturbation_zero {n : ℕ}
    (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    autoPeanoHessianPerturbation B 0=sym (fun i j => B (Yau.realVec i) (Yau.realVec j)) := by
  simp [autoPeanoHessianPerturbation]

theorem autoPeanoHessianPerturbation_continuous {n : ℕ}
    (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) : Continuous (autoPeanoHessianPerturbation B) := by
  have hc : Continuous (fun eta : ℝ => (fun i j : Yau.RIdx n =>
      B (Yau.realVec i) (Yau.realVec j)+(2*eta)*inner ℝ (Yau.realVec i) (Yau.realVec j))) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fun_prop
  exact (continuous_selfAdjointPart ℝ (Mat n)).comp hc

theorem autoPeanoSpatialPolynomial_hessian {n : ℕ} (c : ℝ) (x : Space n)
    (l : Space n →L[ℝ] ℝ) (B : Space n →L[ℝ] Space n →L[ℝ] ℝ)
    (hB : ∀ v w, B v w=B w v) (eta : ℝ) (p : Point n) :
    hessian (fun q : Point n => autoPeanoSpatialPolynomial c x l B eta q.1) p=
      autoPeanoHessianPerturbation B eta := by
  let lf := l.comp (ContinuousLinearMap.fst ℝ (Space n) ℝ)
  let bf := B.bilinearComp (ContinuousLinearMap.fst ℝ (Space n) ℝ)
    (ContinuousLinearMap.fst ℝ (Space n) ℝ)
  have hbf (v w : Point n) : bf v w=bf w v := hB v.1 w.1
  have he : (fun q : Point n => autoPeanoSpatialPolynomial c x l B eta q.1)=
      fun q => peanoPolynomial c (x,0) lf bf eta q+(-eta*q.2^2) := by
    funext q
    simp only [autoPeanoSpatialPolynomial,peanoPolynomial,lf,bf,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearMap.coe_fst',Prod.fst_sub,Prod.snd_sub,sub_zero,qnorm2]
    ring
  rw [he,auto_hessian_add_time (peanoPolynomial c (x,0) lf bf eta) (fun t : ℝ => -eta*t^2) p,
    peanoPolynomial_hessian c (x,0) lf bf hbf eta p]
  congr 1

theorem auto_peano_spatial_upper_test {n : ℕ} {u : Point n → ℝ} {p : Point n}
    {l : Space n →L[ℝ] ℝ} {B : Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hRem : (fun y : Space n => u (y,p.2)-u p-l (y-p.1)-
      (1/2 : ℝ)*B (y-p.1) (y-p.1))=o[𝓝 p.1](fun y => ‖y-p.1‖^2))
    {eta : ℝ} (heta : 0<eta) :
    autoPeanoSpatialPolynomial (u p) p.1 l B eta p.1=u p ∧
      ∀ᶠ y in 𝓝 p.1, u (y,p.2)≤autoPeanoSpatialPolynomial (u p) p.1 l B eta y := by
  refine ⟨by simp [autoPeanoSpatialPolynomial],?_⟩
  filter_upwards [hRem.bound heta] with y hy
  have hab := (le_abs_self (u (y,p.2)-u p-l (y-p.1)-(1/2 : ℝ)*B (y-p.1) (y-p.1))).trans hy
  simp only [Real.norm_eq_abs,abs_pow,abs_norm] at hab
  dsimp only [autoPeanoSpatialPolynomial]
  linarith only [hab]

theorem auto_peano_spatial_lower_test {n : ℕ} {u : Point n → ℝ} {p : Point n}
    {l : Space n →L[ℝ] ℝ} {B : Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (hRem : (fun y : Space n => u (y,p.2)-u p-l (y-p.1)-
      (1/2 : ℝ)*B (y-p.1) (y-p.1))=o[𝓝 p.1](fun y => ‖y-p.1‖^2))
    {eta : ℝ} (heta : 0<eta) :
    autoPeanoSpatialPolynomial (u p) p.1 l B (-eta) p.1=u p ∧
      ∀ᶠ y in 𝓝 p.1, autoPeanoSpatialPolynomial (u p) p.1 l B (-eta) y≤u (y,p.2) := by
  refine ⟨by simp [autoPeanoSpatialPolynomial],?_⟩
  filter_upwards [hRem.bound heta] with y hy
  have hlo := neg_abs_le (u (y,p.2)-u p-l (y-p.1)-(1/2 : ℝ)*B (y-p.1) (y-p.1))
  simp only [Real.norm_eq_abs,abs_pow,abs_norm] at hy
  dsimp only [autoPeanoSpatialPolynomial]
  linarith only [hlo,hy]

end Yau.LeafProofs.L05AutonomousAux
