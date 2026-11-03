import Yau.LeafProofs.L05PerturbationPucciHolder
import Yau.LeafProofs.L05PerturbationActualEquation
import Yau.LeafProofs.L05JetCombinationMatrix

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_actual_variable_pucci {n : ℕ} {ell L a b : ℝ}
    (hell : 0 ≤ ell) (hL : ell ≤ L) {Phi : Sym n → Point n → ℝ}
    (hE : ∀ p∈backward 1, globalElliptic (fun H => Phi H p) ell L)
    {u f : Point n → ℝ} (hu : C2 (backward 1) u)
    (hEq : ∀ p∈backward 1, timeD (backward 1) u p-Phi (hessian u p) p=f p)
    (hPhi0 : ∀ p∈backward 1, |Phi 0 p| ≤ a) (hf : ∀ p∈backward 1, |f p| ≤ b) :
    viscositySub (unitOpen n) (fun H _ => pucciPlus ell L H) (fun _ => a+b) u ∧
      viscositySuper (unitOpen n) (fun H _ => harnackPucciMinus ell L H) (fun _ => -(a+b)) u := by
  have hO : IsOpen (unitOpen n) := isOpen_ball.prod isOpen_Ioo
  have hOB : unitOpen n ⊆ backward 1 := by
    intro p hp
    exact ⟨hp.1,by simpa only [one_pow] using hp.2.1,hp.2.2.le⟩
  have huO := c2_open_restrict hO hOB hu
  constructor
  · intro p hp phi hphi ht
    have hpB := hOB hp
    have hJets := parabolic_touchAbove_jets hO huO hp hphi ht
    have hMono := perron_globalElliptic_mono hell (hE p hpB) hJets.2
    have hPucci := jet_elliptic_difference_le_pucci hell hL (hE p hpB) (hessian phi p) 0
    simp only [sub_zero] at hPucci
    have hTime : timeD (backward 1) u p=timeD univ phi p :=
      (timeD_open_restrict hO hOB u hp).symm.trans hJets.1
    have hActual := hEq p hpB
    rw [hTime] at hActual
    have hPhiB := (abs_le.mp (hPhi0 p hpB)).2
    have hfB := (abs_le.mp (hf p hpB)).2
    change timeD univ phi p-pucciPlus ell L (hessian phi p) ≤ a+b
    nlinarith only [hActual,hMono,hPucci,hPhiB,hfB]
  · intro p hp phi hphi ht
    have hpB := hOB hp
    have hJets := parabolic_touchBelow_jets hO huO hp hphi ht
    have hMono := perron_globalElliptic_mono hell (hE p hpB) hJets.2
    have hPucci := jet_elliptic_difference_le_pucci hell hL (hE p hpB) 0 (hessian phi p)
    simp only [zero_sub] at hPucci
    have hTime : timeD (backward 1) u p=timeD univ phi p :=
      (timeD_open_restrict hO hOB u hp).symm.trans hJets.1
    have hActual := hEq p hpB
    rw [hTime] at hActual
    have hPhiB := (abs_le.mp (hPhi0 p hpB)).1
    have hfB := (abs_le.mp (hf p hpB)).1
    change -(a+b) ≤ timeD univ phi p-(-pucciPlus ell L (-hessian phi p))
    nlinarith only [hActual,hMono,hPucci,hPhiB,hfB]

theorem perturb_variable_equation_holder {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ kappa : ℝ, 0 < kappa ∧ kappa < 1 ∧ ∀ delta : ℝ, 0 ≤ delta → delta ≤ 1 →
      ∀ Phi : Sym n → Point n → ℝ,
      (∀ p∈backward 1, globalElliptic (fun H => Phi H p) ell L) → Phi 0 0=0 →
      (∀ H : Sym n, ∀ p∈backward 1, |Phi H p-Phi H 0| ≤ delta*(1+‖H‖)) →
      ∀ u f : Point n → ℝ, C2 (backward 1) u → (∀ p∈backward 1, |u p| ≤ 1) →
      (∀ p∈backward 1, |f p| ≤ delta) →
      (∀ p∈backward 1, timeD (backward 1) u p-Phi (hessian u p) p=f p) →
      HolderBound kappa (perturbClosed (0 : Space n) (1/2) 0) u 100 := by
  obtain ⟨kappa,hk0,hk1,hHolder⟩ := perturb_forced_pucci_holder hn hell hL
  refine ⟨kappa,hk0,hk1,?_⟩
  intro delta hd0 hd1 Phi hE hZero hCoeff u f hu hBound hf hEq
  have hPhi0 : ∀ p∈backward 1, |Phi 0 p| ≤ delta := by
    intro p hp
    simpa only [hZero,sub_zero,norm_zero,add_zero,mul_one] using hCoeff 0 p hp
  have hPucci := perturb_actual_variable_pucci hell.le hL hE hu hEq hPhi0 hf
  have hSub : viscositySub (unitOpen n) (fun H _ => pucciPlus ell L H) (fun _ => 2) u :=
    viscositySub_mono_source hPucci.1 (fun _ _ => by linarith)
  have hSuper : viscositySuper (unitOpen n) (fun H _ => harnackPucciMinus ell L H)
      (fun _ => -2) u := viscositySuper_mono_source hPucci.2 (fun _ _ => by linarith)
  exact hHolder u hu.1 hBound hSub hSuper

end Yau.LeafProofs.L05Aux
