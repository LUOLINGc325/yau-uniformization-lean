import Yau.LeafProofs.L05PerturbationBarrierShapes
import Yau.LeafProofs.L05PerturbationFrozenHalf
import Yau.LeafProofs.L05PerronComparison

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_quantitative_barrier_of_shape {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {F : Sym n → ℝ} (hF : Continuous F)
    (hE : globalElliptic F ell L) {kappa H0 Smax : ℝ} (hk0 : 0 < kappa)
    (hk1 : kappa < 1) (hMax : 1 ≤ Smax) {g h : Point n → ℝ}
    (hG : HolderBound kappa (unitClosed n) g H0) (hC : ContinuousOn h (unitClosed n))
    (hEq : EqOn h g (parabolicBoundary n))
    (hSol : viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) h)
    (p : Point n) (hp : p∈parabolicBoundary n) (v : Space n) (a k d : ℝ)
    (hShape : ∀ q∈unitClosed n,
      let S := perronSeparatedPolynomial 0 p v a k d q
      0 ≤ S ∧ S ≤ Smax ∧ ‖q.1-p.1‖^2 ≤ 2*S ∧ |q.2-p.2|^2 ≤ S)
    (hRes : ∀ c A : ℝ, 0 ≤ A → ∀ q∈unitOpen n,
      (2*A ≤ timeD univ (perronSeparatedPolynomial c p (A • v) (A*a) (A*k) (A*d)) q-
        F (hessian (perronSeparatedPolynomial c p (A • v) (A*a) (A*k) (A*d)) q)) ∧
      (timeD univ (perronSeparatedPolynomial c p ((-A) • v) ((-A)*a) ((-A)*k) ((-A)*d)) q-
        F (hessian (perronSeparatedPolynomial c p ((-A) • v) ((-A)*a) ((-A)*k) ((-A)*d)) q) ≤ -2*A)) :
    ∀ q∈unitClosed n, |h q-g p| ≤
      2*(H0*(2+2*Smax))*(perronSeparatedPolynomial 0 p v a k d q)^(kappa/4) := by
  let S := perronSeparatedPolynomial 0 p v a k d
  let nu := kappa/4
  let Bbar := H0*(2+2*Smax)
  have hn0 : 0 < nu := by dsimp only [nu]; positivity
  have hn1 : nu < 1 := by dsimp only [nu]; linarith
  have hBbar : 0 ≤ Bbar := mul_nonneg hG.1 (by linarith)
  have hpC := harnack_boundary_subset_unitClosed hp
  intro q hq
  have hSq := hShape q hq
  change |h q-g p| ≤ 2*Bbar*(S q)^nu
  by_cases hSz : S q=0
  · have hx : ‖q.1-p.1‖=0 := by
      have hh := hSq.2.2.1
      change ‖q.1-p.1‖^2 ≤ 2*S q at hh
      rw [hSz,mul_zero] at hh
      nlinarith only [hh,norm_nonneg (q.1-p.1)]
    have ht : |q.2-p.2|=0 := by
      have hh := hSq.2.2.2
      change |q.2-p.2|^2 ≤ S q at hh
      rw [hSz] at hh
      nlinarith only [hh,abs_nonneg (q.2-p.2)]
    have hqp : q=p := Prod.ext (sub_eq_zero.mp (norm_eq_zero.mp hx))
      (sub_eq_zero.mp (abs_eq_zero.mp ht))
    subst q
    rw [hEq hp,sub_self,abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hBbar) (Real.rpow_nonneg hSq.1 nu)
  have hSp : 0 < S q := lt_of_le_of_ne hSq.1 (Ne.symm hSz)
  let eps := S q
  let A := Bbar*eps^(nu-1)
  have hA : 0 ≤ A := mul_nonneg hBbar (Real.rpow_nonneg hSp.le _)
  let low := perronSeparatedPolynomial (g p-Bbar*eps^nu) p ((-A) • v) ((-A)*a) ((-A)*k) ((-A)*d)
  let upper := perronSeparatedPolynomial (g p+Bbar*eps^nu) p (A • v) (A*a) (A*k) (A*d)
  have hl : ContDiff ℝ ∞ low := perronSeparatedPolynomial_smooth _ _ _ _ _ _
  have hu : ContDiff ℝ ∞ upper := perronSeparatedPolynomial_smooth _ _ _ _ _ _
  have hLow : viscositySub (unitOpen n) (fun H _ => F H) (fun _ => 0) low := by
    apply perron_classical_sub hell hE (fun _ _ => hl.contDiffAt.of_le (by simp))
    intro r hr
    exact ((hRes (g p-Bbar*eps^nu) A hA r hr).2).trans (by nlinarith only [hA])
  have hUpper : viscositySuper (unitOpen n) (fun H _ => F H) (fun _ => 0) upper := by
    apply perron_classical_super hell hE (fun _ _ => hu.contDiffAt.of_le (by simp))
    intro r hr
    exact (show 0 ≤ 2*A by positivity).trans ((hRes (g p+Bbar*eps^nu) A hA r hr).1)
  have hDom (r : Point n) (hr : r∈unitClosed n) : low r ≤ g r ∧ g r ≤ upper r := by
    have hSr := hShape r hr
    have hHolder := hG.2.2 r hr p hpC
    rw [Real.norm_eq_abs] at hHolder
    have hWeight := perturb_shape_weight hk0 hk1 hSr.1 hSr.2.1 hMax r p hSr.2.2.1 hSr.2.2.2
    have hPower := perturb_power_barrier hSr.1 hSp hn0 hn1
    have hDiff : |g r-g p| ≤ Bbar*(eps^nu+eps^(nu-1)*S r) := by
      calc
        _ ≤ H0*((2+2*Smax)*(S r)^nu) :=
          hHolder.trans (mul_le_mul_of_nonneg_left hWeight hG.1)
        _ = Bbar*(S r)^nu := by dsimp only [Bbar]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hPower hBbar
    have hLo := (abs_le.mp hDiff).1
    have hHi := (abs_le.mp hDiff).2
    dsimp only [low,upper]
    rw [perronSeparatedPolynomial_scale,perronSeparatedPolynomial_scale]
    change (g p-Bbar*eps^nu)+(-A)*S r ≤ g r ∧ g r ≤ (g p+Bbar*eps^nu)+A*S r
    dsimp only [A]
    constructor <;> nlinarith only [hLo,hHi]
  have hLC : ∀ r∈unitClosed n, low r ≤ h r := by
    have hh := perron_continuous_compare hn hell hL (R := 1) (a := -1) (b := 0) (c := 0)
      (by norm_num) (by norm_num) hF hE hl.continuous.continuousOn hC hLow hSol.2
      (fun r hr => by rw [hEq hr,add_zero]; exact (hDom r (harnack_boundary_subset_unitClosed hr)).1)
    simpa only [add_zero,unitClosed,Yau.Parabolic.cylinder,abpClosed] using hh
  have hUC : ∀ r∈unitClosed n, h r ≤ upper r := by
    have hh := perron_continuous_compare hn hell hL (R := 1) (a := -1) (b := 0) (c := 0)
      (by norm_num) (by norm_num) hF hE hC hu.continuous.continuousOn hSol.1 hUpper
      (fun r hr => by rw [hEq hr,add_zero]; exact (hDom r (harnack_boundary_subset_unitClosed hr)).2)
    simpa only [add_zero,unitClosed,Yau.Parabolic.cylinder,abpClosed] using hh
  have hLo := hLC q hq
  have hHi := hUC q hq
  dsimp only [low,upper] at hLo hHi
  rw [perronSeparatedPolynomial_scale] at hLo hHi
  have hAPow : A*S q=Bbar*(S q)^nu := by
    dsimp only [A,eps]
    rw [mul_assoc,← Real.rpow_add_one hSp.ne']
    congr 2
    ring
  change (g p-Bbar*(S q)^nu)+(-A)*S q ≤ h q at hLo
  change h q ≤ (g p+Bbar*(S q)^nu)+A*S q at hHi
  rw [hAPow] at hHi
  have hAMinus : (-A)*S q= -(Bbar*(S q)^nu) := by rw [neg_mul,hAPow]
  rw [hAMinus] at hLo
  exact abs_le.mpr ⟨by linarith only [hLo],by linarith only [hHi]⟩

end Yau.LeafProofs.L05Aux
