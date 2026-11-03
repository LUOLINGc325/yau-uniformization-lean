import Yau.LeafProofs.L05PerturbationQuantitativeBarriers

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_lateral_unit_residual {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) {F : Sym n → ℝ} (hE : globalElliptic F ell L) (h0 : F 0=0)
    {p : Point n} (hp : p∈unitClosed n) (c A : ℝ) (hA : 0 ≤ A)
    {q : Point n} (hq : q∈unitClosed n) :
    let K := perturbLateralCoefficient n ell
    (4*A ≤ timeD univ (perronSeparatedPolynomial c p (A • ((-(1+2*K)) • p.1)) 0 (A*(-K)) A) q-
      F (hessian (perronSeparatedPolynomial c p (A • ((-(1+2*K)) • p.1)) 0 (A*(-K)) A) q)) ∧
    (timeD univ (perronSeparatedPolynomial c p ((-A) • ((-(1+2*K)) • p.1)) 0 ((-A)*(-K)) (-A)) q-
      F (hessian (perronSeparatedPolynomial c p ((-A) • ((-(1+2*K)) • p.1)) 0 ((-A)*(-K)) (-A)) q) ≤ -4*A) := by
  intro K
  have hd : 0 < (Fintype.card (Yau.RIdx n) : ℝ) := by
    simp only [Yau.RIdx,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    positivity
  have hK : 0 < K := perturb_lateral_coefficient_pos hn hell
  have hKeq : K*(Fintype.card (Yau.RIdx n) : ℝ)*ell=3 := by
    dsimp only [K,perturbLateralCoefficient]
    field_simp [hd.ne',hell.ne']
  have hh := perron_scalar_ellipticity hE h0 (show 0 ≤ 2*A*K by positivity)
  have hLow : -1 ≤ q.2-p.2 := by linarith [hq.2.1,hp.2.2]
  have hHi : q.2-p.2 ≤ 1 := by linarith [hq.2.2,hp.2.1]
  have htl := mul_le_mul_of_nonneg_left hLow (show 0 ≤ 2*A by positivity)
  have htu := mul_le_mul_of_nonneg_left hHi (show 0 ≤ 2*A by positivity)
  rw [perronSeparatedPolynomial_timeD,perronSeparatedPolynomial_hessian,
    perronSeparatedPolynomial_timeD,perronSeparatedPolynomial_hessian]
  have hMinus : (2*(A*(-K))) • sym (1 : Mat n)= -((2*A*K) • sym (1 : Mat n)) := by module
  have hPlus : (2*((-A)*(-K))) • sym (1 : Mat n)=(2*A*K) • sym (1 : Mat n) := by module
  rw [hMinus,hPlus]
  have hIdentity := congrArg (fun t : ℝ => 2*A*t) hKeq
  constructor <;> nlinarith [hh.1.1,hh.2.2]

theorem perturb_initial_boundary_barrier {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {F : Sym n → ℝ} (hF : Continuous F)
    (hE : globalElliptic F ell L) (h0 : F 0=0) {kappa H0 : ℝ}
    (hk0 : 0 < kappa) (hk1 : kappa < 1) {g h : Point n → ℝ}
    (hG : HolderBound kappa (unitClosed n) g H0) (hC : ContinuousOn h (unitClosed n))
    (hEq : EqOn h g (parabolicBoundary n))
    (hSol : viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) h)
    {p : Point n} (hp : p∈unitClosed n) (hpt : p.2=(-1 : ℝ)) :
    ∀ q∈unitClosed n, |h q-g p| ≤ 2*(H0*(2+2*perturbShapeMax n ell L))*
      (perronInitialShape p (perturbInitialSpeed n L) q)^(kappa/4) := by
  have hLp : 0 ≤ L := hell.le.trans hL
  have hpB : p∈parabolicBoundary n := Or.inl ⟨hp.1,mem_singleton_iff.mpr hpt⟩
  change ∀ q∈unitClosed n, |h q-g p| ≤ 2*(H0*(2+2*perturbShapeMax n ell L))*
    (perronSeparatedPolynomial 0 p 0 (perturbInitialSpeed n L) 1 0 q)^(kappa/4)
  apply perturb_quantitative_barrier_of_shape hn hell hL hF hE hk0 hk1
    (perturb_shapeMax_ge_one n ell hLp) hG hC hEq hSol p hpB 0 (perturbInitialSpeed n L) 1 0
  · intro q hq
    exact perturb_initial_shape_bounds hLp hp hpt hq
  · intro c A hA q _
    simpa only [perturbInitialSpeed,smul_zero,mul_one,mul_zero] using
      perron_initial_residual hE h0 p c A hA q

theorem perturb_lateral_boundary_barrier {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {F : Sym n → ℝ} (hF : Continuous F)
    (hE : globalElliptic F ell L) (h0 : F 0=0) {kappa H0 : ℝ}
    (hk0 : 0 < kappa) (hk1 : kappa < 1) {g h : Point n → ℝ}
    (hG : HolderBound kappa (unitClosed n) g H0) (hC : ContinuousOn h (unitClosed n))
    (hEq : EqOn h g (parabolicBoundary n))
    (hSol : viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) h)
    {p : Point n} (hp : p∈unitClosed n) (hpn : ‖p.1‖=1) :
    ∀ q∈unitClosed n, |h q-g p| ≤ 2*(H0*(2+2*perturbShapeMax n ell L))*
      (perronLateralShape p (perturbLateralCoefficient n ell) q)^(kappa/4) := by
  have hLp : 0 ≤ L := hell.le.trans hL
  have hK : 0 ≤ perturbLateralCoefficient n ell := (perturb_lateral_coefficient_pos hn hell).le
  have hpB : p∈parabolicBoundary n :=
    Or.inr ⟨by simpa only [mem_sphere,dist_zero_right] using hpn,hp.2⟩
  change ∀ q∈unitClosed n, |h q-g p| ≤ 2*(H0*(2+2*perturbShapeMax n ell L))*
    (perronSeparatedPolynomial 0 p ((-(1+2*perturbLateralCoefficient n ell)) • p.1)
      0 (-perturbLateralCoefficient n ell) 1 q)^(kappa/4)
  apply perturb_quantitative_barrier_of_shape hn hell hL hF hE hk0 hk1
    (perturb_shapeMax_ge_one n ell hLp) hG hC hEq hSol p hpB
    ((-(1+2*perturbLateralCoefficient n ell)) • p.1) 0 (-perturbLateralCoefficient n ell) 1
  · intro q hq
    exact perturb_lateral_shape_bounds hK hp hpn hq
  · intro c A hA q hq
    have hqC : q∈unitClosed n := ⟨ball_subset_closedBall hq.1,hq.2.1.le,hq.2.2.le⟩
    have hr := perturb_lateral_unit_residual hn hell hE h0 hp c A hA hqC
    simp only [mul_zero,mul_one]
    constructor <;> linarith [hr.1,hr.2]

end Yau.LeafProofs.L05Aux
