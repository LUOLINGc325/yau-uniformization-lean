import Yau.LeafProofs.L23FieldMetricConnection
import Yau.LeafProofs.L23Commutator

/-! Local metric compatibility and curvature algebra with MetricSmooth only. -/

noncomputable section
open Filter
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem inverseMetric_directional_derivative (h : HermitianField M) (hh : MetricSmooth h)
    (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a) (k : RIdx n) :
    L12Aux.matrixDirectionalDerivative (fun w => (realMetricFn h a w)⁻¹) z (realVec k) =
      -(L12Aux.connectionMatrix h a z k * (realMetricFn h a z)⁻¹ +
        (realMetricFn h a z)⁻¹ * (L12Aux.connectionMatrix h a z k)ᵀ) := by
  let G := realMetricFn h a z
  let C := L12Aux.connectionMatrix h a z k
  have hunit : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr (L12Aux.realMetricFn_posDef h a z hz).det_pos.ne'
  have hGA : G*G⁻¹=1 := Matrix.mul_nonsing_inv G hunit
  have hAG : G⁻¹*G=1 := Matrix.nonsing_inv_mul G hunit
  have hd := L12Aux.matrixDirectionalDerivative_inv
    (fun i j => ((hh a i j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz)).differentiableAt (by simp))
    (L12Aux.realMetricFn_posDef h a z hz).det_pos.ne' (realVec k)
  rw [metricDirectionalDerivative_eq_connection h hh a z hz k] at hd
  change L12Aux.matrixDirectionalDerivative (fun w => (realMetricFn h a w)⁻¹) z
      (realVec k) = -(C*G⁻¹+G⁻¹*Cᵀ)
  rw [hd]
  change -(G⁻¹*(Cᵀ*G+G*C)*G⁻¹) = _
  congr 1
  calc
    _ = G⁻¹*Cᵀ*(G*G⁻¹)+(G⁻¹*G)*C*G⁻¹ := by noncomm_ring
    _ = _ := by rw [hGA,hAG]; simp only [Matrix.mul_one,Matrix.one_mul]; abel

theorem inverseMetric_derivative_connection (h : HermitianField M) (hh : MetricSmooth h)
    (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a) (k i j : RIdx n) :
    rDeriv (fun w => (realMetricFn h a w)⁻¹ i j) z k =
      -(∑ p, christoffel h a z i k p*(realMetricFn h a z)⁻¹ p j) -
        ∑ p, christoffel h a z j k p*(realMetricFn h a z)⁻¹ i p := by
  have hd := congrArg (fun B : Matrix (RIdx n) (RIdx n) ℝ => B i j)
    (inverseMetric_directional_derivative h hh a hz k)
  simpa only [L12Aux.matrixDirectionalDerivative,rDeriv,Matrix.neg_apply,Matrix.add_apply,
    Matrix.mul_apply,Matrix.transpose_apply,L12Aux.connectionMatrix,
    neg_add_rev,neg_add,sub_eq_add_neg,mul_comm,add_comm] using hd

theorem curvatureMatrix_metric_skew (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    (L12Aux.curvatureMatrix h x z a b)ᵀ*realMetricFn h x z +
      realMetricFn h x z*L12Aux.curvatureMatrix h x z a b = 0 := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) x
  have hG (i j : RIdx n) : ContDiffAt ℝ 2 (fun w => realMetricFn h x w i j) z :=
    ((hh x i j).contDiffAt (hO.mem_nhds hz)).of_le (by simp)
  have hC (k i j : RIdx n) :
      DifferentiableAt ℝ (fun w => L12Aux.connectionMatrix h x w k i j) z :=
    ((christoffel_contDiffOn h hh x i k j).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have he (k : RIdx n) : ∀ᶠ w in 𝓝 z,
      L12Aux.matrixDirectionalDerivative (fun p => realMetricFn h x p) w (realVec k) =
        (L12Aux.connectionMatrix h x w k)ᵀ*realMetricFn h x w +
          realMetricFn h x w*L12Aux.connectionMatrix h x w k := by
    filter_upwards [hO.mem_nhds hz] with w hw
    exact metricDirectionalDerivative_eq_connection h hh x w hw k
  have hs := L12Aux.matrix_curvature_skew_of_metricCompatibility hG (hC a) (hC b)
    (realVec a) (realVec b) (he a) (he b)
  rw [L12Aux.curvatureMatrix_eq]
  exact hs

theorem curvature4_swap_last (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c d : RIdx n) :
    L12Aux.curvature4 h x z a b c d = -L12Aux.curvature4 h x z a b d c := by
  have hs := congrArg (fun A : Matrix (RIdx n) (RIdx n) ℝ => A c d)
    (curvatureMatrix_metric_skew h hh x z hz a b)
  simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,
    Matrix.zero_apply,L12Aux.curvatureMatrix] at hs
  have heq : (∑ l, realMetricFn h x z c l*riemannCoeff h x z a b d l) =
      L12Aux.curvature4 h x z a b d c := by
    unfold L12Aux.curvature4
    apply Finset.sum_congr rfl
    intro l _
    rw [L12Aux.realMetricFn_symm h x z c l]
  have hfirst : (∑ l, riemannCoeff h x z a b c l*realMetricFn h x z l d) =
      L12Aux.curvature4 h x z a b c d := by simp only [L12Aux.curvature4,mul_comm]
  rw [heq,hfirst] at hs
  linarith

theorem curvature4_pair_swap (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c d : RIdx n) :
    L12Aux.curvature4 h x z a b c d = L12Aux.curvature4 h x z c d a b :=
  L12Aux.algebraic_curvature_pair_swap (L12Aux.curvature4 h x z)
    (L12Aux.curvature4_swap_first h x z) (curvature4_swap_last h hh x z hz)
    (L12Aux.curvature4_firstBianchi h x z) a b c d

theorem curvatureMatrix_trace_zero (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    (L12Aux.curvatureMatrix h x z a b).trace=0 :=
  L12Aux.matrix_trace_zero_of_metric_skew (realMetricFn h x z)
    (L12Aux.curvatureMatrix h x z a b)
    (isUnit_iff_ne_zero.mpr (L12Aux.realMetricFn_posDef h x z hz).det_pos.ne')
    (curvatureMatrix_metric_skew h hh x z hz a b)

theorem realRicciMatrix_symm (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (b c : RIdx n) :
    L12Aux.realRicciMatrix h x z b c=L12Aux.realRicciMatrix h x z c b := by
  have hsum : L12Aux.realRicciMatrix h x z b c+
      (L12Aux.curvatureMatrix h x z b c).trace-L12Aux.realRicciMatrix h x z c b=0 := by
    simp only [L12Aux.realRicciMatrix,Matrix.trace,Matrix.diag_apply,L12Aux.curvatureMatrix]
    rw [←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro a _
    have hb := L12Aux.riemannCoeff_firstBianchi h x z a b c a
    rw [L12Aux.riemannCoeff_swap h x z c a b a] at hb
    linarith
  rw [curvatureMatrix_trace_zero h hh x z hz b c] at hsum
  linarith

/-- The second Bianchi cancellation is a matrix polynomial, with ordinary
second partial derivatives already commuted. -/
theorem matrix_secondBianchi_algebra {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (Γ : ι → Matrix κ κ ℝ) (dΓ : ι → ι → Matrix κ κ ℝ)
    (ddΓ : ι → ι → ι → Matrix κ κ ℝ)
    (hdd : ∀ a b c, ddΓ a b c=ddΓ b a c) (a b c : ι) :
    let R := fun i j => dΓ i j-dΓ j i+Γ i*Γ j-Γ j*Γ i
    let dR := fun d i j => ddΓ d i j-ddΓ d j i+
      dΓ d i*Γ j+Γ i*dΓ d j-dΓ d j*Γ i-Γ j*dΓ d i
    (dR a b c+Γ a*R b c-R b c*Γ a)+
      (dR b c a+Γ b*R c a-R c a*Γ b)+
      (dR c a b+Γ c*R a b-R a b*Γ c)=0 := by
  dsimp only
  rw [hdd b c a,hdd c a b,hdd c b a,hdd a b c]
  noncomm_ring

theorem rDeriv_add {f g : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : RIdx n) :
    rDeriv (fun w => f w+g w) z i = rDeriv f z i+rDeriv g z i := by
  unfold rDeriv
  rw [fderiv_fun_add hf hg]
  rfl

theorem connectionDerivativeMatrix_contDiffOn (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (a b i j : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => L12Aux.connectionDerivativeMatrix h c z a b i j)
      (chartTarget c) :=
  L12Aux.rDeriv_contDiffOn (isOpen_extChartAt_target (I := ComplexModel n) c)
    (christoffel_contDiffOn h hh c i b j) a

theorem curvatureMatrix_directionalDerivative (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a i j : RIdx n) :
    L12Aux.matrixDirectionalDerivative (fun w => L12Aux.curvatureMatrix h c w i j) z (realVec a) =
      L12Aux.matrixDirectionalDerivative (fun w => L12Aux.connectionDerivativeMatrix h c w i j) z (realVec a) -
        L12Aux.matrixDirectionalDerivative (fun w => L12Aux.connectionDerivativeMatrix h c w j i) z (realVec a) +
        L12Aux.connectionDerivativeMatrix h c z a i*L12Aux.connectionMatrix h c z j +
        L12Aux.connectionMatrix h c z i*L12Aux.connectionDerivativeMatrix h c z a j -
        L12Aux.connectionDerivativeMatrix h c z a j*L12Aux.connectionMatrix h c z i -
        L12Aux.connectionMatrix h c z j*L12Aux.connectionDerivativeMatrix h c z a i := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) c
  have hΓ (b k l : RIdx n) :
      DifferentiableAt ℝ (fun w => L12Aux.connectionMatrix h c w b k l) z :=
    ((christoffel_contDiffOn h hh c k b l).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  have hdΓ (b d k l : RIdx n) :=
    ((connectionDerivativeMatrix_contDiffOn h hh c b d k l).contDiffAt
      (hO.mem_nhds hz)).differentiableAt (by simp)
  have hprod (b d : RIdx n) := L12Aux.matrix_entries_differentiable_mul (hΓ b) (hΓ d)
  have hsub (k l : RIdx n) := (hdΓ i j k l).sub (hdΓ j i k l)
  have hsum (k l : RIdx n) := (hsub k l).add (hprod i j k l)
  simp_rw [L12Aux.curvatureMatrix_eq]
  rw [L12Aux.matrixDirectionalDerivative_sub
      (A := fun w => L12Aux.connectionDerivativeMatrix h c w i j-
        L12Aux.connectionDerivativeMatrix h c w j i+
        L12Aux.connectionMatrix h c w i*L12Aux.connectionMatrix h c w j)
      (B := fun w => L12Aux.connectionMatrix h c w j*L12Aux.connectionMatrix h c w i)
      hsum (hprod j i),
    L12Aux.matrixDirectionalDerivative_add
      (A := fun w => L12Aux.connectionDerivativeMatrix h c w i j-
        L12Aux.connectionDerivativeMatrix h c w j i)
      (B := fun w => L12Aux.connectionMatrix h c w i*L12Aux.connectionMatrix h c w j)
      hsub (hprod i j),
    L12Aux.matrixDirectionalDerivative_sub
      (A := fun w => L12Aux.connectionDerivativeMatrix h c w i j)
      (B := fun w => L12Aux.connectionDerivativeMatrix h c w j i) (hdΓ i j) (hdΓ j i),
    L12Aux.matrixDirectionalDerivative_mul (hΓ i) (hΓ j),
    L12Aux.matrixDirectionalDerivative_mul (hΓ j) (hΓ i)]
  change _ = _
  abel

theorem curvatureMatrix_secondBianchi (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (a b d : RIdx n) :
    (L12Aux.matrixDirectionalDerivative (fun w => L12Aux.curvatureMatrix h c w b d) z (realVec a) +
      L12Aux.connectionMatrix h c z a*L12Aux.curvatureMatrix h c z b d -
      L12Aux.curvatureMatrix h c z b d*L12Aux.connectionMatrix h c z a) +
    (L12Aux.matrixDirectionalDerivative (fun w => L12Aux.curvatureMatrix h c w d a) z (realVec b) +
      L12Aux.connectionMatrix h c z b*L12Aux.curvatureMatrix h c z d a -
      L12Aux.curvatureMatrix h c z d a*L12Aux.connectionMatrix h c z b) +
    (L12Aux.matrixDirectionalDerivative (fun w => L12Aux.curvatureMatrix h c w a b) z (realVec d) +
      L12Aux.connectionMatrix h c z d*L12Aux.curvatureMatrix h c z a b -
      L12Aux.curvatureMatrix h c z a b*L12Aux.connectionMatrix h c z d) = 0 := by
  let Γ := fun i => L12Aux.connectionMatrix h c z i
  let dΓ := fun i j => L12Aux.connectionDerivativeMatrix h c z i j
  let ddΓ := fun i j k => L12Aux.matrixDirectionalDerivative
    (fun w => L12Aux.connectionDerivativeMatrix h c w j k) z (realVec i)
  have hdd (i j k : RIdx n) : ddΓ i j k=ddΓ j i k := by
    ext l m
    have hΓ2 : ContDiffAt ℝ 2 (fun w => christoffel h c w l k m) z :=
      ((christoffel_contDiffOn h hh c l k m).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).of_le (by simp)
    change rDeriv (fun w => rDeriv (fun u => christoffel h c u l k m) w j) z i =
      rDeriv (fun w => rDeriv (fun u => christoffel h c u l k m) w i) z j
    rw [L18Aux.rDeriv_rDeriv_eq_hessian hΓ2,L18Aux.rDeriv_rDeriv_eq_hessian hΓ2]
    exact hΓ2.isSymmSndFDerivAt (by norm_num) (realVec i) (realVec j)
  have halg := matrix_secondBianchi_algebra Γ dΓ ddΓ hdd a b d
  dsimp only at halg
  dsimp only [Γ,dΓ,ddΓ] at halg
  rw [←curvatureMatrix_directionalDerivative h hh c hz a b d,
    ←curvatureMatrix_directionalDerivative h hh c hz b d a,
    ←curvatureMatrix_directionalDerivative h hh c hz d a b] at halg
  simpa only [←L12Aux.curvatureMatrix_eq] using halg

end Yau.LeafProofs.L23Aux
