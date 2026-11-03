import Yau.Proofs.G04TraceChart
import Yau.Proofs.G04LeviForms
import Yau.Proofs.G01ConnectionJ

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G04Aux
open Yau Yau.LeafProofs L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

def covariantTwo (h : HermitianField M) (A : RealForm M 2) (x : M.Carrier)
    (z : ComplexVector n) (a b c : RIdx n) : ℝ :=
  covariantComponents h x (formComponents A x) z a ![b,c]

theorem covariantTwo_formula (h : HermitianField M) (A : RealForm M 2) (x : M.Carrier)
    (z : ComplexVector n) (a b c : RIdx n) :
    covariantTwo h A x z a b c = rDeriv (fun w => chartFormMatrix A x w b c) z a -
      (∑ p, christoffel h x z p a b * chartFormMatrix A x z p c) -
      (∑ p, christoffel h x z p a c * chartFormMatrix A x z b p) := by
  have hu₀ (p : RIdx n) : Function.update ![b,c] (0 : Fin 2) p = ![p,c] := by
    funext i
    fin_cases i <;> simp
  have hu₁ (p : RIdx n) : Function.update ![b,c] (1 : Fin 2) p = ![b,p] := by
    funext i
    fin_cases i <;> simp
  unfold covariantTwo covariantComponents
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hu₀, hu₁]
  change rDeriv (fun w => chartFormMatrix A x w b c) z a -
    ((∑ p, christoffel h x z p a b * chartFormMatrix A x z p c) +
      (∑ p, christoffel h x z p a c * chartFormMatrix A x z b p)) = _
  ring

theorem chartForm_apply_two (A : RealForm M 2) (x : M.Carrier) (z u v : ComplexVector n) :
    L03.chartForm A x z ![u,v] = A (chartInv x z) ![chartVec x (chartInv x z) u, chartVec x (chartInv x z) v] := by
  simp only [L03.chartForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, L03.chartRealContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem chartForm_oneOne (A : RealForm M 2) (hA : RealOneOne A) (x : M.Carrier)
    (z u v : ComplexVector n) :
    L03.chartForm A x z ![Complex.I • u, Complex.I • v] = L03.chartForm A x z ![u,v] := by
  rw [chartForm_apply_two, chartForm_apply_two, chartVec_complex_smul, chartVec_complex_smul]
  exact hA _ _ _

theorem chartFormMatrix_J (A : RealForm M 2) (hA : RealOneOne A) (x : M.Carrier)
    (z : ComplexVector n) (a b : RIdx n) :
    chartFormMatrix A x z (jIndex n a) (jIndex n b) =
      jSign a * jSign b * chartFormMatrix A x z a b := by
  have ha : realVec (jIndex n a) = jSign a • (Complex.I • realVec a) := L18Aux.realVec_jIndex a
  have hb : realVec (jIndex n b) = jSign b • (Complex.I • realVec b) := L18Aux.realVec_jIndex b
  rw [chartFormMatrix_apply, chartFormMatrix_apply, ← alternatingBilin_apply, ← alternatingBilin_apply, ha, hb]
  simp only [map_smul, smul_apply, smul_eq_mul, alternatingBilin_apply]
  rw [chartForm_oneOne A hA]
  ring

theorem christoffel_Jboth (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (a b p : RIdx n) :
    christoffel h x z (jIndex n p) a (jIndex n b) =
      jSign b * jSign p * christoffel h x z p a b := by
  have he := G01Aux.christoffel_jIndex h hs hk x z hz a b (jIndex n p)
  rw [jIndex_involutive] at he
  calc
    _ = jSign b * (jSign b * christoffel h x z (jIndex n p) a (jIndex n b)) := by
      rw [← mul_assoc, jSign_sq, one_mul]
    _ = _ := by rw [he]; ring

theorem covariantTwo_skew (h : HermitianField M) (A : RealForm M 2) (hA : SmoothRealForm A)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    covariantTwo h A x z a c b = -covariantTwo h A x z a b c := by
  have hcoef (p q : RIdx n) :
      L03.covariantChartForm h A x z a ![realVec p, realVec q] = covariantTwo h A x z a p q := by
    unfold covariantTwo
    rw [← L03.covariantChartForm_coeff h A hA x hz a ![p,q]]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [← hcoef, ← hcoef]
  exact alternating_two_swap _ _ _

theorem covariantTwo_J (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    covariantTwo h A x z a (jIndex n b) (jIndex n c) =
      jSign b * jSign c * covariantTwo h A x z a b c := by
  have hfun : (fun w => chartFormMatrix A x w (jIndex n b) (jIndex n c)) =
      (fun w => (jSign b * jSign c) * chartFormMatrix A x w b c) :=
    funext (fun w => chartFormMatrix_J A h11 x w b c)
  have hdiff : DifferentiableAt ℝ (fun w => chartFormMatrix A x w b c) z :=
    ((hA x ![b,c]).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hsum₁ : (∑ p, christoffel h x z p a (jIndex n b) * chartFormMatrix A x z p (jIndex n c)) =
      (jSign b * jSign c) * ∑ p, christoffel h x z p a b * chartFormMatrix A x z p c := by
    rw [← (jIndex n).sum_comp (fun p => christoffel h x z p a (jIndex n b) *
      chartFormMatrix A x z p (jIndex n c)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [christoffel_Jboth h hs hk x hz, chartFormMatrix_J A h11]
    calc
      _ = (jSign p * jSign p) * ((jSign b * jSign c) *
          (christoffel h x z p a b * chartFormMatrix A x z p c)) := by ring
      _ = _ := by rw [jSign_sq, one_mul]
  have hsum₂ : (∑ p, christoffel h x z p a (jIndex n c) * chartFormMatrix A x z (jIndex n b) p) =
      (jSign b * jSign c) * ∑ p, christoffel h x z p a c * chartFormMatrix A x z b p := by
    rw [← (jIndex n).sum_comp (fun p => christoffel h x z p a (jIndex n c) *
      chartFormMatrix A x z (jIndex n b) p), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [christoffel_Jboth h hs hk x hz, chartFormMatrix_J A h11]
    calc
      _ = (jSign p * jSign p) * ((jSign b * jSign c) *
          (christoffel h x z p a c * chartFormMatrix A x z b p)) := by ring
      _ = _ := by rw [jSign_sq, one_mul]
  rw [covariantTwo_formula, covariantTwo_formula, hfun, rDeriv_const_mul hdiff,
    hsum₁, hsum₂]
  ring

theorem covariantTwo_cyclic (h : HermitianField M) (A : RealForm M 2) (hclosed : ClosedRealForm A)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    covariantTwo h A x z a b c + covariantTwo h A x z b c a + covariantTwo h A x z c a b = 0 := by
  have hd := hclosed x z hz ![a,b,c]
  simp [exteriorComponents, Fin.sum_univ_succ, Fin.succAbove, formComponents_degree_two] at hd
  have heq : (fun w => chartFormMatrix A x w c a) = (fun w => -chartFormMatrix A x w a c) :=
    funext (fun w => chartFormMatrix_skew A x w a c)
  have hdca : rDeriv (fun w => chartFormMatrix A x w c a) z b =
      -rDeriv (fun w => chartFormMatrix A x w a c) z b := by
    rw [heq]
    simp only [rDeriv, fderiv_fun_neg, neg_apply]
  have hcancel : (∑ p, christoffel h x z p a b * chartFormMatrix A x z p c) +
      (∑ p, christoffel h x z p a c * chartFormMatrix A x z b p) +
      (∑ p, christoffel h x z p b c * chartFormMatrix A x z p a) +
      (∑ p, christoffel h x z p b a * chartFormMatrix A x z c p) +
      (∑ p, christoffel h x z p c a * chartFormMatrix A x z p b) +
      (∑ p, christoffel h x z p c b * chartFormMatrix A x z a p) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro p _
    rw [christoffel_symm_lower h x z p b a, christoffel_symm_lower h x z p c a,
      christoffel_symm_lower h x z p c b, chartFormMatrix_skew A x z p c,
      chartFormMatrix_skew A x z b p, chartFormMatrix_skew A x z p a]
    ring
  rw [covariantTwo_formula, covariantTwo_formula, covariantTwo_formula, hdca]
  linarith

end Yau.NodeProofs.G04Aux
