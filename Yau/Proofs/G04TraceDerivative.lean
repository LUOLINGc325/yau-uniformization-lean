import Yau.Proofs.G04CovariantTwoForm
import Yau.Proofs.G04FormCodifferential
import Yau.LeafProofs.L23CovariantTrace

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter
namespace Yau.NodeProofs.G04Aux
open Yau Yau.LeafProofs L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

def matrixTensor (K : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ) : ComplexVector n → CovTensor n 2 :=
  fun z I => K z (I 0) (I 1)

def matrixJRight (K : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ) :
    ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ :=
  fun z a b => jSign b * K z a (jIndex n b)

theorem covariantD_matrixTensor (h : HermitianField M) (x : M.Carrier)
    (K : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ) (z : ComplexVector n) (a b c : RIdx n) :
    covariantD h x (matrixTensor K) z (Fin.cons a ![b,c]) =
      rDeriv (fun w => K w b c) z a - (∑ p, christoffel h x z p a b * K z p c) -
        (∑ p, christoffel h x z p a c * K z b p) := by
  have hu₀ (p : RIdx n) : Function.update ![b,c] (0 : Fin 2) p = ![p,c] := by
    funext i
    fin_cases i <;> simp
  have hu₁ (p : RIdx n) : Function.update ![b,c] (1 : Fin 2) p = ![b,p] := by
    funext i
    fin_cases i <;> simp
  simp only [covariantD, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, hu₀, hu₁, matrixTensor]
  ring

theorem covariantD_chartFormMatrix (h : HermitianField M) (A : RealForm M 2)
    (x : M.Carrier) (z : ComplexVector n) (a b c : RIdx n) :
    covariantD h x (matrixTensor (chartFormMatrix A x)) z (Fin.cons a ![b,c]) =
      covariantTwo h A x z a b c := by
  have he : matrixTensor (chartFormMatrix A x) = formComponents A x := by
    funext w I
    exact (formComponents_degree_two A x w I).symm
  rw [he, covariantD_form_cons]
  rfl

theorem connection_Jright_contraction (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (K : Matrix (RIdx n) (RIdx n) ℝ) (a b c : RIdx n) :
    (∑ p, christoffel h x z p a c * jSign p * K b (jIndex n p)) =
      jSign c * ∑ p, christoffel h x z p a (jIndex n c) * K b p := by
  rw [← (jIndex n).sum_comp (fun p => christoffel h x z p a c * jSign p * K b (jIndex n p)),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [jIndex_involutive]
  have he := G01Aux.christoffel_jIndex h hs hk x z hz a c p
  calc
    _ = (jSign (jIndex n p) * christoffel h x z (jIndex n p) a c) * K b p := by ring
    _ = _ := by rw [← he]; ring

theorem covariantD_Jright (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    covariantD h x (matrixTensor (matrixJRight (chartFormMatrix A x))) z (Fin.cons a ![b,c]) =
      jSign c * covariantTwo h A x z a b (jIndex n c) := by
  have hd : DifferentiableAt ℝ (fun w => chartFormMatrix A x w b (jIndex n c)) z :=
    ((hA x ![b,jIndex n c]).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  rw [covariantD_matrixTensor, covariantTwo_formula]
  simp only [matrixJRight]
  rw [rDeriv_const_mul hd]
  have hsum₁ : (∑ p, christoffel h x z p a b * (jSign c * chartFormMatrix A x z p (jIndex n c))) =
      jSign c * ∑ p, christoffel h x z p a b * chartFormMatrix A x z p (jIndex n c) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hsum₂ := connection_Jright_contraction h hs hk x hz (chartFormMatrix A x z) a b c
  rw [hsum₁]
  simp only [mul_assoc] at hsum₂
  rw [hsum₂]
  ring

theorem trace_covariant_derivative (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (i : RIdx n) :
    rDeriv (inChart x (formTrace h A)) z i = (1 / 2 : ℝ) * ∑ a, ∑ b,
      (realMetricFn h x z)⁻¹ a b * jSign b * covariantTwo h A x z i a (jIndex n b) := by
  let K := chartFormMatrix A x
  let B := matrixTensor (matrixJRight K)
  let tr : ComplexVector n → ℝ := fun w => L23Aux.tensorMetricTrace (realMetricFn h x w)⁻¹ (B w) Fin.elim0
  have hB (I : Fin 2 → RIdx n) : ContDiffOn ℝ ∞ (fun w => B w I) (chartTarget x) :=
    contDiffOn_const.mul (hA x ![I 0,jIndex n (I 1)])
  have htr : ContDiffOn ℝ ∞ tr (chartTarget x) := by
    apply ContDiffOn.sum
    intro a _
    apply ContDiffOn.sum
    intro b _
    exact (L23Aux.realMetricFn_inverse_contDiffOn h hs x a b).mul (hB (Fin.cons a (Fin.cons b Fin.elim0)))
  have heq : inChart x (formTrace h A) =ᶠ[𝓝 z] (fun w => (1 / 2 : ℝ) * tr w) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    change inChart x (formTrace h A) w = (1 / 2 : ℝ) * ∑ a, ∑ b,
      (realMetricFn h x w)⁻¹ a b * (jSign b * chartFormMatrix A x w a (jIndex n b))
    rw [trace_in_chart h A h11 x hw]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hd := L23Aux.covariantD_tensorMetricTrace h hs x B hz
    (fun I => ((hB I).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)) i Fin.elim0
  have hds : rDeriv tr z i = ∑ a, ∑ b, (realMetricFn h x z)⁻¹ a b *
      (jSign b * covariantTwo h A x z i a (jIndex n b)) := by
    have hleft : covariantD h x
        (fun w => L23Aux.tensorMetricTrace (realMetricFn h x w)⁻¹ (B w)) z (Fin.cons i Fin.elim0) =
        rDeriv tr z i := by
      simp [covariantD, tr]
    rw [hleft] at hd
    have hright (a b : RIdx n) : covariantD h x B z (Fin.cons i (Fin.cons a (Fin.cons b Fin.elim0))) =
        jSign b * covariantTwo h A x z i a (jIndex n b) := by
      exact covariantD_Jright h hs hk A hA x hz i a b
    simp_rw [hright] at hd
    exact hd
  calc
    rDeriv (inChart x (formTrace h A)) z i = rDeriv (fun w => (1 / 2 : ℝ) * tr w) z i :=
      congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec i)) heq.fderiv_eq
    _ = (1 / 2 : ℝ) * rDeriv tr z i := rDeriv_const_mul
      ((htr.contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)) _ _
    _ = _ := by rw [hds]; congr 1; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring

end Yau.NodeProofs.G04Aux
