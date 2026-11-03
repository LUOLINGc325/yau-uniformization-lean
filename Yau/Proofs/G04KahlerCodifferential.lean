import Yau.Proofs.G04TraceDerivative
import Yau.Proofs.G04KahlerContraction

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G04Aux
open Yau Yau.LeafProofs L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem closed_oneOne_codifferential (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A) (hc : ClosedRealForm A)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (c : RIdx n) :
    codifferentialComponents h x (formComponents A x) z (fun _ : Fin 1 => c) =
      jSign c * rDeriv (inChart x (formTrace h A)) z (jIndex n c) := by
  have hGJ (a b : RIdx n) : (realMetricFn h x z)⁻¹ (jIndex n a) (jIndex n b) =
      jSign a * jSign b * (realMetricFn h x z)⁻¹ a b := L18Aux.realMetricFn_inverse_jIndex h x hz a b
  have hp := kahler_three_contraction (realMetricFn h x z)⁻¹
    (realMetricFn_isSymm h x z).inv hGJ (covariantTwo h A x z)
    (covariantTwo_skew h A hA x hz) (covariantTwo_J h hs hk A hA h11 x hz)
    (covariantTwo_cyclic h A hc x hz) c
  have ht := trace_covariant_derivative h hs hk A hA h11 x hz (jIndex n c)
  have hcalc : codifferentialComponents h x (formComponents A x) z (fun _ : Fin 1 => c) =
      -(∑ a, ∑ b, (realMetricFn h x z)⁻¹ a b * covariantTwo h A x z a b c) := by
    unfold codifferentialComponents
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    have hI : Fin.cons b (fun _ : Fin 1 => c) = ![b,c] := by
      funext r
      fin_cases r <;> rfl
    rw [hI]
    rfl
  rw [hcalc, hp, ← ht]

theorem codifferential_closed_oneOne_eq (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (A : RealForm M 2) (hA : SmoothRealForm A) (h11 : RealOneOne A) (hc : ClosedRealForm A) :
    L03.codifferentialRealForm h A = jDifferential (formTrace h A) := by
  have hτ := trace_smooth h hs A hA h11
  apply L03.realForm_eq_of_center_components
  intro x I
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  rw [codifferential_represents h hs A hA x (chartPt x x) hz I,
    jDifferential_components (formTrace h A) hτ x hz I]
  have hI : I = fun _ : Fin 1 => I 0 := by
    funext r
    exact congrArg I (Fin.eq_zero r)
  rw [hI]
  exact closed_oneOne_codifferential h hs hk A hA h11 hc x hz (I 0)

end Yau.NodeProofs.G04Aux
