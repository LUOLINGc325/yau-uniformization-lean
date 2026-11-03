import Yau.Proofs.G01ConnectionJ
import Yau.LeafProofs.L18
import Yau.Blueprint.NormalizationTargets

noncomputable section
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.G04Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem christoffel_double_J (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    jSign a * jSign b * christoffel h x z c (jIndex n a) (jIndex n b) =
      -christoffel h x z c a b := by
  have h₁ := G01Aux.christoffel_jIndex h hs hk x z hz (jIndex n a) b c
  have h₂ := G01Aux.christoffel_jIndex h hs hk x z hz b a (jIndex n c)
  rw [jIndex_involutive, christoffel_symm_lower h x z (jIndex n c) b (jIndex n a),
    christoffel_symm_lower h x z c b a] at h₂
  rcases a with ⟨ai, a⟩
  rcases b with ⟨bi, b⟩
  rcases c with ⟨ci, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [jIndex, jSign] at h₁ h₂ ⊢ <;> linarith

theorem christoffel_trace_zero (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget x) (c : RIdx n) :
    (∑ a, ∑ b, (realMetricFn h x z)⁻¹ a b * christoffel h x z c a b) = 0 := by
  let F := fun a b => (realMetricFn h x z)⁻¹ a b * christoffel h x z c a b
  have hj : (∑ a, ∑ b, F a b) = -(∑ a, ∑ b, F a b) := by
    calc
      (∑ a, ∑ b, F a b) = ∑ a, ∑ b, F (jIndex n a) (jIndex n b) :=
        (L18Aux.sum_jIndex_two F).symm
      _ = ∑ a, ∑ b, -F a b := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        dsimp only [F]
        have hinv : (realMetricFn h x z)⁻¹ (jIndex n a) (jIndex n b) =
            jSign a * jSign b * (realMetricFn h x z)⁻¹ a b :=
          L18Aux.realMetricFn_inverse_jIndex h x hz a b
        rw [hinv]
        calc
          _ = (realMetricFn h x z)⁻¹ a b *
              (jSign a * jSign b * christoffel h x z c (jIndex n a) (jIndex n b)) := by ring
          _ = _ := by rw [christoffel_double_J h hs hk x hz a b c]; ring
      _ = _ := by simp only [Finset.sum_neg_distrib]
  dsimp only [F] at hj
  linarith

theorem scalarLaplacian (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) : PaperScalarLaplacianNormalization h := by
  intro f hf x z hz
  have hfc : ContDiffAt ℝ 2 (inChart x f) z :=
    ((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have hp : (∑ a, ∑ b, (realMetricFn h x z)⁻¹ a b *
      rDeriv (fun w => rDeriv (inChart x f) w b) z a) =
      2 * laplacian h f (chartInv x z) := by
    simp only [L18Aux.rDeriv_rDeriv_eq_hessian hfc]
    rw [L18Aux.principal_realLaplacian_eq_twice_traceWith h x hz hfc,
      L18Aux.traceWith_inChart_eq_laplacian h hf x hz]
  have hc : (∑ a, ∑ b, (realMetricFn h x z)⁻¹ a b *
      (∑ c, christoffel h x z c a b * rDeriv (inChart x f) z c)) = 0 := by
    simp only [Finset.mul_sum]
    rw [L18Aux.sum_three_cycle]
    calc
      _ = ∑ c, (∑ a, ∑ b, (realMetricFn h x z)⁻¹ a b * christoffel h x z c a b) *
          rDeriv (inChart x f) z c := by
        apply Finset.sum_congr rfl
        intro c _
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = 0 := by simp only [christoffel_trace_zero h hs hk x hz, zero_mul, Finset.sum_const_zero]
  unfold realLaplacianInChart
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hp, hc, sub_zero]

theorem scalarHodge_eq_neg_realLaplacian (h : HermitianField M) (f : M.Carrier → ℝ)
    (x : M.Carrier) (z : ComplexVector n) :
    hodgeComponents h x 0 (fun w (_ : Fin 0 → RIdx n) => inChart x f w) z Fin.elim0 =
      -realLaplacianInChart h x f z := by
  have hd : exteriorComponents (fun w (_ : Fin 0 → RIdx n) => inChart x f w) =
      fun z I => rDeriv (inChart x f) z (I 0) := by
    funext z I
    simp [exteriorComponents, Fin.sum_univ_succ]
  rw [hodgeComponents, hd]
  simp [codifferentialComponents, covariantComponents, Fin.sum_univ_succ,
    realLaplacianInChart]

theorem scalarHodgeNormalization (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) :
    ∀ f : M.Carrier → ℝ, SmoothFn f → ∀ x z, z ∈ chartTarget x →
      hodgeGeneratorComponents h x (fun w (_ : Fin 0 → RIdx n) => inChart x f w)
        z Fin.elim0 = laplacian h f (chartInv x z) := by
  intro f hf x z hz
  unfold hodgeGeneratorComponents
  rw [scalarHodge_eq_neg_realLaplacian, scalarLaplacian h hs hk f hf x z hz]
  ring

end Yau.NodeProofs.G04Aux
