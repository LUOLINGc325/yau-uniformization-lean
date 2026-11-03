import Yau.Proofs.C05IntrinsicInverseEnergyTime
import Yau.Proofs.C05NormalizedGradientSmall

/-! Uniform bounds on the genuine inverse and scalar source turn actual
scalar-gradient decay into actual inverse-energy time decay. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n} {ι : Type*}
set_option backward.isDefEq.respectTransparency false

theorem intrinsicInverseEnergyTime_tendsto_zero (k : ι → HermitianField M)
    (hk : ∀ i, MetricSmooth (k i)) (hK : ∀ i, KahlerClosed (k i)) (x : M.Carrier)
    (l : Filter ι) {CA CB CQ : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCQ : 0 ≤ CQ)
    (hC : ∀ᶠ i in l, metricTensorNorm (realMetricFn (k i) x (chartPt x x))
      (ricciInverseTensor (k i) x (chartPt x x)) ≤ CA)
    (hB : ∀ᶠ i in l, scalarJetNorm (k i) (scalarCurvature (k i)) 2 x ≤ CB)
    (hQ : ∀ᶠ i in l, scalarJetNorm (k i) (scalarHarnackSource (k i) 0) 1 x ≤ CQ)
    (hgrad : Tendsto (fun i => scalarJetNorm (k i) (scalarCurvature (k i)) 1 x) l (𝓝 0)) :
    Tendsto (fun i => intrinsicInverseEnergyTime (k i) x) l (𝓝 0) := by
  have hb : ∀ᶠ i in l, |intrinsicInverseEnergyTime (k i) x| ≤
      ((1/2:ℝ)*(2*n:ℕ)*CA^2*CB) * scalarJetNorm (k i) (scalarCurvature (k i)) 1 x ^ 2 +
      (CA*CQ)*scalarJetNorm (k i) (scalarCurvature (k i)) 1 x := by
    filter_upwards [hC,hB,hQ] with i hCi hBi hQi
    have hn := scalarJetNorm_nonneg (k i) (scalarCurvature (k i)) 1 x
    have hnC := metricTensorNorm_nonneg (realMetricFn (k i) x (chartPt x x))
      (ricciInverseTensor (k i) x (chartPt x x))
    have hn2 := scalarJetNorm_nonneg (k i) (scalarCurvature (k i)) 2 x
    have hnQ := scalarJetNorm_nonneg (k i) (scalarHarnackSource (k i) 0) 1 x
    calc
      _ ≤ _ := intrinsicInverseEnergyTime_abs_le (k i) (hk i) (hK i) x
      _ ≤ (1/2:ℝ)*(2*n:ℕ)*CA^2*CB*scalarJetNorm (k i) (scalarCurvature (k i)) 1 x ^ 2 +
          CA*scalarJetNorm (k i) (scalarCurvature (k i)) 1 x*CQ := by gcongr
      _ = _ := by ring
  have ht : Tendsto (fun i =>
      ((1/2:ℝ)*(2*n:ℕ)*CA^2*CB) * scalarJetNorm (k i) (scalarCurvature (k i)) 1 x ^ 2 +
      (CA*CQ)*scalarJetNorm (k i) (scalarCurvature (k i)) 1 x) l (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2≠0),mul_zero,add_zero] using
      ((hgrad.pow 2).const_mul ((1/2:ℝ)*(2*n:ℕ)*CA^2*CB)).add (hgrad.const_mul (CA*CQ))
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr
    (squeeze_zero' (Eventually.of_forall (fun i => abs_nonneg (intrinsicInverseEnergyTime (k i) x))) hb ht)

end Yau.Proofs.C05Aux
