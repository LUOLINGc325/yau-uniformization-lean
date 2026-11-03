import Yau.Proofs.C05IntrinsicInverseEnergyTimeLimit
import Yau.Proofs.C05RicciInverseEnergyRegularity
import Yau.Proofs.C05InverseEnergySpatialError

/-! The actual spatial remainder in the inverse-energy heat identity
vanishes with the undifferentiated scalar differential. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05Aux
open Yau Yau.Proofs.C05HessianPropagationAux
variable {n : ℕ} {M : ComplexManifold n} {ι : Type*}
set_option backward.isDefEq.respectTransparency false

def ricciInverseJetNorm (k : HermitianField M) (j : ℕ) (x : M.Carrier) : ℝ :=
  metricTensorNorm (realMetricFn k x (chartPt x x))
    (inverseFieldJet k x (fun z => Matrix.of (realRicciCoeff k x z)) j (chartPt x x))

def intrinsicInverseEnergySpatialRemainder (k : HermitianField M)
    (f : M.Carrier → ℝ) (x : M.Carrier) : ℝ :=
  inverseEnergySpatialRemainder k x (ricciInverseTensor k x) (scalarJet k f x 1) (chartPt x x)

theorem intrinsicInverseEnergySpatialRemainder_abs_le (k : HermitianField M)
    (hk : MetricSmooth k) (hK : KahlerClosed k) (hA : ∀ y, (ricci k y).PosDef)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (x : M.Carrier) :
    |intrinsicInverseEnergySpatialRemainder k f x| ≤
      Real.sqrt (2*n:ℕ)*ricciInverseJetNorm k 2 x*scalarJetNorm k f 1 x^2 +
      2*ricciInverseJetNorm k 0 x*Real.sqrt (2*n:ℕ)*scalarJetNorm k f 3 x*scalarJetNorm k f 1 x +
      4*ricciInverseJetNorm k 1 x*scalarJetNorm k f 2 x*scalarJetNorm k f 1 x := by
  exact inverseEnergySpatialRemainder_abs_le k hk x (ricciInverseTensor k x) (scalarJet k f x 1)
    (ricciInverseTensor_contDiffOn k hk hK hA x) (scalarJet_contDiffOn k hk f hf x 1)
    (mem_extChartAt_target x)

theorem intrinsicInverseEnergySpatialRemainder_tendsto_zero
    (k : ι → HermitianField M) (hk : ∀ i, MetricSmooth (k i))
    (hK : ∀ i, KahlerClosed (k i)) (hA : ∀ i y, (ricci (k i) y).PosDef)
    (f : ι → M.Carrier → ℝ) (hf : ∀ i, SmoothFn (f i)) (x : M.Carrier)
    (l : Filter ι) {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hC : ∀ᶠ i in l, ∀ j ≤ 2, ricciInverseJetNorm (k i) j x ≤ CA)
    (hB : ∀ᶠ i in l, scalarJetNorm (k i) (f i) 2 x ≤ CB ∧ scalarJetNorm (k i) (f i) 3 x ≤ CB)
    (hgrad : Tendsto (fun i => scalarJetNorm (k i) (f i) 1 x) l (𝓝 0)) :
    Tendsto (fun i => intrinsicInverseEnergySpatialRemainder (k i) (f i) x) l (𝓝 0) := by
  have hb : ∀ᶠ i in l, |intrinsicInverseEnergySpatialRemainder (k i) (f i) x| ≤
      (Real.sqrt (2*n:ℕ)*CA)*scalarJetNorm (k i) (f i) 1 x^2 +
      (2*CA*Real.sqrt (2*n:ℕ)*CB+4*CA*CB)*scalarJetNorm (k i) (f i) 1 x := by
    filter_upwards [hC,hB] with i hCi hBi
    have hn := scalarJetNorm_nonneg (k i) (f i) 1 x
    have hn2 := scalarJetNorm_nonneg (k i) (f i) 2 x
    have hn3 := scalarJetNorm_nonneg (k i) (f i) 3 x
    have hc0 := hCi 0 (by norm_num)
    have hc1 := hCi 1 (by norm_num)
    have hc2 := hCi 2 (by norm_num)
    have hn0 := metricTensorNorm_nonneg (realMetricFn (k i) x (chartPt x x))
      (inverseFieldJet (k i) x (fun z => Matrix.of (realRicciCoeff (k i) x z)) 0 (chartPt x x))
    have hn1 := metricTensorNorm_nonneg (realMetricFn (k i) x (chartPt x x))
      (inverseFieldJet (k i) x (fun z => Matrix.of (realRicciCoeff (k i) x z)) 1 (chartPt x x))
    change 0 ≤ ricciInverseJetNorm (k i) 0 x at hn0
    change 0 ≤ ricciInverseJetNorm (k i) 1 x at hn1
    calc
      _ ≤ _ := intrinsicInverseEnergySpatialRemainder_abs_le (k i) (hk i) (hK i) (hA i) (f i) (hf i) x
      _ ≤ Real.sqrt (2*n:ℕ)*CA*scalarJetNorm (k i) (f i) 1 x^2 +
          2*CA*Real.sqrt (2*n:ℕ)*CB*scalarJetNorm (k i) (f i) 1 x +
          4*CA*CB*scalarJetNorm (k i) (f i) 1 x := by gcongr <;> first | exact hBi.1 | exact hBi.2
      _ = _ := by ring
  have ht : Tendsto (fun i =>
      (Real.sqrt (2*n:ℕ)*CA)*scalarJetNorm (k i) (f i) 1 x^2 +
      (2*CA*Real.sqrt (2*n:ℕ)*CB+4*CA*CB)*scalarJetNorm (k i) (f i) 1 x) l (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2≠0),mul_zero,add_zero] using
      ((hgrad.pow 2).const_mul (Real.sqrt (2*n:ℕ)*CA)).add
        (hgrad.const_mul (2*CA*Real.sqrt (2*n:ℕ)*CB+4*CA*CB))
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr
    (squeeze_zero' (Eventually.of_forall (fun i => abs_nonneg
      (intrinsicInverseEnergySpatialRemainder (k i) (f i) x))) hb ht)

end Yau.Proofs.C05Aux
