import Yau.Proofs.C05IntrinsicRigiditySequence

/-! The original clock only needs an eventual upper bound. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05IntrinsicRigiditySequenceAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
open Yau.Proofs.C05HarnackFrameIdentitiesAux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem eventually_intrinsic_realHess_negative_of_eventually_clock_le
    (k : ℕ → HermitianField M) (hk : ∀ i, MetricSmooth (k i))
    (hK : ∀ i, KahlerClosed (k i)) (hA : ∀ i y, (ricci (k i) y).PosDef)
    (x : M.Carrier) (μ K : ℝ) (hμ : 0 < μ) (hK0 : 0 ≤ K)
    (κ : ℕ → ℝ) (hκnonneg : ∀ i, 0 ≤ κ i) (hκbound : ∀ᶠ i in atTop, κ i ≤ K)
    (hnorm : ∀ i, scalarCurvature (k i) x=1)
    (hpin : ∀ i, μ ≤ relMinEigenvalue (gMat (k i) x) (ricci (k i) x))
    (hPSD : ∀ i, (sliceHarnackMatrix (k i) (κ i) x).PosSemidef)
    (hS : Tendsto (fun i => scalarHarnackSource (k i) (κ i) x) atTop (𝓝 0))
    (hE : Tendsto (fun i => intrinsicInverseEnergyHeatRemainder (k i) x) atTop (𝓝 0))
    (hL : ∀ ε > 0, ∀ᶠ i in atTop, intrinsicMinimizedHeat (k i) (κ i) x ≤ ε) :
    ∀ᶠ i in atTop, ∀ v : TangentVector M x,
      realHess (k i) (scalarCurvature (k i)) x v v ≤ -(μ^2/2)*realNormSq (k i) x v := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hκbound
  have htail : ∀ᶠ i in atTop, ∀ v : TangentVector M x,
      realHess (k (i+N)) (scalarCurvature (k (i+N))) x v v ≤
        -(μ^2/2)*realNormSq (k (i+N)) x v :=
    eventually_intrinsic_realHess_negative (n := n) (M := M) (fun i => k (i+N))
    (fun i => hk (i+N)) (fun i => hK (i+N)) (fun i => hA (i+N)) x μ K hμ hK0
    (fun i => κ (i+N))
    (fun i => ⟨hκnonneg (i+N),hN (i+N) (by omega)⟩)
    (fun i => hnorm (i+N)) (fun i => hpin (i+N)) (fun i => hPSD (i+N))
    (hS.comp (tendsto_add_atTop_nat N)) (hE.comp (tendsto_add_atTop_nat N))
    (fun ε hε => (tendsto_add_atTop_nat N).eventually (hL ε hε))
  obtain ⟨J,hJ⟩ := eventually_atTop.mp htail
  apply eventually_atTop.mpr
  refine ⟨J+N,?_⟩
  intro i hi
  have hNi : N ≤ i := by omega
  have hJi : J ≤ i-N := by omega
  simpa only [Nat.sub_add_cancel hNi] using hJ (i-N) hJi

end Yau.Proofs.C05IntrinsicRigiditySequenceAux
