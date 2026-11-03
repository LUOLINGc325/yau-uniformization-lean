import Yau.Proofs.C05IntrinsicHarnackHeat
import Yau.Proofs.C05UnitaryFrame
import Yau.Proofs.C05HarnackFrameIdentities
import Yau.Proofs.C05FiniteHarnackSequence
import Yau.Proofs.C05RealHessianFrameTransfer

/-! The genuine intrinsic heat identity forces actual center Hessian negativity. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05IntrinsicRigiditySequenceAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
open Yau.Proofs.C05UnitaryFrameAux Yau.Proofs.C05HarnackFrameIdentitiesAux
open Yau.Proofs.C05HessianFrameEnergyBindingAux Yau.Proofs.C05FiniteHarnackSequenceAux
open Yau.Proofs.C05RealHessianFrameTransferAux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem eventually_intrinsic_realHess_negative
    (k : ℕ → HermitianField M) (hk : ∀ i, MetricSmooth (k i))
    (hK : ∀ i, KahlerClosed (k i)) (hA : ∀ i y, (ricci (k i) y).PosDef)
    (x : M.Carrier) (μ K : ℝ) (hμ : 0 < μ) (hK0 : 0 ≤ K)
    (κ : ℕ → ℝ) (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ K)
    (hnorm : ∀ i, scalarCurvature (k i) x=1)
    (hpin : ∀ i, μ ≤ relMinEigenvalue (gMat (k i) x) (ricci (k i) x))
    (hPSD : ∀ i, (sliceHarnackMatrix (k i) (κ i) x).PosSemidef)
    (hS : Tendsto (fun i => scalarHarnackSource (k i) (κ i) x) atTop (𝓝 0))
    (hE : Tendsto (fun i => intrinsicInverseEnergyHeatRemainder (k i) x) atTop (𝓝 0))
    (hL : ∀ ε > 0, ∀ᶠ i in atTop, intrinsicMinimizedHeat (k i) (κ i) x ≤ ε) :
    ∀ᶠ i in atTop, ∀ v : TangentVector M x,
      realHess (k i) (scalarCurvature (k i)) x v v ≤ -(μ^2/2)*realNormSq (k i) x v := by
  classical
  have hg (i : ℕ) : (gMat (k i) x).PosDef :=
    Yau.LeafProofs.L18Aux.hMat_posDef (k i) x (chartPt x x) (mem_extChartAt_target x)
  have ht (i : ℕ) : (((gMat (k i) x)⁻¹ * ricci (k i) x).trace).re=1 := hnorm i
  choose W lam hdet hGram hDiag hlam hsum hlo hup using
    (fun i => unitary_frame_exists_trace_one (gMat (k i) x) (ricci (k i) x)
      (hg i) (hA i x) hμ (hpin i) (ht i))
  let MM := fun i => (W i)ᴴ*sliceHarnackMatrix (k i) (κ i) x*W i
  let PP := fun i => hessianPure (frameHessian (k i) (scalarCurvature (k i)) x (W i))
  let LL := fun i => intrinsicMinimizedHeat (k i) (κ i) x
  let EE := fun i => intrinsicInverseEnergyHeatRemainder (k i) x
  have hf (i : ℕ) : SmoothFn (scalarCurvature (k i)) := scalarCurvature_smoothFn (k i) (hk i) (hK i)
  have hM (i : ℕ) : (MM i).PosSemidef := (hPSD i).conjTranspose_mul_mul_same (W i)
  have htrace (i : ℕ) : (MM i).trace.re=scalarHarnackSource (k i) (κ i) x :=
    sliceHarnackMatrix_frame_trace (k i) (κ i) x (W i) (hdet i) (hGram i)
  have he : Tendsto (fun i => (MM i).trace.re) atTop (𝓝 0) :=
    hS.congr' (Eventually.of_forall (fun i => (htrace i).symm))
  have hshift (i : ℕ) : (W i)ᴴ*levi (scalarCurvature (k i)) x*W i =
      MM i-Matrix.diagonal (fun j => ((lam i j*(lam i j+κ i):ℝ):ℂ)) :=
    sliceHarnackMatrix_frame_shift (k i) (κ i) x (W i) (lam i) (hdet i) (hGram i) (hDiag i)
  have hidentity (i : ℕ) : LL i=weightedHessianSquare (lam i) (PP i)+
      (∑ j,lam i j*(MM i j j).re)-2*κ i*(MM i).trace.re+
      weightedHessianSquare (lam i) (MM i)-EE i := by
    have H : LL i=sliceHarnackLeading (k i) (κ i) x+
        (1/2:ℝ)*inverseEnergyHessianSquare (k i) (scalarCurvature (k i)) x (chartPt x x)-EE i :=
      intrinsicMinimizedHeat_decomposition (k i) (hk i) (hK i) (hA i) (κ i) x
    rw [sliceHarnackLeading_frame (k i) (κ i) x (W i) (lam i) (hdet i) (hGram i) (hDiag i),
      half_inverseEnergyHessianSquare_frame (k i) (hk i) (hK i) _ (hf i) x (W i)
        (hdet i) (hGram i) (lam i) (hDiag i) (hlam i),hshift i] at H
    calc
      LL i = diagonalScalarHarnackEvolution (lam i) (κ i) (MM i) -
          (-weightedHessianSquare (lam i) (MM i-Matrix.diagonal
            (fun j => ((lam i j*(lam i j+κ i):ℝ):ℂ))) -
              weightedHessianSquare (lam i) (PP i)+EE i) := by rw [H]; ring
      _ = _ := diagonal_harnack_cancellation (lam i) (hlam i) (κ i) (EE i) (MM i) (PP i)
  have hfinite := (finite_harnack_sequence μ K hμ hK0 lam hlam hlo hup κ hκ
    MM PP hM LL EE he hE hL hidentity).2
  have hactualFinite : ∀ᶠ i in atTop, ∀ w : Fin n → ℂ,
      unitaryHessianQuadratic ((W i)ᴴ*levi (scalarCurvature (k i)) x*W i) (PP i) w ≤
        -(μ^2/2)*(2*∑ j,‖w j‖^2) := by
    filter_upwards [hfinite] with i hi
    intro w
    rw [hshift i]
    exact hi w
  exact eventually_realHess_le_of_unitaryHessian k hk hK (fun i => scalarCurvature (k i)) hf
    (fun _ => x) W hdet hGram (μ^2/2) hactualFinite

end Yau.Proofs.C05IntrinsicRigiditySequenceAux
