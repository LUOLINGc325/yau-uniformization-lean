import Yau.Proofs.C05HessianFrameEnergyBinding

/-! The same invertible frame transfers every finite Hessian bound to all genuine tangent vectors. -/
noncomputable section
open Filter
open scoped Topology Matrix Manifold ContDiff
namespace Yau.Proofs.C05RealHessianFrameTransferAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
open Yau.LeafProofs.L12Aux
open Yau.Proofs.C05HessianFrameEnergyBindingAux
variable {n : ℕ} {M : ComplexManifold n}

def inverseFrameCoordinates (x : M.Carrier) (W : Matrix (Fin n) (Fin n) ℂ)
    (v : TangentVector M x) : ComplexVector n :=
  WithLp.toLp 2 (W⁻¹ *ᵥ WithLp.ofLp (tangentCoords x x v))

theorem frameVector_inverseFrameCoordinates (x : M.Carrier)
    (W : Matrix (Fin n) (Fin n) ℂ) (hdet : W.det ≠ 0) (v : TangentVector M x) :
    frameVector x W (inverseFrameCoordinates x W v) = v := by
  unfold frameVector inverseFrameCoordinates
  rw [WithLp.ofLp_toLp,Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv W (isUnit_iff_ne_zero.mpr hdet),Matrix.one_mulVec,WithLp.toLp_ofLp]
  exact chartVec_tangentCoords x x (mem_extChartAt_source x) v

theorem frameVector_surjective (x : M.Carrier) (W : Matrix (Fin n) (Fin n) ℂ)
    (hdet : W.det ≠ 0) : Function.Surjective (frameVector x W) := by
  intro v
  exact ⟨inverseFrameCoordinates x W v,frameVector_inverseFrameCoordinates x W hdet v⟩

theorem realHess_le_of_unitaryHessian (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (f : M.Carrier → ℝ) (hf : SmoothFn f) (x : M.Carrier)
    (W : Matrix (Fin n) (Fin n) ℂ) (hdet : W.det ≠ 0)
    (hGram : Wᴴ*gMat k x*W=1) (a : ℝ)
    (hfinite : ∀ w : Fin n → ℂ,
      unitaryHessianQuadratic (Wᴴ*levi f x*W) (hessianPure (frameHessian k f x W)) w ≤
        -a*(2*∑ j,‖w j‖^2)) :
    ∀ v : TangentVector M x, realHess k f x v v ≤ -a*realNormSq k x v := by
  intro v
  obtain ⟨w,rfl⟩ := frameVector_surjective x W hdet v
  rw [realHess_frame k hk hK f hf x W w,realNormSq_frame k x W hGram w]
  exact hfinite (WithLp.ofLp w)

theorem eventually_realHess_le_of_unitaryHessian {ι : Type*} {l : Filter ι}
    (k : ι → HermitianField M) (hk : ∀ i, MetricSmooth (k i))
    (hK : ∀ i, KahlerClosed (k i)) (f : ι → M.Carrier → ℝ) (hf : ∀ i, SmoothFn (f i))
    (x : ι → M.Carrier) (W : ι → Matrix (Fin n) (Fin n) ℂ)
    (hdet : ∀ i, (W i).det ≠ 0) (hGram : ∀ i, (W i)ᴴ*gMat (k i) (x i)*W i=1) (a : ℝ)
    (hfinite : ∀ᶠ i in l, ∀ w : Fin n → ℂ,
      unitaryHessianQuadratic ((W i)ᴴ*levi (f i) (x i)*W i)
        (hessianPure (frameHessian (k i) (f i) (x i) (W i))) w ≤ -a*(2*∑ j,‖w j‖^2)) :
    ∀ᶠ i in l, ∀ v : TangentVector M (x i),
      realHess (k i) (f i) (x i) v v ≤ -a*realNormSq (k i) (x i) v := by
  exact hfinite.mono fun i hi =>
    realHess_le_of_unitaryHessian (k i) (hk i) (hK i) (f i) (hf i) (x i)
      (W i) (hdet i) (hGram i) a hi

end Yau.Proofs.C05RealHessianFrameTransferAux
