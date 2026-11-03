import Yau.Proofs.V02WallTaylorNativeIncrements

/-! Literal outer-candidate family identities and invariance of nonzero
parameter jets under an arbitrary constant shift. -/

open scoped Topology ContDiff Manifold

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_const_shift (c : F) (f : E → F) (m : ℕ) (hm : m ≠ 0) (z : E) :
    iteratedFDeriv ℝ m (fun x => c + f x) z = iteratedFDeriv ℝ m f z := by
  cases m with
  | zero => exact (hm rfl).elim
  | succ m =>
    ext v
    rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_succ_apply_right]
    simp only [fderiv_const_add]

variable {n q b : ℕ} {X : KahlerManifold n}

theorem wallSprayFamily_zero (d : VariationData X q) (j a : ℕ)
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    (hzero : ∀ y, Ψ (y, 0) = y) (F : VariationDisc X) (c : ℂ → Fin b → ℂ) :
    wallSprayFamily d j a Ψ F c 0 = F.f := by
  funext ζ
  simp only [wallSprayFamily, zero_mul]
  exact congrArg NativeCotangentPoint.val (hzero _)

theorem wallSprayFamily_boundary_eq_nativeWallPoint {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (c : ℂ → Fin b → ℂ) (z : ℂ) (θ : ℝ) :
    wallSprayFamily d j a Ψ F c z (circlePoint θ) =
      nativeWallPoint d j a Ψ (F.f (circlePoint θ)) (z, (outerWallPhase d j a F.f θ, c (circlePoint θ))) := by
  apply congrArg (fun τ : Fin b → ℂ => (Ψ (NativeCotangentPoint.mk (F.f (circlePoint θ)), τ)).val)
  ext k
  rw [outerCandidate_eq_wallPower_mul_phase hd hF a θ]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

theorem logTrace_wallSprayFamily_eq {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (c : ℂ → Fin b → ℂ) (z : ℂ) (θ : ℝ) :
    logTrace d j (wallSprayFamily d j a Ψ F c z) θ = logTrace d j F.f θ +
      nativeLogIncrement d j a Ψ (F.f (circlePoint θ))
        (z, (outerWallPhase d j a F.f θ, c (circlePoint θ))) := by
  unfold logTrace
  rw [wallSprayFamily_boundary_eq_nativeWallPoint hd j a hF c z θ]
  dsimp [nativeLogIncrement]
  ring

end Yau.Blueprint.V02WallTaylorProof
