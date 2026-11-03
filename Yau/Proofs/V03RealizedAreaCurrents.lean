import Yau.Proofs.V03GaussDiscCurrent
import Yau.Proofs.V03BaseDiscCurrent
import Yau.Proofs.V03JointGaussAmbientDiagonal
import Yau.Proofs.V03JointBaseAmbientDiagonal
import Yau.Proofs.V03VelocityBounds

/-! Both original mixed area derivatives are genuine radial currents
of their intrinsic ambient tensors and the prescribed first velocity alone. -/

open scoped Manifold Topology ContDiff Matrix
open Filter MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def ambientQuadraticDiscCurrent (B : CotangentPoint X.manifold → Matrix (Fin q) (Fin q) ℂ)
    (f : ℂ → CotangentPoint X.manifold) (V : ℂ → ComplexVector q) : ℝ :=
  (1 / 4 : ℝ) * ∫ θ in (-Real.pi)..Real.pi,
    closedRealGradient (fun ζ => 2 * (star (fun a => V ζ a) ⬝ᵥ (B (f ζ) *ᵥ fun a => V ζ a)).re)
      (circlePoint θ) (circlePoint θ)

theorem realizes_joint_ambient_velocity {d : VariationData X q} (hd : VariationSetup d)
    {j a : ℕ} {F : VariationDisc X} {E : ℂ → CotangentMatrix n}
    {l : ℂ → CotangentIndex n → ℂ} {h α : ℂ → ℂ}
    {fz : ℂ → ℂ → CotangentPoint X.manifold} {R : ℝ}
    (hR : RealizesFirstField d j a F E l h α fz R)
    {ζ : ℂ} (hζ : ζ ∈ Metric.closedBall (0 : ℂ) 1) :
    fderivWithin ℂ (fun p : ℂ × ℂ => d.G (fz p.1 p.2))
      (Metric.ball (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) 1) (0, ζ) (1, 0) =
        ambientVelocity d F E l h α ζ := by
  have hH := cotangentHolomorphicOn_ambient_contDiffOn hR.1.2.2 hd.2.2.2.2.1.1
  rw [← fderiv_complex_parameter_slice Metric.isOpen_ball (Metric.mem_ball_self hR.1.1) hζ
    ((hH.differentiableOn (by simp)) _ ⟨Metric.mem_ball_self hR.1.1, hζ⟩) (1 : ℂ)]
  exact realizes_ambient_first_derivative d hd j a F E l h α fz R hR ζ hζ

theorem realized_gaussArea_mixed_current {d : VariationData X q} (hd : VariationSetup d)
    {j a : ℕ} {F : VariationDisc X} {E : ℂ → CotangentMatrix n}
    {l : ℂ → CotangentIndex n → ℂ} {h α : ℂ → ℂ}
    {fz : ℂ → ℂ → CotangentPoint X.manifold} {R : ℝ}
    (hR : RealizesFirstField d j a F E l h α fz R) :
    mixedReal (fun z => gaussArea d.G (fz z)) =
      ambientQuadraticDiscCurrent (ambientGaussTensor d.G) F.f (ambientVelocity d F E l h α) := by
  let S : Set (ℂ × ℂ) := Metric.ball (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) 1
  let Ω := jointGaussTwoForm d.G (fun p : ℂ × ℂ => fz p.1 p.2) S
  have hS : UniqueDiffOn ℂ S := Metric.isOpen_ball.uniqueDiffOn.prod uniqueDiffOn_complex_closedDisc
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self hR.1.1
  have he (ζ : ℂ) (hζ : ζ ∈ Metric.closedBall (0 : ℂ) 1) :
      Ω (0, ζ) ![((1, 0) : ℂ × ℂ), ((Complex.I, 0) : ℂ × ℂ)] =
        2 * (star (fun a => ambientVelocity d F E l h α ζ a) ⬝ᵥ
          (ambientGaussTensor d.G (F.f ζ) *ᵥ fun a => ambientVelocity d F E l h α ζ a)).re := by
    have hI : ((Complex.I, 0) : ℂ × ℂ) = Complex.I • ((1, 0) : ℂ × ℂ) := by
      simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero]
    rw [hI, jointGaussTwoForm_ambient_diagonal hd.2.2.2.2.1 hR.1.2.2 ⟨h0, hζ⟩ (hS _ ⟨h0, hζ⟩)]
    rw [realizes_joint_ambient_velocity hd hR hζ, congrFun hR.1.2.1 ζ]
  rw [gaussArea_mixed_eq_boundary_current (G := d.G) (f := fun p : ℂ × ℂ => fz p.1 p.2)
    hd.2.2.2.2.1 Metric.isOpen_ball hR.1.2.2 h0]
  unfold ambientQuadraticDiscCurrent
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  have heq : (fun ζ => Ω (0, ζ) ![((1, 0) : ℂ × ℂ), ((Complex.I, 0) : ℂ × ℂ)]) =ᶠ[
      𝓝[Metric.closedBall (0 : ℂ) 1] (circlePoint θ)]
      (fun ζ => 2 * (star (fun a => ambientVelocity d F E l h α ζ a) ⬝ᵥ
        (ambientGaussTensor d.G (F.f ζ) *ᵥ fun a => ambientVelocity d F E l h α ζ a)).re) := by
    filter_upwards [self_mem_nhdsWithin] with ζ hζ
    exact he ζ hζ
  exact congrArg (fun A : ℂ →L[ℝ] ℝ => A (circlePoint θ))
    (heq.fderivWithin_eq_of_mem (circlePoint_mem_closedBall θ))

theorem realized_baseArea_mixed_current {d : VariationData X q} (hd : VariationSetup d)
    {j a : ℕ} {F : VariationDisc X} {E : ℂ → CotangentMatrix n}
    {l : ℂ → CotangentIndex n → ℂ} {h α : ℂ → ℂ}
    {fz : ℂ → ℂ → CotangentPoint X.manifold} {R : ℝ}
    (hR : RealizesFirstField d j a F E l h α fz R) :
    mixedReal (fun z => (discArea X.metric.form (fun ζ => (fz z ζ).1)).toReal) =
      ambientQuadraticDiscCurrent (ambientBaseTensor d.G X.metric.form) F.f
        (ambientVelocity d F E l h α) := by
  let S : Set (ℂ × ℂ) := Metric.ball (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) 1
  let Ω := jointBaseTwoForm X.metric.form (fun p : ℂ × ℂ => fz p.1 p.2) S
  have hS : UniqueDiffOn ℂ S := Metric.isOpen_ball.uniqueDiffOn.prod uniqueDiffOn_complex_closedDisc
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self hR.1.1
  have he (ζ : ℂ) (hζ : ζ ∈ Metric.closedBall (0 : ℂ) 1) :
      Ω (0, ζ) ![((1, 0) : ℂ × ℂ), ((Complex.I, 0) : ℂ × ℂ)] =
        2 * (star (fun a => ambientVelocity d F E l h α ζ a) ⬝ᵥ
          (ambientBaseTensor d.G X.metric.form (F.f ζ) *ᵥ fun a => ambientVelocity d F E l h α ζ a)).re := by
    have hI : ((Complex.I, 0) : ℂ × ℂ) = Complex.I • ((1, 0) : ℂ × ℂ) := by
      simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero]
    rw [hI, jointBaseTwoForm_ambient_diagonal hd.2.2.2.2.1 X.metric.form hR.1.2.2
      ⟨h0, hζ⟩ (hS _ ⟨h0, hζ⟩)]
    rw [realizes_joint_ambient_velocity hd hR hζ, congrFun hR.1.2.1 ζ]
  rw [baseArea_mixed_eq_boundary_current X.metric X.kahler_metric (f := fun p : ℂ × ℂ => fz p.1 p.2)
    Metric.isOpen_ball hR.1.2.2 h0]
  unfold ambientQuadraticDiscCurrent
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  have heq : (fun ζ => Ω (0, ζ) ![((1, 0) : ℂ × ℂ), ((Complex.I, 0) : ℂ × ℂ)]) =ᶠ[
      𝓝[Metric.closedBall (0 : ℂ) 1] (circlePoint θ)]
      (fun ζ => 2 * (star (fun a => ambientVelocity d F E l h α ζ a) ⬝ᵥ
        (ambientBaseTensor d.G X.metric.form (F.f ζ) *ᵥ fun a => ambientVelocity d F E l h α ζ a)).re) := by
    filter_upwards [self_mem_nhdsWithin] with ζ hζ
    exact he ζ hζ
  exact congrArg (fun A : ℂ →L[ℝ] ℝ => A (circlePoint θ))
    (heq.fderivWithin_eq_of_mem (circlePoint_mem_closedBall θ))

end Yau.Blueprint.V03Proof
