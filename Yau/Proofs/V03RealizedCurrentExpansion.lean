import Yau.Proofs.V03RealizedCurrentAtom
import Yau.Proofs.V03TensorRadialJet
import Yau.Proofs.V03QuadraticRadialSumAlgebra

/-! The actual radial quadratic current expands into finitely many
genuine signed derivative atoms, using only the prescribed first velocity. -/

open scoped Manifold Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem realized_quadratic_radial_expansion {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ)
    {B : CotangentPoint X.manifold → Matrix (Fin q) (Fin q) ℂ}
    (hB : ∀ x b c, ContDiffOn ℝ ∞ (fun z => B (cotangentChartInv x z) b c) (cotangentTarget x))
    (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
    (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) (θ : ℝ) :
    closedRealGradient (fun ζ => 2 *
      (star (fun b => ambientVelocity d F E l h α ζ b) ⬝ᵥ
        (B (F.f ζ) *ᵥ fun b => ambientVelocity d F E l h α ζ b)).re) (circlePoint θ) (circlePoint θ) =
      2 * ∑ i : Fin q, ∑ k : Fin q,
        ((∑ c : Fin q,
          (realizedCurrentAtom d B F E l h α (some i) (some k) (.inr ((i, k), (c, 0))) 1 (.inl c) θ +
            realizedCurrentAtom d B F E l h α (some k) (some i) (.inr ((i, k), (c, 0))) 1 (.inl c) θ +
            realizedCurrentAtom d B F E l h α (some i) (some k) (.inr ((i, k), (c, 1))) 0 (.inl c) θ -
            realizedCurrentAtom d B F E l h α (some k) (some i) (.inr ((i, k), (c, 1))) 0 (.inl c) θ)) +
          realizedCurrentAtom d B F E l h α (some k) none (.inl (i, k)) 3 (.inr i) θ +
          realizedCurrentAtom d B F E l h α (some i) none (.inl (i, k)) 1 (.inr k) θ) := by
  let V := ambientVelocity d F E l h α
  have hV := realized_ambientVelocity_contDiffOn hd j a F E l h α fz R hR
  have hVi (i : Fin q) : ContDiffOn ℂ ∞ (fun ζ => V ζ i) (Metric.closedBall (0 : ℂ) 1) :=
    (contDiffOn_piLp 2).mp hV i
  have hp := circlePoint_mem_closedBall θ
  have hA (i k : Fin q) : DifferentiableWithinAt ℝ (fun ζ => B (F.f ζ) i k)
      (Metric.closedBall (0 : ℂ) 1) (circlePoint θ) :=
    ((cotangentHolomorphicOn_coefficient_contDiffOn (b := fun y => B y i k)
      (cotangentDisc_holomorphicOn hF.1) (fun x => hB x i k)).differentiableOn (by simp)) _ hp
  change fderivWithin ℝ (fun ζ => 2 * (star (fun b => V ζ b) ⬝ᵥ
    (B (F.f ζ) *ᵥ fun b => V ζ b)).re) (Metric.closedBall (0 : ℂ) 1) (circlePoint θ) (circlePoint θ) = _
  rw [fderivWithin_real_quadratic_apply (uniqueDiffOn_real_closedDisc _ hp) hA
    (fun i => (((hVi i).restrict_scalars ℝ).differentiableOn (by simp)) _ hp)]
  simp only [Complex.re_sum]
  apply congrArg (fun t : ℝ => 2 * t)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [closedDisc_holomorphic_radial_derivative (hVi i) θ,
    closedDisc_holomorphic_radial_derivative (hVi k) θ,
    tensor_coefficient_radial_jet hd.2.2.2.2.1 hF.1 hB i k θ]
  simp only [dotProduct]
  have hg (x y z : ℂ) : (x + y + z).re = (x + z).re + y.re := by
    simp only [Complex.add_re]
    ring
  rw [hg, quadratic_velocity_radial_algebra, quadratic_coefficient_radial_sum_algebra]
  have hGfn (c : Fin q) : currentDerivativeFunction d.G F.f (ambientVelocity d F E l h α) (.inl c) =
      (fun ζ => d.G (F.f ζ) c) := rfl
  have hVfn (c : Fin q) : currentDerivativeFunction d.G F.f (ambientVelocity d F E l h α) (.inr c) =
      (fun ζ => ambientVelocity d F E l h α ζ c) := rfl
  have hC0 : tensorRealCoefficient B i k 0 = (fun y => (B y i k).re) := rfl
  have hC1 : tensorRealCoefficient B i k 1 = (fun y => (B y i k).im) := rfl
  dsimp only [V]
  simp only [realizedCurrentAtom, currentVelocityFactor, tensorCurrentCoefficient,
    signedCurrentCoefficient, tensorFirstCoefficient, Fin.reduceEq, ↓reduceIte, mul_one,
    hGfn, hVfn, hC0, hC1]
  ring

end Yau.Blueprint.V03Proof
