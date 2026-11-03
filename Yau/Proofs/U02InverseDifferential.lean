import Yau.Proofs.U02MetricAlgebra

/-! Differentiating the genuine inverse-sheet identity retains the
initial metric lower bound on every actual tangent vector. -/

open scoped Manifold Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint

theorem raw_inverse_differential_metric {n : ℕ} {M : ComplexManifold n}
    (g h : HermitianField M) (p x : M.Carrier)
    (Phi : ComplexVector n → M.Carrier) (f : M.Carrier → ComplexVector n)
    {r c C a : ℝ} (hc : UnitaryChart h p Phi r c C)
    (hfx : f x ∈ ball 0 r)
    (hdf : MDifferentiableAt (ComplexModel n) 𝓘(ℂ, ComplexVector n) f x)
    (hleft : ∀ᶠ y in 𝓝 x, Phi (f y) = y)
    (hmetric : HermLE ((a : ℂ) • gMat g x) (gMat h x)) (v : TangentVector M x) :
    a * hermitianNormSq (g x) v ≤ C *
      ‖(tangentSpaceCastModel 𝓘(ℂ, ComplexVector n) (f x))
        (mfderiv (ComplexModel n) 𝓘(ℂ, ComplexVector n) f x v)‖ ^ 2 := by
  have hPhi := ((hc.1.1 (f x) hfx).contMDiffAt (isOpen_ball.mem_nhds hfx)).mdifferentiableAt
    (by simp)
  have heq : (Phi ∘ f) =ᶠ[𝓝 x] id := hleft
  have hval : Phi (f x) = x := heq.eq_of_nhds
  have he := heq.mfderiv_eq (I := ComplexModel n) (I' := ComplexModel n)
  rw [mfderiv_comp x hPhi hdf, mfderiv_id] at he
  have hev := congrArg (fun L => L v) he
  change mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Phi (f x)
    (mfderiv (ComplexModel n) 𝓘(ℂ, ComplexVector n) f x v) = v at hev
  have hup := unitaryChart_tangent_normSq h p Phi hc hfx
    (mfderiv (ComplexModel n) 𝓘(ℂ, ComplexVector n) f x v)
  rw [hev, hval] at hup
  exact (hermLE_tangent_normSq g h x a hmetric v).trans hup

end Yau.NodeProofs.U02Proof
