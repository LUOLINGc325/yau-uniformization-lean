import Yau.Proofs.C03EndpointLevi

/-! Admissible holomorphic endpoints give actual scalar lower supports of
the attained moving-ball maximum on each specified affine complex line. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux L22Aux
open Yau.NodeProofs.P02Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem exists_endpoint_lower_support (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (hcompact : ∀ p R, IsCompact {x | inducedDistance k p x ≤ R})
    (ψ : ComplexVector n → ℝ) (hψc : Continuous ψ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (z y V W Q : ComplexVector n)
    (hψ : ContDiffAt ℝ 2 ψ y)
    (hy : ψ y = fieldBallMaximum k ψ ρ z)
    (hadmissible : ∀ᶠ a : ℂ in 𝓝 0,
      inducedDistance k (z + a • V) (y + a • W + ((1 / 2 : ℂ) * a ^ 2) • Q) ≤ ρ) :
    ∃ s : ℂ → ℝ, ContDiffAt ℝ 2 s 0 ∧ s 0 = fieldBallMaximum k ψ ρ z ∧
      (∀ᶠ a : ℂ in 𝓝 0, s a ≤ fieldBallMaximum k ψ ρ (z + a • V)) ∧
      planarTrace s 0 = 4 * complexLeviQuadratic ψ y W := by
  let s : ℂ → ℝ := fun a => ψ (y + a • W + ((1 / 2 : ℂ) * a ^ 2) • Q)
  refine ⟨s, quadratic_endpoint_contDiffAt ψ y W Q hψ, ?_, ?_,
    planarTrace_quadratic_endpoint ψ y W Q hψ⟩
  · simpa only [s, zero_smul, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using hy
  · filter_upwards [hadmissible] with a ha
    obtain ⟨_, _, _, hmax⟩ := fieldBallMaximum_spec k hk hcompact ψ hψc ρ hρ (z + a • V)
    exact hmax (y + a • W + ((1 / 2 : ℂ) * a ^ 2) • Q) ha

end Yau.Proofs.C03Aux
