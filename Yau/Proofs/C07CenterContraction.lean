import Yau.Proofs.Y03CenterFrame

/-! A later smaller metric makes the genuine centered transition a contraction. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Yau.Blueprint.Alignment
open Yau.Blueprint.Alignment.Y03Proof

variable {n : ℕ}

theorem matOpNorm_le_one_of_gram (A : Herm n)
    (hA : (1 - A.conjTranspose * A).PosSemidef) : matOpNorm A ≤ 1 := by
  let L := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  apply (L A).opNorm_le_bound zero_le_one
  intro v
  rw [one_mul]
  have hnorm (w : ComplexVector n) :
      (star (WithLp.ofLp w) ⬝ᵥ WithLp.ofLp w).re = ‖w‖ ^ 2 := by
    have hh := inner_self_eq_norm_sq (𝕜 := ℂ) w
    rw [EuclideanSpace.inner_eq_star_dotProduct, RCLike.re_eq_complex_re] at hh
    simpa only [dotProduct_comm] using hh
  have hnormA : (star (WithLp.ofLp v) ⬝ᵥ
      ((A.conjTranspose * A) *ᵥ WithLp.ofLp v)).re = ‖L A v‖ ^ 2 := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_conjTranspose, star_star]
    exact hnorm (L A v)
  have hp := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg (WithLp.ofLp v))).1
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, Complex.sub_re,
    hnorm, hnormA] at hp
  nlinarith [norm_nonneg (L A v), norm_nonneg v]

theorem frame_transition_contraction (H₀ H₁ P₀ P₁ A : Herm n)
    (h₀ : P₀.conjTranspose * H₀ * P₀ = 1)
    (h₁ : P₁.conjTranspose * H₁ * P₁ = 1)
    (hchain : P₁ * A = P₀) (horder : HermLE H₁ H₀) : matOpNorm A ≤ 1 := by
  have hquad : A.conjTranspose * A = P₀.conjTranspose * H₁ * P₀ := by
    calc
      A.conjTranspose * A = A.conjTranspose * (P₁.conjTranspose * H₁ * P₁) * A := by
        rw [h₁, Matrix.mul_one]
      _ = (P₁ * A).conjTranspose * H₁ * (P₁ * A) := by
        rw [Matrix.conjTranspose_mul]
        noncomm_ring
      _ = _ := by rw [hchain]
  apply matOpNorm_le_one_of_gram
  have hp := horder.conjTranspose_mul_mul_same P₀
  rwa [Matrix.mul_sub, Matrix.sub_mul, h₀, ← hquad] at hp

theorem transition_center_contraction {X : KahlerManifold n} {o : Pt X} {h : Flow X}
    {Φ Ψ : ComplexVector n → Pt X} {F : ComplexVector n → ComplexVector n}
    {t u r R q c C c' C' : ℝ} (hq : 0 < q) (hR : 0 < R)
    (hΦ : UnitaryChart (h t) o Φ r c C)
    (hΨ : UnitaryChart (h u) o Ψ R c' C')
    (hF : DifferentiableOn ℂ F (Metric.ball 0 q)) (hFzero : F 0 = 0)
    (hgerm : ∀ᶠ z in 𝓝 0, Ψ (F z) = Φ z)
    (horder : HermLE (gMat (h u) o) (gMat (h t) o)) :
    ‖centerDeriv F‖ ≤ 1 := by
  rw [← matOpNorm_derivativeMatrix]
  exact frame_transition_contraction (gMat (h t) o) (gMat (h u) o)
    (centerFrameMatrix o Φ) (centerFrameMatrix o Ψ) (derivativeMatrix F)
    (unitaryChart_centerFrame_gram hΦ) (unitaryChart_centerFrame_gram hΨ)
    (centerFrameMatrix_chain o hq hR hΨ.1.1 hF hFzero hgerm) horder

end Yau.Proofs.C07Aux
