import Yau.Proofs.D05CompactMatrixBounds
import Yau.Proofs.D05GeneratedBundle
import Yau.Proofs.D05ClosedFactors
import Yau.Proofs.V03CirclePeriod
import Yau.Proofs.V03LogTrace

/-! The boundary Gram matrix of an actual full-column frame supplies the
original smooth periodic D06 source, with genuine positive spectral bounds. -/

open scoped Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau V03Proof

theorem euclidean_star_dot_norm {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    star (WithLp.ofLp v) ⬝ᵥ WithLp.ofLp v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  have he : inner ℂ v v = star (WithLp.ofLp v) ⬝ᵥ WithLp.ofLp v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [← he]
  simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v)

theorem matrix_gram_quadratic {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix κ ι ℂ) (v : EuclideanSpace ℂ ι) :
    star (WithLp.ofLp v) ⬝ᵥ ((Matrix.conjTranspose A * A) *ᵥ WithLp.ofLp v) =
      ((‖Matrix.toEuclideanLin A v‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
  exact euclidean_star_dot_norm (Matrix.toEuclideanLin A v)

theorem gram_spectral_bounds {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix κ ι ℂ) {γ Γ : ℝ} (hγ : 0 ≤ γ) (hΓ : 0 ≤ Γ)
    (hb : ∀ v : EuclideanSpace ℂ ι,
      γ * ‖v‖ ≤ ‖Matrix.toEuclideanLin A v‖ ∧
        ‖Matrix.toEuclideanLin A v‖ ≤ Γ * ‖v‖) :
    (Matrix.conjTranspose A * A - ((γ ^ 2 : ℝ) : ℂ) • 1).PosSemidef ∧
      (((Γ ^ 2 : ℝ) : ℂ) • 1 - Matrix.conjTranspose A * A).PosSemidef := by
  have hHerm : (Matrix.conjTranspose A * A).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self A
  have hscalar (c : ℝ) : ((c : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian :=
    Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])
  constructor
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hHerm.sub (hscalar (γ ^ 2)))
    intro u
    let v : EuclideanSpace ℂ ι := WithLp.toLp 2 u
    have hn := sq_le_sq₀ (mul_nonneg hγ (norm_nonneg v))
      (norm_nonneg (Matrix.toEuclideanLin A v)) |>.mpr (hb v).1
    rw [mul_pow] at hn
    have hq := matrix_gram_quadratic A v
    change star (WithLp.ofLp v) ⬝ᵥ
      ((Matrix.conjTranspose A * A - ((γ ^ 2 : ℝ) : ℂ) • 1) *ᵥ WithLp.ofLp v) ≥ 0
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul, hq, euclidean_star_dot_norm]
    exact_mod_cast sub_nonneg.mpr hn
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ((hscalar (Γ ^ 2)).sub hHerm)
    intro u
    let v : EuclideanSpace ℂ ι := WithLp.toLp 2 u
    have hn := sq_le_sq₀ (norm_nonneg (Matrix.toEuclideanLin A v))
      (mul_nonneg hΓ (norm_nonneg v)) |>.mpr (hb v).2
    rw [mul_pow] at hn
    have hq := matrix_gram_quadratic A v
    change star (WithLp.ofLp v) ⬝ᵥ
      ((((Γ ^ 2 : ℝ) : ℂ) • 1 - Matrix.conjTranspose A * A) *ᵥ WithLp.ofLp v) ≥ 0
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul, hq, euclidean_star_dot_norm]
    exact_mod_cast sub_nonneg.mpr hn

theorem boundary_gram_source {q r : ℕ} {ρ : ℝ} (hρ : 1 < ρ)
    (V : ℂ → Matrix (Fin q) (Fin r) ℂ)
    (hV : ∀ a j, ContDiffOn ℂ ∞ (fun z => V z a j) (Metric.ball 0 ρ))
    (hi : ∀ z ∈ Metric.ball (0 : ℂ) ρ, Function.Injective (V z).mulVec) :
    ∃ s : Yau.NodeProofs.D06Aux.BoundarySource r,
      ∀ θ, s.L θ = Matrix.conjTranspose (V (circlePoint θ)) * V (circlePoint θ) := by
  have hsub : Metric.sphere (0 : ℂ) 1 ⊆ Metric.ball 0 ρ := by
    intro z hz
    simpa only [Metric.mem_sphere, Metric.mem_ball, dist_zero_right] using
      (show dist z 0 < ρ from (show dist z 0 = 1 from hz).trans_lt hρ)
  obtain ⟨γ, Γ, hγ, hγΓ, hb⟩ := compact_matrix_bounds (isCompact_sphere (0 : ℂ) 1)
    (fun a j => (hV a j).continuousOn.mono hsub)
    (fun z hz => toEuclideanLin_injective_of_mulVec (V z) (hi z (hsub hz)))
  have hΓ : 0 < Γ := lt_of_lt_of_le hγ hγΓ
  let L : ℝ → Matrix (Fin r) (Fin r) ℂ :=
    fun θ => Matrix.conjTranspose (V (circlePoint θ)) * V (circlePoint θ)
  have hcircle (θ : ℝ) : circlePoint θ ∈ Metric.ball (0 : ℂ) ρ := by
    simpa only [Metric.mem_ball, dist_zero_right, circlePoint_norm] using hρ
  have hVs (a : Fin q) (j : Fin r) : ContDiff ℝ ∞ (fun θ => V (circlePoint θ) a j) := by
    apply contDiff_iff_contDiffAt.mpr
    intro θ
    exact ((hV a j).contDiffAt (Metric.isOpen_ball.mem_nhds (hcircle θ))).restrict_scalars ℝ
      |>.comp θ circlePoint_contDiff.contDiffAt
  let s : Yau.NodeProofs.D06Aux.BoundarySource r :=
    { L := L, m := γ ^ 2, M := Γ ^ 2, m_pos := sq_pos_of_pos hγ,
      m_le_M := (sq_le_sq₀ hγ.le hΓ.le).mpr hγΓ,
      smooth := ?_, periodic := ?_, order := ?_ }
  exact ⟨s, fun _ => rfl⟩
  · intro i j
    change ContDiff ℝ ∞ (fun θ => ∑ a, star (V (circlePoint θ) a i) * V (circlePoint θ) a j)
    exact ContDiff.sum fun a _ =>
      (Complex.conjCLE.contDiff.comp (hVs a i)).mul (hVs a j)
  · intro θ
    dsimp only [L]
    rw [circlePoint_periodic θ]
  · intro θ
    exact_mod_cast gram_spectral_bounds (V (circlePoint θ)) hγ.le hΓ.le
      (hb (circlePoint θ) (by simp [Metric.mem_sphere, circlePoint_norm]))

end Yau.Blueprint.D05Proof
