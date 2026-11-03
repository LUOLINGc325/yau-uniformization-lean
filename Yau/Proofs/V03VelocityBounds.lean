import Yau.Proofs.V03FirstField
import Yau.Proofs.V03OuterUniqueness

/-! Boundary speed bounds follow from the actual normalized frame and the
actual first-field realization, with no velocity hypothesis added. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem euclidean_mulVec_norm_of_gram_eq_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (U : Matrix ι κ ℂ) (hU : Uᴴ * U = 1) (v : κ → ℂ) :
    ‖(WithLp.toLp 2 (U *ᵥ v) : EuclideanSpace ℂ ι)‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ κ)‖ := by
  have hq : star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ v := by
    calc
      _ = star v ⬝ᵥ ((Uᴴ * U) *ᵥ v) := by
        symm
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          Matrix.vecMul_conjTranspose, star_star]
      _ = _ := by rw [hU, Matrix.one_mulVec]
  have hn : ‖(WithLp.toLp 2 (U *ᵥ v) : EuclideanSpace ℂ ι)‖ ^ 2 =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ κ)‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    have hq' : (U *ᵥ v) ⬝ᵥ star (U *ᵥ v) = v ⬝ᵥ star v :=
      (dotProduct_comm _ _).trans (hq.trans (dotProduct_comm _ _))
    exact congrArg Complex.re hq'
  nlinarith [norm_nonneg (WithLp.toLp 2 (U *ᵥ v) : EuclideanSpace ℂ ι),
    norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℂ κ)]

theorem ambientVelocity_boundary_norm_le
    (d : VariationData X q) (hd : VariationSetup d) (j a : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (hE : NormalizedDiscFrame d.G F.f E)
    (l : ℂ → CotangentIndex n → ℂ)
    (hl : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (r : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz r) (θ : ℝ) :
    ‖ambientVelocity d F E l h α (circlePoint θ)‖ ≤ L := by
  have hζ := circlePoint_mem_closedBall θ
  have hhn := realized_h_norm_le_one d hd j a F hF E l h α fz r hR _ hζ
  have hαn := hR.2.2.2.2.2.2.2.2.1 _ hζ
  have hln : ‖(WithLp.toLp 2 (l (circlePoint θ)) :
      EuclideanSpace ℂ (CotangentIndex n))‖ ≤ L := by
    have hsq : ‖(WithLp.toLp 2 (l (circlePoint θ)) :
        EuclideanSpace ℂ (CotangentIndex n))‖ ^ 2 ≤ L ^ 2 := by
      simpa only [EuclideanSpace.norm_sq_eq] using hl (circlePoint θ) hζ
    nlinarith [norm_nonneg (WithLp.toLp 2 (l (circlePoint θ)) :
      EuclideanSpace ℂ (CotangentIndex n))]
  unfold ambientVelocity
  rw [norm_smul, norm_mul,
    euclidean_mulVec_norm_of_gram_eq_one _ (hE.2.1 θ)]
  have hprod : ‖α (circlePoint θ)‖ * ‖h (circlePoint θ)‖ ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hαn hhn (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  exact (mul_le_mul_of_nonneg_right hprod (norm_nonneg _)).trans (by simpa using hln)

theorem realized_ambient_boundary_derivative_norm_le
    (d : VariationData X q) (hd : VariationSetup d) (j a : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (hE : NormalizedDiscFrame d.G F.f E)
    (l : ℂ → CotangentIndex n → ℂ)
    (hl : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (r : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz r) (θ : ℝ) :
    ‖fderiv ℂ (fun z => d.G (fz z (circlePoint θ))) 0 1‖ ≤ L := by
  rw [realizes_ambient_first_derivative d hd j a F E l h α fz r hR _
    (circlePoint_mem_closedBall θ)]
  exact ambientVelocity_boundary_norm_le d hd j a hL F hF E hE l hl h α fz r hR θ

end Yau.Blueprint.V03Proof
