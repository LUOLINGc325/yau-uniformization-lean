import Yau.Proofs.V03RealizedMultipliers
import Yau.Proofs.V03BoundarySum

/-! The actual normalized realization scalar, including the exact wall
power cancellation and its modulus-square half-order control. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def normalizedVelocityScalar (d : VariationData X q) (j a : ℕ) (F : VariationDisc X)
    (h α : ℂ → ℂ) (θ : ℝ) : ℂ :=
  α (circlePoint θ) * (h (circlePoint θ) / (wallPower d j a (F.f (circlePoint θ)) : ℂ))

theorem normalizedVelocityScalar_periodic (d : VariationData X q) (j a : ℕ)
    (F : VariationDisc X) (h α : ℂ → ℂ) :
    Function.Periodic (normalizedVelocityScalar d j a F h α) (2 * Real.pi) :=
  circleTrace_periodic (fun ζ => α ζ * (h ζ / (wallPower d j a (F.f ζ) : ℂ)))

theorem normalizedVelocityScalar_continuous {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) :
    Continuous (normalizedVelocityScalar d j a F h α) := by
  have he : normalizedVelocityScalar d j a F h α = (fun θ => α (circlePoint θ) *
      circlePoint ((a : ℝ) * harmonicConjugateTrace (logTrace d j F.f) θ)) := by
    funext θ
    exact congrArg (α (circlePoint θ) * ·)
      (realized_h_normalized_phase d hd j a F hF E l h α fz R hR θ)
  rw [he]
  exact (closedDisc_trace_contDiff hR.2.2.2.2.1).continuous.mul
    (circlePoint_contDiff.continuous.comp (continuous_const.mul
      (harmonicConjugateTrace_contDiff (admissible_logTrace_contDiff hd hF)
        (logTrace_periodic d j F)).continuous))

theorem normalizedVelocityScalar_mul_power {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (h α : ℂ → ℂ) (θ : ℝ) :
    normalizedVelocityScalar d j a F h α θ * (wallPower d j a (F.f (circlePoint θ)) : ℂ) =
      α (circlePoint θ) * h (circlePoint θ) := by
  have hp : wallProduct d j (F.f (circlePoint θ)) ≠ 0 :=
    (admissible_wallProduct_bounds hd hF θ).1.ne'
  have hP : (wallPower d j a (F.f (circlePoint θ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero a hp)
  unfold normalizedVelocityScalar
  field_simp

theorem normalizedVelocityScalar_sq_norm_boundaryDSq {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) :
    boundaryDSq (fun θ (_ : Unit) => star (normalizedVelocityScalar d j a F h α θ) *
      normalizedVelocityScalar d j a F h α θ) ≤
      8 * (1 + ENNReal.ofReal ((a : ℝ) ^ 2) * variationEnergy d j F) := by
  let c := normalizedVelocityScalar d j a F h α
  have hc : Continuous c := normalizedVelocityScalar_continuous hd j a F hF E l h α fz R hR
  have hp := normalizedVelocityScalar_periodic d j a F h α
  have hcn : ∀ θ, ‖c θ‖ ≤ 1 :=
    realized_normalized_multiplier_norm_le d hd j a F hF E l h α fz R hR
  have hstar : Function.Periodic (fun θ => star (c θ)) (2 * Real.pi) := fun θ => congrArg star (hp θ)
  have hb := boundaryDSq_mul_le hc.star hc hstar hp (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 1) (fun θ => by simpa only [norm_star] using hcn θ) hcn
  rw [scalarDSq_conj hc hp] at hb
  norm_num only [one_pow, mul_one, ENNReal.ofReal_ofNat] at hb
  have hD := realized_normalized_multiplier_boundaryDSq_le d hd j a F hF E l h α fz R hR
  norm_num only [ENNReal.ofReal_ofNat] at hD
  calc
    _ ≤ 2 * (2 * (1 + ENNReal.ofReal ((a : ℝ) ^ 2) * variationEnergy d j F)) +
        2 * (2 * (1 + ENNReal.ofReal ((a : ℝ) ^ 2) * variationEnergy d j F)) := by
      apply hb.trans
      gcongr
      · exact hD
      · exact hD
    _ = _ := by ring

end Yau.Blueprint.V03Proof
