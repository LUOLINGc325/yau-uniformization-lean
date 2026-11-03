import Yau.Proofs.V03LogFieldContractions

/-! The actual pointwise logarithmic mixed jet is the quadratic
contraction of the smooth cleared tensor with the original normalized field. -/

open scoped Topology ContDiff Matrix Manifold

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem realized_logMixedJet_cleared {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a)
    (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) (θ : ℝ) :
    mixedReal (fun z => logTrace d j (fz z) θ) =
      (star (normalizedVelocityScalar d j a F h α θ) * normalizedVelocityScalar d j a F h α θ *
        (star (boundaryColumnField d F E l θ) ⬝ᵥ
          (ambientLogTensor d j a (F.f (circlePoint θ)) *ᵥ boundaryColumnField d F E l θ))).re := by
  rw [realized_logTrace_mixed hd j a F hF E l h α fz R hR θ,
    ambientLogTensor_boundary_contract hd j a ha F hF E l θ]
  have hb := logWall_chart_contDiffAt hd j (F.f (circlePoint θ)).1
    (mem_extChartAt_source (F.f (circlePoint θ)).1)
    (admissible_wallProduct_bounds hd hF θ).1.ne'
  rw [cotangent_levi_contraction hb, cotangent_levi_contraction hb, quadratic_complex_smul]
  have hp := normalizedVelocityScalar_mul_power hd j a F hF h α θ
  rw [← hp]
  simp only [star_mul, Complex.star_def, map_mul, Complex.conj_ofReal]
  congr 1
  ring

end Yau.Blueprint.V03Proof
