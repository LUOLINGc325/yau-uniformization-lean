import Yau.Proofs.V03CotangentScalarMixed
import Yau.Proofs.V03WirtingerDirections
import Yau.Proofs.V03SpatialHessianTransport

/-! Scalar mixed variations use the original centered chart, frame and
first field. The parameter acceleration cancels by holomorphicity. -/

open scoped Topology ContDiff Matrix Manifold
open Filter

noncomputable section
namespace Yau.Blueprint.V02CostMixedProof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem quadValue_frame (H E : CotangentMatrix n) (v : CotangentIndex n → ℂ) :
    quadValue H (E *ᵥ v) = quadValue (Eᴴ * H * E) v := by
  unfold quadValue
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem quadValue_smul (H : CotangentMatrix n) (v : CotangentIndex n → ℂ) (c : ℂ) :
    quadValue H (c • v) = ‖c‖ ^ 2 * quadValue H v := by
  unfold quadValue
  simp only [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  have hcc : c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    simp [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
  rw [← mul_assoc, hcc, Complex.re_ofReal_mul]

theorem quadValue_real_smul (H : CotangentMatrix n) (v : CotangentIndex n → ℂ) (t : ℝ) :
    quadValue ((t : ℂ) • H) v = t * quadValue H v := by
  simp only [quadValue, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Complex.re_ofReal_mul]

theorem scalar_chart_contDiffAt_centered (b : CotangentPoint X.manifold → ℝ)
    (x : Pt X) {y : CotangentPoint X.manifold} (hy : y ∈ cotangentSource x)
    (hb : ContDiffAt ℝ 2 (fun w => b (cotangentChartInv x w)) (cotangentChart x y)) :
    ContDiffAt ℝ 2 (fun w => b (cotangentChartInv y.1 w)) (cotangentChart y.1 y) := by
  let z0 := cotangentChart y.1 y
  let T : CotangentCoord n → CotangentCoord n := fun z =>
    cotangentChart x (cotangentChartInv y.1 z)
  have hself : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hz : z0 ∈ cotangentTarget y.1 := cotangentChart_mapsTo y.1 hself
  have hz' : chartInv y.1 z0.1 ∈ (extChartAt (ComplexModel n) x).source := by
    have he : chartInv y.1 z0.1 = y.1 := (extChartAt (ComplexModel n) y.1).left_inv hself
    rw [he]
    exact hy
  have hT : ContDiffAt ℂ ∞ T z0 := cotangentChartTransition_contDiffAt y.1 x hz hz'
  have hTz : T z0 = cotangentChart x y := by
    dsimp only [T, z0]
    rw [cotangentChart_left_inv y.1 hself]
  have hbf : ContDiffAt ℝ 2 (fun w => b (cotangentChartInv x w)) (T z0) := by
    rw [hTz]
    exact hb
  apply (hbf.comp z0 ((hT.of_le (by simp)).restrict_scalars ℝ)).congr_of_eventuallyEq
  filter_upwards [(isOpen_cotangentChartOverlap y.1 x).mem_nhds ⟨hz, hz'⟩] with z hzone
  exact congrArg b (cotangentChart_left_inv x hzone.2).symm

theorem realized_scalar_mixed {d : VariationData X q} {j a : ℕ}
    {F : VariationDisc X} {E : ℂ → CotangentMatrix n} {l : ℂ → CotangentIndex n → ℂ}
    {h α : ℂ → ℂ} {fz : ℂ → ℂ → CotangentPoint X.manifold} {r : ℝ}
    (hR : RealizesFirstField d j a F E l h α fz r) {ζ : ℂ}
    (hζ : ζ ∈ Metric.closedBall 0 1) (b : CotangentPoint X.manifold → ℝ)
    (hb : ContDiffAt ℝ 2 (fun w => b (cotangentChartInv (F.f ζ).1 w))
      (cotangentChart (F.f ζ).1 (F.f ζ))) :
    mixedReal (fun z => b (fz z ζ)) =
      ‖α ζ * h ζ‖ ^ 2 * quadValue ((E ζ)ᴴ * spatialHessian b (F.f ζ) * E ζ) (l ζ) := by
  have hs : CotangentHolomorphicOn (fun z => fz z ζ) (Metric.ball (0 : ℂ) r) :=
    hR.1.2.2.comp (contDiff_id.prodMk contDiff_const) (fun z hz => ⟨hz, hζ⟩)
  have hzero : fz 0 ζ = F.f ζ := congrFun hR.1.2.1 ζ
  have hb' : ContDiffAt ℝ 2 (fun w => b (cotangentChartInv (fz 0 ζ).1 w))
      (cotangentChart (fz 0 ζ).1 (fz 0 ζ)) := by simpa only [hzero] using hb
  have hm := cotangentHolomorphicOn_scalar_mixed hs (Metric.ball_mem_nhds 0 hR.1.1) hb'
  rw [hzero, hR.2.2.1 ζ hζ, cotangent_levi_contraction hb] at hm
  rw [hm]
  change quadValue (spatialHessian b (F.f ζ)) ((α ζ * h ζ) • (E ζ *ᵥ l ζ)) = _
  rw [quadValue_smul, quadValue_frame]

end Yau.Blueprint.V02CostMixedProof
