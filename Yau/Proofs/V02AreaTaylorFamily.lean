import Yau.Proofs.V02FlowCoordinates
import Yau.Proofs.V02AreaTaylorDensity

/-! The literal native spray family and smoothness of its original spatial
density. The clock, frame, test and penalties do not enter this construction. -/

open scoped Topology ContDiff Matrix Manifold

noncomputable section
namespace Yau.Blueprint.V02AreaTaylorProof
open Yau Yau.Blueprint V03Proof V02FlowProof

variable {n q b : ℕ} {X : KahlerManifold n}

def sprayFamily
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold)
    (f : ℂ → CotangentPoint X.manifold) (h : ℂ → ℂ) (c : ℂ → ComplexVector b)
    (z ζ : ℂ) : CotangentPoint X.manifold :=
  (Ψ (NativeCotangentPoint.mk (f ζ), fun k => z * h ζ * c ζ k)).val

theorem sprayFamily_holomorphic
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) → NativeCotangentPoint X.manifold}
    {U : Set (NativeCotangentPoint X.manifold)} {R r : ℝ}
    (hΨ : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ Metric.ball 0 R))
    {f : ℂ → CotangentPoint X.manifold} (hf : CotangentDisc f)
    (hfU : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, NativeCotangentPoint.mk (f ζ) ∈ U)
    {h : ℂ → ℂ} (hh : ContDiffOn ℂ ∞ h (Metric.closedBall 0 1))
    {c : ℂ → ComplexVector b} (hc : ContDiffOn ℂ ∞ c (Metric.closedBall 0 1))
    (hparam : ∀ p ∈ Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1,
      (fun k => p.1 * h p.2 * c p.2 k) ∈ Metric.ball (0 : Fin b → ℂ) R) :
    CotangentHolomorphicOn (fun p : ℂ × ℂ => sprayFamily Ψ f h c p.1 p.2)
      (Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1) := by
  let S := Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1
  have hFn : ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CotangentCoord n) ∞
      (fun p : ℂ × ℂ => NativeCotangentPoint.mk (f p.2)) S :=
    (cotangentDisc_native_contMDiffOn hf).comp contDiff_snd.contDiffOn.contMDiffOn (fun p hp => hp.2)
  have hτ : ContDiffOn ℂ ∞ (fun p : ℂ × ℂ => fun k => p.1 * h p.2 * c p.2 k) S := by
    apply contDiffOn_pi.mpr
    intro k
    exact (contDiffOn_fst.mul (hh.comp contDiffOn_snd (fun p hp => hp.2))).mul
      (((contDiffOn_piLp 2).mp hc k).comp contDiffOn_snd (fun p hp => hp.2))
  exact native_contMDiffOn_cotangentHolomorphicOn
    (hΨ.comp (hFn.prodMk hτ.contMDiffOn) (fun p hp => ⟨hfU _ hp.2, hparam p hp⟩))

theorem spatialDensity_joint_contDiffOn {d : VariationData X q}
    (hG : CotangentImmersion d.G) {f : ℂ × ℂ → CotangentPoint X.manifold}
    {U : Set ℂ} (hU : IsOpen U)
    (hf : CotangentHolomorphicOn f (U ×ˢ Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (fun p : ℂ × ℂ => spatialDensity d (fun ζ => f (p.1, ζ)) p.2)
      (U ×ˢ Metric.closedBall (0 : ℂ) 1) := by
  have hS : UniqueDiffOn ℂ (U ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    hU.uniqueDiffOn.prod uniqueDiffOn_complex_closedDisc
  have hBase := twoFormCoefficient_contDiffOn (jointBaseTwoForm_contDiffOn X.metric hf hS)
    ((0, 1) : ℂ × ℂ) ((0, Complex.I) : ℂ × ℂ)
  have hGauss := twoFormCoefficient_contDiffOn (jointGaussTwoForm_contDiffOn hG hf hS)
    ((0, 1) : ℂ × ℂ) ((0, Complex.I) : ℂ × ℂ)
  have hAmbient := cotangentHolomorphicOn_ambient_contDiffOn hf hG.1
  have hD := (hAmbient.fderivWithin hS (m := ∞) (by simp)).clm_apply
    (contDiffOn_const (c := ((0, 1) : ℂ × ℂ)))
  have hEucl := (contDiffOn_const (c := (2 : ℝ))).mul ((hD.restrict_scalars ℝ).norm_sq ℂ)
  apply ((hBase.add hEucl).add hGauss).congr
  intro p hp
  rw [jointBaseTwoForm_spatial_diagonal X.metric.form hf hp.1 hp.2,
    jointGaussTwoForm_spatial_diagonal hG hf hp.1 hp.2]
  change spatialDensity d (fun ζ => f (p.1, ζ)) p.2 =
    baseDensityWithin X.metric.form (fun ζ => f (p.1, ζ)) p.2 +
      2 * ‖fderivWithin ℂ (fun q => d.G (f q)) (U ×ˢ Metric.closedBall 0 1) p (0, 1)‖ ^ 2 +
        gaussDensityWithin d.G (fun ζ => f (p.1, ζ)) p.2
  unfold spatialDensity closedDiscDerivative
  rw [fderivWithin_complex_disc_slice hp.1 hp.2
    ((hAmbient.differentiableOn (by simp)) p hp) 1]

theorem spatialArea_family_contDiffOn {d : VariationData X q}
    (hG : CotangentImmersion d.G) {f : ℂ × ℂ → CotangentPoint X.manifold}
    {U : Set ℂ} (hU : IsOpen U)
    (hf : CotangentHolomorphicOn f (U ×ˢ Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (fun z => spatialArea d (fun ζ => f (z, ζ))) U := by
  have hb := baseFamilyArea_contDiffOn X.metric hU hf
  have hg := gaussFamilyArea_contDiffOn hG hU hf
  have he := euclideanFamilyArea_contDiffOn hU (cotangentHolomorphicOn_ambient_contDiffOn hf hG.1)
  exact (hb.add he).add hg

end Yau.Blueprint.V02AreaTaylorProof
