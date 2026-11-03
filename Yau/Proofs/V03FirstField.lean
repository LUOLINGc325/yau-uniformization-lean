import Yau.Proofs.V03Charts

/-! Transport of the realization's actual first parameter derivative to the
ambient immersion. This uses the genuine joint cotangent holomorphic family. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def ambientVelocity (d : VariationData X q) (F : VariationDisc X)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (ζ : ℂ) : ComplexVector q :=
  (α ζ * h ζ) • WithLp.toLp 2 (ambientFrame d.G F.f E ζ *ᵥ l ζ)

theorem cotangentHolomorphicOn_ambient_fderiv
    {G : CotangentPoint X.manifold → ComplexVector q} (hG : CotangentHolomorphic G)
    {f : ℂ → CotangentPoint X.manifold} {S : Set ℂ}
    (hf : CotangentHolomorphicOn f S) (hS : S ∈ 𝓝 (0 : ℂ)) :
    fderiv ℂ (fun z => G (f z)) 0 =
      (fderiv ℂ (fun w => G (cotangentChartInv (f 0).1 w))
        (cotangentChart (f 0).1 (f 0))).comp
        (fderiv ℂ (fun z => cotangentChart (f 0).1 (f z)) 0) := by
  obtain ⟨V, hV, h0V, hsrc, hcoord⟩ := hf.2 0 (mem_of_mem_nhds hS)
  have hSV : S ∩ V ∈ 𝓝 (0 : ℂ) := inter_mem hS (hV.mem_nhds h0V)
  have hdiffC : DifferentiableAt ℂ (fun z => cotangentChart (f 0).1 (f z)) 0 :=
    (hcoord.contDiffAt hSV).differentiableAt (by simp)
  have htarget : cotangentChart (f 0).1 (f 0) ∈ cotangentTarget (f 0).1 :=
    cotangentChart_mapsTo (f 0).1 (mem_extChartAt_source (f 0).1)
  have hopen : IsOpen (cotangentTarget (f 0).1) :=
    (isOpen_extChartAt_target (I := ComplexModel n) (f 0).1).prod isOpen_univ
  have hdiffG : DifferentiableAt ℂ (fun w => G (cotangentChartInv (f 0).1 w))
      (cotangentChart (f 0).1 (f 0)) :=
    (hG (f 0).1 _ htarget).differentiableAt (hopen.mem_nhds htarget)
  have heq : (fun z => G (f z)) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => G (cotangentChartInv (f 0).1 (cotangentChart (f 0).1 (f z)))) := by
    filter_upwards [hSV] with z hz
    rw [cotangentChart_left_inv (f 0).1 (hsrc z hz)]
  rw [heq.fderiv_eq]
  exact fderiv_comp 0 hdiffG hdiffC

theorem realizes_ambient_first_derivative
    (d : VariationData X q) (hd : VariationSetup d) (j a : ℕ)
    (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
    (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
    (fz : ℂ → ℂ → CotangentPoint X.manifold) (r : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz r) :
    ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1,
      fderiv ℂ (fun z => d.G (fz z ζ)) 0 1 = ambientVelocity d F E l h α ζ := by
  intro ζ hζ
  have hslice : CotangentHolomorphicOn (fun z => fz z ζ) (Metric.ball (0 : ℂ) r) :=
    hR.1.2.2.comp (contDiff_id.prodMk contDiff_const) (fun z hz => ⟨hz, hζ⟩)
  have hzero : fz 0 ζ = F.f ζ := congrFun hR.1.2.1 ζ
  have hD := cotangentHolomorphicOn_ambient_fderiv hd.2.2.2.2.1.1 hslice
    (Metric.ball_mem_nhds 0 hR.1.1)
  simp only [hzero] at hD
  rw [hD, ContinuousLinearMap.comp_apply, hR.2.2.1 ζ hζ]
  ext b
  rw [← cotangentDG_mulVec]
  simp [ambientVelocity, ambientFrame, Matrix.mulVec_smul, Matrix.mulVec_mulVec]

end Yau.Blueprint.V03Proof
