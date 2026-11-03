import Yau.Proofs.V02SprayCoordinates

/-! The original test evaluated along the actual spray is jointly smooth
at every point where the initial and terminal chart values are valid. -/

open scoped Manifold Topology ContDiff
open Metric Set Filter

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof

abbrev SprayCenterData (n b : ℕ) := (CotangentCoord n × ℝ) × (ℂ × (Fin b → ℂ))

variable {n b q : ℕ} {X : KahlerManifold n}

def sprayTestParameter (p : ℂ × SprayCenterData n b) :
    CotangentCoord n × (Fin b → ℂ) :=
  (p.2.1.1, fun k => p.1 * p.2.2.1 * p.2.2.2 k)

def nativeSprayTest (d : VariationData X q)
    (Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) →
      NativeCotangentPoint X.manifold) (p : ℂ × SprayCenterData n b) : ℝ :=
  d.test (Ψ (NativeCotangentPoint.mk (cotangentChartInv d.chart p.2.1.1),
    (sprayTestParameter p).2)).val p.2.1.2

theorem sprayTestParameter_contDiff :
    ContDiff ℝ ∞ (sprayTestParameter (n := n) (b := b)) := by
  apply ContDiff.prodMk
  · exact contDiff_snd.fst.fst
  · apply contDiff_pi.mpr
    intro k
    have hk : ContDiff ℝ ∞ (fun p : ℂ × SprayCenterData n b => p.2.2.2 k) := by
      simpa only [Function.comp_def] using
        ((contDiff_apply ℝ (fun _ : Fin b => ℂ) k).comp
          (contDiff_snd.snd.snd : ContDiff ℝ ∞
            (fun p : ℂ × SprayCenterData n b => p.2.2.2)))
    exact (contDiff_fst.mul contDiff_snd.snd.fst).mul hk

theorem nativeSprayTest_contDiffAt
    {d : VariationData X q}
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) →
      NativeCotangentPoint X.manifold}
    {U : Set (NativeCotangentPoint X.manifold)} {R : ℝ} (hU : IsOpen U)
    (hΨ : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ Ψ (U ×ˢ ball 0 R))
    {V : Set (CotangentCoord n × ℝ)} (hV : IsOpen V)
    (htest : ContDiffOn ℝ ∞
      (fun v : CotangentCoord n × ℝ => d.test (cotangentChartInv d.chart v.1) v.2) V)
    {p : ℂ × SprayCenterData n b}
    (hu : p.2.1.1 ∈ cotangentTarget d.chart)
    (hI : NativeCotangentPoint.mk (cotangentChartInv d.chart p.2.1.1) ∈ U)
    (hτ : (sprayTestParameter p).2 ∈ ball (0 : Fin b → ℂ) R)
    (hsource : (Ψ (NativeCotangentPoint.mk (cotangentChartInv d.chart p.2.1.1),
      (sprayTestParameter p).2)).val ∈ cotangentSource d.chart)
    (hT : (cotangentChart d.chart
      (Ψ (NativeCotangentPoint.mk (cotangentChartInv d.chart p.2.1.1),
        (sprayTestParameter p).2)).val, p.2.1.2) ∈ V) :
    ContDiffAt ℝ ∞ (nativeSprayTest d Ψ) p := by
  let D : CotangentCoord n × (Fin b → ℂ) → NativeCotangentPoint X.manifold :=
    fun v => Ψ (NativeCotangentPoint.mk (cotangentChartInv d.chart v.1), v.2)
  have hcoord := (nativeSprayCoordinate_contDiffAt hU hΨ d.chart
    (u := p.2.1.1) (τ := (sprayTestParameter p).2) hu hI hτ hsource).restrict_scalars ℝ
  have hmap : ContDiffAt ℝ ∞ (fun v : ℂ × SprayCenterData n b =>
      (cotangentChart d.chart (D (sprayTestParameter v)).val, v.2.1.2)) p :=
    by
      simpa only [Function.comp_def, D, sprayTestParameter] using
        (hcoord.comp p (sprayTestParameter_contDiff (n := n) (b := b)).contDiffAt).prodMk
          (contDiff_snd.fst.snd : ContDiff ℝ ∞
            (fun v : ℂ × SprayCenterData n b => v.2.1.2)).contDiffAt
  have hchart := (htest.contDiffAt (hV.mem_nhds hT)).comp p hmap
  have hInv : ContinuousAt
      (fun u => NativeCotangentPoint.mk (cotangentChartInv d.chart u)) p.2.1.1 :=
    (nativeCotangentChartHomeomorph d.chart).continuousOn_symm.continuousAt
      ((nativeCotangentChartHomeomorph d.chart).open_target.mem_nhds hu)
  have hdec : ContinuousAt D (sprayTestParameter p) := by
    have hi : ContinuousAt
        (fun v : CotangentCoord n × (Fin b → ℂ) =>
          (NativeCotangentPoint.mk (cotangentChartInv d.chart v.1), v.2))
        (sprayTestParameter p) :=
      (hInv.comp_of_eq (continuous_fst.continuousAt : ContinuousAt
        (Prod.fst : CotangentCoord n × (Fin b → ℂ) → CotangentCoord n)
        (sprayTestParameter p)) rfl).prodMk
          (continuous_snd.continuousAt : ContinuousAt
            (Prod.snd : CotangentCoord n × (Fin b → ℂ) → Fin b → ℂ)
            (sprayTestParameter p))
    have hψ : ContinuousAt Ψ (NativeCotangentPoint.mk
        (cotangentChartInv d.chart p.2.1.1), (sprayTestParameter p).2) :=
      by
        have hmem : (NativeCotangentPoint.mk (cotangentChartInv d.chart p.2.1.1),
            (sprayTestParameter p).2) ∈ U ×ˢ ball (0 : Fin b → ℂ) R := ⟨hI, hτ⟩
        exact (hΨ.contMDiffAt ((hU.prod isOpen_ball).mem_nhds hmem)).continuousAt
    exact hψ.comp_of_eq hi rfl
  have hnear : ∀ᶠ v in 𝓝 p, (D (sprayTestParameter v)).val ∈ cotangentSource d.chart :=
    (hdec.comp_of_eq (sprayTestParameter_contDiff (n := n) (b := b)).continuous.continuousAt rfl).preimage_mem_nhds
      ((nativeCotangentChartHomeomorph d.chart).open_source.mem_nhds hsource)
  apply hchart.congr_of_eventuallyEq
  filter_upwards [hnear] with v hv
  exact congrArg (fun y => d.test y v.2.1.2) (cotangentChart_left_inv d.chart hv).symm

end Yau.Blueprint.V02Proof
