import Yau.Proofs.V03AreaFamilySmoothness
import Yau.Proofs.V03EuclideanAreaVariation
import Yau.Proofs.V03LogEnergySmoothness
import Yau.Proofs.V03EnergyIdentity

/-! The actual computed full energy mixed derivative is the sum of its
four genuine spatial and logarithmic mixed derivatives; the original clock is fixed. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem realized_energy_mixed_split {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) {j a : ℕ}
    {F : VariationDisc X} {E : ℂ → CotangentMatrix n} {l : ℂ → CotangentIndex n → ℂ}
    {h α : ℂ → ℂ} {fz : ℂ → ℂ → CotangentPoint X.manifold} {R : ℝ}
    (hR : RealizesFirstField d j a F E l h α fz R) :
    mixedReal (fun z => (variationEnergy d j {F with f := fz z}).toReal) =
      mixedReal (fun z => (discArea X.metric.form (fun ζ => (fz z ζ).1)).toReal) +
        mixedReal (fun z => (euclideanArea (fun ζ => d.G (fz z ζ))).toReal) +
          mixedReal (fun z => gaussArea d.G (fz z)) +
            mixedReal (fun z => (scalarDSq (logTrace d j (fz z))).toReal) := by
  have h0 : Metric.ball (0 : ℂ) R ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 hR.1.1
  have hBase := baseFamilyArea_contDiffOn X.metric (f := fun p : ℂ × ℂ => fz p.1 p.2)
    Metric.isOpen_ball hR.1.2.2
  have hGauss := gaussFamilyArea_contDiffOn hd.2.2.2.2.1 (f := fun p : ℂ × ℂ => fz p.1 p.2)
    Metric.isOpen_ball hR.1.2.2
  have hAmbient := cotangentHolomorphicOn_ambient_contDiffOn hR.1.2.2 hd.2.2.2.2.1.1
  have hEucl := euclideanFamilyArea_contDiffOn (H := fun p : ℂ × ℂ => d.G (fz p.1 p.2))
    Metric.isOpen_ball hAmbient
  have hLog := family_logEnergy_contDiffOn hd j hR.1 hR.2.1
  have hb : ContDiffAt ℝ 2 (fun z => ((discArea X.metric.form (fun ζ => (fz z ζ).1)).toReal : ℂ)) 0 :=
    ((hBase.contDiffAt h0).of_le (by simp)).continuousLinearMap_comp Complex.ofRealCLM
  have he : ContDiffAt ℝ 2 (fun z => ((euclideanArea (fun ζ => d.G (fz z ζ))).toReal : ℂ)) 0 :=
    ((hEucl.contDiffAt h0).of_le (by simp)).continuousLinearMap_comp Complex.ofRealCLM
  have hg : ContDiffAt ℝ 2 (fun z => (gaussArea d.G (fz z) : ℂ)) 0 :=
    ((hGauss.contDiffAt h0).of_le (by simp)).continuousLinearMap_comp Complex.ofRealCLM
  have hl : ContDiffAt ℝ 2 (fun z => ((scalarDSq (logTrace d j (fz z))).toReal : ℂ)) 0 :=
    ((hLog.contDiffAt h0).of_le (by simp)).continuousLinearMap_comp Complex.ofRealCLM
  have hbe : ContDiffAt ℝ 2 (fun z =>
      (((discArea X.metric.form (fun ζ => (fz z ζ).1)).toReal +
        (euclideanArea (fun ζ => d.G (fz z ζ))).toReal : ℝ) : ℂ)) 0 := by
    simpa only [Complex.ofReal_add] using hb.add he
  have hs : ContDiffAt ℝ 2 (fun z => (spatialArea d (fz z) : ℂ)) 0 := by
    simpa only [spatialArea, Complex.ofReal_add] using (hb.add he).add hg
  rw [realized_energy_mixed_actual hd.2.2.2.2.1 hR]
  have hcomm : (fun z => spatialArea d (fz z) + (clockArea F).toReal +
      (scalarDSq (logTrace d j (fz z))).toReal) =
      (fun z => (spatialArea d (fz z) + (scalarDSq (logTrace d j (fz z))).toReal) +
        (clockArea F).toReal) := by funext z; ring
  rw [hcomm, mixedReal_add_const, mixedReal_add hs hl]
  change mixedReal (fun z => (discArea X.metric.form (fun ζ => (fz z ζ).1)).toReal +
      (euclideanArea (fun ζ => d.G (fz z ζ))).toReal + gaussArea d.G (fz z)) + _ = _
  rw [mixedReal_add hbe hg, mixedReal_add hb he]

end Yau.Blueprint.V03Proof
