import Yau.LeafProofs.L12EndpointEnergy

/-! First variation after an arbitrary actual variation of both endpoints. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- The two-endpoint first variation remains valid after any C1 variation
of the actual endpoints. Its covectors are the actual metric momenta. -/
theorem realSegmentEnergy_endpointComposition_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : SmoothMetric M) (d : ℝ) (U : Set (M.Carrier × M.Carrier)) (hU : IsOpen U)
    (P : M.Carrier × M.Carrier → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (f : E → M.Carrier × M.Carrier) (z : E) (a b : M.Carrier)
    (hz : f z ∈ U) (ha : (f z).1 ∈ (chartAt (ComplexVector n) a).source)
    (hb : (f z).2 ∈ (chartAt (ComplexVector n) b).source) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) (realPhaseModel n) 1 P U →
    (∀ u ∈ U, (P u).proj = u.1 ∧ (realGeodesicFlow g (P u) d).proj = u.2) →
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) 1 f z →
    HasFDerivAt (fun u => realSegmentEnergy g d (P (f u)))
      (((-realChartMomentum g a (P (f z))).coprod
        (realChartMomentum g b (realGeodesicFlow g (P (f z)) d))).comp
        (fderiv ℝ (fun u => (chartPt a (f u).1, chartPt b (f u).2)) z)) z := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hP hends hf
  let X : E → ComplexVector n × ComplexVector n :=
    fun u => (chartPt a (f u).1, chartPt b (f u).2)
  let χ : ComplexVector n × ComplexVector n → M.Carrier × M.Carrier :=
    fun u => (chartInv a u.1, chartInv b u.2)
  let Q := P ∘ χ
  have ha' : (f z).1 ∈ (extChartAt (ComplexModel n) a).source := by
    simpa only [extChartAt_source] using ha
  have hb' : (f z).2 ∈ (extChartAt (ComplexModel n) b).source := by
    simpa only [extChartAt_source] using hb
  have hXa : (X z).1 ∈ chartTarget a := (extChartAt (ComplexModel n) a).map_source ha'
  have hXb : (X z).2 ∈ chartTarget b := (extChartAt (ComplexModel n) b).map_source hb'
  have hχ₀ : χ (X z) = f z := Prod.ext
    ((extChartAt (ComplexModel n) a).left_inv ha')
    ((extChartAt (ComplexModel n) b).left_inv hb')
  have hχ : ContMDiffAt 𝓘(ℝ, ComplexVector n × ComplexVector n)
      (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n)) 1 χ (X z) :=
    (((contMDiffAt_chartInv_real a (X z).1 hXa).of_le (by simp)).comp (X z)
      contDiffAt_fst.contMDiffAt).prodMk
      (((contMDiffAt_chartInv_real b (X z).2 hXb).of_le (by simp)).comp (X z)
        contDiffAt_snd.contMDiffAt)
  have hQ : ContMDiffAt 𝓘(ℝ, ComplexVector n × ComplexVector n) (realPhaseModel n) 1 Q (X z) :=
    (hP.contMDiffAt (hU.mem_nhds (hχ₀ ▸ hz))).comp (X z) hχ
  have hQends : ∀ᶠ u in 𝓝 (X z), (Q u).proj = chartInv a u.1 ∧
      (realGeodesicFlow g (Q u) d).proj = chartInv b u.2 := by
    filter_upwards [hχ.continuousAt.eventually (hU.mem_nhds (hχ₀ ▸ hz))] with u hu
    exact hends (χ u) hu
  have henergy := realSegmentEnergy_endpointChart_hasFDerivAt g d a b Q (X z) hXa hXb hQ hQends
  have hca : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1
      (chartPt a) (f z).1 := contMDiffAt_extChartAt' ha
  have hcb : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1
      (chartPt b) (f z).2 := contMDiffAt_extChartAt' hb
  have hX : ContDiffAt ℝ 1 X z :=
    ((hca.comp z hf.fst).contDiffAt).prodMk
      ((hcb.comp z hf.snd).contDiffAt)
  have hcomp := henergy.comp z (hX.differentiableAt (by simp)).hasFDerivAt
  have hN₀ : ∀ᶠ u in 𝓝 z, (f u).1 ∈ (chartAt (ComplexVector n) a).source :=
    (hf.continuousAt.fst).eventually ((chartAt (ComplexVector n) a).open_source.mem_nhds ha)
  have hN₁ : ∀ᶠ u in 𝓝 z, (f u).2 ∈ (chartAt (ComplexVector n) b).source :=
    (hf.continuousAt.snd).eventually ((chartAt (ComplexVector n) b).open_source.mem_nhds hb)
  have heq : (realSegmentEnergy g d ∘ Q) ∘ X =ᶠ[𝓝 z]
      (fun u => realSegmentEnergy g d (P (f u))) := by
    filter_upwards [hN₀, hN₁] with u hu hv
    dsimp only [Q, χ, X, Function.comp_apply]
    have hau : chartInv a (chartPt a (f u).1) = (f u).1 :=
      (extChartAt (ComplexModel n) a).left_inv (by simpa only [extChartAt_source] using hu)
    have hbu : chartInv b (chartPt b (f u).2) = (f u).2 :=
      (extChartAt (ComplexModel n) b).left_inv (by simpa only [extChartAt_source] using hv)
    rw [hau, hbu]
  have hQ₀ : Q (X z) = P (f z) := congrArg P hχ₀
  rw [hQ₀] at hcomp
  exact heq.hasFDerivAt_iff.mp hcomp

end Yau.LeafProofs.L12Aux
