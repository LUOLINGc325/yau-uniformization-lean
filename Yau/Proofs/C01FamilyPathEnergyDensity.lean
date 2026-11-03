import Yau.Proofs.C01PathEnergy
import Yau.Proofs.C01MetricFamilyPathQuadratic
import Yau.LeafProofs.L12NormalDistance

/-! Joint regularity of the genuine actual path-energy density.
The local chart calculation is reconstructed from canonical Ae0dbe
L23LocalDistanceSupportEnergyDensity, SHA 7ae05667e9b4e00b26b793ac60f97142cf1f5f9a020f30fe6335dc247698e2d2.
Its only project inputs here are the displayed already prepared modules;
no pending completeness geometry parent is imported. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold
namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem actualPathSpeed_sq_eq_chartDerivative
    (h : HermitianField M) (γ : ℝ → M.Carrier) (c : M.Carrier) (t : ℝ)
    (hc : γ t ∈ (chartAt (ComplexVector n) c).source) (V : ComplexVector n) :
    letI := manifold_realSmooth M
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) γ t →
    HasDerivAt (fun u => chartPt c (γ u)) V t →
    actualPathSpeed h γ t ^ 2 = realMetricInChart h c (chartPt c (γ t)) V V := by
  letI := manifold_realSmooth M
  intro hγ HD
  have HV := realCurveVelocity_coords_of_hasDerivAt γ t c V hc hγ HD
  have HM := realMetricInChart_tangentCoords h c (γ t) hc (realCurveVelocity γ t) (realCurveVelocity γ t)
  rw [HV] at HM
  rw [actualPathSpeed_sq]
  exact HM.symm

def familyActualPathEnergyDensity {E : Type*} (h : ℝ → HermitianField M)
    (F : E → ℝ → M.Carrier) (p : (E × ℝ) × ℝ) : ℝ :=
  actualPathSpeed (h p.1.2) (F p.1.1) p.2 ^ 2

theorem familyActualPathEnergyDensity_contDiffOn_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ → HermitianField M) (I : Set ℝ) (hI : IsOpen I) (hh : MetricFamilySmooth h I)
    (F : E → ℝ → M.Carrier) (U : Set E) (J : Set ℝ) (hU : IsOpen U) (hJ : IsOpen J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ComplexVector n) 3 (Function.uncurry F) (U ×ˢ J) →
    ContDiffOn ℝ 2 (familyActualPathEnergyDensity h F) ((U ×ˢ I) ×ˢ J) := by
  letI := manifold_realSmooth M
  intro hF p hp
  let c := F p.1.1 p.2
  let D := U ×ˢ J
  let K := D ∩ (Function.uncurry F) ⁻¹' (chartAt (ComplexVector n) c).source
  have hD : IsOpen D := hU.prod hJ
  have hK : IsOpen K := hF.continuousOn.isOpen_inter_preimage hD (chartAt (ComplexVector n) c).open_source
  have hpK : (p.1.1,p.2) ∈ K := ⟨⟨hp.1.1,hp.2⟩,mem_chart_source _ _⟩
  let f := fun q : E × ℝ => chartPt c (F q.1 q.2)
  have Hf : ContDiffOn ℝ 3 f K := by
    intro q hq
    have HF : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ComplexVector n) 3 (Function.uncurry F) q :=
      (hF q hq.1).contMDiffAt (hD.mem_nhds hq.1)
    have HC : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3 (chartPt c) (F q.1 q.2) := by
      convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := 3)
        (x := c) (x' := F q.1 q.2) hq.2) using 1
    exact (HC.comp q HF).contDiffAt.contDiffWithinAt
  let V := fun q : E × ℝ => fderiv ℝ f q (0,1)
  have HV : ContDiffOn ℝ 2 V K := (Hf.fderiv_of_isOpen hK (by norm_num)).clm_apply contDiffOn_const
  let π : (E × ℝ) × ℝ → E × ℝ := fun z => (z.1.1,z.2)
  have Hπ : ContDiff ℝ ∞ π := contDiff_fst.fst.prodMk contDiff_snd
  have Hπ₂ : ContDiffAt ℝ 2 π p := Hπ.contDiffAt.of_le (by simp)
  have Hf₂ : ContDiffAt ℝ 2 f (π p) := (Hf.contDiffAt (hK.mem_nhds hpK)).of_le (by norm_num)
  have HfAt : ContDiffAt ℝ 2 (fun z => f (π z)) p :=
    Hf₂.comp p Hπ₂
  have HV₂ : ContDiffAt ℝ 2 V (π p) := HV.contDiffAt (hK.mem_nhds hpK)
  have HVAt : ContDiffAt ℝ 2 (fun z => V (π z)) p :=
    HV₂.comp p Hπ₂
  have Harg : ContDiffAt ℝ 2 (fun z : (E × ℝ) × ℝ => (f (π z),z.1.2)) p :=
    HfAt.prodMk (contDiffAt_fst.snd)
  have Hmetric := metricFamily_realMetricInChart_contDiffOn h I hh c
  have Htarget : (f (π p),p.1.2) ∈ chartTarget c ×ˢ I :=
    ⟨mem_extChartAt_target c,hp.1.2⟩
  have HG₂ : ContDiffAt ℝ 2 (fun q : ComplexVector n × ℝ => realMetricInChart (h q.2) c q.1) (f (π p),p.1.2) :=
    (Hmetric.contDiffAt (((isOpen_extChartAt_target (I := ComplexModel n) c).prod hI).mem_nhds Htarget)).of_le (by simp)
  have HG : ContDiffAt ℝ 2 (fun z : (E × ℝ) × ℝ => realMetricInChart (h z.1.2) c (f (π z))) p :=
    HG₂.comp (f := fun z : (E × ℝ) × ℝ => (f (π z),z.1.2))
      (g := fun q : ComplexVector n × ℝ => realMetricInChart (h q.2) c q.1) p Harg
  have Hdensity := (HG.clm_apply HVAt).clm_apply HVAt
  apply ContDiffAt.contDiffWithinAt
  apply Hdensity.congr_of_eventuallyEq
  have Hnear : ∀ᶠ z in 𝓝 p, π z ∈ K := Hπ.continuous.continuousAt.preimage_mem_nhds (hK.mem_nhds hpK)
  filter_upwards [Hnear] with z hz
  have HFz : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ComplexVector n) 3 (Function.uncurry F) (π z) :=
    (hF (π z) hz.1).contMDiffAt (hD.mem_nhds hz.1)
  have Hfiber : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 (F z.1.1) z.2 :=
    (HFz.comp z.2 ((contDiffAt_const.prodMk contDiffAt_id).contMDiffAt)).of_le (by norm_num)
  have HD := ((Hf.contDiffAt (hK.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt z.2
    ((hasDerivAt_const z.2 z.1.1).prodMk (hasDerivAt_id z.2))
  exact actualPathSpeed_sq_eq_chartDerivative (h z.1.2) (F z.1.1) c z.2 hz.2 (V (π z))
    (Hfiber.mdifferentiableAt (by norm_num)) HD

end Yau.NodeProofs.C01Aux
