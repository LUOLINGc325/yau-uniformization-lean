import Yau.Proofs.V03LogRadial
import Yau.Proofs.V03BaseRadial
import Yau.Proofs.V03GaussRadial
import Yau.Proofs.V03ClockRadial
import Yau.Proofs.V03EnergyIdentity

/-! Radial convergence of the entire original computed energy, with its
logarithmic Fourier summand and justified finite real conversions. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem radial_energy_ne_top_eventually {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    ∀ᶠ r : ℝ in 𝓝[Set.Icc 0 1] 1, variationEnergy d j (radialVariationDisc F r) ≠ ⊤ := by
  have hG : CotangentImmersion d.G := hd.2.2.2.2.1
  filter_upwards [admissible_logWall_radial_contDiff_eventually hd hF] with r hr
  have hrad := cotangentDisc_radial hF.1 hr.1.1 hr.1.2
  have hw := clock_contDiff_radial hF.2.1 hr.1.1 hr.1.2
  have hC1 := complex_C1_radial_trace hr.1 hr.2
  have hlog := boundaryDSq_ne_top_of_periodic_C1 hC1.1 hC1.2.1 hC1.2.2
  have hbase := discArea_ne_top_of_cotangentDisc X.metric hrad
  have hamb := euclideanArea_ne_top_of_closedDisc (cotangentDisc_ambient_contDiffOn hrad hG.1)
  have hclock := clockArea_ne_top_of_closedDisc (F := radialVariationDisc F r) hw
  simp only [variationEnergy, ENNReal.add_ne_top]
  exact ⟨⟨⟨⟨hbase, hamb⟩, ENNReal.ofReal_ne_top⟩, hclock⟩, hlog⟩

theorem radial_energy_toReal_tendsto {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    Tendsto (fun r : ℝ => (variationEnergy d j (radialVariationDisc F r)).toReal)
      (𝓝[Set.Icc 0 1] 1) (𝓝 (variationEnergy d j F).toReal) := by
  have hG : CotangentImmersion d.G := hd.2.2.2.2.1
  have hbase := (ENNReal.tendsto_toReal (discArea_ne_top_of_cotangentDisc X.metric hF.1)).comp
    (discArea_radial_tendsto X.metric hF.1)
  have hH := cotangentDisc_ambient_contDiffOn hF.1 hG.1
  have hamb := (ENNReal.tendsto_toReal (euclideanArea_ne_top_of_closedDisc hH)).comp
    (euclideanArea_radial_tendsto hH)
  have hgauss := gaussArea_radial_tendsto hG hF.1
  have hclock := clockArea_radial_toReal_tendsto hF.2.1
  have hlog := logSeminorm_radial_toReal_tendsto hd hF
  have hsum := (((hbase.add hamb).add hgauss).add hclock).add hlog
  have hsplit := variationEnergy_toReal_actual hG j hF.2.2.2.2.2.2.2.2
  dsimp only [spatialArea] at hsplit
  rw [← hsplit] at hsum
  apply hsum.congr'
  filter_upwards [radial_energy_ne_top_eventually hd hF] with r hr
  exact (variationEnergy_toReal_actual hG j hr).symm

theorem radial_admissible_eventually {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    ∀ᶠ r : ℝ in 𝓝[Set.Icc 0 1] 1, AdmissibleVariationDisc d j (radialVariationDisc F r) := by
  filter_upwards [self_mem_nhdsWithin, radial_boundaryRegion_eventually hd hF,
    radial_energy_ne_top_eventually hd hF] with r hr hb he
  obtain ⟨hf, hw, hw0, hs, hsT, hc, ht, _, _⟩ := hF
  refine ⟨cotangentDisc_radial hf hr.1 hr.2, clock_contDiff_radial hw hr.1 hr.2,
    ?_, hs, hsT, ?_, ?_, hb, he⟩
  · simpa only [radial_clock_center] using hw0
  · simpa only [radialVariationDisc, Complex.ofReal_mul, mul_zero] using hc
  · intro ζ hζ
    exact ht ((r : ℂ) * ζ) (radial_maps_closedBall hr.1 hr.2 hζ)

end Yau.Blueprint.V03Proof
