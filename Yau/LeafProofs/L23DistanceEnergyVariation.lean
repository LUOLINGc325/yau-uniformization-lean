import Yau.LeafProofs.L23DistanceEnergyPairing

/-! First and second variations of the true energy density in actual coordinates. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
open L12Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem mapDirection_congr {f g : E → V} {p : E} (heq : f=ᶠ[𝓝 p] g) (a : E) :
    mapDirection f a p=mapDirection g a p := by
  unfold mapDirection
  rw [heq.fderiv_eq]

theorem mapCovariantD_congr (Γ : V → V →L[ℝ] V →L[ℝ] V) (Z : E → V)
    {f g : E → V} {p : E} (heq : f=ᶠ[𝓝 p] g) (a : E) :
    mapCovariantD Γ Z a f p=mapCovariantD Γ Z a g p := by
  simp only [mapCovariantD,mapDirection_congr heq a,heq.self_of_nhds]

theorem mapDirection_const_mul (f : E → ℝ) {p : E} (hf : DifferentiableAt ℝ f p) (c : ℝ) (a : E) :
    mapDirection (fun q => c*f q) a p=c*mapDirection f a p := by
  unfold mapDirection
  rw [fderiv_const_mul hf]
  rfl

variable {n : ℕ} {M : ComplexManifold n}

theorem mapMetricDensity_secondDirection (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (Z W : E → ComplexVector n) {p : E} (hz : Z p∈chartTarget c)
    (hZ : ContDiffAt ℝ 2 Z p) (hW : ContDiffAt ℝ 2 W p) (a : E) :
    mapDirection (mapDirection (fun q => realMetricInChart h c (Z q) (W q) (W q)) a) a p=
      2*realMetricInChart h c (Z p)
        (mapCovariantD (chartChristoffelBilin h c) Z a W p)
        (mapCovariantD (chartChristoffelBilin h c) Z a W p)+
      2*realMetricInChart h c (Z p) (W p)
        (mapCovariantD (chartChristoffelBilin h c) Z a
          (mapCovariantD (chartChristoffelBilin h c) Z a W) p) := by
  let L := mapCovariantD (chartChristoffelBilin h c) Z a W
  have hL : DifferentiableAt ℝ L p :=
    (mapCovariantD_contDiffAt h hh c Z W hz 1 hZ hW a).differentiableAt_one
  have hZd := hZ.differentiableAt (by norm_num)
  have hWd := hW.differentiableAt (by norm_num)
  have heq : mapDirection (fun q => realMetricInChart h c (Z q) (W q) (W q)) a=ᶠ[𝓝 p]
      (fun q => 2*realMetricInChart h c (Z q) (W q) (L q)) := by
    filter_upwards [(hZ.of_le (by norm_num : (1 : ℕ∞ω)≤2)).eventually (by norm_num),
      (hW.of_le (by norm_num : (1 : ℕ∞ω)≤2)).eventually (by norm_num),
      hZ.continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)] with q hqZ hqW hq
    exact mapDirection_metricSelf h hh c Z W hq hqZ.differentiableAt_one hqW.differentiableAt_one a
  rw [mapDirection_congr heq a,
    mapDirection_const_mul _ (mapMetricPair_hasFDerivAt h hh c Z W L hz hZd hWd hL).differentiableAt 2 a,
    mapDirection_metricPair h hh c Z W L hz hZd hWd hL a]
  change 2*(realMetricInChart h c (Z p) (L p) (L p)+
    realMetricInChart h c (Z p) (W p) (mapCovariantD (chartChristoffelBilin h c) Z a L p))=_
  dsimp only [L]
  ring

theorem mapEnergyDensity_secondVariation (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (Z : E → ComplexVector n) {p : E} (hz : Z p∈chartTarget c)
    (hZ : ContDiffAt ℝ 3 Z p) (a b : E)
    (hRadial : mapCovariantD (chartChristoffelBilin h c) Z b
      (mapCovariantD (chartChristoffelBilin h c) Z a (mapDirection Z a)) p=0) :
    mapDirection (mapDirection (fun q => realMetricInChart h c (Z q)
      (mapDirection Z b q) (mapDirection Z b q)) a) a p=
      2*realMetricInChart h c (Z p)
        (mapCovariantD (chartChristoffelBilin h c) Z a (mapDirection Z b) p)
        (mapCovariantD (chartChristoffelBilin h c) Z a (mapDirection Z b) p)+
      2*realMetricInChart h c (Z p) (mapDirection Z b p)
        (connectionCurvature (chartChristoffelBilin h c) (Z p)
          (mapDirection Z a p) (mapDirection Z b p) (mapDirection Z a p)) := by
  have hZ₂ : ContDiffAt ℝ 2 Z p := hZ.of_le (by norm_num)
  have hJ : ContDiffAt ℝ 2 (mapDirection Z a) p := mapDirection_contDiffAt Z 2 hZ a
  have hT : ContDiffAt ℝ 2 (mapDirection Z b) p := mapDirection_contDiffAt Z 2 hZ b
  have hΓ : DifferentiableAt ℝ (chartChristoffelBilin h c) (Z p) :=
    ((chartChristoffelBilin_contDiffOn h hh c).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  have heq : mapCovariantD (chartChristoffelBilin h c) Z a (mapDirection Z b)=ᶠ[𝓝 p]
      mapCovariantD (chartChristoffelBilin h c) Z b (mapDirection Z a) := by
    filter_upwards [(hZ.of_le (by norm_num : (2 : ℕ∞ω)≤3)).eventually (by norm_num)] with q hq
    exact mapCovariantD_torsionFree _ Z hq (chartChristoffelBilin_symm h c (Z q)) a b
  have hComm := mapCovariantD_commutator (chartChristoffelBilin h c) Z
    (mapDirection Z a) hΓ hZ₂ hJ a b
  rw [hRadial,sub_zero] at hComm
  have hOuter := (mapCovariantD_congr (chartChristoffelBilin h c) Z heq a).trans hComm
  rw [mapMetricDensity_secondDirection h hh c Z (mapDirection Z b) hz hZ₂ hT a,hOuter]

end Yau.LeafProofs.L23Aux
