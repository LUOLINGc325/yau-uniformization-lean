import Yau.Proofs.C03EnergyVariation
import Yau.Proofs.P02EndpointLevi

/-! The acceleration trace of a holomorphic endpoint cancels before taking
the path-direction covariant derivative. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

theorem covariant_pair_zero_of_eventually_sum_zero
    {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Γ : V → V →L[ℝ] V →L[ℝ] V) (Z f g : E → V) {p : E}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p)
    (hfg : (fun q => f q + g q) =ᶠ[𝓝 p] fun _ => 0) (b : E) :
    mapCovariantD Γ Z b f p + mapCovariantD Γ Z b g p = 0 := by
  have hd : fderiv ℝ f p b + fderiv ℝ g p b = 0 := by
    have hfd := hfg.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_fun_add hf hg, fderiv_const_apply] at hfd
    exact congrArg (fun L : E →L[ℝ] V => L b) hfd
  have hv : f p + g p = 0 := hfg.self_of_nhds
  calc
    _ = (fderiv ℝ f p b + fderiv ℝ g p b) +
        Γ (Z p) (mapDirection Z b p) (f p + g p) := by
      simp only [mapCovariantD, mapDirection, map_add]
      abel
    _ = 0 := by rw [hd, hv, map_zero, zero_add]

theorem map_radial_acceleration_pair_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (hh : MetricSmooth h) (hK : KahlerClosed h)
    (c : M.Carrier) (Z : E → ComplexVector n) {p : E}
    (hz : Z p ∈ chartTarget c) (a ai : E)
    (hfirst : mapDirection Z ai p = Complex.I • mapDirection Z a p)
    (hsecond : mapDirection (mapDirection Z a) a p +
      mapDirection (mapDirection Z ai) ai p = 0) :
    mapCovariantD (chartChristoffelBilin h c) Z a (mapDirection Z a) p +
      mapCovariantD (chartChristoffelBilin h c) Z ai (mapDirection Z ai) p = 0 := by
  unfold mapCovariantD
  rw [hfirst, Yau.NodeProofs.P02Aux.chartChristoffelBilin_I_I h hh hK c hz]
  convert hsecond using 1 <;> abel

theorem holomorphic_mapDirection_I {m n : ℕ}
    {F : ComplexVector m → ComplexVector n} {p : ComplexVector m}
    (hF : ContDiffAt ℂ 2 F p) (v : ComplexVector m) :
    mapDirection F (Complex.I • v) p = Complex.I • mapDirection F v p := by
  have hd := hF.differentiableAt (by norm_num)
  unfold mapDirection
  rw [hd.fderiv_restrictScalars ℝ]
  change (fderiv ℂ F p) (Complex.I • v) = Complex.I • (fderiv ℂ F p) v
  exact (fderiv ℂ F p).map_smul Complex.I v

theorem holomorphic_mapDirection_second_pair {m n : ℕ}
    {F : ComplexVector m → ComplexVector n} {p : ComplexVector m}
    (hF : ContDiffAt ℂ 2 F p) (v : ComplexVector m) :
    mapDirection (mapDirection F v) v p +
      mapDirection (mapDirection F (Complex.I • v)) (Complex.I • v) p = 0 := by
  have heq (w : ComplexVector m) :
      mapDirection (mapDirection F w) w p = fderiv ℝ (fderiv ℝ F) p w w := by
    change fderiv ℝ (mapDirection F w) p w = _
    rw [(mapDirection_hasFDerivAt F (hF.restrict_scalars ℝ) w).fderiv]
    rfl
  rw [heq, heq, Yau.LeafProofs.L18Aux.secondFDeriv_complex_I_I hF]
  exact add_neg_cancel _

theorem holomorphic_radial_acceleration_pair_zero
    {m n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (hh : MetricSmooth h) (hK : KahlerClosed h)
    (c : M.Carrier) (F : ComplexVector m → ComplexVector n) {p : ComplexVector m}
    (hz : F p ∈ chartTarget c) (hF : ContDiffAt ℂ 2 F p) (v : ComplexVector m) :
    mapCovariantD (chartChristoffelBilin h c) F v (mapDirection F v) p +
      mapCovariantD (chartChristoffelBilin h c) F (Complex.I • v)
        (mapDirection F (Complex.I • v)) p = 0 :=
  map_radial_acceleration_pair_zero h hh hK c F hz v (Complex.I • v)
    (holomorphic_mapDirection_I hF v) (holomorphic_mapDirection_second_pair hF v)

end Yau.Proofs.C03Aux
