import Yau.Proofs.V03GaussPositive
import Yau.Proofs.V03Wirtinger

/-! Exact real energy splitting, including on every nearby realized slice.
The clock term is literally fixed, and Gauss clipping is removed by proof. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem variationEnergy_toReal_actual {d : VariationData X q}
    (hG : CotangentImmersion d.G) (j : ℕ) {F : VariationDisc X}
    (hF : variationEnergy d j F ≠ ⊤) :
    (variationEnergy d j F).toReal = spatialArea d F.f + (clockArea F).toReal +
      (scalarDSq (logTrace d j F.f)).toReal :=
  variationEnergy_toReal_split_of_gauss_nonneg hF (gaussArea_nonneg_of_immersion hG F.f)

theorem realized_energy_actual_local {d : VariationData X q}
    (hG : CotangentImmersion d.G) {j a : ℕ} {F : VariationDisc X}
    {E : ℂ → CotangentMatrix n} {l : ℂ → CotangentIndex n → ℂ}
    {h α : ℂ → ℂ} {fz : ℂ → ℂ → CotangentPoint X.manifold} {r : ℝ}
    (hR : RealizesFirstField d j a F E l h α fz r) :
    (fun z => (variationEnergy d j {F with f := fz z}).toReal) =ᶠ[𝓝 0]
      (fun z => spatialArea d (fz z) + (clockArea F).toReal +
        (scalarDSq (logTrace d j (fz z))).toReal) := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR.1.1] with z hz
  exact variationEnergy_toReal_actual hG j (hR.2.1 z hz).2.2.2.2.2.2.2.2

theorem realized_energy_mixed_actual {d : VariationData X q}
    (hG : CotangentImmersion d.G) {j a : ℕ} {F : VariationDisc X}
    {E : ℂ → CotangentMatrix n} {l : ℂ → CotangentIndex n → ℂ}
    {h α : ℂ → ℂ} {fz : ℂ → ℂ → CotangentPoint X.manifold} {r : ℝ}
    (hR : RealizesFirstField d j a F E l h α fz r) :
    mixedReal (fun z => (variationEnergy d j {F with f := fz z}).toReal) =
      mixedReal (fun z => spatialArea d (fz z) + (clockArea F).toReal +
        (scalarDSq (logTrace d j (fz z))).toReal) :=
  mixedReal_congr (realized_energy_actual_local hG hR)

end Yau.Blueprint.V03Proof
