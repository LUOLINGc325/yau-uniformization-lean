import Yau.Proofs.E01RawScale
import Yau.Proofs.E01FiberRescale

/-! Exact positive homogeneity of the original lower-semicontinuous chart envelope. -/

noncomputable section
open scoped Matrix Topology
open Filter Set

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem covectorOfCoords_complex_smul (x y : M.Carrier) (c : ℂ) (η : ComplexVector n) :
    covectorOfCoords x y (c • η) = c • covectorOfCoords x y η := by
  ext v
  simp only [covectorOfCoords, PiLp.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

theorem envelopeRawChart_positive_real_smul
    (h : ℝ → HermitianField M) (T : ℝ) (x : M.Carrier)
    (p : ComplexVector n × ComplexVector n × ℝ) (r : ℝ) (hr : 0 < r) :
    envelopeRawChart h T x (p.1, (r : ℂ) • p.2.1, p.2.2) =
      ((r ^ 2 : ℝ) : EReal) * envelopeRawChart h T x p := by
  unfold envelopeRawChart
  rw [covectorOfCoords_complex_smul, envelopeRaw_positive_real_smul h T _ _ _ r hr]

theorem envelopeChart_positive_real_smul
    (h : ℝ → HermitianField M) (T : ℝ) (x : M.Carrier)
    (z η : ComplexVector n) (t : ℝ) (hz : z ∈ chartTarget x) (ht : t ∈ Ioo 0 T)
    (r : ℝ) (hr : 0 < r) :
    envelopeChart h T x (z, (r : ℂ) • η, t) =
      ((r ^ 2 : ℝ) : EReal) * envelopeChart h T x (z, η, t) := by
  let S : Set (ComplexVector n × ComplexVector n × ℝ) :=
    {p | p.1 ∈ chartTarget x ∧ p.2.2 ∈ Ioo 0 T}
  have hp : (z, η, t) ∈ S := ⟨hz, ht⟩
  haveI : NeBot (𝓝[S] (z, η, t)) := nhdsWithin_neBot_of_mem hp
  have hm := fiberRescaleHomeomorph_map_nhdsWithin r hr.ne' (chartTarget x) (Ioo 0 T) (z, η, t)
  change liminf (envelopeRawChart h T x) (𝓝[S] (z, (r : ℂ) • η, t)) =
    ((r ^ 2 : ℝ) : EReal) * liminf (envelopeRawChart h T x) (𝓝[S] (z, η, t))
  apply liminf_scaling_of_filter_map (envelopeRawChart h T x) (fiberRescaleHomeomorph r hr.ne')
    (𝓝[S] (z, η, t)) (𝓝[S] (z, (r : ℂ) • η, t)) hm (r ^ 2) (sq_nonneg r)
  intro q
  rw [fiberRescaleHomeomorph_apply]
  exact envelopeRawChart_positive_real_smul h T x q r hr

end Yau.NodeProofs.E01Aux
