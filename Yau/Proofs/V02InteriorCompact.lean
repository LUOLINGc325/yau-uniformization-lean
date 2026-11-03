import Yau.Proofs.D02CotangentBox
import Yau.Proofs.V03Energy

/-! The original D02 cotangent-confinement clause produces the actual
intrinsic compact required by V02 realization. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem variation_baseArea_le_energy (d : VariationData X q) (j : ℕ)
    (F : VariationDisc X) :
    discArea X.metric.form (fun ζ => (F.f ζ).1) ≤ variationEnergy d j F := by
  unfold variationEnergy
  exact le_self_add.trans (le_self_add.trans (le_self_add.trans le_self_add))

theorem interiorCompact_of_originalD02 (hD02 : DiscCompactness X)
    {d : VariationData X q} (hd : VariationSetup d) (j : ℕ) (E₀ : ℝ)
    (F : ℕ → VariationDisc X)
    (hF : ∀ ν, AdmissibleVariationDisc d j (F ν) ∧
      (variationEnergy d j (F ν)).toReal ≤ E₀) :
    ∃ K' : Set (CotangentPoint X.manifold), CotangentCompact K' ∧
      ∀ ν, ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, (F ν).f ζ ∈ K' := by
  have hg : d.h 0 = X.metric.form := hd.2.2.1.1.1.1
  have hK : IsCompact {x : Pt X | d.u x ≤ d.A j} := hd.2.2.2.1.2.1 _
  obtain ⟨K, R, hK', hb⟩ :=
    (hD02 {x : Pt X | d.u x ≤ d.A j} hK (max E₀ 0)).2.2 (d.B j ^ 2) |>.1
  let K' : Set (CotangentPoint X.manifold) :=
    {y | InCotangentCompact X.metric.form K R y.1 y.2}
  refine ⟨K', Yau.NodeProofs.D02Aux.cotangentBoxCompact n X.manifold X.metric.form
    (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric) K R hK', ?_⟩
  intro ν ζ hζ
  apply hb (fun z => ((F ν).f z).1) (fun z => ((F ν).f z).2) (hF ν).1.1
  · intro z hz
    have he : circlePoint (Complex.arg z) = z := by
      simpa only [circlePoint, hz, Complex.ofReal_one, one_mul] using
        Complex.norm_mul_exp_arg_mul_I z
    have hzR := (hF ν).1.2.2.2.2.2.2.2.1 (Complex.arg z)
    rw [he] at hzR
    exact ⟨hzR.1.le, by simpa only [hg] using hzR.2.le⟩
  · have hfin := (hF ν).1.2.2.2.2.2.2.2.2
    have henergy : variationEnergy d j (F ν) ≤ ENNReal.ofReal (max E₀ 0) :=
      (ENNReal.le_ofReal_iff_toReal_le hfin (le_max_right E₀ 0)).mpr
        ((hF ν).2.trans (le_max_left E₀ 0))
    exact (variation_baseArea_le_energy d j (F ν)).trans henergy
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hζ

end Yau.Blueprint.V02Proof
