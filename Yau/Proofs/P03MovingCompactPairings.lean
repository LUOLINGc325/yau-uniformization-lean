import Yau.Proofs.P03CompactIntegralFamilies

open scoped Topology
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {A K P : Type*} [TopologicalSpace A] [LocallyCompactSpace A]
  [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [CompactSpace K]
  [TopologicalSpace P] (μ : Measure K) [IsFiniteMeasure μ]

/-- Evaluation on a continuously moving compact family, followed by a fixed
compact weighted integral, is jointly continuous in the original continuous
function and the spatial parameter. -/
theorem continuous_moving_compactPairing (j : P × K → A) (hj : Continuous j)
    (w : C(K, ℂ)) :
    Continuous (fun q : C(A, ℂ) × P => ∫ k, w k * q.1 (j (q.2, k)) ∂μ) := by
  have hf : Continuous (fun q : (C(A, ℂ) × P) × K => q.1.1) :=
    continuous_fst.comp continuous_fst
  have harg : Continuous (fun q : (C(A, ℂ) × P) × K => j (q.1.2, q.2)) :=
    hj.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hval := continuous_eval.comp (hf.prodMk harg)
  have hweight : Continuous (fun q : (C(A, ℂ) × P) × K => w q.2) :=
    w.continuous.comp continuous_snd
  have hwhole := hweight.mul hval
  let F : (C(A, ℂ) × P) → C(K, ℂ) := fun q =>
    ⟨fun k => w k * q.1 (j (q.2, k)),
      hwhole.comp (continuous_const.prodMk continuous_id)⟩
  exact continuous_integral_compact_family μ F hwhole

end Yau.NodeProofs.P03Aux
