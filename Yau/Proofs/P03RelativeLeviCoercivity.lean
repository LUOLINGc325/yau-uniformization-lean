import Yau.Proofs.P03CompactLeviCoercivity
import Yau.LeafProofs.L22LeviTransport

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs Yau.LeafProofs.L22Aux Yau.LeafProofs.L12Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- On a fixed compact chart set, the actual strictly positive Levi form
bounds a positive multiple of the actual background metric. -/
theorem exists_compact_relative_levi_lower (g : Yau.SmoothMetric M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffOn ℝ ∞ f (chartTarget a))
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKO : K ⊆ chartTarget a)
    (hpos : ∀ z ∈ K, (leviC f z).PosDef) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ z ∈ K, ∀ v,
      lam * realMetricInChart g.form a z v v ≤ complexLeviQuadratic f z v := by
  obtain ⟨δ, hδ, hδbound⟩ := exists_uniform_levi_lower_bound_on_compact
    (isOpen_extChartAt_target a) hf hK hKO hpos
  have hG : ContinuousOn (fun p : ComplexVector n × ComplexVector n =>
      realMetricInChart g.form a p.1 p.2 p.2) (K ×ˢ Metric.sphere 0 1) := by
    have HG : ContDiffOn ℝ ∞
        (fun p : ComplexVector n × ComplexVector n => realMetricInChart g.form a p.1)
        (chartTarget a ×ˢ Set.univ) :=
      (L12Aux.realMetricInChart_smooth g a).comp contDiffOn_fst (fun p hp => hp.1)
    exact ((HG.clm_apply contDiffOn_snd).clm_apply contDiffOn_snd).continuousOn.mono
      (fun p hp => ⟨hKO hp.1, Set.mem_univ _⟩)
  obtain ⟨C, hC, hCbound⟩ := exists_uniform_quadratic_bound_on_compact
    (fun z v => realMetricInChart g.form a z v v) hK hG (by
      intro z v t
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring)
  let lam := δ / (C + 1)
  have hden : 0 < C + 1 := by linarith
  have hlam : 0 < lam := div_pos hδ hden
  have he : lam * (C + 1) = δ := div_mul_cancel₀ δ hden.ne'
  have hlamC : lam * C ≤ δ := by nlinarith [hlam.le]
  refine ⟨lam, hlam, ?_⟩
  intro z hz v
  calc
    lam * realMetricInChart g.form a z v v ≤ lam * (C * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (abs_le.mp (hCbound z hz v)).2 hlam.le
    _ = (lam * C) * ‖v‖ ^ 2 := by ring
    _ ≤ δ * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hlamC (sq_nonneg _)
    _ ≤ complexLeviQuadratic f z v := hδbound z hz v

end Yau.NodeProofs.P03Aux
