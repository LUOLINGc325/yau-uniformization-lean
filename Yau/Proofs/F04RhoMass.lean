import Yau.Proofs.F04BallVolume

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L18Aux

theorem flow_rho_ball_mass_polynomial {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {T : ℝ} (hT : 0 < T) :
    ∃ D : ℝ, 0 < D ∧ ∀ L : ℝ, 1 ≤ L → ∀ t ∈ Icc 0 T,
      IntegrableOn (fun x => ρ x t) (distBall X.metric.form o L) μ ∧
        (∫ x in distBall X.metric.form o L, ρ x t ∂μ) ≤ D * L ^ (2 * n + 1) := by
  obtain ⟨C₀, hC₀⟩ := hloc.2.2.2.2.2.2.2.2.2.2.2.1 T hT.le
  let A := max C₀ 1
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨V, hV, hvol⟩ := flow_ball_volume_polynomial X o h U P ρ hloc μ hμ
  refine ⟨A * V, mul_pos hA hV, ?_⟩
  intro L hL t ht
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hρ : SmoothFn (fun x => ρ x t) := by
    intro c
    exact (hloc.2.2.2.1 c).comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun _ hz => ⟨hz, ht.1⟩)
  have hint := smoothFn_integrableOn_distBall X.metric μ hμ hρ o hLp
  have hb : BallIntegralLE X.metric.form μ o (fun x => ρ x t) L (A * L) :=
    Proofs.F02Aux.ballIntegralLE_mono_bound _ _ _ _ _ (hC₀ μ hμ L hL t ht)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hLp.le)
  have havg := (ballIntegralLE_iff_average X μ hμ o hLp (mul_nonneg hA.le hLp.le)
    (fun x => ρ x t) hint (ae_of_all _ (fun x => rho_nonneg o h U P ρ hloc x t ht.1))).2.mp hb
  have hv := ball_volume_facts X μ hμ o hLp
  refine ⟨hint, ?_⟩
  calc
    _ ≤ (A * L) * (μ (distBall X.metric.form o L)).toReal := (div_le_iff₀ hv.2.2.2).mp havg
    _ ≤ (A * L) * (V * L ^ (2 * n)) :=
      mul_le_mul_of_nonneg_left (hvol L hL) (mul_nonneg hA.le hLp.le)
    _ = (A * V) * L ^ (2 * n + 1) := by rw [pow_succ]; ring

end Yau.F04Proof
