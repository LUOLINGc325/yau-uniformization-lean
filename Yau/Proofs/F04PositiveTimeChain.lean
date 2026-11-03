import Yau.Proofs.F04PositiveBochner
import Yau.Proofs.F04SmoothPositiveTime
import Yau.Proofs.F04SameTraceApproximation
import Yau.Proofs.F04DualPairing

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L16HilbertTimeRegularization
  Yau.LeafProofs.L16LionsApproximation Yau.LeafProofs.L16LionsLimit

variable {n : ℕ} {M : ComplexManifold n}

/-- The positive-part weak time chain for the original continuous L2 trace,
with actual L1 dual pairing and all closed-time endpoint pairs. -/
theorem dirichlet_posPart_weak_time_chain
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    {T : ℝ} (hT : 0 < T) {U : ℝ → DirichletEnergy g μ hμ O}
    {R : ℝ → StrongDual ℝ (DirichletEnergy g μ hμ O)}
    (hU : MemLp U 2 (volume.restrict (Ioo 0 T)))
    (hR : MemLp R 2 (volume.restrict (Ioo 0 T)))
    (hw : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ioo 0 T →
      (∫ t in Ioo 0 T, deriv η t • hilbertEmbedding (dirichletL2 g μ hμ O) (U t)) =
        -(∫ t in Ioo 0 T, η t • R t))
    (a : ℝ → Lp ℝ 2 (μ.restrict O)) (ha : ContinuousOn a (Icc 0 T))
    (hae : ∀ᵐ t ∂volume.restrict (Ioo 0 T), dirichletL2 g μ hμ O (U t) = a t) :
    IntegrableOn (fun t => R t (dirichletPosPart g μ hμ O hO (U t))) (Ioo 0 T) ∧
      ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
        ‖Lp.posPart (a t)‖ ^ 2 - ‖Lp.posPart (a s)‖ ^ 2 =
          2 * ∫ q in s..t, R q (dirichletPosPart g μ hμ O hO (U q)) := by
  let := dirichletEnergy_completeSpace g μ hμ O
  let J := dirichletL2 g μ hμ O
  let z : ℕ → ℝ → DirichletEnergy g μ hμ O := reflectedSmooth T U
  let Q : ℕ → ℝ → StrongDual ℝ (DirichletEnergy g μ hμ O) := reflectedDualSmooth T R
  have hJ : ‖J‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun v => by simpa only [one_mul] using dirichletL2_norm_le g μ hμ O v)
  have hzLp (k : ℕ) : MemLp (z k) 2 (volume.restrict (Ioo 0 T)) :=
    (reflectedSmooth_memLp hT hU k).restrict (Ioo 0 T)
  have hQLp (k : ℕ) : MemLp (Q k) 2 (volume.restrict (Ioo 0 T)) :=
    (reflectedDualSmooth_memLp hT hR k).restrict (Ioo 0 T)
  have hPU := dirichletPosPart_memLp g hK μ hμ O hO (volume.restrict (Ioo 0 T)) U hU
  have hPz (k : ℕ) := dirichletPosPart_memLp g hK μ hμ O hO
    (volume.restrict (Ioo 0 T)) (z k) (hzLp k)
  have hpair := dualPairing_integrable_L2 hPU hR
  refine ⟨hpair, ?_⟩
  have huni := reflectedSmooth_uniform_to_same_trace J hJ hT hU hR hw a ha hae
  have hPzlim := dirichlet_posPart_strongL2 g hK μ hμ O hO (volume.restrict (Ioo 0 T))
    z U hzLp hU (reflectedSmooth_L2_tendsto hT hU)
  have hprod := strongL2_duality_L1 hPz hQLp hPU hR hPzlim
    (reflectedDualSmooth_L2_tendsto hT hR)
  intro s hs t ht
  have hInt := intervalIntegral_tendsto_of_L1
    (fun k => dualPairing_integrable_L2 (hPz k) (hQLp k)) hpair hprod hs ht
  have hEnd := (((Lp.continuous_posPart.tendsto (a t)).comp (huni.tendsto_at ht)).norm.pow 2).sub
    (((Lp.continuous_posPart.tendsto (a s)).comp (huni.tendsto_at hs)).norm.pow 2)
  have he (k : ℕ) : ‖Lp.posPart (J (z k t))‖ ^ 2 - ‖Lp.posPart (J (z k s))‖ ^ 2 =
      2 * ∫ q in s..t, Q k q (dirichletPosPart g μ hμ O hO (z k q)) :=
    smooth_positive_energy_increment g hK μ hμ O hO
      ((reflectedSmooth_contDiff hT hU k).of_le (by simp))
      (reflectedDualSmooth_contDiff hT hR k).continuous.continuousOn
      (fun q hq => reflectedSmooth_derivative (hilbertEmbedding J) hT hU hR hw k hq) hs ht
  have hEnd' : Tendsto (fun k => 2 * ∫ q in s..t,
      Q k q (dirichletPosPart g μ hμ O hO (z k q))) atTop
      (𝓝 (‖Lp.posPart (a t)‖ ^ 2 - ‖Lp.posPart (a s)‖ ^ 2)) := by
    convert hEnd using 1
    funext k
    exact (he k).symm
  exact tendsto_nhds_unique hEnd' (hInt.const_mul 2)

end Yau.F04Proof
