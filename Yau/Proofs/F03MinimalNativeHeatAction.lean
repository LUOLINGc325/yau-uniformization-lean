import Yau.Proofs.F03MinimalKernelL2Action
import Yau.Proofs.F03ExhaustionHeat

/-! The actual exhaustion-limit integral is the native L² heat almost everywhere. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings HeatTargetCandidates LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem dirichletMinimalKernelCandidate_native_heat_ae
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) :
    (fun x => ∫ y, dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*f y ∂μ) =ᵐ[μ]
      (scalarHeatFamily g μ hμ t f : M.Carrier → ℝ) := by
  let V : ℕ → Lp ℝ 2 μ := fun j => l2ZeroExtension μ (O j) (hO.1 j).1.measurableSet
    (dirichletHeat g μ hμ (O j) t (l2Restriction μ (O j) f))
  have hAE : ∀ j, (fun x => ∫ y, dirichletExhaustionKernels g hK μ hμ O hO j t x y*f y ∂μ)
      =ᵐ[μ] (V j : M.Carrier → ℝ) := by
    intro j
    have hfj : ScalarL2 (μ.restrict (O j)) (f : M.Carrier → ℝ) :=
      (scalarL2_iff_memLp _ _).mpr ((Lp.memLp f).restrict (O j))
    have hsrc : scalarToLp hfj=l2Restriction μ (O j) f := by
      apply Lp.ext
      filter_upwards [scalarToLp_coe hfj,restrictL2_coe μ (O j) f] with y hy hz
      exact hy.trans hz.symm
    have heq := dirichletKernelCandidate_evolution_eq g hK μ hμ (O j) (hO.1 j).1 ht f hfj
    rw [hsrc] at heq
    filter_upwards [dirichletClassicalHeat_ambient_ae g hK μ hμ (O j) (hO.1 j).1
      (l2Restriction μ (O j) f) ht] with x hx
    have heqx := congrFun heq x
    simp only [boundedKernelEvolution,if_neg ht.ne'] at heqx
    exact heqx.trans hx
  have hstrong : Tendsto V atTop (𝓝 (scalarHeatFamily g μ hμ t f)) :=
    dirichletHeat_exhaustion_strong_tendsto g μ hμ hO t ht f
  obtain ⟨ns,hns,hnsAE⟩ := (tendstoInMeasure_of_tendsto_Lp hstrong).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ j,
      (∫ y, dirichletExhaustionKernels g hK μ hμ O hO j t x y*f y ∂μ)=V j x :=
    ae_all_iff.mpr hAE
  filter_upwards [hnsAE,hall] with x hx hxeq
  have hlim := (dirichletExhaustionKernels_l2_integral_tendsto g hK μ hμ O hO f
    ((scalarL2_iff_memLp _ _).mpr (Lp.memLp f)) ht x).comp hns.tendsto_atTop
  exact tendsto_nhds_unique (hlim.congr' (Eventually.of_forall (fun j => hxeq (ns j)))) hx

end Yau.Proofs.F03Aux
