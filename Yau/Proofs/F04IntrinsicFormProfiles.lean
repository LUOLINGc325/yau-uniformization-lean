import Yau.Proofs.F04IntrinsicFormBinding

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.Proofs.F03Aux Yau.MassTargetStatements

variable {n : ℕ}

local instance (X : KahlerManifold n) (μ : Measure (Pt X))
    (hμ : IsRiemannianVolume X.metric.form μ) (O : Set (Pt X)) :
    CompleteSpace (DirichletEnergy X.metric μ hμ O) := dirichletEnergy_completeSpace X.metric μ hμ O

/-- The actual physical-profile construction additionally exposes its genuine
 global scalar continuity and operator bound, for the Galerkin construction. -/
theorem flow_intrinsic_form_profiles
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O K : Set (Pt X)) (hO : IsOpen O) (hK : IsCompact K) (hOK : O ⊆ K)
    {T : ℝ} (hT : 0 < T) :
    ∃ (B : ℝ → DirichletEnergy X.metric μ hμ O →L[ℝ]
        EnergyDual (DirichletEnergy X.metric μ hμ O)) (C shift : ℝ),
      IntrinsicFormBinding X.metric.form μ O h T C (1 / 2) shift
        (dirichletL2 X.metric μ hμ O) (energyRepresentative X.metric μ hμ O) B ∧
      (∀ t u v, ‖B t u v‖ ≤ C * ‖u‖ * ‖v‖) ∧ (∀ u v, Continuous (fun t => B t u v)) := by
  obtain ⟨C, Φ, hC, hΦb, hΦcore⟩ :=
    flow_core_form_extension X o h U P ρ hloc μ hμ O K hK hOK hT
  obtain ⟨shift, hshift, hGard⟩ := flow_core_garding X o h U P ρ hloc μ hμ O K hK hOK hT
  let B := physicalProfileForm hT.le Φ
  have hBcore (t : ℝ) (ht : t ∈ Icc 0 T) (f v : dirichletCore X.metric μ hμ O) :
      B t (dirichletCoreEmbedding X.metric μ hμ O f) (dirichletCoreEmbedding X.metric μ hμ O v) =
        -(∫ x, v.val x * laplacian (h t) f.val x ∂μ) := by
    have hτ : (⟨timeClamp T hT.le t, timeClamp_mem T hT.le t⟩ : Icc (0 : ℝ) T) = ⟨t, ht⟩ :=
      Subtype.ext (timeClamp_eq_of_mem T hT.le ht)
    change Φ (dirichletCoreEmbedding X.metric μ hμ O f)
      (dirichletCoreEmbedding X.metric μ hμ O v) ⟨timeClamp T hT.le t, timeClamp_mem T hT.le t⟩ = _
    rw [hτ]
    exact hΦcore f v ⟨t, ht⟩
  refine ⟨B, C, shift, ?_, ?_, ?_⟩
  · refine ⟨hC, by norm_num, hshift, ?_, ?_⟩
    · intro u v
      exact (physicalProfileForm_continuous hT.le Φ u v).measurable
    · intro t ht
      refine ⟨physicalProfileForm_norm_le hT.le Φ hC.le hΦb t, ?_, ?_⟩
      · intro u
        have hc : IsClosed {w : DirichletEnergy X.metric μ hμ O |
            (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ B t w w + shift * ‖dirichletL2 X.metric μ hμ O w‖ ^ 2} :=
          isClosed_le (continuous_const.mul (continuous_norm.pow 2))
            (((B t).continuous.clm_apply continuous_id).add
              (continuous_const.mul ((dirichletL2 X.metric μ hμ O).continuous.norm.pow 2)))
        have hcore : Set.range (dirichletCoreEmbedding X.metric μ hμ O) ⊆
            {w | (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ B t w w + shift * ‖dirichletL2 X.metric μ hμ O w‖ ^ 2} := by
          rintro _ ⟨f, rfl⟩
          change (1 / 2 : ℝ) * ‖dirichletCoreEmbedding X.metric μ hμ O f‖ ^ 2 ≤
            B t (dirichletCoreEmbedding X.metric μ hμ O f) (dirichletCoreEmbedding X.metric μ hμ O f) +
              shift * ‖dirichletL2 X.metric μ hμ O (dirichletCoreEmbedding X.metric μ hμ O f)‖ ^ 2
          rw [hBcore t ht f f]
          exact hGard t ht f
        exact (closure_minimal hcore hc) (dirichletCoreEmbedding_denseRange X.metric μ hμ O u)
      · intro f df v dv hf hv hdf hdv _hfc _hvc
        let cf : dirichletCore X.metric μ hμ O := ⟨⟨f, hf.1, hf.2.1⟩, hf.2.2⟩
        let cv : dirichletCore X.metric μ hμ O := ⟨⟨v, hv.1, hv.2.1⟩, hv.2.2⟩
        have hef : energyRepresentative X.metric μ hμ O f df =
            dirichletCoreEmbedding X.metric μ hμ O cf := by
          rw [scalarExterior_unique hf.1 hdf]
          exact energyRepresentative_core X.metric X.kahler_metric μ hμ O hO.measurableSet cf
        have hev : energyRepresentative X.metric μ hμ O v dv =
            dirichletCoreEmbedding X.metric μ hμ O cv := by
          rw [scalarExterior_unique hv.1 hdv]
          exact energyRepresentative_core X.metric X.kahler_metric μ hμ O hO.measurableSet cv
        have hi := compact_test_laplacian_integrable X.metric μ hμ (h t)
          (metricFamilySmooth_slice h (Ici 0) hloc.1.2.1 t ht.1) hf.1 hv.1 hv.2.1
        refine ⟨hi.restrict, ?_⟩
        have hInt : (∫ x in O, v x * laplacian (h t) f x ∂μ) =
            ∫ x, v x * laplacian (h t) f x ∂μ := by
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro x hx
          rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (hv.2.2 hs)), zero_mul]
        rw [hef, hev, hBcore t ht cf cv]
        unfold intrinsicTestForm
        rw [hInt]

  · intro t u v
    change ‖Φ u v ⟨timeClamp T hT.le t, timeClamp_mem T hT.le t⟩‖ ≤ _
    exact ((Φ u v).norm_coe_le_norm _).trans (hΦb u v)
  · exact physicalProfileForm_continuous hT.le Φ

end Yau.F04Proof
