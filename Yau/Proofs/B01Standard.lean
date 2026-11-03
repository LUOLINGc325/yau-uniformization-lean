import Yau.Blueprint.BundlePresentation

/-! The actual punctured unit disc in the one-dimensional complex manifold API. -/
open scoped Manifold Topology ContDiff
open Topology Set
noncomputable section

namespace Yau.Proofs.B01Aux
namespace StandardAux

private abbrev Disc := {z : ℂ // z ∈ Blueprint.puncturedUnitDisc}

private theorem disc_isOpen : IsOpen Blueprint.puncturedUnitDisc :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

private def polar (p : ℝ × ℝ) : ℂ :=
  Complex.exp (-(Real.exp p.1 : ℂ) + (p.2 : ℂ) * Complex.I)

private theorem polar_mem (p : ℝ × ℝ) : polar p ∈ Blueprint.puncturedUnitDisc := by
  have hn : ‖polar p‖ = Real.exp (-Real.exp p.1) := by
    simp only [polar, Complex.norm_exp, Complex.add_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
  change 0 < ‖polar p‖ ∧ ‖polar p‖ < 1
  rw [hn]
  exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos _))⟩

private instance : Nonempty Disc := ⟨⟨polar (0, 0), polar_mem _⟩⟩

private theorem disc_connected : ConnectedSpace Disc := by
  let f : ℝ × ℝ → Disc := fun p => ⟨polar p, polar_mem p⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact Complex.continuous_exp.comp
      (((Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_fst)).neg).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hs : Function.Surjective f := by
    intro z
    refine ⟨(Real.log (-Real.log ‖(z : ℂ)‖), Complex.arg z), ?_⟩
    apply Subtype.ext
    change Complex.exp _ = (z : ℂ)
    have hl : Real.log ‖(z : ℂ)‖ < 0 := Real.log_neg z.property.1 z.property.2
    rw [Real.exp_log (neg_pos.mpr hl)]
    simpa [Complex.log] using Complex.exp_log (norm_pos_iff.mp z.property.1)
  exact hs.connectedSpace hf

private theorem disc_noncompact : NoncompactSpace Disc := by
  refine ⟨?_⟩
  intro hc
  have hk : IsCompact Blueprint.puncturedUnitDisc := by
    simpa only [Set.image_univ, Subtype.range_coe_subtype, Set.ofPred_mem_eq] using
      hc.image (continuous_subtype_val : Continuous (Subtype.val : Disc → ℂ))
  have he : Blueprint.puncturedUnitDisc = Set.univ :=
    (show IsClopen Blueprint.puncturedUnitDisc from ⟨hk.isClosed, disc_isOpen⟩).eq_univ
      ⟨polar (0, 0), polar_mem _⟩
  have hzero : (0 : ℂ) ∈ Blueprint.puncturedUnitDisc := he ▸ Set.mem_univ _
  simp [Blueprint.puncturedUnitDisc] at hzero

private def oneEquiv : ℂ ≃ₗᵢ[ℂ] ComplexVector 1 :=
  (OrthonormalBasis.singleton (Fin 1) ℂ).repr

private def inclusion : Disc → ComplexVector 1 := fun z => oneEquiv z.val

private theorem inclusion_open : IsOpenEmbedding inclusion :=
  oneEquiv.toHomeomorph.isOpenEmbedding.comp disc_isOpen.isOpenEmbedding_subtypeVal

private instance disc_charted : ChartedSpace (ComplexVector 1) Disc :=
  inclusion_open.singletonChartedSpace

private instance disc_manifold : IsManifold (ComplexModel 1) ⊤ Disc :=
  inclusion_open.isManifold_singleton

private abbrev manifold : ComplexManifold 1 where
  Carrier := Disc
  topology := inferInstance
  charted := disc_charted
  manifold := disc_manifold
  t2 := inferInstance
  secondCountable := inferInstance
  connected := disc_connected
  noncompact := disc_noncompact
  dimension := 1
  dimension_eq := rfl

private def coordinate : Blueprint.BundlePresentation.DiscCoordinate manifold :=
  disc_isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val

private theorem coordinate_analytic :
    ContMDiff (ComplexModel 1) 𝓘(ℂ, ℂ) ⊤ coordinate := by
  change ContMDiff (ComplexModel 1) 𝓘(ℂ, ℂ) ⊤ (Subtype.val : Disc → ℂ)
  have hi : ContMDiff (ComplexModel 1) (ComplexModel 1) ⊤ inclusion :=
    contMDiff_isOpenEmbedding inclusion_open
  have he := oneEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff
    (n := (⊤ : ℕ∞ω))
  exact (he.comp hi).congr fun z => (oneEquiv.symm_apply_apply z.val).symm

private theorem coordinate_symm_analytic :
    ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel 1) ⊤ coordinate.symm
      Blueprint.puncturedUnitDisc := by
  change ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel 1) ⊤
    (disc_isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
      (Subtype.val : Disc → ℂ)).symm Blueprint.puncturedUnitDisc
  have hi : ContMDiffOn (ComplexModel 1) (ComplexModel 1) ⊤
      (inclusion_open.toOpenPartialHomeomorph inclusion).symm (Set.range inclusion) :=
    contMDiffOn_isOpenEmbedding_symm inclusion_open
  have he := oneEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff
    (n := (⊤ : ℕ∞ω))
  have h := hi.comp he.contMDiffOn (s := Blueprint.puncturedUnitDisc) (by
    intro z hz
    exact ⟨⟨z, hz⟩, rfl⟩)
  apply h.congr
  intro z hz
  have hc : (disc_isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
      (Subtype.val : Disc → ℂ)).symm z = (⟨z, hz⟩ : Disc) :=
    disc_isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv
      Subtype.val (x := ⟨z, hz⟩)
  have hi : (inclusion_open.toOpenPartialHomeomorph inclusion).symm (oneEquiv z) =
      (⟨z, hz⟩ : Disc) :=
    inclusion_open.toOpenPartialHomeomorph_left_inv inclusion (x := ⟨z, hz⟩)
  exact hc.trans hi.symm

end StandardAux

/-- A genuine connected, noncompact punctured disc with a complex analytic global coordinate. -/
theorem standardDiscRealization : Blueprint.BundlePresentation.StandardDiscRealization := by
  refine ⟨StandardAux.manifold, StandardAux.coordinate, rfl, ?_,
    StandardAux.coordinate_analytic, StandardAux.coordinate_symm_analytic⟩
  rw [StandardAux.coordinate, IsOpenEmbedding.toOpenPartialHomeomorph_target]
  exact Subtype.range_coe_subtype

end Yau.Proofs.B01Aux
