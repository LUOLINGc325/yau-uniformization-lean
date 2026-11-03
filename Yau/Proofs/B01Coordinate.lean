import Yau.Blueprint.ExtraIntegrability

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

theorem puncturedUnitDisc_isOpen : IsOpen puncturedUnitDisc :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

theorem puncturedUnitDisc_measurableSet : MeasurableSet puncturedUnitDisc :=
  puncturedUnitDisc_isOpen.measurableSet

def complexOneEquiv : ℂ ≃ₗᵢ[ℂ] ComplexVector 1 :=
  (OrthonormalBasis.singleton (Fin 1) ℂ).repr

@[simp] theorem complexOneEquiv_apply (z : ℂ) (i : Fin 1) : complexOneEquiv z i = z :=
  OrthonormalBasis.singleton_repr z i

theorem holomorphic_contDiffOn_one {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {S : Set (ComplexVector 1)}
    {f : ComplexVector 1 → F} (hf : DifferentiableOn ℂ f S) (hS : IsOpen S) :
    ContDiffOn ℂ ∞ f S := by
  let e : ℂ ≃L[ℂ] ComplexVector 1 := complexOneEquiv.toContinuousLinearEquiv
  have hsc : DifferentiableOn ℂ (f ∘ e) (e ⁻¹' S) :=
    hf.comp e.differentiable.differentiableOn (fun _ hz => hz)
  have hsm : ContDiffOn ℂ ∞ (f ∘ e) (e ⁻¹' S) :=
    hsc.contDiffOn (hS.preimage e.continuous)
  have ht : ContDiffOn ℂ ∞ (fun z => f (e (e.symm z))) S :=
    hsm.comp e.symm.contDiff.contDiffOn (fun z hz => by simpa only [mem_preimage, e.apply_symm_apply] using hz)
  simpa only [e.apply_symm_apply] using ht

variable {M : ComplexManifold 1} (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
include hc

theorem disc_mem_source (x : M.Carrier) : x ∈ c.source := by
  rw [hc.1]
  trivial

theorem disc_mem (x : M.Carrier) : c x ∈ puncturedUnitDisc := by
  rw [← hc.2.1]
  exact c.map_source (disc_mem_source c hc x)

theorem disc_left_inv (x : M.Carrier) : c.symm (c x) = x :=
  c.left_inv (disc_mem_source c hc x)

theorem disc_right_inv {z : ℂ} (hz : z ∈ puncturedUnitDisc) : c (c.symm z) = z :=
  c.right_inv (hc.2.1.symm ▸ hz)

theorem disc_continuous : Continuous c := by
  rw [← continuousOn_univ, ← hc.1]
  exact c.continuousOn

theorem disc_injective : Function.Injective c := by
  intro x y h
  simpa only [disc_left_inv c hc] using congrArg c.symm h

def discHomeomorph : M.Carrier ≃ₜ puncturedUnitDisc where
  toFun x := ⟨c x, disc_mem c hc x⟩
  invFun z := c.symm z
  left_inv := disc_left_inv c hc
  right_inv z := Subtype.ext (disc_right_inv c hc z.property)
  continuous_toFun := (disc_continuous c hc).subtype_mk _
  continuous_invFun := by
    apply ContinuousOn.comp_continuous (s := puncturedUnitDisc)
      (hc.2.1 ▸ c.continuousOn_symm) continuous_subtype_val
    exact fun z => z.property

@[simp] theorem discHomeomorph_apply (x : M.Carrier) :
    (discHomeomorph c hc x : ℂ) = c x := rfl

@[simp] theorem discHomeomorph_symm_apply (z : puncturedUnitDisc) :
    (discHomeomorph c hc).symm z = c.symm z := rfl

theorem disc_symm_aemeasurable :
    AEMeasurable c.symm ((volume : Measure ℂ).restrict puncturedUnitDisc) := by
  exact ((hc.2.1 ▸ c.continuousOn_symm).aemeasurable
    puncturedUnitDisc_measurableSet)

theorem discArea_map :
    Measure.map c (BundlePresentation.discArea c) =
      (volume : Measure ℂ).restrict puncturedUnitDisc := by
  rw [BundlePresentation.discArea,
    AEMeasurable.map_map_of_aemeasurable
      (disc_continuous c hc).measurable.aemeasurable (disc_symm_aemeasurable c hc)]
  trans Measure.map id ((volume : Measure ℂ).restrict puncturedUnitDisc)
  · apply Measure.map_congr
    filter_upwards [ae_restrict_mem puncturedUnitDisc_measurableSet] with z hz
    exact disc_right_inv c hc hz
  · exact Measure.map_id

theorem disc_measurableEmbedding : MeasurableEmbedding c :=
  (c.isOpenEmbedding hc.1).measurableEmbedding

theorem lintegral_discArea (F : M.Carrier → ℝ≥0∞) :
    (∫⁻ x, F x ∂BundlePresentation.discArea c) =
      ∫⁻ z in puncturedUnitDisc, F (c.symm z) ∂volume := by
  rw [← discArea_map c hc, (disc_measurableEmbedding c hc).lintegral_map]
  simp only [disc_left_inv c hc]

theorem setLIntegral_discArea (S : Set ℂ) (hS : MeasurableSet S)
    (hSD : S ⊆ puncturedUnitDisc) (F : M.Carrier → ℝ≥0∞) :
    (∫⁻ x in c ⁻¹' S, F x ∂BundlePresentation.discArea c) =
      ∫⁻ z in S, F (c.symm z) ∂volume := by
  rw [← lintegral_indicator (hS.preimage (disc_continuous c hc).measurable),
    lintegral_discArea c hc]
  calc
    (∫⁻ z in puncturedUnitDisc, (c ⁻¹' S).indicator F (c.symm z) ∂volume) =
        ∫⁻ z in puncturedUnitDisc, S.indicator (fun z => F (c.symm z)) z ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem puncturedUnitDisc_measurableSet] with z hz
      unfold Set.indicator
      congr 1
      exact propext (by simp only [mem_preimage, disc_right_inv c hc hz])
    _ = ∫⁻ z in S, F (c.symm z) ∂volume := by
      rw [lintegral_indicator hS, Measure.restrict_restrict_of_subset hSD]

theorem disc_mdifferentiableAt (x : M.Carrier) :
    MDifferentiableAt (ComplexModel 1) 𝓘(ℂ, ℂ) c x :=
  hc.2.2.1.mdifferentiableAt (by simp)

theorem disc_symm_mdifferentiableAt {z : ℂ} (hz : z ∈ puncturedUnitDisc) :
    MDifferentiableAt 𝓘(ℂ, ℂ) (ComplexModel 1) c.symm z :=
  (hc.2.2.2.mdifferentiableOn (by simp)).mdifferentiableAt
    (puncturedUnitDisc_isOpen.mem_nhds hz)

theorem disc_mfderiv_left_inv (x : M.Carrier) (v : TangentVector M x) :
    mfderiv 𝓘(ℂ, ℂ) (ComplexModel 1) c.symm (c x)
      (mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x v) = v := by
  rw [← mfderiv_comp_apply x (disc_symm_mdifferentiableAt c hc (disc_mem c hc x))
    (disc_mdifferentiableAt c hc x)]
  have he : (c.symm ∘ c : M.Carrier → M.Carrier) = id := by
    funext y
    exact disc_left_inv c hc y
  rw [he, mfderiv_id]
  rfl

theorem disc_mfderiv_right_inv (x : M.Carrier) (t : ℂ) :
    mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x
      (mfderiv 𝓘(ℂ, ℂ) (ComplexModel 1) c.symm (c x) t) = t := by
  have hm := mfderiv_comp_apply (c x)
    (disc_mdifferentiableAt c hc (c.symm (c x)))
    (disc_symm_mdifferentiableAt c hc (disc_mem c hc x)) t
  rw [disc_left_inv c hc] at hm
  refine hm.symm.trans ?_
  have hlocal : (c ∘ c.symm : ℂ → ℂ) =ᶠ[𝓝 (c x)] id :=
    c.eventually_right_inverse (hc.2.1.symm ▸ disc_mem c hc x)
  have he := hlocal.mfderiv_eq (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ))
  exact (congrArg (fun L => L t) he).trans (by rw [mfderiv_id])

theorem disc_mfderiv_injective (x : M.Carrier) :
    Function.Injective (mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x) := by
  intro u v huv
  exact (disc_mfderiv_left_inv c hc x u).symm.trans
    ((congrArg (mfderiv 𝓘(ℂ, ℂ) (ComplexModel 1) c.symm (c x)) huv).trans
      (disc_mfderiv_left_inv c hc x v))

omit hc in
def discCoordinateVector (x : M.Carrier) : TangentVector M x :=
  mfderiv 𝓘(ℂ, ℂ) (ComplexModel 1) c.symm (c x) (1 : ℂ)

omit hc in
def discDerivative (x : M.Carrier) : TangentVector M x →ₗ[ℂ] ℂ :=
  ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (c x)).toContinuousLinearMap.comp
    (mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x)).toLinearMap

omit hc in
@[simp] theorem discDerivative_apply (x : M.Carrier) (v : TangentVector M x) :
    discDerivative c x v = (show ℂ from mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x v) := rfl

theorem discCoordinateVector_map (x : M.Carrier) :
    (show ℂ from mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x (discCoordinateVector c x)) = 1 :=
  disc_mfderiv_right_inv c hc x 1

theorem tangent_eq_discCoordinateVector (x : M.Carrier) (v : TangentVector M x) :
    v = (show ℂ from mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x v) • discCoordinateVector c x := by
  let d : ℂ →ₗ[ℂ] TangentVector M x :=
    (mfderiv 𝓘(ℂ, ℂ) (ComplexModel 1) c.symm (c x)).toLinearMap
  let b : ℂ := mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x v
  calc
    v = d b := (disc_mfderiv_left_inv c hc x v).symm
    _ = b • d 1 := by rw [← map_smul, smul_eq_mul, mul_one]
    _ = _ := rfl

theorem disc_inChart_contDiffAt (a : M.Carrier) {z : ComplexVector 1}
    (hz : z ∈ chartTarget a) :
    ContDiffAt ℂ ∞ (fun w => c (chartInv a w)) z := by
  have hi : ContMDiffAt (ComplexModel 1) (ComplexModel 1) ⊤ (chartInv a) z :=
    (contMDiffOn_extChartAt_symm (I := ComplexModel 1) a).contMDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel 1) a).mem_nhds hz)
  exact (((hc.2.2.1 (chartInv a z)).comp z hi).of_le le_top).contDiffAt

theorem disc_inChart_fderiv (a : M.Carrier) {z : ComplexVector 1}
    (hz : z ∈ chartTarget a) (v : ComplexVector 1) :
    fderiv ℂ (fun w => c (chartInv a w)) z v =
      (show ℂ from mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c (chartInv a z)
        (chartVec a (chartInv a z) v)) := by
  have hi : MDifferentiableAt (ComplexModel 1) (ComplexModel 1) (chartInv a) z := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := ComplexModel 1) hz
    rwa [ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ] at h
  have hm := mfderiv_comp_apply z (disc_mdifferentiableAt c hc (chartInv a z)) hi v
  rw [mfderiv_eq_fderiv] at hm
  change fderiv ℂ (fun w => c (chartInv a w)) z v =
    mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c (chartInv a z)
      (mfderiv (ComplexModel 1) (ComplexModel 1) (chartInv a) z v) at hm
  have hpt : chartPt a (chartInv a z) = z := (extChartAt (ComplexModel 1) a).right_inv hz
  unfold chartVec
  rw [hpt]
  exact hm

omit hc in
theorem discAreaTransport : DiscAreaTransport := by
  intro M c hc
  refine ⟨discArea_map c hc, ?_⟩
  intro f hf
  rw [← discArea_map c hc, lintegral_map hf (disc_continuous c hc).measurable]

end Yau.Proofs.B01Aux
