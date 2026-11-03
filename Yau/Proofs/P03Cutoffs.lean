import Yau.Proofs.P03Polynomials
import Yau.Proofs.P03Jets

open scoped Manifold Topology ContDiff
open Filter

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- Restricting the actual holomorphic atlas gives the smooth real atlas used
to construct cutoffs. -/
theorem real_manifold (M : ComplexManifold n) :
    IsManifold 𝓘(ℝ, ComplexVector n) ∞ M.Carrier := by
  apply isManifold_of_contDiffOn 𝓘(ℝ, ComplexVector n) ∞ M.Carrier
  intro e e' he he'
  have hc := (ComplexModel n).contDiffOn_extendCoordChange (n := ∞)
    (IsManifold.subset_maximalAtlas he) (IsManifold.subset_maximalAtlas he')
  convert! hc.restrict_scalars ℝ using 1
  simp [ModelWithCorners.extendCoordChange_source, ComplexModel, mfld_simps]

theorem contMDiff_real_chart {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M.Carrier → F}
    (hf : ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, F) ∞ f) (a : M.Carrier) :
    ContDiffOn ℝ ∞ (inChart a f) (chartTarget a) := by
  letI := real_manifold M
  have h := hf.comp_contMDiffOn
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, ComplexVector n)) a)
  change ContDiffOn ℝ ∞ (fun z => f ((extChartAt (ComplexModel n) a).symm z))
    (extChartAt (ComplexModel n) a).target
  convert! h.contDiffOn using 1

/-- Compactly supported cutoffs in an arbitrary prescribed neighborhood,
with genuine smoothness in every chart. -/
theorem exists_smooth_cutoff (p : M.Carrier) {U : Set M.Carrier} (hU : U ∈ 𝓝 p) :
    ∃ ρ : M.Carrier → ℝ, SmoothFn ρ ∧ HasCompactSupport ρ ∧
      ρ =ᶠ[𝓝 p] 1 ∧ tsupport ρ ⊆ U := by
  letI := real_manifold M
  obtain ⟨b, _, hb⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, ComplexVector n)) p).mem_iff.mp hU
  exact ⟨b, contMDiff_real_chart b.contMDiff, b.hasCompactSupport,
    b.eventuallyEq_one, hb⟩

/-- A prescribed polynomial germ has a global smooth compactly supported
seed. This seed is the actual scalar datum to which the dbar correction is
applied; no holomorphic global realization is assumed. -/
theorem exists_scalar_seed (p : M.Carrier) (P : MvPolynomial (Fin n) ℂ)
    {U : Set M.Carrier} (hU : U ∈ 𝓝 p) :
    ∃ f : M.Carrier → ℂ,
      (∀ a, ContDiffOn ℝ ∞ (inChart a f) (chartTarget a)) ∧
      HasCompactSupport f ∧ tsupport f ⊆ U ∧
      (inChart p f =ᶠ[𝓝 (chartPt p p)]
        (fun z => MvPolynomial.eval (fun i => z i - chartPt p p i) P)) ∧
      ∀ k, JetAgreeFn f p P k := by
  letI := real_manifold M
  obtain ⟨b, _, hb⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, ComplexVector n)) p).mem_iff.mp hU
  let g : M.Carrier → ℂ := fun x =>
    MvPolynomial.eval (fun i => chartPt p x i - chartPt p p i) P
  let f : M.Carrier → ℂ := fun x => b x • g x
  have hg : ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℂ) ∞ g
      (chartAt (ComplexVector n) p).source := by
    intro x hx
    have hP : ContDiff ℝ ∞ (fun z : ComplexVector n =>
        MvPolynomial.eval (fun i => z i - chartPt p p i) P) :=
      (centeredPolynomial_real_contDiff P (chartPt p p)).of_le le_top
    have hc := hP.comp_contMDiffWithinAt
      (contMDiffOn_extChartAt (I := 𝓘(ℝ, ComplexVector n)) (x := p) x hx)
    convert! hc using 1
  have hf : ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℂ) ∞ f := b.contMDiff_smul hg
  have hfs : tsupport f ⊆ tsupport (b : M.Carrier → ℝ) := tsupport_smul_subset_left b g
  have hfc : HasCompactSupport f :=
    b.hasCompactSupport.isCompact.of_isClosed_subset (isClosed_tsupport f) hfs
  have hcp : Tendsto (chartInv p) (𝓝 (chartPt p p)) (𝓝 p) := by
    change Tendsto (extChartAt (ComplexModel n) p).symm
      (𝓝 ((extChartAt (ComplexModel n) p) p)) (𝓝 p)
    simpa only [extChartAt_to_inv] using
      (continuousAt_extChartAt_symm (I := ComplexModel n) p).tendsto
  have ht : chartTarget p ∈ 𝓝 (chartPt p p) := by
    simpa [chartTarget, chartPt, ComplexModel] using
      extChartAt_target_mem_nhdsWithin (I := ComplexModel n) p
  have hfg : inChart p f =ᶠ[𝓝 (chartPt p p)]
      (fun z => MvPolynomial.eval (fun i => z i - chartPt p p i) P) := by
    filter_upwards [b.eventuallyEq_one.comp_tendsto hcp, ht] with z h1 hz
    simp only [Function.comp_apply, Pi.one_apply] at h1
    have hinv : chartPt p (chartInv p z) = z :=
      (extChartAt (ComplexModel n) p).right_inv hz
    simp [inChart, f, g, h1, hinv]
  exact ⟨f, contMDiff_real_chart hf, hfc, hfs.trans hb, hfg,
    jetAgreeFn_of_polynomial_germ hfg⟩

end Yau.NodeProofs.P03Aux
