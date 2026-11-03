import Yau.Proofs.P03CompactChartSources

open scoped Manifold Topology ContDiff
open Filter MeasureTheory Bundle

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- A prescribed polynomial germ and its actual smooth closed Dolbeault
source are supported in any prescribed neighbourhood. The source is zero
in a neighbourhood of the interpolation point. -/
theorem exists_compact_top_jet_seed (hE : Holomorphic (r := r) E)
    (a : M.Carrier) (P : Fin r → MvPolynomial (Fin n) ℂ)
    {U : Set M.Carrier} (hU : U ∈ 𝓝 a) :
    ∃ (s : NQForm E 0) (f : NQForm E 1),
      SmoothForm (r := r) E s ∧ SmoothForm (r := r) E f ∧
      IsDbarOf (r := r) E s f ∧ WeakDbar (r := r) E s f ∧ WeaklyClosed (r := r) E f ∧
      IsCompact (closure {x | s x ≠ (0 : NQForm E 0) x}) ∧
      closure {x | s x ≠ (0 : NQForm E 0) x} ⊆ U ∧
      IsCompact (closure {x | f x ≠ (0 : NQForm E 1) x}) ∧
      closure {x | f x ≠ (0 : NQForm E 1) x} ⊆ U ∧
      ((fun z => coefficients (r := r) E s a z Fin.elim0) =ᶠ[𝓝 (chartPt a a)]
        (fun z => WithLp.toLp 2
          (fun α => MvPolynomial.eval (fun i => z i - chartPt a a i) (P α)))) ∧
      ∀ᶠ x in 𝓝 a, f x = (0 : NQForm E 1) x := by
  have hself : a ∈ bundleChartSource (r := r) E a :=
    ⟨mem_extChartAt_source a, FiberBundle.mem_baseSet_trivializationAt' a⟩
  have hz := chartPt_mem_localDomain E a a hself
  have hci : Tendsto (chartInv a) (𝓝 (chartPt a a)) (𝓝 a) := by
    change Tendsto (extChartAt (ComplexModel n) a).symm
      (𝓝 ((extChartAt (ComplexModel n) a) a)) (𝓝 a)
    simpa only [extChartAt_to_inv] using
      (continuousAt_extChartAt_symm (I := ComplexModel n) a).tendsto
  have hV : localDomain (r := r) E a ∩ (chartInv a) ⁻¹' U ∈ 𝓝 (chartPt a a) :=
    inter_mem ((localDomain_isOpen E a).mem_nhds hz) (hci hU)
  obtain ⟨F, hF, hc, hsupport, hgerm⟩ := exists_compact_polynomial_model (chartPt a a) P hV
  have hs := hsupport.trans Set.inter_subset_left
  let s := topFormPushforward (r := r) E a F
  let f := oneFormPushforward (r := r) E a (modelTopDbar F)
  obtain ⟨hsmooth, hfsmooth, hweak, hclosed, hfcompact⟩ := smooth_compact_chart_source E hE a F hF hc hs
  have hD := topFormPushforward_isDbarOf E hE a F hF hc hs
  have hK : IsCompact (chartInv a '' tsupport F) := hc.isCompact.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hs.trans Set.inter_subset_left))
  have hKsub : chartInv a '' tsupport F ⊆ U := by
    rintro x ⟨z, hzf, rfl⟩
    exact (hsupport hzf).2
  have hssupport := topFormPushforward_support E a F hc hs
  have hcD : HasCompactSupport (modelTopDbar F) :=
    hc.isCompact.of_isClosed_subset (isClosed_tsupport _) (tsupport_modelTopDbar_subset F)
  have hsD := (tsupport_modelTopDbar_subset F).trans hs
  have hfsupport := oneFormPushforward_support E a (modelTopDbar F) hcD hsD
  have hfU : closure {x | f x ≠ (0 : NQForm E 1) x} ⊆ U :=
    hfsupport.trans ((Set.image_mono (tsupport_modelTopDbar_subset F)).trans hKsub)
  refine ⟨s, f, hsmooth, hfsmooth, hD, hweak, hclosed,
    hK.of_isClosed_subset isClosed_closure hssupport, hssupport.trans hKsub,
    hfcompact, hfU, ?_, polynomial_chart_source_eventually_zero E a F P hgerm⟩
  filter_upwards [(localDomain_isOpen E a).mem_nhds hz, hgerm] with z hz hzg
  exact (topFormPushforward_coefficients E a F z hz).trans hzg

end Yau.NodeProofs.P03Aux
