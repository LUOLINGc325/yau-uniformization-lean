import Yau.Proofs.F03DirichletResolvent

/-! The literal actual Dirichlet Friedrichs graph equals the constructed resolvent graph. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
open LeafProofs.L03 LeafProofs.L18Aux LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem scalarFriedrichsPair_iff_variational (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f w : M.Carrier → ℝ)
    (hf : ScalarL2 (μ.restrict O) f) (hw : ScalarL2 (μ.restrict O) w) :
    ScalarFriedrichsPair g.form μ O f w ↔
      ∃ u : DirichletEnergy g μ hμ O, dirichletL2 g μ hμ O u = scalarToLp hf ∧
        ∀ v, dirichletClosedEnergy g μ hμ O u v =
          ⟪scalarToLp hw, dirichletL2 g μ hμ O v⟫_ℝ := by
  constructor
  · rintro ⟨_, df, hcl, hgraph⟩
    obtain ⟨u, hJu, hDu⟩ := (scalarEnergyClosure_iff g μ hμ O f df hf hcl.2.1).mp hcl
    refine ⟨u, hJu, fun v => ?_⟩
    let kv : M.Carrier → ℝ := dirichletL2 g μ hμ O v
    have hkv : ScalarL2 (μ.restrict O) kv :=
      (scalarL2_iff_memLp _ _).mpr (Lp.memLp (dirichletL2 g μ hμ O v))
    have hkvEq : scalarToLp hkv = dirichletL2 g μ hμ O v :=
      scalarToLp_of_coe _ hkv
    obtain ⟨dv, hdv, hdvEq⟩ :=
      l2FormHilbert_exists_section g (μ.restrict O) (dirichletD g μ hμ O v)
    have hvcl : ScalarEnergyClosure g.form μ O kv dv :=
      (scalarEnergyClosure_iff g μ hμ O kv dv hkv hdv).mpr ⟨v, hkvEq.symm, hdvEq.symm⟩
    have h := hgraph kv dv hvcl
    calc
      dirichletClosedEnergy g μ hμ O u v =
          (1 / 2 : ℝ) * ⟪dirichletD g μ hμ O u, dirichletD g μ hμ O v⟫_ℝ :=
        dirichletClosedEnergy_eq_differential g μ hμ O u v
      _ = (1 / 2 : ℝ) * ∫ x in O, formInner g.form df dv x ∂μ := by
        rw [hDu, ← hdvEq, realizeL2Form_inner]
        rfl
      _ = ∫ x in O, w x * kv x ∂μ := by linarith only [h.2.2]
      _ = ⟪scalarToLp hw, dirichletL2 g μ hμ O v⟫_ℝ := by
        rw [← hkvEq]
        exact (scalarToLp_inner hw hkv).symm
  · rintro ⟨u, hJu, he⟩
    obtain ⟨df, hdf, hdfEq⟩ :=
      l2FormHilbert_exists_section g (μ.restrict O) (dirichletD g μ hμ O u)
    have hfcl : ScalarEnergyClosure g.form μ O f df :=
      (scalarEnergyClosure_iff g μ hμ O f df hf hdf).mpr ⟨u, hJu, hdfEq.symm⟩
    refine ⟨hw, df, hfcl, ?_⟩
    intro v dv hvcl
    obtain ⟨z, hJz, hDz⟩ :=
      (scalarEnergyClosure_iff g μ hμ O v dv hvcl.1 hvcl.2.1).mp hvcl
    refine ⟨formInner_integrable g (μ.restrict O) df dv hdf hvcl.2.1,
      scalarL2_product_integrable hw hvcl.1, ?_⟩
    have h := he z
    rw [dirichletClosedEnergy_eq_differential, ← hdfEq, hDz,
      realizeL2Form_inner, hJz, scalarToLp_inner] at h
    simp only [L2FormSpace.toSection_ofSection] at h
    linarith only [h]

/-- No operator or form-domain oracle is supplied: both sides refer to the
fixed actual metric, volume, supported closure and its constructed adjoint. -/
theorem scalarFriedrichsPair_iff_resolvent (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f w : M.Carrier → ℝ)
    (hf : ScalarL2 (μ.restrict O) f) (hw : ScalarL2 (μ.restrict O) w) :
    ScalarFriedrichsPair g.form μ O f w ↔
      scalarToLp hf = dirichletResolvent g μ hμ O (scalarToLp hf + scalarToLp hw) :=
  (scalarFriedrichsPair_iff_variational g μ hμ O f w hf hw).trans
    (dirichlet_variational_iff_resolvent g μ hμ O (scalarToLp hf) (scalarToLp hw))

end Yau.Proofs.F03Aux
