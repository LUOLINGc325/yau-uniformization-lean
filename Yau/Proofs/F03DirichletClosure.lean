import Yau.Proofs.F03DirichletClosedGraph
import Yau.Proofs.F03DirichletCoreApprox
import Yau.Proofs.F03ScalarL2Convergence

/-! Identification with the literal sequence closure of the actual scalar d graph. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
open LeafProofs.L03 LeafProofs.L18Aux LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletCore_scalarL2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : dirichletCore g μ hμ O) : ScalarL2 (μ.restrict O) f.val :=
  (scalarL2_iff_memLp _ _).mpr ((scalarEnergyDomain_memLp g μ hμ f.val).restrict O)

theorem dirichletL2_core_eq_scalarToLp (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : dirichletCore g μ hμ O) (hf : ScalarL2 (μ.restrict O) f.val) :
    dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f) = scalarToLp hf := by
  rw [dirichletL2_core]
  apply Lp.ext
  filter_upwards [restrictL2_coe μ O (scalarEnergyDomainL2 g μ hμ f.val),
    ae_restrict_of_ae (scalarEnergyDomainL2_coe g μ hμ f.val), scalarToLp_coe hf]
    with x hr hk hf
  change restrictL2 μ O (scalarEnergyDomainL2 g μ hμ f.val) x = scalarToLp _ x
  rw [hr, hk, hf]

/-- Exact identification of the frozen actual sequence closure. Values of the
representatives outside O are unrestricted throughout this equivalence. -/
theorem scalarEnergyClosure_iff (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : M.Carrier → ℝ) (df : RealForm M 1)
    (hf : ScalarL2 (μ.restrict O) f) (hdf : L2RealForm g.form (μ.restrict O) df) :
    ScalarEnergyClosure g.form μ O f df ↔
      ∃ v : DirichletEnergy g μ hμ O,
        dirichletL2 g μ hμ O v = scalarToLp hf ∧
        dirichletD g μ hμ O v =
          realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection df hdf) := by
  classical
  constructor
  · rintro ⟨_, _, fs, dfs, hc, ht⟩
    let vs : ℕ → dirichletCore g μ hμ O := fun j =>
      ⟨⟨fs j, (hc j).1.1, (hc j).1.2.1⟩, (hc j).1.2.2⟩
    let us : ℕ → L2FormSpace g (μ.restrict O) 1 := fun j =>
      L2FormSpace.ofSection (dfs j) (hc j).2.2.2.1
    have hJcore (j : ℕ) :
        dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O (vs j)) =
          scalarToLp (hc j).2.1 :=
      dirichletL2_core_eq_scalarToLp g μ hμ O (vs j) (hc j).2.1
    have hDcore (j : ℕ) :
        dirichletD g μ hμ O (dirichletCoreToEnergy g μ hμ O (vs j)) =
          realizeL2Form g (μ.restrict O) (us j) := by
      rw [dirichletD_core]
      apply (realizeL2Form_eq_iff_ae g (μ.restrict O) _ _).mpr
      have heq := scalarExterior_unique (hc j).1.1 (hc j).2.2.2.2
      exact ae_of_all _ (fun x => congrFun heq.symm x)
    have htJ : Tendsto (fun j => scalarL2DistanceSq (μ.restrict O) (fs j) f)
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
        (fun _ => bot_le) (fun _ => le_add_of_nonneg_right (by positivity))
    have htD : Tendsto (fun j => formL2DistanceSq g.form (μ.restrict O) (dfs j) df)
        atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
        (fun _ => bot_le) (fun _ => le_add_of_nonneg_left (by positivity))
    have hJlim : Tendsto (fun j => dirichletL2 g μ hμ O
        (dirichletCoreToEnergy g μ hμ O (vs j))) atTop (𝓝 (scalarToLp hf)) := by
      simpa only [hJcore] using
        (tendsto_scalarToLp_iff (μ.restrict O) fs f (fun j => (hc j).2.1) hf).mpr htJ
    have hDlim : Tendsto (fun j => dirichletD g μ hμ O
        (dirichletCoreToEnergy g μ hμ O (vs j))) atTop
        (𝓝 (realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection df hdf))) := by
      simpa only [hDcore] using
        (tendsto_realizeL2Form_iff g (μ.restrict O) us
          (L2FormSpace.ofSection df hdf)).mpr htD
    have hmem := (dirichletGraphMap_isClosed_range g μ hμ O).mem_of_tendsto
      (hJlim.prodMk_nhds hDlim) (Filter.Eventually.of_forall (fun j =>
        show (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O (vs j)),
          dirichletD g μ hμ O (dirichletCoreToEnergy g μ hμ O (vs j))) ∈
          Set.range (dirichletGraphMap g μ hμ O) from
          ⟨dirichletCoreToEnergy g μ hμ O (vs j), rfl⟩))
    obtain ⟨v, hv⟩ := hmem
    exact ⟨v, congrArg Prod.fst hv, congrArg Prod.snd hv⟩
  · rintro ⟨v, hJ, hD⟩
    obtain ⟨ks, hks⟩ := exists_dirichletCore_tendsto g μ hμ O v
    let fs : ℕ → M.Carrier → ℝ := fun j => (ks j).val
    let dfs : ℕ → RealForm M 1 := fun j => scalarExterior (fs j)
    have hfs : ∀ j, ScalarL2 (μ.restrict O) (fs j) :=
      fun j => dirichletCore_scalarL2 g μ hμ O (ks j)
    have hdfs : ∀ j, L2RealForm g.form (μ.restrict O) (dfs j) :=
      fun j => scalarExterior_l2_restrict g μ hμ O (ks j).val.2.1 (ks j).val.2.2
    refine ⟨hf, hdf, fs, dfs, fun j => ?_, ?_⟩
    · exact ⟨⟨(ks j).val.2.1, (ks j).val.2.2, (ks j).property⟩,
        hfs j, scalarExterior_smooth (ks j).val.2.1, hdfs j,
        scalarExterior_represents (ks j).val.2.1⟩
    · have htJ := ((dirichletL2 g μ hμ O).continuous.tendsto v).comp hks
      rw [hJ] at htJ
      have htJs : Tendsto (fun j => scalarToLp (hfs j)) atTop (𝓝 (scalarToLp hf)) := by
        convert htJ using 1
        funext j
        exact (dirichletL2_core_eq_scalarToLp g μ hμ O (ks j) (hfs j)).symm
      have htD := ((dirichletD g μ hμ O).continuous.tendsto v).comp hks
      rw [hD] at htD
      have htDs : Tendsto (fun j => realizeL2Form g (μ.restrict O)
          (L2FormSpace.ofSection (dfs j) (hdfs j))) atTop
          (𝓝 (realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection df hdf))) := by
        simpa only [Function.comp_def, dirichletD_core, scalarEnergyDomainD, dfs, fs] using htD
      have hscalar := (tendsto_scalarToLp_iff (μ.restrict O) fs f hfs hf).mp htJs
      have hform := (tendsto_realizeL2Form_iff g (μ.restrict O)
        (fun j => L2FormSpace.ofSection (dfs j) (hdfs j))
        (L2FormSpace.ofSection df hdf)).mp htDs
      simpa only [zero_add, L2FormSpace.toSection_ofSection] using hscalar.add hform

end Yau.Proofs.F03Aux
