import Yau.Proofs.F03DirichletResolventBounds
import Yau.Proofs.F03DirichletCoreApprox
import Yau.LeafProofs.L19NormalContraction

/-! Normal contractions preserve the actual supported energy space. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau
open LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ O) := dirichletEnergy_completeSpace g μ hμ O

theorem dirichletL2_norm_eq_ambient (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    (v : DirichletEnergy g μ hμ O) :
    ‖dirichletL2 g μ hμ O v‖ = ‖scalarEnergyL2 g μ hμ v.val‖ := by
  rw [← dirichletL2_zeroExtension g μ hμ O hO v, l2ZeroExtension_norm]

def smoothNormalClipCore (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (K ε : ℝ) (hε : 0 < ε) (f : dirichletCore g μ hμ O) : dirichletCore g μ hμ O :=
  ⟨smoothNormalClipDomain g μ hμ K ε hε f.val, by
    exact (tsupport_comp_subset (smoothNormalClip_zero K hε) (f.val : M.Carrier → ℝ)).trans
      f.property⟩

theorem smoothNormalClipCore_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (K ε : ℝ) (hε : 0 < ε) (f : dirichletCore g μ hμ O) :
    dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O
      (smoothNormalClipCore g μ hμ O K ε hε f)) =
      smoothNormalClipL2 (μ.restrict O) K ε hε
        (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f)) := by
  rw [dirichletL2_core, dirichletL2_core]
  apply Lp.ext
  filter_upwards [restrictL2_coe μ O (scalarEnergyDomainL2 g μ hμ
      (smoothNormalClipCore g μ hμ O K ε hε f).val),
    ae_restrict_of_ae (scalarEnergyDomainL2_coe g μ hμ
      (smoothNormalClipCore g μ hμ O K ε hε f).val),
    smoothNormalClipL2_coe (μ.restrict O) K ε hε
      (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ f.val)),
    restrictL2_coe μ O (scalarEnergyDomainL2 g μ hμ f.val),
    ae_restrict_of_ae (scalarEnergyDomainL2_coe g μ hμ f.val)]
    with x hcl hcc hcr hfr hfc
  change restrictL2 μ O (scalarEnergyDomainL2 g μ hμ _) x = _
  rw [hcl, hcc, hcr]
  change smoothNormalClip K ε (f.val x) =
    smoothNormalClip K ε (restrictL2 μ O (scalarEnergyDomainL2 g μ hμ f.val) x)
  rw [hfr, hfc]

theorem smoothNormalClipCore_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (K ε : ℝ) (hε : 0 < ε) (f : dirichletCore g μ hμ O) :
    ‖dirichletCoreToEnergy g μ hμ O (smoothNormalClipCore g μ hμ O K ε hε f)‖ ≤
      ‖dirichletCoreToEnergy g μ hμ O f‖ := by
  change ‖((smoothNormalClipDomain g μ hμ K ε hε f.val) : ScalarEnergySpace g μ hμ)‖ ≤
    ‖(f.val : ScalarEnergySpace g μ hμ)‖
  rw [UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  exact smoothNormalClipDomain_norm_le g μ hμ K ε hε f.val

theorem dirichletCore_energy_norm_sq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    (f : dirichletCore g μ hμ O) :
    ‖dirichletCoreToEnergy g μ hμ O f‖ ^ 2 -
      ‖dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f)‖ ^ 2 =
        scalarEnergyPair g μ f.val f.val := by
  rw [dirichletL2_norm_eq_ambient g μ hμ O hO]
  change ‖(f.val : ScalarEnergySpace g μ hμ)‖ ^ 2 -
    ‖scalarEnergyL2 g μ hμ (f.val : ScalarEnergySpace g μ hμ)‖ ^ 2 = _
  rw [UniformSpace.Completion.norm_coe, scalarEnergyL2_coe,
    scalarEnergyDomain_norm_sq]
  ring

theorem dirichletEnergy_normalClip_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    (u : DirichletEnergy g μ hμ O) (K : ℝ) (hK : 0 ≤ K) :
    ∃ v : DirichletEnergy g μ hμ O,
      dirichletL2 g μ hμ O v = normalClipL2 (μ.restrict O) K hK (dirichletL2 g μ hμ O u) ∧
      ‖v‖ ^ 2 - ‖dirichletL2 g μ hμ O v‖ ^ 2 ≤
        ‖u‖ ^ 2 - ‖dirichletL2 g μ hμ O u‖ ^ 2 := by
  classical
  let H := DirichletEnergy g μ hμ O
  let J := dirichletL2 g μ hμ O
  obtain ⟨fs, hcore⟩ := exists_dirichletCore_tendsto g μ hμ O u
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hεpos (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let w₀ : ℕ → dirichletCore g μ hμ O :=
    fun j => smoothNormalClipCore g μ hμ O K (ε j) (hεpos j) (fs j)
  let w : ℕ → H := fun j => dirichletCoreToEnergy g μ hμ O (w₀ j)
  let z := normalClipL2 (μ.restrict O) K hK (J u)
  have hJcore : Tendsto (fun j => J (dirichletCoreToEnergy g μ hμ O (fs j))) atTop
      (𝓝 (J u)) := J.continuous.continuousAt.tendsto.comp hcore
  have hstrong : Tendsto (fun j => J (w j)) atTop (𝓝 z) := by
    have ht := smoothNormalClipL2_tendsto_moving (μ.restrict O) K hK _ (J u)
      hJcore ε hεpos hε
    simpa only [J, w, w₀, smoothNormalClipCore_L2, z] using ht
  have hbound : ∀ᶠ j in atTop, ‖w j‖ ≤ ‖u‖ + 1 := by
    have hb := hcore.norm.eventually (gt_mem_nhds (lt_add_one ‖u‖))
    filter_upwards [hb] with j hj
    exact (smoothNormalClipCore_norm_le g μ hμ O K (ε j) (hεpos j) (fs j)).trans hj.le
  let a : ℕ → ℝ := fun j => ‖dirichletCoreToEnergy g μ hμ O (fs j)‖ ^ 2 -
    ‖J (dirichletCoreToEnergy g μ hμ O (fs j))‖ ^ 2 + ‖J (w j)‖ ^ 2
  have hupper : ∀ᶠ j in atTop, ‖w j‖ ^ 2 ≤ a j := by
    apply Eventually.of_forall
    intro j
    have hE := smoothNormalClipDomain_energy_le g μ hμ K (ε j) (hεpos j) (fs j).val
    change scalarEnergyPair g μ (w₀ j).val (w₀ j).val ≤
      scalarEnergyPair g μ (fs j).val (fs j).val at hE
    have hw := dirichletCore_energy_norm_sq g μ hμ O hO (w₀ j)
    have hf := dirichletCore_energy_norm_sq g μ hμ O hO (fs j)
    change ‖w j‖ ^ 2 ≤ _
    dsimp only [a]
    change ‖w j‖ ^ 2 - ‖J (w j)‖ ^ 2 = _ at hw
    change _ = scalarEnergyPair g μ (fs j).val (fs j).val at hf
    linarith
  have ha : Tendsto a atTop (𝓝 (‖u‖ ^ 2 - ‖J u‖ ^ 2 + ‖z‖ ^ 2)) :=
    ((hcore.norm.pow 2).sub (hJcore.norm.pow 2)).add (hstrong.norm.pow 2)
  obtain ⟨v, hvJ, hv⟩ := hilbert_strong_image_limit J w z a _ (‖u‖ + 1)
    hbound hstrong hupper ha
  refine ⟨v, hvJ, ?_⟩
  change ‖v‖ ^ 2 - ‖J v‖ ^ 2 ≤ ‖u‖ ^ 2 - ‖J u‖ ^ 2
  rw [hvJ]
  linarith

end Yau.Proofs.F03Aux
