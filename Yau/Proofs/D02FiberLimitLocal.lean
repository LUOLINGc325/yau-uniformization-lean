import Yau.Proofs.D02FiberLimitReconstruction
import Yau.Proofs.D02FiberLimitUniform

open scoped Manifold Topology ContDiff
open Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02FiberLimitAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.NodeProofs.D02Aux Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false

variable {n m : ℕ} {M : ComplexManifold n}

/-- A same-index joint limit of base maps and finite field evaluations has a
genuine local holomorphic covector-coordinate limit in the chart centered
at f(z₀). The actual inverse is constructed from the original spanning fields. -/
theorem local_fiber_limit (g : SmoothMetric M)
    (V : Fin m → VectorField M) (hV : ∀ a, IsHolomorphicField (V a))
    (hspan : ∀ x, Submodule.span ℂ (Set.range fun i ↦ V i x) = ⊤)
    (fs : ℕ → ℂ → M.Carrier) (ξs : ℕ → ℂ → Covector n)
    (hfs : ∀ j, IsCotangentDisc (fs j) (ξs j))
    (f : ℂ → M.Carrier) (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f (ball 0 1))
    (hconv : letI := L12Aux.inducedMetricSpace g;
      TendstoLocallyUniformlyOn fs f atTop (ball 0 1))
    (e : ℂ → (Fin m → ℂ)) (he : DifferentiableOn ℂ e (ball 0 1))
    (heconv : TendstoLocallyUniformlyOn
      (fun j z ↦ evaluationVector V (fs j z, ξs j z)) e atTop (ball 0 1))
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball (0 : ℂ) 1) :
    ∃ (R : ℝ) (η : ℂ → ComplexVector n), 0 < R ∧ closedBall z₀ R ⊆ ball (0 : ℂ) 1 ∧
      MapsTo f (closedBall z₀ R) (extChartAt (ComplexModel n) (f z₀)).source ∧
      DifferentiableOn ℂ η (ball z₀ R) ∧
      TendstoUniformlyOn (fun j z ↦ covectorCoords (f z₀) (fs j z) (ξs j z)) η atTop (closedBall z₀ R) ∧
      ∀ z ∈ closedBall z₀ R, ∀ i,
        fieldEvaluation (V i) (f z, covectorOfCoords (f z₀) (f z) (η z)) = e z i := by
  classical
  letI := L12Aux.inducedMetricSpace g
  letI := L12Aux.inducedMetricSpace_proper g
  let x := f z₀
  obtain ⟨C, hC⟩ := exists_frame_coefficients V hspan x
  let O : Set M.Carrier := (extChartAt (ComplexModel n) x).source ∩
    (chartPt x) ⁻¹' frameDomain V C x
  have hO : IsOpen O := (continuousOn_extChartAt (I := ComplexModel n) x).isOpen_inter_preimage
    (isOpen_extChartAt_source (I := ComplexModel n) x) (frameDomain_isOpen V hV C x)
  have hxO : x ∈ O := ⟨mem_extChartAt_source x, frameDomain_center V C x hC⟩
  have hparam : ball (0 : ℂ) 1 ∩ f ⁻¹' O ∈ 𝓝 z₀ :=
    (hf.continuousOn.isOpen_inter_preimage isOpen_ball hO).mem_nhds ⟨hz₀, hxO⟩
  obtain ⟨R, hR, hsub⟩ := nhds_basis_closedBall.mem_iff.mp hparam
  have hRD : closedBall z₀ R ⊆ ball (0 : ℂ) 1 := fun z hz ↦ (hsub hz).1
  have hfO : MapsTo f (closedBall z₀ R) O := fun z hz ↦ (hsub hz).2
  have hbase := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hconv
    (closedBall z₀ R) hRD (isCompact_closedBall z₀ R)
  have heval := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp heconv
    (closedBall z₀ R) hRD (isCompact_closedBall z₀ R)
  obtain ⟨hfsO, hcoord⟩ := uniform_limit_compact_composition (isCompact_closedBall z₀ R)
    (hf.continuousOn.mono hRD) hbase hO hfO (chartPt x)
    ((continuousOn_extChartAt (I := ComplexModel n) x).mono inter_subset_left)
  let q := fun z ↦ (chartPt x (f z), e z)
  let qs := fun j z ↦ (chartPt x (fs j z), evaluationVector V (fs j z, ξs j z))
  have hqc : ContinuousOn q (closedBall z₀ R) :=
    (((continuousOn_extChartAt (I := ComplexModel n) x).comp (hf.continuousOn.mono hRD)
      (fun z hz ↦ (hfO hz).1))).prodMk (he.continuousOn.mono hRD)
  have hqconv : TendstoUniformlyOn qs q atTop (closedBall z₀ R) := uniform_pair hcoord heval
  have hqmap : MapsTo q (closedBall z₀ R) (frameDomain V C x ×ˢ univ) :=
    fun z hz ↦ ⟨(hfO hz).2, mem_univ _⟩
  obtain ⟨_, hrec⟩ := uniform_limit_compact_composition (isCompact_closedBall z₀ R) hqc hqconv
    ((frameDomain_isOpen V hV C x).prod isOpen_univ) hqmap
    (frameReconstruct V C x) (frameReconstruct_continuousOn V hV C x)
  let η := fun z ↦ frameReconstruct V C x (q z)
  have hηconv : TendstoUniformlyOn (fun j z ↦ covectorCoords x (fs j z) (ξs j z)) η
      atTop (closedBall z₀ R) := by
    apply hrec.congr
    filter_upwards [hfsO] with j hj z hz
    exact frameReconstruct_evaluation V C x (fs j z) (hj hz).1 (hj hz).2.2 (ξs j z)
  have hηlocal := hηconv.tendstoLocallyUniformlyOn.mono ball_subset_closedBall
  have hηdiff : ∀ᶠ j in atTop, DifferentiableOn ℂ
      (fun z ↦ covectorCoords x (fs j z) (ξs j z)) (ball z₀ R) := by
    filter_upwards [hfsO] with j hj z hz
    have hzD : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall (hRD (ball_subset_closedBall hz))
    have hc := (cotangentDisc_coords_contDiffWithinAt (f := fun z ↦ (fs j z, ξs j z))
      (hfs j) hzD x ((hj (ball_subset_closedBall hz)).1)).snd
    exact (hc.mono (ball_subset_closedBall.trans (hRD.trans ball_subset_closedBall))).differentiableWithinAt
      (by simp)
  refine ⟨R, η, hR, hRD, fun z hz ↦ (hfO hz).1,
    hηlocal.differentiableOn hηdiff isOpen_ball, hηconv, ?_⟩
  intro z hz i
  have hcoordlim : Tendsto (fun j ↦ covectorCoords x (fs j z) (ξs j z)) atTop (𝓝 (η z)) :=
    hηconv.tendsto_at hz
  have hbaselim : Tendsto (fun j ↦ chartPt x (fs j z)) atTop (𝓝 (chartPt x (f z))) :=
    hcoord.tendsto_at hz
  have hfieldlim : Tendsto (fun j ↦ fieldCoords (V i) x (chartPt x (fs j z))) atTop
      (𝓝 (fieldCoords (V i) x (chartPt x (f z)))) :=
    ((fieldCoords_continuousOn (hV i) x).continuousAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds (hfO hz).2.1)).tendsto.comp hbaselim
  have hpairlim : Tendsto (fun j ↦ ∑ a, fieldCoords (V i) x (chartPt x (fs j z)) a *
      covectorCoords x (fs j z) (ξs j z) a) atTop
      (𝓝 (∑ a, fieldCoords (V i) x (chartPt x (f z)) a * η z a)) := by
    exact tendsto_finset_sum _ (fun a ha ↦ ((PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℂ) a).continuousAt.tendsto.comp hfieldlim).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℂ) a).continuousAt.tendsto.comp hcoordlim))
  have heqlim : Tendsto (fun j ↦ fieldEvaluation (V i) (fs j z, ξs j z)) atTop
      (𝓝 (∑ a, fieldCoords (V i) x (chartPt x (f z)) a * η z a)) := by
    apply hpairlim.congr'
    filter_upwards [hfsO] with j hj
    exact (field_evaluation_coordinates (V i) x (fs j z) (hj hz).1 (ξs j z)).symm
  have hevalpoint := (heconv.tendsto_at (hRD hz)).apply_nhds i
  have heq := tendsto_nhds_unique heqlim hevalpoint
  rw [field_evaluation_coordinates (V i) x (f z) (hfO hz).1,
    covectorCoords_ofCoords x (f z) (hfO hz).1 (η z)]
  exact heq

end Yau.NodeProofs.D02FiberLimitAux
