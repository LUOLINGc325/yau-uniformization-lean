import Yau.Proofs.F05RealizedJetLimit
import Yau.Proofs.F05EventualNonlinearJetEquation
import Yau.Proofs.F05TerminalEquationClosure
import Yau.Proofs.F05IntrinsicClosedChartEquation
import Yau.Proofs.F05SmoothSchauder
import Yau.Proofs.F05BootstrapRestrictions
import Yau.Proofs.F05SmoothContinuity
import Yau.Proofs.F05SchauderLinear

/-! A convergent actual compatible jet sequence produces an actual
manifold solution on the late closed slab. Only eventual equations at
strict earlier times are used; reflected approximants need no later PDE. -/

open Set Filter
open scoped Topology Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16BoundaryTimeAux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_native_add_jets {Q : Set (Point n)} {u v : Point n → ℝ}
    (hu : C2 Q u) (hv : C2 Q v) {z : Point n} (hz : z ∈ Q) :
    spatialD (fun p => u p+v p) z = spatialD u z+spatialD v z ∧
      spatialDD (fun p => u p+v p) z = spatialDD u z+spatialDD v z ∧
      timeD Q (fun p => u p+v p) z = timeD Q u z+timeD Q v z := by
  let : NormedAddCommGroup (F05Hessian n) := f05_jetHessianGroup
  have hNeg : C2 Q (fun p => (-1 : ℝ)*v p) :=
    c2_spatial_mul (φ := fun _ => (-1 : ℝ)) contDiff_const hv
  have hD := spatialD_sub hu hNeg hz
  have hH := spatialDD_sub hu hNeg hz
  have hJ := timeD_sub hu hNeg hz
  rw [(F05_spatial_const_mul_jets (-1) v z).1] at hD
  rw [(F05_spatial_const_mul_jets (-1) v z).2] at hH
  rw [timeD_spatial_mul Q (fun _ => (-1 : ℝ))] at hJ
  have hNegD : (-1 : ℝ) • spatialD v z = -spatialD v z := by
    ext a
    simp only [smul_apply,neg_apply,smul_eq_mul,neg_one_mul]
  have hNegH : (-1 : ℝ) • spatialDD v z = -spatialDD v z := by
    ext a b
    simp only [smul_apply,neg_apply,smul_eq_mul,neg_one_mul]
  rw [hNegD] at hD
  rw [hNegH] at hH
  exact ⟨by simpa only [neg_one_mul,sub_neg_eq_add] using hD,
    by simpa only [neg_one_mul,sub_neg_eq_add] using hH,
    by simpa only [neg_one_mul,sub_neg_eq_add] using hJ⟩

theorem F05_cofinal_nonlinear_limit {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (p : M.Carrier → ℝ → ℝ) {α r T : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) (hrT : r < T)
    (hh : MetricFamilySmooth h (Icc 0 T)) (hp : SmoothSpaceTime p (Icc 0 T))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 T))
    (u : ℕ → F05CompatibleJetGraph A α hT.le)
    (uLim : F05CompatibleJetGraph A α hT.le) (hu : Tendsto u atTop (𝓝 uLim))
    (hEq : ∀ i (z : F05Q A i T), z.val.2 ∈ Ico r T → ∀ᶠ k in atTop,
      timeD (F05Q A i T) (pull A i p) z.val+((u k).val i).val.2.2.2.val.1 z =
        Real.exp (-(pull A i p z.val+((u k).val i).val.1 z))*
          ((∑ a,∑ b,flatA (h z.val.2) A i z.val a b*
              (spatialDD (pull A i p) z.val+((u k).val i).val.2.2.1.val.1 z) (realVec a) (realVec b))+
            ∑ a,flatB (h z.val.2) A i z.val a*
              (spatialD (pull A i p) z.val+((u k).val i).val.2.1 z) (realVec a))+
          (1-Real.exp (-(pull A i p z.val+((u k).val i).val.1 z)))*
            scalarCurvature (h z.val.2) (lift A i z.val.1)) :
    ∃ (W : M.Carrier → ℝ → ℝ) (K : ℝ), 0 < K ∧
      (∀ i, SchauderBound α (F05Q A i T) (pull A i W) K) ∧
      ContinuousOn (fun z : M.Carrier × ℝ => W z.1 z.2) (closure O ×ˢ Icc 0 T) ∧
      (∀ x, W x 0 = p x 0) ∧
      (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, W x t = p x t) ∧
      (∀ x ∈ closure O, ∀ t ∈ Icc r T,
        derivWithin (W x) (Icc r T) t = Real.exp (-W x t)*laplacian (h t) (fun y => W y t) x+
          (1-Real.exp (-W x t))*scalarCurvature (h t) x) ∧
      ∀ i (z : F05Q A i T),
        Tendsto (fun k => pull A i p z.val+((u k).val i).val.1 z) atTop (𝓝 (pull A i W z.val)) := by
  let : NormedAddCommGroup (F05Hessian n) := f05_jetHessianGroup
  obtain ⟨Z,C,hC,hZSch,hZCont,hZ0,hZBoundary,hZEval⟩ := F05_realized_jet_limit hA hχ hT u uLim hu
  obtain ⟨P,hP,hPSch⟩ := F05_smooth_schauder_uniform hA p hT hp
  have hPBound := hPSch α hα hα1 T hT le_rfl
  let W := fun x t => p x t+Z x t
  have hWSch (i : Fin A.count) : SchauderBound α (F05Q A i T) (pull A i W) (P+C) :=
    schauderBound_add (hPBound i) (hZSch i)
  have hPDEOpen (i : Fin A.count) (z : Point n) (hz : z ∈ F05D A i ×ˢ Ico r T) :
      timeD (F05Q A i T) (pull A i W) z = Real.exp (-pull A i W z)*
        ((∑ a,∑ b,flatA (h z.2) A i z a b*spatialDD (pull A i W) z (realVec a) (realVec b))+
          ∑ a,flatB (h z.2) A i z a*spatialD (pull A i W) z (realVec a))+
        (1-Real.exp (-pull A i W z))*scalarCurvature (h z.2) (lift A i z.1) := by
    have hzQ : z ∈ F05Q A i T := ⟨hz.1,hr.trans hz.2.1,hz.2.2.le⟩
    have hEval := hZEval i ⟨z,hzQ⟩
    have hVal := (tendsto_const_nhds (x := pull A i p z)).add hEval.1
    have hGrad := (tendsto_const_nhds (x := spatialD (pull A i p) z)).add hEval.2.1
    have hHess := (tendsto_const_nhds (x := spatialDD (pull A i p) z)).add hEval.2.2.1
    have hTime := (tendsto_const_nhds (x := timeD (F05Q A i T) (pull A i p) z)).add hEval.2.2.2
    have hLimit := F05_eventual_nonlinear_jet_equation (flatA (h z.2) A i z)
      (flatB (h z.2) A i z) (scalarCurvature (h z.2) (lift A i z.1))
      (fun k => pull A i p z+((u k).val i).val.1 ⟨z,hzQ⟩)
      (fun k => spatialD (pull A i p) z+((u k).val i).val.2.1 ⟨z,hzQ⟩)
      (fun k => spatialDD (pull A i p) z+((u k).val i).val.2.2.1.val.1 ⟨z,hzQ⟩)
      (fun k => timeD (F05Q A i T) (pull A i p) z+((u k).val i).val.2.2.2.val.1 ⟨z,hzQ⟩)
      hVal hGrad hHess hTime (hEq i ⟨z,hzQ⟩ hz.2)
    have hPull : pull A i W = fun z => pull A i p z+pull A i Z z := rfl
    have hAdds := F05_native_add_jets (hPBound i).1 (hZSch i).1 hzQ
    rw [hPull,hAdds.1,hAdds.2.1,hAdds.2.2]
    exact hLimit
  have hPDEClosed (i : Fin A.count) := by
    have hFlat := F05_flat_coefficients_smooth hA h hh i
    have hScalar := F05_pull_spacetime_smooth hA _ hR i
    have hSub : F05Q A i T ⊆ Metric.ball 0 3 ×ˢ Icc 0 T :=
      fun z hz => ⟨F05D_mem_ball hz.1,hz.2⟩
    exact F05_nonlinear_equation_terminal_closure hr hrT (hWSch i).1
      (fun z => flatA (h z.2) A i z) (fun z => flatB (h z.2) A i z)
      (pull A i (fun x t => scalarCurvature (h t) x))
      (fun a b => ((matrixEntryCLM a b).continuous.comp_continuousOn hFlat.1.continuousOn).mono hSub)
      (fun a => (hFlat.2 a).continuousOn.mono hSub) (hScalar.continuousOn.mono hSub) (hPDEOpen i)
  have hSmallEq (i : Fin A.count) (z : Point n) (hz : z ∈ cylinder (F05D A i) r T) :
      timeD (cylinder (F05D A i) r T) (pull A i W) z = Real.exp (-pull A i W z)*
        ((∑ a,∑ b,flatA (h z.2) A i z a b*spatialDD (pull A i W) z (realVec a) (realVec b))+
          ∑ a,flatB (h z.2) A i z a*spatialD (pull A i W) z (realVec a))+
        (1-Real.exp (-pull A i W z))*scalarCurvature (h z.2) (lift A i z.1) := by
    rw [F05_timeD_restrict_interval hrT hr le_rfl (hWSch i).1 hz]
    exact hPDEClosed i z hz
  have hEquation := F05_intrinsic_nonlinear_of_closed_charts hA h W
    (fun i => F05_c2_restrict_interval hrT hr le_rfl (hWSch i).1) hSmallEq
  refine ⟨W,P+C,add_pos hP hC,hWSch,
    ((F05_smooth_spacetime_continuousOn hp).mono (prod_mono (subset_univ _) subset_rfl)).add hZCont,
    ?_,?_,hEquation,?_⟩
  · intro x
    dsimp only [W]
    rw [hZ0 x,add_zero]
  · intro x hx t ht
    dsimp only [W]
    rw [hZBoundary x hx t ht,add_zero]
  · intro i z
    change Tendsto (fun k => pull A i p z.val+((u k).val i).val.1 z) atTop
      (𝓝 (pull A i p z.val+pull A i Z z.val))
    exact (tendsto_const_nhds (x := pull A i p z.val)).add (hZEval i z).1

end Yau.Proofs.F05Aux
