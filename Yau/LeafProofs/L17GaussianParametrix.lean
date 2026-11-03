import Yau.LeafProofs.L17GaussianLocalJets
import Yau.LeafProofs.L17UniformGaussianResidual
import Yau.LeafProofs.L17LocalizedSchauder

/-! Geometry produces the actual bounded Gaussian parametrix into the original X space. -/

open Set Metric
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17HolderAux L17SchauderAux L17SourceLocalizationAux L17LocalizedSchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

local instance gaussian_add_group {P : UniformChartPartition g} {T γ : ℝ} {hT : 0 < T} :
    AddCommGroup (SchauderSpace P T γ hT) :=
  (schauderSpace_normedAddCommGroup P T γ hT).toAddCommGroup
local instance gaussian_normed_space {P : UniformChartPartition g} {T γ : ℝ} {hT : 0 < T} :
    NormedSpace ℝ (SchauderSpace P T γ hT) := schauderSpace_normedSpace P T γ hT

def GaussianKernelBounds (P : UniformChartPartition g) (T : ℝ) (hT : 0 < T)
    (γ C K R : ℝ) : Prop :=
  ∀ (f : HolderSpace P T γ) (p : P.centers),
    let S := T/P.radius^2
    let v := P.charts.frozenHeatDuhamel p (rescaledSource P T hT.le f p)
    let s := S^(1/2 : ℝ)+S^((1-γ)/2)
    HolderBound γ Set.univ (rescaledSource P T hT.le f p) (C*‖f‖) ∧
    SchauderBound γ (cylinder Set.univ 0 S) v (K*‖f‖) ∧
    (∀ q ∈ cylinder Set.univ 0 S, ‖spatialDD v q‖ ≤ K*‖f‖*S^(γ/2)) ∧
    HolderBound γ (cylinder Set.univ 0 S) (fun q => (v q,spatialD v q)) (K*‖f‖*s) ∧
    HolderBound γ (cylinder (ball (0 : Space n) 2) 0 S)
      (unitGaussianResidual P T hT.le f p) (R*‖f‖*(P.radius+s))

theorem BoundedChartFamily.exists_uniform_gaussian_parametrix
    (A : BoundedChartFamily g) (hg : MetricSmooth g) :
    ∃ N : ℕ, ∃ B : ℕ → ℝ, ∃ C : ℝ, ∃ K R D : Ioo (0 : ℝ) 1 → ℝ,
      (∀ k, 0 < B k) ∧ 0 < C ∧ (∀ γ, 0 < K γ) ∧ (∀ γ, 0 < R γ) ∧ (∀ γ, 0 < D γ) ∧
      ∀ ε : ℝ, 0 < ε → ∃ P : UniformChartPartition g,
        P.charts = A ∧ P.radius < ε ∧ P.radius ≤ 1 ∧ 2*P.radius < A.radius ∧ P.overlapBudget = N ∧
        (∀ k (p : P.centers) q z, z ∈ ball (0 : ComplexVector n) (2*P.radius) →
          ‖iteratedFDeriv ℝ k (fun w => P.weight p (P.charts.chart q w)) z‖ ≤ B k*(P.radius⁻¹)^k ∧
          ‖iteratedFDeriv ℝ k (fun w => P.localization p (P.charts.chart q w)) z‖ ≤ B k*(P.radius⁻¹)^k) ∧
        ∀ (T : ℝ) (hT : 0 < T), T ≤ P.radius^2 → ∀ γ : Ioo (0 : ℝ) 1,
          GaussianKernelBounds P T hT γ.val C (K γ) (R γ) ∧
          ∃ Q : HolderSpace P T γ.val →L[ℝ] SchauderSpace P T γ.val hT,
            (∀ f, schauderFun (Q f) = gaussianParametrixFun P T hT.le f) ∧ ‖Q‖ ≤ D γ := by
  obtain ⟨N,B,C,K,R,hB,hC,hK,hR,hPart⟩ := A.exists_uniform_gaussian_residual hg
  let Ccut := ∑ j ∈ Finset.range 4, B j
  have hCcut : 0 ≤ Ccut := Finset.sum_nonneg (fun j _ => (hB j).le)
  choose E hE hAssembly using fun γ : Ioo (0 : ℝ) 1 =>
    exists_uniform_localized_schauder_assembly A hg N Ccut γ.val hCcut γ.property.1 γ.property.2.le
  refine ⟨N,B,C,K,R,fun γ => 4*E γ*K γ,hB,hC,hK,hR,?_,?_⟩
  · intro γ
    exact mul_pos (mul_pos (by norm_num) (hE γ)) (hK γ)
  · intro ε hε
    obtain ⟨P,hA,hρε,hρ1,hρA,hN,hJets,hKernel⟩ := hPart ε hε
    have hρP : 2*P.radius < P.charts.radius := by simpa only [hA] using hρA
    have hCut : CutoffJetBounds P 2 Ccut := by
      apply cutoffJetBounds_of_all_orders P B (fun k => (hB k).le)
      intro k p q z hz
      exact scale_backgroundChart_jet_bound P.charts (P.localization_smooth p) P.radius_pos hρP q k
        (B k) (fun w hw => (hJets k p q w hw).2) hz
    refine ⟨P,hA,hρε,hρ1,hρA,hN,hJets,?_⟩
    intro T hT hTR γ
    have hG : GaussianKernelBounds P T hT γ.val C (K γ) (R γ) := hKernel T hT hTR γ
    have hSch (f : HolderSpace P T γ.val) (p : P.centers) := (hG f p).2.1
    have hLow (f : HolderSpace P T γ.val) (p : P.centers) := (hG f p).2.2.2.1
    have hu (f : HolderSpace P T γ.val) (p : P.centers) :
        C2 (cylinder Set.univ 0 T) (localGaussian P T hT.le f p) := by
      rw [localGaussian_eq_unscale]
      exact c2_parabolicUnscale P.radius_pos.ne' hT (hSch f p).1
    have hSolve (f : HolderSpace P T γ.val) : ∃! u : SchauderSpace P T γ.val hT,
        schauderFun u = gaussianParametrixFun P T hT.le f ∧ ‖u‖ ≤ E γ*(4*K γ*‖f‖) := by
      exact hAssembly γ P hA hN.le hρ1 hρA hCut T hT (4*K γ*‖f‖)
        (mul_nonneg (mul_nonneg (by norm_num) (hK γ).le) (norm_nonneg f))
        (gaussianLocalFunction P T hT.le f) (gaussianLocalGradient P T hT.le f)
        (gaussianLocalHessian P T hT.le f) (gaussianLocalTime P T hT.le f)
        (gaussian_local_true_jets P T hT.le f (hu f))
        (gaussian_local_scaled_jet_bounds P T hT hTR γ.property.1.le γ.property.2.le (hK γ).le f (hSch f) (hLow f))
    let q : HolderSpace P T γ.val → SchauderSpace P T γ.val hT := fun f => Classical.choose (hSolve f)
    have hValue (f : HolderSpace P T γ.val) : schauderFun (q f) = gaussianParametrixFun P T hT.le f :=
      (Classical.choose_spec (hSolve f)).1.1
    have hNorm (f : HolderSpace P T γ.val) : ‖q f‖ ≤ (4*E γ*K γ)*‖f‖ := by
      change ‖Classical.choose (hSolve f)‖ ≤ _
      simpa only [mul_assoc,mul_left_comm,mul_comm] using (Classical.choose_spec (hSolve f)).1.2
    let L : HolderSpace P T γ.val →ₗ[ℝ] SchauderSpace P T γ.val hT := {
      toFun := q
      map_add' := by
        intro f h
        apply schauderFun_injective
        funext x
        change functionCLM P T γ.val hT (q (f+h)) x = functionCLM P T γ.val hT (q f+q h) x
        rw [(functionCLM P T γ.val hT).map_add]
        change schauderFun (q (f+h)) x = schauderFun (q f) x+schauderFun (q h) x
        rw [hValue,hValue,hValue]
        exact gaussianParametrixFun_add P T hT.le f h x
      map_smul' := by
        intro c f
        apply schauderFun_injective
        funext x
        change functionCLM P T γ.val hT (q (c • f)) x = functionCLM P T γ.val hT (c • q f) x
        rw [(functionCLM P T γ.val hT).map_smul]
        change schauderFun (q (c • f)) x = c*schauderFun (q f) x
        rw [hValue,hValue]
        exact gaussianParametrixFun_smul P T hT.le c f x }
    let Q := L.mkContinuous (4*E γ*K γ) hNorm
    refine ⟨hG,Q,hValue,?_⟩
    exact Q.opNorm_le_bound (mul_nonneg (mul_nonneg (by norm_num) (hE γ).le) (hK γ).le) hNorm

end Yau.LeafProofs.L17Aux
