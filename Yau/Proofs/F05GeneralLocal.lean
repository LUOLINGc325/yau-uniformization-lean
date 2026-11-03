import Yau.Proofs.F05GeneralInitial
import Yau.Proofs.F05LinearInverse
import Yau.Proofs.F05NonlinearJetHolder
import Yau.Proofs.F05NonlinearRecomposition
import Yau.Proofs.F05SourceBall
import Yau.Proofs.F05Contraction

/-! The actual nonlinear Banach contraction also handles a nonconstant
initial profile with its literal first equation compatibility condition. -/

open Set
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_nonlinear_local_general_from_background_bounds {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (p : M.Carrier → ℝ → ℝ) {S : ℝ} (hS : 0 < S)
    (hh : MetricFamilySmooth h (Icc 0 S)) (hp : SmoothSpaceTime p (Icc 0 S))
    {α B F₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hB : 0 < B) (hF₀ : 0 < F₀)
    (hP2 : ∀ (T : ℝ), 0 < T → T ≤ S → ∀ i, C2 (F05Q A i T) (pull A i p))
    (hCompat : ∀ (T : ℝ), 0 < T → T ≤ S → ∀ x,
      derivWithin (p x) (Icc 0 T) 0 = Real.exp (-p x 0)*laplacian (h 0) (fun y => p y 0) x+
        (1-Real.exp (-p x 0))*scalarCurvature (h 0) x)
    (hCoeff : ∀ (T : ℝ), T ≤ S → ∀ i,
      HolderBound α (F05Q A i T) (pull A i (fun x t => Real.exp (-p x t))) B ∧
      HolderBound α (F05Q A i T) (pull A i (fun x t => laplacian (h t) (fun y => p y t) x)) B ∧
      HolderBound α (F05Q A i T) (pull A i (fun x t => scalarCurvature (h t) x)) B)
    (hZero : ∀ (T : ℝ), 0 < T → T ≤ S → T ≤ 1 → ∀ i,
      HolderBound α (F05Q A i T) (pull A i (F05NonlinearCorrection h T p (fun _ _ => 0)))
        (F₀*T^((1-α)/2))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ S ∧ δ ≤ 1 ∧ ∀ (T : ℝ) (hT : 0 < T), T ≤ δ →
      ∃ z : F05CompatibleJetGraph A α hT.le, ‖z‖ ≤ 1 ∧
        ∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
          derivWithin (fun s => p x s+F05CanonicalJetFunction A χ α hT.le z x s) (Icc 0 T) t =
            Real.exp (-(p x t+F05CanonicalJetFunction A χ α hT.le z x t))*
              laplacian (h t) (fun y => p y t+F05CanonicalJetFunction A χ α hT.le z y t) x+
                (1-Real.exp (-(p x t+F05CanonicalJetFunction A χ α hT.le z x t)))*scalarCurvature (h t) x := by
  let c := fun x t => Real.exp (-p x t)
  have hc : SmoothSpaceTime c (Icc 0 S) := fun x => (hp x).neg.exp
  obtain ⟨δ,CL,CB,hδ,hδS,hδ1,hCL,hCB,hInverse⟩ := F05_linear_inverse hA hχ h c hS hh hc
    (fun _ _ _ => Real.exp_pos _) hα hα1
  obtain ⟨G,C,hG,hC,hLip⟩ := F05_nonlinear_jet_holder hA hχ h hS hh hα hα1 hB (by norm_num : (0 : ℝ) < 1)
  let E := 1+G+CB*C+CB*F₀
  have hE : 0 < E := by dsimp only [E]; positivity
  have hGE : G ≤ E := by dsimp only [E]; nlinarith
  have hCE : CB*C ≤ E := by dsimp only [E]; nlinarith
  have hFE : CB*F₀ ≤ E := by dsimp only [E]; nlinarith
  obtain ⟨δ₀,hδ₀,hδ₀δ,hδ₀1,hSmall⟩ := F05_uniform_small_time hα1 hE hδ
  refine ⟨δ₀,hδ₀,hδ₀δ.trans hδS,hδ₀1,?_⟩
  intro T hT hTδ₀
  have hTδ : T ≤ δ := hTδ₀.trans hδ₀δ
  have hTS : T ≤ S := hTδ.trans hδS
  have hT1 : T ≤ 1 := hTδ₀.trans hδ₀1
  have hPow : 0 ≤ T^((1-α)/2) := Real.rpow_nonneg hT.le _
  have hSmallE := hSmall T hT hTδ₀
  have hScaleG : G*T^((1-α)/2) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hGE hPow
    linarith
  obtain ⟨hρ,hρ1,hScale,hPower⟩ := F05_sqrt_scale hT hT1 α
  have hLipT := hLip (Real.sqrt T) T hT hρ hρ1 hScale.le hTS (by rwa [hPower]) p
    (hP2 T hT hTS) (fun i => (hCoeff T hTS i).1) (fun i => (hCoeff T hTS i).2.1)
    (fun i => (hCoeff T hTS i).2.2)
  let F := fun z : F05CompatibleJetGraph A α hT.le =>
    F05NonlinearCorrection h T p (F05CanonicalJetFunction A χ α hT.le z)
  have hDiff (u v : F05CompatibleJetGraph A α hT.le) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (i : Fin A.count) :
      HolderBound α (F05Q A i T) (fun q => pull A i (F u) q-pull A i (F v) q)
        ((C*T^((1-α)/2))*‖u-v‖) := by
    simpa only [hPower] using hLipT u v hu hv i
  have hInit (u : F05CompatibleJetGraph A α hT.le) (_ : ‖u‖ ≤ 1) (x : M.Carrier) (_ : x ∈ closure O) : F u x 0 = 0 :=
    F05_nonlinear_initial_general h T p _
      (F05CanonicalJetFunction_initial A χ α hT.le u) (hCompat T hT hTS) x
  have hCanon0 : F05CanonicalJetFunction A χ α hT.le 0 = (fun _ _ => 0) := by
    funext x t
    simp only [← F05CanonicalJetLinear_apply,map_zero,Pi.zero_apply]
  have hZeroT (i : Fin A.count) : HolderBound α (F05Q A i T) (pull A i (F 0)) (F₀*T^((1-α)/2)) := by
    dsimp only [F]
    rw [hCanon0]
    exact hZero T hT hTS hT1 i
  obtain ⟨N,hNValue,hN0,hNLip⟩ := F05_actual_source_ball hA hα hT.le (by norm_num : (0 : ℝ) < 1)
    (mul_nonneg hC.le hPow) (mul_nonneg hF₀.le hPow) F hDiff hInit hZeroT
  obtain ⟨L,Binv,hL,hBinv,hLB,hBL,hLValue⟩ := hInverse T hT hTδ
  have hSmallLip : ‖Binv‖*(C*T^((1-α)/2)) ≤ (1/2 : ℝ) := by
    have hStep := mul_le_mul_of_nonneg_right hBinv (mul_nonneg hC.le hPow)
    have hBound := mul_le_mul_of_nonneg_right hCE hPow
    nlinarith
  have hSmallZero : ‖Binv‖*‖N 0‖ ≤ (1 : ℝ)/2 := by
    have hStep := mul_le_mul hBinv hN0 (norm_nonneg _) hCB.le
    have hBound := mul_le_mul_of_nonneg_right hFE hPow
    nlinarith
  obtain ⟨z,hz,hEquation⟩ := F05_contraction_equation L Binv hLB N (by norm_num : (0 : ℝ) < 1)
    (mul_nonneg hC.le hPow) hNLip hSmallLip hSmallZero
  refine ⟨z,hz,?_⟩
  intro x hx t ht
  obtain ⟨i,y,hy,heq⟩ := F05_cover hA hx
  have hyT : (y,t) ∈ F05Q A i T := ⟨hy,ht⟩
  have hAt := congrArg (fun f : F05SourceZeroGraph A α T => holderGraphFun (f.val i) (y,t)) hEquation
  rw [hLValue z i ⟨(y,t),hyT⟩,hNValue z hz i ⟨(y,t),hyT⟩] at hAt
  rw [F05JetOperator_eq_intrinsic hA hχ c h α hT z i hyT] at hAt
  change F05IntrinsicLinearOperator c h T (F05CanonicalJetFunction A χ α hT.le z) (lift A i y) t = F z (lift A i y) t at hAt
  rw [heq] at hAt
  exact F05_nonlinear_correction_recompose hA h T p _ (hP2 T hT hTS)
    (fun j => (F05CanonicalJetFunction_realizes hA hχ α hT z j).1) hx ht hAt

end Yau.Proofs.F05Aux
