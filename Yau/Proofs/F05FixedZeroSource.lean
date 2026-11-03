import Yau.Proofs.F05SmoothLaplacian
import Yau.Proofs.F05SmoothTimeJets
import Yau.Proofs.F05NonlinearInitial

/-! The zero-correction source is a fixed actual smooth function, independent
of the moving endpoint on its own slab. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_nonlinear_zero_formula (h : ℝ → HermitianField M) (T : ℝ)
    (p : M.Carrier → ℝ → ℝ) (x : M.Carrier) (t : ℝ) :
    F05NonlinearCorrection h T p (fun _ _ => 0) x t =
      (1-Real.exp (-p x t))*scalarCurvature (h t) x-derivWithin (p x) (Icc 0 T) t+
        Real.exp (-p x t)*laplacian (h t) (fun y => p y t) x := by
  unfold F05NonlinearCorrection F05IntrinsicLinearOperator
  simp only [add_zero,sub_self,zero_mul,zero_add]
  ring

theorem F05_derivWithin_Icc_restrict {f : ℝ → ℝ} {S T t : ℝ}
    (hT : 0 < T) (hTS : T ≤ S) (ht : t ∈ Icc 0 T)
    (hf : DifferentiableWithinAt ℝ f (Icc 0 S) t) :
    derivWithin f (Icc 0 T) t = derivWithin f (Icc 0 S) t :=
  (hf.hasDerivWithinAt.mono (show Icc (0 : ℝ) T ⊆ Icc 0 S from
    fun _ hs => ⟨hs.1,hs.2.trans hTS⟩)).derivWithin (uniqueDiffOn_Icc hT t ht)

theorem F05_nonlinear_zero_restrict {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (p : M.Carrier → ℝ → ℝ)
    {S T : ℝ} (hp : SmoothSpaceTime p (Icc 0 S)) (hT : 0 < T) (hTS : T ≤ S)
    (i : Fin A.count) {q : Point n} (hq : q ∈ Metric.ball 0 3 ×ˢ Icc 0 T) :
    pull A i (F05NonlinearCorrection h T p (fun _ _ => 0)) q =
      pull A i (F05NonlinearCorrection h S p (fun _ _ => 0)) q := by
  have hφ := F05_pull_spacetime_smooth hA p hp i
  have hSlice : ContDiffOn ℝ ∞ (fun t => p (lift A i q.1) t) (Icc 0 S) :=
    hφ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun t ht => ⟨hq.1,ht⟩)
  have hDeriv := F05_derivWithin_Icc_restrict hT hTS hq.2
    (hSlice.differentiableOn (by simp) q.2 ⟨hq.2.1,hq.2.2.trans hTS⟩)
  unfold pull
  rw [F05_nonlinear_zero_formula,F05_nonlinear_zero_formula,hDeriv]

theorem F05_pull_zero_source_smooth {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (p : M.Carrier → ℝ → ℝ)
    {S : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hp : SmoothSpaceTime p (Icc 0 S))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 S)) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (pull A i (F05NonlinearCorrection h S p (fun _ _ => 0)))
      (Metric.ball 0 3 ×ˢ Icc 0 S) := by
  have hφ := F05_pull_spacetime_smooth hA p hp i
  have hExp := hφ.neg.exp
  have hScalar := F05_pull_spacetime_smooth hA _ hR i
  have hLap := F05_pull_laplacian_smooth hA h p hh hp i
  have hTime := F05_joint_time_derivative_smooth (uniqueDiffOn_Icc hS) hφ
  have hExpr := ((((contDiffOn_const (c := (1 : ℝ))).sub hExp).mul hScalar).sub hTime).add (hExp.mul hLap)
  apply hExpr.congr
  intro q hq
  exact F05_nonlinear_zero_formula h S p (lift A i q.1) q.2

end Yau.Proofs.F05Aux
