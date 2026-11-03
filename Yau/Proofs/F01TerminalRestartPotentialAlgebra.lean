import Yau.Proofs.F01FlowRebaseAlgebra
import Yau.Proofs.F01LogDetRatioSmooth

/-! The potential of a restarted native flow is lifted back to the
original background by its computed determinant correction. The
original clock and potential identity are retained. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

def liftedRestartPotential (g K : HermitianField M) (u : M.Carrier → ℝ)
    (V : M.Carrier → ℝ → ℝ) (x : M.Carrier) (s : ℝ) : ℝ :=
  u x + V x s + s * flowLogDetRatio g (fun _ => K) x 0

theorem liftedRestartPotential_initial
    (g K : HermitianField M) (u : M.Carrier → ℝ) (V : M.Carrier → ℝ → ℝ)
    (hV0 : ∀ x, V x 0 = 0) (x : M.Carrier) : liftedRestartPotential g K u V x 0 = u x := by
  simp only [liftedRestartPotential, hV0, add_zero, zero_mul]

theorem liftedRestartPotential_smooth
    (g K : HermitianField M) (hg : MetricSmooth g) (hK : MetricSmooth K)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (V : M.Carrier → ℝ → ℝ)
    {I : Set ℝ} (hV : SmoothSpaceTime V I) : SmoothSpaceTime (liftedRestartPotential g K u V) I := by
  have hRatio : SmoothFn (fun x => flowLogDetRatio g (fun _ => K) x 0) :=
    smoothSpaceTime_slice (flowLogDetRatio_smoothSpaceTime g hg (fun _ => K)
      (metricFamilySmooth_const hK univ)) (mem_univ (0 : ℝ))
  intro a
  exact (((hu a).comp contDiffOn_fst (fun _ hp => hp.1)).add (hV a)).add
    (contDiffOn_snd.mul ((hRatio a).comp contDiffOn_fst (fun _ hp => hp.1)))

theorem lifted_restart_metric_potential_identity
    (g K : HermitianField M) (hg : MetricSmooth g) (hK : MetricSmooth K)
    (u : M.Carrier → ℝ) (hu : SmoothFn u)
    (h : ℝ → HermitianField M) (V : M.Carrier → ℝ → ℝ) (T s : ℝ)
    (hVs : SmoothFn (fun x => V x s))
    (hTerminal : ∀ x, gMat K x = gMat g x - (T : ℂ) • ricci g x + levi u x)
    (hRestart : ∀ x, gMat (h s) x = gMat K x - (s : ℂ) • ricci K x + levi (fun y => V y s) x) :
    ∀ x, gMat (h s) x = gMat g x - ((T + s : ℝ) : ℂ) • ricci g x +
      levi (fun y => liftedRestartPotential g K u V y s) x := by
  have hRatio : SmoothFn (fun x => flowLogDetRatio g (fun _ => K) x 0) :=
    smoothSpaceTime_slice (flowLogDetRatio_smoothSpaceTime g hg (fun _ => K)
      (metricFamilySmooth_const hK univ)) (mem_univ (0 : ℝ))
  have hSum : SmoothFn (fun x => u x + V x s) := fun a => (hu a).add (hVs a)
  have hMultiple : SmoothFn (fun x => s * flowLogDetRatio g (fun _ => K) x 0) :=
    fun a => contDiffOn_const.mul (hRatio a)
  intro x
  have hLevi : levi (fun y => flowLogDetRatio g (fun _ => K) y 0) x = -ricci K x + ricci g x :=
    levi_logdet_ratio_native K g hK hg x
  unfold liftedRestartPotential
  rw [levi_add_native hSum hMultiple, levi_add_native hu hVs,
    levi_const_mul_native hRatio s, hLevi, hRestart x, hTerminal x]
  simp only [Complex.ofReal_add, add_smul, smul_add, smul_neg]
  abel

end Yau.NodeProofs.F01Aux
