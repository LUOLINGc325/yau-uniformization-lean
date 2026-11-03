import Yau.Proofs.C05ScalarLaplacianJets

/-! Linearity of every actual scalar covariant jet and its metric norm. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05Aux
open Yau Yau.Proofs.C05HessianPropagationAux
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem scalarJet_add (k : HermitianField M) (hk : MetricSmooth k)
    (f g : M.Carrier → ℝ) (hf : SmoothFn f) (hg : SmoothFn g)
    (c : M.Carrier) (m : ℕ) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    scalarJet k (fun y => f y + g y) c m z = scalarJet k f c m z + scalarJet k g c m z := by
  induction m generalizing z with
  | zero => rfl
  | succ m ih =>
      have he : scalarJet k (fun y => f y + g y) c m =ᶠ[𝓝 z]
          (fun w => scalarJet k f c m w + scalarJet k g c m w) := by
        filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
        exact ih hw
      have hfd (v : Fin m → RIdx n) := ((scalarJet_contDiffOn k hk f hf c m v).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      have hgd (v : Fin m → RIdx n) := ((scalarJet_contDiffOn k hk g hg c m v).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      change covariantD k c _ z = _
      rw [covariantD_eventuallyEq k c _ _ z he,covariantD_add_at k c _ _ z hfd hgd]
      rfl

theorem scalarJet_const_mul (k : HermitianField M) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (a : ℝ)
    (c : M.Carrier) (m : ℕ) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    scalarJet k (fun y => a * f y) c m z = fun v => a * scalarJet k f c m z v := by
  induction m generalizing z with
  | zero => rfl
  | succ m ih =>
      have he : scalarJet k (fun y => a * f y) c m =ᶠ[𝓝 z]
          (fun w v => a * scalarJet k f c m w v) := by
        filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
        exact ih hw
      have hfd (v : Fin m → RIdx n) := ((scalarJet_contDiffOn k hk f hf c m v).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      change covariantD k c _ z = _
      rw [covariantD_eventuallyEq k c _ _ z he,covariantD_const_mul_at k c _ z hfd]
      rfl

theorem scalarJetNorm_add_le (k : HermitianField M) (hk : MetricSmooth k)
    (f g : M.Carrier → ℝ) (hf : SmoothFn f) (hg : SmoothFn g) (m : ℕ) (x : M.Carrier) :
    scalarJetNorm k (fun y => f y + g y) m x ≤ scalarJetNorm k f m x + scalarJetNorm k g m x := by
  unfold scalarJetNorm
  rw [scalarJet_add k hk f g hf hg x m (z := chartPt x x) (mem_extChartAt_target x)]
  exact sqrt_covTensorNormSq_add_le _ (realMetricFn_posDef k x _ (mem_extChartAt_target x)) _ _

theorem scalarJetNorm_const_mul (k : HermitianField M) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (a : ℝ) (m : ℕ) (x : M.Carrier) :
    scalarJetNorm k (fun y => a * f y) m x = |a| * scalarJetNorm k f m x := by
  unfold scalarJetNorm
  rw [scalarJet_const_mul k hk f hf a x m (z := chartPt x x) (mem_extChartAt_target x),sqrt_covTensorNormSq_const_mul]

theorem scalarJetNorm_nonneg (k : HermitianField M) (f : M.Carrier → ℝ)
    (m : ℕ) (x : M.Carrier) : 0 ≤ scalarJetNorm k f m x := Real.sqrt_nonneg _

theorem scalarJetNorm_zero (k : HermitianField M) (f : M.Carrier → ℝ) (x : M.Carrier) :
    scalarJetNorm k f 0 x = |f x| := by
  have hi : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  simp [scalarJetNorm,scalarJet,covTensorNormSq,inChart,hi,Real.sqrt_sq_eq_abs,← sq]

end Yau.Proofs.C05Aux
