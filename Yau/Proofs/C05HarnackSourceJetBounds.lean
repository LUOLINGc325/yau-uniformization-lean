import Yau.Proofs.C05ScalarHarnackScaling
import Yau.Proofs.G01RicciNormalization

/-! Intrinsic spatial bounds for the actual normalized scalar Harnack source. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05Aux
open Yau Blueprint Yau.Proofs.C05HessianPropagationAux
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem scalarCurvature_smoothFn (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) : SmoothFn (scalarCurvature k) := by
  intro c
  have hF : ContDiffOn ℝ ∞ (fun z => (1/2:ℝ) * realScalarCurvatureInChart k c z)
      (chartTarget c) := by
    apply contDiffOn_const.mul
    apply ContDiffOn.sum
    intro a _
    apply ContDiffOn.sum
    intro b _
    exact (Yau.LeafProofs.L23Aux.realMetricFn_inverse_contDiffOn k hk c a b).mul
      (realRicciCoeff_contDiffOn k hk c a b)
  apply hF.congr
  intro z hz
  have he := Yau.NodeProofs.G01Aux.realScalarCurvatureInChart_eq k hk hK c z hz
  change scalarCurvature k (chartInv c z) = _
  linarith

theorem ricciNormSq_smoothFn (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) : SmoothFn (ricciNormSq k) := by
  intro c
  have hR := realRicciJet_contDiffOn k hk c 0
  have hF := chartTensorPair_contDiffOn k hk c (realRicciJet k c 0) (realRicciJet k c 0) hR hR
  exact (contDiffOn_const.mul hF).congr (fun z hz => ricciNormSq_inChart k hk hK c hz)

theorem laplacian_smoothFn (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (f : M.Carrier → ℝ) (hf : SmoothFn f) :
    SmoothFn (laplacian k f) := by
  intro c
  have hA := scalarJet_contDiffOn k hk f hf c 2
  have hF := singleTraceEval_contDiffOn (scalarLapTraceWord 0) k hk c _ hA Fin.elim0
  exact (contDiffOn_const.mul hF).congr (fun z hz =>
    scalarJet_laplacian_trace k hk hK f hf c 0 hz Fin.elim0)

theorem scalarHarnackSource_smoothFn (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (κ : ℝ) : SmoothFn (scalarHarnackSource k κ) := by
  have hR := scalarCurvature_smoothFn k hk hK
  have hL := laplacian_smoothFn k hk hK _ hR
  have hA := ricciNormSq_smoothFn k hk hK
  intro c
  exact ((hL c).add (hA c)).add (contDiffOn_const.mul (hR c))

theorem scalarJetNorm_scalarHarnackSource_le (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (κ : ℝ) (m : ℕ) (x : M.Carrier) :
    scalarJetNorm k (scalarHarnackSource k κ) m x ≤
      (Real.sqrt (2*n:ℕ) / 2) * scalarJetNorm k (scalarCurvature k) (2+m) x +
        scalarJetNorm k (ricciNormSq k) m x + |κ| * scalarJetNorm k (scalarCurvature k) m x := by
  have hR := scalarCurvature_smoothFn k hk hK
  have hL := laplacian_smoothFn k hk hK _ hR
  have hA := ricciNormSq_smoothFn k hk hK
  have hsum : SmoothFn (fun y => laplacian k (scalarCurvature k) y + ricciNormSq k y) :=
    fun c => (hL c).add (hA c)
  have hκ : SmoothFn (fun y => κ * scalarCurvature k y) := fun c => contDiffOn_const.mul (hR c)
  have h₁ := scalarJetNorm_add_le k hk _ _ hL hA m x
  have h₂ := scalarJetNorm_add_le k hk _ _ hsum hκ m x
  have h₃ := scalarJetNorm_laplacian_le k hk hK _ hR m x
  rw [scalarJetNorm_const_mul k hk _ hR κ m x] at h₂
  change scalarJetNorm k (scalarHarnackSource k κ) m x ≤ _ at h₂
  linarith

end Yau.Proofs.C05Aux
