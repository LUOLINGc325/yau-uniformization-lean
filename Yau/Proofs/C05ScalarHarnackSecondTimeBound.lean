import Yau.Proofs.C05NormalizedHarnackRegularity
import Yau.Proofs.C05ScalarTimeSourceBounds

/-! The actual second normalized-time derivative has a uniform budget
from scalar/Ricci jets and the original inverse-clock bound alone. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05Aux
open Yau Blueprint
open Yau.Proofs.C05NormalizedScalarTimeEvolutionAux Yau.Proofs.C05ScalarTimeSourceBoundsAux
variable {n : ℕ} {M : ComplexManifold n} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

def scalarHarnackSecondTimeBudget (n : ℕ) (B K : ℝ) : ℝ :=
  b3 n B+K*b2 n B+2*K^2*b1 n B+2*K^3*B

theorem scalarHarnackSecondTimeBudget_nonneg (n : ℕ) {B K : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) : 0 ≤ scalarHarnackSecondTimeBudget n B K := by
  have h1 := b1_nonneg n hB
  have h2 := b2_nonneg n hB
  have h3 := b3_nonneg n hB
  unfold scalarHarnackSecondTimeBudget
  positivity

theorem intrinsicScalarHarnackSecondTime_abs_le (k : HermitianField M)
    (hk : MetricSmooth k) (hK : KahlerClosed k) (κ : ℝ) (x : M.Carrier)
    {B K : ℝ} (hB : 0 ≤ B) (hK0 : 0 ≤ K) (hκ : |κ| ≤ K)
    (hScalar : ∀ j ≤ 6, scalarJetNorm k (scalarCurvature k) j x ≤ B)
    (hRicci : ∀ j ≤ 4, realRicciJetNorm k j x ≤ B) :
    |intrinsicScalarHarnackSecondTime k κ x| ≤ scalarHarnackSecondTimeBudget n B K := by
  have h1 : |scalarTimeSource1 k x| ≤ b1 n B := by
    simpa only [scalarJetNorm_zero] using source1_jet_bound k hk hK 0 (by norm_num) x hB hScalar hRicci
  have h2 : |scalarTimeSource2 k x| ≤ b2 n B := by
    simpa only [scalarJetNorm_zero] using source2_jet_bound k hk hK 0 (by norm_num) x hB hScalar hRicci
  have h3 := source3_abs_bound k hk hK x hB hScalar hRicci
  have h0 : |scalarCurvature k x| ≤ B := by
    simpa only [scalarJetNorm_zero] using hScalar 0 (by norm_num)
  have hsum : |intrinsicScalarHarnackSecondTime k κ x| ≤
      |scalarTimeSource3 k x| + |κ| * |scalarTimeSource2 k x| + 
        2* |κ|^2* |scalarTimeSource1 k x| + 2* |κ|^3* |scalarCurvature k x| := by
    have ha := abs_add_le (scalarTimeSource3 k x) (κ*scalarTimeSource2 k x)
    have hb : |scalarTimeSource3 k x+κ*scalarTimeSource2 k x-2*κ^2*scalarTimeSource1 k x| ≤
        |scalarTimeSource3 k x+κ*scalarTimeSource2 k x| + |2*κ^2*scalarTimeSource1 k x| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le
        (scalarTimeSource3 k x+κ*scalarTimeSource2 k x) (-(2*κ^2*scalarTimeSource1 k x))
    have hc := abs_add_le (scalarTimeSource3 k x+κ*scalarTimeSource2 k x-
      2*κ^2*scalarTimeSource1 k x) (2*κ^3*scalarCurvature k x)
    simp only [abs_mul,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<2)] at ha hb hc
    unfold intrinsicScalarHarnackSecondTime
    linarith
  apply hsum.trans
  unfold scalarHarnackSecondTimeBudget
  gcongr

theorem normalized_scalarHarnack_second_deriv_abs_le (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (ti R : ℝ) (hR : 0 < R) (x : Pt X)
    (z : ℝ) (ht : 0 < ti+z/R) {B K : ℝ} (hB : 0 ≤ B) (hK0 : 0 ≤ K)
    (hκ : |(ti*R+z)⁻¹| ≤ K)
    (hScalar : ∀ j ≤ 6, scalarJetNorm (normalizedMetric h ti R hR z)
      (scalarCurvature (normalizedMetric h ti R hR z)) j x ≤ B)
    (hRicci : ∀ j ≤ 4, realRicciJetNorm (normalizedMetric h ti R hR z) j x ≤ B) :
    |iteratedDeriv 2 (fun w => scalarHarnackSource (normalizedMetric h ti R hR w) (ti*R+w)⁻¹ x) z| ≤
      scalarHarnackSecondTimeBudget n B K := by
  have hbase := Yau.LeafProofs.L23Aux.metricFamilySmooth_slice h hf.1.2.1 ht.le
  have hk := C04RescaledTubeAux.metricSmooth_scale R hR (h (ti+z/R)) hbase
  have hK := C04RescaledTubeAux.kahlerClosed_scale R hR (h (ti+z/R)) hbase
    (hf.1.2.2.1 (ti+z/R) ht.le)
  rw [normalized_scalarHarnack_iteratedDeriv_two o h U P ρ hf ti R hR x z ht]
  exact intrinsicScalarHarnackSecondTime_abs_le _ hk hK _ x hB hK0 hκ hScalar hRicci

end Yau.Proofs.C05Aux
