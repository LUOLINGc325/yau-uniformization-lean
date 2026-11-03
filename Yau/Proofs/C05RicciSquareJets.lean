import Yau.Proofs.C05RicciSquareJetsGeneric

/-! The actual scalar Ricci-square jets, with a uniform finite-order budget. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05RicciSquareJetsAux
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem scalarJet_ricciNormSq_terms (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (c : M.Carrier) (m : ℕ)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (v : Fin m → RIdx n) :
    scalarJet k (ricciNormSq k) c m z v =
      (1/2:ℝ) * evalTerms (ricciSquareTerms m) k c z v := by
  induction m generalizing z with
  | zero =>
      change inChart c (ricciNormSq k) z = _
      rw [ricciNormSq_inChart k hk hK c hz]
      simp only [ricciSquareTerms,evalTerms,ricciSquareTermZero,RicciTerm.eval,
        List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,ricciSquareWord_eval]
  | succ m ih =>
      have hE : scalarJet k (ricciNormSq k) c m =ᶠ[𝓝 z]
          (fun w v => (1/2:ℝ) * evalTerms (ricciSquareTerms m) k c w v) := by
        filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
        funext u
        exact ih hw u
      have hd (u : Fin m → RIdx n) :=
        ((evalTerms_contDiffOn (ricciSquareTerms m) k hk c u).contDiffAt
          ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      change covariantD k c (scalarJet k (ricciNormSq k) c m) z v = _
      rw [covariantD_eventuallyEq k c _ _ z hE,
        covariantD_const_mul_at k c _ z hd,covariantD_evalTerms _ k hk c hz]
      rfl

theorem scalarJetNorm_ricciNormSq_le (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (m : ℕ) (hm : m ≤ 3) (x : M.Carrier)
    {B : ℝ} (hB : 0 ≤ B) (hR : ∀ j ≤ 3, realRicciJetNorm k j x ≤ B) :
    scalarJetNorm k (ricciNormSq k) m x ≤ 8 * (2*n:ℕ) * B ^ 2 := by
  have he : scalarJet k (ricciNormSq k) x m (chartPt x x) =
      fun v => (1/2:ℝ) * evalTerms (ricciSquareTerms m) k x (chartPt x x) v := by
    funext v
    exact scalarJet_ricciNormSq_terms k hk hK x m (mem_extChartAt_target x) v
  have H := evalTerms_norm_le (ricciSquareTerms m) hm k x hB hR
  have hcount : ((ricciSquareTerms m).length : ℝ) ≤ 8 := by
    rw [ricciSquareTerms_length]
    interval_cases m <;> norm_num
  have hn : (0:ℝ) ≤ (2*n:ℕ) * B^2 := by positivity
  unfold scalarJetNorm
  rw [he,sqrt_covTensorNormSq_const_mul]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  calc
    _ ≤ (1/2:ℝ) * ((ricciSquareTerms m).length:ℝ) * (2*n:ℕ) * B^2 := by
      simpa only [metricTensorNorm,mul_assoc] using mul_le_mul_of_nonneg_left H (by norm_num : (0:ℝ)≤1/2)
    _ ≤ (1/2:ℝ) * 8 * (2*n:ℕ) * B^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hcount hn]
    _ ≤ _ := by nlinarith

theorem scalarJetNorm_ricciNormSq_le_four (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (m : ℕ) (hm : m ≤ 4) (x : M.Carrier)
    {B : ℝ} (hB : 0 ≤ B) (hR : ∀ j ≤ 4, realRicciJetNorm k j x ≤ B) :
    scalarJetNorm k (ricciNormSq k) m x ≤ 16 * (2*n:ℕ) * B ^ 2 := by
  have he : scalarJet k (ricciNormSq k) x m (chartPt x x) =
      fun v => (1/2:ℝ) * evalTerms (ricciSquareTerms m) k x (chartPt x x) v := by
    funext v
    exact scalarJet_ricciNormSq_terms k hk hK x m (mem_extChartAt_target x) v
  have H := evalTerms_norm_le (ricciSquareTerms m) hm k x hB hR
  have hcount : ((ricciSquareTerms m).length : ℝ) ≤ 16 := by
    rw [ricciSquareTerms_length]
    interval_cases m <;> norm_num
  have hn : (0:ℝ) ≤ (2*n:ℕ) * B^2 := by positivity
  unfold scalarJetNorm
  rw [he,sqrt_covTensorNormSq_const_mul]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  calc
    _ ≤ (1/2:ℝ) * ((ricciSquareTerms m).length:ℝ) * (2*n:ℕ) * B^2 := by
      simpa only [metricTensorNorm,mul_assoc] using mul_le_mul_of_nonneg_left H (by norm_num : (0:ℝ)≤1/2)
    _ ≤ (1/2:ℝ) * 16 * (2*n:ℕ) * B^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hcount hn]
    _ ≤ _ := by nlinarith

end Yau.Proofs.C05RicciSquareJetsAux
