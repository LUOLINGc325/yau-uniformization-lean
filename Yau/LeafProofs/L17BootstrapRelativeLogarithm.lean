import Yau.LeafProofs.L17MatrixLogarithmHolder
import Yau.LeafProofs.L17MatrixLogDetPath

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17LocalHolderBanachAlgebraAux
local instance relativeLogMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T gamma : ℝ)

def relativeMetricRadius
    (K : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma) (lambda : ℝ) : ℝ :=
  min lambda (1/(8*(1+‖K‖)))

theorem relativeMetricRadius_pos
    (K : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    {lambda : ℝ} (hlambda : 0<lambda) : 0<relativeMetricRadius P T gamma K lambda :=
  lt_min hlambda (by positivity)

def relativeMetricPerturbation
    (K Hstar H : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma) :
    LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma := K*(H-Hstar)

theorem relativeMetricPerturbation_norm_lt
    (K Hstar H : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (lambda : ℝ) (hH : ‖H-Hstar‖<relativeMetricRadius P T gamma K lambda) :
    ‖relativeMetricPerturbation P T gamma K Hstar H‖<1/8 := by
  calc
    _ ≤ ‖K‖*‖H-Hstar‖ := norm_mul_le _ _
    _ ≤ ‖K‖*relativeMetricRadius P T gamma K lambda :=
      mul_le_mul_of_nonneg_left hH.le (norm_nonneg K)
    _ ≤ ‖K‖*(1/(8*(1+‖K‖))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (norm_nonneg K)
    _ < 1/8 := by
      rw [mul_one_div]
      apply (div_lt_iff₀ (by positivity : 0<8*(1+‖K‖))).mpr
      nlinarith [norm_nonneg K]

def relativeTraceLog
    (K Hstar H : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma) :
    LocalHolderBanach ℝ P T gamma :=
  matrixTraceLogIncrement P T gamma (relativeMetricPerturbation P T gamma K Hstar H)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

theorem relativeTraceLog_contDiffOn
    (K Hstar : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    {H : E → LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma}
    (hH : ContDiffOn ℝ ∞ H s)
    (hSmall : ∀ a∈s, ‖relativeMetricPerturbation P T gamma K Hstar (H a)‖<1) :
    ContDiffOn ℝ ∞ (fun a => relativeTraceLog P T gamma K Hstar (H a)) s := by
  exact (matrixTraceLogIncrement_contDiffOn P T gamma).comp
    (contDiffOn_const.mul (hH.sub contDiffOn_const))
    (fun a ha => by simpa only [mem_ball,dist_zero_right] using hSmall a ha)

theorem relativeTraceLog_value
    (K Hstar H : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (hK : ∀ q : LocalCylinder P T, K q=(Hstar q)⁻¹)
    (hBase : ∀ q : LocalCylinder P T, (Hstar q).PosDef)
    (hH : ∀ q : LocalCylinder P T, (H q).PosDef)
    (hSmall : ‖relativeMetricPerturbation P T gamma K Hstar H‖<1)
    (q : LocalCylinder P T) :
    relativeTraceLog P T gamma K Hstar H q=Real.log ((H q).det.re/(Hstar q).det.re) := by
  let Z := relativeMetricPerturbation P T gamma K Hstar H
  have hEval : ‖Z q‖ ≤ ‖Z‖ := by
    exact (localValue_norm_le _ Z.value q).trans
      ((norm_value_le_half _ P T gamma Z).trans (by nlinarith [norm_nonneg Z]))
  have hPoint : ‖(Hstar q)⁻¹*(H q-Hstar q)‖<1 := by
    have hForm : Z q=(Hstar q)⁻¹*(H q-Hstar q) := by
      change K q*(H q-Hstar q)=_
      rw [hK q]
    rw [←hForm]
    exact hEval.trans_lt hSmall
  rw [relativeTraceLog,matrixTraceLogIncrement_value P T gamma _ hSmall]
  change (Matrix.trace (L17BanachLogarithmAux.logIncrement _
    (K q*(H q-Hstar q)))).re=_
  rw [hK q]
  have hEnd : (Hstar q+(H q-Hstar q)).PosDef := by simpa only [add_sub_cancel] using hH q
  simpa only [add_sub_cancel] using
    matrixTraceLogIncrement_eq_logdet_ratio (Hstar q) (H q-Hstar q) (hBase q) hEnd hPoint

end Yau.LeafProofs.L17BootstrapMetricAux
