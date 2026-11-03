import Yau.Proofs.V03ExponentialBounds
import Yau.Proofs.V03CirclePeriod
import Yau.Proofs.V03Walls

/-! The actual powered wall trace is controlled by the original
logarithmic Fourier energy with the precise exponent-dependent factor. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n r : ℕ} {X : KahlerManifold n}

theorem admissible_logTrace_nonpos {d : VariationData X r} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (θ : ℝ) :
    logTrace d j F.f θ ≤ 0 := by
  have hp := admissible_wallProduct_bounds hd hF θ
  exact Real.log_nonpos hp.1.le hp.2

theorem wallPower_trace_eq_exp {d : VariationData X r} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (a : ℕ) :
    (fun θ => wallPower d j a (F.f (circlePoint θ))) =
      fun θ => Real.exp ((a : ℝ) * logTrace d j F.f θ) := by
  funext θ
  unfold wallPower logTrace
  rw [Real.exp_nat_mul, Real.exp_log (admissible_wallProduct_bounds hd hF θ).1]

theorem wallPower_scalarDSq_le_logTrace {d : VariationData X r} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (a : ℕ) :
    scalarDSq (fun θ => wallPower d j a (F.f (circlePoint θ))) ≤
      ENNReal.ofReal ((a : ℝ) ^ 2) * scalarDSq (logTrace d j F.f) := by
  rw [wallPower_trace_eq_exp hd hF a]
  exact scalarDSq_exp_nonpos_le (admissible_logTrace_contDiff hd hF).continuous
    (logTrace_periodic d j F) (admissible_logTrace_nonpos hd hF) (by positivity)

end Yau.Blueprint.V03Proof
