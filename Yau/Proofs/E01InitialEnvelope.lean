import Yau.Proofs.E01CentralDual
import Yau.Proofs.E01InitialDiscMean
import Yau.Proofs.E01EnvelopeBounds

/-! The genuine initial dual circle mean and the resulting original chart-envelope lower bound. -/

noncomputable section
open scoped Matrix

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem initial_cotangent_disc_mean (X : KahlerManifold n)
    (f : ℂ → Pt X) (ξd : ℂ → Covector n) (hd : IsCotangentDisc f ξd) :
    dualNorm X.metric.form (f 0) (ξd 0) ≤ circleAverage (fun θ =>
      dualNorm X.metric.form (f (Complex.exp (θ * Complex.I))) (ξd (Complex.exp (θ * Complex.I)))) :=
  initial_disc_mean_of_centered_dual_levi_nonneg X (initial_centered_dual_levi_nonneg X) f ξd hd

theorem envelopeChart_actual_initial_lower {X : KahlerManifold n}
    {o : Pt X} {h : Flow X} {U P ρ : STF X} (hloc : LocalizedFlow X o h U P ρ)
    (T : ℝ) (x : Pt X) (z η : ComplexVector n) (t : ℝ)
    (hz : z ∈ chartTarget x) (ht : t ∈ Set.Ioo 0 T) :
    (dualNormChart X.metric.form x z η : EReal) ≤ envelopeChart h T x (z, η, t) :=
  envelopeChart_lower_of_initial_circle_mean hloc (initial_cotangent_disc_mean X) T x z η t hz ht

end Yau.NodeProofs.E01Aux
