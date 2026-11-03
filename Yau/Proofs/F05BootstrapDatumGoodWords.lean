import Yau.Proofs.F05BootstrapDatumEquation
import Yau.Proofs.F05BootstrapNonlinearGoodWords
import Yau.Proofs.F05BootstrapSmoothLocalSchauder
import Yau.Proofs.F05BootstrapRelativeCongruence

/-! The full good-word induction for the original physical datum. The
subtraction is performed once at the original equation, and every new
coefficient and source word is constructed by the finite nonlinear proof. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2400000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ}

theorem F05_local_schauder_congr {ν : Option (RIdx n)} {T α : ℝ} {f g : Point n → ℝ}
    (hf : F05LocalSchauder α ν T f) (hEq : EqOn f g (F05PosPatch ν T)) :
    F05LocalSchauder α ν T g := by
  intro r hr hr2 s hs hsT
  obtain ⟨C,hC,hSch⟩ := hf r hr hr2 s hs hsT
  exact ⟨C,hC,F05_relative_schauder_congr hSch (fun z hz =>
    hEq (F05_receiving_subset_posPatch ν hr2 hs hz))⟩

theorem F05_physical_datum_nonlinear_good_words {ν : Option (RIdx n)} {T α lam upper : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1)
    (A : Point n → Mat n) (B : Point n → RIdx n → ℝ) (R p u : Point n → ℝ)
    (hA : ContDiffOn ℝ ∞ A (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hB : ∀ j, ContDiffOn ℝ ∞ (fun z => B z j) (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hR : ContDiffOn ℝ ∞ R (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hp : ContDiffOn ℝ ∞ p (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hu : F05LocalSchauder α ν T u) (hFace : F05ZeroFace ν T (fun z => u z-p z))
    (hEll : Elliptic (F05PosPatch ν T) (fun z => Real.exp (-u z) • A z) lam upper)
    (hPDE : ∀ z ∈ F05PosPatch ν T,
      F05RelOp (F05PosSpace ν) (Ioc 0 T) (fun z => Real.exp (-u z) • A z)
        (fun z j => Real.exp (-u z)*B z j) u z = (1-Real.exp (-u z))*R z) :
    ∀ β : List (Option (RIdx n)), F05GoodList ν β →
      F05LocalSchauder α ν T (F05GoodWord T β u) := by
  let v : Point n → ℝ := fun z => u z-p z
  have hPRegular := F05_smooth_background_local_schauder (ν := ν) hα hα1 hp
  have hV := F05_local_schauder_sub hu hPRegular
  have hCoefficients := F05_datum_coefficients_smooth A B R p hA hB hR hp
  have hEllV : Elliptic (F05PosPatch ν T)
      (fun z => Real.exp (-v z) • F05DatumPrincipal p A z) lam upper := by
    change Elliptic (F05PosPatch ν T)
      (fun z => Real.exp (-(u z-p z)) • F05DatumPrincipal p A z) lam upper
    rw [F05_datum_principal_identity]
    exact hEll
  have hEquation := F05_subtract_datum_equation A B R p u hp (F05_local_schauder_to_relative hu) hPDE
  have hWords := F05_zero_trace_nonlinear_good_words hT hα hα1
    (F05DatumPrincipal p A) (F05DatumDrift p B) (F05DatumSource p A B R) (F05DatumFree T p R) v
    hCoefficients.1 hCoefficients.2.1 hCoefficients.2.2.1 hCoefficients.2.2.2 hV hFace hEllV hEquation
  have hRecover : u = fun z => v z+p z := by funext z; dsimp only [v]; ring
  intro β hβ
  have hPV := F05_smooth_background_good_words Metric.isOpen_ball hp β
  have hSum := F05_local_schauder_add (hWords β hβ).1
    (F05_smooth_background_local_schauder (ν := ν) hα hα1 hPV)
  have hEq : EqOn (F05GoodWord T β u)
      (fun z => F05GoodWord T β v z+F05GoodWord T β p z) (F05PosPatch ν T) := by
    rw [hRecover]
    exact F05_good_word_add β v p hβ
      (fun γ hLen hGood d hd => F05_local_schauder_good_diff hd (hWords γ hGood).1)
      (fun γ hLen hGood d hd => F05_smooth_background_good_diff
        (F05_smooth_background_good_words Metric.isOpen_ball hp γ) d)
  exact F05_local_schauder_congr hSum (fun z hz => (hEq hz).symm)

end Yau.Proofs.F05Aux
