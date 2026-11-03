import Yau.Proofs.F05BootstrapDatumGoodWords
import Yau.Proofs.F05BootstrapExponentialEllipticity

/-! The original value bound and background ellipticity discharge the
last coefficient condition in the full physical-datum good-word theorem. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ}

theorem F05_relative_exponential_operator {X : Set (Space n)} {I : Set ℝ}
    (A : Point n → Mat n) (B : Point n → RIdx n → ℝ) (u : Point n → ℝ) (z : Point n) :
    F05RelOp X I (fun z => Real.exp (-u z) • A z) (fun z j => Real.exp (-u z)*B z j) u z =
      F05RelT I u z-Real.exp (-u z)*((∑ j,∑ k,A z j k*F05RelDD X u z (realVec j) (realVec k))+
        ∑ j,B z j*F05RelD X u z (realVec j)) := by
  simp only [F05RelOp,Matrix.smul_apply,smul_eq_mul,mul_add,Finset.mul_sum,mul_assoc]
  ring

theorem F05_value_bounded_physical_good_words {ν : Option (RIdx n)} {T α lam upper K : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1) (hK : 0 ≤ K)
    (A : Point n → Mat n) (B : Point n → RIdx n → ℝ) (R p u : Point n → ℝ)
    (hA : ContDiffOn ℝ ∞ A (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hB : ∀ j, ContDiffOn ℝ ∞ (fun z => B z j) (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hR : ContDiffOn ℝ ∞ R (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hp : ContDiffOn ℝ ∞ p (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hu : F05LocalSchauder α ν T u) (hFace : F05ZeroFace ν T (fun z => u z-p z))
    (hEll : Elliptic (F05PosPatch ν T) A lam upper)
    (hBound : ∀ z ∈ F05PosPatch ν T, |u z| ≤ K)
    (hPDE : ∀ z ∈ F05PosPatch ν T,
      F05RelT (Ioc 0 T) u z = Real.exp (-u z)*
        ((∑ j,∑ k,A z j k*F05RelDD (F05PosSpace ν) u z (realVec j) (realVec k))+
          ∑ j,B z j*F05RelD (F05PosSpace ν) u z (realVec j))+(1-Real.exp (-u z))*R z) :
    ∀ β : List (Option (RIdx n)), F05GoodList ν β →
      F05LocalSchauder α ν T (F05GoodWord T β u) := by
  apply F05_physical_datum_nonlinear_good_words hT hα hα1 A B R p u hA hB hR hp hu hFace
    (F05_exp_principal_elliptic hEll hK hBound)
  intro z hz
  rw [F05_relative_exponential_operator,hPDE z hz]
  ring

end Yau.Proofs.F05Aux
