import Yau.Proofs.F03ScalarL2
import Mathlib.MeasureTheory.Measure.OpenPos

/-! One positive source identifies ordered separately continuous kernels. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem ordered_kernels_eq_of_positive_action
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) [μ.IsOpenPosMeasure]
    (H K : α → α → ℝ) (f : α → ℝ)
    (hOrder : ∀ x y,H x y ≤ K x y)
    (hHL : ∀ y,Continuous (fun x => H x y)) (hKL : ∀ y,Continuous (fun x => K x y))
    (hHR : ∀ x,Continuous (H x)) (hKR : ∀ x,Continuous (K x))
    (hf : ∀ᵐ y ∂μ,0 < f y)
    (hHI : ∀ x,Integrable (fun y => H x y*f y) μ)
    (hKI : ∀ x,Integrable (fun y => K x y*f y) μ)
    (hAction : (fun x => ∫ y,H x y*f y ∂μ) =ᵐ[μ] (fun x => ∫ y,K x y*f y ∂μ)) :
    H=K := by
  have hRows : ∀ᵐ x ∂μ,∀ y,H x y=K x y := by
    filter_upwards [hAction] with x hx
    let d : α → ℝ := fun y => (K x y-H x y)*f y
    have hi : Integrable d μ := by
      apply ((hKI x).sub (hHI x)).congr
      exact ae_of_all _ (fun y => by change K x y*f y-H x y*f y=(K x y-H x y)*f y;ring)
    have hn : 0 ≤ᵐ[μ] d := by
      filter_upwards [hf] with y hy
      exact mul_nonneg (sub_nonneg.mpr (hOrder x y)) hy.le
    have hz : (∫ y,d y ∂μ)=0 := by
      calc
        _ = ∫ y,K x y*f y-H x y*f y ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ (fun y => by change (K x y-H x y)*f y=K x y*f y-H x y*f y;ring)
        _ = (∫ y,K x y*f y ∂μ)-(∫ y,H x y*f y ∂μ) := integral_sub (hKI x) (hHI x)
        _ = 0 := sub_eq_zero.mpr hx.symm
    have hd := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
    have hRow : H x =ᵐ[μ] K x := by
      filter_upwards [hd,hf] with y hdy hfy
      have hmul : (K x y-H x y)*f y=0 := hdy
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right (ne_of_gt hfy))).symm
    have heq := Measure.eq_of_ae_eq hRow (hHR x) (hKR x)
    exact congrFun heq
  funext x y
  have hAE : (fun z => H z y) =ᵐ[μ] (fun z => K z y) := by
    filter_upwards [hRows] with z hz
    exact hz y
  exact congrFun (Measure.eq_of_ae_eq hAE (hHL y) (hKL y)) x

end Yau.Proofs.F03Aux
