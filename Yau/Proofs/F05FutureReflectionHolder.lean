import Yau.Proofs.F05FutureReflectionJets
import Yau.Proofs.F05BootstrapSchauderLimit

/-! The reflection has one common bound for all four actual jets, suitable
for finite-chart Arzelà–Ascoli. The constants precede the moving horizon. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux Yau.LeafProofs.L16BoundaryTimeAux
variable {n : ℕ}

theorem F05_future_reflection_full_holder {X : Set (Space n)}
    {τ T α C : ℝ} (hτ : 0 < τ) (hτT : τ < T) (hBack : 0 ≤ 3*τ-2*T) (hα : 0 < α)
    {u : Point n → ℝ} (hu : C2 (cylinder X 0 τ) u)
    (hLow : HolderBound α (cylinder X 0 τ) (fun p => (u p,spatialD u p)) C)
    (hHess : HolderBound α (cylinder X 0 τ) (spatialDD u) C)
    (hTime : HolderBound α (cylinder X 0 τ) (timeD (cylinder X 0 τ) u) C) :
    HolderBound α (cylinder X 0 T)
      (fun p => ((F05FutureReflection τ u p,spatialD (F05FutureReflection τ u) p),
        (spatialDD (F05FutureReflection τ u) p,timeD (cylinder X 0 T) (F05FutureReflection τ u) p)))
      (C*(38+12*(2:ℝ)^(α/2))) := by
  obtain ⟨hMap1,hMap2⟩ := F05_future_reflection_time_maps hτT.le hBack
  obtain ⟨hTailC2,hJets⟩ := F05_future_tail_jets hτT hBack hu
  have hC := hLow.1
  have hPow : 0 ≤ (2:ℝ)^(α/2) := by positivity
  let D := C*(18+6*(2:ℝ)^(α/2))
  have hLRaw := holderBound_sub (F05_holder_const_smul (F05_holder_timeAffine hMap1 hLow) 3)
    (F05_holder_const_smul (F05_holder_timeAffine hMap2 hLow) 2)
  have hL : HolderBound α (cylinder X τ T)
      (fun p => (F05FutureTail τ u p,spatialD (F05FutureTail τ u) p)) (C*(8+2*(2:ℝ)^(α/2))) := by
    have hEq : EqOn
        (fun p => (3 : ℝ) • F05TimeAffine (-1) (2*τ) (fun z => (u z,spatialD u z)) p-
          (2 : ℝ) • F05TimeAffine (-2) (3*τ) (fun z => (u z,spatialD u z)) p)
        (fun p => (F05FutureTail τ u p,spatialD (F05FutureTail τ u) p)) (cylinder X τ T) := by
      intro p hp
      apply Prod.ext
      · rfl
      · exact (hJets p hp).1.symm
    have hh := holderBound_congr_on hLRaw hEq
    convert! hh using 1 <;> norm_num <;> ring
  have hHRaw := holderBound_sub (F05_holder_const_smul (F05_holder_timeAffine hMap1 hHess) 3)
    (F05_holder_const_smul (F05_holder_timeAffine hMap2 hHess) 2)
  have hH : HolderBound α (cylinder X τ T) (spatialDD (F05FutureTail τ u))
      (C*(8+2*(2:ℝ)^(α/2))) := by
    have hh := holderBound_congr_on hHRaw (fun p hp => (hJets p hp).2.1.symm)
    convert! hh using 1 <;> norm_num <;> ring
  have hTRaw := holderBound_sub (F05_holder_const_smul (F05_holder_timeAffine hMap1 hTime) (-3))
    (F05_holder_const_smul (F05_holder_timeAffine hMap2 hTime) (-4))
  have hJ : HolderBound α (cylinder X τ T) (timeD (cylinder X τ T) (F05FutureTail τ u))
      (C*(10+4*(2:ℝ)^(α/2))) := by
    have hEq : EqOn
        (fun p => (-3 : ℝ) • F05TimeAffine (-1) (2*τ) (timeD (cylinder X 0 τ) u) p-
          (-4 : ℝ) • F05TimeAffine (-2) (3*τ) (timeD (cylinder X 0 τ) u) p)
        (timeD (cylinder X τ T) (F05FutureTail τ u)) (cylinder X τ T) := by
      intro p hp
      rw [(hJets p hp).2.2]
      simp only [smul_eq_mul]
      ring
    have hh := holderBound_congr_on hTRaw hEq
    convert! hh using 1 <;> norm_num <;> ring
  have hLD : C*(8+2*(2:ℝ)^(α/2)) ≤ D := by dsimp only [D]; nlinarith [mul_nonneg hC hPow]
  have hJD : C*(10+4*(2:ℝ)^(α/2)) ≤ D := by dsimp only [D]; nlinarith [mul_nonneg hC hPow]
  have hTrace : ∀ x : Space n, u (x,τ) = F05FutureTail τ u (x,τ) :=
    fun x => (F05_future_tail_trace τ u x).symm
  have hLowPaste := holderBound_timePaste_space hα hLow (holderBound_mono_const hL hLD)
    (fun x _ => Prod.ext (hTrace x) (spatialD_eq_of_trace hTrace x))
  have hHessPaste := holderBound_timePaste_space hα hHess (holderBound_mono_const hH hLD)
    (fun x _ => spatialDD_eq_of_trace hTrace x)
  have hTimePaste := holderBound_timePaste_space hα hTime (holderBound_mono_const hJ hJD)
    (fun x hx => (F05_future_tail_time_trace hτT hBack hu hx).symm)
  have hLowActual : HolderBound α (cylinder X 0 T)
      (fun p => (F05FutureReflection τ u p,spatialD (F05FutureReflection τ u) p)) (2*(C+D)) := by
    apply holderBound_congr_on hLowPaste
    intro p hp
    change timePaste τ (fun z => (u z,spatialD u z))
      (fun z => (F05FutureTail τ u z,spatialD (F05FutureTail τ u) z)) p = _
    rw [F05FutureReflection,spatialD_timePaste]
    by_cases ht : p.2 ≤ τ <;> simp only [timePaste,ht,ite_true,ite_false]
  have hHessActual : HolderBound α (cylinder X 0 T)
      (spatialDD (F05FutureReflection τ u)) (2*(C+D)) := by
    simpa only [F05FutureReflection,spatialDD_timePaste] using hHessPaste
  have hTimeActual : HolderBound α (cylinder X 0 T)
      (timeD (cylinder X 0 T) (F05FutureReflection τ u)) (2*(C+D)) :=
    holderBound_congr_on hTimePaste (fun p hp =>
      (timeD_timePaste_space hτ hτT hu hTailC2 (fun x _ => hTrace x)
        (fun x hx => (F05_future_tail_time_trace hτT hBack hu hx).symm) hp).symm)
  have hFull := F05_holderBound_prod_same hLowActual (F05_holderBound_prod_same hHessActual hTimeActual)
  convert! hFull using 1
  dsimp only [D]
  ring

end Yau.Proofs.F05Aux
