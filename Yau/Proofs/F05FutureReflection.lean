import Yau.Proofs.F05SchauderTimeAffine
import Yau.LeafProofs.L16BoundaryTimeContinuation

/-! A genuine first-order reflection through the terminal time. The
coefficients 3,-2 match both the value and the one-sided time derivative;
no spatial derivatives of the time derivative are used. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux Yau.LeafProofs.L16BoundaryTimeAux
variable {n : ℕ}

def F05FutureTail (τ : ℝ) (u : Point n → ℝ) : Point n → ℝ :=
  fun p => 3*F05TimeAffine (-1) (2*τ) u p-2*F05TimeAffine (-2) (3*τ) u p

def F05FutureReflection (τ : ℝ) (u : Point n → ℝ) : Point n → ℝ :=
  timePaste τ u (F05FutureTail τ u)

theorem F05_future_reflection_time_maps {τ T : ℝ} (hτT : τ ≤ T) (hBack : 0 ≤ 3*τ-2*T) :
    MapsTo (fun t : ℝ => (-1)*t+2*τ) (Icc τ T) (Icc 0 τ) ∧
      MapsTo (fun t : ℝ => (-2)*t+3*τ) (Icc τ T) (Icc 0 τ) := by
  constructor <;> intro t ht <;> constructor <;> linarith [ht.1,ht.2]

theorem F05_future_tail_trace (τ : ℝ) (u : Point n → ℝ) (x : Space n) :
    F05FutureTail τ u (x,τ) = u (x,τ) := by
  dsimp only [F05FutureTail,F05TimeAffine,F05TimeAffinePoint]
  rw [show (-1)*τ+2*τ = τ by ring,show (-2)*τ+3*τ = τ by ring]
  ring

theorem F05_future_tail_time_trace {X : Set (Space n)} {τ T : ℝ}
    (hτT : τ < T) (hBack : 0 ≤ 3*τ-2*T) {u : Point n → ℝ}
    (hu : C2 (cylinder X 0 τ) u) {x : Space n} (hx : x ∈ X) :
    timeD (cylinder X τ T) (F05FutureTail τ u) (x,τ) =
      timeD (cylinder X 0 τ) u (x,τ) := by
  obtain ⟨hMap1,hMap2⟩ := F05_future_reflection_time_maps hτT.le hBack
  have hC1 := F05_c2_timeAffine hτT hMap1 hu
  have hC2 := F05_c2_timeAffine hτT hMap2 hu
  have hMul1 : C2 (cylinder X τ T) (fun p => 3*F05TimeAffine (-1) (2*τ) u p) := by
    exact c2_spatial_mul (φ := fun _ => (3 : ℝ)) contDiff_const hC1
  have hMul2 : C2 (cylinder X τ T) (fun p => 2*F05TimeAffine (-2) (3*τ) u p) := by
    exact c2_spatial_mul (φ := fun _ => (2 : ℝ)) contDiff_const hC2
  have hp : (x,τ) ∈ cylinder X τ T := ⟨hx,le_rfl,hτT.le⟩
  change timeD _ (fun p => 3*F05TimeAffine (-1) (2*τ) u p-2*F05TimeAffine (-2) (3*τ) u p) _ = _
  rw [timeD_sub hMul1 hMul2 hp,
    timeD_spatial_mul _ (fun _ => 3),timeD_spatial_mul _ (fun _ => 2),
    F05_timeD_timeAffine hτT hMap1 hu hp,F05_timeD_timeAffine hτT hMap2 hu hp]
  dsimp only [F05TimeAffinePoint]
  rw [show (-1)*τ+2*τ = τ by ring,show (-2)*τ+3*τ = τ by ring]
  ring

theorem F05_schauder_future_reflection {X : Set (Space n)} (hClosed : IsClosed X)
    {τ T α C : ℝ} (hτ : 0 < τ) (hτT : τ < T) (hBack : 0 ≤ 3*τ-2*T)
    (hα : 0 < α) {u : Point n → ℝ} (hu : SchauderBound α (cylinder X 0 τ) u C) :
    SchauderBound α (cylinder X 0 T) (F05FutureReflection τ u)
      (C*(38+12*(2:ℝ)^(α/2))) ∧
      EqOn (F05FutureReflection τ u) u (cylinder X 0 τ) := by
  obtain ⟨hMap1,hMap2⟩ := F05_future_reflection_time_maps hτT.le hBack
  have hOne := F05_schauder_timeAffine hτT hMap1 hu
  have hTwo := F05_schauder_timeAffine hτT hMap2 hu
  have hTail := F05_schauder_sub (F05_schauder_const_mul hOne 3) (F05_schauder_const_mul hTwo 2)
  have hSch := schauderBound_timePaste_space hClosed hα hτ hτT hu hTail
    (fun x => (F05_future_tail_trace τ u x).symm)
    (fun x hx => (F05_future_tail_time_trace hτT hBack hu.1 hx).symm)
  refine ⟨?_,timePaste_eqOn_left_space u (F05FutureTail τ u)⟩
  change SchauderBound α (cylinder X 0 T)
    (timePaste τ u (fun p => 3*F05TimeAffine (-1) (2*τ) u p-2*F05TimeAffine (-2) (3*τ) u p)) _
  convert! hSch using 1 <;> norm_num <;> ring

end Yau.Proofs.F05Aux
