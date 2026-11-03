import Yau.Proofs.F05BootstrapBufferedHighStep
import Yau.Proofs.F05BootstrapBufferedRegions
import Yau.Proofs.F05BootstrapSetAbsorption
import Yau.Proofs.F05BootstrapRawBound
import Yau.LeafProofs.L16RadiusAbsorption

/-! Absorption on genuinely buffered physical caps. The final constant
precedes every coefficient and candidate, and the actual compact raw jet
bound disappears from the conclusion. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_uniform_buffered_physical_high_bound (ν : Option (RIdx n))
    (χ : ContDiffBump (0 : Space n)) {Rbase : ℝ} (hχ : χ.rOut ≤ Rbase) {α M lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r0 s0 τ T0 : ℝ) (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
        (f u : Point n → ℝ) (F B : ℝ),
      0 ≤ r0 → r0+ε*(3/2) ≤ χ.rIn → s0 ≤ τ-ε^2*(3/2)^2 → τ ≤ T0 →
      Elliptic (region ν Rbase ×ˢ Icc s0 T0) a lam upper →
      HolderBound α (region ν Rbase ×ˢ Icc s0 T0) a M →
      (∀ j, HolderBound α (region ν Rbase ×ˢ Icc s0 T0) (fun z => b z j) M) →
      HolderBound α (region ν Rbase ×ˢ Icc s0 T0) f F → F05RelC2 (region ν Rbase) (Icc s0 T0) u →
      (∀ z ∈ region ν Rbase ×ˢ Icc s0 T0, |u z| ≤ B) →
      (∀ j, ν = some j → ∀ x ∈ region ν Rbase, realCoord x j = 0 →
        ∀ t ∈ Icc s0 T0, u (x,t) = 0) →
      (∀ z ∈ region ν Rbase ×ˢ Icc s0 T0, F05RelOp (region ν Rbase) (Icc s0 T0) a b u z = f z) →
      ∀ z ∈ F05NestedCap ν r0 ε τ T0 (5/4),
        F05RelHigh (region ν Rbase) (Icc s0 T0) u z ≤ C*(B+F) := by
  have hRbase : 0 < Rbase := χ.rOut_pos.trans_le hχ
  obtain ⟨δ,A,hδ,hδ1,hA,hHigh⟩ :=
    F05_uniform_buffered_physical_high_step (M := M) (lam := lam) (upper := upper) ν χ hχ hα hα1 hM
  obtain ⟨P,C,hC,hParameters⟩ := exists_radius_absorption_parameters hα hα1 hA
  let CE := C*(ε⁻¹)^P
  have hCE : 0 < CE := by dsimp only [CE]; positivity
  refine ⟨2*CE*(8 : ℝ)^P,by positivity,?_⟩
  intro r0 s0 τ T0 a b f u F B hr0 hRadius hStart hEnd hEll ha hb hf hu hB hFace hEq
  let Q := F05NestedCap ν r0 ε τ T0
  let J := F05RelHigh (region ν Rbase) (Icc s0 T0) u
  have hRadius2 : r0+ε*(3/2) ≤ Rbase := hRadius.trans (χ.rIn_lt_rOut.le.trans hχ)
  have hB0 : 0 ≤ B := by
    have hZero : ((0,T0) : Point n) ∈ region ν Rbase ×ˢ Icc s0 T0 := by
      refine ⟨?_,?_,le_rfl⟩
      · cases ν <;> simpa [region,realCoord] using hRbase.le
      · nlinarith [sq_nonneg ε]
    exact (abs_nonneg _).trans (hB (0,T0) hZero)
  obtain ⟨Kstar,hKstar,hRaw⟩ := F05_relative_cap_raw_high_bound ν hu
  have hInitial : ∀ z ∈ Q (3/2), J z ≤ Kstar := by
    intro z hz
    have hzBase := F05_nested_cap_subset hε.le (by norm_num) le_rfl hRadius2 hStart hz
    exact max_le (hRaw z hzBase).1 (hRaw z hzBase).2
  have hMono : ∀ r R : ℝ, 1 ≤ r → r ≤ R → R ≤ 3/2 → Q r ⊆ Q R := by
    intro r R hr hrR hR
    exact F05_nested_cap_mono hε.le (by linarith) hrR
  have hStep : ∀ r R K : ℝ, 1 ≤ r → r < R → R ≤ 3/2 → 0 ≤ K →
      (∀ z ∈ Q R, J z ≤ K) → ∀ z ∈ Q r,
        J z ≤ (2^(P+1) : ℝ)⁻¹*K+CE*((R-r)⁻¹)^P*(B+F) := by
    intro r R K hr hrR hR hK hBound z hz
    let rg := (r0+ε*R)-(r0+ε*r)
    have hGapEq : rg = ε*(R-r) := by dsimp only [rg]; ring
    have hrg : 0 < rg := by rw [hGapEq]; exact mul_pos hε (sub_pos.mpr hrR)
    have hrg1 : rg ≤ 1 := by
      rw [hGapEq]
      have hd1 : R-r ≤ 1 := by linarith
      calc
        ε*(R-r) ≤ ε*1 := mul_le_mul_of_nonneg_left hd1 hε.le
        _ = ε := mul_one _
        _ ≤ 1 := hε1
    obtain ⟨ρ,hρ,hρ1,hρMargin,hArithmetic⟩ := hParameters rg hrg hrg1
    have hLarge : r0+ε*R ≤ χ.rIn := (by nlinarith : r0+ε*R ≤ r0+ε*(3/2)).trans hRadius
    have hSmall : 0 ≤ r0+ε*r := by positivity
    have hLarge0 : 0 < R := by linarith
    have hTimeStart : s0 ≤ τ-ε^2*R^2 := by
      have hSq := pow_le_pow_left₀ hLarge0.le hR 2
      nlinarith [mul_le_mul_of_nonneg_left hSq (sq_nonneg ε)]
    have hTimeEnd : τ-ε^2*R^2 < T0 := by nlinarith [sq_pos_of_pos hε,sq_pos_of_pos hLarge0]
    have hTimeGap : localSchauderTime δ rg ≤ (τ-ε^2*r^2)-(τ-ε^2*R^2) := by
      rw [hGapEq]
      convert F05_nested_cap_patch_time_gap hδ.le hδ1 hε.le hr hrR hR using 1 <;> ring
    have hEstimate := hHigh s0 T0 a b f u F B hEll ha hb hf hu hB hFace hEq
      (r0+ε*r) (r0+ε*R) (τ-ε^2*R^2) (τ-ε^2*r^2) ρ K hSmall
      (by dsimp only [rg] at hrg; linarith) hLarge hrg1 hTimeStart hTimeEnd hTimeGap
      hρ hρ1 hρMargin hK hBound z hz
    have hArithmetic' := hArithmetic K B F hK hB0 hf.1
    have hFactor : C*(rg⁻¹)^P*(B+F) = CE*((R-r)⁻¹)^P*(B+F) := by
      rw [F05_buffered_radius_inverse_power]
      dsimp only [CE]
      ring
    rw [hFactor] at hArithmetic'
    exact hEstimate.trans hArithmetic'
  exact F05_nested_set_high_absorption hMono hCE.le (add_nonneg hB0 hf.1) hKstar.le hInitial hStep

end Yau.Proofs.F05Aux
