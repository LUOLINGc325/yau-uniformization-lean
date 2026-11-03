import Yau.Proofs.F05BootstrapBufferedAbsorption

/-! An arbitrary compact receiving cap and later time slab have a uniform
raw high-jet bound. The buffer is chosen before all PDE data and candidates. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_buffered_high_on_receiving_slab (ν : Option (RIdx n))
    (χ : ContDiffBump (0 : Space n)) {Rbase : ℝ} (hχ : χ.rOut ≤ Rbase)
    {α M lam upper r s0 s : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M)
    (hr : 0 < r) (hrχ : r < χ.rIn) (hs : s0 < s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T0 : ℝ) (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
        (f u : Point n → ℝ) (F B : ℝ),
      Elliptic (region ν Rbase ×ˢ Icc s0 T0) a lam upper →
      HolderBound α (region ν Rbase ×ˢ Icc s0 T0) a M →
      (∀ j, HolderBound α (region ν Rbase ×ˢ Icc s0 T0) (fun z => b z j) M) →
      HolderBound α (region ν Rbase ×ˢ Icc s0 T0) f F → F05RelC2 (region ν Rbase) (Icc s0 T0) u →
      (∀ z ∈ region ν Rbase ×ˢ Icc s0 T0, |u z| ≤ B) →
      (∀ j, ν = some j → ∀ x ∈ region ν Rbase, realCoord x j = 0 →
        ∀ t ∈ Icc s0 T0, u (x,t) = 0) →
      (∀ z ∈ region ν Rbase ×ˢ Icc s0 T0, F05RelOp (region ν Rbase) (Icc s0 T0) a b u z = f z) →
      ∀ z ∈ region ν r ×ˢ Icc s T0,
        F05RelHigh (region ν Rbase) (Icc s0 T0) u z ≤ C*(B+F) := by
  let ε := min 1 (min (r/2) (min (χ.rIn-r) (Real.sqrt (s-s0)/2)))
  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min zero_lt_one (lt_min (by positivity) (lt_min (sub_pos.mpr hrχ) (by positivity)))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεr : ε ≤ r/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεχ : ε ≤ χ.rIn-r := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεTime : ε ≤ Real.sqrt (s-s0)/2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hεSquare : ε^2*(3/2 : ℝ)^2 ≤ s-s0 := by
    have hSqrt : 0 ≤ Real.sqrt (s-s0) := Real.sqrt_nonneg _
    have hSq := pow_le_pow_left₀ hε.le hεTime 2
    have hId := Real.sq_sqrt (sub_nonneg.mpr hs.le)
    nlinarith
  let r0 := r-(5/4)*ε
  have hr0 : 0 ≤ r0 := by dsimp only [r0]; nlinarith
  have hRadius : r0+ε*(3/2) ≤ χ.rIn := by dsimp only [r0]; nlinarith
  obtain ⟨C,hC,hEstimate⟩ := F05_uniform_buffered_physical_high_bound
    (M := M) (lam := lam) (upper := upper) ν χ hχ hα hα1 hM ε hε hε1
  refine ⟨C,hC,?_⟩
  intro T0 a b f u F B hEll ha hb hf hu hB hFace hEq z hz
  have hStart : s0 ≤ z.2-ε^2*(3/2)^2 := by linarith [hz.2.1]
  have hBound := hEstimate r0 s0 z.2 T0 a b f u F B hr0 hRadius hStart hz.2.2
    hEll ha hb hf hu hB hFace hEq
  apply hBound z
  have hRadiusEq : r0+ε*(5/4) = r := by dsimp only [r0]; ring
  refine ⟨?_,?_,hz.2.2⟩
  · change z.1 ∈ region ν (r0+ε*(5/4))
    rw [hRadiusEq]
    exact hz.1
  · change z.2-ε^2*(5/4)^2 ≤ z.2
    nlinarith [sq_nonneg ε]

end Yau.Proofs.F05Aux
