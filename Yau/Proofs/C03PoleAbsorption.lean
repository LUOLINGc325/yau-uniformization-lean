import Yau.Proofs.C03LeviOrder
import Yau.Proofs.C03LeviGerms

/-! One scale absorbs the actual lower Levi bound of every smooth pole
regularization. The smooth base weight is fixed before that sequence. -/

noncomputable section
open Filter Set
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs.L22Aux Yau.NodeProofs.E01Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem exists_pole_absorbing_scale (F : ComplexVector n → ℝ) (hF : ContDiff ℝ ∞ F)
    (hFp : ∀ z, (leviC F z).PosSemidef) (H : ComplexVector n → Herm n)
    (hHp : ∀ z, (H z).PosDef) (T : Set (ComplexVector n))
    (κ C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C)
    (hstrict : ∀ z ∈ T, HermLE ((κ : ℂ) • H z) (leviC F z))
    (p : ℕ → ComplexVector n → ℝ) (hp : ∀ j, ContDiff ℝ ∞ (p j))
    (hneg : ∀ j z, z ∈ T → ∀ v,
      -C * ellipsoidQuadratic (H z) v ≤ complexLeviQuadratic (p j) z v)
    (hvanish : ∀ j z, z ∉ T → p j =ᶠ[𝓝 z] fun _ => 0) :
    ∃ k : ℝ, k = (C + 1) / κ ∧ 0 < k ∧ ∀ j,
      ContDiff ℝ ∞ (fun z => k * F z + p j z) ∧
      (∀ z, (leviC (fun w => k * F w + p j w) z).PosSemidef) ∧
      ∀ z ∈ T, HermLE (H z) (leviC (fun w => k * F w + p j w) z) := by
  let k := (C + 1) / κ
  have hk : 0 < k := div_pos (by linarith) hκ
  have hkκ : k * κ = C + 1 := div_mul_cancel₀ _ hκ.ne'
  let w (j : ℕ) (z : ComplexVector n) := k * F z + p j z
  have hw (j : ℕ) : ContDiff ℝ ∞ (w j) := (contDiff_const.mul hF).add (hp j)
  have hquad (j : ℕ) (z v : ComplexVector n) :
      complexLeviQuadratic (w j) z v =
        k * complexLeviQuadratic F z v + complexLeviQuadratic (p j) z v := by
    exact (complexLeviQuadratic_add
      (contDiffAt_const.mul (hF.contDiffAt.of_le (by simp)))
      ((hp j).contDiffAt.of_le (by simp)) v).trans (by
        rw [complexLeviQuadratic_const_mul (hF.contDiffAt.of_le (by simp)) k v])
  have hscalar (j : ℕ) (z : ComplexVector n) (hz : z ∈ T) (v : ComplexVector n) :
      ellipsoidQuadratic (H z) v ≤ complexLeviQuadratic (w j) z v := by
    have Hf := complexLeviQuadratic_ge_of_HermLE F z v
      (hF.contDiffAt.of_le (by simp)) (H z) κ (hstrict z hz)
    have Hfm := mul_le_mul_of_nonneg_left Hf hk.le
    have Hp := hneg j z hz v
    have Hscale := congrArg (fun t : ℝ => t * ellipsoidQuadratic (H z) v) hkκ
    rw [hquad]
    nlinarith only [Hfm, Hp, Hscale]
  refine ⟨k, rfl, hk, ?_⟩
  intro j
  refine ⟨hw j, ?_, ?_⟩
  · intro z
    apply (leviC_posSemidef_iff ((hw j).contDiffAt.of_le (by simp))).mpr
    intro v
    by_cases hz : z ∈ T
    · exact (ellipsoidQuadratic_nonneg (hHp z).posSemidef v).trans (hscalar j z hz v)
    · rw [hquad, complexLeviQuadratic_congr_germ (hvanish j z hz) v,
        complexLeviQuadratic_zero, add_zero]
      exact mul_nonneg hk.le
        ((leviC_posSemidef_iff (hF.contDiffAt.of_le (by simp))).mp (hFp z) v)
  · intro z hz
    exact HermLE_leviC_of_quadratic (w j) z ((hw j).contDiffAt.of_le (by simp))
      (H z) (hHp z).isHermitian (hscalar j z hz)

end Yau.Proofs.C03Aux
