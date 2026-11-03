import Yau.Proofs.F05BootstrapBufferedLocalEstimate
import Yau.Proofs.F05PostHolderCoefficients
import Yau.Proofs.F05PositiveScalar

/-! On a full interior chart, the exponential value modulus supplies every
nonlinear coefficient budget for the native local Schauder estimate.
The resulting constant does not depend on any candidate derivative norm. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_wide_interior_nonlinear_schauder_uniform {α M D B lam upper s0 s : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hs : s0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, s < T →
      ∀ (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (R u : Point n → ℝ),
      Elliptic (region none (5/2) ×ˢ Icc s0 T) a lam upper →
      HolderBound α (region none (5/2) ×ˢ Icc s0 T) a M →
      (∀ j, HolderBound α (region none (5/2) ×ˢ Icc s0 T) (fun z => b z j) M) →
      HolderBound α (region none (5/2) ×ˢ Icc s0 T) R M →
      HolderBound α (region none (5/2) ×ˢ Icc s0 T) (fun z => Real.exp (u z)) D →
      F05RelC2 (region none (5/2)) (Icc s0 T) u →
      (∀ z ∈ region none (5/2) ×ˢ Icc s0 T, 0 ≤ u z ∧ u z ≤ B) →
      (∀ z ∈ region none (5/2) ×ˢ Icc s0 T,
        F05RelT (Icc s0 T) u z = Real.exp (-u z)*
          ((∑ j,∑ k,a z j k*F05RelDD (region none (5/2)) u z (realVec j) (realVec k))+
            ∑ j,b z j*F05RelD (region none (5/2)) u z (realVec j))+
          (1-Real.exp (-u z))*R z) →
      F05RelSchauder α (region none (9/4)) (Icc s T) u C := by
  let E : ℝ := 4+16*D
  let N : ℝ := 1+2*E*M
  let F : ℝ := 2*(1+E)*M
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  let χ : ContDiffBump (0 : Space n) := ⟨19/8,39/16,by norm_num,by norm_num⟩
  obtain ⟨C0,hC0,hLocal⟩ := F05_buffered_physical_local_schauder
    (M := N) (lam := Real.exp (-B)*lam) (upper := upper) none χ
    (by norm_num [χ] : χ.rOut ≤ (5/2 : ℝ)) hα hα1 hN
    (by norm_num : (0 : ℝ) < 9/4) (by norm_num [χ] : (9/4 : ℝ) < χ.rIn) hs
  refine ⟨1+C0*(B+F),by positivity,?_⟩
  intro T hsT a b R u hEll ha hb hR hExp hu hRange hEq
  let Q := region (n := n) none (5/2) ×ˢ Icc s0 T
  have hNonneg : ∀ z ∈ Q, 0 ≤ u z := fun z hz => (hRange z hz).1
  have hc : HolderBound α Q (fun z => Real.exp (-u z)) E :=
    F05_nonnegative_exp_inverse_holder hExp hNonneg
  have haProduct := holderBound_smul_refined hc ha hE hM
    (fun z hz => by simpa only [Real.norm_eq_abs] using hc.2.1 z hz) ha.2.1
  have haNew : HolderBound α Q (fun z => Real.exp (-u z) • a z) N := by
    apply holderBound_mono_const haProduct
    dsimp only [N]
    nlinarith
  have hbNew (j : RIdx n) : HolderBound α Q (fun z => Real.exp (-u z)*b z j) N := by
    apply holderBound_mono_const (holderBound_mul hc (hb j))
    dsimp only [N]
    linarith
  have hEllNew : Elliptic Q (fun z => Real.exp (-u z) • a z)
      (Real.exp (-B)*lam) upper := by
    have he := F05_elliptic_scalar_mul hEll (Real.exp_pos (-B))
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hB))
      (fun z hz => show Real.exp (-B) ≤ Real.exp (-u z) ∧ Real.exp (-u z) ≤ 1 from
        ⟨Real.exp_le_exp.mpr (neg_le_neg (hRange z hz).2),
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hRange z hz).1)⟩)
    simpa only [one_mul] using he
  have hf : HolderBound α Q (fun z => (1-Real.exp (-u z))*R z) F :=
    F05_nonnegative_exp_reaction_holder hExp hNonneg hR
  have hActual : ∀ z ∈ Q,
      F05RelOp (region none (5/2)) (Icc s0 T)
        (fun z => Real.exp (-u z) • a z) (fun z j => Real.exp (-u z)*b z j) u z =
      (1-Real.exp (-u z))*R z := by
    intro z hz
    dsimp only [F05RelOp]
    rw [hEq z hz]
    simp only [Matrix.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum]
    ring
  have hSch := hLocal T (fun z => Real.exp (-u z) • a z)
    (fun z j => Real.exp (-u z)*b z j) (fun z => (1-Real.exp (-u z))*R z) u F B hsT
    hEllNew haNew hbNew hf hu
    (fun z hz => by rw [abs_of_nonneg (hRange z hz).1]; exact (hRange z hz).2)
    (fun j hj => by cases hj) hActual
  have hConst : C0*(B+F) ≤ 1+C0*(B+F) := by linarith
  exact ⟨hSch.1,holderBound_mono_const hSch.2.1 hConst,
    holderBound_mono_const hSch.2.2.1 hConst,holderBound_mono_const hSch.2.2.2 hConst⟩

end Yau.Proofs.F05Aux
