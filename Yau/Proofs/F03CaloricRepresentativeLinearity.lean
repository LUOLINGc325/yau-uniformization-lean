import Yau.Proofs.F03CaloricRepresentative

/-! Genuine linearity of the native smooth representatives on their open slab. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

section
variable (hd : 0 < d) (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O) (hlr : l < r)
  (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
  (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)

theorem caloricRepresentative_zero :
    EqOn (caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll 0)
      (fun _ => 0) (O ×ˢ Ioo l r) := by
  apply caloricRepresentative_eqOn_of_ae hd O l r lam upper hO hlr a b hAB hEll 0
    (fun _ => 0) continuousOn_const
  exact Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volume.restrict (O ×ˢ Ioo l r))

theorem caloricRepresentative_add
    (e f : CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB) :
    EqOn (caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll (e+f))
      (fun p => caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e p+
        caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll f p) (O ×ˢ Ioo l r) := by
  have he := caloricRepresentative_spec hd O l r lam upper hO hlr a b hAB hEll e
  have hf := caloricRepresentative_spec hd O l r lam upper hO hlr a b hAB hEll f
  apply caloricRepresentative_eqOn_of_ae hd O l r lam upper hO hlr a b hAB hEll (e+f)
    _ (he.1.continuousOn.add hf.1.continuousOn)
  filter_upwards [Lp.coeFn_add e.val.1 f.val.1,he.2.1,hf.2.1] with p hp hpe hpf
  change (e.val.1+f.val.1) p=_
  rw [hp,Pi.add_apply,hpe,hpf]
  rfl

theorem caloricRepresentative_const_smul (c : ℝ)
    (e : CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB) :
    EqOn (caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll (c • e))
      (fun p => c*caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e p) (O ×ˢ Ioo l r) := by
  have he := caloricRepresentative_spec hd O l r lam upper hO hlr a b hAB hEll e
  apply caloricRepresentative_eqOn_of_ae hd O l r lam upper hO hlr a b hAB hEll (c • e)
    _ (continuousOn_const.mul he.1.continuousOn)
  filter_upwards [Lp.coeFn_smul c e.val.1,he.2.1] with p hp hpe
  change (c • e.val.1) p=_
  rw [hp,Pi.smul_apply,smul_eq_mul,hpe]
  rfl

end
end Yau.Proofs.F03Aux
