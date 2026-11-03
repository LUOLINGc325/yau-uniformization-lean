import Yau.Proofs.F05PhysicalManifoldOperator

/-! FTC uniqueness identifies the computed jet operator with the actual
operator of every genuine C2 function having those physical values. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05JetOperator_eq_intrinsic_of_values {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    (α : ℝ) {T : ℝ} (hT : 0 < T) (u : F05CompatibleJetGraph A α hT.le)
    (F : M.Carrier → ℝ → ℝ) (hF : ∀ i, C2 (F05Q A i T) (pull A i F))
    (hValue : ∀ i (p : F05Q A i T), (u.val i).val.1 p = pull A i F p.val)
    (i : Fin A.count) {p : Point n} (hp : p ∈ F05Q A i T) :
    F05JetOperator A c h α hT.le u i p = F05IntrinsicLinearOperator c h T F (lift A i p.1) p.2 := by
  let ui : F05LocalFTCGraph A i α hT.le := ⟨(u.val i).val,(u.val i).property.1.1.1⟩
  have hActualValue : EqOn (pull A i F) (F05BCFFun (u.val i).val.1) (F05Q A i T) := by
    intro q hq
    rw [F05BCFFun_apply _ ⟨q,hq⟩]
    exact (hValue i ⟨q,hq⟩).symm
  have hReal := F05LocalFTCGraph_realization A i α hT ui (pull A i F) hActualValue
    (fun q hq => (hF i).2.2.2.2.1 q hq)
  dsimp only [ui] at hReal
  rw [F05_intrinsic_operator_eq_chart hA h c T F i hp.1 ((hF i).2.2.2.2.1 p hp)]
  unfold F05JetOperator linearOp F05FlowPrincipal F05FlowDrift
  rw [hReal.2.1 hp,hReal.2.2.1 hp,hReal.2.2.2 hp]
  unfold pull
  simp only [Matrix.smul_apply,smul_eq_mul,mul_add,Finset.mul_sum,mul_assoc]
  ring

end Yau.Proofs.F05Aux
