import spec.CHAIN.CONTRACTS

/-! SOURCE-ONLY E03 candidate: the actual two vector blocks and clock coordinate. -/

noncomputable section
open scoped Matrix

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint

abbrev JointIndex (n : ℕ) := (Fin n ⊕ Fin n) ⊕ Unit
abbrev JointSpace (n : ℕ) := ComplexVector n × ComplexVector n × ℂ

def jointCoordinate {n : ℕ} (p : JointSpace n) : JointIndex n → ℂ :=
  Sum.elim (Sum.elim (fun i => p.1 i) (fun i => p.2.1 i)) (fun _ => p.2.2)

def jointAssembly {n : ℕ} (u : JointIndex n → ℂ) : JointSpace n :=
  (WithLp.toLp 2 (fun i => u (.inl (.inl i))),
    WithLp.toLp 2 (fun i => u (.inl (.inr i))), u (.inr ()))

theorem jointCoordinate_jointAssembly {n : ℕ} (u : JointIndex n → ℂ) (i : JointIndex n) :
    jointCoordinate (jointAssembly u) i = u i := by
  rcases i with (i | i) | u <;> rfl

theorem jointAssembly_jointCoordinate {n : ℕ} (p : JointSpace n) :
    jointAssembly (jointCoordinate p) = p := by
  rcases p with ⟨z, η, w⟩
  rfl

theorem jointCoordinate_injective {n : ℕ} :
    Function.Injective (jointCoordinate (n := n)) := by
  intro p q hpq
  have he := congrArg jointAssembly hpq
  simpa only [jointAssembly_jointCoordinate] using he

def jointLinearEquiv (n : ℕ) :
    ComplexVector (Fintype.card (JointIndex n)) ≃ₗ[ℂ] JointSpace n where
  toFun q := jointAssembly (fun i => q (Fintype.equivFin (JointIndex n) i))
  invFun p := WithLp.toLp 2 (fun k => jointCoordinate p ((Fintype.equivFin (JointIndex n)).symm k))
  left_inv q := by
    ext k
    change jointCoordinate (jointAssembly (fun i => q (Fintype.equivFin (JointIndex n) i)))
      ((Fintype.equivFin (JointIndex n)).symm k) = q k
    rw [jointCoordinate_jointAssembly, Equiv.apply_symm_apply]
  right_inv p := by
    change jointAssembly (fun i => jointCoordinate p
      ((Fintype.equivFin (JointIndex n)).symm (Fintype.equivFin (JointIndex n) i))) = p
    simp only [Equiv.symm_apply_apply, jointAssembly_jointCoordinate]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def jointContinuousLinearEquiv (n : ℕ) :
    ComplexVector (Fintype.card (JointIndex n)) ≃L[ℂ] JointSpace n :=
  (jointLinearEquiv n).toContinuousLinearEquiv

theorem jointCoordinate_jointLinearEquiv {n : ℕ}
    (q : ComplexVector (Fintype.card (JointIndex n))) (i : JointIndex n) :
    jointCoordinate (jointLinearEquiv n q) i = q (Fintype.equivFin (JointIndex n) i) :=
  jointCoordinate_jointAssembly _ _

theorem jointCoordinate_jointDir {n : ℕ} (i j : JointIndex n) :
    jointCoordinate (jointDir i) j = if j = i then 1 else 0 := by
  rcases i with (i | i) | u
  · rcases j with (j | j) | v <;>
      simp [jointCoordinate, jointDir, stdVec, PiLp.single_apply, eq_comm]
  · rcases j with (j | j) | v <;>
      simp [jointCoordinate, jointDir, stdVec, PiLp.single_apply, eq_comm]
  · rcases j with (j | j) | v <;>
      simp [jointCoordinate, jointDir, stdVec, PiLp.single_apply, eq_comm]

theorem jointContinuousLinearEquiv_stdVec {n : ℕ} (i : JointIndex n) :
    jointContinuousLinearEquiv n (stdVec (Fintype.equivFin (JointIndex n) i)) = jointDir i := by
  apply jointCoordinate_injective
  funext j
  change jointCoordinate (jointLinearEquiv n
    (stdVec (Fintype.equivFin (JointIndex n) i))) j = _
  rw [jointCoordinate_jointLinearEquiv, jointCoordinate_jointDir]
  simp [stdVec, PiLp.single_apply, (Fintype.equivFin (JointIndex n)).injective.eq_iff]

end Yau.NodeProofs.E03Aux
