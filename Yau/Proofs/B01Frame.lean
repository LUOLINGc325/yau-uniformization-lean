import Yau.Proofs.B01ImageCurvature

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Set Filter Bundle

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation
open LeafProofs.L14Aux

variable {r q : ℕ}

theorem holomorphic_matrix_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℂ → Matrix ι ι ℂ} {U : Set ℂ}
    (hA : ∀ i j, ContDiffOn ℂ ∞ (fun z => A z i j) U) :
    ContDiffOn ℂ ∞ (fun z => (A z).det) U := by
  simp_rw [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul
    (contDiffOn_prod fun i _ => hA (σ i) i)

theorem holomorphic_matrix_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℂ → Matrix ι ι ℂ} {U : Set ℂ}
    (hA : ∀ i j, ContDiffOn ℂ ∞ (fun z => A z i j) U)
    (hdet : ∀ z ∈ U, (A z).det ≠ 0) (i j : ι) :
    ContDiffOn ℂ ∞ (fun z => (A z)⁻¹ i j) U := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
    smul_eq_mul, Matrix.adjugate_apply]
  apply ((holomorphic_matrix_det hA).inv hdet).mul
  apply holomorphic_matrix_det
  intro k l
  simp only [Matrix.updateRow_apply]
  by_cases hkj : k = j
  · simp only [hkj, ↓reduceIte]
    exact contDiffOn_const
  · simp only [hkj, ↓reduceIte]
    exact hA k l

theorem holomorphic_matrix_mul {m n p : ℕ}
    {A : ℂ → Matrix (Fin m) (Fin n) ℂ} {B : ℂ → Matrix (Fin n) (Fin p) ℂ}
    {U : Set ℂ} (hA : ∀ i j, ContDiffOn ℂ ∞ (fun z => A z i j) U)
    (hB : ∀ i j, ContDiffOn ℂ ∞ (fun z => B z i j) U) (i j) :
    ContDiffOn ℂ ∞ (fun z => (A z * B z) i j) U := by
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun l _ => (hA i l).mul (hB l j)

theorem frameLinear_mul (B : Matrix (Fin q) (Fin r) ℂ) (C : Matrix (Fin r) (Fin r) ℂ) :
    frameLinear (B * C) = (frameLinear B).comp (frameLinear C) := by
  exact Matrix.toLpLin_mul 2 2 2 B C

theorem frame_leftInverse (B : Matrix (Fin q) (Fin r) ℂ)
    (hB : Function.Injective (frameLinear B)) :
    ∃ L : Matrix (Fin r) (Fin q) ℂ, L * B = 1 := by
  obtain ⟨l, hl⟩ := (frameLinear B).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hB)
  refine ⟨Matrix.toEuclideanLin.symm l, ?_⟩
  change l.comp (Matrix.toEuclideanLin B) = LinearMap.id at hl
  apply Matrix.toEuclideanLin.injective
  simpa only [Matrix.toLpLin_mul_same, LinearEquiv.apply_symm_apply, Matrix.toLpLin_one] using hl

theorem frame_mul_injective (C : Matrix (Fin r) (Fin r) ℂ)
    (hC : Function.Injective (frameLinear C)) : C.det ≠ 0 := by
  apply (Matrix.isUnit_iff_isUnit_det C).mp ?_ |>.ne_zero
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  have he : frameLinear C (WithLp.toLp 2 u) = frameLinear C (WithLp.toLp 2 v) := by
    simpa only [frameLinear, Matrix.toLpLin_apply] using congrArg (WithLp.toLp 2) huv
  exact congrArg WithLp.ofLp (hC he)

theorem frame_gauge_factor (B F : Matrix (Fin q) (Fin r) ℂ)
    (L : Matrix (Fin r) (Fin q) ℂ)
    (hB : Function.Injective (frameLinear B)) (hF : Function.Injective (frameLinear F))
    (hRange : LinearMap.range (frameLinear F) = LinearMap.range (frameLinear B))
    (hLB : (L * B).det ≠ 0) :
    let C := (L * B)⁻¹ * L * F
    B * C = F ∧ C.det ≠ 0 := by
  dsimp only
  have hLC : L * B * ((L * B)⁻¹ * L * F) = L * F := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hLB), Matrix.one_mul]
  have hEq : B * ((L * B)⁻¹ * L * F) = F := by
    apply Matrix.toEuclideanLin.injective
    apply LinearMap.ext
    intro v
    obtain ⟨u, hu⟩ := hRange ▸ LinearMap.mem_range_self (frameLinear F) v
    have hL : frameLinear (L * B) ((frameLinear ((L * B)⁻¹ * L * F)) v) =
        frameLinear (L * B) u := by
      have hx := congrArg (fun K => frameLinear K v) hLC
      have hx' : frameLinear (L * B) ((frameLinear ((L * B)⁻¹ * L * F)) v) =
          frameLinear L (frameLinear F v) := by
        simpa only [frameLinear, Matrix.toLpLin_mul_same, LinearMap.comp_apply] using hx
      have hLu : frameLinear L (frameLinear B u) = frameLinear (L * B) u := by
        exact (congrArg (fun f => f u) (Matrix.toLpLin_mul 2 2 2 L B)).symm
      exact hx'.trans ((congrArg (frameLinear L) hu.symm).trans hLu)
    have hInj : Function.Injective (frameLinear (L * B)) := by
      have hg := Matrix.mulVec_injective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hLB))
      intro x y he
      apply WithLp.ofLp_injective
      apply hg
      exact congrArg WithLp.ofLp he
    change frameLinear (B * ((L * B)⁻¹ * L * F)) v = frameLinear F v
    rw [frameLinear_mul]
    exact (congrArg (frameLinear B) (hInj hL)).trans hu
  refine ⟨hEq, frame_mul_injective _ ?_⟩
  intro u v huv
  apply hF
  have he := congrArg (fun K => frameLinear K) hEq
  rw [frameLinear_mul] at he
  rw [← he]
  exact congrArg (frameLinear B) huv

/-- Two arbitrary embedded frames admit a genuine local holomorphic gauge. -/
theorem local_frame_gauge (E : EmbeddedFibers q)
    (B F : ℂ → Matrix (Fin q) (Fin r) ℂ) (V U : Set ℂ)
    (hB : LocalEmbeddedFrame E B V) (hF : LocalEmbeddedFrame E F U)
    (z : ℂ) (hzV : z ∈ V) (hzU : z ∈ U) :
    ∃ O : Set ℂ, IsOpen O ∧ z ∈ O ∧ O ⊆ U ∩ V ∧
      ∃ C : ℂ → Matrix (Fin r) (Fin r) ℂ,
        (∀ i j, ContDiffOn ℂ ∞ (fun w => C w i j) O) ∧
        (∀ i j, ContDiffOn ℂ ∞ (fun w => (C w)⁻¹ i j) O) ∧
        (∀ w ∈ O, B w * C w = F w) ∧ (∀ w ∈ O, (C w).det ≠ 0) := by
  obtain ⟨L, hL⟩ := frame_leftInverse (B z) (hB.2.2.2 z hzV).2
  have hBa (i j) : ContDiffOn ℂ ∞ (fun w => B w i j) V :=
    ((differentiableOn_pi.mp (differentiableOn_pi.mp hB.2.2.1 i) j).contDiffOn hB.1).of_le le_top
  have hFa (i j) : ContDiffOn ℂ ∞ (fun w => F w i j) U :=
    ((differentiableOn_pi.mp (differentiableOn_pi.mp hF.2.2.1 i) j).contDiffOn hF.1).of_le le_top
  have hLB (i j) : ContDiffOn ℂ ∞ (fun w => (L * B w) i j) V :=
    holomorphic_matrix_mul (A := fun _ => L) (fun _ _ => contDiffOn_const) hBa i j
  have hdet := holomorphic_matrix_det hLB
  let O := U ∩ V ∩ {w | (L * B w).det ≠ 0}
  have hVN : IsOpen (V ∩ {w | (L * B w).det ≠ 0}) :=
    hdet.continuousOn.isOpen_inter_preimage hB.1 isOpen_ne
  have hO : IsOpen O := by
    simpa only [O, inter_assoc] using hF.1.inter hVN
  have hzO : z ∈ O := ⟨⟨hzU, hzV⟩, by change (L * B z).det ≠ 0; rw [hL, Matrix.det_one]; exact one_ne_zero⟩
  have hOV : O ⊆ V := fun _ hw => hw.1.2
  have hOU : O ⊆ U := fun _ hw => hw.1.1
  have hi (i j) := holomorphic_matrix_inv (fun i j => (hLB i j).mono hOV)
    (fun w (hw : w ∈ O) => hw.2) i j
  let C := fun w => (L * B w)⁻¹ * L * F w
  have hIL (i j) : ContDiffOn ℂ ∞ (fun w => ((L * B w)⁻¹ * L) i j) O :=
    holomorphic_matrix_mul (B := fun _ => L) hi (fun _ _ => contDiffOn_const) i j
  have hC (i j) : ContDiffOn ℂ ∞ (fun w => C w i j) O :=
    holomorphic_matrix_mul hIL (fun i j => (hFa i j).mono hOU) i j
  have hCF : ∀ w ∈ O, B w * C w = F w ∧ (C w).det ≠ 0 := by
    intro w hw
    exact frame_gauge_factor _ _ L (hB.2.2.2 w hw.1.2).2 (hF.2.2.2 w hw.1.1).2
      ((hF.2.2.2 w hw.1.1).1.trans (hB.2.2.2 w hw.1.2).1.symm) hw.2
  exact ⟨O, hO, hzO, fun _ hw => hw.1, C, hC,
    holomorphic_matrix_inv hC (fun w hw => (hCF w hw).2),
    fun w hw => (hCF w hw).1, fun w hw => (hCF w hw).2⟩

end Yau.Proofs.B01Aux
