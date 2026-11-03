import Yau.Proofs.D05GaussDensity
import Yau.Proofs.D05MatrixProjection
import Yau.Proofs.V03AmbientTensorAlgebra

/-! Unique lifting of an actual full-column ambient frame to centered
cotangent coordinates. Complex regularity is proved in each valid fixed chart. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau V03Proof

theorem matrix_leftInverse {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix κ ι ℂ) (hA : Function.Injective A.mulVec) :
    ∃ L : Matrix ι κ ℂ, L * A = 1 := by
  classical
  have hEu : Function.Injective (Matrix.toEuclideanLin A) := by
    intro u v huv
    apply WithLp.ofLp_injective
    apply hA
    exact congrArg WithLp.ofLp huv
  obtain ⟨l, hl⟩ := (Matrix.toEuclideanLin A).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hEu)
  refine ⟨Matrix.toEuclideanLin.symm l, ?_⟩
  apply Matrix.toEuclideanLin.injective
  simpa only [Matrix.toLpLin_mul_same, LinearEquiv.apply_symm_apply, Matrix.toLpLin_one] using hl

theorem leftInverse_lift_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix κ ι ℂ) (L : Matrix ι κ ℂ) (V : Matrix κ ι ℂ)
    (hLA : L * A = 1)
    (hV : ∀ j, ∃ u : ι → ℂ, A *ᵥ u = fun a => V a j) :
    A * (L * V) = V := by
  ext a j
  obtain ⟨u, hu⟩ := hV j
  have hLu : L *ᵥ (fun a => V a j) = u := by
    rw [← hu, Matrix.mulVec_mulVec, hLA, Matrix.one_mulVec]
  change (A *ᵥ (L *ᵥ (fun a => V a j))) a = V a j
  rw [hLu]
  exact congrFun hu a

theorem matrix_mul_contDiffOn {ι κ τ : Type*} [Fintype κ]
    {A : ℂ → Matrix ι κ ℂ} {B : ℂ → Matrix κ τ ℂ} {S : Set ℂ}
    (hA : ∀ i j, ContDiffOn ℂ ∞ (fun z => A z i j) S)
    (hB : ∀ i j, ContDiffOn ℂ ∞ (fun z => B z i j) S) (i : ι) (j : τ) :
    ContDiffOn ℂ ∞ (fun z => (A z * B z) i j) S := by
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hA i k).mul (hB k j)

variable {n q : ℕ} {M : ComplexManifold n}

def centeredAmbientLift (G : CotangentPoint M → ComplexVector q)
    (f : ℂ → CotangentPoint M) (V : ℂ → Matrix (Fin q) (CotangentIndex n) ℂ)
    (z : ℂ) : CotangentMatrix n :=
  gramLeftInverse (cotangentDG G (f z).1 (f z)) * V z

theorem centeredAmbientLift_ambient {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) (f : ℂ → CotangentPoint M)
    (V : ℂ → Matrix (Fin q) (CotangentIndex n) ℂ) {z : ℂ}
    (hV : ∀ j, ∃ u : CotangentIndex n → ℂ,
      cotangentDG G (f z).1 (f z) *ᵥ u = fun a => V z a j) :
    ambientFrame G f (centeredAmbientLift G f V) z = V z := by
  have hGram : IsUnit ((cotangentDG G (f z).1 (f z))ᴴ * cotangentDG G (f z).1 (f z)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (cotangentDG_gram_posDef hG (f z)).det_pos.ne')
  exact leftInverse_lift_mul _ _ _ (gramLeftInverse_mul hGram) hV

theorem ambient_frame_lift_is_frame {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : ℂ → CotangentPoint M} (hf : CotangentDisc f)
    (V : ℂ → Matrix (Fin q) (CotangentIndex n) ℂ)
    (hVs : ∀ a j, ContDiffOn ℂ ∞ (fun z => V z a j) (Metric.closedBall (0 : ℂ) 1))
    (hVi : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective (V z).mulVec)
    (hVr : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ j,
      ∃ u : CotangentIndex n → ℂ,
        cotangentDG G (f z).1 (f z) *ᵥ u = fun a => V z a j) :
    IsDiscFrame f (centeredAmbientLift G f V) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        ambientFrame G f (centeredAmbientLift G f V) z = V z := by
  let E := centeredAmbientLift G f V
  have hEV : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ambientFrame G f E z = V z :=
    fun z hz => centeredAmbientLift_ambient hG f V (hVr z hz)
  have hEdet : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, (E z).det ≠ 0 := by
    intro z hz
    have hEinj : Function.Injective (E z).mulVec := by
      intro v w hvw
      apply hVi z hz
      calc
        V z *ᵥ v = ambientFrame G f E z *ᵥ v := by rw [hEV z hz]
        _ = ambientFrame G f E z *ᵥ w := by
          simp only [ambientFrame, ← Matrix.mulVec_mulVec, hvw]
        _ = V z *ᵥ w := by rw [hEV z hz]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.mulVec_injective_iff_isUnit.mp hEinj)).ne_zero
  refine ⟨⟨hEdet, hf, ?_⟩, hEV⟩
  intro z₀ hz₀
  let x := (f z₀).1
  obtain ⟨V₀, hV₀, hz₀V, hsource, hcoord⟩ := (cotangentDisc_holomorphicOn hf).2 z₀ hz₀
  let W : ℂ → Matrix (Fin q) (CotangentIndex n) ℂ := fun z => cotangentDG G x (f z)
  have hW : ∀ a j, ContDiffOn ℂ ∞ (fun z => W z a j) (Metric.closedBall 0 1 ∩ V₀) := by
    intro a j z hz
    exact cotangentDG_entry_contDiffWithinAt hG.1 x (hsource z hz) (hcoord z hz) a j
  have hW₀ : Function.Injective (W z₀).mulVec :=
    cotangentDG_mulVec_injective_in_chart hG x (f z₀) (mem_extChartAt_source _)
  obtain ⟨L, hL⟩ := matrix_leftInverse (W z₀) hW₀
  have hLW : ∀ i j, ContDiffOn ℂ ∞ (fun z => (L * W z) i j)
      (Metric.closedBall 0 1 ∩ V₀) :=
    matrix_mul_contDiffOn (fun _ _ => contDiffOn_const) hW
  have hdet := Yau.Proofs.B01Aux.holomorphic_matrix_det hLW
  have hdet₀ : (L * W z₀).det ≠ 0 := by rw [hL, Matrix.det_one]; exact one_ne_zero
  have hdetEvent : ∀ᶠ z in 𝓝[Metric.closedBall 0 1 ∩ V₀] z₀, (L * W z).det ≠ 0 :=
    (hdet.continuousOn z₀ ⟨hz₀, hz₀V⟩).eventually_ne hdet₀
  obtain ⟨O, hO, hz₀O, hdetO⟩ := mem_nhdsWithin.mp hdetEvent
  let V₁ := V₀ ∩ O
  have hSV : Metric.closedBall (0 : ℂ) 1 ∩ V₁ ⊆ Metric.closedBall 0 1 ∩ V₀ :=
    fun z hz => ⟨hz.1, hz.2.1⟩
  have hdet₁ : ∀ z ∈ Metric.closedBall (0 : ℂ) 1 ∩ V₁, (L * W z).det ≠ 0 :=
    fun z hz => hdetO ⟨hz.2.2, ⟨hz.1, hz.2.1⟩⟩
  have hInv : ∀ i j, ContDiffOn ℂ ∞ (fun z => (L * W z)⁻¹ i j)
      (Metric.closedBall 0 1 ∩ V₁) :=
    Yau.Proofs.B01Aux.holomorphic_matrix_inv (fun i j => (hLW i j).mono hSV) hdet₁
  have hCand : ∀ i j, ContDiffOn ℂ ∞ (fun z => ((L * W z)⁻¹ * L * V z) i j)
      (Metric.closedBall 0 1 ∩ V₁) :=
    matrix_mul_contDiffOn (matrix_mul_contDiffOn hInv (fun _ _ => contDiffOn_const))
      (fun a j => (hVs a j).mono Set.inter_subset_left)
  have hGauge : ∀ z ∈ Metric.closedBall (0 : ℂ) 1 ∩ V₁,
      frameInChart x f E z = (L * W z)⁻¹ * L * V z := by
    intro z hz
    have hWV : W z * frameInChart x f E z = V z :=
      (ambientFrame_in_fixed_chart hG.1 f E x z (hsource z (hSV hz))).symm.trans (hEV z hz.1)
    have hLS : (L * W z) * frameInChart x f E z = L * V z := by
      rw [Matrix.mul_assoc, hWV]
    calc
      frameInChart x f E z = ((L * W z)⁻¹ * (L * W z)) * frameInChart x f E z := by
        rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet₁ z hz)), Matrix.one_mul]
      _ = (L * W z)⁻¹ * L * V z := by rw [Matrix.mul_assoc, hLS, ← Matrix.mul_assoc]
  refine ⟨V₁, hV₀.inter hO, ⟨hz₀V, hz₀O⟩,
    fun z hz => hsource z (hSV hz), ?_⟩
  intro i j
  exact (hCand i j).congr (fun z hz => congrFun (congrFun (hGauge z hz) i) j)

end Yau.Blueprint.D05Proof
