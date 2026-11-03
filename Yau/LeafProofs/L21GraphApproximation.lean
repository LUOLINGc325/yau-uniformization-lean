import Yau.LeafProofs.L21FirstOrderEstimate
import Yau.LeafProofs.L21L2Limits
import Yau.LeafProofs.L14LocalFriedrichs

/-! Fixed-support graph approximation for the literal Newlander--Nirenberg
rows and their genuine distributional equation. -/

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def DbarWeakEquation (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (u : X n → ℂ) (w : X n → Fin n → ℂ) : Prop :=
  ∀ i (ψ : X n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    (∫ x, (ψ x : ℂ) * w x i ∂Yau.lebesgueC n) =
      ∫ x, u x * transposeRow A i ψ x ∂Yau.lebesgueC n

theorem exists_fixed_support_dbarA_graph_approx
    {O K : Set (X n)} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (u : X n → ℂ) (w : X n → Fin n → ℂ)
    (hu : MemLp u 2 (Yau.lebesgueC n))
    (hw : ∀ i, MemLp (fun x => w x i) 2 (Yau.lebesgueC n))
    (hsu : tsupport u ⊆ K) (hsw : ∀ i, tsupport (fun x => w x i) ⊆ K)
    (heq : DbarWeakEquation A u w) :
    ∃ (L : Set (X n)) (U : ℕ → CompactTest O), IsCompact L ∧ L ⊆ O ∧
      (∀ m, tsupport (U m) ⊆ L) ∧
      Tendsto (fun m => ∫ x, ‖U m x - u x‖ ^ 2 ∂Yau.lebesgueC n) atTop (𝓝 0) ∧
      ∀ i, (∀ m, MemLp (fun x => dbarA A i (U m) x - w x i) 2 (Yau.lebesgueC n)) ∧
        Tendsto (fun m => ∫ x, ‖dbarA A i (U m) x - w x i‖ ^ 2 ∂Yau.lebesgueC n)
          atTop (𝓝 0) := by
  let a := fun (i : Fin n) (_ : Unit) (r : Yau.RIdx n) x => dbarRealCoefficient A i r x
  let b := fun (_ : Fin n) (_ : Unit) (_ : X n) => (0 : ℂ)
  have hr : ∀ i (ψ : X n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x, (ψ x : ℂ) * w x i ∂Yau.lebesgueC n) =
        ∫ x, ∑ c : Unit, u x *
          Yau.LeafProofs.L14Aux.complexFormalAdjointTestRow Yau.realVec a b i c ψ x
          ∂Yau.lebesgueC n := by
    intro i ψ hψ hcψ
    simpa only [a, b, Yau.LeafProofs.L14Aux.complexFormalAdjointTestRow,
      Fintype.sum_unique, zero_mul, add_zero, transposeRow] using heq i ψ hψ hcψ
  obtain ⟨L, U, hcL, hLO, hU, htU, htD⟩ :=
    Yau.LeafProofs.L14Aux.exists_fixed_support_complex_firstOrder_graph_approx_norm
      hO hK hKO Yau.realVec a b (fun i _ r => dbarRealCoefficient_smoothOn hA i r)
      (fun _ _ => contDiffOn_const) (fun x (_ : Unit) => u x) w
      (fun _ => hu) hw (fun _ => hsu) hsw hr
  let V : ℕ → CompactTest O := fun m =>
    ⟨fun x => U m x (), (hU m ()).1,
      hcL.of_isClosed_subset (isClosed_tsupport _) (hU m ()).2, ((hU m ()).2).trans hLO⟩
  refine ⟨L, V, hcL, hLO, fun m => (hU m ()).2, (htU ()).2, ?_⟩
  intro i
  have hh := htD i
  simpa only [Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply,
    a, b, Fintype.sum_unique, zero_mul, add_zero, ← dbarA_eq_real_rows] using hh

theorem dbarA_sub
    (A : X n → Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    {f g : X n → ℂ} {x : X n} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dbarA A i (f - g) x = dbarA A i f x - dbarA A i g x := by
  simp only [dbarA_eq_real_rows, fderiv_sub hf hg, _root_.sub_apply,
    mul_sub, Finset.sum_sub_distrib]

theorem directional_memLp {f : X n → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) (v : X n) :
    MemLp (fun x => fderiv ℝ f x v) 2 (Yau.lebesgueC n) := by
  letI : IsLocallyFiniteMeasure (Yau.lebesgueC n) := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  exact (contDiff_directional hf v).continuous.memLp_of_hasCompactSupport (hcf.fderiv_apply ℝ v)

theorem dbarA_memLp {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (f : CompactTest O) (i : Fin n) :
    MemLp (dbarA A i f) 2 (Yau.lebesgueC n) := by
  letI : IsLocallyFiniteMeasure (Yau.lebesgueC n) := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  let g := testD hO hA i f
  exact g.property.1.continuous.memLp_of_hasCompactSupport g.property.2.1

theorem dbarA_graph_convergence_gradient_cauchy
    {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hsmall : ∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2)
    (U : ℕ → CompactTest O) (w : X n → Fin n → ℂ)
    (hw : ∀ i, MemLp (fun x => w x i) 2 (Yau.lebesgueC n))
    (htD : ∀ i, Tendsto (fun m => ∫ x, ‖dbarA A i (U m) x - w x i‖ ^ 2
      ∂Yau.lebesgueC n) atTop (𝓝 0)) :
    ∀ a : Yau.RIdx n, CauchySeq (fun m =>
      (directional_memLp (U m).property.1 (U m).property.2.1 (Yau.realVec a)).toLp
        (fun x => fderiv ℝ (U m) x (Yau.realVec a))) := by
  have ht (i : Fin n) := complex_pair_norm_sq_tendsto_zero
    (fun m x => dbarA A i (U m) x) (fun x => w x i)
    (fun m => dbarA_memLp hO hA (U m) i) (hw i) (htD i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => ht i)
  simp only [Finset.sum_const_zero] at hsum
  have he (p : ℕ × ℕ) := first_order_energy_on_compact_tests hO hA hsmall (U p.1 - U p.2)
  have hsub (p : ℕ × ℕ) (x : X n) (a : Yau.RIdx n) :
      fderiv ℝ (fun y => U p.1 y - U p.2 y) x (Yau.realVec a) =
        fderiv ℝ (U p.1) x (Yau.realVec a) - fderiv ℝ (U p.2) x (Yau.realVec a) := by
    rw [fderiv_fun_sub ((U p.1).property.1.differentiable (by simp) x)
      ((U p.2).property.1.differentiable (by simp) x), _root_.sub_apply]
  have hdsub (p : ℕ × ℕ) (x : X n) (i : Fin n) :
      dbarA A i (U p.1 - U p.2 : CompactTest O) x =
        dbarA A i (U p.1) x - dbarA A i (U p.2) x :=
    dbarA_sub A i ((U p.1).property.1.differentiable (by simp) x)
      ((U p.2).property.1.differentiable (by simp) x)
  have hsub' (p : ℕ × ℕ) (x : X n) (a : Yau.RIdx n) :
      fderiv ℝ (U p.1 - U p.2 : CompactTest O) x (Yau.realVec a) =
        fderiv ℝ (U p.1) x (Yau.realVec a) - fderiv ℝ (U p.2) x (Yau.realVec a) := hsub p x a
  intro a
  apply complex_cauchySeq_toLp_of_pair_norm_sq
  apply squeeze_zero (fun p => integral_nonneg fun x => sq_nonneg _) ?_
    (by simpa only [mul_zero] using hsum.const_mul 16)
  intro p
  have h := he p
  simp only [hsub', hdsub] at h
  exact (Finset.single_le_sum
    (fun b _ => integral_nonneg fun x => sq_nonneg ‖fderiv ℝ (U p.1) x (Yau.realVec b) -
      fderiv ℝ (U p.2) x (Yau.realVec b)‖) (Finset.mem_univ a)).trans h

end Yau.LeafProofs.L21Aux
