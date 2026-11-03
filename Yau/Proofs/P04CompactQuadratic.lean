import Yau.Proofs.P04RankOneBound

noncomputable section
open Set WithLp
open scoped Topology InnerProductSpace Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ}

def matrixQuadratic (A : Matrix (Fin n) (Fin n) ℂ) (v : ComplexVector n) : ℝ :=
  (star (fun i => v i) ⬝ᵥ (A *ᵥ (fun i => v i))).re

theorem matrixQuadratic_real_smul (A : Matrix (Fin n) (Fin n) ℂ)
    (r : ℝ) (v : ComplexVector n) : matrixQuadratic A (r • v)=r^2*matrixQuadratic A v := by
  have heq : star (fun i => (r • v) i) ⬝ᵥ (A *ᵥ (fun i => (r • v) i)) =
      ((r^2 : ℝ) : ℂ)*(star (fun i => v i) ⬝ᵥ (A *ᵥ (fun i => v i))) := by
    simp only [Matrix.mulVec,dotProduct,Pi.star_apply,PiLp.smul_apply,Complex.real_smul,
      map_mul,Complex.star_def,Complex.conj_ofReal,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  unfold matrixQuadratic
  rw [heq]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem matrixQuadratic_continuous {α : Type*} [TopologicalSpace α]
    {A : α → Matrix (Fin n) (Fin n) ℂ} (hA : Continuous A) :
    Continuous (fun p : α × ComplexVector n => matrixQuadratic (A p.1) p.2) := by
  unfold matrixQuadratic Matrix.mulVec dotProduct
  apply Complex.continuous_re.comp
  apply continuous_finset_sum
  intro i _
  apply Continuous.mul
  · exact ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℂ) i).comp continuous_snd).star
  · apply continuous_finset_sum
    intro j _
    exact (((continuous_apply j).comp ((continuous_apply i).comp hA)).comp continuous_fst).mul
      ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℂ) j).comp continuous_snd)

theorem matrixQuadratic_pos {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef)
    {v : ComplexVector n} (hv : v ≠ 0) : 0 < matrixQuadratic A v := by
  apply (Complex.pos_iff.mp (hA.dotProduct_mulVec_pos (x := fun i => v i) ?_)).1
  intro hzero
  apply hv
  ext i
  exact congrFun hzero i

/-- Strict positivity on a compact parameter family gives one positive
quadratic lower bound; no global eigenvalue bound is assumed. -/
theorem compact_posDef_uniform_lower_bound {α : Type*} [TopologicalSpace α] [CompactSpace α]
    (A : α → Matrix (Fin n) (Fin n) ℂ) (hA : Continuous A) (hpos : ∀ a, (A a).PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a v, δ*‖v‖^2 ≤ matrixQuadratic (A a) v := by
  let K : Set (α × ComplexVector n) := univ ×ˢ Metric.sphere 0 1
  have hK : IsCompact K := isCompact_univ.prod (isCompact_sphere 0 1)
  have hn (v : ComplexVector n) (hv : v ≠ 0) : ‖‖v‖⁻¹ • v‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hmem (a : α) (v : ComplexVector n) (hv : v ≠ 0) :
      (a,‖v‖⁻¹ • v) ∈ K := ⟨mem_univ a,by simpa only [Metric.mem_sphere,dist_zero_right] using hn v hv⟩
  by_cases hne : K.Nonempty
  · obtain ⟨p,hp,hmin⟩ := hK.exists_isMinOn hne (matrixQuadratic_continuous hA).continuousOn
    have hp0 : p.2 ≠ 0 := by
      have Hnorm : ‖p.2‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hp.2
      intro hzero
      simp [hzero] at Hnorm
    refine ⟨matrixQuadratic (A p.1) p.2,matrixQuadratic_pos (hpos _) hp0,fun a v => ?_⟩
    by_cases hv : v=0
    · subst v
      simp [matrixQuadratic,Matrix.mulVec,dotProduct]
    · have HH := hmin (hmem a v hv)
      change matrixQuadratic (A p.1) p.2 ≤ matrixQuadratic (A a) (‖v‖⁻¹ • v) at HH
      rw [matrixQuadratic_real_smul] at HH
      have Hmul := mul_le_mul_of_nonneg_right HH (sq_nonneg ‖v‖)
      have hcancel : (‖v‖⁻¹)^2*‖v‖^2=1 := by
        rw [← mul_pow,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv),one_pow]
      have heq : (‖v‖⁻¹)^2*matrixQuadratic (A a) v*‖v‖^2 = matrixQuadratic (A a) v := by
        calc
          _ = matrixQuadratic (A a) v*((‖v‖⁻¹)^2*‖v‖^2) := by ring
          _ = _ := by rw [hcancel,mul_one]
      rwa [heq] at Hmul
  · refine ⟨1,by norm_num,fun a v => ?_⟩
    have hv : v=0 := by by_contra hv; exact hne ⟨_,hmem a v hv⟩
    simp [hv,matrixQuadratic,Matrix.mulVec,dotProduct]

end Yau.Proofs.P04Aux
