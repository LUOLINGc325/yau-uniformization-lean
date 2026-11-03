import Yau.Proofs.P06HodgeRegularityCalculus

/-! Genuine weak Leibniz and linearity identities used in the elliptic jet
bootstrap. Every multiplication and integral retains its actual L² domain. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsLocallyFiniteMeasure ν]

/-- Weak Leibniz rule for a fixed smooth compact coefficient. -/
theorem regularityWeakDeriv_compact_mul {O : Set E} {e : E} {u v a : E → ℝ}
    (hu : MemLp u 2 (ν.restrict O)) (hv : MemLp v 2 (ν.restrict O))
    (hweak : regularityWeakDeriv ν O e u v)
    (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a) :
    MemLp (fun z => a z * u z) 2 (ν.restrict O) ∧
      MemLp (fun z => a z * v z + fderiv ℝ a z e * u z) 2 (ν.restrict O) ∧
      regularityWeakDeriv ν O e (fun z => a z * u z)
        (fun z => a z * v z + fderiv ℝ a z e * u z) := by
  have htop : MemLp a (⊤ : ENNReal) (ν.restrict O) :=
    (ha.continuous.memLp_top_of_hasCompactSupport hca _).restrict O
  have hdtop : MemLp (fun z => fderiv ℝ a z e) (⊤ : ENNReal) (ν.restrict O) :=
    ((((ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous).memLp_top_of_hasCompactSupport (hca.fderiv_apply ℝ e) _).restrict O
  have hau : MemLp (fun z => a z * u z) 2 (ν.restrict O) := htop.mul hu
  have hav : MemLp (fun z => a z * v z) 2 (ν.restrict O) := htop.mul hv
  have hdau : MemLp (fun z => fderiv ℝ a z e * u z) 2 (ν.restrict O) := hdtop.mul hu
  refine ⟨hau, hav.add hdau, ?_⟩
  intro φ hφ
  have hφL := regularityTest_memLp ν hφ
  have hDφL := regularityTest_memLp ν (regularityTest_direction hφ e)
  have hX : Integrable (fun z => (a z * u z) * fderiv ℝ φ z e) (ν.restrict O) :=
    hau.integrable_mul hDφL
  have hY : Integrable (fun z => (fderiv ℝ a z e * u z) * φ z) (ν.restrict O) :=
    hdau.integrable_mul hφL
  have hZ : Integrable (fun z => (a z * v z) * φ z) (ν.restrict O) := hav.integrable_mul hφL
  have h := hweak (fun z => φ z * a z) (regularityTest_mul hφ ha)
  have hprod (z : E) : fderiv ℝ (fun y => φ y * a y) z e =
      φ z * fderiv ℝ a z e + a z * fderiv ℝ φ z e := by
    rw [fderiv_fun_mul (hφ.1.differentiable (by simp) z) (ha.differentiable (by simp) z)]
    rfl
  have hleft : (fun z => u z * fderiv ℝ (fun y => φ y * a y) z e) =
      fun z => (a z * u z) * fderiv ℝ φ z e + (fderiv ℝ a z e * u z) * φ z := by
    funext z
    rw [hprod]
    ring
  have hright : (fun z => v z * (φ z * a z)) = fun z => (a z * v z) * φ z := by
    funext z
    ring
  rw [hleft, hright, integral_add hX hY] at h
  have hgoal : (fun z => (a z * v z + fderiv ℝ a z e * u z) * φ z) =
      fun z => (a z * v z) * φ z + (fderiv ℝ a z e * u z) * φ z := by
    funext z
    ring
  rw [hgoal, integral_add hZ hY]
  linarith

theorem regularityWeakDeriv_zero (O : Set E) (e : E) :
    regularityWeakDeriv ν O e (fun _ => 0) (fun _ => 0) := by
  intro φ hφ
  simp

theorem regularityWeakDeriv_add {O : Set E} {e : E} {u v du dv : E → ℝ}
    (hu : MemLp u 2 (ν.restrict O)) (hv : MemLp v 2 (ν.restrict O))
    (hdu : MemLp du 2 (ν.restrict O)) (hdv : MemLp dv 2 (ν.restrict O))
    (hwu : regularityWeakDeriv ν O e u du) (hwv : regularityWeakDeriv ν O e v dv) :
    regularityWeakDeriv ν O e (fun z => u z + v z) (fun z => du z + dv z) := by
  intro φ hφ
  have hφL := regularityTest_memLp ν hφ
  have hDφL := regularityTest_memLp ν (regularityTest_direction hφ e)
  have hI := integral_add (hu.integrable_mul hDφL) (hv.integrable_mul hDφL)
  have hJ := integral_add (hdu.integrable_mul hφL) (hdv.integrable_mul hφL)
  simp only [Pi.mul_apply] at hI hJ
  simp_rw [add_mul]
  rw [hI, hJ, hwu φ hφ, hwv φ hφ]
  ring

theorem regularityWeakDeriv_const_mul {O : Set E} {e : E} {u du : E → ℝ}
    (hwu : regularityWeakDeriv ν O e u du) (c : ℝ) :
    regularityWeakDeriv ν O e (fun z => c * u z) (fun z => c * du z) := by
  intro φ hφ
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_const_mul, hwu φ hφ]
  ring

/-- Changing a raw representative on a null set preserves its actual weak
identity. This applies independently to the value and derivative fields. -/
theorem regularityWeakDeriv_congr_ae {O : Set E} {e : E} {u v u' v' : E → ℝ}
    (h : regularityWeakDeriv ν O e u v)
    (hu : u =ᵐ[ν.restrict O] u') (hv : v =ᵐ[ν.restrict O] v') :
    regularityWeakDeriv ν O e u' v' := by
  intro φ hφ
  have hi : (∫ z, u' z * fderiv ℝ φ z e ∂ν.restrict O) =
      ∫ z, u z * fderiv ℝ φ z e ∂ν.restrict O :=
    integral_congr_ae (hu.mono fun z hz => by dsimp only; rw [hz])
  have hj : (∫ z, v' z * φ z ∂ν.restrict O) = ∫ z, v z * φ z ∂ν.restrict O :=
    integral_congr_ae (hv.mono fun z hz => by dsimp only; rw [hz])
  rw [hi, hj]
  exact h φ hφ

end Yau.NodeProofs.P06Aux
