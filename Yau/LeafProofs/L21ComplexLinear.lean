import Yau.Geometry.Calculus

/-! Complex linear and conjugate-linear parts of a real continuous linear map. -/

noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def complexLinearOfReal (L : E →L[ℝ] F)
    (hI : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    E →L[ℂ] F where
  toFun := L
  map_add' := L.map_add
  map_smul' := by
    intro c v
    conv_lhs => rw [← c.re_add_im]
    conv_rhs => rw [← c.re_add_im]
    simp only [add_smul, mul_smul, Complex.coe_smul, L.map_add,
      L.map_smul, hI, RingHom.id_apply]
  cont := L.continuous

def linearPartReal (L : E →L[ℝ] F) :
    E →L[ℝ] F :=
  (1 / 2 : ℝ) • (L - Complex.I •
    (L.comp (Complex.I • ContinuousLinearMap.id ℝ E)))

def antilinearPartReal (L : E →L[ℝ] F) :
    E →L[ℝ] F :=
  (1 / 2 : ℝ) • (L + Complex.I •
    (L.comp (Complex.I • ContinuousLinearMap.id ℝ E)))

theorem linearPartReal_apply
    (L : E →L[ℝ] F) (v : E) :
    linearPartReal L v = (1 / 2 : ℝ) • (L v - Complex.I • L (Complex.I • v)) := rfl

theorem antilinearPartReal_apply
    (L : E →L[ℝ] F) (v : E) :
    antilinearPartReal L v = (1 / 2 : ℝ) • (L v + Complex.I • L (Complex.I • v)) := rfl

theorem linearPartReal_add_antilinearPartReal
    (L : E →L[ℝ] F) :
    linearPartReal L + antilinearPartReal L = L := by
  ext v
  simp only [_root_.add_apply, linearPartReal_apply, antilinearPartReal_apply]
  rw [← smul_add]
  have h : L v - Complex.I • L (Complex.I • v) +
      (L v + Complex.I • L (Complex.I • v)) = (2 : ℝ) • L v := by
    rw [two_smul]
    abel
  rw [h, smul_smul]
  norm_num

theorem linearPartReal_I
    (L : E →L[ℝ] F) (v : E) :
    linearPartReal L (Complex.I • v) = Complex.I • linearPartReal L v := by
  simp only [linearPartReal_apply, smul_smul, Complex.I_mul_I, neg_one_smul,
    map_neg, smul_neg]
  rw [smul_comm Complex.I (1 / 2 : ℝ)]
  simp only [smul_sub, smul_neg, smul_smul, Complex.I_mul_I,
    neg_one_smul, sub_neg_eq_add]
  abel

theorem antilinearPartReal_I
    (L : E →L[ℝ] F) (v : E) :
    antilinearPartReal L (Complex.I • v) = -Complex.I • antilinearPartReal L v := by
  simp only [antilinearPartReal_apply, smul_smul, Complex.I_mul_I, neg_one_smul,
    map_neg, smul_neg]
  rw [smul_comm (-Complex.I) (1 / 2 : ℝ)]
  simp only [smul_add, smul_neg, smul_smul, neg_smul, neg_mul,
    Complex.I_mul_I, neg_neg, one_smul]
  abel

def linearPart (L : E →L[ℝ] F) :
    E →L[ℂ] F :=
  complexLinearOfReal (linearPartReal L) (linearPartReal_I L)

end Yau.LeafProofs.L21Aux
