import Yau.LeafProofs.L05ChuFrozenLinear

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem chu_transformed_difference {n : ℕ} {T : Sym n → Point n → Sym n}
    {K beta : ℝ} (hT : ChuH2 T K beta) (S : Point n → Sym n)
    (H J : Sym n) {p q : Point n} (hp : p ∈ backward 1) :
    (S p+T H p)-(S q+T J q)=T (H-J) p+(S p-S q)+(T J p-T J q) := by
  have he := (chuTransformLinear hT p hp).map_sub H J
  change T (H-J) p=T H p-T J p at he
  rw [he]
  abel

theorem chu_transformed_difference_norm {n : ℕ} {T : Sym n → Point n → Sym n}
    {S : Point n → Sym n} {K beta : ℝ} (hK : 0 ≤ K) (hT : ChuH2 T K beta)
    (hS : ChuH3 S K beta) (H J : Sym n) {p q : Point n}
    (hp : p ∈ backward 1) (hq : q ∈ backward 1) :
    ‖(S p+T H p)-(S q+T J q)‖ ≤
      chuTransformNormConstant n K*‖H-J‖+K*(1+2*‖J‖)*holderWeight beta p q := by
  rw [chu_transformed_difference hT S H J hp]
  have ht := chuTransform_norm_le hK hT hp (H-J)
  have hs := hS.2 p hp q hq
  have hv := chuTransform_variation hT J p hp q hq
  have hn := (norm_add_le (T (H-J) p+(S p-S q)) (T J p-T J q)).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  nlinarith only [hn,ht,hs,hv]

theorem chu_transformed_difference_frozen {n : ℕ} {T : Sym n → Point n → Sym n}
    {K beta : ℝ} (hT : ChuH2 T K beta) (S : Point n → Sym n)
    (H J : Sym n) {p q p0 : Point n} (hp : p ∈ backward 1) :
    ((S p+T H p)-(S q+T J q))-T (H-J) p0=
      (T (H-J) p-T (H-J) p0)+(S p-S q)+(T J p-T J q) := by
  rw [chu_transformed_difference hT S H J hp]
  abel

theorem chu_transformed_difference_frozen_norm {n : ℕ} {T : Sym n → Point n → Sym n}
    {S : Point n → Sym n} {K beta : ℝ} (hT : ChuH2 T K beta)
    (hS : ChuH3 S K beta) (H J : Sym n) {p q p0 : Point n}
    (hp : p ∈ backward 1) (hq : q ∈ backward 1) (hp0 : p0 ∈ backward 1) :
    ‖((S p+T H p)-(S q+T J q))-T (H-J) p0‖ ≤
      2*K*‖H-J‖*holderWeight beta p p0+K*(1+2*‖J‖)*holderWeight beta p q := by
  rw [chu_transformed_difference_frozen hT S H J hp]
  have ht := chuTransform_variation hT (H-J) p hp p0 hp0
  have hs := hS.2 p hp q hq
  have hv := chuTransform_variation hT J p hp q hq
  have hn := (norm_add_le ((T (H-J) p-T (H-J) p0)+(S p-S q)) (T J p-T J q)).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  nlinarith only [hn,ht,hs,hv]

set_option maxHeartbeats 1600000 in
theorem chu_frozen_nonlinear_error {n : ℕ} {E U : Set (Sym n)} (hE : Convex ℝ E)
    {F : Sym n → Point n → ℝ} {T : Sym n → Point n → Sym n} {S : Point n → Sym n}
    {ell L K beta : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) (hK : 0 ≤ K)
    (hF : ChuH1 E U F ell L K beta) (hT : ChuH2 T K beta) (hS : ChuH3 S K beta)
    {omega : ℝ → ℝ} (hm : Modulus omega) (hDF : ChuDerivativeModulus E F omega)
    {A0 H J : Sym n} (hA0 : A0 ∈ E) {p q p0 : Point n}
    (hp : p ∈ backward 1) (hq : q ∈ backward 1) (hp0 : p0 ∈ backward 1)
    (hAp : S p+T H p ∈ E) (hAq : S q+T J q ∈ E)
    {delta : ℝ} (hd : 0 ≤ delta) (hAd : ‖S p+T H p-A0‖ ≤ delta)
    (hBd : ‖S q+T J q-A0‖ ≤ delta) :
    |F (S p+T H p) p-F (S q+T J q) q-chuFrozenLinear hT F A0 p0 hp0 (H-J)| ≤
      (omega (delta+parabolicDistance p p0)*chuTransformNormConstant n K+
        2*bellmanMatrixConstant n L*K*holderWeight beta p p0)*‖H-J‖+
      (K+(omega (delta+parabolicDistance p p0)+bellmanMatrixConstant n L)*K*(1+2*‖J‖))*
        holderWeight beta p q := by
  let A := S p+T H p
  let B := S q+T J q
  let V := A-B
  let Z := V-T (H-J) p0
  let l := fderiv ℝ (fun N => F N p0) A0
  have hl := chu_linearization_spaceTime_error hE hF hm hDF hAp hAq hA0 hp hq hp0 hd hAd hBd
  have hdZ := chuDerivative_bound hell hF hA0 hp0 Z
  have hnorm := chu_transformed_difference_norm hK hT hS H J hp hq
  have hnormZ := chu_transformed_difference_frozen_norm hT hS H J hp hq hp0
  have hw : 0 ≤ omega (delta+parabolicDistance p p0) :=
    hm.2.1 _ (add_nonneg hd (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)))
  have hC := bellmanMatrixConstant_nonneg n (hell.trans hL)
  have hscaled := mul_le_mul_of_nonneg_left hnorm hw
  have hscaledZ := mul_le_mul_of_nonneg_left hnormZ hC
  have he : F A p-F B q-chuFrozenLinear hT F A0 p0 hp0 (H-J)=
      (F A p-F B q-l V)+l Z := by
    have hz : l Z=l V-l (T (H-J) p0) := l.map_sub V (T (H-J) p0)
    change F A p-F B q-l (T (H-J) p0)=(F A p-F B q-l V)+l Z
    linarith only [hz]
  rw [he]
  have htri := abs_add_le (F A p-F B q-l V) (l Z)
  change |F A p-F B q-l V| ≤ omega (delta+parabolicDistance p p0)*‖V‖+
    K*holderWeight beta p q at hl
  change |l Z| ≤ bellmanMatrixConstant n L*‖Z‖ at hdZ
  change omega (delta+parabolicDistance p p0)*‖V‖ ≤ _ at hscaled
  change bellmanMatrixConstant n L*‖Z‖ ≤ _ at hscaledZ
  nlinarith only [htri,hl,hdZ,hscaled,hscaledZ]

end Yau.LeafProofs.L05Aux
