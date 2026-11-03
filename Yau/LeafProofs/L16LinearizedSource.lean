import Yau.LeafProofs.L16DifferenceQuotient

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def linearizedSpatialSource {n : ℕ} (e : Space n) (u : Point n → ℝ)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (f : Point n → ℝ) (p : Point n) : ℝ :=
  spatialPartial f e p+
    (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
      spatialPartial a e p i j*spatialDD u p (Yau.realVec i) (Yau.realVec j))+
    ∑ i : Yau.RIdx n, spatialPartial (fun q => b q i) e p*spatialD u p (Yau.realVec i)

def quotientSpatialSource {n : ℕ} (e : Space n) (h : ℝ) (u : Point n → ℝ)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (f : Point n → ℝ) (p : Point n) : ℝ :=
  spatialDifferenceQuotient f e h p+
    (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
      spatialDifferenceQuotient a e h p i j*
        spatialDD u (p.1+h • e,p.2) (Yau.realVec i) (Yau.realVec j))+
    ∑ i : Yau.RIdx n, spatialDifferenceQuotient (fun q => b q i) e h p*
      spatialD u (p.1+h • e,p.2) (Yau.realVec i)

def linearizedSourceBudget (n : ℕ) (F M U : ℝ) : ℝ :=
  F+(Fintype.card (Yau.RIdx n) : ℝ)^2*(M*U+M*U)+(Fintype.card (Yau.RIdx n) : ℝ)*(2*M*U)

theorem linearizedSpatialSource_holderBound {n : ℕ} {α T F M U : ℝ}
    {u f : Point n → ℝ} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (e : Space n) (hu : SchauderBound α (cylinder Set.univ 0 T) u U)
    (hLow : HolderBound α (cylinder Set.univ 0 T) (fun p => (u p,spatialD u p)) U)
    (hDa : HolderBound α (cylinder Set.univ 0 T) (spatialPartial a e) M)
    (hDb : ∀ i, HolderBound α (cylinder Set.univ 0 T) (spatialPartial (fun p => b p i) e) M)
    (hDf : HolderBound α (cylinder Set.univ 0 T) (spatialPartial f e) F) :
    HolderBound α (cylinder Set.univ 0 T) (linearizedSpatialSource e u a b f)
      (linearizedSourceBudget n F M U) := by
  have hPrincipal := hessian_contraction_holderBound hDa.1 hu.2.1
    (fun i j => holderBound_matrix_entry hDa i j)
    (fun i j p hp => by simpa only [Real.norm_eq_abs] using
      (holderBound_matrix_entry hDa i j).2.1 p hp) hu.2.2.2.1 hu.2.2.2.1.2.1
  have hDrift := holderBound_finset_sum Finset.univ (fun i _ =>
    holderBound_mul (hDb i) (holderBound_gradient_component (holderBound_snd hLow) i))
  have h := holderBound_add (holderBound_add hDf hPrincipal) hDrift
  change HolderBound α (cylinder Set.univ 0 T) (fun p => linearizedSpatialSource e u a b f p) _
  simpa only [linearizedSpatialSource,linearizedSourceBudget,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using h

theorem hessian_contraction_difference_bound {n : ℕ} (A B : Mat n)
    (H G : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    |(∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, A i j*H (Yau.realVec i) (Yau.realVec j))-
      (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, B i j*G (Yau.realVec i) (Yau.realVec j))| ≤
      (Fintype.card (Yau.RIdx n) : ℝ)^2*(‖A-B‖*‖H‖+‖B‖*‖H-G‖) := by
  let R : ℝ := ‖A-B‖*‖H‖+‖B‖*‖H-G‖
  have hEach (i j : Yau.RIdx n) :
      |A i j*H (Yau.realVec i) (Yau.realVec j)-B i j*G (Yau.realVec i) (Yau.realVec j)| ≤ R := by
    have hCoeff : |A i j-B i j| ≤ ‖A-B‖ := by
      simpa only [Matrix.sub_apply] using frobenius_entry_abs_le (A-B) i j
    have hHess : |H (Yau.realVec i) (Yau.realVec j)-G (Yau.realVec i) (Yau.realVec j)| ≤ ‖H-G‖ := by
      simpa only [sub_apply] using norm_hessian_component_le (H-G) i j
    have hEq : A i j*H (Yau.realVec i) (Yau.realVec j)-B i j*G (Yau.realVec i) (Yau.realVec j) =
        (A i j-B i j)*H (Yau.realVec i) (Yau.realVec j)+
          B i j*(H (Yau.realVec i) (Yau.realVec j)-G (Yau.realVec i) (Yau.realVec j)) := by ring
    rw [hEq]
    calc
      _ ≤ |(A i j-B i j)*H (Yau.realVec i) (Yau.realVec j)|+
        |B i j*(H (Yau.realVec i) (Yau.realVec j)-G (Yau.realVec i) (Yau.realVec j))| := abs_add_le _ _
      _ = |A i j-B i j| *|H (Yau.realVec i) (Yau.realVec j)|+
        |B i j| *|H (Yau.realVec i) (Yau.realVec j)-G (Yau.realVec i) (Yau.realVec j)| := by rw [abs_mul,abs_mul]
      _ ≤ R := add_le_add
        (mul_le_mul hCoeff (norm_hessian_component_le H i j) (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul (frobenius_entry_abs_le B i j) hHess (abs_nonneg _) (norm_nonneg _))
  have hRow (i : Yau.RIdx n) :
      |∑ j : Yau.RIdx n, (A i j*H (Yau.realVec i) (Yau.realVec j)-B i j*G (Yau.realVec i) (Yau.realVec j))| ≤
        (Fintype.card (Yau.RIdx n) : ℝ)*R := by
    exact (Finset.abs_sum_le_sum_abs _ Finset.univ).trans (by
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun j _ => hEach i j))
  have hSum := (Finset.abs_sum_le_sum_abs (fun i : Yau.RIdx n =>
    ∑ j : Yau.RIdx n, (A i j*H (Yau.realVec i) (Yau.realVec j)-B i j*G (Yau.realVec i) (Yau.realVec j))) Finset.univ).trans
      (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hRow i))
  simpa only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,pow_two,mul_assoc,R] using hSum

theorem drift_contraction_difference_bound {n : ℕ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (b d : Yau.RIdx n → ℝ) (V W : Space n →L[ℝ] ℝ)
    (hDiff : ∀ i, |b i-d i| ≤ A) (hValue : ∀ i, |d i| ≤ B) :
    |(∑ i : Yau.RIdx n, b i*V (Yau.realVec i))-(∑ i : Yau.RIdx n, d i*W (Yau.realVec i))| ≤
      (Fintype.card (Yau.RIdx n) : ℝ)*(A*‖V‖+B*‖V-W‖) := by
  have hEach (i : Yau.RIdx n) : |b i*V (Yau.realVec i)-d i*W (Yau.realVec i)| ≤ A*‖V‖+B*‖V-W‖ := by
    have hGrad : |V (Yau.realVec i)-W (Yau.realVec i)| ≤ ‖V-W‖ := by
      simpa only [sub_apply] using norm_gradient_component_le (V-W) i
    rw [show b i*V (Yau.realVec i)-d i*W (Yau.realVec i) =
      (b i-d i)*V (Yau.realVec i)+d i*(V (Yau.realVec i)-W (Yau.realVec i)) by ring]
    exact (abs_add_le _ _).trans (by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul (hDiff i) (norm_gradient_component_le V i) (abs_nonneg _) hA)
        (mul_le_mul (hValue i) hGrad (abs_nonneg _) hB))
  have h := (Finset.abs_sum_le_sum_abs _ Finset.univ).trans
    (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hEach i))
  simpa only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using h

theorem quotientSpatialSource_sub_bound {n : ℕ} {α T F M U : ℝ} (hα : 0 < α)
    {u f : Point n → ℝ} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (e : Space n) (hu : SchauderBound α (cylinder Set.univ 0 T) u U)
    (hLow : HolderBound α (cylinder Set.univ 0 T) (fun p => (u p,spatialD u p)) U)
    (hDa : HolderBound α (cylinder Set.univ 0 T) (spatialPartial a e) M)
    (hDb : ∀ i, HolderBound α (cylinder Set.univ 0 T) (spatialPartial (fun p => b p i) e) M)
    (hDf : HolderBound α (cylinder Set.univ 0 T) (spatialPartial f e) F)
    (hDiffa : ∀ p ∈ cylinder Set.univ 0 T, DifferentiableAt ℝ (fun x => a (x,p.2)) p.1)
    (hDiffb : ∀ i, ∀ p ∈ cylinder Set.univ 0 T, DifferentiableAt ℝ (fun x => b (x,p.2) i) p.1)
    (hDifff : ∀ p ∈ cylinder Set.univ 0 T, DifferentiableAt ℝ (fun x => f (x,p.2)) p.1)
    {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) {h : ℝ} (hh : h ≠ 0) :
    |quotientSpatialSource e h u a b f p-linearizedSpatialSource e u a b f p| ≤
      linearizedSourceBudget n F M U*‖h • e‖^α := by
  letI : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
  let r : ℝ := ‖h • e‖^α
  have hr : 0 ≤ r := Real.rpow_nonneg (norm_nonneg _) _
  let q : Point n := (p.1+h • e,p.2)
  have hq : q ∈ cylinder Set.univ 0 T := ⟨Set.mem_univ _,hp.2⟩
  let Aq : Mat n := spatialDifferenceQuotient a e h p
  let Ad : Mat n := spatialPartial a e p
  let Hq := spatialDD u q
  let H0 := spatialDD u p
  let bq : Yau.RIdx n → ℝ := fun i => spatialDifferenceQuotient (fun q => b q i) e h p
  let bd : Yau.RIdx n → ℝ := fun i => spatialPartial (fun q => b q i) e p
  let Vq := spatialD u q
  let V0 := spatialD u p
  let R0 : ℝ := (M*r)*U+M*(U*r)
  have hADiff : ‖Aq-Ad‖ ≤ M*r := spatial_difference_quotient_bound hα e hDiffa hDa hp hh
  have hAD : ‖Ad‖ ≤ M := hDa.2.1 p hp
  have hHQ : ‖Hq‖ ≤ U := hu.2.2.2.1.2.1 q hq
  have hHDiff : ‖Hq-H0‖ ≤ U*r := holderBound_spatial_increment hα hu.2.2.2.1 hp (h • e)
  have hVQ : ‖Vq‖ ≤ U := (hu.2.2.1 q hq).2
  have hVDiff : ‖Vq-V0‖ ≤ U*r := holderBound_spatial_increment hα (holderBound_snd hLow) hp (h • e)
  have hBDiff (i : Yau.RIdx n) : |bq i-bd i| ≤ M*r := by
    simpa only [spatialDifferenceQuotient,Real.norm_eq_abs,bq,bd,r] using
      spatial_difference_quotient_bound hα e (hDiffb i) (hDb i) hp hh
  have hBD (i : Yau.RIdx n) : |bd i| ≤ M := by
    simpa only [Real.norm_eq_abs] using (hDb i).2.1 p hp
  have hF : |spatialDifferenceQuotient f e h p-spatialPartial f e p| ≤ F*r := by
    simpa only [spatialDifferenceQuotient,Real.norm_eq_abs] using
      spatial_difference_quotient_bound hα e hDifff hDf hp hh
  have hPrincipal := hessian_contraction_difference_bound Aq Ad Hq H0
  have hPrincipal' : |(∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, Aq i j*Hq (Yau.realVec i) (Yau.realVec j))-
      (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, Ad i j*H0 (Yau.realVec i) (Yau.realVec j))| ≤
      (Fintype.card (Yau.RIdx n) : ℝ)^2*R0 := hPrincipal.trans
    (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul hADiff hHQ (norm_nonneg _) (mul_nonneg hDa.1 hr))
      (mul_le_mul hAD hHDiff (norm_nonneg _) hDa.1)) (sq_nonneg _))
  have hDrift := drift_contraction_difference_bound (mul_nonneg hDa.1 hr) hDa.1 bq bd Vq V0 hBDiff hBD
  have hDrift' : |(∑ i : Yau.RIdx n, bq i*Vq (Yau.realVec i))-
      (∑ i : Yau.RIdx n, bd i*V0 (Yau.realVec i))| ≤ (Fintype.card (Yau.RIdx n) : ℝ)*R0 :=
    hDrift.trans (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left hVQ (mul_nonneg hDa.1 hr))
      (mul_le_mul_of_nonneg_left hVDiff hDa.1)) (Nat.cast_nonneg _))
  have hEq : quotientSpatialSource e h u a b f p-linearizedSpatialSource e u a b f p =
      (spatialDifferenceQuotient f e h p-spatialPartial f e p)+
      ((∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, Aq i j*Hq (Yau.realVec i) (Yau.realVec j))-
        (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, Ad i j*H0 (Yau.realVec i) (Yau.realVec j)))+
      ((∑ i : Yau.RIdx n, bq i*Vq (Yau.realVec i))-(∑ i : Yau.RIdx n, bd i*V0 (Yau.realVec i))) := by
    dsimp only [quotientSpatialSource,linearizedSpatialSource,Aq,Ad,Hq,H0,bq,bd,Vq,V0,q]
    ring
  rw [hEq]
  calc
    _ ≤ |spatialDifferenceQuotient f e h p-spatialPartial f e p|+
      |(∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, Aq i j*Hq (Yau.realVec i) (Yau.realVec j))-
        (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, Ad i j*H0 (Yau.realVec i) (Yau.realVec j))|+
      |(∑ i : Yau.RIdx n, bq i*Vq (Yau.realVec i))-(∑ i : Yau.RIdx n, bd i*V0 (Yau.realVec i))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ F*r+(Fintype.card (Yau.RIdx n) : ℝ)^2*R0+(Fintype.card (Yau.RIdx n) : ℝ)*R0 :=
      add_le_add (add_le_add hF hPrincipal') hDrift'
    _ = _ := by dsimp only [linearizedSourceBudget,R0,r]; ring

end Yau.LeafProofs.L16Aux
