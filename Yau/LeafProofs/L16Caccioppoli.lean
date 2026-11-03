import Yau.LeafProofs.L16EnergyLimit

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

private theorem caccioppoli_young {lam x y : ℝ} (hlam : 0 < lam) :
    |x*y| ≤ lam/2*x^2+y^2/(2*lam) := by
  apply (mul_le_mul_iff_left₀ (show 0 < 2*lam by positivity)).mp
  have h1 := sq_nonneg (lam*x-y)
  have h2 := sq_nonneg (lam*x+y)
  have he : (lam/2*x^2+y^2/(2*lam))*(2*lam) = lam^2*x^2+y^2 := by
    field_simp
  rw [he]
  rw [abs_mul]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]; nlinarith
    · rw [abs_of_neg (lt_of_not_ge hy)]; nlinarith
  · rw [abs_of_neg (lt_of_not_ge hx)]
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]; nlinarith
    · rw [abs_of_neg (lt_of_not_ge hy)]; nlinarith

private theorem caccioppoli_abs_mul_le_sq (x y : ℝ) : |x*y| ≤ x^2+y^2 := by
  have h := caccioppoli_young (x := x) (y := y) (lam := 1) (by norm_num)
  nlinarith [sq_nonneg x,sq_nonneg y]

private theorem caccioppoli_forcing_bound {ι : Type*} [Fintype ι]
    {a : ι → ι → ℝ} {c F d : ι → ℝ} {e w A B M : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (ha : ∀ i j, |a i j| ≤ A) (hc : ∀ i, |c i| ≤ B)
    (he : |e| ≤ 1) (hd : ∀ i, |d i| ≤ M) (i : ι) :
    |e*F i+2*w*(∑ j : ι, d j*a j i)-e*c i*w|^2 ≤
      2*(F i)^2+2*(2*(Fintype.card ι : ℝ)*A*M+B)^2*w^2 := by
  have hs : |∑ j : ι, d j*a j i| ≤ (Fintype.card ι : ℝ)*M*A := by
    calc
      _ ≤ ∑ j : ι, |d j*a j i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ι, M*A := Finset.sum_le_sum (fun j _ => by
        rw [abs_mul]
        exact mul_le_mul (hd j) (ha j i) (abs_nonneg _) hM)
      _ = _ := by simp; ring
  have hL : |e*F i+2*w*(∑ j : ι, d j*a j i)-e*c i*w| ≤
      |F i|+(2*(Fintype.card ι : ℝ)*A*M+B)*|w| := by
    calc
      _ ≤ |e*F i|+|2*w*(∑ j : ι, d j*a j i)|+|e*c i*w| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |F i|+2*|w| *((Fintype.card ι : ℝ)*M*A)+B*|w| := by
        apply add_le_add
        · apply add_le_add
          · simpa only [abs_mul,one_mul] using mul_le_mul_of_nonneg_right he (abs_nonneg (F i))
          · simp only [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)]
            exact mul_le_mul_of_nonneg_left hs (by positivity)
        · calc
            _ = |e| * |c i| * |w| := by rw [abs_mul,abs_mul]
            _ ≤ 1*B*|w| := mul_le_mul_of_nonneg_right
              (mul_le_mul he (hc i) (abs_nonneg _) (by norm_num)) (abs_nonneg _)
            _ = _ := by ring
      _ = _ := by ring
  have hsq := sq_le_sq₀ (abs_nonneg _) (show 0 ≤ |F i|+(2*(Fintype.card ι : ℝ)*A*M+B)*|w| by positivity) |>.2 hL
  have hCross := sq_nonneg (|F i|-(2*(Fintype.card ι : ℝ)*A*M+B)*|w|)
  nlinarith [sq_abs (F i),sq_abs w]

private theorem caccioppoli_finite_estimate {ι : Type*} [Fintype ι]
    {a : ι → ι → ℝ} {c H F d : ι → ℝ} {e w f dt lam A B M : ℝ}
    (hlam : 0 < lam) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (ha : ∀ i j, |a i j| ≤ A) (hc : ∀ i, |c i| ≤ B)
    (he : |e| ≤ 1) (hd : ∀ i, |d i| ≤ M) (hdt : |dt| ≤ M)
    (hell : lam*(∑ i : ι, (e*H i)^2) ≤ ∑ i : ι, ∑ j : ι, a i j*(e*H i)*(e*H j)) :
    lam/2*(e^2*∑ i : ι, (H i)^2) ≤
      (-(e*dt)*w^2+
        (∑ i : ι, (e^2*((∑ j : ι, a i j*H j)+F i)*H i+
          2*e*d i*((∑ j : ι, a i j*H j)+F i)*w))-
        e^2*((∑ i : ι, c i*H i)+f)*w)+
      (1/lam+M+(Fintype.card ι : ℝ)*(2*(Fintype.card ι : ℝ)*A*M+B)^2/lam+
        (Fintype.card ι : ℝ)*M+M+1)*(w^2+(∑ i : ι, (F i)^2)+f^2) := by
  let K : ℝ := 2*(Fintype.card ι : ℝ)*A*M+B
  let L : ι → ℝ := fun i => e*F i+2*w*(∑ j : ι, d j*a j i)-e*c i*w
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL (i : ι) : (L i)^2 ≤ 2*(F i)^2+2*K^2*w^2 := by
    simpa only [L,K,sq_abs] using caccioppoli_forcing_bound hA hB hM ha hc he hd i
  have hYoung (i : ι) : -(lam/2*(e*H i)^2+((F i)^2+K^2*w^2)/lam) ≤ (e*H i)*L i := by
    have hY := caccioppoli_young (x := e*H i) (y := L i) hlam
    have hD : (L i)^2/(2*lam) ≤ ((F i)^2+K^2*w^2)/lam := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2*lam) hlam).2
      nlinarith [hL i]
    have hAbs := neg_abs_le ((e*H i)*L i)
    linarith
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hYoung i)
  have hTime : -(M*w^2) ≤ -(e*dt)*w^2 := by
    have hb : e*dt ≤ M := (le_abs_self _).trans (by
      rw [abs_mul]
      exact (mul_le_mul he hdt (abs_nonneg _) (by norm_num)).trans (by simp))
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sq_nonneg w)]
  have hCut (i : ι) : -(M*((F i)^2+w^2)) ≤ 2*e*d i*F i*w := by
    have hCoeff : |e*d i| ≤ M := by
      rw [abs_mul]
      exact (mul_le_mul he (hd i) (abs_nonneg _) (by norm_num)).trans (by simp)
    have hAbs : |2*e*d i*F i*w| ≤ M*((F i)^2+w^2) := by
      calc
        _ = 2*|e*d i| *|F i*w| := by rw [abs_mul,abs_mul,abs_mul]; simp; ring
        _ ≤ 2*M*|F i*w| := by gcongr
        _ ≤ M*((F i)^2+w^2) := by
          have hY := caccioppoli_young (x := F i) (y := w) (lam := 1) (by norm_num)
          nlinarith [mul_nonneg hM (sub_nonneg.mpr hY)]
    exact (neg_le_neg hAbs).trans (neg_abs_le _)
  have hCuts := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hCut i)
  have hSource : -(f^2+w^2) ≤ -(e^2*f*w) := by
    have he2 : |e|^2 ≤ 1 := by nlinarith [abs_nonneg e]
    have hb : |e^2*f*w| ≤ f^2+w^2 := by
      calc
        _ = |e|^2*|f*w| := by rw [abs_mul,abs_mul,abs_pow,abs_mul]; ring
        _ ≤ 1*|f*w| := mul_le_mul_of_nonneg_right he2 (abs_nonneg _)
        _ ≤ _ := by simpa using caccioppoli_abs_mul_le_sq f w
    linarith [le_abs_self (e^2*f*w)]
  have hSwap : (∑ i : ι, (e*H i)*(2*w*(∑ j : ι, d j*a j i))) =
      ∑ i : ι, 2*e*d i*(∑ j : ι, a i j*H j)*w := by
    simp only [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hQuad (i : ι) : e^2*(∑ j : ι, a i j*H j)*H i =
      ∑ j : ι, a i j*(e*H i)*(e*H j) := by
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hDrift : (∑ i : ι, (e*H i)*(e*c i*w)) = e^2*(∑ i : ι, c i*H i)*w := by
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hPoint (i : ι) :
      e^2*((∑ j : ι, a i j*H j)+F i)*H i+2*e*d i*((∑ j : ι, a i j*H j)+F i)*w =
      (∑ j : ι, a i j*(e*H i)*(e*H j))+(e*H i)*(e*F i)+
        2*e*d i*(∑ j : ι, a i j*H j)*w+2*e*d i*F i*w := by
    calc
      _ = e^2*(∑ j : ι, a i j*H j)*H i+(e*H i)*(e*F i)+
          2*e*d i*(∑ j : ι, a i j*H j)*w+2*e*d i*F i*w := by ring
      _ = _ := by rw [hQuad]
  have hLsum : (∑ i : ι, (e*H i)*L i) =
      (∑ i : ι, (e*H i)*(e*F i))+
        (∑ i : ι, 2*e*d i*(∑ j : ι, a i j*H j)*w)-e^2*(∑ i : ι, c i*H i)*w := by
    dsimp only [L]
    simp_rw [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [hSwap,hDrift]
  have hAlg :
      (-(e*dt)*w^2+(∑ i : ι, (e^2*((∑ j : ι, a i j*H j)+F i)*H i+
          2*e*d i*((∑ j : ι, a i j*H j)+F i)*w))-e^2*((∑ i : ι, c i*H i)+f)*w) =
      (∑ i : ι, ∑ j : ι, a i j*(e*H i)*(e*H j))+(∑ i : ι, (e*H i)*L i)-
        e*dt*w^2+(∑ i : ι, 2*e*d i*F i*w)-e^2*f*w := by
    simp_rw [hPoint,Finset.sum_add_distrib,hLsum]
    ring
  rw [hAlg]
  have hT : (∑ i : ι, (e*H i)^2) = e^2*∑ i : ι, (H i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hErrSum : (∑ i : ι, ((F i)^2+K^2*w^2)/lam) =
      ((∑ i : ι, (F i)^2)+(Fintype.card ι : ℝ)*K^2*w^2)/lam := by
    rw [← Finset.sum_div,Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring
  have hCutSum : (∑ i : ι, M*((F i)^2+w^2)) =
      M*(∑ i : ι, (F i)^2)+(Fintype.card ι : ℝ)*M*w^2 := by
    rw [← Finset.mul_sum,Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring
  simp only [Finset.sum_neg_distrib,Finset.sum_add_distrib,hErrSum,hCutSum] at hSum hCuts
  rw [hT] at hell
  have hSumT : (∑ i : ι, lam/2*(e*H i)^2) = lam/2*(e^2*∑ i : ι, (H i)^2) := by
    rw [← Finset.mul_sum,hT]
  rw [hSumT] at hSum
  have hSF : 0 ≤ ∑ i : ι, (F i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hD : 0 ≤ (Fintype.card ι : ℝ)*K^2/lam := by positivity
  have hInv : 0 ≤ 1/lam := by positivity
  have hDM : 0 ≤ (Fintype.card ι : ℝ)*M := by positivity
  dsimp only [K] at hSum hD ⊢
  simp only [div_eq_mul_inv] at hSum hD hInv ⊢
  nlinarith [sq_nonneg w,sq_nonneg f,
    mul_nonneg hD hSF,mul_nonneg hD (sq_nonneg f),
    mul_nonneg hInv (sq_nonneg w),mul_nonneg hInv (sq_nonneg f),
    mul_nonneg hM (sq_nonneg w),mul_nonneg hM (sq_nonneg f),
    mul_nonneg hDM hSF,mul_nonneg hDM (sq_nonneg f),
    mul_nonneg hM hSF]

private theorem caccioppoli_energy_integrable {n : ℕ}
    {ψ w R : Point n → ℝ} {H P : Point n → Yau.RIdx n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hw : MemLp w 2 volume) (hH : ∀ i, MemLp (fun p => H p i) 2 volume)
    (hP : ∀ i, MemLp (fun p => P p i) 2 volume) (hR : MemLp R 2 volume) :
    Integrable (fun p => -(1/2 : ℝ)*fderiv ℝ ψ p (0,1)*(w p)^2+
      (∑ i, P p i*(ψ p*H p i+w p*fderiv ℝ ψ p (Yau.realVec i,0)))-R p*ψ p*w p) volume := by
  have hTop : MemLp ψ (⊤ : ENNReal) volume := hψ.continuous.memLp_top_of_hasCompactSupport hcψ _
  have hDTop (v : Point n) : MemLp (fun p => fderiv ℝ ψ p v) (⊤ : ENNReal) volume :=
    ((hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.memLp_top_of_hasCompactSupport
      (hcψ.fderiv_apply ℝ v) _
  have hA := integrable_weighted_mul_of_memLp (hDTop (0,1)) hw hw
  have hB (i : Yau.RIdx n) := integrable_weighted_mul_of_memLp hTop (hP i) (hH i)
  have hC (i : Yau.RIdx n) := integrable_weighted_mul_of_memLp (hDTop (Yau.realVec i,0)) (hP i) hw
  have hD := integrable_weighted_mul_of_memLp hTop hR hw
  have hSum := integrable_finsetSum Finset.univ (fun i _ => (hB i).add (hC i))
  have hInt := ((hA.const_mul (-(1/2 : ℝ))).add hSum).sub hD
  refine hInt.congr (Filter.Eventually.of_forall ?_)
  intro p
  dsimp only [Pi.add_apply,Pi.sub_apply]
  have hEq : (∑ i, (ψ p*P p i*H p i+fderiv ℝ ψ p (Yau.realVec i,0)*P p i*w p)) =
      ∑ i, P p i*(ψ p*H p i+w p*fderiv ℝ ψ p (Yau.realVec i,0)) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hEq]
  ring

/-- The Caccioppoli constant is chosen from numerical data before any coefficient or field. -/
theorem exists_caccioppoli_constant (n : ℕ) (lam upper A B M : ℝ)
    (hlam : 0 < lam) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ (Q : Set (Point n)) (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
        (η w f : Point n → ℝ) (H P F : Point n → Yau.RIdx n → ℝ) (R : Point n → ℝ),
      Elliptic Q a lam upper →
      (∀ p ∈ Q, ∀ i j, |a p i j| ≤ A) → (∀ p ∈ Q, ∀ i, |c p i| ≤ B) →
      Test Q η → (∀ p, |η p| ≤ 1) →
      (∀ p, |fderiv ℝ η p (0,1)| ≤ M) →
      (∀ p, ∀ i, |fderiv ℝ η p (Yau.realVec i,0)| ≤ M) →
      MemLp w 2 volume → (∀ i, MemLp (fun p => H p i) 2 volume) →
      (∀ i, MemLp (fun p => P p i) 2 volume) → MemLp R 2 volume →
      (∀ i, MemLp (fun p => F p i) 2 volume) → MemLp f 2 volume →
      (∀ p ∈ tsupport η, ∀ i, P p i = energyFlux a H p i+F p i) →
      (∀ p ∈ tsupport η, R p = (∑ i, c p i*H p i)+f p) →
      compactEnergyFunctional (fun p => η p^2) w H P R = 0 →
      (∫ p, η p^2*(∑ i, (H p i)^2)) ≤
        C0*(∫ p, (w p)^2+(∑ i, (F p i)^2)+(f p)^2) := by
  let N : ℝ := Fintype.card (Yau.RIdx n)
  let K : ℝ := 2*N*A*M+B
  let C : ℝ := 1/lam+M+N*K^2/lam+N*M+M+1
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨2*C/lam,by positivity,?_⟩
  intro Q a c η w f H P F R hEll ha hc hη hηBound hTime hSpace hw hH hP hR hF hf hFlux hSource hEnergy
  let ψ : Point n → ℝ := fun p => η p^2
  let T : Point n → ℝ := fun p => η p^2*(∑ i, (H p i)^2)
  let D : Point n → ℝ := fun p => (w p)^2+(∑ i, (F p i)^2)+(f p)^2
  let J : Point n → ℝ := fun p => -(1/2 : ℝ)*fderiv ℝ ψ p (0,1)*(w p)^2+
      (∑ i, P p i*(ψ p*H p i+w p*fderiv ℝ ψ p (Yau.realVec i,0)))-R p*ψ p*w p
  have hψ : ContDiff ℝ ∞ ψ := hη.1.pow 2
  have hSquare (v : Point n → ℝ) : (fun p => v p^2) = v*v := by
    funext p
    rw [Pi.mul_apply,pow_two]
  have hcψ : HasCompactSupport ψ := by
    change HasCompactSupport (fun p => η p^2)
    rw [hSquare]
    exact hη.2.1.mul_right
  have hDeriv (p v : Point n) : fderiv ℝ ψ p v = 2*η p*fderiv ℝ η p v := by
    have hd := hη.1.differentiable (by simp) p
    dsimp only [ψ]
    simp only [pow_two]
    rw [fderiv_fun_mul hd hd]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring
  have hJInt : Integrable J volume := caccioppoli_energy_integrable hψ hcψ hw hH hP hR
  have hJZero : (∫ p, J p) = 0 :=
    (integral_energy_eq_compactEnergyFunctional hψ hcψ hw hH hP hR).trans hEnergy
  have hTop : MemLp ψ (⊤ : ENNReal) volume := hψ.continuous.memLp_top_of_hasCompactSupport hcψ _
  have hTi (i : Yau.RIdx n) : Integrable (fun p => η p^2*(H p i)^2) volume := by
    simpa only [ψ,pow_two,mul_assoc] using integrable_weighted_mul_of_memLp hTop (hH i) (hH i)
  have hTInt : Integrable T volume := by
    have hInt := integrable_finsetSum Finset.univ (fun i _ => hTi i)
    simpa only [T,Finset.mul_sum] using hInt
  have hWInt : Integrable (fun p => (w p)^2) volume := by
    rw [hSquare]
    exact hw.integrable_mul hw
  have hFiInt (i : Yau.RIdx n) : Integrable (fun p => (F p i)^2) volume := by
    rw [hSquare]
    exact (hF i).integrable_mul (hF i)
  have hFInt := integrable_finsetSum Finset.univ (fun i _ => hFiInt i)
  have hfInt : Integrable (fun p => (f p)^2) volume := by
    rw [hSquare]
    exact hf.integrable_mul hf
  have hDInt : Integrable D volume := (hWInt.add hFInt).add hfInt
  have hPoint (p : Point n) : lam/2*T p ≤ J p+C*D p := by
    by_cases hp : p ∈ tsupport η
    · have hpQ := hη.2.2 hp
      have hLower := (hEll.2.2 p hpQ).2 (fun i => η p*H p i) |>.1
      have hFinite := caccioppoli_finite_estimate hlam hA hB hM (ha p hpQ) (hc p hpQ)
        (hηBound p) (hSpace p) (hTime p) hLower (w := w p) (f := f p) (F := F p)
      have hEach (i : Yau.RIdx n) :
          P p i*(ψ p*H p i+w p*fderiv ℝ ψ p (Yau.realVec i,0)) =
          η p^2*((∑ j, a p i j*H p j)+F p i)*H p i+
            2*η p*fderiv ℝ η p (Yau.realVec i,0)*((∑ j, a p i j*H p j)+F p i)*w p := by
        rw [hFlux p hp i,hDeriv]
        dsimp only [energyFlux,ψ]
        ring
      have hJEq : J p = -(η p*fderiv ℝ η p (0,1))*(w p)^2+
          (∑ i, (η p^2*((∑ j, a p i j*H p j)+F p i)*H p i+
            2*η p*fderiv ℝ η p (Yau.realVec i,0)*((∑ j, a p i j*H p j)+F p i)*w p))-
          η p^2*((∑ i, c p i*H p i)+f p)*w p := by
        dsimp only [J]
        simp_rw [hEach]
        rw [hDeriv,hSource p hp]
        dsimp only [ψ]
        ring
      rw [hJEq]
      exact hFinite
    · have hz : η p = 0 := image_eq_zero_of_notMem_tsupport hp
      have hJp : J p = 0 := by
        dsimp only [J,ψ]
        simp only [hDeriv,ψ,hz,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_mul,add_zero,
          Finset.sum_const_zero,sub_zero]
      have hTp : T p = 0 := by simp only [T,hz,zero_pow (by decide : 2 ≠ 0),zero_mul]
      rw [hJp,hTp,mul_zero,zero_add]
      apply mul_nonneg hC.le
      dsimp only [D]
      positivity
  have hInt := integral_mono (hTInt.const_mul (lam/2)) (hJInt.add (hDInt.const_mul C)) hPoint
  simp only [Pi.add_apply] at hInt
  rw [integral_const_mul,integral_add hJInt (hDInt.const_mul C),integral_const_mul,hJZero,zero_add] at hInt
  change (∫ p, T p) ≤ (2*C/lam)*(∫ p, D p)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlam).mpr
  nlinarith

end Yau.LeafProofs.L16Aux
