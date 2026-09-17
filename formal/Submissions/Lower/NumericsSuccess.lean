import Submissions.Lower.NumericsDefs

/-!
# The numerical success-probability bound

Certificate from Appendix B of the paper: `omega ℓ ≥ (5/256) (c^ℓ - 2^-105)` with `c ≤ exp(-5/256)`
rational, `rankSuccess ℓ ≥ bb ℓ` via tabulated rational upper bounds on `z_ℓ^(1/21)`, and
`signFailure ≤ exp(-256) ≤ 1/257`. The resulting rational sum is checked by kernel evaluation.
-/

namespace OptimalOTS.Numerics

namespace SuccessAux

/-- `rTab[ℓ - 2] / 2^20` is an upper bound on `(512 (ℓ - 1) / 255500)^(1/21)`. -/
def rTab : List ℕ := [780042, 806219, 821937, 833274, 842175, 849519, 855778, 861237, 866081, 870437, 874396, 878027, 881380, 884496, 887406, 890138, 892711, 895144, 897452, 899647, 901739, 903739, 905654, 907491, 909257, 910957, 912596, 914177, 915706, 917186, 918619, 920009, 921358, 922669, 923943, 925183, 926391, 927568, 928717, 929837, 930931, 932000, 933045, 934067, 935067, 936046, 937005, 937945, 938866, 939770, 940656, 941527, 942381, 943220, 944045, 944855, 945652, 946435, 947206, 947964, 948711, 949446, 950169, 950882, 951585, 952277, 952959, 953631, 954295, 954949, 955594, 956231, 956859, 957479, 958091, 958696, 959293, 959882, 960465, 961040, 961609, 962171, 962726, 963276, 963819, 964356, 964887, 965412, 965931, 966445, 966954, 967457, 967956, 968449, 968937, 969420, 969899, 970372, 970842, 971306, 971767, 972223, 972675, 973122, 973566, 974005, 974441, 974873, 975301, 975725, 976145, 976562, 976976, 977386, 977792, 978196, 978596, 978992, 979386, 979776, 980163, 980548, 980929, 981307, 981682, 982055, 982425, 982792, 983156, 983518, 983877, 984233, 984587, 984938, 985287, 985633, 985977, 986319, 986658, 986995, 987329, 987661, 987992, 988319, 988645, 988969, 989290, 989610, 989927, 990243, 990556, 990867, 991177, 991484, 991790, 992094, 992396, 992696, 992994, 993290, 993585, 993878, 994170, 994459, 994747, 995033, 995318, 995601, 995882, 996162, 996440, 996717, 996992, 997266, 997538, 997809, 998078, 998346, 998612, 998877, 999141, 999403, 999664, 999923, 1000181, 1000438, 1000694, 1000948, 1001201, 1001452, 1001703, 1001952, 1002200, 1002446, 1002692, 1002936, 1003179, 1003421, 1003662, 1003901, 1004140, 1004377, 1004613, 1004848, 1005082, 1005315, 1005547, 1005778, 1006008, 1006236, 1006464, 1006691, 1006916, 1007141, 1007365, 1007587, 1007809, 1008030, 1008249, 1008468, 1008686, 1008903, 1009119, 1009334, 1009548, 1009761, 1009973, 1010185, 1010395, 1010605, 1010814, 1011022, 1011229, 1011435, 1011640, 1011845, 1012049, 1012252, 1012454, 1012655, 1012856, 1013055, 1013254, 1013453, 1013650, 1013847, 1014042, 1014238, 1014432, 1014626, 1014818, 1015011, 1015202, 1015393, 1015583, 1015772, 1015961, 1016149, 1016336, 1016522, 1016708, 1016893, 1017078, 1017262, 1017445, 1017627, 1017809, 1017990, 1018171, 1018351, 1018530, 1018709, 1018887, 1019064, 1019241, 1019417, 1019593, 1019768, 1019942, 1020116, 1020289, 1020462, 1020634, 1020805, 1020976, 1021146, 1021316, 1021485, 1021654, 1021822, 1021989, 1022156, 1022323, 1022489, 1022654, 1022819, 1022983, 1023147, 1023310, 1023473, 1023635, 1023797, 1023958, 1024119, 1024279, 1024438, 1024598, 1024756, 1024914, 1025072, 1025229, 1025386, 1025542, 1025698, 1025853, 1026008, 1026163, 1026317, 1026470, 1026623, 1026776, 1026928, 1027079, 1027231, 1027381, 1027532, 1027682, 1027831, 1027980, 1028129, 1028277, 1028424, 1028572, 1028719, 1028865, 1029011, 1029157, 1029302, 1029447, 1029591, 1029735, 1029879, 1030022, 1030165, 1030307, 1030449, 1030591, 1030732, 1030873, 1031013, 1031153, 1031293, 1031432, 1031571, 1031710, 1031848, 1031986, 1032123, 1032261, 1032397, 1032534, 1032670, 1032805, 1032941, 1033076, 1033210, 1033344, 1033478, 1033612, 1033745, 1033878, 1034011, 1034143, 1034275, 1034406, 1034537, 1034668, 1034799, 1034929, 1035059, 1035188, 1035318, 1035446, 1035575, 1035703, 1035831, 1035959, 1036086, 1036213, 1036340, 1036466, 1036592, 1036718, 1036844, 1036969, 1037094, 1037218, 1037342, 1037466, 1037590, 1037713, 1037836, 1037959, 1038082, 1038204, 1038326, 1038448, 1038569, 1038690, 1038811, 1038931, 1039052, 1039171, 1039291, 1039411, 1039530, 1039649, 1039767, 1039885, 1040004, 1040121, 1040239, 1040356, 1040473, 1040590, 1040706, 1040822, 1040938, 1041054, 1041169, 1041285, 1041400, 1041514, 1041629, 1041743, 1041857, 1041970, 1042084, 1042197, 1042310, 1042423, 1042535, 1042647, 1042759, 1042871, 1042982, 1043094, 1043205, 1043315]

/-- A rational lower bound on `exp (-5/256)`. -/
def cc : ℚ := 8423790037 / 8589934592

/-- Rational lower bound on `rankSuccess ℓ`. -/
def bb (ℓ : ℕ) : ℚ :=
  if ℓ = 1 then 1 else
    511 / 512 * (1 - 21 / 20 * ((rTab.getD (ℓ - 2) 0 : ℚ) / 2 ^ 20) +
      (512 * ((ℓ : ℚ) - 1) / 255500) / 20)

/-- Rational lower bound on `omega ℓ * rankSuccess ℓ`. -/
def gg (ℓ : ℕ) : ℚ := 5 / 256 * (cc ^ ℓ - 1 / 2 ^ 105) * bb ℓ

theorem tab_ok : ∀ ℓ < 451, 2 ≤ ℓ →
    512 * (ℓ - 1) * (2 ^ 20) ^ 21 ≤ 255500 * (rTab.getD (ℓ - 2) 0) ^ 21 := by
  decide +kernel

theorem nonneg_ok : ∀ ℓ < 451, 1 ≤ ℓ → 0 ≤ bb ℓ ∧ 1 / 2 ^ 105 ≤ cc ^ ℓ := by
  decide +kernel

theorem sum_ok : (3 / 32 : ℚ) < 256 / 257 * ∑ ℓ ∈ Finset.Icc 1 450, gg ℓ := by
  decide +kernel


theorem cc_le_exp : ((cc : ℚ) : ℝ) ≤ Real.exp (-(5 / 256)) := by
  have h := Real.exp_bound (x := -(5 / 256 : ℝ)) (by norm_num [abs_of_neg]) (n := 4) (by norm_num)
  have h' := (abs_le.1 h).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h'
  norm_num [abs_of_neg] at h'
  simp only [cc]
  push_cast
  linarith

theorem omega_ge (ℓ : ℕ) (h1 : 1 ≤ ℓ) (h450 : ℓ ≤ 450) :
    5 / 256 * (((cc : ℚ) : ℝ) ^ ℓ - 1 / 2 ^ 105) ≤ omega ℓ := by
  have hN : (N : ℝ) = 2 ^ 128 := by norm_num [N]
  have hTN : (T : ℝ) * (1 / N) = 5 / 256 := by rw [hN]; norm_num [T]
  have hx1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast h1
  have hx450 : (ℓ : ℝ) ≤ 450 := by exact_mod_cast h450
  set x : ℝ := (ℓ : ℝ) with hx
  set b : ℝ := 1 - x / N with hb
  have hxN : x / N ≤ 1 / 2 ^ 119 := by
    rw [hN, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hxN0 : 0 ≤ x / N := by rw [hN]; positivity
  have hbpos : 0 < b := by rw [hb]; linarith [show (1 : ℝ) / 2 ^ 119 < 1 / 2 by norm_num]
  have hb2 : 1 / 2 ≤ b := by rw [hb]; linarith [show (1 : ℝ) / 2 ^ 119 < 1 / 2 by norm_num]
  have hb1 : b ≤ 1 := by rw [hb]; linarith
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  -- Step A: omega ℓ ≥ (T / N) b ^ T
  have hA : 5 / 256 * b ^ T ≤ omega ℓ := by
    have hd : 1 - (x - 1) / N = b * (1 + 1 / N / b) := by
      rw [mul_add, mul_one, mul_div_cancel₀ _ hbpos.ne', hb]; ring
    unfold omega
    rw [← hx, hd, mul_pow]
    have hbern := one_add_mul_le_pow (a := 1 / N / b)
      (by have : 0 ≤ 1 / N / b := by positivity
          linarith) T
    have hdb : (1 : ℝ) / N ≤ 1 / N / b := le_div_self (by positivity) hbpos hb1
    have hbT : 0 < b ^ T := pow_pos hbpos T
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    calc 5 / 256 * b ^ T = b ^ T * (T * (1 / N)) := by rw [hTN]; ring
      _ ≤ b ^ T * (T * (1 / N / b)) := by gcongr
      _ = b ^ T * (1 + T * (1 / N / b)) - b ^ T := by ring
      _ ≤ b ^ T * (1 + 1 / N / b) ^ T - b ^ T := by gcongr
  -- Step B: b ^ T ≥ exp (-(x * 5 / 256)) - 2^-105
  have hkey : -(x * (5 / 256)) - 1 / 2 ^ 105 ≤ (T : ℝ) * (1 - b⁻¹) := by
    have he : (T : ℝ) * (1 - b⁻¹) = -(5 / 256 * x / b) := by
      rw [← hTN]; field_simp; rw [hb]; field_simp; ring
    have h5 : x * (x / N) ≤ 450 * (1 / 2 ^ 119) := mul_le_mul hx450 hxN hxN0 (by norm_num)
    have h6 : (x * (5 / 256) + 1 / 2 ^ 105) * b =
        x * (5 / 256) - 5 / 256 * (x * (x / N)) + 1 / 2 ^ 105 * b := by rw [hb]; ring
    have h7 : 5 / 256 * x / b ≤ x * (5 / 256) + 1 / 2 ^ 105 := by
      rw [div_le_iff₀ hbpos, h6]; nlinarith [h5, hb2]
    rw [he]; linarith
  have hB : Real.exp (-(x * (5 / 256))) - 1 / 2 ^ 105 ≤ b ^ T := by
    have hlog : 1 - b⁻¹ ≤ Real.log b := Real.one_sub_inv_le_log_of_pos hbpos
    have hbT : b ^ T = Real.exp (T * Real.log b) := by
      rw [Real.exp_nat_mul, Real.exp_log hbpos]
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    have h2 : Real.exp (-(x * (5 / 256)) - 1 / 2 ^ 105) ≤ b ^ T := by
      rw [hbT]; apply Real.exp_le_exp.2
      calc _ ≤ (T : ℝ) * (1 - b⁻¹) := hkey
        _ ≤ T * Real.log b := by gcongr
    have hE : Real.exp (-(x * (5 / 256))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hE0 := Real.exp_pos (-(x * (5 / 256)))
    have h3 : 1 - 1 / 2 ^ 105 ≤ Real.exp (-(1 / 2 ^ 105 : ℝ)) := Real.one_sub_le_exp_neg _
    rw [sub_eq_add_neg, Real.exp_add] at h2
    nlinarith
  have hC : ((cc : ℚ) : ℝ) ^ ℓ ≤ Real.exp (-(x * (5 / 256))) := by
    rw [show -(x * (5 / 256)) = (ℓ : ℝ) * (-(5 / 256)) by rw [hx]; ring, Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by simp only [cc]; norm_num) cc_le_exp
  nlinarith

theorem rank_ge (ℓ : ℕ) (h1 : 1 ≤ ℓ) (h450 : ℓ ≤ 450) : ((bb ℓ : ℚ) : ℝ) ≤ rankSuccess ℓ := by
  unfold bb rankSuccess
  by_cases h : ℓ = 1
  · simp [h]
  · simp only [if_neg h]
    have h2 : 2 ≤ ℓ := by omega
    have ht := tab_ok ℓ (by omega) h2
    have hx1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast h1
    set K := rTab.getD (ℓ - 2) 0
    have hz0 : (0 : ℝ) ≤ 512 * ((ℓ : ℝ) - 1) / 255500 := by
      have : (0 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
      positivity
    have hr : 512 * ((ℓ : ℝ) - 1) / 255500 ≤ ((K : ℝ) / 2 ^ 20) ^ 21 := by
      have : ((512 * (ℓ - 1) * (2 ^ 20) ^ 21 : ℕ) : ℝ) ≤ ((255500 * K ^ 21 : ℕ) : ℝ) := by
        exact_mod_cast ht
      push_cast [Nat.cast_sub h1] at this
      rw [div_pow, div_le_div_iff₀ (by norm_num) (by positivity)]
      linarith
    have hroot : (512 * ((ℓ : ℝ) - 1) / 255500) ^ ((1 : ℝ) / 21) ≤ (K : ℝ) / 2 ^ 20 := by
      calc (512 * ((ℓ : ℝ) - 1) / 255500) ^ ((1 : ℝ) / 21)
          ≤ (((K : ℝ) / 2 ^ 20) ^ 21) ^ ((1 : ℝ) / 21) :=
            Real.rpow_le_rpow hz0 hr (by norm_num)
        _ = (K : ℝ) / 2 ^ 20 := by
          rw [show ((1 : ℝ) / 21) = ((21 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
    push_cast
    nlinarith

theorem signFailure_le : signFailure ≤ 1 / 257 := by
  unfold signFailure
  have h1 : (0 : ℝ) ≤ 1 - (2 : ℝ)⁻¹ ^ 13 := by norm_num
  calc (1 - (2 : ℝ)⁻¹ ^ 13) ^ (2 ^ 21)
      ≤ (Real.exp (-((2 : ℝ)⁻¹ ^ 13))) ^ (2 ^ 21) :=
        pow_le_pow_left₀ h1 (Real.one_sub_le_exp_neg _) _
    _ = Real.exp (-256) := by
        rw [← Real.exp_nat_mul]; norm_num
    _ ≤ 1 / 257 := by
        rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith [Real.add_one_le_exp 256]

theorem sum_ge : ((∑ ℓ ∈ Finset.Icc 1 450, gg ℓ : ℚ) : ℝ) ≤
    ∑ ℓ ∈ Finset.Icc 1 450, omega ℓ * rankSuccess ℓ := by
  rw [Rat.cast_sum]
  apply Finset.sum_le_sum
  intro ℓ hℓ
  rw [Finset.mem_Icc] at hℓ
  obtain ⟨hb0, hc⟩ := nonneg_ok ℓ (by omega) hℓ.1
  have hω := omega_ge ℓ hℓ.1 hℓ.2
  have hr := rank_ge ℓ hℓ.1 hℓ.2
  have hc' : ((1 / 2 ^ 105 : ℚ) : ℝ) ≤ ((cc ^ ℓ : ℚ) : ℝ) := by exact_mod_cast hc
  push_cast at hc'
  have hA : (0 : ℝ) ≤ 5 / 256 * (((cc : ℚ) : ℝ) ^ ℓ - 1 / 2 ^ 105) := by nlinarith
  have hB : (0 : ℝ) ≤ ((bb ℓ : ℚ) : ℝ) := by exact_mod_cast hb0
  unfold gg
  push_cast
  exact mul_le_mul hω hr hB (hA.trans hω)

end SuccessAux

theorem success_lt :
    3 / 32 < (1 - signFailure) * ∑ ℓ ∈ Finset.Icc 1 450, omega ℓ * rankSuccess ℓ := by
  have hq : (3 / 32 : ℝ) < 256 / 257 * ((∑ ℓ ∈ Finset.Icc 1 450, SuccessAux.gg ℓ : ℚ) : ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).2 SuccessAux.sum_ok
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using this
  have hs := SuccessAux.sum_ge
  have hF := SuccessAux.signFailure_le
  have hG : (0 : ℝ) ≤ ((∑ ℓ ∈ Finset.Icc 1 450, SuccessAux.gg ℓ : ℚ) : ℝ) := by nlinarith
  calc (3 / 32 : ℝ) < 256 / 257 * ((∑ ℓ ∈ Finset.Icc 1 450, SuccessAux.gg ℓ : ℚ) : ℝ) := hq
    _ ≤ (1 - signFailure) * ∑ ℓ ∈ Finset.Icc 1 450, omega ℓ * rankSuccess ℓ :=
        mul_le_mul (by linarith) hs hG (by linarith)

end OptimalOTS.Numerics
